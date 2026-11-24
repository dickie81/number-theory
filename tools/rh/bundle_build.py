#!/usr/bin/env python3
"""Compile the files that the archive's top theorems need, many files to a process, and keep count of every error.

    python3 -I tools/rh/bundle_build.py --out OUT [--roots NAME ...] [--add NAME ...] [--jobs N] [--retry] [--dry-run]

`lean` takes five to eight seconds to import Mathlib and a few milliseconds a line after that, and the archive is
175 187 short files; `lean/Bundle.lean` imports once and elaborates many files as one module. This script decides
what to compile and in what order, runs that program, and records the result.

1. What is needed. The declarations that the roots reach in the map of `decl_map.py` (rule W of `decl_query.py`),
   with the commands that define syntax and the instances and attribute commands that name no archive constant,
   where a needed file imports them. Then whole files: every declaration of a file that holds a needed one is
   needed too, and so on. A file is compiled whole, but for its `example`s. (Leaving out the declarations of a
   file that nothing names breaks the file: a later proof may use one through `simp` or an instance.)
2. Order. The files of one level of the import graph do not import each other. A level is cut into chunks of
   about `--chunk` lines, `--jobs` of them running at a time; each chunk is one bundle, a module `B.<name>`, and
   it imports Mathlib and the bundles of the lower levels. Five things keep a bundle from breaking a file
   that compiles alone:
   * two files that declare a private name with the same name, or one privately and one publicly, are not put in
     one bundle (Lean keeps the declarations of the module it compiles under their names without the private
     prefix);
   * a private declaration with the name of a public one of a lower level, which the file does not import and in
     a bundle sees, is renamed in its file, with `_private` after its name;
   * a file that uses a name which another file of its level declares (it does not import that file, so the name
     means something else to it) is not put in a bundle with that file; when the other file is of a lower level
     the name is pinned to what it means under the file's own imports (`capture_rewrites.py`);
   * the 56 files that never see all of Mathlib are compiled one to a bundle, with exactly their own imports;
   * a file sees the instances and the simp lemmas of the files that it imports, and no others: each bundle
     writes down what each of its files added (`<name>.views`), and the job of a later bundle says, for each of
     its files, which of those files it does not import; what they added is erased while that file is compiled.
3. Errors. Lean goes on after an error. A theorem whose proof fails stays declared, with `sorry` for its proof,
   and what uses it is checked against its statement; any other command that fails is undone, so what uses it
   fails too and is seen. Each error is matched to the declaration whose lines hold it. The run stops after a
   level where more than a few definitions failed (`--stop-count`, `--stop-percent`): what is built on them
   would fail too.
   A bundle in which one to three files fail is compiled again without them, and each of them in a bundle of
   its own (OUT/alone.json lists the files tried so): a file sees the instances and simp lemmas of its own
   imports only, and whatever else the files before it in a bundle leave in the environment.
4. A chunk whose process dies is cut in two and run again. A chunk whose process stops using the CPU is killed
   and run again on one thread: with proofs on other threads a process can wait for ever on a task that never
   ends (seen once in 130 chunks, always at the same place).

State is OUT/state.jsonl, one line a bundle; running the script again compiles what is not yet in a bundle.
`--retry` compiles again the bundles that had an error (after a repair: `--add NAME` holds more declarations
needed, and their files are compiled at their level first), and those named with `--again`. `--replan` empties
those bundles instead, and puts their files in new ones (after a change to the rules above); the emptied bundle
stays as a module with nothing in it, because the bundles above import it by name. A theorem that
`bundle_check.py` reports with only the three standard axioms rests on no failed proof.

Lean lifts the proofs inside a definition out of it under the names `d._proof_1`, `d._proof_2`, …, uses one again
for the same statement within a module, and the archive names some in its source. Each file of a bundle therefore
starts with none, as it does alone. The first 572 bundles of the build were made before that, their files
sharing lifted proofs, and the terms of the bundles above name what they made: OUT/shared-proofs.json lists
them, and one of them is compiled again in the same way, which keeps those names. `--own-proofs NAME` takes a bundle off the list
(a file names a lifted proof of one of its declarations) and compiles it again; `proof_refs.py` then finds the
bundles above whose terms may name a proof that has another number now. A bundle that is compiled again leaves
what it held before as `<name>.olean.before`, for that comparison.

The same holds for the order of instances. Lean tries two instances that fit a goal equally in the order of
their import, and each file of a bundle is now given the order that its own header gives (`inst_orders`). The
bundles of the first 43 levels were made with the order of the bundles (OUT/bundle-order.json lists them); one
of them that is compiled again without having failed keeps that order, because its statements name the
instances that Lean found then.

A bundle imports every bundle of the lower levels, and an import reads all of a compiled file. So beside each
bundle a copy without the proofs of its theorems is kept, a fifth of the size (`bundle_slim.py`,
`lean/Slim.lean`), and it is those that a bundle imports; `--no-slim` imports the whole files.

Each compile runs under `sandbox-exec` (macOS): no network, no write outside OUT.
"""
import argparse
import importlib.util
import json
import os
import re
import subprocess
import sys
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
SLOW = ("GroundTheory.LocalFields.", "GroundTheory.GlobalFields.")
ERROR = re.compile(r"^(/.*?\.lean):(\d+):(\d+): error(?:\([^)]*\))?: (.*)$")
# The archive's options, and two of this build's: no linters, and ten times the default budget for the search of
# an instance, because a file in a bundle searches among the instances of files that it does not import.
OPTIONS = [["autoImplicit", "bool", "false"], ["relaxedAutoImplicit", "bool", "false"],
           ["maxSynthPendingDepth", "nat", "3"], ["pp.unicode.fun", "bool", "true"],
           ["maxHeartbeats", "nat", "4000000"], ["linter.all", "bool", "false"],
           ["synthInstance.maxHeartbeats", "nat", "200000"]]
SLOW_OPTIONS = [["synthInstance.maxHeartbeats", "nat", "400000"]]


OPEN_IN = re.compile(r"^\s*open\b.*\bin\s*$")
AGAIN = "to compile again (--again, --own-proofs)"
SLIM_NAME = re.compile(r"_slim_\.([^\s'`]+)")
OPEN_PRIVATE = re.compile(r"(?m)^[ \t]*open\s+private\s+(.*?)\s+from\s+(\S+)", re.S)


def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def sandbox_profile(out, readable):
    home = os.path.expanduser("~")
    lines = ["(version 1)", "(allow default)", "(deny network*)", "(deny file-write*)",
             '(allow file-write* (subpath "%s") (literal "/dev/null") (literal "/dev/stdout") (literal "/dev/stderr"))' % out,
             '(deny file-read* (subpath "%s"))' % home]
    seen = set()
    for p in readable:
        lines.append('(allow file-read* (subpath "%s"))' % p)
        d = os.path.dirname(p)
        while d.startswith(home) and d not in seen:
            seen.add(d)
            lines.append('(allow file-read-metadata (literal "%s"))' % d)
            d = os.path.dirname(d)
    return "\n".join(lines) + "\n"


class Build:
    def __init__(self, args):
        self.args = args
        self.out = os.path.abspath(args.out)
        self.src = os.path.abspath(args.src)
        for d in ("olean/B", "job", "log"):
            os.makedirs(os.path.join(self.out, d), exist_ok=True)
        self.dq = dq = load("decl_query")
        self.g = g = dq.Graph(args.map)
        with open(args.scan) as f:
            scan = json.load(f)
        self.mods = scan["modules"]
        self.external = sorted(x for x in scan["external"] if not x.startswith("Mathlib.")) \
            if "Mathlib" in scan["external"] else sorted(scan["external"])
        self.mod_of = [rel[:-5].replace(os.sep, ".") for rel in g.files]
        self.file_of = {m: i for i, m in enumerate(self.mod_of)}
        self.level = [self.mods[m]["level"] for m in self.mod_of]
        self.by_file = defaultdict(list)
        for d in range(g.n):
            self.by_file[g.d_file[d]].append(d)
        # the private names of each file; the public names that some file declares privately; the renames
        self.priv, self.pub_clash, self.rename = defaultdict(set), defaultdict(set), defaultdict(list)
        for d in range(g.n):
            if g.flags[d] & dq.F_PRIVATE and not g.flags[d] & dq.F_LOCAL and g.kinds[d] not in ("syn", "attr", "example"):
                self.priv[g.d_file[d]].update(g.names[d])
        for f, names in list(self.priv.items()):
            for name in names:
                d = g.arch.get(name)
                if d is None:
                    continue
                self.pub_clash[g.d_file[d]].add(name)
                if self.level[g.d_file[d]] < self.level[f]:
                    short = name.rsplit(".", 1)[-1]
                    self.rename[f].append([short, short + "_private"])
        # 134 theorems are declared in two files, word for word (Lean lets two modules hold the same theorem).
        # In a bundle the second is refused if it sees the first: within a level the two files are kept apart, and
        # across levels the one above is left out
        # … unless `dup_names.py` gave the later declaration another name: it is then compiled like any other
        moved = set()
        if args.renames and os.path.exists(args.renames):
            with open(args.renames) as f:
                data = json.load(f)
            for rel, pairs in data["files"].items():
                # the declaration's own name only: another declaration may end in the same component
                self.rename[self.file_of[rel[:-5].replace(os.sep, ".")]].extend([a, b, "decl"] for a, b in pairs)
            moved = {(self.file_of[rel[:-5].replace(os.sep, ".")], old) for rel, old, new in data["decls"]}
        self.skip_more = defaultdict(list)
        twice = defaultdict(list)
        for d in range(g.n):
            if g.kinds[d] in ("theorem", "lemma") and not g.flags[d] & dq.F_PRIVATE:
                for name in g.names[d]:
                    if (g.d_file[d], name) not in moved:
                        twice[name].append(d)
        for name, ds in twice.items():
            if len(ds) < 2:
                continue
            ds.sort(key=lambda d: (self.level[g.d_file[d]], g.files[g.d_file[d]]))
            low = self.level[g.d_file[ds[0]]]
            for d in ds:
                f = g.d_file[d]
                if self.level[f] == low:
                    self.priv[f].add(name)
                else:
                    self.skip_more[f].append([g.d_l0[d], g.d_l1[d]])
        # the files that never see all of Mathlib, with what they import from outside
        self.partial, outside = set(), {}
        for m in sorted(self.mods, key=lambda m: self.mods[m]["level"]):
            names, full = set(), False
            for i in self.mods[m]["imports"]:
                if i in self.mods:
                    if i in outside:
                        names |= outside[i]
                    else:
                        full = True
                elif i == "Mathlib":
                    full = True
                else:
                    names.add(i)
            if not full:
                outside[m] = names
                self.partial.add(self.file_of[m])
        self.exact = set()
        self.sync = set()       # the bundles to compile on one thread, after a hang
        # what each file added to the instances and to the simp set, as the bundles wrote it down; a bit for each
        # such file; and for each file of the archive the bits of the files that it imports, to the end
        self.added, self.bit, self.clo, self.clo_done = {}, {}, {}, 0
        # the key of each instance in Lean's table of instances, the instances of each key with their files,
        # and where each file stands in the build: its bundle, and its place among the bundle's files
        self.inst_key, self.by_key, self.spot, self.key_groups = {}, defaultdict(dict), {}, None
        keys = os.path.join(self.out, "inst-keys.tsv")
        if os.path.exists(keys):
            with open(keys, encoding="utf-8") as f:
                for line in f:
                    n, _, k = line.rstrip("\n").partition("\t")
                    self.inst_key[n] = k
        self.files_at = defaultdict(list)
        for f in range(len(g.files)):
            self.files_at[self.level[f]].append(f)
        # the names to pin to what they mean under the file's own imports (capture_rewrites.py)
        self.overlay = os.path.abspath(args.overlay) if args.overlay and os.path.isdir(args.overlay) else None
        self.rewrite, self.apart = {}, []
        if args.rewrites and os.path.exists(args.rewrites):
            with open(args.rewrites) as f:
                data = json.load(f)
            self.rewrite = {self.file_of[rel[:-5].replace(os.sep, ".")]: [[str(r[0]), str(r[1]), r[2], r[3], r[4]] for r in rows]
                            for rel, rows in data["pins"].items()}
            # what a local notation declares is private too
            if data.get("n") == g.n:
                for a, b in data.get("edges", ()):
                    g.extra.setdefault(a, []).append(b)
            for rel, keys in data["local"].items():
                self.priv[self.file_of[rel[:-5].replace(os.sep, ".")]].update(keys)
            self.apart = [(self.file_of[a[:-5].replace(os.sep, ".")], self.file_of[b[:-5].replace(os.sep, ".")])
                          for a, b in data.get("apart", [])]
        # and the pins written by hand, for a name that the file's own view reads in two ways and Lean chooses
        # between by type (`borel`: Mathlib's, or the one of an opened namespace), which no rule here decides
        if args.pins and os.path.exists(args.pins):
            with open(args.pins) as f:
                for rel, rows in json.load(f).items():
                    self.rewrite.setdefault(self.file_of[rel[:-5].replace(os.sep, ".")], []).extend(
                        [[str(r[0]), str(r[1]), r[2], r[3], r[4]] for r in rows])
        self.hide = {}
        if args.hide and os.path.exists(args.hide):
            with open(args.hide) as f:
                for rel, names in json.load(f).items():
                    self.hide[self.file_of[rel[:-5].replace(os.sep, ".")]] = list(names)
        # a name of one file that the map resolves to a declaration of another file of the same level: the file
        # does not import that one, so the name means something else there, and the two must not share a bundle
        self.avoid = defaultdict(set)
        for d in range(g.n):
            f = g.d_file[d]
            for e in list(g.sig(d)) + list(g.body(d)):
                h = g.d_file[e]
                if h != f and self.level[h] == self.level[f]:
                    self.avoid[f].add(h)
                    self.avoid[h].add(f)
        # and the pairs that capture_rewrites.py found by reading each name with and without the file's own level
        # (the map reads a name against the whole archive, and a file of a higher level may hide such a pair)
        for a, b in self.apart:
            self.avoid[a].add(b)
            self.avoid[b].add(a)
        # the bundles on record: name -> the last line written for it
        self.bundles = {}
        self.stubs = []
        self.state = os.path.join(self.out, "state.jsonl")
        if os.path.exists(self.state):
            with open(self.state) as f:
                for line in f:
                    r = json.loads(line)
                    self.bundles[r["bundle"]] = r
            self.stubs = []
            if args.replan:
                # empty the bundles that had an error: their files are put in new bundles, under today's rules.
                # The bundles above import the old one by name, so it stays, as a module with nothing in it
                for name, r in self.bundles.items():
                    if r["errors"] or not r["ok"]:
                        self.bundles[name] = dict(bundle=name, level=r["level"], files=[], ok=True, errors=[], ms=0,
                                                  undone=0, stub=True)
                        self.stubs.append(name)
                with open(self.state, "w") as f:
                    for r in self.bundles.values():
                        f.write(json.dumps(r) + "\n")
        # the bundles made when a file still used the lifted proofs of the files before it in its bundle: they are
        # compiled again in the same way, so that the names that the bundles above hold stay what they were
        self.share_path = os.path.join(self.out, "shared-proofs.json")
        self.share = set()
        if os.path.exists(self.share_path):
            with open(self.share_path) as f:
                self.share = set(json.load(f))
        self.old_order_path = os.path.join(self.out, "bundle-order.json")
        self.old_order = set()
        if os.path.exists(self.old_order_path):
            with open(self.old_order_path) as f:
                self.old_order = set(json.load(f))
        if args.own_proofs:
            self.share -= set(args.own_proofs)
            if not args.dry_run:
                with open(self.share_path, "w") as f:
                    json.dump(sorted(self.share), f)
        for name in list(args.again) + list(args.own_proofs):
            r = self.bundles.get(name)
            if r is None or not r["files"]:
                raise SystemExit("%s is not a bundle with files" % name)
            if not any(e[3] == AGAIN for e in r["errors"]):
                marked = dict(r, errors=r["errors"] + [[r["files"][0], 1, -1, AGAIN]])
                if args.dry_run:
                    self.bundles[name] = marked
                else:
                    self.record(marked)
        for name, r in self.bundles.items():
            if r["ok"] and r["files"]:
                self.read_views(name)

    def read_views(self, name):
        path = os.path.join(self.out, "olean", "B", name + ".views")
        if not os.path.exists(path):
            return
        for k, f in enumerate(self.bundles[name]["files"]):
            self.spot[f] = (name, k)
        with open(path, encoding="utf-8") as f:
            for line in f:
                r = json.loads(line)
                if r["inst"] or r["simp"]:
                    i = self.file_of[r["m"]]
                    self.added[i] = dict(inst=r["inst"], simp=r["simp"])
                    self.bit.setdefault(i, len(self.bit))
                    # (the bundles made before `Bundle.lean` wrote the keys have them in inst-keys.tsv)
                    for k, n in enumerate(r["inst"]):
                        key = r["keys"][k] if "keys" in r else self.inst_key.get(n)
                        if key:
                            self.by_key[key][n] = i
                            self.key_groups = None

    def inst_orders(self, f):
        """Lean tries two instances that fit a goal equally in the order of their import, the last first. For a
        file alone that is the order of its own header, module after module; in a bundle it is the order of
        the bundles. Where `f` sees instances of one key from two files or more and the two orders differ,
        this gives the instances with the place of each one's file in the file's own order, for `Bundle.lean`
        to put them so (`reorderInst`). 371 keys have two instances or more in the first 43 levels;
        `MeasurableSpace (Matrix _ _ _)` has three, and they are not all the same structure."""
        clo = self.clo.get(f)
        if not clo:
            return []
        if self.key_groups is None:
            self.key_groups = [list(d.items()) for d in self.by_key.values() if len(set(d.values())) > 1]
        out, pos = [], None
        for members in self.key_groups:
            seen = [(n, g) for n, g in members if g in self.bit and (clo >> self.bit[g]) & 1 and g in self.spot]
            files = {g for _, g in seen}
            if len(files) < 2:
                continue
            if pos is None:
                # the order in which Lean imports the modules of `f`: a module after what it imports, the
                # imports of a module in the order of its header
                pos, visited, stack = {}, {f}, [(f, iter(self.imports_of(f)))]
                while stack:
                    node, it = stack[-1]
                    for child in it:
                        if child not in visited:
                            visited.add(child)
                            stack.append((child, iter(self.imports_of(child))))
                            break
                    else:
                        stack.pop()
                        pos[node] = len(pos)
            alone = sorted(files, key=lambda g: pos.get(g, -1))
            if alone != sorted(files, key=lambda g: self.spot[g]):
                rank = {g: k for k, g in enumerate(alone)}
                out.append([[n, str(rank[g])] for n, g in seen])
        return out

    def imports_of(self, f):
        return [self.file_of[i] for i in self.mods[self.mod_of[f]]["imports"] if i in self.file_of]

    def out_of_view(self, f):
        """The files of lower levels that added an instance or a simp lemma and that `f` does not import, as bits."""
        top = self.level[f]
        # a level is computed once, when its first job is made: the bundles of the lower levels are all done then,
        # and the files of one level do not import each other
        for lv in range(self.clo_done + 1, top + 1):
            for x in self.files_at.get(lv, ()):
                c = 0
                for i in self.mods[self.mod_of[x]]["imports"]:
                    j = self.file_of.get(i)
                    if j is not None:
                        c |= self.clo.get(j, 0)
                        b = self.bit.get(j)
                        if b is not None:
                            c |= 1 << b
                self.clo[x] = c
            self.clo_done = lv
        low = 0
        for i, b in self.bit.items():
            if self.level[i] < top:
                low |= 1 << b
        return low & ~self.clo[f]

    def private_opens(self):
        """`open private a b from M` in each file: {file: [(the file of M, [a, b])]}. A private declaration
        is reached by no name from outside its file, so the map has no reference to it: a file that only
        such commands use is needed by nothing, is not compiled, and the command finds no module. Read once
        from the sources and kept beside the scan (`open-private.json`)."""
        g = self.g
        path = os.path.join(os.path.dirname(os.path.abspath(self.args.scan)), "open-private.json")
        if os.path.exists(path):
            with open(path) as f:
                rows = json.load(f)
        else:
            rows = {}
            for rel in g.files:
                with open(os.path.join(self.src, rel), encoding="utf-8", errors="replace") as f:
                    text = f.read()
                if "open private" not in text:
                    continue
                found = [[m.group(2), m.group(1).split()] for m in OPEN_PRIVATE.finditer(text)]
                if found:
                    rows[rel] = found
            with open(path, "w") as f:
                json.dump(rows, f)
        out = {}
        for rel, found in rows.items():
            f = self.file_of.get(rel[:-5].replace(os.sep, "."))
            if f is not None:
                out[f] = [(self.file_of[m], names) for m, names in found if m in self.file_of]
        return out

    def needed_files(self, names):
        """The files to compile for these roots."""
        g = self.g
        if not hasattr(self, "opened"):
            self.opened = self.private_opens()
        if not hasattr(self, "shared"):
            by = defaultdict(list)
            for d in range(g.n):
                if g.kinds[d] in ("syn", "attr", "example", "export") or g.flags[d] & self.dq.F_PRIVATE:
                    continue
                for name in g.names[d]:
                    by[name].append(d)
            self.shared = {name: ds for name, ds in by.items() if len({g.d_file[d] for d in ds}) > 1}
        roots = [g.find(x) for x in names]
        extra = [d for d in range(g.n) if g.kinds[d] == "syn"] + list(g.orphans)
        files = set()
        while True:
            seen = g.closure(roots, "W")
            now = {g.d_file[d] for d in range(g.n) if seen[d]}
            # the global commands that a needed file can see
            reach, stack = set(now), list(now)
            while stack:
                f = stack.pop()
                for imp in self.mods[self.mod_of[f]]["imports"]:
                    i = self.file_of.get(imp)
                    if i is not None and i not in reach:
                        reach.add(i)
                        stack.append(i)
            more = [d for d in extra if not seen[d] and g.d_file[d] in reach]
            # a name that several files declare: the map's reference goes to the first of them, and the file
            # that uses the name may import another. All of them are held needed
            more += [d2 for name, ds in self.shared.items() if any(seen[d] for d in ds)
                     for d2 in ds if not seen[d2]]
            # whole files
            more += [d for f in now - files for d in self.by_file[f] if not seen[d] and g.kinds[d] != "example"]
            # `open private a from M` in a needed file: the declarations `a` of the file of M
            for f in now - files:
                for target, opened in self.opened.get(f, ()):
                    for d in self.by_file[target]:
                        if not seen[d] and any(n == o or n.endswith("." + o) for n in g.names[d] for o in opened):
                            more.append(d)
            files = now
            if not more:
                return files
            roots = roots + more

    def tasks(self):
        """What to run, by level: new chunks for the files in no bundle, and with --retry the bundles with errors."""
        g, args = self.g, self.args
        dq = self.dq
        names = (args.roots or dq.MAIN) + args.add
        files = self.needed_files(names)
        self.n_needed = len(files)
        done = {f for r in self.bundles.values() if r["ok"] for f in r["files"]}
        by_level = defaultdict(list)
        for f in files - done:
            by_level[self.level[f]].append(f)
        serial = defaultdict(int)
        for name in self.bundles:
            lv, k = int(name[1:4]), int(name[5:])
            serial[lv] = max(serial[lv], k + 1)
        out = defaultdict(list)
        if args.retry:
            for name, r in self.bundles.items():
                if r["errors"] or not r["ok"]:
                    out[r["level"]].append((name, r["files"]))
                    if r.get("exact"):
                        self.exact.add(name)
        for lv, fs in by_level.items():
            if args.max_level and lv > args.max_level:
                continue

            def name_of():
                serial[lv] += 1
                return "l%03dn%03d" % (lv, serial[lv] - 1)

            for f in sorted(f for f in fs if f in self.partial):
                name = name_of()
                self.exact.add(name)
                out[lv].append((name, [f]))
            fs = [f for f in fs if f not in self.partial]
            if not fs:
                continue
            total = sum(g.file_lines[f] for f in fs)
            k = max(1, min(-(-total // args.chunk), len(fs)))
            # a level of less than a chunk is one bundle, compiled on one thread while the other processes
            # wait for the next level (the last hundred levels of the archive are such). It is cut in up to
            # `--spread` bundles of fifteen files or more: an import each, and the files in parallel
            k = max(k, min(args.spread, len(fs) // 15))
            chunks = [dict(files=[], load=0, priv=set(), pub=set(), set=set()) for _ in range(k)]
            for f in sorted(fs, key=lambda f: (-g.file_lines[f], g.files[f])):
                mine, shown, away = self.priv.get(f, set()), self.pub_clash.get(f, set()), self.avoid.get(f)
                best = None
                for c in sorted(chunks, key=lambda c: c["load"]):
                    if mine and (c["priv"] & mine or c["pub"] & mine):
                        continue
                    if shown and c["priv"] & shown:
                        continue
                    if away and c["set"] & away:
                        continue
                    best = c
                    break
                if best is None:
                    best = dict(files=[], load=0, priv=set(), pub=set(), set=set())
                    chunks.append(best)
                best["files"].append(f)
                best["set"].add(f)
                best["load"] += g.file_lines[f]
                best["priv"] |= mine
                best["pub"] |= shown
            for c in chunks:
                if c["files"]:
                    out[lv].append((name_of(), sorted(c["files"], key=lambda f: g.files[f])))
        return out

    def job(self, name, level, files):
        g = self.g
        rows = []
        for f in files:
            skip, thm = list(self.skip_more.get(f, [])), []
            for d in self.by_file[f]:
                span = [g.d_l0[d], g.d_l1[d]]
                if g.kinds[d] == "example":
                    skip.append(span)
                elif g.kinds[d] in ("theorem", "lemma"):
                    thm.append(span)
            skip.sort()
            path = os.path.join(self.src, g.files[f])
            if self.overlay:
                # a file whose proof was repaired for the bundles: the same lines, so that the map's line ranges hold
                other = os.path.join(self.overlay, g.files[f])
                if os.path.exists(other):
                    with open(path, encoding="utf-8", errors="replace") as a, \
                            open(other, encoding="utf-8", errors="replace") as b:
                        if a.read().count("\n") != b.read().count("\n"):
                            raise SystemExit("%s has not the lines of the archive's file" % other)
                    path = other
            # `open N in` is read by the parser, which opens `N` for the rest of the command (the notations of
            # `Topology`) before `Bundle.lean` can pin the name on the parsed command: the pin of a namespace
            # in such a line is made in the text, in a copy of the file
            opens = [r for r in self.rewrite.get(f, []) if r[4] == "o"]
            if opens:
                with open(path, encoding="utf-8", errors="replace") as fh:
                    lines = fh.read().split("\n")
                changed = False
                for l0, l1, old, new, _ in opens:
                    rx = re.compile(r"(?<![\w.'])" + re.escape(old) + r"(?![\w.'])")
                    for k in range(int(l0), min(int(l1), len(lines) - 1) + 1):
                        if OPEN_IN.match(lines[k]):
                            fixed = rx.sub(new, lines[k])
                            if fixed != lines[k]:
                                lines[k], changed = fixed, True
                if changed:
                    path = os.path.join(self.out, "overlay-auto", g.files[f])
                    os.makedirs(os.path.dirname(path), exist_ok=True)
                    with open(path, "w", encoding="utf-8") as fh:
                        fh.write("\n".join(lines))
            rows.append(dict(path=path, module=self.mod_of[f], skip=skip, thm=thm,
                             slow=self.mod_of[f].startswith(SLOW), rename=self.rename.get(f, []),
                             rewrite=self.rewrite.get(f, [])))
        if name in self.exact:
            # one file, with what it imports and no more
            where = {f: b for b, r in self.bundles.items() if r["ok"] for f in r["files"]}
            imports = []
            for i in self.mods[self.mod_of[files[0]]]["imports"]:
                if i not in self.mods:
                    imports.append(i)
                elif self.file_of[i] in where:
                    imports.append("B." + where[self.file_of[i]])
        else:
            lower = sorted(b for b, r in self.bundles.items() if r["ok"] and r["level"] < level)
            imports = self.external + ["B." + b for b in lower]
        # a file sees the instances and the simp lemmas of its own imports only: the rest is erased for it
        hidden = [self.out_of_view(f) for f in files]
        union, common = 0, -1
        for h in hidden:
            union |= h
            common &= h
        if not files:
            common = 0
        source = {b: i for i, b in self.bit.items()}
        place, leak = {}, []
        b = 0
        while union >> b:
            if (union >> b) & 1:
                place[b] = len(leak)
                leak.append(self.added[source[b]])
            b += 1
        for row, h in zip(rows, hidden):
            row["erase"] = [place[b] for b in place if (h >> b) & 1 and not (common >> b) & 1]
        # (a bundle made before that, and compiled again for another reason than an error of its own, keeps
        # the order it had: its statements name the instances that Lean found then, and the bundles above were
        # checked against those statements)
        r = self.bundles.get(name)
        keep = name in self.old_order and not (r and any(e[3] != AGAIN for e in r["errors"]))
        for row, f in zip(rows, files):
            order = [] if keep else self.inst_orders(f)
            if order:
                row["instOrder"] = order
        if not keep and name in self.old_order:
            self.old_order.discard(name)
            with open(self.old_order_path, "w") as f:
                json.dump(sorted(self.old_order), f)
        # two instances that a file imports both, for one type and not equal by definition: Lean tries the one
        # imported last first, and in a bundle the order is that of the levels. The instance that the file's
        # own order of imports puts second is taken out of its view, by hand (`--hide`)
        for row, f in zip(rows, files):
            names = self.hide.get(f)
            if names:
                row["erase"] = row["erase"] + [len(leak)]
                leak.append(dict(inst=names, simp=[]))
        job = dict(name="B." + name, olean=os.path.join(self.out, "olean", "B", name + ".olean"),
                   log=os.path.join(self.out, "log", name + ".log"), imports=imports,
                   options=OPTIONS, slowOptions=SLOW_OPTIONS, rollback=True, files=rows,
                   leak=leak, eraseAll=[place[b] for b in place if (common >> b) & 1],
                   views=os.path.join(self.out, "olean", "B", name + ".views"))
        job["async"] = self.args.threads > 1 and name not in self.sync
        job["shareProofs"] = name in self.share
        path = os.path.join(self.out, "job", name + ".json")
        with open(path, "w") as f:
            json.dump(job, f)
        return path, job

    def launch(self, name, level, files):
        path, job = self.job(name, level, files)
        if os.path.exists(job["olean"]) and not os.path.exists(job["olean"] + ".before"):
            # a bundle compiled again: what it held when the bundles above it were checked is kept, for
            # `proof_refs.py` to say which of them name a constant that is no longer the same
            os.replace(job["olean"], job["olean"] + ".before")
        for p in (job["olean"], job["log"]):
            if os.path.exists(p):
                os.remove(p)
        out = open(os.path.join(self.out, "log", name + ".out"), "w")
        cmd = self.prefix + [self.lean, "-j", str(self.args.threads), "--tstack=400000", "--run",
                             os.path.join(HERE, "lean", "Bundle.lean"), path]
        env = self.env_whole if name in self.whole else self.env
        return subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, env=env), job, out

    def collect(self, name, level, files, proc, job, out):
        """Read a finished chunk. None if the process died."""
        g = self.g
        out.close()
        done, per_file = None, {}
        with open(os.path.join(self.out, "log", name + ".out")) as f:
            for line in f:
                if line.startswith("{"):
                    try:
                        r = json.loads(line)
                    except ValueError:
                        continue
                    if "done" in r:
                        done = r
                    elif "m" in r:
                        per_file[r["m"]] = r
        if proc.returncode != 0 or done is None or not os.path.exists(job["olean"]):
            return None
        # a file is compiled from the archive's tree or from a copy (`overlay/`, `overlay-auto/`), and Lean names
        # it in its messages by the path it was given: both are taken. (Until 22 November only the first was,
        # and two errors in copies went unrecorded: their theorems were kept with `sorry`, which the kernel pass
        # of `bundle_replay.py` reported as `sorryAx`.)
        fid = {os.path.join(self.src, g.files[f]): f for f in files}
        for row, f in zip(job["files"], files):
            fid[row["path"]] = f
        errors = []
        if os.path.exists(job["log"]):
            with open(job["log"], errors="replace") as f:
                for line in f:
                    m = ERROR.match(line)
                    if m and m.group(1) in fid:
                        f_id, ln = fid[m.group(1)], int(m.group(2)) - 1
                        hit = [d for d in self.by_file[f_id] if g.d_l0[d] <= ln <= g.d_l1[d]]
                        errors.append([f_id, ln + 1, hit[0] if hit else -1, m.group(4)[:300]])
        return dict(bundle=name, level=level, files=files, ok=True, errors=errors, ms=done["elab_ms"],
                    undone=sum(r.get("undone", 0) for r in per_file.values()), exact=name in self.exact)

    def holder_of(self, name, proof=False):
        """The bundle that holds a constant, or None if it is not found: a declaration of the archive, a
        constant made for one (`d._proof_3`, `d.eq_1`), or a private one (`_private.Module.0.d`). With `proof`,
        None also for a declaration that the map knows as something else than a theorem or an instance."""
        g = self.g
        parts, f = name.split("."), None
        if parts[0] == "_private" and "0" in parts:
            f = self.file_of.get(".".join(parts[1:parts.index("0")]))
        k = len(parts)
        while f is None and k > 0:
            d = g.arch.get(".".join(parts[:k]))
            if d is not None:
                if proof and k == len(parts) and g.kinds[d] not in ("theorem", "lemma", "instance"):
                    return None
                f = g.d_file[d]
            k -= 1
        if f is None or f not in self.spot:
            return None
        return self.spot[f][0]

    def holders(self, theorems):
        """The bundles that hold these theorems, or None if one of them is not found."""
        out = set()
        for name in theorems:
            b = self.holder_of(name)
            if b is None:
                return None
            out.add(b)
        return sorted(out)

    def keep_chain(self, wanted, most=250):
        """Keep the proofs of the theorems that the kernel asked for, and of those it would ask for next. The
        kernel reduces a proof to a constructor, and a proof is as a rule another theorem applied to proofs:
        with one proof kept it stops at the next, a compilation later. `lean/Slim.lean` names the constants at
        the head of each proof that a copy keeps; those that are theorems of the archive are kept too, and so
        on, nearest first, up to `most`. Returns (the theorems newly kept, the bundles whose copies were made
        again), or None if a theorem that the kernel named cannot be placed."""
        if self.holders(wanted) is None:
            return None
        kept, bundles, layer, first = [], set(), sorted(wanted), True
        while layer and len(kept) < most:
            layer = layer[:most - len(kept)]
            new = self.slim.keep_more(self.out, layer)
            # the first time the copies of all that the kernel named are made again, new on the list or not
            look = layer if first else new
            if not look:
                break
            where = sorted({self.holder_of(n) for n in look})
            heads = {}
            self.slim.make(self.out, self.lean, self.prefix, dict(os.environ), where, 1, heads)
            kept += new
            bundles.update(where)
            have = set(self.slim.kept(self.out))
            layer = sorted({h for n in look for h in heads.get(n, [])
                            if h not in have and self.holder_of(h, True) is not None})
            first = False
        return kept, sorted(bundles)

    def make_slim(self):
        """Write the copies without proofs of the bundles that have none, or an older one."""
        if self.slim is None:
            return
        todo = self.slim.stale(self.out)
        if todo:
            t0 = time.time()
            made, small, whole = self.slim.make(self.out, self.lean, self.prefix, dict(os.environ), todo,
                                                min(3, self.args.jobs))
            if made > 20:
                print("   %d copies without proofs in %.0f s: %.1f GB for %.1f GB"
                      % (made, time.time() - t0, small / 1e9, whole / 1e9), flush=True)

    def record(self, r):
        with open(self.state, "a") as f:
            f.write(json.dumps(r) + "\n")
        self.bundles[r["bundle"]] = r

    def write_failed(self):
        g = self.g
        failed = [[g.files[e[0]], e[1], g.name(e[2]) if e[2] >= 0 else "", g.kinds[e[2]] if e[2] >= 0 else "", e[3]]
                  for name in sorted(self.bundles) for e in self.bundles[name]["errors"]]
        with open(os.path.join(self.out, "failed.json"), "w") as f:
            json.dump(failed, f, indent=1, ensure_ascii=False)

    def summary(self):
        """(files in bundles, lines, declarations with an error, of them not theorems)"""
        g = self.g
        files = {f for r in self.bundles.values() if r["ok"] for f in r["files"]}
        bad = {(e[0], e[2]) for r in self.bundles.values() for e in r["errors"]}
        other = sum(1 for _, d in bad if d < 0 or g.kinds[d] not in ("theorem", "lemma"))
        return len(files), sum(g.file_lines[f] for f in files), len(bad), other

    def run(self):
        g, args = self.g, self.args
        tasks = self.tasks()
        n_files = sum(len(fs) for ts in tasks.values() for _, fs in ts)
        n_lines = sum(g.file_lines[f] for ts in tasks.values() for _, fs in ts for f in fs)
        have = self.summary()
        print("needed: %d files; in bundles: %d files, %d lines, %d declarations with an error; to do: %d files, %d "
              "lines, in %d bundles on %d levels" % (self.n_needed, have[0], have[1], have[2], n_files, n_lines,
                                                    sum(len(ts) for ts in tasks.values()), len(tasks)), flush=True)
        if args.dry_run:
            return
        ws = os.path.abspath(args.workspace)
        lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ws, capture_output=True,
                                   text=True, check=True).stdout.strip()
        self.lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                                   check=True).stdout.strip()
        # a bundle imports the copies without proofs of the bundles below it (`bundle_slim.py`). Lean takes a
        # module from the first directory of the path that holds the package and looks no further, so every
        # bundle below must have its copy: they are made when the build starts and after each level
        paths = ([] if args.no_slim else [os.path.join(self.out, "olean-slim")]) + [os.path.join(self.out, "olean")]
        self.env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths + [lean_path]))
        # … but for a bundle whose check needs a proof of a bundle below (the kernel computing a well-founded
        # recursion unfolds the proof that it ends): the copy has `_slim_` there, the kernel says so, and the
        # bundle is compiled again against the whole files, now and whenever it is compiled again
        self.env_whole = dict(os.environ, LEAN_PATH=os.pathsep.join(paths[-1:] + [lean_path]))
        self.alone_path = os.path.join(self.out, "alone.json")
        self.alone = set()
        if os.path.exists(self.alone_path):
            with open(self.alone_path) as f:
                self.alone = set(json.load(f))
        self.slim_tries = {}
        self.whole_path = os.path.join(self.out, "whole-imports.json")
        self.whole = set()
        if os.path.exists(self.whole_path):
            with open(self.whole_path) as f:
                self.whole = set(json.load(f))
        readable = [os.path.expanduser("~/.elan"), os.path.join(ws, ".lake"), self.src, self.out, HERE] + \
                   ([self.overlay] if self.overlay else [])
        profile = os.path.join(self.out, "sandbox.sb")
        with open(profile, "w") as f:
            f.write(sandbox_profile(self.out, readable))
        self.prefix = [] if args.no_sandbox else ["/usr/bin/sandbox-exec", "-f", profile]
        self.slim = None if args.no_slim else load("bundle_slim")
        self.make_slim()
        for name in self.stubs:
            job = dict(name="B." + name, olean=os.path.join(self.out, "olean", "B", name + ".olean"),
                       log=os.path.join(self.out, "log", name + ".log"), imports=[], options=[], slowOptions=[],
                       rollback=False, files=[])
            path = os.path.join(self.out, "job", name + ".json")
            with open(path, "w") as f:
                json.dump(job, f)
            subprocess.run(self.prefix + [self.lean, "--run", os.path.join(HERE, "lean", "Bundle.lean"), path],
                           env=self.env, check=True, stdout=subprocess.DEVNULL)
        t0 = time.time()
        done_lines = 0
        for lv in sorted(tasks):
            queue = list(tasks[lv])
            running = []
            watch = {}      # process -> (CPU time used, when it last grew)
            tick = 0
            while queue or running:
                # the chunks of a level do not depend on each other: keep `jobs` of them running
                while queue and len(running) < args.jobs:
                    name, files = queue.pop(0)
                    running.append((name, files) + self.launch(name, lv, files))
                time.sleep(0.5)
                tick += 1
                if tick % 40 == 0:
                    # with proofs on other threads a process can wait for ever on a task that never ends: it
                    # uses no CPU. It is killed, and its chunk is compiled again on one thread
                    again = set()
                    for name, files, proc, job, out in running:
                        if proc.poll() is not None:
                            continue
                        used = subprocess.run(["ps", "-o", "time=", "-p", str(proc.pid)], capture_output=True,
                                              text=True).stdout.strip()
                        before = watch.get(proc.pid)
                        if before is None or before[0] != used:
                            watch[proc.pid] = (used, time.time())
                        elif time.time() - before[1] > args.hang:
                            proc.kill()
                            proc.wait()
                            if name in self.sync:
                                continue        # hung on one thread too: it is cut in two below, as one that died
                            print("   %s: no CPU used for %d s; killed, to compile again on one thread"
                                  % (name, args.hang), flush=True)
                            out.close()
                            self.sync.add(name)
                            queue.append((name, files))
                            again.add(proc.pid)
                    running = [r for r in running if r[2].pid not in again]
                still = []
                for name, files, proc, job, out in running:
                    if proc.poll() is None:
                        still.append((name, files, proc, job, out))
                        continue
                    r = self.collect(name, lv, files, proc, job, out)
                    if r is not None and name not in self.whole and any("_slim_" in e[3] for e in r["errors"]):
                        # the kernel says which proof it needed: that theorem keeps its proof in the copy of
                        # its bundle from now on, and the bundle is compiled again as it was
                        wanted = sorted({x for e in r["errors"] for x in SLIM_NAME.findall(e[3])})
                        tries = self.slim_tries.get(name, 0)
                        chain = self.keep_chain(wanted) if wanted and tries < 2 and self.slim else None
                        if chain and chain[0]:
                            self.slim_tries[name] = tries + 1
                            print("   %s: the kernel needed the proof of %s; with the proofs that those lead to, "
                                  "%d stay in the copies of %d bundles, and the bundle is compiled again"
                                  % (name, ", ".join(wanted)[:200], len(chain[0]), len(chain[1])), flush=True)
                            queue.append((name, files))
                            continue
                        self.whole.add(name)
                        with open(self.whole_path, "w") as f:
                            json.dump(sorted(self.whole), f)
                        print("   %s: the kernel needed a proof of a bundle below; compiled again against the "
                              "whole files" % name, flush=True)
                        queue.append((name, files))
                        continue
                    # a file that fails in the company of the files before it in its bundle may pass alone:
                    # what a file leaves in the environment for the next is taken out of view for instances
                    # and simp lemmas only (one proof failed after any other file with a proof in it, and
                    # passed after none). So a bundle with one to three failing files is compiled again
                    # without them, and each of them in a bundle of its own, once
                    if r is not None and len(files) > 1 and not args.no_alone:
                        bad = sorted({e[0] for e in r["errors"]})
                        if bad and len(bad) <= 3 and not self.alone.intersection(g.files[f] for f in bad):
                            self.alone.update(g.files[f] for f in bad)
                            with open(self.alone_path, "w") as f:
                                json.dump(sorted(self.alone), f)
                            used = set(self.bundles) | {n for n, _ in queue} | {x[0] for x in running}
                            k = max(int(n[5:]) for n in used if n.startswith("l%03dn" % lv)) + 1
                            print("   %s: %s failed; the bundle is compiled again without, and the file alone"
                                  % (name, ", ".join(os.path.basename(g.files[f]) for f in bad)), flush=True)
                            queue.append((name, [f for f in files if f not in bad]))
                            for f in bad:
                                queue.append(("l%03dn%03d" % (lv, k), [f]))
                                k += 1
                            continue
                    if r is None:
                        if len(files) == 1:
                            self.record(dict(bundle=name, level=lv, files=files, ok=False, ms=0, undone=0,
                                             errors=[[files[0], 1, -1, "the process died"]]))
                            print("   %s: the process died on %s" % (name, g.files[files[0]]), flush=True)
                        else:
                            half = len(files) // 2
                            used = set(self.bundles) | {n for n, _ in queue} | {x[0] for x in running}
                            k = max(int(n[5:]) for n in used if n.startswith("l%03dn" % lv)) + 1
                            queue.append(("l%03dn%03d" % (lv, k), files[:half]))
                            queue.append(("l%03dn%03d" % (lv, k + 1), files[half:]))
                            print("   %s: the process died; cut in two" % name, flush=True)
                        continue
                    self.record(r)
                    self.read_views(name)
                    done_lines += sum(g.file_lines[f] for f in files)
                    for f_id, ln, d, msg in r["errors"][:args.show]:
                        print("   ERROR %s:%d (%s): %s" % (g.files[f_id], ln, g.name(d) if d >= 0 else "-", msg[:150]),
                              flush=True)
                running = still
            # a definition that fails is undone, and everything that uses it fails after it: past a few of
            # them a level is not worth building on, and the run stops for a repair
            here = [r for r in self.bundles.values() if r["level"] == lv]
            n_here = sum(len(r["files"]) for r in here)
            bad_here = len({(e[0], e[2]) for r in here for e in r["errors"]
                            if e[2] < 0 or g.kinds[e[2]] not in ("theorem", "lemma")})
            el = time.time() - t0
            s = self.summary()
            print("level %d: %d bundles; in all %d files, %d declarations with an error (%d not theorems); %d of %d "
                  "lines; %.0f s; %.0f lines/s" % (lv, len(tasks[lv]), s[0], s[2], s[3], done_lines, n_lines, el,
                                                   done_lines / max(el, 1)), flush=True)
            self.write_failed()
            # the next level imports this one: its copies without proofs are made now
            self.make_slim()
            if bad_here > max(args.stop_count, args.stop_percent * n_here / 100.0):
                print("stopped after level %d: %d of its declarations that are not theorems failed, in %d files. "
                      "Repair them (failed.json), then run with --retry." % (lv, bad_here, n_here), flush=True)
                break
        self.write_failed()
        s = self.summary()
        print("done: %d files in bundles, %d lines; %d declarations with an error (%d not theorems); see failed.json"
              % s)


def main():
    ap = argparse.ArgumentParser()
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap.add_argument("--out", required=True)
    ap.add_argument("--src", default=os.path.join(ext, "extract", "lean", "src"))
    ap.add_argument("--map", default=os.path.join(ext, "declmap"))
    ap.add_argument("--scan", default=os.path.join(ext, "scan.json"))
    ap.add_argument("--workspace", default=os.path.join(ext, "native-ws"))
    ap.add_argument("--rewrites", default=os.path.join(ext, "rewrites.json"), help="the output of capture_rewrites.py")
    ap.add_argument("--renames", default=os.path.join(ext, "dup-renames.json"), help="the output of dup_names.py")
    ap.add_argument("--pins", default=os.path.join(ext, "pins-manual.json"),
                    help="more pins, written by hand: {file: [[first line, last line, name, _root_.constant, 'n']]}")
    ap.add_argument("--hide", default=os.path.join(ext, "hide-manual.json"),
                    help="instances to take out of a file's view, written by hand: {file: [instance, …]}")
    ap.add_argument("--overlay", default=os.path.join(ext, "overlay"),
                    help="a tree of files to compile in place of the archive's (proofs repaired for the bundles)")
    ap.add_argument("--roots", nargs="*", default=[])
    ap.add_argument("--add", nargs="*", default=[], help="more declarations to hold needed (a repair)")
    ap.add_argument("--jobs", type=int, default=5, help="processes at a time; each needs 3 to 4 GB")
    ap.add_argument("--threads", type=int, default=3, help="threads of a process for proofs and the kernel; 1 for none")
    ap.add_argument("--chunk", type=int, default=12000, help="lines of source to a chunk, about")
    ap.add_argument("--spread", type=int, default=3, help="bundles to make at least of a level, if it has the files")
    ap.add_argument("--max-level", type=int, default=0, help="stop after this level of the import graph")
    ap.add_argument("--retry", action="store_true", help="compile again the bundles that had an error")
    ap.add_argument("--replan", action="store_true", help="forget the bundles that had an error, and bundle their files anew")
    ap.add_argument("--again", nargs="*", default=[], help="bundles to compile again with --retry, error or not")
    ap.add_argument("--own-proofs", nargs="*", default=[],
                    help="the same, and from now on each of their files names its lifted proofs as it does alone "
                         "(takes them out of OUT/shared-proofs.json; then see proof_refs.py)")
    ap.add_argument("--no-sandbox", action="store_true")
    ap.add_argument("--no-alone", action="store_true",
                    help="do not compile a failing file again in a bundle of its own")
    ap.add_argument("--no-slim", action="store_true",
                    help="import the whole files of the bundles below, not the copies without proofs")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--show", type=int, default=4)
    ap.add_argument("--hang", type=int, default=150, help="seconds without CPU after which a process is taken for hung")
    ap.add_argument("--stop-count", type=int, default=25, help="stop after a level with more failed non-theorems than this …")
    ap.add_argument("--stop-percent", type=float, default=1.0, help="… and than this share of its files, in percent")
    Build(ap.parse_args()).run()


if __name__ == "__main__":
    main()
