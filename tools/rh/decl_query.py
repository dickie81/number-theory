#!/usr/bin/env python3
"""Questions about the map that `decl_map.py` wrote: what a declaration reaches, and why.

    python3 -I tools/rh/decl_query.py MAP_DIR summary [ROOT ...]
    python3 -I tools/rh/decl_query.py MAP_DIR explain NAME
    python3 -I tools/rh/decl_query.py MAP_DIR inputs NAME
    python3 -I tools/rh/decl_query.py MAP_DIR path FROM TO
    python3 -I tools/rh/decl_query.py MAP_DIR write RULE OUT.json [ROOT ...]

The roots default to the five theorems of the archive's `Main`. The rules, each adding to the one before:

* `L`: the constants that a declaration names;
* `M`: also fields (`h.foo` reaches `N.foo` for every reached or Mathlib `N`, and `O.N.foo`, which a file that
  opens `O` reads the same way), the instances whose signature is reached (an abbreviation in it counts as
  what it stands for), and the `attribute` commands whose names are reached;
* `W`: also the lemmas that tactics find by attribute (`simp`, `ext`, `fun_prop`, ...) whose statement is reached.

`S` is the rule `M` on statements only: the proof of a theorem is not followed. It is what must exist for a
theorem to be stated. All of this is read from text (see `decl_map.py`), so it is an estimate.
"""
import json
import os
import pickle
import sys
from collections import Counter, defaultdict, deque

F_PRIVATE, F_LOCAL, F_SCOPED, F_WEAK, F_ROOT, F_PROTECTED = 1, 2, 4, 8, 16, 32
MAIN = ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
        "LFunction_eq_zero_re_of_isPrimitive"]


class Graph:
    def __init__(self, d):
        with open(os.path.join(d, "graph.pkl"), "rb") as f:
            g = pickle.load(f)
        self.__dict__.update(g)
        with open(os.path.join(d, "mathnames.pkl"), "rb") as f:
            math = pickle.load(f)
        self.n = n = len(self.names)
        # references that the map does not have: what a name means in its file's own view where the whole
        # archive gives another declaration (`capture_rewrites.py`, `edges`); `bundle_build.py` fills it
        self.extra = {}
        self.is_thm = bytearray(1 if k in ("theorem", "lemma") else 0 for k in self.kinds)
        # N.foo, for field notation: the declarations by last component, with the declaration (or Mathlib) N
        self.by_field = defaultdict(list)
        self.by_ns = defaultdict(list)
        fid = self.field_id
        for d_id, names in enumerate(self.names):
            if self.kinds[d_id] in ("syn", "attr"):
                continue
            for name in names:
                if "." not in name:
                    continue
                ns, last = name.rsplit(".", 1)
                f = fid.get(last)
                if f is None:
                    continue
                owner = self.arch.get(ns)
                if owner is None and ns not in math:
                    # `theorem UpperTheory.HF.Formalism.HC.HostAx.splitsC_facts` is a field of the structure
                    # `Formalism.HC.HostAx` for a file that opens `UpperTheory.HF`: Lean looks `S.f` up through
                    # the open namespaces. So `N` may be the end of the namespace too
                    parts = ns.split(".")
                    for k in range(1, len(parts)):
                        tail = ".".join(parts[k:])
                        owner = self.arch.get(tail)
                        if owner is not None or tail in math:
                            break
                    else:
                        continue
                if owner is None:
                    owner = -1
                self.by_field[f].append((d_id, owner))
                if owner >= 0:
                    self.by_ns[owner].append((f, d_id))
        # what waits for its signature to be reached
        self.watch_inst = defaultdict(list)
        self.watch_weak = defaultdict(list)
        self.needs = {}
        self.orphans = []
        for d_id in range(n):
            kind, fl = self.kinds[d_id], self.flags[d_id]
            inst = (kind == "instance" and not fl & F_LOCAL) or kind == "attr"
            weak = fl & F_WEAK and kind not in ("instance", "attr")
            if not (inst or weak):
                continue
            need = set(self.sig(d_id))
            if inst:
                # an abbreviation in the signature of an instance is not a name that the goal has to hold:
                # Lean unfolds it when it files the instance, so `instance : GrpObj (bcObj a A)`, where
                # `abbrev bcObj a A := (Over.pullback (spMap a)).obj A`, answers a goal that names
                # `Over.pullback` and `spMap` only. Its place is taken by what it stands for
                done, stack, need = set(), list(need), set()
                while stack:
                    x = stack.pop()
                    if x in done:
                        continue
                    done.add(x)
                    if x != d_id and (self.kinds[x] == "abbrev" or "reducible" in self.d_attrs[x]):
                        stack.extend(self.sig(x))
                        stack.extend(self.body_e[self.body_o[x]:self.body_o[x + 1]])
                    else:
                        need.add(x)
            if not need:
                self.orphans.append(d_id)
                continue
            self.needs[d_id] = len(need)
            table = self.watch_inst if inst else self.watch_weak
            for x in need:
                table[x].append(d_id)

    def sig(self, d):
        return self.sig_e[self.sig_o[d]:self.sig_o[d + 1]]

    def body(self, d):
        base = self.body_e[self.body_o[d]:self.body_o[d + 1]]
        more = self.extra.get(d) if self.extra else None
        return list(base) + more if more else base

    def name(self, d):
        return self.names[d][0] if self.names[d] else "<%s %s:%d>" % (self.kinds[d], self.files[self.d_file[d]],
                                                                       self.d_l0[d] + 1)

    def find(self, name):
        d = self.arch.get(name)
        if d is None:
            hits = [i for i, ns in enumerate(self.names) if name in ns]
            if not hits:
                raise SystemExit("no declaration named " + name)
            d = hits[0]
        return d

    def closure(self, roots, rule="M", parents=None):
        """The declarations that the roots reach, as a bytearray."""
        fields = rule in ("M", "W", "S")
        inst = rule in ("M", "W", "S")
        weak = rule == "W"
        stmt = rule == "S"
        seen = bytearray(self.n)
        left = dict(self.needs) if inst else {}
        active = set()
        queue = deque()

        def add(d, parent):
            if not seen[d]:
                seen[d] = 1
                queue.append(d)
                if parents is not None:
                    parents[d] = parent

        for r in roots:
            add(r, -1)
        while queue:
            d = queue.popleft()
            proof = not (stmt and self.is_thm[d])
            for e in self.sig(d):
                add(e, d)
            if proof:
                for e in self.body(d):
                    add(e, d)
            if inst:
                for w in self.watch_inst.get(d, ()):
                    left[w] -= 1
                    if left[w] == 0:
                        add(w, d)
            if weak:
                for w in self.watch_weak.get(d, ()):
                    left[w] -= 1
                    if left[w] == 0:
                        add(w, d)
            if fields:
                fs = list(self.sig_f[d])
                if proof:
                    fs.extend(self.body_f[d])
                for f in fs:
                    if f not in active:
                        active.add(f)
                        for c, owner in self.by_field.get(f, ()):
                            if owner < 0 or seen[owner]:
                                add(c, d)
                for f, c in self.by_ns.get(d, ()):
                    if f in active:
                        add(c, d)
        return seen

    def measure(self, seen):
        decls = sum(seen)
        files = set()
        lines = 0
        kinds = Counter()
        tops = Counter()
        for d in range(self.n):
            if seen[d]:
                files.add(self.d_file[d])
                lines += self.d_lines[d]
                kinds[self.kinds[d]] += 1
                tops[".".join(self.files[self.d_file[d]].split(os.sep)[:2])] += self.d_lines[d]
        return dict(declarations=decls, files=len(files), lines=lines, file_lines=sum(self.file_lines[f] for f in files),
                    kinds=kinds.most_common(), tops=tops.most_common(12))

    def file_closure(self, seen):
        """Close under whole files: every declaration of a file that holds a reached one, and what those reach."""
        by_file = defaultdict(list)
        for d in range(self.n):
            by_file[self.d_file[d]].append(d)
        seen = bytearray(seen)
        done = set()
        while True:
            files = {self.d_file[d] for d in range(self.n) if seen[d]} - done
            if not files:
                return seen
            done |= files
            roots = [d for f in files for d in by_file[f] if self.kinds[d] != "example"]
            more = self.closure(roots + [d for d in range(self.n) if seen[d]], "M")
            seen = more


def show(label, m, total):
    print("%-34s %8d decls  %7d files  %9d lines  (%4.1f%% of the archive's lines; the files hold %d)"
          % (label, m["declarations"], m["files"], m["lines"], 100.0 * m["lines"] / total, m["file_lines"]))


def main():
    d, cmd, args = sys.argv[1], sys.argv[2], sys.argv[3:]
    g = Graph(d)
    total = sum(g.file_lines)
    if cmd == "summary":
        roots = [g.find(x) for x in (args or MAIN)]
        print("%d declarations in %d files, %d lines; %d instances and attribute commands name no archive constant"
              % (g.n, len(g.files), total, len(g.orphans)))
        out = {}
        for rule in ("S", "L", "M", "W"):
            seen = g.closure(roots, rule)
            m = out[rule] = g.measure(seen)
            show("rule " + rule, m, total)
        seen = g.closure(roots, "M")
        m = out["M, whole files"] = g.measure(g.file_closure(seen))
        show("rule M, whole files", m, total)
        print("rule M by kind:", out["M"]["kinds"])
        print("rule M by directory (lines):")
        for k, v in out["M"]["tops"]:
            print("   %-55s %9d" % (k, v))
        with open(os.path.join(d, "summary.json"), "w") as f:
            json.dump(out, f, indent=1)
    elif cmd == "explain":
        x = g.find(args[0])
        inv = {v: k for k, v in g.field_id.items()}
        print(g.kinds[x], g.names[x], g.files[g.d_file[x]], "lines %d-%d" % (g.d_l0[x] + 1, g.d_l1[x] + 1),
              "flags", g.flags[x], "attrs", g.d_attrs[x])
        print(" signature:", [g.name(e) for e in g.sig(x)])
        print(" body:", [g.name(e) for e in g.body(x)])
        print(" fields:", [inv[f] for f in g.sig_f[x]], [inv[f] for f in g.body_f[x]])
    elif cmd == "inputs":
        x = g.find(args[0])
        rule = args[1] if len(args) > 1 else "M"
        rows = []
        for e in list(g.sig(x)) + list(g.body(x)):
            m = g.measure(g.closure([e], rule))
            rows.append((m["lines"], m["declarations"], m["files"], g.kinds[e], g.name(e)))
        for lines, decls, files, kind, name in sorted(rows, reverse=True):
            print("%9d lines %8d decls %7d files  %-9s %s" % (lines, decls, files, kind, name))
    elif cmd == "path":
        a, b = g.find(args[0]), g.find(args[1])
        parents = {}
        g.closure([a], args[2] if len(args) > 2 else "M", parents)
        if b not in parents:
            print("not reached")
            return
        chain = []
        while b != -1:
            chain.append(b)
            b = parents[b]
        for x in reversed(chain):
            print("  %-9s %s   (%s)" % (g.kinds[x], g.name(x), g.files[g.d_file[x]]))
    elif cmd == "write":
        rule, out = args[0], args[1]
        roots = [g.find(x) for x in (args[2:] or MAIN)]
        seen = g.closure(roots, rule[0])
        if rule.endswith("F"):
            seen = g.file_closure(seen)
        by_file = defaultdict(list)
        for x in range(g.n):
            if seen[x]:
                by_file[g.files[g.d_file[x]]].append([g.d_l0[x], g.d_l1[x], g.kinds[x], g.name(x)])
        with open(out, "w") as f:
            json.dump(by_file, f)
        print("wrote %d files, %d declarations" % (len(by_file), sum(seen)))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
