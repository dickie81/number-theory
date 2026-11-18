#!/usr/bin/env python3
"""The dead-code check before a commit: from the sources and what is already built, in seconds, with no build.

    python3 scripts/dead_code_fast.py                    # the working tree: every finding
    python3 scripts/dead_code_fast.py --staged           # what `git commit` would record
    python3 scripts/dead_code_fast.py --rev REV          # a commit
    python3 scripts/dead_code_fast.py --against REV      # only the findings that REV does not have
    python3 scripts/dead_code_fast.py --why NAME         # a chain of uses from a root to NAME
    python3 scripts/dead_code_fast.py --sources          # read no build: the sources alone
    python3 scripts/dead_code_fast.py --json OUT         # also write the findings to OUT

`scripts/dead_code.py` is the check that CI runs: it walks the proofs, so it needs the whole library built, the
certificates included, and its verdict comes at the end of that build. This script answers the same question early
and approximately. `.githooks/pre-commit` runs it, as `--staged --against HEAD`, on a commit or a merge that changes
a Lean file (`scripts/install_hooks.sh` installs the hooks; `DEAD_CODE_HOOK=warn git commit …` reports and commits).

What it reads, for each module of lib/core, lib/pnt, lib/dh, lib/zeta23 and lib/check:

* its `.ilean` file in `.lake/build`, if the module's source is the one that file was built from (the hash of the
  source in Lake's `.trace` file is compared): the names that each declaration's source cites, as Lean resolved them.
  These uses are exact;
* otherwise its source: comments and strings removed, split into commands, each declaration linked to every
  declaration of its import cone whose last name component is a component of an identifier in its text (as
  `scripts/decl_reach.py` does). These uses are an over-approximation, so a module read this way hides dead code
  and never invents any.
  The certificates' part files, which few machines have built, are read this way; they cite four names each.

The roots are the theorems that the check files print, as in `scripts/dead_code.py`, and what Lean can use without
naming it: instances, declarations with an attribute other than those of `BENIGN` (a `simp` lemma, say), the
declarations of the meta level, and whatever a `variable`, an `attribute`, a notation, a macro or an unknown command
cites. `#print`, `#check` and `example` use nothing.

It fails on:

1. a theorem, definition, structure or inductive type that no root reaches, or a module that no check file imports;
2. a printed theorem that no other declaration uses and that is neither printed by Check.lean, nor on the page on
   the zeros, nor named in formalisations/ (a result that nothing uses must be registered there);
3. a name of a section "Conditional results" of formalisations/ that no check file prints, or a printed name that no
   module declares.

What it cannot see, and `scripts/dead_code.py` can: an unused instance or `simp` lemma (they are roots here), a
declaration used only inside one of those, the closed hypotheses of a root, and a use that Lean makes without the
source naming it in a declaration with no attribute. For the last one the hook can be passed by with
`DEAD_CODE_HOOK=warn`; `--why NAME` shows what this script takes for a use.

The summaries of the sources and of the `.ilean` files are kept in `.git/dead-code-fast.pickle`, by content: a
second run reads only what changed.
"""
import bisect
import collections
import json
import os
import pickle
import re
import struct
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIRS = ["core", "pnt", "dh", "zeta23", "check"]
CHECKS = ["Check", "CheckAll", "CheckDH", "CheckZeta23"]
VERSION = 2
BUILD = os.path.join(".lake", "build", "lib", "lean")
# a source larger than this that is mostly long numerals (a certificate's part file) is not hashed for Lake's
# trace: it is read as text, which is cheap and, for such a file, as good
BIG = 1 << 16

DECLS = {"theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive", "opaque", "axiom",
         "irreducible_def"}
MODIFIERS = {"private", "protected", "noncomputable", "unsafe", "partial", "nonrec", "scoped", "local", "public",
             "meta"}
# commands whose text uses nothing
SILENT = {"namespace", "section", "end", "open", "export", "universe", "set_option", "import", "include", "omit",
          "unseal", "seal", "suppress_compilation", "module", "prelude", "mutual", "example", "assert_not_exists"}
# commands that are not declarations and whose text may put a declaration to use
CITING = {"variable", "attribute", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "macro",
          "macro_rules", "syntax", "elab", "elab_rules", "declare_syntax_cat", "initialize", "builtin_initialize",
          "deriving", "alias", "run_cmd", "run_meta", "register_simp_attr", "add_decl_doc", "library_note",
          "binder_predicate", "unif_hint", "compile_inductive"}
# of those, the ones that Lean elaborates where they stand, so that a module's `.ilean` records what they cite; the
# others (a notation, a macro, a command that the library defines) quote their text, and are read as text
ELABORATED = {"variable", "attribute", "deriving", "alias", "add_decl_doc"}
STARTERS = DECLS | MODIFIERS | SILENT | CITING
# a line at column 0 that goes on with the command before it
CONTINUES = {"termination_by", "decreasing_by", "where", "with", "from", "then", "else", "at", "using", "in"}
# attributes that give Lean no way to use a declaration that the sources do not name
BENIGN = {"inline", "noinline", "always_inline", "macro_inline", "reducible", "irreducible", "semireducible",
          "specialize", "nospecialize", "inherit_doc", "deprecated", "nolint", "expose", "no_expose",
          "implemented_by", "never_extract", "pp_nodot", "pp_using_anonymous_constructor", "match_pattern",
          "elab_as_elim", "blueprint"}
META = re.compile(r"\b(?:Lean\.\w|MacroM|CommandElabM|TermElabM|TacticM|MetaM|CoreM|AttrM|TSyntax|Syntax\b|Macro\b"
                  r"|ParserDescr|Unexpander|Delab\b|Environment\b|MessageData|Elab\.\w)")

COMP = r"(?:«[^»\n]*»|[^\W\d][\w'₀-₉ₐ-ₜ]*)"
IDENT = re.compile(COMP + r"(?:\." + COMP + r")*")
SKIP = re.compile(r'/-|--|"')
BLOCK = re.compile(r"/-|-/")
STRING_END = re.compile(r'(?:\\.|[^"\\])*"', re.S)
LITERAL = re.compile(r"\b(?:0x[0-9a-fA-F]{48,}|\d{48,})\b")
FIRST = re.compile(r"@\[|#\w+|[^\W\d][\w']*")
NAME = r"`([A-Za-z_][\w.']*\.[\w.']+)`"

M64 = (1 << 64) - 1
MUL = 0xc6a4a7935bd1e995


def lake_hash(data):
    """Lake's hash of a text file, as its `.trace` files record it: Lean's hash of the bytes (MurmurHash64A, seed
    11), mixed into the hash of nothing (1723)."""
    data = data.replace(b"\r\n", b"\n")
    n = len(data)
    h = (11 ^ (n * MUL)) & M64
    full = n - n % 8
    for (k,) in struct.iter_unpack("<Q", data[:full]):
        k = (k * MUL) & M64
        k ^= k >> 47
        h = ((h ^ ((k * MUL) & M64)) * MUL) & M64
    if n % 8:
        h = ((h ^ int.from_bytes(data[full:], "little")) * MUL) & M64
    h ^= h >> 47
    h = (h * MUL) & M64
    h ^= h >> 47
    k = (h * MUL) & M64
    k ^= k >> 47
    k ^= MUL
    return format(((1723 ^ k) * MUL) & M64, "016x")


def strip(text):
    """The text with its comments and strings blanked, line for line."""
    out, pos, n = [], 0, len(text)
    while True:
        m = SKIP.search(text, pos)
        if not m:
            out.append(text[pos:])
            return "".join(out)
        i = m.start()
        out.append(text[pos:i])
        if m.group() == "--":
            j = text.find("\n", i)
            pos = n if j < 0 else j
        elif m.group() == "/-":
            depth, j = 1, i + 2
            while depth:
                b = BLOCK.search(text, j)
                if not b:
                    j = n
                    break
                depth += 1 if b.group() == "/-" else -1
                j = b.end()
            out.append("\n" * text.count("\n", i, j))
            pos = j
        elif i and text[i - 1] == "'" and text[i + 1:i + 2] == "'":   # the character '"'
            out.append(" ")
            pos = i + 1
        else:
            e = STRING_END.match(text, i + 1)
            j = e.end() if e else n
            out.append(' "" ' + "\n" * text.count("\n", i, j))
            pos = j


def components(text):
    """The components of the identifiers of a text: a name may be any prefix of an identifier (`foo.symm`)."""
    out = set()
    for t in IDENT.findall(text):
        out.update(t.split(".")) if "«" not in t else out.add(t)
    return out


def last(name):
    return name.rsplit(".", 1)[-1].rstrip("!?")


def summarise(data):
    """A source's commands: for each, its kind (`decl`, `cite`, `quote` or `skip`), its first and last lines, and
    for a declaration its keyword, its name with its namespaces, the line of its name and whether it is a root
    (`R`) or of the meta level (`M`); and the components of the identifiers of its text. With the module's imports,
    the names it prints, and Lake's hash of the source."""
    text = LITERAL.sub("0", data.decode("utf-8", "replace"))
    data_file = len(data) > BIG and 2 * len(text) < len(data)
    text = strip(text)
    lines = text.split("\n")
    # the commands, by the lines at column 0 that begin one
    cmds, cur = [], None
    for no, line in enumerate(lines, 1):
        if line[:1].strip():
            f = FIRST.match(line)
            first = f.group() if f else ""
            head_only = cur is not None and HEAD_ONLY.fullmatch(" ".join(lines[cur[0] - 1:no - 1])) is not None
            starts = (first == "@[" or first.startswith("#") or first in STARTERS
                      or (f is not None and first not in CONTINUES))
            if starts and not head_only:
                cur = [no, no]
                cmds.append(cur)
                continue
        if cur is not None:
            cur[1] = no
    out, scopes = [], []
    for start, stop in cmds:
        body = "\n".join(lines[start - 1:stop])
        out.append(command(body, start, stop, scopes))
    return {"v": VERSION,
            "imports": re.findall(r"^import\s+(?:all\s+)?(\S+)", text, re.M),
            "prints": re.findall(r"^#print axioms (\S+)", text, re.M),
            "cmds": out,
            "lake": None if data_file else lake_hash(data)}


ATTR = r"@\[(?:[^\[\]]|\[[^\[\]]*\])*\]"
HEAD_ONLY = re.compile(r"\s*(?:(?:" + ATTR + r"|" + "|".join(sorted(MODIFIERS)) + r")\s*)+")
PREFIX = re.compile(r"\s*(?P<attrs>(?:" + ATTR + r"\s*)*)(?P<mods>(?:(?:" + "|".join(sorted(MODIFIERS)) + r")\s+)*)"
                    r"(?P<kw>#?[^\W\d][\w']*)?")
IN = re.compile(r"(?:open|set_option|omit|include|attribute|variable|universe)\b[^\n]*?\bin\b[ \t]*(?=\S)")
DECLNAME = re.compile(r"\s*(?:\(\s*priority[^)]*\)\s*)?(?P<name>[^\s:({\[⦃]+)?")


def command(body, start, stop, scopes):
    """One command, classified; `scopes` is the stack of the namespaces and sections around it, which it may change."""
    # `open X in theorem …`: the command is the one after `in`
    rest = body
    while True:
        m = IN.match(rest)
        if not m:
            break
        rest = rest[m.end():]
    m = PREFIX.match(rest)
    kw = (m.group("kw") or "") if m else ""
    attrs = m.group("attrs") if m else ""
    after = rest[m.end():] if m else rest
    if kw == "noncomputable" or (kw == "section" and "noncomputable" in (m.group("mods") if m else "")):
        kw = "section"
    if kw == "namespace":
        name = after.split()[0] if after.split() else ""
        scopes.append(("ns", name))
        return ("skip", start, stop)
    if kw == "section":
        scopes.append(("sec", ""))
        return ("skip", start, stop)
    if kw == "mutual":
        scopes.append(("mutual", ""))
        return ("skip", start, stop)
    if kw == "end":
        if scopes:
            scopes.pop()
        return ("skip", start, stop)
    if kw.startswith("#") or kw in SILENT:
        return ("skip", start, stop)
    comps = tuple(sorted(components(body)))
    if kw in DECLS:
        n = DECLNAME.match(after)
        name = (n.group("name") or "") if n else ""
        name = re.sub(r"\.\{.*", "", name)
        if name and IDENT.fullmatch(name):
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join([s for kind, s in scopes if kind == "ns" and s] + [name])
            line = start + body[:len(body) - len(after)].count("\n") if after else start
            head = rest.split(":=", 1)[0]
            flags = ""
            if kw == "instance" or any(a not in BENIGN for a in attributes(attrs)):
                flags += "R"
            if META.search(head):
                flags += "M"
            return ("decl", start, stop, kw, full, line, flags, comps)
        # an instance without a name: a root, and what it cites is used
        return ("cite", start, stop, comps)
    return ("cite" if kw in ELABORATED else "quote", start, stop, comps)


def attributes(attrs):
    """The names of the attributes of `@[a, b c, local d]`."""
    out = []
    for block in re.findall(ATTR, attrs):
        for part in block[2:-1].split(","):
            words = [w for w in part.split() if w not in ("local", "scoped")]
            if words:
                out.append(re.match(r"[\w.']*", words[0]).group())
    return out


def ilean(path, ours):
    """A module's `.ilean`: its declarations with the lines of their names, and the constants of the library that
    its source cites, each with the line of the citation."""
    d = json.load(open(path, encoding="utf-8"))
    decls = {user(n): r[4] + 1 for n, r in d.get("decls", {}).items() if len(r) >= 5}
    uses = []
    for key, info in d.get("references", {}).items():
        c = json.loads(key).get("c")
        if not c or c.get("m") not in ours:
            continue
        for u in info.get("usages", ()):
            uses.append((u[0] + 1, c["m"], user(c["n"])))
    return {"v": VERSION, "decls": decls, "uses": uses}


def user(name):
    """A name as the sources write it: a private name without its prefix."""
    m = re.match(r"_private\.(?:.*?)\.0\.(.*)", name)
    return m.group(1) if m else name


def git(*args):
    r = subprocess.run(["git", *args], cwd=ROOT, capture_output=True)
    if r.returncode:
        raise RuntimeError(f"git {' '.join(args)} failed:\n{r.stderr.decode()[-2000:]}")
    return r.stdout


class Tree:
    """One version of the repository: the blob of each file of lib/ and formalisations/, and its contents. `rev`
    is a commit, `:` for the index, or None for the working tree."""

    def __init__(self, rev):
        self.rev, self.blobs, self.disk, self.cat = rev, {}, set(), None
        if rev in (None, ":"):
            for e in git("ls-files", "-s", "-z", "--", "lib", "formalisations").split(b"\0"):
                if e:
                    meta, path = e.split(b"\t", 1)
                    self.blobs[path.decode()] = meta.split()[1].decode()
            dirty = {p.decode() for p in git("diff", "--name-only", "-z", "--", "lib", "formalisations").split(b"\0")
                     if p}
            # the files whose working copy is the index's
            self.disk = {p for p in self.blobs if p not in dirty and os.path.exists(os.path.join(ROOT, p))}
            if rev is None:
                new = git("ls-files", "-o", "--exclude-standard", "-z", "--", "lib", "formalisations").split(b"\0")
                for p in sorted(dirty | {p.decode() for p in new if p}):
                    full = os.path.join(ROOT, p)
                    if os.path.exists(full):
                        self.blobs[p] = git("hash-object", "--", p).decode().strip()
                        self.disk.add(p)
                    else:
                        self.blobs.pop(p, None)
        else:
            for e in git("ls-tree", "-r", "-z", rev, "--", "lib", "formalisations").split(b"\0"):
                if e:
                    meta, path = e.split(b"\t", 1)
                    self.blobs[path.decode()] = meta.split()[2].decode()

    def read(self, path):
        if path in self.disk:
            return open(os.path.join(ROOT, path), "rb").read()
        if self.cat is None:
            self.cat = subprocess.Popen(["git", "cat-file", "--batch"], cwd=ROOT, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE)
        self.cat.stdin.write(self.blobs[path].encode() + b"\n")
        self.cat.stdin.flush()
        size = int(self.cat.stdout.readline().split()[2])
        data = self.cat.stdout.read(size)
        self.cat.stdout.read(1)
        return data

    def close(self):
        if self.cat is not None:
            self.cat.stdin.close()
            self.cat.wait()


class Cache:
    def __init__(self):
        common = git("rev-parse", "--git-common-dir").decode().strip()
        self.path = os.path.join(ROOT, common, "dead-code-fast.pickle")
        self.data, self.used, self.dirty = {}, set(), False
        try:
            data = pickle.load(open(self.path, "rb"))
            if data.get("v") == VERSION:
                self.data = data["entries"]
        except Exception:
            pass

    def get(self, key, make):
        self.used.add(key)
        if key not in self.data:
            self.data[key] = make()
            self.dirty = True
        return self.data[key]

    def save(self, keep):
        """Keep what this run used and, of the rest, what `keep` names (the entries of the other trees)."""
        if not self.dirty:
            return
        entries = {k: v for k, v in self.data.items() if k in self.used or k in keep}
        tmp = self.path + ".tmp"
        try:
            pickle.dump({"v": VERSION, "entries": entries}, open(tmp, "wb"), protocol=pickle.HIGHEST_PROTOCOL)
            os.replace(tmp, self.path)
        except OSError:
            pass


class Node:
    __slots__ = ("mod", "name", "kw", "line", "flags", "exact", "comps")

    def __init__(self, mod, name, kw, line, flags):
        self.mod, self.name, self.kw, self.line, self.flags = mod, name, kw, line, flags
        self.exact, self.comps = [], ()


def fresh(mod, path, summary, build):
    """The hash of the module's `.ilean` if the build has one made from this source, else None."""
    if summary["lake"] is None:
        return None
    base = os.path.join(build, mod)
    try:
        trace = json.load(open(base + ".trace", encoding="utf-8"))
        made = next(h for label, h in trace["inputs"] if isinstance(h, str) and label.endswith("/" + path))
        have = open(base + ".ilean.hash", encoding="utf-8").read().strip()
        if made == summary["lake"] and trace["outputs"]["i"].startswith(have) and os.path.exists(base + ".ilean"):
            return have
    except (OSError, ValueError, KeyError, StopIteration, TypeError):
        pass
    return None


def analyse(tree, cache, use_build=True, why=None):
    """The findings on one tree."""
    paths = {}
    for p in tree.blobs:
        parts = p.split("/")
        if len(parts) == 3 and parts[0] == "lib" and parts[1] in DIRS and p.endswith(".lean"):
            paths[parts[2][:-5]] = p
    ours = set(paths)
    build = os.path.join(ROOT, BUILD)
    summaries, ileans = {}, {}
    for mod, p in paths.items():
        summaries[mod] = cache.get(("src", tree.blobs[p]), lambda p=p: summarise(tree.read(p)))
        h = fresh(mod, p, summaries[mod], build) if use_build else None
        if h:
            ileans[mod] = cache.get(("ilean", mod, h), lambda mod=mod: ilean(os.path.join(build, mod + ".ilean"), ours))
    # the imports, those of the vendored libraries included (they import `Architect`), and for each module of the
    # library the modules of the library that it imports, directly or not: it can use no other
    imports = {m: s["imports"] for m, s in summaries.items()}
    for p, blob in tree.blobs.items():
        parts = p.split("/")
        if len(parts) > 3 and parts[:2] == ["lib", "vendor"] and p.endswith(".lean"):
            imports[".".join(parts[3:])[:-5]] = cache.get(("imports", blob), lambda p=p: re.findall(
                r"^import\s+(?:all\s+)?(\S+)", tree.read(p).decode("utf-8", "replace"), re.M))
    cones = {}

    def cone(m):
        """The modules of the library in the import cone of `m`, itself included."""
        if m not in cones:
            cones[m] = None                     # (an import cycle would not compile)
            out = {m} if m in ours else set()
            for i in imports.get(m, ()):
                if i in imports:
                    out |= cone(i) or set()
            cones[m] = frozenset(out)
        return cones[m]

    sys.setrecursionlimit(max(sys.getrecursionlimit(), 20000))
    # the declarations
    nodes, by_name, by_last, owner = {}, collections.defaultdict(list), collections.defaultdict(list), {}
    cites = []          # (module, command) of the commands that are not declarations and may use one
    for mod, s in summaries.items():
        il = ileans.get(mod)
        sel = collections.defaultdict(list)
        if il:
            for n, line in il["decls"].items():
                sel[line].append(n)
        for c in s["cmds"]:
            if c[0] == "decl":
                _, start, stop, kw, name, line, flags, comps = c
                if il:   # the name as Lean has it
                    names = [n for ln in range(start, stop + 1) for n in sel.get(ln, ()) if last(n) == last(name)]
                    exact = [n for n in names if n == name or n.endswith("." + name)]
                    name = (exact or names or [name])[0]
                node = Node(mod, name, kw, line, flags)
                node.comps = comps
                nodes[(mod, name)] = node
                by_name[name].append(node)
                by_last[last(name)].append(node)
                owner[(mod, start)] = node
            elif c[0] in ("cite", "quote"):
                cites.append((mod, c))
    # the uses that the builds record, by the command they stand in
    starts = {mod: [c[1] for c in s["cmds"]] for mod, s in summaries.items()}
    root_exact, textual = [], set(m for m in summaries if m not in ileans)

    def resolve(m, n):
        """The declarations that a constant of module `m` may stand for: itself; or the one whose field, constructor
        or auxiliary definition it is; or, if the sources name it otherwise than Lean does, the module's
        declarations with its last component."""
        node = nodes.get((m, n))
        if node is not None:
            return [node]
        out, p = [x for x in by_last.get(last(n), ()) if x.mod == m], n
        while "." in p:
            p = p.rsplit(".", 1)[0]
            if (m, p) in nodes:
                out.append(nodes[(m, p)])
                break
        return out

    for mod, il in ileans.items():
        cmds, st = summaries[mod]["cmds"], starts[mod]
        for line, m, n in il["uses"]:
            k = bisect.bisect_right(st, line) - 1
            if k < 0 or line > cmds[k][2]:
                continue
            c = cmds[k]
            if c[0] == "skip":
                continue
            for target in resolve(m, n):
                if c[0] == "decl":
                    src = owner[(mod, c[1])]
                    if src is not target:
                        src.exact.append(target)
                else:
                    root_exact.append((target, f"{mod}:{line}"))
    # the roots
    prints = {c: summaries[c]["prints"] if c in summaries else [] for c in CHECKS}
    printed = sorted({n for c in CHECKS for n in prints[c]})
    via, queue = {}, collections.deque()

    def reach(node, source):
        if node not in via:
            via[node] = source
            queue.append(node)

    missing = []
    for n in printed:
        if by_name.get(n):
            for node in by_name[n]:
                reach(node, "printed by a check file")
        elif not by_last.get(last(n)):
            missing.append(n)
    for node in nodes.values():
        if node.flags:
            reach(node, "an instance, or a declaration with an attribute, or of the meta level")
    for target, where in root_exact:
        reach(target, f"cited at {where}, outside a declaration")
    def loose():
        """The declarations that the text of a command outside the declarations may cite."""
        for mod, c in cites:
            if c[0] == "quote" or mod in textual:
                seen_from = cone(mod)
                for comp in c[-1]:
                    for target in by_last.get(comp, ()):
                        if target.mod in seen_from:
                            yield target, mod, c[1]

    for target, mod, line in loose():
        reach(target, f"cited in {mod}, l. {line}, outside a declaration")
    # the walk; `cited` records, for a declaration, another live one that uses it
    cited = {}

    def targets(node):
        if node.mod in textual:
            seen_from = cone(node.mod)
            for comp in node.comps:
                for t in by_last.get(comp, ()):
                    if t.mod in seen_from:
                        yield t
        else:
            yield from node.exact

    while queue:
        node = queue.popleft()
        for t in targets(node):
            if t is not node:
                cited.setdefault(t, node)
                reach(t, node)
    for target, _ in root_exact:
        cited.setdefault(target, None)
    for target, _, _ in loose():
        cited.setdefault(target, None)
    dead = [n for n in nodes.values() if n not in via]
    inner = {t for n in dead for t in targets(n) if t is not n}
    unused = sorted(({"module": n.mod, "name": n.name, "kind": n.kw, "line": n.line, "top": n not in inner}
                     for n in dead), key=lambda d: (d["module"], d["line"]))
    # the modules that no check file imports
    seen, stack = set(), [c for c in CHECKS if c in summaries]
    while stack:
        m = stack.pop()
        if m not in seen:
            seen.add(m)
            stack += [i for i in imports[m] if i in imports]
    unimported = sorted(ours - seen)
    # the results that nothing uses and nothing registers
    registered, conditional = registry(tree)
    # (those that the page on the zeros presents are taken out by `main`, if any is left to report: the page is
    # slow to read)
    unregistered = [n for n in printed if by_name.get(n) and not any(x in cited for x in by_name[n])
                    and n not in prints["Check"] and n not in registered]
    stale = sorted(conditional - set(printed))
    explain = None
    if why:
        explain = []
        for node in by_name.get(why, []) or [n for n in nodes.values() if n.name.endswith("." + why)]:
            chain, x = [f"{node.name} ({node.mod}, l. {node.line})"], node
            while x in via and isinstance(via[x], Node):
                x = via[x]
                chain.append(f"{x.name} ({x.mod})")
            chain.append(via[x] if x in via else "no root reaches it")
            explain.append(chain)
    return {"unused": unused, "unimported": unimported, "unregistered": unregistered, "stale": stale,
            "missing": missing, "printed": len(printed), "declarations": len(nodes),
            "exact": len(ileans), "textual": len(textual), "why": explain,
            "unbuilt": {m: tree.blobs[paths[m]] for m in textual if summaries[m]["lake"] is not None},
            "keys": {(kind, b) for b in tree.blobs.values() for kind in ("src", "imports")}}


def registry(tree):
    """The names that formalisations/ registers, and those of its tables "Conditional results"."""
    names, conditional = set(), set()
    for p in sorted(tree.blobs):
        if not (p.startswith("formalisations/") and p.endswith(".md")):
            continue
        text = tree.read(p).decode("utf-8", "replace")
        names |= set(re.findall(NAME, text))
        m = re.search(r"^## Conditional results\n(.*?)(?=^## |\Z)", text, re.M | re.S)
        for row in (m.group(1) if m else "").splitlines():
            cells = re.split(r"(?<!\\)\|", row)[1:-1]
            if len(cells) == 3:
                conditional |= set(re.findall(NAME, cells[2]))
    return names, conditional


def page():
    """The theorems that the page on the zeros presents (from the working tree)."""
    out = set()
    try:
        sys.path.insert(0, os.path.join(ROOT, "scripts"))
        import zeros_page

        def walk(o):
            if isinstance(o, str):
                out.update(re.findall(r"[A-Z][\w']*\.[\w.']+", o))
            elif isinstance(o, dict):
                for v in o.values():
                    walk(v)
            elif isinstance(o, (list, tuple)):
                for v in o:
                    walk(v)
        walk(zeros_page.extract())
    except Exception:
        pass
    return out


def items(f):
    """The findings as a set, to compare two trees."""
    out = {("unused", d["module"], d["name"]) for d in f["unused"]}
    out |= {("unimported", m, "") for m in f["unimported"]}
    out |= {("unregistered", n, "") for n in f["unregistered"]}
    out |= {("stale", n, "") for n in f["stale"]}
    out |= {("missing", n, "") for n in f["missing"]}
    return out


def report(f, only=None):
    """Print the findings (those of `only`, if given) and return how many there are."""
    count = 0
    by_mod = collections.defaultdict(list)
    for d in f["unused"]:
        if only is None or ("unused", d["module"], d["name"]) in only:
            by_mod[d["module"]].append(d)
    for m in sorted(by_mod):
        ds = by_mod[m]
        count += len(ds)
        shown = ", ".join(f"{d['name']} (l. {d['line']})" for d in ds[:12])
        print(f"{m}: {len(ds)} unused: {shown}" + (" …" if len(ds) > 12 else ""))
    for kind, text in (("unimported", "imported by no check file"),
                       ("unregistered", "a result that nothing uses, neither a paper's, nor on the page on the zeros, "
                                        "nor in formalisations/"),
                       ("stale", "in a section Conditional results of formalisations/ but printed by no check file"),
                       ("missing", "printed by a check file, but no module declares it")):
        for n in f[kind]:
            if only is None or (kind, n, "") in only:
                count += 1
                print(f"{n}: {text}")
    return count


def main(argv):
    opts = {"--staged": False, "--sources": False}
    values = {"--rev": None, "--against": None, "--why": None, "--json": None}
    i = 0
    while i < len(argv):
        a = argv[i]
        if a in opts:
            opts[a] = True
        elif a in values and i + 1 < len(argv):
            i += 1
            values[a] = argv[i]
        else:
            print(__doc__.split("\n\n")[1], file=sys.stderr)
            return 2
        i += 1
    cache = Cache()
    tree = Tree(values["--rev"] or (":" if opts["--staged"] else None))
    f = analyse(tree, cache, use_build=not opts["--sources"], why=values["--why"])
    tree.close()
    keep, only = set(f["keys"]), None
    what = "the commit " + values["--rev"] if values["--rev"] else "the index" if opts["--staged"] else "the working tree"
    if values["--against"]:
        base = Tree(values["--against"])
        g = analyse(base, cache, use_build=not opts["--sources"])
        base.close()
        keep |= g["keys"]
        only = items(f) - items(g)
        what += f", against {values['--against']}"
        # the modules that the change touches and whose build is not current: read as text, they may hide a finding
        stale = sorted(m for m, blob in f["unbuilt"].items() if g["unbuilt"].get(m) != blob and not opts["--sources"])
        if stale:
            print(f"note: {len(stale)} changed module{'' if len(stale) == 1 else 's'} read from the source, having "
                  f"no current build ({', '.join(stale[:6])}{' …' if len(stale) > 6 else ''}): a use is then any "
                  f"mention of a name. For the exact uses, build first: scripts/build.sh "
                  + " ".join("+" + m for m in stale[:6]) + (" …" if len(stale) > 6 else ""))
    cache.save(keep)
    if any(only is None or ("unregistered", n, "") in only for n in f["unregistered"]):
        shown = page()
        f["unregistered"] = [n for n in f["unregistered"] if n not in shown]
    if values["--why"]:
        for chain in f["why"] or [[f"{values['--why']}: no such declaration"]]:
            print("\n  <- ".join(chain))
        return 0
    count = report(f, only)
    print(f"dead_code_fast ({what}): {f['printed']} printed theorems, {f['declarations']} declarations; "
          f"{f['exact']} modules read from their build, {f['textual']} from their sources; "
          f"{count} finding{'' if count == 1 else 's'}" + (" that the base does not have" if only is not None else ""))
    print("DEAD CODE (FAST) PASS" if not count else "DEAD CODE (FAST) FAIL")
    if values["--json"]:
        out = {k: v for k, v in f.items() if k not in ("keys", "why", "unbuilt")}
        if only is not None:
            out["new"] = sorted(only)
        json.dump(out, open(values["--json"], "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    return 1 if count else 0


if __name__ == "__main__":
    # 0: no finding; 1: findings; 2: the check could not run (the hook then lets the commit through, and says so)
    try:
        code = main(sys.argv[1:])
    except Exception as e:  # noqa: BLE001
        import traceback
        traceback.print_exc()
        print(f"dead_code_fast could not run: {e}", file=sys.stderr)
        code = 2
    sys.exit(code)
