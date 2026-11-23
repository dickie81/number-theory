#!/usr/bin/env python3
"""Find the names that a bundle would read otherwise than the file's own imports do, and what they mean.

    python3 -I tools/rh/capture_rewrites.py OUT.json [--map DIR] [--scan SCAN.json] [--max-level L]

In a bundle a file sees every file of the lower levels, also those it does not import (`bundle_build.py`). If one
of those declares `PI.discr`, then `discr` in the namespace `PI` no longer means `NumberField.discr`; if one
declares `FD.isIntegral_cc` and the file opens `FD` beside the namespace of its own `isIntegral_cc`, the name is
ambiguous. This script reads every name of every declaration (as `decl_map.py` split them) in three views: the
file's own imports, all the lower levels, and the lower levels with the file's own level. Where the second differs
from the first and the first gives one constant, of the archive or of Mathlib, the name is to be read as that
constant: OUT.json lists under `pins`, for each file, `[first line, last line, name as written, _root_.constant,
"n"]`, and `Bundle.lean` replaces the identifier in the commands of those lines. If the first view gives nothing
the name is a local variable that the map took for a constant, and nothing is done. If it gives several, Lean
chooses among them by type, and the bundle must be given the same choice: the entry lists them, `A|B`, and ends
with `"c"`. If the constant is a private declaration of the file itself, the entry reads `_private_.constant`.
A declaration that the bundles hold under another name (`dup_names.py`) is pinned to that name wherever the file's
own view gives it. Where the third view differs from the second, the files of the
same level that make the difference are listed with the file under `apart`, and `bundle_build.py` keeps them in
different bundles.

A command that is not a declaration can name a constant too (`variable {r : G E Ω →* K}`), and the map has no
entry for it. A name that the declarations of the file pin, all to one constant, is pinned in those commands as
well, unless the command binds the name.

The same happens to a namespace: `open WittVector` inside `namespace GlobalTheory.WittGauss` opens
`GlobalTheory.WittVector` once a file that is not imported declares something there, and Lean opens the innermost
one only. Each `open` of each file is resolved in both views, and where they differ the namespace is pinned too
(`_root_.WittVector`); those entries end with `"o"`, and are applied inside `open` only, also to an
`open Classical in` inside a declaration (`GlobalTheory.CompanionTheory.Classical` is a namespace of the archive,
and a definition under `GlobalTheory.CompanionTheory` that opens `Classical` for an `if` then finds no way to
decide its condition). `open Chart (JetR zR)`
is refused when Lean finds a name twice among the namespaces that `Chart` may be, and a namespace `Chart` at the
root, of a file that is not imported, is enough for that: in such a command `Chart` is always pinned to the one
namespace in which the file's own view finds the names.

OUT.json lists under `edges` what the pinned names refer to in their file's own view, as pairs of declarations
of the map (`n` is the number of its declarations): the map follows a name to what the whole archive makes of
it, which may be a namesake in another file, and `bundle_build.py` adds these to what it follows.

OUT.json also lists under `local`, for each file, a name for each local notation or macro that it declares: what
such a command declares is private and named after its atoms, so two files with the same one in the same namespace
cannot share a bundle, like two files with a private theorem of one name.
"""
import argparse
import importlib.util
import json
import multiprocessing as mp
import os
import pickle
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


DM = None
ONLY = re.compile(r"\s*([^\s()]+)\s*\(([^()]*)\)\s*$")
# (a `variable` command has an entry of its own in the map, and is pinned by what it names itself)
GAP_KW = {"notation", "infix", "infixl", "infixr", "prefix", "postfix", "attribute", "macro", "syntax"}
BINDER = re.compile(r"[({⦃\[]([^:()\[\]{}⦃⦄]*):")


def scan_opens(job):
    """The `open`s of some files, each with its lines, the namespace around it, the namespaces it names and, for
    `open N (a b)`, the names `a b`; the namespaces that the files' `namespace` commands make, each with the
    line of the first command that makes it; and a name for each local notation or macro."""
    src, rels, pinned = job
    dm = DM
    out = []
    for rel in rels:
        with open(os.path.join(src, rel), encoding="utf-8", errors="replace") as f:
            text = f.read()
        pins = pinned.get(rel)
        if "open" not in text and "namespace" not in text and not pins:
            out.append((rel, [], [], [], []))
            continue
        gaps = []
        if "--" in text or "/-" in text:
            text = dm.strip_comments(text)
        stack, opens, made, waiting, waiting_only, first = [""], [], {}, [], [], None
        held = [set()]      # beside `stack`: the names that the `variable` commands of each scope bind
        local = []

        def names_of(t):
            t = re.sub(r"\([^)]*\)", " ", t)
            t = re.split(r"\b(?:hiding|renaming)\b", t)[0]
            return [x for x in t.split() if x != "scoped"]

        for l0, l1, chunk in dm.split_commands(text):
            t = chunk
            is_local = False
            if first is None:
                first = l0
            while True:
                t = t.lstrip()
                if t.startswith("@["):
                    t = t[dm.close_bracket(t, 1) + 1:]
                    continue
                m = dm.SETOPT_IN.match(t) or dm.OTHER_IN.match(t)
                if m:
                    t = t[m.end():]
                    continue
                m = dm.ATTR_IN.match(t)
                if m:
                    t = t[m.end():]
                    continue
                m = dm.OPEN_IN.match(t)
                if m:
                    m3 = ONLY.match(m.group(1))
                    if m3:
                        waiting_only.append((m3.group(1), m3.group(2).split()))
                    else:
                        waiting.extend(names_of(m.group(1)))
                    t = t[m.end():]
                    continue
                m = dm.WORD.match(t)
                if m and m.group() in dm.MODS:
                    if m.group() == "local":
                        is_local = True
                    t = t[m.end():]
                    continue
                break
            if not t:
                continue
            ns = stack[-1]
            if waiting:
                opens.append((first, l1, ns, waiting, None))
                waiting = []
            for name, ids in waiting_only:
                opens.append((first, l1, ns, [name], ids))
            waiting_only = []
            m = dm.WORD.match(t)
            kw = m.group() if m else ""
            rest = t[len(kw):]
            if kw == "variable" or (pins and kw in GAP_KW):
                # a command that is not a declaration and names a constant that the file's declarations pin:
                # `variable {r : G E Ω →* K}`. A name that the command binds is not one, nor is a name that an
                # earlier `variable` of the scope bound (`variable {G : Type}` … `variable (gl : G → Γ)`)
                bound = set()
                for m2 in BINDER.finditer(t):
                    bound.update(m2.group(1).split())
                if kw == "variable":
                    held[-1] |= bound
                bound = bound.union(*held)
            if pins and kw in GAP_KW:
                for tok, new in pins.items():
                    if tok not in bound and re.search(r"(?<![\w.'])" + re.escape(tok) + r"(?![\w.'!?])", t):
                        gaps.append([l0, l1, tok, new, "n"])
            if kw == "namespace":
                name = rest.split()[0] if rest.split() else ""
                full = ns
                for part in name.split("."):
                    full = (full + "." + part) if full else part
                    stack.append(full)
                    held.append(set())
                parts = full.split(".")
                for k in range(1, len(parts) + 1):
                    made.setdefault(".".join(parts[:k]), l0)
            elif kw in ("section", "mutual"):
                stack.append(ns)
                held.append(set())
            elif kw == "end":
                name = rest.split()[0] if rest.split() else ""
                for _ in range(len(name.split(".")) if name else 1):
                    if len(stack) > 1:
                        stack.pop()
                        held.pop()
            elif kw == "open":
                m3 = ONLY.match(rest)
                if m3:
                    opens.append((l0, l1, ns, [m3.group(1)], m3.group(2).split()))
                else:
                    opens.append((l0, l1, ns, names_of(rest), None))
            elif is_local and kw in dm.SYN_KW:
                # Lean names what a local notation declares after its atoms, privately, in the namespace
                atoms = re.findall(r'"(?:\\.|[^"\\])*"', rest)
                local.append("%s.«local %s»" % (ns, " ".join(a[1:-1].strip() for a in atoms)))
            if kw not in ("open", "namespace", "section", "mutual", "end") and "open" in t:
                # `open Classical in` inside a declaration: a namespace like any other, read where the body is
                # read, which for `theorem A.b` is inside `A` (and is not for `theorem _root_.A.b`)
                body_ns = ns
                if kw in dm.DECL_KW:
                    m3 = dm.WORD.match(rest.lstrip())
                    if m3 and "." in m3.group() and not m3.group().startswith("_root_."):
                        pre = m3.group().rsplit(".", 1)[0]
                        body_ns = (ns + "." + pre) if ns else pre
                for m3 in dm.BODY_OPEN.finditer(t):
                    inner = names_of(m3.group(1))
                    if inner:
                        opens.append((l0, l1, body_ns, inner, None))
            first = None
        out.append((rel, opens, made, sorted(set(local)), gaps))
    return out


G = {}


def scan_names(s):
    """The names of the declarations of one shard of the map, read in three views: the file's own imports (`own`),
    what a bundle shows at the file's level, all the lower levels (`low`), and that with the files of the same
    level (`same`). Where `low` differs from `own` the name is pinned to what `own` gives, if that is one constant.
    Where `same` differs from `low`, the file and the files of its level that make the difference are to be kept
    in different bundles."""
    g = G
    files, flags, d_file, level, bit = g["files"], g["flags"], g["d_file"], g["level"], g["bit"]
    by_name, math, spaces, top = g["by_name"], g["math"], g["spaces"], g["top"]
    prot = g["prot"]
    renamed = g["renamed"]
    kinds, names, sig_e, sig_o = g["kinds"], g["names"], g["sig_e"], g["sig_o"]
    imports_of, math_alias = g["imports_of"], g["math_alias"]
    with open(os.path.join(g["shard_dir"], "%05d.pkl" % s), "rb") as f:
        shard = pickle.load(f)
    rows, pairs = [], set()
    n_local = n_many = n_looked = 0
    edges = set()
    for k, (rel, decls) in enumerate(shard):
        f_id = s * g["shard_size"] + k
        assert rel == files[f_id]
        lv = level[f_id]
        if lv > top:
            continue
        c = g["closure"][f_id]
        first = g["first_decl"][f_id]
        priv = {}
        for j, other in enumerate(decls):
            if other[2] & 1:
                for name in other[1]:
                    priv[name] = first + j
        # a namespace that holds only private declarations of the file is one too, for the file
        mine_spaces = set()
        for name in priv:
            parts = name.split(".")
            for m in range(1, len(parts)):
                mine_spaces.add(".".join(parts[:m]) + ".")

        def own(h):
            return h == f_id or (c >> bit[h]) & 1

        order_cache = []

        def import_order():
            """The place of each imported file in the order in which Lean reads them: a file after what it
            imports, the imports of a file in the order of its header."""
            if not order_cache:
                pos, visited, st = {}, {f_id}, [(f_id, iter(imports_of[f_id]))]
                while st:
                    node, it = st[-1]
                    for child in it:
                        if child not in visited:
                            visited.add(child)
                            st.append((child, iter(imports_of[child])))
                            break
                    else:
                        st.pop()
                        pos[node] = len(pos)
                order_cache.append(pos)
            return order_cache[0]

        def resolve(tok, chain, opens, seen):
            """What a name can be: ('a', declaration, full name) or ('m', None, Mathlib name), and the components
            left over as fields. A declaration of the file's own imports is taken before another of the same
            name."""
            if tok.startswith("_root_."):
                tok, chain, opens = tok[7:], (), ()
            comps = tok.split(".")
            n = len(comps)

            def look(name):
                i = priv.get(name)
                if i is not None:
                    return i
                best, mine = None, []
                for i in by_name.get(name, ()):
                    h = d_file[i]
                    if own(h):
                        mine.append(i)
                    elif best is None and seen(h):
                        best = i
                if len(mine) > 1:
                    # two files that this one imports declare the name (Lean allows it for theorems of one
                    # type, binders aside): the one imported last is the one that Lean keeps
                    order = import_order()
                    return max(mine, key=lambda i: order.get(d_file[i], -1))
                return mine[0] if mine else best

            for m in range(n, 0, -1):
                t = tok if m == n else ".".join(comps[:m])
                fields = tuple(comps[m:])
                # a protected `N.a` is not what `a` means inside `N` or under `open N`
                atom = m == 1
                for p in chain:
                    if atom and p + t in prot:
                        continue
                    i = look(p + t)
                    if i is not None:
                        return (("a", i, p + t),), fields
                    if p + t in math:
                        return (("m", None, p + t),), fields
                found = []
                i = look(t)
                if i is not None:
                    found.append(("a", i, t))
                elif t in math:
                    found.append(("m", None, t))
                for o in opens:
                    named = False
                    if "|" in o:
                        o, only = o.split("|", 1)
                        if only.startswith("~"):
                            # `open N hiding t`: all of `N` but those names
                            if (" " + t + " ") in only:
                                continue
                        else:
                            # `open N (a b)`: only those names of `N`
                            named = True
                            if (" " + comps[0] + " ") not in only:
                                continue
                    if atom and not named and o + t in prot:
                        continue
                    i = look(o + t)
                    if i is not None:
                        found.append(("a", i, o + t))
                    elif o + t in math:
                        found.append(("m", None, o + t))
                if found:
                    return tuple(found), fields
            return (), tuple(comps[1:])

        def read(found, fields):
            return tuple(sorted({x[2] for x in found})), fields

        def deref(x, name):
            for _ in range(8):
                if kinds[x] != "export":
                    break
                last = name.rsplit(".", 1)[-1]
                step = None
                for e in sig_e[sig_o[x]:sig_o[x + 1]]:
                    for n2 in names[e]:
                        if n2.rsplit(".", 1)[-1] == last:
                            step = (e, n2)
                if step is None:
                    break
                x, name = step
            return x, name

        memo = {}
        for j, rec in enumerate(decls):
            if rec[0] == "example":
                continue
            chain = tuple(rec[7])
            seen_chain = set(chain)
            opens = []
            for o in rec[8]:
                if (o.split("|", 1)[0] in spaces or o.split("|", 1)[0] in mine_spaces) and o not in seen_chain:
                    seen_chain.add(o)
                    opens.append(o)
            opens = tuple(opens)
            d = first + j
            for tok in set(rec[9]) | set(rec[10]):
                if tok.startswith("?"):
                    continue        # may be a field of a variable (`decl_map.py`): followed, and not pinned
                key = (tok, chain, opens)
                r = memo.get(key)
                if r is None:
                    r = (None, ())
                    everything, _ = resolve(tok, chain, opens, lambda h: True)
                    if any(x[0] == "a" and (not own(d_file[x[1]]) or (x[1], x[2]) in renamed
                                            or (kinds[x[1]] == "export" and len(by_name.get(x[2], ())) > 1))
                           for x in everything):
                        n_looked += 1
                        mine = resolve(tok, chain, opens, own)
                        low = resolve(tok, chain, opens, lambda h: level[h] < lv)
                        same = resolve(tok, chain, opens, lambda h: level[h] <= lv)
                        away = ()
                        if read(*same) != read(*low):
                            away = tuple({d_file[x[1]] for x in same[0]
                                          if x[0] == "a" and level[d_file[x[1]]] == lv and d_file[x[1]] != f_id})
                        act = None
                        found, fields = mine
                        # a declaration that the bundles hold under another name (dup_names.py) is pinned
                        # wherever the file's own imports give it: its old name is another declaration there
                        moved = any(x[0] == "a" and ((x[1], x[2]) in renamed or
                                                     (kinds[x[1]] == "export" and len(by_name.get(x[2], ())) > 1))
                                    for x in found)
                        if read(*low) != read(*mine) or moved:
                            if not found:
                                act = "local"
                            else:
                                # the file's own private declaration is not found before the others: an opened
                                # namespace, or one around the declaration, may hold a public one of the same
                                # name. `Bundle.lean` reads `_private_.X` as the private `X` of the file
                                targets = []
                                for kind, x, name in found:
                                    if kind == "m":
                                        # a name that Mathlib exports (`mul_mem` is `MulMemClass.mul_mem`)
                                        name = math_alias.get(name, name)
                                    if kind == "a":
                                        # what `export N (a)` makes is another name of `N.a`, and a file that is
                                        # not imported may declare a constant of that very name: the pin is
                                        # to what the name stands for
                                        x, name = deref(x, name)
                                    if kind == "a" and (x, name) in renamed:
                                        name = renamed[(x, name)]
                                    head = "_private_." if kind == "a" and flags[x] & 1 else "_root_."
                                    new = head + ".".join((name,) + fields)
                                    if new not in targets:
                                        targets.append(new)
                                if any("«" in t or " " in t or "|" in t for t in targets):
                                    act = None
                                elif len(targets) == 1:
                                    act = targets[0]
                                else:
                                    # the file's own view reads the name in several ways and Lean chooses by
                                    # type: the same choice is given to the bundle
                                    act = "|".join(targets)
                        # what the file's own view gives is what the declaration uses: the map, which reads a
                        # name against the whole archive, may have followed it to a namesake
                        # (`Cz.Leaf2Aux.core_of` under `open Leaf2Aux`, beside a `BcB.core_of` of another file)
                        r = (act, away, tuple(x[1] for x in found if x[0] == "a"))
                    memo[key] = r
                act, away, uses = r if len(r) == 3 else r + ((),)
                for x in uses:
                    if x != d:
                        edges.add((d, x))
                for h in away:
                    pairs.add((rel, files[h]))
                if act == "local":
                    n_local += 1
                elif act is not None:
                    if "|" in act:
                        n_many += 1
                    rows.append((rel, [g["d_l0"][d], g["d_l1"][d], tok, act, "c" if "|" in act else "n"]))
    return rows, pairs, (n_local, n_many, n_looked), edges


def main():
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--map", default=os.path.join(ext, "declmap"))
    ap.add_argument("--scan", default=os.path.join(ext, "scan.json"))
    ap.add_argument("--max-level", type=int, default=0)
    ap.add_argument("--src", default=os.path.join(ext, "extract", "lean", "src"))
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--renames", default=os.path.join(ext, "dup-renames.json"), help="the output of dup_names.py")
    ap.add_argument("--aliases", default=os.path.join(ext, "names", "aliases_native.tsv"),
                    help="the names that Mathlib exports, each with what it stands for")
    args = ap.parse_args()
    global DM
    DM = load("decl_map")
    with open(os.path.join(args.map, "graph.pkl"), "rb") as f:
        g = pickle.load(f)
    with open(os.path.join(args.map, "mathnames.pkl"), "rb") as f:
        math = pickle.load(f)
    with open(args.scan) as f:
        mods = json.load(f)["modules"]
    files, names, kinds, flags, d_file = g["files"], g["names"], g["kinds"], g["flags"], g["d_file"]
    arch = g["arch"]
    mod_of = [rel[:-5].replace(os.sep, ".") for rel in files]
    file_of = {m: i for i, m in enumerate(mod_of)}
    level = [mods[m]["level"] for m in mod_of]
    top = args.max_level or max(level)
    # what each file imports, to the end, as a set of bits; a file's bit is its place in the order of the levels
    order = sorted(range(len(files)), key=lambda f: level[f])
    bit = {f: k for k, f in enumerate(order)}
    closure = {}
    for f in order:
        if level[f] > top:
            break
        c = 0
        for i in mods[mod_of[f]]["imports"]:
            j = file_of.get(i)
            if j is not None:
                c |= closure[j] | (1 << bit[j])
        closure[f] = c
    # the namespaces, to tell which `open`s are of something
    spaces, math_spaces = set(), set()
    for table in (arch, math):
        for name in table:
            parts = name.split(".")
            for k in range(1, len(parts)):
                spaces.add(".".join(parts[:k]) + ".")
                if table is math:
                    math_spaces.add(".".join(parts[:k]))
    for name in arch:
        spaces.add(name + ".")
    # every public declaration of each name: two files may declare one name
    by_name = defaultdict(list)
    for d, dnames in enumerate(names):
        if kinds[d] == "syn" or flags[d] & 1:
            continue
        for name in dnames:
            by_name[name].append(d)
    first_decl = {}
    k = 0
    for f in range(len(files)):
        first_decl[f] = k
        while k < len(names) and d_file[k] == f:
            k += 1
    shard_dir = os.path.join(args.map, "shards")
    shard_files = sorted(os.listdir(shard_dir))
    with open(os.path.join(shard_dir, shard_files[0]), "rb") as f:
        shard_size = len(pickle.load(f))
    # the declarations that the bundles hold under another name: (declaration, name) -> the other name
    renamed = {}
    if args.renames and os.path.exists(args.renames):
        with open(args.renames) as f:
            for rel, old, new in json.load(f)["decls"]:
                for d in by_name.get(old, ()):
                    if files[d_file[d]] == rel:
                        renamed[(d, old)] = new
    # the names that Mathlib exports from a namespace: no constants, and each stands for one
    math_alias = {}
    if args.aliases and os.path.exists(args.aliases):
        with open(args.aliases, encoding="utf-8") as f:
            for line in f:
                a, _, t = line.rstrip("\n").partition("\t")
                if t:
                    math_alias[a] = t.split(",")[0]
    G.update(math_alias=math_alias)
    G.update(renamed=renamed, names=names, sig_e=g["sig_e"], sig_o=g["sig_o"],
             imports_of=[tuple(file_of[i] for i in mods[m]["imports"] if i in file_of) for m in mod_of])
    G.update(files=files, kinds=kinds, flags=flags, d_file=d_file, level=level, bit=bit, closure=closure,
             by_name={k: tuple(v) for k, v in by_name.items()}, math=math, spaces=spaces, top=top,
             prot=g.get("prot", set()),
             shard_dir=shard_dir, shard_size=shard_size, first_decl=first_decl, d_l0=g["d_l0"], d_l1=g["d_l1"])
    out = defaultdict(list)
    apart, edges = set(), set()
    made = skipped_local = skipped_many = looked = 0
    with mp.get_context("fork").Pool(args.jobs) as pool:
        for rows, pairs, counts, more in pool.imap_unordered(scan_names, range(len(shard_files))):
            edges |= more
            for rel, row in rows:
                out[rel].append(row)
            apart |= pairs
            made += len(rows)
            skipped_local += counts[0]
            skipped_many += counts[1]
            looked += counts[2]
    print("%d names looked at again; %d pairs of files of one level to keep apart" % (looked, len(apart)), flush=True)
    # the namespaces: every `open` of every file, in the bundle's view and in the file's own
    todo = [files[f] for f in order if level[f] <= top]
    # the names that a file's declarations pin, each to one constant: the same holds in its other commands
    pinned = {}
    for rel, rows in out.items():
        to = defaultdict(set)
        for r in rows:
            to[r[2]].add(r[3])
        one = {tok: next(iter(v)) for tok, v in to.items() if len(v) == 1 and "|" not in next(iter(v))}
        if one:
            pinned[rel] = one
    jobs = [(args.src, todo[k:k + 500], {rel: pinned[rel] for rel in todo[k:k + 500] if rel in pinned})
            for k in range(0, len(todo), 500)]
    scanned = []
    with mp.get_context("fork").Pool(args.jobs) as pool:
        for rows in pool.imap_unordered(scan_opens, jobs):
            scanned.extend(rows)
    wanted, tail_wanted = set(), set()
    for rel, opens, declared, _, _ in scanned:
        for l0, l1, ns, opened, only in opens:
            parts = ns.split(".") if ns else []
            for name in opened:
                wanted.add(name)
                for k in range(len(parts), 0, -1):
                    wanted.add(".".join(parts[:k]) + "." + name)
                for i in only or ():
                    tail_wanted.add(name + "." + i)
    # `open Chart (JetR zR)`: every constant whose name ends in `Chart.JetR`, with its declarations (-1: Mathlib's)
    tails = defaultdict(list)
    if tail_wanted:
        for table in (by_name, math):
            for name in table:
                parts = name.split(".")
                for j in range(len(parts) - 1):
                    tail = ".".join(parts[j:])
                    if tail in tail_wanted:
                        tails[tail].extend((name, d) for d in (by_name[name] if table is by_name else (-1,)))
    mask = defaultdict(int)     # a namespace that some `open` may mean -> the files that make it
    born = {}                   # (file, namespace) -> the line of the file's first declaration under it
    d_l0 = g["d_l0"]
    for d, dnames in enumerate(names):
        if kinds[d] in ("syn", "attr"):
            continue
        b = 1 << bit[d_file[d]]
        for name in dnames:
            parts = name.split(".")
            for k in range(1, len(parts)):
                ns = ".".join(parts[:k])
                if ns in wanted:
                    mask[ns] |= b
                    key = (d_file[d], ns)
                    if d_l0[d] < born.get(key, 1 << 60):
                        born[key] = d_l0[d]
    for rel, opens, declared, _, _ in scanned:
        b = 1 << bit[file_of[rel[:-5].replace(os.sep, ".")]]
        for ns in declared:
            if ns in wanted:
                mask[ns] |= b
    pinned = between = only_pinned = 0
    for rel, opens, declared, _, gaps in scanned:
        f_id = file_of[rel[:-5].replace(os.sep, ".")]
        if gaps:
            out[rel].extend(gaps)
            between += len(gaps)
        view = closure[f_id] | (1 << bit[f_id])

        def has(space, line):
            """Is `space` a namespace in the file's own view at that line: one of Mathlib, of a file that it
            imports, or one that the file itself has made above the line (`namespace GalTw` … `open
            GlobalTheory.RoadU` … `namespace GlobalTheory.RoadU` opens the root's `GlobalTheory.RoadU`: the
            file makes `GalTw.GlobalTheory.RoadU` three lines later. In a bundle a file of the same directory
            has made it already, Lean opens the innermost only, and the names of the root's are unknown)."""
            return (space in math_spaces or bool(mask.get(space, 0) & closure[f_id])
                    or declared.get(space, 1 << 60) < line or born.get((f_id, space), 1 << 60) < line)

        for l0, l1, ns, opened, only in opens:
            parts = ns.split(".") if ns else []
            if only and not opened[0].startswith("_root_."):
                # `open N (a b)`: Lean looks for each name in every namespace that `N` may be, and refuses the
                # command if it finds a name twice. It does when a bundle shows `N.a` in a namespace that the
                # file does not see, and also when the bundle merely has a namespace `N` at the root that the
                # file has not: Lean then looks `N.a` up as a name, finds it through an earlier `open`, and
                # counts the one constant twice (`open Chart (JetR zR)`: "ambiguous identifier `JetR`, possible
                # interpretations: [Chart.JetR, Chart.JetR]"). So `N` is pinned, always, to the one namespace
                # in which the file's own view finds the names: all of them, or one that the map does not know
                # (a constant that Lean makes) could be of another namespace, and the pin would lose it
                homes, every = set(), True
                for i in only:
                    here = {full[:-len(i) - 1] for full, d in tails.get(opened[0] + "." + i, ())
                            if d < 0 or (view >> bit[d_file[d]]) & 1}
                    every = every and bool(here)
                    homes |= here
                if every and len(homes) == 1:
                    out[rel].append([l0, l1, opened[0], "_root_." + next(iter(homes)), "o"])
                    pinned += 1
                    only_pinned += 1
                    continue
            for name in opened:
                if name.startswith("_root_."):
                    continue
                in_bundle = meant = None
                for k in range(len(parts), 0, -1):
                    cand = ".".join(parts[:k]) + "." + name
                    there = cand in math_spaces
                    if in_bundle is None and (there or mask.get(cand, 0)):
                        in_bundle = cand
                    if meant is None and has(cand, l0):
                        meant = cand
                if in_bundle is None:
                    continue        # the bundle opens the root's, as the file does
                if meant is None:
                    if not has(name, l0):
                        # no such namespace at the root either: the name is found through an earlier `open`
                        # (`open CategoryTheory Limits`), and still is, beside the one that the bundle adds
                        continue
                    meant = name
                if meant != in_bundle:
                    out[rel].append([l0, l1, name, "_root_." + meant, "o"])
                    pinned += 1
    for rel in out:
        out[rel].sort(key=lambda r: (r[0], r[1], r[2]))
    local = {rel: keys for rel, _, _, keys, _ in scanned if keys}
    with open(args.out, "w") as f:
        json.dump(dict(pins=out, local=local, apart=sorted(apart), edges=sorted(edges), n=len(names)), f, indent=0,
                  ensure_ascii=False)
    print("%d references that the file's own view gives, for the map's graph" % len(edges))
    print("%d files declare a local notation or macro" % len(local))
    print("%d names and %d namespaces (%d of them in `open N (a b)`) to read as in their file's own view, in %d "
          "files, and %d names in commands that are not declarations; %d names left alone as local variables; %d "
          "of the names are read in several ways by their own file, and are given that choice"
          % (made, pinned, only_pinned, len(out), between, skipped_local, skipped_many))


if __name__ == "__main__":
    main()
