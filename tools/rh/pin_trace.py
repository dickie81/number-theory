#!/usr/bin/env python3
"""Say how a name of one file of the archive is read: by the file's own imports, and by a bundle.

    python3 -I tools/rh/pin_trace.py FILE NAME [PART_OF_A_DECLARATION_NAME] [--map DIR] [--scan SCAN.json]

FILE is a path under the archive's `src`, NAME an identifier as the file writes it. For the first declaration of
the file that uses NAME (or the first whose name contains the third argument), it prints the namespaces around
the declaration, the namespaces that are open there, and what NAME resolves to in four views:

    own    the file and what it imports, to the end: what `lean` sees on the file alone
    low    the file and every file of a lower level: what a bundle shows it (`bundle_build.py`)
    same   the same with the files of its own level
    all    the whole archive

A failure of the bundled build that is a name read wrongly shows here as `own` differing from `low`, and
`capture_rewrites.py` then pins the name. When the build fails on a name and this prints nothing, the map has not
taken NAME for a name in that declaration (it thought it bound: see `bound_names` in `decl_map.py`); when `own`
is empty, the map does not find what the file means (an `open` it does not follow, a name that Mathlib exports).
Both were the cause of failures, and this is how each was found.

It reads the map of `decl_map.py` as `capture_rewrites.py` does, without the import-order rule for a name that
two imported files declare.
"""
import argparse
import json
import os
import pickle

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def main():
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("name")
    ap.add_argument("decl", nargs="?")
    ap.add_argument("--map", default=os.path.join(ext, "declmap"))
    ap.add_argument("--scan", default=os.path.join(ext, "scan.json"))
    args = ap.parse_args()
    with open(os.path.join(args.map, "graph.pkl"), "rb") as f:
        g = pickle.load(f)
    with open(os.path.join(args.map, "mathnames.pkl"), "rb") as f:
        math = pickle.load(f)
    with open(args.scan) as f:
        mods = json.load(f)["modules"]
    files, names, kinds, flags, d_file, arch = g["files"], g["names"], g["kinds"], g["flags"], g["d_file"], g["arch"]
    prot = g.get("prot", set())
    f_id = files.index(args.file)
    mod_of = [r[:-5].replace(os.sep, ".") for r in files]
    file_of = {m: i for i, m in enumerate(mod_of)}
    level = [mods[m]["level"] for m in mod_of]
    closure, stack = set(), [mod_of[f_id]]
    while stack:
        for i in mods[stack.pop()]["imports"]:
            if i in mods and i not in closure:
                closure.add(i)
                stack.append(i)
    own_files = {file_of[m] for m in closure} | {f_id}
    by_name = {}
    for d, dnames in enumerate(names):
        if kinds[d] == "syn" or flags[d] & 1:
            continue
        for n in dnames:
            by_name.setdefault(n, []).append(d)
    spaces = set()
    for table in (arch, math):
        for name in table:
            parts = name.split(".")
            for k in range(1, len(parts)):
                spaces.add(".".join(parts[:k]) + ".")
    for name in arch:
        spaces.add(name + ".")
    shard_dir = os.path.join(args.map, "shards")
    with open(os.path.join(shard_dir, sorted(os.listdir(shard_dir))[0]), "rb") as f:
        size = len(pickle.load(f))
    with open(os.path.join(shard_dir, "%05d.pkl" % (f_id // size)), "rb") as f:
        _, decls = pickle.load(f)[f_id % size]
    first = next(d for d in range(len(names)) if d_file[d] == f_id)
    priv = {}
    for j, rec in enumerate(decls):
        if rec[2] & 1:
            for n in rec[1]:
                priv[n] = first + j
    mine_spaces = set()
    for n in priv:
        parts = n.split(".")
        for k in range(1, len(parts)):
            mine_spaces.add(".".join(parts[:k]) + ".")
    lv = level[f_id]

    def resolve(tok, chain, opens, seen):
        if tok.startswith("_root_."):
            tok, chain, opens = tok[7:], (), ()
        comps = tok.split(".")
        n = len(comps)

        def look(name):
            i = priv.get(name)
            if i is not None:
                return i
            best = None
            for i in by_name.get(name, ()):
                h = d_file[i]
                if h in own_files:
                    return i
                if best is None and seen(h):
                    best = i
            return best

        def where(i):
            return "%s (level %d)" % (files[d_file[i]], level[d_file[i]])

        for m in range(n, 0, -1):
            t = tok if m == n else ".".join(comps[:m])
            fields = comps[m:]
            atom = m == 1
            for p in chain:
                if atom and p + t in prot:
                    continue        # a protected `N.a` is not what `a` means inside `N` or under `open N`
                i = look(p + t)
                if i is not None:
                    return ["around: %s in %s" % (p + t, where(i))], fields
                if p + t in math:
                    return ["around: %s in Mathlib" % (p + t)], fields
            found = []
            i = look(t)
            if i is not None:
                found.append("root: %s in %s" % (t, where(i)))
            elif t in math:
                found.append("root: %s in Mathlib" % t)
            for o in opens:
                named = False
                if "|" in o:
                    o, only = o.split("|", 1)
                    if only.startswith("~"):
                        if (" " + t + " ") in only:
                            continue        # `open N hiding t`
                    else:
                        named = True
                        if (" " + comps[0] + " ") not in only:
                            continue
                if atom and not named and o + t in prot:
                    continue
                i = look(o + t)
                if i is not None:
                    found.append("open: %s in %s" % (o + t, where(i)))
                elif o + t in math:
                    found.append("open: %s in Mathlib" % (o + t))
            if found:
                return found, fields
        return [], comps[1:]

    print("the file is of level %d and imports %d files of the archive" % (lv, len(own_files) - 1))
    for rec in decls:
        if args.name not in set(rec[9]) | set(rec[10]):
            if "?" + args.name in set(rec[9]) | set(rec[10]):
                print("%s %s binds %s somewhere: the name is followed if the whole of it is a constant, and "
                      "is not pinned" % (rec[0], " ".join(rec[1]), args.name.split(".", 1)[0]))
            continue
        if args.decl and not any(args.decl in n for n in rec[1]):
            continue
        chain = tuple(rec[7])
        seen_chain, opens = set(chain), []
        for o in rec[8]:
            if (o.split("|", 1)[0] in spaces or o.split("|", 1)[0] in mine_spaces) and o not in seen_chain:
                seen_chain.add(o)
                opens.append(o)
        print("%s %s, lines %d to %d" % (rec[0], " ".join(rec[1]), rec[4] + 1, rec[5] + 1))
        print("  around it: %s" % " ".join(chain))
        print("  open:      %s" % " ".join(opens))
        for label, seen in (("own", lambda h: h in own_files), ("low", lambda h: level[h] < lv),
                            ("same", lambda h: level[h] <= lv), ("all", lambda h: True)):
            found, fields = resolve(args.name, chain, tuple(opens), seen)
            print("  %-5s %s%s" % (label, "; ".join(found) or "nothing",
                                     ("   (then the fields %s)" % ".".join(fields)) if fields else ""))
        return
    print("no declaration of the file has %s among its names: the map takes it for bound there, or the "
          "declaration is not the one named" % args.name)


if __name__ == "__main__":
    main()
