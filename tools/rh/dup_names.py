#!/usr/bin/env python3
"""The names that two files of the archive both declare, and which declaration is compiled under another name.

    python3 -I tools/rh/dup_names.py OUT.json [--map DIR] [--scan SCAN.json] [--state STATE.jsonl] [--force FILE ...]

Lean lets two modules declare one name as long as nothing imports both, and the archive does it 133 times; for 89
of the names the two texts differ, and for some the statements do (`ReciprocityTheory.L2DbarEstimates.wd_congr`
takes a number in one file and a proof in the other). The bundles of `bundle_build.py` are one environment, and a
name means one thing there. Two modules with one theorem of one statement can both be imported, which is how the
first build treated all of them: within a level the two files go to different bundles, and across levels the upper
declaration is left out and its users are checked against the lower one. That fails as soon as the statements
differ, and two bundles of one level that declare one name with two statements cannot be imported together at all.

So each declaration of such a name but the first, in the order of the levels, is compiled under another name:
`wd_congr` becomes `wd_congr_b2` in its own file (`Bundle.lean` renames the component there), and
`capture_rewrites.py` pins the name in every file whose own imports give that declaration. OUT.json lists, under
`files`, for each file the components to rename, and under `decls` the declarations with their old and new names.

A declaration whose file a build has already compiled keeps the older treatment, so that what is built stays
built: `--state` names the build's `state.jsonl`. `--force` names files to rename in all the same; the bundle
that holds such a file has to be compiled again. Once a build has used OUT.json, make it again only with
`--keep OUT.json`, so that a file compiled under the new names since is not taken for one to leave alone.
"""
import argparse
import json
import os
import pickle
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def main():
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--map", default=os.path.join(ext, "declmap"))
    ap.add_argument("--scan", default=os.path.join(ext, "scan.json"))
    ap.add_argument("--state", help="state.jsonl of a build: the files it has compiled are left as they are")
    ap.add_argument("--force", nargs="*", default=[])
    ap.add_argument("--keep", help="an earlier OUT.json: what it renames stays so, whatever the build has done since")
    args = ap.parse_args()
    with open(os.path.join(args.map, "graph.pkl"), "rb") as f:
        g = pickle.load(f)
    with open(args.scan) as f:
        mods = json.load(f)["modules"]
    files, names, kinds, flags, d_file = g["files"], g["names"], g["kinds"], g["flags"], g["d_file"]
    level = [mods[rel[:-5].replace(os.sep, ".")]["level"] for rel in files]
    done = set()
    if args.state and os.path.exists(args.state):
        last = {}
        with open(args.state) as f:
            for line in f:
                r = json.loads(line)
                last[r["bundle"]] = r
        for r in last.values():
            if r["ok"]:
                done.update(r["files"])
    force = {files.index(rel) for rel in args.force}
    if args.keep and os.path.exists(args.keep):
        with open(args.keep) as f:
            kept = json.load(f)
        force |= {files.index(rel) for rel in kept["files"]}
    by_name = defaultdict(list)
    for d, dnames in enumerate(names):
        if kinds[d] in ("syn", "attr", "example", "export") or flags[d] & 1:
            continue
        for name in dnames:
            by_name[name].append(d)
    per_file, decls = defaultdict(list), []
    shared = renamed = 0
    for name in sorted(by_name):
        ds = sorted(by_name[name], key=lambda d: (level[d_file[d]], files[d_file[d]]))
        if len({d_file[d] for d in ds}) < 2:
            continue
        shared += 1
        first = d_file[ds[0]]
        k = 1
        for d in ds[1:]:
            f = d_file[d]
            if f == first:
                continue
            k += 1
            if f in done and f not in force:
                continue
            last = name.rsplit(".", 1)[-1]
            new = "%s_b%d" % (last, k)
            if [last, new] not in per_file[files[f]]:
                per_file[files[f]].append([last, new])
            decls.append([files[f], name, name[:len(name) - len(last)] + new])
            renamed += 1
    with open(args.out, "w") as f:
        json.dump(dict(files=per_file, decls=decls), f, indent=1, ensure_ascii=False)
    print("%d names are declared in more than one file; %d declarations in %d files get another name"
          % (shared, renamed, len(per_file)))


if __name__ == "__main__":
    main()
