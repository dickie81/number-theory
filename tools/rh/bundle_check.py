#!/usr/bin/env python3
"""Check what a bundled build holds: the axioms of a theorem, and the exact list of what it rests on.

    python3 -I tools/rh/bundle_check.py --out OUT ROOT [ROOT ...]

For each ROOT it imports Mathlib and every bundle of OUT, logs the axioms that ROOT depends on, writes the constants
of the archive that ROOT reaches to OUT/cone/ROOT.txt (`lean/Cone.lean`), and compares them with the declarations
of the map: how many source declarations the theorem really needs, and how many lines they hold.
"""
import argparse
import importlib.util
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def main():
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--map", default=os.path.join(ext, "declmap"))
    ap.add_argument("--workspace", default=os.path.join(ext, "native-ws"))
    ap.add_argument("roots", nargs="+")
    args = ap.parse_args()
    out = os.path.abspath(args.out)
    os.makedirs(os.path.join(out, "cone"), exist_ok=True)
    last = {}
    with open(os.path.join(out, "state.jsonl")) as f:
        for line in f:
            r = json.loads(line)
            last[r["bundle"]] = r
    bundles = sorted(b for b, r in last.items() if r["ok"])
    with open(os.path.join(HERE, "lean", "Cone.lean"), encoding="utf-8") as f:
        cone = f.read().replace("import Lean\n", "import Mathlib\n" + "".join("import B.%s\n" % b for b in bundles), 1)
    for root in args.roots:
        cone += '\n#cone %s "%s"\n' % (root, os.path.join(out, "cone", root + ".txt"))
    path = os.path.join(out, "cone", "Check.lean")
    with open(path, "w", encoding="utf-8") as f:
        f.write(cone)
    ws = os.path.abspath(args.workspace)
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ws, capture_output=True, text=True,
                               check=True).stdout.strip()
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                          check=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=os.path.join(out, "olean") + os.pathsep + lean_path)
    r = subprocess.run([lean, "--tstack=400000", path], env=env, capture_output=True, text=True)
    print(r.stdout.strip()[:4000])
    if r.returncode != 0:
        print(r.stderr.strip()[:2000])
        sys.exit(1)
    spec = importlib.util.spec_from_file_location("decl_query", os.path.join(HERE, "decl_query.py"))
    dq = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(dq)
    g = dq.Graph(args.map)
    private = {}
    for d in range(g.n):
        if g.flags[d] & dq.F_PRIVATE:
            mod = g.files[g.d_file[d]][:-5].replace(os.sep, ".")
            for name in g.names[d]:
                private[(mod, name)] = d
    for root in args.roots:
        used, unmatched = set(), []
        with open(os.path.join(out, "cone", root + ".txt"), encoding="utf-8") as f:
            for line in f:
                kind, name = line.rstrip("\n").split("\t", 1)
                d = None
                if name.startswith("_private."):
                    mod, _, rest = name[len("_private."):].partition(".0.")
                    parts = rest.split(".")
                    while parts and d is None:
                        d = private.get((mod, ".".join(parts)))
                        if d is None:
                            d = g.arch.get(".".join(parts))
                        parts = parts[:-1]
                else:
                    parts = name.split(".")
                    while parts and d is None:
                        d = g.arch.get(".".join(parts))
                        parts = parts[:-1]
                if d is None:
                    unmatched.append(name)
                else:
                    used.add(d)
        static = g.closure([g.find(root)], "M")
        lines = sum(g.d_lines[d] for d in used)
        files = len({g.d_file[d] for d in used})
        print("%s: the kernel's list has %d source declarations in %d files, %d lines; the map's estimate was %d "
              "declarations, %d lines; %d of the kernel's are outside the estimate; %d constants not matched to a "
              "declaration (%s)" % (root, len(used), files, lines, sum(static), sum(g.d_lines[d] for d in range(g.n) if static[d]),
                                    sum(1 for d in used if not static[d]), len(unmatched), ", ".join(unmatched[:5])))
        with open(os.path.join(out, "cone", root + ".decls.json"), "w") as f:
            json.dump(sorted(used), f)


if __name__ == "__main__":
    main()
