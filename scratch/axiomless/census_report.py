#!/usr/bin/env python3
"""Tables from the output of Census.lean.

    python3 scratch/axiomless/census_report.py OUT.tsv [--area-depth N] [--top N]

Prints, for the theorems of the census: how many depend on each set of axioms; how many are free of axioms, have
a statement free of axioms but a proof that is not, or have a statement that already rests on axioms; the same by
area of the library; the constants that name an axiom themselves; and the deepest theorems that are free of axioms.
"""
import sys
from collections import Counter, defaultdict

def load(path):
    axioms, rows = {}, []
    with open(path, encoding="utf-8") as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            if p[0] == "#axiom":
                axioms[int(p[1])] = p[2]
            else:
                rows.append((p[0], p[1], p[2], int(p[3]), int(p[4]), int(p[5]), int(p[6]), p[7] == "1"))
    return axioms, rows

def names(mask, axioms):
    out = [axioms[k] for k in sorted(axioms) if mask >> k & 1]
    return " + ".join(out) if out else "(none)"

def area(module, depth):
    return ".".join(module.split(".")[:depth])

def main():
    args = sys.argv[1:]
    depth, top = 2, 25
    if "--area-depth" in args:
        i = args.index("--area-depth"); depth = int(args[i + 1]); del args[i:i + 2]
    if "--top" in args:
        i = args.index("--top"); top = int(args[i + 1]); del args[i:i + 2]
    axioms, rows = load(args[0])
    kinds = Counter(r[1] for r in rows)
    print(f"{len(rows)} constants: " + ", ".join(f"{v} {k}" for k, v in kinds.most_common()))
    for label, keep in (("all theorems", lambda r: r[1] == "theorem"),
                        ("theorems with a name a person wrote", lambda r: r[1] == "theorem" and not r[7]),
                        ("definitions with a name a person wrote", lambda r: r[1] == "def" and not r[7])):
        sel = [r for r in rows if keep(r)]
        print(f"\n== {label}: {len(sel)}")
        c = Counter(r[3] for r in sel)
        for mask, v in c.most_common(12):
            print(f"  {v:8d}  {100 * v / len(sel):5.1f}%  {names(mask, axioms)}")
    thms = [r for r in rows if r[1] == "theorem" and not r[7]]
    free = [r for r in thms if r[3] == 0]
    proof_only = [r for r in thms if r[3] != 0 and r[4] == 0]
    stmt = [r for r in thms if r[4] != 0]
    n = len(thms)
    print(f"\n== three classes (theorems with a name a person wrote, {n})")
    print(f"  free of axioms:                           {len(free):8d}  {100 * len(free) / n:5.1f}%")
    print(f"  statement free, proof uses axioms:        {len(proof_only):8d}  {100 * len(proof_only) / n:5.1f}%")
    print(f"  statement rests on axioms:                {len(stmt):8d}  {100 * len(stmt) / n:5.1f}%")
    print(f"\n== by area (depth {depth}): theorems, % free, % statement free only, % statement on axioms")
    by = defaultdict(lambda: [0, 0, 0])
    for r in thms:
        a = by[area(r[2], depth)]
        a[0 if r[3] == 0 else 1 if r[4] == 0 else 2] += 1
    for a, (x, y, z) in sorted(by.items(), key=lambda kv: -sum(kv[1])):
        t = x + y + z
        if t >= 200:
            print(f"  {a:40s} {t:7d}  {100 * x / t:5.1f}  {100 * y / t:5.1f}  {100 * z / t:5.1f}")
    print("\n== constants that name an axiom themselves")
    for k in sorted(axioms):
        users = [r for r in rows if r[5] >> k & 1]
        if users:
            print(f"  {axioms[k]}: {len(users)} constants ({sum(1 for r in users if not r[7])} with a name a person wrote)")
    print(f"\n== the {top} deepest theorems free of axioms")
    for r in sorted(free, key=lambda r: -r[6])[:top]:
        print(f"  {r[6]:5d}  {r[0]}   [{r[2]}]")
    print(f"\n  deepest theorem of all: " + ", ".join(f"{r[0]} ({r[6]})" for r in sorted(thms, key=lambda r: -r[6])[:3]))

if __name__ == "__main__":
    main()
