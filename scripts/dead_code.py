#!/usr/bin/env python3
"""The dead-code check: the library keeps no declaration that its printed theorems do not use, and prints no theorem
with a closed hypothesis that no result uses.

    python3 scripts/dead_code.py               # after `lake build Check CheckAll CheckZeta23`
    python3 scripts/dead_code.py --json OUT    # also write the findings, with each declaration's lines, to OUT

The roots are the theorems that lib/check/Check.lean, CheckAll.lean and CheckZeta23.lean print. `lake exe deadcode`
(scripts/lean/DeadCode.lean) imports the check files, Check with CheckAll and then CheckZeta23, which CheckAll cannot
import, and walks what the roots use, through types and proofs. The check fails if:

1. a declaration of lib/core, lib/pnt, lib/zeta23 or lib/check is used by no root (Lean's generated declarations and
   the meta level, macros and syntax, aside), or a module of those directories is imported by no check file;
2. a root has a closed hypothesis, a proposition or an instance that mentions none of its variables (such as
   `RiemannHypothesis`, `SieveRoute.TypeIIAt` or `[SieveCert.Grid]`), and no other root without one, or in
   `CONDITIONAL` below, uses it: a lemma of a route that nothing proves any more.

lib/dh is a library of its own, imported by no check file; the check counts its modules but does not judge them.
"""
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIRS = ["core", "pnt", "zeta23", "check"]
CHECKS = ["Check", "CheckAll", "CheckZeta23"]

# The printed results that are conditional on purpose, on a statement the library does not prove. A root that one of
# these uses passes too.
CONDITIONAL = {
    "LinnikGRH.linnik_two_of_GRH",                   # Linnik's theorem with every exponent above 2, under GRH
    "LinnikGRH.charDensity_two_of_GRH",               # the density exponent 2, under GRH
    "Subconvexity.lindelof_of_RH",                    # the Lindelöf hypothesis from RH
    "HalfPlaneJoinsPNT.psiOmegaSqrt_of_not_RH",       # ψ(x) − x = Ω(x^{1/2+δ}) if RH fails
    "InghamDensity.densityHypothesis_of_lindelof",    # the density hypothesis from Lindelöf
    "LinnikWeylBridge.weylBound_of_PYWeyl",           # under Petrow and Young's Weyl bound for every character
    "LinnikStairs7.charDensity_hy_0",                 # Huxley's steps above 5/6, under the same bound
    "LinnikStairs7.charDensity_hy_top",
}


def modules(d):
    return sorted(f[:-5] for f in os.listdir(os.path.join(ROOT, "lib", d)) if f.endswith(".lean"))


def printed(check):
    text = open(os.path.join(ROOT, "lib", "check", check + ".lean"), encoding="utf-8").read()
    return re.findall(r"^#print axioms (\S+)", text, re.M)


def run(tmp, imports):
    r = subprocess.run(["lake", "exe", "deadcode", os.path.join(tmp, "ours"), os.path.join(tmp, "roots"),
                        os.path.join(tmp, "allow")] + imports, cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"deadcode {' '.join(imports)} failed:\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
    return json.loads(r.stdout.strip().splitlines()[-1])


def main():
    ours = [m for d in DIRS for m in modules(d)]
    roots = sorted({n for c in CHECKS for n in printed(c)})
    with tempfile.TemporaryDirectory() as tmp:
        for name, items in (("ours", ours), ("roots", roots), ("allow", sorted(CONDITIONAL))):
            open(os.path.join(tmp, name), "w", encoding="utf-8").write("\n".join(items) + "\n")
        runs = [run(tmp, ["Check", "CheckAll"]), run(tmp, ["CheckZeta23"])]
    # a declaration is dead if no run that imports its module reaches it
    present = [set(r["ours"]) for r in runs]
    dead = {}
    for r, mods in zip(runs, present):
        for d in r["dead"]:
            dead.setdefault(d["name"], {"decl": d, "mods": set()})["mods"].add(r["modules"][0])
    deadDecls = []
    for name, e in sorted(dead.items()):
        mod = e["decl"]["module"]
        if all(name in {d["name"] for d in r["dead"]} for r, mods in zip(runs, present) if mod in mods):
            deadDecls.append(e["decl"])
    unimported = sorted(set(ours) - set().union(*present))
    # the roots with a closed hypothesis that no root without one, or in CONDITIONAL, uses
    unused = {}
    for r in runs:
        for x in r["roots"]:
            if x["closed"] and x["name"] not in CONDITIONAL:
                if x["usedBy"]:
                    unused[x["name"]] = None
                else:
                    unused.setdefault(x["name"], x)
    unusedRoots = sorted((x for x in unused.values() if x), key=lambda x: x["name"])
    stale = sorted(CONDITIONAL - set(roots))
    dh = len(modules("dh"))
    byMod = {}
    for d in deadDecls:
        byMod.setdefault(d["module"], []).append(d)
    for m in sorted(byMod):
        print(f"{m}: {len(byMod[m])} unused: " + ", ".join(d["name"] for d in byMod[m][:12])
              + (" …" if len(byMod[m]) > 12 else ""))
    for m in unimported:
        print(f"{m}: imported by no check file")
    for x in unusedRoots:
        print(f"{x['name']} ({x['module']}): printed, with the closed hypotheses {', '.join(x['closed'][:3])}, "
              f"and used by no result")
    for n in stale:
        print(f"{n}: in CONDITIONAL but printed by no check file")
    live = sum(r["live"] for r in runs)
    ok = not (deadDecls or unimported or unusedRoots or stale)
    print(f"dead_code: {len(roots)} roots; {len(deadDecls)} unused declarations in {len(byMod)} modules, "
          f"{len(unimported)} modules imported by no check file, {len(unusedRoots)} conditional roots that no result "
          f"uses; lib/dh ({dh} modules) not judged")
    print("DEAD CODE PASS" if ok else "DEAD CODE FAIL")
    if "--json" in sys.argv:
        json.dump({"dead": deadDecls, "unimported": unimported, "unusedRoots": unusedRoots, "stale": stale},
                  open(sys.argv[sys.argv.index("--json") + 1], "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
