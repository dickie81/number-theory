#!/usr/bin/env python3
"""Check the axioms of the papers' theorems: elaborate lib/check/Check.lean (with --all, CheckAll.lean) after
`lake build` and gate its output.

Every `#print axioms` line of the file must produce exactly one report, and every report must name only `propext`,
`Classical.choice` and `Quot.sound` (any subset), or say that the declaration depends on no axioms. Any other axiom
(`sorryAx`, `Lean.ofReduceBool`, a declared `axiom`) fails the check. Run from the repository root; it calls
`lake env lean`, so the modules the file imports must be built first.
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STD = {"propext", "Classical.choice", "Quot.sound"}


def main():
    name = "CheckAll" if "--all" in sys.argv else "Check"
    path = os.path.join("lib", "check", name + ".lean")
    want = len(re.findall(r"^#print axioms ", open(os.path.join(ROOT, path), encoding="utf-8").read(), re.M))
    r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True)
    out = r.stdout + r.stderr
    good, bad = 0, []
    for line in out.splitlines():
        m = re.search(r"'(.+)' depends on axioms: \[(.*)\]$", line)
        if m:
            axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
            (bad.append(line) if not axioms <= STD else None)
            good += axioms <= STD
        elif re.search(r"'(.+)' does not depend on any axioms$", line):
            good += 1
    print(out.rstrip())
    print(f"{name}: lean exit {r.returncode}; {want} #print axioms lines, {good} reports within "
          f"[propext, Classical.choice, Quot.sound], {len(bad)} outside")
    for line in bad:
        print("  OUTSIDE:", line)
    ok = r.returncode == 0 and not bad and good == want
    print("AXIOMS", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
