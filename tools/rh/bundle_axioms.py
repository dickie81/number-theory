#!/usr/bin/env python3
"""Look at every declaration that a bundled build compiled for `sorry` and for axioms.

    python3 -I tools/rh/bundle_axioms.py --out OUT [--workspace WS] [--bundle NAME ...]

`bundle_check.py` answers for one theorem, by walking what it rests on. This answers for the whole build, without
importing it: `lean/Axioms.lean` reads each bundle's `.olean` as data and reports the constants that are declared
as axioms (a declaration that the kernel refused is kept as one), those that name `sorryAx` (a declaration whose
elaboration failed) and those that name an axiom of Lean or Mathlib other than `propext`, `Classical.choice` and
`Quot.sound` (`Lean.ofReduceBool`, of `native_decide`). It prints them by bundle, and what the build as a whole
comes to. A build with none, every bundle of which `bundle_recheck.py` has accepted, has no theorem that rests on
more than those three axioms.
"""
import argparse
import importlib.util
import json
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def main():
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--workspace", default=os.path.join(ext, "native-ws"))
    ap.add_argument("--bundle", nargs="*", default=[], help="these bundles only")
    args = ap.parse_args()
    out = os.path.abspath(args.out)
    last = {}
    with open(os.path.join(out, "state.jsonl")) as f:
        for line in f:
            r = json.loads(line)
            last[r["bundle"]] = r
    names = [b for b in sorted(last) if last[b]["ok"] and last[b]["files"]]
    if args.bundle:
        names = [b for b in names if b in set(args.bundle)]
    os.makedirs(os.path.join(out, "cone"), exist_ok=True)
    job = os.path.join(out, "cone", "axioms.json")
    with open(job, "w") as f:
        json.dump(dict(files=[os.path.join(out, "olean", "B", b + ".olean") for b in names]), f)
    ws = os.path.abspath(args.workspace)
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                          check=True).stdout.strip()
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ws, capture_output=True, text=True,
                               check=True).stdout.strip()
    p = subprocess.run([lean, "--run", os.path.join(HERE, "lean", "Axioms.lean"), job], capture_output=True,
                       text=True, env=dict(os.environ, LEAN_PATH=lean_path))
    if p.returncode != 0:
        raise SystemExit("Axioms.lean failed: " + (p.stderr or p.stdout)[-800:])
    n_ax = n_sorry = n_other = 0
    for line in p.stdout.split("\n"):
        if not line.startswith("{"):
            continue
        r = json.loads(line)
        if "olean" in r:
            b = os.path.basename(r["olean"])[:-len(".olean")]
            n_ax += len(r["axioms"])
            n_sorry += len(r["sorry"])
            n_other += len(r["other"])
            print("%s  axioms %d  with sorry %d  with another axiom %d  %s"
                  % (b, len(r["axioms"]), len(r["sorry"]), len(r["other"]),
                     " ".join((r["axioms"] + r["sorry"] + r["other"])[:4])))
        else:
            print("%d bundles, %d constants: %d declared as axioms, %d that name sorryAx, %d that name an axiom other "
                  "than the three (the axioms of Lean and Mathlib: %s)"
                  % (r["files"], r["constants"], n_ax, n_sorry, n_other, " ".join(sorted(r["known"]))))


if __name__ == "__main__":
    main()
