#!/usr/bin/env python3
"""Census of the declarations a theorem's proof uses, by module.

Usage: census.py MODULE CONSTANT [--all]

Elaborates a file that imports MODULE and walks the declarations CONSTANT depends on: the constants in each one's
type and value, transitively, as `ConstantInfo.getUsedConstantsAsSet` reads them (an inductive type brings its
constructors, a recursor its types). It prints, for each module of the library's own layers (lib/core, lib/pnt,
lib/dh, lib/zeta23), the number of its declarations in that set; with --all, every module, Mathlib's and the
vendored libraries' included. MODULE must be built first (`lake build MODULE`).

The census counts what the proof terms mention, so it is an upper bound on what the proof needs: a declaration whose
use is only in a proof of a fact also proved another way is counted.
"""
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAYERS = ["core", "pnt", "dh", "zeta23"]

LEAN = """import {module}
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut seen : NameSet := {{}}
  let mut todo : Array Name := #[`{constant}]
  unless env.contains `{constant} do
    throwError "unknown constant {constant}"
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet do
        unless seen.contains m do todo := todo.push m
  let mut counts : Std.HashMap Name Nat := {{}}
  for n in seen do
    if let some idx := env.getModuleIdxFor? n then
      let mn := env.header.moduleNames[idx]!
      counts := counts.insert mn (counts.getD mn 0 + 1)
  IO.println s!"CENSUS {{seen.size}} declarations"
  for (mn, c) in counts.toList do
    IO.println s!"MODULE {{mn}} {{c}}"
"""


def own_modules():
    return {f[:-5]: d for d in LAYERS for f in os.listdir(os.path.join(ROOT, "lib", d)) if f.endswith(".lean")}


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if len(args) != 2:
        print(__doc__)
        return 2
    module, constant = args
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, encoding="utf-8") as fh:
        fh.write(LEAN.format(module=module, constant=constant))
        path = fh.name
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.remove(path)
    out = r.stdout + r.stderr
    total = re.search(r"CENSUS (\d+) declarations", out)
    rows = [(m.group(1), int(m.group(2))) for m in re.finditer(r"^MODULE (\S+) (\d+)$", out, re.M)]
    if r.returncode or not total:
        print(out.rstrip())
        print("CENSUS FAIL")
        return 1
    own = own_modules()
    shown = rows if "--all" in sys.argv else [(m, c) for m, c in rows if m in own]
    for m, c in sorted(shown, key=lambda mc: (own.get(mc[0], "~"), mc[0])):
        print(f"{own.get(m, '-'):7} {m:40} {c}")
    print(f"{constant}: {total.group(1)} declarations in {len(rows)} modules; {len([m for m, _ in rows if m in own])} "
          f"of the library's own modules")
    return 0


if __name__ == "__main__":
    sys.exit(main())
