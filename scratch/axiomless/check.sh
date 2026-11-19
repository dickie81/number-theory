#!/bin/sh
# Check the Lean files of this directory: each must compile, and every declaration that claims to be free of
# axioms must be. Needs only the pinned Lean toolchain, not Mathlib. Run from anywhere.
set -e
cd "$(dirname "$0")"
mkdir -p build
export LEAN_PATH=build
fail=0
run() { # run FILE [OLEAN]: compile, and fail on an error or on a declaration of the table that has an axiom
  out=$(lean ${2:+-o "$2"} "$1" 2>&1) || { echo "$out"; echo "FAILED: $1"; fail=1; return; }
  if echo "$out" | grep -q "error"; then echo "$out"; echo "FAILED: $1"; fail=1; return; fi
  echo "ok: $1"
}
run AxiomTools.lean build/AxiomTools.olean
lean Bare.lean | grep -c "does not depend on any axioms" | grep -qx 2 && echo "ok: Bare.lean" || { echo "FAILED: Bare.lean"; fail=1; }
# every line of Tower's table must end with the dash that stands for no axioms
out=$(lean -o build/Tower.olean Tower.lean 2>&1)
if echo "$out" | grep -v ": —$" | grep -q .; then echo "$out" | grep -v ": —$"; echo "FAILED: Tower.lean"; fail=1; else echo "ok: Tower.lean ($(echo "$out" | wc -l) declarations, none with an axiom)"; fi
run Compute.lean
run Spectroscopy.lean
exit $fail
