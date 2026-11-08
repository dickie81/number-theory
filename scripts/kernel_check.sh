#!/usr/bin/env bash
# Re-checks a theorem's proof, with every constant it depends on, by kernels other than the build's.
#
# Usage: scripts/kernel_check.sh [MODULE THEOREM]
#   default: LinnikCGLDensity LinnikCGLDensity.cglDensity. MODULE must be built first (`lake build MODULE`).
#
# The pinned toolchain ships an exporter and external type checkers in its bin/. The script:
#  1. checks the checkers. A module adds `bogus : False := True.intro` with `debug.skipKernelTC` on, and proves
#     `uses_bogus : False` from it. `#print axioms` reports that `uses_bogus` depends on no axioms; every check
#     below must reject it;
#  2. exports THEOREM with every constant it depends on (`leanexport MODULE -- THEOREM`, lean4export's NDJSON);
#  3. checks the export with Lean's kernel (`leanchecker --from-export`), nanoda (an independent kernel in Rust,
#     with only propext, Classical.choice and Quot.sound permitted and any other axiom a hard error), and con-leche
#     and con-ron in their `--verified` mode;
#  4. replays the same constants, from the .olean files, into an empty kernel environment
#     (scripts/lean/ReplayClosure.lean, as `leanchecker --fresh` does for a whole module).
# Every step must pass. It prints each checker's verdict, the time and the export's size. The export goes to a
# temporary directory, removed at the end.
#
# lean4lean, also in the toolchain's bin/, reads only .olean files, and not this toolchain's ("incompatible header"),
# so it is not run.
set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$ROOT"
MOD=${1:-LinnikCGLDensity}
THM=${2:-LinnikCGLDensity.cglDensity}
BIN="$(lean --print-prefix)/bin"
for b in leanexport leanchecker nanoda_bin con-leche con-ron; do
  [ -x "$BIN/$b" ] || { echo "kernel_check: the toolchain has no $b ($BIN)" >&2; exit 2; }
done
export PATH="$BIN:$PATH"
LEAN_PATH=$(lake env printenv LEAN_PATH)
export LEAN_PATH
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

nanoda_config() {  # export file -> path of a nanoda configuration for it
  cat > "$TMP/nanoda.json" <<EOF
{"export_file_path": "$1", "use_stdin": false,
 "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
 "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true,
 "print_success_message": true}
EOF
  echo "$TMP/nanoda.json"
}

check() {  # NAME COMMAND...: runs COMMAND, prints its verdict line, exit code and time, returns its exit code
  local name=$1 t0=$SECONDS rc=0 line
  shift
  "$@" > "$TMP/out" 2>&1 || rc=$?
  # The verdict: a checker's acceptance line, else its first line of failure, else its last line.
  line=$(grep -m1 -E 'accepts the solution|accepted [0-9]+ declarations|^Checked [0-9]+ declarations|REPLAY PASS' \
    "$TMP/out" || grep -m1 -i -E 'reject|invalid|mismatch|panicked|error|FAIL' "$TMP/out" || tail -1 "$TMP/out")
  echo "  $name: exit $rc, $((SECONDS - t0)) s: ${line:0:160}"
  return $rc
}

echo "1. A false theorem added without the kernel"
mkdir -p "$TMP/bogus"
cat > "$TMP/bogus/Bogus.lean" <<'EOF'
import Lean
open Lean

set_option debug.skipKernelTC true in
run_meta do
  addDecl <| .thmDecl { name := `bogus, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }

theorem uses_bogus : False := bogus

#print axioms uses_bogus
EOF
(cd "$TMP/bogus" && lean -o Bogus.olean Bogus.lean) | grep -q "'uses_bogus' does not depend on any axioms" \
  || { echo "kernel_check: #print axioms did not pass the bogus theorem; the control is broken" >&2; exit 1; }
echo "  #print axioms: 'uses_bogus' does not depend on any axioms"
LEAN_PATH="$TMP/bogus" leanexport Bogus -- uses_bogus > "$TMP/bogus.ndjson"
cfg=$(nanoda_config "$TMP/bogus.ndjson")
for c in "leanchecker --from-export $TMP/bogus.ndjson" "nanoda_bin $cfg" "con-leche --verified $TMP/bogus.ndjson" \
         "con-ron --verified $TMP/bogus.ndjson"; do
  # shellcheck disable=SC2086
  if check "${c%% *}" $c; then echo "kernel_check: ${c%% *} accepted the bogus theorem" >&2; exit 1; fi
done
if check replay env LEAN_PATH="$TMP/bogus:$LEAN_PATH" lean --run scripts/lean/ReplayClosure.lean Bogus uses_bogus
then echo "kernel_check: the replay accepted the bogus theorem" >&2; exit 1; fi

echo "2. Export $THM with every constant it depends on"
t0=$SECONDS
leanexport "$MOD" -- "$THM" > "$TMP/closure.ndjson"
echo "  leanexport: $((SECONDS - t0)) s, $(du -h "$TMP/closure.ndjson" | cut -f1), $(wc -l < "$TMP/closure.ndjson") records"

echo "3. Check the export"
check "Lean's kernel (leanchecker --from-export)" leanchecker --from-export "$TMP/closure.ndjson"
check "nanoda" nanoda_bin "$(nanoda_config "$TMP/closure.ndjson")"
check "con-leche --verified" con-leche --verified "$TMP/closure.ndjson"
check "con-ron --verified" con-ron --verified "$TMP/closure.ndjson"

echo "4. Replay the same constants into an empty kernel environment"
check replay lean --run scripts/lean/ReplayClosure.lean "$MOD" "$THM"
grep -E '^\S+: [0-9]+ constants' "$TMP/out" | sed 's/^/  /'
echo "KERNEL CHECK PASS: $THM"
