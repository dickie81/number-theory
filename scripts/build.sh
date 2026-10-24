#!/usr/bin/env bash
# `lake build` with a limit on how many modules compile at once.
#
# Usage: scripts/build.sh [arguments of lake build]
#
# Lake runs about as many module compiles at once as there are cores. The compiles of modules that import Mathlib
# share its files, but each certificate part (`lib/pnt/SieveCert*P<k>.lean`) can use about 5 GiB of private memory.
# This script points Lake at a copy of the toolchain in `.lake/sysroot`. The copy links to the real toolchain
# throughout, except that its `lean` is `scripts/lean-slots.sh`. That wrapper lets at most LEAN_SLOTS module compiles
# run at once (default: the number of cores), with at most LEAN_HEAVY certificate parts among them (default 2). It
# also deletes each module's setup file after a successful compile. The compiler is the toolchain's own, so the build
# and its traces are those of a plain `lake build`.
#
# It needs `flock` (util-linux; on macOS, `brew install flock`).
set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$ROOT"
command -v flock >/dev/null || { echo "scripts/build.sh needs flock; or run plain \`lake build\`" >&2; exit 2; }

PREFIX=$(lean --print-prefix)
SYS="$ROOT/.lake/sysroot"
rm -rf "$SYS"
mkdir -p "$SYS/bin" "$SYS/locks"
for x in "$PREFIX"/*; do
  [ "$(basename "$x")" = bin ] || ln -s "$x" "$SYS/$(basename "$x")"
done
for x in "$PREFIX"/bin/*; do
  [ "$(basename "$x")" = lean ] || ln -s "$x" "$SYS/bin/$(basename "$x")"
done
ln -s "$ROOT/scripts/lean-slots.sh" "$SYS/bin/lean"

export LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT="$SYS"
export LEAN_SLOTS_REAL="$PREFIX/bin/lean" LEAN_SLOTS_LOCKS="$SYS/locks"
export LEAN_SLOTS="${LEAN_SLOTS:-$(getconf _NPROCESSORS_ONLN)}" LEAN_HEAVY="${LEAN_HEAVY:-2}"
echo "scripts/build.sh: at most $LEAN_SLOTS compiles at once, at most $LEAN_HEAVY of them certificate parts"
exec lake build "$@"
