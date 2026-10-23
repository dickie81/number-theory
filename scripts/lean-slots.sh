#!/usr/bin/env bash
# The `lean` of scripts/build.sh's copy of the toolchain.
#
# A module compile (an invocation with `-o`) waits for one of LEAN_SLOTS slots. A certificate part
# (`SieveCert…P<k>.lean`) also waits for one of LEAN_HEAVY heavy slots, because each can use about 5 GiB of private
# memory. Every other invocation (`--githash`, `--print-prefix`, …) goes straight to the real lean.
#
# After a successful compile, the script deletes the module's setup file (the argument of `--setup`). Lake writes that
# file for the compile and does not read it again; for a module that imports Mathlib it is about 8 MB.
REAL=${LEAN_SLOTS_REAL:?set by scripts/build.sh}
case " $* " in *" -o "*) ;; *) exec "$REAL" "$@" ;; esac
LOCKS=${LEAN_SLOTS_LOCKS:?set by scripts/build.sh}

take() {  # take FD PREFIX COUNT: hold one of the lock files PREFIX1 … PREFIXCOUNT on FD
  local i
  for i in $(seq 1 "$3"); do
    eval "exec $1>\"\$LOCKS/$2$i.lock\""
    if flock -n "$1"; then return 0; fi
    eval "exec $1>&-"
  done
  return 1
}

case "$*" in
  *SieveCert*P[0-9]*.lean*) until take 7 heavy "${LEAN_HEAVY:-2}"; do sleep 2; done ;;
esac
until take 9 slot "${LEAN_SLOTS:-2}"; do sleep 2; done

setup= prev=
for a in "$@"; do
  [ "$prev" = --setup ] && setup=$a
  prev=$a
done
"$REAL" "$@"
rc=$?
[ "$rc" -eq 0 ] && [ -n "$setup" ] && rm -f -- "$setup"
exit "$rc"
