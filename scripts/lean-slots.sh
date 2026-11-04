#!/usr/bin/env bash
# The `lean` of scripts/build.sh's copy of the toolchain.
#
# A module compile (an invocation with `-o`) waits for one of LEAN_SLOTS slots. A heavy module also waits for one of
# LEAN_HEAVY heavy slots. The heavy modules are the certificate parts (`SieveCert…P<k>.lean`), each of which can use
# about 5 GiB of private memory, and the modules marked heavy (below). Every other invocation (`--githash`,
# `--print-prefix`, …) goes straight to the real lean.
#
# A module is marked by a line of its source that starts with one of these (a `:` marker is followed by the reason):
#   `-- heavy:`          it is heavy (the CmFinR* kernel checks of lib/core, about 3 GiB each);
#   `-- exclusive-heavy` it holds every heavy slot, so it runs alone among the heavy modules (a certificate part with a
#                        part that can use over 7 GiB);
#   `-- alone:`          it holds every heavy slot and every slot, so nothing else compiles while it does (the CmMomC*
#                        kernel checks, about 8 GiB each: two of them, or one beside a few others, exhaust 16 GB).
# A compile that holds every slot of a kind takes them in order, heavy slots first, so two of them cannot deadlock.
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

hold() {  # hold BASEFD PREFIX COUNT: hold every lock file PREFIX1 … PREFIXCOUNT, in order, waiting for each
  local i
  for i in $(seq 1 "$3"); do
    eval "exec $(($1 + i))>\"\$LOCKS/$2$i.lock\""
    flock "$(($1 + i))"
  done
}

heavy=0 excl=0 alone=0
for a in "$@"; do
  case "$a" in
    *.lean)
      case "$a" in *SieveCert*P[0-9]*.lean) heavy=1 ;; esac
      [ -f "$a" ] || continue
      case "$(grep -m1 -oE '^-- (heavy:|exclusive-heavy|alone:)' "$a")" in
        '-- heavy:') heavy=1 ;;
        '-- exclusive-heavy') heavy=1 excl=1 ;;
        '-- alone:') heavy=1 excl=1 alone=1 ;;
      esac ;;
  esac
done
if [ "$excl" = 1 ]; then
  hold 10 heavy "${LEAN_HEAVY:-2}"
elif [ "$heavy" = 1 ]; then
  until take 7 heavy "${LEAN_HEAVY:-2}"; do sleep 2; done
fi
if [ "$alone" = 1 ]; then
  hold 100 slot "${LEAN_SLOTS:-2}"
else
  until take 9 slot "${LEAN_SLOTS:-2}"; do sleep 2; done
fi

setup= prev=
for a in "$@"; do
  [ "$prev" = --setup ] && setup=$a
  prev=$a
done
"$REAL" "$@"
rc=$?
[ "$rc" -eq 0 ] && [ -n "$setup" ] && rm -f -- "$setup"
exit "$rc"
