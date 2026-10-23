#!/usr/bin/env python3
"""Scan the library's own Lean sources (lib/core, lib/pnt, lib/dh, lib/zeta23 and lib/check) for escape hatches:
`sorry`, `admit`, `native_decide`, a declared `axiom`, `implemented_by`, `extern`, `unsafe`, `Lean.ofReduceBool`,
`debug.skipKernelTC` and `#exit`. Comments and strings are not stripped, so a mention in a docstring is reported
too; each hit is printed for review, and any hit fails.

The vendored upstreams (lib/vendor) are not scanned: PrimeNumberTheoremAnd's Wiener.lean holds two lemmas proved by
`sorry`, outside the dependency cone of every theorem here. The theorems themselves are gated by
scripts/check_axioms.py, which fails on `sorryAx` and on any other axiom.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIRS = ["lib/core", "lib/pnt", "lib/dh", "lib/zeta23", "lib/check"]
PAT = re.compile(r"\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(?:private\s+|protected\s+)?axiom\s|\bimplemented_by\b"
                 r"|@\[extern\b|^\s*unsafe\s|\bofReduceBool\b|\bskipKernelTC\b|^#exit\b")


def main():
    hits, files = [], 0
    for d in DIRS:
        for f in sorted(os.listdir(os.path.join(ROOT, d))):
            if not f.endswith(".lean"):
                continue
            files += 1
            for i, line in enumerate(open(os.path.join(ROOT, d, f), encoding="utf-8"), 1):
                if PAT.search(line):
                    hits.append(f"{d}/{f}:{i}: {line.rstrip()[:160]}")
    for h in hits:
        print(h)
    print(f"{files} files scanned; {len(hits)} lines with an escape hatch")
    print("HYGIENE", "PASS" if not hits else "FAIL")
    return 0 if not hits else 1


if __name__ == "__main__":
    sys.exit(main())
