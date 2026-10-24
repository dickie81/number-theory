#!/usr/bin/env python3
"""Regenerate the Linnik paper's certificate files and compare them with lib/pnt byte for byte.

The certificate of `SieveCert.total2_lt_22475R` (L = 899/400, the window [41335/100000, 48069/100000], n = 300) is
generated in two steps:

1. `mirror2.py 41335 48069 300 CELLS.json` evaluates the refined certificate's definitions (SieveCert2Defs.lean) cell
   by cell in exact integers, cross-checks the totals against `route_limits.replay` and
   `refine_k2_probe.replay2`, and writes each cell's cost and kernel work (about two minutes);
2. `gen_22475r.py CELLS.json OUTDIR` cuts the certificate into parts and writes the Lean files.

This script runs both in a temporary directory and compares SieveGrid22475R.lean, every SieveCert22475RP<k>.lean and
SieveCert22475R.lean with the files in lib/pnt. A file that differs, or a part file that exists on one side only,
fails the check.
"""
import filecmp
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
PNT = os.path.join(HERE, '..', '..', 'lib', 'pnt')


def names(d):
    return sorted(f for f in os.listdir(d)
                  if re.fullmatch(r'SieveGrid22475R\.lean|SieveCert22475R(P\d+)?\.lean', f))


def main():
    with tempfile.TemporaryDirectory() as tmp:
        cells, out = os.path.join(tmp, 'cells.json'), os.path.join(tmp, 'out')
        for args in ([os.path.join(HERE, 'mirror2.py'), '41335', '48069', '300', cells],
                     [os.path.join(HERE, 'gen_22475r.py'), cells, out]):
            r = subprocess.run([sys.executable, *args], capture_output=True, text=True)
            print(r.stdout.rstrip())
            if r.returncode:
                print(r.stderr.rstrip())
                print('CERTIFICATE FAIL')
                return 1
        here, there = names(out), names(PNT)
        only = sorted(set(here) ^ set(there))
        same = [f for f in here if f in there and filecmp.cmp(os.path.join(out, f), os.path.join(PNT, f), shallow=False)]
        bad = [f for f in here if f in there and f not in same]
        print(f'{len(here)} files generated, {len(there)} in lib/pnt: {len(same)} identical, {len(bad)} differ, '
              f'{len(only)} on one side only')
        for f in bad:
            print('  DIFFERS:', f)
        for f in only:
            print('  ONE SIDE ONLY:', f)
        ok = not bad and not only and len(same) == len(there) > 0
        print('CERTIFICATE', 'PASS' if ok else 'FAIL')
        return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
