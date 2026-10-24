#!/usr/bin/env python3
"""Regenerate the Linnik paper's certificate files and compare them with lib/pnt byte for byte.

Two certificates are checked (all of them with no argument, or the one named by its tag):

* `22475R`: `SieveCert.total2_lt_22475R` (L = 899/400, the window [41335/100000, 48069/100000], n = 300, the curve `g7c`);
* `22325R`: `SieveCert.total2_lt_22325R` (L = 893/400, the window [40980/100000, 47731/100000], n = 300, the curve `g7d`).

Each is generated in two steps:

1. `mirror2.py W1 W2 300 CELLS.json` evaluates the refined certificate's definitions (SieveCert2Defs.lean) cell by cell
   in exact integers, cross-checks the totals against `route_limits.replay` and `refine_k2_probe.replay2`, and writes
   each cell's cost and kernel work (about two minutes);
2. `gen_22475r.py CELLS.json OUTDIR [--tag ...]` cuts the certificate into parts and writes the Lean files.

This script runs both in a temporary directory and compares SieveGrid<tag>.lean, every SieveCert<tag>P<k>.lean and
SieveCert<tag>.lean with the files in lib/pnt. A file that differs, or a part file that exists on one side only,
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

# tag: (W1, W2, n, extra arguments of gen_22475r.py)
CERTS = {
    '22475R': (41335, 48069, 300, []),
    '22325R': (40980, 47731, 300, ['--tag', '22325R', '--L', '893/400', '--curve', 'g7d',
                                   '--typeii', 'SieveTypeIIU22325D.typeII_22325d']),
}


def names(d, tag):
    return sorted(f for f in os.listdir(d) if re.fullmatch(rf'SieveGrid{tag}\.lean|SieveCert{tag}(P\d+)?\.lean', f))


def check(tag):
    w1, w2, n, extra = CERTS[tag]
    with tempfile.TemporaryDirectory() as tmp:
        cells, out = os.path.join(tmp, 'cells.json'), os.path.join(tmp, 'out')
        for args in ([os.path.join(HERE, 'mirror2.py'), str(w1), str(w2), str(n), cells],
                     [os.path.join(HERE, 'gen_22475r.py'), cells, out, *extra]):
            r = subprocess.run([sys.executable, *args], capture_output=True, text=True)
            print(r.stdout.rstrip())
            if r.returncode:
                print(r.stderr.rstrip())
                print(f'CERTIFICATE {tag} FAIL')
                return False
        here, there = names(out, tag), names(PNT, tag)
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
        print(f'CERTIFICATE {tag}', 'PASS' if ok else 'FAIL')
        return ok


def main():
    tags = [a for a in sys.argv[1:]] or list(CERTS)
    for t in tags:
        if t not in CERTS:
            print(f'unknown certificate {t}; known: {", ".join(CERTS)}')
            return 2
    results = [check(t) for t in tags]
    if len(tags) > 1:
        print('CERTIFICATE', 'PASS' if all(results) else 'FAIL', '(' + ', '.join(tags) + ')')
    return 0 if all(results) else 1


if __name__ == '__main__':
    sys.exit(main())
