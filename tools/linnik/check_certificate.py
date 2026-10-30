#!/usr/bin/env python3
"""Regenerate the Linnik paper's certificate files and compare them with lib/pnt byte for byte.

Two certificates are checked (with no argument, or one named by its tag):

* `22240R`: `SieveCert.total2_lt_22240R` (L = 278/125, the window [41556/100000, 47531/100000], n = 340, the curve `g7d`);
* `22000E`: `SieveDeep.totalD_lt_22000E` (L = 11/5, the window [43457/100000, 46959/100000], n = 272, the curve `g7d`,
  the decomposition to depth 8 under the bilinear Type I rule).

Earlier certificates, at weaker exponents, are no longer in the tree; see the git history.

Each is generated in two steps:

1. `mirror2.py W1 W2 340 CELLS.json` evaluates the refined certificate's definitions (SieveCert2Defs.lean) cell by cell
   in exact integers, in parallel, and writes each cell's cost and kernel work (about twenty seconds on four cores);
   for `22000E`, `mirror8.py W1 W2 272 11/5 CELLS.json` does the same for SieveDeepDefs.lean (about a minute);
2. `gen_cert.py CELLS.json OUTDIR [--tag ...]` (for `22000E`, `gen_cert8.py`) cuts the certificate into parts and
   writes the Lean files.

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

# tag: (the mirror and its arguments before CELLS.json, the generator and its arguments after OUTDIR)
CERTS = {
    '22240R': (['mirror2.py', '41556', '47531', '340'],
               ['gen_cert.py', '--tag', '22240R', '--L', '278/125', '--curve', 'g7d',
                '--typeii', 'SieveTypeIIU22240D.typeII_22240d']),
    '22000E': (['mirror8.py', '43457', '46959', '272', '11/5'],
               ['gen_cert8.py', '--tag', '22000E', '--curve', 'g7d', '--typeii', 'SieveTypeIIU22000D.typeII_22000d']),
}


def names(d, tag):
    return sorted(f for f in os.listdir(d) if re.fullmatch(rf'SieveGrid{tag}\.lean|SieveCert{tag}(P\d+)?\.lean', f))


def check(tag):
    mirror, gen = CERTS[tag]
    with tempfile.TemporaryDirectory() as tmp:
        cells, out = os.path.join(tmp, 'cells.json'), os.path.join(tmp, 'out')
        for args in ([os.path.join(HERE, mirror[0]), *mirror[1:], cells],
                     [os.path.join(HERE, gen[0]), cells, out, *gen[1:]]):
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
