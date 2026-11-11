#!/usr/bin/env python3
"""Regenerate the Linnik certificates' files and compare them with lib/pnt byte for byte.

Three certificates are checked (with no argument, or one named by its tag):

* `22000E`: `SieveDeep.totalD_lt_22000E` (L = 11/5, the window [43457/100000, 46959/100000], n = 272, the curve `g7d`,
  the decomposition to depth 8 under the bilinear Type I rule), the paper's;
* `21900`: `Linnik21900.tree21900` (L = 219/100, the window [44260/100000, 46717/100000], a tree of Buchstab steps
  that the kernel searches for in parts);
* `21800`: `Linnik21800.tree21800` (L = 218/100, the window [45073/100000, 46472/100000], a search with role
  reversal that the kernel runs in parts).

Earlier certificates, at weaker exponents (the last, `22240R` at 278/125), are no longer in the tree; see the git
history.

The first is generated in two steps:

1. `mirror8.py W1 W2 272 11/5 CELLS.json` evaluates the certificate's definitions (SieveDeepDefs.lean) cell by cell in
   exact integers, in parallel, and writes each cell's cost and kernel work (about a minute on four cores);
2. `gen_cert8.py CELLS.json OUTDIR [--tag ...]` cuts the certificate into parts and writes the Lean files.

This script runs both in a temporary directory and compares SieveGrid<tag>.lean, every SieveCert<tag>P<k>.lean and
SieveCert<tag>.lean with the files in lib/pnt. A file that differs, or a part file that exists on one side only,
fails the check.

The second is `tree_cert.py --check`, which runs the search in Python, cuts it into parts and compares
SieveGrid21900.lean, every SieveTree21900P<k>.lean and Linnik21900.lean with the files in lib/pnt (half a minute).
The third is `rev_cert.py --check`, the same for the search with role reversal and SieveGrid21800.lean, every
SieveTree21800P<k>.lean and Linnik21800.lean (two minutes).
The fourth is `fill_cert.py --check`, the same for the search with no window and SieveFill21650.lean, every
SieveTree21650P<k>.lean and Linnik21650.lean (five minutes).
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
    '22000E': (['mirror8.py', '43457', '46959', '272', '11/5'],
               ['gen_cert8.py', '--tag', '22000E', '--curve', 'g7d', '--typeii', 'SieveTypeIIU22000D.typeII_22000d']),
}


# tag: the generator of a tree's files and its arguments
TREES = {'21900': ['tree_cert.py', '--check'], '21800': ['rev_cert.py', '--check'],
         '21650': ['fill_cert.py', '--check']}


def check_tree(tag):
    gen = TREES[tag]
    r = subprocess.run([sys.executable, os.path.join(HERE, gen[0]), *gen[1:]], capture_output=True, text=True)
    print(r.stdout.rstrip())
    if r.returncode:
        print(r.stderr.rstrip())
    print(f'CERTIFICATE {tag}', 'PASS' if r.returncode == 0 else 'FAIL')
    return r.returncode == 0


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
    tags = [a for a in sys.argv[1:]] or list(CERTS) + list(TREES)
    for t in tags:
        if t not in CERTS and t not in TREES:
            print(f'unknown certificate {t}; known: {", ".join(list(CERTS) + list(TREES))}')
            return 2
    results = [check(t) if t in CERTS else check_tree(t) for t in tags]
    if len(tags) > 1:
        print('CERTIFICATE', 'PASS' if all(results) else 'FAIL', '(' + ', '.join(tags) + ')')
    return 0 if all(results) else 1


if __name__ == '__main__':
    sys.exit(main())
