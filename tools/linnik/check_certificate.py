#!/usr/bin/env python3
"""Regenerate the Linnik certificate at 43/20 and compare its files with lib/pnt byte for byte.

The certificate is that of the Linnik paper's Theorem 1.2, `Linnik21500.linnik_21500` (L = 2150/1000 = 43/20, the
search with the reversal through the largest prime, led by hints): `hint_cert.py 21500 --check --cplan` plans the
search again, cuts the plan into parts, writes the hints of each part, runs every part through the kernel's search
led by its hints (the script's mirror of `SieveAd.solveD`), and compares SieveHint21500.lean, every
SieveHint21500P<k>.lean and Linnik21500.lean with the files in lib/pnt; a file that differs, or a part file that
exists on one side only, fails the check. With `--cplan` the search of each cell of the first prime is the C
planner's (`cplan.py`, compiled once by a C compiler with `__int128`, GCC or Clang, as on CI's runner): the same plans
as the Python planner's, which takes ten times as long (16 November 2026, on four busy cores: 88 seconds against
882).

The certificate of Theorem 1.1, at 21/10 (`hint_cert.py 21000`), is not checked here: its plan takes hours on
several machines. The certificates at 11/5, 219/100, 218/100 and 2115/1000 are in the git history at
commit 76abe3c.

`--inputs` prints, one glob pattern a line from the repository's root, the files that the check reads: this script,
the generators it runs and the files of this directory that they import or compile, the files of lib/pnt that they
read when they start (`READS`), and the files of lib/pnt whose names hold the certificate's tag, which include every
file it compares. Only a change to one of them can change its outcome, so CI runs the check only then (the job
`changes` of .github/workflows/ci.yml).
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# tag: the generator that regenerates and compares a certificate's files, and its arguments
CERTS = {'21500': ['hint_cert.py', '21500', '--check', '--cplan']}
# the files of this directory, other than scripts, that the generators read: the C planner, which `--cplan` compiles
EXTRA = ['cplan/*']
# the files of lib/pnt that the scripts read when they start: the curve `ghx` (`res_test.py`, through
# `route_limits.parse`) and the leaves' region `leafXR` (`tree_cert.py`)
READS = ['lib/pnt/SieveCurveHx.lean', 'lib/pnt/SieveLeafZoneXDefs.lean']


def check(tag):
    gen = CERTS[tag]
    r = subprocess.run([sys.executable, os.path.join(HERE, gen[0]), *gen[1:]], capture_output=True, text=True)
    print(r.stdout.rstrip())
    if r.returncode:
        print(r.stderr.rstrip())
    ok = r.returncode == 0 and f'SEARCH {tag} PASS' in r.stdout
    print(f'CERTIFICATE {tag}', 'PASS' if ok else 'FAIL')
    return ok


def local_imports(script):
    """The scripts of this directory that a script imports."""
    text = open(os.path.join(HERE, script), encoding='utf-8').read()
    return {m + '.py' for m in re.findall(r'^\s*(?:from|import)\s+(\w+)', text, re.M)
            if os.path.exists(os.path.join(HERE, m + '.py'))}


def inputs():
    """The files that the check reads, as glob patterns from the repository's root (see the module's docstring)."""
    todo = [os.path.basename(__file__)] + [gen[0] for gen in CERTS.values()]
    seen = set()
    while todo:
        script = todo.pop()
        if script not in seen:
            seen.add(script)
            todo += local_imports(script)
    here = os.path.relpath(HERE, os.path.join(HERE, '..', '..')).replace(os.sep, '/')
    return ([f'{here}/{s}' for s in sorted(seen) + EXTRA] + READS
            + [f'lib/pnt/*{tag}*.lean' for tag in CERTS])


def main():
    if sys.argv[1:] == ['--inputs']:
        print('\n'.join(inputs()))
        return 0
    tags = sys.argv[1:] or list(CERTS)
    for t in tags:
        if t not in CERTS:
            print(f'unknown certificate {t}; known: {", ".join(CERTS)}')
            return 2
    results = [check(t) for t in tags]
    return 0 if all(results) else 1


if __name__ == '__main__':
    sys.exit(main())
