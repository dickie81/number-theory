#!/usr/bin/env python3
"""recut_cache.py IN OUT [--lam X] [--split2 J]: the cells kept in the cache IN by `hint_cert.py --cache`, cut as
`hint_cert.cut` cuts them now, into OUT, with the certificate's settings at 2100/1000 (lam 0.3, `--split2 1` unless
given). A heavy cell cut before `cut` took a cell that the plan splits in two as its two halves kept such a cell
whole, as one part of up to 250 predicted seconds; its entry has the parts' hints, not the plan, and the plan is read
back from them by the kernel's search (`cplan.recut_cells`, `cplan/gen.h`) and cut again: the same plan, cost and
counts, smaller parts. A light cell is copied as it is. Each cell is checked: the cost of its pieces is the plan's,
and every part passes the kernel's mirror (`dPart`) as it is written."""
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
import cplan  # noqa: E402
from cgen_test import settings  # noqa: E402


def main():
    a = sys.argv[1:]
    src, dst = a[0], a[1]
    par_ = settings(a, False)
    sys.setrecursionlimit(100000)
    os.makedirs(dst, exist_ok=True)
    names = sorted(n for n in os.listdir(src) if n.endswith('.pkl'))
    t0 = time.time()
    worst = 0.0
    for n in names:
        out = os.path.join(dst, n)
        if os.path.exists(out):
            continue
        with open(os.path.join(src, n), 'rb') as fh:
            r = pickle.load(fh)
        before = max(p[7] for p in r[4]) if r[0] == 'heavy' else 0.0
        if r[0] == 'heavy':
            r = cplan.recut_cells(par_, [r])[0]
            worst = max(worst, max(p[7] for p in r[4]))
            print(f'{n}: {r[0]}, cost {r[-1][0] / tc.K:.6f}, the largest part {before:.1f} s -> '
                  f'{max(p[7] for p in r[4]):.1f} s ({len(r[4])} parts)', flush=True)
        with open(out + '.tmp', 'wb') as fh:
            pickle.dump(r, fh, protocol=4)
        os.replace(out + '.tmp', out)
    print(f'{len(names)} cells in {time.time() - t0:.0f} s; the largest part {worst:.1f} predicted seconds')
    return 0


if __name__ == '__main__':
    sys.exit(main())
