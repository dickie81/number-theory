#!/usr/bin/env python3
"""cplan_test.py [--cells I J [STEP]] [--conly] [SETTINGS] | --cache PKL…: the C planner (`cplan.py`) against the
Python planner.

With `--cells` (the cells I to J of the first prime, every STEP-th; the first cell if not given), each cell is
planned by both, `row_job`'s search with the lazy hints found and the cell planned again where one has none, and the
two are compared: the plan node by node, its cost, `W['calls']`, `W['fcalls']` and the search's counts. With
`--conly` the C planner alone is timed. SETTINGS are those of the certificate's plan at 2100/1000 unless changed:
`--L a/b`, `--h`, `--hF`, `--maxlen`, `--depth`, `--lam`, `--skip`, `--sec`, `--split`, `--exh`, `--split2`, and `--nopos`,
`--noenergy`, `--noresF`, `--nocof`, `--nolv`, `--nolazy`, `--normerge`, `--noycorner`, and `--sif` (the cofactor in the
rest whatever its number of primes, `Par(sif=True)`).

With `--cache`, each cell kept by `hint_cert.py --cache` (with those settings) is planned again with `--cplan` (the C
plan, then the Python cut with the kernel's mirror on every hint) and the two results are compared whole.

The Python planner is the reference with `Planner.rescap = 0` (the memo never emptied), and PyPy's float sums (from
the left): run it with PyPy, as the plans are.
"""
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
import fill_cert as fc  # noqa: E402
import hint_cert as hc  # noqa: E402
import cplan  # noqa: E402


def py_plan(par_, a, b):
    """`row_job`'s plan of the cell (before the cut): cost, plan, `W['calls']`, `W['fcalls']`, stat."""
    P = par_.planner()
    assert not P.rescap, 'the reference is the planner whose memo is never emptied'
    c, node = P.plan([(a, b)], False, tc.K)
    while par_.lazy:
        bad = set()
        node = hc.resolve(P, node, bad, {})
        if not bad:
            break
        memo, calls, fcalls = P.resmemo, P.W['calls'], P.W['fcalls']
        for key in bad:
            memo[key] = None
        P = par_.planner()
        P.resmemo = memo
        P.W['calls'], P.W['fcalls'] = calls, fcalls
        P.stat['replan'] = P.stat.get('replan', 0) + len(bad)
        c, node = P.plan([(a, b)], False, tc.K)
    return c, node, P.W['calls'], P.W['fcalls'], dict(P.stat)


def first_diff(x, y, path='root'):
    """The path to the first place where the plans differ, or None."""
    if x == y:
        return None
    if not (isinstance(x, tuple) and isinstance(y, tuple)) or x[0] != y[0] or len(x) != len(y):
        return f'{path}: {str(x)[:200]} != {str(y)[:200]}'
    if x[0] in ('B', 'F', 'P'):
        if x[1] != y[1] or x[3] != y[3] or len(x[2]) != len(y[2]):
            return f'{path}: {x[0]} sel {x[1]}/{y[1]}, bits {x[3]}/{y[3]}, kids {len(x[2])}/{len(y[2])}'
        for i, (u, v) in enumerate(zip(x[2], y[2])):
            d = first_diff(u, v, f'{path}.{x[0]}{i}')
            if d:
                return d
    if x[0] == 'S':
        return first_diff(x[1], y[1], path + '.S0') or first_diff(x[2], y[2], path + '.S1')
    return f'{path}: {str(x)[:200]} != {str(y)[:200]}'


def size(node):
    if node[0] in ('B', 'F', 'P'):
        return 1 + sum(size(k) for k in node[2])
    if node[0] == 'S':
        return 1 + size(node[1]) + size(node[2])
    return 1


def settings(a):
    ln, ld = map(int, a[a.index('--L') + 1].split('/')) if '--L' in a else (2100, 1000)

    def num(k, d, t=float):
        return t(a[a.index(k) + 1]) if k in a else d
    return hc.Par('L0', ln, ld, h=num('--h', 0.003), hF=num('--hF', 0.003), maxlen=num('--maxlen', 6, int),
                  depth=num('--depth', 8, int), lam=num('--lam', 0.3), pos='--nopos' not in a,
                  skip=num('--skip', 3, int), sec=num('--sec', 3, int), energy='--noenergy' not in a, res=True,
                  resF='--noresF' not in a, cof='--nocof' not in a, lv='--nolv' not in a, lazy='--nolazy' not in a,
                  rmerge='--normerge' not in a, split=num('--split', 3, int), ycorner='--noycorner' not in a,
                  exh=num('--exh', 2, int), split2=num('--split2', 0, int), sif='--sif' in a)


def cells_test(par_, a):
    P = par_.planner()
    f0, _ = fc.root_of(P)
    cuts = fc.rowCuts(P, f0)
    cells = list(zip(cuts, cuts[1:]))
    if '--cells' in a:
        i = a.index('--cells') + 1
        step = int(a[i + 2]) if i + 2 < len(a) and a[i + 2].isdigit() else 1
        cells = cells[int(a[i]):int(a[i + 1]):step]
    else:
        cells = cells[:1]
    bad = 0
    for x, y in cells:
        t0 = time.time()
        got = cplan.plan_cells(par_, [(x, y)])[0]
        t1 = time.time()
        if '--conly' in a:
            print(f'cell {x} {y}: C {t1 - t0:.2f} s, cost {got[2] / tc.K:.6f}, {got[3]} boxes ({got[4]} over frozen '
                  f'parts), {size(got[6])} steps', flush=True)
            continue
        c, node, calls, fcalls, stat = py_plan(par_, x, y)
        t2 = time.time()
        d = first_diff(node, got[6])
        ok = d is None and c == got[2] and calls == got[3] and fcalls == got[4] and stat == got[5]
        print(f'cell {x} {y}: {"SAME" if ok else "DIFF"}; Python {t2 - t1:.1f} s, C {t1 - t0:.2f} s; cost '
              f'{c / tc.K:.6f}; {calls} boxes ({fcalls} over frozen parts); {size(node)} steps', flush=True)
        if not ok:
            bad += 1
            print('  cost', c, got[2], 'calls', calls, got[3], 'fcalls', fcalls, got[4])
            if stat != got[5]:
                print('  stat', stat, '\n      ', got[5])
            if d:
                print('  plan', d)
    return bad


def cache_test(par_, pkls):
    par_.cplan = True
    bad = 0
    for p in pkls:
        with open(p, 'rb') as fh:
            ref = pickle.load(fh)
        t0 = time.time()
        got = hc.row_job((par_, ref[1], ref[2]))
        same = got == ref
        print(f'{os.path.basename(p)}: {"SAME" if same else "DIFF"} ({ref[0]}, {time.time() - t0:.0f} s)', flush=True)
        if not same:
            bad += 1
            print('  kinds', got[0], ref[0])
            print('  info', got[-1][:4], '\n      ', ref[-1][:4])
            if got[-1][4] != ref[-1][4]:
                print('  stat', got[-1][4], '\n      ', ref[-1][4])
            if got[0] == ref[0] == 'heavy':
                for i, (x, y) in enumerate(zip(got[4], ref[4])):
                    if x != y:
                        print('  first different part', i, [u == v for u, v in zip(x, y)])
                        break
    return bad


def main():
    a = sys.argv[1:]
    sys.setrecursionlimit(100000)
    par_ = settings(a)
    if '--cache' in a:
        bad = cache_test(par_, [x for x in a if x.endswith('.pkl')])
    else:
        bad = cells_test(par_, a)
    print('CPLAN', 'FAIL' if bad else 'PASS')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
