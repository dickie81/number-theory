#!/usr/bin/env python3
"""cgen_test.py [--cells I J [STEP]] [--group N] [--split2 J] [--lam X] | --cache PKL… | --vscache PKL…: the
generator in C (`cplan.py`: `add_parts`, `cut_cells`, `plan_cells(cut=True)`, `hl_parts`) against the Python
generator (`hint_cert.add_part`, `cut`, `hl_parts`), the results compared whole: the parts with their hints, costs,
predicted seconds and counts, and the pieces of a cut cell.

With `--cells`, the cells I to J of the first prime (every STEP-th) are planned by the C planner with the
certificate's settings at 2100/1000 (`--lam`, default 0.3; `--split2`, default 1); a heavy cell is cut by both, then
cut again with the window's lines named in the hints (`hl`), and its parts written without them are transcoded by
both (`hl_parts`); a light cell is made a part by both, with and without `hl`, and with `--group N` the light cells
are also put together N at a time. With `--cache`, the heavy cells kept by `hint_cert.py --cache` have their parts
transcoded by both. With `--vscache`, the cells kept by `hint_cert.py --cplan --cache` (the C plan, the Python cut)
are planned and cut again with `--cplan --cgen` and the entries compared whole. Run it with PyPy, as the plans and
the parts are made: the predicted seconds of a part are a float sum from the left (PyPy's `sum`).
"""
import os
import pickle
import sys
import time
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
import fill_cert as fc  # noqa: E402
import hint_cert as hc  # noqa: E402
import cplan  # noqa: E402


def settings(a, hl):
    num = lambda k, d, t=float: t(a[a.index(k) + 1]) if k in a else d  # noqa: E731
    return hc.Par('L0', 2100, 1000, h=0.003, hF=0.003, maxlen=6, depth=8, lam=num('--lam', 0.3), pos=True, skip=3,
                  sec=3, energy=True, res=True, resF=True, cof=True, lv=True, lazy=True, rmerge=True, split=3,
                  ycorner=True, exh=2, split2=num('--split2', 1, int), hl=hl)


def first_diff_parts(x, y):
    for i, (u, v) in enumerate(zip(x, y)):
        if u != v:
            return f'part {i}: fields ' + str([j for j, (s, t) in enumerate(zip(u, v)) if s != t])
    if len(x) != len(y):
        return f'{len(x)} parts against {len(y)}'
    return None


def check(name, got, ref):
    ok = got == ref
    if not ok:
        print(f'  DIFF {name}', flush=True)
    return ok


def heavy(par0, par1, a, b, node, c):
    bad = 0
    P = par0.planner()
    t0 = time.time()
    parts = []
    piece = hc.cut(P, par0, node, [(a, b)], False, parts)
    t1 = time.time()
    piece_c, parts_c = cplan.cut_cells(par0, [(a, b, node)])[0]
    t2 = time.time()
    print(f'  cut: {len(parts)} parts; Python {t1 - t0:.1f} s, C {t2 - t1:.2f} s', flush=True)
    if not (check('cut (parts)', parts_c, parts) and check('cut (pieces)', piece_c, piece)):
        bad += 1
        print('   ', first_diff_parts(parts_c, parts))
    if piece[6] != c:
        print('  DIFF the pieces\' cost and the plan\'s', piece[6], c)
        bad += 1
    # the planner and the cut in one run
    got = cplan.plan_cells(par0, [(a, b)], cut=True)[0]
    cnt, piece_p, parts_p = got[6]
    rc_ = Counter()
    hc.count(node, rc_)
    if not (check('plan+cut (parts)', parts_p, parts) and check('plan+cut (pieces)', piece_p, piece)
            and check('plan+cut (counts)', cnt, dict(rc_)) and check('plan+cut (cost)', got[2], c)):
        bad += 1
    # the window's lines named: the parts transcoded, and the cell cut with them
    P1 = par1.planner()
    t0 = time.time()
    hl = hc.hl_parts(P1, parts)
    t1 = time.time()
    hl_c = cplan.hl_parts(par1, parts)
    t2 = time.time()
    ntr = sum(1 for x, y in zip(hl, parts) if x is not y)
    print(f'  hl_parts: {ntr} of {len(parts)} transcoded; Python {t1 - t0:.1f} s, C {t2 - t1:.2f} s', flush=True)
    if not check('hl_parts', hl_c, hl):
        bad += 1
        print('   ', first_diff_parts(hl_c, hl))
    P1 = par1.planner()
    t0 = time.time()
    parts1 = []
    piece1 = hc.cut(P1, par1, node, [(a, b)], False, parts1)
    t1 = time.time()
    piece1_c, parts1_c = cplan.cut_cells(par1, [(a, b, node)])[0]
    t2 = time.time()
    print(f'  cut with hl: Python {t1 - t0:.1f} s, C {t2 - t1:.2f} s', flush=True)
    if not (check('cut with hl (parts)', parts1_c, parts1) and check('cut with hl (pieces)', piece1_c, piece1)):
        bad += 1
        print('   ', first_diff_parts(parts1_c, parts1))
    # a part cut with hl is the part cut without it, transcoded
    if [p[6] for p in parts1] != [p[6] for p in hl]:
        print('  NOTE: the parts cut with hl differ from the transcoded ones (not an error of C)')
    return bad


def light(par_, groups, tag):
    P = par_.planner()
    t0 = time.time()
    ref = []
    for bl, par, group in groups:
        hc.add_part(P, bl, par, group, ref)
    t1 = time.time()
    got = cplan.add_parts(par_, groups)
    t2 = time.time()
    print(f'  add_part {tag}: {len(groups)} parts; Python {t1 - t0:.1f} s, C {t2 - t1:.2f} s', flush=True)
    if not check(f'add_part {tag}', got, ref):
        print('   ', first_diff_parts(got, ref))
        return 1
    return 0


def cells_test(a):
    par0, par1 = settings(a, False), settings(a, True)
    P = par0.planner()
    f0, _ = fc.root_of(P)
    cuts = fc.rowCuts(P, f0)
    cells = list(zip(cuts, cuts[1:]))
    i = a.index('--cells') + 1
    step = int(a[i + 2]) if i + 2 < len(a) and a[i + 2].isdigit() else 1
    sel = list(range(int(a[i]), int(a[i + 1]), step))
    gn = int(a[a.index('--group') + 1]) if '--group' in a else 0
    bad, lights = 0, []
    for r in sel:
        x, y = cells[r]
        t0 = time.time()
        _, _, c, _, _, _, node = cplan.plan_cells(par0, [(x, y)])[0]
        s = hc.secs(node)
        kind = 'light' if s <= par0.cap or node[0] != 'B' else 'heavy'
        print(f'row {r} ({x} {y}): {kind}, predicted {s:.1f} s, cost {c / tc.K:.6f}, planned in '
              f'{time.time() - t0:.0f} s', flush=True)
        if kind == 'heavy':
            bad += heavy(par0, par1, x, y, node, c)
        else:
            lights.append((x, y, node))
            for p in (par0, par1):
                bad += light(p, [([], False, [(x, y, node)])], 'hl' if p.hl else 'no hl')
    if gn > 1 and lights:
        groups = [([], False, lights[j:j + gn]) for j in range(0, len(lights), gn)]
        for p in (par0, par1):
            bad += light(p, groups, f'groups of {gn}, ' + ('hl' if p.hl else 'no hl'))
    return bad


def cache_test(a):
    par1 = settings(a, True)
    bad = 0
    for path in [x for x in a if x.endswith('.pkl')]:
        with open(path, 'rb') as fh:
            r = pickle.load(fh)
        if r[0] != 'heavy':
            continue
        P1 = par1.planner()
        t0 = time.time()
        hl = hc.hl_parts(P1, r[4])
        t1 = time.time()
        hl_c = cplan.hl_parts(par1, r[4])
        t2 = time.time()
        ok = hl_c == hl
        print(f'{os.path.basename(path)}: {"SAME" if ok else "DIFF"}; {len(r[4])} parts; Python {t1 - t0:.1f} s, '
              f'C {t2 - t1:.2f} s', flush=True)
        if not ok:
            bad += 1
            print('   ', first_diff_parts(hl_c, hl))
    return bad


def vscache_test(a):
    """Each cell kept by `hint_cert.py --cplan --cache` (the C plan, the Python cut) planned and cut again with
    `--cplan --cgen` (the C plan and the C cut, in one run), the two entries compared whole."""
    par_ = settings(a, False)
    par_.cplan = par_.cgen = True
    bad = 0
    for path in [x for x in a if x.endswith('.pkl')]:
        with open(path, 'rb') as fh:
            ref = pickle.load(fh)
        t0 = time.time()
        got = hc.row_job((par_, ref[1], ref[2]))
        ok = got == ref
        print(f'{os.path.basename(path)}: {"SAME" if ok else "DIFF"} ({ref[0]}, {len(ref[4]) if ref[0] == "heavy" else 1}'
              f' parts, {time.time() - t0:.0f} s)', flush=True)
        if not ok:
            bad += 1
            print('  kinds', got[0], ref[0], '\n  info', got[-1][:4], '\n      ', ref[-1][:4])
            if got[0] == ref[0] == 'heavy':
                print('   ', first_diff_parts(got[4], ref[4]), got[3] == ref[3])
    return bad


def main():
    a = sys.argv[1:]
    sys.setrecursionlimit(100000)
    bad = cache_test(a) if '--cache' in a else vscache_test(a) if '--vscache' in a else cells_test(a)
    print('CGEN', 'FAIL' if bad else 'PASS')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
