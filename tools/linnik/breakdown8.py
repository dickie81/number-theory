"""breakdown8.py [--variant V] [W1 W2 N a/b]: the certificate to depth 8 (`SieveDeepDefs.lean`'s `totalD`, as
`mirror8.py` computes it), with each candidate cell's cost split by depth and by kind; by default on the paper's grid
`43457 46959 272` at `L = 11/5`. It evaluates `mirror8.py`'s functions, so the total is `mirror8.py`'s to the integer,
and prints the counts and costs that §S6 of the paper's supplement quotes:

* depth 2 (the candidate cells (i, j)): decomposed or dropped; whether the box (i, j) passes `limOK` (its upper sum
  below `lim = DEN − U1`, so that it lies below the line `α₁ + α₂ = 1 − U₁/D`) or reaches the line; for a dropped
  cell the reason: the rule `okIB` fails on (i, j), the rule fails on a counted box (i, j, k) of depth 3 (`ok3D`,
  which at depth 3 is the rule itself), or the cell is allowed but `refcost > bound2` (cheaper dropped);
* depth 3 and 4, below the decomposed cells: the counted boxes (i, j, k), the surely evaluable ones (`inKK` but not
  `ne3`); the cells l of depth 4, masked (surely evaluable, cost 0) or counted, and of the counted ones those dropped
  because the block test `okD` fails, because a box of depth 5 fails (`bad5 > 0`), or because the depth-4 bound is
  cheaper, and those decomposed (in the pure or the masked mode);
* depth 5 and 6, below the decomposed cells of depth 4: the masked coarse cells of depth 5; the coarse cells of depth 6
  decomposed to depth 8 (`vR` takes `trapF·R8`), dropped by the minimum (`vR` takes `q6`), dropped because the block
  test fails (`tail6`'s `q6`), or masked in `tail6` (cost 0).

The costs are exact integers in units of `1/(SC⁸K)` before `refcost`'s rounding up, printed in units of `K`.

The variants change `mirror8.py`'s functions before the worker processes fork:

* `depth8` (the default): the certificate as it is;
* `depth6`: no coarse cell of depth 6 is decomposed (`vR = q6·SC²`);
* `depth4`: no cell of depth 4 is decomposed (`cost4 = q4`);
* `lim`: (R1) alone as the rule (`okIB = limOK` at depth 2, and `dmax3 = 0`, so that `okD` is `limOK`), to depth 8;
* `lim6`: `lim` and `depth6`.

Needs Python 3 only, and uses all cores (through `mirror8.py`); about three minutes on four cores.
"""
import multiprocessing as mp
import os
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mirror8 as m  # noqa: E402

GRID = ('43457', '46959', '272', '11/5')   # the paper's certificate (`SieveGrid22000E`, `ibPar22000E`)
KEYS = ('n_c3', 'n_c3_eval', 'n_c3_lim', 'n_c3_blk',
        'n4_masked', 'n4', 'n4_drop_rule', 'c4_drop_rule', 'n4_drop_bad5', 'c4_drop_bad5',
        'n4_drop_cost_pure', 'c4_drop_cost_pure', 'n4_drop_cost_mask', 'c4_drop_cost_mask',
        'n4_dec_pure', 'c4_dec_pure', 'n4_dec_mask', 'c4_dec_mask',
        'n5_masked', 'n6_dec', 'c6_dec', 'n6_drop_min', 'c6_drop_min', 'n6_drop_forced', 'c6_drop_forced',
        'n6_masked')
VARIANTS = ('depth8', 'depth6', 'depth4', 'lim', 'lim6')
VARIANT = 'depth8'


def apply_variant(v):
    global VARIANT
    VARIANT = v
    if v in ('depth6', 'lim6'):
        m.vR = lambda I5, c: m.memo('vR', (I5, c), lambda: m.q6(I5, c) * m.SC * m.SC)
    if v in ('lim', 'lim6'):
        m.okIB = lambda xs: m.hiSum(xs) < m.G['lim']
        m.dmax3 = lambda i, j, k: 0


def vR_parts(I5, c):
    """(cost decomposed, number decomposed, cost dropped, number dropped) of the coarse cell c of depth 6, in `vR`'s
    units (`SC³K`)."""
    def f():
        q = m.q6(I5, c) * m.SC * m.SC
        v = m.vR(I5, c)
        return (0, 0, q, 1) if v == q else (v, 1, 0, 0)
    return m.memo('vRparts', (I5, c), f)


def vRpre_parts(I5, c):
    def f():
        a = vR_parts(I5, c)
        if c > 0:
            return tuple(x + y for x, y in zip(a, vRpre_parts(I5, c - 1)))
        return a
    return m.memo('vRpreparts', (I5, c), f)


def Fpure_parts(I4, l):
    """`Fpure`'s cells of depth 6, as `vR_parts`, in units of `SC⁴K`."""
    def f():
        V, H, HC = m.G['V'], m.G['H'], m.G['HC']
        r = [0, 0, 0, 0]
        for b in range(m.bcnt(I4, l)):
            cm = min(b + 1, m.creg(4 * V + H * I4 + m.eC(b)))
            if cm != 0:
                t = m.trapF(m.eC(b), HC)
                p = vRpre_parts(I4 + 4 * b, cm - 1)
                r[0] += t * p[0]
                r[1] += p[1]
                r[2] += t * p[2]
                r[3] += p[3]
        return tuple(r)
    return m.memo('Fpureparts', (I4, l), f)


def cost6_acc(hi3, Dm, I4, l, E1, E2):
    """`cost6` and its parts at depths 5 and 6 (the costs in units of `SC⁴K`)."""
    V, H, HC = m.G['V'], m.G['H'], m.G['HC']
    r = 0
    p = dict(n5_masked=0, n6_dec=0, c6_dec=0, n6_drop_min=0, c6_drop_min=0, n6_drop_forced=0, c6_drop_forced=0,
             n6_masked=0)
    for b in range(m.bcnt(I4, l)):
        if m.bit(E1, b):
            p['n5_masked'] += 1
            continue
        cm = min(b + 1, m.creg(4 * V + H * I4 + m.eC(b)))
        cs = min(cm, m.cstar(hi3, Dm, m.e(l) + H, m.eC(b) + HC))
        I5 = I4 + 4 * b
        tb = m.trapF(m.eC(b), HC)
        pre = m.vRpre(I5, cs - 1) if cs else 0
        pp = vRpre_parts(I5, cs - 1) if cs else (0, 0, 0, 0)
        tail = 0
        for c in range(cs, cm):
            if m.bit(E1, c) or m.bit(E2, b + c):
                p['n6_masked'] += 1
            else:
                q = m.q6(I5, c) * m.SC * m.SC
                tail += q
                p['n6_drop_forced'] += 1
                p['c6_drop_forced'] += tb * q
        r += tb * (pre + tail)
        p['c6_dec'] += tb * pp[0]
        p['n6_dec'] += pp[1]
        p['c6_drop_min'] += tb * pp[2]
        p['n6_drop_min'] += pp[3]
    return r, p


def cost4_acc(i, j, k, l, P, acc):
    """`cost4`, with its parts added to `acc` (weighted by the box's `P3`)."""
    H, SC = m.G['H'], m.SC
    I3 = i + j + k
    q4 = m.Q4(I3, l) * SC ** 4
    if VARIANT == 'depth4':
        acc['n4_drop_rule'] += 1
        acc['c4_drop_rule'] += P * q4
        return q4
    hi3 = m.e(i) + m.e(j) + m.e(k) + 3 * H
    Dm = m.dmax3(i, j, k)
    if not m.okD(hi3, Dm, m.e(l) + H, m.e(l) + H):
        acc['n4_drop_rule'] += 1
        acc['c4_drop_rule'] += P * q4
        return q4
    t = m.trapF(m.e(l), H)
    if m.pureOK(hi3, Dm, I3 + l, l):
        F = m.Fpure(I3 + l, l)
        val = m.Gpure(I3, l)
        assert val == min(q4, t * F)
        if val == q4:
            acc['n4_drop_cost_pure'] += 1
            acc['c4_drop_cost_pure'] += P * q4
        else:
            acc['n4_dec_pure'] += 1
            acc['c4_dec_pure'] += P * val
            fp = Fpure_parts(I3 + l, l)
            assert t * (fp[0] + fp[2]) == val
            acc['n6_dec'] += fp[1]
            acc['c6_dec'] += P * t * fp[0]
            acc['n6_drop_min'] += fp[3]
            acc['c6_drop_min'] += P * t * fp[2]
        return val
    E1 = m.emask(1, i, j, k, l)
    E2 = m.emask(2, i, j, k, l)
    w = dict.fromkeys(m.WORK, 0)
    if m.bad5(hi3, Dm, I3 + l, l, E1, w) == 0:
        c6, p = cost6_acc(hi3, Dm, I3 + l, l, E1, E2)
        assert c6 == m.cost6(hi3, Dm, I3 + l, l, E1, E2, w)
        val = min(q4, t * c6)
        if val == q4:
            acc['n4_drop_cost_mask'] += 1
            acc['c4_drop_cost_mask'] += P * q4
        else:
            acc['n4_dec_mask'] += 1
            acc['c4_dec_mask'] += P * val
            for x in ('n5_masked', 'n6_dec', 'n6_drop_min', 'n6_drop_forced', 'n6_masked'):
                acc[x] += p[x]
            for x in ('c6_dec', 'c6_drop_min', 'c6_drop_forced'):
                acc[x] += P * t * p[x]
        return val
    acc['n4_drop_bad5'] += 1
    acc['c4_drop_bad5'] += P * q4
    return q4


def refcost_acc(i, j, acc):
    """`refcost` before its rounding up (in units of `SC⁸K`), with its parts added to `acc`."""
    H = m.G['H']
    r = 0
    for k in range(m.G['n']):
        if not m.inKK(i, j, k):
            continue
        if not m.ne3(i, j, k):
            acc['n_c3_eval'] += 1
            continue
        acc['n_c3'] += 1
        hi3 = m.e(i) + m.e(j) + m.e(k) + 3 * H
        acc['n_c3_lim' if hi3 < m.G['lim'] else 'n_c3_blk'] += 1
        P = m.P3(i, j, k)
        M = m.lmask(i, j, k)
        row = 0
        for l in range(min(k + 1, m.lreg(m.e(i) + m.e(j) + m.e(k)))):
            if m.bit(M, l):
                acc['n4_masked'] += 1
                continue
            acc['n4'] += 1
            row += cost4_acc(i, j, k, l, P, acc)
        r += P * row
    return r


def cell(i, j):
    """(cost, decomposed, limOK of the box (i, j), the reason it is dropped, the raw `refcost`, the parts), or None for
    a cell that is not a candidate."""
    if not m.cand(i, j):
        return None
    lim2 = m.hiSum([m.cell(i), m.cell(j)]) < m.G['lim']
    b2 = m.bound2(m.e(i), m.e(j))
    reason = None
    if not m.okIB([m.cell(i), m.cell(j)]):
        reason = 'okIB2'
    elif any(m.inKK(i, j, k) and m.ne3(i, j, k) and not m.ok3D(i, j, k) for k in range(m.G['n'])):
        reason = 'ok3D'
    if reason is not None:
        return (b2, False, lim2, reason, 0, None)
    acc = dict.fromkeys(KEYS, 0)
    raw = refcost_acc(i, j, acc)
    rc = m.cdiv(raw, m.SC ** 8)
    dec = rc <= b2
    return (rc if dec else b2, dec, lim2, None if dec else 'cost', raw, acc)


def cell_row(args):
    W1, W2, N, L, i = args
    if m.G.get('key') != (W1, W2, N, L):
        m.setup(W1, W2, N, L)
        m.G['key'] = (W1, W2, N, L)
    return i, {j: r for j in range(N) if (r := cell(i, j)) is not None}


def report(cells):
    K = m.K
    f = lambda c: float(Fr(c, K))
    cat = {}
    for cost, dec, lim2, reason, raw, acc in cells:
        names = ['cand']
        if dec:
            names += ['dec', 'dec_lim' if lim2 else 'dec_ib']
        else:
            names += ['drop', 'drop_' + reason, 'drop_' + reason + ('_lim' if lim2 else '_line'),
                      'drop_below' if lim2 else 'drop_line']
        for x in names:
            c = cat.setdefault(x, [0, 0])
            c[0] += 1
            c[1] += cost
    print('\n[depth 2] candidate cells: number, cost/K')
    for name, desc in (('cand', 'all candidate cells'), ('dec', 'decomposed'),
                       ('dec_lim', '  decomposed, the box (i,j) passes limOK (split at X\')'),
                       ('dec_ib', '  decomposed, the box (i,j) fails limOK and passes ibOK and nbOK (taken whole)'),
                       ('drop', 'dropped (at bound2)'),
                       ('drop_okIB2', '  dropped: the rule okIB fails on (i,j)'),
                       ('drop_okIB2_line', '    of which reaching the line (limOK fails)'),
                       ('drop_okIB2_lim', '    of which below the line (cannot happen: limOK implies okIB)'),
                       ('drop_ok3D', '  dropped: (i,j) passes, the rule fails on a counted box (i,j,k) (ok3D)'),
                       ('drop_ok3D_lim', '    of which (i,j) passes limOK'),
                       ('drop_ok3D_line', '    of which (i,j) reaches the line and passes by the bilinear test'),
                       ('drop_cost', '  dropped: allowed, but refcost > bound2 (cheaper dropped)'),
                       ('drop_cost_lim', '    of which below the line'),
                       ('drop_cost_line', '    of which reaching the line'),
                       ('drop_line', '  dropped cells reaching the line a1 + a2 = 1 - U1/D (limOK fails)'),
                       ('drop_below', '  dropped cells below the line (limOK holds)')):
        c = cat.get(name, [0, 0])
        print(f'  {desc}: {c[0]} cells, {f(c[1]):.7f} K')
    U = m.SC ** 8 * K
    for kind, sel in (('decomposed cells of depth 2', lambda v: v[1]),
                      ('decomposed cells of depth 2 that pass limOK', lambda v: v[1] and v[2]),
                      ('cells of depth 2 taken whole by the bilinear test', lambda v: v[1] and not v[2])):
        A = dict.fromkeys(KEYS, 0)
        rawsum = 0
        for v in cells:
            if sel(v):
                for x in KEYS:
                    A[x] += v[5][x]
                rawsum += v[4]
        g = lambda x: float(Fr(A[x], U))
        assert sum(A[x] for x in KEYS if x.startswith('c4_')) == rawsum
        assert sum(A[x] for x in KEYS if x.startswith('c6_')) == A['c4_dec_pure'] + A['c4_dec_mask']
        n4dec = A['n4_dec_pure'] + A['n4_dec_mask']
        n4drop = A['n4_drop_rule'] + A['n4_drop_bad5'] + A['n4_drop_cost_pure'] + A['n4_drop_cost_mask']
        assert n4dec + n4drop == A['n4']
        c4drop = g('c4_drop_rule') + g('c4_drop_bad5') + g('c4_drop_cost_pure') + g('c4_drop_cost_mask')
        print(f'\n[below the {kind}] (costs before refcost\'s rounding up, sum {float(Fr(rawsum, U)):.7f} K)')
        print(f"  depth 3: counted boxes (i,j,k) {A['n_c3']} (upper sum below lim {A['n_c3_lim']}, by the bilinear "
              f"test {A['n_c3_blk']}); surely evaluable {A['n_c3_eval']}")
        print(f"  depth 4: cells l {A['n4'] + A['n4_masked']}: masked (surely evaluable, cost 0) {A['n4_masked']}; "
              f"counted {A['n4']}: decomposed {n4dec} ({g('c4_dec_pure') + g('c4_dec_mask'):.7f} K: pure mode "
              f"{A['n4_dec_pure']}, {g('c4_dec_pure'):.7f} K; masked mode {A['n4_dec_mask']}, "
              f"{g('c4_dec_mask'):.7f} K), dropped {n4drop} ({c4drop:.7f} K: okD fails {A['n4_drop_rule']}, "
              f"{g('c4_drop_rule'):.7f} K; a box of depth 5 fails {A['n4_drop_bad5']}, {g('c4_drop_bad5'):.7f} K; "
              f"the depth-4 bound cheaper, pure mode {A['n4_drop_cost_pure']}, {g('c4_drop_cost_pure'):.7f} K, "
              f"masked mode {A['n4_drop_cost_mask']}, {g('c4_drop_cost_mask'):.7f} K)")
        n6 = A['n6_dec'] + A['n6_drop_min'] + A['n6_drop_forced']
        print(f"  depths 5 and 6, below the decomposed cells of depth 4: coarse cells of depth 5 masked "
              f"{A['n5_masked']}; coarse cells of depth 6 {n6 + A['n6_masked']}: masked (cost 0) {A['n6_masked']}; "
              f"decomposed to depth 8 {A['n6_dec']}, {g('c6_dec'):.7f} K; dropped "
              f"{A['n6_drop_min'] + A['n6_drop_forced']}, {g('c6_drop_min') + g('c6_drop_forced'):.7f} K (the "
              f"depth-6 bound cheaper {A['n6_drop_min']}, {g('c6_drop_min'):.7f} K; the block test fails "
              f"{A['n6_drop_forced']}, {g('c6_drop_forced'):.7f} K)")


def main():
    a = sys.argv[1:]
    if '--variant' in a:
        k = a.index('--variant')
        if a[k + 1] not in VARIANTS:
            sys.exit(f'unknown variant {a[k + 1]}; the variants are {", ".join(VARIANTS)}')
        apply_variant(a[k + 1])
        del a[k:k + 2]
    W1, W2, N, L = a if a else GRID
    W1, W2, N = int(W1), int(W2), int(N)
    m.setup(W1, W2, N, L)
    m.G['key'] = (W1, W2, N, L)
    t0 = time.time()
    with mp.get_context('fork').Pool() as p:
        res = dict(p.imap_unordered(cell_row, [(W1, W2, N, L, i) for i in range(N)], chunksize=1))
    cells = [v for i in sorted(res) for _, v in sorted(res[i].items())]
    total = sum(v[0] for v in cells)
    print(f"variant {VARIANT}: grid [{W1}, {W2}]/1e5 n={N} L={L}: U1={m.G['U1']} U2={m.G['U2']} H={m.G['H']} "
          f"HC={m.G['HC']}: totalD/K {total / m.K:.7f} ({total}); candidate cells {len(cells)}, decomposed "
          f"{sum(1 for v in cells if v[1])}; {time.time() - t0:.0f} s", flush=True)
    report(cells)


if __name__ == '__main__':
    main()
