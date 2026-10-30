"""mirror8.py W1 W2 N a/b [OUT.json] [--rows A B]: the certificate to depth 8 of SieveDeepDefs.lean on the grid
U1 = ⌈(W1/10⁵)DEN⌉, U2 = ⌊(W2/10⁵)DEN⌋, n = N (a multiple of 4, with the coarse grid of N/4 cells of four), under the
bilinear Type I rule at L = a/b, in exact integers, cell by cell as the Lean definitions read: `cand`, `inKK`, `ne3`,
`okIB`, `bound2` (SieveCertDefs.lean, SieveRuleDefs.lean), and `trapF`, `lastF`, `Q4`, `q6`, `R8in`, `R8`, `vR`,
`vRpre`, the masks `lbase1` … `emask`, `creg`, `lreg`, `bcnt`, `Fpure`, `Gpure`, the block test `dcpT`, `dcpF`, `dcp`,
`dmaxL`, `dmax3`, `okD`, `cntH`, `cstar`, the costs `tail6`, `cost6b`, `bad5`, `cost6`, `pureOK`, `cost4`, `row`, `P3`,
`refcost`, and `ok3D`, `allowedD`, `decD`, `costD`, `totalD` (SieveDeepDefs.lean). Prints `totalD`; with OUT, writes
per candidate cell (i, j) its cost and the kernel work it makes (see `WORK`). Rows are computed in parallel processes.
With `--rows A B` only the rows A ≤ i < B (OUT then holds those rows' cells, and the total is theirs).

The kernel's check of a part `rowsJD a b j₀ j₁ ≤ B` evaluates exactly these functions; `gen_cert8.py` cuts the parts
from OUT, with bounds ⌈1.001 × part⌉."""
import json
import os
import sys
import time
from multiprocessing import Pool

DEN, K = 2 ** 40, 2 ** 60
SC = 2 ** 64
TOPK = (K * 565073 + 999999) // 1000000       # `topK`: ⌈0.565073 K⌉, ω* above 3
W1K = (K * 5671433 + 9999999) // 10000000     # `w1K`: ⌈0.5671433 K⌉, the maximum of Buchstab's ω on [2, 3]
LD = 10 ** 9                                  # `LD`, and `lnT`: upper bounds for LD·log((16 + k)/16), k ≤ 16
LNT = [0, 60624623, 117783037, 171850258, 223143553, 271933717, 318453733, 362905495, 405465110, 446287104,
       485507817, 523248145, 559615789, 594707109, 628608661, 661398484, 693147182]
# the work a candidate cell makes, in the order OUT records it after the cost
WORK = ('t3',   # the boxes (i, j, k) that `allowedD` tests with `ok3D`
        'c3',   # the counted cells (i, j, k) of a cell whose `refcost` is evaluated
        'c4',   # their cells l of depth 4 not masked (`cost4` evaluated)
        'p4',   # those in the pure mode (`pureOK`, then `Gpure`)
        'm4',   # those in the masked mode (`bad5`, then `cost6` if no box fails)
        'b5',   # the cells b of depth 5 of the masked mode (`bad5`'s and `cost6`'s terms)
        't6')   # the cells c of depth 6 of the tails (`tail6`'s terms)


def tsub(a, b):
    return a - b if a > b else 0


def cdiv(a, b):
    return (a + b - 1) // b if b else 0


def omF(P, Q):
    """`omF`: K·(1 + log(v − 1))/v at v = P/Q ∈ [2, 3], rounded up, with log(v − 1) ≤ lnT k/LD + (y − 1/y)/2 for
    k = ⌊16(v − 2)⌋ and y = (v − 1)·16/(16 + k) = A/B."""
    k = 16 * (P - 2 * Q) // Q
    A, B = 16 * (P - Q), (16 + k) * Q
    return cdiv(K * Q * (2 * A * B * (LD + LNT[k]) + (A * A - B * B) * LD), 2 * A * B * LD * P)


def invKw(s, t, W, w):
    return K if DEN <= s + 2 * t + W + w else cdiv(K * (t + w), DEN - s - t - W)


def omKw(s, t, W, w):
    """`omKw`: K·ω* on the arguments [lo, hi) of a box, lo = (DEN − s − t − W)/(t + w), hi = (DEN + 1 − s − t)/t."""
    if DEN < s + 2 * t:
        return 0
    if s + 4 * t + W + 3 * w <= DEN:
        return TOPK
    if DEN < s + 3 * t:
        return invKw(s, t, W, w)
    p1 = 0 if s + 3 * t + W + 2 * w <= DEN else invKw(s, t, W, w)
    if 100 * (DEN + 1 - s - t) <= 276 * t:
        p2 = omF(DEN + 1 - s - t, t)
    elif 277 * (t + w) <= 100 * tsub(tsub(tsub(DEN, s), t), W):
        p2 = omF(DEN - s - t - W, t + w)
    else:
        p2 = W1K
    p3 = TOPK if s + 4 * t <= DEN else 0
    return max(p1, p2, p3)


G = {}


def setup(W1, W2, N, L):
    """The grid `⟨⌈W1·DEN/10⁵⌉, ⌊W2·DEN/10⁵⌋, N, 1⟩`, its coarse grid `Gc`, and `IBPar ⟨a, b⟩` for L = a/b."""
    assert N % 4 == 0
    a, b = map(int, L.split('/'))
    U1, U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
    V = U2 - U1
    H = (tsub(DEN // 2, V) + N - 1) // N
    nC = N // 4
    HC = 4 * ((tsub(DEN // 2, V) + nC * 4 - 1) // (nC * 4))
    G.update(W1=W1, W2=W2, n=N, Lnum=a, Lden=b, U1=U1, U2=U2, V=V, H=H, nC=nC, HC=HC, lim=DEN - U1,
             E=[V + H * k for k in range(N)], EC=[V + HC * c for c in range(nC)])
    G['memo'] = {}


def memo(name, key, f):
    d = G['memo'].setdefault(name, {})
    if key not in d:
        d[key] = f()
    return d[key]


def e(k):
    return G['V'] + G['H'] * k


def eC(c):
    return G['V'] + G['HC'] * c


def cell(k):
    return (e(k), e(k) + G['H'])


def subsetSums(xs):
    """`subsetSums`: for `p :: rest`, those of `rest`, then those of `rest` shifted by `p`."""
    if not xs:
        return [(0, 0)]
    rest = subsetSums(xs[1:])
    p = xs[0]
    return rest + [(s1 + p[0], s2 + p[1]) for s1, s2 in rest]


def hiSum(xs):
    return sum(p[1] for p in xs)


def lastHi(xs):
    return xs[-1][1] if xs else 0


def inside(lo, hi):
    U1, U2 = G['U1'], G['U2']
    return (U1 < lo and hi < U2) or (DEN - U2 < lo and hi < DEN - U1)


def surelyEval(xs):
    return any(inside(s1, s2) for s1, s2 in subsetSums(xs))


def cand(i, j):
    H, U1, U2 = G['H'], G['U1'], G['U2']
    return (e(j) < e(i) + H and 2 * e(i) < DEN and e(i) + 2 * e(j) <= DEN and not (U1 < e(i) and e(i) + H < U2)
            and not surelyEval([cell(i), cell(j)]))


def inKK(i, j, k):
    return e(k) < e(j) + G['H'] and e(i) + e(j) + 2 * e(k) <= DEN


def ne3(i, j, k):
    return not surelyEval([cell(i), cell(j), cell(k)])


def bound2(a, b):
    H = G['H']
    return cdiv(H * H * (2 * a + H) * DEN * omKw(a, b, 2 * H, H), 2 * a * (a + H) * (b * (b + H)))


def cIB(s):
    U1, U2 = G['U1'], G['U2']
    return max(tsub(U1, s[0]), tsub(DEN - U2, max(s[0], U2)) if U2 <= s[1] else 0)


def tstar(xs):
    acc = None
    for s in subsetSums(xs):
        if s[1] < DEN - G['U1']:
            acc = cIB(s) if acc is None else min(acc, cIB(s))
    return acc


def condIB(a1, a2):
    Ln, Ld = G['Lnum'], G['Lden']
    return a1 * Ln < tsub(Ln, Ld) * DEN and a1 + 2 * a2 < DEN


def okIB(xs):
    """`okIB = limOK || (ibOK && nbOK)`."""
    if hiSum(xs) < G['lim']:
        return True
    T = tstar(xs)
    if T is None:
        return False
    hs = hiSum(xs)
    ib = any(condIB(s[1] + T, hs - s[1]) or condIB(s[1], hs - s[1] + T) for s in subsetSums(xs))
    return ib and hiSum(xs) + lastHi(xs) < DEN


# fixed point

def trapF(x, w):
    return cdiv(SC * w * (2 * x + w), 2 * x * (x + w))


def lastF(x, w):
    return cdiv(SC * w * DEN, x * (x + w))


# the dropped cells' bounds, by index sums

def Q4(I3, l):
    def f():
        H, V = G['H'], G['V']
        return lastF(e(l), H) * omKw(3 * V + H * I3, e(l), 4 * H, H)
    return memo('Q4', (I3, l), f)


def q6(I5, c):
    def f():
        H, HC, V = G['H'], G['HC'], G['V']
        return lastF(eC(c), HC) * omKw(5 * V + H * I5, eC(c), 4 * H + 2 * HC, HC)
    return memo('q6', (I5, c), f)


def R8in(I7, c7):
    def f():
        H, HC, V = G['H'], G['HC'], G['V']
        r = 0
        for c8 in range(c7 + 1):
            if 7 * V + H * I7 + 2 * eC(c8) <= DEN:
                r += lastF(eC(c8), HC) * omKw(7 * V + H * I7, eC(c8), 4 * H + 4 * HC, HC)
        return r
    return memo('R8in', (I7, c7), f)


def R8(I6, c):
    def f():
        H, HC, V = G['H'], G['HC'], G['V']
        r = 0
        for c7 in range(c + 1):
            if 6 * V + H * I6 + 2 * eC(c7) <= DEN:
                r += trapF(eC(c7), HC) * R8in(I6 + 4 * c7, c7)
        return r
    return memo('R8', (I6, c), f)


def vR(I5, c):
    return memo('vR', (I5, c), lambda: min(q6(I5, c) * SC * SC, trapF(eC(c), G['HC']) * R8(I5 + 4 * c, c)))


def vRpre(I5, c):
    return memo('vRpre', (I5, c), lambda: vR(I5, c) + (vRpre(I5, c - 1) if c > 0 else 0))


# the surely evaluable boxes, as bit masks

def bits(a, b):
    return 0 if b < a else ((1 << (b + 1 - a)) - 1) << a


def bit(M, s):
    return (M >> s) % 2 == 1


def above(x, y, d):
    return (x - y) // d + 1 if y <= x else 0


def lbase1(m, wl, wh):
    V, H = G['V'], G['H']
    if (m + 1) * (V + H) < wh:
        return bits(above(wl, (m + 1) * V, H), (wh - (m + 1) * (V + H) - 1) // H)
    return 0


def lbase(m):
    U1, U2 = G['U1'], G['U2']
    return memo('lbase', m, lambda: lbase1(m, U1, U2) | lbase1(m, DEN - U2, DEN - U1))


def sbase1(mr, m, rho, wl, wh):
    V, H, HC = G['V'], G['H'], G['HC']
    if (mr + m) * V + H * rho + mr * H + m * HC < wh:
        return bits(above(wl, (mr + m) * V + H * rho, HC),
                    (wh - (mr + m) * V - H * rho - mr * H - m * HC - 1) // HC)
    return 0


def sbase(mr, m, rho):
    U1, U2 = G['U1'], G['U2']
    return memo('sbase', (mr, m, rho), lambda: sbase1(mr, m, rho, U1, U2) | sbase1(mr, m, rho, DEN - U2, DEN - U1))


def smask(mr, m, N):
    return sbase(mr, m, N % 4) >> (N // 4)


def lmask(i, j, k):
    return (lbase(0) | (lbase(1) >> i) | (lbase(1) >> j) | (lbase(1) >> k) | (lbase(2) >> (i + j)) |
            (lbase(2) >> (i + k)) | (lbase(2) >> (j + k)) | (lbase(3) >> (i + j + k)))


def emask3(m, i, j, k):
    return (smask(0, m, 0) | smask(1, m, i) | smask(1, m, j) | smask(1, m, k) | smask(2, m, i + j) |
            smask(2, m, i + k) | smask(2, m, j + k) | smask(3, m, i + j + k))


def fmask3(m, i, j, k, rho):
    return (smask(1, m, rho) | smask(2, m, i + rho) | smask(2, m, j + rho) | smask(2, m, k + rho) |
            smask(3, m, i + j + rho) | smask(3, m, i + k + rho) | smask(3, m, j + k + rho) |
            smask(4, m, i + j + k + rho))


def emask(m, i, j, k, l):
    return emask3(m, i, j, k) | (fmask3(m, i, j, k, l % 4) >> (l // 4))


# the regions

def creg(S):
    V, HC = G['V'], G['HC']
    return (DEN - S - 2 * V) // (2 * HC) + 1 if S + 2 * V <= DEN else 0


def lreg(S):
    V, H = G['V'], G['H']
    return (DEN - S - 2 * V) // (2 * H) + 1 if S + 2 * V <= DEN else 0


def bcnt(I4, l):
    return min(l // 4 + 1, creg(4 * G['V'] + G['H'] * I4))


# the cells of depth 4 whose boxes below all pass

def Fpure(I4, l):
    def f():
        V, H, HC = G['V'], G['H'], G['HC']
        r = 0
        for b in range(bcnt(I4, l)):
            cm = min(b + 1, creg(4 * V + H * I4 + eC(b)))
            if cm != 0:
                r += trapF(eC(b), HC) * vRpre(I4 + 4 * b, cm - 1)
        return r
    return memo('Fpure', (I4, l), f)


def Gpure(I3, l):
    return memo('Gpure', (I3, l), lambda: min(Q4(I3, l) * SC ** 4, trapF(e(l), G['H']) * Fpure(I3 + l, l)))


# the block test

def dcpT(a1, a2):
    Ln, Ld = G['Lnum'], G['Lden']
    x = ((Ln - Ld) * DEN - a1 * Ln - 1) // Ln + 1 if a1 * Ln < (Ln - Ld) * DEN else 0
    y = DEN - a1 - 2 * a2 if a1 + 2 * a2 < DEN else 0
    return min(x, y)


def dcpF(a1, a2):
    Ln, Ld = G['Lnum'], G['Lden']
    if a1 * Ln < (Ln - Ld) * DEN:
        return (DEN - a1 - 2 * a2 - 1) // 2 + 1 if a1 + 2 * a2 < DEN else 0
    return 0


def dcp(a1, a2):
    return max(dcpT(a1, a2), dcpF(a1, a2))


def dmaxL(xs, T):
    hs = hiSum(xs)
    acc = 0
    for s in subsetSums(xs):
        acc = max(acc, max(dcp(s[1] + T, hs - s[1]), dcp(s[1], hs - s[1] + T)))
    return acc


def dmax3(i, j, k):
    def f():
        xs = [cell(i), cell(j), cell(k)]
        T = tstar(xs)
        return 0 if T is None else dmaxL(xs, T)
    return memo('dmax3', (i, j, k), f)


def okD(hi3, Dm, D, h):
    return hi3 + D < G['lim'] or (hi3 + D + h < DEN and D < Dm)


def cntH(X):
    V, HC = G['V'], G['HC']
    return (X - V) // HC if V + HC <= X else 0


def cstar(hi3, Dm, hl, hb):
    lim = G['lim']
    a = cntH((lim - hi3 - hl - hb - 1) // 2) if hi3 + hl + hb < lim else 0
    b = cntH((DEN - hi3 - hl - hb - 1) // 3) if hi3 + hl + hb < DEN else 0
    c = cntH((Dm - hl - hb - 1) // 2) if hl + hb < Dm else 0
    return max(a, min(b, c))


# the costs

def tail6(I5, b, cs, cm, E1, E2, w):
    r = 0
    for t in range(cm - cs):
        w['t6'] += 1
        if not (bit(E1, cs + t) or bit(E2, b + cs + t)):
            r += q6(I5, cs + t) * SC * SC
    return r


def cost6b(hi3, Dm, I4, l, b, E1, E2, w):
    V, H, HC = G['V'], G['H'], G['HC']
    cm = min(b + 1, creg(4 * V + H * I4 + eC(b)))
    cs = min(cm, cstar(hi3, Dm, e(l) + H, eC(b) + HC))
    I5 = I4 + 4 * b
    return trapF(eC(b), HC) * ((0 if cs == 0 else vRpre(I5, cs - 1)) +
                               (tail6(I5, b, cs, cm, E1, E2, w) if cs < cm else 0))


def bad5(hi3, Dm, I4, l, E1, w):
    H, HC = G['H'], G['HC']
    r = 0
    for b in range(bcnt(I4, l)):
        w['b5'] += 1
        if not bit(E1, b) and not okD(hi3, Dm, e(l) + H + eC(b) + HC, eC(b) + HC):
            r += 1
    return r


def cost6(hi3, Dm, I4, l, E1, E2, w):
    r = 0
    for b in range(bcnt(I4, l)):
        w['b5'] += 1
        if not bit(E1, b):
            r += cost6b(hi3, Dm, I4, l, b, E1, E2, w)
    return r


def pureOK(hi3, Dm, I4, l):
    V, H, HC = G['V'], G['H'], G['HC']
    bc = bcnt(I4, l)
    if bc == 0:
        return False
    hbm = eC(bc - 1) + HC
    return okD(hi3, Dm, e(l) + H + hbm, hbm) and min(bc, creg(4 * V + H * I4 + V)) <= cstar(hi3, Dm, e(l) + H, hbm)


def cost4(i, j, k, l, w):
    H = G['H']
    I3 = i + j + k
    q4 = Q4(I3, l) * SC ** 4
    hi3 = e(i) + e(j) + e(k) + 3 * H
    Dm = dmax3(i, j, k)
    if not okD(hi3, Dm, e(l) + H, e(l) + H):
        return q4
    if pureOK(hi3, Dm, I3 + l, l):
        w['p4'] += 1
        return Gpure(I3, l)
    w['m4'] += 1
    E1 = emask(1, i, j, k, l)
    E2 = emask(2, i, j, k, l)
    if bad5(hi3, Dm, I3 + l, l, E1, w) == 0:
        return min(q4, trapF(e(l), H) * cost6(hi3, Dm, I3 + l, l, E1, E2, w))
    return q4


def row(i, j, k, w):
    M = lmask(i, j, k)
    r = 0
    for l in range(min(k + 1, lreg(e(i) + e(j) + e(k)))):
        if not bit(M, l):
            w['c4'] += 1
            r += cost4(i, j, k, l, w)
    return r


def P3(i, j, k):
    H = G['H']
    return trapF(e(i), H) * trapF(e(j), H) * trapF(e(k), H)


def refcost(i, j, w):
    r = 0
    for k in range(G['n']):
        if inKK(i, j, k) and ne3(i, j, k):
            w['c3'] += 1
            r += P3(i, j, k) * row(i, j, k, w)
    return cdiv(r, SC ** 8)


def ok3D(i, j, k):
    H = G['H']
    return okD(e(i) + e(j) + e(k) + 3 * H, dmax3(i, j, k), 0, e(k) + H)


def allowedD(i, j, w):
    if not okIB([cell(i), cell(j)]):
        return False
    for k in range(G['n']):
        if inKK(i, j, k) and ne3(i, j, k):
            w['t3'] += 1
            if not ok3D(i, j, k):
                return False
    return True


def costD(i, j):
    """`costD i j` and the work, or None for a cell that is not a candidate (cost 0, no work)."""
    if not cand(i, j):
        return None
    w = dict.fromkeys(WORK, 0)
    b2 = bound2(e(i), e(j))
    dec = False
    rc = None
    if allowedD(i, j, w):
        rc = refcost(i, j, w)
        dec = rc <= b2
    return (rc if dec else b2), dec, w


def cell_row(args):
    W1, W2, N, L, i = args
    if G.get('key') != (W1, W2, N, L):
        setup(W1, W2, N, L)
        G['key'] = (W1, W2, N, L)
    res = {}
    for j in range(N):
        r = costD(i, j)
        if r is not None:
            c, dec, w = r
            res[j] = [c, int(dec)] + [w[x] for x in WORK]
    return i, res


def main():
    a = [x for x in sys.argv[1:]]
    rows = None
    if '--rows' in a:
        r0 = a.index('--rows')
        rows = (int(a[r0 + 1]), int(a[r0 + 2]))
        del a[r0:r0 + 3]
    W1, W2, N, L = int(a[0]), int(a[1]), int(a[2]), a[3]
    OUT = a[4] if len(a) > 4 else None
    setup(W1, W2, N, L)
    t0 = time.time()
    rr = range(N) if rows is None else range(*rows)
    with Pool() as p:
        out = dict(p.imap_unordered(cell_row, [(W1, W2, N, L, i) for i in rr], chunksize=1))
    cells = {}
    total = 0
    for i in sorted(out):
        for j, v in sorted(out[i].items()):
            cells[f'{i},{j}'] = v
            total += v[0]
    ndec = sum(v[1] for v in cells.values())
    sums = {x: sum(v[2 + m] for v in cells.values()) for m, x in enumerate(WORK)}
    print(f'grid [{W1}, {W2}]/1e5 n={N} nC={N // 4} L={L}: U1={G["U1"]} U2={G["U2"]} H={G["H"]} HC={G["HC"]}; '
          f'rows {rr.start}..{rr.stop - 1}: totalD/K {total / K:.7f} ({total}); totalD < K: {total < K}; '
          f'candidate cells {len(cells)}, decomposed {ndec}; {time.time() - t0:.0f} s', flush=True)
    print('kernel work: ' + ', '.join(f'{x} {sums[x]}' for x in WORK), flush=True)
    if OUT:
        json.dump({'W1': W1, 'W2': W2, 'n': N, 'nC': N // 4, 'L': L, 'U1': G['U1'], 'U2': G['U2'], 'H': G['H'],
                   'HC': G['HC'], 'rows': [rr.start, rr.stop], 'totalD': total, 'work': list(WORK),
                   'cells': cells}, open(OUT, 'w'))


if __name__ == '__main__':
    main()
