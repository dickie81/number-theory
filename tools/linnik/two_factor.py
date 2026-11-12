#!/usr/bin/env python3
"""two_factor.py: the certificate of `mirror8.py` with a second Type II estimate, in two variables.

    two_factor.py region a/b                 the region at L = a/b, on the paper's grid
    two_factor.py total W1 W2 N a/b [opts]   the certificate's total on the grid of `mirror8.py W1 W2 N a/b`
    two_factor.py scan a/b ... [opts]        for each L: the window chosen afresh (as `density_payoff.py` does), the
                                             least grid that satisfies the Lean's conditions, and the total
    opts:  --base       without the estimate (the total is then `mirror8.py`'s; `scan` prints both)
           --depth D    the estimate evaluates boxes of depth at most D (2, 3 or 4; the default is 4)
           --stops      the rule's stops may also be stops of the estimate
           --bil        the bilinear Type I rule without the condition that d2 be shorter than the cofactor
           --lean       the region proved in Lean (SieveTwoZone7D.Zone7d), in exact arithmetic, on the rectangle of
                        the two parts' exponents (not with --stops)

A computation, not a certificate: without `--lean` the region is sampled in floating point, and the lemmas that
would bring the estimate to the sieve's sums are not all written (below).  The estimate is in Lean: Proposition 3'
for two polynomials on a region (SieveTypeIIHM.typeII_two_gen), for the curve of Huxley's estimate on the region of `--lean`
(SieveTwoZone7D.typeII_two_hx), and the paper's Lemmas 4.4 and 4.5 with it (SieveFamilyTwo.typeII_sharp_two,
SieveUnwTwo.typeII_unw_two); so is the bilinear Type I estimate of `--bil` (SieveTypeIB.typeIB_bound_wide, and
SieveTypeIBSumWide.leaves_family_wide for a family of leaves).  Nothing in the paper depends on it. Here "the paper" is the Linnik paper's version at 11/5, in the git history at commit 49dc981; the paper now
proves 43/20 by another route (hint_cert.py).

The estimate.  The paper's Type II estimate (its Theorem 3.1) bounds, over the non-trivial characters mod q, the sum
of |W(chi)| times a product of prime sums, for one Dirichlet polynomial W with arbitrary coefficients whose length
P = q^m lies in a window.  In a bin of characters it uses, for W, orthogonality or the Halasz-Montgomery inequality,
and for the number of characters in the bin, the density curve.  With two polynomials W1 and W2, of lengths q^m1 and
q^m2, Cauchy-Schwarz between them needs no count of the bin: the sum over a bin of |W1||W2| is at most the product
of the two mean squares over the bin to the power 1/2, and each mean square is at most (P + q) sum |a|^2
(orthogonality) or e (2P + |bin| H) sum |a|^2 (the Halasz-Montgomery inequality in its mean-square form, the dual of
the paper's, with the same kernel bound H).  With the paper's bound for the prime sums, a bin at beta contributes at
most q^E times the two normalised norms, with

    E = (L - m1 - m2)(beta + w) + sum over i of [ m_i/2 + M(m_i)/2 ],
    M(m) = m for m > 1, and min(1, max(m, g(beta) + b(m))) for m <= 1,   b(m) = 5/12 + m/12 + (1 - m)/1000 + 2/1000,

g the density curve, and the estimate holds on the region T(L) of the (m1, m2) with E <= L - 1/25000 for every beta
in [1/2, 11/12] and w = 4/10^6: the paper's margins.  In exponents a_i = m_i/L of x = q^L, the rest (the product of
the prime sums) has the exponent 1 - a1 - a2.  At L = 11/5 the region is about |a1 - a2| < 0.08 with a rest of at
most 0.164; no window of the paper covers, for example, two primes near x^0.42 and a third near x^0.16.  The region
does not close at L = 13/6, where the window does.

The rule.  A term of the decomposition of depth at most D, a sum of S(A_{p1...pk}, pk) over the primes of a box, is
evaluated if its primes and its cofactor split into two parts, each of them a variable with arbitrary coefficients,
and a rest that is a product of primes, so that the exponents of the two parts lie in T(L) on all of the box.  The
cofactor, whose prime factors are at least pk, may be in the rest or in a part.  The test takes the lattice rectangle
of step half a cell that encloses the box and asks every lattice point of it to be in the region, sampled at 60
values of beta on each piece of the curve.

What is not written.  The estimate itself is the paper's proof with one more Cauchy-Schwarz (in Lean, as above).
The step from it to the sums of the sieve is the analogue of the paper's Lemmas 4.4 to 4.6, with two variables.
Lemmas 4.4 and 4.5 are in Lean for comparisons that have a prime of the rest as a pivot; a comparison between the
two variables has none, and Lemma 4.6 (chains of primes) in two variables, where such comparisons arise, is not
written.  It is assumed here, with Harman's comparison for the new stops.

`--stops`: in the rule's bilinear test (R2), the exponent T of the small primes that a leaf may hold is the least
t(S) over the sets S of the box's primes, the distance of S from the window or its reflection.  With the estimate, a
part A of the box's primes may also be completed by the small primes until its exponent enters the interval on which
the estimate holds with a rest R of the box's primes; the interval must be at least as long as the floor's exponent
and A must not start past it.  It changes little.

`--lean`: the region is the one of `SieveTwoZone7D.zone_hx`, for which Proposition 3' in two variables is proved with
no hypothesis: with m_i = L a_i, s_i = 1 - m_i and rho = L (1 - a1 - a2), it asks rho >= 1/2000, m_i >= 2/3, and
s1, s2 and s1 + s2 at most lambda rho - 1/12500 (lambda = 27637/62500, read from `gen_zone.py`).  The test is exact,
in integers, and on a rectangle, as `SieveUnwTwo.typeII_unw_two` asks: the two parts' exponents range over
[lo(A), hi(A)] x [lo(B), hi(B)] for two parts of primes, and over [lo(A), hi(A)] x [1 - hi(A) - hi(R), 1 - lo(A) - lo(R)]
when the cofactor is in the second part, which is larger than the set of pairs that occur (the two are tied by the
size of n).  The region is convex, so the rectangle lies in it when its corners do.

`--bil`: the paper's Lemma 4.2 asks 2HD < q, so that t d2' = t' d2 (mod q) is an equation.  Without it, for given
(t, d2') there are at most F(2HD/q + 1) pairs (t', d2), and the first term of the lemma has the factor (1 + d2/n)
more, n the cofactor's length.  In exponents of x, with tau = 1/L, a leaf then passes when a1 < 1 - tau and either
a1 + 2 a2 < 1 (the paper's rule) or max(a1, tau) + a1 + 2 a2 < 2 - tau.  Lemma 4.3 on that region is in Lean
(SieveTypeIBAsymWide.leaves_ib_wide, for a cofactor of length at most about q); Harman's comparison with it is not.

Numbers (10 November 2026; n = 272 at 11/5, the paper's window; below it the window is chosen afresh):

    L        paper's certificate   with the estimate (depth 4)   and --bil
    2.200    0.93214               0.76216                       0.73346
    2.199    0.96729               0.78731
    2.198    1.01027               0.80914
    2.196    1.09860               0.86399
    2.194                          0.93548
    2.193                          0.97454
    2.192                          1.03180                       1.00565
    2.191                                                        1.06792

With `--lean`, the region proved in Lean on rectangles: 0.77375 at 2.200, 0.87407 at 2.196, 0.94408 at 2.194 and
0.98606 at 2.193, so the last exponent that passes is the same.

At 11/5 the estimate takes the cost of the decomposed cells from 0.2149 K to 0.0916 K and that of the dropped cells
from 0.7173 K to 0.6706 K.  So in this decomposition the estimate moves the last exponent that passes from 2.199 to
2.193.  The decomposition is built on the window: its floor is the window's width, which tends to 0 at 13/6, and the
cells it must drop are those that the Type I rule does not reach.  `type2_model.py` is the model of the estimate's
region against Harman's.

Needs numpy, `mirror8.py` and `route_limits.py`; uses all cores.  About a minute for a total at n = 272.
"""
import os
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_zone  # noqa: E402
import mirror8 as m8  # noqa: E402
import route_limits as rl  # noqa: E402

DEN = m8.DEN
X = {}


# the region, on the lattice of step H/2

def build(L, curve='g7d'):
    """The tables of the region: `P2` for two parts made of primes (the rest holds the cofactor) and `PC` for a part
    of primes and a rest of primes (the other part holds the cofactor), as prefix sums of the lattice points that
    fail.  The region lies in 0.30 <= a <= 0.60 with a rest of at most 0.20 (`region` prints its bounds); the tables
    are computed there and say "fails" elsewhere."""
    bs, gs = [], []
    for lo, hi, A in rl.parse(curve):
        b = np.linspace(float(lo), float(hi), 60)
        bs.append(b)
        gs.append(np.ones_like(b) if A is None else float(A) * (1 - b))
    b, g = np.concatenate(bs), np.concatenate(gs)
    Lf, w = float(L), 4e-6
    thr = Lf - float(rl.MARGIN)
    d = m8.G['H'] // 2
    T = int(0.80 * DEN) // d + 2
    a = np.arange(T + 1) * (d / DEN)
    i0, i1 = int(0.30 * DEN) // d, int(0.60 * DEN) // d + 1
    j1 = int(0.20 * DEN) // d + 1
    ms = a[i0:i1 + 1] * Lf
    Bs = 5 / 12 + ms / 12 + (1 - ms) / 1000 + 2 / 1000
    a2c = 1.0 - a[i0:i1 + 1, None] - a[None, 0:j1 + 1]      # the cofactor's part, on the lattice of (a1, rest)
    m2c = a2c * Lf
    B2c = 5 / 12 + m2c / 12 + (1 - m2c) / 1000 + 2 / 1000
    f2 = np.zeros((i1 + 1 - i0, i1 + 1 - i0), dtype=bool)
    fc = a2c <= 0
    for bb, gg in zip(b, g):
        M = np.where(ms > 1, ms, np.minimum(1.0, np.maximum(ms, gg + Bs)))
        A1 = -ms * (bb + w) + ms / 2 + M / 2
        f2 |= Lf * (bb + w) + A1[:, None] + A1[None, :] > thr
        Mc = np.where(m2c > 1, m2c, np.minimum(1.0, np.maximum(m2c, gg + B2c)))
        fc |= Lf * (bb + w) + A1[:, None] + (-m2c * (bb + w) + m2c / 2 + Mc / 2) > thr
    bad2 = np.ones((T + 1, T + 1), dtype=bool)
    badc = np.ones((T + 1, T + 1), dtype=bool)
    bad2[i0:i1 + 1, i0:i1 + 1] = f2
    badc[i0:i1 + 1, 0:j1 + 1] = fc
    r2 = np.nonzero((~bad2).any(axis=1))[0]
    rc = np.nonzero((~badc).any(axis=1))[0]
    cc = np.nonzero((~badc).any(axis=0))[0]
    X.update(d=d, T=T, L=Lf, TI={}, ok2=~bad2, okc=~badc,
             a0=int(r2[0]) * d if len(r2) else DEN, a1=int(r2[-1]) * d if len(r2) else -1,
             c0=int(rc[0]) * d if len(rc) else DEN, c1=int(rc[-1]) * d if len(rc) else -1,
             r1=int(cc[-1]) * d if len(cc) else -1,
             P2=np.pad(np.cumsum(np.cumsum(bad2, axis=0), axis=1), ((1, 0), (1, 0))).astype(np.int64),
             PC=np.pad(np.cumsum(np.cumsum(badc, axis=0), axis=1), ((1, 0), (1, 0))).astype(np.int64))


def build_lean(L):
    """The constants of the region `Zone7d L` of `SieveTwoZone7D`, scaled to integers, for exponents in units of
    1/DEN: with rho = DEN - a1 - a2, the region is `i0 <= i1 rho`, `m0 <= m1 a_i`, `c1 - lq a_i <= ll rho` and
    `c2 - lq (a1 + a2) <= ll rho`."""
    L = Fr(L)
    pieces = rl.parse('g7d')
    _, bd = gen_zone.threshold(pieces)
    lam = 2 * (1 - bd - gen_zone.W)
    ln, ld, an, ad = L.numerator, L.denominator, lam.numerator, lam.denominator
    mu = gen_zone.MU
    assert mu == Fr(1, 12500) and gen_zone.RHO0 == Fr(1, 2000) and gen_zone.MMIN == Fr(2, 3)
    X.update(lean=True, L=float(L), Z=dict(i0=DEN * ld, i1=2000 * ln, m0=2 * DEN * ld, m1=3 * ln,
                                           c1=12501 * DEN * ld * ad, c2=25001 * DEN * ld * ad,
                                           lq=ln * ad * 12500, ll=an * ln * 12500))


def zrect(l1, h1, l2, h2):
    """Whether the rectangle [l1, h1] x [l2, h2] of the two parts' exponents lies in `Zone7d L`: each of the region's
    six inequalities at the corner where it is tightest."""
    Z = X['Z']
    lq, ll = Z['lq'], Z['ll']
    return (Z['i0'] <= Z['i1'] * (DEN - h1 - h2) and Z['m0'] <= Z['m1'] * l1 and Z['m0'] <= Z['m1'] * l2
            and Z['c1'] - lq * l1 <= ll * (DEN - l1 - h2) and Z['c1'] - lq * l2 <= ll * (DEN - h1 - l2)
            and Z['c2'] - lq * (l1 + l2) <= ll * (DEN - l1 - l2))


def rect(P, l1, h1, l2, h2):
    """Whether the lattice rectangle that encloses [l1, h1] x [l2, h2] has no failing point."""
    d, T = X['d'], X['T']
    t1, u1, t2, u2 = l1 // d, -(-h1 // d), l2 // d, -(-h2 // d)
    if u1 > T or u2 > T:
        return False
    return P[u1 + 1][u2 + 1] - P[t1][u2 + 1] - P[u1 + 1][t2] + P[t1][t2] == 0


PAIRS = {}


def pairs(k):
    """The disjoint non-empty pairs of sets of k coordinates, as bit masks: unordered for two parts of primes, ordered
    (part, rest) for the cofactor's case."""
    if k not in PAIRS:
        full = (1 << k) - 1
        od = [(A, B) for A in range(1, full + 1) for B in range(1, full + 1) if A & B == 0]
        PAIRS[k] = ([p for p in od if p[0] < p[1]], od)
    return PAIRS[k]


def sums(xs):
    """The lower and upper sums of the sets of the cells `xs`, by bit mask."""
    k = len(xs)
    lo = [0] * (1 << k)
    hi = [0] * (1 << k)
    for S in range(1, 1 << k):
        b = S & -S
        c = xs[b.bit_length() - 1]
        lo[S] = lo[S ^ b] + c[0]
        hi[S] = hi[S ^ b] + c[1]
    return lo, hi


def eval2(xs):
    """Whether the estimate evaluates the box `xs`, a list of cells `(lo, hi)` in units of 1/DEN."""
    lo, hi = sums(xs)
    if X.get('lean'):
        un, od = pairs(len(xs))
        return (any(zrect(lo[A], hi[A], lo[B], hi[B]) for A, B in un)
                or any(zrect(lo[A], hi[A], DEN - hi[A] - hi[R], DEN - lo[A] - lo[R]) for A, R in od))
    P2, PC = X['P2'], X['PC']
    a0, a1, c0, c1, r1 = X['a0'], X['a1'], X['c0'], X['c1'], X['r1']
    un, od = pairs(len(xs))
    for A, B in un:        # the cofactor and the other primes are the rest
        if a0 <= lo[A] and hi[A] <= a1 and a0 <= lo[B] and hi[B] <= a1 and rect(P2, lo[A], hi[A], lo[B], hi[B]):
            return True
    for A, R in od:        # the cofactor and the other primes are the second part
        if c0 <= lo[A] and hi[A] <= c1 and hi[R] <= r1 and rect(PC, lo[A], hi[A], lo[R], hi[R]):
            return True
    return False


# --stops

def target(c0, c1):
    """The exponents a1 with (a1, rest) in the cofactor's region for every lattice value of the rest in [c0, c1]: the
    longest run, as its ends in units of 1/DEN, or None."""
    TI = X['TI']
    if (c0, c1) not in TI:
        okc, d = X['okc'], X['d']
        r = None
        if c1 < okc.shape[1]:
            idx = np.nonzero(okc[:, c0:c1 + 1].all(axis=1))[0]
            if len(idx):
                run = max(np.split(idx, np.nonzero(np.diff(idx) > 1)[0] + 1), key=len)
                r = (int(run[0]) * d, int(run[-1]) * d)
        TI[(c0, c1)] = r
    return TI[(c0, c1)]


def tstar2(xs):
    """`mirror8.tstar` with the estimate's stops as well."""
    T = TSTAR0(xs)
    lo, hi = sums(xs)
    d, V = X['d'], m8.G['V']
    for R in range(1, 1 << len(xs)):
        tg = target(lo[R] // d, -(-hi[R] // d))
        if tg is None or tg[1] - tg[0] < V:
            continue
        for A in range(1 << len(xs)):
            if A & R == 0 and hi[A] <= tg[1]:
                t2 = tg[0] - lo[A] if tg[0] > lo[A] else 0
                if T is None or t2 < T:
                    T = t2
    return T


# --bil

def ustar(a2):
    """Twice the bound that a1·Lnum must stay below in the second alternative, at a given a2."""
    Ln, Ld = m8.G['Lnum'], m8.G['Lden']
    c = Ld * DEN
    y = (2 * Ln - Ld) * DEN - 2 * a2 * Ln
    return 2 * (y - c) if y <= 2 * c else y


def condIB2(a1, a2):
    Ln, Ld = m8.G['Lnum'], m8.G['Lden']
    return a1 * Ln < (Ln - Ld) * DEN and (a1 + 2 * a2 < DEN or 2 * a1 * Ln < ustar(a2))


def dcp2(a1, a2):
    """The number of D >= 0 for which `condIB2` holds with D joined to a1, or to a2: the larger of the two."""
    Ln, Ld = m8.G['Lnum'], m8.G['Lden']
    c, lim1 = Ld * DEN, (Ln - Ld) * DEN
    xo = (lim1 - a1 * Ln - 1) // Ln + 1 if a1 * Ln < lim1 else 0
    yo = DEN - a1 - 2 * a2 if a1 + 2 * a2 < DEN else 0
    u2 = min(2 * lim1, ustar(a2))
    tnew = (u2 - 2 * a1 * Ln - 1) // (2 * Ln) + 1 if 2 * a1 * Ln < u2 else 0
    fo = fnew = 0
    if a1 * Ln < lim1:
        fo = (DEN - a1 - 2 * a2 - 1) // 2 + 1 if a1 + 2 * a2 < DEN else 0
        w = (2 * Ln - Ld) * DEN - (max(a1 * Ln, c) + a1 * Ln)
        fnew = (w - 2 * a2 * Ln - 1) // (2 * Ln) + 1 if 2 * a2 * Ln < w else 0
    return max(min(xo, yo), tnew, fo, fnew)


# the certificate

TSTAR0, COND0, DCP0 = m8.tstar, m8.condIB, m8.dcp
CAND0, NE30, ROW0 = m8.cand, m8.ne3, m8.row


def cand(i, j):
    return CAND0(i, j) and not eval2([m8.cell(i), m8.cell(j)])


def ne3(i, j, k):
    return NE30(i, j, k) and not eval2([m8.cell(i), m8.cell(j), m8.cell(k)])


def row(i, j, k, w):
    M = m8.lmask(i, j, k)
    ci, cj, ck = m8.cell(i), m8.cell(j), m8.cell(k)
    r = 0
    for l in range(min(k + 1, m8.lreg(m8.e(i) + m8.e(j) + m8.e(k)))):
        if not m8.bit(M, l) and not eval2([ci, cj, ck, m8.cell(l)]):
            w['c4'] += 1
            r += m8.cost4(i, j, k, l, w)
    return r


def run(W1, W2, N, L, depth=4, base=False, stops=False, bil=False, lean=False):
    """The total over K, the candidate cells, the decomposed ones, and the costs of the decomposed and of the dropped."""
    m8.setup(W1, W2, N, L)
    m8.G['key'] = (W1, W2, N, L)
    m8.cand, m8.ne3, m8.row, m8.tstar = CAND0, NE30, ROW0, TSTAR0
    m8.condIB, m8.dcp = (condIB2, dcp2) if bil else (COND0, DCP0)
    X.pop('lean', None)
    if not base:
        if lean:
            build_lean(L)
        else:
            build(Fr(L))
        m8.cand = cand if depth >= 2 else CAND0
        m8.ne3 = ne3 if depth >= 3 else NE30
        m8.row = row if depth >= 4 else ROW0
        if stops:
            m8.tstar = tstar2
    with Pool() as p:      # the workers are forked, with the tables and the patched functions
        out = dict(p.imap_unordered(m8.cell_row, [(W1, W2, N, L, i) for i in range(N)], chunksize=1))
    cells = [v for r in out.values() for v in r.values()]
    return (sum(v[0] for v in cells) / m8.K, len(cells), sum(v[1] for v in cells),
            sum(v[0] for v in cells if v[1]) / m8.K, sum(v[0] for v in cells if not v[1]) / m8.K)


def describe(base, depth, stops, bil, lean=False):
    s = 'the paper\'s certificate' if base else f'with the estimate to depth {depth}'
    s += ' on the region proved in Lean' if lean and not base else ''
    return s + (', its stops in the rule' if stops and not base else '') + (', the wider bilinear rule' if bil else '')


def window(pieces, L):
    """`density_payoff.window`: the sampled scan, then the exact corners, an end moving inward while a corner fails."""
    w = rl.window(pieces, L)
    if w is None:
        return None
    W1, W2 = round(w[0] * 100000), round(w[1] * 100000)
    while W1 < W2 and Fr(W2, 100000) * L > 1:
        fails, _, _ = rl.corners(pieces, L, W1, W2)
        if not fails:
            return W1, W2
        ends = {f[0] for f in fails}
        if 'one' in ends:
            return None
        W1 += 'lo' in ends
        W2 -= 'hi' in ends
    return None


def gridok(W1, W2, L, N):
    """`density_payoff.gridok`: the Lean's conditions on the grid and its coarse grid."""
    U1, U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
    V, nC = U2 - U1, N // 4
    H = (max(DEN // 2 - V, 0) + N - 1) // N
    HC = 4 * ((max(DEN // 2 - V, 0) + nC * 4 - 1) // (nC * 4))

    def ok(n, h):
        return (0 < h and U1 < U2 and 2 * U2 < DEN and 2 * (V + h * (n - 1)) < DEN and 4 * h <= V
                and DEN < 2 * (V + n * h))
    return (ok(N, H) and ok(nC, HC) and 4 * H + 2 * HC <= V and N * H <= nC * HC and HC == 4 * H
            and 4 * H + 4 * HC <= V and L * U2 > DEN)


def cmd_region(L):
    m8.setup(43457, 46959, 272, L)
    build(Fr(L))
    d, ok2 = X['d'], X['ok2']
    f = d / DEN
    print(f'L = {L}: the two parts lie in [{X["a0"] / DEN:.4f}, {X["a1"] / DEN:.4f}]; with the cofactor in a part, '
          f'the rest is at most {X["r1"] / DEN:.4f}')
    diag = [i for i in range(ok2.shape[0]) if ok2[i, i]]
    if diag:
        print(f'  a1 = a2 in [{diag[0] * f:.4f}, {diag[-1] * f:.4f}]: a rest between {1 - 2 * diag[-1] * f:.4f} and '
              f'{1 - 2 * diag[0] * f:.4f}')
    for rho in (0.04, 0.08, 0.12, 0.16):
        s = int(round((1 - rho) / f))
        best = max((abs(2 * i - s) for i in range(ok2.shape[0]) if 0 <= s - i < ok2.shape[0] and ok2[i, s - i]),
                   default=None)
        print(f'  rest {rho:.2f}: ' + ('none' if best is None else f'|a1 - a2| up to {best * f:.4f}'))


def main():
    a = sys.argv[1:]
    opt = {x: x in a for x in ('--base', '--stops', '--bil', '--lean')}
    a = [x for x in a if x not in opt]
    depth = 4
    if '--depth' in a:
        i = a.index('--depth')
        depth = int(a[i + 1])
        del a[i:i + 2]
    base, stops, bil, lean = opt['--base'], opt['--stops'], opt['--bil'], opt['--lean']
    if lean and stops:
        sys.exit('two_factor: --lean has no table of the region for --stops')
    if a and a[0] == 'region':
        cmd_region(a[1])
    elif a and a[0] == 'total':
        W1, W2, N, L = int(a[1]), int(a[2]), int(a[3]), a[4]
        t0 = time.time()
        t, nc, nd, cd, cx = run(W1, W2, N, L, depth, base, stops, bil, lean)
        print(f'grid [{W1}, {W2}]/1e5 n={N} L={L}, {describe(base, depth, stops, bil, lean)}: totalD/K {t:.7f}; '
              f'candidate cells {nc}, decomposed {nd} (cost {cd:.4f}), dropped {nc - nd} (cost {cx:.4f}); '
              f'{time.time() - t0:.0f} s')
    elif a and a[0] == 'scan':
        pieces = rl.parse('g7d')
        for s in a[1:]:
            L = Fr(s)
            w = window(pieces, L)
            N = w and next((n for n in range(272, 4000, 4) if gridok(w[0], w[1], L, n)), None)
            if not N:
                print(f'L = {s} ({float(L):.5f}): ' + ('no window' if w is None else f'window {w}, no grid'),
                      flush=True)
                continue
            Ls = f'{L.numerator}/{L.denominator}'
            line = f'L = {s} ({float(L):.5f}): window {w}, n = {N}'
            if base:
                line += f'; the paper\'s certificate {run(w[0], w[1], N, Ls, base=True, bil=bil)[0]:.5f}'
            t = run(w[0], w[1], N, Ls, depth, False, stops, bil, lean)
            print(line + f'; {describe(False, depth, stops, bil, lean)} {t[0]:.5f} ({t[1]} candidate cells, {t[2]} '
                  f'decomposed)', flush=True)
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main()
