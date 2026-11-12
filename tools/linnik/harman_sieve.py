#!/usr/bin/env python3
"""A Harman decomposition for the least prime in a progression that does not lean on the window.

    python3 tools/linnik/harman_sieve.py cells  2130/1000 [--h 0.002] [--flips 6] [--nest 2] ...
    python3 tools/linnik/harman_sieve.py points 2130/1000 ...
    python3 tools/linnik/harman_sieve.py parity 2130/1000 ...
    python3 tools/linnik/harman_sieve.py paper  11/5 ...

A computation in floating point, with no certificate: it says what a sieve built from the estimates below would
give, and those estimates are assumed here in the form stated (two of them are in Lean at the level of their bounds:
see the end). It needs a C compiler (`cc`, with OpenMP); the library is built in the system's temporary directory.

The setting is the paper's: x = q^L, the comparison of A = {n <= x : n = a mod q} with B / phi(q), exponents in
base x, tau = 1/L, theta = 1 - tau, and the same two inputs (the zero-free half-plane and the density curve `g7d`
of route_limits.py). The loss is what the lower bound for the primes of A falls short of the main term by, in
units of the main term: the sieve gives a positive lower bound when it is below 1. The paper's decomposition has a
floor equal to the window's width, evaluates a box only by the window, and stops where the window closes, at 13/6.
Here:

  * Type II. A box is evaluated by the window, where there is one, or by the estimate in two variables of
    two_factor.py: parts A and B of the product and a rest R of primes, with the exponent of A in the zone
    [Alo(rho), Ahi(rho)] of the rest's exponent rho. The cofactor of the term is in B or in the rest.
  * Type I. The products r P are in reach when they split as d1 d2 with d1 < x^theta and either d1 d2^2 < x (the
    paper's bilinear estimate, Lemma 4.2) or, with n = x / (d1 d2) the cofactor's length,
    (d2 / n) max(d1, q) max(n, q) < x (the same proof without the condition 2HD < q: the congruence
    t d2' = t' d2 mod q then has at most (2HD/q + 1) F solutions, not F). The second reaches moduli up to
    x / q^{1/2} whenever d1 lies between q and x / q.
  * The rule. S(A_r, x^f) is evaluated by Harman's comparison when its tree over the primes below x^f can be
    stopped by a Type II configuration before a leaf leaves the reach of Type I: the part that enters the zone is
    a set of the term's primes times the small primes, the rest is a set of the term's primes or the first small
    prime, and the zone is at least as wide as the largest step. The floor f is chosen for each term, the largest
    that passes; a term whose floor reaches its own sifting level is evaluated outright.
  * Role reversal. The numbers p_1 ... p_k m of a term are also r' k with k = p_j and r' = (r / p_j) m, and
    S(A_{r'}, k^{1/2}) has a Buchstab tree over the prime factors of k. A term may be treated through any of its
    primes (`--flips`: for terms of at most this many primes), and so may the terms of that tree (`--nest`).
  * A term that needs a lower bound may be dropped at the cost of its B-version; one that needs an upper bound
    may not.
  * Boundary terms. S(A_r, z) also counts n = r itself, when r is in A. Buchstab's identity on a box that is not
    regular at every point (the cofactor's exponent below the sifting level somewhere) has such terms among its
    children, where the new prime is the whole cofactor, so its children's cells run up to the cofactor's
    exponent; a box with such points is not empty, its drop pays for them too (in the main tree, where the cells
    are independent), and in a reversed tree it is not dropped and its term is not reversed.
  * Sieve bounds (`--sieve`, `--upper`; off by default, they change the values by less than 0.01). Where the rule
    fails at f, S(A_r, x^f) is bounded by the linear sieve of level x^T, T the reach of Type I beyond r: its main
    term is e^{-gamma} F(T/f) (upper bounds) or e^{-gamma} f(T/f) (lower bounds) where S(B_r, x^f) has Buchstab's
    omega, and the difference is the cost. A term that needs an upper bound can also get one from an upper-bound
    sieve on one of its primes.

`cells` takes every test and every cost conservatively on boxes of cells (side `--h` for the first four primes,
coarser below), so its value bounds the loss of this decomposition from above, up to floating point and to the
lattice on which the zone is tabulated. `points` replaces each cell by its midpoint: the limit of fine cells, a
model. `parity` runs `cells` with the sieve bounds and with no Type II information at all; the sieve then must not
detect primes, so the value must be at least 1 (it is about 3). `paper` runs `cells` in the paper's set-up: the
window alone, Lemma 4.2, the window's width as the floor, no reversal.

Values of the loss (10 November 2026; reversal for terms of at most 6 primes, nested twice; `cells` with
--h 0.002, four to seven minutes each on four cores; `points` with --h 0.004):

    L        11/5    2.18    2.16    2.15    2.14    2.13    2.12    2.11    2.10
    cells    0.033   0.163   0.400   0.511   0.634   0.765   0.924   1.097   1.273
    points   0.013   0.090   0.285   0.364   0.459   0.569   0.690   0.849   1.011

(Before the boundary terms were paid for, the cells gave 0.920 at 2.12 and 0.761 at 2.13.) At 2.13 with
--h 0.004 the cells give 1.006; with --nest 1, 1.090; with --flips 4 --nest 1, 1.269; with --flips 0, 1.426;
with --plain, 1.174; with --sieve --upper, 0.999. `paper` at 11/5 gives 0.862 with --h 0.002 and 0.800 with
--h 0.001, where the paper's certificate has 0.932 on its grid, and `parity` gives 3.0.

What the reversal needs (`--rev`; at 2.19 with --no-window --nest 1 --h 0.007, where the cells give 0.463): with
`even`, 1.059, and with `odd`, 0.512, so it is the terms that need an upper bound; with `linear`, 1.091, so it
is the bilinear Type I estimate inside the reversed trees; with `prime`, 0.659; with `floor`, 0.474; with
`offdiag`, 0.468. How large a tree passes: with --flips 0 the cells are below 1 at 2.19 only (0.866 with the
window and --h 0.005, 276000 nodes; 1.066 at 2.18); with --no-window --flips 3 --nest 1 --h 0.01 they give
0.809 at 2.19 with 113000 nodes; with --no-window --nest 1 --h 0.007, 0.749 at 2.17 with 10^6 nodes; with
--no-window --h 0.005, 0.489 at 2.17 with 1.4 10^7 nodes; and the table's tree at 2.12 has 4.7 10^9 nodes.

Which reversals (more of `--rev`; 11 November 2026, at 2.15 with --no-window --h 0.004, where the cells give
1.280 with --flips 0 and 0.688 with --flips 6 --nest 2). A term of the main tree needs to be opened through its
largest prime only: --flips 5 --nest 2 --rev first gives 0.697. From there, each alone: `m2` (a cofactor of at
most two primes) 0.846, `m3` 0.758; `odd` 0.797; --nest 1, 0.832, with `odd` 0.867, with `odd,low` (the reversal
as an inequality, sifted below every atom) 0.925; and inside a reversed tree `natom` (only a prime of r') 0.738,
`nodd` 0.698, `nchain` (only the chain's first prime) 0.823, `nc1` (only chains of one prime) 0.773. The shapes
that are in Lean (--flips 3 --nest 1 --rev odd,first,m2,low) give 0.998. `points` gives for those 0.662 at 2.15,
0.962 at 2.13 and 1.104 at 2.12, and for --flips 5 --nest 2 --rev first 0.365, 0.573 and 0.694. With `--fill`
(the stops whose rest is a small prime as SieveFillComp.prop6_fill has them) and --flips 0 the cells give 1.230
at 2.165 with --h 0.005, where the exact search of fill_cert.py without reversal has 1.221; with the shapes in
Lean, 0.851, where that search has 0.951.

What a tree without reversal needs (`--no-first`, `--direct`; at 2.19 with --flips 0 --h 0.005). Without the
stops whose rest is the first small prime, the top node's floor is the window's width and the cells give 0.945,
with 307000 nodes (0.967 with --plain; 0.865 at 2.195). Of the ways to evaluate a box outright, the window is
needed (1.102 with --direct second,rest) and so is the estimate with the cofactor in the second variable (1.202
with --direct window,rest); the cofactor in the rest is not (0.945 with --direct window,second).

What is assumed, beyond the paper: the estimate in two variables on the tabulated zone (two_factor.py states it;
in Lean it is proved on the region SieveTwoZone7D.Zone7d, which holds all of the zone but under 2% of its width,
as far as chains of primes: SieveTwoChain.chain_two); the bilinear Type I estimate without 2HD < q at the leaves
(in Lean: SieveTypeIBAsymWide.leaves_ib_wide); Harman's comparison with these stops and these leaves (in Lean
for a rest among the term's primes: SieveTwoComp.prop6_two); the same with the first small prime as the rest,
where the small primes below the least rest that the zone takes (eps0) are left to Type I at no cost, which is
Brun's sieve at a fixed level, whose gap is tiny but not o(1); role reversal, with the conditions that tie the
variables of a reversed term together removed; and, with `--sieve` and `--upper`, the linear sieve's bounds F
and f with the bilinear remainder and well-factorable weights. Here "the paper" is the Linnik paper's version at 11/5 (in the git history); the paper now proves 43/20
(Linnik21500.linnik_21500, hint_cert.py), with no window. In Lean, this decomposition with the window,
without role reversal and without the stops whose rest is the first small prime gives the exponent 219/100
(Linnik21900.linnik_21900; tree_cert.py is its search in exact integers), and with the reversal of a term of
three primes through its largest, at one level, the exponent 218/100 (Linnik21800.linnik_21800; rev_cert.py).
In this computation, with one level of reversal for terms of at most three primes (--flips 3 --nest 1 --no-first
--h 0.007) the cells give 0.863 at 2.18 with 463000 nodes and 1.042 at 2.17; with --rev prime,offdiag they give
1.067 at 2.18.
"""
import argparse
import ctypes as C
import hashlib
import math
import os
import subprocess
import sys
import tempfile
import time
from fractions import Fraction as Fr

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

MAXK = 11
DL = 0.0005                     # the lattice of the zone's tables, in the rest and in the part
A0, A1, R1 = 0.30, 0.62, 0.22
DW = DS = 0.001
dp = C.POINTER(C.c_double)
ip = C.POINTER(C.c_int)


class Ctx(C.Structure):
    _fields_ = [('tau', C.c_double), ('theta', C.c_double), ('eps1', C.c_double), ('wide', C.c_int),
                ('NR', C.c_int), ('DL', C.c_double), ('Alo', dp), ('Ahi', dp),
                ('rmax', C.c_double), ('amin', C.c_double), ('amax', C.c_double),
                ('f0hi', dp), ('f0t', dp), ('f0ok', ip), ('f0lo', C.c_int),
                ('haswin', C.c_int), ('u1', C.c_double), ('u2', C.c_double),
                ('NW', C.c_int), ('DW', C.c_double), ('om', dp),
                ('NS', C.c_int), ('DS', C.c_double), ('Fm1', dp), ('omf', dp),
                ('step', C.c_double * (MAXK + 2)), ('maxdepth', C.c_int),
                ('use_ub', C.c_int), ('use_lb', C.c_int), ('use_rev', C.c_int),
                ('fmin', C.c_double), ('smax', C.c_double),
                ('flip', C.c_int), ('flipdepth', C.c_int), ('flipmax', C.c_int), ('flipmin', C.c_double),
                ('wmin', C.c_double), ('split', C.c_int), ('splitdepth', C.c_int), ('pointwise', C.c_int),
                ('rev_odd', C.c_int), ('rev_even', C.c_int), ('rev_prime', C.c_int), ('rev_linear', C.c_int),
                ('rev_floor', C.c_int), ('rev_offdiag', C.c_int),
                ('rev_first', C.c_int), ('rev_m2', C.c_int), ('rev_m3', C.c_int), ('rev_low', C.c_int),
                ('rev_natom', C.c_int), ('rev_nchain', C.c_int), ('rev_nodd', C.c_int), ('rev_nc1', C.c_int),
                ('ev_win', C.c_int), ('ev_second', C.c_int), ('ev_rest', C.c_int)]


class Stats(C.Structure):
    _fields_ = [('nodes', C.c_long * (MAXK + 2))]


_LIB = None


def lib():
    """The compiled library, built once for each version of the source."""
    global _LIB
    if _LIB is None:
        src = os.path.join(HERE, 'harman_sieve.c')
        tag = hashlib.sha256(open(src, 'rb').read()).hexdigest()[:16]
        so = os.path.join(tempfile.gettempdir(), f'harman_sieve_{tag}.so')
        if not os.path.exists(so):
            tmp = f'{so}.{os.getpid()}'
            subprocess.run([os.environ.get('CC', 'cc'), '-O2', '-fopenmp', '-shared', '-fPIC', '-o', tmp, src, '-lm'],
                           check=True)
            os.replace(tmp, so)
        _LIB = C.CDLL(so)
        _LIB.hs_loss.restype = C.c_double
        _LIB.hs_loss.argtypes = [C.POINTER(Ctx), C.c_double, C.c_int, dp, C.POINTER(Stats)]
    return _LIB


def zones(L, curve='g7d', margin=None, samples=60):
    """For each rest rho = c DL: the interval [Alo, Ahi] of the exponents a1 of the first part for which the
    estimate in two variables holds, the second part being 1 - a1 - rho (the longest run on the lattice)."""
    bs, gs = [], []
    for lo, hi, A in rl.parse(curve):
        b = np.linspace(float(lo), float(hi), samples)
        bs.append(b)
        gs.append(np.ones_like(b) if A is None else float(A) * (1 - b))
    b, g = np.concatenate(bs), np.concatenate(gs)
    Lf, w = float(L), 4e-6
    thr = Lf - (float(rl.MARGIN) if margin is None else margin)
    a = A0 + DL * np.arange(int(round((A1 - A0) / DL)) + 1)
    r = DL * np.arange(int(round(R1 / DL)) + 1)
    ms = a * Lf
    Bs = 5 / 12 + ms / 12 + (1 - ms) / 1000 + 2 / 1000
    a2 = 1.0 - a[:, None] - r[None, :]
    m2 = a2 * Lf
    B2 = 5 / 12 + m2 / 12 + (1 - m2) / 1000 + 2 / 1000
    fail = (a2 <= 0) | (r[None, :] <= 0)
    for bb, gg in zip(b, g):
        M = np.where(ms > 1, ms, np.minimum(1.0, np.maximum(ms, gg + Bs)))
        T1 = -ms * (bb + w) + ms / 2 + M / 2
        M2 = np.where(m2 > 1, m2, np.minimum(1.0, np.maximum(m2, gg + B2)))
        fail |= Lf * (bb + w) + T1[:, None] + (-m2 * (bb + w) + m2 / 2 + M2 / 2) > thr
    ok = ~fail
    Alo = np.full(len(r), np.inf)
    Ahi = np.full(len(r), -np.inf)
    for c in range(len(r)):
        idx = np.nonzero(ok[:, c])[0]
        if len(idx):
            run = max(np.split(idx, np.nonzero(np.diff(idx) > 1)[0] + 1), key=len)
            Alo[c], Ahi[c] = a[run[0]], a[run[-1]]
    return r, Alo, Ahi


def buchstab(umax=14.0):
    """Buchstab's function on the lattice u = 1 + i DW: omega = 1/u on [1, 2], (u omega)' = omega(u - 1)."""
    n1 = int(round(1 / DW))
    n = int(round((umax - 1) / DW)) + 1
    u = 1 + DW * np.arange(n)
    om, P = np.zeros(n), np.zeros(n)
    om[:n1 + 1] = 1 / u[:n1 + 1]
    P[:n1 + 1] = 1.0
    for i in range(n1 + 1, n):
        P[i] = P[i - 1] + DW * (om[i - 1 - n1] + om[i - n1]) / 2
        om[i] = P[i] / u[i]
    return om


def linear_sieve(smax=16.0):
    """F(s) - 1 and 1 - f(s) on the lattice s = i DS: s F = 2 e^gamma for s <= 3, f = 0 for s <= 2,
    (s F)' = f(s - 1), (s f)' = F(s - 1)."""
    n1 = int(round(1 / DS))
    n = int(round(smax / DS)) + 1
    s = DS * np.arange(n)
    P = np.full(n, 2 * math.exp(0.5772156649015329))
    Q = np.zeros(n)
    for i in range(2 * n1 + 1, n):
        Q[i] = Q[i - 1] + DS * (P[i - 1 - n1] / s[i - 1 - n1] + P[i - n1] / s[i - n1]) / 2
        if i > 3 * n1:
            P[i] = P[i - 1] + DS * (Q[i - 1 - n1] / s[i - 1 - n1] + Q[i - n1] / s[i - n1]) / 2
    F = np.where(s > 0, P / np.maximum(s, 1e-12), 1e9)
    f = np.where(s > 0, Q / np.maximum(s, 1e-12), 0.0)
    return np.ascontiguousarray(F - 1), np.ascontiguousarray(1 - f)


def window(L):
    """The paper's window at L, or None (the corners are tested as in density_payoff.py)."""
    pieces = rl.parse('g7d')
    w = rl.window(pieces, L)
    if w is None:
        return None
    W1, W2 = round(w[0] * 100000), round(w[1] * 100000)
    while W1 < W2 and Fr(W2, 100000) * L > 1:
        fails, _, _ = rl.corners(pieces, L, W1, W2)
        if not fails:
            return W1 / 100000, W2 / 100000
        ends = {f[0] for f in fails}
        if 'one' in ends:
            return None
        W1 += 'lo' in ends
        W2 -= 'hi' in ends
    return None


class Sieve:
    def __init__(self, L, h=0.004, depth=8, flips=6, nest=2, flipmax=8, flipmin=0.15, wide=True, usewin=True,
                 sieve=False, upper=False, type2=True, eps1=0.002, eps0=0.002, fmin=0.01, smax=7.0, shrink=0.0,
                 tables=None, rev=(), first=True, direct=('window', 'second', 'rest'), fill=False):
        L = Fr(L)
        self.L, Lf = L, float(L)
        r, Alo, Ahi = tables if tables is not None else zones(L)
        Alo, Ahi = Alo + shrink / 2, Ahi - shrink / 2          # a narrower zone, to see what the width is worth
        ok = np.isfinite(Alo) & (Alo <= Ahi) if type2 else np.zeros(len(r), dtype=bool)
        idx = np.nonzero(ok)[0]
        # the cells lean on this: one run of rests, and the zone's ends decrease as the rest grows
        assert not len(idx) or (idx[-1] - idx[0] + 1 == len(idx) and np.all(np.diff(Alo[idx]) <= 1e-12)
                                and np.all(np.diff(Ahi[idx]) <= 1e-12))
        NR = len(r) - 1
        self.Alo = np.ascontiguousarray(np.where(ok, Alo, 1e300))
        self.Ahi = np.ascontiguousarray(np.where(ok, Ahi, -1e300))
        # the stops whose rest is the first small prime, of exponent between eps0 and f = c DL
        self.f0ok = np.zeros(NR + 1, dtype=np.int32)
        self.f0hi = np.full(NR + 1, 1e300)
        self.f0t = np.full(NR + 1, -1e300)
        hi, t = np.inf, -np.inf
        for c in range(int(round(eps0 / DL)), NR + 1):
            if fill:
                # the rest among the tree's primes, as SieveFillComp.prop6_fill has it: the zone on the whole
                # rectangle of the rests up to r[c], and a first variable that grows by steps of r[c]
                if not (ok[c] and ok[1] and Ahi[c] - Alo[1] > r[c]):
                    break
                hi, t = min(hi, Ahi[c]), max(t, Alo[1] + r[c])
            else:
                if not (ok[c] and Ahi[c] - Alo[c] >= r[c]):
                    break
                hi, t = min(hi, Ahi[c]), max(t, Alo[c] + r[c])
            self.f0ok[c], self.f0hi[c], self.f0t[c] = 1, hi, t
        if not first:
            self.f0ok[:] = 0
        self.om = buchstab()
        self.Fm1, self.omf = linear_sieve()
        ctx = Ctx()
        ctx.tau, ctx.theta, ctx.eps1, ctx.wide = 1 / Lf, 1 - 1 / Lf, eps1, int(wide)
        ctx.NR, ctx.DL = NR, DL
        ctx.Alo, ctx.Ahi = self.Alo.ctypes.data_as(dp), self.Ahi.ctypes.data_as(dp)
        ctx.rmax = float(r[idx[-1]]) if len(idx) else 0.0
        ctx.amin = float(Alo[idx].min()) if len(idx) else 9.0
        ctx.amax = float(Ahi[idx].max()) if len(idx) else -9.0
        ctx.f0hi, ctx.f0t = self.f0hi.ctypes.data_as(dp), self.f0t.ctypes.data_as(dp)
        ctx.f0ok = self.f0ok.ctypes.data_as(ip)
        ctx.f0lo = int(np.argmax(self.f0ok)) if self.f0ok.any() else NR + 1
        self.win = window(L) if (usewin and type2) else None
        ctx.haswin = int(self.win is not None)
        if self.win:
            ctx.u1, ctx.u2 = self.win
            ctx.amin, ctx.amax = min(ctx.amin, self.win[0]), max(ctx.amax, 1 - self.win[0])
        ctx.NW, ctx.DW, ctx.om = len(self.om), DW, self.om.ctypes.data_as(dp)
        ctx.NS, ctx.DS = len(self.Fm1), DS
        ctx.Fm1, ctx.omf = self.Fm1.ctypes.data_as(dp), self.omf.ctypes.data_as(dp)
        # the cells' sides: h for the first four primes, then 2h, 3h, 4h in pairs
        self.steps = [h * (1 if d <= 4 else 1 + (d - 3) // 2) for d in range(1, MAXK + 3)]
        for d in range(MAXK + 2):
            ctx.step[d] = self.steps[max(d - 1, 0)]
        ctx.maxdepth = depth
        ctx.use_ub = ctx.use_lb = int(sieve)
        ctx.use_rev = int(upper)
        ctx.fmin, ctx.smax = fmin, smax
        ctx.flip, ctx.flipdepth, ctx.flipmax, ctx.flipmin = (nest if flips > 0 else 0), flips, flipmax, flipmin
        ctx.wmin, ctx.split, ctx.splitdepth = 0.0005, 0, 0
        for name in ('odd', 'even', 'prime', 'linear', 'floor', 'offdiag', 'first', 'm2', 'm3', 'low', 'natom',
                     'nchain', 'nodd', 'nc1'):
            setattr(ctx, 'rev_' + name, int(name in rev))
        ctx.ev_win, ctx.ev_second, ctx.ev_rest = (int(name in direct) for name in ('window', 'second', 'rest'))
        self.ctx = ctx
        # the floor of the top node: the largest f at which S(A, x^f) is evaluated
        T = ctx.theta - eps1
        cs = [c for c in range(1, NR + 1) if self.f0ok[c] and max(self.f0t[c], r[c]) < T]
        self.nu0 = float(r[max(cs)]) if cs else None
        self.width = float((Ahi[idx] - Alo[idx]).max()) if len(idx) else 0.0
        self.rmax = ctx.rmax

    def loss(self, pointwise=False, nu=None):
        nu = self.nu0 if nu is None else nu
        self.ctx.pointwise = int(pointwise)
        n1 = max(1, int(math.ceil((0.5 - nu) / self.steps[0])))
        prof = np.zeros(n1)
        st = Stats()
        v = lib().hs_loss(C.byref(self.ctx), nu, n1, prof.ctypes.data_as(dp), C.byref(st))
        return v, int((prof > 1e200).sum()), sum(st.nodes)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('command', choices=['cells', 'points', 'parity', 'paper'])
    ap.add_argument('L', nargs='+', help='exponents, as fractions a/b')
    ap.add_argument('--h', type=float, default=None, help='side of the cells of the first four primes')
    ap.add_argument('--depth', type=int, default=8, help='primes in a term of the main tree')
    ap.add_argument('--flips', type=int, default=6, help='role reversal for terms of at most this many primes')
    ap.add_argument('--nest', type=int, default=2, help='reversals inside a reversed tree')
    ap.add_argument('--flipmax', type=int, default=8, help='atoms in a term of a reversed tree')
    ap.add_argument('--plain', action='store_true', help="the paper's bilinear estimate only")
    ap.add_argument('--sieve', action='store_true', help='with the linear sieve bounds')
    ap.add_argument('--upper', action='store_true', help='with the upper-bound sieve on a prime')
    ap.add_argument('--no-window', action='store_true')
    ap.add_argument('--fill', action='store_true', help="the stops whose rest is a small prime in the form of "
                    'SieveFillComp.prop6_fill (the rest among the primes of the tree below the stop)')
    ap.add_argument('--flipmin', type=float, default=0.15, help='the least exponent of a prime that is opened')
    ap.add_argument('--shrink', type=float, default=0.0, help='narrow every zone by this much')
    ap.add_argument('--nu', type=float, default=None, help='floor of the top node (default: the largest)')
    ap.add_argument('--rev', default='', help='restrictions on the reversal, comma-separated: odd or even (only '
                    'the terms that need an upper bound, or a lower bound), prime (only where the cofactor is '
                    'prime on the whole box), linear (the linear Type I estimate alone in reversed trees), floor '
                    '(floors below every atom of a reversed term), offdiag (the cell of the reversed prime apart '
                    "from its neighbours'), first (a term of the main tree only through its largest prime), m2 or m3 "
                    '(only where the cofactor has at most two, or three, primes), low (as an inequality, sifted '
                    'below every atom, for the terms that need an upper bound only), and in a reversed tree: natom '
                    "(only a prime of r'), nchain (only the first prime of the chain), nodd (only the terms that "
                    'need an upper bound), nc1 (only the terms with a chain of one prime)')
    ap.add_argument('--no-first', action='store_true', help='no stop whose rest is the first small prime (the top '
                    "node's floor is then the window's width, or --nu)")
    ap.add_argument('--direct', default='window,second,rest', help='how a box may be evaluated outright, '
                    'comma-separated: window, second (the estimate, the cofactor in the second variable), rest '
                    '(the estimate, the cofactor in the rest)')
    a = ap.parse_args()
    h = a.h if a.h is not None else (0.004 if a.command == 'points' else 0.002)
    for Ls in a.L:
        t = time.time()
        if a.command == 'paper':
            s = Sieve(Ls, h=h, depth=a.depth, flips=0, wide=False, shrink=1.0, eps1=0.0)
            if s.win is None:
                print(f'paper L = {Ls}: no window')
                continue
            nu = s.win[1] - s.win[0] - 1e-9
        else:
            s = Sieve(Ls, h=h, depth=a.depth, flips=a.flips, nest=a.nest, flipmax=a.flipmax, flipmin=a.flipmin,
                      fill=a.fill, wide=not a.plain,
                      usewin=not a.no_window, sieve=a.sieve or a.command == 'parity',
                      upper=a.upper or a.command == 'parity', shrink=a.shrink, type2=a.command != 'parity',
                      rev=tuple(x for x in a.rev.split(',') if x), first=not a.no_first,
                      direct=tuple(x for x in a.direct.split(',') if x))
            if a.nu is not None:
                nu = a.nu
            elif s.nu0 is not None:
                nu = s.nu0
            elif s.win is not None:
                nu = s.win[1] - s.win[0] - 1e-9
            elif a.no_first:
                print(f'{a.command} L = {Ls}: no window and no stop with a small prime as the rest, so no floor '
                      'for the top node')
                continue
            else:
                nu = 0.05
        v, bad, nodes = s.loss(pointwise=a.command == 'points', nu=nu)
        print(f'{a.command} L = {Ls} ({float(s.L):.4f}), h = {h}: loss {v:.4f}'
              + (f' ({bad} cells of depth 1 with no bound)' if bad else '')
              + f'; floor {nu:.4f}, widest zone {s.width:.4f}, rests up to {s.rmax:.4f}, window {s.win}; '
              f'{nodes} nodes, {time.time() - t:.0f} s', flush=True)


if __name__ == '__main__':
    main()
