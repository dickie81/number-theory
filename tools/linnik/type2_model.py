#!/usr/bin/env python3
"""type2_model.py [regions L ... | harman05 | widen | zone SET L ... | check]: which Type II sums over the characters
mod q the large-value tools bound: Harman's region of 2005 beside the paper's, and what the paper's inputs add to it.

A model, in floating point: nothing in the library or in the paper depends on it.

The model.  Exponents are in base x, and q = x^tau (tau = 1/L, theta = 1 - tau).  A sum over the non-trivial
characters of |F1(chi) F2(chi) K(chi)|, with F1 and F2 of lengths x^{a1}, x^{a2} and arbitrary coefficients and a
prime-factored rest K of length x^rho (a product of sums over primes, or a sifted variable), a1 + a2 + rho = 1, is
split by the sizes |F_i(chi)| ~ x^{l_i}, |K(chi)| ~ x^{l_K} (a profile).  At most x^c characters have a given
profile, c the least of the bounds below, and they contribute x^{c + l_1 + l_2 + l_K}; so the sum is << x^{1 - delta}
when E, the largest such exponent, is below 1.  Each bound is for a sub-product G of the three (length x^a, level l)
raised to a power k >= 1, for one modulus q and bounded t:

    MVT   orthogonality                                 max(tau, k a) + k a - 2 k l
    HM    the Halasz-Montgomery inequality              2 k (a - l)   where 2 k l - k a >= the kernel's exponent:
                                                        tau/2 (Polya-Vinogradov), or with the half-plane
                                                        tau (5/12 + m/12) for a length q^m, m <= 1
    HUX   Huxley's large values estimate                max(2 k (a - l), tau + k (4 a - 6 l))
    CGL   Chen, Gupta and Li's Proposition 3.1          max(2 k (a - l), tau/2 + k (3 a - 4 l), 4 tau/3 + k (2 a - 4 l))
          (the paper's Input 2)                         for k a >= 2 tau/3 and 7/10 <= l/a (beyond 4/5: its value there)
    DENS  the density curve, for K only                 tau g(l_K / rho), g the curve g7d (route_limits.py): a large
                                                        prime sum has a zero behind it
    cap   the half-plane, for K only                    l_K <= (11/12) rho

Huxley's Theorem 1 (Large values of Dirichlet polynomials III) holds for the characters to one modulus with D = q T
and any coefficients (formalisations/huxley-density.md; in Lean: LinnikReflect.huxley_large_values), so HUX asks
nothing of q.  Its condition V > c G^{1/2} N^{1/4} is not imposed: where it fails, MVT is the smaller bound.

For a count x^{c0} the profiles are those with l_S <= psi_S(c0) for every sub-product S, psi_S the inverse of the
least bound for S; the largest l_1 + l_2 + l_K under these constraints is a linear programme in three variables, whose
dual has half-integral vertices, so it is the least of sum_S y_S psi_S over the covers y in {0, 1/2, 1}^7 of the three
factors: exact.  E is the largest c0 + M(c0), by branch and bound over c0 (M decreases), to a certified tolerance.

The sets of tools:

    H1     MVT, HM (Polya-Vinogradov) on everything; HUX on the powers of the rest only; a (log x)^{-A} saving on K
    H      the same with HUX on every sub-product: Harman's information (2005: (i), (ii), (iv))
    H+cap  H with the half-plane's saving on the prime sums in the place of (log x)^{-A}
    +DENS, +kernel   one after the other: the density curve for K, the half-plane's kernel in HM
    all    all of these and CGL on every sub-product
    ours   MVT and HM on the sums themselves (k = 1), the half-plane's kernel, DENS and the cap: the paper's estimate
           in two variables (two_factor.py, harman_sieve.zones)

With a (log x)^{-A} saving only (H1, H), a configuration passes when no profile with K below its largest size reaches
E = 1 (the profiles with l_K <= rho - 10^-4 must have E <= 1 - 10^-5); with the cap, when E <= 1 - 10^-4.  The trivial
bound, Cauchy-Schwarz and orthogonality on two sub-products longer than q, gives E = 1 exactly, so E <= 1 alone decides
nothing.

`harman05`: Harman's Type II condition (On the number of Carmichael numbers up to x, 2005, p. 646: |a1 - a2| <
2 theta - 1 and rho < gamma(theta) = min(4 theta - 2, (20 theta - 9)/11, (72 theta - 37)/11)) is the case g = 3 of
Baker, Harman and Pintz's gamma_g = min(4 theta - 2, ((8g - 4) theta - (4g - 3))/(4g - 1), (24 g theta - (12g + 1))/
(4g - 1)) (their Lemma 9 of 2001; Harman, Kumchev and Lewis's Lemma 4, who take g = 4 at theta = 0.53).  The last rho
that passes on a1 = a2 (17 November 2026):

    L (theta)          gamma_3    max_g gamma_g   4 theta - 2    H1        H         all       ours
    2.06   (0.5146)    0.0044     0.0579          0.0583         0.0570    0.0579    0.0613    0.0522
    2.08   (0.5192)    0.0350     0.0769          0.0769         0.0754    0.0769    0.0819    0.0691
    2.10   (0.5238)    0.0649     0.0952          0.0952         0.0952    0.0977    0.1016    0.0858
    2.12   (0.5283)    0.0943     0.1132          0.1132         0.1109    0.1195    0.1238    0.1021
    125/59 (0.528)     0.0924     0.1120          0.1120         0.1090    0.1189    0.1232    0.1010
    100/47 (0.53)      0.1055     0.1200          0.1200         0.1187    0.1226    0.1315    0.1083

In base q, with F_i = q^{1 - s_i} and K = q^r: |a1 - a2| < 2 theta - 1 is s_1, s_2 < r/2, and rho < 4 theta - 2 is
s_1 + s_2 < r/2.  H1's region is max(s_1, 0) + max(s_2, 0) < max(1/(2 ceil(1/r)), 2r/3 - 1/(6 floor(1/r))), which is at
most r/2, with equality when 1/r is an integer: Harman's two conditions are its envelope.  The other two terms of
gamma_g are the condition of H for the one power K^g.  So H1 is inside Harman's region and Harman's inside H (no
point of 2400 inside his closed form fails H), each strictly.  What decides all three is one kind of profile: about
q^{1/2} characters at which K, F1 and F2 are near the power 3/4 of their lengths.  The count q^{1/2} at that size is
the count of the density hypothesis, and the powers K^g with g r near 1 have it; the density curve has q^{0.572}
there, which is why the paper's region has 0.442 r where Harman's has r/2 (0.442 = 2 (1 - 0.7789), and 0.7789 is where
the curve of the paper's estimate comes down to q^{1/2}).

`widen`: the half-plane's saving on the prime sums in the place of Harman's (log x)^{-A} does not move his region:
H+cap, with DENS and with the kernel as well, has the same diagonal as H to 0.0006 (the stricter margin), and the same
table of zones but for one step of the lattice at a few rests.  The cap acts on profiles with K near its largest size,
the kernel on profiles with few characters, and the curve has more characters than the powers at the size 3/4.  What
it changes is the saving: a power of x in the interior of the region, which the comparisons of the sieve need.  What
widens the region is Huxley's estimate on the two arbitrary factors (H against H1 and against the closed form) and
Input 2 on them and on the powers of the rest (all): at L = 21/10 the diagonal goes from 0.0952 to 0.0977 and 0.1016,
and the zone of a1 at rho = 0.08 from 0.0476 wide to 0.054 and 0.062.  For every tool listed a necessary condition is
s_1 + s_2 < r (1/2 + max(s_1, s_2)), which `all` attains at r = 1/g: beyond Harman's r/2 there is only a term of the
second order in r.

`zone SET L ...`: the table of a set on the lattice of harman_sieve.py (the rests rho = c/2000, the first part's
exponents 0.30 + j/2000), the run of a1 that passes through the diagonal, written as zones_SET_L.npz in the current
directory; harman_sieve.py reads it with --zone-file, or computes it with --region.

`regions L ...`: at each exponent, side by side: Harman's region as printed in 2005, with g = 4 and with the largest
gamma_g; the model's regions H and all; the paper's region in two variables (its Definition 3.1); the window of the
estimate in one variable (route_limits.window: none below 13/6); and the leaves' region (gen_leafzone.py: empty
below L = 2.0870).

`check`: the two searches (over the count, and over boxes of profiles) agree at random configurations; every sampled
point of Harman's closed form passes H; `ours` agrees with harman_sieve.zones at 21/10 to one step of the lattice.

Needs numpy.  `harman05` and `widen` take about two minutes each, `check` about three.
"""
import itertools
import math
import os
import sys
import time
from fractions import Fraction as Fr

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

SUBSETS = [(0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]   # the factor 2 is the rest K
SUBMAT = np.array([[1 if i in S else 0 for S in SUBSETS] for i in range(3)])


def _covers():
    """The minimal covers y in {0, 1/2, 1}^7 of the three factors by the seven sub-products."""
    cov = [np.array(y) for y in itertools.product((0.0, 0.5, 1.0), repeat=7)
           if np.all(SUBMAT @ np.array(y) >= 1 - 1e-12)]
    cov = np.array(cov)
    keep = [y for y in cov if not (np.all(cov <= y + 1e-12, axis=1) & np.any(cov < y - 1e-12, axis=1)).any()]
    return np.array(keep)


COVERS = _covers()

# ---------------------------------------------------------------------------------------------- the density curve
G7D = [(float(lo), float(hi), None if A is None else float(A)) for lo, hi, A in rl.parse('g7d')]


def g_env(sig):
    """The decreasing envelope of g7d on [0, 11/12): the least value of the curve up to sig (the number of
    characters with a zero to the right of sig decreases with sig); no character from 11/12 on."""
    sig = np.atleast_1d(np.asarray(sig, dtype=float))
    out = np.where(sig < 11 / 12, 1.0, -np.inf)
    for lo, hi, A in G7D:
        if A is not None:
            out = np.minimum(out, np.where(sig >= lo, A * (1 - np.minimum(hi, sig)), np.inf))
    return out


def sigma_star(y):
    """The largest sigma at which the envelope is at least y (11/12 for y <= 0; none for y > 1)."""
    y = np.asarray(y, dtype=float)
    best = np.where(y > 1.0, -np.inf, 11 / 12)
    for lo, hi, A in G7D:
        if A is None:
            cand = np.where(1.0 < y, lo, np.inf)
        else:
            s0 = np.maximum(lo, 1 - y / A)
            cand = np.where(s0 < hi, s0, np.inf)
        best = np.minimum(best, cand)
    return best


# ---------------------------------------------------------------------------------------------- the sets of tools
SETS = ('H1', 'H', 'H+cap', 'H+cap+DENS', 'H+cap+DENS+kernel', 'all', 'ours',
        'H1+CGL', 'H+CGL', 'H1+CGL+cap', 'H+CGL+cap')


def toolset(name):
    """hux: None, 'rest' (the powers of K only) or 'all'; cap: the largest l_K / rho (1: a (log x)^{-A} saving)."""
    ts = dict(name=name, kernel='pv', hux=None, cgl=False, dens=False, cap=1.0, k1=False)
    if name == 'H1':
        ts.update(hux='rest')
    elif name == 'H':
        ts.update(hux='all')
    elif name == 'H+cap':
        ts.update(hux='all', cap=11 / 12)
    elif name == 'H+cap+DENS':
        ts.update(hux='all', cap=11 / 12, dens=True)
    elif name == 'H+cap+DENS+kernel':
        ts.update(hux='all', cap=11 / 12, dens=True, kernel='hp')
    elif name == 'all':
        ts.update(hux='all', cap=11 / 12, dens=True, kernel='hp', cgl=True)
    elif name == 'ours':
        ts.update(cap=11 / 12, dens=True, kernel='hp', k1=True)
    elif name == 'H1+CGL':          # Harman's tools, with Input 2 wherever his proof uses Huxley's (the rest's powers)
        ts.update(hux='rest', cgl='rest')
    elif name == 'H+CGL':           # Huxley's and Input 2 on every sub-product
        ts.update(hux='all', cgl='all')
    elif name == 'H1+CGL+cap':      # the same with the half-plane's saving on the prime sums
        ts.update(hux='rest', cgl='rest', cap=11 / 12)
    elif name == 'H+CGL+cap':
        ts.update(hux='all', cgl='all', cap=11 / 12)
    else:
        raise ValueError(name)
    return ts


def kappa(ts, tau, m_x):
    """The exponent of the kernel of the Halasz-Montgomery inequality for a polynomial of length x^{m_x}."""
    m_x = np.asarray(m_x, dtype=float)
    if ts['kernel'] == 'pv':
        return np.full_like(m_x, tau / 2)
    mq = m_x / tau
    return tau * np.where(mq <= 1, 5 / 12 + mq / 12, 0.5)


def kmax_of(ts, tau, a):
    """The powers k <= ceil(tau / a) suffice: beyond k0 = ceil(tau / a) every bound is at least 2 k (a - l), which is
    at least orthogonality's bound 2 k0 (a - l) for the power k0, of length at least q."""
    return 1 if ts['k1'] else max(1, int(math.ceil(tau / a - 1e-12)))


def has_hux(ts, S):
    return ts['hux'] == 'all' or (ts['hux'] == 'rest' and S == (2,))


def has_cgl(ts, S):
    return ts['cgl'] is True or ts['cgl'] == 'all' or (ts['cgl'] == 'rest' and S == (2,))


def bound(ts, tau, a, l, S):
    """The least bound of the tools for the sub-product S (length x^a) at the levels l, over the powers."""
    l = np.asarray(l, dtype=float)
    out = np.full(l.shape, np.inf)
    for k in range(1, kmax_of(ts, tau, a) + 1):
        ka, kl = k * a, k * l
        out = np.minimum(out, max(tau, ka) + ka - 2 * kl)
        kap = float(kappa(ts, tau, np.array([ka]))[0])
        out = np.minimum(out, np.where(2 * kl - ka >= kap - 1e-15, 2 * (ka - kl), np.inf))
        if has_hux(ts, S):
            out = np.minimum(out, np.maximum(2 * (ka - kl), tau + 4 * ka - 6 * kl))
        if has_cgl(ts, S) and ka >= 2 * tau / 3:
            lp = np.minimum(kl, 0.8 * ka)
            v = np.maximum.reduce([2 * (ka - lp), tau / 2 + 3 * ka - 4 * lp, 4 * tau / 3 + 2 * ka - 4 * lp])
            out = np.minimum(out, np.where(kl >= 0.7 * ka, v, np.inf))
    return out


def count(ts, tau, a, l):
    """The exponent of the number of characters with the profiles l (n x 3)."""
    l = np.atleast_2d(l)
    c = np.full(l.shape[0], tau)
    for S in SUBSETS:
        c = np.minimum(c, bound(ts, tau, sum(a[i] for i in S), l[:, list(S)].sum(axis=1), S))
    if ts['dens']:
        c = np.minimum(c, tau * g_env(l[:, 2] / a[2]))
    return c


def psi(ts, tau, a, c0, S):
    """The largest level of the sub-product S at which its least bound is at least c0 (it may exceed a: no
    constraint; or be negative: no profile)."""
    c0 = np.asarray(c0, dtype=float)[:, None]
    k = np.arange(1, kmax_of(ts, tau, a) + 1, dtype=float)[None, :]
    ka = k * a
    out = (np.maximum(tau, ka) + ka - c0) / (2 * k)
    out = np.minimum(out, np.maximum(a - c0 / (2 * k), (ka + kappa(ts, tau, ka)) / (2 * k)))
    if has_hux(ts, S):
        out = np.minimum(out, np.maximum(a - c0 / (2 * k), (tau + 4 * ka - c0) / (6 * k)))
    if has_cgl(ts, S):
        w = np.maximum.reduce([a - c0 / (2 * k), (tau / 2 + 3 * ka - c0) / (4 * k),
                               (4 * tau / 3 + 2 * ka - c0) / (4 * k)])
        p = np.where(w >= 0.8 * a, np.inf, np.maximum(0.7 * a, w))
        out = np.minimum(out, np.where(ka >= 2 * tau / 3, p, np.inf))
    return out.min(axis=1)


class Problem:
    def __init__(self, ts, tau, a1, a2, rho, capK=None):
        self.ts, self.tau, self.a = ts, tau, (a1, a2, rho)
        self.caps = np.array([a1, a2, rho * ts['cap'] if capK is None else capK])
        self.aS = [sum(self.a[i] for i in S) for S in SUBSETS]

    def U(self, c0):
        c0 = np.atleast_1d(np.asarray(c0, dtype=float))
        u = np.empty((c0.shape[0], 7))
        for j, S in enumerate(SUBSETS):
            v = np.minimum(psi(self.ts, self.tau, self.aS[j], c0, S), sum(self.caps[i] for i in S))
            if S == (2,) and self.ts['dens']:
                v = np.minimum(v, self.a[2] * sigma_star(c0 / self.tau))
            u[:, j] = v
        return u

    def M(self, c0):
        """The largest l_1 + l_2 + l_K among the profiles with at least x^{c0} characters."""
        u = self.U(c0)
        return np.where((u < -1e-15).any(axis=1), -np.inf, (u @ COVERS.T).min(axis=1))


def E_count(P, tol=1e-6, thr=None, n0=512):
    """Branch and bound over the count c0 in [0, tau]: an upper and a lower bound for E, and the count of the lower
    one.  With `thr` it stops once it knows whether E <= thr."""
    edges = np.linspace(0.0, P.tau, n0 + 1)
    lo, hi = edges[:-1], edges[1:]
    LB, cbest, UB = -np.inf, None, -np.inf
    for _ in range(200):
        if not len(lo):
            break
        ub, lb = hi + P.M(lo), hi + P.M(hi)
        j = int(np.argmax(lb))
        if lb[j] > LB:
            LB, cbest = lb[j], hi[j]
        if thr is not None and LB > thr:
            return max(UB, ub.max()), LB, cbest
        done = ub <= LB + tol
        if thr is not None:
            done |= ub <= thr
        done |= hi - lo <= 1e-13
        if done.any():
            UB = max(UB, ub[done].max())
        lo, hi = lo[~done], hi[~done]
        if len(lo) > 400000:
            break
        mid = (lo + hi) / 2
        lo, hi = np.concatenate([lo, mid]), np.concatenate([mid, hi])
    if len(lo):
        UB = max(UB, (hi + P.M(lo)).max())
    return max(UB, LB), LB, cbest


def E_box(P, tol=1e-4, max_boxes=400000):
    """The same by branch and bound over boxes of profiles (every bound decreases with the levels): a check."""
    lo, hi = np.zeros((1, 3)), P.caps[None, :].copy()
    LB, UB, n = -np.inf, -np.inf, 0
    while len(lo):
        n += len(lo)
        clo, chi = count(P.ts, P.tau, P.a, lo), count(P.ts, P.tau, P.a, hi)
        ub = np.where(clo < 0, -np.inf, hi.sum(axis=1) + clo)
        lb = np.where(chi >= 0, hi.sum(axis=1) + chi, -np.inf)
        LB = max(LB, lb.max())
        done = ub <= LB + tol
        if done.any():
            UB = max(UB, ub[done].max())
        lo, hi = lo[~done], hi[~done]
        if n > max_boxes and len(lo):
            UB = max(UB, (hi.sum(axis=1) + count(P.ts, P.tau, P.a, lo)).max())
            break
        if len(lo):
            d = np.argmax(hi - lo, axis=1)
            i = np.arange(len(lo))
            mid = (lo[i, d] + hi[i, d]) / 2
            h2, l3 = hi.copy(), lo.copy()
            h2[i, d], l3[i, d] = mid, mid
            lo, hi = np.concatenate([lo, l3]), np.concatenate([h2, hi])
    return max(UB, LB), LB


H_DELTA = 1e-4


def passes(ts, tau, a1, a2, rho, margin=1e-4):
    """With the cap: E <= 1 - margin.  With a (log x)^{-A} saving: E <= 1 - 10^-5 over the profiles with K at least
    10^-4 below its largest size."""
    if a1 <= 0 or a2 <= 0 or rho <= 0:
        return False
    if ts['cap'] >= 1:
        thr = 1 - H_DELTA / 10
        return E_count(Problem(ts, tau, a1, a2, rho, capK=rho - H_DELTA), tol=H_DELTA / 100, thr=thr)[0] <= thr
    thr = 1 - margin
    return E_count(Problem(ts, tau, a1, a2, rho), tol=margin / 100, thr=thr)[0] <= thr


# ---------------------------------------------------------------------------------------------- regions and zones
def gamma_g(theta, g):
    """Baker, Harman and Pintz's gamma_g (g = 3: Harman's gamma of 2005)."""
    return min(4 * theta - 2, ((8 * g - 4) * theta - (4 * g - 3)) / (4 * g - 1),
               (24 * g * theta - (12 * g + 1)) / (4 * g - 1))


def gamma_max(theta, gmax=200):
    return max(gamma_g(theta, g) for g in range(1, gmax + 1))


def diagonal(ts, tau, step=0.0005, top=0.3):
    """The last rho of the first run of rests that pass on a1 = a2, on the lattice and then by bisection."""
    def ok(r):
        return passes(ts, tau, (1 - r) / 2, (1 - r) / 2, r)
    r, last = step, None
    while r < top:
        if ok(r):
            last = r
        elif last is not None:
            break
        r += step
    if last is None:
        return None
    lo, hi = last, last + step
    for _ in range(12):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return lo


DL, NR, NA, A0 = 0.0005, 441, 641, 0.30


def zone(ts, tau):
    """For each rest rho = c DL: the ends [Alo, Ahi] of the run of a1 = A0 + j DL through the diagonal on which the
    configuration (a1, 1 - a1 - rho, rho) passes (NaN: none).  The model is symmetric in the two parts, so the run is
    followed on the side a1 >= a2 and mirrored."""
    r = DL * np.arange(NR)
    Alo, Ahi = np.full(NR, np.nan), np.full(NR, np.nan)
    for c in range(1, NR):
        rho = r[c]

        def ok(j):
            a1 = A0 + j * DL
            return passes(ts, tau, a1, 1 - a1 - rho, rho)
        j = 400 - c // 2                      # the diagonal, or the lattice point just above it
        jlim = min(2000 - c - 1, max(NA - 1, 800 - c))
        if not ok(j):
            continue
        while j + 10 <= jlim and ok(j + 10):
            j += 10
        lo, hi = j, min(j + 10, jlim + 1)
        while hi - lo > 1:
            mid = (lo + hi) // 2
            lo, hi = (mid, hi) if ok(mid) else (lo, mid)
        Ahi[c] = min(A0 + lo * DL, A0 + (NA - 1) * DL)
        Alo[c] = A0 + max(800 - c - lo, 0) * DL
    return r, Alo, Ahi


# ---------------------------------------------------------------------------------------------- commands
ROWS = (('2.06', 2.06), ('2.08', 2.08), ('2.10', 2.10), ('2.12', 2.12), ('125/59', 125 / 59), ('100/47', 100 / 47))


def cmd_harman05():
    print('the last rho that passes on a1 = a2')
    print(f'    {"L (theta)":18s} {"gamma_3":10s} {"max_g gamma_g":15s} {"4 theta - 2":14s} '
          + ' '.join(f'{n:9s}' for n in ('H1', 'H', 'all', 'ours')))
    for name, L in ROWS:
        tau = 1 / L
        th = 1 - tau
        g = max(range(1, 200), key=lambda gg: gamma_g(th, gg))
        d = [diagonal(toolset(n), tau) for n in ('H1', 'H', 'all', 'ours')]
        print(f'    {name:6s} ({th:.4f})    {gamma_g(th, 3):<10.4f} {gamma_max(th):.4f} (g = {g:<2d})   '
              f'{4 * th - 2:<14.4f} ' + ' '.join(f'{v:<9.4f}' if v is not None else f'{"none":9s}' for v in d),
              flush=True)


def cmd_widen():
    names = ('H', 'H+cap', 'H+cap+DENS', 'H+cap+DENS+kernel', 'all', 'ours')
    print('the last rho that passes on a1 = a2')
    print(f'    {"L":8s}' + ' '.join(f'{n:18s}' for n in names))
    for name, L in ROWS:
        d = [diagonal(toolset(n), 1 / L) for n in names]
        print(f'    {name:8s}' + ' '.join(f'{v:<18.4f}' if v is not None else f'{"none":18s}' for v in d), flush=True)
    L = 2.10
    tau = 1 / L
    print(f'the width of the zone of a1 at L = 21/10 (Harman\'s closed form: 2 theta - 1 = {1 - 2 * tau:.4f} at every '
          'rest below gamma)')
    print(f'    {"rho":8s}' + ' '.join(f'{n:18s}' for n in names))
    tabs = [zone_rows(toolset(n), tau, (0.02, 0.04, 0.06, 0.08)) for n in names]
    for i, rho in enumerate((0.02, 0.04, 0.06, 0.08)):
        print(f'    {rho:<8.2f}' + ' '.join(f'{t[i]:<18.4f}' if t[i] == t[i] else f'{"none":18s}' for t in tabs))


def zone_rows(ts, tau, rhos):
    """The widths of the zone at a few rests (a pass at each, as `zone` does it)."""
    out = []
    for rho in rhos:
        def ok(a1):
            return passes(ts, tau, a1, 1 - a1 - rho, rho)
        d = (1 - rho) / 2
        if not ok(d):
            out.append(float('nan'))
            continue
        lo, hi = d, d + 0.08
        while not ok(lo + (hi - lo) / 2) and hi - lo > 1e-4:
            hi = lo + (hi - lo) / 2
        for _ in range(14):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if ok(mid) else (lo, mid)
        out.append(2 * (lo - d))
    return out


def cmd_zone(args):
    name = args[0]
    for Ls in args[1:]:
        t = time.time()
        r, Alo, Ahi = zone(toolset(name), 1 / float(Fr(Ls)))
        fn = f'zones_{name}_L{Ls.replace("/", "_")}.npz'
        np.savez(fn, r=r, Alo=Alo, Ahi=Ahi)
        ok = ~np.isnan(Ahi)
        print(f'{name} L = {Ls}: rests {r[ok].min():.4f} to {r[ok].max():.4f}, widest {np.nanmax(Ahi - Alo):.4f}; '
              f'{fn}, {time.time() - t:.0f} s' if ok.any() else f'{name} L = {Ls}: no zone', flush=True)


def cmd_regions(args):
    import gen_leafzone as glz
    forms, _ = glz.region()
    lam, mu = 27637 / 62500, 1 / 12500
    for Ls in args:
        L = Fr(Ls)
        tau = 1 / float(L)
        th = 1 - tau
        print(f'L = {Ls} (tau = {tau:.5f}, theta = {th:.5f}).  Exponents of x; two parts x^a1, x^a2 and a rest x^rho of '
              'primes, a1 + a2 + rho = 1.')
        gbest = max(range(1, 200), key=lambda g: gamma_g(th, g))
        print(f'  Harman (2005, p. 646): |a1 - a2| < 2 theta - 1 = {2 * th - 1:.4f}, that is tau - rho/2 < a1 < '
              'theta - rho/2, and')
        for what, g in (('as printed (g = 3)', gamma_g(th, 3)), ('with g = 4 (Harman, Kumchev and Lewis)',
                                                                 gamma_g(th, 4)),
                        (f'with the largest gamma_g (Baker, Harman and Pintz; g = {gbest})', gamma_max(th))):
            print(f'      rho < {g:.4f}  {what}' if g > 0 else f'      no rest  {what}')
        for name, what in (('H', "the model with Harman's tools on every factor"),
                           ('all', "the model with the paper's inputs as well")):
            d = diagonal(toolset(name), tau)
            if d is None:
                print(f'  {what} ({name}): no rest')
                continue
            ws = zone_rows(toolset(name), tau, (d / 4, d / 2, 3 * d / 4))
            print(f'  {what} ({name}): rho up to {d:.4f} on a1 = a2; |a1 - a2| up to '
                  + ', '.join(f'{w:.4f} at rho = {r:.3f}' for w, r in zip(ws, (d / 4, d / 2, 3 * d / 4))))
        rmax = (float(L) - 2 - mu) / (1 - lam) / float(L)
        print(f"  the paper's region in two variables (Definition 3.1): tau - {lam:.6f} rho < a1 < theta - "
              f'{1 - lam:.6f} rho, less {mu * tau:.6f} at each end, for rho up to {rmax:.4f}: |a1 - a2| up to '
              + ', '.join(f'{2 * th - 1 - (1 - 2 * lam) * r - 2 * mu * tau:.4f} at rho = {r:.3f}'
                          for r in (rmax / 4, rmax / 2, 3 * rmax / 4)))
        d = diagonal(toolset('ours'), tau)
        print(f'      (the model of that estimate with the curve g7d, `ours`: rho up to {d:.4f})' if d else
              '      (`ours`: no rest)')
        w = rl.window(rl.parse('g7d'), L)
        print('  the window of the estimate in one variable: '
              + ('none' if w is None else f'one part x^u, u in [{float(w[0]):.5f}, {float(w[1]):.5f}]'))
        V = sorted(glz.vertices(forms + [glz.lin(a=1, b=1, c=1, k=-L), glz.lin(a=-1, b=-1, c=-1, k=L)]))
        if not V:
            print("  the leaves' region: empty")
        else:
            print("  the leaves' region (d1, the cofactor, the primes of d2): "
                  + ', '.join(f'x^{float(min(v[i] for v in V) / L):.4f} to x^{float(max(v[i] for v in V) / L):.4f}'
                              for i in range(3)))


def cmd_check():
    rng = np.random.default_rng(1)
    worst = 0.0
    for name in ('H1', 'H', 'all', 'ours'):
        ts = toolset(name)
        for _ in range(6):
            tau = 1 / rng.uniform(2.04, 2.2)
            rho = rng.uniform(0.02, 0.12)
            a1 = (1 - rho) / 2 + rng.uniform(-0.03, 0.03)
            P = Problem(ts, tau, a1, 1 - a1 - rho, rho)
            e1, e2 = E_count(P, tol=1e-6)[0], E_box(P, tol=1e-4)[0]
            worst = max(worst, abs(e1 - e2))
    print(f'the two searches differ by at most {worst:.1e} at 24 random configurations (tolerance 1e-4)')
    assert worst < 2e-4
    bad = n = 0
    for th in (0.515, 0.52, 0.5238, 0.528, 0.53, 0.535):
        tau, g = 1 - th, gamma_max(th)
        for _ in range(60):
            rho = rng.uniform(0.004, g - 0.001)
            d = rng.uniform(0, 2 * th - 1 - 0.001)
            n += 1
            bad += not passes(toolset('H'), tau, (1 - rho + d) / 2, (1 - rho - d) / 2, rho)
    print(f'{n - bad} of {n} random points of Harman\'s closed form pass H')
    assert bad == 0
    import harman_sieve as hs
    r, lo, hi = hs.zones(Fr(21, 10))
    r2, lo2, hi2 = zone(toolset('ours'), 10 / 21)
    both = np.isfinite(lo) & (lo <= hi) & ~np.isnan(lo2)
    both[int(round(0.086 / DL)):] = False           # the model's last rest keeps a lobe off the diagonal
    dmax = max(np.abs(lo - lo2)[both].max(), np.abs(hi - hi2)[both].max())
    print(f'`ours` and harman_sieve.zones at 21/10: both have a zone at {both.sum()} rests below 0.086, and the ends '
          f'differ by at most {dmax:.4f}')
    assert dmax <= DL + 1e-9
    print('ok')


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else ''
    if cmd == 'harman05':
        cmd_harman05()
    elif cmd == 'widen':
        cmd_widen()
    elif cmd == 'zone' and len(sys.argv) > 3 and sys.argv[2] in SETS:
        cmd_zone(sys.argv[2:])
    elif cmd == 'regions' and len(sys.argv) > 2:
        cmd_regions(sys.argv[2:])
    elif cmd == 'check':
        cmd_check()
    else:
        sys.exit(__doc__)
