#!/usr/bin/env python3
"""type2_model.py [window | harman | every]: which Type II sums over the characters mod q the large-value tools
bound, with and without the one tool that cuts the modulus.

A model, in floating point: nothing in the library or in the paper depends on it. Here "the paper" is the Linnik paper's version at 11/5, in the git history at commit 49dc981; the paper now
proves 43/20 by another route (hint_cert.py).

The model.  Exponents are in base x, and q = x^tau.  A sum over the non-trivial characters of prod_i |F_i(chi)|, with
F_i of length x^{a_i} and sum a_i = 1, is split by the sizes |F_i(chi)| ~ x^{a_i s_i}.  At most x^c characters have a
given profile (s_i), where c is the least of the bounds below, and they contribute x^{c + sum a_i s_i}; the sum is
<< x^{1 - delta} if the largest such exponent E is below 1.  Each bound is for a sub-product G of the factors, of
length x^a and size x^lev, raised to a power k >= 1:

    MVT   orthogonality                 max(tau, k a) + k a - 2 k lev                      every modulus
    HM    Halasz-Montgomery             2 k (a - lev)   if 2 k lev - k a >= tau/2          every modulus
    M4    HM with the fourth moment     max(2k(a - lev), tau + k(6a - 8 lev))              every modulus
    HUX   Huxley's large values         max(2k(a - lev), tau + k(4a - 6 lev))              cuts the range

Huxley's second term comes from cutting the range into cells and applying HM in each.  In t a cell can have any
length; for characters the cells are the cosets of the characters mod a divisor d of q, so q needs a divisor of the
right size, as when it has no large prime factor.  A factor is arbitrary ('A') or prime-factored ('P'): then
|F(chi)| <= F^{beta}, beta the largest real part of a zero of L(s, chi), at most x^{tau D(beta)} characters have a
zero that far right (a density curve D), and with a zero-free half-plane beta <= 11/12.

`window`: the model with orthogonality on one arbitrary factor, the density curve 7/3 and the half-plane gives the
paper's window at L = 11/5, [0.4345, 0.4695] (the paper: [0.43457, 0.46959]).

`harman`: two arbitrary factors x^{a1}, x^{a2} and a prime-factored rest x^rho, with no input but a zero-free region
near 1 (the rest's size is capped at 0.999).  With HUX on the rest and HM on the two factors the model gives the region
of Baker, Harman and Pintz's Lemma 9 (Harman's Lemma 7.3; R. Li's Lemma 4.1): |a1 - a2| < 2 theta - 1 and
rho < gamma(theta), theta = 1 - tau.  So the cut is in one place: Huxley's theorem on powers of the rest.  Without it
(MVT, HM and M4 everywhere) the first condition is unchanged and the second shrinks:

    theta (L)          gamma(theta)   model, his tools   model, no cutting
    0.525  (2.105)     0.100          0.096 - 0.100      0.096 - 0.100
    0.528  (2.119)     0.112          0.108 - 0.112      0.100 - 0.104
    0.535  (2.151)     0.138          0.132 - 0.136      0.124 - 0.128
    6/11   (2.2)       0.174          0.164 - 0.168      0.164 - 0.168

(the last rho that passes and the first that fails, on a1 = a2, in steps of 0.004).  Without cutting, the region at
theta = 0.530 (rho up to 0.118) contains Harman's at 0.528.

`every`: the same with the paper's inputs (the half-plane, and the density curve with 12/5 or with 7/3), and with all
three factors prime-factored.  The inputs change the numbers by at most 0.004: the profile that decides has about
q^{1/2} characters at the size 0.76, where the density curve does not bind.  Without powers (orthogonality and HM on
the sums themselves) the region is the same within 0.004; that case is the estimate of `two_factor.py`.

Needs numpy.  `harman` and `every` take a few minutes.
"""
import itertools
import sys

import numpy as np


def D_ingham_huxley(b):
    b = np.asarray(b, dtype=float)
    return np.where(b <= 0.75, 3 * (1 - b) / (2 - b), 3 * (1 - b) / (3 * b - 1))


def D_with_cgl(b):
    """Ingham to 5/7, Chen-Gupta-Li's 4/(1 + s) to 7/9, Huxley beyond."""
    b = np.asarray(b, dtype=float)
    return np.where(b <= 5 / 7, 3 * (1 - b) / (2 - b),
                    np.where(b <= 7 / 9, 4 * (1 - b) / (1 + b), 3 * (1 - b) / (3 * b - 1)))


def count_bound(a, lev, tau, tools):
    """The least exponent of the number of characters with |G| ~ x^lev, over the tools and the powers of G."""
    out = np.full(lev.shape, tau, dtype=float)
    if 'MVT' in tools:
        k0 = max(1, int(np.floor(tau / a + 1e-12)))
        for k in (k0, k0 + 1):
            out = np.minimum(out, max(tau, k * a) + k * a - 2 * k * lev)
    if 'MVT1' in tools:      # orthogonality on the sum itself
        out = np.minimum(out, max(tau, a) + a - 2 * lev)
    d = 2 * lev - a
    if 'HM' in tools:
        with np.errstate(divide='ignore', invalid='ignore'):
            k = np.where(d > 1e-9, np.ceil(tau / (2 * np.maximum(d, 1e-9)) - 1e-9), np.inf)
        k = np.maximum(k, 1)
        out = np.minimum(out, np.where(np.isfinite(k), 2 * k * (a - lev), np.inf))
    if 'HM1' in tools:       # Halasz-Montgomery on the sum itself
        out = np.minimum(out, np.where(d >= tau / 2 - 1e-12, 2 * (a - lev), np.inf))
    for name, c1, c2 in (('M4', 6.0, 8.0), ('HUX', 4.0, 6.0)):
        if name in tools:
            den = (c2 - 2) * lev - (c1 - 2) * a      # k den = tau where the two terms cross
            with np.errstate(divide='ignore', invalid='ignore'):
                kc = np.where(den > 1e-9, tau / np.maximum(den, 1e-9), np.inf)
            for kk in (np.floor(kc), np.ceil(kc)):
                ok = np.isfinite(kk)
                kk = np.where(ok, np.maximum(kk, 1), 1)
                val = np.maximum(2 * kk * (a - lev), tau + kk * (c1 * a - c2 * lev))
                out = np.minimum(out, np.where(ok, val, np.inf))
    return np.maximum(out, 0.0)


def exponent(factors, tau, tools, dens=None, pcap=11 / 12, step=0.01, box=None, only=None, full=False):
    """E on a grid of profiles: its maximum and where, or with `full` the whole array."""
    n = len(factors)
    grids = []
    for i, (a, typ) in enumerate(factors):
        lo, hi = 0.0, pcap if typ == 'P' else 1.0
        if box is not None:
            lo, hi = max(lo, box[i][0]), min(hi, box[i][1])
        g = np.arange(lo, hi + 1e-12, step)
        if g.size == 0 or g[-1] < hi - 1e-12:
            g = np.append(g, hi)
        grids.append(g)
    mesh = np.meshgrid(*grids, indexing='ij', sparse=True)
    cnt = np.full(tuple(len(g) for g in grids), tau, dtype=float)
    subs = only or [S for r in range(1, n + 1) for S in itertools.combinations(range(n), r)]
    for S in subs:
        S = tuple(S)
        a = sum(factors[i][0] for i in S)
        lev = sum(factors[i][0] * mesh[i] for i in S)
        cnt = np.minimum(cnt, count_bound(a, lev, tau, tools(S) if callable(tools) else tools))
    ps = [mesh[i] for i, (a, typ) in enumerate(factors) if typ == 'P']
    if dens is not None and ps:
        beta = ps[0]
        for p in ps[1:]:
            beta = np.maximum(beta, p)
        cnt = np.minimum(cnt, tau * dens(np.maximum(beta, 0.5)))
    tot = cnt + sum(factors[i][0] * mesh[i] for i in range(n))
    if full:
        return np.broadcast_to(tot, tuple(len(g) for g in grids)), grids
    j = np.unravel_index(np.argmax(tot), tot.shape)
    return float(tot[j]), tuple(float(grids[i][j[i]]) for i in range(n))


def exponent_refined(factors, tau, tools, dens=None, pcap=11 / 12, step=0.01, starts=24, **kw):
    """The maximum, refined around the best well-separated grid points: E has plateaus at exactly 1, where two
    sub-products are both longer than q and orthogonality saves nothing, and a coarse grid can miss them."""
    tot, grids = exponent(factors, tau, tools, dens, pcap, step, full=True, **kw)
    picks = []
    for f in np.argsort(tot, axis=None)[::-1][:4000]:
        j = np.unravel_index(f, tot.shape)
        if all(max(abs(a - b) for a, b in zip(j, p)) > 2 for p in picks):
            picks.append(j)
            if len(picks) >= starts:
                break
    best, barg = -1.0, None
    for j in picks:
        E, arg = float(tot[j]), tuple(float(grids[i][j[i]]) for i in range(len(grids)))
        for fine in (step / 5, step / 25, step / 125):
            E2, arg2 = exponent(factors, tau, tools, dens, pcap, fine, box=[(v - 6 * fine, v + 6 * fine) for v in arg],
                                **kw)
            if E2 > E:
                E, arg = E2, arg2
        if E > best:
            best, barg = E, arg
    return best, barg


def gamma(theta, gmax=12):
    """Baker, Harman and Pintz's gamma(theta) (R. Li's Lemma 4.1)."""
    return max(min(4 * theta - 2, ((8 * g - 4) * theta - (4 * g - 3)) / (4 * g - 1),
                   (24 * g * theta - (12 * g + 1)) / (4 * g - 1)) for g in range(1, gmax + 1))


NOCUT = {'MVT', 'HM', 'M4'}
HARMAN = {
    'his tools (Huxley on the rest, HM on the two)':
        dict(tools=lambda S: {'MVT', 'HUX'} if S == (2,) else {'MVT', 'HM'}, types='AAP', pcap=0.999, dens=None),
    'no cutting (MVT, HM, M4 everywhere)': dict(tools=NOCUT, types='AAP', pcap=0.999, dens=None),
}
EVERY = {
    'no cutting, half-plane, density 12/5': dict(tools=NOCUT, types='AAP', pcap=11 / 12, dens=D_ingham_huxley),
    'no cutting, half-plane, density 7/3': dict(tools=NOCUT, types='AAP', pcap=11 / 12, dens=D_with_cgl),
    'the same, three prime-factored factors': dict(tools=NOCUT, types='PPP', pcap=11 / 12, dens=D_with_cgl),
    'the same, no powers (two_factor.py)': dict(tools={'MVT1', 'HM1'}, types='PPP', pcap=11 / 12, dens=D_with_cgl),
}


def passes(a1, a2, tau, c):
    rho = 1 - a1 - a2
    f = [(a1, c['types'][0]), (a2, c['types'][1]), (rho, c['types'][2])]
    E, _ = exponent_refined(f, tau, c['tools'], c['dens'], c['pcap'])
    if c['pcap'] < 0.99:          # a zero-free half-plane: any power saving will do
        return E < 1 - 1e-6
    return E <= 1 - (1 - c['pcap']) * rho + 1e-7     # no profile above the one where every factor is largest


def extent(vals, test):
    res = [(v, test(v)) for v in vals]
    good, bad = [v for v, o in res if o], [v for v, o in res if not o]
    return (max(good) if good else None, min(bad) if bad else None)


def table(cases, thetas):
    for theta in thetas:
        tau = 1 - theta
        print(f'theta = {theta:.4f} (L = {1 / tau:.4f}): gamma = {gamma(theta):.4f}, 2 theta - 1 = {2 * theta - 1:.4f}')
        for name, c in cases.items():
            d = extent(np.round(np.arange(0.04, 0.30, 0.004), 3), lambda r: passes((1 - r) / 2, (1 - r) / 2, tau, c))
            e = extent(np.round(np.arange(0.0, 0.30, 0.004), 3),
                       lambda dd: passes((0.96 + dd) / 2, (0.96 - dd) / 2, tau, c))
            print(f'   {name:46s} on a1 = a2, rho: last pass {d[0]}, first fail {d[1]};  at rho = 0.04, |a1 - a2|: '
                  f'last pass {e[0]}, first fail {e[1]}', flush=True)


def cmd_window():
    L = 11 / 5
    tau = 1 / L
    us = np.arange(0.40, 0.50001, 0.0005)
    good = [u for u in us if exponent_refined([(u, 'A'), (1 - u, 'P')], tau, {'MVT1'}, D_with_cgl, 11 / 12,
                                                step=0.002, only=[(0,)])[0] < 1 - 1e-9]
    print(f'L = 11/5, one arbitrary factor x^u by orthogonality: u in [{min(good):.4f}, {max(good):.4f}] '
          f'(the paper\'s window: [0.43457, 0.46959])')


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else ''
    if cmd == 'window':
        cmd_window()
    elif cmd == 'harman':
        table(HARMAN, (0.525, 0.528, 0.535, 6 / 11))
    elif cmd == 'every':
        table(EVERY, (0.528, 0.530, 0.535, 6 / 11))
    else:
        sys.exit(__doc__)
