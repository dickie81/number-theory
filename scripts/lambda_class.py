#!/usr/bin/env python3
"""The inverse theorem up to Möbius support N^{1/3} (formalisations/ball-rate.md, section "The inverse theorem up to
Möbius support N^{1/3}"): the asymptotic Q_N(x) = (Diag − Land)/(2π²N) on the class, against the Gram matrix of Q_N.
Uncertified numerics.

    python3 scripts/lambda_class.py [N ...]                  # default N = 2000 8000; needs numpy, scipy, mpmath
    python3 scripts/lambda_class.py --restricted [N ...]     # default N = 2000 8000
    options: --delta δ (default 0.15), the width of η's step; --simple-c, the profile c(u) = (1 − u)³(10u − 2)

The class: x_n = ((F(n) − P)·η(n/N) + P·w(n/N))/n, with F = 1 ∗ e, e supported on d ≤ D₀, P = Σ_d e(d)/d. Here η is
C^∞, 1 on [0, 1 − δ] and 0 on [1, ∞), and w(u) = Σ_{k ≤ 1/u} c(ku) with c(u) = (1 − u)³(−2 + a₁u + a₂u² + a₃u³), an
admissible profile of the sharp upper bound (ŵ = ζ·ĉ, so the class is quiet at the low zeros): a₂ = −6.829 and
a₃ = 120.672 minimise I[c] in this family, to 1.2327 against the optimum 1.0976, and a₁ = 10 − a₂/3 − a₃/7 gives
∫c = 0. With --simple-c, I[c] = 2.558. In the notation of the section, H_a = S(a)·φ_η for a ≥ 2 and H_1 = P·φ_w,
with S(a) = Σ_g e(ag)/g and φ_E = E(0) − E. The prediction is the quadratic form in S of the section's formula: for
a ≥ 2 the closed form with J = ∫φ_η²/y² over [1 − δ, 1], K₁ = ∫φ_η² log y/y², I* = ∫φ_η/y² and
ℓ(a) = −ζ'(2)/ζ(2) − Σ_{p | a} log p/(p² − 1); for a = 1 the integrals I[c] = ∫φ_w²/y², K_w = ∫φ_w² log y/y²,
M_ww(q) = ∫φ_w(y)φ_w(qy)/y² and M_wη(q) = ∫φ_w(y)φ_η(qy)/y², with the sums over b done exactly by prime and the
primes above 2000 by the prime number theorem.

Default mode: for test vectors (e = δ₁, δ₁ − 2δ₂, δ₁ + δ₂, Selberg's weights μ(d)log(z/d)/log z at z = 10, 40, 160,
640, and random e = r_d/d on d ≤ D₀ for D₀ = 8, 32, 128, 512, 2048 up to N/4, r_d standard normal from the seed D₀),
Q_N·N/(Σx_n²·log N) from the Gram matrix, the prediction, their ratio, the share Land/Diag, and θ = log D₀/log N.

--restricted: the smallest value of Q_N/Σx_n² on the class with D₀ = 1, 2, 4, …, 512 (up to N/4): from the Gram matrix,
from the predicted quadratic form, their ratio, against λ_N and K_min·log(N/D₀)/N with K_min = 0.040021.
"""
import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import argparse  # noqa: E402
import math  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402

import mpmath as mp  # noqa: E402
import numpy as np  # noqa: E402
import scipy.linalg as sl  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lambda_heard import mobius  # noqa: E402
from lambda_large import gram  # noqa: E402

K_MIN = 0.040021
Z2 = math.pi ** 2 / 6
ZP2 = float(-mp.zeta(2, derivative=1))       # −ζ'(2) = Σ_b log b/b²
ZL = ZP2 / Z2
PMAX = 2000
MG = 400000                                    # midpoints of (0, 1] for the integrals of φ_w


def step(t):
    """C^∞, 0 for t ≤ 0 and 1 for t ≥ 1."""
    t = np.asarray(t, dtype=float)

    def f(s):
        return np.where(s > 0, np.exp(-1 / np.where(s > 0, s, 1.0)), 0.0)

    a, b = f(t), f(1 - t)
    return a / (a + b)


C_POLY = [-2.0, 0.0, -6.829, 120.672]          # c(u) = (1 − u)³·Σ_k C_POLY[k]u^k, with ∫c = 0 fixing C_POLY[1]


def set_c(poly):
    global SLOPE
    C_POLY[:] = poly
    C_POLY[1] = 10 - C_POLY[2] / 3 - C_POLY[3] / 7                  # ∫(1 − u)³u^k = 1/4, 1/20, 1/60, 1/140
    SLOPE = (6 + C_POLY[1]) / 12                                     # φ_w(y) = (c'(0)/12)y + O(y³)


set_c(C_POLY)


def c_prof(u):
    u = np.asarray(u, dtype=float)
    poly = C_POLY[0] + u * (C_POLY[1] + u * (C_POLY[2] + u * C_POLY[3]))
    return np.where((u >= 0) & (u <= 1), (1 - u) ** 3 * poly, 0.0)


def w_at(u):
    """w(u_i) for increasing u_i in (0, 1]: for each k, add c(k·u) where k·u ≤ 1."""
    u = np.asarray(u, dtype=float)
    w = np.zeros_like(u)
    kmax = int(1 / u[0]) + 1
    for k in range(1, kmax + 1):
        top = np.searchsorted(u, 1.0 / k, side="right")
        if top == 0:
            break
        w[:top] += c_prof(k * u[:top])
    return w


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return [int(p) for p in np.nonzero(s)[0]]


class Profiles:
    def __init__(self, delta):
        self.delta = delta
        h = 1.0 / MG
        y = (np.arange(MG) + 0.5) * h
        pw = 1 - w_at(y)
        self.y, self.pw = y, pw
        self.I_w = float(np.sum(pw ** 2 / y ** 2) * h) + 1.0
        self.K_w = float(np.sum(pw ** 2 * np.log(y) / y ** 2) * h) + 1.0
        cum = np.cumsum((pw / y ** 2)[::-1])[::-1] * h          # ∫_{y_i − h/2}^1 φ_w/y²
        self.cum = cum
        v = np.linspace(1 - delta, 1, 4001)
        pe = self.phi_eta(v)
        tr = lambda g: float(np.trapezoid(g, v))  # noqa: E731
        self.J = tr(pe ** 2 / v ** 2)
        self.K1 = tr(pe ** 2 * np.log(v) / v ** 2) + 1.0
        self.Istar = tr(pe / v ** 2) + 1.0
        self.v, self.pe = v, pe
        self.cache = {}

    def eta(self, u):
        return step((1 - np.asarray(u, dtype=float)) / self.delta)

    def phi_eta(self, y):
        return 1 - self.eta(y)

    def phi_w(self, y):
        y = np.asarray(y, dtype=float)
        inner = np.interp(y, np.concatenate([[0.0], self.y]), np.concatenate([[0.0], self.pw]))
        return np.where(y >= 1, 1.0, inner)

    def tail(self, s):
        """∫_s^∞ φ_w/y² for 0 < s ≤ 1."""
        i = min(int(s * MG), MG - 1)
        return float(self.cum[i]) + 1.0

    def M(self, kind, q):
        key = (kind, q)
        if key not in self.cache:
            if kind == "ww":            # ∫_{1/q}^∞ φ_w/y² + q∫_0^1 φ_w(u/q)φ_w(u)/u² du
                val = self.tail(1 / q) + q * float(np.sum(self.phi_w(self.y / q) * self.pw / self.y ** 2) / MG)
            else:                       # ∫_{1/q}^∞ φ_w/y² + q∫_{1−δ}^1 φ_w(v/q)φ_η(v)/v² dv
                val = self.tail(1 / q) + q * float(np.trapezoid(self.phi_w(self.v / q) * self.pe / self.v ** 2,
                                                                  self.v))
            self.cache[key] = val
        return self.cache[key]

    def c_inf(self):
        """M_ww(q) = s·log q + C∞ + o(1), s = c'(0)/12: the constant, for the primes above PMAX."""
        y, pw = self.y, self.pw
        a = float(np.sum((pw - SLOPE * y) / y ** 2) / MG) + 1.0
        return a + SLOPE * float(np.sum(pw / y) / MG)


def factor(a, P):
    out = []
    for p in P:
        if p * p > a:
            break
        if a % p == 0:
            out.append(p)
            while a % p == 0:
                a //= p
    if a > 1:
        out.append(a)
    return out


def pred_matrix(N, D0, pr):
    """The predicted Q_N as a quadratic form in e, Aᵀ(Md − Ml)A/(2π²N) with S = A e; also Md (the diagonal of the
    mean value) and Ml (Landau's terms) in the S-coordinates."""
    P_ = primes_upto(max(D0, PMAX))
    Md = np.zeros((D0, D0))
    Ml = np.zeros((D0, D0))
    for a in range(2, D0 + 1):
        ps = factor(a, P_)
        om = math.prod(1 - p ** -2.0 for p in ps)
        ell = ZL - sum(math.log(p) / (p * p - 1) for p in ps)
        Md[a - 1, a - 1] += Z2 * om * ((1 + pr.J) * (math.log(N / a) + ell) + pr.K1)
        Ml[a - 1, a - 1] += 2 * pr.Istar * Z2 * om * ell
        for p in P_:
            if a * p > D0:
                break
            q = p
            while a * q <= D0:
                v = Z2 * pr.Istar * om * math.log(p) / q
                Ml[a - 1, a * q - 1] += v
                Ml[a * q - 1, a - 1] += v
                q *= p
    den = 0.0
    for p in P_:
        if p > PMAX and p > D0:
            break
        lp = math.log(p)
        wgt = Z2 * (1 - p ** -2.0)
        for i in range(40):
            if 2 * i * lp > 30 * math.log(10):
                break
            fac = p ** (-2.0 * i) * wgt
            for j in range(1, i + 1):
                den += fac * lp * pr.M("ww", p ** j)
            m = 1
            while p ** m <= D0:
                v = fac * lp * p ** (-m) * pr.M("weta", p ** (i + m))
                Ml[0, p ** m - 1] += v
                Ml[p ** m - 1, 0] += v
                m += 1
    pm = max(PMAX, D0)
    den += Z2 * (SLOPE * (math.log(pm) + 1) + pr.c_inf()) / pm      # the primes above pm, by the PNT
    Md[0, 0] += Z2 * (pr.I_w * math.log(N) + pr.K_w) + pr.I_w * ZP2
    Ml[0, 0] += 2 * den
    A = np.zeros((D0, D0))
    for a in range(1, D0 + 1):
        for d in range(a, D0 + 1, a):
            A[a - 1, d - 1] = a / d
    return A.T @ (Md - Ml) @ A / (2 * math.pi ** 2 * N), Md, Ml


def basis(N, D0, pr):
    m = np.arange(1, N + 1, dtype=float)
    u = m / N
    et, wv = pr.eta(u), w_at(u)
    B = np.zeros((N, D0))
    for d in range(1, D0 + 1):
        col = (wv - et) / d
        col[d - 1::d] += et[d - 1::d]
        B[:, d - 1] = col / m
    return B


def tests(N):
    out = {"e = δ₁": {1: 1.0}, "e = δ₁ − 2δ₂": {1: 1.0, 2: -2.0}, "e = δ₁ + δ₂": {1: 1.0, 2: 1.0}}
    mu = mobius(1000)
    for z in [10, 40, 160, 640]:
        if 4 * z <= N:
            out[f"Selberg, z = {z}"] = {d: mu[d] * math.log(z / d) / math.log(z) for d in range(1, z + 1)
                                        if mu[d] != 0}
    for D0 in [8, 32, 128, 512, 2048]:
        if 4 * D0 <= N:
            r = np.random.default_rng(D0).standard_normal(D0) / np.arange(1, D0 + 1)
            out[f"random, D₀ = {D0}"] = {d + 1: float(r[d]) for d in range(D0)}
    return out


def check_mode(Ns, pr):
    for N in Ns:
        t0 = time.time()
        G = gram(N)
        L = math.log(N)
        print(f"N = {N} (Gram {time.time() - t0:.0f}s)", flush=True)
        print(f"  {'vector':20s} {'θ':>5s} {'Q·N/(Σx² log N)':>16s} {'predicted':>10s} {'ratio':>8s} "
              f"{'Land/Diag':>10s}")
        for name, e in tests(N).items():
            D0 = max(e)
            B = basis(N, D0, pr)
            ev = np.array([e.get(d, 0.0) for d in range(1, D0 + 1)])
            x = B @ ev
            q = float(x @ (G @ x))
            Mp, Md, Ml = pred_matrix(N, D0, pr)
            qp = float(ev @ Mp @ ev)
            S = np.array([sum(e.get(a * g, 0.0) / g for g in range(1, D0 // a + 1)) for a in range(1, D0 + 1)])
            diag, land = float(S @ Md @ S), float(S @ Ml @ S)
            n2 = float(x @ x)
            print(f"  {name:20s} {math.log(D0) / L:5.2f} {q * N / n2 / L:16.4f} {qp * N / n2 / L:10.4f} "
                  f"{q / qp:8.4f} {land / diag:+10.3f}", flush=True)
        del G


def restricted_mode(Ns, pr):
    for N in Ns:
        t0 = time.time()
        G = gram(N)
        lamN = sl.eigh(G, eigvals_only=True, subset_by_index=[0, 0])[0]
        L = math.log(N)
        Dmax = min(512, N // 4)
        B = basis(N, Dmax, pr)
        GB = G @ B
        del G
        print(f"N = {N}: λ_N·N/log N = {lamN * N / L:.5f} ({time.time() - t0:.0f}s)", flush=True)
        print(f"  {'D₀':>5s} {'θ':>5s} {'min·N/log N':>12s} {'predicted':>10s} {'ratio':>8s} {'over λ_N':>9s} "
              f"{'K_min·log(N/D₀)/log N':>22s}")
        D0 = 1
        while D0 <= Dmax:
            Mq = B[:, :D0].T @ GB[:, :D0]
            Mn = B[:, :D0].T @ B[:, :D0]
            Mp, _, _ = pred_matrix(N, D0, pr)
            la = sl.eigh(Mq, Mn, eigvals_only=True, subset_by_index=[0, 0])[0]
            lp = sl.eigh(Mp, Mn, eigvals_only=True, subset_by_index=[0, 0])[0]
            print(f"  {D0:5d} {math.log(D0) / L:5.2f} {la * N / L:12.5f} {lp * N / L:10.5f} {la / lp:8.4f} "
                  f"{la / lamN:9.3f} {K_MIN * math.log(N / D0) / L:22.4f}", flush=True)
            D0 *= 2


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("N", nargs="*", type=int)
    ap.add_argument("--restricted", action="store_true", help="the class's smallest quotient against λ_N")
    ap.add_argument("--delta", type=float, default=0.15, help="the width of η's step (default 0.15)")
    ap.add_argument("--simple-c", action="store_true", help="c(u) = (1 − u)³(10u − 2)")
    a = ap.parse_args()
    if a.simple_c:
        set_c([-2.0, 0.0, 0.0, 0.0])
    pr = Profiles(a.delta)
    print(f"c(u) = (1 − u)³({C_POLY[0]:g} {C_POLY[1]:+.4f}u {C_POLY[2]:+g}u² {C_POLY[3]:+g}u³)", flush=True)
    print(f"δ = {a.delta}: J = {pr.J:.6f}, K₁ = {pr.K1:.6f}, I* = {pr.Istar:.6f}; I[c] = {pr.I_w:.6f}, "
          f"K_w = {pr.K_w:.6f}", flush=True)
    Ns = a.N or [2000, 8000]
    if a.restricted:
        restricted_mode(Ns, pr)
    else:
        check_mode(Ns, pr)


if __name__ == "__main__":
    main()
