#!/usr/bin/env python3
"""dh_abs_zero.py: zeros of the Davenport–Heilbronn function with real part above 1.

    python3 scripts/dh_abs_zero.py search TMAX [WINDOWS] [DIMS]      # needs numpy, mpmath, fpylll
    python3 scripts/dh_abs_zero.py verify K SIGMA DELTA [LAMBDA...]  # needs numpy, mpmath

Numerical, uncertified; CI does not run it. `docs/research-opportunities.md` (§8.5) records what it found.

For `Re s > 1` Titchmarsh's `f` (`scripts/dh_sigma_scan.py`) vanishes exactly where

    G(s) := Σ_{p ≡ ±2 (5)} 2 artanh(χ(p) p^{−s}) = log(L(s, χ)/L(s, χ̄))   equals   −i(π − 2 arctan κ),

a point with `Re G = 0` and `Im G = −2.588…`. Each prime contributes at most `2 arctan p^{−σ}` to `−Im G`, when
`χ(p)p^{−it} = −i`: when `t·log p/2π` is `1/2` modulo 1 for `p ≡ 2 (mod 5)` and `0` modulo 1 for `p ≡ 3 (mod 5)`.

`search`: for the first `n` such primes (`DIMS`, default `22,…,34`) and each window of heights of width `2W`
(`WINDOWS`, default `1e10,3e10,1e11`) below `TMAX`, the lattice point nearest to that alignment, with the weights
`p^{−1/2}` of the quadratic loss `Σ p^{−1}(2πδ_p)²` (fpylll: LLL, BKZ, then the closest vector). At each height `t = K/64`
found, `G(1 + it)` over the primes below `2·10⁶`, with the phases `t·log p/2π` modulo 1 in exact integer arithmetic
from logarithms of 60 digits, and Newton's method for `G(s) = −i(π − 2 arctan κ)`. It prints the heights where that
converges to a point with `Re s > 1`: `K`, the real part and the shift `DELTA` of the height.

`verify`: the same zero by the approximate functional equation of `f`, which does not use the Euler product:

    f(s) = Σ_{n ≤ λx} a_n n^{−s} + X(s) Σ_{n ≤ x/λ} a_n n^{s−1} + O(x^{−σ}),   x = √(5t/2π),

at `s = SIGMA + i(K/64 + DELTA)`, with the phases of `n^{−it}` exact as above (through the prime factors of `n`) and
`X(s)` by mpmath. It polishes the zero by Newton's method at `λ = 1`, prints `|f|` there for each `LAMBDA` (different
splits of the sum; they agree to about `x^{−σ}`), and the winding number of `f` around a circle of radius `0.003`.
"""
import math
import sys
import time

import mpmath as mp
import numpy as np

mp.mp.dps = 80
KAPPA = (math.sqrt(10 - 2 * math.sqrt(5)) - 2) / (math.sqrt(5) - 1)
TARGET = math.pi - 2 * math.atan(KAPPA)      # a zero has Re G = 0 and Im G = −TARGET
DEN = 64                                     # heights are K/DEN
SC = 1 << 260                                # log p / 2π is held as an integer over SC


def primes_upto(N):
    sieve = np.ones(N + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    return np.nonzero(sieve)[0]


def alpha(p):
    """`⌊log p / 2π · SC⌋`."""
    return int(mp.floor(mp.log(int(p)) / (2 * mp.pi) * SC))


def frac_phase(k, a):
    """`t·log p/2π` modulo 1 for `t = k/DEN`, as a float, from `a = alpha(p)`."""
    return (((k * a) // DEN) & (SC - 1)) / SC


# ---------------------------------------------------------------------------------------------------- the search

class Model:
    """`G` over the primes `p ≡ ±2 (mod 5)` below `pmax`."""

    def __init__(self, pmax=2_000_000):
        self.p = [int(p) for p in primes_upto(pmax) if p % 5 in (2, 3)]
        self.alpha = [alpha(p) for p in self.p]
        self.logp = np.array([math.log(p) for p in self.p])
        self.chi = np.where(np.array([p % 5 == 2 for p in self.p]), 1j, -1j)

    def phases(self, k):
        return np.array([frac_phase(k, a) for a in self.alpha])

    def G(self, sigma, u, delta=0.0):
        """`G(sigma + i(t + delta))` and its derivative, from the phases `u` at `t`."""
        z = np.exp(-sigma * self.logp) * np.exp(-1j * (2 * np.pi * u + delta * self.logp)) * self.chi
        return np.sum(2 * np.arctanh(z)), np.sum(-self.logp * 2 * z / (1 - z * z))

    def solve(self, u):
        """Newton's method for `G(s) = −i·TARGET` from `1 + it`: `(sigma, delta)`, or `None`."""
        s = complex(1.0, 0.0)
        for _ in range(60):
            G, dG = self.G(s.real, u, s.imag)
            step = (G + 1j * TARGET) / dG
            if abs(step) > 0.05:
                step *= 0.05 / abs(step)
            s -= step
            if abs(step) < 1e-13:
                return s
        return None


def lattice_points(model, n, W, tmax):
    """For each window of width `2W` below `tmax`, the `K` of the lattice point nearest to the alignment of the
    first `n` primes."""
    from fpylll import BKZ, CVP, LLL, IntegerMatrix
    SH = 110
    w = [math.sqrt(model.p[j] ** -1.0) * 2 * math.pi for j in range(n)]
    slack = sum(2 * math.atan(1 / model.p[j]) for j in range(n)) - TARGET
    eps = math.sqrt(max(slack, 0.02)) / W
    B = IntegerMatrix(n + 1, n + 1)
    e0 = int(eps / DEN * (1 << SH))
    B[0, 0] = e0
    for j in range(n):
        B[0, j + 1] = int(mp.mpf(w[j]) * mp.mpf(model.alpha[j]) / SC / DEN * (1 << SH))
        B[j + 1, j + 1] = int(w[j] * (1 << SH))
    LLL.reduction(B)
    BKZ.reduction(B, BKZ.Param(block_size=min(24, n + 1)))
    out = []
    for c in range(int(tmax / (2 * W)) + 1):
        tc = W * (2 * c + 1)
        target = [int(eps * tc * (1 << SH))] + [int(w[j] * (0.5 if model.p[j] % 5 == 2 else 0.0) * (1 << SH))
                                                 for j in range(n)]
        out.append(round(CVP.closest_vector(B, target)[0] / e0))
    return out


def search(tmax, windows, dims):
    model = Model()
    seen, found = set(), []
    for n in dims:
        for W in windows:
            for k in lattice_points(model, n, W, tmax):
                if k <= 0 or k in seen or k / DEN > 1.2 * tmax:
                    continue
                seen.add(k)
                u = model.phases(k)
                if model.G(1.0, u)[0].imag > -2.45:
                    continue
                s = model.solve(u)
                if s is not None and s.real > 1 and abs(s.imag) < 1:
                    found.append((k / DEN + s.imag, k, s))
    print(f"{len(seen)} heights examined; zeros of the model with Re s > 1:")
    last = None
    for t, k, s in sorted(found):
        if last is None or abs(t - last) > 0.5:
            print(f"K = {k}: s ≈ {s.real:.6f} + {t:.3f} i   (verify {k} {s.real:.6f} {s.imag:.6f})", flush=True)
        last = t


# ------------------------------------------------------------------------------------------ the verification

class AFE:
    """The approximate functional equation of `f` at the heights `k/DEN + delta`."""

    def __init__(self, k, factor=1.0):
        self.k, self.t = k, k / DEN
        N = int(factor * math.sqrt(5 * self.t / (2 * math.pi))) + 1
        spf = np.zeros(N + 1, dtype=np.int32)          # the least prime factor
        for p in range(2, int(N ** 0.5) + 1):
            if spf[p] == 0:
                sl = spf[p * p::p]
                sl[sl == 0] = p
        primes = np.nonzero(spf == 0)[0]
        primes = primes[primes >= 2]
        spf[primes] = primes
        u = np.zeros(N + 1)
        for p in primes:
            u[p] = frac_phase(k, alpha(p))
        lo = 2
        while lo <= N:                                 # the phase of n from those of n/p and p
            hi = min(2 * lo, N + 1)
            n = np.arange(lo, hi)
            comp = n[spf[lo:hi] != n]
            if len(comp):
                p = spf[comp]
                u[comp] = u[comp // p] + u[p]
            lo = hi
        u -= np.floor(u)
        n = np.arange(1, N + 1)
        a = np.array([0.0, 1.0, KAPPA, -KAPPA, -1.0])[n % 5]
        keep = a != 0
        self.n, self.a, self.u = n[keep].astype(float), a[keep], u[1:][keep]
        self.logn = np.log(self.n)

    def X(self, sigma, delta):
        s = mp.mpc(sigma, mp.mpf(self.k) / DEN + delta)
        return complex(mp.power(5, mp.mpf(1) / 2 - s) * mp.power(2, s) * mp.power(mp.pi, s - 1)
                       * mp.gamma(1 - s) * mp.cos(mp.pi * s / 2))

    def f(self, sigma, delta, lam=1.0):
        x0 = math.sqrt(5 * (self.t + delta) / (2 * math.pi))
        m = self.n <= lam * x0
        main = np.sum(self.a[m] * np.exp(-sigma * self.logn[m])
                      * np.exp(-1j * (2 * np.pi * self.u[m] + delta * self.logn[m])))
        m = self.n <= x0 / lam
        dual = np.sum(self.a[m] * np.exp((sigma - 1) * self.logn[m])
                      * np.exp(1j * (2 * np.pi * self.u[m] + delta * self.logn[m])))
        return main + self.X(sigma, delta) * dual


def verify(k, sigma, delta, lams):
    t0 = time.time()
    A = AFE(k, factor=max(max(lams), 1 / min(lams)))
    s = complex(sigma, delta)
    for _ in range(12):
        f0, f1 = A.f(s.real, s.imag), A.f(s.real, s.imag + 1e-5)
        step = f0 / ((f1 - f0) / 1e-5j)
        s -= step
        if abs(step) < 1e-11:
            break
    th = np.linspace(0, 2 * np.pi, 49)
    vals = np.array([A.f(s.real + 0.003 * math.cos(x), s.imag + 0.003 * math.sin(x)) for x in th])
    turn = np.angle(vals[1:] / vals[:-1])
    print(f"K = {k}: zero at {s.real:.10f} + {mp.nstr(mp.mpf(k) / DEN + s.imag, 22)} i "
          f"({len(A.n)} terms, {time.time() - t0:.0f}s)")
    print("   |f| at it: " + ", ".join(f"{abs(A.f(s.real, s.imag, lam=lam)):.1e} (λ = {lam:g})" for lam in lams))
    print(f"   winding number around the circle of radius 0.003: {turn.sum() / (2 * np.pi):+.4f} "
          f"(least |f| on it {np.abs(vals).min():.2e})", flush=True)


def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "search":
        windows = [float(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [1e10, 3e10, 1e11]
        dims = [int(x) for x in sys.argv[4].split(",")] if len(sys.argv) > 4 else [22, 24, 26, 28, 30, 32, 34]
        search(float(sys.argv[2]), windows, dims)
    elif len(sys.argv) >= 5 and sys.argv[1] == "verify":
        lams = [float(x) for x in sys.argv[5:]] or [1.0, 2.0, 0.5]
        verify(int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), lams)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
