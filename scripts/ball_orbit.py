"""The orbit of the Hadamard kernel as a lattice: its Gram–Schmidt pivots, computed from the primes.

A numerical experiment for the sixth first step of docs/ball-conjecture.md. It is not a check, and CI does not run it.

In a realization of K_H(r) = Σ_ρ r^{ρ−½}/(ρ(1−ρ)) by similitudes (BallLattice.Realization), the vectors w_1, w_2, …
have the Gram matrix ⟨w_n, w_m⟩ = √(mn)·K_H(m/n) (BallPsi.gram_explicit). This script computes K_H from the primes,
for x ≥ 1, by

    K_H(x) = √x·(Σ_{n ≤ x} Λ(n)(1/n − 1/x) − log x + 1 + γ − log(2π)/x + Σ_{k ≥ 1} x^{−2k−1}/(2k(2k + 1))).

This is BallPsi.kerH_explicit with its archimedean term in closed form. The closed form is checked numerically against
the integral that defines BallPsi.archH, and is not proved. The script prints the squared Gram–Schmidt norms
d_k = dist(w_k, span(w_1, …, w_{k−1}))² relative to d_1 = ‖w_1‖² = K_H(1) = 2 + γ − log 4π. If d_k ≥ d_1 for every k,
then w_1 is a shortest nonzero vector of the lattice that the orbit spans (BallPsi.orbit_lattice).

    python3 scripts/ball_orbit.py [N]           # default N = 1000; needs numpy
    python3 scripts/ball_orbit.py --smooth [N]  # the zeros replaced by their density, no primes; needs scipy
    python3 scripts/ball_orbit.py --flat [N]    # the Gram matrix against the flat model d_1·min(m, n)
    python3 scripts/ball_orbit.py --zeros [M]   # which zeros carry d_k, from the first M zeros; needs mpmath, slow
    python3 scripts/ball_orbit.py --places [N]  # the Gram matrix as a sum over the places, and its rigidity
    python3 scripts/ball_orbit.py --weil [N]    # the intersection numbers D_m·D_n of BallWeil and the Weil bound

The first three options are the computations of "What a proof under RH would need" in docs/ball-conjecture.md,
--places is that of "Building the lattice forwards", and --weil that of "Weil's form".
"""

import math
import sys

import numpy as np

EULER_GAMMA = 0.57721566490153286060651209


def tables(X):
    """Σ_{n ≤ k} Λ(n)/n and ψ(k) = Σ_{n ≤ k} Λ(n), for k ≤ X."""
    lam = np.zeros(X + 1)
    composite = np.zeros(X + 1, dtype=bool)
    for p in range(2, X + 1):
        if not composite[p]:
            composite[2 * p::p] = True
            pk = p
            while pk <= X:
                lam[pk] = math.log(p)
                pk *= p
    n = np.arange(X + 1, dtype=float)
    n[0] = 1.0
    return np.cumsum(lam / n), np.cumsum(lam)


def kernel_over_sqrt(x, A, B):
    """K_H(x)/√x for an array of x ≥ 1."""
    k = np.floor(x + 1e-12).astype(np.int64)
    y = 1.0 / x
    # Σ_{k ≥ 1} y^{2k+1}/(2k(2k+1)) = y + ½(1 − y)log(1 − y) − ½(1 + y)log(1 + y)
    with np.errstate(divide="ignore", invalid="ignore"):
        t = np.where(y < 1, 0.5 * (1 - y) * np.log1p(-np.minimum(y, 1 - 1e-300)), 0.0)
    tail = y + t - 0.5 * (1 + y) * np.log1p(y)
    return A[k] - B[k] / x - np.log(x) + 1 + EULER_GAMMA - math.log(2 * math.pi) / x + tail


def gram(N):
    """The matrix (⟨w_n, w_m⟩)_{m,n ≤ N} = (max(m, n)·K_H(max/min)/√(max/min))."""
    A, B = tables(N + 1)
    m = np.arange(1, N + 1, dtype=float)
    M, Nn = np.meshgrid(m, m, indexing="ij")
    hi, lo = np.maximum(M, Nn), np.minimum(M, Nn)
    return hi * kernel_over_sqrt(hi / lo, A, B)


def pivots(G):
    """The squared Gram–Schmidt norms d_k, from the Cholesky factor."""
    return np.diag(np.linalg.cholesky(G)) ** 2


def smooth(N):
    """Pivots with the zeros replaced by their density (1/2π)log(|γ|/2π) on |γ| ≥ 2π, against the true ones."""
    from fractions import Fraction
    from scipy.integrate import quad
    dens = lambda t: math.log(t / (2 * math.pi)) / (2 * math.pi) / (0.25 + t * t)
    cache = {}

    def K(x):
        u = abs(math.log(x))
        if u == 0:
            return 2 * quad(dens, 2 * math.pi, np.inf, limit=500)[0]
        return 2 * quad(dens, 2 * math.pi, np.inf, weight="cos", wvar=u, limlst=200)[0]

    S = np.zeros((N, N))
    for m in range(1, N + 1):
        for n in range(1, N + 1):
            f = Fraction(max(m, n), min(m, n))
            if f not in cache:
                cache[f] = K(f.numerator / f.denominator)
            S[m - 1, n - 1] = math.sqrt(m * n) * cache[f]
    ds, dt = pivots(S), pivots(gram(N))
    print(f"N = {N}: d_1 = {ds[0]:.5f} with the density, {dt[0]:.5f} with the zeros")
    print("    k   d_k/d_1 (density)   d_k/d_1 (zeros)   ratio")
    for k in range(2, N + 1):
        rs, rt = ds[k - 1] / ds[0], dt[k - 1] / dt[0]
        print(f"  {k:3d}   {rs:12.3f}   {rt:14.3f}   {rt / rs:7.3f}")


def flat(N):
    """The Gram matrix against the flat model d_1·min(m, n), and the combination Σ w_m/m."""
    for n in [5, 10, 30, 100, 300, N]:
        if n > N:
            continue
        G = gram(n)
        m = np.arange(1, n + 1)
        F = G[0, 0] * np.minimum.outer(m, m).astype(float)
        a = 1.0 / m
        print(f"N = {n:5d}: smallest eigenvalue of G − d_1·min(m, n) = {np.linalg.eigvalsh(G - F)[0]: .3e}; "
              f"‖Σ w_m/m‖² = {a @ G @ a:.4f}, flat model {a @ F @ a:.4f}")


def zeros(M):
    """For each k, the share of d_k carried by the zeros in bands of height, from the first M zeros."""
    import mpmath
    mpmath.mp.dps = 20
    g = np.array([float(mpmath.zetazero(n).imag) for n in range(1, M + 1)])
    print(f"{M} zeros, up to height {g[-1]:.0f}; d_k from the zeros (both signs) against the explicit formula")
    print("    k   d_k/d_1   zeros/explicit   share of d_k from heights  < πk   πk–4πk   4πk–16πk   > 16πk")
    kmax = int(g[-1] / (16 * math.pi))
    for k in range(2, kmax + 1):
        G = gram(k)
        c = np.linalg.solve(G[:k - 1, :k - 1], G[:k - 1, k - 1])
        dk = G[k - 1, k - 1] - G[:k - 1, k - 1] @ c
        j = np.arange(1, k + 1, dtype=float)
        coef = np.concatenate([-c, [1.0]]) * np.sqrt(j)
        err = np.abs(np.exp(1j * np.outer(g, np.log(j))) @ coef) ** 2 / (0.25 + g ** 2)
        tot = 2 * err.sum()
        bands = [g < math.pi * k, (g >= math.pi * k) & (g < 4 * math.pi * k),
                 (g >= 4 * math.pi * k) & (g < 16 * math.pi * k), g >= 16 * math.pi * k]
        shares = "   ".join(f"{2 * err[b].sum() / tot:6.1%}" for b in bands)
        print(f"  {k:3d}   {dk / G[0, 0]:7.3f}   {tot / dk:10.3f}        {shares}")


def primes_upto(X):
    sieve = np.ones(X + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(X ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return [int(p) for p in np.nonzero(sieve)[0]]


def places_gram(N, lam):
    """The Gram matrix from the closed form, for a given von Mangoldt table lam: for m ≥ n,
    G(m, n) = Σ_{k ≤ m/n} Λ(k)(m/k − n)                                   (the primes)
              + (m + n) + γm − n log 2π + m log n − (m − n)log m
              + ½(m − n)log(m − n) − ½(m + n)log(m + n)                    (the archimedean place)."""
    G = np.zeros((N, N))
    for m in range(1, N + 1):
        for n in range(1, m + 1):
            a = (m + n) + EULER_GAMMA * m - math.log(2 * math.pi) * n + m * math.log(n) - (m - n) * math.log(m)
            a += (0.5 * (m - n) * math.log(m - n) if m > n else 0.0) - 0.5 * (m + n) * math.log(m + n)
            a += sum(lam[k] * (m / k - n) for k in range(2, m // n + 1))
            G[m - 1, n - 1] = G[n - 1, m - 1] = a
    return G


def places(N):
    """The Gram matrix as the archimedean part plus a part for each prime, and how its positivity needs every prime."""
    def table(drop=(), add=None, scale=None):
        lam = np.zeros(N + 1)
        for p in primes_upto(N):
            if p in drop:
                continue
            q = p
            while q <= N:
                lam[q] = math.log(p) * (scale.get(p, 1.0) if scale else 1.0)
                q *= p
        for k, v in (add or {}).items():
            lam[k] += v
        return lam
    G = places_gram(N, table())
    print(f"N = {N}: the sum over the places reproduces the Gram matrix to {np.abs(G - gram(N)).max():.1e}")
    P = primes_upto(N)
    e0 = np.linalg.eigvalsh(places_gram(N, np.zeros(N + 1)))[0]
    print(f"  smallest eigenvalue with the archimedean part only: {e0: .3e}")
    for k in range(len(P)):
        e = np.linalg.eigvalsh(places_gram(N, table(drop=set(P[k + 1:]))))[0]
        print(f"  with the primes up to {P[k]:4d}: {e: .3e}")
    primes = set(P)
    powers = {p ** j for p in P for j in range(2, 7)}
    fake = max(k for k in range(9, N + 1, 2) if k not in primes and k not in powers)
    tests = [(f"without the prime {P[-1]}", table(drop={P[-1]})),
             (f"with a fake prime {fake}", table(add={fake: math.log(fake)})),
             ("log 2 off by 0.1%", table(scale={2: 1.001})),
             ("log 2 off by 0.01%", table(scale={2: 1.0001}))]
    for name, lam in tests:
        print(f"  {name:28s}: {np.linalg.eigvalsh(places_gram(N, lam))[0]: .3e}")


def weil(N):
    """The intersection numbers D_m·D_n = m + n − √(mn)·K_H(m/n) of BallWeil against the Weil bound
    |D_m·D_n − m − n| ≤ K_H(1)·√(mn), that is |K_H(m/n)| ≤ K_H(1)."""
    G = gram(N)
    c0 = G[0, 0]
    m = np.arange(1, N + 1, dtype=float)
    R = G / (c0 * np.sqrt(np.outer(m, m)))
    np.fill_diagonal(R, np.nan)
    def at(ij):
        a, b = ij[0] + 1, ij[1] + 1
        g = math.gcd(a, b)
        return f"{R[ij]:.4f} at m/n = {a // g}/{b // g}"
    lo = np.unravel_index(np.nanargmin(R), R.shape)
    hi = np.unravel_index(np.nanargmax(R), R.shape)
    print(f"N = {N}: D_1·D_1 = 2 − K_H(1) = {2 - c0:.6f}, so K_H(1) = {c0:.6f} plays 2g")
    print(f"  over m ≠ n ≤ N, K_H(m/n)/K_H(1) runs from {at(lo)} to {at(hi)}")
    print("  the Weil bound asks for [−1, 1]; the lower end alone gives RH (BallWeil.rh_iff_weil_bound)")
    for n in [2, 3, 5, 10, 100, 1000, 10000]:
        if n <= N:
            d = n + 1 - G[n - 1, 0]
            print(f"  D_{n}·D_1 = {d:13.6f}   (D_n·D_1 − n − 1)/(K_H(1)·√n) = {(d - n - 1) / (c0 * math.sqrt(n)):+.4f}")


def main():
    if len(sys.argv) > 1 and sys.argv[1].startswith("--"):
        arg = int(sys.argv[2]) if len(sys.argv) > 2 else None
        {"--smooth": lambda: smooth(arg or 60), "--flat": lambda: flat(arg or 1000),
         "--zeros": lambda: zeros(arg or 2000), "--places": lambda: places(arg or 60),
         "--weil": lambda: weil(arg or 1000)}[sys.argv[1]]()
        return
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    G = gram(N)
    d1 = G[0, 0]
    d = np.diag(np.linalg.cholesky(G)) ** 2 / d1
    k_min = 2 + int(np.argmin(d[1:]))
    print(f"N = {N}: ‖w_1‖² = K_H(1) = {d1:.12f}")
    print(f"  the Gram matrix is positive definite (Cholesky succeeded); smallest eigenvalue "
          f"{np.linalg.eigvalsh(G)[0]:.3e}")
    print(f"  min over 2 ≤ k ≤ {N} of d_k/d_1 = {d[1:].min():.4f}, at k = {k_min}")
    for k in [2, 3, 5, 10, 30, 100, 300, 1000, 2000, 3000, 5000]:
        if k <= N:
            print(f"  k = {k:>5}: d_k/d_1 = {d[k - 1]:9.3f}   d_k/(d_1·log²k) = {d[k - 1] / math.log(k) ** 2:.3f}")
    print("  so ±w_1 are the shortest nonzero vectors of the lattice spanned by w_1, …, w_N"
          if d[1:].min() > 1 else "  some d_k < d_1")


if __name__ == "__main__":
    main()
