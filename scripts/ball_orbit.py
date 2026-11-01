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

The three options are the computations of "What a proof under RH would need" in docs/ball-conjecture.md.
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


def main():
    if len(sys.argv) > 1 and sys.argv[1].startswith("--"):
        arg = int(sys.argv[2]) if len(sys.argv) > 2 else None
        {"--smooth": lambda: smooth(arg or 60), "--flat": lambda: flat(arg or 1000),
         "--zeros": lambda: zeros(arg or 2000)}[sys.argv[1]]()
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
