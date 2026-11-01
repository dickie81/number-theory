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

    python3 scripts/ball_orbit.py [N]      # default N = 1000; needs numpy
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


def main():
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
