#!/usr/bin/env python3
"""The alternating vector of formalisations/ball-rate.md (section "The upper bound"). Uncertified numerics.

    python3 scripts/alt_vector.py [N ...]       # default N = 100 300 1000 3000 10000 30000; needs numpy

For x_n = (−1)^{n+1}/n (BallUpper.xa) and for the near-flat vector x_n = (1 − n/N)²/ψ(n) of Statement 2A, with ψ
Dedekind's function, this prints the Rayleigh quotient q_N = Q_N(x)/Σ_{n ≤ N} x_n² of the orbit form
Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn) K_H(m/n) as q_N·N/log N, and for N ≤ 3000 the smallest eigenvalue λ_N of the Gram
matrix as λ_N·N/log N. K_H is computed from the primes as in scripts/ball_orbit.py, and Q_N(x) is summed in blocks of
rows, so no N × N matrix is stored beyond N = 3000.
"""
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ball_orbit import gram, kernel_over_sqrt, tables  # noqa: E402


def quad(N, x, A, B, block=2000):
    """Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn) K_H(m/n), with K_H(r) = K_H(1/r)."""
    m = np.arange(1, N + 1, dtype=float)
    total = 0.0
    for s in range(0, N, block):
        rows = m[s:s + block][:, None]
        hi, lo = np.maximum(rows, m[None, :]), np.minimum(rows, m[None, :])
        G = hi * kernel_over_sqrt(hi / lo, A, B)
        total += x[s:s + block] @ (G @ x)
    return total


def dedekind(N):
    """ψ(n) = n Π_{p ∣ n}(1 + 1/p) for n = 1, …, N."""
    psi = np.arange(N + 1, dtype=float)
    composite = np.zeros(N + 1, bool)
    for p in range(2, N + 1):
        if not composite[p]:
            composite[2 * p::p] = True
            psi[p::p] *= 1 + 1 / p
    return psi[1:]


def main():
    Ns = [int(a) for a in sys.argv[1:]] or [100, 300, 1000, 3000, 10000, 30000]
    print(f"{'N':>6} {'alternating q·N/log N':>22} {'near-flat q·N/log N':>20} {'λ_N·N/log N':>12} {'s':>5}")
    for N in Ns:
        t = time.time()
        A, B = tables(N + 1)
        n = np.arange(1, N + 1, dtype=float)
        xa = (-1.0) ** (n - 1) / n
        xd = (1 - n / N) ** 2 / dedekind(N)
        L = math.log(N)
        qa = quad(N, xa, A, B) / (xa @ xa) * N / L
        qd = quad(N, xd, A, B) / (xd @ xd) * N / L
        lam = f"{np.linalg.eigvalsh(gram(N))[0] * N / L:12.4f}" if N <= 3000 else f"{'':>12}"
        print(f"{N:6d} {qa:22.4f} {qd:20.4f} {lam} {time.time() - t:5.0f}", flush=True)


if __name__ == "__main__":
    main()
