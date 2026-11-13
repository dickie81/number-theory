"""The hyperplane Σ x_n = 0 of the orbit lattice: how it sits against w_1, and what lies inside it. Uncertified numerics.

A numerical experiment for the section "How the hyperplane sits" of formalisations/ball-rate.md and the remark "How
the hyperplane sits" of papers/orbit-lattice. It is not a check, and CI does not run it.

On the hyperplane H = {Σ_n x_n = 0} the orbit form Q_N(x) = Σ x_m x_n √(mn)·K_H(m/n) is Weil's form of the step
function g_x(t) = e^{t/2} Σ_n x_n 1_(0, log n](t) (OrbitWindow.form_eq_weilQg). One direction lies off it: w_1. The
script prints four things.

- The squared distance from w_1 to H, dist² = 1/(1ᵀ G_N⁻¹ 1) = min {Q_N(z) : Σ_n z_n = 1}, and the angle between w_1
  and H, arcsin √(dist²/d_1), for every N ≤ 3000 at once: with G_3000 = L Lᵀ, the leading blocks of L factor every
  G_N, so 1ᵀ G_N⁻¹ 1 = Σ_{i ≤ N} v_i² for v = L⁻¹1. A direct solve checks two values. In the flat model,
  G = min(m, n), the angle is 90° for every N, since H then holds the increments of Brownian motion after time 1.
- The shortest nonzero integer vector of H for N ≤ 30, by Fincke–Pohst in the coordinates y_k = Σ_{n ≥ k} x_n
  (k = 2, …, N), the values of the step function on (k − 1, k]. They are unimodular: x_n = y_n − y_{n+1} for n ≥ 2 and
  x_1 = −y_2, so the integer points of H are the integer-valued step functions.
- Q_N of the unit steps δ_k − δ_{k−1}, which are all shortest vectors of H in the flat model.
- The least value over H of QW(g_x)/‖g_x‖² = Q_N(x)/Σ_{k ≥ 2} y_k², Weil's Rayleigh quotient on the window, restricted
  to the step functions. On H the flat form is Σ_{k ≥ 2} y_k² = ‖g_x‖², so this is also ζ's form against the flat one.

The Gram matrix comes from the primes, as in scripts/ball_orbit.py, in double precision.

    python3 scripts/window_hyperplane.py     # needs numpy and scipy; about two seconds
"""
import math
import os
import sys

import numpy as np
import scipy.linalg as sl

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ball_orbit import gram  # noqa: E402

NMAX = 3000
C0 = 999 / 1000 * 2 / 45 * 13 / 10      # the margin of PivotSharp, in Lean: Q ≥ c_0 at every nonzero integer point of H


def step_basis(N):
    """The matrix T with x = T y: columns are the step functions 1_(k−1, k], k = 2..N, in orbit coordinates."""
    T = np.zeros((N, N - 1))
    for k in range(2, N + 1):
        T[k - 1, k - 2] += 1.0
        if k >= 3:
            T[k - 2, k - 2] -= 1.0
    T[0, 0] -= 1.0
    return T


def shortest(G, R, max_nodes=5_000_000):
    """Fincke–Pohst on the positive definite Gram matrix G: every nonzero integer y with yᵀGy ≤ R, sorted."""
    n = len(G)
    U = np.linalg.cholesky(G).T
    dg = np.diag(U) ** 2
    mu = U / np.diag(U)[:, None]
    y = [0] * n
    found, nodes = [], [0]

    def rec(i, rem):
        nodes[0] += 1
        if nodes[0] > max_nodes:
            raise RuntimeError("node budget exceeded")
        c = -sum(mu[i, j] * y[j] for j in range(i + 1, n))
        r = math.sqrt(max(rem, 0.0) / dg[i])
        for v in range(math.ceil(c - r - 1e-9), math.floor(c + r + 1e-9) + 1):
            t = rem - dg[i] * (v - c) ** 2
            if t < -1e-12 * R:
                continue
            y[i] = v
            if i == 0:
                if any(y):
                    found.append((R - t, list(y)))
            else:
                rec(i - 1, t)
        y[i] = 0
    rec(n - 1, R)
    return sorted(found)


def main():
    G = gram(NMAX)
    d1 = G[0, 0]
    print(f"d_1 = K_H(1) = {d1:.6f}; the Lean margin c_0 = {C0:.6f} = {C0 / d1:.4f} d_1")

    print("\n1. How H sits: dist²(w_1, H) = 1/(1ᵀ G_N⁻¹ 1), and the angle between w_1 and H")
    L = np.linalg.cholesky(G)
    v = sl.solve_triangular(L, np.ones(NMAX), lower=True)
    inv = np.cumsum(v * v)
    print(f"   {'N':>5}  {'dist²/d_1':>11}  {'angle':>9}  {'1/(N·dist²/d_1)':>16}")
    for N in (2, 3, 5, 10, 30, 100, 300, 1000, 3000):
        s2 = 1 / inv[N - 1] / d1
        print(f"   {N:>5}  {s2:11.4e}  {math.degrees(math.asin(math.sqrt(s2))):8.4f}°  {1 / (N * s2):16.3f}")
    worst = 0.0
    for N in (10, 1000):
        z = np.linalg.solve(G[:N, :N], np.ones(N))
        worst = max(worst, abs(1 / z.sum() - 1 / inv[N - 1]) * inv[N - 1])
    print(f"   direct solves at N = 10 and 1000 agree to relative {worst:.1e}")
    F = np.minimum.outer(np.arange(1, 101.0), np.arange(1, 101.0))
    sf = 1 / np.linalg.solve(F, np.ones(100)).sum() / F[0, 0]
    print(f"   flat model, G = min(m, n), N = 100: dist²/d_1 = {sf:.12f}, angle {math.degrees(math.asin(math.sqrt(sf))):.6f}°")

    print("\n2. The shortest nonzero integer vectors of H at N = 30 (in units of d_1)")
    N = 30
    T = step_basis(N)
    M = T.T @ G[:N, :N] @ T
    vecs = shortest(np.ascontiguousarray(M), 6.0 * d1)
    seen = []
    for val, y in vecs:
        key = tuple(y) if tuple(y) > tuple(-w for w in y) else tuple(-w for w in y)
        if key in seen:
            continue
        seen.append(key)
        x = T @ np.array(key)
        xs = {n + 1: int(round(w)) for n, w in enumerate(x) if round(w)}
        print(f"   {val / d1:8.4f}   ±x = {xs}")
    print(f"   (every vector below 6 d_1; Fincke–Pohst in the step coordinates; the Lean bound is {C0 / d1:.4f} d_1)")

    print("\n3. The unit steps δ_k − δ_{k−1}: Q/d_1 (each is 1 in the flat model)")
    ks = (2, 3, 5, 10, 30, 100, 300, 1000, 3000)
    vals = [(G[k - 1, k - 1] - 2 * G[k - 1, k - 2] + G[k - 2, k - 2]) / d1 for k in ks]
    print("   " + "  ".join(f"k={k}: {q:.3f}" for k, q in zip(ks, vals)))
    print(f"   growth per unit of log k between k = 100 and 3000: {(vals[-1] - vals[-4]) / math.log(30):.2f} d_1")

    print("\n4. The least value of QW(g_x)/‖g_x‖² over H (Weil's Rayleigh quotient on the step functions)")
    print(f"   {'N':>5}  {'min':>11}  {'min·N²':>8}  {'min·N²/√log N':>14}")
    for N in (2, 3, 5, 10, 30, 100, 300, 1000):
        T = step_basis(N)
        mu = np.linalg.eigvalsh(T.T @ G[:N, :N] @ T)[0]
        print(f"   {N:>5}  {mu:11.4e}  {mu * N * N:8.4f}  {mu * N * N / math.sqrt(math.log(N)):14.4f}")


if __name__ == "__main__":
    main()
