"""A certificate for the orbit-lattice conjecture up to N: rigorous bounds for the Gram–Schmidt pivots of
G_N = (√(mn)·K_H(m/n))_{m,n ≤ N}, the Gram matrix of the orbit of docs/ball-conjecture.md.

It proves, for the N given, that every pivot d_k = dist(w_k, span(w_1, …, w_{k−1}))² with 2 ≤ k ≤ N exceeds
d_1 = K_H(1), and that d_2 is the smallest of them: d_k > d_2 for 3 ≤ k ≤ N. So G_N is positive definite. The proof
is unconditional: the entries come from the primes, and every rounding error is bounded.

1. The entries. For x ≥ 1 and c > 1, (1/2πi)∫_(c) (−ζ'/ζ)(s)·x^s/(s(s − 1)) ds = Σ_{k ≤ x} Λ(k)(x/k − 1), as
   (1/2πi)∫_(c) y^s/(s(s − 1)) ds = max(y − 1, 0). The integrand decays like |s|^−2, so the line moves to the left
   through the poles. They are x(log x − 1 − γ) at s = 1, log 2π at s = 0, x^ρ/(ρ(1 − ρ)) at each zero ρ (with
   multiplicity), and −x^{−2j}/(2j(2j + 1)) at s = −2j. This is the classical explicit formula with the kernel
   1/(s(s − 1)). The sum over the zeros is √x·K_H(x), so for m ≥ n
       G(m, n) = m·A(⌊m/n⌋) − n·ψ(⌊m/n⌋) + (m + n) + γm − n·log 2π + m·log n − (m − n)·log m
                 + ½(m − n)·log(m − n) − ½(m + n)·log(m + n),
   with A(j) = Σ_{k ≤ j} Λ(k)/k and ψ(j) = Σ_{k ≤ j} Λ(k). The series over the trivial zeros is in closed form,
   Σ_j y^{2j}/(2j(2j + 1)) = 1 + ((1 − y)·log(1 − y) − (1 + y)·log(1 + y))/(2y). The Lean form of the formula,
   BallPsi.kerH_explicit, writes the archimedean part as an integral, and agrees with this one numerically
   (scripts/ball_orbit.py).
2. The constants log k for k ≤ 2N, A(j), ψ(j), γ and log 2π are computed in mpmath's interval arithmetic at 120
   bits and rounded to doubles, each checked to lie within u·|v| of its interval, u = 2^−53. An entry is a sum of nine
   terms c·v with c an integer or half-integer below 2N, so its rounding error is at most 16u·Σ|c·v| (two roundings
   for each term and γ_8 for the sum, with room to spare).
3. The pivots. A unit lower-triangular T leaves the leading principal minors of T·G·Tᵀ equal to those of G, so the
   pivots are the same. With T close to the inverse of G's Cholesky factor, H = T·G·Tᵀ is nearly diagonal. The
   floating-point products are enclosed by the standard bound |fl(A·B) − A·B| ≤ γ_n|A|·|B|, γ_n = nu/(1 − nu),
   valid in any order of summation, with a constant added for underflow. Then λ_min of each leading block of H is at
   least its smallest Gershgorin bound μ, and d_k ≥ H_kk − ‖h_k‖²/μ_{k−1}, with h_k the part of the k-th column above
   the diagonal.

It assumes IEEE-754 binary64 arithmetic with rounding to nearest in numpy and its BLAS, and the correctness of
mpmath's interval arithmetic. It is not a check, and CI does not run it.

    python3 scripts/ball_certificate.py [N]   # default 3000, about 10 s; 10000 takes 2 minutes and 6 GB
"""

import sys
import time

import numpy as np
from mpmath import iv, mp, mpf
from scipy.linalg import solve_triangular

U = 2.0 ** -53
mp.prec = 200
iv.prec = 120


def to_double(x):
    """The double nearest the midpoint of the interval x, checked to lie within u·|v| of every point of x."""
    lo, hi = mpf(x.a), mpf(x.b)
    v = float((lo + hi) / 2)
    assert max(abs(mpf(v) - lo), abs(mpf(v) - hi)) <= U * abs(v), (x, v)
    return v


def constants(N):
    """A(j), ψ(j) for j ≤ N, log k for k ≤ 2N, γ and log 2π, as doubles within u·|v| of the true values."""
    sieve = bytearray([1]) * (N + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, N + 1, i)))
    lam = [iv.mpf(0)] * (N + 1)
    for p in range(2, N + 1):
        if sieve[p]:
            lp = iv.log(iv.mpf(p))
            q = p
            while q <= N:
                lam[q] = lp
                q *= p
    A, P = np.zeros(N + 1), np.zeros(N + 1)
    a, s = iv.mpf(0), iv.mpf(0)
    for j in range(1, N + 1):
        a, s = a + lam[j] / j, s + lam[j]
        A[j], P[j] = to_double(a), to_double(s)
    L = np.zeros(2 * N + 1)
    for k in range(1, 2 * N + 1):
        L[k] = to_double(iv.log(iv.mpf(k)))
    return A, P, L, to_double(iv.euler), to_double(iv.log(2 * iv.pi))


def enclosure(N, block=500):
    """Ĝ and E with |G(m, n) − Ĝ(m, n)| ≤ E(m, n) for all m, n ≤ N."""
    A, P, L, gam, l2pi = constants(N)
    G, E = np.zeros((N, N)), np.zeros((N, N))
    for m0 in range(1, N + 1, block):
        m = np.arange(m0, min(m0 + block, N + 1))[:, None]
        n = np.arange(1, N + 1)[None, :]
        m, n = np.broadcast_arrays(m, n)
        keep = n <= m
        m, n = m[keep], n[keep]
        j, d, s = m // n, m - n, m + n
        mf, nf, df, sf = m.astype(float), n.astype(float), d.astype(float), s.astype(float)
        terms = [mf * A[j], -nf * P[j], sf, gam * mf, -l2pi * nf, mf * L[n], -df * L[m],
                 np.where(d > 0, 0.5 * df * L[np.maximum(d, 1)], 0.0), -0.5 * sf * L[s]]
        val, size = np.zeros(len(m)), np.zeros(len(m))
        for t in terms:
            val += t
            size += np.abs(t)
        G[m - 1, n - 1] = G[n - 1, m - 1] = val
        E[m - 1, n - 1] = E[n - 1, m - 1] = 16 * U * size * (1 + 1e-12)
    return G, E


def certify(N):
    t0 = time.time()
    G, E = enclosure(N)
    t1 = time.time()
    T = np.linalg.cholesky(G)
    T /= np.diag(T)[None, :]
    T = solve_triangular(T, np.eye(N), lower=True, unit_diagonal=True, overwrite_b=True)
    T = np.tril(T, -1)
    T[np.diag_indices(N)] = 1.0                  # exactly unit lower-triangular
    g = N * U / (1 - N * U)
    P = T @ G
    H = P @ T.T
    aT = np.abs(T)
    del T
    W = (aT @ np.abs(G)) * (1 + 2 * g)
    W += np.abs(P)
    W *= g
    del P, G
    W += (aT @ E) * (1 + 2 * g)
    del E
    R = (W @ aT.T) * (1 + 2 * g) + 1e-290       # |T·G·Tᵀ − H| ≤ R entrywise; the constant covers underflow
    del W, aT
    t2 = time.time()
    diag_lo = np.diag(H) - np.diag(R) - 4 * U * np.abs(np.diag(H))
    d1_lo, d1_hi = diag_lo[0], H[0, 0] + R[0, 0] + 4 * U * H[0, 0]
    d2_hi = H[1, 1] + R[1, 1] + 4 * U * H[1, 1]
    O = np.abs(H)
    O += R
    del H, R
    O[np.diag_indices(N)] = 0.0
    sq = np.einsum("ij,ij->j", np.triu(O, 1), np.triu(O, 1)) * (1 + 2 * g)   # Σ_{j<k} |H_jk|² ≤ sq[k]
    np.cumsum(O, axis=0, out=O)                  # O[k, j] = Σ_{i ≤ k} |H_ij|, off the diagonal
    mu = np.empty(N)                             # λ_min(H_{k+1}) ≥ mu[k], by Gershgorin
    for k in range(N):
        mu[k] = np.min(diag_lo[:k + 1] - O[k, :k + 1] * (1 + 2 * g))
    d = np.empty(N)
    d[0] = d1_lo
    for k in range(1, N):
        assert mu[k - 1] > 0
        d[k] = diag_lo[k] - sq[k] / mu[k - 1] * (1 + 4 * U)
    t3 = time.time()
    k3 = 3 + int(np.argmin(d[2:]))
    print(f"N = {N}: entries {t1 - t0:.0f} s, congruence {t2 - t1:.0f} s, bounds {t3 - t2:.0f} s")
    print(f"  d_1 = K_H(1) ∈ [{d1_lo:.12f}, {d1_hi:.12f}]")
    print(f"  d_2 ∈ [{d[1]:.12f}, {d2_hi:.12f}], so d_2/d_1 ≥ {d[1] / d1_hi:.6f}")
    print(f"  d_k ≥ {d[2:].min():.6f} = {d[2:].min() / d1_hi:.4f}·d_1 for 3 ≤ k ≤ N, the least lower bound at k = {k3}")
    ok = bool(np.all(d[1:] > d1_hi)) and bool(np.all(d[2:] > d2_hi))
    print("  proved: d_k > d_1 for 2 ≤ k ≤ N, and d_k > d_2 for 3 ≤ k ≤ N" if ok else "  NOT proved")
    return ok


if __name__ == "__main__":
    sys.exit(0 if certify(int(sys.argv[1]) if len(sys.argv) > 1 else 3000) else 1)
