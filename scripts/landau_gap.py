#!/usr/bin/env python3
"""The Landau gap of formalisations/ball-rate.md (section "Why the sampling route stops at 1/N"). Uncertified numerics.

    python3 scripts/landau_gap.py [N ...] [--c0 C ...]

Landau's form is L(c) = 2 Σ_{n ≤ N} Λ(n) n^{−1/2} Σ_{jn ≤ N} c_j c_{jn} = cᵀMc, with M the symmetric matrix of the pairs
(j, jn). BallDensity.landau_le_sharp bounds it by (log N + c₀)|c|², c₀ = log 4 + 1. For each N and c₀ this prints, with
B = (log N + c₀)I − M and D = diag(1/m):

  η_N = min_c [(log N + c₀)|c|² − L(c)] / Σ_m c_m²/m, the largest η with B ⪰ ηD, as 1/(top eigenvalue of
        D^{1/2}B⁻¹D^{1/2});
  Cap(1) = 1/(B⁻¹)₁₁ = min over c with c₁ = 1 of (log N + c₀)|c|² − L(c), the capacity of m = 1;

as η_N/log N, η_N/√log N, Cap(1)/log N and Cap(1)/√log N, against √(2(c₀ + γ)). B⁻¹ is applied by conjugate gradients
(B is positive definite with condition number O(log N)), so N = 10⁶ takes about two minutes.
"""
import argparse
import math
import time

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla

GAMMA = 0.5772156649015329


def mangoldt(N):
    lam = np.zeros(N + 1)
    sieve = np.ones(N + 1, bool)
    sieve[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    for p in np.nonzero(sieve)[0]:
        q, lp = int(p), math.log(p)
        while q <= N:
            lam[q] = lp
            q *= int(p)
    return lam


def landau_matrix(N):
    """The symmetric matrix M with cᵀMc = 2 Σ_n Λ(n) n^{−1/2} Σ_{jn ≤ N} c_j c_{jn} (indices 1..N as 0..N−1)."""
    lam = mangoldt(N)
    rows, cols, vals = [], [], []
    for n in np.nonzero(lam)[0]:
        n = int(n)
        j = np.arange(1, N // n + 1)
        rows.append(j - 1)
        cols.append(j * n - 1)
        vals.append(np.full(len(j), lam[n] / math.sqrt(n)))
    A = sp.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(N, N))
    return (A + A.T).tocsr()


def solve(B, b):
    x, info = sla.cg(B, b, rtol=1e-11, maxiter=5000)
    if info != 0:
        raise RuntimeError(f"conjugate gradients did not converge ({info})")
    return x


def gap(N, c0, M=None):
    M = landau_matrix(N) if M is None else M
    L = math.log(N)
    B = ((L + c0) * sp.identity(N, format="csr") - M).tocsr()
    e1 = np.zeros(N)
    e1[0] = 1.0
    cap1 = 1.0 / solve(B, e1)[0]
    d = 1.0 / np.sqrt(np.arange(1, N + 1, dtype=float))
    op = sla.LinearOperator((N, N), matvec=lambda x: d * solve(B, d * x), dtype=float)
    top = sla.eigsh(op, k=1, which="LA", return_eigenvectors=False, tol=1e-6, maxiter=2000)[0]
    return 1.0 / top, cap1


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("N", nargs="*", type=int, default=[1000, 10000, 100000, 1000000])
    ap.add_argument("--c0", nargs="*", type=float, default=[0.0, math.log(4) + 1])
    args = ap.parse_args()
    print(f"{'N':>9} {'c0':>6} {'eta/logN':>9} {'eta/sqrtL':>10} {'Cap1/logN':>10} {'Cap1/sqrtL':>11} "
          f"{'sqrt(2(c0+g))':>14} {'s':>6}")
    for N in args.N:
        t = time.time()
        M = landau_matrix(N)
        L = math.log(N)
        for c0 in args.c0:
            eta, cap1 = gap(N, c0, M)
            print(f"{N:9d} {c0:6.3f} {eta / L:9.4f} {eta / math.sqrt(L):10.3f} {cap1 / L:10.4f} "
                  f"{cap1 / math.sqrt(L):11.3f} {math.sqrt(2 * (c0 + GAMMA)):14.3f} {time.time() - t:6.0f}",
                  flush=True)


if __name__ == "__main__":
    main()
