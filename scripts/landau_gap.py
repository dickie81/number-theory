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

    python3 scripts/landau_gap.py --spread [N ...]     # default N = 250 500 1000 2000; dense, so N ≤ 3000

The vectors that BallSharp.rate_slack leaves, Q_N(x) ≥ (Σx_n² n + G(c))/(22e⁸N) with c_n = x_n√n and Landau's slack
G(c) = (log N + c₀)Σc_n² − L(c), c₀ = log 4 + 1 (section "Which vectors the slack leaves" of the note). With the spread
A = Σx_n² n/Σx_n² and B = G(c)/Σx_n², it prints λ_N·N/log N; A/log N and B/log N at the minimiser of the orbit form
Q_N; at the edge vector, the minimiser of A + B: (A + B)/√log N, x₁² and Q_N(x)·N/log N; and the first four
eigenvalues of A + B over √log N. Q_N is the prime-side Gram matrix of scripts/ball_orbit.py.

    python3 scripts/landau_gap.py --gap [N ...]        # default N = 10³ 10⁴ 10⁵ 10⁶; N = 10⁷ takes about eight minutes

The edge law of BallGap (section "The Landau gap from below" of the note). It prints the minimum of A + B over x, the
smallest eigenvalue of K = (log N + c₀ + 1)diag(n) − diag(√n)M diag(√n), by inverse iteration with Jacobi-preconditioned
conjugate gradients (K is a positive definite M-matrix), over √log N and over √(2(c₀ + γ + 1)log N), the profile's
prediction; the ratio to the proved √log N/10 (BallGap.edge_law); and two checks of the proof of BallGap.gap_ge at its
weights K = 2 log N, η = √log N/2, d(m) = √(log²m + 2K) − log m − 2√log N/m: the smallest d(m) over 2 ≤ m ≤ N, which must
be ≥ 0, and the smallest slack of the vertex inequality 5 + κ_j + Σ_{n ≤ N/j}(Λ(n)/n)r(jn) − η/j − d(j)[j ≥ 2] ≥ 0,
r(m) = d(m)/(log m + d(m)).

    python3 scripts/landau_gap.py --silent --zeros-file FILE [N ...]   # default N = 1000 2000; dense, so N ≤ 3000

What silence at the low zeros costs in A + B (the note's last section, "What stays open"): m(T), the smallest
eigenvalue of K on the subspace of x with V_x(ρ) = 0 at every zero 0 < γ ≤ T, for T up to about πN/log N, where the
2·#{γ ≤ T} real constraints approach N. FILE has one ordinate per line, e.g. the first 30000 zeros from
scripts/zeta_zeros_rs.py.
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


def spread(N, c0=math.log(4) + 1):
    """The minimiser of Q_N and the edge vector, the minimiser of A + B = xᵀKx/|x|² with
    K = diag(√n)((log N + c₀ + 1)I − M)diag(√n): see the docstring."""
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from ball_orbit import gram
    L = math.log(N)
    n = np.arange(1, N + 1, dtype=float)
    M = landau_matrix(N).toarray()
    s = np.sqrt(n)
    K = s[:, None] * ((L + c0 + 1) * np.eye(N) - M) * s[None, :]
    G = gram(N)
    wq, vq = np.linalg.eigh(G)
    wk, vk = np.linalg.eigh(K)
    v, e = vq[:, 0], vk[:, 0]
    A = (v ** 2 * n).sum()
    B = (L + c0) * A - (v * s) @ (M @ (v * s))
    return (wq[0] * N / L, A / L, B / L, wk[0] / math.sqrt(L), e[0] ** 2, (e @ G @ e) * N / L,
            wk[:4] / math.sqrt(L))


def edge_min(N, c0=math.log(4) + 1, M=None):
    """min_x (Σx_n² n + G(c))/Σx_n² with c_n = x_n√n, the smallest eigenvalue of K: see the docstring."""
    M = landau_matrix(N) if M is None else M
    L = math.log(N)
    n = np.arange(1, N + 1, dtype=float)
    s = sp.diags(np.sqrt(n))
    dg = (L + c0 + 1) * n
    K = (sp.diags(dg) - s @ M @ s).tocsr()
    pre = sla.LinearOperator((N, N), matvec=lambda y: y / dg, dtype=float)
    x = 1.0 / n
    x /= np.linalg.norm(x)
    lam = x @ (K @ x)
    for _ in range(100):
        y, info = sla.cg(K, x, rtol=1e-12, maxiter=5000, M=pre)
        if info != 0:
            raise RuntimeError(f"conjugate gradients did not converge ({info})")
        x = y / np.linalg.norm(y)
        new = x @ (K @ x)
        if abs(new - lam) < 1e-11 * new:
            return new
        lam = new
    return lam


def vertex_check(N, c0=math.log(4) + 1):
    """The smallest d(m) over 2 ≤ m ≤ N and the smallest slack of BallGap's vertex inequality: see the docstring."""
    lam = mangoldt(N)
    L = math.log(N)
    K, sL = 2 * L, math.sqrt(L)
    n = np.arange(N + 1, dtype=float)
    n[0] = 1
    psi1 = np.cumsum(lam / n)
    u = np.log(n)
    d = np.sqrt(u ** 2 + 2 * K) - u - 2 * sL / n
    r = np.zeros(N + 1)
    r[2:] = d[2:] / (u[2:] + d[2:])
    child = np.zeros(N + 1)
    for q in np.nonzero(lam)[0]:
        q = int(q)
        j = np.arange(1, N // q + 1)
        child[j] += lam[q] / q * r[j * q]
    j = np.arange(1, N + 1)
    kappa = L + c0 - psi1[N // j] - np.log(j)
    slack = 5 + kappa + child[1:] - sL / 2 / j - np.where(j >= 2, d[1:], 0.0)
    return d[2:].min(), slack.min()


def silent_cost(N, zeros, c0=math.log(4) + 1):
    """m(T) = min of A + B over the x with V_x(ρ) = 0 at every zero 0 < γ ≤ T: see the docstring."""
    L = math.log(N)
    n = np.arange(1, N + 1, dtype=float)
    s = np.sqrt(n)
    K = s[:, None] * ((L + c0 + 1) * np.eye(N) - landau_matrix(N).toarray()) * s[None, :]
    out = [(0, 0, np.linalg.eigvalsh(K)[0])]
    tmax = math.pi * N / L
    for T in [15, 22, 33, 50, 75, 110, 170, 250, 380, 560, 840, 1260]:
        if T >= 0.95 * tmax:
            break
        g = zeros[zeros <= T]
        C = np.vstack([np.cos(np.outer(g, np.log(n))), np.sin(np.outer(g, np.log(n)))]) * s
        _, sv, vt = np.linalg.svd(C, full_matrices=True)
        r = int(np.sum(sv > sv[0] * 1e-10))
        B = vt[r:].T
        out.append((T, len(g), np.linalg.eigvalsh(B.T @ K @ B)[0]))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("N", nargs="*", type=int)
    ap.add_argument("--c0", nargs="*", type=float, default=[0.0, math.log(4) + 1])
    ap.add_argument("--spread", action="store_true", help="the vectors that BallSharp.rate_slack leaves")
    ap.add_argument("--gap", action="store_true", help="the edge law of BallGap, and checks of its proof")
    ap.add_argument("--silent", action="store_true", help="what silence at the low zeros costs in A + B")
    ap.add_argument("--zeros-file", default=None, help="ordinates of the zeros, one per line (for --silent)")
    args = ap.parse_args()
    if args.silent:
        if not args.zeros_file:
            ap.error("--silent needs --zeros-file")
        zeros = np.asarray(np.loadtxt(args.zeros_file), float).ravel()
        for N in args.N or [1000, 2000]:
            L = math.log(N)
            rows = silent_cost(N, zeros)
            print(f"N = {N}: min(A + B) = {rows[0][2]:.3f} = {rows[0][2] / math.sqrt(L):.2f}·√log N; "
                  f"m(T) at zeros up to T:")
            for T, k, m in rows[1:]:
                print(f"   T = {T:5d} ({k:4d} zeros): m(T) = {m:7.3f} = {m / math.sqrt(L):.2f}·√log N "
                      f"= {m / L:.3f}·log N", flush=True)
        return
    if args.gap:
        c0 = math.log(4) + 1
        print(f"{'N':>9} {'min(A+B)/√logN':>15} {'/√(2(c0+γ+1)logN)':>19} {'/(√logN/10)':>12} "
              f"{'min d(m)':>9} {'min vertex slack':>17} {'s':>5}")
        for N in args.N or [1000, 10000, 100000, 1000000]:
            t = time.time()
            L = math.log(N)
            e = edge_min(N, c0)
            dmin, smin = vertex_check(N, c0)
            print(f"{N:9d} {e / math.sqrt(L):15.4f} {e / math.sqrt(2 * (c0 + GAMMA + 1) * L):19.4f} "
                  f"{e / (math.sqrt(L) / 10):12.1f} {dmin:9.3f} {smin:17.3f} {time.time() - t:5.0f}", flush=True)
        return
    if args.spread:
        print(f"{'N':>5} {'λ_N·N/log N':>12} | minimiser {'A/log N':>8} {'B/log N':>8} | edge vector "
              f"{'(A+B)/√log N':>12} {'x₁²':>5} {'Q_N·N/log N':>11} | eigenvalues of A + B over √log N")
        for N in args.N or [250, 500, 1000, 2000]:
            lam, a, b, edge, x1, qe, ev = spread(N)
            print(f"{N:5d} {lam:12.4f} | {a:18.3f} {b:8.3f} | {edge:24.3f} {x1:5.3f} {qe:11.2f} | "
                  + " ".join(f"{t:.2f}" for t in ev), flush=True)
        return
    args.N = args.N or [1000, 10000, 100000, 1000000]
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
