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

    python3 scripts/landau_gap.py --silent --zeros-file FILE [--fence] [--tmax T] [N ...]   # default N = 1000 2000

What silence costs in A + B (the note's last section, "What stays open"): m(T), the smallest eigenvalue of K on the
subspace of x with V_x(ρ) = 0 at every zero 0 < γ ≤ T, for T on a grid up to --tmax (default 2N). A direction counts as
silent below 1e-7 of the top singular value of the 2·#{γ ≤ T} conditions, since the ordinates carry nine decimals; m at
1e-5 is printed beside it, and a row where the two part by more than 10% is flagged. Each row also gives the spread A of
the minimiser, and the numerical rank of the conditions against the count (T/π)(1 + log(πN/T)). First comes the zeta
vector x_n = w(n/N)/n, w = 1 on [0, ½] and 0 past 1: its A + B, and its rms |V_x(ρ)|/‖x‖ by height. --fence repeats
everything with the picket fence, the k-th point at Φ(t) = (t/2π)log(t/2πe) + 7/8 = k − ½, in place of the zeros. FILE
has one ordinate per line, e.g. the first 30000 zeros from scripts/zeta_zeros_rs.py. N = 1000 and 2000 with --fence
take about a minute and a half, N = 4000 about eight minutes, N = 8000 with --tmax 2800 about half an hour.

    python3 scripts/landau_gap.py --split --zeros-file FILE [N ...]      # default N = 1000 2000; N = 4000 about a minute

Where the cheap silence lives (same section). At T = N/2 and N: the lowest eigenvalues of K on the silent space as in
--silent, at the zeros and at the picket fence; the zeros' eigenvalues ⌊2πN/T⌋ + 1 to ⌊2πN/T⌋ + 4 over the fence's
first four; and the lowest eigenvalue at the zeros on the part of the silent space that
is K-orthogonal to the dilates of the zeta vector, Y_D = span{[d | n]B_j(n/N)/n : d ≤ D, j ≤ 12}, B_j the cubic
B-splines on [0, 1] with uniform knots, for D = 1 and ⌊2πN/T⌋ − 2, …, ⌊2πN/T⌋ + 2.

    python3 scripts/landau_gap.py --quiet --zeros-file FILE [N ...]      # default N = 1000 2000; N = 4000 under a minute

Quiet in place of silent (same section): for μ = 2^(k/2), k = 6..21, the minimiser of A + B + μ(N/log N)·Q_≤N(x) over
unit x, where Q_≤N(x) = Σ_{0 < γ ≤ N} 2|V_x(ρ)|²/(¼ + γ²) is the zeta form cut at height N. It prints the frontier, and
A + B at fixed quietness Q_≤N·N/log N = ε for ε = 0.02, 0.01, 0.005, 0.002, interpolated linearly in log ε.
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


def fence_points(tmax):
    """The picket fence: the k-th point at Φ(t) = (t/2π)log(t/2πe) + 7/8 = k − ½, up to height tmax."""
    from scipy.special import lambertw
    k = np.arange(1, int(tmax * math.log(tmax) / (2 * math.pi)) + 2, dtype=float)
    t = 2 * math.pi * math.e * np.exp(np.real(lambertw((k - 0.5 - 7 / 8) / math.e)))
    return t[t <= tmax]


def smooth_step(u, a=0.5):
    """1 on [0, a], 0 on [1, ∞), C^∞ in between."""
    t = np.clip((u - a) / (1 - a), 0.0, 1.0)
    f = lambda v: np.where(v > 0, np.exp(-1 / np.maximum(v, 1e-300)), 0.0)  # noqa: E731
    return f(1 - t) / (f(1 - t) + f(t))


def silent_cost(N, pts, tmax=None, c0=math.log(4) + 1):
    """Yields min(A + B), then (A + B, rms of |V_x|/‖x‖ by height) for the zeta vector, then per height T
    (T, #points, rank, m(T) at threshold 1e-7, m(T) at 1e-5, the spread A of the minimiser): see the docstring."""
    L = math.log(N)
    n = np.arange(1, N + 1, dtype=float)
    s, lg = np.sqrt(n), np.log(n)
    K = s[:, None] * ((L + c0 + 1) * np.eye(N) - landau_matrix(N).toarray()) * s[None, :]
    yield np.linalg.eigvalsh(K)[0]
    x = smooth_step(n / N) / n
    g = pts[pts <= 2 * N]
    V = np.concatenate([np.abs((np.exp(1j * np.outer(g[i:i + 2048], lg)) * s) @ x)
                        for i in range(0, len(g), 2048)]) / np.linalg.norm(x)
    yield x @ K @ x / (x @ x), [(lo, hi, np.sqrt(np.mean(V[(g > lo) & (g <= hi)] ** 2)))
                                for lo, hi in [(0, 30), (30, 100), (100, 300), (300, 2 * N)]]
    for T in [15, 22, 33, 50, 75, 110, 170, 250, 350, 500, 700, 1000, 1400, 2000, 2800, 4000, 5600, 8000,
              11000, 16000]:
        if T > (tmax or 2 * N):
            return
        g = pts[pts <= T]
        C = np.vstack([np.cos(np.outer(g, lg)), np.sin(np.outer(g, lg))]) * s
        _, sv, vt = np.linalg.svd(C, full_matrices=C.shape[0] < N)
        # The ordinates carry 9 decimals, so C is known to about 1e-9·log N of its norm: directions below 1e-7 of
        # the top singular value count as silent.  The value at 1e-5 is the check: where the two part by more
        # than 10%, the conditions are too nearly dependent to say exactly what silence costs.
        out = [T, len(g)]
        for tol in (1e-7, 1e-5):
            r = int(np.sum(sv > sv[0] * tol))
            w, U = np.linalg.eigh(vt[r:] @ K @ vt[r:].T)
            if tol == 1e-7:
                y = vt[r:].T @ U[:, 0]
                out += [r, w[0]]
            else:
                out += [w[0], float(y * y @ n / (y @ y))]
        yield tuple(out)


def split_cost(N, zeros, T, Ds, J=12, c0=math.log(4) + 1):
    """A + B on the silent space up to T, at the zeros and at the fence, and at the zeros off the dilates d ≤ D."""
    from scipy.interpolate import BSpline
    L = math.log(N)
    n = np.arange(1, N + 1, dtype=float)
    s, lg = np.sqrt(n), np.log(n)
    K = s[:, None] * ((L + c0 + 1) * np.eye(N) - landau_matrix(N).toarray()) * s[None, :]

    def silent(pts):
        g = pts[pts <= T]
        C = np.vstack([np.cos(np.outer(g, lg)), np.sin(np.outer(g, lg))]) * s
        _, sv, vt = np.linalg.svd(C, full_matrices=C.shape[0] < N)
        return vt[int(np.sum(sv > sv[0] * 1e-7)):].T

    B, F = silent(zeros), silent(fence_points(T))
    evz, evf = np.linalg.eigvalsh(B.T @ K @ B), np.linalg.eigvalsh(F.T @ K @ F)
    knots = np.concatenate([[0, 0, 0], np.linspace(0, 1, J - 2), [1, 1, 1]])
    spl = np.stack([BSpline(knots, np.eye(J)[j], 3)(n / N) for j in range(J)], 1)
    off = []
    for D in Ds:
        Y = np.concatenate([((np.arange(1, N + 1) % d == 0) / n)[:, None] * spl for d in range(1, D + 1)], 1)
        _, sm, wt = np.linalg.svd(Y.T @ K @ B, full_matrices=True)
        Zb = B @ wt[int(np.sum(sm > sm[0] * 1e-10)):].T
        off.append((D, np.linalg.eigvalsh(Zb.T @ K @ Zb)[0]))
    return evz, evf, off


def quiet_cost(N, zeros, c=1.0, c0=math.log(4) + 1):
    """Quiet in place of silent: the frontier between A + B and Q_{≤cN}, and A + B at fixed ε (see the docstring)."""
    from scipy.linalg import eigh
    L = math.log(N)
    n = np.arange(1, N + 1, dtype=float)
    s, lg = np.sqrt(n), np.log(n)
    K = s[:, None] * ((L + c0 + 1) * np.eye(N) - landau_matrix(N).toarray()) * s[None, :]
    g = zeros[zeros <= c * N]
    W = np.zeros((N, N))
    for i in range(0, len(g), 2048):
        gg = g[i:i + 2048]
        w = 2 / (0.25 + gg * gg)
        for f in (np.cos, np.sin):
            F = f(np.outer(gg, lg)) * s
            W += (F * w[:, None]).T @ F
    rows = []
    for k in range(6, 22):
        mu = 2 ** (k / 2)
        x = eigh(K + mu * N / L * W, subset_by_index=[0, 0])[1][:, 0]
        rows.append((mu, x @ K @ x, x @ W @ x * N / L))
    fixed = []
    for eps in (0.02, 0.01, 0.005, 0.002):
        for (_, a1, q1), (_, a2, q2) in zip(rows, rows[1:]):
            if q2 <= eps <= q1:
                fixed.append((eps, a1 + math.log(q1 / eps) / math.log(q1 / q2) * (a2 - a1)))
    return rows, fixed


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("N", nargs="*", type=int)
    ap.add_argument("--c0", nargs="*", type=float, default=[0.0, math.log(4) + 1])
    ap.add_argument("--spread", action="store_true", help="the vectors that BallSharp.rate_slack leaves")
    ap.add_argument("--gap", action="store_true", help="the edge law of BallGap, and checks of its proof")
    ap.add_argument("--silent", action="store_true", help="what silence at the zeros up to height 2N costs in A + B")
    ap.add_argument("--zeros-file", default=None, help="ordinates of the zeros, one per line (for --silent, --split, --quiet)")
    ap.add_argument("--fence", action="store_true", help="with --silent: the picket fence as well")
    ap.add_argument("--quiet", action="store_true", help="quiet in place of silent: A + B against Q at the zeros ≤ N")
    ap.add_argument("--split", action="store_true", help="silence at the zeros off the span of the dilates of ζ")
    ap.add_argument("--tmax", type=float, default=None, help="with --silent: the top height (default 2N)")
    args = ap.parse_args()
    if args.split:
        if not args.zeros_file:
            ap.error("--split needs --zeros-file")
        zeros = np.asarray(np.loadtxt(args.zeros_file), float).ravel()
        for N in args.N or [1000, 2000]:
            for T in (N // 2, N):
                d0 = int(2 * math.pi * N / T)
                evz, evf, off = split_cost(N, zeros, T, sorted({1} | set(range(max(1, d0 - 2), d0 + 3))))
                print(f"N = {N}, T = {T}, 2πN/T = {2 * math.pi * N / T:.2f}: A + B on the silent space, lowest "
                      f"eigenvalues\n   zeros (dimension {len(evz)}): " + " ".join(f"{e:.1f}" for e in evz[:d0 + 4])
                      + f"\n   fence (dimension {len(evf)}): " + " ".join(f"{e:.1f}" for e in evf[:4])
                      + f"\n   the zeros' eigenvalues {d0 + 1} to {d0 + 4} over the fence's first four: "
                      + " ".join(f"{a / b:.3f}" for a, b in zip(evz[d0:d0 + 4], evf))
                      + "\n   the lowest at the zeros K-orthogonal to the dilates d ≤ D, 12 B-splines each: "
                      + ", ".join(f"D = {D}: {m:.1f}" for D, m in off)
                      + f"; (T/π)log N = {T / math.pi * math.log(N):.0f}", flush=True)
        return
    if args.quiet:
        if not args.zeros_file:
            ap.error("--quiet needs --zeros-file")
        zeros = np.asarray(np.loadtxt(args.zeros_file), float).ravel()
        for N in args.N or [1000, 2000]:
            L = math.log(N)
            rows, fixed = quiet_cost(N, zeros)
            print(f"N = {N}: the frontier (μ: A + B, Q_≤N·N/log N): "
                  + "; ".join(f"{mu:.0f}: {ab:.3f}, {q:.5f}" for mu, ab, q in rows))
            print("   A + B at Q_≤N·N/log N = ε: " + "; ".join(
                f"ε = {eps}: {ab:.3f} = {ab / L:.4f}·log N = {ab / math.sqrt(L):.3f}·√log N" for eps, ab in fixed),
                flush=True)
        return
    if args.silent:
        if not args.zeros_file:
            ap.error("--silent needs --zeros-file")
        zeros = np.asarray(np.loadtxt(args.zeros_file), float).ravel()
        for N in args.N or [1000, 2000]:
            L = math.log(N)
            sets = [("zeros", zeros)] + ([("picket fence", fence_points(2 * N))] if args.fence else [])
            for name, pts in sets:
                rows = silent_cost(N, pts, args.tmax)
                m0 = next(rows)
                ab, win = next(rows)
                print(f"N = {N}, {name}: min(A + B) = {m0:.3f} = {m0 / math.sqrt(L):.2f}·√log N. The zeta vector "
                      f"x_n = w(n/N)/n has A + B = {ab / L:.2f}·log N and rms |V_x|/‖x‖ "
                      + ", ".join(f"{v:.0e} on ({lo}, {hi}]" for lo, hi, v in win) + ". m(T) at the points up to T:")
                for T, k, r, m, m5, A in rows:
                    count = T / math.pi * (1 + math.log(math.pi * N / T))
                    flag = "  <- the thresholds part by more than 10%" if abs(m - m5) > 0.1 * m else ""
                    print(f"   T = {T:5d}: m = {m:9.3f} [{m5:9.3f} at 1e-5] = {m / math.sqrt(L):7.2f}·√log N "
                          f"= {m / L:7.3f}·log N, spread A = {A:7.1f}; rank {r:5d} of {2 * k:5d} conditions, "
                          f"count (T/π)(1 + log(πN/T)) = {count:6.0f}{flag}", flush=True)
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
