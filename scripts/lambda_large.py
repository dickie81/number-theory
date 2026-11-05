#!/usr/bin/env python3
"""λ_N to N = 3·10⁴, the (A+B, Q) frontier, and the low modes of A + B (formalisations/ball-rate.md, section
"The low zeros"). Uncertified numerics.

    python3 scripts/lambda_large.py [N ...]               # default N = 1000 2000 4000 8000; needs numpy, scipy
    python3 scripts/lambda_large.py --frontier [N ...]    # default N = 2000 8000
    python3 scripts/lambda_large.py --modes [N ...]       # default N = 10000 100000; also needs mpmath

The orbit form Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn) K_H(m/n) is built from the primes as in scripts/ball_orbit.py, in
column blocks into one Fortran-ordered array, and factored in place by Cholesky. Block inverse iteration with
Rayleigh–Ritz then gives the bottom of the spectrum. N = 3·10⁴ needs 7.2 GB and about ten minutes. OpenBLAS's
multithreaded Cholesky crashed above N ≈ 2·10⁴ where this was run, so the script runs it single-threaded.

Default mode: λ_N·N/log N, the ratios λ₂/λ₁ and λ₃/λ₁, and at the minimiser the spread A = Σx_n² n/Σx_n² and Landau's
slack B = G(c)/Σx_n², c_n = x_n√n, G(c) = (log N + log 4 + 1)Σc_n² − L(c) (BallSharp.landauSlack), over log N. With
three N or more it fits λ_N·N by a·log N + b and by a·√log N + b and prints the largest residual of each.

--frontier: for μ = s·log N/N with s = 0, 0.01, 0.1, 1, 10, 100, the minimiser of Q_N + μ(A + B)Σx_n²: Q_N·N/log N,
(A + B)/log N, A/log N and Q_N·(A + B)·N/log²N, against the floor min(A + B) = 2.9√log N.

--modes: the eight lowest eigenvectors of A + B, by LOBPCG on the sparse matrix (log N + log 4 + 2)diag(n) −
diag(√n)M diag(√n) (M the matrix of Landau's form). For each, where it sits, its eigenvalue over k√log N, its values
|V_x(ρ)| at the first three zeros, and the fit V_x(ρ) ≈ αN^ρ/ρ on the first six (|α|√N and the relative residual).
Then the smallest eigenvalue of Σ_{j ≤ J} 2|V_x(ρ_j)|²/(¼ + γ_j²) on the span of the first d modes, against log N/N.
"""
import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import argparse  # noqa: E402
import math  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402

import numpy as np  # noqa: E402
import scipy.linalg as sl  # noqa: E402
import scipy.sparse as sp  # noqa: E402
import scipy.sparse.linalg as sla  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ball_orbit import kernel_over_sqrt, tables  # noqa: E402
from landau_gap import landau_matrix  # noqa: E402

C0 = math.log(4) + 1


def gram(N, extra=None, block=512):
    """The Gram matrix of Q_N, Fortran-ordered (it is symmetric), plus extra = (μ, K) if given."""
    A, B = tables(N + 1)
    G = np.empty((N, N), order="F")
    m = np.arange(1, N + 1, dtype=float)
    for c0 in range(0, N, block):
        c1 = min(N, c0 + block)
        cols = m[c0:c1][None, :]
        hi, lo = np.maximum(m[:, None], cols), np.minimum(m[:, None], cols)
        G[:, c0:c1] = hi * kernel_over_sqrt(hi / lo, A, B)
    if extra is not None:
        mu, K = extra
        Kc = K.tocoo()
        np.add.at(G, (Kc.row, Kc.col), mu * Kc.data)
    return G


def spread_slack(N):
    """A + B as a quadratic form in x: (log N + c₀ + 1)diag(n) − diag(√n)M diag(√n), sparse."""
    L = math.log(N)
    n = np.arange(1, N + 1, dtype=float)
    s = sp.diags(np.sqrt(n))
    return (sp.diags((L + C0 + 1) * n) - s @ landau_matrix(N) @ s).tocsr()


def bottom(Lf, N, k=4, tol=1e-11, maxit=200):
    """The bottom k eigenpairs of Lf·Lfᵀ by block inverse iteration with Rayleigh–Ritz."""
    n = np.arange(1, N + 1, dtype=float)
    X = np.random.default_rng(0).standard_normal((N, k)) / n[:, None]
    X[:, 0] = 1.0 / n
    prev = None
    for _ in range(maxit):
        Y = sl.solve_triangular(Lf, X, lower=True, check_finite=False)
        Y = sl.solve_triangular(Lf, Y, lower=True, trans="T", check_finite=False)
        Y, _ = np.linalg.qr(Y)
        W = sl.blas.dtrmm(1.0, Lf, Y, lower=1, trans_a=1)
        w, U = np.linalg.eigh(W.T @ W)
        X = Y @ U
        if prev is not None and np.max(np.abs(w - prev) / w) < tol:
            break
        prev = w
    return w, X


def lambda_mode(Ns):
    print(f"{'N':>6} {'λ_N·N/log N':>12} {'λ_N·N':>8} {'λ₂/λ₁':>6} {'λ₃/λ₁':>6} {'A/log N':>8} {'B/log N':>8} "
          f"{'(A+B)/log N':>11} {'s':>5}")
    rows = []
    for N in Ns:
        t = time.time()
        L = math.log(N)
        Lf = sl.cholesky(gram(N), lower=True, overwrite_a=True, check_finite=False)
        w, X = bottom(Lf, N)
        del Lf
        x = X[:, 0] / np.linalg.norm(X[:, 0])
        n = np.arange(1, N + 1, dtype=float)
        A, K = x @ (n * x), x @ (spread_slack(N) @ x)
        rows.append((N, w[0] * N))
        print(f"{N:6d} {w[0] * N / L:12.5f} {w[0] * N:8.4f} {w[1] / w[0]:6.3f} {w[2] / w[0]:6.3f} {A / L:8.3f} "
              f"{(K - A) / L:8.3f} {K / L:11.3f} {time.time() - t:5.0f}", flush=True)
    if len(rows) >= 3:
        L = np.log([r[0] for r in rows])
        y = np.array([r[1] for r in rows])
        for name, f in [("a·log N + b", L), ("a·√log N + b", np.sqrt(L))]:
            X = np.vstack([f, np.ones_like(f)]).T
            coef, *_ = np.linalg.lstsq(X, y, rcond=None)
            print(f"  λ_N·N ≈ {name}: a = {coef[0]:.5f}, b = {coef[1]:+.4f}, "
                  f"largest residual {np.max(np.abs(X @ coef - y)):.1e}")


def frontier_mode(Ns):
    for N in Ns:
        L = math.log(N)
        n = np.arange(1, N + 1, dtype=float)
        K = spread_slack(N)
        dg = (L + C0 + 1) * n
        pre = sla.LinearOperator((N, N), matvec=lambda y: (y.T / dg).T if y.ndim > 1 else y / dg, dtype=float)
        X0 = np.zeros((N, 1))
        X0[0, 0] = 1.0
        wk, _ = sla.lobpcg(K, X0 + 1e-3 / n[:, None], M=pre, largest=False, tol=1e-10, maxiter=2000)
        print(f"N = {N}: the floor min(A + B) = {wk[0] / L:.3f}·log N = {wk[0] / math.sqrt(L):.3f}·√log N")
        print(f"   {'μ·N/log N':>9} {'Q·N/log N':>10} {'(A+B)/log N':>11} {'A/log N':>8} {'Q(A+B)N/log²N':>14}")
        for s in [0.0, 0.01, 0.1, 1.0, 10.0, 100.0]:
            mu = s * L / N
            Lf = sl.cholesky(gram(N, extra=(mu, K) if mu > 0 else None), lower=True, overwrite_a=True,
                             check_finite=False)
            w, X = bottom(Lf, N, k=2)
            del Lf
            x = X[:, 0] / np.linalg.norm(X[:, 0])
            Kx, A = x @ (K @ x), x @ (n * x)
            Q = w[0] - mu * Kx
            print(f"   {s:9.2f} {Q * N / L:10.4f} {Kx / L:11.3f} {A / L:8.3f} {Q * Kx * N / L ** 2:14.4f}", flush=True)


def modes_mode(Ns):
    import mpmath
    mpmath.mp.dps = 20
    Z = np.array([float(mpmath.zetazero(j).imag) for j in range(1, 101)])

    def values(x, N, gammas):
        n = np.arange(1, N + 1, dtype=float)
        ln, w = np.log(n), x * np.sqrt(n)
        return np.array([np.dot(w, np.exp(1j * g * ln)) for g in gammas])

    for N in Ns:
        L = math.log(N)
        n = np.arange(1, N + 1, dtype=float)
        K = spread_slack(N)
        dg = (L + C0 + 1) * n
        pre = sla.LinearOperator((N, N), matvec=lambda y: (y.T / dg).T if y.ndim > 1 else y / dg, dtype=float)
        X0 = np.zeros((N, 8))
        for i in range(8):
            X0[i, i] = 1.0
            X0[:, i] += 1e-3 * np.random.default_rng(i).standard_normal(N) / n
        w, V = sla.lobpcg(K, X0, M=pre, largest=False, tol=1e-9, maxiter=2000)
        order = np.argsort(w)
        w, V = w[order], V[:, order]
        print(f"N = {N}:")
        print(f"   {'k':>2} {'sits at':>8} {'mass':>5} {'λ/(k√log N)':>11} {'|V(ρ₁)| |V(ρ₂)| |V(ρ₃)|':>24} "
              f"{'|α|√N':>7} {'residual':>8}")
        pred = np.array([N ** (0.5 + 1j * g) / (0.5 + 1j * g) for g in Z[:6]])
        for i in range(8):
            x = V[:, i] / np.linalg.norm(V[:, i])
            top = np.argsort(-np.abs(x))[:4] + 1
            vals = values(x, N, Z[:6])
            alpha = np.vdot(pred, vals) / np.vdot(pred, pred)
            rel = np.linalg.norm(vals - alpha * pred) / np.linalg.norm(vals)
            print(f"   {i + 1:2d} {top[0]:8d} {(x[top - 1] ** 2).sum():5.3f} {w[i] / (math.sqrt(L) * (i + 1)):11.3f} "
                  f"{abs(vals[0]):8.3f} {abs(vals[1]):7.3f} {abs(vals[2]):7.3f} {abs(alpha) * math.sqrt(N):7.2f} "
                  f"{rel:8.3f}", flush=True)
        print(f"   the form of the first J zeros on the span of the first d modes, smallest eigenvalue "
              f"(log N/N = {L / N:.2e}):")
        for d in [1, 2, 4, 8]:
            Qd, _ = np.linalg.qr(V[:, :d])
            row = []
            for J in [1, 3, 10, 30, 100]:
                Amat = np.array([values(Qd[:, i], N, Z[:J]) for i in range(d)]).T
                F = (Amat.conj().T * (2.0 / (0.25 + Z[:J] ** 2))) @ Amat
                row.append(max(np.linalg.eigvalsh(F.real)[0], 0.0))
            print(f"   d = {d}: " + "  ".join(f"J={J}: {v:.1e}" for J, v in zip([1, 3, 10, 30, 100], row)), flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("N", nargs="*", type=int)
    ap.add_argument("--frontier", action="store_true", help="the (A+B, Q) frontier")
    ap.add_argument("--modes", action="store_true", help="the low modes of A + B at the first zeros")
    args = ap.parse_args()
    if args.frontier:
        frontier_mode(args.N or [2000, 8000])
    elif args.modes:
        modes_mode(args.N or [10000, 100000])
    else:
        lambda_mode(args.N or [1000, 2000, 4000, 8000])


if __name__ == "__main__":
    main()
