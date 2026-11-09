#!/usr/bin/env python3
"""Which zeros hear the cheap vectors, and how those vectors are quiet (formalisations/ball-rate.md, section "Which zeros
hear the cheap vectors"). Uncertified numerics.

    python3 scripts/lambda_heard.py --zeros-file FILE [--zeros-file FILE2] [--bands | --turnon | --dilates] [N ...]

FILE has one ordinate per line, e.g. the first 30000 zeros from scripts/zeta_zeros_rs.py. With two files, the first one's
ordinates replace the first ones of the second (e.g. the first 2000 from mpmath, which are more accurate at low height).
Default N = 1000 2000 4000; N = 4000 takes a few minutes per mode. The Gram matrix of Q_N is the exact one, built from the
primes (scripts/lambda_large.py); the zeros are used only to split it by height.

Default mode, the flattened weight. Replace the weight 1/(¼ + γ²) of the zeros below a height T₀ by its value at T₀. A
test function of the explicit formula whose Fourier transform is supported in [−δ, δ] cannot resolve heights below about
1/δ, so the bottom λ(T₀) of the flattened form is about what such a test function can certify, with T₀ ≈ 1/δ. Prints
λ_N·N/log N, λ(T₀)·N/log N for T₀/N = 4, 2, 1, ½, ¼, and at T₀ = 4N the flattened quotient of the edge vector (the
bottom of A + B, the vector that caps the band-limited route at √log N/N) and its ratio to λ(4N).

    --bands: for μ = s·log N/N, s = 0, 0.01, 0.1, 1, 10, the minimiser of Q_N + μ(A + B)Σx² (lambda_large.py --frontier):
Q·N/log N, (A + B)/log N, A/log N, x₁², and the percentage of its Q_N from the zeros in the height bands [0, 50],
(50, √N], (√N, N/log N], (N/log N, N/4], (N/4, N], (N, 4N] and above 4N (the last as Q_N minus the others).

    --turnon: for s = 10 and 1, the mean of |V_x(ρ)|² (unit x) over the zeros in the bands (√N·2^{j−1}, √N·2^j],
j = −3, …, 5: where the near-floor vectors turn loud.

    --dilates: for s = 10, 1 and 0, α = μ ∗ f with f_m = m·x_m (so f = 1 ∗ α and F = ζ·M with M = Σ α_d d^{−s}): the
percentage of Σ α_d²/d in each dyadic block of d (d = 1, 2–3, 4–7, …), and the D below which 90% of it lies among
d ≤ N/8.

    --sieve: at N = 4000 (or the given N), the sieve vectors f = (1 ∗ λ − c)·(1 − m/N)², x_m = f_m/m, with Selberg's
weights λ_d = μ(d)log(z/d)/log z on d ≤ z and c = Σ λ_d/d, which removes the boundary term N^{1−ρ}/(1 − ρ), for
z = 10, 30, 100, 300: x₁², A/log N against 1/log z, Q_N·N/log N, and the mean of |V_x(ρ)|² over the zeros in the
height bands (10, 50], (50, 100], (100, 200], …, (6400, 12800].
"""
import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import argparse  # noqa: E402
import math  # noqa: E402
import sys  # noqa: E402

import numpy as np  # noqa: E402
import scipy.linalg as sl  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lambda_large import gram, spread_slack  # noqa: E402


def load_zeros(files):
    z = np.asarray(np.loadtxt(files[-1]), float).ravel()
    for f in reversed(files[:-1]):
        lo = np.asarray(np.loadtxt(f), float).ravel()
        z = np.concatenate([lo, z[len(lo):]])
    return z


def w(t):
    return 1.0 / (0.25 + t * t)


def bottom(M):
    _, X = sl.eigh(M, subset_by_index=[0, 0])
    x = X[:, 0] / np.linalg.norm(X[:, 0])
    return x if x[0] >= 0 else -x


def frontier(G, K, N, s):
    return bottom(G + (s * math.log(N) / N) * K if s > 0 else G)


def band_q(x, N, zeros, a, b):
    """Σ_{a < γ ≤ b} 2|V_x(ρ)|²/(¼ + γ²) and the number of zeros in the band."""
    n = np.arange(1, N + 1, dtype=float)
    ln, c = np.log(n), x * np.sqrt(n)
    g = zeros[(zeros > a) & (zeros <= b)]
    tot = 0.0
    for c0 in range(0, len(g), 1024):
        gg = g[c0:c0 + 1024]
        V = c @ np.exp(1j * np.outer(ln, gg))
        tot += float(np.sum(2.0 * np.abs(V) ** 2 * w(gg)))
    return tot, g


def flattened(G, N, zeros, T0):
    """The Gram matrix with the weight of the zeros below T0 flattened to its value at T0."""
    n = np.arange(1, N + 1, dtype=float)
    ln, sq = np.log(n), np.sqrt(n)
    g = zeros[zeros < T0]
    Gt = np.array(G, order="F")
    for c0 in range(0, len(g), 256):
        gg = g[c0:c0 + 256]
        ph = np.outer(ln, gg)
        U, V = sq[:, None] * np.cos(ph), sq[:, None] * np.sin(ph)
        d = 2.0 * (w(gg) - w(T0))
        Gt -= (U * d) @ U.T + (V * d) @ V.T
    return Gt


def flatten_mode(Ns, zeros):
    for N in Ns:
        if 4 * N > zeros[-1]:
            sys.exit(f"N = {N} needs the zeros up to height {4 * N}; the file reaches {zeros[-1]:.0f}")
        L = math.log(N)
        G = gram(N)
        lam = float(sl.eigh(G, eigvals_only=True, subset_by_index=[0, 0])[0])
        row = []
        for r in [4, 2, 1, 0.5, 0.25]:
            Gt = flattened(G, N, zeros, r * N)
            lt = float(sl.eigh(Gt, eigvals_only=True, subset_by_index=[0, 0])[0])
            row.append(lt)
            if r == 4:
                edge = bottom(spread_slack(N).toarray())
                qe = float(edge @ Gt @ edge)
                l4 = lt
            del Gt
        print(f"N = {N}: λ_N·N/log N = {lam * N / L:.4f}; λ(T₀)·N/log N at T₀/N = 4, 2, 1, ½, ¼: "
              + ", ".join(f"{v * N / L:.4f}" for v in row)
              + f"; at T₀ = 4N: λ·N = {l4 * N:.4f}, edge vector Q·N/log N = {qe * N / L:.4f} "
              f"(·N/√log N = {qe * N / math.sqrt(L):.4f}), ratio {qe / l4:.2f}", flush=True)


def bands_mode(Ns, zeros):
    for N in Ns:
        if 4 * N > zeros[-1]:
            sys.exit(f"N = {N} needs the zeros up to height {4 * N}; the file reaches {zeros[-1]:.0f}")
        L = math.log(N)
        n = np.arange(1, N + 1, dtype=float)
        G, K = gram(N), spread_slack(N).toarray()
        edges = [0, 50, math.sqrt(N), N / L, N / 4, N, 4 * N]
        for i in range(1, len(edges)):           # √N < 50 for N < 2500: that band is then empty
            edges[i] = max(edges[i], edges[i - 1])
        print(f"N = {N}: % of Q_N from [0, 50], (50, √N], (√N, N/log N], (N/log N, N/4], (N/4, N], (N, 4N], > 4N",
              flush=True)
        for s in [0.0, 0.01, 0.1, 1.0, 10.0]:
            x = frontier(G, K, N, s)
            Q = float(x @ G @ x)
            parts = [band_q(x, N, zeros, a, b)[0] for a, b in zip(edges[:-1], edges[1:])]
            parts.append(Q - sum(parts))
            print(f"  s = {s:<5g} Q·N/log N = {Q * N / L:7.4f}  (A+B)/log N = {x @ K @ x / L:.3f}  "
                  f"A/log N = {x @ (n * x) / L:.3f}  x₁² = {x[0] ** 2:.3f}  % by band: "
                  + " ".join(f"{100 * p / Q:5.1f}" for p in parts), flush=True)


def turnon_mode(Ns, zeros):
    for s in [10.0, 1.0]:
        print(f"s = {s:g}: mean |V_x(ρ)|² over the zeros in (√N·2^(j−1), √N·2^j], j = −3, …, 5", flush=True)
        for N in Ns:
            G, K = gram(N), spread_slack(N).toarray()
            x = frontier(G, K, N, s)
            r = math.sqrt(N)
            row = []
            for j in range(-3, 6):
                q, g = band_q(x, N, zeros, max(r * 2.0 ** (j - 1), 10.0), r * 2.0 ** j)
                if len(g) == 0:
                    row.append("    – ")
                    continue
                n = np.arange(1, N + 1, dtype=float)
                V = (x * np.sqrt(n)) @ np.exp(1j * np.outer(np.log(n), g))
                row.append(f"{np.mean(np.abs(V) ** 2):6.3f}")
            print(f"  N = {N:5d} (√N = {r:5.1f}, x₁² = {x[0] ** 2:.3f}): " + " ".join(row), flush=True)


def mobius(N):
    mu = np.ones(N + 1, dtype=int)
    mu[0] = 0
    isp = np.ones(N + 1, dtype=bool)
    isp[:2] = False
    for p in range(2, N + 1):
        if isp[p]:
            isp[2 * p::p] = False
            mu[p::p] *= -1
            mu[p * p::p * p] = 0
    return mu


def dilates_mode(Ns):
    for N in Ns:
        L = math.log(N)
        n = np.arange(1, N + 1, dtype=float)
        mu = mobius(N)
        G, K = gram(N), spread_slack(N).toarray()
        print(f"N = {N}: % of Σ α_d²/d by dyadic block of d (1, 2–3, 4–7, …)", flush=True)
        for s in [10.0, 1.0, 0.0]:
            x = frontier(G, K, N, s)
            f = n * x
            alpha = np.zeros(N + 1)
            for e in range(1, N + 1):
                alpha[e::e][:N // e] += f[e - 1] * mu[1:N // e + 1]
            wt = alpha[1:] ** 2 / n
            shares = []
            k = 0
            while 2 ** k <= N:
                shares.append(wt[2 ** k - 1:min(2 ** (k + 1) - 1, N)].sum() / wt.sum())
                k += 1
            low = wt[:N // 8]
            d90 = int(np.searchsorted(np.cumsum(low) / low.sum(), 0.9)) + 1
            print(f"  s = {s:<4g} x₁² = {x[0] ** 2:.3f}  A/log N = {x @ (n * x) / L:.3f}  shares: "
                  + " ".join(f"{100 * v:.0f}" for v in shares) + f"  |  D₉₀ = {d90}", flush=True)


def sieve_mode(Ns, zeros):
    edges = [10, 50, 100, 200, 400, 800, 1600, 3200, 6400, 12800]
    for N in Ns:
        if edges[-1] > zeros[-1]:
            sys.exit(f"--sieve needs the zeros up to height {edges[-1]}; the file reaches {zeros[-1]:.0f}")
        L = math.log(N)
        n = np.arange(1, N + 1, dtype=float)
        mu = mobius(N)
        G = gram(N)
        print(f"N = {N}: mean |V_x(ρ)|² over the zeros in (10, 50], (50, 100], (100, 200], …, (6400, 12800]",
              flush=True)
        for z in [10, 30, 100, 300]:
            d = np.arange(1, z + 1, dtype=float)
            lam = mu[1:z + 1] * np.log(z / d) / math.log(z)
            f = np.zeros(N)
            for k in range(1, z + 1):
                if lam[k - 1] != 0:
                    f[k - 1::k] += lam[k - 1]
            f = (f - float(np.sum(lam / d))) * (1 - n / N) ** 2
            x = f / n
            x /= np.linalg.norm(x)
            row = []
            for a, b in zip(edges[:-1], edges[1:]):
                g = zeros[(zeros > a) & (zeros <= b)]
                V = (x * np.sqrt(n)) @ np.exp(1j * np.outer(np.log(n), g))
                row.append(f"{np.mean(np.abs(V) ** 2):.3f}")
            print(f"  z = {z:3d} (2πN/z = {2 * math.pi * N / z:5.0f}): x₁² = {x[0] ** 2:.3f}  A/log N = "
                  f"{x @ (n * x) / L:.3f} (1/log z = {1 / math.log(z):.3f})  Q·N/log N = {x @ G @ x * N / L:.3f}  "
                  + " ".join(row), flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("N", nargs="*", type=int)
    ap.add_argument("--zeros-file", action="append", default=[], help="ordinates of the zeros, one per line")
    ap.add_argument("--bands", action="store_true", help="the height bands of the frontier vectors' Q_N")
    ap.add_argument("--turnon", action="store_true", help="where the near-floor vectors turn loud")
    ap.add_argument("--dilates", action="store_true", help="α = μ ∗ f for the frontier vectors")
    ap.add_argument("--sieve", action="store_true", help="Selberg's sieve vectors at the zeros")
    args = ap.parse_args()
    Ns = args.N or [1000, 2000, 4000]
    if args.dilates:
        dilates_mode(Ns)
        return
    if not args.zeros_file:
        sys.exit("this mode needs --zeros-file")
    zeros = load_zeros(args.zeros_file)
    if args.sieve:
        sieve_mode(args.N or [4000], zeros)
    elif args.bands:
        bands_mode(Ns, zeros)
    elif args.turnon:
        turnon_mode(Ns, zeros)
    else:
        flatten_mode(Ns, zeros)


if __name__ == "__main__":
    main()
