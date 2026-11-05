#!/usr/bin/env python3
"""The zeros against point sets with their density and no arithmetic, and the shape of the minimiser of Q_N
(formalisations/ball-rate.md, section "Packing: what the zeros allow that a fence does not"). Uncertified numerics.

    python3 scripts/packing.py [N ...]                              # default N = 100 200 400 800 1600; numpy, scipy
    python3 scripts/packing.py --silence --zeros-file FILE [N ...]  # default N = 800 1600
    python3 scripts/packing.py --ground [N ...]                     # default N = 2000 4000 8000

Default mode: the smallest eigenvalue λ_N for the zeros (the prime-side Gram matrix of scripts/lambda_large.py) and for
three point sets with the density Φ'(t) = log(t/2π)/2π of the zeros and no arithmetic, Φ(t) = (t/2π)log(t/2πe) + 7/8:
the picket fence (the k-th point at Φ = k − ½), jittered pickets (the k-th point uniform in Φ ∈ [k − 1, k]) and a
Poisson process of intensity Φ'. For a point set the Gram matrix is √(mn)·(Σ_k 2cos(γ_k u)/(¼ + γ_k²) + tail(u)),
u = log(m/n), with the points explicit up to Γ₀ = Φ⁻¹(K) ≥ 16N and their density beyond. The tail is in closed form at
u = 0 and by three integrations by parts at u ≠ 0, where Γ₀|u| ≥ 16. Moving Γ₀ from 16N to 64N changes λ_N in the
fifth digit at N = 100 and 400. Prints λ_N·√N and λ_N·N/log N, and the slope of log λ_N against log N.

--silence: at the minimiser of each model, the mean of |V_x(γ)|²/Σx_n² n over the points in [T, 2T], for dyadic T: how
far up the minimiser keeps each point set quiet. The zeros come from FILE, one ordinate per line (the first 30000, to
height 25755, cover N ≤ 1600), e.g. the first 2000 from mpmath and the rest from scripts/zeta_zeros_rs.py.

--ground: the minimiser x of Q_N against the ansatz x_n = w(n/N)/ψ(n), ψ(n) = n·Π_{p | n}(1 + 1/p) Dedekind's function:
  - f(n) = n·x_n/x_1 at primes and prime powers against p/(p + 1), and f(mn)/(f(m)f(n)) for coprime m, n;
  - the smallest Rayleigh quotient over w in 16 cubic B-splines on [0, 1] (smooth), and over the staircase
    w(u) = Σ_{k ≤ 1/u} c(ku) with c in 8 or 16 of them, against λ_N;
  - the scatter of f(n)/F(n) in bins of n/N, for F built from f's own values at the prime powers below N/10, and for
    F(n) = n/ψ(n);
  - the local factor: x_n = F(n)w(n/N)/n with F(p^k) = 1 − θ/(p + 1), or 1 − θ/p, for every k ≥ 1, staircase w;
  - twisted staircases Σ_k a(k)c(ku) with a(k) = k/ψ(k), φ(k)/k, μ²(k);
  - the optimal c, recovered from the best staircase vector by Möbius inversion, c(u) = Σ_k μ(k)w(ku), w(1/N) = 1;
  - the four lowest eigenvalues, and with two N or more the fit λ_k·N ≈ a_k log N + b_k (the ladder a_k ≈ k²a_1).

    python3 scripts/packing.py --stair [N ...]                      # default N = 16000 30000

--stair: the best staircase vector of --ground (c in 16 B-splines) at large N, from the Gram matrix in column blocks
without storing it: its quotient·N/log N, to set against λ_N·N/log N from scripts/lambda_large.py.
"""
import os

os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")

import argparse  # noqa: E402
import math  # noqa: E402
import sys  # noqa: E402

import numpy as np  # noqa: E402
from scipy.interpolate import BSpline  # noqa: E402
from scipy.linalg import eigh  # noqa: E402
from scipy.special import lambertw  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lambda_large import gram  # noqa: E402


def Phi(t):
    return t / (2 * math.pi) * np.log(t / (2 * math.pi * math.e)) + 7 / 8


def Phi_inv(a):
    a = np.asarray(a, float) - 7 / 8
    return 2 * math.pi * math.e * np.exp(np.real(lambertw(a / math.e)))


def phi(t):
    """The weight times the density, 2Φ'(t)/(¼ + t²)."""
    return np.log(t / (2 * math.pi)) / math.pi / (0.25 + t * t)


def tail(u, G0):
    """∫_{Γ₀}^∞ φ(t)cos(tu) dt for an array u ≥ 0."""
    out = np.empty_like(u)
    z = u == 0
    L = math.log(G0 / (2 * math.pi))
    out[z] = (L + 1) / (math.pi * G0) - (L + 1 / 3) / (12 * math.pi * G0 ** 3)
    v = u[~z]
    h = 1e-3 * G0
    p0, pp, pm = phi(G0), phi(G0 + h), phi(G0 - h)
    p1, p2 = (pp - pm) / (2 * h), (pp - 2 * p0 + pm) / h ** 2
    s, c = np.sin(G0 * v), np.cos(G0 * v)
    out[~z] = -p0 * s / v - p1 * c / v ** 2 + p2 * s / v ** 3
    return out


def points(model, N, seed=0):
    """The points of the model up to Γ₀ = Φ⁻¹(K), K = ⌈Φ(16N)⌉, and Γ₀."""
    K = int(math.ceil(Phi(16 * N)))
    k = np.arange(1, K + 1, dtype=float)
    rng = np.random.default_rng(seed)
    if model == "picket":
        g = Phi_inv(k - 0.5)
    elif model == "jitter":
        g = Phi_inv(k - 1 + rng.random(K))
    elif model == "poisson":
        g = Phi_inv(np.sort(rng.random(K) * K))
    else:
        raise ValueError(model)
    return g, float(Phi_inv(K))


def gram_points(N, g, G0, chunk=8192):
    lg = np.log(np.arange(1, N + 1, dtype=float))
    w = 2.0 / (0.25 + g * g)
    G = np.zeros((N, N))
    for c0 in range(0, len(g), chunk):
        P = np.outer(lg, g[c0:c0 + chunk])
        C, S = np.cos(P), np.sin(P)
        G += (C * w[c0:c0 + chunk]) @ C.T + (S * w[c0:c0 + chunk]) @ S.T
    G += tail(np.abs(lg[:, None] - lg[None, :]).ravel(), G0).reshape(N, N)
    sq = np.sqrt(np.arange(1, N + 1, dtype=float))
    return G * sq[:, None] * sq[None, :]


def bottom(G):
    w, V = eigh(G, subset_by_index=[0, 0])
    return w[0], V[:, 0] / np.linalg.norm(V[:, 0])


def models_mode(Ns):
    names = ["zeros", "picket", "jitter", "poisson"]
    lam = {m: [] for m in names}
    print(f"{'N':>6} " + " ".join(f"{m + ' λ√N':>13} {'λN/log N':>9}" for m in names))
    for N in Ns:
        row = []
        for m in names:
            if m == "zeros":
                w, _ = bottom(gram(N))
            else:
                g, G0 = points(m, N)
                w, _ = bottom(gram_points(N, g, G0))
            lam[m].append(w)
            row.append(f"{w * math.sqrt(N):13.4f} {w * N / math.log(N):9.4f}")
        print(f"{N:6d} " + " ".join(row), flush=True)
    if len(Ns) >= 2:
        lN = np.log(Ns)
        print("  slope of log λ_N against log N: " + "  ".join(
            f"{m}: {np.polyfit(lN, np.log(lam[m]), 1)[0]:.3f}" for m in names))


def silence_mode(Ns, zeros_file):
    Z = np.asarray(np.loadtxt(zeros_file), float).ravel()

    def profile(x, g, N, Ts):
        n = np.arange(1, N + 1, dtype=float)
        b, lg = x * np.sqrt(n), np.log(n)
        out = []
        for T in Ts:
            s = g[(g >= T) & (g < 2 * T)]
            if len(s) == 0 or 2 * T > g.max():
                out.append(float("nan"))
                continue
            v = np.concatenate([np.abs(np.exp(1j * np.outer(s[i:i + 4096], lg)) @ b) ** 2
                                for i in range(0, len(s), 4096)])
            out.append(v.mean() / (b @ b))
        return out

    for N in Ns:
        Ts = [2.0 ** k for k in range(3, 15)]
        print(f"N = {N} (√N = {math.sqrt(N):.0f}, 2πN = {2 * math.pi * N:.0f}): mean |V_x(γ)|²/Σx_n²n over [T, 2T]")
        print(f"   {'T/N':>22} " + " ".join(f"{T / N:7.3g}" for T in Ts))
        _, x = bottom(gram(N))
        print(f"   {'zeros':>22} " + " ".join(f"{v:7.4f}" for v in profile(x, Z, N, Ts)))
        for m in ["picket", "jitter"]:
            g, G0 = points(m, N)
            _, xm = bottom(gram_points(N, g, G0))
            print(f"   {m:>22} " + " ".join(f"{v:7.4f}" for v in profile(xm, g, N, Ts)))
            if m == "picket":
                print(f"   {'zeros min. at pickets':>22} " + " ".join(f"{v:7.4f}" for v in profile(x, g, N, Ts)))
                print(f"   {'picket min. at zeros':>22} " + " ".join(f"{v:7.4f}" for v in profile(xm, Z, N, Ts)))


def local_factor(N, fp):
    """The multiplicative F with F(p^k) = fp(p) for every k ≥ 1, at n = 1..N."""
    F = np.ones(N + 1)
    comp = np.zeros(N + 1, bool)
    for p in range(2, N + 1):
        if not comp[p]:
            comp[2 * p::p] = True
            F[p::p] *= fp(p)
    return F[1:]


def bspl(J, u, kdeg=3):
    tk = np.concatenate([[0] * kdeg, np.linspace(0, 1, J - kdeg + 1), [1] * kdeg])
    return np.nan_to_num(np.array([BSpline(tk, np.eye(J)[j], kdeg, extrapolate=False)(np.minimum(u, 1 - 1e-12))
                                   for j in range(J)]).T)


def stair(J, u, a=None):
    """The columns Σ_{k ≤ 1/u} a(k)β_j(ku) for the B-splines β_j (a = 1 if not given)."""
    out = np.zeros((len(u), J))
    for k in range(1, int(1 / u.min()) + 2):
        s = k * u <= 1
        if not s.any():
            break
        out[s] += (1.0 if a is None else a[k - 1]) * bspl(J, k * u[s])
    return out


def measured_factor(f, N):
    """F(n) = Π f(q) over the prime powers q ∥ n, with f(q) itself for q ≤ N/10 and p/(p + 1) beyond."""
    spf = np.zeros(N + 1, dtype=np.int64)
    for p in range(2, N + 1):
        if spf[p] == 0:
            spf[p::p] = np.where(spf[p::p] == 0, p, spf[p::p])
    F = np.ones(N)
    for m in range(2, N + 1):
        k, v = m, 1.0
        while k > 1:
            p, q = spf[k], 1
            while k % p == 0:
                k //= p
                q *= p
            v *= f[q - 1] if q <= N // 10 else p / (p + 1)
        F[m - 1] = v
    return F


def ritz(G, Y, rcond=1e-9):
    """The smallest Rayleigh quotient of G on the span of the columns of Y, and its vector."""
    U, sv, _ = np.linalg.svd(Y / np.linalg.norm(Y, axis=0), full_matrices=False)
    Q = U[:, sv > rcond * sv[0]]
    w, V = eigh(Q.T @ (G @ Q))
    return w[0], Q @ V[:, 0]


def ground_mode(Ns):
    ladder = []
    for N in Ns:
        G = gram(N)
        w4, V4 = eigh(G, subset_by_index=[0, 3])
        lam, x = w4[0], V4[:, 0] / np.linalg.norm(V4[:, 0])
        ladder.append((N, w4 * N))
        n = np.arange(1, N + 1, dtype=float)
        u = n / N
        f = n * x / x[0]
        print(f"N = {N}: λ_N·N/log N = {lam * N / math.log(N):.5f}")
        print("   f(p), p/(p + 1): " + " ".join(f"{p}: {f[p - 1]:.3f}/{p / (p + 1):.3f}" for p in [2, 3, 5, 7, 11, 13, 31]))
        print("   f(2^k), k = 1..6: " + " ".join(f"{f[2 ** k - 1]:.3f}" for k in range(1, 7)))
        pairs = [(2, 3), (2, 5), (3, 5), (4, 3), (2, 15), (8, 3), (7, 11), (13, 17)]
        print("   f(mn)/(f(m)f(n)): " + " ".join(f"{a}·{b}: {f[a * b - 1] / (f[a - 1] * f[b - 1]):.3f}" for a, b in pairs))
        psi = n / local_factor(N, lambda p: p / (p + 1))
        Fm = measured_factor(f, N)
        edges = [0, 0.01, 0.05, 0.1, 0.2, 0.5, 0.8, 0.9, 1.0001]
        for name, F in [("own local factors", Fm), ("n/ψ(n)", n / psi)]:
            r_ = f / F
            cells = []
            for a_, b_ in zip(edges[:-1], edges[1:]):
                sel = (u > a_) & (u <= b_)
                q1, md, q3 = np.percentile(r_[sel], [25, 50, 75])
                cells.append(f"({a_:g},{b_:g}]: {md:.3f}±{(q3 - q1) / 2:.3f}")
            print(f"   f/F, F = {name}, median ± half-IQR by n/N: " + " ".join(cells))
        r = {"smooth, 16": ritz(G, (1 / psi)[:, None] * bspl(16, u))[0]}
        for J in [8, 16]:
            r[f"staircase, {J}"], xs = ritz(G, (1 / psi)[:, None] * stair(J, u))
        print("   x = w(n/N)/ψ(n), smallest quotient/λ_N: " + "  ".join(f"{k}: {v / lam:.4f}" for k, v in r.items()))
        S = stair(16, u)
        for name, fam, ths in [("1 − θ/(p + 1)", lambda th: (lambda p: 1 - th / (p + 1)), [0, 0.5, 0.8, 0.9, 1, 1.1, 1.2, 1.5]),
                               ("1 − θ/p", lambda th: (lambda p: 1 - th / p), [0.6, 0.8, 1.0])]:
            row = []
            for th in ths:
                F = local_factor(N, fam(th))
                row.append(f"θ = {th:g}: {ritz(G, (F / n)[:, None] * S)[0] / lam:.4f}")
            print(f"   F(p^k) = {name}, staircase: " + "  ".join(row))
        sqfree = np.ones(N)
        for q in range(2, math.isqrt(N) + 1):
            sqfree[q * q - 1::q * q] = 0
        tw = {"k/ψ(k)": local_factor(N, lambda p: p / (p + 1)), "φ(k)/k": local_factor(N, lambda p: 1 - 1 / p),
              "μ²(k)": sqfree}
        print("   twisted staircase Σ_k a(k)c(ku): " + "  ".join(
            f"a = {k}: {ritz(G, (1 / psi)[:, None] * stair(16, u, a))[0] / lam:.2f}" for k, a in tw.items()))
        wv = xs * psi
        wv /= wv[0]
        mu = np.zeros(N + 1)
        mu[1] = 1
        for k in range(1, N + 1):
            mu[2 * k::k] -= mu[k]
        grid = np.linspace(0.02, 1, 50)
        c = np.array([sum(mu[k] * wv[min(int(round(k * t * N)) - 1, N - 1)] for k in range(1, int(1 / t) + 1))
                      for t in grid])
        print("   c(u), u = " + " ".join(f"{t:.2f}: {v:.3f}" for t, v in zip(grid[::5], c[::5])))
        print(f"   c(0.02) = {c[0]:.3f}, ∫_0.02^1 c = {np.trapezoid(c, grid):.3f}; λ_k·N, k = 1..4: "
              + " ".join(f"{v:.4f}" for v in w4 * N), flush=True)
    if len(ladder) >= 2:
        lN = np.log([r[0] for r in ladder])
        a = [np.polyfit(lN, [r[1][k] for r in ladder], 1)[0] for k in range(4)]
        print("   λ_k·N ≈ a_k log N + b_k: a_k = " + ", ".join(f"{v:.4f}" for v in a)
              + "; a_k/a_1 = " + ", ".join(f"{v / a[0]:.2f}" for v in a))


def stair_big(Ns, block=1024):
    from ball_orbit import kernel_over_sqrt, tables
    for N in Ns:
        n = np.arange(1, N + 1, dtype=float)
        psi = n / local_factor(N, lambda p: p / (p + 1))
        Y = (1 / psi)[:, None] * stair(16, n / N)
        U, sv, _ = np.linalg.svd(Y / np.linalg.norm(Y, axis=0), full_matrices=False)
        Q = U[:, sv > 1e-9 * sv[0]]
        A, B = tables(N + 1)
        GQ = np.zeros_like(Q)
        for c0 in range(0, N, block):
            cols = n[c0:c0 + block][None, :]
            hi, lo = np.maximum(n[:, None], cols), np.minimum(n[:, None], cols)
            GQ += (hi * kernel_over_sqrt(hi / lo, A, B)) @ Q[c0:c0 + block]
        H = Q.T @ GQ
        w = eigh((H + H.T) / 2, eigvals_only=True)[0]
        print(f"N = {N}: best staircase quotient·N/log N = {w * N / math.log(N):.5f}", flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("N", nargs="*", type=int)
    ap.add_argument("--silence", action="store_true", help="how far up each minimiser keeps its points quiet")
    ap.add_argument("--zeros-file", default=None, help="ordinates of the zeros, one per line (for --silence)")
    ap.add_argument("--ground", action="store_true", help="the minimiser against w(n/N)/ψ(n)")
    ap.add_argument("--stair", action="store_true", help="the best staircase vector at large N")
    a = ap.parse_args()
    if a.silence:
        if not a.zeros_file:
            ap.error("--silence needs --zeros-file")
        silence_mode(a.N or [800, 1600], a.zeros_file)
    elif a.ground:
        ground_mode(a.N or [2000, 4000, 8000])
    elif a.stair:
        stair_big(a.N or [16000, 30000])
    else:
        models_mode(a.N or [100, 200, 400, 800, 1600])


if __name__ == "__main__":
    main()
