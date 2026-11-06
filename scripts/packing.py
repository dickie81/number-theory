#!/usr/bin/env python3
"""The zeros against point sets with their density and no arithmetic, the shape of the minimiser of Q_N, and the
variational problem for its profile (formalisations/ball-rate.md, sections "Packing: what the zeros allow that a
fence does not" and "The variational problem, solved"). Uncertified numerics.

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
without storing it: its quotient·N/log N, to set against λ_N·N/log N from scripts/lambda_large.py. Also the additive
form x_n = (F(n) − P + P·w(n/N))/n, F(n) = n/ψ(n): the best vector in the span of F(n)/n, 1/n and the staircases/n.

    python3 scripts/packing.py --fence-class [K]                    # default K = 3000; also needs mpmath

--fence-class: Theorem B of the note's last section. On the class n·x_n = Σ_{d | n, d ≤ D₀} E_d(n/N), the fence form
has lim inf ≥ c(D₀) = min_e m(e)/D(e), m(e) = Σ_k 2|ζ(½ + iγ_k)M_e(½ − iγ_k)|²/(¼ + γ_k²), M_e(s) = Σ_d e(d)d^{−s};
the sum over the first K fence points is a lower bound, every term being ≥ 0.

    python3 scripts/packing.py --fence-cap [N ...]                  # default N = 400 1600 6400

--fence-cap: the constrained minima of the note's Theorem C, q_n = min{Q^pf(x) : x_n = 1} = 1/(G⁻¹)_nn on the picket
fence, for n = 1, 2, 3, 4, 5, 8, 16, 32. Printed with λ_N·√N: q_n·√N; the free part n·W(2πM_n), M_n = max(n, N/n),
W(T) = (log(T/2π) + 1)/(πT), the energy of x_n = 1 above the height where it has no alias; the cost paid below that
height; and A_n, the amplitude of the fit m·x_m ≈ a·cos(2πm/n) + b·sin(2πm/n) over m ≥ 2√N.

    python3 scripts/packing.py --solve [N ...]                      # N optional, e.g. 2000 4000 8000 16000 30000

--solve: the variational problem of the note's section "The variational problem, solved", which needs no N.
  - The profile problem: the minimum of I[c] = ∫_0^∞ (1 − W_c(x))² dx, W_c(x) = Σ_{1 ≤ k ≤ x} c(k/x) (0 for x < 1), over
    cubic splines c on [0, 1] with c(0) = −2, c(1) = 0, ∫c = 0, uniform knots and kinks allowed at the rationals of
    denominator ≤ Q. Gauss–Legendre on each [k, k + 1] up to X, and beyond X the tail ∫(c'(1)²/720 + c'(0)²/144)dx/x².
  - The arithmetic problem: Λ = (1/12)·(T + κP²)/D over multiplicative F = 1 ∗ e with κ = I_min − 1, where
    D = Σ F(n)²/n², S(a) = Σ_g e(ag)/g, P = S(1) and T = Σ_a Π_{p | a}(1 − p⁻²)·S(a)², all Euler products. The local
    factors F(p^v), v ≤ 10, are optimised for p ≤ 200 by BFGS, prime by prime, and for larger p the squarefree factor
    1 − θ/(p + 1) on a grid of θ.
  - The admissible class of the upper-bound theorem (note's section "The upper bound with the sharp constant"): c a
    quintic spline on M uniform intervals with c(0) = −2, ∫c = 0 and c(1) = c'(1) = c''(1) = 0, and e supported on
    d ≤ D₀, where min_e (T + κP²)/(12D) is the bottom of a generalized eigenproblem, T = eᵀSᵀΩSe, P = Σ_d e(d)/d,
    D = ζ(2)Σ_{d,d'} e(d)e(d')/lcm(d, d')².
  - With N given: the Rayleigh quotients, times N/log N, of three fixed vectors built from c_opt, w(u) = Σ_{k ≤ 1/u}
    c_opt(ku): w(n/N)/n (F = 1), F(n)w(n/N)/n and (F(n) − P(1 − w(n/N)))/n with F = n/ψ(n), from the Gram matrix in
    column blocks; with two N or more, the fit A + B/log N, against the predicted limits K(1)·I, K(ψ)·I and
    (T + (I − 1)P²)/12D.
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


def stair_big(Ns):
    def ritz_big(N, Y):
        U, sv, _ = np.linalg.svd(Y / np.linalg.norm(Y, axis=0), full_matrices=False)
        Q = U[:, sv > 1e-9 * sv[0]]
        H = Q.T @ gram_apply(N, Q)
        return eigh((H + H.T) / 2, eigvals_only=True)[0]

    for N in Ns:
        n = np.arange(1, N + 1, dtype=float)
        psi = n / local_factor(N, lambda p: p / (p + 1))
        S = stair(16, n / N)
        w = ritz_big(N, (1 / psi)[:, None] * S)
        wa = ritz_big(N, np.hstack([(1 / psi)[:, None], (1 / n)[:, None], S / n[:, None]]))
        print(f"N = {N}: quotient·N/log N, best staircase {w * N / math.log(N):.5f}, additive {wa * N / math.log(N):.5f}",
              flush=True)


def primes_upto(n):
    s = np.ones(n + 1, bool)
    s[:2] = False
    for p in range(2, math.isqrt(n) + 1):
        if s[p]:
            s[p * p::p] = False
    return np.nonzero(s)[0]


def profile_problem(Q=10, M=30, X=300, G=10, kdeg=3):
    """min I[c] over cubic splines with uniform knots (M intervals) and triple knots at the rationals of denominator ≤ Q."""
    from fractions import Fraction
    from numpy.polynomial.legendre import leggauss
    fr = sorted({Fraction(a, b) for b in range(1, Q + 1) for a in range(b + 1)})
    inner = [float(f) for f in fr if 0 < f < 1]
    pts = np.unique(np.concatenate([[float(f) for f in fr], np.linspace(0, 1, M + 1)]))
    t = np.sort(np.concatenate([[0.0] * kdeg, pts, [1.0] * kdeg, inner, inner]))
    J = len(t) - kdeg - 1
    gx, gw = leggauss(G)
    rows, ws = [], []
    for k in range(1, X):
        for xi, wi in zip(k + (gx + 1) / 2, gw / 2):
            u = np.clip(np.arange(1, k + 1) / xi, 0, 1 - 1e-15)
            rows.append(np.asarray(BSpline.design_matrix(u, t, kdeg).sum(axis=0)).ravel())
            ws.append(wi)
    Wm, ws = np.array(rows), np.array(ws)

    def ev(u, nu=0):
        return np.array([BSpline(t, np.eye(J)[j], kdeg)(u, nu) for j in range(J)])

    b0, b1, d0, d1 = ev(0.0), ev(1.0), ev(0.0, 1), ev(1.0, 1)
    integ = np.array([(t[j + kdeg + 1] - t[j]) / (kdeg + 1) for j in range(J)])
    H = (Wm * ws[:, None]).T @ Wm + (np.outer(d1, d1) / 720 + np.outer(d0, d0) / 144) / X
    g = (Wm * ws[:, None]).sum(axis=0)
    C = np.vstack([b0, b1, integ])
    K = np.block([[2 * H, C.T], [C, np.zeros((3, 3))]])
    a = np.linalg.solve(K, np.concatenate([2 * g, [-2.0, 0.0, 0.0]]))[:J]
    return 1 + a @ H @ a - 2 * g @ a + ws.sum(), BSpline(t, a, kdeg), J


def smooth_profile_problem(M, X=300, G=10, kdeg=5):
    """min I[c] over degree-kdeg splines on M uniform intervals, c(0) = −2, ∫c = 0, c(1) = c'(1) = c''(1) = 0."""
    from numpy.polynomial.legendre import leggauss
    t = np.concatenate([[0.0] * kdeg, np.linspace(0, 1, M + 1), [1.0] * kdeg])
    J = len(t) - kdeg - 1
    gx, gw = leggauss(G)
    rows, ws = [], []
    for k in range(1, X):
        for xi, wi in zip(k + (gx + 1) / 2, gw / 2):
            u = np.clip(np.arange(1, k + 1) / xi, 0, 1 - 1e-15)
            rows.append(np.asarray(BSpline.design_matrix(u, t, kdeg).sum(axis=0)).ravel())
            ws.append(wi)
    Wm, ws = np.array(rows), np.array(ws)

    def ev(u, nu=0):
        return np.array([BSpline(t, np.eye(J)[j], kdeg)(u, nu) for j in range(J)])

    d0, d1 = ev(0.0, 1), ev(1.0, 1)
    integ = np.array([(t[j + kdeg + 1] - t[j]) / (kdeg + 1) for j in range(J)])
    H = (Wm * ws[:, None]).T @ Wm + (np.outer(d1, d1) / 720 + np.outer(d0, d0) / 144) / X
    g = (Wm * ws[:, None]).sum(axis=0)
    C = np.vstack([ev(0.0), integ, ev(1.0), ev(1.0, 1), ev(1.0, 2)])
    rhs = np.array([-2.0, 0.0, 0.0, 0.0, 0.0])
    K = np.block([[2 * H, C.T], [C, np.zeros((5, 5))]])
    a = np.linalg.solve(K, np.concatenate([2 * g, rhs]))[:J]
    return 1 + a @ H @ a - 2 * g @ a + ws.sum(), BSpline(t, a, kdeg)


def finite_arithmetic(D0, kappa):
    """min over e supported on d ≤ D0 of (T + κP²)/(12D), and the minimiser e (e(1) = 1)."""
    d = np.arange(1, D0 + 1)
    om = np.ones(D0 + 1)
    comp = np.zeros(D0 + 1, bool)
    for p in range(2, D0 + 1):
        if not comp[p]:
            comp[2 * p::p] = True
            om[p::p] *= 1 - 1 / p ** 2
    S = np.zeros((D0, D0))
    for a in range(1, D0 + 1):
        S[a - 1, a - 1::a] = a / d[a - 1::a]
    T = S.T @ (om[1:][:, None] * S)
    pv = 1.0 / d
    lcm = np.outer(d, d) // np.gcd.outer(d, d)
    B = (math.pi ** 2 / 6) / lcm.astype(float) ** 2
    w, V = eigh(T + kappa * np.outer(pv, pv), B, subset_by_index=[0, 0])
    return w[0] / 12, V[:, 0] / V[0, 0]


def local_forms(p, V=10):
    """In the local factors F_v = F(p^v), v ≤ V: the forms of T_p and D_p, and the functional s_p(0)."""
    q, n = 1.0 / p, V + 1
    M = np.eye(n) - np.eye(n, k=-1)
    S = np.array([[q ** (j - i) if j >= i else 0.0 for j in range(n)] for i in range(n)])
    SM = S @ M
    A = SM.T @ np.diag([1.0] + [1 - q * q] * (n - 1)) @ SM
    return A, np.diag(q ** (2 * np.arange(n))), SM[0]


def arithmetic_problem(kappa, P=200000, V=10, free_upto=200, iters=8):
    from scipy.optimize import minimize
    ps = primes_upto(P)
    small = [int(p) for p in ps if p <= free_upto]
    forms = {p: local_forms(p, V) for p in small}
    Fs = {p: np.array([1.0] + [p / (p + 1.0)] * V) for p in small}
    big = ps[ps > free_upto].astype(float)
    eb = -1.0 / (big + 1)

    def totals():
        lT = np.sum(np.log((1 + eb / big) ** 2 + (1 - big ** -2.0) * eb * eb))
        lS = np.sum(2 * np.log(1 + eb / big))
        lD = np.sum(np.log(1 + (1 + eb) ** 2 / (big * big - 1.0)))
        for p in small:
            A, B, r = forms[p]
            F = Fs[p]
            lT += math.log(F @ A @ F)
            lS += 2 * math.log(abs(r @ F))
            lD += math.log(F @ B @ F)
        return math.exp(lT), math.exp(lS), math.exp(lD)

    prev = None
    for _ in range(iters):
        T, S2, D = totals()
        lam = (T + kappa * S2) / (12 * D)
        if prev is not None and abs(lam - prev) < 1e-10:
            break
        prev = lam
        for p in small:
            A, B, r = forms[p]
            F = Fs[p]
            To, So, Do = T / (F @ A @ F), S2 / (r @ F) ** 2, D / (F @ B @ F)

            def obj(f):
                Gv = np.concatenate([[1.0], f])
                return (To * (Gv @ A @ Gv) + kappa * So * (r @ Gv) ** 2) / (Do * (Gv @ B @ Gv))

            Fs[p] = np.concatenate([[1.0], minimize(obj, F[1:], method="BFGS", options={"gtol": 1e-12}).x])
            T, S2, D = totals()
        Tb = (1 + eb / big) ** 2 + (1 - big ** -2.0) * eb * eb
        kp = kappa * (S2 / (1 + eb / big) ** 2) / (T / Tb)
        best, cur = eb.copy(), None
        for th in np.linspace(0.4, 1.6, 1201):
            e = -th / (big + 1)
            val = ((1 + e / big) ** 2 * (1 + kp) + (1 - big ** -2.0) * e * e) / (1 + (1 + e) ** 2 / (big * big - 1.0))
            cur = ((1 + best / big) ** 2 * (1 + kp) + (1 - big ** -2.0) * best * best) / (
                1 + (1 + best) ** 2 / (big * big - 1.0))
            best = np.where(val < cur, e, best)
        eb[:] = best
    T, S2, D = totals()
    return (T + kappa * S2) / (12 * D), Fs, float(np.median(-eb * (big + 1))), (T, S2, D)


def gram_apply(N, X, block=1024):
    """G_N·X from the Gram matrix in column blocks, without storing it."""
    from ball_orbit import kernel_over_sqrt, tables
    A, B = tables(N + 1)
    n = np.arange(1, N + 1, dtype=float)
    GX = np.zeros_like(X)
    for c0 in range(0, N, block):
        cols = n[c0:c0 + block][None, :]
        hi, lo = np.maximum(n[:, None], cols), np.minimum(n[:, None], cols)
        GX += (hi * kernel_over_sqrt(hi / lo, A, B)) @ X[c0:c0 + block]
    return GX


def solve_mode(Ns):
    print("The profile problem, min I[c]:")
    best = None
    for Q, M in [(4, 16), (6, 16), (8, 24), (10, 30)]:
        I, c, J = profile_problem(Q, M)
        print(f"   kinks at the rationals of denominator ≤ {Q:2d}, uniform {M} intervals ({J} functions): "
              f"I_min = {I:.6f}", flush=True)
        best = (I, c)
    I, c = best
    print("   c_opt(u), u = 0, 0.05, ..., 1: " + " ".join(f"{c(u):.3f}" for u in np.linspace(0, 1, 21)))
    print(f"   c_opt'(0) = {c(0.0, 1):.3f}, c_opt'(1) = {c(1.0, 1):.3f}")
    ps = primes_upto(200000).astype(float)
    e = -1 / (ps + 1)
    T = math.exp(np.sum(np.log((1 + e / ps) ** 2 + (1 - ps ** -2.0) * e * e)))
    S2 = math.exp(np.sum(2 * np.log(1 + e / ps)))
    D = math.exp(np.sum(np.log(1 + (1 + e) ** 2 / (ps * ps - 1.0))))
    print("The arithmetic problem:")
    print(f"   F = n/ψ(n): T = {T:.6f}, P² = {S2:.6f}, D = {D:.6f}; K = T/12D = {T / (12 * D):.6f}, "
          f"(T + κP²)/12D = {(T + (I - 1) * S2) / (12 * D):.6f} at κ = I_min − 1 = {I - 1:.4f}")
    print(f"   F = 1: K = 1/(2π²) = {1 / (2 * math.pi ** 2):.6f}")
    for kappa in [0.0, I - 1]:
        lam, Fs, th, (T, S2, D) = arithmetic_problem(kappa)
        print(f"   optimal F at κ = {kappa:.4f}: Λ = {lam:.6f} (T = {T:.6f}, P² = {S2:.6f}, D = {D:.6f}); F(p) at p = 2, 3, 5,"
              " 7, 11, 13: " + " ".join(f"{Fs[p][1]:.4f}" for p in [2, 3, 5, 7, 11, 13]) + "; F(2^v), v = 2, 3, 4: "
              + " ".join(f"{v:.4f}" for v in Fs[2][2:5]) + f"; (1 − F(p))(p + 1) → {th:.3f}", flush=True)
    print("The admissible class of the theorem (smooth c, finitely supported e):")
    Is = None
    for M in [48, 96, 192]:
        Is, cs = smooth_profile_problem(M)
        print(f"   quintic c on {M} intervals, c(1) = c'(1) = c''(1) = 0: I[c] = {Is:.6f}", flush=True)
    for D0 in [250, 500, 1000, 2000]:
        lam_f, ef = finite_arithmetic(D0, Is - 1)
        print(f"   e supported on d ≤ {D0}: min (T + κP²)/12D = {lam_f:.6f} at κ = {Is - 1:.6f}; e(1..6) = "
              + " ".join(f"{v:+.4f}" for v in ef[:6]), flush=True)
    if not Ns:
        return
    ps = primes_upto(200000).astype(float)
    e = -1 / (ps + 1)
    T = math.exp(np.sum(np.log((1 + e / ps) ** 2 + (1 - ps ** -2.0) * e * e)))
    S2 = math.exp(np.sum(2 * np.log(1 + e / ps)))
    D = math.exp(np.sum(np.log(1 + (1 + e) ** 2 / (ps * ps - 1.0))))
    pred = [I / (2 * math.pi ** 2), T * I / (12 * D), (T + (I - 1) * S2) / (12 * D)]
    names = ["w/n (F = 1)", "F·w/n, F = n/ψ(n)", "(F − P(1 − w))/n"]
    print("Fixed vectors from c_opt, quotient·N/log N:")
    rows = []
    for N in Ns:
        n = np.arange(1, N + 1, dtype=float)
        w = np.array([c(np.arange(1, N // m + 1) * m / N).sum() for m in range(1, N + 1)])
        F = local_factor(N, lambda p: p / (p + 1))
        X = np.vstack([w / n, F * w / n, (F - math.sqrt(S2) * (1 - w)) / n]).T
        q = np.einsum("ij,ij->j", X, gram_apply(N, X)) / np.einsum("ij,ij->j", X, X) * N / math.log(N)
        rows.append(q)
        print(f"   N = {N:5d}: " + "   ".join(f"{a}: {v:.5f}" for a, v in zip(names, q)), flush=True)
    if len(Ns) >= 2:
        L = np.log(Ns)
        Xf = np.vstack([np.ones_like(L), 1 / L]).T
        for j, a in enumerate(names):
            coef, *_ = np.linalg.lstsq(Xf, np.array([r[j] for r in rows]), rcond=None)
            print(f"   {a}: A + B/log N gives A = {coef[0]:.5f}; predicted limit {pred[j]:.5f}")


def fence_cap_mode(Ns, ns=(1, 2, 3, 4, 5, 8, 16, 32)):
    """The constrained minima q_n = min{Q^pf(x) : x_n = 1} = 1/(G⁻¹)_nn on the picket fence."""
    from scipy.linalg import cho_factor, cho_solve
    for N in Ns:
        g, G0 = points("picket", N)
        G = gram_points(N, g, G0)
        lam = eigh(G, subset_by_index=[0, 0], eigvals_only=True)[0]
        C = cho_factor(G)
        sq, m = math.sqrt(N), np.arange(1, N + 1)
        lg, w = np.log(m.astype(float)), 2.0 / (0.25 + g * g)
        print(f"N = {N}: λ_N·√N = {lam * sq:.4f}")
        print(f"   {'n':>3} {'q_n·√N':>8} {'free·√N':>8} {'below·√N':>9} {'A_n':>6}")
        for n in ns:
            e = np.zeros(N)
            e[n - 1] = 1
            y = cho_solve(C, e)
            q = 1 / y[n - 1]
            x = y * q
            tf = 2 * math.pi * max(n, N / n)
            free = n * (math.log(tf / (2 * math.pi)) + 1) / (math.pi * tf)
            s = g[g < tf]
            ws = w[:len(s)]
            below = sum(float(ws[i:i + 4096] @ np.abs(np.exp(1j * np.outer(s[i:i + 4096], lg)) @ (x * np.sqrt(m))) ** 2)
                        for i in range(0, len(s), 4096))
            sel = m >= 2 * sq
            X = np.stack([np.cos(2 * math.pi * m[sel] / n), np.sin(2 * math.pi * m[sel] / n)], 1)
            ab = np.linalg.lstsq(X, (m * x)[sel], rcond=1e-9)[0]
            amp = math.hypot(*ab) if n > 2 else abs(ab[0])
            print(f"   {n:3d} {q * sq:8.4f} {free * sq:8.4f} {below * sq:9.4f} {amp:6.3f}", flush=True)


def fence_class_mode(K):
    import mpmath
    mpmath.mp.dps = 15
    g = Phi_inv(np.arange(1, K + 1) - 0.5)
    z2 = np.array([float(abs(mpmath.zeta(mpmath.mpc(0.5, t))) ** 2) for t in g])
    wz = 2 * z2 / (0.25 + g ** 2)
    print(f"{K} fence points, to height {g[-1]:.0f}; lower bounds for c(D0) = min_e m(e)/D(e):")
    for D0 in [1, 2, 4, 8, 16, 32, 64]:
        d = np.arange(1, D0 + 1)
        E = np.exp(1j * np.outer(g, np.log(d))) * d ** -0.5
        Mf = ((E.conj() * wz[:, None]).T @ E).real
        lcm = np.outer(d, d) // np.gcd.outer(d, d)
        B = (math.pi ** 2 / 6) / lcm.astype(float) ** 2
        print(f"   D0 = {D0:3d}: c(D0) >= {eigh(Mf, B, eigvals_only=True, subset_by_index=[0, 0])[0]:.5f}", flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("N", nargs="*", type=int)
    ap.add_argument("--silence", action="store_true", help="how far up each minimiser keeps its points quiet")
    ap.add_argument("--zeros-file", default=None, help="ordinates of the zeros, one per line (for --silence)")
    ap.add_argument("--ground", action="store_true", help="the minimiser against w(n/N)/ψ(n)")
    ap.add_argument("--stair", action="store_true", help="the best staircase vector at large N")
    ap.add_argument("--solve", action="store_true", help="the variational problem for c and the arithmetic factor")
    ap.add_argument("--fence-class", action="store_true", help="the fence margin on the arithmetic class")
    ap.add_argument("--fence-cap", action="store_true", help="the fence's constrained minima q_n")
    a = ap.parse_args()
    if a.silence:
        if not a.zeros_file:
            ap.error("--silence needs --zeros-file")
        silence_mode(a.N or [800, 1600], a.zeros_file)
    elif a.ground:
        ground_mode(a.N or [2000, 4000, 8000])
    elif a.stair:
        stair_big(a.N or [16000, 30000])
    elif a.solve:
        solve_mode(a.N)
    elif a.fence_class:
        fence_class_mode(a.N[0] if a.N else 3000)
    elif a.fence_cap:
        fence_cap_mode(a.N or [400, 1600, 6400])
    else:
        models_mode(a.N or [100, 200, 400, 800, 1600])


if __name__ == "__main__":
    main()
