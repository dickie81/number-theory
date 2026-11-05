#!/usr/bin/env python3
"""The constants of formalisations/ball-rate.md against the actual zeros, up to N = 2000. Uncertified numerics.

    python3 scripts/ball_rate.py [--zeros M] [--nmax N] [--cache FILE] [--zeros-file FILE] [--sections ABCDEF]

With the prime-side Gram matrix of scripts/ball_orbit.py (exact kernel from the explicit formula) and the first M zeros
of ζ (mpmath, cached in FILE if given; or read from --zeros-file, one ordinate per line, e.g. the first 2000 from
mpmath and the rest from scripts/zeta_zeros_rs.py, the Riemann–Siegel finder); --sections picks the sections:
  A. λ_N, the smallest eigenvalue of G_N, against 0.048·log N/N;
  B. the explicit vector x_n = (1 − n/N)²/ψ(n), ψ Dedekind's function, its Rayleigh quotient against C·log N/N;
  C. H₀ = 2 + γ − log 4π against Σ_ρ 1/(¼ + γ²) over the first M zeros, and the tail;
  D. the witness level of a zero moved to ½ ± δ ± iγ₁: |a₀|, Λ, λ*, (p₀, q₀), N₀, the twin sum W at λ* (negative) and at
     log(p₀/q₀), and the first level at which the moved Gram matrix is indefinite;
  E. the sampling constant c of statement 3B on the minimising vectors, c(T) = Σ_{|γ| ≤ T}|V_x(ρ)|² / (T·Σ x_n² n), at
     T = N, 2N, 4N, 8N, 12N and at the height of the M-th zero, the share of the prime-side form carried by the zeros
     below each T, and the zero-side form against the prime-side form;
  F. the density model (uniform margin) and the picket-fence model (the sag), the same quantities as in the note.
"""
import argparse
import math
import os
import sys
import time

import numpy as np
import scipy.linalg as sl

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ball_orbit as bo  # noqa: E402

GAMMA_E = 0.5772156649015329
H0 = 2 + GAMMA_E - math.log(4 * math.pi)


def zeros(M, cache, zeros_file=None):
    if zeros_file:
        g = np.loadtxt(zeros_file)
        return g[:M] if len(g) >= M else g
    if cache and os.path.exists(cache):
        g = np.loadtxt(cache)
        if len(g) >= M:
            return g[:M]
    import mpmath
    mpmath.mp.dps = 20
    t0 = time.time()
    g = np.array([float(mpmath.zetazero(n).imag) for n in range(1, M + 1)])
    print(f"  ({M} zeros in {time.time() - t0:.0f}s, up to height {g[-1]:.2f})")
    if cache:
        np.savetxt(cache, g)
    return g


def psi(N):
    """Dedekind's ψ(n) = n·Π_{p|n}(1 + 1/p) for n ≤ N."""
    r = np.arange(N + 1, dtype=float)
    comp = np.zeros(N + 1, dtype=bool)
    for p in range(2, N + 1):
        if not comp[p]:
            comp[2 * p::p] = True
            r[p::p] *= (p + 1) / p
    return r[1:]


def lam_min(G):
    return sl.eigh(G, eigvals_only=True, subset_by_index=[0, 0])[0]


def section_A(Ns, grams, mins):
    print("A. λ_N = smallest eigenvalue of the prime-side Gram matrix, against 0.048·log N/N")
    for N in Ns:
        lam = mins[N][0]
        print(f"   N={N:5d}  λ_N={lam:.4e}  N·λ_N/log N={N * lam / math.log(N):.4f}")


def section_B(Ns, grams, mins):
    print("B. the explicit vector x_n = (1 − n/N)²/ψ(n): Rayleigh quotient q_N, q_N·N/log N (the constant C), q_N/λ_N")
    for N in Ns:
        n = np.arange(1, N + 1)
        x = (1 - n / N) ** 2 / psi(N)
        q = x @ grams[N] @ x / (x @ x)
        print(f"   N={N:5d}  q_N={q:.4e}  C={q * N / math.log(N):.4f}  q_N/λ_N={q / mins[N][0]:.2f}")


def section_C(g, w):
    M, T = len(g), g[-1]
    print("C. H₀ = 2 + γ − log 4π against the zero sum")
    s = 2 * w.sum()
    tail = math.log(T / (2 * math.pi)) / (math.pi * T)  # ∫_T^∞ (1/π) log(t/2π)/t² dt
    print(f"   H₀ = {H0:.6f}; Σ over the first {M} zeros (both signs) = {s:.6f}; density tail ≈ {tail:.6f}; "
          f"sum + tail = {s + tail:.6f}")


def section_D(g, w, Nmax):
    M, T = len(g), g[-1]
    tail = math.log(T / (2 * math.pi)) / (math.pi * T)
    print("D. the witness level for the first zero moved to ½ ± δ ± iγ₁ (single crossing, M = 0)")
    g1 = g[0]
    on = w[1:]  # the other zeros stay on the line
    for d in (0.05, 0.02, 0.01):
        rho = 0.5 + d + 1j * g1
        a0 = 1 / (rho * (1 - rho))
        Lam = math.log((4 * H0 + 4 * abs(a0)) / (2 * abs(a0))) / (2 * d)
        phi = np.angle(a0)
        k = math.ceil((2 * g1 * Lam + phi - math.pi) / (2 * math.pi))
        lam_star = (math.pi - phi + 2 * math.pi * k) / (2 * g1)
        q0 = math.ceil(6 * g1 / math.pi)
        p0 = math.ceil(q0 * math.exp(lam_star))
        N0 = p0 ** 2

        def W(lam):  # the twin sum Σ_ρ a_ρ(2 + e^{λP} + e^{−λP}), P = 2(ρ − ½), with the moved quartet
            P = 2 * (rho - 0.5)
            quart = 4 * np.real(a0 * (np.exp(lam * P) + np.exp(-lam * P)))
            online = (on * (2 + 2 * np.cos(2 * lam * g[1:]))).sum() * 2
            return 2 * 2 * a0.real + quart + online
        Wst, Wpq = W(lam_star), W(math.log(p0 / q0))
        print(f"   δ={d}: |a₀|={abs(a0):.5f}  Λ={Lam:.2f}  λ*={lam_star:.2f}  q₀={q0}  p₀≈e^{math.log(p0):.1f}  "
              f"N₀≈10^{math.log10(N0):.1f}  W(λ*)={Wst:.3e}  W(log p₀/q₀)={Wpq:.3e}  (tail ≤ {4 * tail:.1e})")
    A, B = bo.tables(Nmax + 2)

    def zero_term(u, beta, gg):
        r = beta + 1j * gg
        return 2 * np.real(np.exp((r - 0.5) * u) / (r * (1 - r)))

    for d in (0.05, 0.02):
        def Kmoved(x):
            u = np.log(x)
            return np.sqrt(x) * bo.kernel_over_sqrt(x, A, B) - zero_term(u, 0.5, g1) + zero_term(u, 0.5 + d, g1) \
                + zero_term(u, 0.5 - d, g1)
        first = None
        for N in (64, 128, 256, 512, 1024, 2048):
            if N > Nmax:
                break
            m = np.arange(1, N + 1, dtype=float)
            Mm, Nn = np.meshgrid(m, m, indexing="ij")
            hi, lo = np.maximum(Mm, Nn), np.minimum(Mm, Nn)
            Gm = np.sqrt(Mm * Nn) * Kmoved(hi / lo)
            l = lam_min(Gm)
            if l < 0 and first is None:
                first = N
            print(f"   δ={d}: moved Gram, N={N:5d}: λ_min={l:.3e}")
        print(f"   δ={d}: first indefinite level among powers of two ≤ {Nmax}: {first}  (80/δ = {80 / d:.0f})")


def section_E(Ns, mins, g, w):
    M, T = len(g), g[-1]
    print("E. the sampling constant on the minimising vectors, c(T) = Σ_{|γ|≤T}|V_x(ρ)|² / (T·Σ x_n² n), and the share"
          f" of the prime-side form carried by the zeros below T; T = N, 2N, 4N, 8N, 12N and the top T = {T:.1f} ({M} zeros)")
    for N in Ns:
        lam, x = mins[N]
        n = np.arange(1, N + 1, dtype=float)
        xs = x * np.sqrt(n)
        V2 = np.empty(M)
        for k in range(0, M, 4000):  # chunked: |V_x(½ + iγ)|²
            V2[k:k + 4000] = np.abs(np.exp(1j * np.outer(g[k:k + 4000], np.log(n))) @ xs) ** 2
        cum = np.cumsum(2 * V2)       # Σ_{|γ| ≤ T} |V|², both signs
        cumw = np.cumsum(2 * V2 * w)  # the zero-side form below T
        denom = (x * x * n).sum()
        Ts = [r * N for r in (1, 2, 4, 8, 12) if r * N <= T] + [T]
        idx = [np.searchsorted(g, t, side="right") - 1 for t in Ts]
        cs = " ".join(f"c({t / N:.0f}N)={cum[i] / (t * denom):.2e}" for t, i in zip(Ts, idx))
        sh = " ".join(f"{cumw[i] / lam:.3f}" for i in idx)
        print(f"   N={N:5d}  {cs}  | share below the same T's: {sh}  | zero-side total/prime-side = {cumw[-1] / lam:.4f}")


def section_F():
    print("F. the models: density (uniform margin) and picket fence (the sag)")
    from scipy.integrate import quad
    dens = lambda t: math.log(t / (2 * math.pi)) / (2 * math.pi) / (0.25 + t * t)

    def Kd(u):
        if u == 0:
            return 2 * quad(dens, 2 * math.pi, np.inf, limit=500)[0]
        return 2 * quad(dens, 2 * math.pi, np.inf, weight="cos", wvar=u, limlst=400)[0]
    for N in (50, 100, 200, 400):
        n = np.arange(1, N + 1, dtype=float)
        Mm, Nn = np.meshgrid(n, n, indexing="ij")
        u = np.abs(np.log(Mm / Nn))
        uu, inv = np.unique(np.round(u, 12), return_inverse=True)
        Kv = np.array([Kd(x) for x in uu])[inv].reshape(N, N)
        print(f"   density model N={N:4d}: λ_min={lam_min(np.sqrt(Mm * Nn) * Kv):.5f}  (K_dens(1) = {Kd(0):.5f})")
    from scipy.optimize import brentq
    Mpf = 20000
    gpf = np.array([brentq(lambda t, k=k: t / (2 * math.pi) * math.log(t / (2 * math.pi * math.e)) + 7 / 8 - k,
                           2 * math.pi * math.e, 1e9) for k in range(1, Mpf + 1)])
    Tpf = gpf[-1]
    for N in (50, 100, 200, 400):
        n = np.arange(1, N + 1)
        Vm = np.exp(1j * np.outer(gpf, np.log(n))) * np.sqrt(n)[None, :]
        Gp = 2 * np.real(Vm.conj().T @ (Vm / (0.25 + gpf[:, None] ** 2)))
        # tail of the density beyond T_pf: Σ_{m,n} √(mn)·(1/π)∫_T^∞ log(t/2π) cos(t log(m/n))/t² dt, the diagonal part
        Gp += np.diag(n * math.log(Tpf / (2 * math.pi)) / (math.pi * Tpf))
        print(f"   picket fence N={N:4d} (first {Mpf} mean zeros + diagonal tail): λ_min={lam_min(Gp):.4e}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--zeros", type=int, default=2000)
    ap.add_argument("--nmax", type=int, default=2000)
    ap.add_argument("--cache", default=None)
    ap.add_argument("--zeros-file", default=None)
    ap.add_argument("--sections", default="ABCDEF")
    a = ap.parse_args()
    sec = a.sections.upper()
    Ns = [n for n in (100, 200, 400, 800, 1000, 1600, 2000) if n <= a.nmax]
    g = zeros(a.zeros, a.cache, a.zeros_file)
    w = 1.0 / (0.25 + g ** 2)
    print(f"({len(g)} zeros, to height {g[-1]:.1f})")
    grams, mins = {}, {}
    if any(c in sec for c in "ABE"):
        for N in Ns:
            G = bo.gram(N)
            grams[N] = G
            lam, v = sl.eigh(G, subset_by_index=[0, 0])
            mins[N] = (lam[0], v[:, 0])
    if "A" in sec:
        section_A(Ns, grams, mins)
    if "B" in sec:
        section_B(Ns, grams, mins)
    if "C" in sec:
        section_C(g, w)
    if "D" in sec:
        section_D(g, w, a.nmax)
    if "E" in sec:
        section_E(Ns, mins, g, w)
    if "F" in sec:
        section_F()


if __name__ == "__main__":
    main()
