"""The pivot inequality d_k ≥ d_1 for every k ≥ 2 under RH: a numerical design for the proof.

A numerical experiment for the section "The pivot inequality for every k" of docs/ball-conjecture.md. It is not a
check, and CI does not run it. Floating point and linear programming, uncertified.

Under RH, Weil's explicit formula with h = |D|²Φ_N, D(t) = Σ_{n ≤ N} c_n n^{−it}, c_n = x_n√n, gives for every test
function Φ_N ≤ w = 1/(1/4 + t²) whose Fourier transform is supported in |v| < log(1 + 1/N), and every m ≤ Φ_N·L whose
transform is supported in |v| < log(N/(N − 1)), with L(t) = Re ψ(1/4 + it/2) − log π,

    Q_N(x) = Σ_ρ |V_x(ρ)|²/(1/4 + γ²) ≥ Σ_ρ h(γ) ≥ 2D(i/2)D(−i/2)Φ_N(i/2) + (1/2π)(∫m·Σc_n² − ∫Φ_N·L(c)),

L(c) = 2Σ_q Λ(q)q^{−1/2}Σ_{jq ≤ N} c_j c_{jq} Landau's form: the transform of Φ_N kills every prime term but the
diagonal of Landau's, and that of m every off-diagonal term of ∫|D|²m. Take Φ_N(t) = φ(t/N)/N² and
m(t) = (Φ_N(t)·(log N + λ(t/N)) − r(t/N)/N²), so that in s = t/N everything is independent of N:

    Q_N(x) ≥ (P/N)·((log N + d)Σc_n² − L(c)) − (pole),   P = ∫φ/2π,   d = (∫φλ − ∫r)/∫φ.

The pointwise condition m ≤ Φ_N·L for every N ≥ 2 holds if φ(s)(λ(s) − g(s)) ≤ r(s) for s > 0, where
g(s) = log(s/2π) − E(s) ≤ L(Ns) − log N and E(s) = sup_{t ≥ 2s}(log(t/2π) − L(t))⁺. The top vertex of the
divisibility graph then gives (log N + d)Σc_n² − L(c) ≥ Λ(N, d)·c_N² by a Schur test (weights n^{−1/2}) whose room at
the parent N/q is d + log q − M(q − 1), M(x) = Σ_{n ≤ x} Λ(n)/n:

    Λ(N, d) ≥ log N + d − Σ_{q ∣ N} (Λ(q)²/q)/(d + log q − M(q − 1)).

With x_N = 1, c_N² = N, so the N-th pivot is d_N ≥ P·Λ(N, d). The orbit-lattice conjecture is d_N ≥ d_1 = K_H(1) =
2 + γ − log 4π for every N.

The construction:
  φ(s) = (1 − η)(1 − K₄(s/6))/s²,  K₄(x) = sinc⁴(x)(1 + 2x²/3): 0 ≤ K₄ ≤ 1, 1 − K₄(x) = (11/45)x⁴ + O(x⁶), Fourier
      support 4/6 = 2/3 < 2 log(3/2) (the bound at N = 2), and η the least number with φ(s)(s² + 1/4) ≤ 1;
  λ(s) = λ₀ + Σ_k c_k(1 − sinc²(s/A_k)), c_k ≥ 0, A_k = (2/0.31)·1.2^k: Fourier support 0.31, so φλ has support
      0.977 < 1;
  r(s) = Σ_j b_j(sinc²((s − j/2)/2) + sinc²((s + j/2)/2)), b_j ≥ 0, centres j/2 ≤ s₁ + 4: Fourier support 1;
and linear programming chooses λ₀, c_k, b_j to maximise d, under λ ≤ g on s ≥ s₁ = 12 (with the elementary majorant
x²/3 − 2x⁴/45 + x⁶/315 of 1 − sinc²x, capped at 1) and φ(λ − g) ≤ r below s₁. In s the supports needed are below
N·log(1 + 1/N) for φ, which is at least 0.811, and below N·log(N/(N − 1)) for m, which exceeds 1, at every N ≥ 2.

It prints:
  1. φ: η and P;
  2. λ and r: d, the cost of r, and the largest violation of the pointwise condition on a fine grid (with the exact
     L(Ns) − log N at several N, and with the uniform g);
  3. the pole terms 2D(i/2)D(−i/2)Φ_N(i/2): the largest loss in d over N ≥ 2 (Cauchy–Schwarz);
  4. sup_x (M(x) − log x), which must stay below d for the Schur test, and the minimum of P·Λ(N, d)/d_1 over
     2 ≤ N ≤ 10⁶, with θ = max_q Λ(q)/(q(d + log q − M(q − 1))) and the uniform bound Λ(N, d) ≥ (1 − θ)log N + d;
  5. with --true, the bound against the true pivots for N ≤ 400 (computed from the primes, scripts/ball_orbit.py),
     with the exact minimum of the quadratic form in place of the Schur test;
  6. with --zeros M, the explicit formula as used above against the sum over the first M zeros (mpmath, slow), the
     zeros above the M-th by their density and Landau's drift −(T/2π)Λ(q)/√q.

    python3 scripts/pivot_push.py [--true] [--zeros M]   # needs numpy and scipy (and mpmath for --zeros)
"""

import math
import os
import sys

import numpy as np
from scipy.optimize import linprog
from scipy.special import digamma

D1 = 2 + 0.5772156649015329 - math.log(4 * math.pi)
A_PHI = 6.0           # φ's scale: Fourier support 4/A_PHI
SUPP_LAMBDA = 0.31    # λ's Fourier support
S1 = 12.0             # λ ≤ g from here on; r pays below
SHIFT = 1e-5          # safety: λ₀ lowered by this much after the linear program


def L_arch(t):
    """L(t) = Re ψ(1/4 + it/2) − log π."""
    return np.real(digamma(0.25 + 0.5j * np.asarray(t, float))) - math.log(math.pi)


def sinc(x):
    x = np.asarray(x, float)
    out = np.ones_like(x)
    nz = np.abs(x) > 1e-8
    out[nz] = np.sin(x[nz]) / x[nz]
    return out


def grid():
    return np.unique(np.concatenate([[0.0], np.geomspace(1e-4, 1, 200), np.arange(1, 40, 0.01),
                                     np.arange(40, 600, 0.1), np.arange(600, 5000, 1.0), np.geomspace(5000, 1e6, 1500)]))


def weights(s):
    w = np.zeros_like(s)
    w[1:-1] = (s[2:] - s[:-2]) / 2
    w[0] = (s[1] - s[0]) / 2
    w[-1] = (s[-1] - s[-2]) / 2
    return w


def one_minus_K4(x):
    x = np.abs(np.asarray(x, float))
    k4 = sinc(x) ** 4 * (1 + 2 * x ** 2 / 3)
    return np.where(x < 1e-3, (11 / 45) * x ** 4, 1 - k4)


def phi_raw(s):
    s = np.abs(np.asarray(s, float))
    return np.where(s == 0, 0.0, one_minus_K4(s / A_PHI) / np.where(s == 0, 1, s ** 2))


def E_sup(s):
    """E(s) = sup_{t ≥ 2s} (log(t/2π) − L(t))⁺: the archimedean deficit for every N ≥ 2."""
    t = np.geomspace(1e-3, 1e7, 200000)
    e = np.maximum(np.log(t / (2 * math.pi)) - L_arch(t), 0.0)
    sm = np.maximum.accumulate(e[::-1])[::-1]
    return np.interp(np.maximum(2 * np.asarray(s, float), 1e-3), t, sm)


def u_major(x):
    """An elementary majorant of 1 − sinc²(x): the Taylor polynomial x²/3 − 2x⁴/45 + x⁶/315 below 2.9, then 1."""
    return np.minimum(1.0, np.where(x < 2.9, x ** 2 / 3 - 2 * x ** 4 / 45 + x ** 6 / 315, 1.0))


def bump(c, s):
    return sinc(s / 2) ** 2 if c == 0 else sinc((s - c) / 2) ** 2 + sinc((s + c) / 2) ** 2


class Design:
    """φ, λ = λ₀ + Σ c_k(1 − sinc²(s/A_k)) and r = Σ b_j·bump(j/2), from the linear program."""

    def __init__(self, ratio=1.2, bump_step=0.5):
        s = grid()
        ph = phi_raw(s)
        self.eta = max(0.0, 1 - 1 / np.max(ph * (s ** 2 + 0.25)))
        ph = (1 - self.eta) * ph
        w = weights(s)
        self.Iphi = 2 * (w @ ph + (1 - self.eta) / s[-1])
        self.P = self.Iphi / (2 * math.pi)
        g = np.log(np.where(s == 0, 1e-300, s) / (2 * math.pi)) - E_sup(s)
        self.As = (2.0 / SUPP_LAMBDA) * ratio ** np.arange(0, 60)
        Bt = np.array([np.ones_like(s)] + [1 - sinc(s / a) ** 2 for a in self.As]).T
        Bm = np.array([np.ones_like(s)] + [u_major(s / a) for a in self.As]).T
        self.cs = np.arange(0, S1 + 4 + 1e-9, bump_step)
        F = np.array([bump(c, s) for c in self.cs]).T
        self.Fint = np.array([2 * math.pi if c == 0 else 4 * math.pi for c in self.cs])
        nl, nb = Bt.shape[1], len(self.cs)
        lo = (s < S1) & (ph > 0)
        hi = s >= S1
        obj = np.concatenate([-(2 * (w * ph) @ Bt + 2 * (1 - self.eta) / s[-1]), self.Fint])
        Aub = np.vstack([np.hstack([ph[lo][:, None] * Bm[lo], -F[lo]]),          # s < s₁: φ(λ − g) ≤ r
                         np.hstack([Bm[hi], np.zeros((hi.sum(), nb))])])         # s ≥ s₁: λ ≤ g
        bub = np.concatenate([ph[lo] * g[lo], g[hi]])
        res = linprog(obj, A_ub=Aub, b_ub=bub, bounds=[(None, None)] + [(0, None)] * (nl - 1 + nb), method="highs")
        assert res.status == 0, res.message
        self.lam_c, self.b = res.x[:nl].copy(), res.x[nl:]
        self.lam_c[0] -= SHIFT
        self.d = -res.fun / self.Iphi - SHIFT
        self.rint = self.b @ self.Fint

    def phi(self, s):
        return (1 - self.eta) * phi_raw(s)

    def lam(self, s):
        return self.lam_c[0] + sum(c * (1 - sinc(s / a) ** 2) for c, a in zip(self.lam_c[1:], self.As) if c > 0)

    def r(self, s):
        return sum(bj * bump(c, s) for c, bj in zip(self.cs, self.b) if bj > 0)

    def phi_imag(self, y):
        """|φ(iy)| = (1 − η)(1 − K₄(iy/6))/y², K₄(ix) = (sinh x/x)⁴(1 − 2x²/3)."""
        x = y / A_PHI
        sh = math.sinh(x) / x if x > 1e-4 else 1 + x * x / 6 + x ** 4 / 120
        one_m = 1 - sh ** 4 * (1 - 2 * x * x / 3) if x > 1e-2 else (11 / 45) * x ** 4
        return (1 - self.eta) * one_m / y ** 2


def verify(D):
    """The largest value of φ(λ − ĝ) − r on a fine grid, ĝ the exact L(Ns) − log N or the uniform g."""
    x = np.concatenate([np.linspace(0, 50, 500001)[1:], np.linspace(50, 2000, 400001)[1:],
                        np.geomspace(2000, 1e7, 200001)[1:]])
    phx, lx, rx = D.phi(x), D.lam(x), D.r(x)
    out = []
    for N in [2, 3, 5, 10, 100, 10 ** 4, 10 ** 6]:
        out.append((N, float(np.max(phx * (lx - (L_arch(N * x) - math.log(N))) - rx))))
    gx = np.log(x / (2 * math.pi)) - E_sup(x)
    return out, float(np.max(phx * (lx - gx) - rx))


def pole_loss(D, Nmax=10 ** 4):
    """max over 2 ≤ N ≤ Nmax of (N/P)·2|Φ_N(i/2)|·√(Σ_{n≤N} n·Σ_{n≤N} 1/n), Φ_N(i/2) = φ(i/2N)/N²."""
    best, H = (0.0, None), 1.0
    for N in range(2, Nmax + 1):
        H += 1 / N
        delta = (N / D.P) * 2 * D.phi_imag(1 / (2 * N)) / N ** 2 * math.sqrt(N * (N + 1) / 2 * H)
        best = max(best, (delta, N))
    return best


def mertens_table(X):
    lam = np.zeros(X + 1)
    comp = np.zeros(X + 1, bool)
    spf = np.zeros(X + 1, dtype=np.int64)
    for p in range(2, X + 1):
        if not comp[p]:
            comp[2 * p::p] = True
            spf[p::p] = np.where(spf[p::p] == 0, p, spf[p::p])
            q = p
            while q <= X:
                lam[q] = math.log(p)
                q *= p
    n = np.arange(X + 1, dtype=float)
    n[0] = 1
    return lam, np.cumsum(lam / n), spf


def schur(N, d, lam, M, spf):
    pen, m = 0.0, N
    while m > 1:
        p = int(spf[m])
        qq = p
        while m % p == 0:
            pen += (lam[qq] ** 2 / qq) / (d + math.log(qq) - M[qq - 1])
            m //= p
            qq *= p
    return math.log(N) + d - pen


def scan(P, d, X=10 ** 6):
    lam, M, spf = mertens_table(X)
    q = np.arange(2, X + 1)
    isq = lam[2:] > 0
    room = d + np.log(q) - M[1:-1]                 # room at the parent N/q: d + log q − M(q − 1)
    theta = np.max((lam[2:] / (q * room))[isq])
    excess = np.max(M[1:] - np.log(np.arange(1, X + 1)))
    worst = (math.inf, None)
    for N in range(2, X + 1):
        r = P * schur(N, d, lam, M, spf) / D1
        if r < worst[0]:
            worst = (r, N)
    return worst, theta, excess


def landau_min(N, d, lam):
    """min over c with c_N = 1 of (log N + d)Σc² − L(c), exactly."""
    A = np.zeros((N, N))
    for j in range(1, N + 1):
        for q in range(2, N // j + 1):
            if lam[q] > 0:
                A[j - 1, j * q - 1] = A[j * q - 1, j - 1] = lam[q] / math.sqrt(q)
    F = (math.log(N) + d) * np.eye(N) - A
    return F[-1, -1] - F[:-1, -1] @ np.linalg.solve(F[:-1, :-1], F[:-1, -1])


def against_true(P, d, Nmax=400):
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import ball_orbit
    piv = ball_orbit.pivots(ball_orbit.gram(Nmax))
    lam, M, spf = mertens_table(Nmax)
    print("     N   d_N/d_1   bound (exact form)   bound (Schur test)")
    worst = 0.0
    for N in range(2, Nmax + 1):
        be = P * landau_min(N, d, lam)
        worst = max(worst, be / piv[N - 1])
        if N <= 12 or N in (30, 60, 100, 210, 400):
            print(f"  {N:4d}   {piv[N - 1] / D1:7.3f}   {be / D1:10.3f}          {P * schur(N, d, lam, M, spf) / D1:10.3f}")
    print(f"  the bound is below the true pivot for every N ≤ {Nmax}; the largest ratio is {worst:.3f}")


def against_zeros(D, Mz):
    import mpmath
    mpmath.mp.dps = 20
    g = np.array([float(mpmath.zetazero(n).imag) for n in range(1, Mz + 1)])
    T = g[-1]
    lam, _, _ = mertens_table(64)
    rng = np.random.default_rng(1)
    print(f"  {Mz} zeros, up to height {T:.0f}")
    for N in [1, 2, 3, 4, 6]:
        c = rng.normal(size=N)
        n = np.arange(1, N + 1)

        def D2(t):
            return np.abs(np.exp(-1j * np.outer(np.asarray(t, float), np.log(n))) @ c) ** 2

        def Phi(t):
            return D.phi(np.asarray(t, float) / N) / N ** 2

        Lc = 2 * sum(lam[q] / math.sqrt(q) * c[j - 1] * c[q * j - 1] for q in range(2, N + 1) for j in range(1, N // q + 1))
        X = 2e5
        tt = np.arange(T, X, 0.01)
        tail = np.trapezoid(D2(tt) * Phi(tt) * np.log(tt / (2 * math.pi)), tt) / (2 * math.pi)
        tail += c @ c * (math.log(X / (2 * math.pi)) + 1) / (2 * math.pi * X)
        drift = Lc / (2 * math.pi) * (np.trapezoid(Phi(tt), tt) + 1 / X)
        zeros = 2 * (np.sum(D2(g) * Phi(g)) + tail) - 2 * drift
        t = np.concatenate([np.arange(0, 2000, 0.002), np.arange(2000, X, 0.05)])
        arch = 2 * np.trapezoid(D2(t) * Phi(t) * L_arch(t), t) / (2 * math.pi)
        arch += 2 * (c @ c) * (math.log(X / (2 * math.pi)) + 1) / X / (2 * math.pi)
        pole = -2 * (c @ np.sqrt(n)) * (c @ (1 / np.sqrt(n))) * D.phi_imag(1 / (2 * N)) / N ** 2
        formula = pole + arch - D.P / N * Lc
        print(f"  N = {N}: zeros {zeros:.7f}   formula {formula:.7f}   (pole {pole:.1e}, Landau {D.P / N * Lc:+.5f})")


def main(argv):
    D = Design()
    print(f"φ = (1 − η)(1 − K₄(s/6))/s²: Fourier support 2/3, η = {D.eta:.2e}, P = ∫φ/2π = {D.P:.5f}")
    nst = int((D.lam_c[1:] > 1e-9).sum())
    print(f"λ (support {SUPP_LAMBDA}, {nst} steps, λ₀ = {D.lam_c[0]:.4f}) and r ({int((D.b > 0).sum())} bumps at "
          f"{', '.join(f'{c:g}' for c in D.cs[D.b > 0])}): d = {D.d:.4f}, of which r costs {D.rint / D.Iphi:.4f}")
    per_N, unif = verify(D)
    print("largest φ(λ − (L(Ns) − log N)) − r on a fine grid: "
          + ", ".join(f"N = {N}: {v:.1e}" for N, v in per_N) + f"; with the uniform g: {unif:.1e}")
    delta, Nd = pole_loss(D)
    d = D.d - delta
    print(f"pole terms: the loss in d is at most {delta:.1e} (at N = {Nd}); d_eff = {d:.4f}")
    worst, theta, excess = scan(D.P, d)
    print(f"sup_x (M(x) − log x) = {excess:.3f} < d (x ≤ 10⁶)")
    print(f"min over 2 ≤ N ≤ 10⁶ of P·Λ(N, d)/d_1 = {worst[0]:.4f} at N = {worst[1]}")
    print(f"θ = max_q Λ(q)/(q(d + log q − M(q − 1))) = {theta:.4f}, so Λ(N, d) ≥ {1 - theta:.4f}·log N + d, and "
          f"P·({1 - theta:.4f}·log 2 + d)/d_1 = {D.P * ((1 - theta) * math.log(2) + d) / D1:.4f}")
    print(f"against BallPivot.pivot_ge: constant P = {D.P:.4f} in place of 1/(22e⁸) = {1 / (22 * math.exp(8)):.2e}, "
          f"diagonal log N + {d:.2f} in place of log N/2 + 3.39")
    if "--true" in argv:
        against_true(D.P, d)
    if "--zeros" in argv:
        i = argv.index("--zeros")
        against_zeros(D, int(argv[i + 1]) if i + 1 < len(argv) else 500)


if __name__ == "__main__":
    main(sys.argv[1:])
