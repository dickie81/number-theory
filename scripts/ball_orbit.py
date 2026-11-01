"""The orbit of the Hadamard kernel as a lattice: its Gram–Schmidt pivots, computed from the primes.

A numerical experiment for the sixth first step of docs/ball-conjecture.md. It is not a check, and CI does not run it.

In a realization of K_H(r) = Σ_ρ r^{ρ−½}/(ρ(1−ρ)) by similitudes (BallLattice.Realization), the vectors w_1, w_2, …
have the Gram matrix ⟨w_n, w_m⟩ = √(mn)·K_H(m/n) (BallPsi.gram_explicit). This script computes K_H from the primes,
for x ≥ 1, by

    K_H(x) = √x·(Σ_{n ≤ x} Λ(n)(1/n − 1/x) − log x + 1 + γ − log(2π)/x + Σ_{k ≥ 1} x^{−2k−1}/(2k(2k + 1))).

This is BallPsi.kerH_explicit with its archimedean term in closed form. The closed form is checked numerically against
the integral that defines BallPsi.archH, and is not proved. The script prints the squared Gram–Schmidt norms
d_k = dist(w_k, span(w_1, …, w_{k−1}))² relative to d_1 = ‖w_1‖² = K_H(1) = 2 + γ − log 4π. If d_k ≥ d_1 for every k,
then w_1 is a shortest nonzero vector of the lattice that the orbit spans (BallPsi.orbit_lattice).

    python3 scripts/ball_orbit.py [N]           # default N = 1000; needs numpy
    python3 scripts/ball_orbit.py --smooth [N]  # the zeros replaced by their density, no primes; needs scipy
    python3 scripts/ball_orbit.py --flat [N]    # the Gram matrix against the flat model d_1·min(m, n)
    python3 scripts/ball_orbit.py --zeros [M]   # which zeros carry d_k, from the first M zeros; needs mpmath, slow
    python3 scripts/ball_orbit.py --places [N]  # the Gram matrix as a sum over the places, and its rigidity
    python3 scripts/ball_orbit.py --weil [N]    # the intersection numbers D_m·D_n of BallWeil and the Weil bound
    python3 scripts/ball_orbit.py --forward [N] # local pieces, reduced basis, and the coupling between the primes
    python3 scripts/ball_orbit.py --slices [X]  # the lattice of the numbers built from a fixed set of primes
    python3 scripts/ball_orbit.py --lattice [N] # the Gram matrix as a form over the logarithms of the primes

The first three options are the computations of "What a proof under RH would need" in docs/ball-conjecture.md,
--places, --forward and --slices those of "Building the lattice forwards", --weil that of "Weil's form", and --lattice
that of "The limit and the lattice".
"""

import math
import sys

import numpy as np

EULER_GAMMA = 0.57721566490153286060651209


def tables(X):
    """Σ_{n ≤ k} Λ(n)/n and ψ(k) = Σ_{n ≤ k} Λ(n), for k ≤ X."""
    lam = np.zeros(X + 1)
    composite = np.zeros(X + 1, dtype=bool)
    for p in range(2, X + 1):
        if not composite[p]:
            composite[2 * p::p] = True
            pk = p
            while pk <= X:
                lam[pk] = math.log(p)
                pk *= p
    n = np.arange(X + 1, dtype=float)
    n[0] = 1.0
    return np.cumsum(lam / n), np.cumsum(lam)


def kernel_over_sqrt(x, A, B):
    """K_H(x)/√x for an array of x ≥ 1."""
    k = np.floor(x + 1e-12).astype(np.int64)
    y = 1.0 / x
    # Σ_{k ≥ 1} y^{2k+1}/(2k(2k+1)) = y + ½(1 − y)log(1 − y) − ½(1 + y)log(1 + y)
    with np.errstate(divide="ignore", invalid="ignore"):
        t = np.where(y < 1, 0.5 * (1 - y) * np.log1p(-np.minimum(y, 1 - 1e-300)), 0.0)
    tail = y + t - 0.5 * (1 + y) * np.log1p(y)
    return A[k] - B[k] / x - np.log(x) + 1 + EULER_GAMMA - math.log(2 * math.pi) / x + tail


def gram(N):
    """The matrix (⟨w_n, w_m⟩)_{m,n ≤ N} = (max(m, n)·K_H(max/min)/√(max/min))."""
    A, B = tables(N + 1)
    m = np.arange(1, N + 1, dtype=float)
    M, Nn = np.meshgrid(m, m, indexing="ij")
    hi, lo = np.maximum(M, Nn), np.minimum(M, Nn)
    return hi * kernel_over_sqrt(hi / lo, A, B)


def pivots(G):
    """The squared Gram–Schmidt norms d_k, from the Cholesky factor."""
    return np.diag(np.linalg.cholesky(G)) ** 2


def smooth(N):
    """Pivots with the zeros replaced by their density (1/2π)log(|γ|/2π) on |γ| ≥ 2π, against the true ones."""
    from fractions import Fraction
    from scipy.integrate import quad
    dens = lambda t: math.log(t / (2 * math.pi)) / (2 * math.pi) / (0.25 + t * t)
    cache = {}

    def K(x):
        u = abs(math.log(x))
        if u == 0:
            return 2 * quad(dens, 2 * math.pi, np.inf, limit=500)[0]
        return 2 * quad(dens, 2 * math.pi, np.inf, weight="cos", wvar=u, limlst=200)[0]

    S = np.zeros((N, N))
    for m in range(1, N + 1):
        for n in range(1, N + 1):
            f = Fraction(max(m, n), min(m, n))
            if f not in cache:
                cache[f] = K(f.numerator / f.denominator)
            S[m - 1, n - 1] = math.sqrt(m * n) * cache[f]
    ds, dt = pivots(S), pivots(gram(N))
    print(f"N = {N}: d_1 = {ds[0]:.5f} with the density, {dt[0]:.5f} with the zeros")
    print("    k   d_k/d_1 (density)   d_k/d_1 (zeros)   ratio")
    for k in range(2, N + 1):
        rs, rt = ds[k - 1] / ds[0], dt[k - 1] / dt[0]
        print(f"  {k:3d}   {rs:12.3f}   {rt:14.3f}   {rt / rs:7.3f}")


def flat(N):
    """The Gram matrix against the flat model d_1·min(m, n), and the combination Σ w_m/m."""
    for n in [5, 10, 30, 100, 300, N]:
        if n > N:
            continue
        G = gram(n)
        m = np.arange(1, n + 1)
        F = G[0, 0] * np.minimum.outer(m, m).astype(float)
        a = 1.0 / m
        print(f"N = {n:5d}: smallest eigenvalue of G − d_1·min(m, n) = {np.linalg.eigvalsh(G - F)[0]: .3e}; "
              f"‖Σ w_m/m‖² = {a @ G @ a:.4f}, flat model {a @ F @ a:.4f}")


def zeros(M):
    """For each k, the share of d_k carried by the zeros in bands of height, from the first M zeros."""
    import mpmath
    mpmath.mp.dps = 20
    g = np.array([float(mpmath.zetazero(n).imag) for n in range(1, M + 1)])
    print(f"{M} zeros, up to height {g[-1]:.0f}; d_k from the zeros (both signs) against the explicit formula")
    print("    k   d_k/d_1   zeros/explicit   share of d_k from heights  < πk   πk–4πk   4πk–16πk   > 16πk")
    kmax = int(g[-1] / (16 * math.pi))
    for k in range(2, kmax + 1):
        G = gram(k)
        c = np.linalg.solve(G[:k - 1, :k - 1], G[:k - 1, k - 1])
        dk = G[k - 1, k - 1] - G[:k - 1, k - 1] @ c
        j = np.arange(1, k + 1, dtype=float)
        coef = np.concatenate([-c, [1.0]]) * np.sqrt(j)
        err = np.abs(np.exp(1j * np.outer(g, np.log(j))) @ coef) ** 2 / (0.25 + g ** 2)
        tot = 2 * err.sum()
        bands = [g < math.pi * k, (g >= math.pi * k) & (g < 4 * math.pi * k),
                 (g >= 4 * math.pi * k) & (g < 16 * math.pi * k), g >= 16 * math.pi * k]
        shares = "   ".join(f"{2 * err[b].sum() / tot:6.1%}" for b in bands)
        print(f"  {k:3d}   {dk / G[0, 0]:7.3f}   {tot / dk:10.3f}        {shares}")


def primes_upto(X):
    sieve = np.ones(X + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(X ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return [int(p) for p in np.nonzero(sieve)[0]]


def places_gram(N, lam):
    """The Gram matrix from the closed form, for a given von Mangoldt table lam: for m ≥ n,
    G(m, n) = Σ_{k ≤ m/n} Λ(k)(m/k − n)                                   (the primes)
              + (m + n) + γm − n log 2π + m log n − (m − n)log m
              + ½(m − n)log(m − n) − ½(m + n)log(m + n)                    (the archimedean place)."""
    G = np.zeros((N, N))
    for m in range(1, N + 1):
        for n in range(1, m + 1):
            a = (m + n) + EULER_GAMMA * m - math.log(2 * math.pi) * n + m * math.log(n) - (m - n) * math.log(m)
            a += (0.5 * (m - n) * math.log(m - n) if m > n else 0.0) - 0.5 * (m + n) * math.log(m + n)
            a += sum(lam[k] * (m / k - n) for k in range(2, m // n + 1))
            G[m - 1, n - 1] = G[n - 1, m - 1] = a
    return G


def places(N):
    """The Gram matrix as the archimedean part plus a part for each prime, and how its positivity needs every prime."""
    def table(drop=(), add=None, scale=None):
        lam = np.zeros(N + 1)
        for p in primes_upto(N):
            if p in drop:
                continue
            q = p
            while q <= N:
                lam[q] = math.log(p) * (scale.get(p, 1.0) if scale else 1.0)
                q *= p
        for k, v in (add or {}).items():
            lam[k] += v
        return lam
    G = places_gram(N, table())
    print(f"N = {N}: the sum over the places reproduces the Gram matrix to {np.abs(G - gram(N)).max():.1e}")
    P = primes_upto(N)
    e0 = np.linalg.eigvalsh(places_gram(N, np.zeros(N + 1)))[0]
    print(f"  smallest eigenvalue with the archimedean part only: {e0: .3e}")
    for k in range(len(P)):
        e = np.linalg.eigvalsh(places_gram(N, table(drop=set(P[k + 1:]))))[0]
        print(f"  with the primes up to {P[k]:4d}: {e: .3e}")
    primes = set(P)
    powers = {p ** j for p in P for j in range(2, 7)}
    fake = max(k for k in range(9, N + 1, 2) if k not in primes and k not in powers)
    tests = [(f"without the prime {P[-1]}", table(drop={P[-1]})),
             (f"with a fake prime {fake}", table(add={fake: math.log(fake)})),
             ("log 2 off by 0.1%", table(scale={2: 1.001})),
             ("log 2 off by 0.01%", table(scale={2: 1.0001}))]
    for name, lam in tests:
        print(f"  {name:28s}: {np.linalg.eigvalsh(places_gram(N, lam))[0]: .3e}")


def weil(N):
    """The intersection numbers D_m·D_n = m + n − √(mn)·K_H(m/n) of BallWeil against the Weil bound
    |D_m·D_n − m − n| ≤ K_H(1)·√(mn), that is |K_H(m/n)| ≤ K_H(1)."""
    G = gram(N)
    c0 = G[0, 0]
    m = np.arange(1, N + 1, dtype=float)
    R = G / (c0 * np.sqrt(np.outer(m, m)))
    np.fill_diagonal(R, np.nan)
    def at(ij):
        a, b = ij[0] + 1, ij[1] + 1
        g = math.gcd(a, b)
        return f"{R[ij]:.4f} at m/n = {a // g}/{b // g}"
    lo = np.unravel_index(np.nanargmin(R), R.shape)
    hi = np.unravel_index(np.nanargmax(R), R.shape)
    print(f"N = {N}: D_1·D_1 = 2 − K_H(1) = {2 - c0:.6f}, so K_H(1) = {c0:.6f} plays 2g")
    print(f"  over m ≠ n ≤ N, K_H(m/n)/K_H(1) runs from {at(lo)} to {at(hi)}")
    print("  the Weil bound asks for [−1, 1]; the lower end alone gives RH (BallWeil.rh_iff_weil_bound)")
    for n in [2, 3, 5, 10, 100, 1000, 10000]:
        if n <= N:
            d = n + 1 - G[n - 1, 0]
            print(f"  D_{n}·D_1 = {d:13.6f}   (D_n·D_1 − n − 1)/(K_H(1)·√n) = {(d - n - 1) / (c0 * math.sqrt(n)):+.4f}")


def lll(G, delta=0.99):
    """LLL reduction of the lattice with Gram matrix G: an integer matrix B whose rows are the coefficients of the
    reduced basis in the original one, and the reduced Gram matrix B·G·Bᵀ."""
    n = G.shape[0]
    B = np.eye(n, dtype=np.int64)

    def gso(H):
        L = np.linalg.cholesky(H)
        return L / np.diag(L)[None, :], np.diag(L) ** 2

    H = G.copy()
    k = 1
    while k < n:
        mu, d = gso(H)
        for j in range(k - 1, -1, -1):
            q = round(mu[k, j])
            if q:
                B[k] -= q * B[j]
                H = B @ G @ B.T
                mu, d = gso(H)
        if d[k] >= (delta - mu[k, k - 1] ** 2) * d[k - 1]:
            k += 1
        else:
            B[[k - 1, k]] = B[[k, k - 1]]
            H = B @ G @ B.T
            k = max(k - 1, 1)
    return B, H


def hadamard_ratio(H):
    """(det H)^(1/2n) over the geometric mean of the norms: 1 exactly for an orthogonal basis."""
    sign, logdet = np.linalg.slogdet(H)
    return math.exp(logdet / (2 * H.shape[0]) - 0.5 * np.log(np.diag(H)).mean())


def divisor_sums(N):
    """The rows of the change of basis w ↦ u, u_n = Σ_{d | n} w_d."""
    T = np.zeros((N, N))
    for n in range(1, N + 1):
        T[n - 1, [d - 1 for d in range(1, n + 1) if n % d == 0]] = 1
    return T


def independent(N):
    """The orbit's Gram matrix with independent prime directions: √(mn)·K_H(1)·Π_p κ_p(v_p(m) − v_p(n)), with the
    exact one-prime values κ_p(j) = K_H(p^|j|)/K_H(1). It is the Gram matrix of the tensor product of the lattices of
    the single primes, and positive definite when each of them is."""
    A, B = tables(N + 1)
    c0 = 2 + EULER_GAMMA - math.log(4 * math.pi)
    n = np.arange(1, N + 1)
    P = np.ones((N, N))
    for p in primes_upto(N):
        v = np.zeros(N, dtype=int)
        q = p
        while q <= N:
            v[n % q == 0] += 1
            q *= p
        x = np.array([float(p) ** j for j in range(1, v.max() + 1)])
        kap = np.concatenate([[1.0], kernel_over_sqrt(x, A, B) * np.sqrt(x) / c0])
        P *= kap[np.abs(v[:, None] - v[None, :])]
    return c0 * np.sqrt(np.outer(n, n).astype(float)) * P


def forward(N):
    """What a construction of the vectors place by place meets: the local pieces C_p are indefinite; making them
    positive leaves an indefinite rest; the reduced basis is made of divisor sums; and the prime directions are coupled
    by the real place, which cuts the pivots far below those of independent prime directions."""
    n0 = 60
    G = gram(n0)
    m = np.arange(1, n0 + 1, dtype=float)
    M, Nn = np.meshgrid(m, m, indexing="ij")
    hi, lo = np.maximum(M, Nn), np.minimum(M, Nn)
    A, B = tables(1000)
    c0 = G[0, 0]
    lam = np.diff(B, prepend=0.0)          # Λ(k) for k ≤ 1000
    print(f"1. At N = {n0}, each prime's piece C_p of the sum over the places is indefinite (its diagonal is 0):")
    for p in primes_upto(13):
        C = np.zeros((n0, n0))
        q = p
        while q <= n0:
            C += np.where(hi / q > lo, hi / q - lo, 0.0)
            q *= p
        e = np.linalg.eigvalsh(C)
        print(f"   p = {p:2d}: eigenvalues from {e[0]:9.3f} to {e[-1]:8.3f}")
    print(f"2. The positive pieces (Λ(k)/√k)·Gram(1_[0,n] − √k·1_[0,n/k]) over the prime powers k ≤ X leave a rest")
    print(f"   whose smallest eigenvalue is (the whole matrix has {np.linalg.eigvalsh(G)[0]:.2e}):")
    for X in [1, 2, 5, 10, 60, 1000]:
        S = np.zeros((n0, n0))
        for k in range(2, X + 1):
            if lam[k] > 0:
                S += lam[k] / math.sqrt(k) * (2 * lo - math.sqrt(k) * (np.minimum(M, Nn / k) + np.minimum(M / k, Nn)))
        print(f"   X = {X:4d}: {np.linalg.eigvalsh(G - S)[0]: .3e}")
    print("3. K_H(r)/K_H(1), against the value −1/(2√r) below which w_n + w_{n/r} is shorter than w_n:")
    for r in [2, 3, 5, 7, 4, 8, 9, 6, 10, 1.5, 2.5, 3.5]:
        k = float(kernel_over_sqrt(np.array([float(r)]), A, B)[0] * math.sqrt(r) / c0)
        print(f"   r = {r:4}: {k:+.3f}   (−1/(2√r) = {-0.5 / math.sqrt(r):+.3f})")
    Bl, H = lll(gram(40))
    order = np.argsort(np.diag(H))
    print("   the shortest vectors of the LLL-reduced basis at N = 40, squared norms in units of K_H(1):")
    for i in order[:12]:
        c = Bl[i] if Bl[i][np.nonzero(Bl[i])[0][-1]] > 0 else -Bl[i]
        terms = " ".join(f"{'+' if v > 0 else '−'}{abs(v) if abs(v) != 1 else ''}w{j + 1}"
                         for j, v in enumerate(c) if v)
        print(f"   {H[i, i] / c0:7.3f}   {terms}")
    print("   Hadamard ratios (1 for an orthogonal basis) of the bases w_n, w_n − w_{n−1}, Σ_{d|n} w_d and LLL's:")
    for n1 in [40, 100, 200]:
        G1 = gram(n1)
        I = np.eye(n1) - np.eye(n1, k=-1)
        T = divisor_sums(n1)
        print(f"   N = {n1:3d}: {hadamard_ratio(G1):.3f}, {hadamard_ratio(I @ G1 @ I.T):.3f}, "
              f"{hadamard_ratio(T @ G1 @ T.T):.3f}, {hadamard_ratio(lll(G1)[1]):.3f}")

    def kr(r):
        x = max(r, 1 / r)
        return float(kernel_over_sqrt(np.array([x]), A, B)[0] * math.sqrt(x) / c0)
    print("4. Independent prime directions would make K_H(ab) = K_H(a/b) = K_H(a)K_H(b)/K_H(1) for coprime a, b:")
    for a, b in [(2, 3), (2, 5), (3, 5), (2, 7), (4, 3), (2, 9)]:
        print(f"   a = {a}, b = {b}: K(ab) {kr(a * b):+.3f}, K(a/b) {kr(a / b):+.3f}, K(a)K(b) {kr(a) * kr(b):+.3f}"
              "  (in units of K_H(1))")
    G, Gi = gram(N), independent(N)
    d, di = pivots(G) / c0, pivots(Gi) / c0
    P = set(primes_upto(N))
    isp = np.array([k in P for k in range(1, N + 1)])
    r = d / di
    print(f"   N = {N}: pivots d_k/d_1 with the true Gram matrix and with independent prime directions:")
    for k in [2, 3, 5, 10, 30, 100, 300, 1000, 3000]:
        if k <= N:
            print(f"   k = {k:4d}: {d[k - 1]:9.3f}  {di[k - 1]:9.3f}   ratio {r[k - 1]:.3f}")
    print(f"   the smallest is {d[1:].min():.3f} at k = {2 + int(np.argmin(d[1:]))} in both"
          if np.argmin(d[1:]) == np.argmin(di[1:]) else "   the smallest pivots differ")
    print(f"   median ratio {np.median(r[1:]):.3f}: {np.median(r[isp]):.3f} at the primes, "
          f"{np.median(r[~isp][1:]):.3f} at the composites")


def smooth_numbers(S, X):
    """The numbers up to X whose prime factors all lie in S, in increasing order."""
    out = [1]
    for p in S:
        new = []
        for n in out:
            while n <= X:
                new.append(n)
                n *= p
        out = new
    return sorted(out)


def slices(X):
    """The orbit lattice restricted to the S-smooth numbers: the directions of the primes of S alone."""
    A, B = tables(X)
    c0 = 2 + EULER_GAMMA - math.log(4 * math.pi)

    def gram_on(ns):
        n = np.array(ns, dtype=float)
        hi, lo = np.maximum.outer(n, n), np.minimum.outer(n, n)
        return hi * kernel_over_sqrt(hi / lo, A, B)

    def kappa(r):
        """K_H(r)/K_H(1) for r ≥ 1."""
        return float(kernel_over_sqrt(np.array([float(r)]), A, B)[0] * math.sqrt(r) / c0)

    def g_local(x, S):
        """G(x, 1) with only the primes of S in the explicit formula: G_∞(x, 1) + Σ_{S-powers k ≤ x} Λ(k)(x/k − 1)."""
        t = 0.5 * (x - 1) * np.log(np.maximum(x - 1, 1e-300)) * (x > 1)
        out = ((x + 1) + EULER_GAMMA * x - math.log(2 * math.pi) - (x - 1) * np.log(x) + t
               - 0.5 * (x + 1) * np.log(x + 1))
        for p in S:
            q = p
            while q <= x.max():
                out = out + np.where(x >= q, math.log(p) * (x / q - 1), 0.0)
                q *= p
        return out

    def valuations(ns, S):
        V = np.zeros((len(ns), len(S)), dtype=int)
        for i, n in enumerate(ns):
            for j, p in enumerate(S):
                while n % p == 0:
                    n //= p
                    V[i, j] += 1
        return V

    def independent_on(ns, S):
        V = valuations(ns, S)
        P = np.ones((len(ns), len(ns)))
        for j, p in enumerate(S):
            D = np.abs(V[:, j][:, None] - V[:, j][None, :])
            P *= np.array([1.0] + [kappa(float(p) ** e) for e in range(1, D.max() + 1)])[D]
        n = np.array(ns, dtype=float)
        return c0 * np.sqrt(np.outer(n, n)) * P

    print(f"1. One prime, the slice {{p^j}} up to {X}: pivots d/d_1, and e = d(p^j)/(p^j·d_1), 1 for a free vector")
    for p in [2, 3, 5]:
        ns = smooth_numbers([p], X)
        d = pivots(gram_on(ns)) / c0
        e = d / np.array(ns, dtype=float)
        print(f"   p = {p}: K_H(p^j)/K_H(1) = " + ", ".join(f"{kappa(p ** j):+.3f}" for j in range(1, 5))
              + f", …; e from {e[1]:.3f} at j = 1 to {e[-1]:.3f} at j = {len(ns) - 1}")
        n = np.array(ns, dtype=float)
        hi, lo = np.maximum.outer(n, n), np.minimum.outer(n, n)
        GS = lo * g_local(hi / lo, [p])
        k = next((k for k in range(2, len(ns) + 1) if np.linalg.eigvalsh(GS[:k, :k])[0] < 0), None)
        print(f"          with only the prime {p} and the real place it is indefinite from p^j = {ns[k - 1]}"
              if k else f"          with only the prime {p} and the real place it stays positive")
    print("2. Two primes: the real place couples 2 and 3 through the near-coincidences of their powers")
    for a, b in [(3, 2), (8, 5), (19, 12)]:
        r = max(3 ** b / 2 ** a, 2 ** a / 3 ** b)
        print(f"   3^{b}/2^{a} = {3 ** b / 2 ** a:.5f}: cos(w_(3^{b}), w_(2^{a})) = {kappa(r):+.3f}, "
              f"with independent directions {kappa(2 ** a) * kappa(3 ** b):+.4f}")
    print("3. Growing sets of primes: the median of e over the top decade of each slice, true and with the primes of S")
    print("   independent, and the smallest pivot after w_1")
    for S, X0 in [([2], X), ([2, 3], X), ([2, 3, 5], X), ([2, 3, 5, 7], X), (primes_upto(13), X // 10),
                  (primes_upto(31), X // 50), (primes_upto(3000), 3000)]:
        ns = smooth_numbers(S, X0)
        n = np.array(ns, dtype=float)
        d = pivots(gram_on(ns)) / c0
        di = pivots(independent_on(ns, S)) / c0
        top = n >= X0 / 10
        lab = "{" + ", ".join(map(str, S)) + "}" if len(S) <= 4 else f"primes ≤ {S[-1]}"
        k = 1 + int(np.argmin(d[1:]))
        print(f"   {lab:15s} up to {X0:>7}: {len(ns):4d} vectors; e {np.median((d / n)[top]):.3f}, "
              f"independent {np.median((di / n)[top]):.3f}; smallest d/d_1 {d[k]:.3f} at n = {ns[k]}")


def valuation(p, n):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def local_part(p, m, n):
    """The rational coefficient Q_p(m, n) of log p in G(m, n): for m ≥ n,
    Σ_{j ≥ 1, p^j ≤ m/n} (m/p^j − n) + m·v_p(n) − (m − n)·v_p(m) + ½(m − n)·v_p(m − n) − ½(m + n)·v_p(m + n)."""
    from fractions import Fraction
    if m < n:
        m, n = n, m
    s = Fraction(0)
    q = p
    while q * n <= m:
        s += Fraction(m, q) - n
        q *= p
    s += m * valuation(p, n) - (m - n) * valuation(p, m) - Fraction(m + n, 2) * valuation(p, m + n)
    if m > n:
        s += Fraction(m - n, 2) * valuation(p, m - n)
    return s


def lattice(N):
    """The Gram matrix as a form over 1, γ, log 2π and the log p: for m ≥ n,
    G(m, n) = (1 + γ)(m + n) − (γ + log 2π)·n + Σ_p log p·Q_p(m, n), with Q_p rational (local_part), and the
    Frobenius at p, multiplication by p, a similitude of factor p: G(pm, pn) = p·G(m, n)."""
    G = gram(N)
    P = primes_upto(2 * N)
    err = 0.0
    for m in range(1, N + 1):
        for n in range(1, m + 1):
            rec = (1 + EULER_GAMMA) * (m + n) - (EULER_GAMMA + math.log(2 * math.pi)) * n
            rec += sum(math.log(p) * float(local_part(p, m, n)) for p in P if p <= m + n)
            err = max(err, abs(rec - G[m - 1, n - 1]))
    print(f"N = {N}: G(m, n) = (1 + γ)(m + n) − (γ + log 2π)·min(m, n) + Σ_p log p·Q_p(m, n) to {err:.1e}")
    den = sorted({local_part(p, m, n).denominator for p in [2, 3, 5] for m in range(1, 61) for n in range(1, 61)})
    print(f"  the denominators of Q_2, Q_3 and Q_5 for m, n ≤ 60: {den}")
    for p in [2, 3]:
        print(f"  Q_{p}(m, n) for m, n ≤ 6:")
        for m in range(1, 7):
            print("    " + "  ".join(f"{str(local_part(p, m, n)):>6}" for n in range(1, 7)))
    half = N // 2
    sim = max(abs(G[p * m - 1, p * n - 1] - p * G[m - 1, n - 1]) for p in [2, 3] for m in range(1, half // p + 1)
              for n in range(1, half // p + 1))
    print(f"  G(pm, pn) = p·G(m, n) for p = 2, 3 to {sim:.1e}: multiplication by p is a similitude of factor p")
    print("  the trace Tr(n) = G(n, 1) = √n·K_H(n) = n + 1 − D_n·D_1, for n = 1, …, 8:",
          ", ".join(f"{G[n - 1, 0]:+.4f}" for n in range(1, 9)))


def main():
    if len(sys.argv) > 1 and sys.argv[1].startswith("--"):
        arg = int(sys.argv[2]) if len(sys.argv) > 2 else None
        {"--smooth": lambda: smooth(arg or 60), "--flat": lambda: flat(arg or 1000),
         "--zeros": lambda: zeros(arg or 2000), "--places": lambda: places(arg or 60),
         "--weil": lambda: weil(arg or 1000), "--forward": lambda: forward(arg or 1000),
         "--slices": lambda: slices(arg or 10 ** 6), "--lattice": lambda: lattice(arg or 120)}[sys.argv[1]]()
        return
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    G = gram(N)
    d1 = G[0, 0]
    d = np.diag(np.linalg.cholesky(G)) ** 2 / d1
    k_min = 2 + int(np.argmin(d[1:]))
    print(f"N = {N}: ‖w_1‖² = K_H(1) = {d1:.12f}")
    print(f"  the Gram matrix is positive definite (Cholesky succeeded); smallest eigenvalue "
          f"{np.linalg.eigvalsh(G)[0]:.3e}")
    print(f"  min over 2 ≤ k ≤ {N} of d_k/d_1 = {d[1:].min():.4f}, at k = {k_min}")
    for k in [2, 3, 5, 10, 30, 100, 300, 1000, 2000, 3000, 5000]:
        if k <= N:
            print(f"  k = {k:>5}: d_k/d_1 = {d[k - 1]:9.3f}   d_k/(d_1·log²k) = {d[k - 1] / math.log(k) ** 2:.3f}")
    print("  so ±w_1 are the shortest nonzero vectors of the lattice spanned by w_1, …, w_N"
          if d[1:].min() > 1 else "  some d_k < d_1")


if __name__ == "__main__":
    main()
