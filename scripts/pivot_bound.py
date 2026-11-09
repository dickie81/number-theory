"""The Gram–Schmidt pivots of the orbit against the bound of BallPivot, and the top-vertex inequality.

A numerical experiment for the section "The pivots" of formalisations/ball-rate.md. It is not a check, and CI does not
run it. Floating point, uncertified.

The orbit's Gram matrix is G(m, n) = √(mn)·K_H(m/n), computed from the primes by scripts/ball_orbit.py. Its k-th
pivot is d_k = min{Q_k(x) : x_k = 1}, the squared distance of w_k from the span of w_1, …, w_{k−1} in a realization.
The orbit-lattice conjecture of docs/ball-conjecture.md is d_k ≥ d_1 = K_H(1) for every k.

For each k in a short list the script prints

    d_k, d_k/log k, u_k = log(k/2π) + 1 − γ (the squared distance from w_{k−1} alone, up to o(1)), d_k/u_k,
    the bound of BallPivot.pivot_ge (under RH), (log k/2 + log 4 + 2)/(22e⁸),
    and what the same argument gives from a sampling inequality with constant ρ and margin s,
        Q_N(x) ≥ (π/(4ρN))·((log N + s)Σc_n² − L(c)),  c_n = x_n√n,  L Landau's form:
        d_k ≥ (π/(4ρ))·(s + Σ_{q ∣ k}Λ(q)·g/(g + Λ(q)/q)),  g = s + 0.34 the grounding at the parents k/q,

then the least d_k/d_1, the largest k ≤ 10⁶ at which the bound with ρ and s is below d_1, and a test of
BallPivot.slack_top on random and adversarial vectors: the least value of (Σc_n² + G(c))/((log N/2 + log 4 + 2)c_N²),
which the theorem says is at least 1.

    python3 scripts/pivot_bound.py [N] [rho] [s]    # default N = 3000, rho = 120, s = 0.5; needs numpy
"""

import math
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import ball_orbit as bo  # noqa: E402


def von_mangoldt(N):
    """Λ(n) for n ≤ N."""
    lam = np.zeros(N + 1)
    sieve = np.ones(N + 1, dtype=bool)
    for p in range(2, N + 1):
        if sieve[p]:
            sieve[2 * p :: p] = False
            q = p
            while q <= N:
                lam[q] = math.log(p)
                q *= p
    return lam


def prime_powers_dividing(k):
    """The pairs (q, p) with q a power of the prime p and q ∣ k."""
    out, m, p = [], k, 2
    while p * p <= m:
        if m % p == 0:
            q = p
            while k % q == 0:
                out.append((q, p))
                q *= p
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        out.append((m, m))
    return out


def natural_bound(k, rho, s):
    """(π/(4ρ))·(s + Σ_{q ∣ k}Λ(q)g/(g + Λ(q)/q)) with g = s + 0.34."""
    g = s + 0.34
    total = s + sum(math.log(p) * g / (g + math.log(p) / q) for q, p in prime_powers_dividing(k))
    return math.pi / (4 * rho) * total


def natural_bounds(M, rho, s):
    """natural_bound(k, rho, s) for every k ≤ M, by a sieve; the entries 0 and 1 are those of k = 1."""
    g = s + 0.34
    total = np.zeros(M + 1)
    sieve = np.ones(M + 1, dtype=bool)
    for p in range(2, M + 1):
        if sieve[p]:
            sieve[2 * p :: p] = False
            q = p
            while q <= M:
                total[q::q] += math.log(p) * g / (g + math.log(p) / q)
                q *= p
    return math.pi / (4 * rho) * (s + total)


def landau_slack(N, c, lam):
    """Σc_n² and G(c) = (log N + log 4 + 1)Σc_n² − 2Σ_n Λ(n)n^{−1/2}Σ_{jn ≤ N}c_j c_{jn}, for c[1..N]."""
    s2 = float(np.sum(c[1:] ** 2))
    form = 0.0
    for n in range(2, N + 1):
        if lam[n] == 0.0:
            continue
        J = N // n
        form += lam[n] / math.sqrt(n) * float(np.dot(c[1 : J + 1], c[n : n * J + 1 : n]))
    return s2, (math.log(N) + math.log(4) + 1) * s2 - 2 * form


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rho = float(sys.argv[2]) if len(sys.argv) > 2 else 120.0
    s = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5
    d = bo.pivots(bo.gram(N))
    print(f"d_1 = {d[0]:.6f}   (K_H(1) = 2 + γ − log 4π = {2 + bo.EULER_GAMMA - math.log(4 * math.pi):.6f})")
    print(f"{'k':>6} {'d_k':>9} {'d_k/log k':>10} {'u_k':>8} {'d_k/u_k':>8} {'pivot_ge':>10} {'rho,s':>9}")
    for k in sorted({2, 3, 5, 10, 30, 60, 100, 210, 300, 1000, 2310, 2520, 3000, 10000, N}):
        if k > N:
            continue
        u = math.log(k / (2 * math.pi)) + 1 - bo.EULER_GAMMA
        lean = (math.log(k) / 2 + math.log(4) + 2) / (22 * math.exp(8))
        ratio = f"{d[k - 1] / u:8.3f}" if u > 0.5 else " " * 8
        print(f"{k:6d} {d[k - 1]:9.5f} {d[k - 1] / math.log(k):10.4f} {u:8.4f} {ratio} {lean:10.3e} "
              f"{natural_bound(k, rho, s):9.5f}")
    r = d[1:] / d[0]
    print(f"least d_k/d_1 over 2 ≤ k ≤ {N}: {r.min():.4f} at k = {2 + int(r.argmin())}")
    M = 10**6
    b = natural_bounds(M, rho, s)
    below = np.nonzero(b[2:] < d[0])[0] + 2
    last = int(below[-1]) if len(below) else 1
    k_min = last + 1 + int(np.argmin(b[last + 1 :]))
    print(f"the bound with ρ = {rho:g}, s = {s:g} is below d_1 at {len(below)} values of k ≤ {M}, the largest {last}; "
          f"beyond it the least is {b[k_min]:.5f}, at k = {k_min}")

    rng = np.random.default_rng(1)
    worst = math.inf
    for M in [12, 30, 60, 64, 210, 360]:
        lam = von_mangoldt(M)
        for trial in range(300):
            c = np.zeros(M + 1)
            c[1:] = rng.standard_normal(M)
            if trial % 2:  # the adversary: √q·c_M at the parents M/q
                for q in range(2, M + 1):
                    if M % q == 0:
                        c[M // q] = math.sqrt(q) * c[M] * rng.uniform(0.5, 1.5)
            s2, slack = landau_slack(M, c, lam)
            worst = min(worst, (s2 + slack) / (c[M] ** 2 * (math.log(M) / 2 + math.log(4) + 2)))
    print(f"slack_top: least (Σc² + G(c))/((log N/2 + log 4 + 2)c_N²) over the tests: {worst:.3f} (the theorem: ≥ 1)")


if __name__ == "__main__":
    main()
