#!/usr/bin/env python3
"""Function-field controlled model for signed Z(a).

Over F_q[t], modulus irreducible P of degree d: (A/(P))* is cyclic of order
N = q^d - 1. Dirichlet L-functions are polynomials; Weil RH puts all reciprocal
zeros on the circle |α| = q^{1/2}.

We work with the dual group Z/NZ (character index k). Three experiments:

  (E1) RH model: place deg(L)-many zeros on the critical circle with RANDOM angles
       (proxy for Weil zeros); form Z(a); report max/△ and α.
  (E2) Adversarial off-line: displace a density-sized set W of characters to radius
       q^{-σ} (σ=5/7 analogue: use σ_ff so that q_ff^{A(1-σ)} matches), with
       LINEAR angles aligning at a0 — keep homomorphism χ(a)=e(k ind(a)/N).
  (E3) Exact AP comparison (tiny): for very small (q,d), count monic irreducibles
       in each residue class up to degree n by brute force, compare variation of
       π(n; P, a) across a — this IS Z via explicit formula under RH.
       Label: EXACT_FF_PRIMES (only tiny parameters).

No fabrication: E1/E2 are models; E3 is exact enumeration at tiny size.
"""
from __future__ import annotations

import argparse
import itertools
import numpy as np

A = 7 / 3
SIGMA = 5 / 7


def e1_rh_random(N: int, nzeros_per_chi: int, rng: np.random.Generator) -> dict:
    """All N-1 non-principal χ; each has nzeros_per_chi unit-modulus contributions
    with random angles. amp=1 (critical line)."""
    # coeff[k] = sum of nzeros random phases
    coeff = np.zeros(N, dtype=np.complex128)
    total = 0
    for k in range(1, N):
        phases = rng.random(nzeros_per_chi)
        coeff[k] = np.exp(2j * np.pi * phases).sum()
        total += nzeros_per_chi
    Z = np.fft.fft(coeff)
    # Only indices 0..N-1; principal k=0 left at 0
    absZ = np.abs(Z)
    tri = float(total)
    return dict(max_over_tri=float(absZ.max() / tri),
                rms=float(np.sqrt(np.mean(absZ ** 2))),
                M_terms=total)


def e2_adversary(N: int, M: int, a0: int, rng: np.random.Generator) -> dict:
    """Density-sized W, linear phases, off-line amp factor r = 'x^{σ-1/2}' proxy = 2.0."""
    M = min(M, N - 1)
    # symmetric W
    candidates = list(range(1, N))
    rng.shuffle(candidates)
    W = set()
    for k in candidates:
        if len(W) >= M:
            break
        mk = (-k) % N
        if mk == 0:
            continue
        if len(W) + (1 if mk == k else 2) <= M or mk in W:
            W.add(k)
            if mk != k and len(W) < M:
                W.add(mk)
    W = sorted(W)[:M]
    amp = 2.0  # off-line displacement factor
    coeff = np.zeros(N, dtype=np.complex128)
    for k in W:
        # align: χ̄_k(a0) * e^{i θ_k} = 1 => θ_k = 2π k a0 / N
        theta = 2 * np.pi * k * a0 / N
        coeff[k] = amp * np.exp(1j * theta)
    Z = np.fft.fft(coeff)
    tri = len(W) * amp
    return dict(M=len(W), ratio_a0=float(np.abs(Z[a0 % N]) / tri),
                ratio_max=float(np.abs(Z).max() / tri))


def e3_exact_primes(q: int, d: int, n_max: int) -> dict:
    """Enumerate monic polys over F_q, modulus t^d + ... use prime field F_p with p=q
    and modulus a monic irreducible of degree d.

    For tiny q,d: list all monic irreducibles of degree <= n_max, reduce mod P,
    count per residue class in (A/P)*.
    """
    # Build F_q[t]/(P). Take q prime for simplicity.
    assert q < 20 and d <= 3 and n_max <= 8
    # Find a monic irreducible P of degree d over F_q
    P = find_irreducible(q, d)
    # Residue classes: polys of deg < d, not 0 mod P — identify with 0..q^d-1
    N = q ** d  # including 0; units: N-1 if P irreducible... actually |A/(P)| = q^d,
    # units = q^d - 1 only if P prime (=irreducible). Yes.
    counts = {r: 0 for r in range(1, q ** d)}  # skip 0
    # Enumerate monic irreducibles of deg 1..n_max
    irreds = list_irreducibles(q, n_max)
    for f in irreds:
        if deg(f, q) >= d and poly_mod(f, P, q) == 0:
            continue  # divisible by P
        r = poly_mod(f, P, q)
        if r == 0:
            continue
        counts[r] = counts.get(r, 0) + 1
    vals = np.array([counts[r] for r in range(1, q ** d)], dtype=float)
    mean = float(vals.mean()) if len(vals) else 0.0
    if mean <= 0:
        return dict(q=q, d=d, P=P, n_irred=len(irreds), mean=0, max_dev=0,
                    rel_spread=0.0, label="EXACT_FF_PRIMES")
    dev = vals - mean
    return dict(
        q=q, d=d, P=P, n_irred=len(irreds),
        mean=mean,
        max_abs_dev=float(np.max(np.abs(dev))),
        rel_spread=float(np.max(np.abs(dev)) / mean),
        rms_dev=float(np.sqrt(np.mean(dev ** 2))),
        label="EXACT_FF_PRIMES",
    )


# --- tiny poly helpers base-q digits, low degree first ---
def deg(f: int, q: int) -> int:
    if f == 0:
        return -1
    d = 0
    while q ** (d + 1) <= f:
        d += 1
    # f as coeffs: actually we store poly as integer with coeffs in base q, highest deg = top
    # redo: value f = sum a_i q^i, deg = max i with a_i≠0
    d = 0
    x = f
    i = 0
    while x:
        if x % q:
            d = i
        x //= q
        i += 1
    return d


def poly_mod(f: int, P: int, q: int) -> int:
    """Reduce f mod P in F_q[t]."""
    pd = deg(P, q)
    while deg(f, q) >= pd:
        fd = deg(f, q)
        # leading coeffs
        def lead(g):
            return (g // (q ** deg(g, q))) % q
        lc_f, lc_P = lead(f), lead(P)
        # multiply P by x^{fd-pd} * (lc_f / lc_P)
        inv = pow(int(lc_P), -1, q)
        scale = (lc_f * inv) % q
        shift = fd - pd
        add = 0
        tmp = P
        i = 0
        while tmp:
            add += ((tmp % q) * scale % q) * (q ** (i + shift))
            tmp //= q
            i += 1
        # subtract in F_q
        f = poly_sub(f, add, q)
    return f


def poly_sub(a: int, b: int, q: int) -> int:
    out = 0
    i = 0
    while a or b:
        da, db = a % q, b % q
        out += ((da - db) % q) * (q ** i)
        a //= q
        b //= q
        i += 1
    return out


def poly_mul(a: int, b: int, q: int) -> int:
    out = 0
    i = 0
    aa = a
    while aa:
        da = aa % q
        if da:
            bb = b
            j = 0
            while bb:
                db = bb % q
                if db:
                    out = poly_add(out, ((da * db) % q) * (q ** (i + j)), q)
                bb //= q
                j += 1
        aa //= q
        i += 1
    return out


def poly_add(a: int, b: int, q: int) -> int:
    out = 0
    i = 0
    while a or b:
        out += ((a % q + b % q) % q) * (q ** i)
        a //= q
        b //= q
        i += 1
    return out


def is_irreducible(f: int, q: int) -> bool:
    d = deg(f, q)
    if d <= 0:
        return False
    # check no root in F_q for d>=1: eval
    # trial division by all monics of deg <= d/2
    for e in range(1, d // 2 + 1):
        for g in range(q ** e, q ** (e + 1)):  # monic deg e: leading 1 => g in [q^e, q^{e+1})
            # all polys deg e: 0..q^{e+1}-1 with deg==e
            if deg(g, q) != e:
                continue
            if poly_mod(f, g, q) == 0:
                return False
    return True


def find_irreducible(q: int, d: int) -> int:
    # monic: leading coeff 1 => f in [q^d, 2*q^d) roughly — leading=1 means
    # f = q^d + lower
    for lower in range(q ** d):
        f = q ** d + lower  # leading coeff 1 at degree d
        if is_irreducible(f, q):
            return f
    raise RuntimeError(f"no irreducible deg {d} over F_{q}")


def list_irreducibles(q: int, n_max: int) -> list:
    out = []
    for d in range(1, n_max + 1):
        for lower in range(q ** d):
            f = q ** d + lower
            if is_irreducible(f, q):
                out.append(f)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=2)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)

    print("=== E1: RH random angles (function-field proxy) ===")
    print(f"{'N=q^d-1':>10} {'nz/χ':>6} {'max/△':>10}")
    for qd, nz in [(16, 2), (32, 2), (64, 3), (128, 3), (256, 4)]:
        # N = qd  as proxy group order (use N=qd, close enough; exact q^d-1 similar)
        N = qd
        r = e1_rh_random(N, nz, rng)
        print(f"{N:10d} {nz:6d} {r['max_over_tri']:10.6f}")

    print()
    print("=== E2: adversarial off-line linear alignment (homomorphism kept) ===")
    print(f"{'N':>6} {'M':>5} {'Z(a0)/△':>10} {'max/△':>10}")
    for N in [16, 32, 64, 128, 256, 512]:
        M = max(int(N ** (A * (1 - SIGMA) * 0.5)), 2)  # milder density for small N
        # use M ~ N^{A(1-σ)/log factor}; simpler: M = max(N//4, 2) capped by density formula
        M = min(max(int(N ** (A * (1 - SIGMA))), 2), N - 1)
        r = e2_adversary(N, M, a0=1, rng=rng)
        print(f"{N:6d} {r['M']:5d} {r['ratio_a0']:10.6f} {r['ratio_max']:10.6f}")

    print()
    print("=== E3: EXACT_FF_PRIMES — monic irreducibles by residue class ===")
    print(f"{'q':>3} {'d':>3} {'#irred':>8} {'mean':>8} {'max|dev|':>10} {'rel_spread':>11}")
    for q, d, nmax in [(2, 2, 6), (2, 3, 5), (3, 2, 5), (2, 2, 7)]:
        try:
            r = e3_exact_primes(q, d, nmax)
            print(f"{r['q']:3d} {r['d']:3d} {r['n_irred']:8d} {r['mean']:8.3f} "
                  f"{r['max_abs_dev']:10.3f} {r['rel_spread']:11.4f}")
        except Exception as e:
            print(f"{q:3d} {d:3d} ERROR {e}")


if __name__ == "__main__":
    main()
