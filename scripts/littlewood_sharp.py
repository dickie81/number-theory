#!/usr/bin/env python3
"""The constants of lib/pnt/LittlewoodSharp.lean and lib/pnt/ClassNumberSharp.lean, and what they give. Uncertified numerics.

    python3 scripts/littlewood_sharp.py [--sections ABCD] [--qmax Q] [--dmax D]

  A. The constants of `LittlewoodSharp.norm_LFunction_one_bounds_sharp`: the ψ constant A = 2·10¹¹·156⁵ of
     `ExplicitConstants.psiChi_le_explicit` at η = 1/156 (θ = 12/13), A/e⁵², and at x = (e⁵² log(N + 2))¹³ the tail
     13(A/e⁵²)(2/log x + 13/(12 log² x)) and Mertens' error (log 4 + 6)/log x, whose sum is below 3/100.
  B. The bounds against the actual values: |L(1, χ)| for every character χ ≠ 1 mod q ≤ Q (from the digamma function,
     L(1, χ) = −(1/q)Σ χ(a)ψ(a/q)), against e^{−γ−3/100}/(13(52 + ℓ)) and 13e^{γ+3/100}(52 + ℓ), ℓ = log log(q + 2).
  C. The class-number search bounds: the largest X with √X ≤ 85h(52 + log log(X + 2)) (`ClassNumberSharp.classNumber_ge_85`),
     for h = 1, 2, 10, 100, and with the constant of `classNumber_ge_sharp` at w = 2 and the true γ.
  D. Class number one below 2.5·10⁷ (`ClassNumberSharp.abs_discr_lt_of_classNumber_eq_one`): by genus theory a
     fundamental discriminant of class number one is −4, −8 or −p with p ≡ 3 mod 4 prime, and h(−p) > 1 as soon as a
     prime ℓ < (p + 1)/4 splits in ℚ(√−p). The sieve to D (default 2.5·10⁷) leaves 3, 7, 11, 19, 43, 67, 163. This is
     an illustration of the finite check, not a proof of it.
"""
import argparse
import math

import numpy as np

GAMMA_E = 0.5772156649015329
C = GAMMA_E + 3 / 100


def section_a():
    print("A. The constants")
    A = 2e11 * 156 ** 5
    ratio = A / math.exp(52)
    print(f"  A = 2·10¹¹·156⁵ = {A:.6e},  A/e⁵² = {ratio:.6f}  (Lean: ≤ 0.483, `A_le`)")
    for ell in [math.log(math.log(3)), 1.0, 3.0, 10.0]:
        logx = 13 * (52 + ell)
        tail = 13 * ratio * (2 / logx + 13 / (12 * logx ** 2))
        mert = (math.log(4) + 6) / logx
        print(f"  log log(N + 2) = {ell:6.3f}: log x = {logx:8.2f}, tail {tail:.5f}, Mertens {mert:.5f},"
              f" total {tail + mert:.5f} (Lean: ≤ 3/100, `err_le`)")
    print(f"  e^(γ + 3/100) = {math.exp(C):.5f}  (Lean: ≤ 2.08 from γ < 2/3, `exp_c_le`);"
          f" 13e^(γ+3/100) = {13 * math.exp(C):.3f}")


def chars_mod(q):
    """The Dirichlet characters mod q, as arrays over residues 0..q−1 (complex), by the structure of (ℤ/qℤ)ˣ found
    numerically: we diagonalise the regular representation's translations through FFT on a discrete log for prime q,
    and for composite q fall back to a brute-force construction from the generators of the group."""
    units = [a for a in range(1, q) if math.gcd(a, q) == 1]
    # brute force: characters are homomorphisms; build from a basis of the unit group
    order = {a: next(k for k in range(1, q + 1) if pow(a, k, q) == 1) for a in units}
    gens, span = [], {1 % q}
    for a in sorted(units, key=lambda a: -order[a]):
        if a in span:
            continue
        gens.append(a)
        new = set()
        for s in span:
            x = s
            for _ in range(order[a]):
                new.add(x)
                x = x * a % q
        span = new
        if len(span) == len(units):
            break
    # express each unit as a product of generator powers (first match)
    import itertools
    exps = {}
    for es in itertools.product(*[range(order[g]) for g in gens]):
        x = 1 % q
        for g, e in zip(gens, es):
            x = x * pow(g, e, q) % q
        exps.setdefault(x, es)
    out = []
    for ks in itertools.product(*[range(order[g]) for g in gens]):
        chi = np.zeros(q, dtype=complex)
        for a in units:
            es = exps[a]
            chi[a] = np.exp(2j * np.pi * sum(k * e / order[g] for k, e, g in zip(ks, es, gens)))
        out.append((ks, chi))
    return out


def section_b(qmax):
    from scipy.special import digamma
    print(f"B. |L(1, χ)| for χ ≠ 1 mod q, 3 ≤ q ≤ {qmax}, against the bounds")
    lo_ratio, hi_ratio, n = float("inf"), 0.0, 0
    for q in range(3, qmax + 1):
        ell = math.log(math.log(q + 2))
        lower = math.exp(-C) / (13 * (52 + ell))
        upper = 13 * math.exp(C) * (52 + ell)
        psi = digamma(np.arange(1, q + 1) / q)
        for ks, chi in chars_mod(q):
            if all(k == 0 for k in ks):
                continue
            L1 = -sum(chi[a] * psi[a - 1] for a in range(1, q)) / q
            v = abs(L1)
            n += 1
            lo_ratio = min(lo_ratio, v / lower)
            hi_ratio = max(hi_ratio, v / upper)
    print(f"  {n} characters: min |L(1,χ)|/lower = {lo_ratio:.1f}, max |L(1,χ)|/upper = {hi_ratio:.2e}")


def d0(h, k):
    """The largest X with √X ≤ k·h·(52 + log log(X + 2)), by bisection on the crossing."""
    lo, hi = 3.0, 1e30
    f = lambda X: math.sqrt(X) - k * h * (52 + math.log(math.log(X + 2)))
    for _ in range(300):
        mid = math.sqrt(lo * hi)
        if f(mid) > 0:
            hi = mid
        else:
            lo = mid
    return hi


def section_c():
    print("C. Class-number search bounds")
    k_lean = 85
    k_true = 13 * math.pi * math.exp(C)  # classNumber_ge_sharp at w = 2, true γ
    for h in [1, 2, 10, 100]:
        print(f"  h ≤ {h:3d}: |D| ≤ {d0(h, k_lean):.3e} (85, `classNumber_ge_85`),"
              f" {d0(h, k_true):.3e} ({k_true:.2f}, true γ)")


def section_d(dmax):
    print(f"D. Class number one below {dmax:.2e}: the split-prime sieve on −p, p ≡ 3 mod 4 prime")
    n = int(dmax)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    primes = np.nonzero(sieve)[0]
    small = [int(l) for l in primes[:2000]]
    survivors, worst = [], (0, 0)
    for p in primes:
        p = int(p)
        if p % 4 != 3:
            continue
        bound = (p + 1) / 4
        found = None
        for l in small:
            if l >= bound:
                break
            if l == 2:
                split = (-p) % 8 == 1
            elif l == p:
                continue
            else:
                split = pow((-p) % l, (l - 1) // 2, l) == 1
            if split:
                found = l
                break
        if found is None:
            survivors.append(p)
        elif found > worst[0]:
            worst = (found, p)
    print(f"  survivors: {survivors}; largest least split prime needed: {worst[0]} (at p = {worst[1]})")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sections", default="ABCD")
    ap.add_argument("--qmax", type=int, default=60)
    ap.add_argument("--dmax", type=float, default=2.5e7)
    a = ap.parse_args()
    if "A" in a.sections:
        section_a()
    if "B" in a.sections:
        section_b(a.qmax)
    if "C" in a.sections:
        section_c()
    if "D" in a.sections:
        section_d(a.dmax)


if __name__ == "__main__":
    main()
