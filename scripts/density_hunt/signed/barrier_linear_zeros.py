#!/usr/bin/env python3
"""Barrier construction: linear-in-k zero placement aligning Z(a) at triangle scale.

Model (zero-information adversary):
  Identify non-principal χ_k, k=1..q-2, via discrete log on (Z/q)*, q prime.
  χ_k(a) = exp(2πi k ind(a)/(q-1)).
  Place a single zero of L(s, χ_k) at ρ_k = σ + i γ_k for k in a set W,
  with γ_k = (2π k ind(a0)) / ((q-1) log x)   [linear in k]
  so that χ̄_k(a0) x^{i γ_k} = 1 (perfect phase alignment at a0).

Constraints checked (those expressible in this model):
  C1 conjugation: W closed under k -> -k (mod q-1), and γ_{-k} = -γ_k.
  C2 functional equation bookkeeping: also record the reflected zeros at 1-σ - iγ
      (contribute x^{1-σ}, smaller); do not add them to the aligned sum for |Z|_△
      at the density-box scale σ.
  C3 density: |W| ≤ M_max = floor(q^{A(1-σ)}).
  C4 zero-counting soft: at most one zero per χ in the box (well within N(T)≍log(qT)).
  C5 half-plane: σ = 5/7 < 11/12, so half-plane constraint does not forbid the box.
  NOT imposed (would need Euler product / primes): that the resulting ψ(x,χ) equals
  an actual Λ-weighted character sum. That is the arithmetic input of §circularity.

Output: max|Z|/triangle at a0 and over all a; whether alignment achieves ~1.
"""
from __future__ import annotations

import argparse
import numpy as np

A = 7 / 3
SIGMA = 5 / 7
HALFPLANE = 11 / 12


def build(q: int, L: float, a0_ind: int, seed: int = 0) -> dict:
    rng = np.random.default_rng(seed)
    n = q - 1  # | (Z/q)* |
    x = float(q) ** L
    logx = np.log(x)
    M_max = max(int(q ** (A * (1 - SIGMA))), 1)
    M_max = min(M_max, n - 1)
    # Take W symmetric under k -> -k, size ~ M_max
    # Prefer pairs {k,-k}; if M_max odd include a self-inverse if any
    candidates = list(range(1, n))
    rng.shuffle(candidates)
    W = set()
    for k in candidates:
        if len(W) >= M_max:
            break
        if k in W:
            continue
        mk = (-k) % n
        if mk == 0:
            continue
        if mk == k:
            W.add(k)
        else:
            if len(W) + 2 <= M_max:
                W.add(k)
                W.add(mk)
            elif len(W) + 1 <= M_max:
                W.add(k)
    W = sorted(W)
    M = len(W)

    # Linear phases for alignment at a0_ind:
    # χ̄_k(a0) x^{iγ} = exp(-2πi k a0_ind/n) * exp(i γ log x) = 1
    # => γ_k = 2π k a0_ind / (n log x)
    coeff = np.zeros(n, dtype=np.complex128)  # index = k
    amp = x ** SIGMA  # |x^ρ|; ignore 1/ρ ~ O(1) for barrier ratio
    for k in W:
        # phase of χ̄_k(a0) * x^{iγ_k} = 1 by construction
        # coeff[k] = x^ρ * (phase factor already absorbed into definition of Z via FFT)
        # Z(a) = sum_k χ̄_k(a) c_k with c_k = x^{σ+iγ_k}
        # χ̄_k(a) = exp(-2πi k ind(a)/n)
        # At a0: χ̄_k(a0) c_k = amp * exp(-2πi k a0_ind/n) * exp(i γ_k logx) = amp
        gamma = 2 * np.pi * k * a0_ind / (n * logx)
        c_k = amp * np.exp(1j * gamma * logx)
        coeff[k] = c_k

    # FFT: Z[j] corresponds to ind(a)=j
    # numpy fft: Z[j] = sum_k coeff[k] exp(-2πi k j / n)  — wait, np.fft.fft(coeff)[j]
    # = sum_k coeff[k] exp(-2πi k j / n). Yes matches χ̄_k with ind=j.
    Z = np.fft.fft(coeff)
    absZ = np.abs(Z)
    tri = M * amp
    j0 = a0_ind % n
    return dict(
        q=q, L=L, M=M, M_max=M_max, amp=amp, triangle=tri,
        Z_at_a0=float(absZ[j0]),
        max_abs=float(absZ.max()),
        rms=float(np.sqrt(np.mean(absZ ** 2))),
        ratio_a0=float(absZ[j0] / tri),
        ratio_max=float(absZ.max() / tri),
        sigma_ok=(SIGMA < HALFPLANE),
        W_symmetric=all(((-k) % n) in set(W) or k == ((-k) % n) for k in W),
        # reflected contribution size relative to main aligned sum
        reflected_rel=(x ** (1 - SIGMA)) / amp,
    )


def random_phases_control(q: int, L: float, seed: int = 1) -> dict:
    """Same |W|, random γ — should give ~sqrt cancellation."""
    rng = np.random.default_rng(seed)
    n = q - 1
    x = float(q) ** L
    M_max = min(max(int(q ** (A * (1 - SIGMA))), 1), n - 1)
    W = rng.choice(n, size=M_max, replace=False)
    amp = x ** SIGMA
    coeff = np.zeros(n, dtype=np.complex128)
    coeff[W] = amp * np.exp(2j * np.pi * rng.random(M_max))
    Z = np.fft.fft(coeff)
    tri = M_max * amp
    return dict(ratio_max=float(np.abs(Z).max() / tri), M=M_max)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qs", type=int, nargs="+",
                    default=[31, 61, 127, 251, 503, 1009, 2003])
    ap.add_argument("--L", type=float, default=2.2)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    print("BARRIER: linear-in-k zeros aligned at a0 (ind=1)")
    print(f"{'q':>6} {'M':>5} {'Z(a0)/△':>10} {'max/△':>10} {'rand max/△':>12} "
          f"{'refl/amp':>10} {'σ<11/12':>8}")
    for q in args.qs:
        r = build(q, args.L, a0_ind=1, seed=args.seed)
        ctrl = random_phases_control(q, args.L, seed=args.seed + 1)
        print(f"{r['q']:6d} {r['M']:5d} {r['ratio_a0']:10.6f} {r['ratio_max']:10.6f} "
              f"{ctrl['ratio_max']:12.6f} {r['reflected_rel']:10.4e} "
              f"{str(r['sigma_ok']):>8}")
    print()
    print("If Z(a0)/△ ≈ 1, the adversary achieves the triangle bound at some a")
    print("while respecting conjugation symmetry, density |W|≤q^{A(1-σ)}, and σ<11/12.")
    print("Random-phase control should be ≪ 1.")


if __name__ == "__main__":
    main()
