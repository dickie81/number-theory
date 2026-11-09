#!/usr/bin/env python3
"""Monte Carlo: random-phase model for Z(a) at the CGL corner.

Synthetic: place N = floor(q^{A(1-sigma)}) unit-modulus contributions with
iid uniform phases, form Z(a) for many a (or just one draw of phases),
compare max_|Z|, RMS, and triangle N.

Reports the empirical cancellation exponent alpha where max|Z| ~ N^{alpha}.
Under full random cancellation alpha -> 1/2; triangle is alpha=1.
"""
from __future__ import annotations

import argparse
import numpy as np


A = 7 / 3
SIGMA = 5 / 7


def run(q: int, trials: int = 200, seed: int = 0) -> dict:
    rng = np.random.default_rng(seed)
    N = max(int(q ** (A * (1 - SIGMA))), 1)
    # For each trial: N random phases; |sum e^{i theta_j}|
    # Also simulate "characters": assign each zero a random chi-index in 1..q-1
    # and evaluate Z(a) = sum_j chi_j(a)^{-1} * e^{i gamma_j} for all a via FFT.
    # Model: chi on (Z/q)* via discrete log; random gamma phases.
    # Simpler honest model: Z(a) = sum_{k=1}^{N} exp(2 pi i (u_k * ind(a) + v_k))
    # with u_k random in 0..q-2, v_k random — i.e. random character × random phase.
    g = 0  # unused; pure random Fourier
    # Build N random frequencies
    freqs = rng.integers(0, q - 1, size=N)
    phases = rng.random(N)
    # One coefficient vector on F_{q-1}: accumulate e^{2pi i phase} at freq
    coeff = np.zeros(q - 1, dtype=np.complex128)
    for f, p in zip(freqs, phases):
        coeff[f] += np.exp(2j * np.pi * p)
    # Z on a-side via FFT (characters of (Z/q)* ~ Z/(q-1))
    Z = np.fft.fft(coeff)
    absZ = np.abs(Z)
    # second moment identity: (1/(q-1)) sum |Z|^2 = sum |coeff|^2
    # Triangle: N
    rms = float(np.sqrt(np.mean(absZ ** 2)))
    mx = float(absZ.max())
    tri = float(N)
    # empirical alpha: mx ~ N^alpha
    alpha = float(np.log(max(mx, 1e-300)) / np.log(N)) if N > 1 else 1.0
    return dict(q=q, N=N, max_abs=mx, rms=rms, triangle=tri,
                max_over_rms=mx / max(rms, 1e-300),
                max_over_tri=mx / tri,
                alpha_emp=alpha)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qs", type=int, nargs="+", default=[31, 61, 127, 251, 503, 1009])
    ap.add_argument("--seed", type=int, default=42)
    args = ap.parse_args()
    print(f"{'q':>6} {'N':>8} {'max|Z|':>12} {'rms':>12} {'tri':>8} "
          f"{'max/rms':>8} {'max/tri':>8} {'alpha':>7}")
    alphas = []
    for q in args.qs:
        r = run(q, seed=args.seed + q)
        alphas.append(r["alpha_emp"])
        print(f"{r['q']:6d} {r['N']:8d} {r['max_abs']:12.4f} {r['rms']:12.4f} "
              f"{r['triangle']:8.0f} {r['max_over_rms']:8.3f} {r['max_over_tri']:8.4f} "
              f"{r['alpha_emp']:7.4f}")
    print(f"mean alpha_emp = {np.mean(alphas):.4f} (random-phase prediction 0.5)")
    print("Heuristic Linnik: see bookkeeping.random_phase_heuristic_L")
    # Pure-explicit L ~ A/2 under alpha=1/2
    print(f"Conditional L (pure explicit, alpha=1/2): A/2 = {A/2:.6f}")
    print(f"Conditional sieve floor if A->A/2: 1+A/4 = {1+A/4:.6f}")


if __name__ == "__main__":
    main()
