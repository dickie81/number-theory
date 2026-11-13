#!/usr/bin/env python3
"""Synthetic off-line zeros for Z(a) (clearly labelled SYNTHETIC).

Place, for each of M 'characters', a single zero at sigma=5/7 with random height
phase, form Z(a) = sum_chi chi-bar(a) * x^{sigma} * e^{i gamma_chi}, compare
max|Z|, RMS, triangle. Also a GRH-like model with sigma=1/2 (low-lying).

This is NOT computed from actual L-functions.
"""
from __future__ import annotations

import argparse
import numpy as np

A = 7 / 3
SIGMA_OFF = 5 / 7
SIGMA_GRH = 0.5


def synth(q: int, sigma: float, use_density_M: bool, x_exp: float,
          rng: np.random.Generator) -> dict:
    """x = q^{x_exp}. One zero per character in a set W of size M."""
    if use_density_M:
        M = max(int(q ** (A * (1 - SIGMA_OFF))), 1)
        M = min(M, q - 1)
    else:
        M = q - 1  # all non-principal
    # coefficients on Z/(q-1): random M frequencies, phase from gamma ~ Exp or Unif
    freqs = rng.choice(q - 1, size=M, replace=False)
    # x^{i gamma}: model gamma uniform [0, 2pi] / log x  => phase uniform
    phases = rng.random(M)
    coeff = np.zeros(q - 1, dtype=np.complex128)
    amp = q ** (x_exp * sigma)  # |x^rho| = x^sigma
    coeff[freqs] = amp * np.exp(2j * np.pi * phases)
    Z = np.fft.fft(coeff)
    absZ = np.abs(Z)
    tri = M * amp
    rms = float(np.sqrt(np.mean(absZ ** 2)))
    mx = float(absZ.max())
    alpha = float(np.log(max(mx / amp, 1e-300)) / np.log(M)) if M > 1 else 1.0
    return dict(q=q, sigma=sigma, M=M, amp=amp, max_abs=mx, rms=rms,
                triangle=tri, alpha=alpha, max_over_tri=mx / tri,
                label="SYNTHETIC")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qs", type=int, nargs="+", default=[31, 61, 127, 251])
    ap.add_argument("--L", type=float, default=2.2, help="x = q^L")
    ap.add_argument("--seed", type=int, default=99)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    print(f"SYNTHETIC Z(a) at x=q^{args.L}")
    print(f"{'label':<12} {'q':>5} {'sig':>5} {'M':>6} {'max/tri':>9} {'alpha':>7}")
    for q in args.qs:
        for sigma, dens in [(SIGMA_OFF, True), (SIGMA_GRH, False)]:
            r = synth(q, sigma, dens, args.L, rng)
            lab = "off+dens" if dens else "GRH-all"
            print(f"{lab:<12} {q:5d} {sigma:5.3f} {r['M']:6d} "
                  f"{r['max_over_tri']:9.5f} {r['alpha']:7.4f}")
    print("Random-phase alpha≈0.5; triangle would be 1.0.")


if __name__ == "__main__":
    main()
