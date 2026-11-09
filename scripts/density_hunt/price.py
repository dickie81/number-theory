#!/usr/bin/env python3
"""Bookkeeping for a density-exponent saving.

If S3 gets a factor q^{-delta} relative to CGL's critical term, their 4/(1+sigma)
becomes (4-2*delta)/(1+sigma); it meets Ingham 3/(2-sigma) at
sigma* = (5-4*delta)/(7-2*delta), and the uniform A is 7/3 - 2*delta/3 for
delta <= 1/26 (at which point A hits Guth-Maynard's 30/13).

Sieve Linnik threshold is 1 + A/2. Classical is A.
This script is pure arithmetic; no claims about existence of delta.
"""
from __future__ import annotations

def A_of_delta(delta: float) -> float:
    # for delta in [0, 1/26]
    return 7 / 3 - 2 * delta / 3

def sigma_star(delta: float) -> float:
    return (5 - 4 * delta) / (7 - 2 * delta)

def main() -> None:
    print(f"{'delta':>10} {'A':>10} {'1+A/2':>10} {'A_classical':>12} {'sigma*':>10}")
    for k in range(0, 27):
        d = k / 26 / 10  # 0 .. 1/26 in steps of 1/260
        if k % 2 and k not in (0, 26):
            continue
        # print at 0, and multiples; also 1/26
    for d in [0, 0.01, 0.02, 0.03, 1 / 26, 0.05]:
        if d > 1 / 26 + 1e-12:
            # beyond: A freezes at 30/13 once delta>=1/26 in the cgl-s3 model
            A = 30 / 13
        else:
            A = A_of_delta(d)
        print(f"{d:10.5f} {A:10.5f} {1+A/2:10.5f} {A:12.5f} {sigma_star(min(d,1/26)):10.5f}")
    print()
    print("Reference: A=7/3 => classical L>2.333..., sieve L>13/6≈2.1667; paper proves 11/5=2.2")
    print("At delta=1/26: A=30/13≈2.3077, sieve 1+A/2≈2.1538")

if __name__ == "__main__":
    main()
