#!/usr/bin/env python3
"""S3-saving delta -> peak A under CGL LV terms with a,y re-optimisation; Linnik floors.

c = 4/3 - 2*delta/3  (as in scripts/cgl_s3/price.py).
Peak of min(Ingham, A_CGL, Huxley) on sigma in [0.69,0.80].
Note: once delta is large enough that CGL dips below the Ingham–GM glue, the peak
freezes near 30/13 ≈ 2.308; further S3 savings alone do not help uniform A.
"""
from __future__ import annotations

import numpy as np


def A_cgl_vec(s, c, ratio=1.5, a_lo=2 / 3, a_hi=1.2, y_floor=2 / 3, na=401, ny=81):
    As = np.linspace(a_lo, a_hi, na)
    Y = As[:, None] * np.linspace(1.0, ratio, ny)[None, :]
    mvt = np.maximum(Y * (2 - 2 * s), 1 + Y * (1 - 2 * s))
    t11 = np.maximum.reduce(
        [Y * (2 - 2 * s), 0.5 + Y * (3 - 4 * s), c + Y * (2 - 4 * s), 1 + Y * (12 / 5 - 4 * s)]
    )
    val = np.where(Y < y_floor, mvt, np.minimum(mvt, t11))
    return float(val.max(axis=1).min() / (1 - s))


def peak_detail(c, n=401):
    best = (0.0, None, None)
    for s in np.linspace(0.69, 0.80, n):
        ing, hux, a = 3 / (2 - s), 3 / (3 * s - 1), A_cgl_vec(s, c)
        v, k = min([(ing, "Ingham"), (a, "CGL"), (hux, "Huxley")])
        if v > best[0]:
            best = (v, float(s), k)
    return best, A_cgl_vec(5 / 7, c)


def c_of_delta(delta: float) -> float:
    return 4 / 3 - 2 * delta / 3


def delta_for_target(At: float, n_bin=40, n_peak=201) -> float:
    lo, hi = 0.0, 0.5
    for _ in range(n_bin):
        mid = (lo + hi) / 2
        (peak, _, _), _ = peak_detail(c_of_delta(mid), n=n_peak)
        if peak > At:
            lo = mid
        else:
            hi = mid
    return hi


if __name__ == "__main__":
    print(f"{'delta':>8} {'c':>8} {'peakA':>8} {'at_s':>8} {'who':>8} {'A(5/7)':>8} {'sieve':>8}")
    for delta in [0, 0.005, 0.01, 0.015, 0.02, 0.03, 1 / 26, 0.05, 0.1]:
        (peak, s, who), a57 = peak_detail(c_of_delta(delta))
        print(f"{delta:8.4f} {c_of_delta(delta):8.4f} {peak:8.5f} {s:8.5f} {who:>8} {a57:8.5f} {1+peak/2:8.5f}")
    print("\nTargets:")
    for At in [2.33, 2.325, 2.32, 2.31, 30 / 13, 2.30]:
        d = delta_for_target(At)
        (peak, s, who), _ = peak_detail(c_of_delta(d))
        print(f"  A<={At:.5f}: delta≈{d:.5f} peak={peak:.5f} ({who}) sieve={1+peak/2:.5f}")
    y, s = 7 / 9, 5 / 7
    print("\nFixed y=7/9, s=5/7: min(S3,MVT) as delta grows (MVT freezes the tie):")
    for delta in [0, 0.01, 0.02, 0.03846]:
        c = c_of_delta(delta)
        S3 = c + y * (2 - 4 * s)
        MVT = max(y * (2 - 2 * s), 1 + y * (1 - 2 * s))
        print(f"  delta={delta:.4f} S3={S3:.5f} MVT={MVT:.5f} min={min(S3,MVT):.5f}")
