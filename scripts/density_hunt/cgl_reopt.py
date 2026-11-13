#!/usr/bin/env python3
"""Re-optimise CGL §12 case-split parameters numerically (no new analytic input).

Baseline (scripts/cgl_s3/price.py): at length q^y
  MVT:    max(y(2-2s), 1+y(1-2s))
  Thm1.1: max(y(2-2s), 1/2+y(3-4s), c+y(2-4s), 1+y(12/5-4s)) for y>=2/3
with c=4/3 from S3, and
  A(s)=min_a max_{y in [a,3a/2]} min(MVT,Thm1.1)/(1-s), a in [2/3,1.2].

Tests whether retuning ratio, y_floor, or a-range (without changing the four LV
terms) can drop the peak of min(Ingham,A,Huxley) below 7/3.
"""
from __future__ import annotations

import numpy as np


def A_cgl_vec(s, c, ratio=1.5, a_lo=2 / 3, a_hi=1.2, y_floor=2 / 3, na=401, ny=81):
    As = np.linspace(a_lo, a_hi, na)
    Y = As[:, None] * np.linspace(1.0, ratio, ny)[None, :]
    mvt = np.maximum(Y * (2 - 2 * s), 1 + Y * (1 - 2 * s))
    diag = Y * (2 - 2 * s)
    half = 0.5 + Y * (3 - 4 * s)
    S3 = c + Y * (2 - 4 * s)
    GM = 1 + Y * (12 / 5 - 4 * s)
    t11 = np.maximum(np.maximum(diag, half), np.maximum(S3, GM))
    stack = np.stack([diag, half, S3, GM], axis=0)
    which = np.argmax(stack, axis=0)
    names = np.array(["diag", "half", "S3", "GM"])
    use_mvt = (Y < y_floor) | (mvt <= t11)
    val = np.where(Y < y_floor, mvt, np.minimum(mvt, t11))
    j = np.argmax(val, axis=1)
    vmax = val[np.arange(na), j]
    i = int(np.argmin(vmax))
    wname = "MVT" if use_mvt[i, j[i]] else str(names[which[i, j[i]]])
    return float(vmax[i] / (1 - s)), float(As[i]), wname


def peak(c, ratio=1.5, a_lo=2 / 3, a_hi=1.2, y_floor=2 / 3, n=201):
    best = (0.0, None, None, None, None)
    for s in np.linspace(0.69, 0.80, n):
        ing = 3 / (2 - s)
        hux = 3 / (3 * s - 1)
        a, aa, wb = A_cgl_vec(s, c, ratio, a_lo, a_hi, y_floor)
        v, k = min([(ing, "Ingham"), (a, "CGL"), (hux, "Huxley")])
        if v > best[0]:
            best = (v, float(s), k, aa, wb if k == "CGL" else None)
    return best


if __name__ == "__main__":
    s, y, c = 5 / 7, 7 / 9, 4 / 3
    print("Terms at (s,y,c)=(5/7,7/9,4/3):")
    for name, val in [
        ("diag", y * (2 - 2 * s)),
        ("half", 0.5 + y * (3 - 4 * s)),
        ("S3", c + y * (2 - 4 * s)),
        ("GM", 1 + y * (12 / 5 - 4 * s)),
        ("MVT1", y * (2 - 2 * s)),
        ("MVT2", 1 + y * (1 - 2 * s)),
    ]:
        print(f"  {name:6s} {val:.6f}")
    print(f"  (7/3)(1-s) = {(7/3)*(1-s):.6f}")
    print("Baseline", peak(4 / 3))
    print("ratio sweep")
    for r in [1.2, 1.3, 1.4, 1.5, 1.6, 1.8, 2.0]:
        print(" ", r, peak(4 / 3, ratio=r)[:3])
    print("y_floor sweep")
    for yf in [0.5, 0.55, 0.6, 2 / 3, 0.7, 0.75]:
        print(" ", round(yf, 3), peak(4 / 3, y_floor=yf)[:3])
    print("a-range sweep")
    for alo, ahi in [(0.5, 1.2), (2 / 3, 1.2), (2 / 3, 1.5), (2 / 3, 2.0), (0.5, 2.0)]:
        print(" ", alo, ahi, peak(4 / 3, a_lo=alo, a_hi=ahi)[:3])
    print("c sweep")
    for c0 in [4 / 3, 1.30, 1.25, 1.20, 1.10, 1.00]:
        print(" ", c0, peak(c0)[:3])
    print("binding near 5/7:")
    for s0 in np.linspace(0.70, 0.76, 13):
        A, aa, wb = A_cgl_vec(s0, 4 / 3)
        print(f"  s={s0:.4f} A={A:.5f} Ing={3/(2-s0):.5f} a*={aa:.4f} bind={wb}")
