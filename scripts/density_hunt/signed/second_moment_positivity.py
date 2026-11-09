#!/usr/bin/env python3
"""Second-moment identity, higher moments, and one-sided positivity notes.

(a) Plancherel: for Z(a) = sum_chi chi-bar(a) c_chi,
      sum_{a mod q}^* |Z(a)|^2 = phi(q) sum_chi |c_chi|^2.
    So RMS = sqrt(sum |c|^2). Average-a bound is square-root cancellation.
    Pointwise every-a requires more.

(b) 2k-th moment: if c_chi are 1_W, then
      sum_a |Z(a)|^{2k} = phi(q) * (number of 2k-tuples in W with chi-product 1).
    Holder: max|Z| <= (sum |Z|^{2k})^{1/(2k)}.
    Without structure on W this is essentially the same as random-matrix /
    expander bounds — no unconditional power saving below triangle for every a
    when |W| is as large as the density bound.

(c) Positivity: Linnik needs psi_f(x;q,a) > 0, i.e. Re(main - Z/phi) > 0,
    so only a one-sided bound on Re Z(a). Fejer / positive kernels can replace
    |Z| by a smoothed positive combination, but the classical obstacle remains:
    without cancellation across chi, the triangle still governs. Fejer does not
    create cross-character cancellation.

Numeric: for random c on W, compare max Re_+ Z vs |Z| vs RMS.
"""
from __future__ import annotations

import argparse
import numpy as np

A = 7 / 3
SIGMA = 5 / 7


def moments(q: int, seed: int = 0) -> dict:
    rng = np.random.default_rng(seed)
    M = max(int(q ** (A * (1 - SIGMA))), 1)
    M = min(M, q - 1)
    W = rng.choice(q - 1, size=M, replace=False)
    hat = np.zeros(q - 1, dtype=np.complex128)
    hat[W] = np.exp(2j * np.pi * rng.random(M))
    Z = np.fft.fft(hat)
    absZ = np.abs(Z)
    reZ = np.real(Z)
    # Plancherel check: mean |Z|^2 == (q-1)/ (q-1) * sum|hat|^2 * (q-1) for numpy
    # numpy: sum|Z|^2 = (q-1) sum|hat|^2
    s2 = float(np.mean(absZ ** 2))
    plancherel_pred = float(np.sum(np.abs(hat) ** 2))
    # higher moments
    s4 = float(np.mean(absZ ** 4))
    s6 = float(np.mean(absZ ** 6))
    mx = float(absZ.max())
    # one-sided: max of Re Z (worst for positivity of main - Re Z)
    max_re = float(reZ.max())
    # Fejer-smoothed: nonnegative weights on a multiplicative interval — proxy:
    # convolve | periodic Fejer of width K
    K = max(M // 2, 2)
    # Fejer kernel on cyclic group length n=q-1: F(j) = sum_{|k|<K} (1-|k|/K) e^{...}
    # Apply to Z by multiplying hat by Fejer multiplier
    n = q - 1
    mult = np.zeros(n, dtype=np.float64)
    for k in range(-K + 1, K):
        mult[k % n] = 1.0 - abs(k) / K
    Zf = np.fft.fft(hat * np.fft.ifft(np.fft.fft(mult)))  # wrong — simpler:
    # Fejer on spatial side: smooth Z
    ker = np.array([1.0 - abs(k) / K for k in range(-K + 1, K)])
    ker /= ker.sum()
    ext = np.concatenate([reZ[-(K - 1):], reZ, reZ[: K - 1]])
    # only length match
    smooth = np.convolve(reZ, ker, mode="same")
    return dict(
        q=q, M=M,
        mean_abs2=s2, plancherel_sum_c2=plancherel_pred,
        mean_abs4=s4, mean_abs6=s6,
        max_abs=mx, rms=float(np.sqrt(s2)),
        max_re=max_re,
        max_re_smooth=float(smooth.max()),
        triangle=float(M),
        max_over_tri=mx / M,
        max_re_over_tri=max_re / M,
        smooth_re_over_tri=float(smooth.max()) / M,
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qs", type=int, nargs="+", default=[31, 61, 127, 251, 503])
    args = ap.parse_args()
    print(f"{'q':>5} {'M':>5} {'max/tri':>8} {'maxRe/tri':>10} {'smRe/tri':>9} "
          f"{'rms':>8} {'(E|Z|^4)^{1/4}':>14}")
    for q in args.qs:
        r = moments(q)
        m4 = r["mean_abs4"] ** 0.25
        print(f"{r['q']:5d} {r['M']:5d} {r['max_over_tri']:8.4f} "
              f"{r['max_re_over_tri']:10.4f} {r['smooth_re_over_tri']:9.4f} "
              f"{r['rms']:8.3f} {m4:14.3f}")
    print()
    print("Plancherel gives average-a (rms) ~ sqrt(M); max and max Re stay")
    print("a larger fraction of triangle at these sizes. Fejer smoothing reduces")
    print("the one-sided max only by a constant, not a power of q.")


if __name__ == "__main__":
    main()
