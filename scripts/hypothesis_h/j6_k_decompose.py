"""Decompose J6(I) = sum_{|k|<=K} N(kq) for I=(x,2x] and I=[1,x], x=q^{7/18}.

For each k report N(kq) / (|I|^6/q), and the cumulative excess over the main term.
Identifies which |k| carries the excess (obstacle localization).
Also counts the exact diagonal E6 = N(0) for integer equality.
"""
from __future__ import annotations

import argparse
import math

import numpy as np
from sympy import nextprime


def build_r3(lo: int, hi: int):
    """r3[n] = #{(a,b,c) in [lo,hi]^3 : a*b*c = n}."""
    r2 = np.zeros(hi * hi + 1, np.int64)
    for a in range(lo, hi + 1):
        r2[a * np.arange(lo, hi + 1)] += 1
    m = np.nonzero(r2)[0]
    v = r2[m]
    r3 = np.zeros(hi**3 + 1, np.float64)
    for c in range(lo, hi + 1):
        r3[c * m] += v
    return r3


def N_via_fft(r3: np.ndarray):
    """N(h) = sum_m r3(m) r3(m+h) for h = 0..len-1, via FFT autocorrelation."""
    L = len(r3)
    n = 1 << int(math.ceil(math.log2(2 * L)))
    F = np.fft.rfft(r3, n)
    N = np.rint(np.fft.irfft(F * np.conj(F), n)[:L]).astype(np.float64)
    return N


def run(q: int, which: str = "dyadic"):
    x = int(round(q ** (7 / 18)))
    if which == "dyadic":
        lo, hi = x + 1, 2 * x
        name = "(x,2x]"
    else:
        lo, hi = 1, x
        name = "[1,x]"
    L = hi - lo + 1
    r3 = build_r3(lo, hi)
    N = N_via_fft(r3)
    tot = float(r3.sum())  # = L^3
    main = tot**2 / (q - 1)
    # max |n-m| for products in [lo^3, hi^3]
    K = int((hi**3 - lo**3) // q) + 1
    # collect N(kq)
    ks = list(range(0, K + 1))
    vals = []
    for k in ks:
        h = k * q
        if h >= len(N):
            nk = 0.0
        else:
            nk = float(N[h])
        # for k>0, both +h and -h contribute equally if N symmetric
        vals.append((k, nk))

    # J6 = N(0) + 2 sum_{k=1}^K N(kq)  (N even)
    J6 = vals[0][1] + 2 * sum(v for k, v in vals[1:] if k * q < len(N))
    excess = J6 - main
    unit = main  # report in units of |I|^6/q ≈ main

    print(f"q={q} x={x} L={L} K={K} name={name}")
    print(f"  |I|^3={tot:.0f}  main=|I|^6/(q-1)={main:.4e}")
    print(f"  J6={J6:.4e}  (J6-main)/main={excess/main:+.4f}")
    print(f"  N(0)={vals[0][1]:.4e}  N(0)/main={vals[0][1]/main:.4f}  "
          f"(diagonal; expected ~ q^{{1/6}} below main asymptotically)")

    # per-k contributions in units of main; for k>0 count both signs via the 2*
    print(f"  {'k':>4} {'N(kq)':>12} {'2N/main':>10} {'cumul (J-main)/main':>20}")
    cumul = vals[0][1] - main  # start with diagonal vs main
    print(f"  {0:4d} {vals[0][1]:12.4e} {vals[0][1]/main:10.4f} {cumul/main:+20.4f}")
    for k, nk in vals[1:]:
        if k * q >= len(N):
            break
        contrib = 2 * nk
        cumul += contrib
        print(f"  {k:4d} {nk:12.4e} {contrib/main:10.4f} {cumul/main:+20.4f}")

    # localize: which |k|-bands carry absolute excess
    # compare each 2N(kq) to the 'fair share' 2*main/(2K+1) ≈ main/K
    fair = main / max(K, 1)
    print(f"  fair share per |k|-pair ~ main/K = {fair:.4e} ({fair/main:.4f} of main)")
    # sum of |2N(kq) - 2*mean| 
    nonzero = [2 * nk for k, nk in vals[1:] if k * q < len(N)]
    if nonzero:
        arr = np.array(nonzero)
        print(f"  nonzero-k: mean(2N)={arr.mean():.4e} sd={arr.std():.4e} "
              f"min={arr.min():.4e} max={arr.max():.4e}")
        # small-k vs large-k
        mid = max(len(arr) // 3, 1)
        print(f"  small |k| (1..{mid}): mean 2N/main={(arr[:mid]/main).mean():.4f}")
        print(f"  large |k| ({2*mid}..): mean 2N/main={(arr[2*mid:]/main).mean():.4f}"
              if 2 * mid < len(arr) else "  large: n/a")
    return dict(q=q, name=name, main=main, J6=J6, excess_ratio=excess / main,
                N0_ratio=vals[0][1] / main, K=K)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("qs", nargs="*", type=float)
    ap.add_argument("--both", action="store_true", help="run [1,x] and (x,2x]")
    args = ap.parse_args()
    sizes = [int(s) for s in args.qs] or [503, 1009, 5003, 10007, 30011]
    qs = [int(nextprime(s - 1)) for s in sizes]
    for q in qs:
        run(q, "dyadic")
        if args.both:
            run(q, "initial")
        print()


if __name__ == "__main__":
    main()
