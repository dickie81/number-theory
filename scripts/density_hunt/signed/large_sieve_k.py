#!/usr/bin/env python3
"""Does a large-sieve / Tao argument over character-index k obstruct linear alignment?

The coefficient sequence c_k = 1_W(k) * exp(i α k) is a modulated indicator.
Large sieve inequalities bound average of |sum c_k χ(k)| over characters, which is
exactly Plancherel again: they control average_a |Z(a)|, not max_a |Z(a)|.

Tao on Z/(q-1): |supp c| + |supp hat c| ≥ (q-1)+1 if q-1 prime (Sophie Germain /
safeprime case). When c = modulated 1_W with |W|=M, hat c = Z is the Fourier
transform — Tao says |supp Z| ≥ n+1-M, i.e. Z non-sparse, which we already knew.
It does NOT bound ||Z||_∞ / ||c||_1.

Numeric: for the linear-phase adversary, report ||Z||_∞ / ||c||_1 (=1) and the
fraction of a with |Z(a)| > (1/2) max (support density).
"""
from __future__ import annotations

import argparse
import numpy as np
from barrier_linear_zeros import build, A, SIGMA


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qs", type=int, nargs="+",
                    default=[31, 61, 127, 251, 503, 1009, 2003])
    ap.add_argument("--L", type=float, default=2.2)
    args = ap.parse_args()
    print(f"{'q':>6} {'n=q-1':>7} {'n prime?':>9} {'M':>5} {'||Z||∞/△':>10} "
          f"{'frac>|max|/2':>14} {'Tao lower |supp Z|':>20}")
    for q in args.qs:
        r = build(q, args.L, a0_ind=1, seed=0)
        n = q - 1
        # rebuild Z to get support fraction
        from barrier_linear_zeros import build as B
        # manual
        x = float(q) ** args.L
        logx = np.log(x)
        amp = x ** SIGMA
        M_max = min(max(int(q ** (A * (1 - SIGMA))), 1), n - 1)
        # same W construction as build
        rng = np.random.default_rng(0)
        candidates = list(range(1, n))
        rng.shuffle(candidates)
        W = set()
        for k in candidates:
            if len(W) >= M_max:
                break
            mk = (-k) % n
            if mk == 0:
                continue
            if mk == k:
                W.add(k)
            else:
                if len(W) + 2 <= M_max:
                    W.add(k); W.add(mk)
                elif len(W) + 1 <= M_max:
                    W.add(k)
        coeff = np.zeros(n, dtype=np.complex128)
        a0_ind = 1
        for k in W:
            gamma = 2 * np.pi * k * a0_ind / (n * logx)
            coeff[k] = amp * np.exp(1j * gamma * logx)
        Z = np.fft.fft(coeff)
        absZ = np.abs(Z)
        mx = absZ.max()
        frac = float(np.mean(absZ > 0.5 * mx))
        M = len(W)
        tao = (n + 1 - M) if is_prime(n) else None
        # actual support (above numerical eps)
        supp = int(np.sum(absZ > 1e-8 * mx))
        print(f"{q:6d} {n:7d} {str(is_prime(n)):>9} {M:5d} {mx/(M*amp):10.6f} "
              f"{frac:14.4f} {str(tao) if tao else 'n/a (n composite)':>20} "
              f"(actual supp≈{supp})")
    print()
    print("Verdict: large-sieve / Tao over k force Z to be NON-SPARSE on a,")
    print("but the spike at a0 still has height = triangle. No obstruction to")
    print("every-a saving failure (i.e. no forced θ>0 saving).")


if __name__ == "__main__":
    main()
