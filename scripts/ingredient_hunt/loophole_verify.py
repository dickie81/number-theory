#!/usr/bin/env python3
"""Sceptical verification of the ADV-realisability loophole.

1. CGL Thm 1.3 / Prop 3.1: LV for arbitrary |a_n|<=1 (matrix M is coefficient-free;
   Lemma 4.1 absorbs |b_n|<=1). Main density route uses this general LV.
2. At T=1 with short mollifier, class-I reduces to interval sums of length
   x <= q^{1/2+eps}; critical meeting of 4th/6th moments at x=q^{7/18}, V=x^{5/7}.
3. The N=q^{7/9}, V=N^{5/7} interval test from ingredient-hunt is NOT the T=1
   detector object: by Polya-Vinogradov, |sum_{n in I} chi(n)| << sqrt(q) log q
   < N^{5/7}=q^{5/9} for large q, so |W_crit|=0 trivially — a toy, not a density input.

This script:
  (A) Confirms PV forbids critical LV for intervals of length N=q^{7/9}.
  (B) Counts large values for intervals of the TRUE T=1 length x=q^{7/18}.
  (C) Dual-moment bookkeeping for completed sums.
  (D) Correlation of ADV (at N=q^{7/9}) with detector convolutions / power-raised coeffs.
"""
from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
from sympy import factorint, isprime, mobius, nextprime, primitive_root

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cgl_s3"))
from probe import Field, tpm  # noqa: E402

SIGMA = 5 / 7


def character_sums_interval(q: int, x: int, V: float) -> dict:
    """Count non-principal chi with |sum_{n=1}^{min(x,q-1)} chi(n)| >= V
    and also for dyadic block (x, 2x] capped below q.
    Uses FFT over (Z/q)*.
    """
    g = int(primitive_root(q))
    # ind[a] = discrete log; build chi-sum via FFT of indicator of [1,x]
    nmax = min(x, q - 1)
    A = np.zeros(q - 1, dtype=np.complex128)
    a = 1
    # values at residue a=g^j
    # S(chi_k) = sum_{n=1}^{nmax} chi_k(n) = sum_j 1_{pw[j]<=nmax} exp(2pi i k j /(q-1))
    # So place 1 at indices j where g^j in 1..nmax
    pw = np.empty(q - 1, dtype=np.int64)
    aa = 1
    for j in range(q - 1):
        pw[j] = aa
        aa = aa * g % q
    mask = (pw >= 1) & (pw <= nmax)
    A[mask] = 1.0
    S = np.fft.fft(A)  # S[k] = sum over n in [1,nmax] chi_k(n), k=0 is principal
    absS = np.abs(S)
    # exclude principal k=0
    absS[0] = 0.0
    Wcrit = int(np.sum(absS >= V))
    # dyadic (x, 2x]
    lo, hi = x + 1, min(2 * x, q - 1)
    A2 = np.zeros(q - 1, dtype=np.complex128)
    mask2 = (pw >= lo) & (pw <= hi)
    A2[mask2] = 1.0
    S2 = np.fft.fft(A2)
    absS2 = np.abs(S2)
    absS2[0] = 0.0
    V2 = float((hi - lo + 1) ** SIGMA) if hi >= lo else 1.0
    # use same relative: V for length x; for dyadic use (length)^{5/7}
    Ldy = max(hi - lo + 1, 1)
    Vdy = Ldy ** SIGMA
    Wdy = int(np.sum(absS2 >= Vdy))
    pv = math.sqrt(q) * math.log(q)
    return dict(
        q=q, x=x, V=V, pv=pv, W_init=Wcrit, max_init=float(absS.max()),
        W_dyadic=Wdy, V_dyadic=Vdy, max_dyadic=float(absS2.max()),
        pv_beats_V=(pv < V),
    )


def dual_bookkeeping() -> None:
    """Exponent comparison: 2k-moments of dual short sums vs MVT 2/3."""
    print("=== Dual / completing bookkeeping (analytic, no fabrication) ===")
    print("Main CGL critical: N = q^{7/9}, V = N^{5/7} = q^{5/9}.")
    print("  Polya-Vinogradov: |S_I(chi)| << q^{1/2} log q for ANY interval I.")
    print("  Compare: q^{5/9} vs q^{1/2}: 5/9 > 1/2, so PV forbids |S_I|>=V for large q.")
    print("  => |W|=0 for pure interval coeffs at (N,V)=(q^{7/9},N^{5/7}). TRIVIAL.")
    print("  This object is NOT what Thm 1.3/1.4 feeds on (those allow arbitrary a_n).")
    print()
    print("T=1 detector critical (cgl-s3 §8): x = q^{7/18}, V = x^{5/7} = q^{5/18}.")
    print("  PV cap q^{1/2} >> q^{5/18}: large values ARE possible.")
    print("  Fourth moment => |W| << q * x^2 / V^4 = q^{1 - 6*(7/18)/7} = q^{2/3}.")
    print("  Sixth moment (MVT) => |W| << x^{6(1-sigma)} = q^{12/7 * 7/18} = q^{2/3}.")
    print("  Both meet at q^{2/3} = MVT face. Completing to length q/x = q^{11/18}:")
    print("  dual sum length > sqrt(q); moments of dual don't beat q^{2/3} by known")
    print("  complete-sum bounds alone (Weil => individual |S|<<sqrt(q), same PV).")
    print()
    # Compare exponents if one had sharp 2k moment for dual of length q^{2/9}
    # (that would be for completing N=q^{7/9} sums — already killed by PV)
    print("If one ignores PV and formally completes N=q^{7/9} to M=q^{2/9}:")
    print("  |S_N| ~ sqrt(q)/N^0 * |S_M^*| roughly |tau|/sqrt(q) * |dual|.")
    print("  More precisely |sum_{n<=N} chi(n)| ~= |tau(chi)|/q * |sum_{|m|<q/N} chi-bar(m)/(1-e(...))|")
    print("  Standard: << sqrt(q) log q always. Formal dual-moment cannot beat PV.")
    print()


def power_raised_corr(q: int) -> None:
    """Can ADV be approximated by mu-convolutions or their divisor-bounded powers?"""
    F = Field(q)
    R = max(1, int(round(q ** (2 / 3))))
    _, _, badv, _ = tpm(F, np.ones(len(F.ns), dtype=complex), R, iters=25)

    def corr(b):
        b = b / (np.linalg.norm(b) + 1e-300)
        a = badv / (np.linalg.norm(badv) + 1e-300)
        return float(abs(np.vdot(a, b)))

    ns = F.ns
    # short mollifier detector
    X = max(2, int(F.N ** 0.05))
    det = np.zeros(len(ns), dtype=complex)
    for i, n in enumerate(ns):
        s = 0
        nn = int(n)
        d = 1
        while d * d <= nn:
            if nn % d == 0:
                if d <= X:
                    s += mobius(d)
                o = nn // d
                if o != d and o <= X:
                    s += mobius(o)
            d += 1
        det[i] = s
    # Type I style: 1 on [N,2N] (=interval)
    interval = np.ones(len(ns), dtype=complex)
    # divisor-bounded 'power raise' proxy: d_2(n) clipped to [-1,1] after norm
    d2 = np.array([complex(sum(1 for d in range(1, int(n) + 1) if int(n) % d == 0)) for n in ns])
    d2 = d2 / (np.max(np.abs(d2)) + 1e-300)
    # random |b|<=1 multiplicative: random completely multiplicative ±1
    rng = np.random.default_rng(0)
    signs = {}
    def mul_rand(n):
        n = int(n)
        fac = factorint(n)
        v = 1
        for p, e in fac.items():
            if p not in signs:
                signs[p] = 1 if rng.random() < 0.5 else -1
            v *= signs[p] ** e
        return complex(v)
    mul = np.array([mul_rand(n) for n in ns])

    print(f"=== ADV correlation with structure classes at q={q}, N={F.N} ===")
    for name, b in [
        ("interval", interval),
        ("short det X=N^0.05", det),
        ("d2-normalized", d2),
        ("rand completely-mult ±1", mul),
    ]:
        if np.linalg.norm(b) < 1e-12:
            print(f"  {name}: zero")
            continue
        print(f"  corr(ADV, {name}) = {corr(b):.4f}")


def main():
    dual_bookkeeping()
    print("=== (A) Interval LV at CGL Thm length N=q^{7/9}, V=N^{5/7} ===")
    print(f"{'q':>10} {'N':>8} {'V=N^σ':>12} {'PV':>12} {'PV<V?':>7} {'W_init':>7} {'max|S|':>10}")
    for q0 in [503, 1009, 5003, 10007, 30011]:
        q = q0 if isprime(q0) else int(nextprime(q0))
        N = int(round(q ** (7 / 9)))
        V = N ** SIGMA
        r = character_sums_interval(q, N, V)
        print(f"{q:10d} {N:8d} {V:12.4e} {r['pv']:12.4e} {str(r['pv_beats_V']):>7} "
              f"{r['W_init']:7d} {r['max_init']:10.4e}")

    print()
    print("=== (B) T=1 detector length x=q^{7/18}, V=x^{5/7} ===")
    print(f"{'q':>10} {'x':>8} {'V':>12} {'W_[1,x]':>8} {'max':>10} {'W_(x,2x]':>9} {'max_dy':>10} {'q^{2/3}':>8}")
    for q0 in [10007, 30011, 100003]:
        q = q0 if isprime(q0) else int(nextprime(q0))
        x = max(2, int(round(q ** (7 / 18))))
        V = x ** SIGMA
        r = character_sums_interval(q, x, V)
        print(f"{q:10d} {x:8d} {V:12.4e} {r['W_init']:8d} {r['max_init']:10.4e} "
              f"{r['W_dyadic']:9d} {r['max_dyadic']:10.4e} {q**(2/3):8.1f}")

    print()
    power_raised_corr(10007)


if __name__ == "__main__":
    main()
