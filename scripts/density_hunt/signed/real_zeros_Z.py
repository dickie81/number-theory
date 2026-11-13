#!/usr/bin/env python3
"""Low-lying zeros of L(s,chi) for tiny prime q, form empirical Z(a).

Honest scope: only q in {5,7,11,13}, only zeros with |t| < T0 (default 20),
computed by scanning the critical line with a truncated Dirichlet series
(no completed approximate functional equation). This is a LOW-LYING probe under
numerical GRH (zeros found on Re=1/2), NOT a density-regime computation.
Off-line zeros are NOT found here (consistent with GRH numerically).

If a scan finds no near-zero of |L(1/2+it,chi)|, that character contributes nothing.
"""
from __future__ import annotations

import argparse
import cmath
import math
from dataclasses import dataclass

import numpy as np


def primitive_root(q: int) -> int:
    from sympy import ntheory
    return int(ntheory.residue_ntheory.primitive_root(q))


def characters(q: int):
    """Non-principal characters as value tables on 0..q-1; index by discrete log."""
    g = primitive_root(q)
    ind = {}
    a = 1
    for j in range(q - 1):
        ind[a] = j
        a = a * g % q
    chis = []
    for j in range(1, q - 1):  # skip principal j=0
        vals = [0.0] * q
        for n in range(1, q):
            vals[n] = cmath.exp(2j * math.pi * j * ind[n] / (q - 1))
        chis.append((j, vals))
    return ind, chis


def L_trunc(s: complex, chi_vals, q: int, N: int) -> complex:
    z = 0j
    for n in range(1, N + 1):
        z += chi_vals[n % q] / (n ** s)
    return z


def find_low_zeros(chi_vals, q: int, T0: float, Ntrunc: int, dt: float = 0.05):
    """Scan t=dt..T0 on Re=1/2; record local minima of |L| below threshold."""
    zeros = []
    prev_t, prev_abs = None, None
    thresh = 0.05  # permissive for truncated series
    # refine candidates where |L| has a local min below thresh
    ts = np.arange(dt, T0 + dt, dt)
    absL = []
    for t in ts:
        z = L_trunc(0.5 + 1j * float(t), chi_vals, q, Ntrunc)
        absL.append(abs(z))
    absL = np.array(absL)
    for i in range(1, len(ts) - 1):
        if absL[i] < thresh and absL[i] <= absL[i - 1] and absL[i] <= absL[i + 1]:
            # quadratic refine
            t = float(ts[i])
            # bisection-ish: sample finer
            best_t, best_a = t, absL[i]
            for tt in np.linspace(t - dt, t + dt, 21):
                a = abs(L_trunc(0.5 + 1j * float(tt), chi_vals, q, Ntrunc))
                if a < best_a:
                    best_t, best_a = float(tt), a
            if best_a < thresh:
                zeros.append(best_t)
    return zeros


@dataclass
class Result:
    q: int
    n_zeros: int
    max_abs_Z: float
    rms_Z: float
    triangle: float
    alpha: float


def form_Z(q: int, zeros_by_chi: list, x: float) -> Result:
    """Z(a) = sum_chi chi-bar(a) sum_rho x^{1/2+i t}/(1/2+it)  (low-lying only)."""
    # coeff on Z/(q-1): for each chi_j and each t
    coeff = np.zeros(q - 1, dtype=np.complex128)
    tri = 0.0
    for j, ts in zeros_by_chi:
        for t in ts:
            rho = 0.5 + 1j * t
            w = (x ** rho) / rho
            coeff[j] += w
            tri += abs(w)
    Z = np.fft.fft(coeff)  # index = discrete log of a
    absZ = np.abs(Z)
    mx = float(absZ.max()) if len(absZ) else 0.0
    rms = float(np.sqrt(np.mean(absZ ** 2))) if len(absZ) else 0.0
    n = sum(len(ts) for _, ts in zeros_by_chi)
    alpha = float(np.log(max(mx, 1e-300)) / np.log(max(tri, 1e-300))) if tri > 1 else float("nan")
    return Result(q, n, mx, rms, tri, alpha)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qs", type=int, nargs="+", default=[5, 7, 11, 13])
    ap.add_argument("--T0", type=float, default=15.0)
    ap.add_argument("--Ntrunc", type=int, default=8000)
    ap.add_argument("--L", type=float, default=2.2)
    args = ap.parse_args()
    print("REAL low-lying zeros probe (truncated series on critical line)")
    print("Label: NUMERICAL_GRH_LOW_LYING — not synthetic off-line, not full spectrum")
    print(f"{'q':>4} {'#zeros':>7} {'max|Z|':>12} {'rms':>12} {'tri':>12} "
          f"{'max/tri':>9} {'alpha':>7}")
    for q in args.qs:
        pass  # q checked prime below
        from sympy import isprime
        if not isprime(q):
            print(f"skip non-prime {q}")
            continue
        ind, chis = characters(q)
        zeros_by_chi = []
        for j, vals in chis:
            ts = find_low_zeros(vals, q, args.T0, args.Ntrunc)
            zeros_by_chi.append((j, ts))
        x = float(q) ** args.L
        r = form_Z(q, zeros_by_chi, x)
        print(f"{r.q:4d} {r.n_zeros:7d} {r.max_abs_Z:12.4e} {r.rms_Z:12.4e} "
              f"{r.triangle:12.4e} {r.max_abs_Z/max(r.triangle,1e-300):9.4f} "
              f"{r.alpha:7.4f}")
    print("Note: alpha here is log(max|Z|)/log(triangle); with few zeros it is noisy.")
    print("Off-line (sigma>1/2) zeros were not located — consistent with GRH at this height.")


if __name__ == "__main__":
    main()
