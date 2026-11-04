#!/usr/bin/env python3
"""dh_sigma_scan.py T0 T1 [SIGMA0 SIGMA1]: zeros of the Davenport–Heilbronn function with real part above 1.

The function is Titchmarsh's (§10.25): `f(s) = ((1 − iκ)/2) L(s, χ) + ((1 + iκ)/2) L(s, χ̄)`, with `χ` the character mod 5
with `χ(2) = i` and `κ = (√(10 − 2√5) − 2)/(√5 − 1)`; `lib/dh` has `dh = 4cos²(θ/2)·f` (`formalisations/davenport-heilbronn.md`),
so the zeros are the same. `L(s, χ)` is evaluated as `5^{−s} Σ_a χ(a) ζ(s, a/5)`, with the Hurwitz zeta function by
Euler–Maclaurin (`N = max|Im s| + 60` terms and twelve Bernoulli corrections, in double precision; the error is below
`10⁻¹³` for `|Im s| ≤ 10⁴`, checked against mpmath).

The scan takes the rectangle `[SIGMA0, SIGMA1] × [T0, T1]` (default `[1, 3/2]`: beyond `3/2` the first coefficient
dominates and `f` has no zero) in windows of height 1, computes the winding number of `f` around each window's boundary
(steps `1/200` on the vertical sides and `1/100` on the horizontal ones), reports every window with a nonzero winding
number or a phase jump above `2.5` between consecutive samples (a zero close to the boundary), and then polishes a zero
in each such window by Newton's method from the grid point of least `|f|`. Needs numpy only; `docs/research-opportunities.md`
records what it found.
"""
import sys
from math import factorial

import numpy as np

SQ5 = np.sqrt(5.0)
KAPPA = (np.sqrt(10 - 2 * SQ5) - 2) / (SQ5 - 1)
CHI = {1: 1, 2: 1j, 3: -1j, 4: -1}                # χ(2) = i, χ(3) = χ(2)³ = −i, χ(4) = −1
BERN = [1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66, -691 / 2730, 7 / 6, -3617 / 510, 43867 / 798,
        -174611 / 330, 854513 / 138, -236364091 / 2730]   # B₂, …, B₂₄


def hurwitz(s, a, N=None, K=12):
    """ζ(s, a) for an array `s`, `0 < a ≤ 1`, by Euler–Maclaurin with `N` direct terms and `K` Bernoulli terms."""
    s = np.asarray(s, dtype=complex)
    if N is None:
        N = int(np.max(np.abs(s.imag))) + 60
    n = np.arange(N, dtype=float)[:, None] + a
    direct = np.sum(np.exp(-s[None, :] * np.log(n)), axis=0)
    x = N + a
    lx = np.log(x)
    tail = np.exp((1 - s) * lx) / (s - 1) + 0.5 * np.exp(-s * lx)
    poch = np.ones_like(s)
    for k in range(1, K + 1):
        poch = s.copy() if k == 1 else poch * (s + 2 * k - 3) * (s + 2 * k - 2)
        tail += BERN[k - 1] / factorial(2 * k) * poch * np.exp(-(s + 2 * k - 1) * lx)
    return direct + tail


def L(s, conj=False, N=None):
    s = np.asarray(s, dtype=complex)
    tot = np.zeros_like(s)
    for a, c in CHI.items():
        tot += (np.conj(c) if conj else c) * hurwitz(s, a / 5.0, N=N)
    return np.exp(-s * np.log(5.0)) * tot


def dh(s, N=None):
    """Titchmarsh's `f`; the library's `dh` is a positive real multiple of it."""
    s = np.asarray(s, dtype=complex)
    return 0.5 * (1 - 1j * KAPPA) * L(s, False, N) + 0.5 * (1 + 1j * KAPPA) * L(s, True, N)


def newton(s0, iters=50, tol=1e-13, h=1e-6):
    s = complex(s0)
    for _ in range(iters):
        f = complex(dh(np.array([s]))[0])
        fp = complex((dh(np.array([s + h])) - dh(np.array([s - h])))[0]) / (2 * h)
        step = f / fp
        s -= step
        if abs(step) < tol:
            break
    return s, abs(complex(dh(np.array([s]))[0]))


def boundary(t, sig0, sig1, dt, hv=0.005, hh=0.01):
    """The boundary of `[sig0, sig1] × [t, t + dt]`, counter-clockwise."""
    bottom = sig0 + np.arange(0, sig1 - sig0, hh) + 1j * t
    right = sig1 + 1j * (t + np.arange(0, dt, hv))
    top = (sig1 - np.arange(0, sig1 - sig0, hh)) + 1j * (t + dt)
    left = sig0 + 1j * (t + dt - np.arange(0, dt, hv))
    return np.concatenate([bottom, right, top, left])


def winding(vals):
    v = np.append(vals, vals[0])
    d = np.angle(v[1:] / v[:-1])
    return d.sum() / (2 * np.pi), np.abs(d).max()


def main():
    t0, t1 = float(sys.argv[1]), float(sys.argv[2])
    sig0 = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
    sig1 = float(sys.argv[4]) if len(sys.argv) > 4 else 1.5
    dt, batch = 1.0, 40
    found = []
    t = t0
    while t < t1:
        ts = [t + k * dt for k in range(batch) if t + k * dt < t1]
        pts = np.concatenate([boundary(tt, sig0, sig1, dt) for tt in ts])
        vals = dh(pts)
        npts = len(pts) // len(ts)
        for i, tt in enumerate(ts):
            w, jmax = winding(vals[i * npts:(i + 1) * npts])
            if abs(w) > 0.3 or jmax > 2.5:
                print(f"window t in [{tt:.2f}, {tt + dt:.2f}]: winding {w:+.3f}, max phase jump {jmax:.2f}", flush=True)
                if abs(w) > 0.3:
                    found.append(tt)
        t += batch * dt
    print("=== Newton polishing ===", flush=True)
    for tt in found:
        sg, tg = np.arange(sig0, sig1, 0.01), np.arange(tt, tt + dt, 0.01)
        S, T = np.meshgrid(sg, tg)
        grid = (S + 1j * T).ravel()
        s0 = grid[np.argmin(np.abs(dh(grid)))]
        z, r = newton(s0)
        print(f"zero near {s0:.3f}: s = {z.real:.15f} + {z.imag:.15f} i   |f(s)| = {r:.2e}", flush=True)


if __name__ == "__main__":
    main()
