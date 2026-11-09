#!/usr/bin/env python3
"""dh_right_scan.py T0 T1 [SIGMA0] [--exact]: zeros of the Davenport–Heilbronn function right of `Re s = SIGMA0`.

How the zero of `lib/dh/DHLocate5.lean` was found (`docs/research-opportunities.md`, §8.5). Floating point,
uncertified; CI does not run it. Needs numpy.

The function is Titchmarsh's `f` (`scripts/dh_sigma_scan.py`), a positive multiple of the library's `dh`: its
coefficients are real, `a_n = 1, κ, −κ, −1, 0` by `n mod 5`, and `f(s) = X(s) f(1 − s)` with
`X(s) = 5^{1/2−s} 2^s π^{s−1} Γ(1 − s) cos(πs/2)`. So

    f(s) ≈ Σ_{n ≤ x} a_n n^{−s} + X(s) Σ_{n ≤ x} a_n n^{s−1},   x = √(5t/2π),

the approximate functional equation, with an error of about `x^{−σ}`: a few percent at height `10³`, `10⁻³` at
`10⁴`. At height `10⁵` that is 300 terms a side, where the Euler–Maclaurin sum of `dh_sigma_scan.py` has `4·10⁵`.

The scan follows `arg f(SIGMA0 + it)` (default `SIGMA0 = 11/12`) in steps of `0.05`. `f → 1` as `Re s → ∞`, so by
the argument principle each zero right of the line turns the argument by `−2π` as `t` passes it, and a zero close to
the line on either side shows as a jump of nearly `π` between two samples. The script lists both kinds of height,
then polishes a zero near each by Newton's method on the exact `f` (Euler–Maclaurin), from the point of least `|f|`
of a grid, and prints its real part less `SIGMA0`. With `--exact` the scan itself uses the exact `f` (the cost per
unit height then grows like the height).

    python3 scripts/dh_right_scan.py 20000 200000      # about a minute, then the polishing
"""
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import dh_sigma_scan as ds  # noqa: E402

A = np.array([0.0, 1.0, float(ds.KAPPA), -float(ds.KAPPA), -1.0])  # a_n by n mod 5


def log_gamma(z):
    """`log Γ(z)` by Stirling's series, for `|z|` large."""
    z = np.asarray(z, dtype=complex)
    zi = 1.0 / z
    zi2 = zi * zi
    series = zi * (1 / 12.0 - zi2 * (1 / 360.0 - zi2 * (1 / 1260.0 - zi2 * (1 / 1680.0))))
    return (z - 0.5) * np.log(z) - z + 0.5 * np.log(2 * np.pi) + series


def log_x(s):
    """`log X(s)` for `Im s` large and positive, where `cos(πs/2) = e^{−iπs/2}/2` up to `e^{−πt}`."""
    s = np.asarray(s, dtype=complex)
    return ((0.5 - s) * np.log(5.0) + s * np.log(2.0) + (s - 1) * np.log(np.pi) + log_gamma(1 - s)
            - 1j * np.pi * s / 2 - np.log(2.0))


def f_afe(sigma, t):
    """`f(sigma + it)` for an array `t` of nearby heights, by the approximate functional equation."""
    t = np.asarray(t, dtype=float)
    x = int(np.sqrt(5 * float(np.mean(t)) / (2 * np.pi)))
    n = np.arange(1, x + 1)
    a = A[n % 5]
    n, a = n[a != 0].astype(float), a[a != 0]
    e = np.exp(-1j * np.outer(t, np.log(n)))
    main = e @ (a * n ** (-sigma))
    dual = np.conj(e) @ (a * n ** (sigma - 1))
    return main + np.exp(log_x(sigma + 1j * t)) * dual


def f_exact(pts, batch=50):
    """The exact `f` at the points `pts`, in batches."""
    pts = np.asarray(pts, dtype=complex)
    out = np.empty_like(pts)
    for i in range(0, len(pts), batch):
        out[i:i + batch] = ds.dh(pts[i:i + batch])
    return out


def scan(sigma0, t0, t1, h=0.05, exact=False, block=100.0):
    """The heights where `arg f(sigma0 + it)` winds, and where it jumps by more than `2` between samples."""
    events, last, cum, level, t = [], None, 0.0, 0, t0
    while t < t1:
        ts = t + np.arange(0, min(block, t1 - t), h)
        v = f_exact(sigma0 + 1j * ts) if exact else f_afe(sigma0, ts)
        if last is not None:
            v, ts = np.concatenate([[last], v]), np.concatenate([[ts[0] - h], ts])
        d = np.angle(v[1:] / v[:-1])
        for k in np.nonzero(np.abs(d) > 2.0)[0]:
            events.append((float(ts[k]), "jump"))
        c = cum + np.cumsum(d)
        lev = np.round(-c / (2 * np.pi)).astype(int)
        for k in np.nonzero(np.diff(np.concatenate([[level], lev])) != 0)[0]:
            events.append((float(ts[k + 1]), "winding"))
        level, cum, last = int(lev[-1]), float(c[-1]), v[-1]
        t += block
    return events


def polish(tc, s0=0.86, s1=1.15, exact=False):
    """A zero near height `tc`: Newton's method on the exact `f`, from the least `|f|` of a grid."""
    ts = np.arange(tc - 0.6, tc + 0.6, 0.005)
    best = None
    for sg in np.arange(s0, s1, 0.005):
        v = np.abs(f_exact(sg + 1j * ts) if exact else f_afe(sg, ts))
        k = int(np.argmin(v))
        if best is None or v[k] < best[0]:
            best = (float(v[k]), complex(sg, ts[k]))
    s = best[1]
    for _ in range(40):
        f, fp, fm = f_exact(np.array([s, s + 1e-6, s - 1e-6]))
        step = f / ((fp - fm) / 2e-6)
        s -= step
        if abs(step) < 1e-13:
            break
    return s, abs(f_exact(np.array([s]))[0])


def main():
    args = [a for a in sys.argv[1:] if a != "--exact"]
    exact = "--exact" in sys.argv
    t0, t1 = float(args[0]), float(args[1])
    sigma0 = float(args[2]) if len(args) > 2 else 11 / 12
    events = scan(sigma0, t0, t1, exact=exact)
    print(f"Re s = {sigma0:.6f}, {t0:g} ≤ t ≤ {t1:g}: {len(events)} heights flagged", flush=True)
    seen = []
    for tc, kind in events:
        if any(abs(tc - u) < 0.5 for u in seen):
            continue
        seen.append(tc)
        z, r = polish(tc, exact=exact or tc < 3000)
        side = "right" if z.real > sigma0 else "left"
        print(f"t ≈ {tc:.2f} ({kind}): zero at {z.real:.10f} + {z.imag:.8f} i, |f| = {r:.1e}, "
              f"Re s − {sigma0:.4f} = {z.real - sigma0:+.6f} ({side})", flush=True)


if __name__ == "__main__":
    main()
