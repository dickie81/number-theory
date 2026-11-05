#!/usr/bin/env python3
"""The first M zeros of ζ on the critical line, by the Riemann–Siegel formula, vectorised. Uncertified numerics.

    python3 scripts/zeta_zeros_rs.py M OUT [--check FILE]    # one ordinate per line; --check compares with a table

Z(t) with the correction terms C₀ = Ψ and C₁ = −Ψ‴/(96π²), Ψ(p) = cos(2π(p² − p − 1/16))/cos(2πp) taken by Taylor
polynomials near its removable singularities p = 1/4, 3/4; the sign changes of Z on a grid of step 0.02 from t = 14,
refined by bisection. The count is checked against θ(T)/π + 1 (|S(T)| small) and the smallest gap is printed (the pair
at 17143.79, 17143.82 is real). Against mpmath: 2.5·10⁻³ on the first ten zeros (the formula is poor at t < 50),
below 10⁻⁴ above height 240, 3·10⁻⁷ at heights 3500–25000; 30000 zeros, to height 25755, take about 2.5 minutes.
scripts/ball_rate.py takes the result through --zeros-file (use mpmath's zeros for the first 2000, this for the rest).
"""
import sys, time, math
import numpy as np
import sympy as sp

# Ψ(p) = cos(2π(p² − p − 1/16))/cos(2πp) is entire (the zeros of the denominator are removable); its quotient form
# loses all precision near p = 1/4, 3/4, so there we use Taylor polynomials (degree 16) about those points.
_p, _h = sp.symbols('p h')
_Psi = sp.cos(2*sp.pi*(_p**2 - _p - sp.Rational(1, 16))) / sp.cos(2*sp.pi*_p)
_Psi3 = sp.diff(_Psi, _p, 3)
Psi0_q = sp.lambdify(_p, _Psi, 'numpy')
Psi3_q = sp.lambdify(_p, _Psi3, 'numpy')
def _taylor(expr, c, deg):
    ser = sp.series(expr.subs(_p, c + _h), _h, 0, deg + 1).removeO()
    return sp.lambdify(_h, sp.expand(ser), 'numpy')
_T0 = {c: _taylor(_Psi, sp.Rational(c), 16) for c in ("1/4", "3/4")}
_T3 = {c: _taylor(_Psi3, sp.Rational(c), 16) for c in ("1/4", "3/4")}

def Psi0(p):
    out = Psi0_q(p)
    for c, fn in _T0.items():
        cc = float(sp.Rational(c)); near = np.abs(p - cc) < 0.04
        out = np.where(near, fn(p - cc), out)
    return out

def Psi3(p):
    out = Psi3_q(p)
    for c, fn in _T3.items():
        cc = float(sp.Rational(c)); near = np.abs(p - cc) < 0.04
        out = np.where(near, fn(p - cc), out)
    return out

def theta(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)

def Z(t):
    """Riemann–Siegel Z(t) for an array t (t ≥ 50), with C₀ and C₁."""
    t = np.asarray(t, dtype=float)
    a = np.sqrt(t/(2*np.pi)); M = np.floor(a).astype(int); p = a - M
    th = theta(t)
    Mmax = int(M.max())
    n = np.arange(1, Mmax + 1, dtype=float)
    # main sum, masked to n ≤ M(t)
    S = np.zeros_like(t)
    for k0 in range(0, Mmax, 64):
        nn = n[k0:k0+64]
        term = np.cos(th[:, None] - t[:, None]*np.log(nn)[None, :]) / np.sqrt(nn)[None, :]
        term[nn[None, :] > M[:, None]] = 0.0
        S += term.sum(axis=1)
    # the correction (p near 1/4, 3/4 is a removable singularity of Ψ; keep p away from it by a tiny shift)
    with np.errstate(divide="ignore", invalid="ignore"):
        C0 = Psi0(p); C1 = -Psi3(p)/(96*np.pi**2)
    R = (-1.0)**(M - 1) * a**(-0.5) * (C0 + C1 / a)
    return 2*S + R

def zeros(M_want, t0=10.0):
    h = 0.02
    found = []
    T = t0; t_end_guess = 2*np.pi*M_want/np.log(M_want/(2*np.pi*np.e)) * 1.02 + 50
    chunk = 200000
    t_prev = None; z_prev = None
    while len(found) < M_want and T < t_end_guess * 1.5:
        tt = T + h*np.arange(chunk + 1)
        tt = tt[tt >= 14.0]
        zz = Z(tt)
        if t_prev is not None:
            tt = np.concatenate([[t_prev], tt]); zz = np.concatenate([[z_prev], zz])
        s = np.sign(zz)
        idx = np.nonzero(s[:-1]*s[1:] < 0)[0]
        lo, hi = tt[idx].copy(), tt[idx+1].copy(); zlo = zz[idx].copy()
        for _ in range(28):  # bisection to ~1e-9
            mid = 0.5*(lo + hi); zm = Z(mid)
            left = np.sign(zm) == np.sign(zlo)
            lo = np.where(left, mid, lo); zlo = np.where(left, zm, zlo); hi = np.where(left, hi, mid)
        found.extend((0.5*(lo+hi)).tolist())
        t_prev, z_prev = tt[-1], zz[-1]
        T = tt[-1] + h
    return np.array(found[:M_want]), np.array(found)

if __name__ == "__main__":
    M = int(sys.argv[1]); out = sys.argv[2]
    t0 = time.time()
    g, allg = zeros(M)
    # the count check: N(T) = θ(T)/π + 1 + S(T), with |S(T)| typically < 1
    T = g[-1]; expected = theta(T)/np.pi + 1
    print(f"{len(g)} zeros in {time.time()-t0:.0f}s, last at {T:.6f}; θ(T)/π + 1 = {expected:.3f} (count {len(g)}; S(T) ≈ {len(g)-expected:+.3f})")
    gaps = np.diff(g); print(f"min gap {gaps.min():.4f} at {g[gaps.argmin()]:.3f}; max gap {gaps.max():.4f}")
    np.savetxt(out, g, fmt="%.9f")
    if len(sys.argv) > 4 and sys.argv[3] == "--check":
        ref = np.loadtxt(sys.argv[4]); k = min(len(ref), len(g))
        print(f"against the reference ({k} zeros): max |diff| = {np.abs(ref[:k]-g[:k]).max():.2e}")
