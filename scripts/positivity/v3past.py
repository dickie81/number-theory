"""Past log 3/2 (docs/weil-vprime-log3.md, "Beyond log 3/2"): the Zhu-reduced matrix on V' at support L, with every
prime power log n < 2L in the weight, in double precision (not certified).

    R = b*·I + (1/pi) int_0^T# (Psi_L - b*) T_n T_m,   b* = log(T#/2pi) - 1/T# - sum_{log n < 2L} 2 Lambda(n)/sqrt n,

with T_n(t) = (-1)^floor(n/2) sqrt(2L) sqrt(2n+1) j_n(L t) the transform of the n-th normalised Legendre mode on [-L, L].
It prints lambda_min of R on V' (even: x0 = 0 and the cosh pole; odd: the sinh pole) and, for the odd sector, without
the constraint, for each head size H. Usage: python3 scripts/positivity/v3past.py H1,H2,... L:T# [L:T# ...]
(NODES=… sets the quadrature size, default 6000)."""
import math, os, sys
import numpy as np, mpmath as mp
from scipy.special import spherical_jn
from scipy.linalg import null_space
def vM(n):
    for p in range(2, n + 1):
        if n % p == 0:
            k, m = 0, n
            while m % p == 0: m //= p; k += 1
            return math.log(p) if m == 1 else 0.0
    return 0.0
def run(L, Tsharp, Hs, nodes=int(os.environ.get("NODES", "6000"))):
    pw = [(n, 2 * vM(n) / math.sqrt(n)) for n in range(2, int(math.exp(2 * L)) + 2) if math.log(n) < 2 * L and vM(n) > 0]
    S = sum(c for _, c in pw)
    bstar = math.log(Tsharp / (2 * math.pi)) - 1 / Tsharp - S
    xg, wg = np.polynomial.legendre.leggauss(nodes); t = (xg + 1) * Tsharp / 2; wt = wg * Tsharp / 2
    psi = np.array([float(mp.re(mp.digamma(0.25 + 0.5j * tt))) for tt in t]) - math.log(math.pi)
    for n, c in pw: psi -= c * np.cos(t * math.log(n))
    xs, ws = np.polynomial.legendre.leggauss(400); u = xs * L; wu = ws * L
    legT = lambda n, x: np.polynomial.legendre.Legendre.basis(n)(x / L) * math.sqrt((2 * n + 1) / (2 * L))
    out = []
    for H in Hs:
        res = {}
        for par in (0, 1):
            ns = [2 * i + par for i in range(H)]
            Th = np.array([(-1) ** (n // 2) * math.sqrt(2 * L) * math.sqrt(2 * n + 1) * spherical_jn(n, L * t) for n in ns])
            R = bstar * np.eye(H) + (Th * ((psi - bstar) * wt)) @ Th.T / math.pi
            if par == 0:
                p = np.array([np.sum(wu * legT(n, u) * np.cosh(u / 2)) for n in ns]); e0 = np.zeros(H); e0[0] = 1
                C = np.vstack([p, e0])
            else:
                C = np.array([[np.sum(wu * legT(n, u) * np.sinh(u / 2)) for n in ns]])
            N = null_space(C)
            res[par] = (np.linalg.eigvalsh(N.T @ R @ N)[0], np.linalg.eigvalsh(R)[0])
        out.append((H, res))
    return [n for n, _ in pw], bstar, out
if __name__ == "__main__":
    Hs = [int(h) for h in sys.argv[1].split(",")]
    for spec in sys.argv[2:]:
        L, Ts = (float(x) for x in spec.split(":"))
        ns, b, out = run(L, Ts, Hs)
        for H, res in out:
            print(f"L={L:.4f} T#={Ts:g} primes={ns} b*={b:+.3f} H={H}: V' even {res[0][0]:+.3e}  odd {res[1][0]:+.3e} "
                  f"(odd unconstrained {res[1][1]:+.3e})", flush=True)
