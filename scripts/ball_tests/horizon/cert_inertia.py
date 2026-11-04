"""Certify lambda_min brackets by Sylvester inertia: LDL in arb of G - t*M; #negative pivots = #eigs < t.
M = I for lambda_min(G_N), or the flat model d_1*min(m, n) for the pencil.

    python3 cert_inertia.py N [PREC] [DIGITS]   # bracket the float64 estimates to relative 10^-DIGITS (default 6)

The float64 estimates are computed here from scripts/ball_orbit.py, so no data file is needed.
"""
import os, sys
from fractions import Fraction
import numpy as np, scipy.linalg as sl
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'hunt')); sys.path.insert(0, os.path.join(HERE, '..', '..'))
from flint import arb, ctx
from cert_zeta import make_kover
import ball_orbit as bo
N = int(sys.argv[1])
ctx.prec = int(sys.argv[2]) if len(sys.argv) > 2 else 256
DIG = int(sys.argv[3]) if len(sys.argv) > 3 else 6
Kover = make_kover(N)
G = bo.gram(N); m = np.arange(1, N+1)
EST = {'I': np.linalg.eigvalsh(G)[0],
       'F': sl.eigh(G, G[0, 0]*np.minimum.outer(m, m).astype(float), eigvals_only=True, subset_by_index=[0, 0])[0]}
def negcount(t, kind):
    d1 = Kover(Fraction(1))
    A = [[None]*N for _ in range(N)]
    for m in range(1, N+1):
        for n in range(1, m+1):
            M = (1 if m == n else 0) if kind == 'I' else d1*n
            A[m-1][n-1] = m*Kover(Fraction(m, n)) - t*M
    neg = 0
    for k in range(N):
        p = A[k][k]
        if p < 0: neg += 1
        elif not p > 0: return None
        for i in range(k+1, N):
            f = A[i][k]/p; Ai = A[i]
            for j in range(k+1, i+1): Ai[j] = Ai[j] - f*A[j][k]
    return neg
for kind in ['I', 'F']:
    lam = float(EST[kind])
    eps = arb(10)**-DIG
    lo, hi = arb(lam)*(1-eps), arb(lam)*(1+eps)
    print(N, kind, 'float64 %.10e' % lam, 'eigs<lo:', negcount(lo, kind), 'eigs<hi:', negcount(hi, kind), flush=True)
