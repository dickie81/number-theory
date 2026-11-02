"""Certify lambda_min brackets by Sylvester inertia: LDL in arb of G - t*M; #negative pivots = #eigs < t (M=I or flat F)."""
import sys, json
from fractions import Fraction
sys.argv = [sys.argv[0], sys.argv[1]] + sys.argv[2:]
N = int(sys.argv[1])
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'hunt'))
import importlib.util
from flint import arb, ctx
ctx.prec = int(sys.argv[2]) if len(sys.argv)>2 else 200
src = open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'hunt', 'cert_zeta.py')).read().split('G = [[None]')[0]
src = src.replace('ctx.prec = 256', 'ctx.prec = %d' % (int(sys.argv[2]) if len(sys.argv)>2 else 256)); exec(src)
R = {r['N']: r for r in json.load(open('zeta_eigs.json'))}
def negcount(t, kind):
    d1 = m_kover = Kover(Fraction(1))
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
for kind, key in [('I', 'lam'), ('F', 'gen')]:
    lam = R[N][key]
    lo, hi = arb(lam)*(1-arb(10)**-int(sys.argv[3] if len(sys.argv)>3 else 6)), arb(lam)*(1+arb(10)**-int(sys.argv[3] if len(sys.argv)>3 else 6))
    print(N, kind, 'float64 %.10e' % lam, 'eigs<lo:', negcount(lo, kind), 'eigs<hi:', negcount(hi, kind), flush=True)
