"""Certified (arb ball arithmetic) Gram-Schmidt pivots of the zeta orbit, k <= N, from the closed form
K_H(x) = sqrt(x)(sum_{n<=x} Lambda(n)(1/n-1/x) - log x + 1 + gamma - log(2pi)/x + tail(1/x)), x>=1,
tail(y) = y + (1-y)log(1-y)/2 - (1+y)log(1+y)/2 (tail(1)=1-log2)."""
import sys, math
from fractions import Fraction
from flint import arb, ctx
ctx.prec = 256
N = int(sys.argv[1])
lam = [arb(0)]*(N+1)
for p in range(2, N+1):
    if all(p % d for d in range(2, int(p**.5)+1)):
        pk = p
        while pk <= N: lam[pk] = arb(p).log(); pk *= p
A = [arb(0)]*(N+1); B = [arb(0)]*(N+1)
for n in range(1, N+1): A[n] = A[n-1]+lam[n]/n; B[n] = B[n-1]+lam[n]
g = arb.const_euler(); l2p = (2*arb.pi()).log()
cache = {}
def Kover(x):  # K_H(x)/sqrt(x)
    if x in cache: return cache[x]
    xm = arb(x.numerator)/x.denominator; k = x.numerator//x.denominator; y = 1/xm
    t = (1 - arb(2).log()) if x == 1 else y + (1-y)*(1-y).log()/2 - (1+y)*(1+y).log()/2
    v = A[k]-B[k]/xm - xm.log() + 1 + g - l2p/xm + t
    cache[x] = v; return v
G = [[None]*N for _ in range(N)]
for m in range(1, N+1):
    for n in range(1, m+1):
        G[m-1][n-1] = G[n-1][m-1] = m*Kover(Fraction(m, n))  # = sqrt(mn) K_H(m/n)
d = []
for k in range(N):
    p = G[k][k]; d.append(p)
    if not p > 0: print('pivot', k+1, 'not certified positive', p); break
    for i in range(k+1, N):
        f = G[i][k]/p
        Gi = G[i]
        for j in range(k+1, i+1): Gi[j] = Gi[j] - f*G[j][k]
    # keep symmetric lower triangle use only: rows i, cols<=i
ok = all((d[k]/d[0]) > 1 for k in range(1, len(d)))
print('N', N, 'd1', d[0], 'all d_k/d_1 > 1 certified (k=2..%d):' % len(d), ok)
worst = min(range(1, len(d)), key=lambda k: float((d[k]/d[0]).mid()))
print('ratios k=2,3,10,50,100,N:', [(kk, (d[kk-1]/d[0]).mid().str(8)) for kk in (2,3,10,50,100,len(d)) if kk<=len(d)])
print('min ratio at k=%d:' % (worst+1), d[worst]/d[0], ' radius of last pivot', d[-1].rad())
