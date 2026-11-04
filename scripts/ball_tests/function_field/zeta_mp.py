"""dps-40 rerun of scripts/ball_orbit.py's zeta pivots, compared with its float64 Cholesky."""
import sys, math, numpy as np, mpmath as mp
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..'))
import ball_orbit as bo
from ffcore import pivots
mp.mp.dps = 40
N = int(sys.argv[1])
lam = [mp.mpf(0)]*(N+2)
for p in bo.primes_upto(N+1):
    pk = p
    while pk <= N+1: lam[pk] = mp.log(p); pk *= p
A = [mp.mpf(0)]*(N+2); B = [mp.mpf(0)]*(N+2)
for n in range(1, N+2): A[n] = A[n-1]+lam[n]/n; B[n] = B[n-1]+lam[n]
cache = {}
def Ks(x):  # K_H(x)/sqrt(x), x=hi/lo exact Fraction
    from fractions import Fraction
    if x in cache: return cache[x]
    xm = mp.mpf(x.numerator)/x.denominator; k = x.numerator//x.denominator; y = 1/xm
    t = (1-y)*mp.log(1-y)/2 if y < 1 else mp.mpf(0)
    v = A[k]-B[k]/xm-mp.log(xm)+1+mp.euler-mp.log(2*mp.pi)/xm + y + t - (1+y)*mp.log(1+y)/2
    cache[x] = v; return v
from fractions import Fraction
G = np.empty((N, N), dtype=object)
for m in range(1, N+1):
    for n in range(1, m+1):
        G[m-1, n-1] = G[n-1, m-1] = m*Ks(Fraction(m, n))
dm = pivots(G)
df = bo.pivots(bo.gram(N))
rel = [abs(float(dm[k])-df[k])/float(dm[k]) for k in range(N)]
print("d1 mp =", mp.nstr(dm[0], 20), " exact 2+gamma-log4pi =", mp.nstr(2+mp.euler-mp.log(4*mp.pi), 20))
print("max rel diff float64 vs dps40 pivots:", max(rel), "at k =", rel.index(max(rel))+1)
r = [dm[k]/dm[0] for k in range(N)]
print("min_k d_k/d_1 (k>=2):", mp.nstr(min(r[1:]), 12), "at k =", r.index(min(r[1:]))+1, "; any < 1:", any(x < 1 for x in r[1:]))
for k in [2,3,5,10,50,100,200,300,400,500]:
    if k <= N: print(k, mp.nstr(r[k-1], 10), "float64:", df[k-1]/df[0])
