import math, numpy as np
from fractions import Fraction
from scipy.integrate import quad
import sys; sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..')); import ball_orbit as bo
dens = lambda t: math.log(t/(2*math.pi))/(2*math.pi)/(0.25+t*t)
cache = {}
def K(f):
    if f in cache: return cache[f]
    u = math.log(f.numerator/f.denominator)
    v = 2*quad(dens, 2*math.pi, np.inf, limit=500)[0] if u == 0 else 2*quad(dens, 2*math.pi, np.inf, weight='cos', wvar=u, limlst=200)[0]
    cache[f] = v; return v
NM = 200; S = np.zeros((NM, NM))
for m in range(1, NM+1):
    for n in range(1, m+1):
        S[m-1, n-1] = S[n-1, m-1] = math.sqrt(m*n)*K(Fraction(m, n))
G = bo.gram(NM)
for N in [25, 50, 100, 200]:
    s = np.linalg.eigvalsh(S[:N, :N])[0]; g = np.linalg.eigvalsh(G[:N, :N])[0]; e = np.linalg.eigvalsh((G-S)[:N, :N])
    print(N, 'lam_min density %.3e (xN %.3f)  zeta %.3e  (G-S): min %.3e max %.3e' % (s, s*N, g, e[0], e[-1]), flush=True)
