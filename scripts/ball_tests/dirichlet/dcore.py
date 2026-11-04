"""Dirichlet analogue of K_H.  chi primitive mod q, parity a (chi(-1)=(-1)^a).
K_chi(x) = sum_rho x^{rho-1/2}/(rho(1-rho)) over nontrivial zeros; for x>=1 (y=1/x):
 K_chi(x) = sqrt(x) * [ K1 + sum_{n<=x} chi(n)Lambda(n)(1/n-1/x) + (1-a)(1-(1+log x)/x) + b(1-1/x) - C_a + tail_a(y) ]
 K1 = K_chi(1) = log(q/pi) + digamma((1+a)/2) + 2 Re L'/L(1,chi)
 b  = L'/L(0,chi) (a=1);  L''(0)/(2L'(0)) (a=0)        [Davenport ch.19 explicit formula constant]
 C_0 = 1-log2, tail_0 = y + (1-y)log(1-y)/2 - (1+y)log(1+y)/2 ;  C_1 = log2, tail_1 = y artanh y + log(1-y^2)/2
 K_chi(1/x) = conj K_chi(x).  Derivation: f(x)=sum x^rho/(rho(1-rho)) satisfies d/dx(f/x) = -x^-2 sum x^rho/rho; insert
 psi(x,chi) = -sum x^rho/rho - (1-a)log x - b + sum_{m>=1} x^{a-2m}/(2m-a) and integrate from 1.
"""
import mpmath as mp, numpy as np, math, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'function_field')); sys.path.insert(0, os.path.join(HERE, '..', '..'))
from ffcore import pivots  # noqa: E402  (the shared LDL routine)
from ball_orbit import primes_upto  # noqa: E402  (the shared sieve)
def kron(D, n):
    """Kronecker symbol (D/n), n>=1."""
    if math.gcd(D, n) != 1: return 0
    r = 1
    while n % 2 == 0:
        n //= 2
        if D % 8 in (3, 5): r = -r
    # Jacobi (D/n) n odd
    a = D % n; m = n
    while a:
        while a % 2 == 0:
            a //= 2
            if m % 8 in (3, 5): r = -r
        a, m = m, a
        if a % 4 == 3 and m % 4 == 3: r = -r
        a %= m
    return r if m == 1 else 0
def prim_root(p):
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in range(2, p) if (p-1) % f == 0 and all(f % d for d in range(2, f))): return g
def char_prime(p, k):
    """chi(g^j) = e(jk/(p-1)); returns list chi[0..p-1] of mpc."""
    g = prim_root(p); c = [mp.mpc(0)]*p; x = 1
    for j in range(p-1):
        c[x] = mp.expjpi(mp.mpf(2*j*k)/(p-1)); x = x*g % p
    return c
def char_kron(D):
    q = abs(D); return [mp.mpc(kron(D, n)) for n in range(q)]
def parity(c): return 0 if abs(c[-1]-1) < 1e-20 else 1
def constants(c):
    q = len(c); a = parity(c)
    def L(s, d=0):
        # L(s)=sum_a chi(a) q^-s zeta(s,a/q); derivatives by Leibniz
        tot = 0
        for r in range(1, q):
            if c[r] == 0: continue
            h = [mp.zeta(s, mp.mpf(r)/q, j) for j in range(d+1)]
            tot += c[r]*sum(mp.binomial(d, j)*(-mp.log(q))**(d-j)*h[j] for j in range(d+1))
        return tot*mp.power(q, -s)
    F0 = sum(c[r]*mp.stieltjes(0, mp.mpf(r)/q) for r in range(1, q) if c[r] != 0)
    F1 = -sum(c[r]*mp.stieltjes(1, mp.mpf(r)/q) for r in range(1, q) if c[r] != 0)
    K1 = mp.log(q/mp.pi) + mp.digamma(mp.mpf(1+a)/2) + 2*mp.re((F1 - mp.log(q)*F0)/F0)
    b = L(0, 1)/L(0) if a == 1 else L(0, 2)/(2*L(0, 1))
    return K1, b, a
class Kernel:
    def __init__(self, c, X, lamc=None):
        self.q = len(c); self.K1, self.b, self.a = constants(c)
        lam = [mp.mpf(0)]*(X+1)
        for p in primes_upto(X):
            pk = p; cp = c[p % self.q] if lamc is None else lamc[p]
            v = cp
            while pk <= X: lam[pk] = v*mp.log(p); pk *= p; v *= cp
        self.A = [mp.mpc(0)]*(X+1); self.B = [mp.mpc(0)]*(X+1)
        for n in range(1, X+1): self.A[n] = self.A[n-1]+lam[n]/n; self.B[n] = self.B[n-1]+lam[n]
    def __call__(self, x):  # x = Fraction >= 1
        xm = mp.mpf(x.numerator)/x.denominator; k = x.numerator//x.denominator; y = 1/xm; a = self.a
        if a == 0:
            C = 1-mp.log(2); t = y + ((1-y)*mp.log(1-y)/2 if y < 1 else 0) - (1+y)*mp.log(1+y)/2
        else:
            C = mp.log(2); t = (y*mp.atanh(y) + mp.log(1-y*y)/2) if y < 1 else mp.log(2)
        v = self.K1 + self.A[k] - self.B[k]/xm + (1-a)*(1-(1+mp.log(xm))/xm) + self.b*(1-y) - C + t
        return mp.sqrt(xm)*v
def gram(K, idx, real=False):
    from fractions import Fraction
    N = len(idx); G = np.empty((N, N), dtype=object); cache = {}
    for i, m in enumerate(idx):
        for j, n in enumerate(idx[:i+1]):
            f = Fraction(m, n)
            if f not in cache: cache[f] = K(f)
            v = n*cache[f]*mp.sqrt(f)  # = sqrt(mn) K(m/n)
            if real: v = mp.re(v)
            G[i, j] = v; G[j, i] = mp.conj(v)
    return G
