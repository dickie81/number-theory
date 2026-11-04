"""Check closed form K_chi(x) against direct sums over zeros |gamma|<T (zeros by sign changes of the rotated Lambda)."""
import mpmath as mp, sys
from fractions import Fraction
from dcore import *
mp.mp.dps = 20
def Lfun(c, s):
    q = len(c); return mp.power(q, -s)*sum(c[r]*mp.zeta(s, mp.mpf(r)/q) for r in range(1, q) if c[r] != 0)
def zeros(c, T, h=0.04):
    q = len(c); a = parity(c)
    Lam = lambda t: mp.power(q/mp.pi, (mp.mpf(1)/2+1j*t)/2)*mp.gamma((mp.mpf(1)/2+1j*t+a)/2)*Lfun(c, mp.mpf(1)/2+1j*t)
    l0 = Lam(mp.mpf('0.013')); 
    # root number via Lambda(1/2+it) = eps*conj(Lambda(1/2+it)) for real t
    eps = l0/mp.conj(l0); se = mp.sqrt(eps)
    Z = lambda t: mp.re(Lam(t)/se)
    out = []; t = -T; zp = Z(t)
    while t < T:
        t2 = t+h; z2 = Z(t2)
        if zp*z2 < 0: out.append(mp.findroot(Z, (t, t2), solver='bisect' if False else 'anderson'))
        t, zp = t2, z2
    return out
if __name__ == '__main__':
    T = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    for name, c in [('kron5', char_kron(5)), ('kron-4', char_kron(-4)), ('chi5_k1', char_prime(5, 1)), ('chi7_k1', char_prime(7, 1))]:
        g = zeros(c, T); K = Kernel(c, 40); q = len(c)
        tail = (mp.log(q*T/(2*mp.pi))+1)/(mp.pi*T)
        print(name, 'parity', parity(c), 'zeros', len(g), 'gamma1..', [mp.nstr(x, 6) for x in sorted(g, key=abs)[:3]])
        for x in [Fraction(1), Fraction(2), Fraction(7, 2), Fraction(10)]:
            xm = mp.mpf(x.numerator)/x.denominator
            direct = sum(mp.exp(1j*gm*mp.log(xm))/(mp.mpf(1)/4+gm**2) for gm in g)
            print('  x=', x, 'closed', mp.nstr(K(x), 8), 'zeros', mp.nstr(direct, 8), ('+tail %s' % mp.nstr(direct+tail, 8)) if x == 1 else '', 'tail bound ~', mp.nstr(tail, 3))
