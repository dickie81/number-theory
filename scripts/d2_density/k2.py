"""Rigorous (arb ball arithmetic) evaluation of K1=K(1) and K(2) for zeta and primitive Dirichlet characters.
d_2/d_1 = 2(1 - |K(2)|^2/K1^2)  (G11=K1, G22=2K1, G12=sqrt2 K(2)).  d_2>=d_1  <=>  |K(2)| <= K1/sqrt2.
Closed forms (x=2: the prime sum sum_{n<=2} chi(n)Lambda(n)(1/n-1/2) vanishes):
 l = L'/L(1,chi),  K1 = log(q/pi) + digamma((1+a)/2) + 2 Re l,  b = -log(q/pi) + gamma + log2 - conj(l)
 K(2)/sqrt2 = K1 + (1-a)(1-(1+log2)/2) + b/2 - C_a + tail_a(1/2)
"""
import flint, sys
from flint import arb, acb, acb_series, dirichlet_char, ctx
ctx.prec = 128
g = arb.const_euler(); l2 = arb(2).log(); pi = arb.pi()
half = arb(1)/2
T0 = half + arb(1)/4*half.log() - arb(3)/4*(arb(3)/2).log(); C0 = 1 - l2
T1 = half*half.atanh() + half*(arb(3)/4).log(); C1 = l2
def zeta_k2():
    K1 = 2 + g - (4*pi).log()
    K2 = arb(2).sqrt()*(-l2 + 1 + g - (2*pi).log()/2 + T0)
    return K1, K2
def char_k2(chi):
    q = chi.modulus(); a = chi.parity()
    s = acb_series([1, 1], prec=2)
    Ls = acb_series.dirichlet_l(s, chi)
    c = Ls.coeffs(); l = c[1]/c[0]
    K1 = (arb(q)/pi).log() + (arb(-1)*g - 2*l2 if a == 0 else -g) + 2*l.real
    b = -(arb(q)/pi).log() + g + l2 - l.conjugate()
    inner = K1 + (1-a)*(1-(1+l2)/2) + b/2 - (C0 if a == 0 else C1) + (T0 if a == 0 else T1)
    return K1, arb(2).sqrt()*inner, l
if __name__ == '__main__':
    K1, K2 = zeta_k2(); r = 2*(1-K2**2/K1**2)
    print('zeta: K1 =', K1, ' K(2) =', K2, ' d2/d1 =', r, ' certified >=1:', bool(r > 1))
