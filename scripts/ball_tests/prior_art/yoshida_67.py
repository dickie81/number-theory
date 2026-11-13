import mpmath as mp
mp.mp.dps = 20
a = mp.log(2)/2
q = mp.mpf(1)/4
t0 = mp.findroot(lambda t: mp.re(mp.digamma(q + 1j*t/2)), 2.0)
I0 = mp.quad(lambda t: mp.re(mp.digamma(q + 1j*t/2)), [0, t0])
print("t0 =", mp.nstr(t0, 6), "  int_0^t0 Re psi(1/4+it/2) dt =", mp.nstr(I0, 6))
def bound(t1, N, C):
    S1 = mp.nsum(lambda n: (1/n**2)*(1 + mp.pi*n/(mp.pi*n - a*t1))**2, [N+1, mp.inf])
    S0 = mp.nsum(lambda n: (1/n**2)*(1 + mp.pi*n/(mp.pi*n - a*t0))**2, [N+1, mp.inf])
    return C - mp.log(mp.pi) - (1/mp.sqrt(2) - mp.log(2)) - a*C/(2*mp.pi**3)*(t1 - mp.sin(2*a*t1)/(2*a))*S1 - mp.mpf('2.77')*a/mp.pi**3*S0
for t1, N in [(50, 10), (700, 199), (800, 199)]:
    C = mp.re(mp.digamma(q + 1j*t1/2))
    print("t1=%d N=%d: C = Re psi(1/4+i t1/2) = %s ; (6.7) bound = %s" % (t1, N, mp.nstr(C, 6), mp.nstr(bound(t1, N, C), 5)))
print("(6.7) with t1=700, N=199 but C=5.9914 as printed:", mp.nstr(bound(700, 199, mp.mpf('5.9914')), 5))
# constants (6.19), (6.27)
C1 = 2*a/mp.pi**2*(mp.e**(a/2)-mp.e**(-a/2))**2 + 2*a/mp.pi**2*mp.e**(-a)/(1-mp.e**(-4*a)) + (mp.mpf(1)/2 + a/(2*mp.pi**2))
C2 = 2*a/mp.pi**2*(mp.e**(a/2)-mp.e**(-a/2))**2 + 2*a/mp.pi**2*mp.e**(-a)/(1-mp.e**(-4*a)) + (mp.mpf(1)/2 + (2*a)**2/(10*mp.pi**3))
print("C1^2 =", mp.nstr(C1**2, 6), " (printed 0.3508...);  C2^2 =", mp.nstr(C2**2, 6), " (printed 0.3321...)")
print("C1^2/10 =", mp.nstr(C1**2/10, 6), " C2^2/199 =", mp.nstr(C2**2/199, 6))
print("odd pole bound (e^a - e^-a - 2a) = 1/sqrt2 - log2 =", mp.nstr(mp.e**a - mp.e**(-a) - 2*a, 6), mp.nstr(1/mp.sqrt(2)-mp.log(2), 6))
