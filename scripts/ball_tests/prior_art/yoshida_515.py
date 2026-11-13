# Check Yoshida (5.15) at n = 0, k = Q, a = log2/2, against (i) the zero sum and
# (ii) a direct evaluation of the explicit formula of Sec. 0 for F = chi_0 * chi_0~.
import mpmath as mp
mp.mp.dps = 30
a = mp.log(2)/2
# (5.15), n = 0, r1 = 1, r2 = 0, log A_Q = -log pi; prime sum over e log p <= 2a = log 2 is the
# single term p = 2, e = 1, whose weight (2a - log 2) vanishes.
pole = (4/a)*(mp.e**(a/2) - mp.e**(-a/2))**2
ser = mp.nsum(lambda k: mp.exp(-2*a*(2*k+mp.mpf(1)/2))/(2*k+mp.mpf(1)/2)**2, [0, mp.inf])
arch = (1/(2*a))*(-2*ser + 2*a*mp.re(mp.digamma(mp.mpf(1)/4)) + mp.re(mp.psi(1, mp.mpf(1)/4))/2)
y515 = pole - mp.log(mp.pi) + arch
print("(5.15) at n=0:            ", mp.nstr(y515, 12))
# explicit formula of Sec. 0 with F(x) = (2a-|x|)_+/(2a), Fhat(t) = (2/a) sin^2(a t)/t^2
F0 = 1
polet = mp.quad(lambda x: (2*a - x)/(2*a)*(mp.e**(x/2) + mp.e**(-x/2)), [0, 2*a])*2
Fhat = lambda t: (2/a)*mp.sin(a*t)**2/t**2 if t != 0 else 2*a
# The archimedean integral (1/pi) int_0^oo Fhat(t) Re psi(1/4 + it/2) dt decays only like log t/t^2 and oscillates:
# quadrature on [0, T0], then from T0 the smooth part (1/a) Re psi/t^2 by quad and the part -(1/a) cos(2at) Re psi/t^2
# by quadosc. (A single quad to infinity loses about 1e-3.)
rp = lambda t: mp.re(mp.digamma(mp.mpf(1)/4 + 1j*t/2))
T0 = 40
body = mp.quad(lambda t: Fhat(t)*rp(t), mp.linspace(0, T0, 4*T0 + 1))
smooth = mp.quad(lambda t: rp(t)/(a*t**2), [T0, mp.inf])
osc = mp.quadosc(lambda t: -mp.cos(2*a*t)*rp(t)/(a*t**2), [T0, mp.inf], omega=2*a)
archt = (body + smooth + osc)/mp.pi
ef = polet - mp.log(mp.pi)*F0 + archt
print("explicit formula (Sec. 0):", mp.nstr(ef, 12))
# zero sum (under RH): sum over all gamma of (2/a) sin^2(a gamma)/gamma^2, first K zeros + density tail
K = 600
s = mp.mpf(0)
for n in range(1, K+1):
    g = mp.im(mp.zetazero(n))
    s += 2*(2/a)*mp.sin(a*g)**2/g**2
T = g
tail = (1/(a*mp.pi))*(mp.log(T/(2*mp.pi)) + 1)/T
# The tail also carries the resonance with the prime 2 (2a = log 2): by Landau's formula
# sum_{0 < gamma <= T} cos(gamma log 2) ~ -(T/2pi) log(2)/sqrt(2), which adds sqrt(2)/(pi T).
tail += mp.sqrt(2)/(mp.pi*T)
print("zero sum, %d zeros + tail:" % K, mp.nstr(s + tail, 12), " (tail %s)" % mp.nstr(tail, 4))
print("K_H(1) = 2 + gamma - log 4pi =", mp.nstr(2 + mp.euler - mp.log(4*mp.pi), 12))
