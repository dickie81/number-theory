import mpmath as mp
mp.mp.dps = 20
a = mp.log(2)/2
ser = mp.nsum(lambda k: mp.exp(-2*a*(2*k+mp.mpf(1)/2))/(2*k+mp.mpf(1)/2)**2, [0, mp.inf])
arch_closed = (1/(2*a))*(-2*ser + 2*a*mp.digamma(mp.mpf(1)/4) + mp.psi(1, mp.mpf(1)/4)/2)
# V_1 = (1/pi) int_0^inf (1/a)(1-cos(2at))/t^2 Re psi(1/4+it/2) dt, integrated to Tb in pieces,
# plus tail using Re psi(1/4+it/2) = log(t/2) + O(1/t^2) and dropping the cos part (O(log Tb/Tb^2)).
f = lambda t: (1/a)*(1-mp.cos(2*a*t))/t**2*mp.re(mp.digamma(mp.mpf(1)/4+1j*t/2)) if t != 0 else 2*a*mp.digamma(mp.mpf(1)/4)
Tb = 3000
pts = [mp.mpf(i)/2 for i in range(0, 2*Tb+1)]
body = mp.quad(f, pts)
tail = (1/a)*(mp.log(Tb/2) + 1)/Tb
arch_num = (body + tail)/mp.pi
print("archimedean V_1, closed form (5.15):", mp.nstr(arch_closed, 10))
print("archimedean V_1, numerical         :", mp.nstr(arch_num, 10))
