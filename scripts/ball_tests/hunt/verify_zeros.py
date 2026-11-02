"""Direct zero-sum check of K1, K(2) for a character (zeros via sign changes of Hardy Z from flint, |t|<T)."""
import sys, math
from flint import arb, acb, dirichlet_char, ctx
from k2 import char_k2
ctx.prec = 64
q, n, T = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
c = dirichlet_char(q, n)
Z = lambda t: c.hardy_z(acb(t)).real.mid()
h = 0.02; zs = []; t = -T; z0 = float(Z(t))
while t < T:
    z1 = float(Z(t+h))
    if z0*z1 < 0:
        a, b = t, t+h
        for _ in range(30):
            m = (a+b)/2; zm = float(Z(m))
            if zm*z0 < 0: b = m
            else: a, z0 = m, zm
        zs.append((a+b)/2)
    t += h; z0 = z1
K1d = sum(1/(0.25+g*g) for g in zs); K2d = sum(complex(math.cos(g*math.log(2)), math.sin(g*math.log(2)))/(0.25+g*g) for g in zs)
tail = (math.log(q*T/(2*math.pi))+1)/(math.pi*T)
K1, K2, l = char_k2(c)
print('q', q, 'n', n, 'parity', c.parity(), 'zeros found', len(zs), 'lowest', sorted(zs, key=abs)[:4])
print('K1 closed', K1.mid(), ' zero-sum', K1d, '+tail', K1d+tail)
print('K2 closed', K2.mid(), ' zero-sum', K2d, ' |K2|/K1 closed', float((abs(K2)/K1).mid()), 'zero-sum', abs(K2d)/(K1d+tail))
