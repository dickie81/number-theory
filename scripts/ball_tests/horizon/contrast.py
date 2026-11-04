import sys, json, numpy as np, mpmath as mp
from fractions import Fraction
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'dirichlet')); sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'function_field'))
from dcore import Kernel
import ffcore
from flint import dirichlet_char
mp.mp.dps = 25
Ns = [10, 20, 50, 100, 150, 168, 169, 200, 300, 500]
fc = dirichlet_char(19, 3)
c = [mp.mpc(0)] + [mp.mpc(complex(fc(n).real.mid()), complex(fc(n).imag.mid())) for n in range(1, 19)]
K = Kernel(c, 500)
NM = 500; G = np.zeros((NM, NM), complex); cache = {}
for m in range(1, NM+1):
    for n in range(1, m+1):
        f = Fraction(m, n)
        if f not in cache: cache[f] = complex(K(f))
        G[m-1, n-1] = n*cache[f]*np.sqrt(m/n); G[n-1, m-1] = np.conj(G[m-1, n-1])
Pc = [1, 2, 13]  # genus-1 curve over F_13 (a_p=-2)
Gc = np.array(ffcore.gram(Pc, 13, 300), dtype=float)
out = {'chi19_3': [], 'curve13': []}
for N in Ns:
    g = G[:N, :N]; d1 = g[0, 0].real; m = np.arange(1, N+1); F = d1*np.minimum.outer(m, m)
    w = np.linalg.eigvalsh(g)[0]; Dm = 1/np.sqrt(np.diag(g).real); cw = np.linalg.eigvalsh(g*Dm[:, None]*Dm[None, :])[0]
    out['chi19_3'].append((N, w, w/d1, cw))
    if N <= 300:
        h = Gc[:N, :N]; e1 = h[0, 0]; wc = np.linalg.eigvalsh(h)[0]; Dh = 1/np.sqrt(np.diag(h)); cwc = np.linalg.eigvalsh(h*Dh[:, None]*Dh[None, :])[0]
        out['curve13'].append((N, wc, wc/e1, cwc))
for k, v in out.items():
    print(k); [print('  N=%d lam=%.3e lam/d1=%.3e corr=%.3e' % t) for t in v]
json.dump(out, open('contrast.json', 'w'))
