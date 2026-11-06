import math, sys
import numpy as np
from scipy.linalg import eigvalsh
sys.path.insert(0, sys.path[0])
HERE = sys.path[0]
exec(open(f"{HERE}/quantum.py").read().split("# ---------------------------------------------------------------- Q1")[0])
def stats_of(ev):
    ev = np.clip(ev, 0, None); q = ev / ev.sum(); qq = q[q > 0]
    return np.sort(q)[::-1][:3].sum(), math.exp(-(qq * np.log(qq)).sum()), 1 / (q * q).sum()
print(f"{'N':>6} {'top-3 share':>12} {'e^S':>7} {'PR':>7}   smallest/largest eigenvalue")
G = gram(4096)
for N in (64, 256, 1024, 4096):
    ev = eigvalsh(G[:N, :N])
    t3, eS, pr = stats_of(ev)
    print(f"{N:6d} {t3:12.3f} {eS:7.2f} {pr:7.2f}   {ev.min() / ev.max():.2e}")
# the frozen limit, in the zero basis (both signs of gamma)
g = np.concatenate([gam, -gam]); d = 0.25 + g * g
C0 = 2 / (2 + 1j * (g[:, None] - g[None, :]))
M = C0 / np.sqrt(d[:, None] * d[None, :])
ev = np.linalg.eigvalsh(M)
t3, eS, pr = stats_of(ev)
print(f"{'limit':>6} {t3:12.3f} {eS:7.2f} {pr:7.2f}   (from {len(gam)} zeros of each sign)")
