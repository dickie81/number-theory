import math, sys
import numpy as np
from scipy.linalg import eigvalsh
HERE = sys.path[0]
gam = np.load(f"{HERE}/zeros_3000.npy"); G1, G2 = gam[0], gam[1]
# ---- Q12: the co-rotating window (plane 1 + the turning unit vector in plane 2), from the fixed 4D moment tensor
NMAX = 1 << 21
n = np.arange(1, NMAX + 1, dtype=float); t = np.log(n); r = np.sqrt(2 * n)
r1, r2 = 1 / math.hypot(0.5, G1), 1 / math.hypot(0.5, G2)
V = [r * r1 * np.cos(G1 * t), r * r1 * np.sin(G1 * t), r * r2 * np.cos(G2 * t), r * r2 * np.sin(G2 * t)]
cs = {(i, j): np.cumsum(V[i] * V[j]) for i in range(4) for j in range(i, 4)}
del V
Ns = np.unique(np.round(np.exp(np.linspace(math.log(1 << 12), math.log(NMAX), 3000))).astype(int))
eig, ang = [], []
for N in Ns:
    M4 = np.empty((4, 4))
    for (i, j), c in cs.items(): M4[i, j] = M4[j, i] = c[N - 1]
    a1, a2 = G1 * math.log(N), G2 * math.log(N)
    R = np.zeros((4, 3))                       # columns: the observer's axes at time N
    R[:2, 0] = [math.cos(a1), math.sin(a1)]; R[:2, 1] = [-math.sin(a1), math.cos(a1)]
    R[2:, 2] = [math.cos(a2), math.sin(a2)]
    M = R.T @ M4 @ R / N
    w, v = np.linalg.eigh(M); eig.append(w[::-1]); ang.append(math.atan2(v[1, 2], v[0, 2]))
eig = np.array(eig); a = np.sqrt(eig / Ns[:, None]) * 0 + np.sqrt(eig); lnN = np.log(Ns)
rates = np.gradient(np.log(np.sqrt(eig)), lnN, axis=0)
shear = np.sqrt(((rates - rates.mean(1, keepdims=True)) ** 2).mean(1)) / rates.mean(1)
ratio = np.sqrt(eig / eig[:, :1])
turn = np.abs(np.gradient(np.unwrap(2 * np.array(ang)) / 2, lnN))
print("== Q12: the co-rotating window ==")
print(f"axis ratios: middle {ratio[:, 1].min():.4f}–{ratio[:, 1].max():.4f}, short {ratio[:, 2].min():.4f}–{ratio[:, 2].max():.4f}")
print(f"mean rate H·t = {rates.mean():.4f}; each axis's own rate within ±{np.abs(rates - 0.5).max():.1e} of 1/2")
for lo, hi in ((1 << 12, 1 << 15), (1 << 15, 1 << 18), (1 << 18, 1 << 21)):
    s = (Ns >= lo) & (Ns < hi)
    print(f"  N in [2^{int(math.log2(lo))}, 2^{int(math.log2(hi))}): shear σ/H max {shear[s].max():.1e}; axes turn ≤ {turn[s].max():.1e} rad per unit log N")
b, a0 = np.polyfit(lnN, np.log(shear + 1e-300), 1)
print(f"  shear falls like N^{b:.2f}; extrapolated to N = 8e60: σ/H ≈ {math.exp(a0) * 8.07e60 ** b:.0e}")
print(f"  (fixed outside axes, round 2: σ/H median 0.77; long axis turning 14.1 rad per unit log N)")
# ---- Q13: the share of the tower in the top three axes
exec(open(f"{HERE}/quantum.py").read().split("# ---------------------------------------------------------------- Q1")[0].split("# ---------------------------------------------------------------- zeros (cached)")[0])
exec(open(f"{HERE}/quantum.py").read().split("# ---------------------------------------------------------------- primes and the closed-form kernel")[1].split("# ---------------------------------------------------------------- Q1")[0])
print("\n== Q13: the share of the outer product in its top three axes ==")
G = gram(4096)
for N in (1024, 2048, 4096):
    ev = eigvalsh(G[:N, :N]); ev = np.sort(ev)[::-1]
    print(f"  N = {N}: top-3 share {ev[:3].sum() / ev.sum():.4f} (axes {ev[0] / ev.sum():.4f}, {ev[1] / ev.sum():.4f}, {ev[2] / ev.sum():.4f})")
