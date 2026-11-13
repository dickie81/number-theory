"""Isotropy in turning windows of 2, 3 and 4 dimensions: the first zero's plane; that plane plus a turning axis of the
second (the 3D window of round 10); and the first two planes. Shows that isotropy does not need the window to be 3D."""
import math, sys
import numpy as np
HERE = sys.path[0]
gam = np.load(f"{HERE}/zeros_3000.npy"); G1, G2 = gam[0], gam[1]
NMAX = 1 << 21
n = np.arange(1, NMAX + 1, dtype=float); t = np.log(n); r = np.sqrt(2 * n)
r1, r2 = 1 / math.hypot(0.5, G1), 1 / math.hypot(0.5, G2)
V = [r * r1 * np.cos(G1 * t), r * r1 * np.sin(G1 * t), r * r2 * np.cos(G2 * t), r * r2 * np.sin(G2 * t)]
cs = {(i, j): np.cumsum(V[i] * V[j]) for i in range(4) for j in range(i, 4)}
del V
Ns = np.unique(np.round(np.exp(np.linspace(math.log(1 << 12), math.log(NMAX), 2000))).astype(int))

def frame(N, dim):
    """The observer's axes at time N, turning with each plane at that zero's rate."""
    a1, a2 = G1 * math.log(N), G2 * math.log(N)
    R = np.zeros((4, 4))
    R[:2, 0] = [math.cos(a1), math.sin(a1)]; R[:2, 1] = [-math.sin(a1), math.cos(a1)]
    R[2:, 2] = [math.cos(a2), math.sin(a2)]; R[2:, 3] = [-math.sin(a2), math.cos(a2)]
    return R[:, :dim]

for dim in (2, 3, 4):
    eig = []
    for N in Ns:
        M4 = np.empty((4, 4))
        for (i, j), c in cs.items(): M4[i, j] = M4[j, i] = c[N - 1]
        R = frame(N, dim)
        eig.append(np.sort(np.linalg.eigvalsh(R.T @ M4 @ R / N))[::-1])
    eig = np.array(eig); lnN = np.log(Ns)
    rates = np.gradient(np.log(np.sqrt(eig)), lnN, axis=0)
    shear = np.sqrt(((rates - rates.mean(1, keepdims=True)) ** 2).mean(1)) / rates.mean(1)
    ok = shear > 0
    b = np.polyfit(lnN[ok], np.log(shear[ok]), 1)[0] if ok.sum() > 10 else float("nan")
    print(f"{dim}D window: axis ratios {', '.join(f'{x:.4f}' for x in np.sqrt(eig[-1] / eig[-1][0]))};"
          f" mean H·t {rates.mean():.4f}; shear at N = 2^21 {shear[-1]:.1e}, max over N ≥ 2^18"
          f" {shear[Ns >= 1 << 18].max():.1e}; falls like N^{b:.2f}")
