import math, sys
import numpy as np
HERE = sys.path[0]
exec(open(f"{HERE}/quantum.py").read().split("# ---------------------------------------------------------------- Q1")[0])
G1, G2 = gam[0], gam[1]
def Gfull(N, n):                     # embedded observer: the full inner product (N >= n)
    return N * kos(np.asarray(N, float) / n)
def G3(N, n):                        # 3D observer: shadows in the drawn slice
    N = np.asarray(N, float); r1, r2 = 0.25 + G1 * G1, 0.25 + G2 * G2
    return 2 * np.sqrt(N * n) * (np.cos(G1 * np.log(N / n)) / r1 + np.cos(G2 * np.log(N)) * np.cos(G2 * math.log(n)) / r2)
def auc(score, lab):
    a, b = score[lab], score[~lab]
    return (np.sum(a[:, None] > b[None, :]) + 0.5 * np.sum(a[:, None] == b[None, :])) / (len(a) * len(b))
NM = 3000
for n in (1, 6):
    N = np.arange(n + 2, NM + 1)
    D = Gfull(N + 1, n) - 2 * Gfull(N, n) + Gfull(N - 1, n)
    D3 = G3(N + 1, n) - 2 * G3(N, n) + G3(N - 1, n)
    m = N / n
    click = np.array([(x == int(x)) and ppow[int(x)] for x in m])
    pred = np.where(click, lam[np.where(click, m, 1).astype(int)] / np.where(click, m, 1), 0.0)
    resid = D - pred
    print(f"n = {n}: {click.sum()} predicted clicks for N <= {NM}")
    print(f"   strongest clicks (N, measured, predicted): " + ", ".join(
        f"({int(a)}, {b:.4f}, {c:.4f})" for a, b, c in sorted(zip(N[click], D[click], pred[click]), key=lambda t: -t[2])[:5]))
    r = D - pred + 1 / N
    print(f"   D(N) = click − 1/N + residual: |residual| <= {np.max(np.abs(r)):.1e} over all N (the −1/N background is"
          f" rough at small N); for N >= 100, |residual| <= {np.max(np.abs(r[N >= 100])):.1e},"
          f" against the faintest click there {pred[click & (N >= 100)].min():.1e}")
    for nm, dd in (("embedded", D), ("3D", D3)):
        print(f"   {nm:8s} observer: AUC for finding the click times = {auc(dd + 1 / N, click):.3f}")
# total click strength per tick, summed over every past integer, by the closed-form rule
print("\ntotal click strength per tick, Σ_{p^k | N} log p / p^k:")
tot = np.zeros(NM + 1)
for mm in range(2, NM + 1):
    if ppow[mm]:
        tot[mm::mm] += lam[mm] / mm
Ns = np.arange(2, NM + 1)
pr = isp[2:NM + 1]
print(f"   primes: median {np.median(tot[2:][pr]):.4f} (one click each, against n = 1);"
      f" composites: median {np.median(tot[2:][~pr]):.4f}")
print(f"   e.g. N = 2999 (prime): {tot[2999]:.4f};  N = 2520 = 2^3·3^2·5·7: {tot[2520]:.4f}")
