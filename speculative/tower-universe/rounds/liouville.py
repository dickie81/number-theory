import math, sys
import numpy as np
import mpmath as mp
HERE = sys.path[0]
N = 10 ** 7
Om = np.zeros(N + 1, np.int8)
isp = np.ones(N + 1, bool); isp[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if isp[p]: isp[p * p::p] = False
for p in np.nonzero(isp)[0]:
    q = int(p)
    while q <= N: Om[q::q] += 1; q *= int(p)
lam = np.where(Om % 2 == 0, 1, -1).astype(np.int8); lam[0] = 0
L = np.cumsum(lam.astype(np.int64))
zh = float(mp.zeta(0.5))
rng = np.random.default_rng(20261106)
coin = rng.choice(np.array([-1, 1], np.int8), N + 1); coin[0] = 0
S = np.cumsum(coin.astype(np.int64))
xs = np.unique(np.round(np.exp(np.linspace(math.log(1e3), math.log(N), 4000))).astype(int))
print("== Q10: the click-parity coin λ(N) = (−1)^Ω(N), N ≤ 10^7 ==")
for nm, W, x in (("click parity", L, lam), ("random coin ", S, coin)):
    r = W[xs] / np.sqrt(xs)
    ac = [float(np.mean(x[1:N + 1 - h].astype(np.int32) * x[1 + h:N + 1])) for h in (1, 2, 3)]
    a, b, c = x[1:N - 1].astype(int), x[2:N].astype(int), x[3:N + 1].astype(int)
    code = (a > 0) * 4 + (b > 0) * 2 + (c > 0)
    freq = np.bincount(code, minlength=8) / len(code)
    print(f"  {nm}: mean of sum/√N = {r.mean():+.3f} (1/ζ(½) = {1 / zh:+.3f}); range {r.min():+.2f} to {r.max():+.2f};"
          f" lag-1..3 correlations {', '.join(f'{v:+.1e}' for v in ac)} (noise ~{1 / math.sqrt(N):.0e});"
          f" 3-step patterns {freq.min():.4f}–{freq.max():.4f} (fair 0.1250)")
print("\n== Q11: the hidden zeros predict the coin's wiggles ==")
gam = np.load(f"{HERE}/zeros_3000.npy")
mp.mp.dps = 20
coef = []
for g in gam[:200]:
    rho = mp.mpc(0.5, g)
    coef.append(complex(mp.zeta(2 * rho) / (rho * mp.zeta(rho, derivative=1))))
coef = np.array(coef)
zs = np.unique(np.round(np.exp(np.linspace(math.log(1e4), math.log(N), 2000))).astype(int))
r = L[zs] / np.sqrt(zs) - 1 / zh
for K in (10, 50, 200):
    pred = 2 * np.real(np.exp(1j * np.outer(np.log(zs), gam[:K])) @ coef[:K])
    print(f"  K = {K:3d} zeros: correlation(actual wiggles, prediction) = {np.corrcoef(r, pred)[0, 1]:.3f};"
          f" rms actual {r.std():.3f}, rms left over {np.std(r - pred):.3f}")
