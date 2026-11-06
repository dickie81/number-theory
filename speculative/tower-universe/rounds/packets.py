import math, sys
import numpy as np
from scipy.linalg import eigh
from scipy.stats import spearmanr
HERE = sys.path[0]
exec(open(f"{HERE}/quantum.py").read().split("# ---------------------------------------------------------------- Q1")[0])
NMAX = 2048
G = gram(NMAX)
P = [p for p in range(2, NMAX + 1) if isp[p]]
need = sorted({p - 1 for p in P} | set(P) | {256, 512, 1024, 2048} | {255, 511, 1023, 2047})
lamN = {N: (H0 if N == 1 else eigh(G[:N, :N], subset_by_index=[0, 0], eigvals_only=True)[0]) for N in need}
inv = {N: 1 / v for N, v in lamN.items()}
np.save(f"{HERE}/packets_inv.npy", np.array(sorted(inv.items())))
rows = []
for p, q in zip(P, P[1:]):
    rows.append((p, q - p, inv[p] - inv[p - 1], inv[q - 1] - inv[p - 1]))
rows = np.array(rows)
print(f"1/λ_N at N = 2048: {inv[2048]:.0f}; primes so far {len(P)}; per prime on average {inv[2048] / len(P):.1f}")
for lo, hi in ((256, 512), (512, 1024), (1024, 2048)):
    m = (inv[hi - 1] - inv[lo - 1]) / (hi - lo)          # mean increment per integer in the window
    sel = (rows[:, 0] >= lo) & (rows[:, 0] < hi) & (rows[:, 0] + rows[:, 1] <= hi)
    p_, g, dp, dk = rows[sel].T
    share = dp / dk
    b, a = np.polyfit(g, dk / m, 1)
    rho = spearmanr(g, dk).correlation
    k = dp / m; prevg = np.array([p - max(x for x in P if x < p) for p in p_.astype(int)])
    print(f"     the prime's own kick: quartiles {np.percentile(k, 25):.2f} / {np.median(k):.2f} / {np.percentile(k, 75):.2f}"
          f" integers' worth (CV {k.std() / k.mean():.2f}); Spearman with the gap after it {spearmanr(g, k).correlation:.2f},"
          f" with the gap before it {spearmanr(prevg, k).correlation:.2f}")
    print(f"[{lo}, {hi}): {sel.sum()} packets; a prime is worth {np.median(dp / m):.2f} integers"
          f" (each other integer ~1 on average); the prime's share of its packet: median {np.median(share):.2f}"
          f" (range {share.min():.2f}–{share.max():.2f})")
    print(f"     packet size ≈ {a:.2f} + {b:.2f}·gap (integers' worth); Spearman(packet, gap) = {rho:.2f}")
    for gg in sorted(set(g.astype(int)))[:1] + [int(np.median(g))] + [int(g.max())]:
        s = g == gg
        print(f"       gap {gg:2d}: packet {np.mean(dk[s] / m):.1f} integers' worth ({s.sum()} packets)")
