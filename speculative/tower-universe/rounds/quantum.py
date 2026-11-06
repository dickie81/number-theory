"""Round 4 (PREREG4.md): Q1 orthogonality of new primes, Q2 turns of the thinnest axis,
Q3 wave-particle duality (each side rebuilt from the other), Q4 level statistics of the zeros."""
import math, os, sys, time
import numpy as np
from scipy.linalg import lapack, eigh
from scipy.special import erf
import mpmath as mp

HERE = sys.path[0]
EG = 0.5772156649015329
H0 = 2 + EG - math.log(4 * math.pi)

# ---------------------------------------------------------------- zeros (cached)
KZ = 3000
zf = f"{HERE}/zeros_{KZ}.npy"
if os.path.exists(zf):
    gam = np.load(zf)
else:
    mp.mp.dps = 15; t0 = time.time()
    gam = np.array([float(mp.zetazero(k).imag) for k in range(1, KZ + 1)]); np.save(zf, gam)
    print(f"[computed {KZ} zeros in {time.time() - t0:.0f} s]")

# ---------------------------------------------------------------- primes and the closed-form kernel
XMAX = 1 << 22
isp = np.ones(XMAX + 1, bool); isp[:2] = False
for p in range(2, int(XMAX ** 0.5) + 1):
    if isp[p]: isp[p * p::p] = False
primes = np.nonzero(isp)[0]
lam = np.zeros(XMAX + 1); ppow = np.zeros(XMAX + 1, bool)
for p in primes:
    q, lp = int(p), math.log(p)
    while q <= XMAX: lam[q] = lp; ppow[q] = True; q *= int(p)
k = np.arange(XMAX + 1, dtype=float); k[0] = 1
A = np.cumsum(lam / k); B = np.cumsum(lam)

def kos(x):
    fl = np.floor(x + 1e-9).astype(np.int64); y = 1 / x
    with np.errstate(divide="ignore", invalid="ignore"):
        t = y - 0.5 * (1 + y) * np.log1p(y) + np.where(y < 1, 0.5 * (1 - y) * np.log1p(-np.minimum(y, 1 - 1e-16)), 0.0)
    return A[fl] - B[fl] / x - np.log(x) + 1 + EG - math.log(2 * math.pi) / x + t

def gram(N):
    G = np.zeros((N, N)); m = np.arange(1, N + 1, dtype=float)
    for j in range(N):
        x = m[j:] / m[j]; G[j:, j] = m[j:] * kos(x); G[j, j:] = G[j:, j]
    return G

kind = np.array(["one"] + ["prime" if isp[n] else ("power" if ppow[n] else "composite") for n in range(2, 5001)])

# ---------------------------------------------------------------- Q1
print("== Q1: the angle at which each new integer arrives (to the span of all earlier ones) ==")
N1 = 4096
L, info = lapack.dpotrf(np.asfortranarray(gram(N1)), lower=1)
assert info == 0
n = np.arange(1, N1 + 1)
theta = np.degrees(np.arcsin(np.sqrt(np.minimum(1, np.diag(L) ** 2 / (n * H0)))))
print("first arrivals:", ", ".join(f"{i}: {theta[i - 1]:.1f}°" for i in range(2, 14)))
for lo, hi in ((2, 64), (64, 512), (512, 4096)):
    sel = (n >= lo) & (n < hi)
    parts = []
    for kd in ("prime", "power", "composite"):
        s = sel & (kind[:N1] == kd)
        if s.any(): parts.append(f"{kd}s {np.median(theta[s]):.2f}° (max {theta[s].max():.2f}°)")
    print(f"  n in [{lo}, {hi}): median " + "; ".join(parts))
big = (theta >= 45) & (n >= 2)
print(f"  arrivals at >= 45°: n = {list(n[big])}")

# ---------------------------------------------------------------- Q2
print("\n== Q2: how far the thinnest axis turns when integer N arrives ==")
N2 = 600
G2 = gram(N2)
prev = None; turn = np.zeros(N2 + 1); gapr = np.zeros(N2 + 1)
for N in range(1, N2 + 1):
    w, v = eigh(G2[:N, :N], subset_by_index=[0, min(1, N - 1)])
    u = v[:, 0]
    if prev is not None:
        turn[N] = math.degrees(math.acos(min(1.0, abs(float(u[:-1] @ prev)))))
    if N > 1: gapr[N] = w[1] / w[0]
    prev = u
Ns = np.arange(N2 + 1)
for lo, hi in ((3, 50), (50, 600)):
    sel = (Ns >= lo) & (Ns <= hi)
    parts = [f"{kd}s {np.median(turn[sel & (kind[np.maximum(Ns, 1) - 1] == kd)]):.3f}°" for kd in ("prime", "power", "composite")]
    print(f"  N in [{lo}, {hi}]: median turn " + "; ".join(parts))
top = np.argsort(turn)[::-1][:8]
print("  largest turns: " + ", ".join(f"N = {t} ({kind[t - 1]}) {turn[t]:.1f}°" for t in top))
print(f"  turns >= 45°: {[int(t) for t in Ns[turn >= 45]]}; smallest gap ratio λ2/λ1 over N >= 3: {gapr[3:].min():.2f}")

# ---------------------------------------------------------------- Q3a: particles -> waves
print("\n== Q3a: from the primes alone, Fourier-transform the tower's correlation K(e^u) ==")
U = math.log(XMAX); du = 0.0005
u = np.arange(0, U, du); f = np.exp(u / 2) * kos(np.exp(u))
print(f"  check: K(1) = {f[0]:.6f} (H0 = {H0:.6f})")
w = np.cos(np.pi * u / (2 * U)) ** 2
gg = np.arange(5, 46, 0.002)
F = np.array([2 * np.trapezoid(f * w * np.cos(g * u), u) for g in gg])
pk = [i for i in range(1, len(F) - 1) if F[i] > F[i - 1] and F[i] > F[i + 1]]
at = [i for i in pk if np.min(np.abs(gam[:12] - gg[i])) <= 0.5]; off = [i for i in pk if i not in at]
found = gg[at]
print("  peaks at a zero:", ", ".join(f"{gg[i]:.3f}" for i in at))
print("  zeros:          ", ", ".join(f"{x:.3f}" for x in gam[:8]))
print(f"  weakest peak at a zero {min(F[at]):.2e}; strongest peak elsewhere {max(F[off]) if off else 0:.2e}")
miss = [g for g in gam[:8] if np.min(np.abs(found - g)) > 0.5]
print(f"  every one of the first 8 zeros recovered within 0.5: {not miss}")

# ---------------------------------------------------------------- Q3b: waves -> particles
print("\n== Q3b: from the first zeros alone, -Σ cos(γ_k u) (Fejér-tapered) ==")
for K in (100, KZ):
    g = gam[:K]; tap = 1 - g / g[-1]
    uu = np.arange(0.5, math.log(31), 0.0002)
    S = -np.array([np.sum(tap * np.cos(g * x)) for x in uu])
    pk = [i for i in range(1, len(S) - 1) if S[i] > S[i - 1] and S[i] > S[i + 1]]
    want = [m for m in range(2, 31) if ppow[m]]
    best = {}
    for m in want:                                  # the highest peak within 0.02 of log m
        c = [i for i in pk if abs(uu[i] - math.log(m)) < 0.02]
        if c: best[m] = max(c, key=lambda i: S[i])
    other = [i for i in pk if min(abs(uu[i] - math.log(m)) for m in want) >= 0.02]
    lo = min(S[i] for i in best.values()); hi = max(S[i] for i in other) if other else -np.inf
    weak = min(best, key=lambda m: S[best[m]])
    print(f"  {K} zeros: peaks at {len(best)}/{len(want)} prime powers <= 30; weakest (at {weak}) {lo:.1f},"
          f" strongest peak elsewhere {hi:.1f} (at x = {math.exp(uu[max(other, key=lambda i: S[i])]):.2f})"
          f" -> clean separation: {lo > hi}")

# ---------------------------------------------------------------- Q4: level statistics
print("\n== Q4: nearest-neighbour spacings of the first zeros ==")
Nbar = lambda T: T / (2 * math.pi) * np.log(T / (2 * math.pi * math.e)) + 7 / 8
s = np.diff(Nbar(gam)); s = s / s.mean()
cdf = {"GUE (no time reversal)": lambda x: erf(2 * x / math.sqrt(math.pi)) - 4 * x / math.pi * np.exp(-4 * x * x / math.pi),
       "GOE (time reversal)": lambda x: 1 - np.exp(-math.pi * x * x / 4),
       "Poisson (uncorrelated)": lambda x: 1 - np.exp(-x)}
ss = np.sort(s); emp = np.arange(1, len(ss) + 1) / len(ss)
print(f"  {len(s)} spacings; share below 0.25: {np.mean(s < 0.25):.4f}")
for nm, c in cdf.items():
    ks = max(np.max(np.abs(emp - c(ss))), np.max(np.abs(emp - 1 / len(ss) - c(ss))))
    print(f"  {nm:24s}: predicts {float(c(np.array(0.25))):.4f} below 0.25; KS distance {ks:.3f}")
