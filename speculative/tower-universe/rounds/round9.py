"""Round 9 (PREREG9.md): ANU quantum bits against the tower's click-parity coin."""
import math, sys, time
import numpy as np
import mpmath as mp
HERE = sys.path[0]
L = 10 ** 7

# ------------------------------------------------------------------ sequences
def sieve(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]: s[p * p::p] = False
    return np.nonzero(s)[0]

def omega_window(N0, n, base):
    """Ω(m) for m in [N0, N0 + n), by dividing out every prime up to sqrt(N0 + n)."""
    res = np.arange(N0, N0 + n, dtype=np.int64); Om = np.zeros(n, np.int8); hi = N0 + n - 1
    for p in base:
        p = int(p); pk = p
        while pk <= hi:
            st = (-N0) % pk
            if st >= n: break
            Om[st::pk] += 1; res[st::pk] //= p; pk *= p
    Om += (res > 1)
    return Om

def omega_full(n):
    Om = np.zeros(n + 1, np.int8)
    for p in sieve(n):
        q = int(p)
        while q <= n: Om[q::q] += 1; q *= int(p)
    return Om

t0 = time.time()
full = omega_full(L)
chk = omega_window(1, 10 ** 6, sieve(1001))
assert np.array_equal(chk, full[1:10 ** 6 + 1]), "segmented Ω disagrees with the plain sieve"
print(f"[segmented Ω matches the plain sieve on [1, 10^6]; {time.time() - t0:.0f} s]")
pm = lambda Om: np.where(Om % 2 == 0, 1, -1).astype(np.int8)
seqs = {"tower, from its origin": [pm(full[1:L + 1])]}
for N0s, tag in (([10 ** 12 + j * 10 ** 9 for j in range(4)], "tower, late (10^12)"),
                 ([10 ** 15 + j * 10 ** 9 for j in range(4)], "tower, late (10^15)")):
    base = sieve(int(math.isqrt(max(N0s) + L)) + 1)
    seqs[tag] = []
    for N0 in N0s:
        t0 = time.time(); seqs[tag].append(pm(omega_window(N0, L, base)))
        print(f"[window at {N0:.3e}: {time.time() - t0:.0f} s]")
raw = np.unpackbits(np.frombuffer(open(f"{HERE}/qrng_dl/anubits_1.prefix", "rb").read()[:25 * 10 ** 6], np.uint8))
seqs["ANU quantum bits"] = [np.where(raw[k * L:(k + 1) * L] == 1, 1, -1).astype(np.int8) for k in range(20)]
rng = np.random.default_rng(20261106)
seqs["pseudo-random (PCG64)"] = [rng.choice(np.array([-1, 1], np.int8), L) for _ in range(20)]

# ------------------------------------------------------------------ the tower's tone pattern (round 8, Q11)
gam = np.load(f"{HERE}/zeros_3000.npy")[:200]
mp.mp.dps = 20
coef = np.array([complex(mp.zeta(2 * mp.mpc(0.5, g)) / (mp.mpc(0.5, g) * mp.zeta(mp.mpc(0.5, g), derivative=1))) for g in gam])
zt = np.unique(np.round(np.exp(np.linspace(math.log(1e4), math.log(L), 2000))).astype(int))
P = 2 * np.real(np.exp(1j * np.outer(np.log(zt), gam)) @ coef)
xd = np.unique(np.round(np.exp(np.linspace(math.log(1e3), math.log(L), 4000))).astype(int))

def stats(x):
    S = np.cumsum(x, dtype=np.int64)
    a, b, c = (x[:-2] > 0), (x[1:-1] > 0), (x[2:] > 0)
    cnt = np.bincount(a * 4 + b * 2 + c, minlength=8); n3 = len(a)
    zpat = np.max(np.abs(cnt - n3 / 8) / math.sqrt(n3 * (1 / 8) * (7 / 8)))
    zbias = S[-1] / math.sqrt(len(x))
    zlag = max(abs(float(np.dot(x[:-h].astype(np.int32), x[h:]))) / math.sqrt(len(x)) for h in (1, 2, 3))
    D = float(np.mean(S[xd - 1] / np.sqrt(xd)))
    r = S[zt - 1] / np.sqrt(zt); tone = float(np.corrcoef(r - r.mean(), P)[0, 1])
    return zpat, zbias, zlag, D, tone

print(f"\n{'sequence':24s} {'n':>3s} {'S1 patterns |z|':>15s} {'bias z':>8s} {'lags |z|':>9s}"
      f" {'S2 drift D':>16s} {'S3 tones':>15s} {'fingerprints':>12s}")
for name, xs in seqs.items():
    st = np.array([stats(x) for x in xs])
    fp = int(np.sum((np.abs(st[:, 3] + 0.685) <= 0.3) & (st[:, 4] > 0.5)))
    sd = lambda v: f"{v.mean():+.3f}" + (f" ± {v.std(ddof=1):.3f}" if len(v) > 1 else "        ")
    print(f"{name:24s} {len(xs):3d} {st[:, 0].max():15.2f} {np.abs(st[:, 1]).max():8.2f} {st[:, 2].max():9.2f}"
          f" {sd(st[:, 3]):>16s} {sd(st[:, 4]):>15s} {fp:>6d}/{len(xs)}")
