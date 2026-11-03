# Uncertified: more junction splits ("hyperplanes") of the prime-side Gram matrix (ball_orbit.gram; no zeros used),
# and half-dimensional sphere-area weights. Junction J = off-block part of G; report SVD capture.
import sys, os, functools, numpy as np
print = functools.partial(print, flush=True)
from math import gamma, pi, log, sqrt
sys.path.insert(0, 'scripts')
import ball_orbit as bo
Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4095
cache = '/workspace/gram_4095.npy'   # optional local cache of ball_orbit.gram(4095); slicing is consistent (see junction_scale.py)
G = np.load(cache, mmap_mode='r')[:Mmax, :Mmax].copy() if os.path.exists(cache) else np.array(bo.gram(Mmax), dtype=float)
N = np.arange(1, Mmax + 1)
def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
F = [factor(int(n)) for n in N]
Om = np.array([sum(f.values()) for f in F]); sqf = np.array([all(e == 1 for e in f.values()) for f in F])
mu = np.where(sqf, (-1) ** Om, 0)
def qr(p): return np.array([0 if n % p == 0 else (1 if pow(int(n), (p - 1) // 2, p) == 1 else 2) for n in N])
splits = {
    "base sqrt2 (half-dyadic)": lambda M: np.floor(2 * np.log2(N[:M])).astype(int),
    "base golden ratio": lambda M: np.floor(np.log(N[:M]) / log((1 + sqrt(5)) / 2)).astype(int),
    "squarefree vs not": lambda M: sqf[:M].astype(int),
    "Liouville sign (Omega parity)": lambda M: Om[:M] % 2,
    "mu sign classes (-1,0,1)": lambda M: mu[:M] + 1,
    "QR class mod 3": lambda M: qr(3)[:M], "QR class mod 5": lambda M: qr(5)[:M], "QR class mod 7": lambda M: qr(7)[:M],
    "reflection n<sqrtM vs n>sqrtM": lambda M: (N[:M] > sqrt(M)).astype(int),
    "reflection dyadic in n/sqrtM": lambda M: np.floor(np.abs(np.log2(N[:M] / sqrt(M)))).astype(int) * np.sign(np.log(N[:M] / sqrt(M)) + 1e-12).astype(int),
    "dyadic (reference)": lambda M: np.floor(np.log2(N[:M])).astype(int),
}
sizes = [M for M in (255, 511, 1023, 2047, 4095) if M <= Mmax]
store = {}
print("## Junction capture: frac by 4 directions / directions for 95%")
for name, lab in splits.items():
    out = []
    for M in sizes:
        L = lab(M); H = G[:M, :M]; J = np.where(L[:, None] == L[None, :], 0.0, H)
        U, s, _ = np.linalg.svd(J); f = np.cumsum(s**2) / (s**2).sum()
        out.append(f"{f[3]:.2f}/{int(np.searchsorted(f, .95) + 1)}"); store[name] = (U, s, L)
    print(f"{name:32s} " + "  ".join(out))
print("\n## Best Mellin frequency of top-4 junction vectors (largest size), on n in [M/2, M]")
gs = np.arange(2, 60, 0.02); M = sizes[-1]; n = np.arange(M // 2, M + 1)
for name in ("base sqrt2 (half-dyadic)", "base golden ratio", "reflection dyadic in n/sqrtM", "Liouville sign (Omega parity)"):
    U = store[name][0]; res = []
    for i in range(4):
        x = U[n - 1, i]; r = [np.linalg.norm(x - (B := np.stack([np.ones(len(n)), np.cos(g * np.log(n)), np.sin(g * np.log(n))], 1)) @ np.linalg.lstsq(B, x, rcond=None)[0]) / np.linalg.norm(x) for g in gs]
        j = int(np.argmin(r)); res.append(f"{gs[j]:.1f}(r={r[j]:.2f})")
    print(f"{name:32s} " + " ".join(res))
print("\n## Half-dimensional area weights, dyadic blocks; min eigenvalue")
area = lambda d: 2 * pi ** (d / 2) / gamma(d / 2)
schemes = {"d=k+1/2": lambda k: area(k + .5), "d=2^k+1/2": lambda k: area(min(2**k, 340) + .5),
           "d=k/2+1/2": lambda k: area(k / 2 + .5)}
for M in sizes:
    H = G[:M, :M]; L = np.floor(np.log2(N[:M])).astype(int); same = L[:, None] == L[None, :]
    row = [f"M={M:5d} unweighted {np.linalg.eigvalsh(H)[0]:+.2e}"]
    for nm, f in schemes.items():
        w = np.array([f(k) for k in L]); w /= w.max(); sw = np.sqrt(w)
        B = np.where(same, w[:, None] * H, H)                       # blocks weighted
        C = np.where(same, H, sw[:, None] * H * sw[None, :])        # junction only weighted
        row.append(f"[{nm}] B {np.linalg.eigvalsh(B)[0]:+.2e} C {np.linalg.eigvalsh(C)[0]:+.2e}")
    print(" | ".join(row))
