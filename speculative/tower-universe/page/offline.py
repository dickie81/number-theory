"""Pivots and smallest eigenvalues of the orbit Gram matrix to N = 32768, for the Gravastar Tower page.
One in-place Cholesky per scenario (its leading blocks factor every G_k), then blocked inverse iteration on leading
blocks. Scenarios: the zeros on the line, and the first zero moved to 1/2 ± δ ± iγ₁ (scripts/ball_rate.py, section D)."""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
import sys, math, json, time, base64
import numpy as np
from scipy.linalg import lapack, solve_triangular
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'scripts'))
from ball_orbit import kernel_over_sqrt, tables
G1 = 14.134725141734693

def zero_term(u, beta):
    r = beta + 1j * G1
    return 2 * np.real(np.exp((r - 0.5) * u) / (r * (1 - r)))

def build(N, delta, block=256):
    A, B = tables(N + 1)
    G = np.empty((N, N), order='F')
    m = np.arange(1, N + 1, dtype=float)
    for c0 in range(0, N, block):
        c1 = min(N, c0 + block)
        cols = m[c0:c1][None, :]
        hi = np.maximum(m[:, None], cols); lo = np.minimum(m[:, None], cols)
        x = hi / lo
        blk = hi * kernel_over_sqrt(x, A, B)
        if delta:
            u = np.log(x)
            blk += np.sqrt(m[:, None] * cols) * (-zero_term(u, 0.5) + zero_term(u, 0.5 + delta) + zero_term(u, 0.5 - delta))
        G[:, c0:c1] = blk
    return G

def fsolve(L, b, k, bs=1024):
    for c0 in range(0, k, bs):
        c1 = min(k, c0 + bs)
        b[c0:c1] = solve_triangular(L[c0:c1, c0:c1], b[c0:c1], lower=True, check_finite=False)
        if c1 < k:
            b[c1:k] -= L[c1:k, c0:c1] @ b[c0:c1]
    return b

def bsolve(L, b, k, bs=1024):
    for c0 in reversed(range(0, k, bs)):
        c1 = min(k, c0 + bs)
        if c1 < k:
            b[c0:c1] -= L[c1:k, c0:c1].T @ b[c1:k]
        b[c0:c1] = solve_triangular(L[c0:c1, c0:c1], b[c0:c1], lower=True, trans='T', check_finite=False)
    return b

def lam_grid(L, ks, iters=6):
    out, v = [], None
    for k in ks:
        if v is None:
            v = np.ones(k) / math.sqrt(k)
        else:
            v = np.concatenate([v, np.zeros(k - len(v))]); v /= np.linalg.norm(v)
        lam = None
        for _ in range(iters):
            z = bsolve(L, fsolve(L, v.copy(), k), k)
            lam = 1.0 / float(v @ z)
            v = z / np.linalg.norm(z)
        out.append([int(k), lam])
        print(f"   k={k}: lambda={lam:.6e}  k*lambda={k*lam:.5f}", flush=True)
    return out

def run(delta, Ntry):
    t0 = time.time()
    G = build(Ntry, delta)
    print(f"delta={delta}: built N={Ntry} in {time.time()-t0:.0f}s", flush=True)
    t1 = time.time()
    c, info = lapack.dpotrf(G, lower=1, clean=0, overwrite_a=1)
    assert c is G or np.shares_memory(c, G)
    kc = int(info) if info > 0 else 0
    good = (kc - 1) if kc else Ntry
    print(f"delta={delta}: dpotrf info={info} ({time.time()-t1:.0f}s); positive definite through N={good}", flush=True)
    piv = np.diag(c)[:good] ** 2
    ratio = (piv / piv[0]).astype(np.float32)
    ks = [k for k in sorted({int(round(2048 * 2 ** (j / 16))) for j in range(0, 65)}) if k <= good]
    if kc:
        ks = sorted(set(ks) | {good - d for d in (0, 1, 2, 4, 8, 16, 32, 64, 128, 256) if good - d >= 2048})
    lam = lam_grid(c, ks) if ks else []
    res = {"delta": delta, "collapse": kc, "good": good, "pivots": base64.b64encode(ratio.tobytes()).decode(),
           "lam": lam, "d1": float(piv[0])}
    del G, c
    return res

out = []
for delta, Ntry in ((0.01, 16384), (0.005, 16384), (0.002, 24576), (0.0, 32768)):
    r = run(delta, Ntry)
    out.append(r)
    with open(os.path.join(HERE, 'data.json'), 'w') as f:
        json.dump(out, f)
print("done", flush=True)
