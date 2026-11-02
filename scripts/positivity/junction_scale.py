# Uncertified: does the dyadic junction rank stay bounded as the size grows, and what are its directions?
import sys, time, numpy as np
sys.path.insert(0, 'scripts')
import ball_orbit as bo
Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4095
t0 = time.time(); G = np.array(bo.gram(Mmax), dtype=float); print("gram", Mmax, f"{time.time()-t0:.1f}s")
Gs = np.array(bo.gram(2047), dtype=float)
print("cutoff consistency max|G_2047 - G_4095[:2047]| / max|G| =", np.abs(Gs - G[:2047, :2047]).max() / np.abs(Gs).max())
print("symmetry", np.abs(G - G.T).max())
def lab(M): return np.floor(np.log2(np.arange(1, M + 1))).astype(int)
res = {}
for M in (255, 511, 1023, 2047, 4095):
    if M > Mmax: break
    H = G[:M, :M]; L = lab(M)
    J = np.where(L[:, None] == L[None, :], 0.0, H)
    U, s, _ = np.linalg.svd(J)
    f = np.cumsum(s**2) / (s**2).sum()
    ks = [int(np.searchsorted(f, q) + 1) for q in (0.90, 0.95, 0.99)]
    r = s[1:21] / s[:20]
    print(f"M={M:5d} k90={ks[0]:3d} k95={ks[1]:3d} k99={ks[2]:4d} sigma ratios s_(i+1)/s_i (i=1..12): " +
          " ".join(f"{x:.2f}" for x in r[:12]))
    res[M] = (U, s, L)
# per-pair coupling vs |a-b| (relative Frobenius norm normalised by sqrt of block norms), largest size
M = max(res); U, s, L = res[M]; H = G[:M, :M]
print("\npair coupling ‖C_ab‖_F / sqrt(‖G_aa‖_F ‖G_bb‖_F) by gap |a-b| (averaged), M =", M)
for gap in range(1, 9):
    vals = []
    for a in range(3, L.max() + 1 - gap):
        A = L == a; B = L == a + gap
        vals.append(np.linalg.norm(H[np.ix_(A, B)]) / np.sqrt(np.linalg.norm(H[np.ix_(A, A)]) * np.linalg.norm(H[np.ix_(B, B)])))
    print(f"gap {gap}: {np.mean(vals):.3f}")
# directions: restrict top singular vectors to each block, resample on u = n/2^a in [1,2), compare across a
print("\ndirections: correlation of top-6 vectors' block profiles (u = n/2^a) between consecutive blocks a, a+1")
ug = np.linspace(1, 2, 200, endpoint=False)
def profile(v, a):
    n = np.arange(2**a, 2**(a+1)); x = v[n - 1]
    p = np.interp(ug, n / 2**a, x); return p / (np.linalg.norm(p) + 1e-300)
for i in range(6):
    v = U[:, i]
    cs = [abs(profile(v, a) @ profile(v, a + 1)) for a in range(5, L.max())]
    print(f"vec {i+1}: |corr| consecutive blocks a=5..{L.max()-1}: " + " ".join(f"{c:.2f}" for c in cs))
# fits on the top block profile: basis in t = log u
print("\nfit of block profiles (largest two blocks) to basis families: relative residual")
for i in range(6):
    v = U[:, i]; out = []
    for a in (L.max() - 1, L.max()):
        n = np.arange(2**a, min(2**(a+1), M + 1)); x = v[n - 1]; u = n / 2**a; t = np.log(u)
        fams = {
            "Legendre deg<=3 in log u": np.stack([t**d for d in range(4)], 1),
            "u^{1/2},u^{-1/2},u^{1/2}log u,1": np.stack([u**.5, u**-.5, u**.5 * t, np.ones_like(u)], 1),
            "Mellin gamma=14.13,21.02 (cos,sin) + 1": np.stack([np.ones_like(u)] + [g(gm * np.log(n)) for gm in (14.1347, 21.0220) for g in (np.cos, np.sin)], 1),
            "Mellin gamma=10,17 (control)": np.stack([np.ones_like(u)] + [g(gm * np.log(n)) for gm in (10.0, 17.0) for g in (np.cos, np.sin)], 1),
        }
        out.append({k: np.linalg.norm(x - B @ np.linalg.lstsq(B, x, rcond=None)[0]) / np.linalg.norm(x) for k, B in fams.items()})
    print(f"vec {i+1}: " + "; ".join(f"{k}: {out[0][k]:.2f}/{out[1][k]:.2f}" for k in out[0]))
# frequency scan: best single Mellin frequency gamma (cos, sin, 1) for each top vector on the largest full block
print("\nfrequency scan, gamma in [2, 60] step 0.01: best gamma per vector (largest full block)")
a = int(np.log2(M + 1)) - 1; n = np.arange(2**a, 2**(a+1)); gs = np.arange(2, 60, 0.01)
for i in range(8):
    x = U[n - 1, i]; r = []
    for gm in gs:
        B = np.stack([np.ones_like(n, dtype=float), np.cos(gm * np.log(n)), np.sin(gm * np.log(n))], 1)
        r.append(np.linalg.norm(x - B @ np.linalg.lstsq(B, x, rcond=None)[0]) / np.linalg.norm(x))
    r = np.array(r); j = np.argmin(r)
    print(f"vec {i+1}: best gamma={gs[j]:.2f} resid={r[j]:.2f}  (sigma_{i+1}={s[i]:.3e})")
