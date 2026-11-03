# Uncertified: do junction directions between the top two dyadic blocks come in groups of 4 per zeta zero?
import sys, time, numpy as np
sys.path.insert(0, 'scripts'); import ball_orbit as bo
Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4095
Z = np.array([14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271])
out = open('scripts/positivity/junction_groups_results.txt', 'a')
def P(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
t0 = time.time(); G = np.array(bo.gram(Mmax), dtype=float); P(f"gram {Mmax} {time.time()-t0:.0f}s")
gs = np.arange(2, 60, 0.02)
def bestg(x, n):
    ln = np.log(n); one = np.ones_like(ln); best = (1e9, 0)
    for g in gs:
        B = np.stack([one, np.cos(g*ln), np.sin(g*ln)], 1)
        r = np.linalg.norm(x - B @ np.linalg.lstsq(B, x, rcond=None)[0]) / np.linalg.norm(x)
        if r < best[0]: best = (r, g)
    return best[1], best[0]
M = 255
while M <= Mmax:
    k = int(np.log2(M + 1)); A = np.arange(2**(k-2), 2**(k-1)); B = np.arange(2**(k-1), 2**k)
    C = G[np.ix_(A-1, B-1)]; U, s, Vt = np.linalg.svd(C)
    f = np.cumsum(s**2)/(s**2).sum(); k95, k99 = [int(np.searchsorted(f, q)+1) for q in (.95, .99)]
    P(f"\nM={M} blocks [{A[0]},{A[-1]}]x[{B[0]},{B[-1]}] k95={k95} k99={k99} resolution 2pi/log2={2*np.pi/np.log(2):.1f}")
    P("  s_i/s_1: " + " ".join(f"{x:.3f}" for x in s[:24]/s[0]))
    P("  gaps s_i/s_(i+1) (big = cluster edge): " + " ".join(f"{i+1}:{s[i]/s[i+1]:.2f}" for i in range(23)))
    cnt = {}
    for i in range(24):
        gl, rl = bestg(U[:, i], A.astype(float)); gr, rr = bestg(Vt[i], B.astype(float))
        zl = Z[np.argmin(abs(Z-gl))]; zr = Z[np.argmin(abs(Z-gr))]
        for g, z in ((gl, zl), (gr, zr)):
            if abs(g-z) < 2: cnt[z] = cnt.get(z, 0) + 1
        P(f"  vec{i+1:2d} left g={gl:5.2f} r={rl:.2f} | right g={gr:5.2f} r={rr:.2f}")
    P("  side-fits within 2 of a zero (2 sides x 24 vecs): " + str({float(z): c for z, c in sorted(cnt.items())}))
    M = 2*M + 1
