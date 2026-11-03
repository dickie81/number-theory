# Uncertified: does the prime-side Gram look like a round-sphere Laplacian S^d (or a function of one)?
import sys, time, numpy as np
from math import comb
sys.path.insert(0, 'scripts'); import ball_orbit as bo
out = open('scripts/positivity/hypersphere_results.txt', 'w')
def P(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
def sphere(d, K):  # eigenvalues l(l+d-1) of S^d, multiplicity dim H_l, first K
    ev = []; l = 0
    while len(ev) < K:
        m = comb(l+d, d) - (comb(l+d-2, d) if l >= 2 else 0); ev += [l*(l+d-1)]*m; l += 1
    return np.array(ev[:K], float)
def ratio_stat(e):
    e = np.sort(e); s = np.diff(e); s = s[s > 0]; r = np.minimum(s[1:], s[:-1]) / np.maximum(s[1:], s[:-1]); return r.mean()
def weyl_slope(e):  # slope of log N(lambda) vs log lambda on middle 10..90% (sphere: d/2)
    e = np.sort(e); e = e[e > 0]; K = len(e); i = np.arange(int(.1*K), int(.9*K))
    return np.polyfit(np.log(e[i]), np.log(i+1), 1)[0]
def sphere_fit(e):  # best d, affine scale, relative rms error (on the spectrum sorted ascending)
    e = np.sort(e); K = len(e); best = []
    for d in range(1, 13):
        s = sphere(d, K); A = np.stack([s, np.ones(K)], 1); c = np.linalg.lstsq(A, e, rcond=None)[0]
        best.append((np.linalg.norm(A@c - e)/np.linalg.norm(e - e.mean()), d))
    return sorted(best)[:3]
def degeneracy(e):  # fraction of consecutive relative gaps < 1e-6 (exact multiplicities)
    e = np.sort(abs(e)); g = np.diff(e)/np.maximum(e[1:], 1e-300); return (g < 1e-6).mean()
P("reference <r>: Poisson 0.386, GOE 0.531, GUE 0.600, picket fence 1.0 (degenerate sphere: many exact ties)")
for d in (2, 3, 5): s = sphere(d, 4095); P(f"S^{d} first 4095: Weyl slope {weyl_slope(s[s>0]):.2f} (d/2={d/2}), tie fraction {degeneracy(s[s>0]):.2f}")
G = np.array(bo.gram(4095), dtype=float)
for M in (255, 1023, 4095):
    H = G[:M, :M]; w = np.linalg.eigvalsh(H); n = np.arange(1, M+1, dtype=float)
    wi = np.linalg.eigvalsh(n[:, None] + n[None, :] - H); neg = -wi[wi < 0]
    P(f"\n=== M={M} === eig G range [{w.min():.2e}, {w.max():.2e}]")
    for lab, e in (("G", w), ("log G (shifted)", np.log(w) - np.log(w.min())), ("1/G", 1/w), ("-inter neg part", neg)):
        P(f" {lab:16s}: Weyl slope {weyl_slope(e):.3f} (=> d≈{2*weyl_slope(e):.2f}), <r>={ratio_stat(e):.3f}, ties {degeneracy(e):.3f}, best sphere fits (relerr,d) {[(round(a,3),b) for a,b in sphere_fit(e)]}")
# zeta zeros
import mpmath as mp
t0 = time.time(); NZ = int(sys.argv[1]) if len(sys.argv) > 1 else 1000; z = []
for k in range(1, NZ+1):
    z.append(float(mp.zetazero(k).imag))
    if time.time() - t0 > 400: break
z = np.array(z); P(f"\n=== zeta zeros: {len(z)} computed ({time.time()-t0:.0f}s), gamma_max={z[-1]:.1f} ===")
k = np.arange(1, len(z)+1); rv = lambda T: T/(2*np.pi)*np.log(T/(2*np.pi*np.e)) + 7/8
P(f" Riemann–von Mangoldt N(T) misfit: max |k - N(gamma_k)| = {np.abs(k - 0.5 - rv(z)).max():.2f}")
# treat gamma as sqrt of Laplacian eigenvalue (lambda = gamma^2) and as lambda = gamma
for lab, e in (("lambda=gamma^2", z**2), ("lambda=gamma", z)):
    sl = weyl_slope(e); i = np.arange(int(.1*len(e)), int(.9*len(e)))
    c = np.polyfit(np.log(e[i]), np.log(i+1), 1); res = np.log(i+1) - np.polyval(c, np.log(e[i]))
    P(f" {lab}: power-law slope {sl:.3f} (=> d≈{2*sl:.2f}), rms log-residual of power law {res.std():.4f}, best sphere fits {[(round(a,3),b) for a,b in sphere_fit(e)]}")
# local slope drift: if power law, slope constant; RvM gives slope 1 + 1/log(T/2pi) drifting
for a, b in ((0.1, 0.3), (0.4, 0.6), (0.7, 0.9)):
    i = np.arange(int(a*len(z)), int(b*len(z))); P(f"  local slope d log N / d log gamma on [{a},{b}]: {np.polyfit(np.log(z[i]), np.log(i+1), 1)[0]:.3f}")
P(f" zeros <r> = {ratio_stat(z):.3f}, ties {degeneracy(z):.3f}")
