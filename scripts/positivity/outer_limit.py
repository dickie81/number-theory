# Uncertified: outer products in the limit. (a) dyadic junction as k -> infinity; (b) the limit operator in the log
# variable and its outer-product (Bochner) structure; (c) averaged outer products of sphere vectors.
import sys, numpy as np
sys.path.insert(0, 'scripts'); import ball_orbit as bo
out = open('scripts/positivity/outer_limit_results.txt', 'w')
def P(s): print(s, flush=True); out.write(s + "\n"); out.flush()
X = 10**5; A, B = bo.tables(X + 2)
K = lambda x: np.sqrt(x) * bo.kernel_over_sqrt(np.asarray(x, float), A, B)   # K_H(x), x >= 1
# (a) continuum junction kernel: m = 2^{k+u}, n = 2^{k+1+v}, counting measure ~ 2^{k+u} ln2 du, so G/(4^k ln2) -> 2^u 2^{1+v} K(2^{1+v-u})
g = 400; u = (np.arange(g) + .5)/g
Kc = np.outer(2**u, 2**(1+u)) * K(2**(1 + u[None, :] - u[:, None])) / g
Uc, sc, Vc = np.linalg.svd(Kc)
P("(a) continuum junction kernel B_inf(u,v) = 2^u 2^(1+v) K_H(2^(1+v-u)): top singular values")
P("   " + " ".join(f"{x:.4f}" for x in sc[:10]) + f"   k95={np.searchsorted(np.cumsum(sc**2)/np.sum(sc**2), .95)+1}, rank-1 share {sc[0]**2/np.sum(sc**2):.3f}")
for k in range(6, 12):
    a = np.arange(2**k, 2**(k+1)); b = np.arange(2**(k+1), 2**(k+2))
    M = np.sqrt(np.outer(a, b)) * K(np.outer(1/a, b)) / (4**k * np.log(2))
    U, s, Vt = np.linalg.svd(M)
    ua = np.log2(a) - k; f1 = np.interp(u, ua, U[:, 0]); f1 /= np.linalg.norm(f1); c1 = abs(f1 @ Uc[:, 0])
    P(f"   k={k:2d}: top sv/(4^k ln2) " + " ".join(f"{x:.4f}" for x in s[:6]) + f" | max rel diff to continuum (top 6) {np.max(abs(s[:6]-sc[:6])/sc[:6]):.2e} | leading singular function corr {c1:.4f}")
# (b) limit operator: convolution by k(t) = K_H(e^|t|) on the log line; outer products = Bochner measure
T = np.log(X); t = np.linspace(0, T, 40001); kt = K(np.exp(t)); dt = t[1] - t[0]
xi = np.linspace(0.5, 60, 2391); fej = 1 - t/T
F = np.array([2*np.sum(kt*fej*np.cos(x*t))*dt - kt[0]*dt for x in xi])  # Fejer-windowed Fourier transform (even k)
P(f"\n(b) Fejer-windowed Fourier transform of k(t)=K_H(e^|t|) on |t| <= log {X:.0e}: min {F.min():.3e} at xi={xi[np.argmin(F)]:.2f}, max {F.max():.3e}")
pk = [xi[i] for i in range(1, len(F)-1) if F[i] > F[i-1] and F[i] > F[i+1] and F[i] > 0.1*F.max()]
P("   peaks (outer-product frequencies of the limit, cos(xi t)cos(xi s)+sin sin): " + " ".join(f"{p:.2f}" for p in pk[:12]))
P("   (Bochner: k positive definite <=> transform >= 0 <=> the limit is a nonnegative superposition of outer products; under RH the measure sits at the zeros)")
# (c) averaged outer products of unit vectors of the block metric: E[v v^T] = G^{-1}/d for v uniform on {v'Gv = 1}
d = 32; Gb = np.array(bo.gram(2*d - 1), float)[d-1:, d-1:]; L = np.linalg.cholesky(Gb)
rng = np.random.default_rng(0); w = rng.standard_normal((200000, d)); w /= np.linalg.norm(w, axis=1)[:, None]
v = np.linalg.solve(L.T, w.T).T; E = v.T @ v / len(v)
P(f"\n(c) block [{d},{2*d-1}]: ||E[vv^T] - G^-1/d|| / ||G^-1/d|| = {np.linalg.norm(E - np.linalg.inv(Gb)/d)/np.linalg.norm(np.linalg.inv(Gb)/d):.3f} (Monte Carlo); the average is the inverse Gram, positive iff G is")
