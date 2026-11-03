# Uncertified: which parts of the prime-side Gram are manifestly Gram, and how big is the non-Gram remainder?
# K_H(x)/sqrt x = sum_{k<=x} Lam(k)(1/k - 1/x) - log x + 1 + gamma - log(2pi)/x + tail(1/x)   (ball_orbit)
# Split 1: G = P + A, P_mn = sum_{k<=r} Lam(k)(hi/k - lo) (primes, weights >= 0), A = hi*(arch terms incl. -log r).
# Split 2: G = C + R, C = hi*(1 + gamma - log(2pi)/r + tail(1/r)) (no primes), R = hi*int_1^r (psi(t)-t)/t^2 dt.
import sys, math, numpy as np
sys.path.insert(0, 'scripts'); import ball_orbit as bo
out = open('scripts/positivity/junction_sphere_results.txt', 'w')
def P_(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
Mx = 4095; G = np.array(bo.gram(Mx), dtype=float)
m = np.arange(1, Mx+1, dtype=float); HI = np.maximum.outer(m, m); LO = np.minimum.outer(m, m); r = HI/LO; y = 1/r
with np.errstate(divide="ignore", invalid="ignore"):
    t = np.where(y < 1, 0.5*(1-y)*np.log1p(-np.minimum(y, 1-1e-300)), 0.0)
tail = y + t - 0.5*(1+y)*np.log1p(y)
C = HI*(1 + bo.EULER_GAMMA - math.log(2*math.pi)*y + tail)
A = C - HI*np.log(r); Pp = G - A; R = G - C
P_(f"check P >= 0 entrywise: min {Pp.min():.2e}; diag of P max |.| {abs(np.diag(Pp)).max():.2e} (zero diagonal => P is not PSD)")
lmin = lambda X: np.linalg.eigvalsh(X)[0]
for M in (255, 1023, 4095):
    S = slice(0, M)
    P_(f"\nM={M}: lambda_min  G {lmin(G[S,S]):.3e} | P(primes) {lmin(Pp[S,S]):.3e} | A(arch) {lmin(A[S,S]):.3e} | C(main) {lmin(C[S,S]):.3e} | R(psi-t) {lmin(R[S,S]):.3e}")
    K = int(np.log2(M+1)); bl = [np.arange(2**a, 2**(a+1))-1 for a in range(K)]
    for a in (K-3, K-2):
        I, J = bl[a], bl[a+1]; ix = np.r_[I, J]
        Ga, Gb, B = G[np.ix_(I, I)], G[np.ix_(J, J)], G[np.ix_(I, J)]
        wa, Va = np.linalg.eigh(Ga); wb, Vb = np.linalg.eigh(Gb)
        T = (Va/np.sqrt(wa)) .T @ B @ (Vb/np.sqrt(wb))   # A^{-1/2} B C^{-1/2}
        contr = np.linalg.norm(T, 2)
        Cp, Rp = C[np.ix_(ix, ix)], R[np.ix_(ix, ix)]
        wc, Vc = np.linalg.eigh(Cp)
        P_(f"  pair [{I[0]+1},{I[-1]+1}]x[{J[0]+1},{J[-1]+1}]: ||A^-1/2 B C^-1/2|| = {contr:.6f} (<=1 iff junction realisable by the blocks' own vectors); "
           f"lambda_min pair G {lmin(G[np.ix_(ix,ix)]):.3e}, C {wc[0]:.3e}, R {lmin(Rp):.3e}; ||R||/||C|| = {np.linalg.norm(Rp)/np.linalg.norm(Cp):.3f}; "
           f"margin of C on C-positive part vs remainder: max over top-|R| dir of -v'Rv/v'Cv = {max(-(Vc[:,i]@Rp@Vc[:,i])/wc[i] for i in range(len(wc)) if wc[i]>0):.3f}")
