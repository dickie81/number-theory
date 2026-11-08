import sys, numpy as np
from sympy import nextprime, primerange
from probe import tpm
from s3direct import KField, gram
q = int(nextprime(int(float(sys.argv[1]))))
F = KField(q); Kd = F.Kvec(); N = F.N; R = int(round(q**(2/3))); M = q/N
val, W, b, it = tpm(F, np.ones(len(F.ns), complex), R)
G = gram(Kd, W, q-1)
ev = np.linalg.eigvalsh(G)[::-1]
print(f"q={q} N={N} R={R} M={M:.2f}  top eigenvalues of G_W / N: {np.round(ev[:12]/N, 2)}")
print(f"  #eig > 2N: {np.sum(ev > 2*N)}, > 3N: {np.sum(ev > 3*N)};  sum eig^3 / (|W|N^3) = {np.sum(ev**3)/(R*N**3):.3f}")
off = np.abs(G[~np.eye(R, dtype=bool)])**2
allK = np.abs(Kd[1:])**2
print(f"  |K|^2 on W-differences: mean {off.mean()/N:.2f} N, 99% {np.quantile(off,0.99)/N:.2f} N, max {off.max()/N:.2f} N;"
      f"  over all psi: mean {allK.mean()/N:.2f} N, max {allK.max()/N:.2f} N (q/N = {q/N:.1f})")
# top eigenvector support structure over W
vals, vecs = np.linalg.eigh(G); v = vecs[:, -1]
p = np.abs(v)**2
print(f"  top eigvec over W: participation ratio 1/sum p^2 = {1/np.sum(p**2):.0f} of {R}")
# the W-indices mod small divisors of q-1
from sympy import divisors
for d in [d for d in divisors(q-1) if 2 <= d <= 60]:
    c = np.bincount(np.asarray(W) % d, minlength=d)
    print(f"  W mod {d}: max/mean {c.max()/c.mean():.2f}")
# which characters: is W close to the top-|K| set?
topK = np.argpartition(-np.abs(Kd), R)[:R]
print(f"  overlap with top-|K| set: {len(np.intersect1d(W, topK))}/{R}")
# the top singular vector b on n: correlation with smooth/flat
bn = np.abs(b)**2
print(f"  b: participation {1/np.sum((bn/bn.sum())**2):.0f} of {len(bn)} n's")
