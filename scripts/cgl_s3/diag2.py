import sys, math, numpy as np
from collections import Counter
from sympy import nextprime, factorint
from probe import Field, tpm
q = int(nextprime(int(float(sys.argv[1])))); F = Field(q); N = F.N; R = int(round(q**(2/3)))
val, W, b, it = tpm(F, np.ones(len(F.ns), complex), R, iters=80)
p = np.abs(b)**2; p /= p.sum()
order = np.argsort(-p); top = F.ns[order[:150]]
print(f"q={q} N={N} R={R} s1^2/N={val/N:.2f} participation {1/np.sum(p**2):.0f}")
print("  top n's:", sorted(top[:40].tolist()))
print("  mass in top 50/150/500:", [round(p[order[:k]].sum(), 3) for k in (50, 150, 500)])
g = Counter(); 
for n in top[:150]:
    for r in factorint(int(n)): g[r] += 1
print("  most common prime factors among top 150 n:", g.most_common(12))
print("  spread of top 150: min", top.min(), "max", top.max(), " (N, 2N) =", (N, 2*N))
# are they in an AP mod some small modulus? residues of n mod small m
for m in [2,3,4,5,6,8,10,12,30]:
    c = Counter((top % m).tolist()); print(f"  mod {m}: {dict(sorted(c.items()))}")
