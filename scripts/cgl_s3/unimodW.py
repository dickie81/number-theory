"""For the W found with unimodular b: its free large-sieve constant s1(M_W)^2 (any b), and S3 = tr(E^3) / CGL bound."""
import sys, numpy as np
from sympy import nextprime
from probe import fixedW_norm
from s3direct import KField, gram

def unimod_W(F, b, R, iters=150):
    best = (0, None)
    for it in range(iters):
        D = F.D(b); P = np.abs(D)**2
        W = np.argpartition(P, -R)[-R:]
        val = P[W].sum()/np.sum(F.w**2)
        if val > best[0]:
            best = (val, np.sort(W))
        c = np.zeros_like(D); c[W] = D[W]
        b = np.exp(1j*np.angle(F.adj(c)))
    return best

for q0 in sys.argv[1:]:
    q = int(nextprime(int(float(q0)))); F = KField(q); N = F.N; R = int(round(q**(2/3)))
    val, W = unimod_W(F, np.ones(len(F.ns), complex), R)
    s1 = fixedW_norm(F, W, iters=100)
    line = f"q={q} N={N} R={R}: unimodular sum={val/N:.2f}N; free s1(M_W)^2 for that W = {s1/N:.2f}N = {s1/q:.3f}q"
    if R <= 2500:
        Kd = F.Kvec(); G = gram(Kd, W, q-1); E = G - np.diag(np.diag(G)); trE3 = np.sum(E*(E@E).T).real
        line += f"; S3/CGL = {trE3/(q**2*R**1.5):.3f}"
    print(line, flush=True)
