import sys, numpy as np
from fractions import Fraction
from sympy import nextprime
from probe import Field
from schatten import Rvec
def ratrec(x, q, B):
    """small a/b with a = b x mod q, |a|,|b| <= B (brute force over b)"""
    best = None
    for b in range(1, B+1):
        a = (b*x) % q
        if a > q//2: a -= q
        if abs(a) <= B and (best is None or max(abs(a), b) < max(abs(best[0]), best[1])):
            best = (a, b)
    return best
for q0 in sys.argv[1:]:
    q = int(nextprime(int(float(q0)))); F = Field(q); Rn = int(round(q**(2/3)))
    bb = np.ones(len(F.ns), complex); best = (0, None)
    for _ in range(120):
        D = F.D(bb); Pw = np.abs(D)**2; Wu = np.argpartition(Pw, -Rn)[-Rn:]
        if Pw[Wu].sum() > best[0]: best = (Pw[Wu].sum(), Wu)
        c = np.zeros_like(D); c[Wu] = D[Wu]; bb = np.exp(1j*np.angle(F.adj(c)))
    W = best[1]
    R = np.abs(Rvec(F, W)); R[0] = 0; R[1] = 0
    top = np.argsort(-R)[:8]
    print(f"q={q} |W|={Rn}  top |R(x)|/|W| at x =", ", ".join(f"{x}~{ratrec(int(x), q, 60)}:{R[x]/Rn:.2f}" for x in top))
    par = np.mean(np.exp(2j*np.pi*np.asarray(W)*F.ind[q-1]/(q-1))).real
    print(f"   mean chi(-1) over W = {par:.3f}")
