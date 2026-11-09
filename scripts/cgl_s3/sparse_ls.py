"""The sparse large sieve: max over |W| = R of s1(M_W)^2 at fixed q and N = q^{7/9}, for R from q^{1/3} to q^{5/6},
by the truncated power method from several starts (probe.tpm).  Compared with N + sqrt(qR) (the conjecture),
q^{2/3} R^{1/2} (Chen-Gupta-Li's S3 bound, read as a bound for s1^2) and the large sieve N + q."""
import sys, math, numpy as np
from sympy import nextprime
from probe import Field, tpm

if __name__ == '__main__':
    q = int(nextprime(int(float(sys.argv[1])))); F = Field(q); N = F.N
    exps = [float(e) for e in sys.argv[2:]] or [1/3, 0.4, 0.5, 0.6, 2/3, 0.75, 5/6]
    rng = np.random.default_rng(3)
    print(f"q={q} N={N}  s1^2 / (N + sqrt(qR)) [conjecture], / (q^(2/3) R^(1/2)) [CGL], / q [large sieve]", flush=True)
    for e in exps:
        R = int(round(q**e))
        best = 0
        for b0 in (np.ones(len(F.ns), complex), rng.standard_normal(len(F.ns)) + 1j*rng.standard_normal(len(F.ns))):
            v, W, b, it = tpm(F, b0, R, iters=60)
            best = max(best, v)
        print(f"  R=q^{e:.3f}={R:7d}: s1^2/N={best/N:6.2f}  /(N+sqrt(qR))={best/(N+math.sqrt(q*R)):6.3f}"
              f"  /(q^(2/3)R^(1/2))={best/(q**(2/3)*math.sqrt(R)):6.3f}  /q={best/q:6.3f}", flush=True)
