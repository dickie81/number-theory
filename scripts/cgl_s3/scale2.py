"""Scaling of max s1(M_W)^2 (truncated power method) at |W| = q^{2/3}, N = q^{7/9}, and the structure of the maximiser:
|mean_{chi in W} chi(p)| for small primes p (1 = W aligned on p after a twist, ~|W|^{-1/2} for random W)."""
import sys, math, time
import numpy as np
from sympy import nextprime, primerange
from probe import Field, tpm, fixedW_norm

def align(F, W, ps):
    out = []
    for p in ps:
        ph = np.exp(2j*np.pi*np.asarray(W)*F.ind[p]/(F.q-1))
        out.append(abs(ph.mean()))
    return out

if __name__ == '__main__':
    rng = np.random.default_rng(11)
    for q0 in [int(float(a)) for a in sys.argv[1:]]:
        q = int(nextprime(q0)); t0 = time.time()
        F = Field(q); N = F.N; R = int(round(q**(2/3))); M = q/N
        ps = list(primerange(2, 60))
        print(f"q={q} N={N} R={R} M={M:.2f} [setup {time.time()-t0:.1f}s]", flush=True)
        Wr = rng.choice(q-1, R, replace=False)
        v = fixedW_norm(F, Wr, iters=40)
        print(f"  random W   s1^2/N={v/N:6.3f}  s1^2/q={v/q:7.4f}", flush=True)
        for name, b0 in [('interval', np.ones(len(F.ns), complex)),
                         ('gauss', rng.standard_normal(len(F.ns)) + 1j*rng.standard_normal(len(F.ns)))]:
            t1 = time.time()
            val, W, b, it = tpm(F, b0, R, iters=60)
            al = align(F, W, ps)
            print(f"  {name:9s}  s1^2/N={val/N:6.3f}  s1^2/q={val/q:7.4f}  iters {it} [{time.time()-t1:.0f}s]", flush=True)
            print("     |mean chi(p)| p=" + " ".join(f"{p}:{a:.2f}" for p, a in zip(ps, al)), flush=True)
