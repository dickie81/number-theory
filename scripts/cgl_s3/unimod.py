"""The same search restricted to unimodular coefficients |b_n| = 1 on the support of w (the shape a large-values
polynomial with 1-bounded coefficients and |D| >= N^sigma must have, up to a constant): projected power method
b <- phase(M_W^* M_W b), W <- top R of |D_b|.  Reports sum_{top R}|D_b|^2 / sum_n w_n^2 against q (the large-values
threshold at sigma = 5/7: |D| >= N^{5/7} on R = q^{2/3} characters means sum >= q * sum w^2 when |D| is flat on W),
and min_{chi in W}|D_b(chi)| / N^{5/7}."""
import sys, numpy as np
from sympy import nextprime
from probe import Field

def run(F, b, R, iters=150):
    best = (0, None)
    for it in range(iters):
        D = F.D(b); P = np.abs(D)**2
        W = np.argpartition(P, -R)[-R:]
        val = P[W].sum()/np.sum(F.w**2)
        mn = np.sqrt(P[W].min())
        if val > best[0]:
            best = (val, mn)
        c = np.zeros_like(D); c[W] = D[W]
        g = F.adj(c)
        b = np.exp(1j*np.angle(g))
    return best

if __name__ == '__main__':
    rng = np.random.default_rng(5)
    for q0 in sys.argv[1:]:
        q = int(nextprime(int(float(q0)))); F = Field(q); N = F.N; R = int(round(q**(2/3)))
        V = N**(5/7)
        res = []
        for name, b0 in [('interval', np.ones(len(F.ns), complex)),
                         ('rand-phase', np.exp(2j*np.pi*rng.random(len(F.ns)))),
                         ('rand-phase2', np.exp(2j*np.pi*rng.random(len(F.ns))))]:
            val, mn = run(F, b0, R)
            res.append((name, val, mn))
        print(f"q={q} N={N} R={R} M={q/N:.1f}: " + "; ".join(
            f"{n}: sum/q={v/q:.4f} (={v/N:.2f}N), min|D|/N^(5/7)={m/V:.2f}" for n, v, m in res), flush=True)
