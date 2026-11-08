"""Condition (C1): max_{x != 1} |R_W(x)| <= |W|^{1/2} q^{1/9 - 2 delta}  (pointwise square-root cancellation of R),
which with Heath-Brown's double-sum theorem bounds the weighted energy (iv).  Reports max_{x!=1}|R|/|W|^{1/2}
and the allowed q^{1/9 - 2/26} (delta = 1/26) and q^{1/9} (delta -> 0)."""
import sys, numpy as np
from sympy import nextprime
from probe import Field, tpm
from schatten import Rvec
rng = np.random.default_rng(13)
for q0 in [float(a) for a in sys.argv[1:]]:
    q = int(nextprime(int(q0))); F = Field(q); N = F.N; Rn = int(round(q**(2/3)))
    Ws = {'random': rng.choice(q-1, Rn, replace=False)}
    val, Wa, b, it = tpm(F, np.ones(len(F.ns), complex), Rn); Ws['adversarial'] = Wa
    bb = np.ones(len(F.ns), complex); best = (0, None)
    for _ in range(120):
        D = F.D(bb); Pw = np.abs(D)**2; Wu = np.argpartition(Pw, -Rn)[-Rn:]
        if Pw[Wu].sum() > best[0]: best = (Pw[Wu].sum(), Wu)
        c = np.zeros_like(D); c[Wu] = D[Wu]; bb = np.exp(1j*np.angle(F.adj(c)))
    Ws['from |b_n|=1'] = best[1]
    line = f"q={q} |W|={Rn}: "
    for name, W in Ws.items():
        R = np.abs(Rvec(F, W)); R[0] = R[1] = 0
        line += f"{name}: {R.max()/np.sqrt(Rn):5.2f}  "
    print(line + f"| allowed delta=1/26: {q**(1/9-2/26):.2f}, delta->0: {q**(1/9):.2f}", flush=True)
