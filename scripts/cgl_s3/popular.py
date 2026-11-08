"""The sufficient condition: popular differences of W are not pretentious.
  (iv) <= E' := sum_{psi != 1} r_W(psi)^2 |P(psi)|^4    (Cauchy-Schwarz),
  and E' is typical iff the weights |P(psi)|^4 are not correlated with r_W(psi)^2.
Reports: max_{psi!=1} r_W(psi) / (|W|^2/q);  bias(E') = E' / (sum_{psi!=1} r^2 * mean_{psi!=1}|P|^4);
         actual (iv) / E';  allowed bias for delta = 1/26 at this |W|, N: q^{1/9 - 2/26} * q^{5/3} / E."""
import sys, math, numpy as np
from sympy import nextprime
from probe import tpm
from s3direct import KField
from schatten import setup_dual, schatten
from q4split import autocorr, Pvec

rng = np.random.default_rng(9)
for q0 in [float(a) for a in sys.argv[1:]]:
    q = int(nextprime(int(q0))); F = KField(q); N = F.N; Rn = int(round(q**(2/3))); M = q/N
    ms, H = setup_dual(F); P = Pvec(F, ms, H); SH = np.sum(np.abs(H))
    P2 = np.abs(P)**2; P4 = P2**2
    m4 = (P4.sum() - P4[0])/(q-2); avgP2 = (P2.sum()-P2[0])/(q-2)
    Ws = {'random': np.sort(rng.choice(q-1, Rn, replace=False))}
    val, Wa, b, it = tpm(F, np.ones(len(F.ns), complex), Rn); Ws['adversarial'] = Wa
    bb = np.ones(len(F.ns), complex); best = (0, None)
    for _ in range(120):
        D = F.D(bb); Pw = np.abs(D)**2; Wu = np.argpartition(Pw, -Rn)[-Rn:]
        if Pw[Wu].sum() > best[0]: best = (Pw[Wu].sum(), np.sort(Wu))
        c = np.zeros_like(D); c[Wu] = D[Wu]; bb = np.exp(1j*np.angle(F.adj(c)))
    Ws['from |b_n|=1'] = best[1]
    print(f"q={q} N={N} |W|={Rn} M={M:.2f}", flush=True)
    for name, W in Ws.items():
        w = len(W); r = autocorr(W, q-1).astype(float)
        E = float(np.sum(r**2)); Enon = E - 2*w*w + w
        Ep = float(np.sum(r[1:]**2*P4[1:]))
        bias = Ep/(np.sum(r[1:]**2)*m4)
        S2n, S4n, _ = schatten(F, W, ms, H, want_s3=False)
        offdiag = float(np.sum(r[1:]*P2[1:]))
        iv = S4n/(q-1) - (w*SH**4 + 2*SH**2*offdiag)
        allowed = q**(1/9 - 2/26)*q**(5/3)/E
        print(f"  {name:14s} max r/(|W|^2/q)={r[1:].max()/(w*w/q):6.2f}  bias(E')={bias:6.3f}  (iv)/E'={iv/Ep:6.3f}"
              f"  rho_iv={iv/(Enon*avgP2**2):6.3f}  allowed rho for delta=1/26: {allowed:6.3f}", flush=True)
