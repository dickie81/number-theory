"""Hybrid bound: split the dilations c by the operator norm of X_c (schatten.py's matrices).
  generic G = {c : ||X_c||_op <= tau}:  sum over x with all three y_i(x) in G of |tr| <= sum_{c in G} ||X_c||_{S3}^3
                                        (<= tau sum_c ||X_c||_{S2}^2, no energy needed);
  structured x (some y_i(x) not in G):  |tr(X_y1 X_y2 X_y3)| <= ||X_ys||_op * prod_{j != s} ||X_yj||_{S2}.
B_hyb(tau) = q^{-2} (generic + structured), minimised over tau; compared with tr(E^3), the pure Hoelder bound
B3 = q^{-2} sum_c ||X_c||_{S3}^3 and CGL's q^2|W|^{3/2}.  y1 = -x, y2 = (1-x)/x, y3 = -1/(1-x)."""
import sys, math, numpy as np
from sympy import nextprime, primerange
from s3direct import KField, gram
from schatten import setup_dual, Rvec
from bohr import unimod_W
from probe import tpm

def norms(F, W, ms, H, chunk=512):
    q = F.q; R = Rvec(F, W); ma = ms % q
    inv = np.array([pow(int(b), q-2, q) for b in ma])
    ratio = (ma[:, None]*inv[None, :]) % q
    sl, ph = np.sqrt(np.abs(H)), H/np.abs(H)*np.sqrt(np.abs(H))
    op = np.zeros(q); s2 = np.zeros(q); s3 = np.zeros(q)
    for i in range(1, q, chunk):
        c = np.arange(i, min(i+chunk, q))
        X = R[(c[:, None, None]*ratio[None, :, :]) % q]*sl[None, :, None]*ph[None, None, :]
        ev = np.clip(np.linalg.eigvalsh(np.conj(np.transpose(X, (0, 2, 1))) @ X), 0, None)
        op[c] = np.sqrt(ev[:, -1]); s2[c] = np.sqrt(ev.sum(1)); s3[c] = (ev**1.5).sum(1)
    return op, s2, s3

def hybrid(q, op, s2, s3, taus):
    x = np.arange(2, q)
    y1 = (-x) % q
    y2 = ((1 - x) % q)*np.array([pow(int(v), q-2, q) for v in x]) % q
    y3 = (-np.array([pow(int(v), q-2, q) for v in (1 - x) % q])) % q
    best = None
    for tau in taus:
        g = op <= tau
        gen = g[y1] & g[y2] & g[y3]
        A = s3[g].sum()
        cand = []
        for ys, o1, o2 in ((y1, y2, y3), (y2, y1, y3), (y3, y1, y2)):
            v = np.where(~g[ys], op[ys]*s2[o1]*s2[o2], np.inf)
            cand.append(v)
        B = np.min(np.vstack(cand), axis=0)[~gen].sum()
        val = (A + B)/q**2
        if best is None or val < best[0]:
            best = (val, tau, (~g[1:]).mean(), A/q**2, B/q**2)
    return best

if __name__ == '__main__':
    rng = np.random.default_rng(6)
    for q0 in [float(a) for a in sys.argv[1:]]:
        q = int(nextprime(int(q0))); F = KField(q); N = F.N; R_ = int(round(q**(2/3))); M = q/N
        ms, H = setup_dual(F); Kd = F.Kvec(); cgl = q**2*R_**1.5
        Ws = {'random': np.sort(rng.choice(q-1, R_, replace=False))}
        Ws['from |b_n|=1'] = unimod_W(F, R_)
        val, Wa, b, it = tpm(F, np.ones(len(F.ns), complex), R_); Ws['adversarial'] = Wa
        kk = np.arange(q-1)
        for k in (3, 6):
            dev = np.zeros(q-1)
            for p in list(primerange(2, 100))[:k]:
                t = (kk*F.ind[p]) % (q-1); dev = np.maximum(dev, np.minimum(t, q-1-t)/(q-1))
            Ws[f'Bohr k={k}'] = np.nonzero(dev <= np.sort(dev)[R_-1])[0]
        print(f"q={q} N={N} |W|={R_} M={M:.2f}", flush=True)
        for name, W in Ws.items():
            G = gram(Kd, W, q-1); E = G - np.diag(np.diag(G)); S3 = np.sum(E*(E@E).T).real
            op, s2, s3 = norms(F, W, ms, H)
            taus = np.quantile(op[1:], [0.5, 0.8, 0.9, 0.95, 0.98, 0.99, 0.995, 0.999, 1.0])
            hb, tau, frac, A, B = hybrid(q, op, s2, s3, taus)
            print(f"  {name:13s} S3/CGL={S3/cgl:7.4f}  B3/CGL={s3[1:].sum()/q**2/cgl:6.3f}  hybrid/CGL={hb/cgl:6.3f}"
                  f" (structured share of c {frac:.3%}; generic {A/cgl:.3f} + structured {B/cgl:.3f})", flush=True)
