"""Where the cancellation in S3 lives.  With y1 = -x, y2 = (1-x)/x, y3 = -1/(1-x) and T(x) = tr(X_y1 X_y2 X_y3):
  E3 = q^-2 |sum_x T(x)|            (~ S3: with all cancellation)
  A1 = q^-2 sum_x |T(x)|            (no cancellation across x)
  VN = q^-2 sum_x sum_i s_i(X_y1) s_i(X_y2) s_i(X_y3)   (von Neumann: the best bound from singular values alone, per x)
  B3 = q^-2 sum_c ||X_c||_{S3}^3    (Schatten-Hoelder across x)
all over CGL's q^2|W|^{3/2}.  A1 >> E3: cancellation across x (the Jacobi-sum phases).  VN >> A1: cancellation inside each
trace (misaligned singular vectors), invisible to any bound that uses norms only."""
import sys, numpy as np
from sympy import nextprime, primerange
from s3direct import KField, gram
from schatten import setup_dual, Rvec
from bohr import unimod_W
from probe import tpm

def build(F, W, ms, H):
    q = F.q; R = Rvec(F, W); ma = ms % q
    inv = np.array([pow(int(b), q-2, q) for b in ma])
    ratio = (ma[:, None]*inv[None, :]) % q
    sl, ph = np.sqrt(np.abs(H)), H/np.abs(H)*np.sqrt(np.abs(H))
    return lambda c: R[(c[:, None, None]*ratio[None, :, :]) % q]*sl[None, :, None]*ph[None, None, :]

def analyse(F, W, ms, H, chunk=256):
    q = F.q; X = build(F, W, ms, H)
    sv = np.zeros((q, len(ms)))
    for i in range(1, q, chunk):
        c = np.arange(i, min(i+chunk, q))
        sv[c] = np.linalg.svd(X(c), compute_uv=False)
    xs = np.arange(2, q)
    invx = np.array([pow(int(v), q-2, q) for v in xs]); inv1x = np.array([pow(int(v), q-2, q) for v in (1 - xs) % q])
    y1, y2, y3 = (-xs) % q, ((1 - xs) % q)*invx % q, (-inv1x) % q
    tot = 0j; a1 = 0.0
    for i in range(0, len(xs), chunk):
        s = slice(i, i+chunk)
        T = np.einsum('nij,njk,nki->n', X(y1[s]), X(y2[s]), X(y3[s]))
        tot += T.sum(); a1 += np.abs(T).sum()
    vn = np.sum(sv[y1]*sv[y2]*sv[y3])
    b3 = np.sum(sv[1:]**3)
    return abs(tot)/q**2, a1/q**2, vn/q**2, b3/q**2

if __name__ == '__main__':
    rng = np.random.default_rng(6)
    for q0 in [float(a) for a in sys.argv[1:]]:
        q = int(nextprime(int(q0))); F = KField(q); N = F.N; R_ = int(round(q**(2/3)))
        ms, H = setup_dual(F); Kd = F.Kvec(); cgl = q**2*R_**1.5
        Ws = {'random': np.sort(rng.choice(q-1, R_, replace=False)), 'from |b_n|=1': unimod_W(F, R_)}
        val, Wa, b, it = tpm(F, np.ones(len(F.ns), complex), R_); Ws['adversarial'] = Wa
        kk = np.arange(q-1)
        for k in (3, 6):
            dev = np.zeros(q-1)
            for p in list(primerange(2, 100))[:k]:
                t = (kk*F.ind[p]) % (q-1); dev = np.maximum(dev, np.minimum(t, q-1-t)/(q-1))
            Ws[f'Bohr k={k}'] = np.nonzero(dev <= np.sort(dev)[R_-1])[0]
        print(f"q={q} N={N} |W|={R_} M={q/N:.2f}   (all over CGL's q^2|W|^1.5)", flush=True)
        for name, W in Ws.items():
            G = gram(Kd, W, q-1); E = G - np.diag(np.diag(G)); S3 = np.sum(E*(E@E).T).real
            e3, a1, vn, b3 = analyse(F, W, ms, H)
            print(f"  {name:13s} S3={S3/cgl:7.4f}  E3={e3/cgl:7.4f}  A1={a1/cgl:7.4f}  VN={vn/cgl:7.4f}  B3={b3/cgl:7.4f}",
                  flush=True)
