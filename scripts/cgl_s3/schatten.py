"""Schatten-Hoelder route for S3 at q prime, T = 1.
Exact dual form: K(psi) = (psi(-1) tau(psi)/q) sum_m conj(psi)(m) H(m),  H(m) = sum_n h(n/N) e(mn/q), h = w^2.
Truncating to 0 < |m| <= L and summing the Jacobi sums over x:
  Full_L = q^{-2} sum_{x != 0,1} tr( X_{-x} X_{(1-x)/x} X_{-1/(1-x)} ),   X_c[a,b] = |H(a)|^{1/2} R(c a/b) H(b)|H(b)|^{-1/2},
  R(y) = sum_{chi in W} chi(y);   tr(E^3) = Full_L - (non-distinct triples) ~ Full_L.
Hoelder: |Full_L| <= B3 = q^{-2} sum_c ||X_c||_{S3}^3 <= B24 = q^{-2} (sum_c ||X_c||_{S2}^2)^{1/2} (sum_c ||X_c||_{S4}^4)^{1/2},
sum_c ||X_c||_{S2}^2 = (sum|H|)^2 (q-1)|W| exactly, sum_c ||X_c||_{S4}^4 = (q-1) Q4 (4-cycles over additive quadruples of W)."""
import sys, math, numpy as np
from sympy import nextprime
from probe import Field, tpm, wfun
from s3direct import KField, gram

def setup_dual(F, Lfac=4.0):
    q, N = F.q, F.N
    M = q/N; L = int(math.ceil(Lfac*M))
    ms = np.array([m for m in range(-L, L+1) if m != 0])
    H = np.array([np.sum(F.w**2*np.exp(2j*np.pi*m*F.ns/q)) for m in ms])
    return ms, H

def Rvec(F, W):
    """R(y) for all y in F_q^x, as an array indexed by y (0 unused)."""
    A = np.zeros(F.q-1, complex); A[np.asarray(W)] = 1.0
    Rl = np.fft.ifft(A)*(F.q-1)            # Rl[j] = sum_k 1_W(k) e(jk/(q-1)) = R(g^j)
    R = np.zeros(F.q, complex); R[F.pw] = Rl
    return R

def schatten(F, W, ms, H, chunk=512, want_s3=True):
    q = F.q
    R = Rvec(F, W)
    ma = ms % q
    inv = np.array([pow(int(b), q-2, q) for b in ma])
    ratio = (ma[:, None]*inv[None, :]) % q            # a/b mod q
    sl, ph = np.sqrt(np.abs(H)), H/np.maximum(np.abs(H), 1e-300)*np.sqrt(np.abs(H))
    S2 = S4 = S3 = 0.0
    cs = np.arange(1, q)
    for i in range(0, len(cs), chunk):
        c = cs[i:i+chunk]
        X = R[(c[:, None, None]*ratio[None, :, :]) % q]*sl[None, :, None]*ph[None, None, :]
        S2 += np.sum(np.abs(X)**2)
        G = np.conj(np.transpose(X, (0, 2, 1))) @ X
        S4 += np.sum(np.abs(G)**2)
        if want_s3:
            ev = np.linalg.eigvalsh(G)
            S3 += np.sum(np.clip(ev, 0, None)**1.5)
    return S2, S4, S3

def full_L(F, W, ms, H):
    """q^-2 sum_x tr(...) directly (validation)."""
    q = F.q; R = Rvec(F, W); ma = ms % q
    inv = {int(b): pow(int(b), q-2, q) for b in ma}
    tot = 0.0
    xs = np.arange(2, q)
    ib = np.array([inv[int(b)] for b in ma])
    rat = (ma[:, None]*ib[None, :]) % q
    for x in xs:
        c1 = (-x) % q; c2 = ((1-x) % q)*pow(int(x), q-2, q) % q; c3 = (-pow(int((1-x) % q), q-2, q)) % q
        A = R[(c1*rat) % q]*H[None, :]; B = R[(c2*rat) % q]*H[None, :]; C = R[(c3*rat) % q]*H[None, :]
        tot += np.trace(A @ B @ C)
    return tot/q**2

if __name__ == '__main__':
    rng = np.random.default_rng(2)
    for q0 in [float(a) for a in sys.argv[1:]]:
        q = int(nextprime(int(q0))); F = KField(q); N = F.N; R_ = int(round(q**(2/3))); M = q/N
        ms, H = setup_dual(F)
        Kd = F.Kvec()
        cgl = q**2*R_**1.5
        Ws = {'random': np.sort(rng.choice(q-1, R_, replace=False))}
        val, Wa, b, it = tpm(F, np.ones(len(F.ns), complex), R_); Ws['adversarial'] = Wa
        # unimodular-derived W
        bb = np.ones(len(F.ns), complex); best = (0, None)
        for _ in range(120):
            D = F.D(bb); P = np.abs(D)**2; Wu = np.argpartition(P, -R_)[-R_:]
            v = P[Wu].sum()
            if v > best[0]: best = (v, np.sort(Wu))
            c = np.zeros_like(D); c[Wu] = D[Wu]; bb = np.exp(1j*np.angle(F.adj(c)))
        Ws['from |b_n|=1'] = best[1]
        print(f"q={q} N={N} |W|={R_} M={M:.2f} L={len(ms)//2}  (CGL bound q^2|W|^1.5 = {cgl:.3e})")
        for name, W in Ws.items():
            G = gram(Kd, W, q-1); E = G - np.diag(np.diag(G)); S3 = np.sum(E*(E@E).T).real
            S2n, S4n, S3n = schatten(F, W, ms, H, want_s3=(q < 40000))
            B24 = math.sqrt(S2n*S4n)/q**2
            B3 = S3n/q**2
            line = f"  {name:14s} S3/CGL={S3/cgl:8.4f}  B3/CGL={B3/cgl:8.4f}  B24/CGL={B24/cgl:8.4f}"
            if q < 6000:
                fl = full_L(F, W, ms, H); line += f"  [Full_L/S3={fl.real/S3:.3f}]"
            print(line, flush=True)
