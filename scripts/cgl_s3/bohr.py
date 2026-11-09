"""The Bohr-set test.  (iv)(S) = sum over the non-degenerate additive quadruples of S of |P(psi)|^2 |P(psi')|^2 is
computed directly (one FFT of length q - 1 per element of S), and its bias rho = (iv)/(E_nondeg(S) avg|P|^2^2).

A. Proxies: W = the top q^{2/3} characters of the best |b_n| = 1 polynomial.  Its most biased small rationals x_i
   (largest |R(x_i)|, |a|,|b| <= 12) define phases arg chi(x_i) - arg R(x_i); cells = sign of their cosines.
   For W and each cell: size, alignment |R(x_i)|/|S|, rho, S3/(q^2|S|^{3/2}), and the share of W's (iv) and of its
   energy that lies inside single cells.
B. Synthetic Bohr sets W = {chi : |arg chi(p_i)| <= eta, i <= k} at the first k primes, eta set so |W| ~ q^{2/3}:
   rho, E/|W|^{5/2} (CGL's energy bound at the critical point is E <~ |W|^{5/2}), S3/(q^2|W|^{3/2})."""
import sys, math, numpy as np
from sympy import nextprime, primerange
from s3direct import KField, gram
from schatten import setup_dual, Rvec
from q4split import autocorr, Pvec

def weighted(S, P2, q):
    """((iv)(S), E(S), E_nondeg(S)) by FFT: for each chi2 in S, sum_{chi1,chi3 in S} 1_S(chi1+chi3-chi2) u(chi1) u(chi3)
    with u(k) = |P(chi2 - k)|^2 1_S(k), minus the degenerate quadruples."""
    n = q - 1; S = np.asarray(S); w = len(S)
    ind = np.zeros(n); ind[S] = 1.0
    P0 = P2[0]; tot = 0.0
    for c2 in S:
        u = np.zeros(n); u[S] = P2[(c2 - S) % n]
        conv = np.fft.irfft(np.fft.rfft(u)**2, n)          # (u*u)[s]
        full = conv[(S + c2) % n].sum()
        tot += full - 2*P0*u.sum() + P0**2
    r = autocorr(S, n).astype(float)
    E = float(np.sum(r**2))
    return tot, E, E - 2*w*w + w

def s3ratio(Kd, S, q):
    G = gram(Kd, np.asarray(S), q-1); E = G - np.diag(np.diag(G))
    return np.sum(E*(E@E).T).real/(q**2*len(S)**1.5)

def unimod_W(F, R_):
    bb = np.ones(len(F.ns), complex); best = (0, None)
    for _ in range(120):
        D = F.D(bb); Pw = np.abs(D)**2; Wu = np.argpartition(Pw, -R_)[-R_:]
        if Pw[Wu].sum() > best[0]: best = (Pw[Wu].sum(), np.sort(Wu))
        c = np.zeros_like(D); c[Wu] = D[Wu]; bb = np.exp(1j*np.angle(F.adj(c)))
    return best[1]

def small_rats(q, B):
    out = {}
    for a in range(-B, B+1):
        for b in range(1, B+1):
            if a == 0 or math.gcd(abs(a), b) != 1 or (a == 1 and b == 1): continue
            out[(a, b)] = (a % q)*pow(b, q-2, q) % q
    return out

def partA(q0, k=2):
    q = int(nextprime(int(q0))); F = KField(q); R_ = int(round(q**(2/3)))
    ms, H = setup_dual(F); P = Pvec(F, ms, H); P2 = np.abs(P)**2
    avg2 = (P2.sum() - P2[0])/(q-2); Kd = F.Kvec()
    W = unimod_W(F, R_)
    R = Rvec(F, W); rats = small_rats(q, 12)
    top = sorted(rats, key=lambda r: -abs(R[rats[r]]))
    chosen = []
    for r in top:                                  # skip x if 1/x already chosen (same Bohr direction)
        if (r[1]*np.sign(r[0]), abs(r[0])) not in chosen:
            chosen.append(r)
        if len(chosen) == k: break
    ph = []
    for (a, b) in chosen:
        x = rats[(a, b)]
        th = 2*np.pi*np.asarray(W)*F.ind[x]/(q-1) - np.angle(R[x])
        ph.append(np.cos(th) > 0)
    print(f"A. q={q} |W|={R_} M={q/F.N:.2f}; Bohr directions: " +
          ", ".join(f"{a}/{b} (|R|/|W|={abs(R[rats[(a,b)]])/R_:.2f})" for a, b in chosen), flush=True)
    iv, E, En = weighted(W, P2, q)
    print(f"   W        |S|={R_:5d}  rho={iv/(En*avg2**2):6.3f}  E/(2|S|^2+|S|^4/q)={E/(2*R_**2+R_**4/q):5.2f}"
          f"  S3/CGL={s3ratio(Kd, W, q):6.3f}", flush=True)
    iv_in = E_in = 0.0
    codes = sum((p.astype(int) << i) for i, p in enumerate(ph))
    for c in range(2**k):
        S = np.asarray(W)[codes == c]
        if len(S) < 20: continue
        ivc, Ec, Enc = weighted(S, P2, q); iv_in += ivc; E_in += Ec
        RS = Rvec(F, S)
        al = " ".join(f"{abs(RS[rats[r]])/len(S):.2f}" for r in chosen)
        sgn = "".join("+" if (c >> i) & 1 else "-" for i in range(k))
        print(f"   cell {sgn}  |S|={len(S):5d}  rho={ivc/(Enc*avg2**2):6.3f}  "
              f"E/(2|S|^2+|S|^4/q)={Ec/(2*len(S)**2+len(S)**4/q):5.2f}  S3/CGL={s3ratio(Kd, S, q):6.3f}  align [{al}]",
              flush=True)
    print(f"   inside single cells: {iv_in/iv:.1%} of (iv), {E_in/E:.1%} of E", flush=True)

def partB(q0, ks=(1, 2, 3, 4, 5, 6)):
    q = int(nextprime(int(q0))); F = KField(q); R_ = int(round(q**(2/3)))
    ms, H = setup_dual(F); P = Pvec(F, ms, H); P2 = np.abs(P)**2
    avg2 = (P2.sum() - P2[0])/(q-2); Kd = F.Kvec()
    ps = list(primerange(2, 100))
    print(f"B. q={q} |W|~{R_} M={q/F.N:.2f}", flush=True)
    rng = np.random.default_rng(1)
    Wr = np.sort(rng.choice(q-1, R_, replace=False))
    iv, E, En = weighted(Wr, P2, q)
    print(f"   random      rho={iv/(En*avg2**2):6.3f}  E/|W|^2.5={E/R_**2.5:6.2f}  S3/CGL={s3ratio(Kd, Wr, q):6.3f}", flush=True)
    kk = np.arange(q-1)
    for k in ks:
        dev = np.zeros(q-1)
        for p in ps[:k]:
            t = (kk*F.ind[p]) % (q-1)
            ang = np.minimum(t, q-1-t)/(q-1)                      # |arg chi(p)|/(2 pi)
            dev = np.maximum(dev, ang)
        eta = np.sort(dev)[R_-1]
        W = np.nonzero(dev <= eta)[0]
        iv, E, En = weighted(W, P2, q)
        print(f"   k={k} eta={360*eta:5.1f}deg |W|={len(W):5d}  rho={iv/(En*avg2**2):6.3f}  E/|W|^2.5={E/len(W)**2.5:6.2f}"
              f"  S3/CGL={s3ratio(Kd, W, q):6.3f}", flush=True)

if __name__ == '__main__':
    part = sys.argv[1]
    for q0 in sys.argv[2:]:
        (partA if part == 'A' else partB)(float(q0))
