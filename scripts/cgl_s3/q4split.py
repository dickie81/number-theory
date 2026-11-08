"""Split Q4 = (q-1)^{-1} sum_c ||X_c||_{S4}^4 into its diagonal part (degenerate additive quadruples) and the
non-degenerate part (iv) = sum_{chi1 chi3 = chi2 chi4, nondeg} |P(psi)|^2 |P(psi')|^2, P(psi) = sum_m |H(m)| psi(m).
Bias ratios (1 = typical weights):
  rho_diag = sum_{chi != chi'} |P(chi'/chi)|^2 / (|W|(|W|-1) avg_{psi != 1}|P(psi)|^2)
  rho_iv   = (iv) / (E_nondeg(W) * (avg|P|^2)^2)
and the two parts of the bound B24 against CGL's q^2|W|^{3/2}."""
import sys, math, numpy as np
from sympy import nextprime
from probe import Field, tpm
from s3direct import KField, gram
from schatten import setup_dual, schatten

def autocorr(W, n):
    A = np.zeros(n); A[np.asarray(W)] = 1
    f = np.fft.fft(A)
    return np.rint(np.fft.ifft(np.abs(f)**2).real).astype(np.int64)   # r[d] = #{(k,k') in W^2: k - k' = d}

def Pvec(F, ms, H):
    """P(chi_k) for all k: sum_m |H(m)| chi_k(m), chi_k(g^j) = e(jk/(q-1))."""
    q = F.q; A = np.zeros(q-1, complex)
    for m, h in zip(ms, H):
        A[F.ind[m % q]] += abs(h)
    return np.fft.ifft(A)*(q-1)        # sum_j A[j] e(+jk/(q-1))

if __name__ == '__main__':
    rng = np.random.default_rng(4)
    for q0 in [float(a) for a in sys.argv[1:]]:
        q = int(nextprime(int(q0))); F = KField(q); N = F.N; Rn = int(round(q**(2/3))); M = q/N
        ms, H = setup_dual(F)
        P = Pvec(F, ms, H); SH = np.sum(np.abs(H))
        P2 = np.abs(P)**2; avgP2 = (P2.sum() - P2[0])/(q-2)
        Kd = F.Kvec(); cgl = q**2*Rn**1.5
        Ws = {'random': np.sort(rng.choice(q-1, Rn, replace=False))}
        val, Wa, b, it = tpm(F, np.ones(len(F.ns), complex), Rn); Ws['adversarial'] = Wa
        bb = np.ones(len(F.ns), complex); best = (0, None)
        for _ in range(120):
            D = F.D(bb); Pw = np.abs(D)**2; Wu = np.argpartition(Pw, -Rn)[-Rn:]
            if Pw[Wu].sum() > best[0]: best = (Pw[Wu].sum(), np.sort(Wu))
            c = np.zeros_like(D); c[Wu] = D[Wu]; bb = np.exp(1j*np.angle(F.adj(c)))
        Ws['from |b_n|=1'] = best[1]
        dvs = [d for d in range(2, 4000) if (q-1) % d == 0]
        d = min(dvs, key=lambda d: abs(math.log(d/Rn)))
        Ws[f'subgroup({d})'] = np.arange(0, q-1, (q-1)//d)
        print(f"q={q} N={N} |W|={Rn} M={M:.2f}", flush=True)
        for name, W in Ws.items():
            w = len(W)
            r = autocorr(W, q-1)
            E = int(np.sum(r.astype(float)**2)); Enon = E - 2*w*w + w
            offdiag = float(np.sum(r[1:]*P2[1:]))      # sum_{chi != chi'} |P(chi'/chi)|^2  (P2 symmetric in k -> -k)
            S2n, S4n, _ = schatten(F, W, ms, H, want_s3=False)
            Q4 = S4n/(q-1)
            Qdiag = w*SH**4 + 2*SH**2*offdiag
            iv = Q4 - Qdiag
            rho_d = offdiag/(w*(w-1)*avgP2)
            rho_iv = iv/(Enon*avgP2**2) if Enon > 0 else float('nan')
            pref = SH*math.sqrt(w)/q            # B24 = q^-1 (sum|H|) |W|^{1/2} Q4^{1/2}
            Bd, Bi = pref*math.sqrt(max(Qdiag, 0)), pref*math.sqrt(max(iv, 0))
            G = gram(Kd, W, q-1); Em = G - np.diag(np.diag(G)); S3 = np.sum(Em*(Em@Em).T).real
            print(f"  {name:14s} E/|W|^2.5={E/w**2.5:6.3f} rho_diag={rho_d:6.3f} rho_iv={rho_iv:7.3f} | "
                  f"B24 diag/CGL={Bd/cgl:6.3f} (iv)/CGL={Bi/cgl:6.3f} | S3/CGL={S3/cgl:6.3f}", flush=True)
