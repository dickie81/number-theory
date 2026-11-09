"""S3 = tr(E^3) exactly, E the off-diagonal Gram matrix (K(chi chi'^-1))_{chi != chi' in W}, K(psi) = sum_n w(n/N)^2 psi(n),
at q prime, T = 1, one point per character (CGL Lemma 4.5 with (5.2): S3 = the m1 m2 m3 != 0 part; the coincident-pair
terms of S3 are O(N/q) times S2 and are dropped).  Compared with CGL's S3 <~ q^2|W|^{3/2} and with the threshold
|W|^3 N^{6 sigma - 3} at sigma = 5/7 (what a large-values set of size |W| forces)."""
import sys, math, itertools
import numpy as np
from sympy import isprime, nextprime, divisors, Poly, symbols, GF
from probe import Field, tpm, wfun

class KField(Field):
    def Kvec(self):
        A = np.zeros(self.q-1, complex); A[self.jn] = self.w**2
        D = np.fft.fft(A)          # D[k] = sum w^2 conj(chi_k(n))
        return D                   # K(chi_k) = D[-k]

def gram(Kd, W, qm1):
    W = np.asarray(W)
    idx = (W[None, :] - W[:, None]) % qm1     # G[i,j] = K(chi_{k_i - k_j}) = D[k_j - k_i]
    return Kd[idx]

def s3_stats(F, Kd, W, label, sig=5/7):
    q, N = F.q, F.N
    G = gram(Kd, W, q-1); K0 = G[0, 0].real
    E = G - np.diag(np.diag(G))
    E2 = E @ E
    trE2 = np.trace(E2).real
    trE3 = np.sum(E * E2.T).real
    lmax = np.linalg.eigvalsh(G)[-1]
    w = len(W)
    cgl = q**2 * w**1.5
    thr = w**3 * N**(6*sig-3)
    print(f"  {label:22s} |W|={w:5d}  S3=tr(E^3)={trE3:11.4e}  /CGL(q^2|W|^1.5)={trE3/cgl:9.2e}  /threshold={trE3/thr:9.2e}"
          f"  S2~3K0 trE2={3*K0*trE2:9.2e}  lam_max(G)/N={lmax/N:6.2f}")
    return trE3

def singer(p):
    """Singer difference set in Z/v, v = (p^4-1)/(p-1): {i : Tr(alpha^i) = 0}, alpha primitive in F_{p^4}."""
    import random
    rnd = random.Random(p)
    pm = p**4 - 1
    fac = list(__import__('sympy').factorint(pm))
    def mulmod(a, b, f):   # polynomials as lists of length 4 (low->high), f monic degree 4 (list of 5)
        r = [0]*7
        for i in range(4):
            if a[i]:
                for j in range(4):
                    r[i+j] = (r[i+j] + a[i]*b[j]) % p
        for k in range(6, 3, -1):
            c = r[k]
            if c:
                for t in range(5):
                    r[k-4+t] = (r[k-4+t] - c*f[t]) % p
        return r[:4]
    def powx(e, f):
        res, base = [1, 0, 0, 0], [0, 1, 0, 0]
        while e:
            if e & 1: res = mulmod(res, base, f)
            base = mulmod(base, base, f); e >>= 1
        return res
    while True:
        f = [rnd.randrange(p) for _ in range(4)] + [1]
        if f[0] == 0: continue
        if powx(pm, f) != [1, 0, 0, 0]: continue
        if all(powx(pm//r, f) != [1, 0, 0, 0] for r in fac):
            break
    # power sums s_k = Tr(x^k) of the roots of f (Newton), k = 0..3
    e = [1, (-f[3]) % p, f[2] % p, (-f[1]) % p, f[0] % p]   # elementary symmetric e1..e4 (signs from monic poly)
    s = [4 % p, 0, 0, 0]
    s[1] = e[1] % p
    s[2] = (e[1]*s[1] - 2*e[2]) % p
    s[3] = (e[1]*s[2] - e[2]*s[1] + 3*e[3]) % p
    v = (p**4 - 1)//(p - 1)
    D, a = [], [1, 0, 0, 0]
    for i in range(v):
        if sum(a[k]*s[k] for k in range(4)) % p == 0:
            D.append(i)
        a = mulmod(a, [0, 1, 0, 0], f)
    return v, D

if __name__ == '__main__':
    rng = np.random.default_rng(3)
    # 1. Singer primes q = p^3+p^2+p+2
    for p in [7, 13, 23, 29, 37, 41, 43, 47]:
        q = p**3 + p**2 + p + 2
        if not isprime(q): continue
        v, D = singer(p)
        assert v == q - 1 and len(D) == p*p + p + 1
        F = KField(q); Kd = F.Kvec()
        print(f"q={q} (Singer, p={p}) N={F.N} M={q/F.N:.2f} |W|={len(D)} q^(2/3)={q**(2/3):.0f}")
        # check flatness of R
        R = np.fft.fft(np.isin(np.arange(q-1), D).astype(float))
        print(f"  |R|^2 off 0: min {np.min(np.abs(R[1:])**2):.3f} max {np.max(np.abs(R[1:])**2):.3f} (p^2 = {p*p})")
        s3_stats(F, Kd, D, 'Singer')
        for t in range(2):
            s3_stats(F, Kd, np.sort(rng.choice(q-1, len(D), replace=False)), f'random #{t}')
        val, Wt, b, it = tpm(F, np.ones(len(F.ns), complex), len(D))
        s3_stats(F, Kd, Wt, 'top (power method)')
        # subgroup of order near |D| if q-1 has such a divisor
        d = min(divisors(q-1), key=lambda d: abs(math.log(d/len(D))))
        H = np.arange(0, q-1, (q-1)//d)
        s3_stats(F, Kd, H, f'subgroup d={d}')
