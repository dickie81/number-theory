"""Top-R large sieve constant at Chen-Gupta-Li's critical point (q prime, T = 1, sigma = 5/7):
    Lam_R(q, N) = max_{|W| = R} s1(M_W)^2,  M_W = (w(n/N) chi(n))_{chi in W, n},
with N = q^{7/9}, R = q^{2/3}.  CGL's S3 bound S3 <~ q^2|W|^{3/2} is (via their Lemmas 4.1-4.2) the statement
s1(M_W)^2 <~ q^{2/3}|W|^{1/2}, which at R = q^{2/3} is q; random W give about N + R + 2(NR)^{1/2}.
Maximised by the truncated power method: b -> D_b(chi) for all chi (one FFT on discrete logs), W = top R of |D_b|,
b <- M_W^* M_W b (one inverse FFT).  Monotone in the objective sum_{top R}|D_b|^2/|b|^2."""
import math, sys, time
import numpy as np
from sympy import primitive_root, nextprime, factorint
from sympy import mobius

def wfun(x):
    """smooth bump: 0 outside [1,2], 1 on [1.2,1.8], C-infinity transitions"""
    x = np.asarray(x, float)
    def s(t):
        t = np.clip(t, 0, 1)
        f = lambda u: np.where(u > 0, np.exp(-1/np.maximum(u, 1e-300)), 0.0)
        return f(t)/(f(t)+f(1-t))
    return s((x-1)/0.2)*s((2-x)/0.2)

class Field:
    def __init__(self, q, N=None):
        self.q = q
        g = primitive_root(q)
        B = 4096
        pw = np.empty(q-1, dtype=np.int64)
        a = 1
        for j in range(min(B, q-1)):
            pw[j] = a; a = a*g % q
        gB = pow(g, B, q); step = 1
        for i in range(1, (q-1+B-1)//B):
            step = step*gB % q
            lo, hi = i*B, min((i+1)*B, q-1)
            pw[lo:hi] = pw[:hi-lo]*step % q
        self.pw = pw
        ind = np.empty(q, dtype=np.int64); ind[pw] = np.arange(q-1)
        self.ind = ind
        self.N = N or int(round(q**(7/9)))
        self.ns = np.arange(self.N, 2*self.N+1)
        self.w = wfun(self.ns/self.N)
        keep = self.w > 0
        self.ns, self.w = self.ns[keep], self.w[keep]
        assert self.ns[-1] < q
        self.jn = ind[self.ns]
    def D(self, b):
        A = np.zeros(self.q-1, complex); A[self.jn] = self.w*b
        return np.fft.fft(A)
    def adj(self, c):
        F = np.fft.ifft(c)*(self.q-1)
        return self.w*F[self.jn]

def tpm(F, b, R, iters=60, tol=1e-9):
    b = b/np.linalg.norm(b); hist = []
    for it in range(iters):
        D = F.D(b); P = np.abs(D)**2
        W = np.argpartition(P, -R)[-R:]
        val = P[W].sum()
        hist.append(val)
        if it > 3 and hist[-1] - hist[-2] < tol*hist[-1]:
            break
        c = np.zeros_like(D); c[W] = D[W]
        b = F.adj(c); b /= np.linalg.norm(b)
    return val, np.sort(W), b, len(hist)

def fixedW_norm(F, W, iters=80, seed=0):
    rng = np.random.default_rng(seed)
    b = rng.standard_normal(len(F.ns)) + 1j*rng.standard_normal(len(F.ns)); b /= np.linalg.norm(b)
    for _ in range(iters):
        D = F.D(b); c = np.zeros_like(D); c[W] = D[W]
        b = F.adj(c); nb = np.linalg.norm(b); b /= nb
    D = F.D(b)
    return (np.abs(D[W])**2).sum()

def starts(F, rng):
    ns = F.ns; q = F.q
    yield 'interval', np.ones(len(ns), complex)
    yield 'gauss', rng.standard_normal(len(ns)) + 1j*rng.standard_normal(len(ns))
    lam = np.array([(-1)**sum(factorint(int(n)).values()) for n in ns], float)
    yield 'liouville', lam.astype(complex)
    mu = np.array([mobius(int(n)) for n in ns], float)
    yield 'mobius', mu.astype(complex)
    pr = np.array([1.0 if len(factorint(int(n))) == 1 and list(factorint(int(n)).values())[0] == 1 else 0.0 for n in ns])
    yield 'primes', pr.astype(complex)
    y = int(F.N**(1/3))
    sm = np.array([1.0 if max(factorint(int(n))) <= y else 0.0 for n in ns])
    if sm.sum() > 0:
        yield f'smooth(y={y})', sm.astype(complex)
    r = int(rng.integers(1, q))
    yield 'additive', np.exp(2j*np.pi*r*ns/q)

if __name__ == '__main__':
    qs = [int(a) for a in sys.argv[1:]] or [10007]
    rng = np.random.default_rng(1)
    for q0 in qs:
        q = int(nextprime(q0))
        t0 = time.time()
        F = Field(q)
        N, R = F.N, int(round(q**(2/3)))
        cgl = q**(2/3)*R**0.5
        print(f"q={q}  N={N}  R={R}  M=q/N={q/N:.2f}  [setup {time.time()-t0:.1f}s]")
        Wr = rng.choice(q-1, R, replace=False)
        v = fixedW_norm(F, Wr)
        print(f"  random W:          s1^2={v:12.1f}  /N={v/N:6.3f}  /q={v/q:7.4f}  /(q^(2/3)R^(1/2))={v/cgl:7.4f}"
              f"   [N+R+2sqrt(NR) = {(math.sqrt(N)+math.sqrt(R))**2/N:.3f} N]")
        for name, b0 in starts(F, rng):
            t1 = time.time()
            val, W, b, it = tpm(F, b0, R)
            print(f"  {name:16s} s1^2={val:12.1f}  /N={val/N:6.3f}  /q={val/q:7.4f}  /(q^(2/3)R^(1/2))={val/cgl:7.4f}"
                  f"   iters {it} [{time.time()-t1:.1f}s]", flush=True)
