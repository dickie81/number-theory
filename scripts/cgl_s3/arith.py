"""Do arithmetic coefficients give unbiased sets?  For several b on [N, 2N], W = the top q^{2/3} characters by |D_b|
(and, separately, after the |b_n| = 1 refinement started from b).  Reports: the level of the values
(min_W |D| / N^{5/7}, max |D| / sqrt(q)), the bias of R on small rationals (max over x = a/b, |a|,|b| <= 12, of
|R(x)|/|W|), the weighted-energy bias rho (bohr.weighted), and S3/CGL.  Random W: bias ~ |W|^{-1/2}, rho ~ 1."""
import sys, math, numpy as np
from sympy import nextprime
from s3direct import KField, gram
from schatten import setup_dual, Rvec
from q4split import Pvec
from bohr import weighted, s3ratio, small_rats

def sa(lo, hi):
    """Liouville lambda(n), mu(n), primality and largest prime factor for lo <= n <= hi (numpy sieve)."""
    big = np.ones(hi+1, np.int64); omega = np.zeros(hi+1, np.int64); sqfree = np.ones(hi+1, bool)
    isp = np.ones(hi+1, bool); isp[:2] = False
    for p in range(2, int(hi**0.5)+1):
        if isp[p]:
            isp[p*p::p] = False
    for p in np.nonzero(isp)[0]:
        big[p::p] = p
        pk = p
        while pk <= hi:
            omega[pk::pk] += 1
            pk *= p
        if p*p <= hi:
            sqfree[p*p::p*p] = False
    sl = slice(lo, hi+1)
    lam = (-1.0)**omega[sl]
    return lam, np.where(sqfree[sl], lam, 0.0), isp[sl].astype(float), big[sl]


def refine(F, b, R_, iters=100):
    best = (0, None, None)
    for _ in range(iters):
        D = F.D(b); Pw = np.abs(D)**2; W = np.argpartition(Pw, -R_)[-R_:]
        if Pw[W].sum() > best[0]: best = (Pw[W].sum(), np.sort(W), b)
        c = np.zeros_like(D); c[W] = D[W]; b = np.exp(1j*np.angle(F.adj(c)))
    return best[1], best[2]

def report(F, name, b, W, P2, avg2, Kd, rats, q, R_):
    D = np.abs(F.D(b)); V = F.N**(5/7)*np.sqrt(np.mean(np.abs(b)**2))
    R = Rvec(F, W); bias = max(abs(R[x]) for x in rats.values())/len(W)
    iv, E, En = weighted(W, P2, q)
    print(f"  {name:22s} min_W|D|/N^5/7={D[W].min()/V:5.2f} max|D|/sqrt(q)={D.max()/np.sqrt(q*np.mean(np.abs(b)**2)):5.2f}"
          f"  small-rational bias={bias:5.2f}  rho={iv/(En*avg2**2):6.3f}  S3/CGL={s3ratio(Kd, W, q):6.3f}", flush=True)

if __name__ == '__main__':
    rng = np.random.default_rng(21)
    for q0 in [float(a) for a in sys.argv[1:]]:
        q = int(nextprime(int(q0))); F = KField(q); R_ = int(round(q**(2/3)))
        ms, H = setup_dual(F); P = Pvec(F, ms, H); P2 = np.abs(P)**2; avg2 = (P2.sum()-P2[0])/(q-2)
        Kd = F.Kvec(); rats = small_rats(q, 12)
        lam, mu, pr, big = sa(int(F.ns[0]), int(F.ns[-1]))
        n = F.ns.astype(float)
        bs = {'interval (smooth)': np.ones(len(n), complex),
              'mobius': mu.astype(complex), 'liouville': lam.astype(complex), 'primes': pr.astype(complex),
              'random +-1': rng.choice([-1.0, 1.0], len(n)).astype(complex),
              'random phases': np.exp(2j*np.pi*rng.random(len(n))),
              'quadratic phase': np.exp(2j*np.pi*(math.sqrt(2)*n*n/q)),
              'additive e(n m0/q)': np.exp(2j*np.pi*n*int(rng.integers(q//3, q//2))/q)}
        print(f"q={q} N={F.N} |W|={R_} M={q/F.N:.2f}   (random W: bias ~ {1/math.sqrt(R_):.2f})", flush=True)
        for name, b in bs.items():
            D = np.abs(F.D(b)); W = np.sort(np.argpartition(D, -R_)[-R_:])
            report(F, name + ' / top', b, W, P2, avg2, Kd, rats, q, R_)
            W2, b2 = refine(F, np.exp(1j*np.angle(b + 1e-12)), R_)
            report(F, name + ' / refined', b2, W2, P2, avg2, Kd, rats, q, R_)
