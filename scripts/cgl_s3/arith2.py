"""Scaling of the bias for arithmetic coefficients (top q^{2/3} characters, no refinement):
Mobius, Liouville, primes, the zero detector c_n = sum_{d | n, d <= X} mu(d) at X = N^{1/2}, a quadratic phase, and
random signs.  rho is the weighted-energy bias; 'allowed' is q^{1/9 - 2 delta} q^{5/3} / E at delta = 0 and 1/26."""
import sys, math, numpy as np
from sympy import nextprime
from s3direct import KField
from schatten import setup_dual, Rvec
from q4split import Pvec
from bohr import weighted, s3ratio, small_rats
from arith import sa

def detector(lo, hi, X):
    """c_n = sum_{d | n, d <= X} mu(d) for lo <= n <= hi."""
    mu_small = sa(1, X)[1]
    c = np.zeros(hi - lo + 1)
    for d in range(1, X + 1):
        m = mu_small[d - 1]
        if m == 0: continue
        start = ((lo + d - 1)//d)*d
        c[start - lo::d] += m
    return c

if __name__ == '__main__':
    rng = np.random.default_rng(5)
    for q0 in [float(a) for a in sys.argv[1:]]:
        q = int(nextprime(int(q0))); F = KField(q); R_ = int(round(q**(2/3)))
        ms, H = setup_dual(F); P = Pvec(F, ms, H); P2 = np.abs(P)**2; avg2 = (P2.sum()-P2[0])/(q-2)
        Kd = F.Kvec(); rats = small_rats(q, 12)
        lo, hi = int(F.ns[0]), int(F.ns[-1])
        lam, mu, pr, big = sa(lo, hi)
        n = F.ns.astype(float)
        X = int(math.sqrt(F.N))
        bs = {'mobius': mu, 'liouville': lam, 'primes': pr, f'detector X={X}': detector(lo, hi, X),
              'quadratic phase': np.exp(2j*np.pi*(math.sqrt(2)*n*n/q)), 'random +-1': rng.choice([-1.0, 1.0], len(n))}
        print(f"q={q} N={F.N} |W|={R_} M={q/F.N:.2f}  allowed(delta=0) ~ {q**(1/9):.2f}*q^(5/3)/E, (1/26) ~ {q**(1/9-2/26):.2f}*q^(5/3)/E", flush=True)
        for name, b in bs.items():
            b = np.asarray(b, complex)
            D = np.abs(F.D(b)); W = np.sort(np.argpartition(D, -R_)[-R_:])
            R = Rvec(F, W); bias = max(abs(R[x]) for x in rats.values())/R_
            iv, E, En = weighted(W, P2, q)
            rho = iv/(En*avg2**2); e = E/q**(5/3)
            print(f"  {name:16s} bias={bias:5.2f}  rho={rho:6.3f}  E/q^(5/3)={e:5.2f}  rho/allowed(0)={rho*e/q**(1/9):5.2f}"
                  f"  rho/allowed(1/26)={rho*e/q**(1/9-2/26):5.2f}  S3/CGL={s3ratio(Kd, W, q):6.3f}", flush=True)
