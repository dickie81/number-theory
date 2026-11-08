"""Sec. 8: character sums over an interval at Chen-Gupta-Li's critical length.  q prime, x = q^(7/18), sigma = 5/7.

At T = 1 their detector (mollifier length (qT)^eps) is a sum of block sums S_I(chi) = sum_{n in I} chi(n).  For
I = [1, x] and I = (x, 2x] this prints, over all chi mod q (one FFT on discrete logarithms):
  count  = #{chi != chi_0 : |S_I| >= x^(5/7)}, against q^(2/3) and against the rigorous fourth-moment bound
           (q-1) E4(I) / x^(20/7), E4(I) = #{ab = cd in I} (x^2 < q makes the fourth moment an equation);
  M6/x^6 = sum_{chi != chi_0} |S_I|^6 over the principal character's |S_I(chi_0)|^6, which is what the mean value
           theorem charges at length x^3 > q;
  for [1, x] also M6 / (q E6), E6 = #{abc = def in [1, x]} (the integer diagonal), and E6 / x^3.
About a minute for the default primes 1e5, 1e6, 1e7, 3e7 (the last needs about 4 GB)."""
import sys
import numpy as np
from sympy import primitive_root, nextprime

def dlog(q):
    g = primitive_root(q); B = 4096
    pw = np.empty(q-1, dtype=np.int64); a = 1
    for j in range(min(B, q-1)):
        pw[j] = a; a = a*g % q
    gB = pow(g, B, q); step = 1
    for i in range(1, (q-1+B-1)//B):
        step = step*gB % q
        lo, hi = i*B, min((i+1)*B, q-1)
        pw[lo:hi] = pw[:hi-lo]*step % q
    ind = np.empty(q, dtype=np.int64); ind[pw] = np.arange(q-1)
    return ind

def E4(lo, hi):
    n = np.arange(lo, hi+1, dtype=np.int64)
    _, c = np.unique((n[:, None]*n[None, :]).ravel(), return_counts=True)
    return int((c.astype(np.int64)**2).sum())

def E6_initial(x):
    """#{abc = def : a, ..., f in [1, x]}"""
    r2 = np.zeros(x*x+1, np.int32)
    for a in range(1, x+1):
        r2[a*np.arange(1, x+1)] += 1
    m = np.nonzero(r2)[0]; v = r2[m]
    r3 = np.zeros(x**3+1, np.int32)
    for c in range(1, x+1):
        r3[c*m] += v
    tot, step = 0, 1 << 24
    for s in range(0, len(r3), step):
        u = r3[s:s+step].astype(np.int64); tot += int((u*u).sum())
    return tot

def run(q, sig=5/7):
    x = int(round(q**(7/18))); V = x**sig; R = q**(2/3)
    ind = dlog(q)
    print(f"q={q} x={x} q^(2/3)={R:.0f} x^(5/7)={V:.1f}", flush=True)
    for name, lo, hi in [('[1,x]  ', 1, x), ('(x,2x] ', x+1, 2*x)]:
        f = np.zeros(q-1); f[ind[lo:hi+1]] = 1.0
        a = np.abs(np.fft.fft(f))[1:]; del f
        L = hi - lo + 1
        cnt = int((a >= V).sum()); bound = (q-1)*E4(lo, hi)/V**4
        a2 = a*a; M6 = float((a2**3).sum())
        line = (f"  {name}: count={cnt} = {cnt/R:.2f} q^(2/3) = {cnt/bound:.3f} of the fourth-moment bound "
                f"({bound/R:.2f} q^(2/3));  M6/x^6={M6/L**6:.2f}")
        if lo == 1:
            e6 = E6_initial(x)
            line += f";  M6/(q E6)={M6/((q-1)*e6):.3f}, E6/x^3={e6/x**3:.1f}"
        print(line, flush=True)

if __name__ == '__main__':
    qs = [nextprime(int(float(s))-1) for s in sys.argv[1:]] or [100003, 1000003, 10000019, 30000001]
    for q in qs:
        run(q)
