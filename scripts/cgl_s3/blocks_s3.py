"""Sec. 8: CGL's S3 on the genuine critical set.  q prime, x = q^(7/18), N = x^2 = q^(7/9).
W_crit = {chi != chi_0 : |sum_{x < n <= 2x} chi(n)| >= x^(5/7)} (the T = 1 detector), against a random W of the same
size: S3 = tr(E^3) over q^2|W|^(3/2), and lam_max(G)/N for the smooth-weight Gram matrix G of length N, where
CGL's bound at the critical point is lam_max(G) <~ q.  About two minutes for q = 1e5 and 1e6."""
import sys
import numpy as np
from sympy import nextprime
from s3direct import KField, s3_stats

def run(q, sig=5/7):
    x = int(round(q**(7/18)))
    F = KField(q, N=x*x); Kd = F.Kvec()
    f = np.zeros(q-1); f[F.ind[x+1:2*x+1]] = 1.0
    A = np.abs(np.fft.fft(f)); A[0] = 0
    W = np.nonzero(A >= x**sig)[0]
    print(f"q={q} x={x} N={F.N}: |W_crit|={len(W)} = {len(W)/q**(2/3):.2f} q^(2/3);  CGL's q/N = {q/F.N:.1f}", flush=True)
    s3_stats(F, Kd, W, 'W_crit (x,2x]')
    rng = np.random.default_rng(1)
    s3_stats(F, Kd, np.sort(rng.choice(np.arange(1, q-1), len(W), replace=False)), 'random, same size')

if __name__ == '__main__':
    for q in [nextprime(int(float(s))-1) for s in sys.argv[1:]] or [100003, 1000003]:
        run(q)
