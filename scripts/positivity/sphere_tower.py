# Uncertified: Li coefficients of xi split into the sphere tower and the prime radiation.
# log xi(s) = log(pi^{-s/2} Gamma(s/2+1)) + log((s-1) zeta(s));  pi^{-s/2}Gamma(s/2+1) = 1/V_s, V_s = unit-ball volume
# in dimension s (and pi^{-s/2}Gamma(s/2) = 2/|S^{s-1}|). With l_k the Taylor coefficients at s = 1,
# lambda_n = sum_{k=1}^n k C(n,k) l_k (from d/dz log xi(1/(1-z)) = sum lambda_{n+1} z^n), split additively.
import mpmath as mp, time
mp.mp.dps = 230; NMAX = 1000; NPTS = 4096; R = mp.mpf('2.5')
out = open('scripts/positivity/sphere_tower_results.txt', 'w')
def P(s): print(s, flush=True); out.write(s + "\n"); out.flush()
t0 = time.time()
# sphere part: exact via polygamma
la = [mp.mpf(0)] * (NMAX + 1)
la[1] = -mp.log(mp.pi)/2 + mp.digamma(mp.mpf(3)/2)/2
for k in range(2, NMAX + 1): la[k] = mp.polygamma(k-1, mp.mpf(3)/2) / (2**k * mp.factorial(k))
P(f"sphere coefficients {time.time()-t0:.0f}s")
# radiation part: Cauchy integral of log((s-1)zeta(s)) on |s-1| = R (no zeros inside; trivial zero -2 at distance 3)
vals = []; prev = None
for j in range(NPTS):
    w = R * mp.expjpi(mp.mpf(2*j)/NPTS); v = mp.log(w * mp.zeta(1 + w))
    if prev is not None:
        while v.imag - prev.imag > mp.pi: v -= 2j*mp.pi
        while v.imag - prev.imag < -mp.pi: v += 2j*mp.pi
    vals.append(v); prev = v
P(f"zeta samples {time.time()-t0:.0f}s; branch closes: {mp.nstr(vals[-1].imag - vals[0].imag, 5)}")
lr = [mp.mpf(0)] * (NMAX + 1); roots = [mp.expjpi(-mp.mpf(2*j)/NPTS) for j in range(NPTS)]
for k in range(1, NMAX + 1):
    lr[k] = (mp.fsum(vals[j] * roots[(j*k) % NPTS] for j in range(NPTS)) / NPTS / R**k).real
P(f"radiation coefficients {time.time()-t0:.0f}s")
def lam(l, n): return mp.fsum(k * mp.binomial(n, k) * l[k] for k in range(1, n+1))
P("n | sphere part | radiation part | lambda_n | ratio radiation/sphere | (n/2)log n")
for n in (1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000):
    a, b = lam(la, n), lam(lr, n); P(f"{n} | {mp.nstr(a, 10)} | {mp.nstr(b, 10)} | {mp.nstr(a+b, 10)} | {mp.nstr(b/a, 6)} | {mp.nstr(n/2*mp.log(n), 6)}")
neg = [n for n in range(1, NMAX+1) if lam(la, n) + lam(lr, n) < 0]
P(f"negative lambda_n for n <= {NMAX}: {neg[:10]} (count {len(neg)}); total {time.time()-t0:.0f}s")
