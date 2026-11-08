"""Sec. 9: the count J6(I) = #{a1a2a3 = b1b2b3 (mod q) : all in I = (x, 2x]}, x = q^(7/18), split by the integer
difference h = a1a2a3 - b1b2b3 = kq, |k| <= K = 7x^3/q:  J6 = sum_k N(kq), N(h) = sum_m r3(m) r3(m+h), the shifted
convolution of the box-restricted ternary divisor function.  With Nt(h) the quadratic least-squares fit of N over
the h' with |h' - h| <= q/2, h' != h and the same small-prime signature as h (p^min(v_p, 2), p <= 13),
  J6 - |I|^6/(q-1) = D + S + F,  D = N(0) - Nt(0) (the integer diagonal minus its band),
  F = sum_{k != 0} (N(kq) - Nt(kq)) (the error of the shifted convolution at the shifts kq),
  S = the rest (the singular series of N averaged over the shifts, and edge terms).
Prints each over |I|^6/q.  About ten minutes for the default primes 1e5, 3e5, 1e6 (the last needs about 5 GB)."""
import sys, numpy as np
for q in [int(s) for s in sys.argv[1:]] or [100003, 300007, 1000003]:
    x = int(round(q**(7/18))); lo, hi = x+1, 2*x
    r2 = np.zeros(4*x*x+1, np.int64)
    for a in range(lo, hi+1): r2[a*np.arange(lo, hi+1)] += 1
    m = np.nonzero(r2)[0]; v = r2[m]
    r3 = np.zeros(8*x**3+1, np.float64)
    for c in range(lo, hi+1): r3[c*m] += v
    L = len(r3); n = 1 << int(np.ceil(np.log2(2*L)))
    F_ = np.fft.rfft(r3, n); N = np.rint(np.fft.irfft(F_*np.conj(F_), n)[:L]); del F_
    tot = r3.sum(); main = tot**2/(q-1)
    K = (7*x**3)//q; half = q//2
    Nfull = np.concatenate([N[:0:-1], N])            # N(h) for h = -(L-1) .. L-1, index h + L-1
    t = np.arange(-half, half+1, dtype=np.float64); keep = t != 0; tk = t[keep]/half
    V = np.vstack([np.ones_like(tk), tk, tk*tk]).T; P = np.linalg.pinv(V)
    PR = [2, 3, 5, 7, 11, 13]
    def sig(h):  # small-prime signature: p^min(v_p(h), 2) for p <= 13
        h = np.abs(np.asarray(h, np.int64)); out = np.ones(h.shape, np.int64)
        for p in PR:
            out *= np.where(h % (p*p) == 0, p*p, np.where(h % p == 0, p, 1))
        return out
    def Nt(h):  # quadratic fit of N over h' in |h'-h| <= q/2, h' != h, with sig(h') = sig(h)
        w = Nfull[h-half+L-1: h+half+L]
        if len(w) < len(t): return float('nan')
        hh = (h + t).astype(np.int64); m = keep & (sig(hh) == sig(np.array([h]))[0])
        tm = t[m]/half; Vm = np.vstack([np.ones_like(tm), tm, tm*tm]).T
        return float(np.linalg.lstsq(Vm, w[m], rcond=None)[0][0])
    J6 = N[0] + 2*sum(N[k*q] for k in range(1, K+1))
    D = N[0] - Nt(0)
    dev = np.array([N[k*q] - Nt(k*q) for k in range(1, K+1)])
    Fsum = 2*dev.sum()
    rel = dev/np.array([Nt(k*q) for k in range(1, K+1)])
    print(f"q={q} x={x} K={K}: (J6-|I|^6/q)/(|I|^6/q) = {(J6-main)/main:+.4f} = D {D/main:+.4f} + S {(J6-main-D-Fsum)/main:+.4f}"
          f" + F {Fsum/main:+.4f};  per-shift (N-Nt_sig)/Nt_sig: mean {rel.mean():+.4f}, sd {rel.std():.4f};  F/(x^3 sqrt K)={Fsum/(x**3*np.sqrt(K)):+.2f}", flush=True)
