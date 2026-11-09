"""Numerics for S(r) = sum_{n1,n2,n3 in I} e(r n1 n2 n3 / q), I=(x,2x], x=q^{7/18}.

Reports max_{r!=0} |S|, RMS = sqrt(mean |S|^2), vs geometric x^2 and trivial x^3.
Via: for each r, sum over n1,n2 of geometric sum over n3 (exact closed form).
Also checks Parseval: mean_{r} |S|^2 = q * (J6 / q) ... sum_r |S|^2 = q * J6_tuples.
"""
from __future__ import annotations

import argparse
import math

import numpy as np
from sympy import nextprime


def run(q: int):
    x = int(round(q ** (7 / 18)))
    lo, hi = x + 1, 2 * x
    I = np.arange(lo, hi + 1, dtype=np.int64)
    L = len(I)
    trivial = float(L) ** 3
    geo = float(L) ** 2
    need = q ** (2 / 3)

    # Precompute all pairwise products mod q for speed when L small
    # S(r) = sum_{a,b in I} sum_{c in I} exp(2pi i r a b c / q)
    #      = sum_{a,b} exp(i pi r a b (lo+hi)/q) * sin(pi r a b L / q) / sin(pi r a b / q)  (geometric)
    # Use complex accumulation over a,b with geometric in c.

    # For q up to 1e5, L~88: L^2 = 7744 — fine to loop a,b and vectorize r
    # We'll compute |S(r)| for all r via FFT trick:
    # Let u[n] = # ways n = a*b with a,b in I (mod q? no — integer product then mod)
    # S(r) = sum_{a,b,c} e(r abc/q) = sum_m r2(m) * sum_c e(r m c / q) where m=ab
    # sum_c e(alpha c) with alpha = r m / q.

    max_prod2 = hi * hi
    r2 = np.zeros(max_prod2 + 1, np.int64)
    for a in I:
        r2[a * I] += 1
    m_idx = np.nonzero(r2)[0]
    m_val = r2[m_idx]

    # For each r=1..q-1, S = sum_m r2(m) * Geo(r*m, I)
    # Geo(alpha, I) = sum_{c in I} e(alpha c / q)
    def geo_sum(alpha_mod):
        # alpha_mod = (r * m) % q; sum_{c=lo..hi} e(alpha_mod * c / q)
        a = alpha_mod.astype(np.float64)
        # vectorized over many alphas
        # sum_{k=0}^{L-1} e(a*(lo+k)/q) = e(a lo/q) * (1 - e(a L/q))/(1 - e(a/q))
        twopi = 2 * math.pi / q
        phase0 = np.exp(1j * twopi * a * lo)
        e1 = np.exp(1j * twopi * a)
        # handle a==0
        out = np.empty(a.shape, dtype=np.complex128)
        zero = a == 0
        out[zero] = L
        nz = ~zero
        if np.any(nz):
            e1n = e1[nz]
            out[nz] = phase0[nz] * (1 - e1n**L) / (1 - e1n)
        return out

    # Compute S for all r by blocking over m
    # Memory: store S[r] accumulating
    S = np.zeros(q, dtype=np.complex128)
    # Process m in chunks
    chunk = 2000
    for s in range(0, len(m_idx), chunk):
        ms = m_idx[s : s + chunk]
        vs = m_val[s : s + chunk]
        # for each r, alphas = (r * ms) % q — shape (chunk, ) then broadcast r
        # Too big if we do all r at once for large q. Loop r in blocks.
        pass

    # Better: for each m, add vs[m] * geo_sum over all r of (r*m % q)
    # geo_sum as function of alpha=0..q-1 can be precomputed once!
    alphas = np.arange(q, dtype=np.float64)
    G = geo_sum(alphas)  # G[alpha] = sum_{c in I} e(alpha c / q)

    for m, v in zip(m_idx, m_val):
        # S[r] += v * G[(r*m) % q]
        # For all r: indices = (r * m) % q
        idx = (np.arange(q, dtype=np.int64) * int(m)) % q
        S += v * G[idx]

    # S[0] should be L^3
    absS = np.abs(S)
    max_nz = float(absS[1:].max())
    rms = float(np.sqrt(np.mean(absS[1:] ** 2)))
    # Parseval check: sum_r |S|^2 / q should equal J6 (count of congruent product pairs)
    sum_abs2 = float(np.sum(absS ** 2))
    J6_est = sum_abs2 / q
    main = trivial**2 / (q - 1)

    print(
        f"q={q} x={x} L={L}  trivial={trivial:.4e} geo={geo:.4e} need={need:.4e}"
    )
    print(
        f"  |S(0)|={absS[0]:.4e} (expect {trivial:.4e})"
    )
    print(
        f"  max|S|={max_nz:.4e}  max/geo={max_nz/geo:.3f}  max/need={max_nz/need:.3f}  "
        f"max/trivial={max_nz/trivial:.3f}"
    )
    print(
        f"  RMS|S|={rms:.4e}  RMS/geo={rms/geo:.3f}  RMS/need={rms/need:.3f}"
    )
    # fit: log(max/geo) / log q  as "extra" beyond geometric (negative = better than geo)
    if max_nz > 0:
        exp_max = math.log(max_nz) / math.log(q)
        exp_rms = math.log(rms) / math.log(q)
        print(
            f"  exp: max~q^{exp_max:.4f}  RMS~q^{exp_rms:.4f}  "
            f"geo=q^{2*math.log(L)/math.log(q):.4f}  need=q^{2/3:.4f}"
        )
    print(
        f"  Parseval: sum|S|^2/q={J6_est:.4e}  main={main:.4e}  "
        f"(J6-main)/main={(J6_est-main)/main:+.3f}"
    )
    return dict(q=q, max=max_nz, rms=rms, geo=geo, need=need, trivial=trivial)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("qs", nargs="*", type=float)
    args = ap.parse_args()
    sizes = [int(s) for s in args.qs] or [503, 1009, 5003, 10007, 30011, 100003]
    for s in sizes:
        q = int(nextprime(s - 1))
        run(q)
        print()


if __name__ == "__main__":
    main()
