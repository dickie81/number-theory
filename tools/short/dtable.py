"""delta_req(D): the least moment delta for which a prime-factored polynomial N with T = N^D satisfies
int |N(1/2+it)|^delta << N^{delta/2} with a power saving (any delta > delta_req works). For each sigma, the count
R(sigma) of large values N^sigma is bounded through a power N^k by the mean value theorem, Huxley, or (gm) also
Guth-Maynard's Theorem 1.1; delta_req(D) = sup_sigma min_bounds R-exponent / (1 - sigma)."""
import numpy as np, sys

def delta_req(D, gm, gm_range=(0.7, 0.8), ns=40000, kmax=None):
    s = 0.5 + 0.5 * (np.arange(ns) + 0.5) / ns                 # sigma in (1/2, 1)
    kmax = kmax or int(3 * D) + 8
    best = np.full(ns, D)                                       # trivial: R <= T
    for k in range(1, kmax + 1):
        best = np.minimum(best, max(D, k) + k * (1 - 2 * s))   # mean value theorem for N^k
        best = np.minimum(best, np.maximum(2 * k * (1 - s), D + k * (4 - 6 * s)))
        if gm:
            g = np.maximum.reduce([2 * k * (1 - s), k * (3.6 - 4 * s), D + k * (2.4 - 4 * s)])
            if gm_range is not None:
                g = np.where((s >= gm_range[0]) & (s <= gm_range[1]), g, np.inf)
            best = np.minimum(best, g)
    # sigma -> 1: the mean value bound with k >= D gives 2k, Huxley with 2k >= D gives 2k
    tail = 2 * min(int(np.ceil(D)), 2 * int(np.ceil(D / 2)))
    return max(float(np.max(best / (1 - s))), 0.0), tail

def hux_formula(D):
    """delta_req for Huxley in closed form: on (m, m+1/2] it is 4D - 2m, on (m+1/2, m+1] it is 2m+2."""
    import math
    if D <= 1: return 2.0
    m = math.floor(D - 1e-12)
    return 4 * D - 2 * m if D - m <= 0.5 else 2 * m + 2

if __name__ == '__main__':
    for D in [1.2, 1.5, 1.7, 2.0, 2.3, 3.2, 3.5, 3.6, 3.8, 5.5, 5.6]:
        h, th = delta_req(D, False)
        g, tg = delta_req(D, True)
        print(f"D {D:4.2f}: Huxley {h:.4f} (closed form {hux_formula(D):.4f}, tail {th});  GM {g:.4f} (tail {tg})")
