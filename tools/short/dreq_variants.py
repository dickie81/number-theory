"""delta_req(D) with subsets of the large values estimates: MVT only, MVT + Huxley, MVT + GM, all three."""
import numpy as np
def dreq(D, mv=True, hux=False, gm=False, ns=20000):
    s = 0.5 + 0.5 * (np.arange(ns) + 0.5) / ns
    best = np.full(ns, D)
    for k in range(1, int(3 * D) + 9):
        if mv:  best = np.minimum(best, max(D, k) + k * (1 - 2 * s))
        if hux: best = np.minimum(best, np.maximum(2 * k * (1 - s), D + k * (4 - 6 * s)))
        if gm:
            g = np.maximum.reduce([2 * k * (1 - s), k * (3.6 - 4 * s), D + k * (2.4 - 4 * s)])
            best = np.minimum(best, np.where((s >= 0.7) & (s <= 0.8), g, np.inf))
    return float(np.max(best / (1 - s)))
print(f"{'D':>5} {'MVT':>7} {'MVT+Hux':>8} {'MVT+GM':>8} {'all':>7}")
for D in (1.0, 1.2, 1.4, 1.5, 1.6, 1.8, 2.0, 2.2, 2.4, 2.5, 2.7, 3.0, 3.3, 3.5, 3.8, 4.2, 4.5, 5.5, 7.5):
    print(f"{D:5.2f} {dreq(D):7.3f} {dreq(D, hux=True):8.3f} {dreq(D, gm=True):8.3f} {dreq(D, hux=True, gm=True):7.3f}")
