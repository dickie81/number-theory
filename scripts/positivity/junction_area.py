# Uncertified: glue the dyadic "spheres" (blocks n in [2^k, 2^(k+1))) of the prime-side Gram matrix
# (ball_orbit.gram, computed from the primes; no zeros used) with weights from unit-sphere surface areas.
# Two gluings:  (A) congruence  W^{1/2} G W^{1/2}  (cross terms by sqrt(w_a w_b));
#               (B) diagonal-only reweighting: blocks scaled by w_k, cross terms left unweighted.
# (A) is a congruence by a positive diagonal matrix, so by Sylvester its sign pattern equals G's.
import sys, numpy as np
from math import gamma, pi
sys.path.insert(0, 'scripts')
import ball_orbit as bo
area = lambda d: 2 * pi ** (d / 2) / gamma(d / 2)          # |S^{d-1}|
Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4095
G = np.array(bo.gram(Mmax), dtype=float)
schemes = {
    "d=k+1": lambda k: area(k + 1),
    "d=2^k": lambda k: area(min(2 ** k, 340)),             # Gamma overflows past ~340; area is ~0 there anyway
    "ratio |S^d|/|S^(d-1)|, d=k+1": lambda k: area(k + 2) / area(k + 1),
}
print("min eigenvalue / max eigenvalue (relative); unweighted vs weighted")
for M in (255, 511, 1023, 2047, 4095):
    if M > Mmax: break
    H = G[:M, :M]; L = np.floor(np.log2(np.arange(1, M + 1))).astype(int)
    ev = np.linalg.eigvalsh(H); row = [f"M={M:5d} unweighted min={ev[0]:+.3e} rel={ev[0]/ev[-1]:+.2e}"]
    same = L[:, None] == L[None, :]
    for name, f in schemes.items():
        w = np.array([f(k) for k in L]); w = w / w.max()
        A = np.sqrt(w)[:, None] * H * np.sqrt(w)[None, :]
        B = np.where(same, w[:, None] * H, H)
        ea, eb = np.linalg.eigvalsh(A), np.linalg.eigvalsh(B)
        top = L.max(); share = w[L == top].mean()
        row.append(f"  [{name}] A: min={ea[0]:+.3e} rel={ea[0]/ea[-1]:+.2e} | B: min={eb[0]:+.3e} | top-block weight={share:.1e}")
    print("\n".join(row))
