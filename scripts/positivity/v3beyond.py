"""Past log 3/2 (docs/weil-vprime-log3.md, "Beyond log 3/2"): the true Weil form (every prime power with log n < 2L)
on the full space, on V (the pole constraint) and on V', by hpcore's high-precision sine basis (not certified).
Interlacing bounds: lambda_min on V' <= lambda_3 (even) and lambda_2 (odd) of the full form.
Usage: python3 scripts/positivity/v3beyond.py K DPS L [L ...]  (K modes, DPS decimal digits)."""
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp, hpcore as hc, numpy as np
from scipy.linalg import null_space
mp.mp.dps = int(sys.argv[2]); K = int(sys.argv[1])
def mat(M): return np.array([[float(M[i, j]) for j in range(M.cols)] for i in range(M.rows)])
for L in [float(x) for x in sys.argv[3:]]:
    row = 'L=%.2f K=%d primes=%s' % (L, K, [round(math.exp(float(y)), 3) for y, w in hc.lam_list(L)])
    for odd in (False, True):
        M, ks = hc.form(L, K, odd=odd)
        v = mp.matrix(hc.pole_vec(ks, mp.mpf(L), odd)); n = len(ks)
        iv = [(2 * mp.mpf(L) / (k * mp.pi)) * (1 - mp.cos(k * mp.pi)) / mp.sqrt(L) for k in ks]
        # orthonormal basis of V and V' in mpmath (Gram-Schmidt against the constraint vectors), then eigenvalues
        def comp(cons):
            B = []
            for c in cons:
                c = mp.matrix(c)
                for b in B: c = c - (b.T * c)[0] * b
                B.append(c / mp.norm(c))
            # projector onto complement, then an orthonormal basis via eigen-decomposition of I - sum b b^T
            Pm = mp.eye(n)
            for b in B: Pm = Pm - b * b.T
            E, U = mp.eigsy(Pm); cols = [U[:, i] for i in range(n) if E[i] > 0.5]
            Nm = mp.matrix(n, len(cols))
            for j, c in enumerate(cols):
                for i in range(n): Nm[i, j] = c[i]
            return Nm
        NV = comp([v]); NV2 = NV if odd else comp([v, iv])
        Ef = sorted(mp.eigsy(M)[0]); EV = sorted(mp.eigsy(NV.T * M * NV)[0]); EV2 = sorted(mp.eigsy(NV2.T * M * NV2)[0])
        row += "\n  %s: full lam1..3 %s | on V %s | on V' %s" % ('odd ' if odd else 'even', ['%.2e' % float(x) for x in Ef[:3]],
               '%.3e' % float(EV[0]), '%.3e' % float(EV2[0]))
    print(row, flush=True)
