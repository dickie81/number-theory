"""Lower failures, checked D by D: d2 < d1 also when l_D < -(2/5)(log(|D|/pi) + psi_a + c_a).

That threshold is <= -3.2 only for |D| >= 1.0757e5 (D > 0) and |D| >= 2.07e4 (D < 0); below that, the bound
"min l >= -3.0" does not rule lower failures out. This script computes l_D (PARI, as big.py) for EVERY fundamental
discriminant with 1 < |D| <= X+ (D > 0) or X- (D < 0) and compares it with its own lower and upper thresholds.

    python3 lower.py 107600 20800
"""
import sys, math, json
from multiprocessing import Pool
import cypari2
from big import init, ell

G, L2 = 0.5772156649015329, math.log(2)
C = {0: -0.25*math.log(27/4), 1: 0.75*math.log(3/4)}       # c_0, c_1 (D2Criterion.c0_closed, c1_closed)
PSI = {0: -G - 2*L2, 1: -G}                                 # psi(1/2), psi(1)


def lower(D, a): return -0.4*(math.log(abs(D)/math.pi) + PSI[a] + C[a])


if __name__ == '__main__':
    Xp, Xm = int(float(sys.argv[1])), int(float(sys.argv[2]))
    pp = cypari2.Pari()
    Ds = [d for d in range(2, Xp+1) if pp.isfundamental(d)] + [-d for d in range(2, Xm+1) if pp.isfundamental(-d)]
    with Pool(4, initializer=init) as pool: ls = pool.map(ell, Ds, chunksize=64)
    out = {}
    for a, name, X in ((0, 'D>0', Xp), (1, 'D<0', Xm)):
        S = [(D, l) for D, l in zip(Ds, ls) if (D > 0) == (a == 0)]
        lo = [(D, l) for D, l in S if l < lower(D, a)]
        up = sum(l > -2*C[a] for D, l in S)
        mD, ml = min(S, key=lambda x: x[1] - lower(x[0], a))
        out[name] = dict(X=X, n=len(S), upper_failures=up, lower_failures=len(lo), lower_examples=lo[:10],
                         min_l=min(l for _, l in S), closest_to_lower=dict(D=mD, l=ml, threshold=lower(mD, a)))
        print('%s |D|<=%d: n=%d  upper failures (l > %.6f) %d  lower failures %d  min l %.4f  closest to lower: D=%d l=%.4f vs %.4f'
              % (name, X, len(S), -2*C[a], up, len(lo), out[name]['min_l'], mD, ml, lower(mD, a)))
    json.dump(out, open('lower.json', 'w'), indent=1)
