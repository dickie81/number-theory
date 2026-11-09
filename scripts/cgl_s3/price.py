"""Price of a q^{-delta} saving in CGL's S3 bound (S3 <~ (qT)^{2-delta}|W|^{3/2}) at T = 1, q prime.

CGL §12 structure (their proof of Theorem 1.2, q1 = q): zero detector D_N with N <~ q^{1/2}; a power N^k lies in
[q^a, q^{3a/2}] (a >= 2/3).  At length q^y the large-values count is the better of
  MVT (1.2):        max(y(2-2s), 1 + y(1-2s))
  Thm 1.1, q1 = q:  max(y(2-2s), 1/2 + y(3-4s), c + y(2-4s), 1 + y(12/5-4s))     [y >= 2/3]
where c = 4/3 is the S3 term's constant (S3 <~ q^2|W|^{3/2} gives |W| <~ q^{4/3}N^{2-4s});
a saving q^{-delta} in S3 gives c = 4/3 - 2*delta/3.  A(s) = min_a max_{y in [a,3a/2]} min(MVT, Thm1.1) / (1-s).
The density curve is min(Ingham 3/(2-s), A(s), Huxley 3/(3s-1)) on [0.7, 0.8] (Ingham alone below 0.7).
"""
import numpy as np
from fractions import Fraction as Fr

def lv(y, s, c):
    mvt = max(y*(2-2*s), 1 + y*(1-2*s))
    if y < 2/3:
        return mvt
    t11 = max(y*(2-2*s), 0.5 + y*(3-4*s), c + y*(2-4*s), 1 + y*(12/5-4*s))
    return min(mvt, t11)

def A_cgl(s, c, na=1601, ny=241):
    best = 9.0
    for a in np.linspace(2/3, 1.2, na):
        ys = np.linspace(a, 1.5*a, ny)
        v = max(lv(y, s, c) for y in ys)
        if v < best:
            best, abest = v, a
    return best/(1-s), abest

def curve(s, c):
    ing = 3/(2-s)
    hux = 3/(3*s-1)
    if s < 0.7:
        return ing, 'Ingham'
    a, _ = A_cgl(s, c)
    vals = {'Ingham': ing, 'CGL': a, 'Huxley': hux}
    k = min(vals, key=vals.get)
    return vals[k], k

def peak(delta, lo=0.69, hi=0.75, n=241):
    c = 4/3 - 2*delta/3
    best = (0, None, None)
    for s in np.linspace(lo, hi, n):
        v, k = curve(s, c)
        if v > best[0]:
            best = (v, s, k)
    return best

if __name__ == '__main__':
    print("check: A_CGL at delta=0 against 4/(1+s):")
    for s in [0.70, 0.705, 5/7, 0.73, 0.75, 0.78]:
        a, aa = A_cgl(s, 4/3)
        print(f"  s={s:.4f}  A={a:.5f}  4/(1+s)={4/(1+s):.5f}  a*={aa:.4f}")
    print("\npeak of min(Ingham, CGL_delta, Huxley) over s, vs the closed form 7/3 - 2delta/3 (capped at 30/13):")
    for d in [0, 0.005, 0.01, 0.02, 0.03, 1/26, 0.05, 0.1, 0.25, 0.5]:
        v, s, k = peak(d)
        cf = max(7/3 - 2*d/3, 30/13)
        print(f"  delta={d:.4f}: peak {v:.5f} at s={s:.4f} ({k});  closed form {cf:.5f}")
