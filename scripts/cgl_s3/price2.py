"""Density peak with the Schatten bound in place of CGL's first S3 term (T = 1, q prime, exponents base q, N = q^y).
Large-values consequences (each gives w <= ...), CGL Prop 11.1 / 10.2 structure:
  CGL:      y(2-2s); 1/2+y(3-4s); 4/3+y(2-4s); 1+y(9/2-7s); 18/19+y(72-112s)/19
  Schatten: diag part with E from Prop 10.2 (three cases): 7/9+y(2-28s/9); 58/59+y(120-208s)/59; 1+y(15-26s)/7
            energy part (conditional: pretentiously weighted energy = E x typical weights) = CGL's 2nd/4th/5th.
Then CGL §12: min over a of max_{y in [a,3a/2]} min(MVT, LV) / (1-s); curve = min(Ingham, that, Huxley)."""
import numpy as np

def lv(y, s, mode):
    mvt = max(y*(2-2*s), 1 + y*(1-2*s))
    if y < 2/3:
        return mvt
    base = [y*(2-2*s), 0.5 + y*(3-4*s), 1 + y*(4.5-7*s), 18/19 + y*(72-112*s)/19]
    if mode == 'cgl':
        t = base + [4/3 + y*(2-4*s)]
    else:
        t = base + [7/9 + y*(2-28*s/9), 58/59 + y*(120-208*s)/59, 1 + y*(15-26*s)/7]
    return min(mvt, max(t))

def A(s, mode, na=801, ny=161):
    best = 9
    for a in np.linspace(2/3, 1.2, na):
        v = max(lv(y, s, mode) for y in np.linspace(a, 1.5*a, ny))
        best = min(best, v)
    return best/(1-s)

def peak(mode, lo=0.66, hi=0.80, n=141):
    out = (0, 0, '')
    for s in np.linspace(lo, hi, n):
        vals = {'Ingham': 3/(2-s), 'Huxley': 3/(3*s-1)}
        if s >= 0.7:
            vals['LV'] = A(s, mode)
        k = min(vals, key=vals.get)
        if vals[k] > out[0]:
            out = (vals[k], s, k)
    return out

for mode in ['cgl', 'schatten']:
    v, s, k = peak(mode)
    print(f"{mode:9s}: peak {v:.5f} at sigma = {s:.4f} ({k});  7/3 = {7/3:.5f}, 30/13 = {30/13:.5f}")
    for s in [0.70, 0.705, 5/7, 0.73, 0.75, 0.78]:
        print(f"    s={s:.4f}: A = {A(s, mode):.5f}   Ingham {3/(2-s):.5f}")
