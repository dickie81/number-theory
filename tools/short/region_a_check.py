"""Can the real-exponent Hölder test (V2: Huxley, V3: Guth-Maynard) make any part of Li's region A asymptotic?
Region A: 0.25 <= t1 < 0.4, (1 - t1)/3 <= t2 < min(t1, 1 - 2 t1), three primes p1 p2 p3 with t3 = 1 - t1 - t2.
Tests every grouping of the three primes into Dirichlet polynomials (each prime alone, or two merged)."""
import math
import re
import sys

src = open('dtables.h').read()
D0, STEP = 0.9, 0.0005
tab = {k: [float(x) for x in re.search(r'DT_%s\[\d+\] = \{([^}]*)\}' % k, src).group(1).split(',')] for k in ('GM', 'HX')}


def dreq(D, k):
    if D <= D0:
        return tab[k][0]
    i = math.ceil((D - D0) / STEP - 1e-9)
    return tab[k][i] if i < len(tab[k]) else 1e9


def best(groups, omt, k):
    """max over the saving factor s of w_ml(s) + sum_{j != s} max(w_mv(j), w_ml(j)); > 1 means asymptotic."""
    ml = [1 / dreq(omt / a, k) for a in groups]
    mv = [1 / (2 * math.ceil(omt / a - 1e-12)) for a in groups]
    anyw = [max(x, y) for x, y in zip(mv, ml)]
    return max(sum(anyw) - anyw[s] + ml[s] for s in range(len(groups)))


for th in (0.520, 0.519, 0.5185):
    omt = 1 - th
    top = {'HX': (0, None), 'GM': (0, None)}
    n = 400
    for i in range(n):
        t1 = 0.25 + 0.15 * (i + 0.5) / n
        lo, hi = (1 - t1) / 3, min(t1, 1 - 2 * t1)
        for j in range(n):
            t2 = lo + (hi - lo) * (j + 0.5) / n
            if t2 >= hi:
                continue
            t3 = 1 - t1 - t2
            for k in ('HX', 'GM'):
                for g in ([t1, t2, t3], [t1 + t2, t3], [t1 + t3, t2], [t2 + t3, t1]):
                    v = best(g, omt, k)
                    if v > top[k][0]:
                        top[k] = (v, (round(t1, 4), round(t2, 4), round(t3, 4), [round(x, 4) for x in g]))
    print(f"theta {th}: best Hölder sum in region A  Huxley {top['HX'][0]:.4f} at {top['HX'][1]}"
          f"  GM {top['GM'][0]:.4f} at {top['GM'][1]}  (> 1 needed)")
