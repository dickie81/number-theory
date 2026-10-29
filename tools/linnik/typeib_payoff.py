#!/usr/bin/env python3
"""typeib_payoff.py: what a bilinear Type I estimate would buy the sieve route (issue #39), by replaying the library's
certificate with a wider sharp rule.

Usage:
  typeib_payoff.py total W1 W2 N L EST [--margin M] [--json OUT]
      `mirror2.py`'s `total2` on the grid `[W1, W2]/10⁵` with `N` cells a side, at the exponent `L` (a fraction), with
      the estimate `EST`; with `EST = off` it is `mirror2.py`'s `total2`, to the integer.
  typeib_payoff.py scan EST [START [STEP]]
      the lowest `L` passed with `total2 < 0.999K` at `N = 340`, on the curve `g7d`, with the window that
      `density_payoff.window` computes at each `L`: from `START` (default `278/125`, which must pass), `L` lowered by
      `STEP` (default `1/1000`) while the total passes, then one test `STEP/2` below the last `L` passed.

The estimate. For `x = q^L`, `d₁ ~ x^{a₁}` and `d₂ ~ x^{a₂}` with bounded coefficients, prime to `q`, and the cofactor
`k` over an interval with a weight `w`,
`Σ_{d₁,d₂} α(d₁)β(d₂)Σ_k w(k)(1[d₁d₂k ≡ a] − 1[(d₁d₂k, q) = 1]/φ(q)) = o(x/q)` when `L > 2` and (`EST`):
* `parseval`: `a₁ < 1 − 1/L` and `a₁ + 2a₂ < 1`. In Fourier form the sum is `q⁻¹Σ_{h≠0} ŵ(h)B(h)`; Cauchy–Schwarz
  over `d₁`, with the residues `d̄₁` extended to all of `ℤ/qℤ`, Parseval, and the diagonal `h d̄₂ = h′ d̄₂′`, which for
  `|h|, |h′| ≤ H` with `2H·d₂ < q` is the equation `hd₂′ = h′d₂` in the integers, give `(m x)^{1/2+ε}` with
  `m = 1 + d₁/q`. The weight is a spline (a repeated convolution of intervals), whose transform decays as fast as a
  smooth weight's, so the frequencies above `H ≈ q^{1+ε}/k` cost nothing; `a₁ + 2a₂ < 1` keeps `d₂` below `k`.
  `lib/pnt/SieveTypeIB.lean` proves the bound (`SieveTypeIB.typeIB_bound`).
* `trap`: `parseval`'s conditions and, for a trapezoid weight (transform decaying as `1/h²`), `3a₁ + 7a₂ < 2(2 − 1/L)`
  if `a₁ ≤ 1/L`, else `4a₁ + 7a₂ < 2(2 − 1/(2L))`.
* `sharp`: an interval weight: `a₁ < 1 − 1/L` and `a₁ + 3a₂ < 2(1 − 1/L)` if `a₁ ≤ 1/L`, else `2a₁ + 3a₂ < 2 − 1/L`.
* `weil`: `a₁ < 1 − 1/L` and `a₁ + 2a₂ < 2 − 5/(2L)`: Cauchy–Schwarz over `d₁` in its interval, the frequency merged
  into `d₂`, and Weil's bound for the incomplete Kloosterman sums over `d₁`.
* `off`: no estimate; the replay is `mirror2.py`'s.
`--margin M` lowers both limits of the estimate by `M`.

The sharp rule. `mirror2.py` (as `SieveCertDefs.allowed` and `allowed4`) lets a term over prime boxes `B` be split and
decomposed only when the upper end of `ΣB` is below `1 − U1/D`: then Proposition `prop:harman` evaluates its
`S(A_r, z₀)`, whose branches stop once the product enters the window's reflection. Here a term may also be decomposed
when `ib(B)`: the same iteration from `z₀` down to `w`, with a branch (the product `e` of the cofactor's primes below
`z₀`, each below `x^v`) stopped as soon as `p_S·e` enters the window or its reflection for some subset `S` of the term's
primes, and its leaves compared by the estimate with `d₁ = p_{S₁}·e` and `d₂ = p_{S₂}`, or `d₁ = p_{S₁}` and
`d₂ = p_{S₂}·e`. `ib` takes `t*`, the least over `S` of the largest point over the box at which `p_S·e` enters the
window or its reflection (from below), and asks the estimate at the box's upper ends with `e` of exponent `t*`.

Recorded results (`N = 340`, curve `g7d`): at `278/125` the total `0.99754K` becomes `0.64160K` (`weil`), `0.46069K`
(`parseval`), `0.52727K` (`trap`) and `0.66346K` (`sharp`); the lowest `L` passed is `2207/1000` (`weil`),
`4403/2000 = 2.2015` (`parseval`), `2203/1000` (`trap`) and `276/125` (`sharp`). The gain at `278/125` is in the
candidate cells below `1 − U1/D` that their cells of depth three blocked (with `weil`, `3275` cells, `0.349K` of cost
down to `0.014K`); the cells past that line keep their cost. These are computations under the model above, not
theorems of the library. Needs Python 3 only (and `route_limits.py`, `density_payoff.py`); a total takes one to four
minutes on four cores.
"""
import json
import os
import re
import subprocess
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

tsub, cdiv = rl.tsub, rl.cdiv
DEN, K = 2 ** 40, 2 ** 60
TOPK = (K * 565073 + 999999) // 1000000
W1K = (K * 5671433 + 9999999) // 10000000
LD = 10 ** 9
LNT = [0, 60624623, 117783037, 171850258, 223143553, 271933717, 318453733, 362905495, 405465110, 446287104,
       485507817, 523248145, 559615789, 594707109, 628608661, 661398484, 693147182]
ESTS = ('off', 'parseval', 'trap', 'sharp', 'weil')
G = {}   # the grid and the estimate, set by `setup` before the worker processes fork


def setup(W1, W2, n, L, est, margin=Fr(0)):
    assert n % 4 == 0 and est in ESTS
    U1, U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
    V = U2 - U1
    H = (tsub(DEN // 2, V) + n - 1) // n
    nC = n // 4
    HC = 4 * ((tsub(DEN // 2, V) + 4 * nC - 1) // (4 * nC))
    c1 = (1 - 1 / L - margin) * DEN
    G.update(W1=W1, W2=W2, n=n, nC=nC, L=L, est=est, U1=U1, U2=U2, V=V, H=H, HC=HC, lim=tsub(DEN, U1),
             E=[V + H * k for k in range(n)], EC=[V + HC * b for b in range(nC)],
             LO2=tsub(DEN, U2), HI2=tsub(DEN, U1),
             A1MAX=-((-c1.numerator) // c1.denominator) - 1,            # the largest a₁ with a₁ < (1 − 1/L)·DEN
             B_weil=2 * (1 - Fr(5, 4) / L - margin) * DEN,               # a₁ + 2a₂ < 2 − 5/(2L)
             B_pars=(1 - margin) * DEN,                                  # a₁ + 2a₂ < 1
             T1=2 * (2 - 1 / L - margin) * DEN, T2=2 * (2 - 1 / (2 * L) - margin) * DEN,
             S1=2 * (1 - 1 / L - margin) * DEN, S2=2 * (1 - 1 / (2 * L) - margin) * DEN, memo={})


def lt(x, bound):
    """`x < bound` for an integer `x` and a fraction `bound`."""
    return x * bound.denominator < bound.numerator


def cond2(a1, a2):
    """The estimate's second condition at `(a₁, a₂)`, in units of `1/DEN`."""
    est, L = G['est'], G['L']
    small = a1 * L.numerator <= DEN * L.denominator                     # a₁ ≤ 1/L
    if est == 'weil':
        return lt(a1 + 2 * a2, G['B_weil'])
    if est == 'sharp':
        return lt(a1 + 3 * a2, G['S1']) if small else lt(2 * a1 + 3 * a2, G['S2'])
    if not lt(a1 + 2 * a2, G['B_pars']):
        return False
    if est == 'trap':
        return lt(3 * a1 + 7 * a2, G['T1']) if small else lt(4 * a1 + 7 * a2, G['T2'])
    return True


def inside(lo, hi):
    return (G['U1'] < lo and hi < G['U2']) or (G['LO2'] < lo and hi < G['HI2'])


def sums(boxes):
    """The subset sums `(lo, hi)` of boxes `[(lo, width)]`, the empty subset included."""
    out = [(0, 0)]
    for lo, w in boxes:
        out = out + [(a + lo, b + lo + w) for a, b in out]
    return out


def surely(boxes):
    return any(inside(a, b) for a, b in sums(boxes))


def extend(S, lo, w):
    return any(inside(a + lo, b + lo + w) for a, b in S)


def tstar(boxes):
    """An upper bound over the box for the exponent of `e` at a leaf: the least over subsets `S` of the largest point at
    which `p_S·e` enters the window (from at or below `U1`) or its reflection (from `[U2, DEN − U2]`); `None` if no `S`
    stops every point of the box (a subset sum reaching `DEN − U1` never stops)."""
    U1, U2, LO2, HI2 = G['U1'], G['U2'], G['LO2'], G['HI2']
    best = None
    for a, b in sums(boxes):
        if b >= HI2:
            continue
        c = U1 - a if a <= U1 else 0
        if b >= U2 and a <= LO2:
            c = max(c, LO2 - max(a, U2))
        best = c if best is None else min(best, c)
    return best


def ib_leaf(his, t):
    """Some `S₁` with `e` wholly in `d₁` or wholly in `d₂` satisfies the estimate at the upper ends `his`."""
    k, tot = len(his), sum(his)
    for mask in range(1 << k):
        s1 = sum(his[i] for i in range(k) if mask >> i & 1)
        for a1, a2 in ((s1 + t, tot - s1), (s1, tot - s1 + t)):
            if a1 <= G['A1MAX'] and cond2(a1, a2):
                return True
    return False


def ib(boxes):
    if G['est'] == 'off':
        return False
    key = tuple(boxes)
    r = G['memo'].get(key)
    if r is None:
        t = tstar(boxes)
        r = t is not None and ib_leaf([lo + w for lo, w in boxes], t)
        G['memo'][key] = r
    return r


def ok(boxes):
    """May the term over these prime boxes be split and decomposed: `mirror2.py`'s test, or the estimate."""
    return sum(lo + w for lo, w in boxes) < G['lim'] or ib(boxes)


# `mirror2.py`'s bounds, as there

def omF(P, Q):
    k = 16 * (P - 2 * Q) // Q
    A, B = 16 * (P - Q), (16 + k) * Q
    return cdiv(K * Q * (2 * A * B * (LD + LNT[k]) + (A * A - B * B) * LD), 2 * A * B * LD * P)


def invKw(s, t, W, w):
    return K if DEN <= s + 2 * t + W + w else cdiv(K * (t + w), DEN - s - t - W)


def omKw(s, t, W, w):
    if DEN < s + 2 * t:
        return 0
    if s + 4 * t + W + 3 * w <= DEN:
        return TOPK
    if DEN < s + 3 * t:
        return invKw(s, t, W, w)
    p1 = 0 if s + 3 * t + W + 2 * w <= DEN else invKw(s, t, W, w)
    if 100 * (DEN + 1 - s - t) <= 276 * t:
        p2 = omF(DEN + 1 - s - t, t)
    elif 277 * (t + w) <= 100 * tsub(tsub(tsub(DEN, s), t), W):
        p2 = omF(DEN - s - t - W, t + w)
    else:
        p2 = W1K
    p3 = TOPK if s + 4 * t <= DEN else 0
    return max(p1, p2, p3)


def bound2(a, b):
    H = G['H']
    return cdiv(H * H * (2 * a + H) * DEN * omKw(a, b, 2 * H, H), 2 * a * (a + H) * (b * (b + H)))


def bound4(a, b, c, d):
    H = G['H']
    return cdiv(H ** 4 * ((2 * a + H) * (2 * b + H) * (2 * c + H)) * DEN * omKw(a + b + c, d, 4 * H, H),
                8 * (a * (a + H)) * (b * (b + H)) * (c * (c + H)) * (d * (d + H)))


def bound6(a, b, c, d, f, g):
    H, HC = G['H'], G['HC']
    return cdiv(H ** 4 * HC ** 2 * ((2 * a + H) * (2 * b + H) * (2 * c + H) * (2 * d + H) * (2 * f + HC)) * DEN *
                omKw(a + b + c + d + f, g, 4 * H + 2 * HC, HC),
                32 * (a * (a + H)) * (b * (b + H)) * (c * (c + H)) * (d * (d + H)) * (f * (f + HC)) * (g * (g + HC)))


def keepK(i, j, k):
    E, H = G['E'], G['H']
    d = (2 * E[i] + H) * (2 * E[j] + H) * (2 * E[k] + H) * tsub(tsub(tsub(DEN, E[i]), E[j]), E[k])
    return K * 8 * H ** 3 * DEN // d if d else 0


def sub2(i, j):
    """The kept parts of the candidate cell `(i, j)`."""
    E, H, n = G['E'], G['H'], G['n']
    if not (E[j] + H <= E[i] and 2 * (E[i] + H) <= DEN):
        return 0
    tot = 0
    for k in range(n):
        if E[j] + H <= E[k] and 2 * (E[k] + H) + E[i] + E[j] + 2 * H <= DEN:
            if surely([(E[i], H), (E[j], H), (E[k], H)]):
                tot += keepK(i, j, k)
    return tot


def cell_row(i):
    """`{j: (cost2, cost, dec, decomposable without the estimate)}` for the candidate cells of row `i`."""
    E, EC, H, HC, n, nC, U1, U2 = G['E'], G['EC'], G['H'], G['HC'], G['n'], G['nC'], G['U1'], G['U2']
    lim = G['lim']
    res = {}
    ei = E[i]
    for j in range(n):
        ej = E[j]
        if not (ej < ei + H and 2 * ei < DEN and ei + 2 * ej <= DEN and not (U1 < ei and ei + H < U2)):
            continue
        if surely([(ei, H), (ej, H)]):
            continue
        b2 = bound2(ei, ej)
        al_old = ei + ej + 2 * H < lim
        al = ok([(ei, H), (ej, H)])
        ks = []
        for k in range(n):
            ek = E[k]
            if ek < ej + H and ei + ej + 2 * ek <= DEN:
                S3 = sums([(ei, H), (ej, H), (ek, H)])
                if not any(inside(a, b) for a, b in S3):
                    ks.append((k, S3))
                    if not (ei + ej + ek + 3 * H < lim):
                        al_old = False
                    if al and not ok([(ei, H), (ej, H), (ek, H)]):
                        al = False
        dec = False
        if al:
            ref = 0
            for k, S3 in ks:
                ek = E[k]
                for l in range(k + 1):
                    el = E[l]
                    if not (ei + ej + ek + 2 * el <= DEN) or extend(S3, el, H):
                        continue
                    S4 = ei + ej + ek + el
                    box4 = [(ei, H), (ej, H), (ek, H), (el, H)]
                    d = ok(box4)
                    b4 = bound4(ei, ej, ek, el)
                    S4s = sums(box4)
                    ne5 = []
                    for b in range(nC):
                        eb = EC[b]
                        if eb < el + H and S4 + 2 * eb <= DEN and not extend(S4s, eb, HC):
                            ne5.append(b)
                            if d and not ok(box4 + [(eb, HC)]):
                                d = False
                    if d:
                        r5 = 0
                        for b in ne5:
                            eb = EC[b]
                            S5s = S4s + [(a + eb, c + eb + HC) for a, c in S4s]
                            for c in range(b + 1):
                                ec = EC[c]
                                if S4 + eb + 2 * ec <= DEN and not extend(S5s, ec, HC):
                                    r5 += bound6(ei, ej, ek, el, eb, ec)
                        ref += r5 if r5 <= b4 else b4
                    else:
                        ref += b4
            dec = ref <= b2
        if dec:
            c2 = c1 = ref
        else:
            c2, c1 = tsub(b2, sub2(i, j)), b2
        res[j] = (c2, c1, dec, al_old)
    return i, res


def total(W1, W2, n, L, est, margin=Fr(0), out=None):
    setup(W1, W2, n, L, est, margin)
    t0 = time.time()
    with Pool() as p:
        rows = dict(p.imap_unordered(cell_row, range(n), chunksize=1))
    tot = tot2 = 0
    cells = {}
    for i in range(n):
        for j, (c2, c1, dec, al_old) in sorted(rows[i].items()):
            tot += c1
            tot2 += c2
            cells[f'{i},{j}'] = (c2, dec, al_old)
    print(f'grid [{W1}, {W2}]/1e5 n={n} L={L} ({float(L):.5f}) est={est} margin={margin}: total/K {tot / K:.6f}; '
          f'total2/K {tot2 / K:.7f} ({tot2}); {time.time() - t0:.0f} s', flush=True)
    if out:
        json.dump({'W1': W1, 'W2': W2, 'n': n, 'L': str(L), 'est': est, 'margin': str(margin), 'total': tot,
                   'total2': tot2, 'cells': cells}, open(out, 'w'))
    return tot2


def scan(est, start=Fr(278, 125), step=Fr(1, 1000)):
    import density_payoff as dp
    pieces = dp.curve('today')

    def run(L):
        w = dp.window(pieces, L)
        if w is None:
            return None, None
        o = subprocess.run([sys.executable, os.path.abspath(__file__), 'total', str(w[0]), str(w[1]), '340', str(L),
                            est], capture_output=True, text=True, check=True).stdout
        return w, float(re.search(r'total2/K ([0-9.]+)', o).group(1))

    def show(L, w, t):
        print(f'  L = {L} ({float(L):.4f}): window {w}, total2/K {t}', flush=True)

    w, t = run(start)
    show(start, w, t)
    if t is None or t >= 0.999:
        raise SystemExit(f'{est}: {start} fails')
    good = start
    while True:
        L = good - step
        w, t = run(L)
        show(L, w, t)
        if t is None or t >= 0.999:
            break
        good = L
    mid = good - step / 2
    w, t = run(mid)
    show(mid, w, t)
    if t is not None and t < 0.999:
        good = mid
    print(f'{est}: lowest L passed {good} = {float(good):.4f}')


def main():
    args = sys.argv[1:]
    margin = Fr(args[args.index('--margin') + 1]) if '--margin' in args else Fr(0)
    out = args[args.index('--json') + 1] if '--json' in args else None
    if args and args[0] == 'total':
        W1, W2, n, L, est = int(args[1]), int(args[2]), int(args[3]), Fr(args[4]), args[5]
        total(W1, W2, n, L, est, margin, out)
    elif args and args[0] == 'scan':
        est = args[1]
        start = Fr(args[2]) if len(args) > 2 else Fr(278, 125)
        step = Fr(args[3]) if len(args) > 3 else Fr(1, 1000)
        scan(est, start, step)
    else:
        raise SystemExit(__doc__)


if __name__ == '__main__':
    main()
