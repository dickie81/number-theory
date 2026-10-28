#!/usr/bin/env python3
"""dropped_mass.py [L ...]: how much of what the certificate drops a Type II sum over the window could still recover.

For each exponent `L` (with none: `89/40`, `111/50`, `443/200` and `221/100`, in about seven minutes), the script takes
the window that `density_payoff.py` computes for the curve `g7d` at `L` (at `89/40` the library's
`[41479, 47555]/10⁵`) and replays the library's certificate on it at `n = 340`: `mirror2.py`'s decisions and costs,
copied below with the dropped terms recorded. The replay's `total` and `total2` must equal those of `mirror2.py`, which
the script runs on the same window, exactly, or it stops. These are computations, not theorems, and nothing in the
library depends on them.

It then estimates the true mass of the integers that the dropped terms count, in units of `x/log x`, the unit of the
certificate's `total/K` (the paper's Lemma `lem:drop`). Over a dropped box of depth `k` (2, 4 or 6) the true mass is
the integral of `ω((1 − α₁ − ⋯ − α_k)/α_k)/(α₁ ⋯ α_{k−1} α_k²)` over the part of the box where the term is not empty:
`α₁ > ⋯ > α_k`, `α₁ < 1/2`, and at depths 4 and 6, whose terms come from the parts below the splits at
`X′ = x^{1 − U₂/D}`, `α₁ + α₂ ≤ 1 − U₂/D` and `α₁ + α₂ + α₃ ≤ 1 − U₂/D`, and at depth 6 also
`α₁ + ⋯ + α₅ ≤ 1 − U₂/D`. Here `ω` is Buchstab's function (`1/u` on `[1, 2]` and `uω(u) = 1 + ∫₁^{u−1} ω` beyond,
tabulated on `[1, 30]` at step `10⁻⁴` by the trapezoidal rule), where the certificate's cost bounds the integrand with
`ω*` and by its maximum on the box. Each dropped box gets `cost·S/K` points, rounded stochastically (`S = 300000`;
`cost` is the box's `bound2`, `bound4` or `bound6`, so a dropped cell of depth 2 is sampled with its kept parts),
uniform in the box, and each point is weighted by the integrand times the box's volume times `K/(S·cost)`, so that the
weights' sum over a box has the box's true mass as its expectation.

At each point the term's cofactor `m` (exponent `g = 1 − α₁ − ⋯ − α_k`, no prime factor below `p_k`) is factored
into primes drawn from their asymptotic distribution: `m` is prime with probability `α_k/(g·ω(g/α_k))`, and otherwise
its least prime has exponent `ρ` with density proportional to `ω((g − ρ)/ρ)/ρ²` on `[α_k, g/2]`, the rest being a
cofactor of exponent `g − ρ` with no prime factor below it, factored in the same way. The sampled integer is
*recoverable* if a product of some of its primes, the term's and the cofactor's, has its exponent in
`𝒰 = (U₁/D, U₂/D) ∪ (1 − U₂/D, 1 − U₁/D)`, the paper's set of evaluable exponents: then the integer lies in a Type II
sum over the window. No Type II sum over this window contains the other integers, so their mass, the *unrecoverable*
mass, is a floor for the loss of a certificate that drops these terms, whatever parts of them it recovers by Type II
sums over the window. A point of a dropped cell `(i, j)` of depth 2 lies in the cell's kept parts if the cell is in
`reg2` and the point's cofactor is two primes `q₁ < q₂` with `q₁` in a fine cell `k` that the certificate's `keep`
accepts; the kept parts are recoverable, and `total2` already recovers them.

For each `L` it prints the window, the totals, and the true mass of the dropped terms in three parts: with a product of
the term's own primes in `𝒰` (points near the edges of cells whose boxes the exact tests find not surely evaluable),
with one only among the products that take a prime of the cofactor, and unrecoverable. Then it prints the kept parts'
mass, and the true and unrecoverable masses by depth; at depth 2 also by where `α₁` lies (below the window, inside it in
a cell that straddles one of its ends, or in the gap `(U₂/D, 1/2)` above it) and by whether `α₁ + α₂ ≥ 1 − U₁/D`, where
the term is not decomposed because the split at `X′` would leave cofactors below the window. It also prints why the
certificate drops the cell: the sharp rule does not allow decomposing it (`sharp`), decomposing it costs more than its
bound (`cost`), or it has depth 6, where the decomposition ends (`-`); and the number of dropped boxes of each depth
for each reason, counted exactly. A `±` is the square root of the sum of the squared weights counted, whose expectation
bounds the estimate's variance. At the end it prints a table of the totals and masses for every `L`.

Needs Python 3 only (and `mirror2.py` and `density_payoff.py`); uses all cores.
"""
import os
import random
import re
import subprocess
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import density_payoff as dp  # noqa: E402
import route_limits as rl  # noqa: E402

DEN, K = 2 ** 40, 2 ** 60
TOPK = rl.TOPK
tsub, cdiv = rl.tsub, rl.cdiv
n = 340
nC = n // 4
S = 300000
DEFAULT = [Fr(89, 40), Fr(111, 50), Fr(443, 200), Fr(221, 100)]

# Buchstab's omega on [1, 30], step 1e-4: omega = 1/u on [1, 2], u omega(u) = 1 + int_1^{u-1} omega for u >= 2
STEP = 1e-4
NW = int(29 / STEP) + 2
OM = [0.0] * NW
INT = [0.0] * NW
K2 = int(round(1 / STEP))
for _k in range(NW):
    _u = 1 + _k * STEP
    OM[_k] = 1 / _u if _k <= K2 else (1 + INT[_k - K2]) / _u
    if _k:
        INT[_k] = INT[_k - 1] + (OM[_k - 1] + OM[_k]) * STEP / 2


def omega(u):
    if u < 1:
        return 0.0
    x = (u - 1) / STEP
    k = int(x)
    if k >= NW - 1:
        return OM[-1]
    return OM[k] + (OM[k + 1] - OM[k]) * (x - k)


def cofactor(rng, g, t):
    """the exponents of the prime factors, least first, of an integer of exponent g with no prime factor below
    exponent t, drawn from their asymptotic distribution"""
    out = []
    while True:
        u = g / t
        if u < 2 or rng.random() < t / (g * omega(u)):
            out.append(g)
            return out
        a, b = 1 / t, 2 / g
        while True:                      # the least prime: density proportional to omega((g - r)/r)/r^2 on [t, g/2]
            r = 1 / (a - rng.random() * (a - b))
            if rng.random() < omega((g - r) / r):
                break
        out.append(r)
        g, t = g - r, r


def visible(xs, lo, hi):
    """whether a sum of some of the exponents xs lies in (lo, hi) or (1 - hi, 1 - lo)"""
    sums = [0.0]
    for e in xs:
        new = []
        for s in sums:
            t = s + e
            if lo < t < hi or 1 - hi < t < 1 - lo:
                return True
            if t < 1 - lo:
                new.append(t)
        sums += new
    return False


def setup(w1, w2):
    """mirror2.py's grid on the window [w1, w2]/10^5, in this process's globals"""
    global W1, W2, U1, U2, V, H, HC, lim, E, EC, LO2, HI2, lo1, hi1, XI
    W1, W2 = w1, w2
    U1, U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
    V = U2 - U1
    H = (tsub(DEN // 2, V) + n - 1) // n
    HC = (tsub(DEN // 2, V) + nC - 1) // nC
    lim = tsub(DEN, U1)
    E = [V + H * k for k in range(n)]
    EC = [V + HC * b for b in range(nC)]
    LO2, HI2 = tsub(DEN, U2), tsub(DEN, U1)
    lo1, hi1 = U1 / DEN, U2 / DEN
    XI = 1 - U2 / DEN                    # X' = x^XI: products above it have their cofactor in the window


# mirror2.py's cell code
def inside(lo, hi): return (U1 < lo and hi < U2) or (LO2 < lo and hi < HI2)


def sums(boxes):
    out = [(0, 0)]
    for lo, w in boxes:
        out = out + [(a + lo, b + lo + w) for a, b in out]
    return out


def surely(boxes): return any(inside(a, b) for a, b in sums(boxes))
def extend(S_, lo, w): return any(inside(a + lo, b + lo + w) for a, b in S_)
def invKw(s, t, W, w): return K if DEN <= s + 2 * t + W + w else cdiv(K * (t + w), DEN - s - t - W)


def omKw(s, t, W, w):
    if DEN < s + 2 * t: return 0
    if s + 3 * t + W + 2 * w <= DEN: return TOPK
    if DEN < s + 3 * t: return invKw(s, t, W, w)
    return max(invKw(s, t, W, w), TOPK)


def bound2(a, b): return cdiv(H * H * DEN * omKw(a, b, 2 * H, H), a * b * b)
def bound4(a, b, c, d): return cdiv(H ** 4 * DEN * omKw(a + b + c, d, 4 * H, H), a * b * c * d * d)


def bound6(a, b, c, d, f, g):
    return cdiv(H ** 4 * HC ** 2 * DEN * omKw(a + b + c + d + f, g, 4 * H + 2 * HC, HC), a * b * c * d * f * g * g)


def reg2(i, j): return E[j] + H <= E[i] and 2 * (E[i] + H) <= DEN


def keepK(i, j, k):
    d = (E[i] + H) * (E[j] + H) * (E[k] + H) * tsub(tsub(tsub(DEN, E[i]), E[j]), E[k])
    return K * H ** 3 * DEN // d if d else 0


def keepbox(i, j, k):
    return (E[j] + H <= E[k] and 2 * (E[k] + H) + E[i] + E[j] + 2 * H <= DEN
            and surely([(E[i], H), (E[j], H), (E[k], H)]))


def sub2(i, j):
    if not reg2(i, j): return 0
    return sum(keepK(i, j, k) for k in range(n) if keepbox(i, j, k))


def true_f(al, depth):
    """the true integrand of a dropped term of the given depth at the exponents al (decreasing), 0 where it is empty"""
    for x, y in zip(al, al[1:]):
        if not y < x:
            return 0.0
    if not al[0] < 0.5:
        return 0.0
    if depth >= 4 and not (al[0] + al[1] <= XI and al[0] + al[1] + al[2] <= XI):
        return 0.0
    if depth == 6 and not sum(al[:5]) <= XI:
        return 0.0
    g = 1 - sum(al)
    t = al[-1]
    w = omega(g / t)
    if w == 0:
        return 0.0
    p = 1.0
    for x in al[:-1]:
        p *= x
    return w / (p * t * t)


def sample_box(rng, depth, box, cost, i, j, kept_ok, acc, why):
    """box: [(lo, width)] in DEN units, the term's primes in order; cost: its bound in K units. acc[key] collects
    [points, mass, mass recoverable by the term's primes, mass recoverable only with the cofactor's, kept mass,
    sum of squared weights, sum of squared weights of the unrecoverable points, unrecoverable mass]"""
    m = cost * S / K
    cnt = int(m) + (rng.random() < m - int(m))
    if not cnt:
        return
    vol = 1.0
    for _, w in box:
        vol *= w / DEN
    for _ in range(cnt):
        al = [(lo + rng.random() * w) / DEN for lo, w in box]
        f = true_f(al, depth)
        if f == 0:
            continue
        wt = f * vol * K / (S * cost)
        cof = cofactor(rng, 1 - sum(al), al[-1])
        if depth == 2:
            a1, a2 = al
            key = (2, 'below' if a1 <= lo1 else 'gap' if a1 >= hi1 else 'window', a1 + a2 >= 1 - lo1, why)
        else:
            key = (depth, '', '', why)
        a = acc.setdefault(key, [0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0])
        a[0] += 1
        a[1] += wt
        a[5] += wt * wt
        if visible(al, lo1, hi1):
            a[2] += wt
        elif visible(al + cof, lo1, hi1):
            a[3] += wt
        else:
            a[6] += wt * wt
            a[7] += wt
        if kept_ok and len(cof) == 2:
            kq = int((cof[0] * DEN - V) // H)
            if 0 <= kq < n and keepbox(i, j, kq):
                a[4] += wt


def cell_row(i):
    """mirror2.py's row i, with each dropped box sampled: (total, total2, acc, the dropped boxes counted by depth and
    reason)"""
    rng = random.Random(1000003 * W1 + 7919 * i + W2)
    acc = {}
    cells = {}
    tot = tot2 = 0
    ei = E[i]
    for j in range(n):
        ej = E[j]
        if not (ej < ei + H and 2 * ei < DEN and ei + 2 * ej <= DEN and not (U1 < ei and ei + H < U2)): continue
        S2 = sums([(ei, H), (ej, H)])
        if any(inside(a, b) for a, b in S2): continue
        b2 = bound2(ei, ej)
        al = ei + H + (ej + H) < lim
        ks = []
        for k in range(n):
            ek = E[k]
            if ek < ej + H and ei + ej + 2 * ek <= DEN:
                S3 = sums([(ei, H), (ej, H), (ek, H)])
                if not any(inside(a, b) for a, b in S3):
                    ks.append((k, S3))
                    if not (ei + H + (ej + H) + (ek + H) < lim): al = False
        dec = False
        drops = []
        if al:
            ref = 0
            for k, S3 in ks:
                ek = E[k]
                for l in range(k + 1):
                    el = E[l]
                    if not (ei + ej + ek + 2 * el <= DEN): continue
                    if extend(S3, el, H): continue          # surely evaluable: cost 0
                    S4 = ei + ej + ek + el
                    T4 = S4 + 4 * H
                    d = T4 < lim
                    b4 = bound4(ei, ej, ek, el)
                    S4s = sums([(ei, H), (ej, H), (ek, H), (el, H)])
                    ne5 = []
                    for b in range(nC):
                        eb = EC[b]
                        if eb < el + H and S4 + 2 * eb <= DEN:
                            if not extend(S4s, eb, HC):
                                ne5.append(b)
                                if not (T4 + eb + HC < lim): d = False
                    if d:
                        r5 = 0
                        six = []
                        for b in ne5:
                            eb = EC[b]
                            S5s = S4s + [(a + eb, c + eb + HC) for a, c in S4s]
                            for c in range(b + 1):
                                ec = EC[c]
                                if S4 + eb + 2 * ec <= DEN:
                                    if not extend(S5s, ec, HC):
                                        b6 = bound6(ei, ej, ek, el, eb, ec)
                                        r5 += b6
                                        six.append((b, c, b6))
                        if r5 <= b4:
                            ref += r5
                            drops += [(6, (k, l, b, c), b6, '-') for b, c, b6 in six]
                        else:
                            ref += b4
                            drops.append((4, (k, l), b4, 'cost'))
                    else:
                        ref += b4
                        drops.append((4, (k, l), b4, 'sharp'))
            dec = ref <= b2
        if dec:
            tot += ref
            tot2 += ref
            for depth, idx, cost, why in drops:
                cells[depth, why] = cells.get((depth, why), 0) + 1
                if depth == 4:
                    k, l = idx
                    box = [(ei, H), (ej, H), (E[k], H), (E[l], H)]
                else:
                    k, l, b, c = idx
                    box = [(ei, H), (ej, H), (E[k], H), (E[l], H), (EC[b], HC), (EC[c], HC)]
                sample_box(rng, depth, box, cost, i, j, False, acc, why)
        else:
            s = sub2(i, j)
            tot += b2
            tot2 += tsub(b2, s)
            why = 'cost' if al else 'sharp'
            cells[2, why] = cells.get((2, why), 0) + 1
            sample_box(rng, 2, [(ei, H), (ej, H)], b2, i, j, reg2(i, j), acc, why)
    return tot, tot2, acc, cells


def mirror_totals(w1, w2):
    """mirror2.py's total and total2 on the window, as exact integers"""
    out = subprocess.run([sys.executable, os.path.join(HERE, 'mirror2.py'), str(w1), str(w2), str(n)],
                         capture_output=True, text=True, check=True).stdout
    m = re.search(r'total/K [0-9.]+ \((\d+)\); total2/K [0-9.]+ \((\d+)\)', out)
    return int(m.group(1)), int(m.group(2))


def measure(L):
    """the window at L, the replay's totals (checked against mirror2.py's) and the dropped terms' sampled masses"""
    w = dp.window(rl.parse('g7d'), L)
    if w is None:
        raise SystemExit(f'L = {L}: no window')
    t0 = time.time()
    with Pool(initializer=setup, initargs=w) as p:
        res = p.map(cell_row, range(n), chunksize=1)
    tot, tot2 = sum(r[0] for r in res), sum(r[1] for r in res)
    acc = {}
    cells = {}
    for _, _, a, c in res:
        for key, v in a.items():
            b = acc.setdefault(key, [0] * len(v))
            for q in range(len(v)):
                b[q] += v[q]
        for key, v in c.items():
            cells[key] = cells.get(key, 0) + v
    secs = time.time() - t0
    if mirror_totals(*w) != (tot, tot2):
        raise SystemExit(f'L = {L}: the replay\'s totals ({tot}, {tot2}) differ from mirror2.py\'s')
    return w, tot, tot2, acc, cells, secs


def show(L, w, tot, tot2, acc, cells, secs):
    T = [sum(v[q] for v in acc.values()) for q in range(8)]
    print(f'L = {L} ({float(L):.4f}): window [{w[0]}, {w[1]}]/10^5; total/K {tot / K:.5f} and total2/K {tot2 / K:.5f}, '
          f'equal to mirror2.py\'s; {T[0]} points, {secs:.0f} s')
    print(f'  true mass of the dropped terms                              {T[1]:.5f} ± {T[5] ** 0.5:.5f}')
    print(f'    a product of the term\'s own primes in U                  {T[2]:.5f}')
    print(f'    a product in U only with a prime of the cofactor          {T[3]:.5f}')
    print(f'    no product in U: unrecoverable                            {T[7]:.5f} ± {T[6] ** 0.5:.5f}')
    print(f'  in the kept parts (recoverable, and recovered by total2)    {T[4]:.5f}')
    print('  depth  alpha_1     alpha_1 + alpha_2 >= 1 - U1/D  dropped by  true mass  unrecoverable')
    for key in sorted(acc, key=lambda k: (k[0], k[1], str(k[2]), k[3])):
        depth, where, high, why = key
        v = acc[key]
        hi = '' if depth > 2 else 'yes' if high else 'no'
        print(f'  {depth:5d}  {where:10s}  {hi:29s}  {why:10s}  {v[1]:9.5f}  {v[7]:13.5f}')
    print('  dropped boxes by depth and reason: ' + ', '.join(f'{d} {y} {c}' for (d, y), c in sorted(cells.items())))
    return T


def main():
    Ls = [Fr(a) for a in sys.argv[1:]] or DEFAULT
    rows = []
    for L in Ls:
        w, tot, tot2, acc, cells, secs = measure(L)
        T = show(L, w, tot, tot2, acc, cells, secs)
        rows.append((L, w, tot, tot2, T))
        print(flush=True)
    print('L         window          total/K  total2/K  true mass  kept     net of kept  unrecoverable')
    for L, w, tot, tot2, T in rows:
        print(f'{str(L):9s} [{w[0]}, {w[1]}]  {tot / K:.5f}  {tot2 / K:.5f}   {T[1]:.5f}    {T[4]:.5f}  '
              f'{T[1] - T[4]:.5f}      {T[7]:.5f}')


if __name__ == '__main__':
    main()
