"""mirror2.py W1 W2 N [OUT.json] [--depth4] [--ib a/b]: the deep certificate of SieveCertDefs.lean / SieveCert2Defs.lean
on the grid U1 = ⌈(W1/10⁵)DEN⌉, U2 = ⌊(W2/10⁵)DEN⌋, n = N (a multiple of 4, with the coarse grid of N/4 cells), in exact integers,
cell by cell as the Lean definitions read: `cand`, `allowed`, `counted4`, `allowed4`, `inKK5`, `ne5`, `counted6`,
`omF`, `invKw`, `omKw`, `bound2`, `bound4`, `bound6`, `refcost5`, `dec4`, `cost4`, `refcost`, `dec`, and the kept parts
`reg2`, `keep`, `keepK`, `sub2`, `cost2` (natural subtraction truncated at 0). Prints `total` (the certificate without the kept parts) and
`total2` (with them), and, with OUT, writes per candidate cell (i, j): cost2 and the kernel work it makes: the counted
cells of depth 4 evaluated (t4), the depth-5 cells evaluated (t5, in `allowed4` and `refcost5` together), the depth-6
cells evaluated (t6) and the `surelyEval` tests of `sub2` (ts). It also prints the number of cells of depth 3 tested by
`ne3` below the decomposed candidate cells (the boxes of `inKK`, counted as t4 is), which OUT does not record. Rows are computed in parallel processes. With `--depth4`
no counted cell of depth 4 is decomposed: the decomposition stopped at depth four, whose `total` on the library's grid
(`41556 47531 340`) is the paper's `1.45721𝒦`.

With `--ib a/b` it is the certificate under the bilinear Type I rule of SieveRuleDefs.lean at `L = a/b` (`ibRule`,
`total2R`): a box may be split and decomposed when its upper sum is below `lim` (`limOK`), or when the bilinear test
passes it (`ibOK`: `tstar`, the least `cIB` over its subsets with upper sum below `DEN − U1`, and a split of its primes
with `a₁ < (1 − 1/L)DEN` and `a₁ + 2a₂ < DEN` at the upper ends, `leafIB`) with no boundary term (`nbOK`: the upper sum
plus the last cell's upper end below `DEN`). OUT then records a sixth number per cell, the `ibOK` tests the kernel makes
(tib, weighted by `2^k/16` for a box of `k` cells: two passes over its `2^k` subset sums)."""
import json, os, sys, time
from multiprocessing import Pool
DEN, K = 2 ** 40, 2 ** 60
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl
tsub, cdiv = rl.tsub, rl.cdiv
TOPK = (K * 565073 + 999999) // 1000000       # `topK`: ⌈0.565073 K⌉, ω* above 3
W1K = (K * 5671433 + 9999999) // 10000000     # `w1K`: ⌈0.5671433 K⌉, the maximum of Buchstab's ω on [2, 3]
LD = 10 ** 9                                  # `LD`, and `lnT`: upper bounds for LD·log((16 + k)/16), k ≤ 16
LNT = [0, 60624623, 117783037, 171850258, 223143553, 271933717, 318453733, 362905495, 405465110, 446287104,
       485507817, 523248145, 559615789, 594707109, 628608661, 661398484, 693147182]
DEPTH4 = '--depth4' in sys.argv
IB = sys.argv[sys.argv.index('--ib') + 1] if '--ib' in sys.argv else None
ARGS = [a for k, a in enumerate(sys.argv[1:], 1) if a not in ('--depth4', '--ib') and sys.argv[k - 1] != '--ib']
W1, W2, N = int(ARGS[0]), int(ARGS[1]), int(ARGS[2])
OUT = ARGS[3] if len(ARGS) > 3 else None
assert N % 4 == 0
n = N
nC = n // 4
U1, U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
V = U2 - U1
H = (tsub(DEN // 2, V) + n - 1) // n
HC = 4 * ((tsub(DEN // 2, V) + 4 * nC - 1) // (4 * nC))   # the coarse grid `Gc`: nC cells of four, HC = 4H
lim = tsub(DEN, U1)
E = [V + H * k for k in range(n)]
EC = [V + HC * b for b in range(nC)]
LO2, HI2 = tsub(DEN, U2), tsub(DEN, U1)
def inside(lo, hi):
    return (U1 < lo and hi < U2) or (LO2 < lo and hi < HI2)
def sums(boxes):
    """the subset sums (lo, hi) of boxes [(lo, width)], the empty subset included"""
    out = [(0, 0)]
    for lo, w in boxes:
        out = out + [(a + lo, b + lo + w) for a, b in out]
    return out
def surely(boxes): return any(inside(a, b) for a, b in sums(boxes))
def extend(S, lo, w):
    """the subset sums with one more box, when those of S are known not to be inside"""
    return any(inside(a + lo, b + lo + w) for a, b in S)
def omF(P, Q):
    """`omF`: K·(1 + log(v − 1))/v at v = P/Q ∈ [2, 3], rounded up, with log(v − 1) ≤ lnT k/LD + (y − 1/y)/2 for
    k = ⌊16(v − 2)⌋ and y = (v − 1)·16/(16 + k) = A/B."""
    k = 16 * (P - 2 * Q) // Q
    A, B = 16 * (P - Q), (16 + k) * Q
    return cdiv(K * Q * (2 * A * B * (LD + LNT[k]) + (A * A - B * B) * LD), 2 * A * B * LD * P)
def invKw(s, t, W, w):
    return K if DEN <= s + 2 * t + W + w else cdiv(K * (t + w), DEN - s - t - W)
def omKw(s, t, W, w):
    """`omKw`: K·ω* on the arguments [lo, hi) of a box, lo = (DEN − s − t − W)/(t + w), hi = (DEN + 1 − s − t)/t."""
    if DEN < s + 2 * t: return 0                                  # hi ≤ 1
    if s + 4 * t + W + 3 * w <= DEN: return TOPK                  # lo ≥ 3
    if DEN < s + 3 * t: return invKw(s, t, W, w)                  # hi ≤ 2
    p1 = 0 if s + 3 * t + W + 2 * w <= DEN else invKw(s, t, W, w) # lo < 2: 1/max(lo, 1)
    if 100 * (DEN + 1 - s - t) <= 276 * t: p2 = omF(DEN + 1 - s - t, t)                 # hi ≤ 2.76: ω increases
    elif 277 * (t + w) <= 100 * tsub(tsub(tsub(DEN, s), t), W): p2 = omF(DEN - s - t - W, t + w)  # lo ≥ 2.77
    else: p2 = W1K
    p3 = TOPK if s + 4 * t <= DEN else 0                          # hi > 3
    return max(p1, p2, p3)
def bound2(a, b):
    return cdiv(H * H * (2 * a + H) * DEN * omKw(a, b, 2 * H, H), 2 * a * (a + H) * (b * (b + H)))
def bound4(a, b, c, d):
    return cdiv(H ** 4 * ((2 * a + H) * (2 * b + H) * (2 * c + H)) * DEN * omKw(a + b + c, d, 4 * H, H),
                8 * (a * (a + H)) * (b * (b + H)) * (c * (c + H)) * (d * (d + H)))
def bound6(a, b, c, d, f, g):
    return cdiv(H ** 4 * HC ** 2 * ((2 * a + H) * (2 * b + H) * (2 * c + H) * (2 * d + H) * (2 * f + HC)) * DEN *
                omKw(a + b + c + d + f, g, 4 * H + 2 * HC, HC),
                32 * (a * (a + H)) * (b * (b + H)) * (c * (c + H)) * (d * (d + H)) * (f * (f + HC)) * (g * (g + HC)))
def reg2(i, j): return E[j] + H <= E[i] and 2 * (E[i] + H) <= DEN
def keepK(i, j, k):
    d = (2 * E[i] + H) * (2 * E[j] + H) * (2 * E[k] + H) * tsub(tsub(tsub(DEN, E[i]), E[j]), E[k])
    return K * 8 * H ** 3 * DEN // d if d else 0   # division by zero is zero in Lean
def sub2(i, j):
    if not reg2(i, j): return 0, 0
    tot = tests = 0
    S2 = sums([(E[i], H), (E[j], H)])
    for k in range(n):
        if not (E[j] + H <= E[k]): continue
        if not (2 * (E[k] + H) + E[i] + E[j] + 2 * H <= DEN): continue
        tests += 1
        if inside_any3(i, j, k):
            tot += keepK(i, j, k)
    return tot, tests
def inside_any3(i, j, k): return surely([(E[i], H), (E[j], H), (E[k], H)])
# the bilinear Type I rule (`--ib a/b`), as SieveRuleDefs.lean reads it
if IB:
    LNUM, LDEN = map(int, IB.split('/'))
def cIB(s):
    """`cIB`: the largest exponent at which `p_S·e` enters the window from at or below `U1`, or its reflection from
    `[U2, DEN − U2]`, for `S` with subset sums `s = (lo, hi)`."""
    return max(tsub(U1, s[0]), tsub(tsub(DEN, U2), max(s[0], U2)) if U2 <= s[1] else 0)
def condIB(a1, a2): return a1 * LNUM < tsub(LNUM, LDEN) * DEN and a1 + 2 * a2 < DEN
def ibOK(boxes):
    """`ibOK`: `tstar`, then `leafIB` at the upper ends."""
    ss = sums(boxes)
    cs = [cIB(s) for s in ss if s[1] < tsub(DEN, U1)]
    if not cs: return False
    T, tot = min(cs), sum(lo + w for lo, w in boxes)
    return any(condIB(s[1] + T, tot - s[1]) or condIB(s[1], tot - s[1] + T) for s in ss)
def nbOK(boxes): return sum(lo + w for lo, w in boxes) + boxes[-1][0] + boxes[-1][1] < DEN
IBT = [0]   # the `ibOK` tests of the current cell, weighted by 2^k/16
def ok(boxes):
    """`Rule.ok`: `limOK` (the certificate's own rule), or with `--ib`, `okIB = limOK || (ibOK && nbOK)`."""
    if sum(lo + w for lo, w in boxes) < lim: return True
    if not IB: return False
    IBT[0] += 2 ** len(boxes) / 16
    return ibOK(boxes) and nbOK(boxes)

def cell_row(i):
    """all candidate cells of the row i: {j: (cost, cost_nokept, t4, t5, t6, ts, t3, dec)}"""
    res = {}
    ei = E[i]
    for j in range(n):
        ej = E[j]
        if not (ej < ei + H and 2 * ei < DEN and ei + 2 * ej <= DEN and not (U1 < ei and ei + H < U2)): continue
        S2 = sums([(ei, H), (ej, H)])
        if any(inside(a, b) for a, b in S2): continue
        b2 = bound2(ei, ej)
        IBT[0] = 0
        al = ok([(ei, H), (ej, H)])
        ks = []
        c3 = 0
        for k in range(n):
            ek = E[k]
            if ek < ej + H and ei + ej + 2 * ek <= DEN:
                c3 += 1
                S3 = sums([(ei, H), (ej, H), (ek, H)])
                if not any(inside(a, b) for a, b in S3):
                    ks.append((k, S3))
                    if al and not ok([(ei, H), (ej, H), (ek, H)]): al = False
        t3 = c3 if al else 0
        t4 = t5 = t6 = 0
        dec = False
        if al:
            ref = 0
            for k, S3 in ks:
                ek = E[k]
                for l in range(k + 1):
                    el = E[l]
                    if not (ei + ej + ek + 2 * el <= DEN): continue
                    t4 += 1
                    if extend(S3, el, H): continue          # surely evaluable: cost 0
                    S4 = ei + ej + ek + el
                    d = not DEPTH4 and ok([(ei, H), (ej, H), (ek, H), (el, H)])
                    b4 = bound4(ei, ej, ek, el)
                    # the cells of depth 5
                    S4s = sums([(ei, H), (ej, H), (ek, H), (el, H)])
                    ne5 = []
                    for b in range(nC):
                        eb = EC[b]
                        if eb < el + H and S4 + 2 * eb <= DEN:
                            t5 += 1
                            if not extend(S4s, eb, HC):
                                ne5.append(b)
                                if d and not ok([(ei, H), (ej, H), (ek, H), (el, H), (eb, HC)]): d = False
                    if d:
                        r5 = 0
                        for b in ne5:
                            eb = EC[b]
                            S5s = S4s + [(a + eb, c + eb + HC) for a, c in S4s]
                            for c in range(b + 1):
                                ec = EC[c]
                                if S4 + eb + 2 * ec <= DEN:
                                    t6 += 1
                                    if not extend(S5s, ec, HC):
                                        r5 += bound6(ei, ej, ek, el, eb, ec)
                        ref += r5 if r5 <= b4 else b4
                    else:
                        ref += b4
            dec = ref <= b2
        if dec:
            c = c1 = ref; ts = 0
        else:
            s, ts = sub2(i, j)
            c = tsub(b2, s); c1 = b2
        res[j] = (c, c1, t4, t5, t6, ts, t3, dec, round(IBT[0]))
    return i, res

if __name__ == '__main__':
    t0 = time.time()
    with Pool() as p:
        rows = dict(p.imap_unordered(cell_row, range(n), chunksize=1))
    cells = {}; total = total2 = t3 = 0
    for i in range(n):
        for j, (c, c1, t4, t5, t6, ts, c3, _, tib) in sorted(rows[i].items()):
            total += c1; total2 += c; t3 += c3
            cells[f'{i},{j}'] = (c, t4, t5, t6, ts, tib) if IB else (c, t4, t5, t6, ts)
    print(f'grid [{W1}, {W2}]/1e5 n={n} nC={nC}: U1={U1} U2={U2} H={H} HC={HC}; total/K {total / K:.5f} ({total}); '
          f'total2/K {total2 / K:.6f} ({total2}); total2 < K: {total2 < K}; {time.time() - t0:.0f} s', flush=True)
    t4 = sum(v[1] for v in cells.values()); t5 = sum(v[2] for v in cells.values())
    t6 = sum(v[3] for v in cells.values()); ts = sum(v[4] for v in cells.values())
    print(f'kernel work: depth-3 tests {t3}, depth-4 tests {t4}, depth-5 tests {t5}, depth-6 tests {t6}, '
          f'sub2 surelyEval tests {ts}, candidate cells {len(cells)}' +
          (f', ibOK tests (weighted) {sum(v[5] for v in cells.values())}' if IB else ''))
    if OUT:
        json.dump({'W1': W1, 'W2': W2, 'n': n, 'nC': nC, 'U1': U1, 'U2': U2, 'H': H, 'HC': HC, 'total': total,
                   'total2': total2, 'cells': cells, **({'ib': IB} if IB else {})}, open(OUT, 'w'))
