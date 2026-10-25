"""mirror2.py W1 W2 N [OUT.json]: the deep certificate of SieveCertDefs.lean / SieveCert2Defs.lean on the grid
U1 = ⌈(W1/10⁵)DEN⌉, U2 = ⌊(W2/10⁵)DEN⌋, n = N (a multiple of 4, with the coarse grid of N/4 cells), in exact integers,
cell by cell as the Lean definitions read: `cand`, `allowed`, `counted4`, `allowed4`, `inKK5`, `ne5`, `counted6`,
`bound2`, `bound4`, `bound6`, `refcost5`, `dec4`, `cost4`, `refcost`, `dec`, and the kept parts `reg2`, `keep`, `keepK`,
`sub2`, `cost2` (natural subtraction truncated at 0). Prints `total` (the certificate without the kept parts) and
`total2` (with them), and, with OUT, writes per candidate cell (i, j): cost2 and the kernel work it makes: the counted
cells of depth 4 evaluated (t4), the depth-5 cells evaluated (t5, in `allowed4` and `refcost5` together), the depth-6
cells evaluated (t6) and the `surelyEval` tests of `sub2` (ts). Rows are computed in parallel processes."""
import json, os, sys, time
from multiprocessing import Pool
DEN, K = 2 ** 40, 2 ** 60
TOPK = None  # set below: ⌈0.5672 K⌉ as in SieveCertDefs.lean
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl
TOPK = rl.TOPK
tsub, cdiv = rl.tsub, rl.cdiv
W1, W2, N = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
OUT = sys.argv[4] if len(sys.argv) > 4 else None
assert N % 4 == 0
n = N
nC = n // 4
U1, U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
V = U2 - U1
H = (tsub(DEN // 2, V) + n - 1) // n
HC = (tsub(DEN // 2, V) + nC - 1) // nC            # the coarse grid `Gc` of `nC` cells
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
def invKw(s, t, W, w):
    return K if DEN <= s + 2 * t + W + w else cdiv(K * (t + w), DEN - s - t - W)
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
    return K * H ** 3 * DEN // d if d else 0   # division by zero is zero in Lean
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

def cell_row(i):
    """all candidate cells of the row i: {j: (cost, cost_nokept, t4, t5, t6, ts)}"""
    res = {}
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
                    T4 = S4 + 4 * H
                    d = T4 < lim
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
                                if not (T4 + eb + HC < lim): d = False
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
        res[j] = (c, c1, t4, t5, t6, ts)
    return i, res

if __name__ == '__main__':
    t0 = time.time()
    with Pool() as p:
        rows = dict(p.imap_unordered(cell_row, range(n), chunksize=1))
    cells = {}; total = total2 = 0
    for i in range(n):
        for j, (c, c1, t4, t5, t6, ts) in sorted(rows[i].items()):
            total += c1; total2 += c
            cells[f'{i},{j}'] = (c, t4, t5, t6, ts)
    print(f'grid [{W1}, {W2}]/1e5 n={n} nC={nC}: U1={U1} U2={U2} H={H} HC={HC}; total/K {total / K:.5f} ({total}); '
          f'total2/K {total2 / K:.6f} ({total2}); total2 < K: {total2 < K}; {time.time() - t0:.0f} s', flush=True)
    t4 = sum(v[1] for v in cells.values()); t5 = sum(v[2] for v in cells.values())
    t6 = sum(v[3] for v in cells.values()); ts = sum(v[4] for v in cells.values())
    print(f'kernel work: depth-4 tests {t4}, depth-5 tests {t5}, depth-6 tests {t6}, sub2 surelyEval tests {ts}, '
          f'candidate cells {len(cells)}')
    if OUT:
        json.dump({'W1': W1, 'W2': W2, 'n': n, 'nC': nC, 'U1': U1, 'U2': U2, 'H': H, 'HC': HC, 'total': total,
                   'total2': total2, 'cells': cells}, open(OUT, 'w'))
