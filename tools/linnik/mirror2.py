"""mirror2.py W1 W2 N [OUT.json]: SieveCert2Defs.lean's `total2` on the grid U1 = ⌈(W1/10⁵)DEN⌉, U2 = ⌊(W2/10⁵)DEN⌋,
n = N, in exact integers, cell by cell as the Lean definitions read (`cand`, `allowed`, `refcost`, `dec`, `bound2`,
`reg2`, `keep`, `keepK`, `sub2`, `cost2`; natural subtraction truncated at 0). Also `route_limits.replay`'s `total`
and `refine_k2_probe.replay2`'s refined total, as cross-checks. With OUT, writes per cell (i, j) of nonzero cost or
work: cost2, the depth-4 tests the kernel makes for it (`counted4` evaluations in `refcost`, for allowed cells) and
the `surelyEval` tests of `sub2` (for dropped cells of `reg2`)."""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import route_limits as rl
import refine_k2_probe as rk
DEN, K, TOPK = rl.DEN, rl.K, rl.TOPK
tsub, cdiv, subset_sums = rl.tsub, rl.cdiv, rl.subset_sums
W1, W2, N = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
OUT = sys.argv[4] if len(sys.argv) > 4 else None
U1, U2 = (W1 * DEN + 99999) // 100000, W2 * DEN // 100000
n = N
V = U2 - U1
H = (tsub(DEN // 2, V) + n - 1) // n
lim = tsub(DEN, U1)
e = lambda k: V + H * k
def inside(lo, hi):
    return (U1 < lo and hi < U2) or (tsub(DEN, U2) < lo and hi < tsub(DEN, U1))
surely = lambda xs: any(inside(*s) for s in subset_sums(xs))
def invK(s, t, m):
    return K if DEN <= s + 2 * t + (m + 1) * H else cdiv(K * (t + H), DEN - s - t - m * H)
def omK(s, t, m):
    if DEN < s + 2 * t: return 0
    if s + 3 * t + (m + 2) * H <= DEN: return TOPK
    if DEN < s + 3 * t: return invK(s, t, m)
    return max(invK(s, t, m), TOPK)
cell = lambda k: (e(k), e(k) + H)
def bound2(a, b): return cdiv(H * H * DEN * omK(a, b, 2), a * b * b)
def bound4(a, b, c, d): return cdiv(H ** 4 * DEN * omK(a + b + c, d, 4), a * b * c * d * d)
def cand(i, j):
    ei, ej = e(i), e(j)
    return (ej < ei + H and 2 * ei < DEN and ei + 2 * ej <= DEN and not (U1 < ei and ei + H < U2)
            and not surely([cell(i), cell(j)]))
def inKK(i, j, k): return e(k) < e(j) + H and e(i) + e(j) + 2 * e(k) <= DEN
def ne3(i, j, k): return not surely([cell(i), cell(j), cell(k)])
def allowed(i, j):
    return e(i) + H + (e(j) + H) < lim and all(not (inKK(i, j, k) and ne3(i, j, k)) or e(i) + H + (e(j) + H) + (e(k) + H) < lim
                                                for k in range(n))
def counted4(i, j, k, l): return e(i) + e(j) + e(k) + 2 * e(l) <= DEN and not surely([cell(i), cell(j), cell(k), cell(l)])
def refcost(i, j):
    """refcost and the counted4 evaluations (`row`'s sumTo over l ≤ k, for each k with inKK && ne3)."""
    tot = tests = 0
    for k in range(n):
        if inKK(i, j, k) and ne3(i, j, k):
            for l in range(k + 1):
                tests += 1
                if counted4(i, j, k, l):
                    tot += bound4(e(i), e(j), e(k), e(l))
    return tot, tests
def reg2(i, j): return e(j) + H <= e(i) and 2 * (e(i) + H) <= DEN
def keep_tests(i, j, k):
    """(keep, whether `surelyEval` is evaluated): Bool `&&` evaluates its second argument only when the first is true."""
    if not (e(j) + H <= e(k)): return False, 0
    if not (2 * (e(k) + H) + e(i) + e(j) + 2 * H <= DEN): return False, 0
    return surely([cell(i), cell(j), cell(k)]), 1
def keepK(i, j, k):
    d = (e(i) + H) * (e(j) + H) * (e(k) + H) * tsub(tsub(tsub(DEN, e(i)), e(j)), e(k))
    return K * H ** 3 * DEN // d if d else 0
def sub2(i, j):
    if not reg2(i, j): return 0, 0
    tot = tests = 0
    for k in range(n):
        kp, t = keep_tests(i, j, k)
        tests += t
        if kp: tot += keepK(i, j, k)
    return tot, tests
t0 = time.time()
total = total2 = 0
cells = {}
rowcost = [0] * n
for i in range(n):
    for j in range(n):
        if not cand(i, j): continue
        b2 = bound2(e(i), e(j))
        al = allowed(i, j)
        t4 = 0
        if al:
            ref, t4 = refcost(i, j)
            dec = ref <= b2
        else:
            dec = False
        if dec:
            c = ref; c1 = ref; ts = 0
        else:
            s, ts = sub2(i, j)
            c = tsub(b2, s); c1 = b2
        total += c1; total2 += c
        rowcost[i] += c
        cells[f'{i},{j}'] = (c, t4, ts)
print(f'grid [{W1}, {W2}]/1e5 n={n}: U1={U1} U2={U2} H={H}; total/K {total / K:.5f} ({total}); total2/K {total2 / K:.5f} '
      f'({total2}); total2 < K: {total2 < K}; {time.time() - t0:.0f} s', flush=True)
rt, cnt, gok = rl.replay(U1, U2, n)
rv = rk.replay2(U1, U2, n)  # the fifth value: total2 by the certificate's own decisions (cost2)
r1, r2 = rv[:2]
print(f'route_limits.replay total {rt} equal: {rt == total}; refine_k2_probe.replay2 (total, total2) = ({r1}, {r2}) '
      f'equal: {r1 == total and r2 == total2}; GridOK {all(gok.values())}')
if len(rv) > 4:
    print(f'refine_k2_probe.replay2 fifth value {rv[4]} equal to total2: {rv[4] == total2}')
t4 = sum(v[1] for v in cells.values()); ts = sum(v[2] for v in cells.values())
print(f'kernel work: depth-4 tests {t4}, sub2 surelyEval tests {ts}, candidate cells {len(cells)}')
if OUT:
    json.dump({'W1': W1, 'W2': W2, 'n': n, 'U1': U1, 'U2': U2, 'H': H, 'total': total, 'total2': total2,
               'cells': cells}, open(OUT, 'w'))
