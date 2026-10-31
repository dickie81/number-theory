"""Li's full lower-bound accounting at each theta, from every run file: region C is
U_C01 + U_C03 + U_C04 + U_C05 + U_C06 + U_C07 + U_C08 + U_C12 + U_C13 (his final bound, with the savings
U_C02, U_C09, U_C10 and the correction U_C11 set to 0), and the constant is 1 - 2 A - C with A = 0.240227.
Dropping the savings only raises the loss: U_C02 is subtracted, and U_C09 + U_C10 - U_C11 counts, once each, the
part of U_C08's set where at least one of its two further decompositions is asymptotic, so it is >= 0.
Region A is the same for every variant (region_a_check.py: no grouping of its three primes passes the test)."""
import math
import re
import sys

A2 = 2 * 0.240227
TERMS = {'C4DLoss': 'U_C01', 'C6DLoss1': 'U_C03', 'C6DLoss2': 'U_C04', 'UC05': 'U_C05', 'UC06': 'U_C06',
         'UC07': 'U_C07', 'C4DRRLoss': 'U_C08', 'C6DRRLoss2': 'U_C12', 'C6DRRLoss3': 'U_C13'}
# est[theta][piece] = list of (V0, se0, cut1, se1, cut2, se2, cut3, se3), one per run
est = {}
for path in sys.argv[1:]:
    th = None
    for line in open(path):
        m = re.match(r'theta (\S+)', line)
        if m:
            th = round(float(m.group(1)), 4)
            continue
        m = re.match(r'(\w+)\s+\(\s*\d+s\):\s+V0 (\S+)\+-(\S+)\s+V1 -(\S+)\+-(\S+)\s+V2 -(\S+)\+-(\S+)\s+V3 -(\S+)\+-(\S+)', line)
        if m and th is not None and m.group(1) in TERMS:
            est.setdefault(th, {}).setdefault(m.group(1), []).append([float(x) for x in m.groups()[1:]])


def combine(runs, k):
    """Inverse-variance mean of column k (value) with its standard error in column k + 1."""
    w = [1 / max(r[k + 1], 1e-7) ** 2 for r in runs]
    m = sum(wi * r[k] for wi, r in zip(w, runs)) / sum(w)
    return m, math.sqrt(1 / sum(w))


rows = []
print(f"{'theta':>7} {'terms':>5}  {'C (V0)':>15}  {'LB V0':>16} {'LB V1':>8} {'LB V2':>16} {'LB V3':>16}")
for th in sorted(est):
    d = est[th]
    if len(d) < len(TERMS):
        print(f"{th:7.4f} {len(d):5d}  (missing: {', '.join(t for t in TERMS if t not in d)})")
        continue
    c0 = [combine(r, 0) for r in d.values()]
    C0, E0 = sum(m for m, _ in c0), math.sqrt(sum(e * e for _, e in c0))
    lbs = []
    for v in range(4):
        if v == 0:
            lbs.append((1 - A2 - C0, E0))
            continue
        cut = [combine(r, 2 * v) for r in d.values()]
        cv, ev = sum(m for m, _ in cut), math.sqrt(sum(e * e for _, e in cut))
        lbs.append((1 - A2 - C0 + cv, math.sqrt(E0 ** 2 + ev ** 2)))
    rows.append((th, lbs))
    print(f"{th:7.4f} {len(d):5d}  {C0:8.4f}+-{E0:.4f}  {lbs[0][0]:8.4f}+-{lbs[0][1]:.4f} {lbs[1][0]:8.4f}"
          f" {lbs[2][0]:8.4f}+-{lbs[2][1]:.4f} {lbs[3][0]:8.4f}+-{lbs[3][1]:.4f}")

print()
for v, name in ((0, 'V0 (Li, integrated without rounding)'), (2, 'V2 (real exponents, Huxley)'),
                (3, 'V3 (real exponents, Guth-Maynard)')):
    pts = [(th, lbs[v][0]) for th, lbs in rows]
    cross = [(a, b) for a, b in zip(pts, pts[1:]) if a[1] < 0 <= b[1]]
    if cross:
        (t0, l0), (t1, l1) = cross[-1]
        print(f"{name}: the constant crosses 0 at theta ~ {t0 + (t1 - t0) * (-l0) / (l1 - l0):.5f}")
    else:
        print(f"{name}: no crossing in the computed range")
