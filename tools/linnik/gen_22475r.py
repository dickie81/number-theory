"""gen_22475r.py CELLS.json OUTDIR [PCAP] [FCAP] [CCAP] [PMAX]: the Lean files of the refined certificate at
L = 899/400 with n = 300 (SieveCert2Defs.lean's `total2`).

The kernel parts are cut by work = depth-4 tests + `sub2`'s `surelyEval` tests: a part is a range of consecutive light
rows (`rows2`), or a column piece `rowsJ2 i (i+1) j₀ j₁` of a heavy row, with at most PCAP work; a part file holds
consecutive parts with at most FCAP work in all. The bounds are ⌈1.001 × part⌉ in exact integers; the cells and costs
come from CELLS.json, mirror2.py's output for `41335 48069 300`.

Files into OUTDIR, which must not exist or be empty: SieveGrid22475R.lean (imports SieveCert2Defs),
SieveCert22475RP1..k.lean, SieveCert22475R.lean (total2 < K, with SieveCert2's split lemmas), and, as records,
parts22475r.json, files22475r.json and modules22475r.txt."""
import json, re, sys, os, textwrap
CELLS, OUT = sys.argv[1], os.path.join(sys.argv[2], '')
PCAP = int(sys.argv[3]) if len(sys.argv) > 3 else 8000
FCAP = int(sys.argv[4]) if len(sys.argv) > 4 else 30000
CCAP = int(sys.argv[5]) if len(sys.argv) > 5 else 2500
PMAX = int(sys.argv[6]) if len(sys.argv) > 6 else 10
os.makedirs(OUT, exist_ok=True)
assert not os.listdir(OUT), f'{OUT} is not empty'
W1, W2, DW, N = 41335, 48069, 100000, 300
DEN = 2 ** 40; K = 2 ** 60
D = json.load(open(CELLS))
assert D['n'] == N and D['W1'] == W1 and D['W2'] == W2
U1, U2 = (W1 * DEN + DW - 1) // DW, W2 * DEN // DW
assert D['U1'] == U1 and D['U2'] == U2
cells = {tuple(map(int, k.split(','))): tuple(v) for k, v in D['cells'].items()}  # (cost2, tests4, sub2tests)
rows = [0] * N; work = [0] * N; cnd = [0] * N
for (i, j), (c, t4, ts) in cells.items():
    rows[i] += c; work[i] += t4 + ts; cnd[i] += 1
assert sum(rows) == D['total2'] < K
parts = []; a = 0; acc = 0; accC = 0
def flush(b):
    global a, acc, accC
    if b > a: parts.append(('rows', a, b, sum(work[a:b]), sum(rows[a:b])))
    a = b; acc = 0; accC = 0
for i in range(N):
    if work[i] > PCAP:
        flush(i)
        cols = sorted((j, t4 + ts, c) for (ii, j), (c, t4, ts) in cells.items() if ii == i)
        j0 = 0; tt = 0; cc = 0; pieces = []
        for j, t, c in cols:
            if tt + t > PCAP and tt > 0:
                pieces.append((j0, j, tt, cc)); j0 = j; tt = 0; cc = 0
            tt += t; cc += c
        pieces.append((j0, N, tt, cc))
        assert sum(p[3] for p in pieces) == rows[i] and sum(p[2] for p in pieces) == work[i]
        for j0, j1, tt, cc in pieces: parts.append(('cols', i, j0, j1, tt, cc))
        a = i + 1; acc = 0; accC = 0
        continue
    if (acc + work[i] > PCAP or accC + cnd[i] > CCAP) and i > a: flush(i)
    acc += work[i]; accC += cnd[i]
flush(N)
assert sum(p[-1] for p in parts) == D['total2']
B = [(1001 * p[-1] + 999) // 1000 for p in parts]
assert all(b >= p[-1] and 1000 * b >= 1001 * p[-1] > 1000 * (b - 1) for b, p in zip(B, parts)) and sum(B) < K
np_ = len(parts); heavy = sorted({p[1] for p in parts if p[0] == 'cols'})
groups, g, acc = [], [], 0
for k, p in enumerate(parts):
    t = p[-2]
    if g and (acc + t > FCAP or len(g) >= PMAX): groups.append(g); g, acc = [], 0
    g.append(k); acc += t
if g: groups.append(g)
NF = len(groups)
gt = [sum(parts[k][-2] for k in g) for g in groups]
print(f'parts {np_} ({sum(1 for p in parts if p[0] == "rows")} row ranges, {sum(1 for p in parts if p[0] == "cols")} '
      f'column pieces of {len(heavy)} heavy rows); files {NF}; work per file max {max(gt)}, min {min(gt)}; '
      f'sum B / K = {sum(B) / K:.5f}; exact total2 / K = {D["total2"] / K:.10f}')
json.dump({'n': N, 'pcap': PCAP, 'fcap': FCAP, 'parts': parts, 'bounds': B, 'files': groups, 'work_per_file': gt,
           'sumB_over_K': sum(B) / K, 'heavy_rows': heavy}, open(OUT + 'parts22475r.json', 'w'))
def term(p): return f'rows2 {p[1]} {p[2]}' if p[0] == 'rows' else f'rowsJ2 {p[1]} {p[1] + 1} {p[2]} {p[3]}'
rowranges = []
for p in parts:
    if p[0] == 'rows': rowranges.append((p[1], p[2]))
    elif not rowranges or rowranges[-1] != (p[1], p[1] + 1): rowranges.append((p[1], p[1] + 1))
assert rowranges[0][0] == 0 and rowranges[-1][1] == N and all(rowranges[k][1] == rowranges[k + 1][0] for k in range(len(rowranges) - 1))
chain = []; rowbound = {}
for k, p in enumerate(parts):
    if p[0] == 'rows': rowbound[(p[1], p[2])] = (f'rows22475R_{k}', B[k])
for i in heavy:
    ks = [k for k, p in enumerate(parts) if p[0] == 'cols' and p[1] == i]
    pcs = [parts[k] for k in ks]
    assert pcs[0][2] == 0 and pcs[-1][3] == N and all(pcs[m][3] == pcs[m + 1][2] for m in range(len(pcs) - 1))
    name = f'rows22475R_{ks[-1]}'; acc = B[ks[-1]]
    for m in range(len(pcs) - 2, -1, -1):
        j0 = pcs[m][2]; acc2 = acc + B[ks[m]]
        chain.append(f'theorem c22475R_{i}_{m} : rowsJ2 {i} {i + 1} {j0} {N} ≤ {acc2} :=\n'
                     f'  rowsJ2_le_of_split {i} {i + 1} (by norm_num) (by norm_num) rows22475R_{ks[m]} {name} (by norm_num)')
        name = f'c22475R_{i}_{m}'; acc = acc2
    chain.append(f'theorem hr22475R_{i} : rows2 {i} {i + 1} ≤ {acc} := rows2_le_of_rowsJ2 {i} {i + 1} {name}')
    rowbound[(i, i + 1)] = (f'hr22475R_{i}', acc)
name, acc = rowbound[rowranges[-1]]
for m in range(len(rowranges) - 2, -1, -1):
    x, y = rowranges[m]; hname, hb = rowbound[(x, y)]; acc2 = acc + hb
    chain.append(f'theorem t22475R_{m} : rows2 {x} {N} ≤ {acc2} :=\n'
                 f'  rows2_le_of_split (by norm_num) (by norm_num) {hname} {name} (by norm_num)')
    name = f't22475R_{m}'; acc = acc2
assert acc == sum(B)
chain = '\n\n'.join(chain); nr = len(rowranges); FINAL = name; FINALB = acc
grid = f"""/-
# The grid of the refined certificate at `L = 899/400` with `n = {N}`

The grid of `SieveTypeIIU22475C.typeII_22475c`'s window: `U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`,
`n = {N}` (`grid22475R`, `gridOK22475R`), the window of `tools/linnik/route_limits.jsonl`'s rows for `g7c` at
`899/400`. Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in {np_} parts, {NF} files
(`SieveCert22475RP1.lean` … `SieveCert22475RP{NF}.lean`, one `lean` process each): ranges of consecutive rows, and the
{len(heavy)} heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert22475R.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, so neither it nor the part files load
`Mathlib`.
-/
import SieveCert2Defs

namespace SieveCert

/-- **The grid at `L = 899/400` with `n = {N}`**: `U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`. -/
@[instance_reducible] def grid22475R : Grid := ⟨({W1} * DEN + {DW - 1}) / {DW}, {W2} * DEN / {DW}, {N}⟩

theorem gridOK22475R : @GridOK grid22475R :=
  @GridOK.mk grid22475R (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end SieveCert

#print axioms SieveCert.gridOK22475R
"""
open(OUT + 'SieveGrid22475R.lean', 'w', encoding='utf-8').write(grid)
for fi, g in enumerate(groups, 1):
    lem = '\n\n'.join(f'theorem rows22475R_{k} : {term(parts[k])} ≤ {B[k]} := by decide +kernel' for k in g)
    desc = ', '.join(f'rows {parts[k][1]}–{parts[k][2] - 1}' if parts[k][0] == 'rows' else
                     f'row {parts[k][1]} columns {parts[k][2]}–{parts[k][3] - 1}' for k in g)
    desc = textwrap.fill(f'`SieveGrid22475R.grid22475R` ({len(g)} parts, {gt[fi - 1]} tests: {desc}), each a sum of refined '
                         f'costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time '
                         f'(`Elab.async false`).', width=116)
    part = f"""/-
# The refined certificate at `L = 899/400` with `n = {N}`, parts {g[0]}–{g[-1]} of {np_}

File {fi} of {NF}: the parts `rows22475R_{g[0]}` … `rows22475R_{g[-1]}` of `SieveCert22475R.lean`'s certificate on
{desc}

The file imports `SieveGrid22475R.lean`.
-/
import SieveGrid22475R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22475R

{lem}

end

end SieveCert

#print axioms SieveCert.rows22475R_{g[0]}
""" + (f"#print axioms SieveCert.rows22475R_{g[-1]}\n" if len(g) > 1 else '')
    open(OUT + f'SieveCert22475RP{fi}.lean', 'w', encoding='utf-8').write(part)
imports_parts = '\n'.join(f'import SieveCert22475RP{fi}' for fi in range(1, NF + 1))
cert_head = textwrap.fill(f"On `SieveGrid22475R.grid22475R` (`U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`, `n = {N}`), "
    f"`SieveCert.total2` is less than `K` (it is below `{-(-D['total2'] * 10 ** 5 // K) / 10 ** 5:.5f}K`, rounded up; the certificate of `SieveCertDefs.lean` "
    f"on the same grid totals `{D['total'] / K:.5f}K`): `total2` is `rows2 0 n` (`SieveCert2.total2_eq_rows2_full`), "
    f"and its bound is assembled one step at a time from the {np_} parts' bounds (`rows22475R_0` … `rows22475R_{np_ - 1}`, "
    f"each by `decide +kernel` in one of the {NF} part files): a heavy row's bound from its column pieces' "
    f"(`rowsJ2_le_of_split`, `rows2_le_of_rowsJ2`), then the {nr} ranges of rows from the last to the first "
    f"(`rows2_le_of_split`), every bound a literal and every step a theorem of its own (`c22475R_…`, `hr22475R_…`, `t22475R_…`); the bounds, "
    f"`⌈1.001 × part⌉` computed exactly in integers, sum to `{FINALB}`, less than `K` by `decide +kernel` "
    f"(`total2_lt_22475R`).", width=116)
cert = f"""/-
# The refined certificate of the sieve route's loss at `L = 899/400` with `n = {N}`: `total2 < K`

{cert_head}

The file imports `SieveCert2.lean` and `SieveCert22475RP1.lean` … `SieveCert22475RP{NF}.lean`.
-/
import SieveCert2
{imports_parts}

namespace SieveCert

section

attribute [local instance] grid22475R

/-! The chain of bounds: `c22475R_{{i}}_{{m}}` for the heavy row `i` from its `m`-th column piece on, `hr22475R_{{i}}` for
the heavy row `i`, `t22475R_{{m}}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from the other certificates' chains in the same namespace. -/

{chain}

/-- **The refined certificate on `grid22475R`**: the loss's bound is less than `K`, the {np_} parts checked by the
kernel. -/
theorem total2_lt_22475R : total2 < K := by
  rw [total2_eq_rows2_full]
  exact lt_of_le_of_lt {FINAL} (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2_lt_22475R
"""
open(OUT + 'SieveCert22475R.lean', 'w', encoding='utf-8').write(cert)
bad = []
for f in ['SieveGrid22475R'] + [f'SieveCert22475RP{i}' for i in range(1, NF + 1)] + ['SieveCert22475R']:
    s = open(OUT + f + '.lean', encoding='utf-8').read()
    long = [i for i, l in enumerate(s.split('\n'), 1) if len(l) > 120]
    if long: bad.append((f, long))
print('files', NF + 2, 'long lines', bad)
def pcands(p):
    if p[0] == 'rows': return sum(cnd[p[1]:p[2]])
    return sum(1 for (ii, j) in cells if ii == p[1] and p[2] <= j < p[3])
man = []
for fi, g in enumerate(groups, 1):
    mt = max(parts[k][-2] for k in g); T = sum(parts[k][-2] for k in g); C = sum(pcands(parts[k]) for k in g)
    man.append(dict(file=f'SieveCert22475RP{fi}', parts=len(g), work=T, maxpart=mt, cands=C,
                    peak=round(2.02 + 0.2237 * mt / 1000, 2), secs=round(T / 180)))
json.dump(man, open(OUT + 'files22475r.json', 'w'))
print(f'predicted: kernel time one lane {sum(m["secs"] for m in man) / 3600:.2f} h; parts {np_}, files {NF}, '
      f'largest cands per part {max(pcands(p) for p in parts)}')
open(OUT + 'modules22475r.txt', 'w').write(' '.join(['SieveCert2Defs', 'SieveGrid22475R'] +
    [f'SieveCert22475RP{i}' for i in range(1, NF + 1)]) + '\n')
