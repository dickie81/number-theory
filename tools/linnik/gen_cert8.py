"""gen_cert8.py CELLS.json OUTDIR [--tag T] [--curve g] [--typeii X] [--cap S] [--fcap S] [--pmax P]: the Lean files of
the certificate to depth 8 (SieveDeepDefs.lean's `totalD`) for the window, `n` and `L` of CELLS.json, `mirror8.py`'s
output. With no options these are the library's, L = 11/5 with n = 272 (window [43457, 46959]/100000, tag 22000E);
`check_certificate.py 22000E` generates them and compares them with `lib/pnt`.

The parts are cut by the kernel's time as predicted from each candidate cell's work in CELLS.json (`mirror8.WORK`),
`T = 0.0525 + 0.00226·c4 + 0.0000807·b5 + 0.000332·t6 + 0.00798·t3` seconds, a least-squares fit to the kernel's checks
of seventeen parts across the grid (an error of at most six seconds, on parts of twenty to a hundred seconds); the
kernel's memory grows with its time, about 1 GB and 0.053 GB a second. A part is a range of consecutive light rows,
`rowsJD a b 0 n`, or a column piece `rowsJD i (i + 1) j₀ j₁` of a heavy row, with a predicted time of at most CAP
seconds (default 30); a part file holds consecutive parts, at most PMAX of them (default 10) and FCAP predicted seconds
(default 300) in all. The bounds are ⌈1.001 × part⌉ in exact integers.

Files into OUTDIR, which must not exist or be empty: SieveGrid<T>.lean (imports SieveDeepDefs), SieveCert<T>P1..k.lean,
SieveCert<T>.lean (`totalD < K`, with SieveDeepCert's split lemmas), and, as records, parts<t>.json, files<t>.json and
modules<t>.txt (T the tag, t its lower case)."""
import json
import os
import sys
import textwrap

DEFAULTS = {'--tag': '22000E', '--curve': 'g7d', '--typeii': 'SieveTypeIIU22000D.typeII_22000d', '--cap': '30',
            '--fcap': '300', '--pmax': '10'}
OPTS = dict(DEFAULTS)
_args = []
_it = iter(sys.argv[1:])
for _a in _it:
    if _a in OPTS:
        OPTS[_a] = next(_it)
    else:
        _args.append(_a)
CUSTOM = {k: v for k, v in OPTS.items() if k in ('--tag', '--curve', '--typeii')} != \
    {k: v for k, v in DEFAULTS.items() if k in ('--tag', '--curve', '--typeii')}
TAG, CURVE, TYPEII = OPTS['--tag'], OPTS['--curve'], OPTS['--typeii']
CAP, FCAP, PMAX = float(OPTS['--cap']), float(OPTS['--fcap']), int(OPTS['--pmax'])
TAGL = TAG.lower()
CELLS, OUT = _args[0], os.path.join(_args[1], '')
os.makedirs(OUT, exist_ok=True)
assert not os.listdir(OUT), f'{OUT} is not empty'
DW = 100000
DEN = 2 ** 40
K = 2 ** 60
D = json.load(open(CELLS))
W1, W2, N, LSTR = D['W1'], D['W2'], D['n'], D['L']
assert CUSTOM or (W1, W2, N, LSTR) == (43457, 46959, 272, '11/5')
assert D['rows'] == [0, N], 'CELLS.json must hold every row'
LNUM, LDEN = map(int, LSTR.split('/'))
LTXT = f'{LNUM}/{LDEN}'
U1, U2 = (W1 * DEN + DW - 1) // DW, W2 * DEN // DW
assert D['U1'] == U1 and D['U2'] == U2
assert D['work'] == ['t3', 'c3', 'c4', 'p4', 'm4', 'b5', 't6']


def secs(v):
    """The predicted kernel time of a candidate cell `[cost, dec, t3, c3, c4, p4, m4, b5, t6]`, in seconds."""
    return 0.0525 + 0.00226 * v[4] + 0.0000807 * v[7] + 0.000332 * v[8] + 0.00798 * v[2]


cells = {tuple(map(int, k.split(','))): (v[0], secs(v)) for k, v in D['cells'].items()}
rows = [0] * N
work = [0.0] * N
for (i, j), (c, t) in cells.items():
    rows[i] += c
    work[i] += t
assert sum(rows) == D['totalD'] < K
# the parts: ('rows', a, b, secs, value) or ('cols', i, j0, j1, secs, value)
parts = []
a = 0
acc = 0.0


def flush(b):
    global a, acc
    if b > a:
        parts.append(('rows', a, b, sum(work[a:b]), sum(rows[a:b])))
    a = b
    acc = 0.0


for i in range(N):
    if work[i] > CAP:
        flush(i)
        cs = sorted((j, t, c) for (ii, j), (c, t) in cells.items() if ii == i)
        j0, tt, cc, pieces = 0, 0.0, 0, []
        for j, t, c in cs:
            if tt + t > CAP and tt > 0:
                pieces.append((j0, j, tt, cc))
                j0, tt, cc = j, 0.0, 0
            tt += t
            cc += c
        pieces.append((j0, N, tt, cc))
        assert sum(p[3] for p in pieces) == rows[i]
        for j0, j1, tt, cc in pieces:
            parts.append(('cols', i, j0, j1, tt, cc))
        a = i + 1
        acc = 0.0
        continue
    if acc + work[i] > CAP and i > a:
        flush(i)
    acc += work[i]
flush(N)
assert sum(p[-1] for p in parts) == D['totalD']
B = [(1001 * p[-1] + 999) // 1000 for p in parts]
assert all(b >= p[-1] and 1000 * b >= 1001 * p[-1] > 1000 * (b - 1) for b, p in zip(B, parts)) and sum(B) < K
np_ = len(parts)
heavy = sorted({p[1] for p in parts if p[0] == 'cols'})
groups, g, acc = [], [], 0.0
for k, p in enumerate(parts):
    t = p[-2]
    if g and (acc + t > FCAP or len(g) >= PMAX):
        groups.append(g)
        g, acc = [], 0.0
    g.append(k)
    acc += t
if g:
    groups.append(g)
NF = len(groups)
gt = [sum(parts[k][-2] for k in g) for g in groups]
print(f'parts {np_} ({sum(1 for p in parts if p[0] == "rows")} row ranges, '
      f'{sum(1 for p in parts if p[0] == "cols")} column pieces of {len(heavy)} heavy rows); files {NF}; '
      f'predicted seconds per part max {max(p[-2] for p in parts):.1f}, per file max {max(gt):.0f}, '
      f'in all {sum(gt) / 3600:.2f} h; sum B / K = {sum(B) / K:.6f}; exact totalD / K = {D["totalD"] / K:.10f}')
json.dump({'n': N, 'cap': CAP, 'fcap': FCAP, 'pmax': PMAX, 'parts': parts, 'bounds': B, 'files': groups,
           'secs_per_file': gt, 'sumB_over_K': sum(B) / K, 'heavy_rows': heavy}, open(OUT + f'parts{TAGL}.json', 'w'))


def term(p):
    return f'rowsJD {p[1]} {p[2]} 0 {N}' if p[0] == 'rows' else f'rowsJD {p[1]} {p[1] + 1} {p[2]} {p[3]}'


rowranges = []
for p in parts:
    if p[0] == 'rows':
        rowranges.append((p[1], p[2]))
    elif not rowranges or rowranges[-1] != (p[1], p[1] + 1):
        rowranges.append((p[1], p[1] + 1))
assert rowranges[0][0] == 0 and rowranges[-1][1] == N
assert all(rowranges[k][1] == rowranges[k + 1][0] for k in range(len(rowranges) - 1))
chain = []
rowbound = {}
for k, p in enumerate(parts):
    if p[0] == 'rows':
        rowbound[(p[1], p[2])] = (f'rows{TAG}_{k}', B[k])
for i in heavy:
    ks = [k for k, p in enumerate(parts) if p[0] == 'cols' and p[1] == i]
    pcs = [parts[k] for k in ks]
    assert pcs[0][2] == 0 and pcs[-1][3] == N and all(pcs[m][3] == pcs[m + 1][2] for m in range(len(pcs) - 1))
    name = f'rows{TAG}_{ks[-1]}'
    acc = B[ks[-1]]
    for m in range(len(pcs) - 2, -1, -1):
        j0 = pcs[m][2]
        acc2 = acc + B[ks[m]]
        chain.append(f'theorem c{TAG}_{i}_{m} : rowsJD {i} {i + 1} {j0} {N} ≤ {acc2} :=\n'
                     f'  rowsJD_le_of_splitJ {i} {i + 1} (by norm_num) (by norm_num) rows{TAG}_{ks[m]} {name} '
                     f'(by norm_num)')
        name = f'c{TAG}_{i}_{m}'
        acc = acc2
    rowbound[(i, i + 1)] = (name, acc)
name, acc = rowbound[rowranges[-1]]
for m in range(len(rowranges) - 2, -1, -1):
    x, y = rowranges[m]
    hname, hb = rowbound[(x, y)]
    acc2 = acc + hb
    chain.append(f'theorem t{TAG}_{m} : rowsJD {x} {N} 0 {N} ≤ {acc2} :=\n'
                 f'  rowsJD_le_of_splitI 0 {N} (by norm_num) (by norm_num) {hname} {name} (by norm_num)')
    name = f't{TAG}_{m}'
    acc = acc2
assert acc == sum(B)
chain = '\n\n'.join(chain)
nr = len(rowranges)
FINAL, FINALB = name, acc
INST = f'grid{TAG} ibPar{TAG}'
grid_head = textwrap.fill(
    f"The grid of `{TYPEII}`'s window: `U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`, `n = {N}` (`grid{TAG}`, "
    f"`gridOK{TAG}`, `gridOKC{TAG}`), the window `route_limits.window` and `route_limits.corners` give for `{CURVE}` "
    f"at `{LTXT}`, and the bilinear Type I rule's exponent `{LTXT}` (`ibPar{TAG}`). Its certificate to depth 8 "
    f"(`SieveDeepDefs.totalD`) is checked by the kernel in {np_} parts, {NF} files (`SieveCert{TAG}P1.lean` … "
    f"`SieveCert{TAG}P{NF}.lean`, one `lean` process each): ranges of consecutive rows, and the {len(heavy)} heavy "
    f"rows in column pieces (`SieveDeepDefs.rowsJD`); assembled in `SieveCert{TAG}.lean`.", width=116)
grid = f"""/-
# The grid of the certificate to depth 8 at `L = {LTXT}` with `n = {N}`

{grid_head}

The file imports `SieveDeepDefs.lean`, which imports `SieveRuleDefs.lean` only; so neither it nor the part files load
more of `Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import SieveDeepDefs

namespace SieveCert

/-- **The grid at `L = {LTXT}` with `n = {N}`**: `U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`,
multiplier `1`. -/
@[instance_reducible] def grid{TAG} : Grid := ⟨({W1} * DEN + {DW - 1}) / {DW}, {W2} * DEN / {DW}, {N}, 1⟩

theorem gridOK{TAG} : @GridOK grid{TAG} :=
  @GridOK.mk grid{TAG} (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The coarse grid `Gc` (`n / 4 = {N // 4}` cells) and the facts about it that the deepest levels use. -/
theorem gridOKC{TAG} : @GridOKC grid{TAG} :=
  @GridOKC.mk grid{TAG}
    (@GridOK.mk (@Gc grid{TAG}) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide)

/-- **The bilinear Type I rule's exponent** at `L = {LTXT}`: `{LNUM}/{LDEN}`. -/
@[instance_reducible] def ibPar{TAG} : IBPar := ⟨{LNUM}, {LDEN}⟩

end SieveCert

#print axioms SieveCert.gridOK{TAG}
#print axioms SieveCert.gridOKC{TAG}
"""
open(OUT + f'SieveGrid{TAG}.lean', 'w', encoding='utf-8').write(grid)
for fi, g in enumerate(groups, 1):
    lem = '\n\n'.join(f'theorem rows{TAG}_{k} : {term(parts[k])} ≤ {B[k]} := by decide +kernel' for k in g)
    desc = ', '.join(f'rows {parts[k][1]}–{parts[k][2] - 1}' if parts[k][0] == 'rows' else
                     f'row {parts[k][1]} columns {parts[k][2]}–{parts[k][3] - 1}' for k in g)
    desc = textwrap.fill(f'`SieveGrid{TAG}.grid{TAG}` ({len(g)} parts, predicted {gt[fi - 1]:.0f} s of the kernel: '
                         f'{desc}), each a sum of the costs (`rowsJD`) at most its bound, by `decide +kernel`, '
                         f'one at a time (`Elab.async false`).', width=116)
    part = f"""/-
# The certificate to depth 8 at `L = {LTXT}` with `n = {N}`, parts {g[0]}–{g[-1]} of {np_}

File {fi} of {NF}: the parts `rows{TAG}_{g[0]}` … `rows{TAG}_{g[-1]}` of `SieveCert{TAG}.lean`'s certificate on
{desc}

The file imports `SieveGrid{TAG}.lean`.
-/
import SieveGrid{TAG}

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveDeep

open SieveCert

section

attribute [local instance] {INST}

{lem}

end

end SieveDeep

#print axioms SieveDeep.rows{TAG}_{g[0]}
""" + (f"#print axioms SieveDeep.rows{TAG}_{g[-1]}\n" if len(g) > 1 else '')
    open(OUT + f'SieveCert{TAG}P{fi}.lean', 'w', encoding='utf-8').write(part)
imports_parts = '\n'.join(f'import SieveCert{TAG}P{fi}' for fi in range(1, NF + 1))
cert_head = textwrap.fill(
    f"On `SieveGrid{TAG}.grid{TAG}` (`U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`, `n = {N}`) under `ibRule` "
    f"(`ibPar{TAG}`, `L = {LTXT}`), `SieveDeep.totalD` is less than `K` (it is below "
    f"`{-(-D['totalD'] * 10 ** 5 // K) / 10 ** 5:.5f}K`, rounded up): `totalD` is `rowsJD 0 n 0 n` "
    f"(`SieveDeep.totalD_eq_rowsJD`), and its bound is assembled one step at a time from the {np_} parts' bounds "
    f"(`rows{TAG}_0` … `rows{TAG}_{np_ - 1}`, each by `decide +kernel` in one of the {NF} part files): a heavy row's "
    f"bound from its column pieces' (`rowsJD_le_of_splitJ`), then the {nr} ranges of rows from the last to the first "
    f"(`rowsJD_le_of_splitI`), every bound a literal and every step a theorem of its own (`c{TAG}_…`, `t{TAG}_…`); "
    f"the bounds, `⌈1.001 × part⌉` computed exactly in integers, sum to `{FINALB}`, less than `K` by "
    f"`decide +kernel` (`totalD_lt_{TAG}`).", width=116)
cert = f"""/-
# The certificate to depth 8 of the sieve route's loss at `L = {LTXT}` with `n = {N}`: `totalD < K`

{cert_head}

The file imports `SieveDeepCert.lean` and `SieveCert{TAG}P1.lean` … `SieveCert{TAG}P{NF}.lean`.
-/
import SieveDeepCert
{imports_parts}

namespace SieveDeep

open SieveCert

section

attribute [local instance] {INST}

/-! The chain of bounds: `c{TAG}_{{i}}_{{m}}` for the heavy row `i` from its `m`-th column piece on, `t{TAG}_{{m}}` for
the rows from the `m`-th range on; each a theorem of its own. -/

{chain}

/-- **The certificate to depth 8 on `grid{TAG}`**: the loss's bound is less than `K`, the {np_} parts checked by the
kernel. -/
theorem totalD_lt_{TAG} : totalD < K := by
  rw [totalD_eq_rowsJD]
  exact lt_of_le_of_lt {FINAL} (by decide +kernel)

end

end SieveDeep

#print axioms SieveDeep.totalD_lt_{TAG}
"""
open(OUT + f'SieveCert{TAG}.lean', 'w', encoding='utf-8').write(cert)
bad = []
for f in [f'SieveGrid{TAG}'] + [f'SieveCert{TAG}P{i}' for i in range(1, NF + 1)] + [f'SieveCert{TAG}']:
    s = open(OUT + f + '.lean', encoding='utf-8').read()
    long = [i for i, line in enumerate(s.split('\n'), 1) if len(line) > 120]
    if long:
        bad.append((f, long))
print('files', NF + 2, 'long lines', bad)
man = [dict(file=f'SieveCert{TAG}P{fi}', parts=len(g), secs=round(gt[fi - 1]),
            maxpart=round(max(parts[k][-2] for k in g), 1),
            peak=round(1.0 + 0.053 * max(parts[k][-2] for k in g), 1)) for fi, g in enumerate(groups, 1)]
json.dump(man, open(OUT + f'files{TAGL}.json', 'w'))
open(OUT + f'modules{TAGL}.txt', 'w').write(' '.join(['SieveDeepDefs', f'SieveGrid{TAG}'] +
                                                      [f'SieveCert{TAG}P{i}' for i in range(1, NF + 1)]) + '\n')
