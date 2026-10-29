"""gen_cert.py CELLS.json OUTDIR [PCAP] [FCAP] [CCAP] [PMAX] [--tag T --L a/b --curve g --typeii X]: the Lean files of the
refined certificate (SieveCert2Defs.lean's `total2`) for the window and `n` of CELLS.json. With no options these are the
default certificate's, L = 278/125 with n = 340 (window [41556, 47531]/100000, tag 22240R, the library's);
the options only set the names and the text of the files, see below. `check_certificate.py` generates it and compares it
with `lib/pnt`. (Earlier certificates, at weaker exponents, are in the git history; this script no longer generates them.)

The kernel parts are cut by work = depth-4 tests + 2 × depth-5 tests + 4 × depth-6 tests + `sub2`'s `surelyEval` tests: a part is a range of consecutive light
rows (`rows2`), or a column piece `rowsJ2 i (i+1) j₀ j₁` of a heavy row, with at most PCAP work; a part file holds
consecutive parts with at most FCAP work in all. The bounds are ⌈1.001 × part⌉ in exact integers; the cells and costs
come from CELLS.json, mirror2.py's output for the window and `n` (`41556 47531 340` by default).

Files into OUTDIR, which must not exist or be empty: SieveGrid<T>.lean (imports SieveCert2Defs),
SieveCert<T>P1..k.lean, SieveCert<T>.lean (total2 < K, with SieveCert2's split lemmas), and, as records,
parts<t>.json, files<t>.json and modules<t>.txt (T the tag, t its lower case)."""
import json, re, sys, os, textwrap
# Options (before or after the positional arguments), for a certificate other than the default one:
#   --tag T       the files' tag (default 22240R): SieveGridT, SieveCertTP<k>, SieveCertT, `total2_lt_T`
#   --L a/b       the exponent L = a/b written in the files' text (default 278/125)
#   --curve g    the curve's name in the text (default g7d)
#   --typeii X    the Type II theorem the grid belongs to, in the text (default SieveTypeIIU22240D.typeII_22240d)
#   --rule ib     the certificate under the bilinear Type I rule of SieveRuleDefs.lean (`ibRule`, `total2R`,
#                 `rows2R`, `rowsJ2R`), from `mirror2.py --ib` (default `lim`: SieveCert2Defs.lean's `total2`)
# The window [W1, W2]/100000 and n come from CELLS.json (mirror2.py's output); without options they must be the default
# certificate's (41556, 47531, 340). Under `--rule ib` the exponent of the rule is CELLS.json's (`ib`).
DEFAULTS = {'--tag': '22240R', '--L': '278/125', '--curve': 'g7d', '--typeii': 'SieveTypeIIU22240D.typeII_22240d',
            '--rule': 'lim'}
OPTS = dict(DEFAULTS)
_args = []
_it = iter(sys.argv[1:])
for _a in _it:
    if _a in OPTS: OPTS[_a] = next(_it)
    else: _args.append(_a)
CUSTOM = OPTS != DEFAULTS
TAG, LSTR, CURVE, TYPEII, RULE = OPTS['--tag'], OPTS['--L'], OPTS['--curve'], OPTS['--typeii'], OPTS['--rule']
TAGL = TAG.lower()
assert RULE in ('lim', 'ib')
# the names under the rule: `rows2R`, `rowsJ2R`, `total2R` and their lemmas (SieveRule.lean) for `ib`
R = '' if RULE == 'lim' else 'R'
CELLS, OUT = _args[0], os.path.join(_args[1], '')
EXCL = 17000  # a part file with a part of more than EXCL work is run alone among the heavy slots
PCAP = int(_args[2]) if len(_args) > 2 else 8000
FCAP = int(_args[3]) if len(_args) > 3 else 100000
CCAP = int(_args[4]) if len(_args) > 4 else 2500
PMAX = int(_args[5]) if len(_args) > 5 else 40
os.makedirs(OUT, exist_ok=True)
assert not os.listdir(OUT), f'{OUT} is not empty'
DW = 100000
DEN = 2 ** 40; K = 2 ** 60
D = json.load(open(CELLS))
W1, W2, N = D['W1'], D['W2'], D['n']
assert CUSTOM or (W1, W2, N) == (41556, 47531, 340)
assert (RULE != 'lim') == ('ib' in D)
if RULE != 'lim':
    LNUM, LDEN = map(int, D['ib'].split('/'))
U1, U2 = (W1 * DEN + DW - 1) // DW, W2 * DEN // DW
assert D['U1'] == U1 and D['U2'] == U2
# a cell's work, in units of one depth-4 test (the subset sums of 4 boxes): the depth-5 tests (5 boxes) count 2 each, the
# depth-6 tests (6 boxes) 4, and the `sub2` tests (3 boxes) 1
def wk(t4, t5, t6, ts): return t4 + 2 * t5 + 4 * t6 + ts
# (cost2, t4, t5, t6, sub2tests), and under `ib` the weighted `ibOK` tests, which count as depth-4 tests
cells = {tuple(map(int, k.split(','))): (v[0], v[1], v[2], v[3], v[4] + (v[5] if len(v) > 5 else 0))
         for k, v in D['cells'].items()}
rows = [0] * N; work = [0] * N; cnd = [0] * N
for (i, j), (c, t4, t5, t6, ts) in cells.items():
    rows[i] += c; work[i] += wk(t4, t5, t6, ts); cnd[i] += 1
assert sum(rows) == D['total2'] < K
parts = []; a = 0; acc = 0; accC = 0
def flush(b):
    global a, acc, accC
    if b > a: parts.append(('rows', a, b, sum(work[a:b]), sum(rows[a:b])))
    a = b; acc = 0; accC = 0
for i in range(N):
    if work[i] > PCAP:
        flush(i)
        cols = sorted((j, wk(t4, t5, t6, ts), c) for (ii, j), (c, t4, t5, t6, ts) in cells.items() if ii == i)
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
           'sumB_over_K': sum(B) / K, 'heavy_rows': heavy}, open(OUT + f'parts{TAGL}.json', 'w'))
def term(p): return f'rows2{R} {p[1]} {p[2]}' if p[0] == 'rows' else f'rowsJ2{R} {p[1]} {p[1] + 1} {p[2]} {p[3]}'
rowranges = []
for p in parts:
    if p[0] == 'rows': rowranges.append((p[1], p[2]))
    elif not rowranges or rowranges[-1] != (p[1], p[1] + 1): rowranges.append((p[1], p[1] + 1))
assert rowranges[0][0] == 0 and rowranges[-1][1] == N and all(rowranges[k][1] == rowranges[k + 1][0] for k in range(len(rowranges) - 1))
chain = []; rowbound = {}
for k, p in enumerate(parts):
    if p[0] == 'rows': rowbound[(p[1], p[2])] = (f'rows{TAG}_{k}', B[k])
for i in heavy:
    ks = [k for k, p in enumerate(parts) if p[0] == 'cols' and p[1] == i]
    pcs = [parts[k] for k in ks]
    assert pcs[0][2] == 0 and pcs[-1][3] == N and all(pcs[m][3] == pcs[m + 1][2] for m in range(len(pcs) - 1))
    name = f'rows{TAG}_{ks[-1]}'; acc = B[ks[-1]]
    for m in range(len(pcs) - 2, -1, -1):
        j0 = pcs[m][2]; acc2 = acc + B[ks[m]]
        chain.append(f'theorem c{TAG}_{i}_{m} : rowsJ2{R} {i} {i + 1} {j0} {N} ≤ {acc2} :=\n'
                     f'  rowsJ2{R}_le_of_split {i} {i + 1} (by norm_num) (by norm_num) rows{TAG}_{ks[m]} {name} (by norm_num)')
        name = f'c{TAG}_{i}_{m}'; acc = acc2
    chain.append(f'theorem hr{TAG}_{i} : rows2{R} {i} {i + 1} ≤ {acc} := rows2{R}_le_of_rowsJ2{R} {i} {i + 1} {name}')
    rowbound[(i, i + 1)] = (f'hr{TAG}_{i}', acc)
name, acc = rowbound[rowranges[-1]]
for m in range(len(rowranges) - 2, -1, -1):
    x, y = rowranges[m]; hname, hb = rowbound[(x, y)]; acc2 = acc + hb
    chain.append(f'theorem t{TAG}_{m} : rows2{R} {x} {N} ≤ {acc2} :=\n'
                 f'  rows2{R}_le_of_split (by norm_num) (by norm_num) {hname} {name} (by norm_num)')
    name = f't{TAG}_{m}'; acc = acc2
assert acc == sum(B)
chain = '\n\n'.join(chain); nr = len(rowranges); FINAL = name; FINALB = acc
if RULE == 'lim':
    GRIDHEAD = f"""/-
# The grid of the refined certificate at `L = {LSTR}` with `n = {N}`

The grid of `{TYPEII}`'s window: `U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`,
`n = {N}` (`grid{TAG}`, `gridOK{TAG}`), the window of `tools/linnik/route_limits.jsonl`'s rows for `{CURVE}` at
`{LSTR}`. Its refined certificate (`SieveCert2Defs.total2`) is checked by the kernel in {np_} parts, {NF} files
(`SieveCert{TAG}P1.lean` … `SieveCert{TAG}P{NF}.lean`, one `lean` process each): ranges of consecutive rows, and the
{len(heavy)} heavy rows in column pieces (`SieveCert2Defs.rowsJ2`); assembled in `SieveCert{TAG}.lean`.

The file imports `SieveCert2Defs.lean`, which imports `SieveCertDefs.lean` only, which imports only
`Mathlib.Data.Nat.Notation` from `Mathlib`; so neither it nor the part files load the rest of `Mathlib`.
-/
import SieveCert2Defs
"""
    GRIDTAIL = ''
    INST = f'grid{TAG}'
    UNDER = ''
else:
    GRIDHEAD = f"""/-
# The grid of the refined certificate at `L = {LSTR}` with `n = {N}`, under the bilinear Type I rule

The grid of `{TYPEII}`'s window: `U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`,
`n = {N}` (`grid{TAG}`, `gridOK{TAG}`), the window `route_limits.window` and `route_limits.corners` give for `{CURVE}`
at `{LSTR}`, and the bilinear Type I rule's exponent `{LNUM}/{LDEN}` (`ibPar{TAG}`). Its refined certificate under the
rule (`SieveRuleDefs.total2R` with `ibRule`) is checked by the kernel in {np_} parts, {NF} files
(`SieveCert{TAG}P1.lean` … `SieveCert{TAG}P{NF}.lean`, one `lean` process each): ranges of consecutive rows, and the
{len(heavy)} heavy rows in column pieces (`SieveRuleDefs.rowsJ2R`); assembled in `SieveCert{TAG}.lean`.

The file imports `SieveRuleDefs.lean`, which imports `SieveCert2Defs.lean` only; so neither it nor the part files load
more of `Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import SieveRuleDefs
"""
    GRIDTAIL = f"""
/-- **The bilinear Type I rule's exponent** at `L = {LSTR}`: `{LNUM}/{LDEN}`. -/
@[instance_reducible] def ibPar{TAG} : IBPar := ⟨{LNUM}, {LDEN}⟩
"""
    INST = f'grid{TAG} ibPar{TAG} ibRule'
    UNDER = ', under the bilinear Type I rule'
grid = GRIDHEAD + f"""
namespace SieveCert

/-- **The grid at `L = {LSTR}` with `n = {N}`**: `U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`,
multiplier `1`. -/
@[instance_reducible] def grid{TAG} : Grid := ⟨({W1} * DEN + {DW - 1}) / {DW}, {W2} * DEN / {DW}, {N}, 1⟩

theorem gridOK{TAG} : @GridOK grid{TAG} :=
  @GridOK.mk grid{TAG} (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The coarse grid `Gc` (`n / 4 = {N // 4}` cells) and the facts about it that the deepest levels use. -/
theorem gridOKC{TAG} : @GridOKC grid{TAG} :=
  @GridOKC.mk grid{TAG}
    (@GridOK.mk (@Gc grid{TAG}) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide) (by decide)
{GRIDTAIL}
end SieveCert

#print axioms SieveCert.gridOK{TAG}
#print axioms SieveCert.gridOKC{TAG}
"""
open(OUT + f'SieveGrid{TAG}.lean', 'w', encoding='utf-8').write(grid)
for fi, g in enumerate(groups, 1):
    lem = '\n\n'.join(f'theorem rows{TAG}_{k} : {term(parts[k])} ≤ {B[k]} := by decide +kernel' for k in g)
    desc = ', '.join(f'rows {parts[k][1]}–{parts[k][2] - 1}' if parts[k][0] == 'rows' else
                     f'row {parts[k][1]} columns {parts[k][2]}–{parts[k][3] - 1}' for k in g)
    desc = textwrap.fill(f'`SieveGrid{TAG}.grid{TAG}` ({len(g)} parts, work {gt[fi - 1]} in units of a depth-4 test: {desc}), each a sum of refined '
                         f'costs (`rows2{R}` or `rowsJ2{R}`) at most its bound, by `decide +kernel`, one at a time '
                         f'(`Elab.async false`).', width=116)
    excl = ('-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts\n'
            if max(parts[k][-2] for k in g) > EXCL else '')
    part = f"""/-
# The refined certificate at `L = {LSTR}` with `n = {N}`{UNDER}, parts {g[0]}–{g[-1]} of {np_}

File {fi} of {NF}: the parts `rows{TAG}_{g[0]}` … `rows{TAG}_{g[-1]}` of `SieveCert{TAG}.lean`'s certificate on
{desc}

The file imports `SieveGrid{TAG}.lean`.
-/
import SieveGrid{TAG}
{excl}
/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] {INST}

{lem}

end

end SieveCert

#print axioms SieveCert.rows{TAG}_{g[0]}
""" + (f"#print axioms SieveCert.rows{TAG}_{g[-1]}\n" if len(g) > 1 else '')
    open(OUT + f'SieveCert{TAG}P{fi}.lean', 'w', encoding='utf-8').write(part)
imports_parts = '\n'.join(f'import SieveCert{TAG}P{fi}' for fi in range(1, NF + 1))
ONRULE = '' if RULE == 'lim' else f' under `ibRule` (`ibPar{TAG}`, `L = {LNUM}/{LDEN}`)'
WITHOUT = ('the certificate of `SieveCertDefs.lean` on the same grid' if RULE == 'lim' else
           'without the kept parts the certificate under the rule')
EQ = 'SieveCert2.total2_eq_rows2_full' if RULE == 'lim' else 'SieveRule.total2R_eq_rows2R_full'
cert_head = textwrap.fill(f"On `SieveGrid{TAG}.grid{TAG}` (`U1 = ⌈({W1}/{DW})DEN⌉`, `U2 = ⌊({W2}/{DW})DEN⌋`, `n = {N}`){ONRULE}, "
    f"`SieveCert.total2{R}` is less than `K` (it is below `{-(-D['total2'] * 10 ** 5 // K) / 10 ** 5:.5f}K`, rounded up; {WITHOUT} "
    f"totals `{D['total'] / K:.5f}K`): `total2{R}` is `rows2{R} 0 n` (`{EQ}`), "
    f"and its bound is assembled one step at a time from the {np_} parts' bounds (`rows{TAG}_0` … `rows{TAG}_{np_ - 1}`, "
    f"each by `decide +kernel` in one of the {NF} part files): a heavy row's bound from its column pieces' "
    f"(`rowsJ2{R}_le_of_split`, `rows2{R}_le_of_rowsJ2{R}`), then the {nr} ranges of rows from the last to the first "
    f"(`rows2{R}_le_of_split`), every bound a literal and every step a theorem of its own (`c{TAG}_…`, `hr{TAG}_…`, `t{TAG}_…`); the bounds, "
    f"`⌈1.001 × part⌉` computed exactly in integers, sum to `{FINALB}`, less than `K` by `decide +kernel` "
    f"(`total2{R}_lt_{TAG}`).", width=116)
cert = f"""/-
# The refined certificate of the sieve route's loss at `L = {LSTR}` with `n = {N}`{UNDER}: `total2{R} < K`

{cert_head}

The file imports `{'SieveCert2' if RULE == 'lim' else 'SieveRule'}.lean` and `SieveCert{TAG}P1.lean` … `SieveCert{TAG}P{NF}.lean`.
-/
import {'SieveCert2' if RULE == 'lim' else 'SieveRule'}
{imports_parts}

namespace SieveCert

section

attribute [local instance] {INST}

/-! The chain of bounds: `c{TAG}_{{i}}_{{m}}` for the heavy row `i` from its `m`-th column piece on, `hr{TAG}_{{i}}` for
the heavy row `i`, `t{TAG}_{{m}}` for the rows from the `m`-th range on; each a theorem of its own, its name distinct
from the other certificates' chains in the same namespace. -/

{chain}

/-- **The refined certificate on `grid{TAG}`**: the loss's bound is less than `K`, the {np_} parts checked by the
kernel. -/
theorem total2{R}_lt_{TAG} : total2{R} < K := by
  rw [total2{R}_eq_rows2{R}_full]
  exact lt_of_le_of_lt {FINAL} (by decide +kernel)

end

end SieveCert

#print axioms SieveCert.total2{R}_lt_{TAG}
"""
open(OUT + f'SieveCert{TAG}.lean', 'w', encoding='utf-8').write(cert)
bad = []
for f in [f'SieveGrid{TAG}'] + [f'SieveCert{TAG}P{i}' for i in range(1, NF + 1)] + [f'SieveCert{TAG}']:
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
    man.append(dict(file=f'SieveCert{TAG}P{fi}', parts=len(g), work=T, maxpart=mt, cands=C,
                    peak=round(2.5 + 0.29 * mt / 1000, 1), secs=round(T / 1500 + 5)))
json.dump(man, open(OUT + f'files{TAGL}.json', 'w'))
print(f'predicted: kernel time one lane {sum(m["secs"] for m in man) / 3600:.2f} h; parts {np_}, files {NF}, '
      f'largest cands per part {max(pcands(p) for p in parts)}')
open(OUT + f'modules{TAGL}.txt', 'w').write(' '.join(['SieveCert2Defs'] + ([] if RULE == 'lim' else ['SieveRuleDefs']) +
    [f'SieveGrid{TAG}'] +
    [f'SieveCert{TAG}P{i}' for i in range(1, NF + 1)]) + '\n')
