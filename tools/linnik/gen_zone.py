#!/usr/bin/env python3
"""The Type II estimate in two variables: the curve `ghx` (`lib/pnt/SieveCurveHx.lean`) and its zone
(`lib/pnt/SieveTwoZone7D.lean`).

    python3 tools/linnik/gen_zone.py            write the two Lean files
    python3 tools/linnik/gen_zone.py --check    fail if a file on disk differs from what would be written
    python3 tools/linnik/gen_zone.py --exact    the exact zone against the region, on a grid
    python3 tools/linnik/gen_zone.py --table    the curve's pieces and the parameters of the step at the threshold
    python3 tools/linnik/gen_zone.py --pv [EPS ...]   the cases with the Pólya–Vinogradov bound for the kernels

The estimate in two variables (`SieveTwoTypeII.typeII_two_gen`) holds for two polynomials of lengths `q^{m₁}` and
`q^{m₂}` when, for every `β ∈ [1/2, 11/12]` and `w ∈ [0, 4·10⁻⁶]`, there are exponents `M_i` of the two mean squares
with

    (L − m₁ − m₂)(β + w) + (m₁ + M₁)/2 + (m₂ + M₂)/2 ≤ L − 1/25000,

`M_i = max(m_i, 1)` by orthogonality or `M_i = max(m_i, g(β) + b(m_i))` by the Halász–Montgomery inequality,
`g` a curve with the counts of the characters with a zero in `Re s ≥ β`, `b(m) = 5/12 + m/12 + δ′(1 − m) + 2ε′` with
`δ′ = ε′ = 1/1000`. Write `s_i = 1 − m_i` (positive for a variable shorter than `q`) and `ρ = L − m₁ − m₂` (the
exponent of the rest). The condition is

    D(s₁, β) + D(s₂, β) + 1/12500 ≤ 2ρ(1 − β − w),
    D(s, β) = max(0, min(s, g(β) − (1/2 − 2ε′) + (11/12 + δ′)s)):

it does not involve `L` except through `ρ`. The Halász–Montgomery inequality is the better of the two exactly when
`g(β) ≤ 1/2 − 2ε′ + (1/12 − δ′)s`.

The curve `ghx` is the trivial count `1` below the threshold `β† = 7789/10000` and Huxley's density estimate from `β†`
on: the exponent `A(1 − σ)` on a step `[lo, hi]`, with `A` just above `3/(3σ − 1)` at `lo`
(`LinnikHuxStep.charDensity_gen`). The step `[β†, 131/168]` is written in `SieveCurveHx.lean` (`hxT`); its parameters
`(M, a, λ, A_i, A)` are those of least `A` on a grid (`a` a multiple of `10⁻⁵`, `λ` of `1/200000`, `A_i` of `10⁻⁵`,
`A = A_i + 10⁻⁵`), every condition of `Par.Good` checked here in exact rationals. From `131/168` on the steps are
`hx7_5` … `hx7_19` of `LinnikStairs7.lean` (parsed from it), then `(101/50)(1 − σ)` from `5/6`
(`LinnikStep.charDensity_step`). Neither Ingham's estimate nor Chen, Gupta and Li's is used: the estimate needs a
curve only where the Halász–Montgomery inequality is used, and the curve is at most `1/2 − 2ε′` exactly from `β†` on.

The region written here uses orthogonality for `β ≤ β†` and the Halász–Montgomery inequality from `β†` on, for both
variables:

    Zone7d L m₁ m₂:   ρ ≥ 1/2000,   m₁ ≥ 2/3,   m₂ ≥ 2/3,
                      s₁ + 1/12500 ≤ λρ,   s₂ + 1/12500 ≤ λρ,   s₁ + s₂ + 1/12500 ≤ λρ,
                      λ = 2(1 − β† − 4·10⁻⁶) = 27637/62500 = 0.442192.

The three inequalities with `λ` are the condition at `β†` by orthogonality; below `β†` they imply it because `ρ ≥ 0`.
From `β†` on the curve is at most `1/2 − 2ε′`, and the cases at the two ends of each piece hold on the region (checked
here in exact arithmetic at the vertices of the region cut to `ρ ≤ 10`, `s_i ≥ −10`). The region is the one of the
certificate's tests (`SieveAdTwoDefs`), so `β†` and `λ` are fixed here. Below `β†` the curve `1` leaves only
orthogonality, so the exact zone of `ghx` for one short variable is the region up to the margin `1/12500` (`--exact`).

The Lean proof of the zone glues the curve's pieces: `zone7d_orth` on `[1/2, β†]` (orthogonality, for every curve),
and `zonePiece_HH` on each piece from `β†` on, the cases at the two ends of a piece by `linarith` from the six
inequalities (`zends`).

`--pv` checks the same cases with the Pólya–Vinogradov bound `|k_Y(ψ)| ≪ q^{1/2 + ε}` for the kernels in place of the
bound from the half-plane (`SieveTypeIIHM.offK_bound`): the Halász–Montgomery case is then
`max(0, g(β) − (1/2 − ε) + s)`. It prints, for each `ε` given (default `1/1000, 2/1000, 3/1000, 37/10000, 4/1000`),
whether the cases hold at the vertices, and the largest `ε` for which they do, by bisection. Not formalised.
"""
import itertools
import math
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
PNT = os.path.join(HERE, '..', '..', 'lib', 'pnt')
OUT_ZONE = os.path.join(PNT, 'SieveTwoZone7D.lean')
OUT_CURVE = os.path.join(PNT, 'SieveCurveHx.lean')
STAIRS = os.path.join(PNT, 'LinnikStairs7.lean')
D = E = Fr(1, 1000)
W = Fr(4, 10 ** 6)
MU = Fr(1, 12500)
RHO0 = Fr(1, 2000)
MMIN = Fr(2, 3)
T = Fr(1, 2) - 2 * E                 # the curve's value below which Halász–Montgomery wins at s = 0
H1 = Fr(11, 12) + D                  # κ_H − m = g − T + H1·s
BD = Fr(7789, 10000)                 # the threshold β†: the region of the certificate's tests is made at it
LAM = Fr(27637, 62500)               # λ = 2(1 − β† − W), as `SieveAdTwoDefs` has it
JOIN = Fr(131, 168)                  # where `LinnikStairs7`'s Huxley steps start
ES = Fr(1, 100000)                   # `LinnikHuxStep.εs`


def lit(x):
    x = Fr(x)
    return f'{x.numerator}' if x.denominator == 1 else f'{x.numerator} / {x.denominator}'


def frac(s):
    n, d = (s.split(' / ') + ['1'])[:2]
    return Fr(int(n), int(d))


def ceilq(x, d):
    return Fr(math.ceil(x * d), d)


# ---------------------------------------------------------------- Huxley's step at the threshold

def check_good(p):
    """Every field of `LinnikHuxStep.Par.Good` for the parameters `p`, in exact rationals. The exponent conditions
    `h1`–`h3` are affine in `σ`, so they are checked at the ends of the step; `h4` (for every `σ ≤ hi`) at `σ = hi`."""
    M, a, lam, lo, hi, Ai, A = (p[k] for k in ('M', 'a', 'lam', 'lo', 'hi', 'Ai', 'A'))
    assert M >= 1 and a > 0 and a + ES <= Fr(M, 2000)
    assert Fr(201, 200) + ES <= lam and 3 * (a + ES) / 2 <= lam and lam <= 2
    assert Fr(3, 4) <= lo < hi <= Fr(11, 12)
    for s in (lo, hi):
        assert lam * (2 - 2 * s + ES) + ES / 12 <= Ai * (1 - s), ('h1', s)
        assert (a + ES) * (4 - 6 * s + 3 * ES) + (ES / 4 + (1 + Fr(3, 2) * ES) + ES / 4) <= Ai * (1 - s), ('h2', s)
        assert Fr(201, 100) * (Fr(1, 2) - s) + Fr(1, 500) + (1 + ES) <= A * (1 - s), ('h3', s)
    assert A >= Ai and ES / (24 * M) + Ai * (1 - hi) <= A * (1 - hi), 'h4'
    assert 0 <= A <= 16
    return True


def least_Ai(a, lam, lo, hi):
    """The least multiple of `10⁻⁵` that `h1` and `h2` allow at both ends."""
    need = Fr(0)
    for s in (lo, hi):
        need = max(need, (lam * (2 - 2 * s + ES) + ES / 12) / (1 - s),
                   ((a + ES) * (4 - 6 * s + 3 * ES) + 1 + 2 * ES) / (1 - s))
    return ceilq(need, 100000)


def step(lo, hi):
    """The parameters of least `A` for a step `[lo, hi]`: `a` near `1/(3lo − 1)`, `λ = 3(a + ε)/2` rounded up,
    `A_i` the least that `h1` and `h2` allow, `A = A_i + 10⁻⁵`, `M` the least with `a + ε ≤ M/2000`."""
    best = None
    a0 = 1 / (3 * lo - 1) - ES
    for k in range(-300, 300):
        a = Fr(round(a0 * 100000) + k, 100000)
        lam = max(Fr(201, 200) + ES, ceilq(3 * (a + ES) / 2, 200000))
        Ai = least_Ai(a, lam, lo, hi)
        p = dict(M=math.ceil(2000 * (a + ES)), a=a, lam=lam, lo=lo, hi=hi, Ai=Ai, A=Ai + ES)
        try:
            check_good(p)
        except AssertionError:
            continue
        if best is None or p['A'] < best['A']:
            best = p
    assert best is not None
    return best


def stairs():
    """Huxley's steps of `LinnikStairs7.lean` from `131/168` on, as `(name, lo, hi, A, A's literal)`."""
    t = open(STAIRS, encoding='utf-8').read()
    out = []
    pat = (r'def parHx7_(\d+) : Par where\n  M := \d+\n  a := [\d /]+\n  lam := [\d /]+\n'
           r'  lo := ([\d /]+)\n  hi := ([\d /]+)\n  Ai := [\d /]+\n  A := ([\d /]+)\n')
    for m in re.finditer(pat, t):
        lo, hi = frac(m.group(2)), frac(m.group(3))
        if lo >= JOIN:
            assert lit(frac(m.group(4))) == m.group(4), m.group(4)
            out.append((f'hx7_{m.group(1)}', lo, hi, frac(m.group(4))))
    out.sort(key=lambda r: r[1])
    assert out and out[0][1] == JOIN and out[-1][2] == Fr(5, 6), out
    for p, q in zip(out, out[1:]):
        assert p[2] == q[1], (p, q)
    return out


def pieces():
    """The pieces `(lo, hi, A, name)` of `ghx` on `[1/2, 11/12]`: `A = None` for the trivial count."""
    hxT = step(BD, JOIN)
    ps = [(Fr(1, 2), BD, None, 'trivial'), (BD, JOIN, hxT['A'], 'hxT')]
    ps += [(lo, hi, A, nm) for nm, lo, hi, A in stairs()]
    ps.append((Fr(5, 6), Fr(11, 12), Fr(101, 50), 'top'))
    for p, q in zip(ps, ps[1:]):
        assert p[1] == q[0], (p, q)
    return ps, hxT


# ---------------------------------------------------------------- the zone

def region(lam):
    """The six inequalities of the region as `(a₁, a₂, a₃, c)`: `a₁s₁ + a₂s₂ + a₃ρ ≤ c`."""
    return [(0, 0, -1, -RHO0), (1, 0, 0, 1 - MMIN), (0, 1, 0, 1 - MMIN),
            (1, 0, -lam, -MU), (0, 1, -lam, -MU), (1, 1, -lam, -MU)]


def det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def vertices(cons):
    """The vertices of the polyhedron `{v : a·v ≤ c}` in three variables (it must be bounded)."""
    out = []
    for tri in itertools.combinations(cons, 3):
        m = [list(map(Fr, t[:3])) for t in tri]
        dt = det3(m)
        if dt == 0:
            continue
        v = []
        for j in range(3):
            mj = [row[:] for row in m]
            for i in range(3):
                mj[i][j] = Fr(tri[i][3])
            v.append(det3(mj) / dt)
        if all(sum(Fr(a) * x for a, x in zip(c[:3], v)) <= c[3] for c in cons):
            out.append(tuple(v))
    return out


def cases(A, beta, t=T, h1=H1):
    """The four inequalities of a piece at `β`, `w = 4·10⁻⁶`, as linear forms `(a₁, a₂, a₃, c)` to be `≤ c`:
    `Σ (c_i − m_i)/2 + 1/25000 − ρ(1 − β − W) ≤ 0`, `c_i − m_i ∈ {0, κ_i − m_i}`; `A = None` for orthogonality
    (`κ − m = s`), else `κ − m = A(1 − β) − t + h1·s` (`t = T`, `h1 = H1` for the kernel bound of the half-plane,
    `t = 1/2 − ε`, `h1 = 1` for Pólya–Vinogradov's)."""
    out = []
    for c1 in (0, 1):
        for c2 in (0, 1):
            a1 = a2 = const = Fr(0)
            for which, on in ((1, c1), (2, c2)):
                if not on:
                    continue
                coef, k0 = (Fr(1), Fr(0)) if A is None else (h1, A * (1 - beta) - t)
                if which == 1:
                    a1 += coef / 2
                else:
                    a2 += coef / 2
                const += k0 / 2
            out.append((a1, a2, -(1 - beta - W), -(const + MU / 2)))
    return out


def check(ps, lam):
    """Every case of the Lean proof holds at the vertices of the region cut to `ρ ≤ 10`, `s_i ≥ −10`: orthogonality
    at `1/2` and `β†`, and the Halász–Montgomery inequality at the two ends of every piece from `β†` on."""
    assert ps[0][2] is None and ps[0][1] == BD and all(A is not None for _, _, A, _ in ps[1:])
    assert all(A * (1 - lo) <= T for lo, _, A, _ in ps[1:])
    cons = region(lam) + [(0, 0, 1, 10), (-1, 0, 0, 10), (0, -1, 0, 10)]
    vs = vertices(cons)
    assert vs
    todo = [(None, Fr(1, 2)), (None, BD)]
    for lo, hi, A, _ in ps[1:]:
        todo += [(A, lo), (A, hi)]
    worst = None
    for A, beta in todo:
        for a1, a2, a3, c in cases(A, beta):
            m = max(a1 * v[0] + a2 * v[1] + a3 * v[2] - c for v in vs)
            assert m <= 0, (A, beta, float(m))
            worst = m if worst is None else max(worst, m)
    return len(todo), worst


def worst_case(ps, lam, t=T, h1=H1):
    """The largest excess of a case of `check` at the vertices of the region cut to `ρ ≤ 10`, `s_i ≥ −10`: the cases
    hold when it is at most `0`."""
    vs = vertices(region(lam) + [(0, 0, 1, 10), (-1, 0, 0, 10), (0, -1, 0, 10)])
    todo = [(None, Fr(1, 2)), (None, BD)] + [(A, b) for lo, hi, A, _ in ps[1:] for b in (lo, hi)]
    return max(a1 * v[0] + a2 * v[1] + a3 * v[2] - c
               for A, beta in todo for a1, a2, a3, c in cases(A, beta, t, h1) for v in vs)


def pv(ps, lam, epss):
    """The cases with the Pólya–Vinogradov bound for the kernels, at each `ε` of `epss`, and the largest `ε`."""
    ok = lambda e: worst_case(ps, lam, Fr(1, 2) - e, Fr(1)) <= 0
    for e in epss:
        print(f'  ε = {lit(e):>9s} = {float(e):.5f}: the cases ' + ('hold' if ok(e) else 'fail'))
    a, b = Fr(0), Fr(1, 100)
    assert ok(a) and not ok(b)
    for _ in range(40):
        mid = (a + b) / 2
        a, b = (mid, b) if ok(mid) else (a, mid)
    print(f'  they hold exactly for ε up to {float(a):.7f}')


def exact(ps, lam):
    """The largest `s` in the exact zone for one short variable against `λρ − 1/12500`."""
    def ok(s, rho):
        for lo, hi, A, _ in ps:
            for i in range(41):
                beta = lo + (hi - lo) * i / 40
                g = Fr(1) if A is None else A * (1 - beta)
                dd = max(Fr(0), min(s, g - T + H1 * s))
                if dd + MU > 2 * rho * (1 - beta - W):
                    return False
        return True
    print('   ρ      exact s    region s   ratio')
    for rho in (Fr(1, 100), Fr(1, 20), Fr(1, 10), Fr(1, 5), Fr(3, 10)):
        a, b = Fr(0), Fr(1, 2)
        for _ in range(30):
            mid = (a + b) / 2
            a, b = (mid, b) if ok(mid, rho) else (a, mid)
        reg = lam * rho - MU
        print(f'  {float(rho):5.3f}  {float(a):9.6f}  {float(reg):9.6f}  {float(reg / a):6.4f}')


# ---------------------------------------------------------------- the Lean files

CURVE_HEAD = '''/-
# The curve `ghx` of the Type II estimate in two variables, and its counts

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/gen_zone.py`; do not edit by hand.

The curve `ghx` is the trivial count `1` below `β† = @BD@` and Huxley's density estimate from `β†` on: the
exponent `A(1 − σ)` on a step `[lo, hi]`, with `A` just above Huxley's `3/(3σ − 1)` at `lo`
(`LinnikHuxStep.charDensity_gen`). The step `[@BD@, 131 / 168]`, with `A = @A@`, is written here; from
`131 / 168` on the steps are `hx7_5` … `hx7_19` of `LinnikStairs7.lean`, then `(101/50)(1 − σ)` from `5/6`
(`LinnikStep.charDensity_step`). Its counts need no hypothesis, and use neither Ingham's estimate nor Chen, Gupta and
Li's. The estimate in two variables needs a curve only where it uses the Halász–Montgomery inequality, from `β†` on
(`SieveTwoZone7D`), where `ghx` is at most `1/2 − 1/500`.

* `parHxT`, `parHxT_good`, `charDensity_hxT`: Huxley's step at the threshold, on `[@BD@, 131 / 168]` with the
  exponent `(@A@)(1 − σ)` (Huxley's `3/(3σ − 1)` is `@HUX@` at `σ = @BD@`).
* `ghx`, `ghx_le_one`, `ghx_half`; `counts_hx`: `CurveCounts ghx`, with no hypothesis, glued by
  `SieveCurveGlue.rangeCounts_glue` from the trivial count, `charDensity_hxT`, `LinnikStairs7`'s steps and
  `LinnikStep.charDensity_step`.

The file imports `SieveCurveGlue.lean` (for `rangeCounts_glue`), `LinnikStairs7.lean` and `LinnikStep.lean`.
-/
import SieveCurveGlue
import LinnikStairs7
import LinnikStep

open Complex Real Finset

noncomputable section

namespace SieveCurveHx

open DirichletCharacter SieveTypeIIGen SieveCurveGlue LinnikHuxStep

/-- The parameters of Huxley's step at the threshold, on `[@BD@, 131 / 168]`: the exponent `@A@`
(`3/(3σ₁ − 1)` is `@HUX@` at the left end). -/
def parHxT : Par where
  M := @M@
  a := @a@
  lam := @lam@
  lo := @BD@
  hi := 131 / 168
  Ai := @Ai@
  A := @A@

theorem parHxT_good : parHxT.Good := by stairs_good parHxT

open scoped Classical in
/-- **Huxley's step at the threshold**: there is `C ≥ 0` such that for every `q ≥ 1`, `@BD@ ≤ σ ≤ 131 / 168` and
`T ≥ 2` at most `C(qT)^{(@A@)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T`. -/
theorem charDensity_hxT :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), @BD@ ≤ σ → σ ≤ 131 / 168 → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((@A@) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_gen parHxT parHxT_good

/-- The curve `ghx`: the trivial count `1` below `@BD@`, Huxley's step at the threshold on
`[@BD@, 131 / 168]`, Huxley's steps `5` to `19` of `LinnikStairs7` on `[131/168, 5/6]`, and `(101/50)(1 − σ)` from
`5/6` on. -/
CHAIN

/-- `ghx ≤ 1`: on each step `A(1 − σ) ≤ A(1 − lo) ≤ 1`, and `(101/50)(1 − σ) ≤ 101/300` from `5/6` on. -/
LEONE

lemma ghx_half : ghx (1 / 2) = 1 := by unfold ghx; norm_num

/-- **The counts of the curve** (`CurveCounts ghx`), with no hypothesis: the trivial count, Huxley's step at the
threshold, Huxley's steps `5` to `19` and `LinnikStep.charDensity_step`, glued. -/
COUNTS

end SieveCurveHx

#print axioms SieveCurveHx.charDensity_hxT
#print axioms SieveCurveHx.counts_hx
'''

ZONE_HEAD = '''/-
# The zone of the Type II estimate in two variables, for the curve `ghx`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/gen_zone.py`; do not edit by hand.

`SieveTwoTypeII.typeII_two_gen` is Proposition 3′ for two polynomials of lengths `q^{m₁}` and `q^{m₂}`, for a curve
`g` and a region `R` of pairs `(m₁, m₂)` with the zone's exponents `ZoneOK g L d e R`. This file proves them for the
curve `ghx` (`SieveCurveHx`: the trivial count below `BDLIT`, Huxley's density estimate from there on; its bounds
`ghx_le_one`, `ghx_half` and its counts `counts_hx`, with no hypothesis) on an explicit region, for every exponent
`L`. Write `s_i = 1 − m_i` and `ρ = L − m₁ − m₂`.

* `Zone7d L m₁ m₂`, **the region**: `ρ ≥ 1/2000`, `m₁ ≥ 2/3`, `m₂ ≥ 2/3`, and `s₁ + 1/12500 ≤ λρ`,
  `s₂ + 1/12500 ≤ λρ`, `s₁ + s₂ + 1/12500 ≤ λρ` with `λ = LAMLIT = LAMDEC`. Two variables of length at least `q`
  (`s_i ≤ 0`) are in it whenever `ρ ≥ 1/2000`; a variable shorter than `q` may be short by `λ` times the exponent
  of the rest. (The name is that of the curve `g7d` of `SieveCurve7D`, for which the region was first proved; the
  certificate's tests, `SieveAdTwoDefs`, are written for it.)
* `zone_hx`: `ZoneOK ghx L (1/1000) (1/1000) (Zone7d L)`, for every `L`.
* `typeII_two_hx`, **Proposition 3′ in two variables for the curve `ghx`**, with no hypothesis:
  `typeII_two_gen` at `ghx` on `Zone7d L`.

Proof of `zone_hx`. For `β ≤ BDLIT` both mean squares are bounded by orthogonality, for every curve
(`zone7d_orth`): at `β = BDLIT` and `w = 4·10⁻⁶` the three inequalities with `λ = 2(1 − BDLIT − 4·10⁻⁶)`
are the exponent's bound. From `BDLIT` on the curve is at most `1/2 − 2/1000`, where the Halász–Montgomery
inequality is the better bound; each of the curve's NHM pieces there is `zonePiece_HH`, its cases at the two ends
by `linarith` from the six inequalities of the region (the tactic `zends`). The pieces are glued as `ghx` is
written.

The file imports `SieveCurveHx.lean` and `SieveTwoPieces.lean`.
-/
import SieveCurveHx
import SieveTwoPieces

open Complex Real Finset

noncomputable section

namespace SieveTwoZone7D

open DirichletCharacter SieveTypeIIGen SieveTypeIIHM SieveCurveHx

/-- **The region of the estimate in two variables.** With `s_i = 1 − m_i` and `ρ = L − m₁ − m₂`: `ρ ≥ 1/2000`,
`m_i ≥ 2/3`, and `s₁ + 1/12500`, `s₂ + 1/12500`, `s₁ + s₂ + 1/12500` at most `λρ`, `λ = LAMLIT`. -/
def Zone7d (L m₁ m₂ : ℝ) : Prop :=
  1 / 2000 ≤ L - m₁ - m₂ ∧ 2 / 3 ≤ m₁ ∧ 2 / 3 ≤ m₂ ∧
    (1 - m₁) + 1 / 12500 ≤ LAMLIT * (L - m₁ - m₂) ∧
    (1 - m₂) + 1 / 12500 ≤ LAMLIT * (L - m₁ - m₂) ∧
    (1 - m₁) + (1 - m₂) + 1 / 12500 ≤ LAMLIT * (L - m₁ - m₂)

/-- The region lies in `m₁ + m₂ ≤ L`. -/
lemma zone7d_le (L : ℝ) (m₁ m₂ : ℝ) (h : Zone7d L m₁ m₂) : m₁ + m₂ ≤ L := by
  have := h.1; linarith

/-- For `β ≤ BDLIT` the zone's exponents hold on the region by orthogonality, whatever the curve. -/
lemma zone7d_orth (g : ℝ → ℝ) (L : ℝ) :
    ZonePiece g L (1 / 1000) (1 / 1000) (Zone7d L) (1 / 2) (BDLIT) :=
  zonePiece_OO g (zone7d_le L) (by zends)

set_option maxHeartbeats 20000000 in
/-- **The zone's exponents for the curve `ghx` on the region `Zone7d L`**, for every exponent `L`. -/
theorem zone_hx (L : ℝ) : ZoneOK ghx L (1 / 1000) (1 / 1000) (Zone7d L) :=
  zoneOK_of_piece <| GLUE

open scoped ContDiff in
/-- **Proposition 3′ in two variables for the curve `ghx`**, with no hypothesis: `typeII_two_gen` on the region
`Zone7d L`. For `f0` smooth (`hf0`) with support in `[1/2, 2]` (`hsupp`), `K₀`, `e₁ > 0` (`he₁`) and `0 < η ≤ 10⁻⁵`
(`hη`, `hη1`) there is `q₀` such that for `q ≥ q₀`, `S_i ⊆ (P_i, 2P_i]` with `P_i ≥ 1` and
`Zone7d L (log_q P₁) (log_q P₂)`, and `K ≤ K₀` prime sums at scales `Q_j ≥ q^{e₁}` and heights `|h_j| ≤ q^η` with
`∏ Q_j ≤ 2^{K₀}q^L/(P₁P₂)`: the sum over `χ ≠ 1` of `|dp S₁ (aχ) h₁||dp S₂ (bχ) h₂||∏_j Sp χ f0 (Q_j) (h_j)|` is at
most `q^{L − 1/50000}(Σ|a|²/P₁)^{1/2}(Σ|b|²/P₂)^{1/2}`. -/
theorem typeII_two_hx (L : ℝ) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {e₁ η : ℝ} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P₁ P₂ : ℕ) (S₁ S₂ : Finset ℕ), S₁ ⊆ Finset.Ioc P₁ (2 * P₁) → S₂ ⊆ Finset.Ioc P₂ (2 * P₂) →
      0 < P₁ → 0 < P₂ → Zone7d L (Real.logb q P₁) (Real.logb q P₂) →
      ∀ (a b : ℕ → ℂ) (h₁ h₂ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / ((P₁ : ℝ) * P₂) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S₁ (fun m => a m * χ m) h₁‖ * ‖DirMean.dp S₂ (fun m => b m * χ m) h₂‖ *
            ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (L - 1 / 50000) *
          (Real.sqrt ((∑ m ∈ S₁, ‖a m‖ ^ 2) / P₁) * Real.sqrt ((∑ m ∈ S₂, ‖b m‖ ^ 2) / P₂)) :=
  typeII_two_gen ghx_le_one ghx_half counts_hx (zone_hx L) hf0 hsupp K₀ he₁ hη hη1

end SieveTwoZone7D

#print axioms SieveTwoZone7D.zone_hx
#print axioms SieveTwoZone7D.typeII_two_hx
'''


def curve_text(ps, hxT):
    chain = ['def ghx (σ : ℝ) : ℝ :=']
    for lo, hi, A, nm in ps[:-1]:
        chain.append(f'  if σ < {lit(hi)} then ' + ('1' if A is None else f'({lit(A)}) * (1 - σ)') + ' else')
    assert ps[-1][2] == Fr(101, 50)
    chain.append('  (101 / 50) * (1 - σ)')
    le = ['lemma ghx_le_one (σ : ℝ) : ghx σ ≤ 1 := by', '  unfold ghx']
    for k, (lo, hi, A, nm) in enumerate(ps[:-1]):
        if A is not None:
            assert A * (1 - lo) <= 1
        le.append(f'  by_cases h{k} : σ < {lit(hi)}')
        if k == 0:
            le.append(f'  · simp only [h{k}, ite_true, le_refl]')
        else:
            le.append(f'  · simp only [h{k}, ite_true]; linarith only [not_lt.1 h{k - 1}]')
        le.append(f'  simp only [h{k}, ite_false]')
        if k >= 1:
            le.append(f'  clear h{k - 1}')
    assert Fr(101, 50) * (1 - ps[-1][0]) <= 1
    le.append(f'  linarith only [not_lt.1 h{len(ps) - 2}]')
    glue = ['theorem counts_hx : CurveCounts ghx :=',
            '  curveCounts_of_range <| rangeCounts_glue (rangeCounts_trivial _ _) <|',
            '    rangeCounts_glue (rangeCounts_of_density charDensity_hxT) <|']
    for lo, hi, A, nm in ps[2:-1]:
        glue.append(f'    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_{nm}) <|')
    glue.append('    rangeCounts_of_density LinnikStep.charDensity_step')
    t = CURVE_HEAD.replace('CHAIN', '\n'.join(chain)).replace('LEONE', '\n'.join(le))
    t = t.replace('COUNTS', '\n'.join(glue))
    hux = 3 / (3 * BD - 1)
    for a, b in [('@HUX@', f'{float(hux):.5f}'), ('@M@', str(hxT['M'])), ('@a@', lit(hxT['a'])),
                 ('@lam@', lit(hxT['lam'])), ('@Ai@', lit(hxT['Ai'])), ('@A@', lit(hxT['A'])), ('@BD@', lit(BD))]:
        t = t.replace(a, b)
    assert '@' not in t
    return t


def glue(ps):
    """The zone's proof, piece by piece as `ghx` is written."""
    lines = ['zonePiece_glue (zone7d_orth (fun _ => 1) L) <|']
    for k, (lo, hi, A, nm) in enumerate(ps[1:], 1):
        body = (f'zonePiece_HH (A := {lit(A)}) (lo := {lit(lo)}) (hi := {lit(hi)}) (zone7d_le L)\n'
                f'        (by zends)')
        lines.append(f'    zonePiece_glue ({body}) <|' if k < len(ps) - 1 else f'    {body}')
    return '\n'.join(lines)


def zone_text(ps):
    t = ZONE_HEAD.replace('GLUE', glue(ps))
    t = t.replace('LAMLIT', lit(LAM)).replace('LAMDEC', f'{float(LAM):.6f}'.rstrip('0'))
    t = t.replace('BDLIT', lit(BD)).replace('NHM', str(len(ps) - 1))
    return t


def generate():
    ps, hxT = pieces()
    assert 2 * (1 - BD - W) == LAM
    n, worst = check(ps, LAM)
    return {OUT_CURVE: curve_text(ps, hxT), OUT_ZONE: zone_text(ps)}, (ps, hxT, n, worst)


def main():
    files, (ps, hxT, n, worst) = generate()
    if '--exact' in sys.argv:
        exact(ps, LAM)
        return
    if '--pv' in sys.argv:
        args = [Fr(x.replace(' ', '')) for x in sys.argv[sys.argv.index('--pv') + 1:]]
        pv(ps, LAM, args or [Fr(1, 1000), Fr(2, 1000), Fr(3, 1000), Fr(37, 10000), Fr(4, 1000)])
        return
    if '--table' in sys.argv:
        for lo, hi, A, nm in ps:
            print(f'  {nm:8s} [{lit(lo):>13s}, {lit(hi):>13s}]  ' + ('1' if A is None else f'{float(A):.6f}(1 − σ)'))
        print('  hxT:', {k: lit(v) for k, v in hxT.items()}, f'Huxley 3/(3β† − 1) = {float(3 / (3 * BD - 1)):.6f}')
        return
    msg = (f'gen_zone: threshold {lit(BD)}, λ = {lit(LAM)}, step hxT A = {lit(hxT["A"])}; {n} ends checked, '
           f'largest case {float(worst):.2e}')
    root = os.path.join(HERE, '..', '..')
    if '--check' in sys.argv:
        for path, t in files.items():
            cur = open(path, encoding='utf-8').read() if os.path.exists(path) else ''
            if cur != t:
                raise SystemExit(f'gen_zone: {os.path.relpath(path, root)} differs from the generated text')
        print(msg + '; files up to date')
        return
    for path, t in files.items():
        with open(path, 'w', encoding='utf-8') as f:
            f.write(t)
    print(msg + '; wrote ' + ', '.join(os.path.relpath(p, root) for p in files))


if __name__ == '__main__':
    main()
