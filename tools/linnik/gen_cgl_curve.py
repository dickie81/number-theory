#!/usr/bin/env python3
"""gen_cgl_curve.py [--check]: the Lean files of the curve `g7d` and its theorem at `L = 893/400`.

`g7d` is `g7c` (`lib/pnt/SieveTypeIIU226C.lean`) with Chen-Gupta-Li's Proposition 3.1 used at every point of
`[5/7, 131/168]` instead of the flat `7/3 + 1/2000` and Huxley's steps there, and with Ingham's last step
`[99/140, 5/7]` at `ε = 1/400000` (the exponent `7/3 + 1/100000`) instead of `ε = 1/8000` (`7/3 + 1/2000`). On each
step `[lo, hi]` of width `1/1680` (`STEP`; `g7c`'s pieces are cut into steps from their left ends) the library's step
(`LinnikCGLStep.charDensity_cglGen`, with `ParC` parameters `M = 1556`, `a`, `λ`, `A_i`, `A`, `e = 1/100000`) gives the
exponent `A(1 - σ)`. The parameters of a step are the ones that minimise the six exponents of `ParC.Good.hc` at the
step's two ends over `(a, λ)` (a convex problem, solved in floating point, rounded up to multiples of `10⁻⁵`, then
checked in exact rationals), `A_i` the least multiple of `10⁻⁵` that satisfies them, and `A = A_i + 10⁻⁵`. Every
condition of `ParC.Good` is checked here in exact rationals (`check_good`) before a file is written. From `131/168` on,
`g7d` is `g7c` (Huxley's steps `hx7_5` ... `hx7_19`, then `(101/50)(1 - σ)` from `5/6`): there Huxley's exponent is
smaller than the step's.

The steps are narrow because the window's lower end is set where a step's exponent most exceeds the curve it bounds,
at a step's right end: with steps of `1/280` that was the step containing `7/9`, where `4/(1 + σ)` meets Huxley's
`3/(3σ − 1)`. The window's upper end is set by the largest exponent, `7/3` at `5/7`, where Ingham's last step and the
first Chen-Gupta-Li step meet; Ingham's theorem (`LinnikInghamC.charDensity_ingham_c`) takes any `ε > 0`, so its slack
there is cut to `10⁻⁵`.

Writes `lib/pnt/LinnikCGLSteps.lean` (the steps, and Ingham's last step `charDensity_inT`),
`lib/pnt/SieveTypeIIU22325D.lean` (`g7d`, its counts, its window and Proposition 3′) and `lib/pnt/Linnik22325R.lean`
(the theorem). The window `[W1, W2]/100000` is the one
`route_limits.py run` computes for `g7d` at `L` (the sampled scan, then the exact corners). With `--check`, nothing is
written: the files are regenerated in memory and compared with `lib/pnt` (exit 1 on a difference). With `--table`, the
steps' parameters are printed.

Needs Python 3 only. About a minute (the window's scan).
"""
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

PNT = os.path.join(HERE, '..', '..', 'lib', 'pnt')
E = Fr(1, 100000)
M = 1556
L = Fr(893, 400)
TAG, LNUM, LDEN = '22325', 893, 400
STEP = Fr(1, 1680)
# Ingham's last step, at ε = 1/400000: the exponent 2 + 4c + 4ε with c = 1/12
INGHAM_T = (Fr(99, 140), Fr(5, 7), Fr(7, 3) + Fr(1, 100000))
N = 300
TOP = Fr(4, 5)


def need(lo, hi, a, lam, e):
    """The least `A_i` for which the six inequalities of `ParC.Good.hc` hold at both ends (they are affine in `σ`)."""
    w = 0
    for s in (lo, hi):
        t = [lam * (2 - 2 * s), a * (2 - 2 * s), 0.5 + lam * (3 - 4 * s), 0.5 + a * (3 - 4 * s),
             4 / 3 + lam * (2 - 4 * s), 4 / 3 + a * (2 - 4 * s)]
        w = max(w, (max(t) + e / 4) / (1 - s))
    return w


def need_exact(lo, hi, a, lam, e=E):
    w = Fr(0)
    for s in (lo, hi):
        t = [lam * (2 - 2 * s), a * (2 - 2 * s), Fr(1, 2) + lam * (3 - 4 * s), Fr(1, 2) + a * (3 - 4 * s),
             Fr(4, 3) + lam * (2 - 4 * s), Fr(4, 3) + a * (2 - 4 * s)]
        w = max(w, (max(t) + e / 4) / (1 - s))
    return w


def tern(f, lo, hi, it=200):
    for _ in range(it):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if f(m1) < f(m2):
            hi = m2
        else:
            lo = m1
    return (lo + hi) / 2


def best(lo, hi):
    """The minimising `(a, λ)` (floating point) of `need` over `2/3 ≤ a`, `λ ≥ max(201/200 + e, 3(a + e)/2)`, `λ ≤ 2`."""
    e = float(E)

    def inner(a):
        l0 = max(1.005 + e, 1.5 * (a + e))
        if l0 > 2:
            return 9, None
        lam = tern(lambda x: need(lo, hi, a, x, e), l0, 2)
        return need(lo, hi, a, lam, e), lam
    a = tern(lambda x: inner(x)[0], 2 / 3, 0.9)
    return a, inner(a)[1]


def ceilq(x, d):
    return Fr(math.ceil(x * d), d)


def check_good(p):
    """Every field of `LinnikCGLStep.ParC.Good` for the parameters `p`, in exact rationals; the exponent inequalities are
    affine in `σ`, so at the ends of the range (`h4`: at `σ = hi`, the worst `σ ≤ hi`)."""
    lo, hi, a, lam, Ai, A, e = (p[k] for k in ('lo', 'hi', 'a', 'lam', 'Ai', 'A', 'e'))
    assert 0 < e <= Fr(1, 100000) and p['M'] >= 1 and Fr(2, 3) <= a and a + e <= Fr(p['M'], 2000)
    assert Fr(201, 200) + e <= lam and 3 * (a + e) / 2 <= lam and lam <= 2
    assert Fr(5, 7) <= lo <= hi <= Fr(4, 5) and 0 <= A <= 10
    for s in (lo, hi):
        t = [lam * (2 - 2 * s), a * (2 - 2 * s), Fr(1, 2) + lam * (3 - 4 * s), Fr(1, 2) + a * (3 - 4 * s),
             Fr(4, 3) + lam * (2 - 4 * s), Fr(4, 3) + a * (2 - 4 * s)]
        assert all(x + e / 4 <= Ai * (1 - s) for x in t), (lo, hi, s)
        assert Fr(201, 100) * (Fr(1, 2) - s) + Fr(1, 500) + (1 + e) <= A * (1 - s), ('h3', lo, hi, s)
    assert e / (24 * p['M']) + Ai * (1 - hi) <= A * (1 - hi)
    assert e / (24 * p['M']) <= (A - Ai) * (1 - hi)
    return True


def raw_pieces():
    """The textual literals of `g7c`'s pieces (`hi`, `A` as written in the Lean file; the glue needs them verbatim)."""
    import re
    t = open(os.path.join(PNT, 'SieveTypeIIU226C.lean'), encoding='utf-8').read()
    i = t.index('def g7c (σ : ℝ) : ℝ :=')
    body = t[i:t.index('\n\n', i)]
    out = []
    for m in re.finditer(r'if σ < (\d+ / \d+) then (?:1|\((\d+ / \d+)\) \* \(1 - σ\)) else', body):
        out.append((m.group(1), m.group(2)))
    return out


def steps(base):
    """The pieces of `g7d` from the pieces of `g7c`, and the parameters of the new steps."""
    assert len(base) == 43 and base[0][2] is None and base[21][:2] == (Fr(5, 7), Fr(16, 21))
    new, params = [], {}
    for lo, hi, Aold in base[21:42]:
        if hi > Fr(131, 168):
            break
        xs = [lo]
        k = 1
        while lo + k * STEP < hi:
            xs.append(lo + k * STEP)
            k += 1
        xs.append(hi)
        for a_, b_ in zip(xs, xs[1:]):
            a0, l0 = best(float(a_), float(b_))
            a = ceilq(Fr(a0), 100000)
            lam = max(ceilq(Fr(l0), 100000), ceilq(Fr(3, 2) * (a + E), 100000))
            Ai = ceilq(need_exact(a_, b_, a, lam), 100000)
            A = Ai + Fr(1, 100000)
            p = dict(M=M, lo=a_, hi=b_, a=a, lam=lam, Ai=Ai, A=A, e=E)
            check_good(p)
            assert A < Aold, (a_, b_, float(A), float(Aold))
            new.append((a_, b_, A))
            params[(a_, b_)] = p
    # g7c's pieces: 0 trivial, 1..20 Ingham steps in7_0..19, 21 the plateau, 22..41 Huxley steps hx7_0..19, 42 top
    raw = raw_pieces()
    assert len(raw) == 42
    keep = [(lo, hi, A, 'in7_%d' % (i - 1), raw[i]) for i, (lo, hi, A) in enumerate(base[1:21], 1)]
    lo, hi, A = INGHAM_T
    assert keep[-1][:2] == (lo, hi) and A < keep[-1][2]
    keep[-1] = (lo, hi, A, 'inT', (lit(hi), lit(A)))
    hx = [(lo, hi, A, 'hx7_%d' % (i - 22), raw[i]) for i, (lo, hi, A) in enumerate(base[22:42], 22) if lo >= Fr(131, 168)]
    assert hx[0][0] == new[-1][1] == Fr(131, 168) and len(hx) == 15
    return keep, new, params, hx


def lit(x):
    """A rational as a Lean real literal: `n` or `(n / d)`."""
    x = Fr(x)
    return f'{x.numerator}' if x.denominator == 1 else f'{x.numerator} / {x.denominator}'


def litp(x):
    x = Fr(x)
    return f'{x.numerator}' if x.denominator == 1 else f'({x.numerator} / {x.denominator})'


def dec(x, k=6):
    return f'{float(x):.{k}f}'


def window_for(pieces):
    w = rl.window(pieces, L)
    assert w is not None
    W1, W2 = round(w[0] * 100000), round(w[1] * 100000)
    moves = 0
    while True:
        fails, slack, tag = rl.corners(pieces, L, W1, W2)
        if not fails:
            return W1, W2, moves
        ends = {f[0] for f in fails}
        assert 'one' not in ends, fails[:3]
        W1 += 'lo' in ends
        W2 -= 'hi' in ends
        moves += 1
        assert moves <= 50


# ---------------------------------------------------------------------------------------------------------------------
def steps_file(new, params):
    out = []
    w = out.append
    n = len(new)
    w(f'''/-
# Chen–Gupta–Li's Proposition 3.1 at every point of `[5/7, 131/168]`: {n} density steps with the exponent
`A(1 − σ)`, `A` just above `4/(1 + σ)` at the step's left end

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/gen_cgl_curve.py`; do not edit by hand.

Plain statement (`charDensity_s0` … `charDensity_s{n - 1}`). For each step `[lo, hi]` of the table below there is `C ≥ 0`
such that for every `q ≥ 1`, `lo ≤ σ ≤ hi` and `T ≥ 2` at most `C(qT)^{{A(1−σ)}}(log qT)^{{10}}` characters mod `q` have a
zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`. There is no hypothesis: `LinnikCGLHB101.prop31` proves Chen–Gupta–Li's
Proposition 3.1.

This is `LinnikCGLStep.charDensity_cglGen` (the library's step from Proposition 3.1, as `charDensity_cgl` on
`[5/7, 16/21]`) at new `ParC` parameters. `ParC.Good` has one exponent condition per use of Proposition 3.1: on `[lo, hi]`
the six of `hc` (they are affine in `σ`, so they ask for the step's two ends), `h3` for the integral class and `h4` for
the number of dyadic blocks; the other fields are `M = 1556`, `e = 1/100000`, `2/3 ≤ a`, `a + e ≤ M/2000` and the
bounds on `λ`. With `A_i` the least multiple of `10⁻⁵` that satisfies the six inequalities at the step's ends at the
parameters `(a, λ)`, `A = A_i + 10⁻⁵`. The parameters `(a, λ)` minimise the six exponents at the two ends
(`tools/linnik/gen_cgl_curve.py`, which also checks every field of `Good` in exact rationals). The exponent `A` is
within `10⁻⁴` of `4/(1 + lo)`, the exponent of Chen–Gupta–Li's Theorem 1.2 for `q₁ = q` (their divisor form `4/(1 + σ)`)
at the left end `lo`; the library proves its own Proposition 3.1 route, not Theorem 1.2.

| step | `lo` | `hi` | `a` | `λ` | `A_i` | `A` | `4/(1 + lo)` |
|---|---|---|---|---|---|---|---|''')
    for k, (lo, hi, A) in enumerate(new):
        p = params[(lo, hi)]
        w(f'| {k} | `{lit(lo)}` | `{lit(hi)}` | `{dec(p["a"], 5)}` | `{dec(p["lam"], 5)}` | `{dec(p["Ai"], 5)}` | '
          f'`{dec(A, 5)}` | `{dec(Fr(4) / (1 + lo), 5)}` |')
    w('''
Every step is `(parS_k, parS_k_good, charDensity_s_k)`: the parameters `ParC` (`M := 1556`, the others as in the table,
`e := 1/100000`), `parS_k.Good` by `norm_num` and `linarith` (the exponent conditions are linear in `σ` once the
parameters are numerals), and the density estimate by `charDensity_cglGen LinnikCGLHB101.prop31`.

The file also holds Ingham's last step at a smaller slack, `charDensity_inT`: `LinnikInghamC.charDensity_ingham_c` at
`ε = 1/400000` on `[99/140, 5/7]`, with the exponent `7/3 + 1/100000`, in place of `LinnikStairs7.charDensity_in7_19`'s
`7/3 + 1/2000`. The largest exponent of the curve is at `5/7`, and it bounds the window's upper end.

The file imports `LinnikCGLHB101.lean` and `LinnikInghamC.lean`.
-/
import LinnikCGLHB101
import LinnikInghamC

open Real

noncomputable section

namespace LinnikCGLSteps

open LinnikCGLStep
''')
    for k, (lo, hi, A) in enumerate(new):
        p = params[(lo, hi)]
        w(f'''/-- Step {k}, `[{lit(lo)}, {lit(hi)}]`: `M = 1556`, `a = {dec(p["a"], 5)}`, `λ = {dec(p["lam"], 5)}`, `A_i = {dec(p["Ai"], 5)}`,
`A = {dec(A, 5)}`, `e = 1/100000`. -/
def parS{k} : ParC where
  M := 1556
  a := {litp(p["a"])}
  lam := {litp(p["lam"])}
  lo := {litp(lo)}
  hi := {litp(hi)}
  Ai := {litp(p["Ai"])}
  A := {litp(A)}
  e := 1 / 100000

theorem parS{k}_good : parS{k}.Good where
  he := by simp only [parS{k}]; norm_num
  he1 := by simp only [parS{k}]; norm_num
  hM := by simp [parS{k}]
  ha := by simp only [parS{k}]; norm_num
  hat := by simp only [parS{k}]; norm_num
  hlam1 := by simp only [parS{k}]; norm_num
  hlam2 := by simp only [parS{k}]; norm_num
  hlam3 := by simp only [parS{k}]; norm_num
  hlo := by simp only [parS{k}]; norm_num
  hhi := by simp only [parS{k}]; norm_num
  hc := by
    intro σ h1 h2
    simp only [parS{k}] at *
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  h3 := by
    intro σ h1 h2
    simp only [parS{k}] at *
    linarith
  h4 := by
    intro σ h2
    simp only [parS{k}] at *
    push_cast
    linarith
  hA := by simp only [parS{k}]; norm_num
  hA10 := by simp only [parS{k}]; norm_num

open scoped Classical in
/-- **Chen–Gupta–Li's Proposition 3.1 on `[{lit(lo)}, {lit(hi)}]`, density step {k}**: there is `C ≥ 0` such that for every
`q ≥ 1`, `{lit(lo)} ≤ σ ≤ {lit(hi)}` and `T ≥ 2` at most `C(qT)^{{({lit(A)})(1−σ)}}(log qT)^{{10}}`
characters mod `q` have a zero of
`L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`; no hypothesis. -/
theorem charDensity_s{k} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), {litp(lo)} ≤ σ → σ ≤ {litp(hi)} → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ({litp(A)} * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) :=
  charDensity_cglGen LinnikCGLHB101.prop31 parS{k} parS{k}_good
''')
    lo, hi, A = INGHAM_T
    w(f'''open scoped Classical in
/-- **Ingham's last step at `ε = 1/400000`**: there is `C ≥ 0` such that for every `q ≥ 1`,
`{lit(lo)} ≤ σ ≤ {lit(hi)}` and `T ≥ 2` at most `C(qT)^{{({lit(A)})(1−σ)}}(log qT)^{{10}}` characters mod `q`
have a zero of `L(·, χ)` in `Re s ≥ σ`, `|Im s| ≤ T`: `LinnikInghamC.charDensity_ingham_c` at `c = 1/12`, where `2 + 4c = 7/3 = 3/(2 − 5/7)`. -/
theorem charDensity_inT :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), {litp(lo)} ≤ σ → σ ≤ {litp(hi)} → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ({litp(A)} * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  have h := LinnikInghamC.charDensity_ingham_c (ε := 1 / 400000) (c := 1 / 12)
    (δ₀ := 29 / 140) (σ₂ := 5 / 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [show (2 + 4 * (1 / 12 : ℝ) + 4 * (1 / 400000)) * (1 - σ) =
      {litp(A)} * (1 - σ) by ring] at this
''')
    w('end LinnikCGLSteps\n')
    for k in range(n):
        w(f'#print axioms LinnikCGLSteps.charDensity_s{k}')
    w('#print axioms LinnikCGLSteps.charDensity_inT')
    return '\n'.join(out) + '\n'


# ---------------------------------------------------------------------------------------------------------------------
def curve_file(keep, new, hx, W1, W2, tag=TAG, LN=f'{LNUM} / {LDEN}'):
    """`SieveTypeIIU{TAG}D.lean`: g7d, its counts, its window and Proposition 3′."""
    pcs = [(Fr(1, 2), Fr(4, 7), None, 'trivial', ('4 / 7', None))] + keep + \
        [(lo, hi, A, 's%d' % k, (lit(hi), lit(A))) for k, (lo, hi, A) in enumerate(new)] + hx
    top = (Fr(5, 6), Fr(11, 12), Fr(101, 50), 'top', ('11 / 12', '101 / 50'))
    allp = pcs + [top]
    # a boundary is written the same on both sides of every glue
    for p, q in zip(pcs, pcs[1:]):
        assert p[1] == q[0], (p, q)
    assert pcs[-1][4][0] == '5 / 6'
    for k in range(len(pcs) - 1):
        assert Fr(*map(int, pcs[k][4][0].split(' / '))) == pcs[k][1]
    los = ['1 / 2'] + [p[4][0] for p in pcs[:-1]]
    # the `if` chain: one `if σ < hi` per piece but the last
    chain = ['def g7d (σ : ℝ) : ℝ :=']
    for lo, hi, A, nm, (hr, ar) in pcs:
        chain.append(f'  if σ < {hr} then ' + ('1' if A is None else f'({ar}) * (1 - σ)') + ' else')
    chain.append('  (101 / 50) * (1 - σ)')
    le = ['lemma g7d_le_one (σ : ℝ) : g7d σ ≤ 1 := by', '  unfold g7d']
    for k, (lo, hi, A, nm, (hr, ar)) in enumerate(pcs):
        if A is not None:
            assert A * (1 - lo) <= 1
        le.append(f'  by_cases h{k} : σ < {hr}')
        if k == 0:
            le.append(f'  · simp only [h{k}, ite_true, le_refl]')
        else:
            le.append(f'  · simp only [h{k}, ite_true]; linarith only [not_lt.1 h{k - 1}]')
        le.append(f'  simp only [h{k}, ite_false]')
        if k >= 1:
            le.append(f'  clear h{k - 1}')
    assert Fr(101, 50) * (1 - Fr(5, 6)) <= 1
    le.append(f'  linarith only [not_lt.1 h{len(pcs) - 1}]')
    glue = ['theorem counts_7d : CurveCounts g7d :=',
            '  curveCounts_of_range <| rangeCounts_glue (rangeCounts_trivial _ _) <|']
    for lo, hi, A, nm, _ in pcs[1:]:
        if nm.startswith('in7') or nm.startswith('hx7'):
            glue.append(f'    rangeCounts_glue (rangeCounts_of_density LinnikStairs7.charDensity_{nm}) <|')
        else:
            glue.append(f'    rangeCounts_glue (rangeCounts_of_density LinnikCGLSteps.charDensity_{nm.replace("s", "s", 1)}) <|')
    glue.append('    rangeCounts_of_density LinnikStep.charDensity_step')
    win = ['theorem window_%sd : WindowOKHM g7d (%s) (%d / 100000 * (%s)) (%d / 100000 * (%s))' % (tag, LN, W1, LN, W2, LN),
           '    (1 / 1000) (1 / 1000) :=']
    for k, (lo, hi, A, nm, (hr, ar)) in enumerate(pcs):
        if A is None:
            body = 'windowPiece_one (by norm_num) (by norm_num) (by corners) (by corners)'
            piece = f'      {body}'
        else:
            piece = (f'      windowPiece_const (A := {ar}) (lo := {los[k]}) (hi := {hr})\n'
                     f'        (by norm_num) (by norm_num) (by corners) (by corners)')
        pre = '  windowOKHM_of_piece <| ' if k == 0 else '    '
        win.append(f'{pre}windowPieceHM_glue (windowPieceHM_of_piece <|\n{piece}) <|')
    win.append('    windowPieceHM_const_split (A := 101 / 50) (lo := 5 / 6) (hi := 11 / 12)')
    win.append('      (by norm_num) (by cornersHMD) (by cornersHMD) (by cornersHMD)')
    n = len(new)
    txt = f'''/-
# Proposition 3′ at `L = {LN}` on the Halász–Montgomery window `[{W1}/100000, {W2}/100000]·L`, for the curve `g7d`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/gen_cgl_curve.py`; do not edit by hand.

The curve `g7d` is `g7c` of `SieveTypeIIU226C.lean` with the {n} steps of `LinnikCGLSteps.lean` (Chen–Gupta–Li's
Proposition 3.1, exponent `A(1 − σ)` with `A` just above `4/(1 + σ)` at the step's left end) on `[5/7, 131/168]` in place
of `7/3 + 1/2000` on `[5/7, 16/21]` and Huxley's steps `hx7_0` … `hx7_4`; from `131/168` on it is `g7c` (Huxley's steps
`hx7_5` … `hx7_19`, then `(101/50)(1 − σ)` from `5/6`, `LinnikStep.charDensity_step`); below `5/7` it is `g7c` with
Ingham's last step at `ε = 1/400000` (`LinnikCGLSteps.charDensity_inT`, `7/3 + 1/100000` in place of `7/3 + 1/2000`).
Its counts need no hypothesis. The window and the Type II estimate are as in `SieveTypeIIU22475C.lean`: every piece of
`WindowOKHM` below `5/6` holds by orthogonality at its corners (the tactic `corners`), the top piece `[5/6, 11/12]` by
`windowPieceHM_const_split` (`cornersHMD`).

* `g7d`, `g7d_le_one`, `g7d_half`; `counts_7d`: `CurveCounts g7d`, with no hypothesis, glued by
  `SieveCurveGlue.rangeCounts_glue` from `LinnikStairs7`'s steps, `LinnikCGLSteps.charDensity_s0` … `charDensity_s{n - 1}`
  and `LinnikStep.charDensity_step`.
* `window_{tag}d`: `WindowOKHM g7d L m₁ m₂ (1/1000) (1/1000)` at `L = {LN}` on `[{W1}/100000, {W2}/100000]·L`.
* `typeII_{tag}d`: `typeII_gen_hm` at `g7d`, with no hypothesis.

The window is the one `tools/linnik/route_limits.py run` computes for `g7d` at `L = {LN}` (`route_limits.jsonl`).

The file imports `SieveTypeIIU227.lean` (for `LinnikStairs7`, `corners` and `rangeCounts_glue`), `LinnikStep.lean`,
`LinnikCGLSteps.lean` and `SieveTypeIIHM.lean`.
-/
import SieveTypeIIU227
import LinnikStep
import LinnikCGLSteps
import SieveTypeIIHM

open Complex Real Finset

noncomputable section

/- The curve has one `if` per piece, about 150 of them, and its glue and window proofs nest as deeply; the default
recursion depth is not enough to elaborate them. -/
set_option maxRecDepth 10000

namespace SieveTypeIIU{tag}D

open DirichletCharacter SieveTypeIIGen SieveCurveGlue SieveTypeIIU227 SieveTypeIIHM

set_option hygiene false in
/-- The corner cases of `windowPieceHM_const_split`: two values of `β`, two of `m`, two of `w`, each by `norm_num`. -/
macro "cornersHMD" : tactic =>
  `(tactic| (intro β m w hb hm hw
             rcases hb with rfl | rfl <;> rcases hm with rfl | rfl <;> rcases hw with rfl | rfl <;> norm_num))

/-- The curve `g7d`: `1` below `4/7`, the twenty Ingham steps (the last at `ε = 1/400000`),
the {n} steps of `LinnikCGLSteps` on `[5/7, 131/168]`,
Huxley's steps `5` to `19` of `LinnikStairs7` on `[131/168, 5/6]`, and `(101/50)(1 − σ)` from `5/6` on. -/
{chr(10).join(chain)}

set_option maxHeartbeats 20000000 in
/-- `g7d ≤ 1`: on each step `A(1 − σ) ≤ A(1 − lo) ≤ 1`, and `(101/50)(1 − σ) ≤ 101/300` from `5/6` on. -/
{chr(10).join(le)}

lemma g7d_half : g7d (1 / 2) = 1 := by unfold g7d; norm_num

/-- **The counts of the curve** (`CurveCounts g7d`), with no hypothesis: the trivial count,
the twenty Ingham steps (the last `charDensity_inT`),
the {n} steps of `LinnikCGLSteps` (Proposition 3.1), Huxley's steps `5` to `19` and `LinnikStep.charDensity_step`,
glued. -/
{chr(10).join(glue)}

set_option maxHeartbeats 20000000 in
/-- **The window's exponents** at `L = {LN}` on `[{W1}/100000, {W2}/100000]·L`, with the Halász–Montgomery branch on the
top piece. -/
{chr(10).join(win)}

open scoped ContDiff in
/-- **Proposition 3′ at `L = {LN}` on `[{W1}/100000, {W2}/100000]·L`, for the curve `g7d`**, with no hypothesis:
`typeII_gen_hm` for `f0` smooth (`hf0`) with support in `[1/2, 2]` (`hsupp`), `K₀`, `e₁ > 0` (`he₁`) and `0 < η ≤ 10⁻⁵`
(`hη`, `hη1`): there is `q₀` such that its bound holds for `q ≥ 1` with `q ≥ q₀`. -/
theorem typeII_{tag}d {{f0 : ℝ → ℝ}} (hf0 : ContDiff ℝ ∞ f0)
    (hsupp : Function.support f0 ⊆ Set.Icc (1 / 2) 2)
    (K₀ : ℕ) {{e₁ η : ℝ}} (he₁ : 0 < e₁) (hη : 0 < η) (hη1 : η ≤ 1 / 100000) :
    ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ (P : ℕ) (S : Finset ℕ), S ⊆ Finset.Ioc P (2 * P) →
      (q : ℝ) ^ ({W1} / 100000 * ({LN}) : ℝ) ≤ P →
      (P : ℝ) ≤ (q : ℝ) ^ ({W2} / 100000 * ({LN}) : ℝ) →
      ∀ (a : ℕ → ℂ) (h₀ : ℝ) (K : ℕ), K ≤ K₀ → ∀ Q h : ℕ → ℝ,
      (∀ j < K, (q : ℝ) ^ e₁ ≤ Q j ∧ |h j| ≤ (q : ℝ) ^ η) →
      ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * (q : ℝ) ^ ({LN} : ℝ) / P →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖DirMean.dp S (fun m => a m * χ m) h₀‖ * ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (h j)‖ ≤
        (q : ℝ) ^ (({LN} : ℝ) - 1 / 50000) * Real.sqrt ((∑ m ∈ S, ‖a m‖ ^ 2) / P) :=
  typeII_gen_hm g7d_le_one g7d_half counts_7d window_{tag}d hf0 hsupp K₀ he₁ hη hη1

end SieveTypeIIU{tag}D

#print axioms SieveTypeIIU{tag}D.counts_7d
#print axioms SieveTypeIIU{tag}D.window_{tag}d
#print axioms SieveTypeIIU{tag}D.typeII_{tag}d
'''
    return txt, allp


def final_file(W1, W2, tag=TAG, LNUM=LNUM, LDEN=LDEN):
    LN = f'{LNUM} / {LDEN}'
    d = lambda x: f'{x}'
    return f'''/-
# Linnik's theorem with exponent `{LN}`, under the refined certificate at `n = {N}`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/gen_cgl_curve.py`; do not edit by hand.

Plain statement (`linnik_{tag}r`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`, with no hypothesis. The route at `L = {LN}` on the window
`[{W1}/100000, {W2}/100000]` of `tools/linnik/route_limits.jsonl`'s rows for `g7d` (`route{tag}D`, with its Type II
estimate `SieveTypeIIU{tag}D.typeII_{tag}d`), on its grid with `n = {N}` (`SieveCert.grid{tag}R`), whose refined certificate's
total is less than `K` (`SieveCert.total2_lt_{tag}R`), with `SieveMain2.linnik_route_lt2`. The curve `g7d` uses
Chen–Gupta–Li's Proposition 3.1 at every point of `[5/7, 131/168]` (`LinnikCGLSteps`); the theorem is `Linnik22475R`'s
route with that curve and the window and certificate of `L = {LN}`; `Linnik22475R.linnik_22475r` is unchanged.

* `route{tag}D`, `routeOK{tag}D`: `L = {LN}` on `[{W1}/100000, {W2}/100000]`; `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`.
* `typeII{tag}d`: `SieveTypeIIU{tag}D.typeII_{tag}d` as `TypeIIAt`.
* `fits{tag}R`: `grid{tag}R` fits `route{tag}D`: `({W1}/100000)·DEN < U1`, `U2 < ({W2}/100000)·DEN` and
  `DEN < ({LN})·U2`.
* `linnik_{tag}r`: `SieveMain2.linnik_route_lt2` at them.

The file imports `SieveMain2.lean`, `SieveCert{tag}R.lean` and `SieveTypeIIU{tag}D.lean`.
-/
import SieveMain2
import SieveCert{tag}R
import SieveTypeIIU{tag}D

namespace Linnik{tag}R

open SieveCert SieveRoute SieveQ

/-- **The route's parameters at `{LN}`**: `L = {LN}` on the window `[{W1}/100000, {W2}/100000]`. -/
@[instance_reducible] noncomputable def route{tag}D : Route := ⟨{LN}, {W1} / 100000, {W2} / 100000⟩

/-- `route{tag}D` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK{tag}D : @RouteOK route{tag}D :=
  @RouteOK.mk route{tag}D (show (2 : ℝ) < {LN} by norm_num) (show (0 : ℝ) < {W1} / 100000 by norm_num)
    (show ({W1} / 100000 : ℝ) < {W2} / 100000 by norm_num) (show ({W2} / 100000 : ℝ) < 1 by norm_num)
    (show ({LN} : ℝ) ≤ 5 / 2 by norm_num)

/-- **`SieveTypeIIU{tag}D.typeII_{tag}d` as `TypeIIAt`** at the route's parameters. -/
theorem typeII{tag}d : @TypeIIAt route{tag}D := by
  intro f0 hf0 hsupp K₀ e₁ η he₁ hη hη1
  exact SieveTypeIIU{tag}D.typeII_{tag}d hf0 hsupp K₀ he₁ hη hη1

/-- `grid{tag}R` fits `route{tag}D`: `({W1}/100000)·DEN < U1`, `U2 < ({W2}/100000)·DEN` and `DEN < ({LN})·U2`. -/
theorem fits{tag}R : @Fits route{tag}D grid{tag}R := by
  refine @Fits.mk route{tag}D grid{tag}R ?_ ?_ ?_
  · have h : ({W1} * DEN : ℕ) < 100000 * (({W1} * DEN + 99999) / 100000) := by decide
    have h' : ({W1} : ℝ) * DEN < 100000 * ((({W1} * DEN + 99999) / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show ({W1} / 100000 : ℝ) * DEN < ((({W1} * DEN + 99999) / 100000 : ℕ) : ℝ)
    linarith
  · have h : 100000 * ({W2} * DEN / 100000) < {W2} * DEN := by decide
    have h' : (100000 : ℝ) * (({W2} * DEN / 100000 : ℕ) : ℝ) < {W2} * DEN := by exact_mod_cast h
    show (({W2} * DEN / 100000 : ℕ) : ℝ) < {W2} / 100000 * DEN
    linarith
  · have h : {LDEN} * DEN < {LNUM} * ({W2} * DEN / 100000) := by decide
    have h' : ({LDEN} : ℝ) * DEN < {LNUM} * (({W2} * DEN / 100000 : ℕ) : ℝ) := by exact_mod_cast h
    show (DEN : ℝ) < {LN} * (({W2} * DEN / 100000 : ℕ) : ℝ)
    linarith

/-- **Linnik's theorem with exponent `{LN}`, by the refined certificate at `n = {N}`**: there is `K` such that for every
`q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`. -/
theorem linnik_{tag}r : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ ({LN} : ℝ) :=
  @SieveMain2.linnik_route_lt2 route{tag}D routeOK{tag}D grid{tag}R gridOK{tag}R fits{tag}R typeII{tag}d
    total2_lt_{tag}R

end Linnik{tag}R

#print axioms Linnik{tag}R.fits{tag}R
#print axioms Linnik{tag}R.linnik_{tag}r
'''


def generate():
    base = rl.parse('g7c')
    keep, new, params, hx = steps(base)
    sfile = steps_file(new, params)
    # the curve's pieces, for the window
    pcs = [(Fr(1, 2), Fr(4, 7), None)] + [(lo, hi, A) for lo, hi, A, _, _ in keep] + new + [(lo, hi, A) for lo, hi, A, _, _ in hx] \
        + [(Fr(5, 6), Fr(11, 12), Fr(101, 50))]
    W1, W2, moves = window_for(pcs)
    cfile, allp = curve_file(keep, new, hx, W1, W2)
    assert [(lo, hi, A) for lo, hi, A, _, _ in allp] == pcs
    files = {'LinnikCGLSteps.lean': sfile, f'SieveTypeIIU{TAG}D.lean': cfile, f'Linnik{TAG}R.lean': final_file(W1, W2)}
    return files, \
        (W1, W2, moves, params, new)


def main():
    files, (W1, W2, moves, params, new) = generate()
    if '--table' in sys.argv:
        for k, (lo, hi, A) in enumerate(new):
            p = params[(lo, hi)]
            print(k, lit(lo), lit(hi), 'a', dec(p['a'], 5), 'lam', dec(p['lam'], 5), 'Ai', dec(p['Ai'], 5), 'A', dec(A, 5),
                  '4/(1+lo)', dec(Fr(4) / (1 + lo), 5))
    print(f'window [{W1}, {W2}]/100000 at L = {L} (corner moves {moves}); {len(new)} steps, every ParC.Good field checked')
    if '--check' in sys.argv:
        bad = [n for n, t in files.items()
               if not os.path.exists(os.path.join(PNT, n)) or open(os.path.join(PNT, n), encoding='utf-8').read() != t]
        print('GENERATED FILES', 'DIFFER: ' + ', '.join(bad) if bad else 'MATCH lib/pnt')
        return 1 if bad else 0
    for n, t in files.items():
        with open(os.path.join(PNT, n), 'w', encoding='utf-8') as f:
            f.write(t)
        print('wrote', n)
    return 0


if __name__ == '__main__':
    sys.exit(main())
