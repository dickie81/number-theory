#!/usr/bin/env python3
"""The zone of the Type II estimate in two variables for the curve `g7d`: `lib/pnt/SieveTwoZone7D.lean`.

    python3 tools/linnik/gen_zone.py            write the Lean file
    python3 tools/linnik/gen_zone.py --check    fail if the file on disk differs from what would be written
    python3 tools/linnik/gen_zone.py --exact    the exact zone against the region, on a grid

The estimate in two variables (`SieveTwoTypeII.typeII_two_gen`) holds for two polynomials of lengths `q^{m₁}` and
`q^{m₂}` when, for every `β ∈ [1/2, 11/12]` and `w ∈ [0, 4·10⁻⁶]`, there are exponents `M_i` of the two mean squares
with

    (L − m₁ − m₂)(β + w) + (m₁ + M₁)/2 + (m₂ + M₂)/2 ≤ L − 1/25000,

`M_i = max(m_i, 1)` by orthogonality or `M_i = max(m_i, g(β) + b(m_i))` by the Halász–Montgomery inequality,
`b(m) = 5/12 + m/12 + δ′(1 − m) + 2ε′` with `δ′ = ε′ = 1/1000`. Write `s_i = 1 − m_i` (positive for a variable
shorter than `q`) and `ρ = L − m₁ − m₂` (the exponent of the rest). The condition is

    D(s₁, β) + D(s₂, β) + 1/12500 ≤ 2ρ(1 − β − w),
    D(s, β) = max(0, min(s, g(β) − (1/2 − 2ε′) + (11/12 + δ′)s)):

it does not involve `L` except through `ρ`. The Halász–Montgomery inequality is the better of the two exactly when
`g(β) ≤ 1/2 − 2ε′ + (1/12 − δ′)s`; for the curve `g7d` and `s = 0` that is from `β* = 0.77887…` on, inside the piece
`[163/210, 131/168]`. The region written here uses orthogonality for `β ≤ β† = 7789/10000` and the
Halász–Montgomery inequality from `β†` on, for both variables:

    Zone7d L m₁ m₂:   ρ ≥ 1/2000,   m₁ ≥ 2/3,   m₂ ≥ 2/3,
                      s₁ + 1/12500 ≤ λρ,   s₂ + 1/12500 ≤ λρ,   s₁ + s₂ + 1/12500 ≤ λρ,
                      λ = 2(1 − β† − 4·10⁻⁶) = 27637/62500 = 0.442192.

The three inequalities with `λ` are the condition at `β†` by orthogonality; below `β†` they imply it because `ρ ≥ 0`;
from `β†` on the curve is at most `1/2 − 2ε′` and decreases faster than `2ρ(1 − β)`. The exact zone is the union
over thresholds of such regions; for one short variable its boundary is `s(A − 0.1647ρ) = ρ(0.996 − 2AW) − A/12500`
(`A` the slope of the curve at the threshold), against `s = λρ − 1/12500` here: the region loses under 2% of `s`
at `ρ = 0.3` and under 0.5% at `ρ = 0.05` (`--exact`).

The Lean proof glues the 67 pieces of `g7d`: `zonePiece_OO` once on `[1/2, β†]` for every curve, and `zonePiece_HH`
on each piece from `β†` on, the cases at the two ends of a piece by `linarith` from the six inequalities (`zends`).
This script checks the same cases in exact arithmetic at the vertices of the region cut to `ρ ≤ 10`, `s_i ≥ −10`.
"""
import itertools
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

OUT = os.path.join(HERE, '..', '..', 'lib', 'pnt', 'SieveTwoZone7D.lean')
D = E = Fr(1, 1000)
W = Fr(4, 10 ** 6)
MU = Fr(1, 12500)
RHO0 = Fr(1, 2000)
MMIN = Fr(2, 3)
T = Fr(1, 2) - 2 * E                 # the curve's value below which Halász–Montgomery wins at s = 0
H1 = Fr(11, 12) + D                  # κ_H − m = g − T + H1·s


def lit(x):
    x = Fr(x)
    return f'{x.numerator}' if x.denominator == 1 else f'{x.numerator} / {x.denominator}'


def threshold(pieces):
    """The piece `k` in which the curve crosses `T`, and `β†`: the curve is at most `T` from `β†` on."""
    for k, (lo, hi, A) in enumerate(pieces):
        if A is not None and all(a * (1 - l) <= T for l, _, a in pieces[k + 1:]) and A * (1 - hi) <= T:
            x = Fr(int(T / A * 10 ** 4), 10 ** 4)
            bd = 1 - x
            assert lo < bd < hi and A * (1 - bd) <= T, (k, lo, bd, hi)
            return k, bd
    raise SystemExit('no threshold')


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


def cases(A, beta):
    """The four inequalities of a piece at `β`, `w = 4·10⁻⁶`, as linear forms `(a₁, a₂, a₃, c)` to be `≤ c`:
    `Σ (c_i − m_i)/2 + 1/25000 − ρ(1 − β − W) ≤ 0`, `c_i − m_i ∈ {0, κ_i − m_i}`; `A = None` for orthogonality
    (`κ − m = s`), else `κ − m = A(1 − β) − T + H1·s`."""
    out = []
    for c1 in (0, 1):
        for c2 in (0, 1):
            a1 = a2 = const = Fr(0)
            for which, on in ((1, c1), (2, c2)):
                if not on:
                    continue
                coef, k0 = (Fr(1), Fr(0)) if A is None else (H1, A * (1 - beta) - T)
                if which == 1:
                    a1 += coef / 2
                else:
                    a2 += coef / 2
                const += k0 / 2
            out.append((a1, a2, -(1 - beta - W), -(const + MU / 2)))
    return out


def check(pieces, k0, bd, lam):
    """Every case of the Lean proof holds at the vertices of the region cut to `ρ ≤ 10`, `s_i ≥ −10`."""
    cons = region(lam) + [(0, 0, 1, 10), (-1, 0, 0, 10), (0, -1, 0, 10)]
    vs = vertices(cons)
    assert vs
    todo = [(None, Fr(1, 2)), (None, bd)]
    lo, hi, A = pieces[k0]
    todo += [(A, bd), (A, hi)]
    for lo, hi, A in pieces[k0 + 1:]:
        todo += [(A, lo), (A, hi)]
    worst = None
    for A, beta in todo:
        for a1, a2, a3, c in cases(A, beta):
            m = max(a1 * v[0] + a2 * v[1] + a3 * v[2] - c for v in vs)
            assert m <= 0, (A, beta, float(m))
            worst = m if worst is None else max(worst, m)
    return len(todo), worst


def exact(pieces, lam):
    """The largest `s` in the exact zone for one short variable against `λρ − 1/12500`."""
    def ok(s, rho):
        for lo, hi, A in pieces:
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


HEAD = '''/-
# The zone of the Type II estimate in two variables for the curve `g7d`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/gen_zone.py`; do not edit by hand.

`SieveTwoTypeII.typeII_two_gen` is Proposition 3′ for two polynomials of lengths `q^{m₁}` and `q^{m₂}`, for a curve
`g` and a region `R` of pairs `(m₁, m₂)` with the zone's exponents `ZoneOK g L d e R`. This file proves them for the
paper's curve `g7d` (`SieveCurve7D`: its bounds `g7d_le_one`, `g7d_half` and its counts `counts_7d`, with no
hypothesis) on an explicit region, for every exponent `L`. Write `s_i = 1 − m_i` and `ρ = L − m₁ − m₂`.

* `Zone7d L m₁ m₂`, **the region**: `ρ ≥ 1/2000`, `m₁ ≥ 2/3`, `m₂ ≥ 2/3`, and `s₁ + 1/12500 ≤ λρ`,
  `s₂ + 1/12500 ≤ λρ`, `s₁ + s₂ + 1/12500 ≤ λρ` with `λ = LAMLIT = LAMDEC`. Two variables of length at least `q`
  (`s_i ≤ 0`) are in it whenever `ρ ≥ 1/2000`; a variable shorter than `q` may be short by `λ` times the exponent
  of the rest.
* `zone_7d`: `ZoneOK g7d L (1/1000) (1/1000) (Zone7d L)`, for every `L`.
* `typeII_two_7d`, **Proposition 3′ in two variables for the curve `g7d`**, with no hypothesis:
  `typeII_two_gen` at `g7d` on `Zone7d L`.

Proof of `zone_7d`. For `β ≤ BDLIT` both mean squares are bounded by orthogonality, for every curve
(`zone7d_orth`): at `β = BDLIT` and `w = 4·10⁻⁶` the three inequalities with `λ = 2(1 − BDLIT − 4·10⁻⁶)`
are the exponent's bound. From `BDLIT` on the curve is at most `1/2 − 2/1000`, where the Halász–Montgomery
inequality is the better bound; each of the curve's NHM pieces there is `zonePiece_HH`, its cases at the two ends
by `linarith` from the six inequalities of the region (the tactic `zends`). The pieces are glued as `g7d` is
written.

The file imports `SieveCurve7D.lean` and `SieveTwoPieces.lean`.
-/
import SieveCurve7D
import SieveTwoPieces

open Complex Real Finset

noncomputable section

/- The zone's proof glues the curve's NP pieces, nested as deeply; the default recursion depth is not enough to
elaborate it. -/
set_option maxRecDepth 10000

namespace SieveTwoZone7D

open DirichletCharacter SieveTypeIIGen SieveTypeIIHM SieveCurve7D

/-- **The region of the estimate in two variables for the curve `g7d`.** With `s_i = 1 − m_i` and
`ρ = L − m₁ − m₂`: `ρ ≥ 1/2000`, `m_i ≥ 2/3`, and `s₁ + 1/12500`, `s₂ + 1/12500`, `s₁ + s₂ + 1/12500` at most
`λρ`, `λ = LAMLIT`. -/
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
/-- **The zone's exponents for the curve `g7d` on the region `Zone7d L`**, for every exponent `L`. -/
theorem zone_7d (L : ℝ) : ZoneOK g7d L (1 / 1000) (1 / 1000) (Zone7d L) :=
  zoneOK_of_piece <| GLUE

open scoped ContDiff in
/-- **Proposition 3′ in two variables for the curve `g7d`**, with no hypothesis: `typeII_two_gen` on the region
`Zone7d L`. For `f0` smooth (`hf0`) with support in `[1/2, 2]` (`hsupp`), `K₀`, `e₁ > 0` (`he₁`) and `0 < η ≤ 10⁻⁵`
(`hη`, `hη1`) there is `q₀` such that for `q ≥ q₀`, `S_i ⊆ (P_i, 2P_i]` with `P_i ≥ 1` and
`Zone7d L (log_q P₁) (log_q P₂)`, and `K ≤ K₀` prime sums at scales `Q_j ≥ q^{e₁}` and heights `|h_j| ≤ q^η` with
`∏ Q_j ≤ 2^{K₀}q^L/(P₁P₂)`: the sum over `χ ≠ 1` of `|dp S₁ (aχ) h₁||dp S₂ (bχ) h₂||∏_j Sp χ f0 (Q_j) (h_j)|` is at
most `q^{L − 1/50000}(Σ|a|²/P₁)^{1/2}(Σ|b|²/P₂)^{1/2}`. -/
theorem typeII_two_7d (L : ℝ) {f0 : ℝ → ℝ} (hf0 : ContDiff ℝ ∞ f0)
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
  typeII_two_gen g7d_le_one g7d_half counts_7d (zone_7d L) hf0 hsupp K₀ he₁ hη hη1

end SieveTwoZone7D

#print axioms SieveTwoZone7D.zone_7d
#print axioms SieveTwoZone7D.typeII_two_7d
'''


def glue(pieces, k0, bd):
    """The glued proof, piece by piece as `g7d` is written."""
    lines = []
    last = len(pieces) - 1
    for k, (lo, hi, A) in enumerate(pieces):
        g = 'fun _ => 1' if A is None else f'fun β => {lit(A)} * (1 - β)'
        if k < k0:
            body = (f'zonePiece_mono (lo\' := {lit(lo)}) (hi\' := {lit(hi)})\n'
                    f'        (zone7d_orth ({g}) L) (by norm_num) (by norm_num)')
        elif k == k0:
            body = (f'zonePiece_join (mid := {lit(bd)})\n'
                    f'        (zonePiece_mono (lo\' := {lit(lo)}) (zone7d_orth ({g}) L)\n'
                    f'          (by norm_num) le_rfl)\n'
                    f'        (zonePiece_HH (A := {lit(A)}) (lo := {lit(bd)}) (hi := {lit(hi)}) (zone7d_le L)\n'
                    f'          (by zends))')
        else:
            body = (f'zonePiece_HH (A := {lit(A)}) (lo := {lit(lo)}) (hi := {lit(hi)}) (zone7d_le L)\n'
                    f'        (by zends)')
        if k == 0:
            lines.append(f'zonePiece_glue ({body}) <|')
        elif k < last:
            lines.append(f'    zonePiece_glue ({body}) <|')
        else:
            lines.append(f'    {body}')
    return '\n'.join(lines)


def text():
    pieces = rl.parse('g7d')
    k0, bd = threshold(pieces)
    lam = 2 * (1 - bd - W)
    n, worst = check(pieces, k0, bd, lam)
    t = HEAD.replace('GLUE', glue(pieces, k0, bd))
    t = t.replace('LAMLIT', lit(lam)).replace('LAMDEC', f'{float(lam):.6f}'.rstrip('0'))
    t = t.replace('BDLIT', lit(bd)).replace('NHM', str(len(pieces) - k0)).replace('NP', str(len(pieces)))
    return t, (k0, bd, lam, n, worst, pieces)


def main():
    t, (k0, bd, lam, n, worst, pieces) = text()
    if '--exact' in sys.argv:
        exact(pieces, lam)
        return
    if '--check' in sys.argv:
        cur = open(OUT, encoding='utf-8').read() if os.path.exists(OUT) else ''
        if cur != t:
            raise SystemExit('gen_zone: lib/pnt/SieveTwoZone7D.lean differs from the generated text')
        print(f'gen_zone: threshold {lit(bd)} in piece {k0}, λ = {lit(lam)}; {n} ends checked, '
              f'largest case {float(worst):.2e}; file up to date')
        return
    with open(OUT, 'w', encoding='utf-8') as f:
        f.write(t)
    print(f'gen_zone: threshold {lit(bd)} in piece {k0}, λ = {lit(lam)}; {n} ends checked, '
          f'largest case {float(worst):.2e}; wrote {os.path.relpath(OUT, os.path.join(HERE, "..", ".."))}')


if __name__ == '__main__':
    main()
