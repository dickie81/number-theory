/-
# Curves of counts glued from pieces

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The resonant window (`SieveTypeIIHM.typeII_res`) takes a curve `g` with `CurveCounts g`. A curve made of many constant
pieces `A_i(1 − σ)` (a staircase above a density curve) is glued here piece by piece.

*  `RangeCounts g lo hi`: the counts of `g` on `lo ≤ σ ≤ hi` (`CurveCounts` restricted to a range).
*  `rangeCounts_of_density`: a density estimate `C(qT)^{A(1−σ)}(log qT)^{10}` on `[lo, hi]` gives
  `RangeCounts (fun σ => A(1 − σ)) lo hi`.
*  `rangeCounts_trivial`: at most `q ≤ qT` characters: `RangeCounts (fun _ => 1) lo hi` for every `lo`, `hi`
  .
*  `rangeCounts_glue`: `RangeCounts g lo mid` and `RangeCounts g' mid hi` give
  `RangeCounts (fun σ => if σ < mid then g σ else g' σ) lo hi`.
*  `curveCounts_of_range`: `RangeCounts g (1/2) 1` is `CurveCounts g`.

The file imports `SieveTypeIIGen.lean`.
-/
import SieveTypeIIGen

open Complex Real Finset

noncomputable section

namespace SieveCurveGlue

open DirichletCharacter SieveTypeIIGen

open scoped Classical in
/-- **The counts of a curve on a range**: there is `C ≥ 0` such that for every `q ≥ 1`, `lo ≤ σ ≤ hi` and `T ≥ 2` at
most `C(qT)^{g(σ)}(1 + log qT)^{10}` characters mod `q` have a zero with `Re s ≥ σ` and `|Im s| ≤ T`. -/
def RangeCounts (g : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), lo ≤ σ → σ ≤ hi → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
        C * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10

theorem curveCounts_of_range {g : ℝ → ℝ} (h : RangeCounts g (1 / 2) 1) : CurveCounts g := h

open scoped Classical in
/-- A density estimate on `[lo, hi]` with the exponent `A(1 − σ)` and `(log qT)^{10}` gives the counts of
`σ ↦ A(1 − σ)` there. -/
theorem rangeCounts_of_density {A lo hi : ℝ}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), lo ≤ σ → σ ≤ hi → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ)) :
    RangeCounts (fun σ => A * (1 - σ)) lo hi := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by linarith)
  have hlog : Real.log ((q : ℝ) * T) ^ (10 : ℝ) ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ hl (by linarith) 10
  have hP : 0 ≤ ((q : ℝ) * T) ^ (A * (1 - σ)) := Real.rpow_nonneg (by linarith) _
  calc _ ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := hC q σ T hσ hσ1 hT
    _ ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ)) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr

open scoped Classical in
/-- The trivial count: at most `q ≤ qT = (qT)^1` characters, on any range. -/
theorem rangeCounts_trivial (lo hi : ℝ) : RangeCounts (fun _ => 1) lo hi := by
  refine ⟨1, zero_le_one, fun q _ σ T _ _ hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have hl1 : 1 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := one_le_pow₀ (by linarith)
  have hc := LinnikDensity.card_chars_le (q := q) (Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
    ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0)
  rw [Real.rpow_one]
  calc _ ≤ (q : ℝ) := hc
    _ ≤ 1 * ((q : ℝ) * T) * 1 := by nlinarith
    _ ≤ 1 * ((q : ℝ) * T) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by gcongr

open scoped Classical in
/-- **Gluing two ranges**: counts for `g` on `[lo, mid]` and for `g'` on `[mid, hi]` give counts for the curve that is
`g` below `mid` and `g'` from `mid` on, on `[lo, hi]`. -/
theorem rangeCounts_glue {g g' : ℝ → ℝ} {lo mid hi : ℝ} (h₁ : RangeCounts g lo mid) (h₂ : RangeCounts g' mid hi) :
    RangeCounts (fun σ => if σ < mid then g σ else g' σ) lo hi := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have hl1 : 0 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := by positivity
  by_cases hm : σ < mid
  · simp only [hm, ite_true]
    have hP : 0 ≤ ((q : ℝ) * T) ^ g σ := Real.rpow_nonneg (by nlinarith) _
    calc _ ≤ C₁ * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 := hC₁ q σ T hσ hm.le hT
      _ ≤ max C₁ C₂ * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          gcongr; exact le_max_left _ _
  · simp only [hm, ite_false]
    have hP : 0 ≤ ((q : ℝ) * T) ^ g' σ := Real.rpow_nonneg (by nlinarith) _
    calc _ ≤ C₂ * ((q : ℝ) * T) ^ g' σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 :=
          hC₂ q σ T (not_lt.1 hm) hσ1 hT
      _ ≤ max C₁ C₂ * ((q : ℝ) * T) ^ g' σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          gcongr; exact le_max_right _ _

end SieveCurveGlue
