/-
# Shared proofs for the staircase file `LinnikStairs7.lean` (and the earlier `LinnikStairs.lean`, removed; see the git history)

Each step of a staircase is an instance of a parametric argument at numerals, and the instances differ only in the
numerals. This file holds what they share, so that each step's file text is its parameters and its statement:

* `stairs_good P`: `LinnikHuxStep.Par.Good P` for the numerals `P`. The fourteen fields are closed in the order of the
  structure: `norm_num` on the unfolded parameters for the numeric ones, `nlinarith` for the exponent conditions
  (`h1`, `h2`, `h3` on `[lo, hi]` and `h4` for every `σ ≤ hi`, polynomial in `σ` of degree at most `1` once the
  parameters are numerals).
* `stairs_good_y P`: the same for `LinnikHuxStepY.ParY.Good P`, whose fifth exponent condition `h5` is numeric.
* `charDensity_ingham_inst`: `LinnikInghamC.charDensity_ingham_c` on `[lo, σ₂]`, in the form of the Ingham steps
  (`charDensity_in7_0` … in `LinnikStairs7`; `charDensity_in0` … were in `LinnikStairs`): at numerals its hypotheses are
  `norm_num` goals.

Both tactics use `εs` (`LinnikHuxStep.εs`) as the proofs they replace did; they are written without hygiene so that
it, and the parameter, are read at the use.
-/
import LinnikInghamC
import LinnikHuxStep
import LinnikHuxStepY

open Complex Real Finset

noncomputable section

namespace LinnikStairsGen

set_option hygiene false in
/-- `LinnikHuxStep.Par.Good P` for numerals `P` (uses `LinnikHuxStep.εs`, so `open LinnikHuxStep`). -/
macro "stairs_good " P:ident : tactic =>
  `(tactic| (
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [$P:ident]
    · simp only [$P:ident]; norm_num
    · simp only [$P:ident, εs]; norm_num
    · simp only [$P:ident, εs]; norm_num
    · simp only [$P:ident, εs]; norm_num
    · simp only [$P:ident]; norm_num
    · simp only [$P:ident]; norm_num
    · simp only [$P:ident]; norm_num
    · intro σ h1 h2
      simp only [$P:ident, εs] at *
      nlinarith
    · intro σ h1 h2
      simp only [$P:ident, εs] at *
      nlinarith
    · intro σ h1 h2
      simp only [$P:ident, εs] at *
      nlinarith
    · intro σ h2
      simp only [$P:ident, εs] at *
      push_cast
      nlinarith
    · simp only [$P:ident]; norm_num
    · simp only [$P:ident]; norm_num))

set_option hygiene false in
/-- `LinnikHuxStepY.ParY.Good P` for numerals `P` (uses `LinnikHuxStep.εs`). -/
macro "stairs_good_y " P:ident : tactic =>
  `(tactic| (
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [$P:ident]
    · simp only [$P:ident]; norm_num
    · simp only [$P:ident, εs]; norm_num
    · simp only [$P:ident, εs]; norm_num
    · simp only [$P:ident, εs]; norm_num
    · simp only [$P:ident]; norm_num
    · simp only [$P:ident]; norm_num
    · simp only [$P:ident]; norm_num
    · intro σ h1 h2
      simp only [$P:ident, εs] at *
      nlinarith
    · intro σ h1 h2
      simp only [$P:ident, εs] at *
      nlinarith
    · simp only [$P:ident, εs]; norm_num
    · intro σ h2
      simp only [$P:ident, εs] at *
      push_cast
      nlinarith
    · simp only [$P:ident]; norm_num
    · simp only [$P:ident]; norm_num))

open scoped Classical in
/-- **Ingham's step on `[lo, σ₂]`**: `charDensity_ingham_c` at `ε`, `c`, `δ₀`, `σ₂` with `1/2 + δ₀ ≤ lo`, and the
exponent `A = 2 + 4c + 4ε`. -/
theorem charDensity_ingham_inst {ε c δ₀ σ₂ lo A : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hδ₀ : 0 < δ₀) (hσ₂ : σ₂ ≤ 11 / 12)
    (hexp : 4 / 3 * (1 + 2 * c) * (1 / 2 - σ₂) + 1 ≤ (2 + 4 * c) * (1 - σ₂)) (hlo : 1 / 2 + δ₀ ≤ lo)
    (hA : 2 + 4 * c + 4 * ε = A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), lo ≤ σ → σ ≤ σ₂ → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := LinnikInghamC.charDensity_ingham_c hε hε1 hc0 hc1 hδ₀ hσ₂ hexp
  refine ⟨C, hC0, fun q _ σ T hσ hσ1 hT => ?_⟩
  have := hC q σ T (by linarith) hσ1 hT
  rwa [hA] at this

end LinnikStairsGen
