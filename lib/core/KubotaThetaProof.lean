import KubotaCuspSeries
import KubotaRows

/-! # The Kubota–Patterson display, proved

The display `KubotaTheta` is assembled from the clauses
proved for θ's Fourier series. This file assembles it, at `r = Y = 1`, and with
`ne_zero_of_kubotaTheta` the half-plane:

* **`KubotaTheta`** (**`kubotaTheta`**): the function is the Fourier series `thS 1 1`, with constant
  term `phiG(4/3)/3` and coefficients `tauTh 1 1` at `∞` (`thS` and `dvd_of_tauTh_ne_zero`), and
  constant terms `0` and coefficients from `cusp_clauses` at `γ_±`. The constant `K` of the
  support and size condition is the larger of the (`thetaSupp_tauTh`) and the
  (`ThetaSupp.mono`). Invariance under `SL_2(ℤ)` is `atG_thS_int`, automorphy on `Γ_1(3)`
  `atG_thS`, and the coefficient clause with `C ≠ 0` `exists_display_coef`.
* **The rows** (**`thetaRows`**): the display `ThetaRows`, through `thetaRows_of_kubota`.
* **The route's other displays** (**`squarefreeCompleted`**, **`completedMeanSquare`**, **`dualMeanSquare`**
  and **`meanSquare`**): the companion paper's Lemma 6.6 (`SquarefreeCompleted`, through
  `squarefreeCompleted_of` and `quadLargeSieve`), its Proposition 5.2 (
  `CompletedMeanSquare`), its (4.12) at every `ϑ > 0` (`DualMeanSquare`, with
  `transferEstimate`), and the family's mean square at every `σ > 0` (`MeanSquare`).
* **Every modulus** (**`thetaRowsM`**,
  **`squarefreeCompletedM`**, **`completedMeanSquareM`** and **`dualMeanSquareM`**): the displays at
  every `md ≠ 0` (`ThetaRowsM md`, through `thetaRowsM_of_kubota`; `SquarefreeCompletedM md`;
  `CompletedMeanSquareM md`), and the dual mean square `DualMeanSquareM md ϑ` for the characters modulo every
  `md ≠ 0` with `4 ∣ md`, at every `ϑ > 0` (`dualMeanSquare_of_completed`).
* **The twisted family** (**`meanSquareNu`**): for a character
  `ν` modulo any `md ≠ 0` with `4 ∣ md`, the mean square of the family with the coefficients `ν(pgen 𝔞 mod md)`
  at every `σ > 0` (`MeanSquareC`, through `meanSquareNu_of_dualMeanSquareM`).
* **The half-plane** (**`ne_zero_of_re_gt_eleven_twelfths`**): `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` for every `s`
  with `Re s > 11/12` (`ne_zero_of_kubotaTheta`).
-/

open Complex NumberField Ideal
open scoped ComplexConjugate

noncomputable section

namespace Eis

/-- **The display `KubotaTheta`, proved**: θ's Fourier series at `r = Y = 1` (`thS`), with
the clauses at `∞` (457 and 459), on `SL_2(ℤ)` and `Γ_1(3)`, and at `γ_±`
. -/
theorem kubotaTheta : KubotaTheta := by
  obtain ⟨K₀, h₀⟩ := thetaSupp_tauTh (r := 1) one_pos (Y := 1) one_pos
  obtain ⟨K₁, tP, tM, hP, hM, hgP, hgM⟩ := cusp_clauses (r := 1) one_pos (Y := 1) one_pos
  obtain ⟨C, hC, hcoef⟩ := exists_display_coef (r := 1) one_pos (Y := 1) one_pos
  exact ⟨fun z v => thS 1 1 one_pos (z, v), max K₀ K₁, C, phiG (4 / 3) / 3, 0, 0, tauTh 1 1 one_pos, tP, tM,
    hC, h₀.mono (le_max_left _ _), hP.mono (le_max_right _ _), hM.mono (le_max_right _ _),
    fun _ h => dvd_of_tauTh_ne_zero h, fun _ _ _ => rfl, hgP, hgM,
    fun γ hdet z _ hv => atG_thS_int one_pos one_pos γ hdet z hv,
    fun γ hdet h3 z _ hv => atG_thS one_pos one_pos γ hdet h3 z hv, hcoef⟩

/-- **The display `ThetaRows`, proved** (`thetaRows_of_kubota`). -/
theorem thetaRows : ThetaRows := thetaRows_of_kubota kubotaTheta

/-- **The companion paper's Lemma 6.6, proved** (the display `SquarefreeCompleted`):
`squarefreeCompleted_of` with `thetaRows` and `quadLargeSieve`. -/
theorem squarefreeCompleted : SquarefreeCompleted := squarefreeCompleted_of thetaRows quadLargeSieve

/-- **The companion paper's Proposition 5.2, proved** (the display `CompletedMeanSquare`):
`completedMeanSquare_of_squarefree`. -/
theorem completedMeanSquare : CompletedMeanSquare := completedMeanSquare_of_squarefree squarefreeCompleted

/-- **The dual mean square at every `ϑ > 0`** (`DualMeanSquare`, the companion paper's (4.12)):
`dualMeanSquare_of_completed_transfer` with `transferEstimate`. -/
theorem dualMeanSquare {ϑ : ℝ} (hϑ : 0 < ϑ) : DualMeanSquare ϑ :=
  dualMeanSquare_of_completed_transfer completedMeanSquare transferEstimate hϑ

/-- **The family's mean square at every `σ > 0`** (`MeanSquare`):
`meanSquare_of_dualMeanSquare`. -/
theorem meanSquare {σ : ℝ} (hσ : 0 < σ) : MeanSquare σ := meanSquare_of_dualMeanSquare hσ (dualMeanSquare hσ)

/-- **The display at every modulus `md ≠ 0`** (`ThetaRowsM md`,
`thetaRowsM_of_kubota`). -/
theorem thetaRowsM {md : 𝓞 K} [NeZero md] : ThetaRowsM md := thetaRowsM_of_kubota kubotaTheta

/-- **The companion paper's Lemma 6.6 at every modulus `md ≠ 0`** (`SquarefreeCompletedM md`):
`squarefreeCompletedM_of` with `thetaRowsM` and `quadLargeSieve`. -/
theorem squarefreeCompletedM {md : 𝓞 K} [NeZero md] : SquarefreeCompletedM md :=
  squarefreeCompletedM_of thetaRowsM quadLargeSieve

/-- **The companion paper's Proposition 5.2 at every modulus `md ≠ 0`** (`CompletedMeanSquareM md`):
`completedMeanSquareM_of_squarefree`. -/
theorem completedMeanSquareM {md : 𝓞 K} [NeZero md] : CompletedMeanSquareM md :=
  completedMeanSquareM_of_squarefree squarefreeCompletedM

/-- **The dual mean square for the characters modulo every `md ≠ 0` with `4 ∣ md`, at every `ϑ > 0`**
(`DualMeanSquareM md ϑ`, the companion paper's (4.12) at `md`): `dualMeanSquare_of_completed`. -/
theorem dualMeanSquareM {md : 𝓞 K} [NeZero md] [Fact ((4 : 𝓞 K) ∣ md)] {ϑ : ℝ} (hϑ : 0 < ϑ) :
    DualMeanSquareM md ϑ :=
  dualMeanSquare_of_completed completedMeanSquareM hϑ

/-- **The twisted family's mean square at every `σ > 0`** (`MeanSquareC`): for a character `ν` modulo
any `md ≠ 0` with `4 ∣ md`, the family `Σ_𝔞 ν(pgen 𝔞)μ(𝔞)(u/𝔞)₆W(N𝔞/Z)`;
`meanSquareNu_of_dualMeanSquareM` with `dualMeanSquareM`. -/
theorem meanSquareNu {md : 𝓞 K} [NeZero md] [Fact ((4 : 𝓞 K) ∣ md)] (ν : MulChar (𝓞 K ⧸ span {md}) ℂ) {σ : ℝ}
    (hσ : 0 < σ) : MeanSquareC (fun I => ν (Ideal.Quotient.mk _ (pgen I))) σ :=
  meanSquareNu_of_dualMeanSquareM ν hσ (dualMeanSquareM hσ)

/-- **The half-plane**: `ζ(s) ≠ 0` and `L(s, χ₋₃) ≠ 0` for `Re s > 11/12` (
`ne_zero_of_kubotaTheta`). -/
theorem ne_zero_of_re_gt_eleven_twelfths {s : ℂ} (hs : 11 / 12 < s.re) :
    riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction PsiOmega.chi3 s ≠ 0 :=
  ne_zero_of_kubotaTheta kubotaTheta hs

end Eis

end

#print axioms Eis.kubotaTheta
#print axioms Eis.thetaRows
#print axioms Eis.squarefreeCompleted
#print axioms Eis.completedMeanSquare
#print axioms Eis.dualMeanSquare
#print axioms Eis.meanSquare
#print axioms Eis.thetaRowsM
#print axioms Eis.squarefreeCompletedM
#print axioms Eis.completedMeanSquareM
#print axioms Eis.dualMeanSquareM
#print axioms Eis.meanSquareNu
#print axioms Eis.ne_zero_of_re_gt_eleven_twelfths
