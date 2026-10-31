import Mathlib

/-!
# Hölder's inequality with real exponents for a product of factors

The Type II estimates of Harman's sieve for primes in short intervals bound the mean of `|L₁ ⋯ Lₙ|` over a range of
heights by Hölder's inequality with exponents `δⱼ`, `Σ 1/δⱼ = 1`, and a bound for each mean of `|Lⱼ|^{δⱼ}`: the
mean value theorem for an even `δⱼ`, Harman's moment lemma for a real one. This module proves the inequalities that
combine them, for functions with values in `ℝ≥0∞` on any measure space:

* `lintegral_prod_le`: `∫ ∏ fⱼ ≤ ∏ (∫ fⱼ^{δⱼ})^{1/δⱼ}` for `δⱼ > 0` with `Σ 1/δⱼ = 1`;
* `lintegral_prod_le_of_moments`: if `∫ fⱼ^{δⱼ} ≤ Aⱼ^{δⱼ}` for each factor, then `∫ ∏ fⱼ ≤ ∏ Aⱼ`.
-/

open MeasureTheory ENNReal Finset

namespace ShortSieveHolder

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Hölder's inequality for `n` factors with real exponents.** For `δⱼ > 0` with `Σ 1/δⱼ = 1`,
`∫ ∏ fⱼ ≤ ∏ (∫ fⱼ^{δⱼ})^{1/δⱼ}`. -/
theorem lintegral_prod_le (s : Finset ι) {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    {δ : ι → ℝ} (hδ : ∀ i ∈ s, 0 < δ i) (hsum : ∑ i ∈ s, 1 / δ i = 1) :
    ∫⁻ a, ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, (∫⁻ a, f i a ^ δ i ∂μ) ^ (1 / δ i) := by
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) s (f := fun i a => f i a ^ δ i)
    (fun i hi => (hf i hi).pow_const _) (p := fun i => 1 / δ i) hsum
    (fun i hi => (one_div_pos.mpr (hδ i hi)).le)
  have heq : ∀ a, ∏ i ∈ s, (f i a ^ δ i) ^ (1 / δ i) = ∏ i ∈ s, f i a := fun a =>
    Finset.prod_congr rfl fun i hi => by
      rw [← ENNReal.rpow_mul, mul_one_div_cancel (hδ i hi).ne', ENNReal.rpow_one]
  simpa only [heq] using h

/-- **The Type II combination.** If `∫ fⱼ^{δⱼ} ≤ Aⱼ^{δⱼ}` for every factor, with `δⱼ > 0` and `Σ 1/δⱼ = 1`, then
`∫ ∏ fⱼ ≤ ∏ Aⱼ`. -/
theorem lintegral_prod_le_of_moments (s : Finset ι) {f : ι → α → ℝ≥0∞}
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) {δ : ι → ℝ} (hδ : ∀ i ∈ s, 0 < δ i)
    (hsum : ∑ i ∈ s, 1 / δ i = 1) {A : ι → ℝ≥0∞} (hA : ∀ i ∈ s, ∫⁻ a, f i a ^ δ i ∂μ ≤ A i ^ δ i) :
    ∫⁻ a, ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, A i := by
  refine (lintegral_prod_le s hf hδ hsum).trans (Finset.prod_le_prod fun i hi => ?_)
  calc (∫⁻ a, f i a ^ δ i ∂μ) ^ (1 / δ i) ≤ (A i ^ δ i) ^ (1 / δ i) :=
        ENNReal.rpow_le_rpow (hA i hi) (one_div_pos.mpr (hδ i hi)).le
    _ = A i := by rw [← ENNReal.rpow_mul, mul_one_div_cancel (hδ i hi).ne', ENNReal.rpow_one]

end ShortSieveHolder
