import Mathlib

/-!
# The exponent of Harman's moment lemma from the mean value theorem and Huxley's estimate

For a Dirichlet polynomial `L` of length `N` on heights up to `T = N^D`, the moment `∫ |L|^δ` is at most `N^δ` (up
to `N^ε`) when, for every level `|L| ≈ N^σ` with `1/2 ≤ σ ≤ 1`, the number of well-spaced points at that level is at
most `N^{δ(1−σ)}` (`ShortSieveLevel`). The large values estimates applied to a power `L^k` give the counts, as powers
of `N`:

* the mean value theorem: `e_MV(k, σ) = max(D, k) + k(1 − 2σ)`;
* Huxley's estimate: `e_H(k, σ) = max(2k(1 − σ), D + k(4 − 6σ))`.

The least `δ` for which some `k` works at every `σ` is Harman's `δ_req(D)`: `2m + 2` for `D ∈ (m + 1/2, m + 1]`, and
`4D − 2m` for `D ∈ (m, m + 1/2]`. This module proves that these values work, with an explicit `k` for each `σ`:

* `mv_exp_le`: for `D ≤ k`, the mean value theorem on `L^k` gives `e_MV(k, σ) = 2k(1 − σ)` at every `σ`;
* `mv_exp_le_of_le_three_quarters` and `hux_exp_le_of_three_quarters_le`: for `D ∈ (m, m + 1/2]` and
  `δ ≥ 4D − 2m`, the mean value theorem on `L^m` works for `σ ≤ 3/4`, and Huxley's estimate on `L^m` for `σ ≥ 3/4`;
* `dreq_hux`: the two together, at every `σ ∈ [1/2, 1]`;
* `eHM_le_eH`, `hm_exp_le_of_three_quarters_le`: the library's Halász–Montgomery count, whose kernel bound
  `Λ^{1/12}T₀^{5/12}` comes from the zero-free half-plane (`ZetaKernel.norm_kz_le`), has exponent
  `e_HM(k, σ) = max(2k(1 − σ), D + k(23/5 − 34σ/5))`, at most Huxley's for `σ ≥ 3/4`, where it is used.
-/

namespace ShortSieveDreq

/-- The count exponent of the mean value theorem on the `k`-th power: `max(D, k) + k(1 − 2σ)`. -/
noncomputable def eMV (D : ℝ) (k : ℕ) (σ : ℝ) : ℝ := max D k + k * (1 - 2 * σ)

/-- The count exponent of Huxley's estimate on the `k`-th power: `max(2k(1 − σ), D + k(4 − 6σ))`. -/
noncomputable def eH (D : ℝ) (k : ℕ) (σ : ℝ) : ℝ := max (2 * k * (1 - σ)) (D + k * (4 - 6 * σ))

/-- **The mean value theorem on a long power.** For `D ≤ k`, `e_MV(k, σ) = 2k(1 − σ)`, at most `δ(1 − σ)` for every
`δ ≥ 2k` and `σ ≤ 1`. -/
theorem mv_exp_le {D δ σ : ℝ} {k : ℕ} (hk : D ≤ k) (hδ : 2 * k ≤ δ) (hσ : σ ≤ 1) :
    eMV D k σ ≤ δ * (1 - σ) := by
  unfold eMV
  rw [max_eq_right hk]
  nlinarith

/-- **The mean value theorem below `3/4`.** For `m < D` and `δ ≥ 4D − 2m`, the mean value theorem on `L^m` works at
every `σ ≤ 3/4`. -/
theorem mv_exp_le_of_le_three_quarters {D δ σ : ℝ} {m : ℕ} (hD : (m : ℝ) < D) (hδ : 4 * D - 2 * m ≤ δ)
    (hσ : σ ≤ 3 / 4) : eMV D m σ ≤ δ * (1 - σ) := by
  unfold eMV
  rw [max_eq_left hD.le]
  have h1 : 0 ≤ 1 - σ := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hδ h1, mul_nonneg (sub_nonneg.2 hD.le) (sub_nonneg.2 hσ)]

/-- **Huxley's estimate above `3/4`.** For `m ≤ D ≤ m + 1/2`, `1 ≤ m` and `δ ≥ 4D − 2m`, Huxley's estimate on
`L^m` works at every `σ ∈ [3/4, 1]`. -/
theorem hux_exp_le_of_three_quarters_le {D δ σ : ℝ} {m : ℕ} (hm : 1 ≤ m) (hD : (m : ℝ) ≤ D)
    (hD' : D ≤ m + 1 / 2) (hδ : 4 * D - 2 * m ≤ δ) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) :
    eH D m σ ≤ δ * (1 - σ) := by
  unfold eH
  have h1 : 0 ≤ 1 - σ := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ1 : δ * (1 - σ) ≥ (4 * D - 2 * m) * (1 - σ) := mul_le_mul_of_nonneg_right hδ h1
  refine max_le ?_ ?_
  · nlinarith [mul_nonneg (sub_nonneg.2 hD) h1]
  · -- `D + m(4 − 6σ) ≤ (4D − 2m)(1 − σ)` is `(2m − D)(4σ − 3) ≥ 0`
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * m - D) (by linarith : (0 : ℝ) ≤ 4 * σ - 3)]

/-- The count exponent of the Halász–Montgomery count with the library's kernel bound
(`ShortSieveCount.card_le_hux`) on the `k`-th power, with the window `T₀ = N^{(24kσ − 13k)/5}` that the kernel's
`Λ^{1/12}T₀^{5/12}` allows: `max(2k(1 − σ), D + k(23/5 − 34σ/5))`. -/
noncomputable def eHM (D : ℝ) (k : ℕ) (σ : ℝ) : ℝ := max (2 * k * (1 - σ)) (D + k * (23 / 5 - 34 / 5 * σ))

/-- Above `3/4` the library's Halász–Montgomery count is at least as good as Huxley's: `e_HM ≤ e_H`. -/
theorem eHM_le_eH {D σ : ℝ} {k : ℕ} (hσ : 3 / 4 ≤ σ) : eHM D k σ ≤ eH D k σ := by
  unfold eHM eH
  refine max_le_max le_rfl ?_
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_nonneg hk (by linarith : (0 : ℝ) ≤ σ - 3 / 4)]

/-- **The library's count above `3/4`.** Under the hypotheses of `hux_exp_le_of_three_quarters_le`, the
Halász–Montgomery count on `L^m` has exponent at most `δ(1 − σ)`. -/
theorem hm_exp_le_of_three_quarters_le {D δ σ : ℝ} {m : ℕ} (hm : 1 ≤ m) (hD : (m : ℝ) ≤ D)
    (hD' : D ≤ m + 1 / 2) (hδ : 4 * D - 2 * m ≤ δ) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) :
    eHM D m σ ≤ δ * (1 - σ) :=
  (eHM_le_eH hσ).trans (hux_exp_le_of_three_quarters_le hm hD hD' hδ hσ hσ1)

/-- **Harman's exponent from the mean value theorem and Huxley's estimate.** For `m ≥ 1`, `D ∈ (m, m + 1/2]` and
`δ ≥ 4D − 2m`, at every `σ ∈ [1/2, 1]` one of the two estimates on `L^m` has count exponent at most `δ(1 − σ)`. -/
theorem dreq_hux {D δ σ : ℝ} {m : ℕ} (hm : 1 ≤ m) (hD : (m : ℝ) < D) (hD' : D ≤ m + 1 / 2)
    (hδ : 4 * D - 2 * m ≤ δ) (hσ1 : σ ≤ 1) :
    eMV D m σ ≤ δ * (1 - σ) ∨ eH D m σ ≤ δ * (1 - σ) := by
  rcases le_total σ (3 / 4) with h | h
  · exact Or.inl (mv_exp_le_of_le_three_quarters hD hδ h)
  · exact Or.inr (hux_exp_le_of_three_quarters_le hm hD.le hD' hδ h hσ1)

end ShortSieveDreq
