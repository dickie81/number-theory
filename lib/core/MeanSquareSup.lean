import Mathlib

/-!
# A uniform bound for most of a family, from mean squares

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, the analytic inputs: the twists): a
discrete Sobolev inequality combined with Markov's, which picks a good prime from a family.

Each member `p` of a finite family `P` has a sequence `S p k` of complex numbers. On an interval `[K₀, K₁]` with
`K₀ ≥ 1`, suppose that the mean square of `S p k` over `P` is at most `M₀ k`, and that of the increment
`S p (k + 1) − S p k` is at most `M₁ k`. With the weight `w k = k^{−(1+2ε)}`, `ε ≥ 0`, `card_bad_le` bounds the number
of bad `p`, those with `‖S p k‖² > c·k^{1+2ε}` at some `k ∈ [K₀, K₁]`:
`c·#{bad p} ≤ #P·(M₀ K₀·w K₀ + Σ_{K₀ ≤ k < K₁} (√(M₁ k)·(√(M₀ k) + √(M₀ (k + 1)))·w k + M₀ k·(w k − w (k + 1))))`.

Proof, with `F p k = ‖S p k‖²·w k`:

1. **Sobolev.** On `[K₀, K₁]`, `F p k ≤ G p = F p K₀ + Σ_{K₀ ≤ j < K₁} |F p (j + 1) − F p j|`, by telescoping.
2. **Markov.** A bad `p` has `G p ≥ F p k > c` for some `k`, and `G ≥ 0`, so `c·#{bad p} ≤ Σ_p G p`.
3. **Increments** (`abs_step_le`). As `w` decreases and `|‖a‖ − ‖b‖| ≤ ‖a − b‖`,
   `|F p (j + 1) − F p j| ≤ ‖S p (j + 1) − S p j‖·(‖S p j‖ + ‖S p (j + 1)‖)·w j + ‖S p j‖²·(w j − w (j + 1))`.
4. **Cauchy–Schwarz.** Summed over `P`, `Σ_p ‖S p (j + 1) − S p j‖·‖S p k‖ ≤ #P·√(M₁ j)·√(M₀ k)` for `k = j, j + 1`.
-/

namespace MeanSquareSup

open Finset

/-- The weight `w ε k = k^{−(1+2ε)}`: `‖S p k‖²·w ε k > c` says that `‖S p k‖² > c·k^{1+2ε}`. -/
noncomputable def w (ε : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) ^ (-(1 + 2 * ε))

/-- One step of `‖x‖²` against a decreasing weight: if `0 ≤ v ≤ u`, then
`|‖y‖²·v − ‖x‖²·u| ≤ ‖y − x‖·(‖x‖ + ‖y‖)·u + ‖x‖²·(u − v)`, since `|‖y‖ − ‖x‖| ≤ ‖y − x‖`. -/
theorem abs_step_le {E : Type*} [SeminormedAddCommGroup E] (x y : E) {u v : ℝ} (hv : 0 ≤ v) (huv : v ≤ u) :
    |‖y‖ ^ 2 * v - ‖x‖ ^ 2 * u| ≤ ‖y - x‖ * ‖x‖ * u + ‖y - x‖ * ‖y‖ * u + ‖x‖ ^ 2 * (u - v) := by
  have hd := abs_sub_le_iff.1 (abs_norm_sub_norm_le y x)
  have hxy := add_nonneg (norm_nonneg x) (norm_nonneg y)
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hxy hv, mul_nonneg (norm_nonneg (y - x)) hxy]

/-- **Mean squares bound most of a family uniformly**: `c` times the number of `p ∈ P` with `‖S p k‖² > c·k^{1+2ε}`
somewhere on `[K₀, K₁]` is at most `#P` times a sum of the mean-square bounds `M₀`, `M₁` against the weight `w ε`. -/
theorem card_bad_le {ι : Type*} (P : Finset ι) (S : ι → ℕ → ℂ) {K₀ K₁ : ℕ} (hK₀ : 1 ≤ K₀) (hK : K₀ ≤ K₁)
    {ε c : ℝ} (hε : 0 ≤ ε) (M₀ M₁ : ℕ → ℝ)
    (h0 : ∀ k ∈ Icc K₀ K₁, ∑ p ∈ P, ‖S p k‖ ^ 2 ≤ P.card * M₀ k)
    (h1 : ∀ k ∈ Ico K₀ K₁, ∑ p ∈ P, ‖S p (k + 1) - S p k‖ ^ 2 ≤ P.card * M₁ k) :
    c * (P.filter fun p => ∃ k ∈ Icc K₀ K₁, c * (k : ℝ) ^ (1 + 2 * ε) < ‖S p k‖ ^ 2).card ≤
      P.card * (M₀ K₀ * w ε K₀ + ∑ k ∈ Ico K₀ K₁,
        (√(M₁ k) * (√(M₀ k) + √(M₀ (k + 1))) * w ε k + M₀ k * (w ε k - w ε (k + 1)))) := by
  have hw (k : ℕ) : 0 ≤ w ε k := Real.rpow_nonneg k.cast_nonneg _
  have hw' (k : ℕ) (hk : K₀ ≤ k) : w ε (k + 1) ≤ w ε k :=
    Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.2 (hK₀.trans hk)) (by simp) (by linarith)
  obtain ⟨F, hF⟩ : ∃ F : ι → ℕ → ℝ, ∀ p k, F p k = ‖S p k‖ ^ 2 * w ε k := ⟨_, fun _ _ => rfl⟩
  -- Sobolev: on `[K₀, K₁]`, `F p` is at most its value at `K₀` plus its total variation.
  have sob (p : ι) (k : ℕ) (hk : k ∈ Icc K₀ K₁) :
      F p k ≤ F p K₀ + ∑ j ∈ Ico K₀ K₁, |F p (j + 1) - F p j| := by
    rw [← sub_le_iff_le_add', ← sum_Ico_sub (F p) (mem_Icc.1 hk).1]
    exact (sum_le_sum fun j _ => le_abs_self _).trans
      (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (mem_Icc.1 hk).2) fun j _ _ => abs_nonneg _)
  -- Markov: the bound is nonnegative, and at least `c` at a bad `p`.
  trans ∑ p ∈ P, (F p K₀ + ∑ j ∈ Ico K₀ K₁, |F p (j + 1) - F p j|)
  · rw [← nsmul_eq_mul']
    refine (card_nsmul_le_sum _ _ _ fun p hp => ?_).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun p _ _ => (hF p K₀ ▸ mul_nonneg (sq_nonneg _) (hw K₀)).trans (sob p K₀ (left_mem_Icc.2 hK)))
    obtain ⟨k, hk, hlt⟩ := (mem_filter.1 hp).2
    refine le_trans ?_ (sob p k hk)
    rw [hF, w, Real.rpow_neg k.cast_nonneg,
      le_mul_inv_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.2 (hK₀.trans (mem_Icc.1 hk).1)) _)]
    exact hlt.le
  -- Sum over `P`: the value at `K₀` is at most `#P·M₀ K₀·w K₀`.
  rw [sum_add_distrib, sum_comm, mul_add, mul_sum]
  gcongr with j hj
  · simpa only [hF, ← sum_mul, mul_assoc] using mul_le_mul_of_nonneg_right (h0 _ (left_mem_Icc.2 hK)) (hw K₀)
  -- The increments, summed over `P` with Cauchy–Schwarz.
  obtain ⟨hj0, hj1⟩ := mem_Ico.1 hj
  have cs (k : ℕ) (hk : k ∈ Icc K₀ K₁) :
      ∑ p ∈ P, ‖S p (j + 1) - S p j‖ * ‖S p k‖ ≤ P.card * (√(M₁ j) * √(M₀ k)) := by
    have h := Nat.cast_nonneg (α := ℝ) P.card
    grw [Real.sum_mul_le_sqrt_mul_sqrt, h1 j hj, h0 k hk, Real.sqrt_mul h, Real.sqrt_mul h, mul_mul_mul_comm,
      Real.mul_self_sqrt h]
  simp only [hF]
  refine (sum_le_sum fun p _ => abs_step_le (S p j) (S p (j + 1)) (hw (j + 1)) (hw' j hj0)).trans ?_
  simp only [sum_add_distrib, ← sum_mul]
  linarith [mul_le_mul_of_nonneg_right (cs j (Ico_subset_Icc_self hj)) (hw j),
    mul_le_mul_of_nonneg_right (cs (j + 1) (mem_Icc.2 ⟨by omega, hj1⟩)) (hw j),
    mul_le_mul_of_nonneg_right (h0 j (Ico_subset_Icc_self hj)) (sub_nonneg.2 (hw' j hj0))]

end MeanSquareSup

#print axioms MeanSquareSup.card_bad_le
