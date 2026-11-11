/-
# The leaves by the bilinear estimate without `2HDm < q`: families and a block pair

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTypeIBFam` and `SieveTypeIBEv` bring the bilinear Type I estimate `SieveSpline.typeIB_spline` to a block pair
of the leaves: the estimate over families with comparisons (`typeIB_smooth`, `typeIB_sharp0`), then a block pair
(`pair_le`), where the cut of the frequencies is `H = ⌊(q − 1)/(2D_m)⌋`, the largest with `2HD_m < q`. This file is
the same with `SieveSpline.typeIB_spline_wide`, which asks only `2H < q` and counts the diagonal on the congruence.

* `typeIB_smooth_wide`, `typeIB_sharp0_wide`: the estimate over a family with smooth, then sharp, comparisons, for
  `2H < q`: the bounds of `typeIB_smooth` and `typeIB_sharp0` with `F(⌊2HDm/q⌋ + 1)` in place of `F`.
* `bdPW`, `pair_le_wide`: a block pair `(β₁, β₂)` with any cut `H`, `2H < q`, and `d(n) ≤ F` for `0 < n ≤ H⌊P₂⌋`:
  the bilinear sum is at most `(∏_j ‖𝓕G_j‖₁ + Σ_j ‖𝓕M_j‖₁)M_fM₂·bdPW` plus the near-boundary masses, with
  `bdPW = √(P₁P₂(P₁/q + 1)F(2HP₂/q + 1)(n/q + 1)n) + (B − A)(q/(2ℓ(H + 1)))^r P₁P₂ + P₁P₂d(q)/φ(q)`,
  `P_i = ρ^{β_i+1}` and `n` the spline's length.

With `H = ⌊(q − 1)/(2D_m)⌋` the factor `2HP₂/q + 1` is at most `2` and the second term is at most
`(B − A)(P₂/ℓ)^r P₁P₂`: `pair_le`, which needs `P₂ ≤ ℓ`, that is `d₁d₂² ≤ x` up to the step's constants. A larger `H`
makes the second term small for any `P₂` at the price of the factor `2HP₂/q + 1` under the root: with
`H ≈ qY/ℓ` it is `Y^{−r}` against `2YP₂/ℓ + 1`. So the estimate reaches leaves with `d₁d₂² > x`, where the paper's
Lemma 4.3 stops; the sum over the block pairs and the asymptotic form (`SieveTypeIBSum`, `SieveTypeIBAsym`) are not
redone here.

The proofs are those of `SieveTypeIBFam` and `SieveTypeIBEv`.

The file imports `SieveTypeIBEv.lean` and `SieveTypeIBWide.lean`.
-/
import SieveTypeIBEv
import SieveTypeIBWide

open Finset Complex MeasureTheory
open scoped FourierTransform

namespace SieveTypeIBPairWide

open SieveTypeIB SieveSpline SieveTypeIBFam SieveTypeIBLeaf SieveTypeIBEv

variable {q : ℕ} [NeZero q]

/-- **The bilinear Type I estimate without `2HDm < q`, over a family with smooth comparisons.** Let `J` continuous
integrable `g_j` with integrable `𝓕g_j` be applied to the forms `φ_j(y₁) + ψ_j(y₂)`. Under the conditions of
`SieveSpline.typeIB_spline_wide` on the values (`π₂ ≤ Dm`, `2H < q`),
`|Σ_{y₁,y₂} a₁a₂ ∏_j g_j(φ_j(y₁) + ψ_j(y₂)) Σ_k w(k)dw(π₁(y₁)π₂(y₂)k)|` is at most `∏_j ‖𝓕g_j‖₁` times
`SieveSpline.typeIB_spline_wide`'s bound with the fibres' aggregates `A₁`, `A₂` of `|a₁|`, `|a₂|`: the bound of
`SieveTypeIBFam.typeIB_smooth` with `F(⌊2HDm/q⌋ + 1)` in place of `F`. -/
theorem typeIB_smooth_wide (a : ZMod q) (ha : IsUnit a) {ι₁ ι₂ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂)
    (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ) (a₁ : ι₁ → ℂ) (a₂ : ι₂ → ℂ) {J : Type*} [Fintype J] {g : J → ℝ → ℂ}
    (hgc : ∀ j, Continuous (g j)) (hgi : ∀ j, Integrable (g j)) (hgf : ∀ j, Integrable (𝓕 (g j)))
    (φ : J → ι₁ → ℝ) (ψ : J → ι₂ → ℝ) (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) {H Dm F m : ℕ}
    (hπ₂ : ∀ y ∈ Y₂, 0 < π₂ y) (hDm : ∀ y ∈ Y₂, π₂ y ≤ Dm) (hq2 : 2 * H < q)
    (hm : ∀ r : ZMod q, #((Y₁.image π₁).filter (fun d : ℕ => IsUnit (d : ZMod q) ∧ ((d : ZMod q))⁻¹ = r)) ≤ m)
    (hF : ∀ t : ℤ, t ≠ 0 → t.natAbs ≤ H → ∀ y ∈ Y₂, (t.natAbs * π₂ y).divisors.card ≤ F) :
    ‖∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, a₁ y₁ * a₂ y₂ * (∏ j, g j (φ j y₁ + ψ j y₂)) *
        ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * SieveFamily.dw q a (π₁ y₁ * π₂ y₂ * k)‖ ≤
      (∏ j, ∫ t, ‖𝓕 (g j) t‖) *
        (√(∑ d ∈ Y₁.image π₁, (∑ y ∈ Y₁.filter (fun y => π₁ y = d), ‖a₁ y‖) ^ 2) *
            √(m * ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) * (∑ d ∈ Y₂.image π₂, (∑ y ∈ Y₂.filter (fun y => π₂ y = d), ‖a₂ y‖) ^ 2) *
              ((((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * (B + r * (ℓ - 1) - A : ℕ))) +
          ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r * ((∑ y ∈ Y₁, ‖a₁ y‖) * (∑ y ∈ Y₂, ‖a₂ y‖)) +
          (∑ y ∈ Y₁, ‖a₁ y‖) * (∑ y ∈ Y₂, ‖a₂ y‖) * (q.divisors.card / q.totient)) := by
  classical
  set X : ℕ → ℂ := fun d => ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * SieveFamily.dw q a (d * k) with hX
  set A₁ : ℕ → ℝ := fun d => ∑ y ∈ Y₁.filter (fun y => π₁ y = d), ‖a₁ y‖ with hA₁
  set A₂ : ℕ → ℝ := fun d => ∑ y ∈ Y₂.filter (fun y => π₂ y = d), ‖a₂ y‖ with hA₂
  set n₀ : ℝ := (((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * (B + r * (ℓ - 1) - A : ℕ) with hn₀
  set W : ℝ := ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r with hW
  set Bd : ℝ := √(∑ d ∈ Y₁.image π₁, A₁ d ^ 2) * √(m * ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) * (∑ d ∈ Y₂.image π₂, A₂ d ^ 2) * n₀) +
      W * ((∑ y ∈ Y₁, ‖a₁ y‖) * (∑ y ∈ Y₂, ‖a₂ y‖)) +
      (∑ y ∈ Y₁, ‖a₁ y‖) * (∑ y ∈ Y₂, ‖a₂ y‖) * (q.divisors.card / q.totient) with hBd
  -- the sum as a separated integral
  have hL : ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, a₁ y₁ * a₂ y₂ * (∏ j, g j (φ j y₁ + ψ j y₂)) * X (π₁ y₁ * π₂ y₂) =
      ∑ y ∈ Y₁ ×ˢ Y₂, (a₁ y.1 * a₂ y.2 * X (π₁ y.1 * π₂ y.2)) * ∏ j, g j (φ j y.1 + ψ j y.2) := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun y₁ _ => Finset.sum_congr rfl fun y₂ _ => by ring
  rw [hL, SieveSep.sum_sep (Y₁ ×ˢ Y₂) _ (fun j y => φ j y.1 + ψ j y.2) hgc hgi hgf, mul_comm _ Bd]
  refine norm_integral_prod_le hgf fun ξ => ?_
  -- for each height `ξ`, the bilinear form with twisted coefficients
  set t₁ : ι₁ → ℂ := fun y => a₁ y * Complex.exp (2 * Real.pi * I * ∑ j, (ξ j : ℂ) * φ j y) with ht₁
  set t₂ : ι₂ → ℂ := fun y => a₂ y * Complex.exp (2 * Real.pi * I * ∑ j, (ξ j : ℂ) * ψ j y) with ht₂
  set α : ℕ → ℂ := fun d => ∑ y ∈ Y₁.filter (fun y => π₁ y = d), t₁ y with hα
  set β : ℕ → ℂ := fun d => ∑ y ∈ Y₂.filter (fun y => π₂ y = d), t₂ y with hβ
  set D₁ := (Y₁.image π₁).filter (fun d : ℕ => IsUnit (d : ZMod q)) with hD₁
  set D₂ := (Y₂.image π₂).filter (fun d : ℕ => IsUnit (d : ZMod q)) with hD₂
  have hXu : ∀ d₁ d₂ : ℕ, ¬ (IsUnit (d₁ : ZMod q) ∧ IsUnit (d₂ : ZMod q)) → X (d₁ * d₂) = 0 := by
    intro d₁ d₂ h
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [dw_of_not_isUnit ha, mul_zero]
    intro hu
    push_cast at hu
    exact h ⟨isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu),
      isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)⟩
  have hform : ∑ y ∈ Y₁ ×ˢ Y₂, a₁ y.1 * a₂ y.2 * X (π₁ y.1 * π₂ y.2) *
        Complex.exp (2 * Real.pi * I * ∑ j, (ξ j : ℂ) * (φ j y.1 + ψ j y.2 : ℝ)) =
      ∑ d₁ ∈ D₁, ∑ d₂ ∈ D₂, α d₁ * β d₂ * X (d₁ * d₂) := by
    -- the twist splits
    have h1 : ∑ y ∈ Y₁ ×ˢ Y₂, a₁ y.1 * a₂ y.2 * X (π₁ y.1 * π₂ y.2) *
          Complex.exp (2 * Real.pi * I * ∑ j, (ξ j : ℂ) * (φ j y.1 + ψ j y.2 : ℝ)) =
        ∑ y₁ ∈ Y₁, t₁ y₁ * ∑ y₂ ∈ Y₂, t₂ y₂ * X (π₁ y₁ * π₂ y₂) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun y₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y₂ _ => ?_
      rw [ht₁, ht₂]
      simp only
      have e : 2 * Real.pi * I * ∑ j, (ξ j : ℂ) * ((φ j y₁ + ψ j y₂ : ℝ) : ℂ) =
          2 * Real.pi * I * ∑ j, (ξ j : ℂ) * φ j y₁ + 2 * Real.pi * I * ∑ j, (ξ j : ℂ) * ψ j y₂ := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
      rw [e, Complex.exp_add]
      ring
    -- the fibres of `π₁`, then of `π₂`
    have h2 : ∀ d₁ : ℕ, ∑ y₂ ∈ Y₂, t₂ y₂ * X (d₁ * π₂ y₂) = ∑ d₂ ∈ Y₂.image π₂, β d₂ * X (d₁ * d₂) :=
      fun d₁ => sum_fiber Y₂ π₂ t₂ (fun d₂ => X (d₁ * d₂))
    rw [h1, sum_fiber Y₁ π₁ t₁ (fun d₁ => ∑ y₂ ∈ Y₂, t₂ y₂ * X (d₁ * π₂ y₂))]
    simp only [h2, Finset.mul_sum]
    -- the values not prime to `q` contribute `0`
    rw [sum_units_eq (Y₁.image π₁) (Y₂.image π₂) (fun d₁ d₂ => α d₁ * (β d₂ * X (d₁ * d₂)))
      fun d₁ d₂ h => by rw [hXu d₁ d₂ h, mul_zero, mul_zero]]
    exact Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => by ring
  have hform' : ∑ y ∈ Y₁ ×ˢ Y₂, a₁ y.1 * a₂ y.2 * X (π₁ y.1 * π₂ y.2) *
        Complex.exp (2 * Real.pi * I * ∑ j, (ξ j : ℂ) * (fun j y => φ j y.1 + ψ j y.2) j y) =
      ∑ d₁ ∈ D₁, ∑ d₂ ∈ D₂, α d₁ * β d₂ * X (d₁ * d₂) := hform
  rw [hform']
  -- the bound of `typeIB_spline`
  have hD₁u : ∀ d ∈ D₁, IsUnit (d : ZMod q) := fun d hd => (Finset.mem_filter.1 hd).2
  have hD₂u : ∀ d ∈ D₂, IsUnit (d : ZMod q) := fun d hd => (Finset.mem_filter.1 hd).2
  have hD₂img : ∀ d ∈ D₂, ∃ y ∈ Y₂, π₂ y = d := fun d hd => Finset.mem_image.1 (Finset.mem_filter.1 hd).1
  have hD₂0 : ∀ d ∈ D₂, 0 < d := fun d hd => by
    obtain ⟨y, hy, rfl⟩ := hD₂img d hd; exact hπ₂ y hy
  have hDm' : ∀ d ∈ D₂, d ≤ Dm := fun d hd => by
    obtain ⟨y, hy, rfl⟩ := hD₂img d hd; exact hDm y hy
  have hm' : ∀ r : ZMod q, #(D₁.filter (fun d : ℕ => ((d : ZMod q))⁻¹ = r)) ≤ m := fun r => by
    rw [hD₁, Finset.filter_filter]; exact hm r
  have hF' : ∀ t : ℤ, t ≠ 0 → t.natAbs ≤ H → ∀ d ∈ D₂, (t.natAbs * d).divisors.card ≤ F := fun t ht htH d hd => by
    obtain ⟨y, hy, rfl⟩ := hD₂img d hd; exact hF t ht htH y hy
  have hb := typeIB_spline_wide a ha D₁ D₂ α β hD₁u hD₂u hD₂0 A B ℓ r hℓ hDm' hq2 hm' hF'
  refine hb.trans ?_
  -- the coefficients against their aggregates
  have hαA : ∀ d, ‖α d‖ ≤ A₁ d := fun d => (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl
    fun y _ => norm_twist (a₁ y) ξ (fun j => φ j y)))
  have hβA : ∀ d, ‖β d‖ ≤ A₂ d := fun d => (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl
    fun y _ => norm_twist (a₂ y) ξ (fun j => ψ j y)))
  have hA₁0 : ∀ d, 0 ≤ A₁ d := fun d => Finset.sum_nonneg fun y _ => norm_nonneg _
  have hA₂0 : ∀ d, 0 ≤ A₂ d := fun d => Finset.sum_nonneg fun y _ => norm_nonneg _
  have hsq₁ : ∑ d ∈ D₁, ‖α d‖ ^ 2 ≤ ∑ d ∈ Y₁.image π₁, A₁ d ^ 2 :=
    (Finset.sum_le_sum fun d _ => pow_le_pow_left₀ (norm_nonneg _) (hαA d) 2).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d _ _ => sq_nonneg _)
  have hsq₂ : ∑ d ∈ D₂, ‖β d‖ ^ 2 ≤ ∑ d ∈ Y₂.image π₂, A₂ d ^ 2 :=
    (Finset.sum_le_sum fun d _ => pow_le_pow_left₀ (norm_nonneg _) (hβA d) 2).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d _ _ => sq_nonneg _)
  have hl1₁ : ∑ d ∈ D₁, ‖α d‖ ≤ ∑ y ∈ Y₁, ‖a₁ y‖ := by
    rw [← sum_fiber_norm Y₁ π₁ a₁]
    exact (Finset.sum_le_sum fun d _ => hαA d).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d _ _ => hA₁0 d)
  have hl1₂ : ∑ d ∈ D₂, ‖β d‖ ≤ ∑ y ∈ Y₂, ‖a₂ y‖ := by
    rw [← sum_fiber_norm Y₂ π₂ a₂]
    exact (Finset.sum_le_sum fun d _ => hβA d).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d _ _ => hA₂0 d)
  have hW0 : 0 ≤ W := by positivity
  have hdq : (0 : ℝ) ≤ q.divisors.card / q.totient := by positivity
  refine add_le_add (add_le_add ?_ ?_) ?_
  · refine mul_le_mul (Real.sqrt_le_sqrt hsq₁) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hn0 : 0 ≤ n₀ := by positivity
    have hmF : (0 : ℝ) ≤ m * ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq₂ hmF) hn0
  · exact mul_le_mul_of_nonneg_left (mul_le_mul hl1₁ hl1₂ (Finset.sum_nonneg fun d _ => norm_nonneg _)
      (Finset.sum_nonneg fun y _ => norm_nonneg _)) hW0
  · refine mul_le_mul_of_nonneg_right (mul_le_mul ((norm_sum_le _ _).trans hl1₁) ((norm_sum_le _ _).trans hl1₂)
      (norm_nonneg _) (Finset.sum_nonneg fun y _ => norm_nonneg _)) hdq


/-- **Sharp comparisons without `2HDm < q`**: for `2H < q` the bound is
`∏_j ‖𝓕G_j‖₁·bd + Σ_j (2φ(q)⁻¹(B − A)Σ_y |a₁||a₂|M_j(ℓ_j) + ‖𝓕M_j‖₁·bd)`, with `bd` the bound `bdIB` of
`SieveTypeIBFam.typeIB_sharp0` at `F(⌊2HDm/q⌋ + 1)` in place of `F`. -/
theorem typeIB_sharp0_wide (a : ZMod q) (ha : IsUnit a) {ι₁ ι₂ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂)
    (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ) (a₁ : ι₁ → ℂ) (a₂ : ι₂ → ℂ) {J : ℕ} (I : Fin J → ι₁ → ι₂ → ℝ)
    (Gs Ms : Fin J → ℝ → ℝ) (hGc : ∀ j, Continuous (fun u => ((Gs j u : ℝ) : ℂ)))
    (hGi : ∀ j, Integrable (fun u => ((Gs j u : ℝ) : ℂ))) (hGf : ∀ j, Integrable (𝓕 (fun u => ((Gs j u : ℝ) : ℂ))))
    (hMc : ∀ j, Continuous (fun u => ((Ms j u : ℝ) : ℂ))) (hMi : ∀ j, Integrable (fun u => ((Ms j u : ℝ) : ℂ)))
    (hMf : ∀ j, Integrable (𝓕 (fun u => ((Ms j u : ℝ) : ℂ))))
    (φ : Fin J → ι₁ → ℝ) (ψ : Fin J → ι₂ → ℝ)
    (hI : ∀ j y₁ y₂, 0 ≤ I j y₁ y₂ ∧ I j y₁ y₂ ≤ 1) (hG : ∀ j u, 0 ≤ Gs j u ∧ Gs j u ≤ 1)
    (hIG : ∀ j y₁ y₂, |I j y₁ y₂ - Gs j (φ j y₁ + ψ j y₂)| ≤ Ms j (φ j y₁ + ψ j y₂))
    (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) {H Dm F m : ℕ}
    (hπ₂ : ∀ y ∈ Y₂, 0 < π₂ y) (hDm : ∀ y ∈ Y₂, π₂ y ≤ Dm) (hq2 : 2 * H < q)
    (hm : ∀ r : ZMod q, #((Y₁.image π₁).filter (fun d : ℕ => IsUnit (d : ZMod q) ∧ ((d : ZMod q))⁻¹ = r)) ≤ m)
    (hF : ∀ t : ℤ, t ≠ 0 → t.natAbs ≤ H → ∀ y ∈ Y₂, (t.natAbs * π₂ y).divisors.card ≤ F) :
    ‖∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, a₁ y₁ * a₂ y₂ * (∏ j, (I j y₁ y₂ : ℂ)) *
        ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * SieveFamily.dw q a (π₁ y₁ * π₂ y₂ * k)‖ ≤
      (∏ j, ∫ t, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) t‖) * bdIB q Y₁ Y₂ π₁ π₂ a₁ a₂ A B ℓ r H (F * (2 * (H * Dm) / q + 1)) m +
        ∑ j, (2 * (q.totient : ℝ)⁻¹ * (((B - A : ℕ) : ℝ) *
            ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, ‖a₁ y₁‖ * ‖a₂ y₂‖ * Ms j (φ j y₁ + ψ j y₂)) +
          (∫ t, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) t‖) * bdIB q Y₁ Y₂ π₁ π₂ a₁ a₂ A B ℓ r H (F * (2 * (H * Dm) / q + 1)) m) := by
  classical
  set T := Y₁ ×ˢ (Y₂ ×ˢ supp A B ℓ r) with hT
  set nn : ι₁ × ι₂ × ℕ → ℕ := fun x => π₁ x.1 * π₂ x.2.1 * x.2.2 with hnn
  set w : ι₁ × ι₂ × ℕ → ℂ := fun x => a₁ x.1 * a₂ x.2.1 * ((spl A B ℓ r x.2.2 : ℝ) : ℂ) with hw
  set ℓf : Fin J → ι₁ × ι₂ × ℕ → ℝ := fun j x => φ j x.1 + ψ j x.2.1 with hℓf
  have hregroup : ∀ (b₁ : ι₁ → ℂ) (b₂ : ι₂ → ℂ) (c : ι₁ → ι₂ → ℂ),
      SieveFamily.Dsum q a T nn (fun x => b₁ x.1 * b₂ x.2.1 * ((spl A B ℓ r x.2.2 : ℝ) : ℂ) * c x.1 x.2.1) =
        ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, b₁ y₁ * b₂ y₂ * c y₁ y₂ *
          ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * SieveFamily.dw q a (π₁ y₁ * π₂ y₂ * k) := by
    intro b₁ b₂ c
    rw [SieveFamily.Dsum, hT, Finset.sum_product]
    refine Finset.sum_congr rfl fun y₁ _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun y₂ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hnn]
    ring
  have hsharp := SieveFamily.norm_Dsum_sharp_le (a := a) T nn w (fun j x => I j x.1 x.2.1)
    (fun j x => Gs j (ℓf j x)) (fun j x => Ms j (ℓf j x)) (fun j x => hI j x.1 x.2.1) (fun j x => hG j (ℓf j x))
    (fun j x => hIG j x.1 x.2.1)
  have eI := hregroup a₁ a₂ (fun y₁ y₂ => ∏ j, (I j y₁ y₂ : ℂ))
  beta_reduce at eI
  rw [eI] at hsharp
  refine hsharp.trans (add_le_add ?_ (Finset.sum_le_sum fun j _ => add_le_add ?_ ?_))
  · have eG := hregroup a₁ a₂ (fun y₁ y₂ => ∏ j, ((Gs j (φ j y₁ + ψ j y₂) : ℝ) : ℂ))
    beta_reduce at eG
    rw [eG]
    exact typeIB_smooth_wide a ha Y₁ Y₂ π₁ π₂ a₁ a₂ hGc hGi hGf φ ψ A B ℓ r hℓ hπ₂ hDm hq2 hm hF
  · have hmass : ∑ x ∈ T, ‖w x‖ * Ms j (ℓf j x) =
        ((B - A : ℕ) : ℝ) * ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, ‖a₁ y₁‖ * ‖a₂ y₂‖ * Ms j (φ j y₁ + ψ j y₂) := by
      rw [hT, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y₁ _ => ?_
      rw [Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y₂ _ => ?_
      have hk : ∀ k, ‖w (y₁, y₂, k)‖ * Ms j (ℓf j (y₁, y₂, k)) =
          ‖a₁ y₁‖ * ‖a₂ y₂‖ * Ms j (φ j y₁ + ψ j y₂) * spl A B ℓ r k := by
        intro k
        simp only [hw, hℓf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (spl_nonneg _ _ _ _ _)]
        ring
      simp only [hk]
      rw [← Finset.mul_sum, sum_spl A B ℓ r hℓ]
      ring
    rw [hmass]
  · have hw' : (fun x : ι₁ × ι₂ × ℕ => ((‖w x‖ * Ms j (ℓf j x) : ℝ) : ℂ)) =
        fun x => ((‖a₁ x.1‖ : ℝ) : ℂ) * ((‖a₂ x.2.1‖ : ℝ) : ℂ) * ((spl A B ℓ r x.2.2 : ℝ) : ℂ) *
          ∏ _i : Fin 1, ((Ms j (φ j x.1 + ψ j x.2.1) : ℝ) : ℂ) := by
      funext x
      simp only [hw, hℓf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (spl_nonneg _ _ _ _ _),
        Fin.prod_univ_one]
      push_cast
      ring
    have eM := hregroup (fun y => ((‖a₁ y‖ : ℝ) : ℂ)) (fun y => ((‖a₂ y‖ : ℝ) : ℂ))
      (fun y₁ y₂ => ∏ _i : Fin 1, ((Ms j (φ j y₁ + ψ j y₂) : ℝ) : ℂ))
    beta_reduce at eM
    rw [hw', eM]
    have h1 := typeIB_smooth_wide a ha Y₁ Y₂ π₁ π₂ (fun y => ((‖a₁ y‖ : ℝ) : ℂ)) (fun y => ((‖a₂ y‖ : ℝ) : ℂ))
      (g := fun _ : Fin 1 => fun u => ((Ms j u : ℝ) : ℂ)) (fun _ => hMc j) (fun _ => hMi j) (fun _ => hMf j)
      (fun _ => φ j) (fun _ => ψ j) A B ℓ r hℓ hπ₂ hDm hq2 hm hF
    refine h1.trans (le_of_eq ?_)
    have h2 := bdIB_norm (q := q) Y₁ Y₂ π₁ π₂ a₁ a₂ A B ℓ r H (F * (2 * (H * Dm) / q + 1)) m
    rw [bdIB] at h2
    rw [h2, Fin.prod_univ_one, bdIB]


/-- A block pair's bound with the cut `H` of the frequencies. With `P_i = ρ^{β_i+1}` and the spline's length `n`:
`√(P₁P₂(P₁/q + 1)F(2HP₂/q + 1)(n/q + 1)n) + (B − A)(q/(2ℓ(H + 1)))^r P₁P₂ + P₁P₂d(q)/φ(q)`. -/
noncomputable def bdPW (q : ℕ) (ρ : ℝ) (β₁ β₂ : ℕ) (t : ℕ × ℕ × ℕ × ℕ) (F H : ℕ) : ℝ :=
  √(ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) * (ρ ^ (β₁ + 1) / q + 1) * (F * (2 * H * ρ ^ (β₂ + 1) / q + 1)) *
      (lenv t / q + 1) * lenv t) +
    massv t * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 * (ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1)) +
    ρ ^ (β₁ + 1) * ρ ^ (β₂ + 1) * ((q.divisors.card : ℝ) / q.totient)

/-- **A block pair, without `2HDm < q`.** Let the comparisons `c = ∏_j I_j` of `SieveTypeIBFam.typeIB_sharp0` be
given, every value `π₁(y₁)`, `π₂(y₂)`, `f_σ` at least `1`, and the fibres bounded: `Σ_{π₁(y₁)f_σ = d} |λ_σ| ≤ M_f` and
`#{y₂ : π₂(y₂) = d} ≤ M₂`. Let `H` be any cut of the frequencies with `2H < q` (`hH`), and let `d(n) ≤ F` for
`0 < n ≤ H⌊ρ^{β₂+1}⌋` (`hF`). The bilinear sum of the block pair `(β₁, β₂)` of `blk ρ` with the spline `t` is at most
`(∏_j ‖𝓕G_j‖₁ + Σ_j ‖𝓕M_j‖₁)·M_fM₂·bdPW` plus the near-boundary masses
`Σ_j 2φ(q)⁻¹(B − A)Σ_{(y₁,σ),y₂} |λ_σ|M_j(ℓ_j)` over the block pair. -/
theorem pair_le_wide (a : ZMod q) (ha : IsUnit a) {ι₁ ι₂ κ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂)
    (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ) (S : Finset κ) (f : κ → ℕ) (lam : κ → ℝ) (c : ι₁ → ι₂ → ℝ)
    {J : ℕ} (I : Fin J → ι₁ → ι₂ → ℝ) (hc : ∀ y₁ y₂, c y₁ y₂ = ∏ j, I j y₁ y₂)
    (Gs Ms : Fin J → ℝ → ℝ) (hGc : ∀ j, Continuous (fun u => ((Gs j u : ℝ) : ℂ)))
    (hGi : ∀ j, Integrable (fun u => ((Gs j u : ℝ) : ℂ))) (hGf : ∀ j, Integrable (𝓕 (fun u => ((Gs j u : ℝ) : ℂ))))
    (hMc : ∀ j, Continuous (fun u => ((Ms j u : ℝ) : ℂ))) (hMi : ∀ j, Integrable (fun u => ((Ms j u : ℝ) : ℂ)))
    (hMf : ∀ j, Integrable (𝓕 (fun u => ((Ms j u : ℝ) : ℂ))))
    (φ : Fin J → ι₁ → ℝ) (ψ : Fin J → ι₂ → ℝ)
    (hI : ∀ j y₁ y₂, 0 ≤ I j y₁ y₂ ∧ I j y₁ y₂ ≤ 1) (hG : ∀ j u, 0 ≤ Gs j u ∧ Gs j u ≤ 1)
    (hIG : ∀ j y₁ y₂, |I j y₁ y₂ - Gs j (φ j y₁ + ψ j y₂)| ≤ Ms j (φ j y₁ + ψ j y₂))
    {ρ : ℝ} (hρ : 1 < ρ) (β₁ β₂ : ℕ) (t : ℕ × ℕ × ℕ × ℕ) (hℓ : 1 ≤ t.2.2.1)
    (hπ₁ : ∀ y ∈ Y₁, 1 ≤ π₁ y) (hπ₂ : ∀ y ∈ Y₂, 1 ≤ π₂ y) (hf : ∀ σ ∈ S, 1 ≤ f σ)
    {Mf M₂ : ℝ} (hMf0 : 0 ≤ Mf) (hMfib : ∀ d, ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => π₁ x.1 * f x.2 = d), |lam x.2| ≤ Mf)
    (hM₂ : ∀ d, (#(Y₂.filter (fun y => π₂ y = d)) : ℝ) ≤ M₂)
    {F : ℕ} (H : ℕ) (hH : 2 * H < q) (hF : ∀ n, 0 < n → n ≤ H * ⌊ρ ^ (β₂ + 1)⌋₊ → n.divisors.card ≤ F) :
    ‖blockSum q a Y₁ Y₂ π₁ π₂ S f lam c (blk ρ) (blk ρ) β₁ β₂ t‖ ≤
      ((∏ j, ∫ u, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) u‖) + ∑ j, ∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖) *
          (Mf * M₂ * bdPW q ρ β₁ β₂ t F H) +
        ∑ j, 2 * (q.totient : ℝ)⁻¹ * (massv t *
          ∑ x ∈ (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁),
            ∑ y₂ ∈ Y₂.filter (fun y => blk ρ (π₂ y) = β₂), |lam x.2| * Ms j (φ j x.1 + ψ j y₂)) := by
  classical
  have hρ0 : 0 < ρ := by linarith
  have hq0 : 0 < q := NeZero.pos q
  set Y₁' := (Y₁ ×ˢ S).filter (fun x => blk ρ (π₁ x.1 * f x.2) = β₁) with hY₁'
  set Y₂' := Y₂.filter (fun y => blk ρ (π₂ y) = β₂) with hY₂'
  set P₁ : ℝ := ρ ^ (β₁ + 1) with hP₁
  set P₂ : ℝ := ρ ^ (β₂ + 1) with hP₂
  have hP₁0 : 0 ≤ P₁ := by positivity
  have hP₂0 : 0 ≤ P₂ := by positivity
  set Dm : ℕ := ⌊P₂⌋₊ with hDm
  set m : ℕ := ⌊P₁⌋₊ / q + 1 with hm
  -- the values of the block pair
  have hv₁ : ∀ x ∈ Y₁', 1 ≤ π₁ x.1 * f x.2 ∧ ((π₁ x.1 * f x.2 : ℕ) : ℝ) ≤ P₁ := by
    intro x hx
    obtain ⟨hx1, hxb⟩ := Finset.mem_filter.1 hx
    obtain ⟨hy, hσ⟩ := Finset.mem_product.1 hx1
    have h1 : 1 ≤ π₁ x.1 * f x.2 := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := hπ₁ _ hy; omega)
      (by have := hf _ hσ; omega))
    refine ⟨h1, ?_⟩
    have := (blk_spec hρ h1).2
    rw [hxb] at this
    exact this.le
  have hv₂ : ∀ y ∈ Y₂', 1 ≤ π₂ y ∧ (π₂ y : ℝ) ≤ P₂ := by
    intro y hy
    obtain ⟨hy2, hyb⟩ := Finset.mem_filter.1 hy
    refine ⟨hπ₂ y hy2, ?_⟩
    have := (blk_spec hρ (hπ₂ y hy2)).2
    rw [hyb] at this
    exact this.le
  -- the block sum in the form of `typeIB_sharp0`
  have hform : blockSum q a Y₁ Y₂ π₁ π₂ S f lam c (blk ρ) (blk ρ) β₁ β₂ t =
      ∑ x ∈ Y₁', ∑ y₂ ∈ Y₂', (fun x : ι₁ × κ => ((lam x.2 : ℝ) : ℂ)) x * (fun _ : ι₂ => (1 : ℂ)) y₂ *
        (∏ j, ((fun j (x : ι₁ × κ) y₂ => I j x.1 y₂) j x y₂ : ℂ)) *
        ∑ k ∈ supp t.1 t.2.1 t.2.2.1 t.2.2.2, ((spl t.1 t.2.1 t.2.2.1 t.2.2.2 k : ℝ) : ℂ) *
          SieveFamily.dw q a ((fun x : ι₁ × κ => π₁ x.1 * f x.2) x * π₂ y₂ * k) := by
    rw [blockSum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y₂ _ => ?_
    rw [hc, Complex.ofReal_prod]
    rfl
  rw [hform]
  have hb := typeIB_sharp0_wide a ha Y₁' Y₂' (fun x : ι₁ × κ => π₁ x.1 * f x.2) π₂
    (fun x : ι₁ × κ => ((lam x.2 : ℝ) : ℂ)) (fun _ : ι₂ => (1 : ℂ)) (fun j (x : ι₁ × κ) y₂ => I j x.1 y₂)
    Gs Ms hGc hGi hGf hMc hMi hMf (fun j (x : ι₁ × κ) => φ j x.1) ψ (fun j x y₂ => hI j x.1 y₂) hG
    (fun j x y₂ => hIG j x.1 y₂) t.1 t.2.1 t.2.2.1 t.2.2.2 hℓ (H := H) (Dm := Dm) (F := F) (m := m)
    (fun y hy => (hv₂ y hy).1)
    (fun y hy => Nat.le_floor (hv₂ y hy).2) hH
    (by
      -- a residue class of the block's values
      intro r
      set T := (Y₁'.image (fun x : ι₁ × κ => π₁ x.1 * f x.2)).filter
        (fun d : ℕ => IsUnit (d : ZMod q) ∧ ((d : ZMod q))⁻¹ = r) with hT
      rcases T.eq_empty_or_nonempty with hT0 | ⟨d₀, hd₀⟩
      · rw [hT0, Finset.card_empty]; exact Nat.zero_le _
      · have hsub : T ⊆ (Finset.Ioc 0 ⌊P₁⌋₊).filter (fun k' : ℕ => (k' : ZMod q) = (d₀ : ZMod q)) := by
          intro d hd
          obtain ⟨hdi, hdu, hdr⟩ := Finset.mem_filter.1 hd
          obtain ⟨hd0i, hd0u, hd0r⟩ := Finset.mem_filter.1 hd₀
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hdi
          refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨(hv₁ x hx).1, Nat.le_floor (hv₁ x hx).2⟩, ?_⟩
          exact eq_of_inv_eq hdu hd0u (hdr.trans hd0r.symm)
        refine (Finset.card_le_card hsub).trans ?_
        have := SieveSpline.card_Ioc_filter_cong_le (q := q) 0 ⌊P₁⌋₊ d₀
        rw [Nat.sub_zero] at this
        exact this)
    (by
      intro τ hτ hτH y hy
      apply hF
      · exact Nat.mul_pos (Int.natAbs_pos.2 hτ) (hv₂ y hy).1
      · exact Nat.mul_le_mul hτH (Nat.le_floor (hv₂ y hy).2))
  refine hb.trans ?_
  -- the bound `bdIB` of the block pair
  set bd := SieveTypeIBFam.bdIB q Y₁' Y₂' (fun x : ι₁ × κ => π₁ x.1 * f x.2) π₂ (fun x : ι₁ × κ => ((lam x.2 : ℝ) : ℂ))
    (fun _ : ι₂ => (1 : ℂ)) t.1 t.2.1 t.2.2.1 t.2.2.2 H (F * (2 * (H * Dm) / q + 1)) m with hbd
  have hM₂0 : 0 ≤ M₂ := le_trans (Nat.cast_nonneg _) (hM₂ 0)
  obtain ⟨hsq₁, hl₁⟩ := fibre_le Y₁' (fun x : ι₁ × κ => π₁ x.1 * f x.2) (fun x => ((lam x.2 : ℝ) : ℂ)) hP₁0 hMf0
    hv₁ (fun d => by
      refine le_trans ?_ (hMfib d)
      simp only [Complex.norm_real, Real.norm_eq_abs]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => abs_nonneg _
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx1).1, hx2⟩)
  obtain ⟨hsq₂, hl₂⟩ := fibre_le Y₂' π₂ (fun _ => (1 : ℂ)) hP₂0 hM₂0 hv₂ (fun d => by
      refine le_trans ?_ (hM₂ d)
      simp only [norm_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast Finset.card_le_card fun y hy => by
        obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
        exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy1).1, hy2⟩)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
  have hdq : (0 : ℝ) ≤ (q.divisors.card : ℝ) / q.totient := by positivity
  have hm' : (m : ℝ) ≤ P₁ / q + 1 := by
    rw [hm]; push_cast
    have h1 : ((⌊P₁⌋₊ / q : ℕ) : ℝ) ≤ (⌊P₁⌋₊ : ℝ) / q := Nat.cast_div_le
    have h2 : (⌊P₁⌋₊ : ℝ) / q ≤ P₁ / q := div_le_div_of_nonneg_right (Nat.floor_le hP₁0) (by positivity)
    linarith
  have hn' : ((((t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1) / q + 1 : ℕ) : ℝ)) ≤ lenv t / q + 1 := by
    push_cast
    have := Nat.cast_div_le (α := ℝ) (m := t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1) (n := q)
    rw [lenv]
    linarith
  have hlen0 : 0 ≤ lenv t := Nat.cast_nonneg _
  -- the diagonal's factor
  have hDmP : (Dm : ℝ) ≤ P₂ := Nat.floor_le hP₂0
  have hFw : (((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ)) ≤ F * (2 * H * P₂ / q + 1) := by
    have h1 : ((2 * (H * Dm) / q : ℕ) : ℝ) ≤ ((2 * (H * Dm) : ℕ) : ℝ) / q := Nat.cast_div_le
    have h2 : ((2 * (H * Dm) : ℕ) : ℝ) / q ≤ 2 * H * P₂ / q := by
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg q)
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) H]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg F)
  have hbdle : bd ≤ Mf * M₂ * bdPW q ρ β₁ β₂ t F H := by
    rw [hbd, SieveTypeIBFam.bdIB, bdPW]
    simp only [norm_one]
    -- the three terms
    have hA : √(∑ d ∈ Y₁'.image (fun x : ι₁ × κ => π₁ x.1 * f x.2),
          (∑ y ∈ Y₁'.filter (fun y => π₁ y.1 * f y.2 = d), ‖((lam y.2 : ℝ) : ℂ)‖) ^ 2) *
        √(m * ((F * (2 * (H * Dm) / q + 1) : ℕ) : ℝ) * (∑ d ∈ Y₂'.image π₂, (∑ y ∈ Y₂'.filter (fun y => π₂ y = d), (1 : ℝ)) ^ 2) *
          ((((t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1) / q + 1 : ℕ) : ℝ) *
            (t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1 : ℕ))) ≤
        Mf * M₂ * √(P₁ * P₂ * (P₁ / q + 1) * (F * (2 * H * P₂ / q + 1)) * (lenv t / q + 1) * lenv t) := by
      have hsq₂' : ∑ d ∈ Y₂'.image π₂, (∑ y ∈ Y₂'.filter (fun y => π₂ y = d), (1 : ℝ)) ^ 2 ≤ M₂ ^ 2 * P₂ := by
        simpa using hsq₂
      have e : Mf * M₂ * √(P₁ * P₂ * (P₁ / q + 1) * (F * (2 * H * P₂ / q + 1)) * (lenv t / q + 1) * lenv t) =
          √(Mf ^ 2 * P₁) * √((P₁ / q + 1) * (F * (2 * H * P₂ / q + 1)) * (M₂ ^ 2 * P₂) * ((lenv t / q + 1) * lenv t)) := by
        rw [← Real.sqrt_mul (by positivity)]
        rw [show Mf ^ 2 * P₁ * ((P₁ / q + 1) * (F * (2 * H * P₂ / q + 1)) * (M₂ ^ 2 * P₂) *
            ((lenv t / q + 1) * lenv t)) =
          (Mf * M₂) ^ 2 * (P₁ * P₂ * (P₁ / q + 1) * (F * (2 * H * P₂ / q + 1)) * (lenv t / q + 1) * lenv t) by ring]
        rw [Real.sqrt_mul (show (0 : ℝ) ≤ (Mf * M₂) ^ 2 by positivity), Real.sqrt_sq (by positivity)]
      rw [e]
      refine mul_le_mul (Real.sqrt_le_sqrt hsq₁) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hn0 : (0 : ℝ) ≤ ((((t.2.1 + t.2.2.2 * (t.2.2.1 - 1) - t.1) / q + 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
      exact mul_le_mul (mul_le_mul (mul_le_mul hm' hFw (Nat.cast_nonneg _) (by positivity)) hsq₂' (Finset.sum_nonneg
        fun d _ => sq_nonneg _) (by positivity)) (mul_le_mul hn' le_rfl hlen0 (by positivity))
        (mul_nonneg hn0 hlen0) (by positivity)
    have hB : ((t.2.1 - t.1 : ℕ) : ℝ) * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 *
          ((∑ y ∈ Y₁', ‖((lam y.2 : ℝ) : ℂ)‖) * ∑ y ∈ Y₂', (1 : ℝ)) ≤
        Mf * M₂ * (massv t * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 * (P₁ * P₂)) := by
      have hl₂' : ∑ y ∈ Y₂', (1 : ℝ) ≤ M₂ * P₂ := by simpa using hl₂
      have hm0 : 0 ≤ massv t := Nat.cast_nonneg _
      have hpow0 : 0 ≤ ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 := by positivity
      calc ((t.2.1 - t.1 : ℕ) : ℝ) * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 *
            ((∑ y ∈ Y₁', ‖((lam y.2 : ℝ) : ℂ)‖) * ∑ y ∈ Y₂', (1 : ℝ))
          ≤ massv t * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 * ((Mf * P₁) * (M₂ * P₂)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hl₁ hl₂' (Finset.sum_nonneg fun _ _ => zero_le_one)
              (by positivity)) (mul_nonneg hm0 hpow0)
        _ = Mf * M₂ * (massv t * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 * (P₁ * P₂)) := by ring
    have hC : (∑ y ∈ Y₁', ‖((lam y.2 : ℝ) : ℂ)‖) * (∑ y ∈ Y₂', (1 : ℝ)) * ((q.divisors.card : ℝ) / q.totient) ≤
        Mf * M₂ * (P₁ * P₂ * ((q.divisors.card : ℝ) / q.totient)) := by
      have hl₂' : ∑ y ∈ Y₂', (1 : ℝ) ≤ M₂ * P₂ := by simpa using hl₂
      calc (∑ y ∈ Y₁', ‖((lam y.2 : ℝ) : ℂ)‖) * (∑ y ∈ Y₂', (1 : ℝ)) * ((q.divisors.card : ℝ) / q.totient)
          ≤ (Mf * P₁) * (M₂ * P₂) * ((q.divisors.card : ℝ) / q.totient) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hl₁ hl₂' (Finset.sum_nonneg fun _ _ => zero_le_one)
              (by positivity)) hdq
        _ = Mf * M₂ * (P₁ * P₂ * ((q.divisors.card : ℝ) / q.totient)) := by ring
    have e : Mf * M₂ * (√(P₁ * P₂ * (P₁ / q + 1) * (F * (2 * H * P₂ / q + 1)) * (lenv t / q + 1) * lenv t) +
        massv t * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 * (P₁ * P₂) + P₁ * P₂ * ((q.divisors.card : ℝ) / q.totient)) =
        Mf * M₂ * √(P₁ * P₂ * (P₁ / q + 1) * (F * (2 * H * P₂ / q + 1)) * (lenv t / q + 1) * lenv t) +
          Mf * M₂ * (massv t * ((q : ℝ) / (2 * t.2.2.1 * (H + 1))) ^ t.2.2.2 * (P₁ * P₂)) +
          Mf * M₂ * (P₁ * P₂ * ((q.divisors.card : ℝ) / q.totient)) := by ring
    rw [e]
    exact add_le_add (add_le_add hA hB) hC
  -- the near-boundary masses
  have hnb : ∀ j, ∑ y₁ ∈ Y₁', ∑ y₂ ∈ Y₂', ‖((lam y₁.2 : ℝ) : ℂ)‖ * ‖(1 : ℂ)‖ * Ms j (φ j y₁.1 + ψ j y₂) =
      ∑ x ∈ Y₁', ∑ y₂ ∈ Y₂', |lam x.2| * Ms j (φ j x.1 + ψ j y₂) := by
    intro j
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y₂ _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one]
  simp only [hnb]
  have hFour : 0 ≤ (∏ j, ∫ u, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) u‖) :=
    Finset.prod_nonneg fun j _ => integral_nonneg fun u => norm_nonneg _
  have hFourM : ∀ j, 0 ≤ ∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖ := fun j => integral_nonneg fun u => norm_nonneg _
  have hbd0 : 0 ≤ bd := by
    rw [hbd, SieveTypeIBFam.bdIB]
    positivity
  rw [add_mul, Finset.sum_mul, Finset.sum_add_distrib]
  have h1 := mul_le_mul_of_nonneg_left hbdle hFour
  have h2 : ∑ j, (∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖) * bd ≤
      ∑ j, (∫ u, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) u‖) * (Mf * M₂ * bdPW q ρ β₁ β₂ t F H) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left hbdle (hFourM j)
  have h3 : ∑ j, 2 * (q.totient : ℝ)⁻¹ * (((t.2.1 - t.1 : ℕ) : ℝ) *
      ∑ x ∈ Y₁', ∑ y₂ ∈ Y₂', |lam x.2| * Ms j (φ j x.1 + ψ j y₂)) =
      ∑ j, 2 * (q.totient : ℝ)⁻¹ * (massv t *
      ∑ x ∈ Y₁', ∑ y₂ ∈ Y₂', |lam x.2| * Ms j (φ j x.1 + ψ j y₂)) := rfl
  linarith

end SieveTypeIBPairWide

#print axioms SieveTypeIBPairWide.typeIB_sharp0_wide
#print axioms SieveTypeIBPairWide.pair_le_wide
