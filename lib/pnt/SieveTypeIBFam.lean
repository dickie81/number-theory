/-
# Type I_B families: the bilinear Type I estimate over families with comparisons

Plain statements. `dw q a n = 1[n ≡ a] − 1[(n, q) = 1]/φ(q)` (`SieveFamily.dw`), and `w` is the spline of
`SieveSpline.spl` on its support `(A, B + r(ℓ − 1)]`. A *family* has two groups of variables, `y₁` over a finite set
`Y₁` with values `π₁(y₁)` and coefficients `a₁(y₁)`, and `y₂` over `Y₂` with `π₂(y₂)` and `a₂(y₂)`; on the fibre of a
value `d` the coefficients aggregate to `A₁(d) = Σ_{π₁(y₁) = d} |a₁(y₁)|` and `A₂(d)`.

* `norm_integral_prod_le`: `|∫ ∏_j h_j(ξ_j)F(ξ) dξ| ≤ B ∏_j ‖h_j‖₁` when `|F| ≤ B` everywhere.
* `sum_fiber`: `Σ_{y∈Y} c(y)f(π(y)) = Σ_{d ∈ π(Y)} (Σ_{π(y) = d} c(y)) f(d)`.
* `dw_of_not_isUnit`: `dw q a n = 0` when `n` is not prime to `q`, for `a` a unit.
* `typeIB_smooth`: let `J` continuous integrable `g_j` with integrable `𝓕g_j` be applied to the forms
  `φ_j(y₁) + ψ_j(y₂)`. Under the conditions of `SieveSpline.typeIB_spline` on the values (`π₂ ≤ Dm`, `2HDm < q`, every
  residue the inverse of at most `m` values `π₁` prime to `q`, every `|t|π₂` with `0 < |t| ≤ H` with at most `F`
  divisors), `|Σ_{y₁,y₂} a₁a₂ ∏_j g_j(φ_j(y₁) + ψ_j(y₂)) Σ_k w(k)dw(π₁(y₁)π₂(y₂)k)|` is at most `∏_j ‖𝓕g_j‖₁` times
  `(ΣA₁²)^{1/2}(mF(ΣA₂²)(⌊n/q⌋ + 1)n)^{1/2} + (B − A)(q/(2ℓ(H + 1)))^r(Σ|a₁|)(Σ|a₂|) + (Σ|a₁|)(Σ|a₂|)d(q)/φ(q)`,
  `n = B + r(ℓ − 1) − A`. `bdIB` is this bound without the factor `∏_j ‖𝓕g_j‖₁`.
* `typeIB_sharp0`: `J` comparisons `I_j(y₁, y₂) ∈ [0, 1]`, replaced by smooth `G_j ∈ [0, 1]` of the forms `ℓ_j` with
  `|I_j − G_j| ≤ M_j(ℓ_j)` for smooth `M_j`. Then `|Σ_{y₁,y₂} a₁a₂ ∏_j I_j Σ_k w(k)dw(π₁π₂k)|` is at most
  `∏_j ‖𝓕G_j‖₁·bdIB + Σ_j (2φ(q)⁻¹(B − A)Σ_y |a₁||a₂|M_j(ℓ_j) + ‖𝓕M_j‖₁·bdIB)`.

The proof:

* `typeIB_smooth`: `SieveSep.sum_sep` writes the sum as an integral over `ℝ^J` of `∏_j 𝓕g_j(ξ_j)` times the twisted
  sum, whose twists `e^{2πiΣ_jξ_jφ_j(y₁)}` and `e^{2πiΣ_jξ_jψ_j(y₂)}` go into the coefficients. Aggregated over the
  fibres (`sum_fiber`) and restricted to the values prime to `q` (`dw_of_not_isUnit`), the twisted sum is the
  bilinear form of `SieveSpline.typeIB_spline`, with coefficients of size at most `A₁` and `A₂`;
  `norm_integral_prod_le` integrates the bound.
* `typeIB_sharp0`: `SieveFamily.norm_Dsum_sharp_le` over the triples `(y₁, y₂, k)`. Its smoothed sum
  and near-boundary sums are `typeIB_smooth`'s, with the coefficients `|a₁|`, `|a₂|` for the latter (`bdIB_norm`), and
  the near-boundary masses carry the spline's mass `B − A` (`SieveSpline.sum_spl`).

The file imports `SieveSpline.lean` and `SieveSep.lean`.
-/
import SieveSpline
import SieveSep

open Finset Complex MeasureTheory
open scoped FourierTransform

namespace SieveTypeIBFam

open SieveTypeIB SieveSpline

/-! ### Integrals and fibres -/

/-- `|∫ ∏_j h_j(ξ_j)F(ξ) dξ| ≤ B ∏_j ‖h_j‖₁` when `|F| ≤ B` everywhere. -/
theorem norm_integral_prod_le {ι : Type*} [Fintype ι] {h : ι → ℝ → ℂ} (hh : ∀ j, Integrable (h j))
    {F : (ι → ℝ) → ℂ} {B : ℝ} (hB : ∀ ξ, ‖F ξ‖ ≤ B) :
    ‖∫ ξ : ι → ℝ, (∏ j, h j (ξ j)) * F ξ‖ ≤ B * ∏ j, ∫ t, ‖h j t‖ := by
  have hHi : Integrable (fun ξ : ι → ℝ => ∏ j, ‖h j (ξ j)‖) :=
    Integrable.fintype_prod (f := fun j t => ‖h j t‖) fun j => (hh j).norm
  calc ‖∫ ξ : ι → ℝ, (∏ j, h j (ξ j)) * F ξ‖ ≤ ∫ ξ : ι → ℝ, ‖(∏ j, h j (ξ j)) * F ξ‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : ι → ℝ, B * ∏ j, ‖h j (ξ j)‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => norm_nonneg _) (hHi.const_mul B)
          (Filter.Eventually.of_forall fun ξ => ?_)
        simp only
        rw [norm_mul, norm_prod, mul_comm]
        exact mul_le_mul_of_nonneg_right (hB ξ) (Finset.prod_nonneg fun j _ => norm_nonneg _)
    _ = B * ∏ j, ∫ t, ‖h j t‖ := by
        rw [integral_const_mul, integral_fintype_prod_volume_eq_prod (f := fun j t => ‖h j t‖)]

/-- **Fibres**: `Σ_{y∈Y} c(y)f(π(y)) = Σ_{d ∈ π(Y)} (Σ_{π(y) = d} c(y)) f(d)`. -/
theorem sum_fiber {ι : Type*} (Y : Finset ι) (π : ι → ℕ) (c : ι → ℂ) (f : ℕ → ℂ) :
    ∑ y ∈ Y, c y * f (π y) = ∑ d ∈ Y.image π, (∑ y ∈ Y.filter (fun y => π y = d), c y) * f d := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := π) (t := Y.image π) (fun y hy => Finset.mem_image_of_mem π hy)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [(Finset.mem_filter.1 hy).2]

/-- The fibres' aggregates of `|c|` sum to `Σ_{y∈Y} |c(y)|`. -/
theorem sum_fiber_norm {ι : Type*} (Y : Finset ι) (π : ι → ℕ) (c : ι → ℂ) :
    ∑ d ∈ Y.image π, ∑ y ∈ Y.filter (fun y => π y = d), ‖c y‖ = ∑ y ∈ Y, ‖c y‖ := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (g := π) (t := Y.image π) (fun y hy => Finset.mem_image_of_mem π hy) _

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- For `a` a unit, `dw q a n = 0` when `n` is not prime to `q`. -/
theorem dw_of_not_isUnit {a : ZMod q} (ha : IsUnit a) {n : ℕ} (hn : ¬ IsUnit (n : ZMod q)) :
    SieveFamily.dw q a n = 0 := by
  have h1 : (n : ZMod q) ≠ a := fun h => hn (h ▸ ha)
  rw [SieveFamily.dw, ite_eq_right h1, ite_eq_right hn]
  simp

/-- Restricting a double sum to the values prime to `q`, when the terms vanish off them. -/
theorem sum_units_eq (S₁ S₂ : Finset ℕ) (f : ℕ → ℕ → ℂ)
    (hf : ∀ d₁ d₂ : ℕ, ¬ (IsUnit (d₁ : ZMod q) ∧ IsUnit (d₂ : ZMod q)) → f d₁ d₂ = 0) :
    ∑ d₁ ∈ S₁, ∑ d₂ ∈ S₂, f d₁ d₂ =
      ∑ d₁ ∈ S₁.filter (fun d : ℕ => IsUnit (d : ZMod q)), ∑ d₂ ∈ S₂.filter (fun d : ℕ => IsUnit (d : ZMod q)),
        f d₁ d₂ := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d₁ _ => ?_
  split_ifs with h₁
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    split_ifs with h₂
    · rfl
    · exact hf d₁ d₂ (fun h => h₂ h.2)
  · exact Finset.sum_eq_zero fun d₂ _ => hf d₁ d₂ (fun h => h₁ h.1)

/-- A twisted coefficient has the coefficient's size. -/
theorem norm_twist {J : Type*} [Fintype J] (c : ℂ) (ξ : J → ℝ) (φ : J → ℝ) :
    ‖c * Complex.exp (2 * Real.pi * I * ∑ j, (ξ j : ℂ) * φ j)‖ = ‖c‖ := by
  have : 2 * Real.pi * I * ∑ j, (ξ j : ℂ) * φ j = ((2 * Real.pi * ∑ j, ξ j * φ j : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The bilinear Type I estimate over a family with smooth comparisons.** Let `J` continuous integrable `g_j` with
integrable `𝓕g_j` be applied to the forms `φ_j(y₁) + ψ_j(y₂)`. Under the conditions of `SieveSpline.typeIB_spline`
on the values, `|Σ_{y₁,y₂} a₁a₂ ∏_j g_j(φ_j(y₁) + ψ_j(y₂)) Σ_k w(k)dw(π₁(y₁)π₂(y₂)k)|` is at most `∏_j ‖𝓕g_j‖₁`
times `SieveSpline.typeIB_spline`'s bound with the fibres' aggregates `A₁`, `A₂` of `|a₁|`, `|a₂|`. -/
theorem typeIB_smooth (a : ZMod q) (ha : IsUnit a) {ι₁ ι₂ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂)
    (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ) (a₁ : ι₁ → ℂ) (a₂ : ι₂ → ℂ) {J : Type*} [Fintype J] {g : J → ℝ → ℂ}
    (hgc : ∀ j, Continuous (g j)) (hgi : ∀ j, Integrable (g j)) (hgf : ∀ j, Integrable (𝓕 (g j)))
    (φ : J → ι₁ → ℝ) (ψ : J → ι₂ → ℝ) (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) {H Dm F m : ℕ}
    (hπ₂ : ∀ y ∈ Y₂, 0 < π₂ y) (hDm : ∀ y ∈ Y₂, π₂ y ≤ Dm) (hDm1 : 1 ≤ Dm) (hq : 2 * H * Dm < q)
    (hm : ∀ r : ZMod q, #((Y₁.image π₁).filter (fun d : ℕ => IsUnit (d : ZMod q) ∧ ((d : ZMod q))⁻¹ = r)) ≤ m)
    (hF : ∀ t : ℤ, t ≠ 0 → t.natAbs ≤ H → ∀ y ∈ Y₂, (t.natAbs * π₂ y).divisors.card ≤ F) :
    ‖∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, a₁ y₁ * a₂ y₂ * (∏ j, g j (φ j y₁ + ψ j y₂)) *
        ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * SieveFamily.dw q a (π₁ y₁ * π₂ y₂ * k)‖ ≤
      (∏ j, ∫ t, ‖𝓕 (g j) t‖) *
        (√(∑ d ∈ Y₁.image π₁, (∑ y ∈ Y₁.filter (fun y => π₁ y = d), ‖a₁ y‖) ^ 2) *
            √(m * F * (∑ d ∈ Y₂.image π₂, (∑ y ∈ Y₂.filter (fun y => π₂ y = d), ‖a₂ y‖) ^ 2) *
              ((((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * (B + r * (ℓ - 1) - A : ℕ))) +
          ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r * ((∑ y ∈ Y₁, ‖a₁ y‖) * (∑ y ∈ Y₂, ‖a₂ y‖)) +
          (∑ y ∈ Y₁, ‖a₁ y‖) * (∑ y ∈ Y₂, ‖a₂ y‖) * (q.divisors.card / q.totient)) := by
  classical
  set X : ℕ → ℂ := fun d => ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * SieveFamily.dw q a (d * k) with hX
  set A₁ : ℕ → ℝ := fun d => ∑ y ∈ Y₁.filter (fun y => π₁ y = d), ‖a₁ y‖ with hA₁
  set A₂ : ℕ → ℝ := fun d => ∑ y ∈ Y₂.filter (fun y => π₂ y = d), ‖a₂ y‖ with hA₂
  set n₀ : ℝ := (((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * (B + r * (ℓ - 1) - A : ℕ) with hn₀
  set W : ℝ := ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r with hW
  set Bd : ℝ := √(∑ d ∈ Y₁.image π₁, A₁ d ^ 2) * √(m * F * (∑ d ∈ Y₂.image π₂, A₂ d ^ 2) * n₀) +
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
  have hb := typeIB_spline a ha D₁ D₂ α β hD₁u hD₂u hD₂0 A B ℓ r hℓ hDm' hDm1 hq hm' hF'
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
    have hmF : (0 : ℝ) ≤ m * F := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq₂ hmF) hn0
  · exact mul_le_mul_of_nonneg_left (mul_le_mul hl1₁ hl1₂ (Finset.sum_nonneg fun d _ => norm_nonneg _)
      (Finset.sum_nonneg fun y _ => norm_nonneg _)) hW0
  · refine mul_le_mul_of_nonneg_right (mul_le_mul ((norm_sum_le _ _).trans hl1₁) ((norm_sum_le _ _).trans hl1₂)
      (norm_nonneg _) (Finset.sum_nonneg fun y _ => norm_nonneg _)) hdq

/-- The bound of `typeIB_smooth` for coefficients `a₁`, `a₂` (it depends on their sizes only). -/
noncomputable def bdIB (q : ℕ) {ι₁ ι₂ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ)
    (a₁ : ι₁ → ℂ) (a₂ : ι₂ → ℂ) (A B ℓ r H F m : ℕ) : ℝ :=
  √(∑ d ∈ Y₁.image π₁, (∑ y ∈ Y₁.filter (fun y => π₁ y = d), ‖a₁ y‖) ^ 2) *
      √(m * F * (∑ d ∈ Y₂.image π₂, (∑ y ∈ Y₂.filter (fun y => π₂ y = d), ‖a₂ y‖) ^ 2) *
        ((((B + r * (ℓ - 1) - A) / q + 1 : ℕ) : ℝ) * (B + r * (ℓ - 1) - A : ℕ))) +
    ((B - A : ℕ) : ℝ) * ((q : ℝ) / (2 * ℓ * (H + 1))) ^ r * ((∑ y ∈ Y₁, ‖a₁ y‖) * (∑ y ∈ Y₂, ‖a₂ y‖)) +
    (∑ y ∈ Y₁, ‖a₁ y‖) * (∑ y ∈ Y₂, ‖a₂ y‖) * (q.divisors.card / q.totient)

omit [NeZero q] in
/-- `bdIB` sees only the sizes of the coefficients. -/
theorem bdIB_norm {ι₁ ι₂ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂) (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ)
    (a₁ : ι₁ → ℂ) (a₂ : ι₂ → ℂ) (A B ℓ r H F m : ℕ) :
    bdIB q Y₁ Y₂ π₁ π₂ (fun y => ((‖a₁ y‖ : ℝ) : ℂ)) (fun y => ((‖a₂ y‖ : ℝ) : ℂ)) A B ℓ r H F m =
      bdIB q Y₁ Y₂ π₁ π₂ a₁ a₂ A B ℓ r H F m := by
  simp only [bdIB, Complex.norm_real, Real.norm_eq_abs, abs_norm]

/-- **Sharp comparisons, with no base weight**: the bound is
`∏_j ‖𝓕G_j‖₁·bd + Σ_j (2φ(q)⁻¹(B − A)Σ_y |a₁||a₂|M_j(ℓ_j) + ‖𝓕M_j‖₁·bd)`. -/
theorem typeIB_sharp0 (a : ZMod q) (ha : IsUnit a) {ι₁ ι₂ : Type*} (Y₁ : Finset ι₁) (Y₂ : Finset ι₂)
    (π₁ : ι₁ → ℕ) (π₂ : ι₂ → ℕ) (a₁ : ι₁ → ℂ) (a₂ : ι₂ → ℂ) {J : ℕ} (I : Fin J → ι₁ → ι₂ → ℝ)
    (Gs Ms : Fin J → ℝ → ℝ) (hGc : ∀ j, Continuous (fun u => ((Gs j u : ℝ) : ℂ)))
    (hGi : ∀ j, Integrable (fun u => ((Gs j u : ℝ) : ℂ))) (hGf : ∀ j, Integrable (𝓕 (fun u => ((Gs j u : ℝ) : ℂ))))
    (hMc : ∀ j, Continuous (fun u => ((Ms j u : ℝ) : ℂ))) (hMi : ∀ j, Integrable (fun u => ((Ms j u : ℝ) : ℂ)))
    (hMf : ∀ j, Integrable (𝓕 (fun u => ((Ms j u : ℝ) : ℂ))))
    (φ : Fin J → ι₁ → ℝ) (ψ : Fin J → ι₂ → ℝ)
    (hI : ∀ j y₁ y₂, 0 ≤ I j y₁ y₂ ∧ I j y₁ y₂ ≤ 1) (hG : ∀ j u, 0 ≤ Gs j u ∧ Gs j u ≤ 1)
    (hIG : ∀ j y₁ y₂, |I j y₁ y₂ - Gs j (φ j y₁ + ψ j y₂)| ≤ Ms j (φ j y₁ + ψ j y₂))
    (A B ℓ r : ℕ) (hℓ : 1 ≤ ℓ) {H Dm F m : ℕ}
    (hπ₂ : ∀ y ∈ Y₂, 0 < π₂ y) (hDm : ∀ y ∈ Y₂, π₂ y ≤ Dm) (hDm1 : 1 ≤ Dm) (hq : 2 * H * Dm < q)
    (hm : ∀ r : ZMod q, #((Y₁.image π₁).filter (fun d : ℕ => IsUnit (d : ZMod q) ∧ ((d : ZMod q))⁻¹ = r)) ≤ m)
    (hF : ∀ t : ℤ, t ≠ 0 → t.natAbs ≤ H → ∀ y ∈ Y₂, (t.natAbs * π₂ y).divisors.card ≤ F) :
    ‖∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, a₁ y₁ * a₂ y₂ * (∏ j, (I j y₁ y₂ : ℂ)) *
        ∑ k ∈ supp A B ℓ r, ((spl A B ℓ r k : ℝ) : ℂ) * SieveFamily.dw q a (π₁ y₁ * π₂ y₂ * k)‖ ≤
      (∏ j, ∫ t, ‖𝓕 (fun u => ((Gs j u : ℝ) : ℂ)) t‖) * bdIB q Y₁ Y₂ π₁ π₂ a₁ a₂ A B ℓ r H F m +
        ∑ j, (2 * (q.totient : ℝ)⁻¹ * (((B - A : ℕ) : ℝ) *
            ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, ‖a₁ y₁‖ * ‖a₂ y₂‖ * Ms j (φ j y₁ + ψ j y₂)) +
          (∫ t, ‖𝓕 (fun u => ((Ms j u : ℝ) : ℂ)) t‖) * bdIB q Y₁ Y₂ π₁ π₂ a₁ a₂ A B ℓ r H F m) := by
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
    exact typeIB_smooth a ha Y₁ Y₂ π₁ π₂ a₁ a₂ hGc hGi hGf φ ψ A B ℓ r hℓ hπ₂ hDm hDm1 hq hm hF
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
    have h1 := typeIB_smooth a ha Y₁ Y₂ π₁ π₂ (fun y => ((‖a₁ y‖ : ℝ) : ℂ)) (fun y => ((‖a₂ y‖ : ℝ) : ℂ))
      (g := fun _ : Fin 1 => fun u => ((Ms j u : ℝ) : ℂ)) (fun _ => hMc j) (fun _ => hMi j) (fun _ => hMf j)
      (fun _ => φ j) (fun _ => ψ j) A B ℓ r hℓ hπ₂ hDm hDm1 hq hm hF
    refine h1.trans (le_of_eq ?_)
    have h2 := bdIB_norm (q := q) Y₁ Y₂ π₁ π₂ a₁ a₂ A B ℓ r H F m
    rw [bdIB] at h2
    rw [h2, Fin.prod_univ_one, bdIB]

end SieveTypeIBFam
