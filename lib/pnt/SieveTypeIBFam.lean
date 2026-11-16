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

end SieveTypeIBFam
