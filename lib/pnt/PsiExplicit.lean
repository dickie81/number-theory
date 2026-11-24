import HalfPlaneFinal

/-!
# `ψ` and `θ` within `C t^{11/12+η}` at every `t ≥ 1` — CONDITIONAL on the half-plane

The library's prime number theorem with error `O(t^{11/12+η})`, `HalfPlanePNT.psi_isBigO_eleven_twelfths`, is a bound
at `∞`. Here it holds at every `t ≥ 1`, with a constant:

* `abs_psi_sub_le`: `|ψ(t) − t| ≤ C t^{11/12+η}`. Beyond the range of the `O` bound use that bound; below it,
  `0 ≤ ψ(t) ≤ (log 4 + 4)t` (Mathlib's `Chebyshev.psi_le_const_mul_self`).
* `abs_theta_sub_le`: `|θ(t) − t| ≤ C t^{11/12+η}`, from `abs_psi_sub_le` and Mathlib's `0 ≤ ψ − θ ≤ C√t`.

**CONDITIONAL.** Through `HalfPlanePNT.psi_isBigO_eleven_twelfths`, both use the half-plane `Re s > 11/12` for `ζ`
(`Eis.LFunction_ne_zero_of_re_gt`), an input formalised in the library that no referee has read (see
`formalisations/openai-half-plane.md`). Lean checks them with the standard axioms only, but they are only as good as
that input, and must be cited as conditional on it.
-/

namespace PsiExplicit

/-- **CONDITIONAL. `ψ(t) = t + O(t^{11/12+η})` at every `t ≥ 1`** (conditional on the half-plane, through
`HalfPlanePNT.psi_isBigO_eleven_twelfths`). -/
theorem abs_psi_sub_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (11 / 12 + η) := by
  obtain ⟨C₁, hC₁⟩ := (HalfPlanePNT.psi_isBigO_eleven_twelfths hη).bound
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hC₁
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨max C₁ 0 + (Real.log 4 + 4) * max T 1, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hta : 1 ≤ t ^ (11 / 12 + η) := Real.one_le_rpow ht (by linarith)
  have hC : 0 ≤ max C₁ 0 * t ^ (11 / 12 + η) := by positivity
  rcases le_total T t with hTt | htT
  · have h := hT t hTt
    rw [Pi.sub_apply, id, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at h
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by positivity : 0 ≤ t ^ (11 / 12 + η)),
      mul_nonneg (by positivity : 0 ≤ (Real.log 4 + 4) * max T 1) (by positivity : 0 ≤ t ^ (11 / 12 + η))]
  · -- below `T`: `0 ≤ ψ(t) ≤ (log 4 + 4)t`
    have h1 := Chebyshev.psi_nonneg t
    have h2 := Chebyshev.psi_le_const_mul_self ht0.le
    have h3 : t ≤ max T 1 * t ^ (11 / 12 + η) := by nlinarith [le_max_left T 1, le_max_right T 1]
    rw [abs_le]
    constructor <;> nlinarith

/-- **CONDITIONAL. `θ(t) = t + O(t^{11/12+η})` at every `t ≥ 1`** (conditional on the half-plane, through
`abs_psi_sub_le`), as `0 ≤ ψ(t) − θ(t) ≤ C√t` (Mathlib's `Chebyshev.psi_sub_theta_le_mul_sqrt`). -/
theorem abs_theta_sub_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → |Chebyshev.theta t - t| ≤ C * t ^ (11 / 12 + η) := by
  obtain ⟨C₁, hC₁, h₁⟩ := abs_psi_sub_le hη
  obtain ⟨C₂, hC₂⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C₁ + max C₂ 0, by positivity, fun t ht => ?_⟩
  have hsq : √t ≤ t ^ (11 / 12 + η) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have h2 : Chebyshev.psi t - Chebyshev.theta t ≤ max C₂ 0 * t ^ (11 / 12 + η) :=
    (hC₂ t).trans (mul_le_mul (le_max_left _ _) hsq (Real.sqrt_nonneg t) (le_max_right _ _))
  have h3 := Chebyshev.theta_le_psi t
  have h4 : 0 ≤ max C₂ 0 * t ^ (11 / 12 + η) :=
    mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
  have h1 := h₁ t ht
  rw [add_mul]
  rw [abs_le] at h1 ⊢
  constructor <;> linarith

end PsiExplicit

#print axioms PsiExplicit.abs_psi_sub_le
#print axioms PsiExplicit.abs_theta_sub_le
