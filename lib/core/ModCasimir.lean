/-
# The flat torus `ℂ/(ℤ + ℤτ)`: spectral zeta function, one-loop determinant and Casimir energy

The classical zeta-regularised one-loop computation for a free massless scalar on a flat 2-torus (Ray–Singer 1973;
Polchinski 1986; see also Polchinski, *String Theory* I, §7.3), formalised on top of the library's completed
Eisenstein series `E*(τ, s)` (`ModContinuation`) and Kronecker's first limit formula (`ModKronecker`). This is a
formalisation of known mathematics, not new mathematics.

**Conventions.** `τ = x + iy ∈ ℍ`; the torus is `T_τ = ℂ/(ℤ + ℤτ)` with the flat metric `|dw|²`, so its area is
`y = Im τ`; the Laplacian is `Δ = ∂²_u + ∂²_v` (`w = u + iv`), with spectrum `−λ`. For `v = (v₀, v₁) ∈ ℤ²` the
eigenvalue is `λ_v = (2π/y)²|v₀τ + v₁|²` (`lam`), with eigenfunction `exp(i⟨k_v, w⟩)`,
`k_v = (2πi/y)(v₁ + v₀τ)` (`dualVec`, `wave`). The zero mode `v = 0` is excluded in all primed sums.

* **Eigenfunctions** (`wave_add_lattice`, `flatLap_wave`, `normSq_dualVec`): `exp(i⟨k_v, ·⟩)` is `ℤ + ℤτ`-periodic
  and `Δ` of it is `−λ_v` times it. (Completeness of these eigenfunctions in `L²(T_τ)` is not proved here.)
* **The spectral zeta function** (`zetaT`, `hasSum_zetaT`, `zetaT_eq`): `ζ_T(s) = Σ'_v λ_v^{−s}` on `Re s > 1`;
  it is `(y/4π)^s Λ_τ(s)/Γ(s) = (y/4π)^s · 2E*(τ, s)/Γ(s)` off `s = 0`, and `zetaT` is its continuation, holomorphic
  off `s = 1` (`differentiableAt_zetaT`).
-/
import Mathlib
import ModEisenstein
import ModContinuation
import ModKronecker

open Complex Real Filter Topology Set
open scoped MatrixGroups

noncomputable section

namespace ModCasimir

open ModEisenstein ModContinuation ModKronecker UpperHalfPlane

/-! ## The spectrum of the flat torus -/

/-- **The Laplace eigenvalue** `λ_v = (2π/y)²|v₀τ + v₁|²` of the flat torus `ℂ/(ℤ + ℤτ)`, `y = Im τ`. -/
def lam (z : ℍ) (v : Fin 2 → ℤ) : ℝ := (2 * π / z.im) ^ 2 * nq z v

lemma lam_nonneg (z : ℍ) (v : Fin 2 → ℤ) : 0 ≤ lam z v := mul_nonneg (sq_nonneg _) (nq_nonneg z v)

lemma lam_inv (z : ℍ) (v : Fin 2 → ℤ) : (lam z v)⁻¹ = z.im / (4 * π ^ 2) * (z.im / nq z v) := by
  have hy := z.im_pos.ne'
  have hπ := Real.pi_pos.ne'
  unfold lam
  rcases eq_or_ne (nq z v) 0 with h | h
  · simp [h]
  · field_simp
    ring

lemma ofReal_cpow_neg {a : ℝ} (ha : 0 ≤ a) (s : ℂ) : (a : ℂ) ^ (-s) = ((a⁻¹ : ℝ) : ℂ) ^ s := by
  rw [Complex.cpow_neg, Complex.ofReal_inv, Complex.inv_cpow]
  rw [Complex.arg_ofReal_of_nonneg ha]; exact Real.pi_pos.ne

/-- `λ_v^{−s} = (y/4π²)^s (y/|v₀τ + v₁|²)^s`. -/
lemma lam_cpow_neg (z : ℍ) (s : ℂ) (v : Fin 2 → ℤ) :
    (lam z v : ℂ) ^ (-s) = ((z.im / (4 * π ^ 2) : ℝ) : ℂ) ^ s * term z s v := by
  rw [ofReal_cpow_neg (lam_nonneg z v), lam_inv, term, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (div_nonneg z.im_pos.le (nq_nonneg z v))]

/-! ## The spectral zeta function -/

/-- **The spectral zeta function of the flat torus**, continued to all `s`:
`ζ_T(s) = (y/4π)^s (sΛ₀(s) − 1 − s/(1 − s))/Γ(s + 1)`, where `Λ_τ = Λ₀ − 1/s − 1/(1 − s)` is the completed Epstein
zeta function `ModContinuation.Lambda`. On `Re s > 1` it is `Σ'λ_v^{−s}` (`hasSum_zetaT`). -/
def zetaT (z : ℍ) (s : ℂ) : ℂ :=
  ((z.im / (4 * π) : ℝ) : ℂ) ^ s * (s * (thetaFEPair z).Λ₀ s - 1 - s / (1 - s)) / Complex.Gamma (s + 1)

lemma Lambda_eq_Λ₀ (z : ℍ) (s : ℂ) : Lambda z s = (thetaFEPair z).Λ₀ s - 1 / s - 1 / (1 - s) := by
  simp [Lambda, WeakFEPair.Λ, thetaFEPair]

lemma mul_Lambda (z : ℍ) {s : ℂ} (h0 : s ≠ 0) :
    s * Lambda z s = s * (thetaFEPair z).Λ₀ s - 1 - s / (1 - s) := by
  rw [Lambda_eq_Λ₀, mul_sub, mul_sub, mul_one_div_cancel h0, mul_one_div]

/-- **`ζ_T(s) = (y/4π)^s Λ_τ(s)/Γ(s)`** off `s = 0`. -/
theorem zetaT_eq (z : ℍ) {s : ℂ} (h0 : s ≠ 0) :
    zetaT z s = ((z.im / (4 * π) : ℝ) : ℂ) ^ s * Lambda z s / Complex.Gamma s := by
  rw [zetaT, ← mul_Lambda z h0, Complex.Gamma_add_one s h0]
  rcases eq_or_ne (Complex.Gamma s) 0 with h | h
  · simp [h]
  · field_simp

/-- **`ζ_T(s) = (y/4π)^s · 2E*(τ, s)/Γ(s)`** off `s = 0`. -/
theorem zetaT_eq_Estar (z : ℍ) {s : ℂ} (h0 : s ≠ 0) :
    zetaT z s = 2 * ((z.im / (4 * π) : ℝ) : ℂ) ^ s * Estar z s / Complex.Gamma s := by
  rw [zetaT_eq z h0, Estar]
  ring

/-- **The spectral zeta function is the zeta-regularised eigenvalue sum**: on `Re s > 1`,
`Σ'_v λ_v^{−s} = ζ_T(s)` (the `v = 0` term `0^{−s}` is `0`). -/
theorem hasSum_zetaT (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v => (lam z v : ℂ) ^ (-s)) (zetaT z s) := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  simp_rw [lam_cpow_neg]
  have hsum := ((summable_norm_term z hs).of_norm).hasSum.mul_left (((z.im / (4 * π ^ 2) : ℝ) : ℂ) ^ s)
  convert hsum using 1
  rw [zetaT_eq z h0, Lambda_eq_epstein z hs, ← epstein]
  have e : z.im / (4 * π) = z.im / (4 * π ^ 2) * π := by field_simp
  rw [e, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) Real.pi_pos.le, Complex.cpow_neg]
  have hπs : (π : ℂ) ^ s ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero h0).2 hπ
  field_simp

/-- **`ζ_T` is holomorphic off `s = 1`** (in particular at `s = 0`). -/
theorem differentiableAt_zetaT (z : ℍ) {s : ℂ} (h1 : s ≠ 1) : DifferentiableAt ℂ (zetaT z) s := by
  have hy : (0 : ℝ) < z.im / (4 * π) := by have := z.im_pos; positivity
  have hs1 : 1 - s ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have e : zetaT z = fun s => ((z.im / (4 * π) : ℝ) : ℂ) ^ s * (s * (thetaFEPair z).Λ₀ s - 1 - s / (1 - s)) *
      (1 / Complex.Gamma (s + 1)) := by
    funext s; rw [zetaT, mul_one_div]
  rw [e]
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
  · exact (differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne')))
  · refine ((differentiableAt_id.mul ((thetaFEPair z).differentiable_Λ₀ s)).sub_const 1).sub ?_
    exact differentiableAt_id.div ((differentiableAt_const _).sub differentiableAt_id) hs1
  · have := (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)) s
    simpa [Function.comp_def, one_div] using this

end ModCasimir
