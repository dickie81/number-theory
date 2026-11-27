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

/-! ## The eigenfunctions -/

/-- The Euclidean inner product `⟨k, w⟩ = Re(k w̄)` of `ℂ = ℝ²`. -/
def ip (k w : ℂ) : ℝ := (k * (starRingEnd ℂ) w).re

/-- The dual-lattice vector `k_v = (2πi/y)(v₁ + v₀τ)` of `ℤ + ℤτ`. -/
def dualVec (z : ℍ) (v : Fin 2 → ℤ) : ℂ := 2 * π * Complex.I / z.im * ((v 1 : ℂ) + (v 0 : ℂ) * z)

/-- The plane wave `w ↦ exp(i⟨k, w⟩)`. -/
def wave (k w : ℂ) : ℂ := cexp (Complex.I * ip k w)

/-- The flat Laplacian `Δf(w) = ∂²_u f + ∂²_v f`, `w = u + iv`, as the sum of the second derivatives along `1` and
`i`. -/
def flatLap (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  deriv (deriv fun t : ℝ => f (w + t)) 0 + deriv (deriv fun t : ℝ => f (w + t * Complex.I)) 0

/-- `⟨k_v, m + nτ⟩ = 2π(nv₁ − mv₀)`. -/
lemma ip_dualVec (z : ℍ) (v : Fin 2 → ℤ) (m n : ℤ) :
    ip (dualVec z v) ((m : ℂ) + (n : ℂ) * z) = 2 * π * ((n * v 1 - m * v 0 : ℤ) : ℝ) := by
  have hy : z.im ≠ 0 := z.im_pos.ne'
  have e : (2 * π * Complex.I / z.im : ℂ) = ((2 * π / z.im : ℝ) : ℂ) * Complex.I := by push_cast; ring
  simp only [ip, dualVec, e]
  simp only [map_add, map_mul, map_intCast, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  push_cast
  field_simp
  ring

/-- **The plane waves `exp(i⟨k_v, ·⟩)` live on the torus**: they are `ℤ + ℤτ`-periodic. -/
theorem wave_add_lattice (z : ℍ) (v : Fin 2 → ℤ) (w : ℂ) (m n : ℤ) :
    wave (dualVec z v) (w + ((m : ℂ) + (n : ℂ) * z)) = wave (dualVec z v) w := by
  have hadd : ip (dualVec z v) (w + ((m : ℂ) + (n : ℂ) * z)) =
      ip (dualVec z v) w + ip (dualVec z v) ((m : ℂ) + (n : ℂ) * z) := by
    simp [ip, mul_add]
  rw [wave, wave, hadd, ip_dualVec]
  push_cast
  rw [mul_add, Complex.exp_add]
  have : Complex.I * (2 * π * ((n : ℂ) * (v 1 : ℂ) - (m : ℂ) * (v 0 : ℂ))) =
      (((n * v 1 - m * v 0 : ℤ)) : ℂ) * (2 * π * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `|k_v|² = λ_v`. -/
theorem normSq_dualVec (z : ℍ) (v : Fin 2 → ℤ) : Complex.normSq (dualVec z v) = lam z v := by
  have hy : z.im ≠ 0 := z.im_pos.ne'
  rw [dualVec, lam, nq, Complex.normSq_mul, show (v 1 : ℂ) + (v 0 : ℂ) * z = (v 0 : ℂ) * z + v 1 by ring]
  congr 1
  rw [show (2 * π * Complex.I / z.im : ℂ) = ((2 * π / z.im : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_I]
  ring

lemma hasDerivAt_exp_line (c b : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (c + t * b)) (cexp (c + t * b) * b) t := by
  have h : HasDerivAt (fun u : ℂ => cexp (c + u * b)) (cexp (c + t * b) * (0 + 1 * b)) (t : ℂ) :=
    ((hasDerivAt_const _ c).add ((hasDerivAt_id (t : ℂ)).mul_const b)).cexp
  simpa using h.comp_ofReal

lemma deriv_deriv_exp_line (c b : ℂ) :
    deriv (deriv fun t : ℝ => cexp (c + t * b)) 0 = cexp c * b ^ 2 := by
  have h1 : deriv (fun t : ℝ => cexp (c + t * b)) = fun t : ℝ => cexp (c + t * b) * b :=
    funext fun t => (hasDerivAt_exp_line c b t).deriv
  rw [h1, ((hasDerivAt_exp_line c b 0).mul_const b).deriv]
  simp; ring

/-- **The plane waves are eigenfunctions of the flat Laplacian**: `Δ exp(i⟨k, ·⟩) = −|k|² exp(i⟨k, ·⟩)`. -/
theorem flatLap_wave (k w : ℂ) : flatLap (wave k) w = -(Complex.normSq k : ℂ) * wave k w := by
  have e1 : (fun t : ℝ => wave k (w + t)) = fun t : ℝ => cexp (Complex.I * ip k w + t * (Complex.I * k.re)) := by
    funext t; simp only [wave, ip]; congr 1; simp [mul_add, Complex.mul_re]; ring
  have e2 : (fun t : ℝ => wave k (w + t * Complex.I)) = fun t : ℝ => cexp (Complex.I * ip k w + t * (Complex.I * k.im)) := by
    funext t; simp only [wave, ip]; congr 1; simp [mul_add, Complex.mul_re]; ring
  rw [flatLap, e1, e2, deriv_deriv_exp_line, deriv_deriv_exp_line, wave, Complex.normSq_apply]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The torus eigenfunctions**: `Δ exp(i⟨k_v, ·⟩) = −λ_v exp(i⟨k_v, ·⟩)`, with `λ_v = (2π/y)²|v₀τ + v₁|²`. -/
theorem flatLap_wave_dualVec (z : ℍ) (v : Fin 2 → ℤ) (w : ℂ) :
    flatLap (wave (dualVec z v)) w = -(lam z v : ℂ) * wave (dualVec z v) w := by
  rw [flatLap_wave, normSq_dualVec]

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

/-! ## The one-loop determinant: `ζ_T(0)` and `ζ_T'(0)` -/

/-- **`ζ_T(0) = −1`**: minus the number of zero modes (the constants). -/
theorem zetaT_zero (z : ℍ) : zetaT z 0 = -1 := by
  simp [zetaT]

/-- The functional equation of the entire part, `Λ₀(1 − s) = Λ₀(s)`. -/
lemma Λ₀_one_sub (z : ℍ) (s : ℂ) : (thetaFEPair z).Λ₀ (1 - s) = (thetaFEPair z).Λ₀ s := by
  have h := (thetaFEPair z).functional_equation₀ s
  rw [thetaFEPair_symm] at h
  have hk : (((thetaFEPair z).k : ℝ) : ℂ) = 1 := by simp [thetaFEPair]
  have he : (thetaFEPair z).ε = 1 := rfl
  rwa [hk, he, one_smul] at h

lemma Lambda_sub_pole_eq (z : ℍ) (s : ℂ) : Lambda z s - 1 / (s - 1) = (thetaFEPair z).Λ₀ s - 1 / s := by
  rw [Lambda_eq_Λ₀, show (1 : ℂ) - s = -(s - 1) by ring, div_neg]
  ring

/-- **Kronecker's limit formula for the entire part**: `Λ₀(1) = 1 + γ − log 4π + 2kron(τ)`, with
`kron(τ) = −log(√y|η(τ)|²)`. -/
theorem Λ₀_one (z : ℍ) : (thetaFEPair z).Λ₀ 1 =
    ((1 + Real.eulerMascheroniConstant - Real.log (4 * π) + 2 * kron z : ℝ) : ℂ) := by
  have h1 := tendsto_Lambda_sub_pole z
  have hc : ContinuousAt (fun s => (thetaFEPair z).Λ₀ s - 1 / s) 1 :=
    ((thetaFEPair z).differentiable_Λ₀ 1).continuousAt.sub (continuousAt_const.div continuousAt_id one_ne_zero)
  have h2 : Tendsto (fun s => Lambda z s - 1 / (s - 1)) (𝓝[≠] 1) (𝓝 ((thetaFEPair z).Λ₀ 1 - 1 / 1)) := by
    simp_rw [Lambda_sub_pole_eq]; exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique h2 h1
  rw [div_one] at this
  push_cast at this ⊢
  linear_combination this

/-- **`ζ_T'(0) = 2kron(τ) − log y = −log(y²|η(τ)|⁴)`**, the derivative of the spectral zeta function at `0`. -/
theorem hasDerivAt_zetaT_zero (z : ℍ) :
    HasDerivAt (zetaT z) ((2 * kron z - Real.log z.im : ℝ) : ℂ) 0 := by
  have hy := z.im_pos
  set a : ℝ := z.im / (4 * π) with ha
  have ha0 : 0 < a := by positivity
  have hA : HasDerivAt (fun s : ℂ => (a : ℂ) ^ s) ((a : ℂ) ^ (0 : ℂ) * Complex.log a * 1) 0 :=
    (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl (by exact_mod_cast ha0.ne'))
  set L := (thetaFEPair z).Λ₀
  have hL : HasDerivAt L (deriv L 0) 0 := ((thetaFEPair z).differentiable_Λ₀ 0).hasDerivAt
  have hq : HasDerivAt (fun s : ℂ => s / (1 - s)) ((1 * (1 - 0) - 0 * (-1)) / (1 - 0) ^ 2) 0 :=
    (hasDerivAt_id (0 : ℂ)).div ((hasDerivAt_id (0 : ℂ)).const_sub 1) (by norm_num)
  have hN : HasDerivAt (fun s : ℂ => s * L s - 1 - s / (1 - s))
      ((1 * L 0 + 0 * deriv L 0) - (1 * (1 - 0) - 0 * (-1)) / (1 - 0) ^ 2) 0 :=
    (((hasDerivAt_id (0 : ℂ)).mul hL).sub_const 1).sub hq
  have hG : HasDerivAt (fun s : ℂ => Complex.Gamma (s + 1)) (-(Real.eulerMascheroniConstant : ℂ)) 0 := by
    have := Complex.hasDerivAt_Gamma_one
    rw [← zero_add (1 : ℂ)] at this
    exact this.comp_add_const 0 1
  have hG0 : Complex.Gamma (0 + 1) ≠ 0 := by rw [zero_add, Complex.Gamma_one]; exact one_ne_zero
  have h := (hA.mul hN).div hG hG0
  have hL0 : L 0 = ((1 + Real.eulerMascheroniConstant - Real.log (4 * π) + 2 * kron z : ℝ) : ℂ) := by
    rw [← Λ₀_one, show (1 : ℂ) = 1 - 0 by ring, Λ₀_one_sub]
  have hlog : Complex.log (a : ℂ) = ((Real.log z.im - Real.log (4 * π) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log ha0.le, ha, Real.log_div hy.ne' (by positivity)]
  convert h using 1
  · funext s; simp [zetaT, a, L]
  · simp only [Pi.mul_apply, zero_add, Complex.Gamma_one, Complex.cpow_zero, zero_mul, zero_div,
      sub_zero, hL0, hlog]
    push_cast
    ring

/-- `ζ_T'(0) = 2kron(τ) − log y`. -/
theorem deriv_zetaT_zero (z : ℍ) : deriv (zetaT z) 0 = ((2 * kron z - Real.log z.im : ℝ) : ℂ) :=
  (hasDerivAt_zetaT_zero z).deriv

/-- **The zeta-regularised determinant of the flat torus** (Ray–Singer; Polchinski):
`log det'Δ = −ζ_T'(0) = log(y²|η(τ)|⁴)`, i.e. `det'Δ = (Im τ)²|η(τ)|⁴`, with Mathlib's Dedekind `η`. -/
theorem logDet_eq (z : ℍ) :
    -(2 * kron z - Real.log z.im) = Real.log (z.im ^ 2 * ‖ModularForm.eta z‖ ^ 4) := by
  have hy := z.im_pos
  have hη : 0 < ‖ModularForm.eta z‖ := norm_pos_iff.2 (ModularForm.eta_ne_zero z.im_pos)
  rw [kron, UpperHalfPlane.coe_im, Real.log_mul (Real.sqrt_pos.2 hy).ne' (by positivity), Real.log_pow,
    Real.log_sqrt hy.le, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **`det'Δ = (Im τ)²|η(τ)|⁴`**: `exp(−ζ_T'(0)) = y²|η(τ)|⁴`. -/
theorem exp_neg_deriv_zetaT_zero (z : ℍ) :
    Real.exp (-(2 * kron z - Real.log z.im)) = z.im ^ 2 * ‖ModularForm.eta z‖ ^ 4 := by
  have hη : 0 < ‖ModularForm.eta z‖ := norm_pos_iff.2 (ModularForm.eta_ne_zero z.im_pos)
  rw [logDet_eq, Real.exp_log (by have := z.im_pos; positivity)]

/-! ## Modular invariance -/

/-- **The Kronecker limit function is `SL(2, ℤ)`-invariant**: `kron(γτ) = kron(τ)`, from `E*(γτ, s) = E*(τ, s)` and
uniqueness of the limit in Kronecker's formula. -/
theorem kron_smul (γ : SL(2, ℤ)) (z : ℍ) : kron (γ • z : ℍ) = kron z := by
  have h1 := tendsto_Estar_sub_pole (γ • z)
  simp_rw [Estar_smul] at h1
  have := tendsto_nhds_unique h1 (tendsto_Estar_sub_pole z)
  have h2 := Complex.ofReal_injective this
  linarith

/-- **The scale-invariant part of the determinant is modular invariant**: `ζ_T'(0) + log(area)` is the same for
`τ` and `γτ` (the tori `ℂ/(ℤ + ℤτ)` and `ℂ/(ℤ + ℤγτ)` differ by the dilation `w ↦ w/(cτ + d)`, which rescales the
spectrum; since `ζ_T(0) = −1`, `ζ_T'(0) + log(area)` does not see the dilation). -/
theorem deriv_zetaT_zero_add_log_smul (γ : SL(2, ℤ)) (z : ℍ) :
    deriv (zetaT (γ • z)) 0 + Real.log (γ • z).im = deriv (zetaT z) 0 + Real.log z.im := by
  rw [deriv_zetaT_zero, deriv_zetaT_zero, kron_smul]
  push_cast
  ring

/-- **`det'Δ/area = (Im τ)|η(τ)|⁴` is `SL(2, ℤ)`-invariant**: the one-loop partition function
`Z(τ) = (det'Δ/area)^{−1/2} = 1/(√(Im τ)|η(τ)|²)` of the free boson does not depend on the choice of basis of the
lattice. -/
theorem det_div_area_smul (γ : SL(2, ℤ)) (z : ℍ) :
    (γ • z).im * ‖ModularForm.eta (γ • z : ℍ)‖ ^ 4 = z.im * ‖ModularForm.eta z‖ ^ 4 := by
  have key : ∀ w : ℍ, w.im * ‖ModularForm.eta w‖ ^ 4 = Real.exp (-2 * kron w) := by
    intro w
    have hη : 0 < ‖ModularForm.eta w‖ := norm_pos_iff.2 (ModularForm.eta_ne_zero w.im_pos)
    rw [kron, UpperHalfPlane.coe_im, show -2 * -Real.log (√w.im * ‖ModularForm.eta w‖ ^ 2) =
      2 * Real.log (√w.im * ‖ModularForm.eta w‖ ^ 2) by ring, ← Real.log_rpow (by positivity),
      Real.exp_log (by positivity)]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow, Real.sq_sqrt w.im_pos.le]
    ring
  rw [key, key, kron_smul]

/-! ## The Casimir energy of the torus -/

/-- **The zeta-regularised Casimir (vacuum) energy** `E₀ = ½Σ'_v √λ_v := ½ζ_T(−½)` of a free massless scalar on the
spatial torus `ℂ/(ℤ + ℤτ)` (units `ħ = c = 1`). -/
def casimir (z : ℍ) : ℂ := zetaT z (-1 / 2) / 2

lemma Gamma_one_half : Complex.Gamma (1 / 2) = ((√π : ℝ) : ℂ) := by
  rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  push_cast; ring_nf

/-- **The Casimir energy of the flat torus**: `E₀ = ½ζ_T(−½) = −(1/(4π√y))Σ'_v (y/|v₀τ + v₁|²)^{3/2}
= −(y/4π)Σ'_ℓ |ℓ|^{−3}`, the sum over the nonzero periods `ℓ = v₀τ + v₁`; it is negative. Via the functional equation
`Λ_τ(−½) = Λ_τ(3/2)`. -/
theorem casimir_eq (z : ℍ) : casimir z = -epstein z (3 / 2) / (4 * π * ((√z.im : ℝ) : ℂ)) := by
  have hy := z.im_pos
  have hπ := Real.pi_pos
  have h0 : (-1 / 2 : ℂ) ≠ 0 := by norm_num
  have hΛ : Lambda z (-1 / 2) = Lambda z (3 / 2) := by
    have := Estar_one_sub z (3 / 2)
    rw [show (1 : ℂ) - 3 / 2 = -1 / 2 by norm_num] at this
    unfold Estar at this
    linear_combination 2 * this
  have hG32 : Complex.Gamma (3 / 2) = ((√π : ℝ) : ℂ) / 2 := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num), Gamma_one_half]; ring
  have hGm : Complex.Gamma (-1 / 2) = -2 * ((√π : ℝ) : ℂ) := by
    have := Complex.Gamma_add_one (-1 / 2) h0
    rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num, Gamma_one_half] at this
    linear_combination 2 * this
  have hre : (1 : ℝ) < (3 / 2 : ℂ).re := by norm_num
  have ha : (((z.im / (4 * π) : ℝ) : ℂ)) ^ (-1 / 2 : ℂ) = ((2 * √π / √z.im : ℝ) : ℂ) := by
    rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    field_simp
  have hp : (π : ℂ) ^ (-(3 / 2 : ℂ)) = ((1 / (π * √π) : ℝ) : ℂ) := by
    rw [show (-(3 / 2) : ℂ) = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hπ.le]
    congr 1
    rw [Real.rpow_neg hπ.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hπ, Real.rpow_one,
      ← Real.sqrt_eq_rpow, one_div]
  rw [casimir, zetaT_eq z h0, hΛ, Lambda_eq_epstein z hre, hG32, hGm, ha, hp]
  have hsπ : (0 : ℝ) < √π := Real.sqrt_pos.2 hπ
  have hsy : (0 : ℝ) < √z.im := Real.sqrt_pos.2 hy
  have : ((√π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsπ.ne'
  have : ((√z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsy.ne'
  have : (π : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  push_cast
  field_simp
  ring

end ModCasimir
