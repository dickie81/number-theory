/-
# The completed Eisenstein series of `SL(2, ℤ)`: continuation, functional equation and constant term

Milestone A of the scattering theory of `SL(2, ℤ)\ℍ²`, on the side of the theta function. For `z = x + iy ∈ ℍ` the
theta function of the lattice `ℤz + ℤ` scaled to covolume one is `θ_z(t) = Σ_{(m, n)} e^{−π|mz + n|²t/y}`.
* **Self-duality** (`theta_inv`): `θ_z(1/t) = tθ_z(t)`, from Mathlib's functional equation of `evenKernel` in each
  row and a swap of the double series; with the bounds `θ_z(t) − 1 = O(e^{−ct})` this makes `θ_z` a weak FE-pair
  (`thetaFEPair`) of weight `1`, its own dual.
* **The completed series** (`Estar`, `Lambda_eq_epstein`, `Estar_eq`): `E*(z, s) = Λ_z(s)/2`, half the Mellin
  transform of `θ_z − 1`, is defined for every `s`, and `E*(z, s) = Λ(2s)E(z, s)` on `Re s > 1`, with Mathlib's
  `completedRiemannZeta`.
* **Functional equation and holomorphy** (`Estar_one_sub`, `differentiableAt_Estar`, `differentiableOn_Estar`):
  `E*(z, 1 − s) = E*(z, s)` for every `s`, and `E*(z, ·)` is holomorphic on `ℂ \ {0, 1}`.
* **Invariance** (`theta_smul`, `Estar_smul`): `θ_{γz} = θ_z`, so `E*(γz, s) = E*(z, s)` for every `γ ∈ SL(2, ℤ)` and
  every `s`.
* **The constant term** (`constTerm_Estar`): `∫_0^1 E*(x + iy, s) dx = Λ(2s)y^s + Λ(2s − 1)y^{1−s}` on `Re s > 1`,
  from `ModEisenstein.constTerm_eq`. Its extension to every `s` (by the identity theorem) is not built here.
-/
import Mathlib
import ModEisenstein
import EpsteinFlat

open Complex Real Filter Topology Set MeasureTheory UpperHalfPlane Matrix HurwitzZeta Asymptotics
open scoped MatrixGroups

noncomputable section

namespace ModContinuation

open ModEisenstein

/-! ## The theta function of `ℤz + ℤ` -/

/-- `Q_z(v)/y = |v₀z + v₁|²/Im z`. -/
def qf (z : ℍ) (v : Fin 2 → ℤ) : ℝ := nq z v / z.im

lemma qf_nonneg (z : ℍ) (v : Fin 2 → ℤ) : 0 ≤ qf z v := div_nonneg (nq_nonneg z v) z.im_pos.le

/-- **The theta function of the lattice `ℤz + ℤ`** of covolume `y`: `θ_z(t) = Σ_v e^{−πt|v₀z + v₁|²/y}`. -/
def theta (z : ℍ) (t : ℝ) : ℝ := ∑' v : Fin 2 → ℤ, rexp (-π * qf z v * t)

/-- The constant `c_z = r(z)²/(2y)`, with Mathlib's `EisensteinSeries.r`. -/
def cz (z : ℍ) : ℝ := EisensteinSeries.r z ^ 2 / (2 * z.im)

lemma cz_pos (z : ℍ) : 0 < cz z := div_pos (pow_pos (EisensteinSeries.r_pos z) 2) (by linarith [z.im_pos])

/-- **The lattice is not degenerate**: `|v₀z + v₁|²/y ≥ c_z(v₀² + v₁²)`. -/
lemma cz_le_qf (z : ℍ) (v : Fin 2 → ℤ) : cz z * ((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2) ≤ qf z v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [qf, nq]
  have h := EisensteinSeries.r_mul_max_le z hv
  have hN : ‖v‖ = max |(v 0 : ℝ)| |(v 1 : ℝ)| := by
    rw [EisensteinSeries.norm_eq_max_natAbs]
    simp [Nat.cast_natAbs, Int.cast_abs]
  have hNsq : (v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    rw [hN]
    rcases le_total |(v 0 : ℝ)| |(v 1 : ℝ)| with h | h
    · rw [max_eq_right h]
      nlinarith [sq_abs (v 0 : ℝ), sq_abs (v 1 : ℝ), abs_nonneg (v 0 : ℝ)]
    · rw [max_eq_left h]
      nlinarith [sq_abs (v 0 : ℝ), sq_abs (v 1 : ℝ), abs_nonneg (v 1 : ℝ)]
  have hr := EisensteinSeries.r_pos z
  have h2 : (EisensteinSeries.r z * ‖v‖) ^ 2 ≤ nq z v := by
    rw [nq_eq]; exact pow_le_pow_left₀ (by positivity) h 2
  have hy := z.im_pos
  unfold qf cz
  rw [le_div_iff₀ hy]
  calc EisensteinSeries.r z ^ 2 / (2 * z.im) * ((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2) * z.im
      = EisensteinSeries.r z ^ 2 * ((v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2) / 2 := by field_simp
    _ ≤ EisensteinSeries.r z ^ 2 * (2 * ‖v‖ ^ 2) / 2 := by gcongr
    _ = (EisensteinSeries.r z * ‖v‖) ^ 2 := by ring
    _ ≤ nq z v := h2

/-- The rectangular majorant, the terms of `θ_1(c_z t)` (`EpsteinFlat.theta 1`). -/
def rect (c t : ℝ) (v : Fin 2 → ℤ) : ℝ := rexp (-π * (c * t) * ((v 0 : ℝ) ^ 2 + 1 ^ 2 * (v 1 : ℝ) ^ 2) / 1)

lemma hasSum_rect {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasSum (rect c t) (EpsteinFlat.theta 1 (c * t)) := by
  have h := EpsteinFlat.hasSum_theta one_pos (mul_pos hc ht)
  rw [← (finTwoArrowEquiv ℤ).hasSum_iff] at h
  exact h

lemma term_le_rect (z : ℍ) {t : ℝ} (ht : 0 < t) (v : Fin 2 → ℤ) :
    rexp (-π * qf z v * t) ≤ rect (cz z) t v := by
  unfold rect
  apply Real.exp_le_exp.2
  have := cz_le_qf z v
  have hpt : 0 < π * t := mul_pos pi_pos ht
  nlinarith [mul_le_mul_of_nonneg_left this hpt.le]

lemma summable_theta (z : ℍ) {t : ℝ} (ht : 0 < t) : Summable fun v => rexp (-π * qf z v * t) :=
  Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (term_le_rect z ht)
    (hasSum_rect (cz_pos z) ht).summable

lemma hasSum_theta (z : ℍ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun v => rexp (-π * qf z v * t)) (theta z t) := (summable_theta z ht).hasSum

lemma one_le_theta (z : ℍ) {t : ℝ} (ht : 0 < t) : 1 ≤ theta z t := by
  have := le_hasSum (hasSum_theta z ht) 0 (fun _ _ => (Real.exp_pos _).le)
  simpa [qf, nq] using this

lemma theta_le_rect (z : ℍ) {t : ℝ} (ht : 0 < t) : theta z t ≤ EpsteinFlat.theta 1 (cz z * t) :=
  hasSum_le (term_le_rect z ht) (hasSum_theta z ht) (hasSum_rect (cz_pos z) ht)

/-! ## Self-duality: `θ_z(1/t) = tθ_z(t)` -/

lemma nq_re_im (z : ℍ) (v : Fin 2 → ℤ) :
    nq z v = ((v 0 : ℝ) * z.re + v 1) ^ 2 + ((v 0 : ℝ) * z.im) ^ 2 := by
  simp only [nq, Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.add_im, Complex.mul_im]
  ring

/-- One row of `θ_z`: `Σ_n e^{−πt|mz + n|²/y} = e^{−πtm²y}θ(mx; t/y)`, with Mathlib's `evenKernel`. -/
lemma hasSum_row (z : ℍ) {t : ℝ} (ht : 0 < t) (m : ℤ) :
    HasSum (fun n : ℤ => rexp (-π * qf z ![m, n] * t))
      (rexp (-π * t * (m : ℝ) ^ 2 * z.im) * evenKernel ((m : ℝ) * z.re) (t / z.im)) := by
  have hy := z.im_pos
  refine ((hasSum_int_evenKernel ((m : ℝ) * z.re) (div_pos ht hy)).mul_left
    (rexp (-π * t * (m : ℝ) ^ 2 * z.im))).congr_fun fun n => ?_
  rw [← Real.exp_add, qf, nq_re_im]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- The dual double series `S_z(t) = Σ_{(m, n)} e^{2πimnx}e^{−πy(tm² + n²/t)}`. -/
def dualTerm (z : ℍ) (t : ℝ) (p : ℤ × ℤ) : ℂ :=
  cexp (2 * π * Complex.I * (((p.1 : ℝ) * z.re : ℝ) : ℂ) * p.2) *
    ((rexp (-π * t * (p.1 : ℝ) ^ 2 * z.im) : ℂ) * (rexp (-π * (p.2 : ℝ) ^ 2 * (z.im / t)) : ℂ))

lemma summable_gauss {c : ℝ} (hc : 0 < c) : Summable fun n : ℤ => rexp (-π * c * (n : ℝ) ^ 2) := by
  have := (hasSum_int_evenKernel 0 hc).summable
  refine this.congr fun n => ?_
  congr 1; ring

lemma summable_dualTerm (z : ℍ) {t : ℝ} (ht : 0 < t) : Summable (dualTerm z t) := by
  have hy := z.im_pos
  have h1 := summable_gauss (mul_pos ht hy)
  have h2 := summable_gauss (div_pos hy ht)
  have hprod := h1.mul_of_nonneg h2 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine Summable.of_norm_bounded hprod fun p => ?_
  rw [dualTerm, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  have : ‖cexp (2 * π * Complex.I * (((p.1 : ℝ) * z.re : ℝ) : ℂ) * p.2)‖ = 1 := by
    rw [show (2 * π * Complex.I * (((p.1 : ℝ) * z.re : ℝ) : ℂ) * p.2) =
      (((2 * π * ((p.1 : ℝ) * z.re) * p.2 : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [this, one_mul]
  apply le_of_eq
  congr 2 <;> ring

/-- **`θ_z(t) = (y/t)^{1/2}S_z(t)`**, from the functional equation of `evenKernel` in each row. -/
lemma theta_eq_dual (z : ℍ) {t : ℝ} (ht : 0 < t) :
    ((theta z t : ℝ) : ℂ) = ((1 / (t / z.im) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑' p, dualTerm z t p := by
  have hy := z.im_pos
  set c : ℝ := 1 / (t / z.im) ^ (1 / 2 : ℝ)
  have hrows : HasSum (fun m : ℤ => rexp (-π * t * (m : ℝ) ^ 2 * z.im) *
      evenKernel ((m : ℝ) * z.re) (t / z.im)) (theta z t) := by
    have h := hasSum_theta z ht
    rw [← (finTwoArrowEquiv ℤ).symm.hasSum_iff] at h
    exact h.prod_fiberwise fun m => hasSum_row z ht m
  have hdual : HasSum (fun m : ℤ => ((rexp (-π * t * (m : ℝ) ^ 2 * z.im) : ℝ) : ℂ) *
      cosKernel ((m : ℝ) * z.re) (z.im / t)) (∑' p, dualTerm z t p) := by
    refine (summable_dualTerm z ht).hasSum.prod_fiberwise fun m => ?_
    have h := (hasSum_int_cosKernel ((m : ℝ) * z.re) (div_pos hy ht)).mul_left
      ((rexp (-π * t * (m : ℝ) ^ 2 * z.im) : ℝ) : ℂ)
    refine h.congr_fun fun n => ?_
    simp only [dualTerm]
    ring
  have h1 := (hasSum_ofReal.2 hrows)
  have h2 := hdual.mul_left (c : ℂ)
  refine h1.unique (h2.congr_fun fun m => ?_)
  rw [evenKernel_functional_equation, one_div_div]
  simp only [c]
  push_cast
  ring

lemma dualTerm_inv (z : ℍ) {t : ℝ} (ht : 0 < t) (p : ℤ × ℤ) :
    dualTerm z (1 / t) p = dualTerm z t p.swap := by
  simp only [dualTerm, Prod.fst_swap, Prod.snd_swap]
  have e1 : (2 * π * Complex.I * (((p.1 : ℝ) * z.re : ℝ) : ℂ) * p.2) =
      (2 * π * Complex.I * (((p.2 : ℝ) * z.re : ℝ) : ℂ) * p.1) := by push_cast; ring
  have e2 : -π * (1 / t) * (p.1 : ℝ) ^ 2 * z.im = -π * (p.1 : ℝ) ^ 2 * (z.im / t) := by ring
  have e3 : -π * (p.2 : ℝ) ^ 2 * (z.im / (1 / t)) = -π * t * (p.2 : ℝ) ^ 2 * z.im := by
    field_simp
  rw [e1, e2, e3]
  ring

/-- **The self-duality of `θ_z`**: `θ_z(1/t) = tθ_z(t)`. The lattice `ℤz + ℤ` of covolume `y`, scaled by
`y^{−1/2}`, is unimodular and self-dual, and the Poisson summation in each row is Mathlib's functional equation of
`evenKernel`. -/
theorem theta_inv (z : ℍ) {t : ℝ} (ht : 0 < t) : theta z (1 / t) = t * theta z t := by
  have hy := z.im_pos
  have hS : ∑' p, dualTerm z (1 / t) p = ∑' p, dualTerm z t p := by
    simp_rw [dualTerm_inv z ht]
    exact (Equiv.prodComm ℤ ℤ).tsum_eq (dualTerm z t)
  have hc : 1 / (1 / t / z.im) ^ (1 / 2 : ℝ) = t * (1 / (t / z.im) ^ (1 / 2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have hA : 0 < Real.sqrt (1 / t / z.im) := Real.sqrt_pos.2 (by positivity)
    have hB : 0 < Real.sqrt (t / z.im) := Real.sqrt_pos.2 (by positivity)
    have key : Real.sqrt (t / z.im) = t * Real.sqrt (1 / t / z.im) := by
      rw [show t / z.im = t ^ 2 * (1 / t / z.im) by field_simp, Real.sqrt_mul (sq_nonneg t),
        Real.sqrt_sq ht.le]
    rw [key]
    field_simp
  have h1 := theta_eq_dual z (one_div_pos.2 ht)
  have h2 := theta_eq_dual z ht
  rw [hS, hc] at h1
  have : ((theta z (1 / t) : ℝ) : ℂ) = ((t * theta z t : ℝ) : ℂ) := by
    rw [h1, Complex.ofReal_mul t (theta z t), h2]; push_cast; ring
  exact_mod_cast this

/-! ## The weak FE-pair and the completed Eisenstein series -/

lemma continuousOn_theta_Ioi (z : ℍ) {a : ℝ} (ha : 0 < a) : ContinuousOn (theta z) (Ioi a) := by
  refine continuousOn_tsum (fun v => by fun_prop) (summable_theta z ha) fun v t (ht : a < t) => ?_
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.2
  have := qf_nonneg z v
  nlinarith [mul_le_mul_of_nonneg_left ht.le (mul_nonneg pi_pos.le this)]

lemma continuousOn_theta (z : ℍ) : ContinuousOn (theta z) (Ioi 0) := by
  intro t (ht : 0 < t)
  have h := continuousOn_theta_Ioi z (half_pos ht)
  exact (h.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

lemma locallyIntegrableOn_theta (z : ℍ) : LocallyIntegrableOn (fun t => (theta z t : ℂ)) (Ioi 0) :=
  (continuous_ofReal.comp_continuousOn (continuousOn_theta z)).locallyIntegrableOn measurableSet_Ioi

/-- `θ_z(t) − 1` decays faster than any power of `t`: it is at most `θ_1(c_z t) − 1`. -/
lemma isBigO_theta_sub (z : ℍ) (r : ℝ) : (fun t => (theta z t : ℂ) - 1) =O[atTop] (· ^ r) := by
  have hc := cz_pos z
  have h1 := (EpsteinFlat.isBigO_theta_sub one_pos r).comp_tendsto (tendsto_id.const_mul_atTop hc)
  have h2 : (fun t : ℝ => (cz z * t) ^ r) =O[atTop] (· ^ r) := by
    refine IsBigO.of_bound (cz z ^ r) ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.mul_rpow hc.le ht.le, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hc.le r)]
  refine (IsBigO.of_bound 1 ?_).trans (h1.trans h2)
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply, id, one_mul]
  have e1 : (theta z t : ℂ) - 1 = ((theta z t - 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (EpsteinFlat.theta 1 (cz z * t) : ℂ) - 1 = ((EpsteinFlat.theta 1 (cz z * t) - 1 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith [one_le_theta z ht])]
  have := theta_le_rect z ht
  exact le_trans (by linarith) (Real.le_norm_self _)

/-- **`θ_z` is a weak FE-pair** of weight `1` and root number `1`, its own dual, with constant term `1`. -/
def thetaFEPair (z : ℍ) : WeakFEPair ℂ where
  f t := (theta z t : ℂ)
  g t := (theta z t : ℂ)
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := locallyIntegrableOn_theta z
  hg_int := locallyIntegrableOn_theta z
  hk := one_pos
  hε := one_ne_zero
  h_feq x hx := by
    show ((theta z (1 / x) : ℝ) : ℂ) = ((1 : ℂ) * ((x ^ (1 : ℝ) : ℝ) : ℂ)) • ((theta z x : ℝ) : ℂ)
    rw [theta_inv z hx, Real.rpow_one, one_mul, smul_eq_mul, ofReal_mul]
  hf_top := isBigO_theta_sub z
  hg_top := isBigO_theta_sub z

lemma thetaFEPair_symm (z : ℍ) : (thetaFEPair z).symm = thetaFEPair z := by
  unfold thetaFEPair WeakFEPair.symm
  congr 1
  exact inv_one

/-- **The completed Epstein zeta function of `ℤz + ℤ`**, Mathlib's `WeakFEPair.Λ` for `θ_z`. -/
def Lambda (z : ℍ) (s : ℂ) : ℂ := (thetaFEPair z).Λ s

/-- **The completed Eisenstein series** `E*(z, s) = Λ_z(s)/2`, defined for every `s`; it is `Λ(2s)E(z, s)` on
`Re s > 1` (`Estar_eq`). -/
def Estar (z : ℍ) (s : ℂ) : ℂ := Lambda z s / 2

/-- **The functional equation** `E*(z, 1 − s) = E*(z, s)`, for every `s`. -/
theorem Estar_one_sub (z : ℍ) (s : ℂ) : Estar z (1 - s) = Estar z s := by
  have h := (thetaFEPair z).functional_equation s
  rw [thetaFEPair_symm] at h
  have hk : (((thetaFEPair z).k : ℝ) : ℂ) = 1 := by simp [thetaFEPair]
  unfold Estar Lambda
  rw [← hk, h]
  simp [thetaFEPair]

/-- **`E*(z, ·)` is holomorphic off `s = 0, 1`**. -/
theorem differentiableAt_Estar (z : ℍ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (Estar z) s :=
  ((thetaFEPair z).differentiableAt_Λ (Or.inl h0) (Or.inl (by simpa [thetaFEPair] using h1))).div_const 2

/-- `E*(z, ·)` is holomorphic on `ℂ \ {0, 1}`. -/
theorem differentiableOn_Estar (z : ℍ) : DifferentiableOn ℂ (Estar z) ({0, 1}ᶜ : Set ℂ) := fun s hs => by
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
  exact (differentiableAt_Estar z hs.1 hs.2).differentiableWithinAt

/-! ## `SL(2, ℤ)`-invariance of `E*` -/

lemma qf_smul (γ : SL(2, ℤ)) (z : ℍ) (v : Fin 2 → ℤ) : qf (γ • z) v = qf z (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  have hd : Complex.normSq (dn γ z) ≠ 0 := (Complex.normSq_pos.2 (dn_ne_zero γ z)).ne'
  have hy := z.im_pos
  unfold qf
  rw [nq_smul, ModEisenstein.im_smul]
  field_simp

/-- `θ_{γz} = θ_z`: `γ` permutes the lattice `ℤz + ℤ` up to the scaling by `cz + d`. -/
theorem theta_smul (γ : SL(2, ℤ)) (z : ℍ) (t : ℝ) : theta (γ • z) t = theta z t := by
  unfold theta
  simp_rw [qf_smul]
  exact (vecMulEquiv γ).tsum_eq (fun v => rexp (-π * qf z v * t))

/-- **`SL(2, ℤ)`-invariance**, for every `s`: `E*(γz, s) = E*(z, s)`. -/
theorem Estar_smul (γ : SL(2, ℤ)) (z : ℍ) (s : ℂ) : Estar (γ • z) s = Estar z s := by
  unfold Estar Lambda
  rw [EpsteinFlat.Λ_congr (P := thetaFEPair (γ • z)) (Q := thetaFEPair z)
    (fun t _ => by simp only [thetaFEPair, theta_smul]) rfl rfl rfl rfl]

/-! ## `E* = Λ(2s)E` on `Re s > 1` -/

lemma qf_eq_zero_iff (z : ℍ) (v : Fin 2 → ℤ) : qf z v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    have h1 := cz_le_qf z v
    have h2 : 0 < (v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 := by
      by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
        have : (0 : ℝ) < (v 1 : ℝ) ^ 2 := by positivity
        nlinarith [sq_nonneg (v 0 : ℝ)]
      · have : (0 : ℝ) < (v 0 : ℝ) ^ 2 := by positivity
        nlinarith [sq_nonneg (v 1 : ℝ)]
    have := mul_pos (cz_pos z) h2
    linarith
  · rintro rfl
    simp [qf, nq]

lemma term_eq_inv (z : ℍ) (s : ℂ) (v : Fin 2 → ℤ) : term z s v = ((((qf z v : ℝ)) : ℂ) ^ s)⁻¹ := by
  unfold term qf
  rw [← inv_div, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg (div_nonneg (nq_nonneg z v) z.im_pos.le)]; exact pi_pos.ne)]

/-- **On `Re s > 1`, `Λ_z(s) = π^{−s}Γ(s)Σ_v(y/|v₀z + v₁|²)^s`**, the completed Epstein zeta function. -/
theorem Lambda_eq_epstein (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Lambda z s = (π : ℂ) ^ (-s) * Complex.Gamma s * epstein z s := by
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun v : Fin 2 → ℤ => if qf z v = 0 then 0
      else (1 : ℂ) * rexp (-π * qf z v * t)) ((theta z t : ℂ) - 1) := by
    intro t (ht : 0 < t)
    have h := (hasSum_ofReal.2 (hasSum_theta z ht)).update 0 0
    convert h using 1
    · funext v
      rcases eq_or_ne v 0 with rfl | hv
      · simp [qf, nq]
      · rw [Function.update_of_ne hv]
        simp [(qf_eq_zero_iff z v).not.2 hv]
    · simp [qf, nq]
      ring
  have hsum : Summable fun v : Fin 2 → ℤ => ‖(1 : ℂ)‖ / qf z v ^ s.re := by
    refine (summable_norm_term z hs).congr fun v => ?_
    rw [norm_term z (by linarith), norm_one, qf, one_div, ← Real.inv_rpow (div_nonneg (nq_nonneg z v)
      z.im_pos.le), inv_div]
  have h := hasSum_mellin_pi_mul₀ (fun v => qf_nonneg z v) (by linarith) hF hsum
  have hM : mellin (fun t => (theta z t : ℂ) - 1) s = Lambda z s :=
    ((thetaFEPair z).hasMellin (by simpa [thetaFEPair] using hs)).2
  rw [hM] at h
  rw [h.tsum_eq.symm, epstein, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [term_eq_inv]
  ring

/-- **`E*(z, s) = Λ(2s)E(z, s)`** on `Re s > 1`, with Mathlib's `completedRiemannZeta`. -/
theorem Estar_eq (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Estar z s = completedRiemannZeta (2 * s) * E z s := by
  have h2 : 1 < (2 * s).re := by simp; linarith
  have e1 : completedRiemannZeta (2 * s) = Complex.Gammaℝ (2 * s) * riemannZeta (2 * s) := by
    rw [riemannZeta_def_of_ne_zero (by intro h; rw [h] at h2; norm_num at h2)]
    field_simp [Complex.Gammaℝ_ne_zero_of_re_pos (by linarith : 0 < (2 * s).re)]
  rw [Estar, Lambda_eq_epstein z hs, e1, Complex.Gammaℝ_def,
    show -(2 * s) / 2 = -s by ring, show 2 * s / 2 = s by ring]
  linear_combination (-((π : ℂ) ^ (-s) * Complex.Gamma s)) * zeta_mul_E z hs

/-- **The constant term of `E*`** on `Re s > 1`: `∫_0^1 E*(x + iy, s) dx = Λ(2s)y^s + Λ(2s − 1)y^{1−s}`. -/
theorem constTerm_Estar {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) :
    ∫ x in (0 : ℝ)..1, Estar (pt x y hy) s =
      completedRiemannZeta (2 * s) * (y : ℂ) ^ s + completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) := by
  have hΛ : completedRiemannZeta (2 * s) ≠ 0 :=
    PavlovFaddeev.completed_ne_zero_of_one_le_re (by simp; linarith)
  simp_rw [Estar_eq _ hs]
  rw [intervalIntegral.integral_const_mul, constTerm_eq hy hs, PavlovFaddeev.scatteringMatrix]
  field_simp

end ModContinuation
