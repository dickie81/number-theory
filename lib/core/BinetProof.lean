import Mathlib
import DigammaGauss

/-! # `ψ` as a Laplace transform

Step C of a proof of Binet's second formula `ψ(z) = log z − 1/(2z) − 2∫_0^∞ t dt/((t² + z²)(e^{2πt} − 1))`,
after the steps A and B of `DigammaGauss.lean`; the later steps, and the formula itself, are in the git history.

* **C. ψ as a Laplace transform.** `ψ(z) = log z − 1/(2z) − ∫_0^∞ e^{−zs}φ(s) ds` for `Re z > 0`, with
  `φ(s) = 1/(1 − e^{−s}) − 1/s − 1/2` (`|φ| ≤ ½`). Gauss's formula, the complex Frullani
  integral `log z − log w = ∫_0^∞ (e^{−ws} − e^{−zs})/s ds` (Fubini over the segment `[w, z]`) and
  `1/z = ∫e^{−zs}` show that `ψ(z) − log z + 1/(2z) + ∫e^{−zs}φ` does not depend on `z`. At `z = n + 1`
  it tends to `0` (`H_n − log(n + 1) → γ`).
-/

open Filter Topology MeasureTheory Set
open scoped Real

noncomputable section

namespace GammaIntegrals

/-! ## C1. The kernel `φ` -/

/-- `φ(s) = 1/(1 − e^{−s}) − 1/s − 1/2`. -/
def phiB (s : ℝ) : ℝ := 1 / (1 - Real.exp (-s)) - 1 / s - 1 / 2

theorem abs_phiB_le {s : ℝ} (hs : 0 < s) : |phiB s| ≤ 1 / 2 := by
  have hd := one_sub_exp_neg_pos hs
  have h2 : (1 + s) * Real.exp (-s) ≤ 1 := by
    have e : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.add_one_le_exp s, Real.exp_pos (-s)]
  have a : 1 / s ≤ 1 / (1 - Real.exp (-s)) :=
    one_div_le_one_div_of_le hd (by linarith [Real.add_one_le_exp (-s)])
  have b : 1 / (1 - Real.exp (-s)) - 1 / s ≤ 1 := by
    rw [div_sub_div _ _ hd.ne' hs.ne', div_le_one (by positivity)]; nlinarith
  unfold phiB; rw [abs_le]; constructor <;> linarith

theorem continuousOn_phiB : ContinuousOn phiB (Ioi 0) := by
  refine ((continuousOn_const.div (continuousOn_const.sub (Real.continuous_exp.comp
    continuous_neg).continuousOn) fun s hs => (one_sub_exp_neg_pos hs).ne').sub
    (continuousOn_const.div continuousOn_id fun s hs => (ne_of_gt hs))).sub continuousOn_const

theorem norm_cexp_neg_mul (z : ℂ) (s : ℝ) : ‖Complex.exp (-(z * s))‖ = Real.exp (-(z.re * s)) := by
  rw [Complex.norm_exp]; simp [Complex.mul_re]

/-- The Laplace transform `∫_0^∞ e^{−zs}φ(s) ds` is absolutely convergent, and `≤ 1/(2 Re z)`. -/
theorem integrableOn_lap {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun s : ℝ => Complex.exp (-(z * s)) * (phiB s : ℂ)) (Ioi 0) := by
  have he : IntegrableOn (fun s : ℝ => Real.exp (-(z.re * s))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hz
  have hb : IntegrableOn (fun s : ℝ => 1 / 2 * Real.exp (-(z.re * s))) (Ioi 0) := he.const_mul _
  refine hb.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)
      ).continuousOn).mul (Complex.continuous_ofReal.comp_continuousOn continuousOn_phiB)
  · rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_phiB_le hs) (Real.exp_pos _).le

theorem integral_exp_neg_mul' {c : ℝ} (hc : 0 < c) : ∫ s in Ioi (0 : ℝ), Real.exp (-(c * s)) = 1 / c := by
  have e : EqOn (fun t : ℝ => t ^ ((1 : ℝ) - 1) * Real.exp (-(c * t)))
      (fun t => Real.exp (-(c * t))) (Ioi 0) := fun t _ => by norm_num
  rw [← setIntegral_congr_fun measurableSet_Ioi e, Real.integral_rpow_mul_exp_neg_mul_Ioi one_pos hc,
    Real.rpow_one, Real.Gamma_one, mul_one]

theorem norm_lap_le {z : ℂ} (hz : 0 < z.re) :
    ‖∫ s in Ioi (0 : ℝ), Complex.exp (-(z * s)) * (phiB s : ℂ)‖ ≤ 1 / (2 * z.re) := by
  have he : IntegrableOn (fun s : ℝ => Real.exp (-(z.re * s))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hz
  have hb : IntegrableOn (fun s : ℝ => 1 / 2 * Real.exp (-(z.re * s))) (Ioi 0) := he.const_mul _
  refine (norm_integral_le_of_norm_le hb ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun s hs => ?_))).trans_eq ?_
  · rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_phiB_le hs) (Real.exp_pos _).le
  · rw [integral_const_mul, integral_exp_neg_mul' hz]; field_simp

/-! ## C2. The complex Frullani integral -/

theorem segment_re_ge {z w : ℂ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    min z.re w.re ≤ (w + θ * (z - w)).re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, zero_mul, sub_zero]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (min_le_right z.re w.re)),
    mul_nonneg h0 (sub_nonneg.2 (min_le_left z.re w.re))]

/-- `(e^{−ws} − e^{−zs})/s = ∫_0^1 (z − w)e^{−(w + θ(z − w))s} dθ`. -/
theorem frullani_inner (z w : ℂ) {s : ℝ} (hs : 0 < s) :
    (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s
      = ∫ θ in (0 : ℝ)..1, (z - w) * Complex.exp (-((w + θ * (z - w)) * s)) := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hd : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => -Complex.exp (-((w + θ * (z - w)) * s)) / s)
      ((z - w) * Complex.exp (-((w + θ * (z - w)) * s))) θ := fun θ => by
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ)) 1 θ := (hasDerivAt_id θ).ofReal_comp
    have h2 := (((h1.mul_const (z - w)).const_add w).mul_const (s : ℂ)).fun_neg.cexp.fun_neg.div_const
      (s : ℂ)
    convert h2 using 1; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero,
    add_sub_cancel]
  ring

theorem integrable_frullani_prod {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Integrable (Function.uncurry fun (s θ : ℝ) => (z - w) * Complex.exp (-((w + θ * (z - w)) * s)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 1))) := by
  set σ := min z.re w.re
  have hσ : 0 < σ := lt_min hz hw
  have hb : Integrable (fun p : ℝ × ℝ => (‖z - w‖ * Real.exp (-(σ * p.1))) * (1 : ℝ))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 1))) :=
    Integrable.mul_prod (f := fun s : ℝ => ‖z - w‖ * Real.exp (-(σ * s))) (g := fun _ : ℝ => (1 : ℝ))
      ((by simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hσ : IntegrableOn
        (fun s : ℝ => Real.exp (-(σ * s))) (Ioi 0)).const_mul _)
      (integrable_const _)
  refine hb.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)).2
    (Eventually.of_forall fun p hp => ?_)
  obtain ⟨hs, hθ⟩ := hp
  have hs' : 0 < p.1 := hs
  show ‖(z - w) * Complex.exp (-((w + (p.2 : ℂ) * (z - w)) * p.1))‖ ≤ ‖z - w‖ * Real.exp (-(σ * p.1)) * 1
  rw [mul_one, norm_mul, norm_cexp_neg_mul]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
    have := segment_re_ge (z := z) (w := w) hθ.1.le hθ.2; nlinarith)) (norm_nonneg _)

/-- **The complex Frullani integral**: `∫_0^∞ (e^{−ws} − e^{−zs})/s ds = log z − log w`. -/
theorem integral_frullani {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    ∫ s in Ioi (0 : ℝ), (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s
      = Complex.log z - Complex.log w := by
  set σ := min z.re w.re
  have hσ : 0 < σ := lt_min hz hw
  have hre : ∀ θ : ℝ, θ ∈ Set.uIcc (0 : ℝ) 1 → 0 < (w + θ * (z - w)).re := fun θ hθ => by
    rw [Set.uIcc_of_le zero_le_one] at hθ
    exact hσ.trans_le (segment_re_ge hθ.1 hθ.2)
  rw [setIntegral_congr_fun measurableSet_Ioi fun s hs => frullani_inner z w hs]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  rw [integral_integral_swap (integrable_frullani_prod hz hw)]
  have hin : ∀ θ ∈ Ioc (0 : ℝ) 1, ∫ s in Ioi (0 : ℝ), (z - w) * Complex.exp (-((w + θ * (z - w)) * s))
      = (z - w) / (w + θ * (z - w)) := fun θ hθ => by
    have hθ' : θ ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le zero_le_one]; exact Ioc_subset_Icc_self hθ
    rw [integral_const_mul, integral_cexp_neg (hre θ hθ')]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hin, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun θ : ℝ => Complex.log (w + θ * (z - w)))
      ((z - w) / (w + θ * (z - w))) θ := fun θ hθ => by
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ)) 1 θ := (hasDerivAt_id θ).ofReal_comp
    have h2 := ((h1.mul_const (z - w)).const_add w).clog_real
      (Complex.mem_slitPlane_iff.2 (Or.inl (hre θ hθ)))
    simpa using h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (ContinuousOn.intervalIntegrable ?_)]
  · simp
  · refine ContinuousOn.div continuousOn_const (Continuous.continuousOn (by fun_prop)) fun θ hθ => ?_
    intro h; have := hre θ hθ; rw [h, Complex.zero_re] at this; exact lt_irrefl _ this

/-! ## C3. `ψ` as a Laplace transform -/

/-- `L(z) = ∫_0^∞ e^{−zs}φ(s) ds`. -/
def lap (z : ℂ) : ℂ := ∫ s in Ioi (0 : ℝ), Complex.exp (-(z * s)) * (phiB s : ℂ)

theorem integrableOn_frullani {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (fun s : ℝ => (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s) (Ioi 0) := by
  set σ := min z.re w.re
  have hσ : 0 < σ := lt_min hz hw
  have he : IntegrableOn (fun s : ℝ => Real.exp (-(σ * s))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hσ
  refine (he.const_mul ‖z - w‖).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      Complex.continuous_ofReal.continuousOn fun s hs => ?_
    exact Complex.ofReal_ne_zero.2 (ne_of_gt hs)
  · have hs' : 0 < s := hs
    have hD := norm_cexp_sub_le (min_le_left z.re w.re) (min_le_right z.re w.re) hs'.le
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs'.le, div_le_iff₀ hs']
    calc _ ≤ ‖z - w‖ * (s * Real.exp (-(σ * s))) := hD
      _ = _ := by ring

theorem K_const {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Complex.digamma z - Complex.log z + 1 / (2 * z) + lap z
      = Complex.digamma w - Complex.log w + 1 / (2 * w) + lap w := by
  have hG := (digamma_sub_eq_integral hz hw).2
  have hF := integral_frullani hz hw
  have I1 := integrableOn_gaussK hz hw
  have I2 := integrableOn_frullani hz hw
  have I3 : IntegrableOn (fun s : ℝ => (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2) (Ioi 0) :=
    ((integrableOn_cexp_neg hz).sub (integrableOn_cexp_neg hw)).div_const 2
  have hC : ∫ s in Ioi (0 : ℝ), (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2
      = (1 / z - 1 / w) / 2 := by
    rw [integral_div, integral_sub (integrableOn_cexp_neg hz) (integrableOn_cexp_neg hw),
      integral_cexp_neg hz, integral_cexp_neg hw]
  have hpt : EqOn (fun s : ℝ => gaussK z w s - (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s
        + (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2)
      (fun s : ℝ => Complex.exp (-(w * s)) * (phiB s : ℂ) - Complex.exp (-(z * s)) * (phiB s : ℂ))
      (Ioi 0) := fun s _ => by
    simp only [gaussK, phiB]; push_cast; ring
  have e := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hpt
  have a1 : (∫ s in Ioi (0 : ℝ), (gaussK z w s - (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s
        + (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2))
      = (∫ s in Ioi (0 : ℝ), (gaussK z w s - (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s))
        + ∫ s in Ioi (0 : ℝ), (Complex.exp (-(z * s)) - Complex.exp (-(w * s))) / 2 :=
    integral_add (I1.sub I2) I3
  have a2 : (∫ s in Ioi (0 : ℝ), (gaussK z w s - (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s))
      = (∫ s in Ioi (0 : ℝ), gaussK z w s)
        - ∫ s in Ioi (0 : ℝ), (Complex.exp (-(w * s)) - Complex.exp (-(z * s))) / s :=
    integral_sub I1 I2
  have a3 : (∫ s in Ioi (0 : ℝ), (Complex.exp (-(w * s)) * (phiB s : ℂ)
        - Complex.exp (-(z * s)) * (phiB s : ℂ)))
      = lap w - lap z := integral_sub (integrableOn_lap hw) (integrableOn_lap hz)
  rw [a1, a2, a3, ← hG, hF, hC] at e
  linear_combination e

theorem tendsto_K_nat :
    Tendsto (fun m : ℕ => Complex.digamma ((m : ℂ) + 1) - Complex.log ((m : ℂ) + 1)
      + 1 / (2 * ((m : ℂ) + 1)) + lap ((m : ℂ) + 1)) atTop (𝓝 0) := by
  have hre : ∀ m : ℕ, ((m : ℂ) + 1).re = (m : ℝ) + 1 := fun m => by simp
  have T0 : Tendsto (fun m : ℕ => (1 : ℝ) / (2 * ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
    rw [mul_zero] at this
    exact this.congr fun m => by field_simp
  have T1 : Tendsto (fun m : ℕ => ((((harmonic m : ℚ) : ℝ) - Real.log ((m : ℝ) + 1)
      - Real.eulerMascheroniConstant : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_harmonic_sub_log_add_one.sub_const Real.eulerMascheroniConstant)
    rw [sub_self] at h
    have := (Complex.continuous_ofReal.tendsto 0).comp h
    rwa [Complex.ofReal_zero] at this
  have T2 : Tendsto (fun m : ℕ => (((1 : ℝ) / (2 * ((m : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp T0
    rwa [Complex.ofReal_zero] at this
  have T3 : Tendsto (fun m : ℕ => lap ((m : ℂ) + 1)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun m => by
      have := norm_lap_le (z := (m : ℂ) + 1) (by rw [hre]; positivity)
      rwa [hre] at this) T0
  have := (T1.add T2).add T3
  rw [add_zero, add_zero] at this
  refine this.congr fun m => ?_
  have hl : Complex.log ((m : ℂ) + 1) = ((Real.log ((m : ℝ) + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [Complex.digamma_nat_add_one, hl]
  push_cast; ring

/-- **`ψ` as a Laplace transform**: `ψ(z) = log z − 1/(2z) − ∫_0^∞ e^{−zs}φ(s) ds` for `Re z > 0`. -/
theorem digamma_eq_lap {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = Complex.log z - 1 / (2 * z) - lap z := by
  have hK : Tendsto (fun _ : ℕ => Complex.digamma z - Complex.log z + 1 / (2 * z) + lap z) atTop
      (𝓝 0) :=
    tendsto_K_nat.congr fun m => (K_const hz (by simp; positivity)).symm
  have := tendsto_nhds_unique tendsto_const_nhds hK
  linear_combination this

end GammaIntegrals

#print axioms GammaIntegrals.integral_frullani
#print axioms GammaIntegrals.digamma_eq_lap
