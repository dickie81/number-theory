/-
# The Fourier expansion of the completed Eisenstein series of `SL(2, ℤ)`

The two pieces of Milestone A left by `ModContinuation`, from one Fubini argument. For `z = x + iy` the completed
series is `E*(z, s) = Λ_z(s)/2`, with `Λ_z = WeakFEPair.Λ` of the theta function `θ_z` (`ModContinuation`).
* **A majorant uniform in `x`** (`theta_le_zero`): `θ_{x+iy}(t) ≤ θ_{iy}(t)`, from the dual series
  `θ_z(t) = (y/t)^{1/2}Σ_{(m, n)}e^{2πimnx}e^{−πy(tm² + n²/t)}`, whose phases are `1` at `x = 0`; so the
  correction `f_modif` of Mathlib's FE-pair machinery is dominated by that of `θ_{iy}`, uniformly in `x`.
* **Averaging over a period** (`integral_mul_Λ₀`, `integral_mul_Lambda`, `differentiable_mellin_avgF`): for a
  measurable weight `|w| ≤ 1`, `∫_0^1 w(x)Λ_{x+iy}(s) dx = M_w(s) − (∫_0^1 w)(1/s + 1/(1 − s))` for every `s`,
  where `M_w` is the Mellin transform of the averaged `f_modif`, itself a strong FE-pair, so `M_w` is entire.
* **The constant term for every `s`** (`integral_Estar`, `differentiableAt_constTerm`, `constTerm_Estar_all`):
  `s ↦ ∫_0^1 E*(x + iy, s) dx` is holomorphic on `ℂ \ {0, 1}`, and by the identity theorem on the connected set
  `ℂ \ {0, ½, 1}` from `ModContinuation.constTerm_Estar` it equals `Λ(2s)y^s + Λ(2s − 1)y^{1−s}` for every
  `s ≠ 0, ½, 1`. (At `s = ½` the right side has two poles that cancel, and Lean's values of `Λ` at its poles do not
  give the limit.)
* **The nonzero Fourier coefficients** (`integral_ek_theta`, `mellin_term`, `integral_ek_Lambda`,
  `fourierCoeff_Estar`, `sum_D`, `fourierCoeff_Estar_divisors`): for `k ≠ 0`,
  `∫_0^1 e^{−2πikx}θ_{x+iy}(t) dx = (y/t)^{1/2}Σ_{mn = k}e^{−πy(tm² + n²/t)}` (the dual series), each term has
  Mellin transform `2√y(|n|/|m|)^{s−1/2}K_{s−1/2}(2πy|k|)` with the library's `Eis.besselK`, and so, for every `s`,
  `∫_0^1 e^{−2πikx}E*(x + iy, s) dx = 2√y Σ_{d ∣ |k|}(|k|/d²)^{s−1/2}K_{s−1/2}(2π|k|y)`, the classical
  `2√y|k|^{s−1/2}σ_{1−2s}(|k|)K_{s−1/2}(2π|k|y)`.
* **The Fourier series** (`Estar_periodic`, `continuous_Estar_x`, `norm_fourierCoeff_Estar_le`,
  `summable_fourierCoeff_Estar`, `hasSum_fourier_Estar`, `hasSum_cos_Estar`, `hasSum_fourier_Estar_explicit`):
  `x ↦ E*(x + iy, s)` is `1`-periodic (`E*(Tz, s) = E*(z, s)`) and continuous (dominated convergence with the
  majorant `θ_{iy}`), so a continuous function on `ℝ/ℤ`; its coefficients decay like `|k|^N e^{−πy|k|}` (the decay
  of `Eis.besselK`), so are summable, and Mathlib's `has_pointwise_sum_fourier_series_of_summable` gives, for every
  `s` and `x`, `E*(x + iy, s) = Σ_{k ∈ ℤ} a_k e^{2πikx}`; pairing `±k`,
  `E*(x + iy, s) = Λ(2s)y^s + Λ(2s − 1)y^{1−s} + 4√y Σ_{n ≥ 1}(Σ_{d ∣ n}(n/d²)^{s−1/2})K_{s−1/2}(2πny)cos(2πnx)`
  for `s ≠ 0, ½, 1` (and with the constant term `∫_0^1 E*(u + iy, s) du` for every `s`).
-/
import Mathlib
import ModContinuation
import BesselK

open Complex Real Filter Topology Set MeasureTheory UpperHalfPlane HurwitzZeta Asymptotics
open scoped MatrixGroups

noncomputable section

namespace ModFourier

open ModEisenstein ModContinuation

variable {y : ℝ} (hy : 0 < y)

/-! ## A majorant uniform in `x` -/

lemma norm_dualTerm (z : ℍ) (t : ℝ) (p : ℤ × ℤ) :
    ‖dualTerm z t p‖ = rexp (-π * t * (p.1 : ℝ) ^ 2 * z.im) * rexp (-π * (p.2 : ℝ) ^ 2 * (z.im / t)) := by
  rw [dualTerm, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  have : ‖cexp (2 * π * Complex.I * (((p.1 : ℝ) * z.re : ℝ) : ℂ) * p.2)‖ = 1 := by
    rw [show (2 * π * Complex.I * (((p.1 : ℝ) * z.re : ℝ) : ℂ) * p.2) =
      (((2 * π * ((p.1 : ℝ) * z.re) * p.2 : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [this, one_mul]

lemma dualTerm_zero (t : ℝ) (p : ℤ × ℤ) :
    dualTerm (pt 0 y hy) t p = ((‖dualTerm (pt 0 y hy) t p‖ : ℝ) : ℂ) := by
  rw [norm_dualTerm, dualTerm, pt_re]
  simp

/-- **The majorant**: `θ_{x+iy}(t) ≤ θ_{iy}(t)`, from the dual series, whose phases are `1` at `x = 0`. -/
lemma theta_le_zero (x : ℝ) {t : ℝ} (ht : 0 < t) : theta (pt x y hy) t ≤ theta (pt 0 y hy) t := by
  have hx := theta_eq_dual (pt x y hy) ht
  have h0 := theta_eq_dual (pt 0 y hy) ht
  simp only [pt_im] at hx h0
  set c : ℝ := 1 / (t / y) ^ (1 / 2 : ℝ)
  have hc : 0 ≤ c := by positivity
  have hs0 : Summable fun p => ‖dualTerm (pt 0 y hy) t p‖ := (summable_dualTerm _ ht).norm
  have hnorm : ∀ p, ‖dualTerm (pt x y hy) t p‖ = ‖dualTerm (pt 0 y hy) t p‖ := fun p => by
    rw [norm_dualTerm, norm_dualTerm, pt_im, pt_im]
  have e0 : ∑' p, dualTerm (pt 0 y hy) t p = ((∑' p, ‖dualTerm (pt 0 y hy) t p‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun p => dualTerm_zero hy t p
  have hθ0 : theta (pt 0 y hy) t = c * ∑' p, ‖dualTerm (pt 0 y hy) t p‖ := by
    rw [e0] at h0
    exact_mod_cast h0
  have hθx : theta (pt x y hy) t = ‖((theta (pt x y hy) t : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [one_le_theta (pt x y hy) ht])]
  rw [hθx, hx, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, hθ0]
  gcongr
  refine (norm_tsum_le_tsum_norm (summable_dualTerm _ ht).norm).trans (le_of_eq ?_)
  exact tsum_congr hnorm

/-- `f_modif` of `θ_z`, written out. -/
lemma fmod_eq (z : ℍ) (t : ℝ) : (thetaFEPair z).f_modif t =
    if 1 < t then ((theta z t - 1 : ℝ) : ℂ) else if 0 < t ∧ t < 1 then ((theta z t - t ^ (-1 : ℝ) : ℝ) : ℂ)
      else 0 := by
  simp only [WeakFEPair.f_modif, thetaFEPair, Pi.add_apply, indicator_apply, mem_Ioi, mem_Ioo]
  split_ifs with h1 h2 h3 <;> first | (exfalso; linarith [h2.2]) | (push_cast; ring)

lemma fmod_nonneg_le (x : ℝ) (t : ℝ) :
    ‖(thetaFEPair (pt x y hy)).f_modif t‖ ≤ ‖(thetaFEPair (pt 0 y hy)).f_modif t‖ := by
  rw [fmod_eq, fmod_eq]
  split_ifs with h1 h2
  · have ht : 0 < t := by linarith
    have a := one_le_theta (pt x y hy) ht
    have b := theta_le_zero hy x ht
    rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg (by linarith)]
    linarith
  · have key : ∀ z : ℍ, t ^ (-1 : ℝ) ≤ theta z t := fun z => by
      have h := theta_inv z (one_div_pos.2 h2.1)
      rw [one_div_one_div] at h
      have h1' := one_le_theta z (one_div_pos.2 h2.1)
      rw [Real.rpow_neg_one]
      have : theta z t = t⁻¹ * theta z (1 / t) := by
        rw [h]; field_simp
      rw [this]
      nlinarith [inv_pos.2 h2.1]
    have a := key (pt x y hy)
    have b := theta_le_zero hy x h2.1
    rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg (by linarith [key (pt 0 y hy)])]
    linarith
  · simp

/-! ## Measurability in `(x, t)` -/

lemma measurable_theta : Measurable fun p : ℝ × ℝ => theta (pt p.1 y hy) p.2 := by
  have e : (fun p : ℝ × ℝ => theta (pt p.1 y hy) p.2) = fun p => ∑' v : Fin 2 → ℤ,
      rexp (-π * ((((v 0 : ℝ) * p.1 + v 1) ^ 2 + ((v 0 : ℝ) * y) ^ 2) / y) * p.2) := by
    funext p
    simp only [theta, qf, nq_pt, pt_im]
  rw [e]
  exact Measurable.tsum fun v => (by fun_prop : Continuous _).measurable

lemma measurable_fmod :
    Measurable fun p : ℝ × ℝ => (thetaFEPair (pt p.1 y hy)).f_modif p.2 := by
  simp_rw [fmod_eq]
  have h := measurable_theta hy
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    (Complex.measurable_ofReal.comp (h.sub measurable_const))
    (Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const))
      (Complex.measurable_ofReal.comp (h.sub (measurable_snd.pow_const _))) measurable_const)

lemma mellinConvergent_fmod (s : ℂ) : MellinConvergent (thetaFEPair (pt 0 y hy)).f_modif s :=
  ((thetaFEPair (pt 0 y hy)).isStrongFEPair_toStrongFEPair.hasMellin s).1

/-! ## Averaging `Λ_z` over a period against a weight -/

/-- The weighted average `∫_0^1 w(x) f_modif_{x+iy}(t) dx`. -/
def avgF (w : ℝ → ℂ) (t : ℝ) : ℂ := ∫ x in Ioc (0 : ℝ) 1, w x * (thetaFEPair (pt x y hy)).f_modif t

instance : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne

lemma integrable_prod (w : ℝ → ℂ) (hw : Measurable w) (hw1 : ∀ x, ‖w x‖ ≤ 1) (s : ℂ) :
    Integrable (Function.uncurry fun (x t : ℝ) => w x * ((t : ℂ) ^ (s - 1) • (thetaFEPair (pt x y hy)).f_modif t))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hM : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (s - 1)‖ * ‖(thetaFEPair (pt 0 y hy)).f_modif t‖)
      (volume.restrict (Ioi 0)) :=
    (mellinConvergent_fmod hy s).norm.congr (ae_of_all _ fun t => norm_smul _ _)
  refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hM) ?_ (ae_of_all _ fun p => ?_)
  · exact ((hw.comp measurable_fst).mul (((Eis.measurable_ofReal_cpow (s - 1)).comp measurable_snd).smul
      (measurable_fmod hy))).aestronglyMeasurable
  · simp only [Function.uncurry, norm_mul, norm_smul, one_mul]
    calc ‖w p.1‖ * (‖(p.2 : ℂ) ^ (s - 1)‖ * ‖(thetaFEPair (pt p.1 y hy)).f_modif p.2‖)
        ≤ 1 * (‖(p.2 : ℂ) ^ (s - 1)‖ * ‖(thetaFEPair (pt 0 y hy)).f_modif p.2‖) :=
          mul_le_mul (hw1 _) (mul_le_mul_of_nonneg_left (fmod_nonneg_le hy _ _) (norm_nonneg _))
            (by positivity) zero_le_one
      _ = _ := one_mul _

/-- **Fubini**: `∫_0^1 w(x)Λ₀_{x+iy}(s) dx` is the Mellin transform of the weighted average of `f_modif`. -/
theorem integral_mul_Λ₀ (w : ℝ → ℂ) (hw : Measurable w) (hw1 : ∀ x, ‖w x‖ ≤ 1) (s : ℂ) :
    ∫ x in Ioc (0 : ℝ) 1, w x * (thetaFEPair (pt x y hy)).Λ₀ s = mellin (avgF hy w) s := by
  have h := integral_integral_swap (integrable_prod hy w hw hw1 s)
  simp only [WeakFEPair.Λ₀, mellin, avgF]
  calc ∫ x in Ioc (0 : ℝ) 1, w x * ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • (thetaFEPair (pt x y hy)).f_modif t
      = ∫ x in Ioc (0 : ℝ) 1, ∫ t : ℝ in Ioi 0,
          w x * ((t : ℂ) ^ (s - 1) • (thetaFEPair (pt x y hy)).f_modif t) := by
        congr 1; funext x; rw [integral_const_mul]
    _ = ∫ t : ℝ in Ioi 0, ∫ x in Ioc (0 : ℝ) 1,
          w x * ((t : ℂ) ^ (s - 1) • (thetaFEPair (pt x y hy)).f_modif t) := h
    _ = _ := by
        congr 1; funext t
        rw [← integral_smul]
        congr 1; funext x
        simp only [smul_eq_mul]; ring

lemma Λ_thetaFEPair (z : ℍ) (s : ℂ) : (thetaFEPair z).Λ s = (thetaFEPair z).Λ₀ s - 1 / s - 1 / (1 - s) := by
  simp [WeakFEPair.Λ, thetaFEPair]

/-- **`∫_0^1 w(x)Λ_{x+iy}(s) dx`**, for every `s`, as a Mellin transform plus the polar terms. -/
theorem integral_mul_Lambda (w : ℝ → ℂ) (hw : Measurable w) (hw1 : ∀ x, ‖w x‖ ≤ 1) (s : ℂ) :
    ∫ x in Ioc (0 : ℝ) 1, w x * Lambda (pt x y hy) s =
      mellin (avgF hy w) s - (∫ x in Ioc (0 : ℝ) 1, w x) * (1 / s + 1 / (1 - s)) := by
  have hI : Integrable (fun x => w x * (thetaFEPair (pt x y hy)).Λ₀ s) (volume.restrict (Ioc 0 1)) := by
    refine (integrable_prod hy w hw hw1 s).integral_prod_left.congr (ae_of_all _ fun x => ?_)
    simp only [Function.uncurry, WeakFEPair.Λ₀, mellin]
    rw [integral_const_mul]
  have hwI : Integrable w (volume.restrict (Ioc (0 : ℝ) 1)) :=
    Integrable.mono' (integrable_const 1) hw.aestronglyMeasurable (ae_of_all _ hw1)
  rw [← integral_mul_Λ₀ hy w hw hw1 s, ← integral_mul_const, ← integral_sub hI (hwI.mul_const _)]
  congr 1; funext x
  rw [Lambda, Λ_thetaFEPair]; ring

lemma norm_avgF_le (w : ℝ → ℂ) (hw1 : ∀ x, ‖w x‖ ≤ 1) (t : ℝ) :
    ‖avgF hy w t‖ ≤ ‖(thetaFEPair (pt 0 y hy)).f_modif t‖ := by
  refine (norm_integral_le_of_norm_le_const (C := ‖(thetaFEPair (pt 0 y hy)).f_modif t‖)
    (ae_of_all _ fun x => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw1 x)).trans (fmod_nonneg_le hy x t)
  · simp

lemma stronglyMeasurable_avgF (w : ℝ → ℂ) (hw : Measurable w) : StronglyMeasurable (avgF hy w) := by
  have h : StronglyMeasurable (Function.uncurry fun (x t : ℝ) => w x * (thetaFEPair (pt x y hy)).f_modif t) :=
    ((hw.comp measurable_fst).mul (measurable_fmod hy)).stronglyMeasurable
  exact h.integral_prod_left

lemma g_modif_eq (z : ℍ) : (thetaFEPair z).g_modif = (thetaFEPair z).f_modif := by
  funext t
  simp [WeakFEPair.g_modif, WeakFEPair.f_modif, thetaFEPair]

lemma integrableOn_avgF (w : ℝ → ℂ) (hw : Measurable w) (hw1 : ∀ x, ‖w x‖ ≤ 1) :
    IntegrableOn (avgF hy w) (Ioi 0) := by
  have h := (mellinConvergent_fmod hy 1).norm
  simp only [sub_self, cpow_zero, one_smul] at h
  exact Integrable.mono' h (stronglyMeasurable_avgF hy w hw).aestronglyMeasurable
    (ae_of_all _ fun t => norm_avgF_le hy w hw1 t)

lemma avgF_inv (w : ℝ → ℂ) {t : ℝ} (ht : 0 < t) : avgF hy w (1 / t) = (t : ℂ) * avgF hy w t := by
  simp only [avgF]
  rw [← integral_const_mul]
  congr 1; funext x
  have h := (thetaFEPair (pt x y hy)).hf_modif_FE t ht
  rw [g_modif_eq] at h
  rw [h]
  simp [thetaFEPair]
  ring

lemma avgF_isBigO (w : ℝ → ℂ) (hw1 : ∀ x, ‖w x‖ ≤ 1) (r : ℝ) :
    (fun t => avgF hy w t - 0) =O[atTop] (· ^ r) :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun t => by
    simpa using norm_avgF_le hy w hw1 t)).trans ((thetaFEPair (pt 0 y hy)).hf_modif_top r)

/-- **The averaged theta function is a strong FE-pair**: for a weight `w` with `|w| ≤ 1`, the average
`∫_0^1 w(x) f_modif_{x+iy}(t) dx` satisfies `A(1/t) = tA(t)` and decays at both ends. -/
def avgPair (w : ℝ → ℂ) (hw : Measurable w) (hw1 : ∀ x, ‖w x‖ ≤ 1) : WeakFEPair ℂ where
  f := avgF hy w
  g := avgF hy w
  k := 1
  ε := 1
  f₀ := 0
  g₀ := 0
  hf_int := (integrableOn_avgF hy w hw hw1).locallyIntegrableOn
  hg_int := (integrableOn_avgF hy w hw hw1).locallyIntegrableOn
  hk := one_pos
  hε := one_ne_zero
  h_feq t ht := by
    rw [avgF_inv hy w ht]
    simp
  hf_top := avgF_isBigO hy w hw1
  hg_top := avgF_isBigO hy w hw1

lemma isStrong_avgPair (w : ℝ → ℂ) (hw : Measurable w) (hw1 : ∀ x, ‖w x‖ ≤ 1) :
    IsStrongFEPair (avgPair hy w hw hw1) := ⟨rfl, rfl⟩

/-- **The Mellin transform of the average is entire.** -/
theorem differentiable_mellin_avgF (w : ℝ → ℂ) (hw : Measurable w) (hw1 : ∀ x, ‖w x‖ ≤ 1) :
    Differentiable ℂ (mellin (avgF hy w)) := by
  have h := (isStrong_avgPair hy w hw hw1).differentiable_Λ
  rwa [(isStrong_avgPair hy w hw hw1).Λ_eq] at h

/-! ## The constant term of `E*` for every `s` -/

/-- **The constant term of `E*` for every `s`**, as a Mellin transform:
`∫_0^1 E*(x + iy, s) dx = (M(s) − 1/s − 1/(1 − s))/2` with `M` entire. -/
theorem integral_Estar (s : ℂ) :
    ∫ x in (0 : ℝ)..1, Estar (pt x y hy) s =
      (mellin (avgF hy fun _ => 1) s - (1 / s + 1 / (1 - s))) / 2 := by
  have h := integral_mul_Lambda hy (fun _ => 1) measurable_const (by simp) s
  simp only [one_mul] at h
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp only [Estar]
  rw [integral_div, h]
  simp

/-- **`s ↦ ∫_0^1 E*(x + iy, s) dx` is holomorphic off `s = 0, 1`.** -/
theorem differentiableAt_constTerm {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => ∫ x in (0 : ℝ)..1, Estar (pt x y hy) s) s := by
  simp_rw [integral_Estar hy]
  have h1' : 1 - s ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  refine ((((differentiable_mellin_avgF hy _ measurable_const (by simp)) s).sub
    (((differentiableAt_const _).div differentiableAt_id h0).add
      ((differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id) h1'))).div_const 2)

include hy in
lemma differentiableAt_rhs {s : ℂ} (h0 : s ≠ 0) (hh : s ≠ 1 / 2) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => completedRiemannZeta (2 * s) * (y : ℂ) ^ s +
      completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s)) s := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have a1 : DifferentiableAt ℂ (fun s : ℂ => completedRiemannZeta (2 * s)) s :=
    (differentiableAt_completedZeta (by intro h; apply h0; linear_combination h / 2)
      (by intro h; apply hh; linear_combination h / 2)).comp s ((differentiableAt_id.const_mul 2))
  have a2 : DifferentiableAt ℂ (fun s : ℂ => completedRiemannZeta (2 * s - 1)) s :=
    (differentiableAt_completedZeta (by intro h; apply hh; linear_combination h / 2)
      (by intro h; apply h1; linear_combination h / 2)).comp s
      ((differentiableAt_id.const_mul 2).sub_const 1)
  exact (a1.mul (differentiableAt_id.const_cpow (Or.inl hy0))).add
    (a2.mul (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hy0)))

/-- **The constant term of `E*` for every `s ≠ 0, ½, 1`**:
`∫_0^1 E*(x + iy, s) dx = Λ(2s)y^s + Λ(2s − 1)y^{1−s}`, by the identity theorem on `ℂ \ {0, ½, 1}` from
`ModContinuation.constTerm_Estar` on `Re s > 1`. -/
theorem constTerm_Estar_all {s : ℂ} (h0 : s ≠ 0) (hh : s ≠ 1 / 2) (h1 : s ≠ 1) :
    ∫ x in (0 : ℝ)..1, Estar (pt x y hy) s =
      completedRiemannZeta (2 * s) * (y : ℂ) ^ s + completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) := by
  set U : Set ℂ := ({0, 1 / 2, 1} : Set ℂ)ᶜ
  have hU : IsOpen U := (Set.toFinite _).isClosed.isOpen_compl
  have hUc : IsPreconnected U := ((Set.toFinite _).countable.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
  have mem : ∀ {s : ℂ}, s ∈ U ↔ s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1 := by
    intro s; simp [U, not_or]
  have hf : AnalyticOnNhd ℂ (fun s => ∫ x in (0 : ℝ)..1, Estar (pt x y hy) s) U :=
    DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_constTerm hy (mem.1 hs).1
      (mem.1 hs).2.2).differentiableWithinAt) hU
  have hg : AnalyticOnNhd ℂ (fun s => completedRiemannZeta (2 * s) * (y : ℂ) ^ s +
      completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s)) U :=
    DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_rhs hy (mem.1 hs).1 (mem.1 hs).2.1
      (mem.1 hs).2.2).differentiableWithinAt) hU
  have h2 : (2 : ℂ) ∈ U := mem.2 ⟨by norm_num, by norm_num, by norm_num⟩
  have hev : (fun s => ∫ x in (0 : ℝ)..1, Estar (pt x y hy) s) =ᶠ[𝓝 2] fun s =>
      completedRiemannZeta (2 * s) * (y : ℂ) ^ s + completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
    exact constTerm_Estar hy hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h2 hev (mem.2 ⟨h0, hh, h1⟩)

/-! ## The nonzero Fourier coefficients -/

/-- The character `e(−kx) = e^{−2πikx}`. -/
def ek (k : ℤ) (x : ℝ) : ℂ := cexp (-(2 * π * Complex.I * k * x))

lemma norm_ek (k : ℤ) (x : ℝ) : ‖ek k x‖ = 1 := by
  rw [ek, show -(2 * π * Complex.I * k * x) = ((-(2 * π * k * x) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma measurable_ek (k : ℤ) : Measurable (ek k) := by
  unfold ek; fun_prop

lemma integral_phase (j : ℤ) :
    ∫ x in Ioc (0 : ℝ) 1, cexp (2 * π * Complex.I * j * x) = if j = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hj
  · simp [hj]
  · have hc : (2 * π * Complex.I * j : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, pi_ne_zero, hj]
    rw [integral_exp_mul_complex hc]
    have : cexp (2 * π * Complex.I * j) = 1 := by
      rw [show 2 * π * Complex.I * j = j * (2 * π * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I j
    simp [this]

lemma integral_ek {k : ℤ} (hk : k ≠ 0) : ∫ x in Ioc (0 : ℝ) 1, ek k x = 0 := by
  have h := integral_phase (-k)
  simp only [neg_eq_zero, hk, ↓reduceIte] at h
  rw [← h]
  congr 1; funext x
  rw [ek]; push_cast; ring_nf

/-- The pairs `(m, n)` with `mn = k`. -/
def D (k : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-|k|) |k|) ×ˢ (Finset.Icc (-|k|) |k|)).filter fun p => p.1 * p.2 = k

lemma mem_D {k : ℤ} (hk : k ≠ 0) {p : ℤ × ℤ} : p ∈ D k ↔ p.1 * p.2 = k := by
  simp only [D, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · have h2 : p.2 ≠ 0 := by rintro h2; rw [h2, mul_zero] at h; exact hk h.symm
    have : |p.1| ≤ |k| := by
      rw [← h, abs_mul]; exact le_mul_of_one_le_right (abs_nonneg _) (Int.one_le_abs h2)
    exact abs_le.1 this
  · have h1 : p.1 ≠ 0 := by rintro h1; rw [h1, zero_mul] at h; exact hk h.symm
    have : |p.2| ≤ |k| := by
      rw [← h, abs_mul]; exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs h1)
    exact abs_le.1 this

/-- The Gaussian weight `e^{−πy(tm² + n²/t)}` of the dual series. -/
def rr (y t : ℝ) (p : ℤ × ℤ) : ℝ := rexp (-π * t * (p.1 : ℝ) ^ 2 * y) * rexp (-π * (p.2 : ℝ) ^ 2 * (y / t))

lemma dualTerm_pt (x t : ℝ) (p : ℤ × ℤ) :
    dualTerm (pt x y hy) t p = cexp (2 * π * Complex.I * ((p.1 * p.2 : ℤ) : ℂ) * x) * (rr y t p : ℂ) := by
  simp only [dualTerm, pt_re, pt_im, rr]
  push_cast
  ring_nf

include hy in
lemma summable_rr {t : ℝ} (ht : 0 < t) : Summable (rr y t) :=
  (summable_dualTerm (pt 0 y hy) ht).norm.congr fun p => by rw [norm_dualTerm, pt_im]; rfl

/-- **The `k`-th Fourier coefficient of `θ_{x+iy}(t)`**, `k ≠ 0`:
`∫_0^1 e^{−2πikx}θ_{x+iy}(t) dx = (y/t)^{1/2}Σ_{mn = k}e^{−πy(tm² + n²/t)}`. -/
theorem integral_ek_theta {k : ℤ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioc (0 : ℝ) 1, ek k x * (theta (pt x y hy) t : ℂ) =
      ((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ p ∈ D k, (rr y t p : ℂ) := by
  set c : ℂ := ((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  have hθ : ∀ x, ek k x * (theta (pt x y hy) t : ℂ) = c * ∑' p, ek k x * dualTerm (pt x y hy) t p := by
    intro x
    have h := theta_eq_dual (pt x y hy) ht
    simp only [pt_im] at h
    rw [h, tsum_mul_left]; ring
  have hnorm : ∀ p x, ‖ek k x * dualTerm (pt x y hy) t p‖ = rr y t p := fun p x => by
    rw [norm_mul, norm_ek, one_mul, norm_dualTerm, pt_im]; rfl
  have hint : ∀ p, Integrable (fun x => ek k x * dualTerm (pt x y hy) t p) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    fun p => Integrable.mono' (integrable_const (rr y t p))
      (((measurable_ek k).mul (by simp_rw [dualTerm_pt]; fun_prop)).aestronglyMeasurable)
      (ae_of_all _ fun x => (hnorm p x).le)
  have hsum : Summable fun p => ∫ x in Ioc (0 : ℝ) 1, ‖ek k x * dualTerm (pt x y hy) t p‖ := by
    refine (summable_rr hy ht).congr fun p => ?_
    simp_rw [hnorm p]; simp
  have hterm : ∀ p, ∫ x in Ioc (0 : ℝ) 1, ek k x * dualTerm (pt x y hy) t p =
      if p.1 * p.2 = k then (rr y t p : ℂ) else 0 := by
    intro p
    have e : ∀ x : ℝ, ek k x * dualTerm (pt x y hy) t p =
        cexp (2 * π * Complex.I * ((p.1 * p.2 - k : ℤ) : ℂ) * x) * (rr y t p : ℂ) := by
      intro x
      rw [dualTerm_pt, ek, ← mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    simp_rw [e]
    rw [integral_mul_const, integral_phase]
    by_cases h : p.1 * p.2 = k
    · simp [h]
    · have : p.1 * p.2 - k ≠ 0 := sub_ne_zero.2 h
      simp [this, h]
  simp_rw [hθ]
  rw [integral_const_mul, ← integral_tsum_of_summable_integral_norm hint hsum]
  congr 1
  simp_rw [hterm]
  rw [tsum_eq_sum (s := D k) (fun p hp => by
    simp only [ite_eq_right_iff]; intro h; exact absurd ((mem_D hk).2 h) hp)]
  exact Finset.sum_congr rfl fun p hp => by simp [(mem_D hk).1 hp]

lemma measurable_theta_x (t : ℝ) : Measurable fun x : ℝ => theta (pt x y hy) t :=
  (measurable_theta hy).comp (f := fun x : ℝ => (x, t)) (by fun_prop)

lemma integral_ek_sub {k : ℤ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t) (a : ℝ) :
    ∫ x in Ioc (0 : ℝ) 1, ek k x * ((theta (pt x y hy) t - a : ℝ) : ℂ) =
      ∫ x in Ioc (0 : ℝ) 1, ek k x * (theta (pt x y hy) t : ℂ) := by
  have i1 : Integrable (fun x => ek k x * (theta (pt x y hy) t : ℂ)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    Integrable.mono' (integrable_const (theta (pt 0 y hy) t))
      ((measurable_ek k).mul (Complex.measurable_ofReal.comp (measurable_theta_x hy t))).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [norm_mul, norm_ek, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (by linarith [one_le_theta (pt x y hy) ht])]
        exact theta_le_zero hy x ht)
  have i2 : Integrable (fun x => ek k x * (a : ℂ)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    Integrable.mono' (integrable_const ‖(a : ℂ)‖) ((measurable_ek k).mul measurable_const).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [norm_mul, norm_ek, one_mul])
  push_cast
  simp_rw [mul_sub]
  rw [integral_sub i1 i2, integral_mul_const, integral_ek hk, zero_mul, sub_zero]

lemma avgF_ek {k : ℤ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t) (h1 : t ≠ 1) :
    avgF hy (ek k) t = ((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ p ∈ D k, (rr y t p : ℂ) := by
  rw [← integral_ek_theta hy hk ht, avgF]
  simp_rw [fmod_eq]
  rcases lt_or_gt_of_ne h1 with h | h
  · have : ¬(1 < t) := not_lt.2 h.le
    simp only [this, ht, h, and_self, ↓reduceIte]
    exact integral_ek_sub hy hk ht _
  · simp only [h, ↓reduceIte]
    exact integral_ek_sub hy hk ht _

lemma cpow_inv_neg {a : ℝ} (ha : 0 < a) (w : ℂ) : ((a⁻¹ : ℝ) : ℂ) ^ (-w) = (a : ℂ) ^ w := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ha.le]; exact pi_ne_zero.symm),
    Complex.cpow_neg, inv_inv]

include hy in
/-- One term in the `K`-Bessel form: for `t > 0` and `mn ≠ 0`,
`(y/t)^{1/2}e^{−πy(tm² + n²/t)} = √y·t^{−1/2}·e^{−(X/2)(t/a + a/t)}` with `X = 2πy|mn|` and `a = |n|/|m|`. -/
lemma term_eq_bkK {p : ℤ × ℤ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) {t : ℝ} (ht : 0 < t) :
    ((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (rr y t p : ℂ) = (√y : ℂ) • ((t : ℂ) ^ (-(1 / 2) : ℂ) •
      (Eis.bkK (2 * π * y * (|(p.1 : ℝ)| * |(p.2 : ℝ)|)) ((|(p.2 : ℝ)| / |(p.1 : ℝ)|)⁻¹ * t) : ℂ)) := by
  have hm : 0 < |(p.1 : ℝ)| := abs_pos.2 (by exact_mod_cast h1)
  have hn : 0 < |(p.2 : ℝ)| := abs_pos.2 (by exact_mod_cast h2)
  have e1 : (t : ℂ) ^ (-(1 / 2) : ℂ) = ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht.le]; push_cast; ring_nf
  rw [e1, smul_eq_mul, smul_eq_mul]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [Real.div_rpow ht.le hy.le, Real.rpow_neg ht.le, Real.sqrt_eq_rpow, rr, Eis.bkK, ← Real.exp_add]
  have ex : -π * t * (p.1 : ℝ) ^ 2 * y + -π * (p.2 : ℝ) ^ 2 * (y / t) =
      -(2 * π * y * (|(p.1 : ℝ)| * |(p.2 : ℝ)|) / 2) *
        ((|(p.2 : ℝ)| / |(p.1 : ℝ)|)⁻¹ * t + ((|(p.2 : ℝ)| / |(p.1 : ℝ)|)⁻¹ * t)⁻¹) := by
    rw [← sq_abs (p.1 : ℝ), ← sq_abs (p.2 : ℝ)]
    field_simp
    ring
  rw [ex]
  have : (0 : ℝ) < y ^ (1 / 2 : ℝ) := by positivity
  have : (0 : ℝ) < t ^ (1 / 2 : ℝ) := by positivity
  field_simp

include hy in
/-- **One term of the Fourier coefficient**: the Mellin transform of `(y/t)^{1/2}e^{−πy(tm² + n²/t)}` is
`2√y(|n|/|m|)^{s−1/2}K_{s−1/2}(2πy|mn|)`, for every `s`. -/
lemma mellin_term {p : ℤ × ℤ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) (s : ℂ) :
    MellinConvergent (fun t => ((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (rr y t p : ℂ)) s ∧
    mellin (fun t => ((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (rr y t p : ℂ)) s =
      2 * (√y : ℂ) * ((|(p.2 : ℝ)| / |(p.1 : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) *
        Eis.besselK (s - 1 / 2) (2 * π * y * (|(p.1 : ℝ)| * |(p.2 : ℝ)|)) := by
  have hm : 0 < |(p.1 : ℝ)| := abs_pos.2 (by exact_mod_cast h1)
  have hn : 0 < |(p.2 : ℝ)| := abs_pos.2 (by exact_mod_cast h2)
  set a : ℝ := |(p.2 : ℝ)| / |(p.1 : ℝ)|
  have ha : 0 < a⁻¹ := inv_pos.2 (div_pos hn hm)
  set X : ℝ := 2 * π * y * (|(p.1 : ℝ)| * |(p.2 : ℝ)|)
  have hX : 0 < X := by positivity
  have hA := (MellinConvergent.comp_mul_left ha).2 (Eis.mellinConvergent_bkK hX (s - 1 / 2))
  have hB : MellinConvergent (fun t => (t : ℂ) ^ (-(1 / 2) : ℂ) • (Eis.bkK X (a⁻¹ * t) : ℂ)) s :=
    MellinConvergent.cpow_smul.2 (by rw [show s + -(1 / 2) = s - 1 / 2 by ring]; exact hA)
  have hC := hB.const_smul (√y : ℂ)
  have eq : EqOn (fun t => ((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (rr y t p : ℂ))
      (fun t => (√y : ℂ) • ((t : ℂ) ^ (-(1 / 2) : ℂ) • (Eis.bkK X (a⁻¹ * t) : ℂ))) (Ioi 0) :=
    fun t ht => term_eq_bkK hy h1 h2 ht
  refine ⟨?_, ?_⟩
  · refine IntegrableOn.congr_fun hC (fun t ht => ?_) measurableSet_Ioi
    simp only [eq ht]
  · have hm' : mellin (fun t => ((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (rr y t p : ℂ)) s =
        mellin (fun t => (√y : ℂ) • ((t : ℂ) ^ (-(1 / 2) : ℂ) • (Eis.bkK X (a⁻¹ * t) : ℂ))) s :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by simp only [eq ht]
    rw [hm', mellin_const_smul, mellin_cpow_smul,
      mellin_comp_mul_left (fun t => (Eis.bkK X t : ℂ)) _ ha, cpow_inv_neg (div_pos hn hm),
      show s + -(1 / 2) = s - 1 / 2 by ring]
    simp only [Eis.besselK, smul_eq_mul]
    ring

/-- **The `k`-th Fourier coefficient of `Λ_{x+iy}(s)`**, for `k ≠ 0` and every `s`:
`∫_0^1 e^{−2πikx}Λ_{x+iy}(s) dx = Σ_{mn = k} 2√y(|n|/|m|)^{s−1/2}K_{s−1/2}(2πy|k|)`. -/
theorem integral_ek_Lambda {k : ℤ} (hk : k ≠ 0) (s : ℂ) :
    ∫ x in Ioc (0 : ℝ) 1, ek k x * Lambda (pt x y hy) s =
      ∑ p ∈ D k, 2 * (√y : ℂ) * ((|(p.2 : ℝ)| / |(p.1 : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) *
        Eis.besselK (s - 1 / 2) (2 * π * y * |(k : ℝ)|) := by
  rw [integral_mul_Lambda hy (ek k) (measurable_ek k) (fun x => (norm_ek k x).le) s, integral_ek hk, zero_mul,
    sub_zero]
  have hnz : ∀ p ∈ D k, p.1 ≠ 0 ∧ p.2 ≠ 0 := fun p hp => by
    have h := (mem_D hk).1 hp
    constructor
    · rintro h0; rw [h0, zero_mul] at h; exact hk h.symm
    · rintro h0; rw [h0, mul_zero] at h; exact hk h.symm
  have hae : mellin (avgF hy (ek k)) s =
      mellin (fun t => ∑ p ∈ D k, ((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (rr y t p : ℂ)) s := by
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (1 : ℝ))] with t h1 ht
    rw [avgF_ek hy hk ht (by simpa using h1), Finset.mul_sum]
  rw [hae]
  simp only [mellin, Finset.smul_sum]
  rw [integral_finsetSum _ (fun p hp => (mellin_term hy (hnz p hp).1 (hnz p hp).2 s).1)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h := (mellin_term hy (hnz p hp).1 (hnz p hp).2 s).2
  simp only [mellin] at h
  rw [h]
  have hk' : |(p.1 : ℝ)| * |(p.2 : ℝ)| = |(k : ℝ)| := by
    rw [← abs_mul, ← (mem_D hk).1 hp]; push_cast; ring_nf
  rw [hk']

/-- **The nonzero Fourier coefficients of `E*`**: for `k ≠ 0` and every `s`,
`∫_0^1 e^{−2πikx}E*(x + iy, s) dx = √y K_{s−1/2}(2π|k|y)Σ_{mn = k}(|n|/|m|)^{s−1/2}`. -/
theorem fourierCoeff_Estar {k : ℤ} (hk : k ≠ 0) (s : ℂ) :
    ∫ x in (0 : ℝ)..1, cexp (-(2 * π * Complex.I * k * x)) * Estar (pt x y hy) s =
      (√y : ℂ) * Eis.besselK (s - 1 / 2) (2 * π * |(k : ℝ)| * y) *
        ∑ p ∈ D k, ((|(p.2 : ℝ)| / |(p.1 : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have h := integral_ek_Lambda hy hk s
  simp only [Estar, mul_div_assoc']
  rw [integral_div]
  change (∫ x in Ioc (0 : ℝ) 1, ek k x * Lambda (pt x y hy) s) / 2 = _
  rw [h, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show 2 * π * |(k : ℝ)| * y = 2 * π * y * |(k : ℝ)| by ring]
  ring

/-! ## The divisor sum -/

lemma fiber_D {k : ℤ} (hk : k ≠ 0) {d : ℕ} (hd : d ∈ k.natAbs.divisors) :
    (D k).filter (fun p => p.1.natAbs = d) = {((d : ℤ), k / d), (-(d : ℤ), -(k / d))} := by
  have hdk : (d : ℤ) ∣ k := Int.natCast_dvd.2 (Nat.dvd_of_mem_divisors hd)
  have hd0 : (d : ℤ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hd; exact_mod_cast this.ne'
  ext p
  simp only [Finset.mem_filter, mem_D hk, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h, hp⟩
    have hp1 : p.1 ≠ 0 := by rintro h0; rw [h0, zero_mul] at h; exact hk h.symm
    rcases Int.natAbs_eq p.1 with e | e <;> rw [hp] at e
    · left
      refine Prod.ext e ?_
      rw [← h, e]; exact (Int.mul_ediv_cancel_left _ hd0).symm
    · right
      refine Prod.ext e ?_
      simp only
      rw [← h, e, neg_mul, Int.neg_ediv_of_dvd (dvd_mul_right _ _), Int.mul_ediv_cancel_left _ hd0, neg_neg]
  · rintro (rfl | rfl)
    · exact ⟨Int.mul_ediv_cancel' hdk, by simp⟩
    · exact ⟨by rw [neg_mul_neg]; exact Int.mul_ediv_cancel' hdk, by simp⟩

lemma card_fiber_D {k : ℤ} (hk : k ≠ 0) {d : ℕ} (hd : d ∈ k.natAbs.divisors) :
    ((D k).filter (fun p => p.1.natAbs = d)).card = 2 := by
  rw [fiber_D hk hd]
  have hd0 : (d : ℤ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hd; exact_mod_cast this.ne'
  refine Finset.card_pair fun h => hd0 ?_
  have := congrArg Prod.fst h
  simp only at this
  omega

/-- **The divisor sum**: `Σ_{mn = k}(|n|/|m|)^w = 2Σ_{d ∣ |k|}(|k|/d²)^w`, that is `2|k|^wσ_{−2w}(|k|)`. -/
theorem sum_D {k : ℤ} (hk : k ≠ 0) (w : ℂ) :
    ∑ p ∈ D k, ((|(p.2 : ℝ)| / |(p.1 : ℝ)| : ℝ) : ℂ) ^ w =
      2 * ∑ d ∈ k.natAbs.divisors, ((|(k : ℝ)| / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ w := by
  have hmaps : ∀ p ∈ D k, p.1.natAbs ∈ k.natAbs.divisors := fun p hp => by
    rw [Nat.mem_divisors]
    refine ⟨Int.natAbs_dvd_natAbs.2 ⟨p.2, ((mem_D hk).1 hp).symm⟩, Int.natAbs_ne_zero.2 hk⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hval : ∀ p ∈ (D k).filter (fun p => p.1.natAbs = d),
      ((|(p.2 : ℝ)| / |(p.1 : ℝ)| : ℝ) : ℂ) ^ w = ((|(k : ℝ)| / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ w := by
    intro p hp
    rw [Finset.mem_filter, mem_D hk] at hp
    have h1 : |(p.1 : ℝ)| = d := by rw [← hp.2, Nat.cast_natAbs, Int.cast_abs]
    have hk' : |(p.1 : ℝ)| * |(p.2 : ℝ)| = |(k : ℝ)| := by
      rw [← abs_mul, ← hp.1]; push_cast; ring_nf
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have e : |(p.2 : ℝ)| / |(p.1 : ℝ)| = |(k : ℝ)| / (d : ℝ) ^ 2 := by
      rw [← hk', h1]; field_simp
    rw [e]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, card_fiber_D hk hd]
  simp

/-- **The Fourier coefficients of `E*` with the divisor function**: for `k ≠ 0` and every `s`,
`∫_0^1 e^{−2πikx}E*(x + iy, s) dx = 2√y Σ_{d ∣ |k|}(|k|/d²)^{s−1/2}·K_{s−1/2}(2π|k|y)`, the classical
`2√y|k|^{s−1/2}σ_{1−2s}(|k|)K_{s−1/2}(2π|k|y)`. -/
theorem fourierCoeff_Estar_divisors {k : ℤ} (hk : k ≠ 0) (s : ℂ) :
    ∫ x in (0 : ℝ)..1, cexp (-(2 * π * Complex.I * k * x)) * Estar (pt x y hy) s =
      2 * (√y : ℂ) * Eis.besselK (s - 1 / 2) (2 * π * |(k : ℝ)| * y) *
        ∑ d ∈ k.natAbs.divisors, ((|(k : ℝ)| / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1 / 2) := by
  rw [fourierCoeff_Estar hy hk s, sum_D hk]
  ring

/-! ## The Fourier series -/

lemma pt_add_one (x : ℝ) : pt (x + 1) y hy = ModularGroup.T • pt x y hy := by
  rw [UpperHalfPlane.modular_T_smul]
  apply UpperHalfPlane.ext
  simp [pt, UpperHalfPlane.coe_vadd]
  ring

/-- **`E*(x + iy, s)` is `1`-periodic in `x`**, by `E*(Tz, s) = E*(z, s)`. -/
theorem Estar_periodic (s : ℂ) : Function.Periodic (fun x => Estar (pt x y hy) s) 1 := fun x => by
  simp only
  rw [pt_add_one, Estar_smul]

lemma continuous_theta_x {t : ℝ} (ht : 0 < t) : Continuous fun x => theta (pt x y hy) t := by
  have e : (fun x => theta (pt x y hy) t) =
      fun x => ((((1 / (t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑' p, dualTerm (pt x y hy) t p)).re := by
    funext x
    have h := theta_eq_dual (pt x y hy) ht
    rw [pt_im] at h
    rw [← h, Complex.ofReal_re]
  rw [e]
  refine Complex.continuous_re.comp (continuous_const.mul ?_)
  refine continuous_tsum (u := fun p => ‖dualTerm (pt 0 y hy) t p‖) (fun p => ?_)
    (summable_dualTerm _ ht).norm (fun p x => ?_)
  · simp only [dualTerm, pt_re, pt_im]
    fun_prop
  · rw [norm_dualTerm, norm_dualTerm, pt_im, pt_im]

lemma continuous_fmod_x (t : ℝ) : Continuous fun x => (thetaFEPair (pt x y hy)).f_modif t := by
  simp_rw [fmod_eq]
  split_ifs with h1 h2
  · exact Complex.continuous_ofReal.comp ((continuous_theta_x hy (by linarith)).sub continuous_const)
  · exact Complex.continuous_ofReal.comp ((continuous_theta_x hy h2.1).sub continuous_const)
  · exact continuous_const

lemma continuous_Λ₀ (s : ℂ) : Continuous fun x => (thetaFEPair (pt x y hy)).Λ₀ s := by
  simp only [WeakFEPair.Λ₀, mellin]
  refine continuous_of_dominated
    (bound := fun t => ‖(t : ℂ) ^ (s - 1)‖ * ‖(thetaFEPair (pt 0 y hy)).f_modif t‖)
    (fun x => ?_) (fun x => ae_of_all _ fun t => ?_) ?_ (ae_of_all _ fun t => ?_)
  · exact ((Eis.measurable_ofReal_cpow (s - 1)).smul
      ((measurable_fmod hy).comp measurable_prodMk_left)).aestronglyMeasurable
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (fmod_nonneg_le hy _ _) (norm_nonneg _)
  · exact (mellinConvergent_fmod hy s).norm.congr (ae_of_all _ fun t => norm_smul _ _)
  · exact (continuous_fmod_x hy t).const_smul ((t : ℂ) ^ (s - 1))

/-- **`x ↦ E*(x + iy, s)` is continuous**, for every `s`: dominated convergence in the Mellin integral, with the
majorant `θ_{iy}`. -/
theorem continuous_Estar_x (s : ℂ) : Continuous fun x => Estar (pt x y hy) s := by
  simp only [Estar, Lambda, Λ_thetaFEPair]
  exact (((continuous_Λ₀ hy s).sub continuous_const).sub continuous_const).div_const 2

/-- `x ↦ E*(x + iy, s)` on the circle `ℝ/ℤ`. -/
def EstarCircle (s : ℂ) : C(UnitAddCircle, ℂ) :=
  ⟨(Estar_periodic hy s).lift, (continuous_Estar_x hy s).quotient_liftOn' _⟩

lemma EstarCircle_coe (s : ℂ) (x : ℝ) : EstarCircle hy s (x : UnitAddCircle) = Estar (pt x y hy) s := rfl

lemma fourierCoeff_EstarCircle (s : ℂ) (k : ℤ) : fourierCoeff (EstarCircle hy s) k =
    ∫ x in (0 : ℝ)..1, cexp (-(2 * π * Complex.I * k * x)) * Estar (pt x y hy) s := by
  rw [fourierCoeff_eq_intervalIntegral _ k 0, zero_add, div_one, one_smul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [fourier_coe_apply, smul_eq_mul, EstarCircle_coe]
  push_cast
  ring_nf

lemma rpow_le_abs {a K : ℝ} (ha : 0 < a) (haK : a ≤ K) (hiK : a⁻¹ ≤ K) (hK : 1 ≤ K) (r : ℝ) :
    a ^ r ≤ K ^ |r| := by
  rcases le_or_gt 0 r with hr | hr
  · exact (Real.rpow_le_rpow ha.le haK hr).trans (Real.rpow_le_rpow_of_exponent_le hK (le_abs_self r))
  · have e : a ^ r = a⁻¹ ^ (-r) := by
      rw [Real.inv_rpow ha.le, Real.rpow_neg ha.le, inv_inv]
    rw [e, abs_of_neg hr]
    exact Real.rpow_le_rpow (inv_pos.2 ha).le hiK (by linarith)

lemma norm_divSum_le {k : ℤ} (hk : k ≠ 0) (w : ℂ) :
    ‖∑ d ∈ k.natAbs.divisors, ((|(k : ℝ)| / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ w‖ ≤ |(k : ℝ)| ^ (1 + |w.re|) := by
  have hK : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hK1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← hK]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hk)
  have hK0 : (0 : ℝ) < |(k : ℝ)| := by linarith
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d ∈ k.natAbs.divisors,
      ‖((|(k : ℝ)| / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ w‖ ≤ |(k : ℝ)| ^ |w.re| := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hdk : (d : ℝ) ≤ |(k : ℝ)| := by
      rw [← hK]; exact_mod_cast Nat.divisor_le hd
    have ha : 0 < |(k : ℝ)| / (d : ℝ) ^ 2 := by positivity
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
    refine rpow_le_abs ha (div_le_self hK0.le (by nlinarith)) ?_ hK1 _
    rw [inv_div, div_le_iff₀ hK0]
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Real.rpow_add hK0, Real.rpow_one]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← hK]
  exact_mod_cast Nat.card_divisors_le_self _

/-- **Exponential decay of the Fourier coefficients**: for `k ≠ 0`,
`|∫_0^1 e^{−2πikx}E*(x + iy, s) dx| ≤ C|k|^N e^{−πy|k|}` with `C`, `N` depending only on `y` and `s`. -/
theorem norm_fourierCoeff_Estar_le (s : ℂ) {k : ℤ} (hk : k ≠ 0) :
    ‖∫ x in (0 : ℝ)..1, cexp (-(2 * π * Complex.I * k * x)) * Estar (pt x y hy) s‖ ≤
      (√y * Eis.bkR (s - 1 / 2).re (2 * π * y / 2)) * |(k : ℝ)| ^ ⌈1 + |(s - 1 / 2).re|⌉₊ *
        rexp (-(π * y) * |(k : ℝ)|) := by
  have hK1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hk)
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  rw [fourierCoeff_Estar_divisors hy hk s, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_ofNat]
  have hB := (Eis.norm_besselK_le (s - 1 / 2) (2 * π * |(k : ℝ)| * y)).trans
    (mul_le_mul_of_nonneg_left (Eis.bkR_le_exp (r := (s - 1 / 2).re) (x₀ := 2 * π * y)
      (x := 2 * π * |(k : ℝ)| * y) (by positivity)
      (by nlinarith [mul_le_mul_of_nonneg_left hK1 (by positivity : (0 : ℝ) ≤ 2 * π * y)])) (by norm_num))
  have hS := (norm_divSum_le hk (s - 1 / 2)).trans
    (Real.rpow_le_rpow_of_exponent_le hK1 (Nat.le_ceil (1 + |(s - 1 / 2).re|)))
  rw [Real.rpow_natCast] at hS
  have he : rexp (-(2 * π * |(k : ℝ)| * y / 2)) = rexp (-(π * y) * |(k : ℝ)|) := by ring_nf
  rw [he] at hB
  have h0 : 0 ≤ Eis.bkR (s - 1 / 2).re (2 * π * y / 2) := Eis.bkR_nonneg _ _
  calc 2 * √y * ‖Eis.besselK (s - 1 / 2) (2 * π * |(k : ℝ)| * y)‖ *
        ‖∑ d ∈ k.natAbs.divisors, ((|(k : ℝ)| / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1 / 2)‖
      ≤ 2 * √y * (1 / 2 * (rexp (-(π * y) * |(k : ℝ)|) * Eis.bkR (s - 1 / 2).re (2 * π * y / 2))) *
          |(k : ℝ)| ^ ⌈1 + |(s - 1 / 2).re|⌉₊ := by gcongr
    _ = _ := by ring

/-- **The Fourier coefficients of `E*` are summable** over `k ∈ ℤ`, for every `y > 0` and `s`. -/
theorem summable_fourierCoeff_Estar (s : ℂ) :
    Summable fun k : ℤ => ∫ x in (0 : ℝ)..1, cexp (-(2 * π * Complex.I * k * x)) * Estar (pt x y hy) s := by
  set C := √y * Eis.bkR (s - 1 / 2).re (2 * π * y / 2)
  set N := ⌈1 + |(s - 1 / 2).re|⌉₊
  have hg : Summable fun k : ℤ => C * |(k : ℝ)| ^ N * rexp (-(π * y) * |(k : ℝ)|) := by
    have h := (Real.summable_pow_mul_exp_neg_nat_mul N (show 0 < π * y by positivity)).mul_left C
    refine Summable.of_nat_of_neg ?_ ?_
    · refine h.congr fun n => ?_
      simp only [Int.cast_natCast, Nat.abs_cast]
      ring
    · refine h.congr fun n => ?_
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
      ring
  refine hg.of_norm_bounded_eventually ?_
  filter_upwards [eventually_cofinite_ne 0] with k hk
  exact norm_fourierCoeff_Estar_le hy s hk

/-- **The Fourier series of `E*`**: for `y > 0`, every `x` and every `s`,
`E*(x + iy, s) = Σ_{k ∈ ℤ} a_k(y, s)e^{2πikx}` with `a_k(y, s) = ∫_0^1 e^{−2πiku}E*(u + iy, s) du`, from Mathlib's
`has_pointwise_sum_fourier_series_of_summable`. -/
theorem hasSum_fourier_Estar (s : ℂ) (x : ℝ) :
    HasSum (fun k : ℤ => (∫ u in (0 : ℝ)..1, cexp (-(2 * π * Complex.I * k * u)) * Estar (pt u y hy) s) *
      cexp (2 * π * Complex.I * k * x)) (Estar (pt x y hy) s) := by
  have hs : Summable (fourierCoeff (EstarCircle hy s)) := by
    rw [show fourierCoeff (EstarCircle hy s) = _ from funext (fourierCoeff_EstarCircle hy s)]
    exact summable_fourierCoeff_Estar hy s
  have h := has_pointwise_sum_fourier_series_of_summable hs (x : UnitAddCircle)
  rw [EstarCircle_coe] at h
  refine h.congr_fun fun k => ?_
  rw [fourierCoeff_EstarCircle, fourier_coe_apply, smul_eq_mul, Complex.ofReal_one, div_one]

lemma coeff_natAbs (s : ℂ) {k : ℤ} {n : ℕ} (hk : k.natAbs = n + 1) :
    ∫ u in (0 : ℝ)..1, cexp (-(2 * π * Complex.I * k * u)) * Estar (pt u y hy) s =
      2 * (√y : ℂ) * Eis.besselK (s - 1 / 2) (2 * π * ((n + 1 : ℕ) : ℝ) * y) *
        ∑ d ∈ (n + 1).divisors, ((((n + 1 : ℕ) : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1 / 2) := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have e : |(k : ℝ)| = ((n + 1 : ℕ) : ℝ) := by rw [← hk, Nat.cast_natAbs, Int.cast_abs]
  rw [fourierCoeff_Estar_divisors hy hk0 s, e, hk]

/-- **The Fourier expansion of `E*` as a cosine series**, for every `s`:
`E*(x + iy, s) − ∫_0^1 E*(u + iy, s) du = 4√y Σ_{n ≥ 1}(Σ_{d ∣ n}(n/d²)^{s−1/2})K_{s−1/2}(2πny)cos(2πnx)`. -/
theorem hasSum_cos_Estar (s : ℂ) (x : ℝ) :
    HasSum (fun n : ℕ => 4 * (√y : ℂ) * Eis.besselK (s - 1 / 2) (2 * π * ((n + 1 : ℕ) : ℝ) * y) *
        (∑ d ∈ (n + 1).divisors, ((((n + 1 : ℕ) : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1 / 2)) *
          Complex.cos (2 * π * ((n + 1 : ℕ) : ℂ) * x))
      (Estar (pt x y hy) s - ∫ u in (0 : ℝ)..1, Estar (pt u y hy) s) := by
  set f : ℤ → ℂ := fun k => (∫ u in (0 : ℝ)..1, cexp (-(2 * π * Complex.I * k * u)) * Estar (pt u y hy) s) *
      cexp (2 * π * Complex.I * k * x)
  have hf : HasSum f (Estar (pt x y hy) s) := hasSum_fourier_Estar hy s x
  have h := (hasSum_nat_add_iff' 1).2 hf.nat_add_neg
  have h0 : f 0 = ∫ u in (0 : ℝ)..1, Estar (pt u y hy) s := by simp [f]
  rw [Finset.sum_range_one, Nat.cast_zero, neg_zero] at h
  rw [show Estar (pt x y hy) s + f 0 - (f 0 + f 0) = Estar (pt x y hy) s - f 0 by ring, h0] at h
  refine h.congr_fun fun n => ?_
  simp only [f]
  rw [coeff_natAbs hy s (k := ((n + 1 : ℕ) : ℤ)) (n := n) (Int.natAbs_natCast _),
    coeff_natAbs hy s (k := -((n + 1 : ℕ) : ℤ)) (n := n) (by rw [Int.natAbs_neg, Int.natAbs_natCast]), ← mul_add]
  have hc : cexp (2 * π * Complex.I * (((n + 1 : ℕ) : ℤ) : ℂ) * x) +
      cexp (2 * π * Complex.I * ((-((n + 1 : ℕ) : ℤ) : ℤ) : ℂ) * x) =
        2 * Complex.cos (2 * π * ((n + 1 : ℕ) : ℂ) * x) := by
    rw [Complex.two_cos]
    push_cast
    ring_nf
  rw [hc]
  ring

/-- **The Fourier expansion of `E*`**, for `s ≠ 0, ½, 1`:
`E*(x + iy, s) = Λ(2s)y^s + Λ(2s − 1)y^{1−s} + 4√y Σ_{n ≥ 1}(Σ_{d ∣ n}(n/d²)^{s−1/2})K_{s−1/2}(2πny)cos(2πnx)`. -/
theorem hasSum_fourier_Estar_explicit {s : ℂ} (h0 : s ≠ 0) (hh : s ≠ 1 / 2) (h1 : s ≠ 1) (x : ℝ) :
    HasSum (fun n : ℕ => 4 * (√y : ℂ) * Eis.besselK (s - 1 / 2) (2 * π * ((n + 1 : ℕ) : ℝ) * y) *
        (∑ d ∈ (n + 1).divisors, ((((n + 1 : ℕ) : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (s - 1 / 2)) *
          Complex.cos (2 * π * ((n + 1 : ℕ) : ℂ) * x))
      (Estar (pt x y hy) s - (completedRiemannZeta (2 * s) * (y : ℂ) ^ s +
        completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s))) := by
  rw [← constTerm_Estar_all hy h0 hh h1]
  exact hasSum_cos_Estar hy s x

end ModFourier
