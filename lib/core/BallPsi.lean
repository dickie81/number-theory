/-
# The Hadamard kernel from the primes: `K_H` through Chebyshev's `ψ`

Plain statement. Let `K_H(r) = Σ_ρ r^{ρ − ½}/(ρ(1 − ρ))` (`BallHadamard.kerH`), `c₀ = 2 + γ − log 4π` and
`A(u) = (1/2π)∫ H_u(r)·Re ψ_Γ(¼ + ir/2) dr` with `H_u(r) = (cos(ru) − cosh(u/2))/(r² + ¼)` (`archH`), where `ψ_Γ` is
the digamma function. For `x ≥ 1`, with `u = log x`,
`K_H(x) = cosh(u/2)·c₀ + sinh(u/2)·(log π − 2u) + A(u) + √x·Σ_{n ≤ x} Λ(n)/n − ψ(x)/√x` (`kerH_explicit`), where `ψ`
is Chebyshev's function (Mathlib's `Chebyshev.psi`). No hypothesis.
* So Mathlib's `RiemannHypothesis` holds if and only if the kernel `kerHψ` on the right, which is built from `Λ`, `γ`,
  `π` and `Γ` and does not mention the zeros, is positive-definite on the positive rationals (`rh_iff_posDef_psi`).
* In a realization of `K_H` (`BallLattice.Realization`), for `1 ≤ n ≤ m`,
  `⟨w_n, w_m⟩ = ((m + n)/2)c₀ + ((m − n)/2)(log π − 2log(m/n)) + √(mn)·A(log(m/n)) + m·Σ_{k ≤ m/n} Λ(k)/k − n·ψ(m/n)`
  (`gram_explicit`). Its prime part is `Σ_{kn ≤ m} Λ(k)(m − kn)/k`, where for an elliptic curve over `𝔽_q` the Gram
  matrix of the Frobenius points has the point counts (`ManinHasse.gram_orbit_card`).
* If every `w_{k+1}` keeps distance at least `‖w_1‖` from the span of `w_1, …, w_k`, then `w_1` is a shortest nonzero
  vector of the subgroup that the orbit generates, which is then a lattice (`orbit_lattice`, from
  `norm_sq_ge_of_dist`).

* The weight `cos(tu)/(t² + ¼)` of `K_H` has poles at `t = ±i/2`, inside the strip of the library's explicit formula
  (`WeilForm.weilExplicit_zeta`). Subtracting `cosh(u/2)/(t² + ¼)` removes them: `H_u` is entire (`Hu`, by `dslope`)
  and in the test class (`stripTest_Hu`), with `H_u(±i/2) = −u·sinh(u/2)`. The subtracted part sums over the zeros to
  `cosh(u/2)·c₀` by Hadamard's identity (`WeilForm.hadamard_zeta`).
* The transform of `H_u` is `½(e^{−|u+v|/2} + e^{−|u−v|/2}) − cosh(u/2)e^{−|v|/2}` (`gh_Hu`), from
  `∫ cos(rw)/(r² + ¼) dr = 2πe^{−|w|/2}` (`integral_cos_div`, by Fourier inversion of `e^{−|x|/2}`). It vanishes for
  `|v| ≥ u`, so only the `n ≤ x` enter the prime sum.

The archimedean term is not computed here. Numerically it is
`A(u) = γ·sinh(u/2) + sinh(u/2)·log(4sinh(u/2)) − cosh(u/2)·log cosh(u/2) − (u/2)e^{−u/2}`, and then the formula is
`K_H(x) = √x·(Σ_{n ≤ x} Λ(n)(1/n − 1/x) − log x + 1 + γ − log(2π)/x + Σ_{k ≥ 1} x^{−2k−1}/(2k(2k + 1)))`, the one that
Perron's integral with the kernel `1/(s(s − 1))` gives. `docs/ball-conjecture.md` computes the Gram matrices of the
orbit from it.
-/
import Mathlib
import BallHadamard

open Real Complex Finset Filter Topology MeasureTheory Set WeilForm WeilTest WeilStrip ComplexConjugate
open scoped FourierTransform InnerProductSpace

noncomputable section

namespace BallPsi

open BallKernel BallLattice BallHadamard

/-! ## The Cauchy kernel `1/(r² + ¼)` and its transform `2πe^{−|w|/2}` -/

/-- `𝓕(e^{−|x|/2})(ξ) = 1/(¼ + 4π²ξ²)`. -/
theorem fourier_exp_neg_abs (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((Real.exp (-|x| / 2) : ℝ) : ℂ)) ξ = ((1 / (1 / 4 + 4 * π ^ 2 * ξ ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set a : ℂ := 1 / 2 - 2 * π * ξ * I with hadef
  set b : ℂ := -(1 / 2) - 2 * π * ξ * I with hbdef
  have ha : 0 < a.re := by simp [a]
  have hb : b.re < 0 := by simp [b]
  have hL : EqOn (fun v : ℝ => cexp (↑(-2 * π * v * ξ) * I) • ((Real.exp (-|v| / 2) : ℝ) : ℂ))
      (fun v : ℝ => cexp (a * v)) (Iic 0) := by
    intro v hv
    simp only
    rw [abs_of_nonpos (mem_Iic.1 hv), smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hR : EqOn (fun v : ℝ => cexp (↑(-2 * π * v * ξ) * I) • ((Real.exp (-|v| / 2) : ℝ) : ℂ))
      (fun v : ℝ => cexp (b * v)) (Ioi 0) := by
    intro v hv
    simp only
    rw [abs_of_pos (mem_Ioi.1 hv), smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hiL : IntegrableOn (fun v : ℝ => cexp (↑(-2 * π * v * ξ) * I) • ((Real.exp (-|v| / 2) : ℝ) : ℂ)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic ha 0).congr_fun hL.symm measurableSet_Iic
  have hiR : IntegrableOn (fun v : ℝ => cexp (↑(-2 * π * v * ξ) * I) • ((Real.exp (-|v| / 2) : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hb 0).congr_fun hR.symm measurableSet_Ioi
  rw [← intervalIntegral.integral_Iic_add_Ioi hiL hiR, setIntegral_congr_fun measurableSet_Iic hL,
    setIntegral_congr_fun measurableSet_Ioi hR, integral_exp_mul_complex_Iic ha,
    integral_exp_mul_complex_Ioi hb]
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  have hab : a * b = -((1 / 4 + 4 * π ^ 2 * ξ ^ 2 : ℝ) : ℂ) := by
    rw [hadef, hbdef]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hq : ((1 / 4 + 4 * π ^ 2 * ξ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show (1 : ℂ) / a + -1 / b = (b - a) / (a * b) by field_simp; ring, hab]
  rw [show b - a = -1 by rw [hadef, hbdef]; ring]
  push_cast
  field_simp

/-- **`∫ cos(rw)/(r² + ¼) dr = 2πe^{−|w|/2}`**, by Fourier inversion of `e^{−|x|/2}`. -/
theorem integral_cos_div (w : ℝ) :
    ∫ r : ℝ, Real.cos (r * w) / (r ^ 2 + 1 / 4) = 2 * π * Real.exp (-|w| / 2) := by
  set F : ℝ → ℂ := fun x => ((Real.exp (-|x| / 2) : ℝ) : ℂ) with hF
  have hFi : Integrable F := by
    have h := integrable_exp_neg_abs (c := 1 / 2) (by norm_num)
    refine (h.congr (Eventually.of_forall fun x => ?_)).ofReal
    simp only; congr 1; ring
  have hFc : Continuous F := by fun_prop
  have hFF : 𝓕 F = fun ξ => ((1 / (1 / 4 + 4 * π ^ 2 * ξ ^ 2) : ℝ) : ℂ) := funext fourier_exp_neg_abs
  have hP : Integrable fun ξ : ℝ => 1 / (1 / 4 + 4 * π ^ 2 * ξ ^ 2) := by
    have h := (integrable_inv_one_add_mul_sq (b := 4 * π) (by positivity)).const_mul 4
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    have : (0 : ℝ) < 1 + (4 * π * ξ) ^ 2 := by positivity
    field_simp
  have hFFi : Integrable (𝓕 F) := by rw [hFF]; exact hP.ofReal
  have h := congrFun (Continuous.fourierInv_fourier_eq hFc hFi hFFi) w
  rw [Real.fourierInv_eq', hFF] at h
  simp only [RCLike.inner_apply, conj_trivial] at h
  have hI : Integrable (fun v : ℝ => cexp (↑(2 * π * (w * v)) * I) •
      ((1 / (1 / 4 + 4 * π ^ 2 * v ^ 2) : ℝ) : ℂ)) := by
    refine hP.ofReal.bdd_mul (c := 1)
      (by fun_prop : Continuous fun v : ℝ => cexp (↑(2 * π * (w * v)) * I)).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hre := congrArg Complex.re h
  have hre2 : (∫ v : ℝ, cexp (↑(2 * π * (w * v)) * I) • ((1 / (1 / 4 + 4 * π ^ 2 * v ^ 2) : ℝ) : ℂ)).re
      = ∫ v : ℝ, (cexp (↑(2 * π * (w * v)) * I) • ((1 / (1 / 4 + 4 * π ^ 2 * v ^ 2) : ℝ) : ℂ)).re :=
    (integral_re hI).symm
  rw [hre2] at hre
  simp only [hF, Complex.ofReal_re] at hre
  have e1 : (fun v : ℝ => (cexp (↑(2 * π * (w * v)) * I) • ((1 / (1 / 4 + 4 * π ^ 2 * v ^ 2) : ℝ) : ℂ)).re) =
      fun v => (fun r => Real.cos (r * w) / (r ^ 2 + 1 / 4)) (2 * π * v) := by
    funext v
    rw [smul_eq_mul, mul_comm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    simp only
    rw [show 2 * π * (w * v) = 2 * π * v * w by ring]
    field_simp
    ring
  rw [e1, Measure.integral_comp_mul_left (fun r => Real.cos (r * w) / (r ^ 2 + 1 / 4)) (2 * π),
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), smul_eq_mul] at hre
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rwa [inv_mul_eq_iff_eq_mul₀ hpi.ne'] at hre

/-! ## The test function `H_u(t) = (cos(tu) − cosh(u/2))/(t² + ¼)` -/

/-- `t ↦ cos(tu)`. -/
def cosu (u : ℝ) (t : ℂ) : ℂ := Complex.cos (t * u)

lemma differentiable_cosu (u : ℝ) : Differentiable ℂ (cosu u) := by
  unfold cosu; fun_prop

lemma half_ne : -(I / 2) ≠ I / 2 := fun h => by
  have := congrArg Complex.im h
  simp at this
  norm_num at this

lemma cosu_half (u : ℝ) : cosu u (I / 2) = ((Real.cosh (u / 2) : ℝ) : ℂ) := by
  unfold cosu
  rw [show I / 2 * (u : ℂ) = ((u / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.cos_mul_I, Complex.ofReal_cosh]

lemma cosu_neg_half (u : ℝ) : cosu u (-(I / 2)) = ((Real.cosh (u / 2) : ℝ) : ℂ) := by
  rw [← cosu_half u]
  unfold cosu
  rw [neg_mul, Complex.cos_neg]

lemma hasDerivAt_cosu (u : ℝ) (t : ℂ) : HasDerivAt (cosu u) (-Complex.sin (t * u) * u) t :=
  (hasDerivAt_mul_const (u : ℂ)).ccos

/-- **The test function** `H_u(t) = (cos(tu) − cosh(u/2))/(t² + ¼)`, with its removable singularities at `t = ±i/2`
filled in by `dslope`. -/
def Hu (u : ℝ) : ℂ → ℂ := dslope (dslope (cosu u) (I / 2)) (-(I / 2))

lemma differentiable_Hu (u : ℝ) : Differentiable ℂ (Hu u) := by
  have h1 : DifferentiableOn ℂ (dslope (cosu u) (I / 2)) univ :=
    (Complex.differentiableOn_dslope univ_mem).2 (differentiable_cosu u).differentiableOn
  have h2 : DifferentiableOn ℂ (Hu u) univ := (Complex.differentiableOn_dslope univ_mem).2 h1
  exact differentiableOn_univ.1 h2

lemma dslope_cosu_neg_half (u : ℝ) : dslope (cosu u) (I / 2) (-(I / 2)) = 0 := by
  rw [dslope_of_ne _ half_ne, slope_def_field, cosu_half, cosu_neg_half, sub_self, zero_div]

lemma Hu_eq (u : ℝ) {t : ℂ} (h1 : t ≠ I / 2) (h2 : t ≠ -(I / 2)) :
    Hu u t = (Complex.cos (t * u) - ((Real.cosh (u / 2) : ℝ) : ℂ)) / (t ^ 2 + 1 / 4) := by
  unfold Hu
  rw [dslope_of_ne _ h2, slope_def_field, dslope_cosu_neg_half, sub_zero, dslope_of_ne _ h1, slope_def_field,
    cosu_half, div_div]
  unfold cosu
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

lemma Hu_neg_half (u : ℝ) : Hu u (-(I / 2)) = -((u * Real.sinh (u / 2) : ℝ) : ℂ) := by
  unfold Hu
  rw [dslope_same]
  have hne : -(I / 2) - I / 2 ≠ 0 := sub_ne_zero.2 half_ne
  have hd : HasDerivAt (fun t => (cosu u t - cosu u (I / 2)) / (t - I / 2))
      (((-Complex.sin (-(I / 2) * u) * u) * (-(I / 2) - I / 2) - (cosu u (-(I / 2)) - cosu u (I / 2)) * 1) /
        (-(I / 2) - I / 2) ^ 2) (-(I / 2)) :=
    ((hasDerivAt_cosu u _).sub_const _).div ((hasDerivAt_id _).sub_const _) hne
  have heq : dslope (cosu u) (I / 2) =ᶠ[𝓝 (-(I / 2))] fun t => (cosu u t - cosu u (I / 2)) / (t - I / 2) := by
    filter_upwards [isOpen_ne.mem_nhds half_ne] with t ht
    rw [dslope_of_ne _ ht, slope_def_field]
  rw [(hd.congr_of_eventuallyEq heq).deriv, cosu_half, cosu_neg_half, sub_self, zero_mul, sub_zero]
  rw [show -(I / 2) * (u : ℂ) = -(((u / 2 : ℝ) : ℂ) * I) by push_cast; ring, Complex.sin_neg, Complex.sin_mul_I]
  have hI : (-(I / 2) - I / 2) = -I := by ring
  have hI2 : (-I) ^ 2 = -1 := by rw [neg_sq, Complex.I_sq]
  rw [hI, hI2]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma Hu_half (u : ℝ) : Hu u (I / 2) = -((u * Real.sinh (u / 2) : ℝ) : ℂ) := by
  unfold Hu
  rw [dslope_of_ne _ half_ne.symm, slope_def_field, dslope_cosu_neg_half, sub_zero, dslope_same,
    (hasDerivAt_cosu u _).deriv]
  rw [show I / 2 * (u : ℂ) = ((u / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.sin_mul_I,
    show I / 2 - -(I / 2) = I by ring]
  push_cast
  field_simp

lemma Hu_even (u : ℝ) (t : ℂ) : Hu u (-t) = Hu u t := by
  by_cases h1 : t = I / 2
  · rw [h1, Hu_neg_half, Hu_half]
  by_cases h2 : t = -(I / 2)
  · rw [h2, neg_neg, Hu_neg_half, Hu_half]
  have h1' : -t ≠ I / 2 := fun h => h2 (by rw [← h, neg_neg])
  have h2' : -t ≠ -(I / 2) := fun h => h1 (neg_inj.1 h)
  rw [Hu_eq u h1' h2', Hu_eq u h1 h2, neg_mul, Complex.cos_neg, neg_sq]

/-- `H_u` on the real line. -/
def HuR (u r : ℝ) : ℝ := (Real.cos (r * u) - Real.cosh (u / 2)) / (r ^ 2 + 1 / 4)

lemma ofReal_ne_half (r : ℝ) : (r : ℂ) ≠ I / 2 := fun h => by
  have := congrArg Complex.im h
  simp at this

lemma ofReal_ne_neg_half (r : ℝ) : (r : ℂ) ≠ -(I / 2) := fun h => by
  have := congrArg Complex.im h
  simp at this

lemma Hu_real (u r : ℝ) : Hu u r = HuR u r := by
  rw [Hu_eq u (ofReal_ne_half r) (ofReal_ne_neg_half r), HuR]
  push_cast
  ring

lemma norm_cos_le (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := Complex.two_cos (x := z)
  have e : Complex.cos z = (cexp (z * I) + cexp (-z * I)) / 2 := by rw [← h]; ring
  rw [e, norm_div, Complex.norm_two]
  have h1 : ‖cexp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (by simp; exact neg_le_abs _)
  have h2 : ‖cexp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (by simp; exact le_abs_self _)
  have := norm_add_le (cexp (z * I)) (cexp (-z * I))
  linarith

/-- **`H_u` is in the test class** of `WeilForm.weilExplicit_zeta`: entire, and `O(1/(1 + (Re t)²))` on the strip. -/
theorem stripTest_Hu (u : ℝ) : ∃ C, StripTest (Hu u) C := by
  have hK : IsCompact (reProdIm (Icc (-1 : ℝ) 1) (Icc (-1) 1)) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (differentiable_Hu u).continuous.continuousOn
  set B := Real.exp |u| + Real.cosh (u / 2) with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨max (2 * max M 0) (8 * B), ⟨(differentiable_Hu u).differentiableOn, fun t ht => ?_⟩⟩
  have hti : -1 ≤ t.im ∧ t.im ≤ 1 := ht
  have hpos : 0 < 1 + t.re ^ 2 := by positivity
  rcases le_or_gt |t.re| 1 with hre | hre
  · have htK : t ∈ reProdIm (Icc (-1 : ℝ) 1) (Icc (-1) 1) := ⟨abs_le.1 hre, hti⟩
    have h1 := hM t htK
    have h2 : t.re ^ 2 ≤ 1 := by nlinarith [abs_nonneg t.re, sq_abs t.re]
    rw [le_div_iff₀ hpos]
    have h3 : ‖Hu u t‖ * (1 + t.re ^ 2) ≤ max M 0 * 2 :=
      mul_le_mul (h1.trans (le_max_left _ _)) (by linarith) hpos.le (le_max_right _ _)
    linarith [le_max_left (2 * max M 0) (8 * B)]
  · have h1 : t ≠ I / 2 := fun h => by rw [h] at hre; norm_num at hre
    have h2 : t ≠ -(I / 2) := fun h => by rw [h] at hre; norm_num at hre
    rw [Hu_eq u h1 h2, norm_div]
    have hnum : ‖Complex.cos (t * u) - ((Real.cosh (u / 2) : ℝ) : ℂ)‖ ≤ B := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos _).le]
      have hc := norm_cos_le (t * u)
      have him : |(t * (u : ℂ)).im| ≤ |u| := by
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul]
        have : |t.im| ≤ 1 := abs_le.2 hti
        nlinarith [abs_nonneg u, abs_nonneg t.im]
      have := Real.exp_le_exp.2 him
      linarith
    have hre2 : 1 ≤ t.re ^ 2 := by nlinarith [sq_abs t.re, abs_nonneg t.re]
    have hden : (1 + t.re ^ 2) / 8 ≤ ‖t ^ 2 + 1 / 4‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      have e : (t ^ 2 + 1 / 4).re = t.re ^ 2 - t.im ^ 2 + 1 / 4 := by
        simp [sq, Complex.mul_re]
      rw [e]
      have : t.im ^ 2 ≤ 1 := by nlinarith
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    have hd0 : 0 < ‖t ^ 2 + 1 / 4‖ := lt_of_lt_of_le (by positivity) hden
    rw [div_le_div_iff₀ hd0 hpos]
    calc ‖Complex.cos (t * u) - ((Real.cosh (u / 2) : ℝ) : ℂ)‖ * (1 + t.re ^ 2)
        ≤ B * (8 * ‖t ^ 2 + 1 / 4‖) := mul_le_mul hnum (by linarith) hpos.le hB0
      _ ≤ max (2 * max M 0) (8 * B) * ‖t ^ 2 + 1 / 4‖ := by
          rw [← mul_assoc, mul_comm B 8]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hd0.le

/-! ## The transform of `H_u` -/

lemma integrable_cauchy : Integrable fun r : ℝ => 1 / (r ^ 2 + 1 / 4) := by
  have h := (integrable_inv_one_add_mul_sq (b := 2) (by norm_num)).const_mul 4
  refine h.congr (Eventually.of_forall fun r => ?_)
  have : (0 : ℝ) < 1 + (2 * r) ^ 2 := by positivity
  field_simp
  ring

lemma integrable_cos_div (w : ℝ) : Integrable fun r : ℝ => Real.cos (r * w) / (r ^ 2 + 1 / 4) := by
  have hc : Continuous fun r : ℝ => Real.cos (r * w) / (r ^ 2 + 1 / 4) :=
    (by fun_prop : Continuous fun r : ℝ => Real.cos (r * w)).div (by fun_prop) fun r => by positivity
  refine integrable_cauchy.mono' hc.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  have h0 : (0 : ℝ) < r ^ 2 + 1 / 4 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos h0]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) h0.le

/-- **The transform of `H_u`**: `ĝ(v) = ½(e^{−|u+v|/2} + e^{−|u−v|/2}) − cosh(u/2)e^{−|v|/2}`. -/
theorem gh_Hu (u v : ℝ) :
    gh (HuR u) v = (Real.exp (-|u + v| / 2) + Real.exp (-|u - v| / 2)) / 2 -
      Real.cosh (u / 2) * Real.exp (-|v| / 2) := by
  unfold gh HuR
  have e : (fun r : ℝ => (Real.cos (r * u) - Real.cosh (u / 2)) / (r ^ 2 + 1 / 4) * Real.cos (r * v)) =
      fun r => (Real.cos (r * (u + v)) / (r ^ 2 + 1 / 4) + Real.cos (r * (u - v)) / (r ^ 2 + 1 / 4)) / 2 -
        Real.cosh (u / 2) * (Real.cos (r * v) / (r ^ 2 + 1 / 4)) := by
    funext r
    rw [show r * (u + v) = r * u + r * v by ring, show r * (u - v) = r * u - r * v by ring, Real.cos_add,
      Real.cos_sub]
    have : (0 : ℝ) < r ^ 2 + 1 / 4 := by positivity
    field_simp
    ring
  have hA := integrable_cos_div (u + v)
  have hB := integrable_cos_div (u - v)
  have hAB : Integrable fun r : ℝ =>
      (Real.cos (r * (u + v)) / (r ^ 2 + 1 / 4) + Real.cos (r * (u - v)) / (r ^ 2 + 1 / 4)) / 2 :=
    (hA.add hB).div_const 2
  have hC : Integrable fun r : ℝ => Real.cosh (u / 2) * (Real.cos (r * v) / (r ^ 2 + 1 / 4)) :=
    (integrable_cos_div v).const_mul _
  rw [e, integral_sub hAB hC, integral_div, integral_add hA hB, integral_const_mul, integral_cos_div,
    integral_cos_div, integral_cos_div]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  field_simp

/-! ## The explicit formula -/

/-- The archimedean term `A(u) = (1/2π)∫ H_u(r)·Re ψ(¼ + ir/2) dr`. -/
def archH (u : ℝ) : ℝ := 1 / (2 * π) * ∫ r, HuR u r * psiRe r

/-- Weil's explicit formula for `H_u` (`WeilForm.weilExplicit_zeta`). -/
lemma weil_Hu (u : ℝ) : WeilExplicit zetaZeroFamily (Hu u) (HuR u) := by
  obtain ⟨C, hC⟩ := stripTest_Hu u
  exact weilExplicit_zeta hC (Hu_even u) (Hu_real u)

lemma ord_ne_half (q : ZIdx) : (zetaZeroFamily q - 1 / 2) / I ≠ I / 2 := fun h => by
  have h0 := (nontrivial_zZF q).re_pos
  have e : zetaZeroFamily q = 0 := by
    have := congrArg (· * I) h
    simp only [div_mul_cancel₀ _ Complex.I_ne_zero] at this
    linear_combination this + Complex.I_sq / 2
  rw [e] at h0
  simp at h0

lemma ord_ne_neg_half (q : ZIdx) : (zetaZeroFamily q - 1 / 2) / I ≠ -(I / 2) := fun h => by
  have h1 := (nontrivial_zZF q).re_lt_one
  have e : zetaZeroFamily q = 1 := by
    have := congrArg (· * I) h
    simp only [div_mul_cancel₀ _ Complex.I_ne_zero] at this
    linear_combination this - Complex.I_sq / 2
  rw [e] at h1
  simp at h1

lemma rho_ne (q : ZIdx) : zetaZeroFamily q * (1 - zetaZeroFamily q) ≠ 0 := by
  have h0 := (nontrivial_zZF q).re_pos
  have h1 := (nontrivial_zZF q).re_lt_one
  refine mul_ne_zero (fun h => by rw [h] at h0; simp at h0) (fun h => ?_)
  rw [← sub_eq_zero.1 h] at h1
  simp at h1

/-- On a zero, `H_u + cosh(u/2)/(ρ(1 − ρ))` is the term `cosh((ρ − ½)u)/(ρ(1 − ρ))` of `K_H`. -/
lemma Hu_term (u : ℝ) (q : ZIdx) :
    Hu u ((zetaZeroFamily q - 1 / 2) / I) + ((Real.cosh (u / 2) : ℝ) : ℂ) *
      (1 / (zetaZeroFamily q * (1 - zetaZeroFamily q))) =
    (cexp ((zetaZeroFamily q - 1 / 2) * u) + cexp ((zetaZeroFamily q - 1 / 2) * ((-u : ℝ) : ℂ))) / 2 /
      (zetaZeroFamily q * (1 - zetaZeroFamily q)) := by
  rw [Hu_eq u (ord_ne_half q) (ord_ne_neg_half q)]
  have hq := rho_ne q
  have e1 : ((zetaZeroFamily q - 1 / 2) / I) ^ 2 + 1 / 4 = zetaZeroFamily q * (1 - zetaZeroFamily q) := by
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have e2 : Complex.cos ((zetaZeroFamily q - 1 / 2) / I * u) =
      (cexp ((zetaZeroFamily q - 1 / 2) * u) + cexp ((zetaZeroFamily q - 1 / 2) * ((-u : ℝ) : ℂ))) / 2 := by
    rw [Complex.cos]
    congr 2
    · congr 1; field_simp
    · congr 1; push_cast; field_simp
  rw [e1, e2]
  field_simp
  ring

/-- The terms of `K_H(x)` and of `K_H(1/x)`, averaged. -/
lemma hasSum_kerH (x : ℝ) :
    HasSum (fun q : ZIdx => (cexp ((zetaZeroFamily q - 1 / 2) * (Real.log x : ℝ)) +
      cexp ((zetaZeroFamily q - 1 / 2) * ((-Real.log x : ℝ) : ℂ))) / 2 /
        (zetaZeroFamily q * (1 - zetaZeroFamily q))) (kerH x) := by
  have hs : ∀ L : ℝ, Summable fun q : ZIdx => cexp ((zetaZeroFamily q - 1 / 2) * L) /
      (zetaZeroFamily q * (1 - zetaZeroFamily q)) := fun L => by
    refine (summable_kerH (L / 2)).congr fun q => ?_
    rw [hG_poleP, one_div_mul_eq_div]
    congr 2
    unfold poleP
    push_cast
    ring
  have h1 := (hs (Real.log x)).hasSum
  have h2 := (hs (-Real.log x)).hasSum
  have e1 : ∑' q : ZIdx, cexp ((zetaZeroFamily q - 1 / 2) * (Real.log x : ℝ)) /
      (zetaZeroFamily q * (1 - zetaZeroFamily q)) = kerH x := rfl
  have e2 : ∑' q : ZIdx, cexp ((zetaZeroFamily q - 1 / 2) * ((-Real.log x : ℝ) : ℂ)) /
      (zetaZeroFamily q * (1 - zetaZeroFamily q)) = kerH x := by
    rw [← kerH_inv x]
    unfold kerH
    rw [Real.log_inv]
  rw [e1] at h1
  rw [e2] at h2
  have h := (h1.add h2).div_const 2
  rw [show (kerH x + kerH x) / 2 = kerH x by ring] at h
  refine h.congr_fun fun q => ?_
  ring

/-- `√y = e^{(log y)/2}`. -/
lemma exp_log_half {y : ℝ} (hy : 0 < y) : Real.exp (Real.log y / 2) = Real.sqrt y := by
  have h : Real.exp (Real.log y / 2) ^ 2 = y := by
    rw [sq, ← Real.exp_add, show Real.log y / 2 + Real.log y / 2 = Real.log y by ring, Real.exp_log hy]
  rw [← h, Real.sqrt_sq (Real.exp_pos _).le, h]

/-- **The prime sum is finite**: only `n ≤ x` contribute, each `−(√x/2)Λ(n)(1/n − 1/x)`. -/
lemma prime_sum {x : ℝ} (hx : 1 ≤ x) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh (HuR (Real.log x)) (Real.log n) =
      -(Real.sqrt x / 2) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (1 / n - 1 / x) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hS : Real.exp (L / 2) = Real.sqrt x := exp_log_half hx0
  have hSpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) fun n hn => ?_, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.1 hn).1
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).1 (Finset.mem_Ioc.1 hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    set l := Real.log n with hl
    have hl0 : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hn1)
    have hlL : l ≤ L := Real.log_le_log hn0 hnx
    have hs : Real.exp (l / 2) = Real.sqrt n := exp_log_half hn0
    have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    have hsn : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
    rw [gh_Hu, abs_of_nonneg (by linarith : 0 ≤ L + l), abs_of_nonneg (by linarith : 0 ≤ L - l),
      abs_of_nonneg hl0, Real.cosh_eq]
    have ea : Real.exp (-(L + l) / 2) = (Real.sqrt x)⁻¹ * (Real.sqrt n)⁻¹ := by
      rw [show -(L + l) / 2 = -(L / 2) + -(l / 2) by ring, Real.exp_add, Real.exp_neg, Real.exp_neg, hS, hs]
    have eb : Real.exp (-(L - l) / 2) = (Real.sqrt x)⁻¹ * Real.sqrt n := by
      rw [show -(L - l) / 2 = -(L / 2) + l / 2 by ring, Real.exp_add, Real.exp_neg, hS, hs]
    have ec : Real.exp (-l / 2) = (Real.sqrt n)⁻¹ := by rw [show -l / 2 = -(l / 2) by ring, Real.exp_neg, hs]
    have ed : Real.exp (-(L / 2)) = (Real.sqrt x)⁻¹ := by rw [Real.exp_neg, hS]
    rw [ea, eb, ec, ed, hS, show (1 : ℝ) / n - 1 / x = 1 / Real.sqrt n ^ 2 - 1 / Real.sqrt x ^ 2 by
      rw [hsn, hsq]]
    field_simp
    ring
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; simp
    · have hn : ⌊x⌋₊ < n := by
        by_contra hle
        exact hn (Finset.mem_Ioc.2 ⟨hpos, not_lt.1 hle⟩)
      have hxn : x < n := (Nat.floor_lt hx0.le).1 hn
      have hn0 : (0 : ℝ) < n := by linarith
      set l := Real.log n with hl
      have hlL : L < l := Real.log_lt_log hx0 hxn
      have hs : Real.exp (l / 2) = Real.sqrt n := exp_log_half hn0
      rw [gh_Hu, abs_of_nonneg (by linarith : 0 ≤ L + l), abs_of_neg (by linarith : L - l < 0),
        abs_of_nonneg (by linarith : 0 ≤ l), Real.cosh_eq]
      have ea : Real.exp (-(L + l) / 2) = (Real.sqrt x)⁻¹ * (Real.sqrt n)⁻¹ := by
        rw [show -(L + l) / 2 = -(L / 2) + -(l / 2) by ring, Real.exp_add, Real.exp_neg, Real.exp_neg, hS, hs]
      have eb : Real.exp (-(-(L - l)) / 2) = Real.sqrt x * (Real.sqrt n)⁻¹ := by
        rw [show -(-(L - l)) / 2 = L / 2 + -(l / 2) by ring, Real.exp_add, Real.exp_neg, hS, hs]
      have ec : Real.exp (-l / 2) = (Real.sqrt n)⁻¹ := by rw [show -l / 2 = -(l / 2) by ring, Real.exp_neg, hs]
      have ed : Real.exp (-(L / 2)) = (Real.sqrt x)⁻¹ := by rw [Real.exp_neg, hS]
      rw [ea, eb, ec, ed, hS]
      ring

/-- **The explicit formula for `K_H`, through Chebyshev's `ψ`**: for `x ≥ 1`, with `u = log x`,
`K_H(x) = cosh(u/2)(2 + γ − log 4π) + sinh(u/2)(log π − 2u) + A(u) + √x·Σ_{n ≤ x} Λ(n)/n − ψ(x)/√x`. -/
theorem kerH_explicit {x : ℝ} (hx : 1 ≤ x) :
    kerH x = ((Real.cosh (Real.log x / 2) * (2 + eulerMascheroniConstant - Real.log (4 * π)) +
      Real.sinh (Real.log x / 2) * (Real.log π - 2 * Real.log x) + archH (Real.log x) +
      Real.sqrt x * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n -
      Chebyshev.psi x / Real.sqrt x : ℝ) : ℂ) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hW := (weil_Hu L).2
  have hH := hadamard_zeta.mul_left ((Real.cosh (L / 2) : ℝ) : ℂ)
  have hsum := hW.add hH
  have hK := hasSum_kerH x
  have e : (fun q : ZIdx => Hu L ((zetaZeroFamily q - 1 / 2) / I) + ((Real.cosh (L / 2) : ℝ) : ℂ) *
      (1 / (zetaZeroFamily q * (1 - zetaZeroFamily q)))) = fun q : ZIdx =>
      (cexp ((zetaZeroFamily q - 1 / 2) * (L : ℝ)) + cexp ((zetaZeroFamily q - 1 / 2) * ((-L : ℝ) : ℂ))) / 2 /
        (zetaZeroFamily q * (1 - zetaZeroFamily q)) := funext fun q => Hu_term L q
  rw [e] at hsum
  have hS : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hSpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsplit : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (1 / n - 1 / x) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / n - Chebyshev.psi x / x := by
    rw [Chebyshev.psi, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hE : Real.exp (L / 2) = Real.sqrt x := exp_log_half hx0
  have hE' : Real.exp (-(L / 2)) = (Real.sqrt x)⁻¹ := by rw [Real.exp_neg, hE]
  rw [hK.unique hsum, Hu_half, Hu_neg_half, prime_sum hx, gh_Hu, add_zero, sub_zero, abs_of_nonneg hL0,
    Real.cosh_eq, hsplit, Real.sinh_eq, show Chebyshev.psi x / x = Chebyshev.psi x / Real.sqrt x ^ 2 by rw [hS]]
  simp only [abs_zero, neg_zero, zero_div, Real.exp_zero, mul_one, neg_div]
  rw [hE, hE']
  unfold archH
  have hSc : ((Real.sqrt x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hSpos.ne'
  have hpic : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-! ## The Riemann hypothesis from the primes alone -/

/-- **The Hadamard kernel built from the primes**: with `y = max(x, 1/x)` and `u = log y`,
`cosh(u/2)(2 + γ − log 4π) + sinh(u/2)(log π − 2u) + A(u) + √y·Σ_{n ≤ y} Λ(n)/n − ψ(y)/√y`. -/
def kerHψ (x : ℝ) : ℂ :=
  ((Real.cosh (Real.log (max x x⁻¹) / 2) * (2 + eulerMascheroniConstant - Real.log (4 * π)) +
    Real.sinh (Real.log (max x x⁻¹) / 2) * (Real.log π - 2 * Real.log (max x x⁻¹)) +
    archH (Real.log (max x x⁻¹)) +
    Real.sqrt (max x x⁻¹) * ∑ n ∈ Finset.Ioc 0 ⌊max x x⁻¹⌋₊, ArithmeticFunction.vonMangoldt n / n -
    Chebyshev.psi (max x x⁻¹) / Real.sqrt (max x x⁻¹) : ℝ) : ℂ)

lemma kerH_eq_kerHψ {x : ℝ} (hx : 0 < x) : kerH x = kerHψ x := by
  unfold kerHψ
  rcases le_total 1 x with h | h
  · rw [max_eq_left ((inv_le_one_of_one_le₀ h).trans h)]
    exact kerH_explicit h
  · have h' : 1 ≤ x⁻¹ := (one_le_inv₀ hx).2 h
    rw [max_eq_right (h.trans h'), ← kerH_inv x]
    exact kerH_explicit h'

lemma posDefQ_congr {k k' : ℝ → ℂ} (h : ∀ x : ℝ, 0 < x → k x = k' x) : PosDefQ k ↔ PosDefQ k' := by
  unfold PosDefQ
  refine forall_congr' fun S => forall_congr' fun c => forall_congr' fun hS => ?_
  have e : ∑ a ∈ S, ∑ b ∈ S, c a * conj (c b) * k ((a : ℝ) / b) =
      ∑ a ∈ S, ∑ b ∈ S, c a * conj (c b) * k' ((a : ℝ) / b) :=
    Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => by
      rw [h _ (div_pos (by exact_mod_cast hS a ha) (by exact_mod_cast hS b hb))]
  rw [e]

/-- **The Riemann hypothesis from the primes**: Mathlib's `RiemannHypothesis` holds if and only if the kernel `kerHψ`,
built from `Λ`, `γ`, `π` and the archimedean term, is positive-definite on the positive rationals. The zeros of `ζ`
do not appear in it. -/
theorem rh_iff_posDef_psi : RiemannHypothesis ↔ PosDefQ kerHψ :=
  rh_iff_posDefH.trans (posDefQ_congr fun _ hx => kerH_eq_kerHψ hx)

/-! ## The Gram matrix of the orbit -/

/-- **The Gram matrix of the orbit, through `ψ`**: in a realization of `K_H`, for `1 ≤ n ≤ m`,
`⟨w_n, w_m⟩ = ((m + n)/2)(2 + γ − log 4π) + ((m − n)/2)(log π − 2log(m/n)) + √(mn)·A(log(m/n))
  + m·Σ_{k ≤ m/n} Λ(k)/k − n·ψ(m/n)`.
Its prime part is `Σ_{kn ≤ m} Λ(k)(m − kn)/k`, where for an elliptic curve the Gram matrix of the Frobenius points has
the point counts (`ManinHasse.gram_orbit_card`). -/
theorem gram_explicit (R : Realization kerH) {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m) :
    ⟪R.w (n : ℚ), R.w (m : ℚ)⟫_ℂ = ((((m : ℝ) + n) / 2 * (2 + eulerMascheroniConstant - Real.log (4 * π)) +
      ((m : ℝ) - n) / 2 * (Real.log π - 2 * Real.log ((m : ℝ) / n)) +
      Real.sqrt ((m : ℝ) * n) * archH (Real.log ((m : ℝ) / n)) +
      m * ∑ k ∈ Finset.Ioc 0 ⌊(m : ℝ) / n⌋₊, ArithmeticFunction.vonMangoldt k / k -
      n * Chebyshev.psi ((m : ℝ) / n) : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hn0 (by exact_mod_cast hnm)
  have hx : 1 ≤ (m : ℝ) / n := (one_le_div hn0).2 (by exact_mod_cast hnm)
  have hg := R.gram (m : ℚ) (n : ℚ) (by exact_mod_cast hm0) (by exact_mod_cast hn0)
  push_cast at hg
  rw [hg, kerH_explicit hx]
  set a := Real.sqrt m with ha
  set b := Real.sqrt n with hb
  have ha0 : 0 < a := Real.sqrt_pos.2 hm0
  have hb0 : 0 < b := Real.sqrt_pos.2 hn0
  have hma : (m : ℝ) = a ^ 2 := (Real.sq_sqrt hm0.le).symm
  have hnb : (n : ℝ) = b ^ 2 := (Real.sq_sqrt hn0.le).symm
  have hsx : Real.sqrt ((m : ℝ) / n) = a / b := Real.sqrt_div' _ hn0.le
  have hsmn : Real.sqrt ((m : ℝ) * n) = a * b := Real.sqrt_mul hm0.le _
  have hE : Real.exp (Real.log ((m : ℝ) / n) / 2) = a / b := by
    rw [exp_log_half (by positivity), hsx]
  have hE' : Real.exp (-(Real.log ((m : ℝ) / n) / 2)) = b / a := by
    rw [Real.exp_neg, hE, inv_div]
  rw [Real.cosh_eq, Real.sinh_eq, hE, hE', hsx, hsmn]
  have hpsi : Chebyshev.psi ((m : ℝ) / n) / (a / b) = Chebyshev.psi ((m : ℝ) / n) * (b / a) := by
    rw [div_div_eq_mul_div, mul_div_assoc]
  rw [hpsi]
  set P := Chebyshev.psi ((m : ℝ) / n)
  set Q := ∑ k ∈ Finset.Ioc 0 ⌊(m : ℝ) / n⌋₊, ArithmeticFunction.vonMangoldt k / k
  rw [hma, hnb]
  have ha' : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hb' : ((b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  push_cast
  field_simp

/-! ## When the orbit spans a lattice -/

/-- **A Gram–Schmidt bound gives a lattice**: if every `v_k` keeps squared distance at least `δ` from the span of
`v_0, …, v_{k−1}`, then every integer combination of the `v_j` with a nonzero coefficient has squared norm at least
`δ`. So the subgroup they generate is discrete when `δ > 0`. -/
theorem norm_sq_ge_of_dist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : ℕ → E) {δ : ℝ}
    (h : ∀ (k : ℕ) (c : ℕ → ℂ), δ ≤ ‖v k - ∑ j ∈ Finset.range k, c j • v j‖ ^ 2)
    (a : ℕ → ℤ) {N : ℕ} (ha : ∃ j < N, a j ≠ 0) :
    δ ≤ ‖∑ j ∈ Finset.range N, (a j : ℂ) • v j‖ ^ 2 := by
  set S := (Finset.range N).filter fun j => a j ≠ 0 with hS
  have hne : S.Nonempty := by
    obtain ⟨j, hj, hj0⟩ := ha
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hj0⟩⟩
  set k := S.max' hne with hk
  have hkS : k ∈ S := S.max'_mem hne
  have hkN : k < N := Finset.mem_range.1 (Finset.mem_filter.1 hkS).1
  have hak : a k ≠ 0 := (Finset.mem_filter.1 hkS).2
  have hzero : ∀ j < N, k < j → a j = 0 := fun j hj hkj => by
    by_contra hj0
    have : j ≤ k := S.le_max' j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hj0⟩)
    omega
  have hsub : ∑ j ∈ Finset.range N, (a j : ℂ) • v j = ∑ j ∈ Finset.range (k + 1), (a j : ℂ) • v j := by
    refine (Finset.sum_subset (fun j hj => Finset.mem_range.2 (by have := Finset.mem_range.1 hj; omega))
      fun j hj hj' => ?_).symm
    have hjN := Finset.mem_range.1 hj
    have hkj : k < j := by
      by_contra hle
      exact hj' (Finset.mem_range.2 (by omega))
    rw [hzero j hjN hkj]
    simp
  have hak' : (a k : ℂ) ≠ 0 := by exact_mod_cast hak
  set c : ℕ → ℂ := fun j => -((a j : ℂ) / a k) with hc
  have hdecomp : ∑ j ∈ Finset.range (k + 1), (a j : ℂ) • v j =
      (a k : ℂ) • (v k - ∑ j ∈ Finset.range k, c j • v j) := by
    rw [Finset.sum_range_succ, smul_sub, Finset.smul_sum]
    have e : ∀ j, (a k : ℂ) • (c j • v j) = -((a j : ℂ) • v j) := fun j => by
      rw [smul_smul, hc]
      simp only
      rw [mul_neg, mul_div_cancel₀ _ hak', neg_smul]
    simp only [e, Finset.sum_neg_distrib, sub_neg_eq_add]
    abel
  rw [hsub, hdecomp, norm_smul, mul_pow]
  have h1 : (1 : ℝ) ≤ ‖(a k : ℂ)‖ ^ 2 := by
    have : (1 : ℝ) ≤ |(a k : ℝ)| := by exact_mod_cast Int.one_le_abs hak
    rw [show ((a k : ℤ) : ℂ) = ((a k : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg (a k : ℝ)]
  have h2 := h k c
  have h3 := sq_nonneg ‖v k - ∑ j ∈ Finset.range k, c j • v j‖
  nlinarith

/-- **The orbit of `K_H` spans a lattice, if the Gram–Schmidt bound holds**: if in a realization every `w_{k+1}` keeps
distance at least `‖w_1‖` from the span of `w_1, …, w_k`, then `w_1` is a shortest nonzero vector of the subgroup that
the orbit `w_1, w_2, …` generates. -/
theorem orbit_lattice (R : Realization kerH)
    (h : ∀ (k : ℕ) (c : ℕ → ℂ),
      ‖R.w 1‖ ≤ ‖R.w ((k : ℚ) + 1) - ∑ j ∈ Finset.range k, c j • R.w ((j : ℚ) + 1)‖)
    (a : ℕ → ℤ) {N : ℕ} (ha : ∃ j < N, a j ≠ 0) :
    ‖R.w 1‖ ≤ ‖∑ j ∈ Finset.range N, (a j : ℂ) • R.w ((j : ℚ) + 1)‖ := by
  have h' := norm_sq_ge_of_dist (fun j : ℕ => R.w ((j : ℚ) + 1)) (δ := ‖R.w 1‖ ^ 2)
    (fun k c => pow_le_pow_left₀ (norm_nonneg _) (h k c) 2) a ha
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h'

end BallPsi

#print axioms BallPsi.kerH_explicit
#print axioms BallPsi.rh_iff_posDef_psi
#print axioms BallPsi.gram_explicit
#print axioms BallPsi.norm_sq_ge_of_dist
#print axioms BallPsi.orbit_lattice
