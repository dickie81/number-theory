/-
# Kronecker's first limit formula

The value at `s = 1` of the Fourier expansion of the completed Eisenstein series (`ModFourier`), and with it the
Laurent expansion of `E*(z, s)` at its pole `s = 1` in terms of Mathlib's Dedekind `η` (`ModularForm.eta`).
* **`K_{1/2}` is elementary** (`integral_exp_sub_inv_sq`, `integral_bkK_half`, `besselK_half`): with the library's
  `Eis.besselK ν x = ½∫_0^∞ t^{ν−1}e^{−(x/2)(t + 1/t)} dt`, `Eis.besselK (1/2) x = √(π/(2x))e^{−x}` for `x > 0`
  (`t = u²`, then `v = u − 1/u` and the Gaussian integral).
* **The `q`-series of `log η`** (`summable_qd`, `hasSum_divisor_inv`, `log_norm_eta`): for `|q| < 1`,
  `Σ_{n ≥ 1}(Σ_{d ∣ n} 1/d)qⁿ = −Σ_{m ≥ 1} log(1 − qᵐ)` (regrouping `Σ_{m, d} q^{md}/d` along `n = md`), and
  `log|η(z)| = −πy/12 + Re Σ_{m ≥ 1} log(1 − qᵐ)`, `q = e^{2πiz}`.
* **The non-constant part at `s = 1`** (`hasSum_cos_one`, `Estar_sub_constTerm_one`): at `s = 1` the cosine series
  of `ModFourier.hasSum_cos_Estar` is `Σ_{n ≥ 1} 2σ_{−1}(n)e^{−2πny}cos(2πnx) = −2 Re Σ_m log(1 − qᵐ)`, so
  `E*(z, 1) − ∫_0^1 E*(u + iy, 1) du = −2 log|∏_m(1 − qᵐ)|`.
* **Kronecker's first limit formula** (`completedRiemannZeta_two`, `continuous_Estar_sub_constTerm`,
  `tendsto_Estar_sub_pole`, `tendsto_Lambda_sub_pole`, `tendsto_E_sub_pole`): with `Λ(2) = π/6` and
  `Λ(u) − 1/(u − 1) → (γ − log 4π)/2` (Mathlib's `completedRiemannZeta₀_one`),
  `E*(z, s) − 1/(2(s − 1)) → (γ − log 4π)/2 − log(√y|η(z)|²)` as `s → 1` (`s ≠ 1`); for the completed Epstein zeta
  function `Λ_z = 2E*` of `|mz + n|²/y`, `Λ_z(s) − 1/(s − 1) → γ − log 4π − 2log(√y|η(z)|²)`; and for
  `E(z, s) = E*(z, s)/Λ(2s)`, `E(z, s) − (3/π)/(s − 1) → (6/π)((γ − log 4π)/2 − log(√y|η(z)|²)) − (36/π²)Λ'(2)`.
-/
import Mathlib
import ModTruncation

open Complex Real Filter Topology Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace ModKronecker

open ModEisenstein ModContinuation ModFourier

/-! ## `K_{1/2}` -/

lemma sq_sub_inv (u : ℝ) : (u⁻¹ - u⁻¹⁻¹) ^ 2 = (u - u⁻¹) ^ 2 := by
  rw [inv_inv]; ring

/-- `∫_0^∞ e^{−a(u − 1/u)²} du = ½√(π/a)`. -/
lemma integral_exp_sub_inv_sq {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ), rexp (-a * (u - u⁻¹) ^ 2) = √(π / a) / 2 := by
  set φ : ℝ → ℝ := fun u => u - u⁻¹
  set G : ℝ → ℝ := fun u => rexp (-a * (u - u⁻¹) ^ 2)
  have hφ' : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (1 + (u ^ 2)⁻¹) (Ioi 0) u := fun u hu => by
    have h := (hasDerivAt_id' u).fun_sub (hasDerivAt_inv (ne_of_gt hu))
    convert h.hasDerivWithinAt using 1
    ring
  have hinj : InjOn φ (Ioi 0) := by
    intro u hu v hv h
    simp only [φ] at h
    have hu' : (0 : ℝ) < u := hu
    have hv' : (0 : ℝ) < v := hv
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have : u⁻¹ > v⁻¹ := inv_strictAnti₀ hu' h1
      linarith
    · have : v⁻¹ > u⁻¹ := inv_strictAnti₀ hv' h1
      linarith
  have himg : φ '' Ioi 0 = univ := by
    refine eq_univ_of_forall fun v => ?_
    refine ⟨(v + √(v ^ 2 + 4)) / 2, ?_, ?_⟩
    · have h1 : |v| < √(v ^ 2 + 4) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
      have := neg_abs_le v
      show (0 : ℝ) < _
      linarith
    · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ v ^ 2 + 4 by positivity)
      have key : (v + √(v ^ 2 + 4)) / 2 * ((v + √(v ^ 2 + 4)) / 2 - v) = 1 := by nlinarith [hs]
      simp only [φ]
      rw [inv_eq_of_mul_eq_one_right key]
      ring
  have hgauss : ∫ v : ℝ, rexp (-a * v ^ 2) = √(π / a) := integral_gaussian a
  have hchg := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφ' hinj
    (fun v => rexp (-a * v ^ 2))
  rw [himg, setIntegral_univ, hgauss] at hchg
  have hint := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hφ' hinj
    (fun v => rexp (-a * v ^ 2))).1 (by rw [himg, integrableOn_univ]; exact integrable_exp_neg_mul_sq ha)
  have habs : ∀ u ∈ Ioi (0 : ℝ), |1 + (u ^ 2)⁻¹| • rexp (-a * φ u ^ 2) = G u + (u ^ 2)⁻¹ * G u := by
    intro u _
    rw [abs_of_pos (by positivity), smul_eq_mul]
    simp only [G, φ]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi habs] at hchg
  have hint' : IntegrableOn (fun u => G u + (u ^ 2)⁻¹ * G u) (Ioi 0) :=
    hint.congr_fun habs measurableSet_Ioi
  have hcont : ContinuousOn G (Ioi 0) := by
    intro u hu
    have : u ≠ 0 := ne_of_gt hu
    exact (by fun_prop : ContinuousAt (fun u : ℝ => rexp (-a * (u - u⁻¹) ^ 2)) u).continuousWithinAt
  have hcont2 : ContinuousOn (fun u => (u ^ 2)⁻¹ * G u) (Ioi 0) := by
    intro u hu
    have : u ≠ 0 := ne_of_gt hu
    have : u ^ 2 ≠ 0 := pow_ne_zero 2 this
    exact ((by fun_prop : ContinuousAt (fun u : ℝ => (u ^ 2)⁻¹) u).mul
      (hcont.continuousAt (Ioi_mem_nhds hu))).continuousWithinAt
  have hG : IntegrableOn G (Ioi 0) := by
    refine Integrable.mono' hint' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have h1 : 0 ≤ G u := (Real.exp_pos _).le
    have h2 : 0 ≤ (u ^ 2)⁻¹ * G u := by positivity
    rw [Real.norm_of_nonneg h1]; linarith
  have hG2 : IntegrableOn (fun u => (u ^ 2)⁻¹ * G u) (Ioi 0) := by
    refine Integrable.mono' hint' (hcont2.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have h1 : 0 ≤ G u := (Real.exp_pos _).le
    have h2 : 0 ≤ (u ^ 2)⁻¹ * G u := by positivity
    rw [Real.norm_of_nonneg h2]; linarith
  have hsym : ∫ u in Ioi (0 : ℝ), (u ^ 2)⁻¹ * G u = ∫ u in Ioi (0 : ℝ), G u := by
    have h := integral_comp_rpow_Ioi G (p := -1) (by norm_num)
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    simp only [smul_eq_mul, G]
    rw [show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg_one, Real.rpow_neg hu'.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_sub_inv u]
    norm_num
  rw [integral_add hG hG2, hsym] at hchg
  linarith

/-- `∫_0^∞ t^{−1/2}e^{−(x/2)(t + 1/t)} dt = e^{−x}√(π/(x/2))`, by `t = u²` and `integral_exp_sub_inv_sq`. -/
lemma integral_bkK_half {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) * Eis.bkK x t = rexp (-x) * √(π / (x / 2)) := by
  have h := integral_comp_rpow_Ioi (fun t => t ^ (-(1 / 2) : ℝ) * Eis.bkK x t) (p := 2) (by norm_num)
  rw [← h]
  have e : ∀ u ∈ Ioi (0 : ℝ), (|(2 : ℝ)| * u ^ ((2 : ℝ) - 1)) • ((u ^ (2 : ℝ)) ^ (-(1 / 2) : ℝ) *
      Eis.bkK x (u ^ (2 : ℝ))) = 2 * rexp (-x) * rexp (-(x / 2) * (u - u⁻¹) ^ 2) := by
    intro u hu
    have hu' : (0 : ℝ) < u := hu
    rw [smul_eq_mul, ← Real.rpow_mul hu'.le, show (2 : ℝ) * (-(1 / 2)) = -1 by norm_num, Real.rpow_neg_one,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, Eis.bkK, abs_two]
    have hu0 : u ≠ 0 := hu'.ne'
    have : -(x / 2) * (u ^ 2 + (u ^ 2)⁻¹) = -x + -(x / 2) * (u - u⁻¹) ^ 2 := by
      field_simp
      ring
    rw [this, Real.exp_add]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_exp_sub_inv_sq (by positivity : 0 < x / 2)]
  ring

/-- **`K_{1/2}` is elementary**: `Eis.besselK (1/2) x = √(π/(2x))e^{−x}` for `x > 0` (the classical
`K_{1/2}(x) = √(π/(2x))e^{−x}`; `Eis.besselK ν x = ½∫_0^∞ t^{ν−1}e^{−(x/2)(t + 1/t)} dt`). -/
theorem besselK_half {x : ℝ} (hx : 0 < x) :
    Eis.besselK (1 / 2) x = ((√(π / (2 * x)) * rexp (-x) : ℝ) : ℂ) := by
  have hm : mellin (fun t => (Eis.bkK x t : ℂ)) (1 / 2) =
      ((∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) * Eis.bkK x t : ℝ) : ℂ) := by
    rw [mellin, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    rw [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_cpow ht'.le]
    push_cast
    ring_nf
  rw [Eis.besselK, hm, integral_bkK_half hx]
  have e : √(π / (x / 2)) = 2 * √(π / (2 * x)) := by
    rw [show π / (x / 2) = 2 ^ 2 * (π / (2 * x)) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [e]
  push_cast
  ring_nf

/-! ## The `q`-series of `log η` -/

/-- The double series `Σ_{m, d ≥ 1} q^{md}/d` is absolutely summable for `|q| < 1`. -/
lemma summable_qd {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun c : ℕ+ × ℕ+ => q ^ ((c.1 : ℕ) * c.2) / ((c.2 : ℕ) : ℂ) := by
  have h := summable_prod_mul_pow (𝕜 := ℝ) 0 (r := ‖q‖) (by rwa [Real.norm_of_nonneg (norm_nonneg q)])
  refine Summable.of_norm_bounded h fun c => ?_
  rw [norm_div, norm_pow, pow_zero, one_mul]
  have h1 : (1 : ℝ) ≤ ‖((c.2 : ℕ) : ℂ)‖ := by
    rw [Complex.norm_natCast]; exact_mod_cast c.2.pos
  exact div_le_self (by positivity) h1

/-- **The `q`-series of `−log ∏(1 − qᵐ)`**: for `|q| < 1`,
`Σ_{n ≥ 1}(Σ_{d ∣ n} 1/d)qⁿ = −Σ_{m ≥ 1} log(1 − qᵐ)`. -/
theorem hasSum_divisor_inv {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (∑ d ∈ (n + 1).divisors, 1 / (d : ℂ)) * q ^ (n + 1))
      (-∑' m : ℕ, Complex.log (1 - q ^ (m + 1))) := by
  have hs := (summable_qd hq).hasSum
  set S := ∑' c : ℕ+ × ℕ+, q ^ ((c.1 : ℕ) * c.2) / ((c.2 : ℕ) : ℂ)
  -- fibres over `m`: `Σ_d q^{md}/d = −log(1 − qᵐ)`
  have hm : ∀ m : ℕ+, HasSum (fun d : ℕ+ => q ^ ((m : ℕ) * d) / ((d : ℕ) : ℂ)) (-Complex.log (1 - q ^ (m : ℕ))) := by
    intro m
    have hqm : ‖q ^ (m : ℕ)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq m.ne_zero
    rw [← Equiv.pnatEquivNat.symm.hasSum_iff]
    convert Complex.hasSum_taylorSeries_neg_log' hqm using 1
    funext n
    simp [Function.comp, pow_mul]
  have hrow := hs.prod_fiberwise hm
  -- fibres over `n = md`
  set F : (ℕ+ × ℕ+) → ℂ := fun c => q ^ ((c.1 : ℕ) * c.2) / ((c.2 : ℕ) : ℂ)
  have hsig : HasSum (F ∘ sigmaAntidiagonalEquivProd) S := (Equiv.hasSum_iff sigmaAntidiagonalEquivProd).2 hs
  have hn := hsig.sigma (fun n => hasSum_fintype (fun x => (F ∘ sigmaAntidiagonalEquivProd) ⟨n, x⟩))
  have hval : ∀ n : ℕ+, ∑ x : (n : ℕ).divisorsAntidiagonal, (F ∘ sigmaAntidiagonalEquivProd) ⟨n, x⟩ =
        (∑ d ∈ (n : ℕ).divisors, 1 / (d : ℂ)) * q ^ (n : ℕ) := by
    intro n
    simp only [F, Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, Equiv.coe_fn_mk,
      PNat.mk_coe]
    rw [Finset.sum_mul, ← Nat.sum_divisorsAntidiagonal' (fun a b => 1 / (b : ℂ) * q ^ (n : ℕ)),
      ← Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun x => 1 / (x.2 : ℂ) * q ^ (n : ℕ)),
      Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [(Nat.mem_divisorsAntidiagonal.mp x.2).1]
    ring
  simp_rw [hval] at hn
  rw [← Equiv.pnatEquivNat.symm.hasSum_iff] at hn hrow
  convert hn using 1
  · funext n; simp [Function.comp]
  · rw [← hrow.tsum_eq, ← tsum_neg]
    simp [Function.comp]

/-- `Σ_{m ≥ 1} log(1 − qᵐ)` for `q = e^{2πiz}`. -/
def logProd (z : ℂ) : ℂ := ∑' m : ℕ, Complex.log (1 - cexp (2 * π * Complex.I * z) ^ (m + 1))

/-- **`log|η(z)| = −πy/12 + Re Σ_{m ≥ 1} log(1 − qᵐ)`**, `q = e^{2πiz}`, for Mathlib's `ModularForm.eta`. -/
theorem log_norm_eta (z : ℍ) : Real.log ‖ModularForm.eta z‖ = -(π * z.im) / 12 + (logProd z).re := by
  set q := cexp (2 * π * Complex.I * z)
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have hne : ∀ m : ℕ, 1 - q ^ (m + 1) ≠ 0 := fun m => by
    have h := ModularForm.one_sub_eta_q_ne_zero m (z := (z : ℂ)) z.im_pos
    rwa [ModularForm.eta_q_eq_pow] at h
  have hsum : Summable fun m : ℕ => Complex.log (1 - q ^ (m + 1)) := by
    have h := Complex.summable_log_one_add_of_summable
      ((summable_geometric_of_norm_lt_one hq).mul_left q).neg
    refine h.congr fun m => ?_
    rw [pow_succ']; ring_nf
  have hprod : ∏' n : ℕ, (1 - ModularForm.eta_q n z) = cexp (logProd z) := by
    rw [logProd, Complex.cexp_tsum_eq_tprod hne hsum]
    simp_rw [ModularForm.eta_q_eq_pow]
    rfl
  have hqp : ‖Function.Periodic.qParam 24 (z : ℂ)‖ = rexp (-(π * z.im) / 12) := by
    rw [Function.Periodic.qParam, Complex.norm_exp]
    congr 1
    simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num
    ring
  rw [ModularForm.eta, norm_mul, hprod, hqp, Complex.norm_exp,
    Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]

/-! ## The non-constant part of `E*` at `s = 1` -/

variable {y : ℝ} (hy : 0 < y)

include hy in
lemma term_one (x : ℝ) (n : ℕ) :
    4 * (√y : ℂ) * Eis.besselK (1 - 1 / 2) (2 * π * ((n + 1 : ℕ) : ℝ) * y) *
        (∑ d ∈ (n + 1).divisors, ((((n + 1 : ℕ) : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ ((1 : ℂ) - 1 / 2)) *
          Complex.cos (2 * π * ((n + 1 : ℕ) : ℂ) * x) =
      ((2 * (∑ d ∈ (n + 1).divisors, 1 / (d : ℝ)) *
        (rexp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * Real.cos (2 * π * ((n + 1 : ℕ) : ℝ) * x)) : ℝ) : ℂ) := by
  set N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN : 0 < N := by positivity
  have hh : (1 : ℂ) - 1 / 2 = ((1 / 2 : ℝ) : ℂ) := by push_cast; norm_num
  rw [hh, show (((1 / 2 : ℝ) : ℂ)) = 1 / 2 by push_cast; ring, besselK_half (by positivity)]
  have hd : ∀ d ∈ (n + 1).divisors, (((N / (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = ((√N / d : ℝ) : ℂ) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hd0.le]
  rw [Finset.sum_congr rfl hd]
  have hs : √(π / (2 * (2 * π * N * y))) = 1 / (2 * √N * √y) := by
    rw [show π / (2 * (2 * π * N * y)) = (1 / (2 * √N * √y)) ^ 2 by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hN.le, Real.sq_sqrt hy.le]
      field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [hs]
  have hc : Complex.cos (2 * π * ((n + 1 : ℕ) : ℂ) * x) = ((Real.cos (2 * π * N * x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos]; simp only [N]; push_cast; ring_nf
  rw [hc]
  have hNs : (0 : ℝ) < √N := Real.sqrt_pos.2 hN
  have hys : (0 : ℝ) < √y := Real.sqrt_pos.2 hy
  push_cast
  have hsum : ∑ d ∈ (n + 1).divisors, (√N : ℂ) / d = √N * ∑ d ∈ (n + 1).divisors, 1 / (d : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have : (√N : ℂ) ≠ 0 := by exact_mod_cast hNs.ne'
  have : (√y : ℂ) ≠ 0 := by exact_mod_cast hys.ne'
  rw [hsum]
  field_simp
  ring

/-- **The cosine series at `s = 1`**: `E*(x + iy, 1) − ∫_0^1 E*(u + iy, 1) du =
Σ_{n ≥ 1} 2σ_{−1}(n)e^{−2πny}cos(2πnx)`, from `ModFourier.hasSum_cos_Estar` and `besselK_half`. -/
theorem hasSum_cos_one (x : ℝ) :
    HasSum (fun n : ℕ => ((2 * (∑ d ∈ (n + 1).divisors, 1 / (d : ℝ)) *
        (rexp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * Real.cos (2 * π * ((n + 1 : ℕ) : ℝ) * x)) : ℝ) : ℂ))
      (Estar (pt x y hy) 1 - ∫ u in (0 : ℝ)..1, Estar (pt u y hy) 1) :=
  (hasSum_cos_Estar hy 1 x).congr_fun fun n => (term_one hy x n).symm

/-- **`E*(z, 1)` minus its constant term** is `−2 Re Σ_{m ≥ 1} log(1 − qᵐ) = −2 log|∏_m(1 − qᵐ)|`. -/
theorem Estar_sub_constTerm_one (x : ℝ) :
    Estar (pt x y hy) 1 - ∫ u in (0 : ℝ)..1, Estar (pt u y hy) 1 = ((-2 * (logProd (pt x y hy)).re : ℝ) : ℂ) := by
  set z := pt x y hy
  set q := cexp (2 * π * Complex.I * z)
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have h := Complex.hasSum_re (hasSum_divisor_inv hq)
  have hre : ∀ n : ℕ, ((∑ d ∈ (n + 1).divisors, 1 / (d : ℂ)) * q ^ (n + 1)).re =
      (∑ d ∈ (n + 1).divisors, 1 / (d : ℝ)) *
        (rexp (-(2 * π * ((n + 1 : ℕ) : ℝ) * y)) * Real.cos (2 * π * ((n + 1 : ℕ) : ℝ) * x)) := by
    intro n
    have e1 : (∑ d ∈ (n + 1).divisors, 1 / (d : ℂ)) = ((∑ d ∈ (n + 1).divisors, 1 / (d : ℝ) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [e1, Complex.re_ofReal_mul, ← Complex.exp_nat_mul, Complex.exp_re]
    congr 2
    · simp [z, pt]; ring
    · simp [z, pt]; ring_nf
  simp_rw [hre] at h
  have h2 := Complex.hasSum_ofReal.2 (h.mul_left 2)
  refine (hasSum_cos_one hy x).unique (h2.congr_fun fun n => ?_) |>.trans ?_
  · push_cast; ring
  · show ((2 * (-(logProd z)).re : ℝ) : ℂ) = _
    rw [Complex.neg_re]
    push_cast
    ring

/-! ## Kronecker's first limit formula -/

/-- `Λ(2) = π/6` (`Λ(2) = π^{−1}Γ(1)ζ(2)`). -/
theorem completedRiemannZeta_two : completedRiemannZeta 2 = π / 6 := by
  have h := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
  have hG : Gammaℝ 2 = 1 / π := by
    rw [Gammaℝ_def, show -(2 : ℂ) / 2 = -1 by norm_num, show (2 : ℂ) / 2 = 1 by norm_num, Complex.Gamma_one,
      Complex.cpow_neg_one]
    ring
  rw [riemannZeta_two, hG] at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at h
  linear_combination -h / 6

/-- **`s ↦ E*(z, s) − ∫_0^1 E*(u + iy, s) du` is entire** (continuous): it is `(Λ₀_z(s) − M(s))/2` with both
`Λ₀_z` (Mathlib's `WeakFEPair.Λ₀`) and `M` (`ModFourier.differentiable_mellin_avgF`) entire. -/
theorem continuous_Estar_sub_constTerm (x : ℝ) :
    Continuous fun s => Estar (pt x y hy) s - ∫ u in (0 : ℝ)..1, Estar (pt u y hy) s := by
  have e : (fun s => Estar (pt x y hy) s - ∫ u in (0 : ℝ)..1, Estar (pt u y hy) s) =
      fun s => ((thetaFEPair (pt x y hy)).Λ₀ s - mellin (avgF hy fun _ => 1) s) / 2 := by
    funext s
    rw [integral_Estar hy, Estar, Lambda, Λ_thetaFEPair]
    ring
  rw [e]
  exact (((thetaFEPair _).differentiable_Λ₀.continuous).sub
    (differentiable_mellin_avgF hy _ measurable_const (by simp)).continuous).div_const 2

/-- The Kronecker limit function `−log(√y|η(z)|²)`, `y = Im z`, with Mathlib's Dedekind `η`. -/
def kron (z : ℂ) : ℝ := -Real.log (√z.im * ‖ModularForm.eta z‖ ^ 2)

lemma kron_eq (z : ℍ) : kron z = -(Real.log z.im) / 2 + π * z.im / 6 - 2 * (logProd z).re := by
  have hη : ‖ModularForm.eta z‖ ≠ 0 := norm_ne_zero_iff.2 (ModularForm.eta_ne_zero z.im_pos)
  rw [kron, UpperHalfPlane.coe_im, Real.log_mul (Real.sqrt_pos.2 z.im_pos).ne' (pow_ne_zero 2 hη),
    Real.log_pow, log_norm_eta, Real.log_sqrt z.im_pos.le]
  push_cast
  ring

include hy in
lemma tendsto_slope_cpow : Tendsto (fun s : ℂ => ((y : ℂ) ^ (1 - s) - 1) / (2 * (s - 1))) (𝓝[≠] 1)
    (𝓝 (-(Real.log y : ℂ) / 2)) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hd : HasDerivAt (fun s : ℂ => (y : ℂ) ^ (1 - s)) ((y : ℂ) ^ (1 - 1 : ℂ) * Complex.log y * (-1)) 1 :=
    ((hasDerivAt_id 1).const_sub 1).const_cpow (Or.inl hy0)
  have h := (hasDerivAt_iff_tendsto_slope.1 hd).div_const 2
  rw [sub_self, Complex.cpow_zero, ← Complex.ofReal_log hy.le] at h
  convert h using 2
  · simp only [slope, sub_self, Complex.cpow_zero, vsub_eq_sub, smul_eq_mul]
    rw [div_eq_mul_inv _ (2 * _), mul_inv]
    ring
  · ring

/-- **Kronecker's first limit formula** for `x + iy`: `E*(x + iy, s) − 1/(2(s − 1)) → (γ − log 4π)/2 + kron`. -/
theorem tendsto_Estar_pt (x : ℝ) :
    Tendsto (fun s => Estar (pt x y hy) s - 1 / (2 * (s - 1))) (𝓝[≠] 1)
      (𝓝 (((Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 + kron (pt x y hy) : ℝ) : ℂ)) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  set F := fun s => Estar (pt x y hy) s - ∫ u in (0 : ℝ)..1, Estar (pt u y hy) s
  -- the four pieces
  have hA : Tendsto F (𝓝[≠] 1) (𝓝 (((-2 * (logProd (pt x y hy)).re : ℝ) : ℂ))) := by
    rw [← Estar_sub_constTerm_one hy x]
    exact ((continuous_Estar_sub_constTerm hy x).tendsto 1).mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun s : ℂ => completedRiemannZeta (2 * s) * (y : ℂ) ^ s) (𝓝[≠] 1)
      (𝓝 (π / 6 * y)) := by
    have h1 : ContinuousAt (fun s : ℂ => completedRiemannZeta (2 * s)) 1 := by
      have := (differentiableAt_completedZeta (s := 2 * 1) (by norm_num) (by norm_num)).continuousAt
      exact this.comp (continuous_const.mul continuous_id).continuousAt
    have h2 : ContinuousAt (fun s : ℂ => (y : ℂ) ^ s) 1 :=
      (continuous_id.const_cpow (Or.inl hy0)).continuousAt
    have h3 : ContinuousAt (fun s : ℂ => completedRiemannZeta (2 * s) * (y : ℂ) ^ s) 1 := h1.mul h2
    have := h3.tendsto.mono_left (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
    simpa [completedRiemannZeta_two] using this
  have hC : Tendsto (fun s : ℂ => (completedRiemannZeta₀ (2 * s - 1) - 1 / (2 * s - 1)) * (y : ℂ) ^ (1 - s))
      (𝓝[≠] 1) (𝓝 ((Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 : ℝ)) := by
    have h1 : ContinuousAt (fun s : ℂ => (completedRiemannZeta₀ (2 * s - 1) - 1 / (2 * s - 1)) *
        (y : ℂ) ^ (1 - s)) 1 := by
      refine ContinuousAt.mul (ContinuousAt.sub ?_ ?_) ?_
      · exact differentiable_completedZeta₀.continuous.continuousAt.comp (by fun_prop)
      · exact continuousAt_const.div (by fun_prop) (by norm_num)
      · exact ((continuous_const.sub continuous_id).const_cpow (Or.inl hy0)).continuousAt
    have := h1.tendsto.mono_left (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)))
    convert this using 2
    rw [show (2 : ℂ) * 1 - 1 = 1 by norm_num, completedRiemannZeta₀_one, sub_self, Complex.cpow_zero,
      show (4 : ℂ) * π = ((4 * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log (by positivity)]
    push_cast
    ring
  have hD := tendsto_slope_cpow hy
  have hsum := ((hA.add hB).add hC).add hD
  -- the identity off `s = 0, ½, 1`
  have hev : (fun s => Estar (pt x y hy) s - 1 / (2 * (s - 1))) =ᶠ[𝓝[≠] 1] fun s =>
      F s + completedRiemannZeta (2 * s) * (y : ℂ) ^ s +
        (completedRiemannZeta₀ (2 * s - 1) - 1 / (2 * s - 1)) * (y : ℂ) ^ (1 - s) +
          ((y : ℂ) ^ (1 - s) - 1) / (2 * (s - 1)) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)),
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 1 / 2))] with s h1 h0 hh
    have h1' : s - 1 ≠ 0 := sub_ne_zero.2 h1
    have hh' : 2 * s - 1 ≠ 0 := fun h => hh (by linear_combination h / 2)
    have hc := constTerm_Estar_all hy h0 hh h1
    simp only [F]
    rw [hc, completedRiemannZeta_eq (2 * s - 1)]
    have : (1 : ℂ) - (2 * s - 1) = -(2 * (s - 1)) := by ring
    rw [this]
    field_simp
    ring
  convert hsum.congr' hev.symm using 2
  rw [kron_eq (pt x y hy), pt_im]
  push_cast
  ring

/-- **Kronecker's first limit formula**: for `z ∈ ℍ`, `y = Im z`,
`E*(z, s) − 1/(2(s − 1)) → (γ − log 4π)/2 − log(√y|η(z)|²)` as `s → 1`, `s ≠ 1`. -/
theorem tendsto_Estar_sub_pole (z : ℍ) :
    Tendsto (fun s => Estar z s - 1 / (2 * (s - 1))) (𝓝[≠] 1)
      (𝓝 (((Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 + kron z : ℝ) : ℂ)) := by
  have h := tendsto_Estar_pt z.im_pos z.re
  rwa [ModTruncation.pt_re_im] at h

/-- **Kronecker's first limit formula for the Epstein zeta function** of `Q_z(m, n) = |mz + n|²/y`: its
completion `Λ_z(s) = π^{−s}Γ(s)Σ'Q_z^{−s}` (`ModContinuation.Lambda_eq_epstein`, `Λ_z = 2E*`) satisfies
`Λ_z(s) − 1/(s − 1) → γ − log 4π − 2log(√y|η(z)|²)` as `s → 1`. -/
theorem tendsto_Lambda_sub_pole (z : ℍ) :
    Tendsto (fun s => Lambda z s - 1 / (s - 1)) (𝓝[≠] 1)
      (𝓝 ((Real.eulerMascheroniConstant - Real.log (4 * π) + 2 * kron z : ℝ) : ℂ)) := by
  have h := (tendsto_Estar_sub_pole z).const_mul 2
  convert h using 1
  · funext s
    rw [Estar]
    rw [div_eq_mul_inv _ (2 * _), mul_inv]
    ring
  · push_cast
    ring_nf

/-- **Kronecker's first limit formula for `E(z, s) = E*(z, s)/Λ(2s)`**: `E(z, s) − (3/π)/(s − 1) →
(6/π)((γ − log 4π)/2 − log(√y|η(z)|²)) − (36/π²)Λ'(2)` as `s → 1`, with `Λ(2) = π/6`. -/
theorem tendsto_E_sub_pole (z : ℍ) :
    Tendsto (fun s => Estar z s / completedRiemannZeta (2 * s) - 3 / π / (s - 1)) (𝓝[≠] 1)
      (𝓝 (6 / π * (((Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 + kron z : ℝ) : ℂ) -
        36 / (π : ℂ) ^ 2 * deriv completedRiemannZeta 2)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set h : ℂ → ℂ := fun s => (completedRiemannZeta (2 * s))⁻¹
  have hΛ : HasDerivAt (fun s : ℂ => completedRiemannZeta (2 * s)) (deriv completedRiemannZeta 2 * 2) 1 := by
    have h1 : HasDerivAt completedRiemannZeta (deriv completedRiemannZeta 2) (2 * 1) := by
      rw [mul_one]; exact (differentiableAt_completedZeta (s := 2) (by norm_num) (by norm_num)).hasDerivAt
    have h2 : HasDerivAt (fun s : ℂ => 2 * s) 2 1 := by simpa using (hasDerivAt_id (1 : ℂ)).const_mul 2
    exact h1.comp 1 h2
  have hΛ1 : completedRiemannZeta (2 * 1) ≠ 0 := by
    rw [mul_one, completedRiemannZeta_two]; exact div_ne_zero hπ (by norm_num)
  have hd := hΛ.inv hΛ1
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hd).const_mul (1 / 2)
  have hcont : Tendsto h (𝓝[≠] 1) (𝓝 (h 1)) :=
    (hΛ.continuousAt.inv₀ hΛ1).tendsto.mono_left nhdsWithin_le_nhds
  have hmain := ((tendsto_Estar_sub_pole z).mul hcont).add hslope
  convert hmain using 1
  · funext s
    simp only [h, slope, vsub_eq_sub, smul_eq_mul, Pi.inv_apply, mul_one, completedRiemannZeta_two]
    rw [div_eq_mul_inv _ (2 * _), mul_inv]
    field_simp
    ring
  · simp only [h, mul_one, completedRiemannZeta_two]
    field_simp
    ring_nf

end ModKronecker
