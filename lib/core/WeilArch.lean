import Mathlib
import DigammaGauss
import WeilFourier

/-! # Zhu's Lemma 2.5: the archimedean term in frequency form (`ArchBridge`) -/

namespace WeilArch

open Real Finset MeasureTheory Set WeilTailB WeilPlanch WeilModes WeilFourier

noncomputable def K (u : ℝ) : ℝ := Real.exp (u / 2) / Real.sinh u

/-- Real part of the digamma at `1/4 + it/2`, shifted by its value at `1/4`. -/
noncomputable def D (t : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - (Complex.digamma (1 / 4)).re

lemma K_pos {u : ℝ} (hu : 0 < u) : 0 < K u := by
  unfold K; exact div_pos (Real.exp_pos _) (Real.sinh_pos_iff.mpr hu)

lemma kern_id (t u : ℝ) (hu : 0 < u) :
    2 * (Real.exp (-(2 * u) / 4) * (1 - Real.cos (t * (2 * u) / 2)) / (1 - Real.exp (-(2 * u))))
      = (1 - Real.cos (t * u)) * K u := by
  unfold K
  rw [Real.sinh_eq, show t * (2 * u) / 2 = t * u by ring]
  have ha := Real.exp_pos (u / 2)
  have e1 : Real.exp (-(2 * u) / 4) = (Real.exp (u / 2))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  have e2 : Real.exp (-(2 * u)) = ((Real.exp (u / 2)) ^ 4)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; ring_nf
  have e3 : Real.exp u = (Real.exp (u / 2)) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have e4 : Real.exp (-u) = ((Real.exp (u / 2)) ^ 2)⁻¹ := by rw [← e3, Real.exp_neg]
  rw [e1, e2, e3, e4]
  set a := Real.exp (u / 2)
  have ha1 : 1 < a := by rw [show a = Real.exp (u / 2) from rfl]; exact Real.one_lt_exp_iff.mpr (by linarith)
  have h4 : a ^ 4 - 1 ≠ 0 := by nlinarith [pow_lt_pow_left₀ ha1 zero_le_one (by norm_num : (4:ℕ) ≠ 0)]
  have h2 : a ^ 2 - (a ^ 2)⁻¹ ≠ 0 := by
    have : 1 < a ^ 2 := one_lt_pow₀ ha1 (by norm_num)
    have : (a ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith
  have h1 : 1 - (a ^ 4)⁻¹ ≠ 0 := by
    have : (a ^ 4)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ ha1 (by norm_num))
    linarith
  field_simp

lemma re_gauss (t x : ℝ) :
    (GammaIntegrals.gaussK (1 / 4 + (t / 2 : ℝ) * Complex.I) (1 / 4) x).re
      = Real.exp (-x / 4) * (1 - Real.cos (t * x / 2)) / (1 - Real.exp (-x)) := by
  unfold GammaIntegrals.gaussK
  rw [Complex.div_ofReal_re, Complex.sub_re, Complex.exp_re, Complex.exp_re]
  congr 1
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  rw [show t / 2 * x = t * x / 2 by ring, show -(1 / 4 * x) = -x / 4 by ring]
  ring

/-- **Kernel identity** (from the repo's Gauss digamma integral): for every real `t`,
`(1 − cos tu)K(u)` is integrable on `(0,∞)` and integrates to `D(t)`. -/
theorem kerD (t : ℝ) :
    IntegrableOn (fun u => (1 - Real.cos (t * u)) * K u) (Ioi 0) ∧
      ∫ u in Ioi (0:ℝ), (1 - Real.cos (t * u)) * K u = D t := by
  have hz : 0 < (1 / 4 + (t / 2 : ℝ) * Complex.I).re := by simp
  have hw : 0 < (1 / 4 : ℂ).re := by norm_num
  obtain ⟨hI, hE⟩ := GammaIntegrals.digamma_sub_eq_integral hz hw
  set f : ℝ → ℝ := fun x => Real.exp (-x / 4) * (1 - Real.cos (t * x / 2)) / (1 - Real.exp (-x))
  have hre : IntegrableOn f (Ioi 0) := by
    have := hI.re
    refine this.congr_fun (fun x _ => re_gauss t x) measurableSet_Ioi
  have hcongr : EqOn (fun u => 2 * f (2 * u)) (fun u => (1 - Real.cos (t * u)) * K u) (Ioi 0) :=
    fun u hu => kern_id t u hu
  refine ⟨?_, ?_⟩
  · have h0 : IntegrableOn (fun x => f (2 * x)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff f 0 (by norm_num : (0:ℝ) < 2)).mpr (by simpa using hre)
    exact (IntegrableOn.congr_fun (Integrable.const_mul h0 2) hcongr measurableSet_Ioi)
  · rw [← setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      integral_comp_mul_left_Ioi f 0 (by norm_num : (0:ℝ) < 2)]
    simp only [mul_zero, smul_eq_mul]
    have h2 := congrArg Complex.re hE
    rw [Complex.sub_re] at h2
    unfold D; rw [h2, ← RCLike.re_to_complex, ← integral_re hI]
    rw [show (2:ℝ) * (2⁻¹ * ∫ x in Ioi 0, f x) = ∫ x in Ioi 0, f x by ring]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => (re_gauss t x).symm)

/-- **`ArchBridge` (Zhu's Lemma 2.5) proved.** -/
theorem archBridge : ArchBridge := by
  intro N x
  set F := WeilZhuRed.Fx 0 N x with hFdef
  have hc : Continuous F := by
    rw [hFdef]; unfold WeilZhuRed.Fx
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (That_cont _))
  have P := modePlancherel_of modeDecay 0 (modeOrth (by norm_num))
  have hF2 : IntegrableOn (fun t => F t ^ 2) (Ioi 0) := by
    simpa using (WeilZhuRed.expand_int 0 N x (fun _ => 1) (Ioi 0) (fun i j => by simpa using P.int1 i j)).1
  have hPs : IntegrableOn (fun t => Psi t * F t ^ 2) (Ioi 0) :=
    (WeilZhuRed.expand_int 0 N x Psi (Ioi 0) P.int2).1
  have hcos : ∀ v : ℝ, IntegrableOn (fun t => Real.cos (t * v) * F t ^ 2) (Ioi 0) := by
    intro v
    refine hF2.bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _
  have hDF : IntegrableOn (fun t => D t * F t ^ 2) (Ioi 0) := by
    have e : (fun t => D t * F t ^ 2) = fun t => Psi t * F t ^ 2
        + ((Real.log π - (Complex.digamma (1 / 4)).re) * F t ^ 2
        + Real.sqrt 2 * Real.log 2 * (Real.cos (t * Real.log 2) * F t ^ 2)) := by
      funext t; unfold D Psi; ring
    rw [e]; exact hPs.add ((hF2.const_mul _).add ((hcos _).const_mul _))
  -- the product integrand
  set φ : ℝ → ℝ → ℝ := fun t u => F t ^ 2 * ((1 - Real.cos (t * u)) * K u)
  have hKm : Measurable K := by unfold K; fun_prop
  have hFm : Measurable F := hc.measurable
  have hmeas : AEStronglyMeasurable (Function.uncurry φ)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have : Measurable (Function.uncurry φ) := by
      show Measurable fun p : ℝ × ℝ => F p.1 ^ 2 * ((1 - Real.cos (p.1 * p.2)) * K p.2)
      fun_prop
    exact this.aestronglyMeasurable
  have hinner : ∀ t, ∫ u in Ioi (0:ℝ), φ t u = D t * F t ^ 2 := by
    intro t
    simp only [φ]
    rw [integral_const_mul, (kerD t).2]; ring
  have hint : Integrable (Function.uncurry φ)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun t => ((kerD t).1.const_mul (F t ^ 2)), ?_⟩
    refine (show Integrable (fun t => D t * F t ^ 2) (volume.restrict (Ioi 0)) from hDF).congr ?_
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [Function.uncurry_apply_pair]
    rw [← hinner t]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have : 0 ≤ φ t u := by
      simp only [φ]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith [Real.cos_le_one (t * u)]) (K_pos hu).le)
    rw [Real.norm_eq_abs, abs_of_nonneg this]
  have hswap := integral_integral_swap hint
  -- autocorrelation values
  have hh : ∀ u : ℝ, |u| ≠ 1 → WeilForm.autocorr (fx N x) u = (1 / π) * ∫ t in Ioi 0, Real.cos (t * u) * F t ^ 2 :=
    fun u hu => acorr_gen N x hu
  have h0 : WeilForm.autocorr (fx N x) 0 = (1 / π) * ∫ t in Ioi 0, F t ^ 2 := by
    have := hh 0 (by norm_num); simpa using this
  have hmain : ∫ u in Ioi (0:ℝ), WeilForm.archIntegrand (fx N x) u = (1 / π) * ∫ t in Ioi 0, D t * F t ^ 2 := by
    have e1 : ∫ t in Ioi (0:ℝ), D t * F t ^ 2 = ∫ t in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), φ t u := by
      congr 1; funext t; rw [hinner]
    rw [e1, hswap, ← integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [(Set.countable_singleton (1:ℝ)).ae_notMem volume] with u hu1 hu
    have hu' : |u| ≠ 1 := by rw [abs_of_pos hu]; simpa using hu1
    have e2 : ∫ t in Ioi (0:ℝ), φ t u = K u * ((∫ t in Ioi 0, F t ^ 2) - ∫ t in Ioi 0, Real.cos (t * u) * F t ^ 2) := by
      rw [← integral_sub hF2 (hcos u), ← integral_const_mul]
      congr 1; funext t; simp only [φ]; ring
    rw [e2]
    unfold WeilForm.archIntegrand
    rw [h0, hh u hu']
    unfold K; ring
  -- assemble
  have hn : WeilForm.normSq (fx N x) = WeilForm.autocorr (fx N x) 0 := by
    unfold WeilForm.normSq WeilForm.autocorr; congr 1; funext t; rw [add_zero, sq]
  have e3 : (fun t => ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π) * F t ^ 2)
      = fun t => D t * F t ^ 2 + ((Complex.digamma (1 / 4)).re - Real.log π) * F t ^ 2 := by
    funext t; unfold D; ring
  show _ = (1 / π) * ∫ t in Ioi 0, ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π) * F t ^ 2
  rw [e3, integral_add hDF (hF2.const_mul _), integral_const_mul, hmain, hn, h0]
  ring

/-- **Even sector, unconditional except for the arb head certificate.**
`0 < weilQ (1/2) (Σ_{i<N} xᵢ T_{2i})` for `N ≥ 28`, `x ≠ 0`; only input `EvenHead`. -/
theorem L05_even (H : EvenHead) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < WeilForm.weilQ (1 / 2) (fx N x) :=
  WeilFourier.L05_even archBridge H N hN x hx

end WeilArch
