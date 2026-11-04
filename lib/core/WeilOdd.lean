import Mathlib
import WeilArch
import OddPositivity

/-! # Both sectors in the general Weil form `weilQg`: `weilQg (1/2) (f_even + g_odd) = QF₀ + QF₁`

For `h = Σ xᵢ T_{2i} + Σ yᵢ T_{2i+1}` on `[−1/2, 1/2]` the general real Weil form `WeilForm.weilQg`
(pole term `2 ĝ(i/2) ĝ(−i/2)`) splits as the even frequency form plus the odd one. The Fourier transform of `h` is
`F₀(2πξ) + i F₁(2πξ)`, so `𝓕h(ξ)𝓕h(−ξ) = F₀² + F₁²`. The even/odd cross terms cancel in the autocorrelation,
and the pole term is `2(A + B)(A − B)`. -/

namespace WeilOdd

open Real Finset MeasureTheory Set WeilTailB WeilPlanch WeilModes WeilFourier WeilArch

noncomputable def gx (N : ℕ) (x : ℕ → ℝ) (u : ℝ) : ℝ := ∑ i ∈ range N, x i * legT (2 * i + 1) u
noncomputable def Qy (N : ℕ) (x : ℕ → ℝ) (u : ℝ) : ℝ := ∑ i ∈ range N, x i * P (2 * i + 1) u

/-- the mixed probe -/
noncomputable def hx (N : ℕ) (x y : ℕ → ℝ) (u : ℝ) : ℝ := fx N x u + gx N y u

lemma gx_eq (N : ℕ) (x : ℕ → ℝ) : gx N x = cut (Qy N x) := by
  funext u
  unfold gx Qy
  simp_rw [legT_eq]
  unfold cut
  by_cases hu : u ∈ I0
  · simp only [Set.indicator_of_mem hu]
  · simp only [Set.indicator_of_notMem hu, mul_zero, Finset.sum_const_zero]

lemma hx_eq (N : ℕ) (x y : ℕ → ℝ) : hx N x y = cut (fun u => Qx N x u + Qy N y u) := by
  funext u; unfold hx; rw [fx_eq, gx_eq]; unfold cut
  by_cases hu : u ∈ I0
  · simp only [Set.indicator_of_mem hu]
  · simp only [Set.indicator_of_notMem hu, add_zero]

lemma legT_neg (n : ℕ) (u : ℝ) : legT n (-u) = (-1) ^ n * legT n u := by
  unfold legT; rw [abs_neg]
  split_ifs
  · rw [Polynomial.shiftedLegendre_eval_symm n (-u + 1 / 2), show (1:ℝ) - (-u + 1 / 2) = u + 1 / 2 by ring]; ring
  · ring

lemma hx_neg (N : ℕ) (x y : ℕ → ℝ) (u : ℝ) : hx N x y (-u) = fx N x u - gx N y u := by
  unfold hx fx gx
  simp_rw [legT_neg]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine sum_congr rfl fun i _ => ?_; rw [pow_mul]; norm_num
  · refine sum_congr rfl fun i _ => ?_; rw [pow_add, pow_mul]; norm_num

/-! ## pole terms -/

lemma pole_sum (N : ℕ) (x y : ℕ → ℝ) (s : ℝ) :
    ∫ u in (-(1/2):ℝ)..(1/2), (fx N x u + s * gx N y u) * Real.exp (-(u / 2))
      = ∑ i ∈ range N, x i * pole (2 * i) + s * ∑ i ∈ range N, y i * pole (2 * i + 1) := by
  have e : ∫ u in (-(1/2):ℝ)..(1/2), (fx N x u + s * gx N y u) * Real.exp (-(u / 2))
      = ∫ u in (-(1/2):ℝ)..(1/2), ((∑ i ∈ range N, x i *
          ((Real.sqrt (2 * ((2 * i : ℕ) : ℝ) + 1) * (sL (2 * i)).eval (u + 1 / 2)) * Real.exp (-(u / 2))))
        + s * ∑ i ∈ range N, y i *
          ((Real.sqrt (2 * ((2 * i + 1 : ℕ) : ℝ) + 1) * (sL (2 * i + 1)).eval (u + 1 / 2)) * Real.exp (-(u / 2)))) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hu' : |u| ≤ 1 / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
    simp only [fx, gx, legT, ite_eq_left hu', aeval_eq, Finset.sum_mul, Finset.mul_sum, add_mul]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_); push_cast; ring
    · refine Finset.sum_congr rfl (fun i _ => ?_); push_cast; ring
  have c0 : ∀ i, Continuous fun u : ℝ => x i *
      ((Real.sqrt (2 * ((2 * i : ℕ) : ℝ) + 1) * (sL (2 * i)).eval (u + 1 / 2)) * Real.exp (-(u / 2))) := by
    intro i; have := (sL (2 * i)).continuous; fun_prop
  have c1 : ∀ i, Continuous fun u : ℝ => y i *
      ((Real.sqrt (2 * ((2 * i + 1 : ℕ) : ℝ) + 1) * (sL (2 * i + 1)).eval (u + 1 / 2)) * Real.exp (-(u / 2))) := by
    intro i; have := (sL (2 * i + 1)).continuous; fun_prop
  have i0 : IntervalIntegrable (fun u : ℝ => ∑ i ∈ range N, x i *
      ((Real.sqrt (2 * ((2 * i : ℕ) : ℝ) + 1) * (sL (2 * i)).eval (u + 1 / 2)) * Real.exp (-(u / 2))))
      volume (-(1/2)) (1/2) := (continuous_finsetSum _ fun i _ => c0 i).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun u : ℝ => s * ∑ i ∈ range N, y i *
      ((Real.sqrt (2 * ((2 * i + 1 : ℕ) : ℝ) + 1) * (sL (2 * i + 1)).eval (u + 1 / 2)) * Real.exp (-(u / 2))))
      volume (-(1/2)) (1/2) := (continuous_const.mul (continuous_finsetSum _ fun i _ => c1 i)).intervalIntegrable _ _
  rw [e, intervalIntegral.integral_add i0 i1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun i _ => (c0 i).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun i _ => (c1 i).intervalIntegrable _ _)]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_const_mul, pole_mode]
  · congr 1; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_const_mul, pole_mode]

lemma poleR_hx (N : ℕ) (x y : ℕ → ℝ) : WeilForm.poleR (hx N x y) (1 / 2)
    = ∑ i ∈ range N, x i * pole (2 * i) + ∑ i ∈ range N, y i * pole (2 * i + 1) := by
  have := pole_sum N x y 1
  simp only [one_mul] at this
  unfold WeilForm.poleR hx; rw [show -(1/2:ℝ) = -(1/2) by ring]; exact this

lemma poleL_hx (N : ℕ) (x y : ℕ → ℝ) : WeilForm.poleL (hx N x y) (1 / 2)
    = ∑ i ∈ range N, x i * pole (2 * i) - ∑ i ∈ range N, y i * pole (2 * i + 1) := by
  have := pole_sum N x y (-1)
  unfold WeilForm.poleL
  have hc := intervalIntegral.integral_comp_neg (a := -(1/2:ℝ)) (b := 1/2)
    (fun u => hx N x y u * Real.exp (u / 2))
  simp only [neg_neg] at hc
  rw [← hc]
  convert this using 1
  · congr 1; funext u; rw [hx_neg]; ring_nf
  · ring

/-! ## Fourier transform and autocorrelation -/

open FourierTransform in
lemma fourier_gx (N : ℕ) (x : ℕ → ℝ) (ξ : ℝ) :
    𝓕 (fun t => ((gx N x t : ℝ) : ℂ)) ξ = Complex.I * (WeilZhuRed.Fx 1 N x (2 * π * ξ) : ℂ) := by
  have e : (fun t => ((gx N x t : ℝ) : ℂ)) = fun t => ∑ i ∈ range N, (x i : ℂ) * ((legT (2 * i + 1) t : ℝ) : ℂ) := by
    funext t; unfold gx; push_cast; rfl
  rw [e, Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · rw [WeilZhuRed.Fx, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h := LF_sec (par := 1) (by norm_num) i ξ
    simp only [pow_one] at h
    rw [Complex.ofReal_mul, show Complex.I * ((x i : ℂ) * (That (2 * i + 1) (2 * π * ξ) : ℂ))
      = (x i : ℂ) * (Complex.I * (That (2 * i + 1) (2 * π * ξ) : ℂ)) by ring, ← h,
      Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1; funext v; simp only [smul_eq_mul]; ring
  · intro i _
    have hl := (legC_int (2 * i + 1)).const_mul (x i : ℂ)
    refine hl.norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul hl.aestronglyMeasurable) ?_
    filter_upwards with v
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

lemma fxC_int (N : ℕ) (x : ℕ → ℝ) : Integrable (fun t => ((fx N x t : ℝ) : ℂ)) := by
  rw [fx_eq]; exact cutC_int _ (continuous_finsetSum _ fun i _ => continuous_const.mul (P_cont _))

lemma gxC_int (N : ℕ) (x : ℕ → ℝ) : Integrable (fun t => ((gx N x t : ℝ) : ℂ)) := by
  rw [gx_eq]; exact cutC_int _ (continuous_finsetSum _ fun i _ => continuous_const.mul (P_cont _))

open FourierTransform in
lemma fourier_hx (N : ℕ) (x y : ℕ → ℝ) (ξ : ℝ) :
    𝓕 (fun t => ((hx N x y t : ℝ) : ℂ)) ξ
      = (WeilZhuRed.Fx 0 N x (2 * π * ξ) : ℂ) + Complex.I * (WeilZhuRed.Fx 1 N y (2 * π * ξ) : ℂ) := by
  rw [← fourier_gx, ← fourier_fx, ← fx_eq]
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_add]
  · congr 1; funext v; unfold hx; push_cast; ring
  · refine (fxC_int N x).norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (fxC_int N x).aestronglyMeasurable) ?_
    filter_upwards with v
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  · refine (gxC_int N y).norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (gxC_int N y).aestronglyMeasurable) ?_
    filter_upwards with v
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- spectral density of the mixed probe -/
noncomputable def S (N : ℕ) (x y : ℕ → ℝ) (t : ℝ) : ℝ := WeilZhuRed.Fx 0 N x t ^ 2 + WeilZhuRed.Fx 1 N y t ^ 2

lemma F0_neg (N : ℕ) (x : ℕ → ℝ) (t : ℝ) : WeilZhuRed.Fx 0 N x (-t) = WeilZhuRed.Fx 0 N x t := by
  unfold WeilZhuRed.Fx; refine Finset.sum_congr rfl (fun i _ => ?_); rw [That_neg, pow_add, pow_mul]; norm_num

lemma F1_neg (N : ℕ) (x : ℕ → ℝ) (t : ℝ) : WeilZhuRed.Fx 1 N x (-t) = -WeilZhuRed.Fx 1 N x t := by
  unfold WeilZhuRed.Fx; rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_); rw [That_neg, pow_add, pow_mul]; norm_num

lemma F_cont (par N : ℕ) (x : ℕ → ℝ) : Continuous (WeilZhuRed.Fx par N x) := by
  unfold WeilZhuRed.Fx; exact continuous_finsetSum _ (fun i _ => continuous_const.mul (That_cont _))

theorem acorr_hx (N : ℕ) (x y : ℕ → ℝ) {v : ℝ} (hv : |v| ≠ 1) : WeilForm.autocorr (hx N x y) v
    = (1 / π) * ∫ t in Set.Ioi 0, Real.cos (t * v) * S N x y t := by
  obtain ⟨C0, hC0, hd0⟩ := decay_sum 0 N x
  obtain ⟨C1, hC1, hd1⟩ := decay_sum 1 N y
  have hl : |(-v)| ≠ 1 := by rw [abs_neg]; exact hv
  have hQ : Continuous (fun u => Qx N x u + Qy N y u) :=
    (continuous_finsetSum _ fun i _ => continuous_const.mul (P_cont _)).add
      (continuous_finsetSum _ fun i _ => continuous_const.mul (P_cont _))
  have key := parseval _ _ hQ hQ (S N x y) (((F_cont 0 N x).pow 2).add ((F_cont 1 N y).pow 2))
    (fun t => by unfold S; rw [F0_neg, F1_neg, neg_sq]) (C0 ^ 2 + C1 ^ 2) (fun t ht => by
      have h1 : 0 < 1 + t := by linarith
      unfold S
      rw [abs_of_nonneg (by positivity), add_div]
      have a := pow_le_pow_left₀ (abs_nonneg _) (hd0 t ht) 2
      have b := pow_le_pow_left₀ (abs_nonneg _) (hd1 t ht) 2
      rw [sq_abs, div_pow] at a b
      linarith)
    (fun ξ => by
      rw [← hx_eq, fourier_hx, fourier_hx, show 2 * π * -ξ = -(2 * π * ξ) by ring, F0_neg, F1_neg]
      unfold S; push_cast
      linear_combination (-(WeilZhuRed.Fx 1 N y (2 * π * ξ) : ℂ) ^ 2) * Complex.I_sq)
    hl
  unfold WeilForm.autocorr
  rw [hx_eq]
  simp only [sub_neg_eq_add, mul_neg, Real.cos_neg] at key
  exact key

/-! ## Archimedean term -/

theorem arch_hx (N : ℕ) (x y : ℕ → ℝ) :
    ((Complex.digamma (1 / 4)).re - Real.log π) * WeilForm.normSq (hx N x y)
      + (∫ u in Set.Ioi (0:ℝ), WeilForm.archIntegrand (hx N x y) u)
      = (1 / π) * ∫ t in Set.Ioi 0, ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π)
          * S N x y t := by
  set F := S N x y with hFdef
  have hc : Continuous F := ((F_cont 0 N x).pow 2).add ((F_cont 1 N y).pow 2)
  have P0 := modePlancherel_of modeDecay 0 (modeOrth (by norm_num))
  have P1 := modePlancherel_of modeDecay 1 (modeOrth (by norm_num))
  have hF2 : IntegrableOn F (Ioi 0) := by
    have a := (WeilZhuRed.expand_int 0 N x (fun _ => 1) (Ioi 0) (fun i j => by simpa using P0.int1 i j)).1
    have b := (WeilZhuRed.expand_int 1 N y (fun _ => 1) (Ioi 0) (fun i j => by simpa using P1.int1 i j)).1
    simp only [one_mul] at a b
    exact a.add b
  have hPs : IntegrableOn (fun t => Psi t * F t) (Ioi 0) := by
    have a := (WeilZhuRed.expand_int 0 N x Psi (Ioi 0) P0.int2).1
    have b := (WeilZhuRed.expand_int 1 N y Psi (Ioi 0) P1.int2).1
    refine (a.add b).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hFdef, S, Pi.add_apply]; ring
  have hcos : ∀ v : ℝ, IntegrableOn (fun t => Real.cos (t * v) * F t) (Ioi 0) := by
    intro v
    refine hF2.bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _
  have hDF : IntegrableOn (fun t => D t * F t) (Ioi 0) := by
    have e : (fun t => D t * F t) = fun t => Psi t * F t
        + ((Real.log π - (Complex.digamma (1 / 4)).re) * F t
        + Real.sqrt 2 * Real.log 2 * (Real.cos (t * Real.log 2) * F t)) := by
      funext t; unfold D Psi; ring
    rw [e]; exact hPs.add ((hF2.const_mul _).add ((hcos _).const_mul _))
  have hF0 : ∀ t, 0 ≤ F t := fun t => by simp only [hFdef, S]; positivity
  set φ : ℝ → ℝ → ℝ := fun t u => F t * ((1 - Real.cos (t * u)) * K u)
  have hKm : Measurable K := by unfold K; fun_prop
  have hFm : Measurable F := hc.measurable
  have hmeas : AEStronglyMeasurable (Function.uncurry φ)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have : Measurable (Function.uncurry φ) := by
      show Measurable fun p : ℝ × ℝ => F p.1 * ((1 - Real.cos (p.1 * p.2)) * K p.2)
      fun_prop
    exact this.aestronglyMeasurable
  have hinner : ∀ t, ∫ u in Ioi (0:ℝ), φ t u = D t * F t := by
    intro t
    simp only [φ]
    rw [integral_const_mul, (kerD t).2]; ring
  have hint : Integrable (Function.uncurry φ)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun t => ((kerD t).1.const_mul (F t)), ?_⟩
    refine (show Integrable (fun t => D t * F t) (volume.restrict (Ioi 0)) from hDF).congr ?_
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [Function.uncurry_apply_pair]
    rw [← hinner t]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    have : 0 ≤ φ t u := by
      simp only [φ]
      exact mul_nonneg (hF0 t) (mul_nonneg (by linarith [Real.cos_le_one (t * u)]) (K_pos hu).le)
    rw [Real.norm_eq_abs, abs_of_nonneg this]
  have hswap := integral_integral_swap hint
  have hh : ∀ u : ℝ, |u| ≠ 1 → WeilForm.autocorr (hx N x y) u = (1 / π) * ∫ t in Ioi 0, Real.cos (t * u) * F t :=
    fun u hu => acorr_hx N x y hu
  have h0 : WeilForm.autocorr (hx N x y) 0 = (1 / π) * ∫ t in Ioi 0, F t := by
    have := hh 0 (by norm_num); simpa using this
  have hmain : ∫ u in Ioi (0:ℝ), WeilForm.archIntegrand (hx N x y) u = (1 / π) * ∫ t in Ioi 0, D t * F t := by
    have e1 : ∫ t in Ioi (0:ℝ), D t * F t = ∫ t in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), φ t u := by
      congr 1; funext t; rw [hinner]
    rw [e1, hswap, ← integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [(Set.countable_singleton (1:ℝ)).ae_notMem volume] with u hu1 hu
    have hu' : |u| ≠ 1 := by rw [abs_of_pos hu]; simpa using hu1
    have e2 : ∫ t in Ioi (0:ℝ), φ t u = K u * ((∫ t in Ioi 0, F t) - ∫ t in Ioi 0, Real.cos (t * u) * F t) := by
      rw [← integral_sub hF2 (hcos u), ← integral_const_mul]
      congr 1; funext t; simp only [φ]; ring
    rw [e2]
    unfold WeilForm.archIntegrand
    rw [h0, hh u hu']
    unfold K; ring
  have hn : WeilForm.normSq (hx N x y) = WeilForm.autocorr (hx N x y) 0 := by
    unfold WeilForm.normSq WeilForm.autocorr; congr 1; funext t; rw [add_zero, sq]
  have e3 : (fun t => ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π) * F t)
      = fun t => D t * F t + ((Complex.digamma (1 / 4)).re - Real.log π) * F t := by
    funext t; unfold D; ring
  rw [e3, integral_add hDF (hF2.const_mul _), integral_const_mul, hmain, hn, h0]
  ring

/-! ## Prime sum -/

lemma hx_supp (N : ℕ) (x y : ℕ → ℝ) {u : ℝ} (hu : 1 / 2 < |u|) : hx N x y u = 0 := by
  unfold hx; rw [fx_supp N x hu]
  unfold gx; rw [zero_add]; refine sum_eq_zero (fun i _ => ?_); unfold legT; rw [ite_eq_right (by linarith)]; ring

lemma autocorr_hx_supp (N : ℕ) (x y : ℕ → ℝ) {u : ℝ} (hu : 1 < |u|) : WeilForm.autocorr (hx N x y) u = 0 := by
  unfold WeilForm.autocorr
  have : ∀ t, hx N x y t * hx N x y (t + u) = 0 := by
    intro t
    by_cases ht : 1 / 2 < |t|
    · rw [hx_supp N x y ht, zero_mul]
    · have : 1 / 2 < |t + u| := by
        have := abs_sub_abs_le_abs_sub u (-(t)); rw [abs_neg] at this
        have e : u - -t = t + u := by ring
        rw [e] at this; push Not at ht; linarith
      rw [hx_supp N x y this, mul_zero]
  simp [this]

theorem prime_hx (N : ℕ) (x y : ℕ → ℝ) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * WeilForm.autocorr (hx N x y) (Real.log n)
      = ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 * WeilForm.autocorr (hx N x y) (Real.log 2) := by
  rw [tsum_eq_single (2:ℕ)]
  · push_cast; ring
  · intro n hn
    by_cases hl : ArithmeticFunction.vonMangoldt n = 0
    · simp [hl]
    · have h2 : 2 ≤ n := by
        rcases Nat.lt_or_ge n 2 with h' | h'
        · interval_cases n <;> simp at hl
        · exact h'
      have h3 : (3:ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have he := Real.exp_one_lt_d9
      have l3 : 1 < Real.log 3 := by rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith
      have := Real.log_le_log (by norm_num) h3
      have hpos : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
      rw [autocorr_hx_supp N x y (by rw [abs_of_nonneg hpos]; linarith), mul_zero]

/-! ## The identity -/

/-- **`weilQg (1/2) (f_even + g_odd) = QF₀(x) + QF₁(y)`** (pole sign `+` even, `−` odd). -/
theorem weilQg_hx (N : ℕ) (x y : ℕ → ℝ) :
    WeilForm.weilQg (1 / 2) (hx N x y) = WeilZhuRed.QF 0 1 N x + WeilZhuRed.QF 1 (-1) N y := by
  have P0 := modePlancherel_of modeDecay 0 (modeOrth (by norm_num))
  have P1 := modePlancherel_of modeDecay 1 (modeOrth (by norm_num))
  have a0 := (WeilZhuRed.expand_int 0 N x (fun _ => 1) (Set.Ioi 0) (fun i j => by simpa using P0.int1 i j)).1
  have a1 := (WeilZhuRed.expand_int 1 N y (fun _ => 1) (Set.Ioi 0) (fun i j => by simpa using P1.int1 i j)).1
  simp only [one_mul] at a0 a1
  have p0 := (WeilZhuRed.expand_int 0 N x Psi (Set.Ioi 0) P0.int2).1
  have p1 := (WeilZhuRed.expand_int 1 N y Psi (Set.Ioi 0) P1.int2).1
  have hS : IntegrableOn (S N x y) (Set.Ioi 0) := a0.add a1
  have hcos : IntegrableOn (fun t => Real.cos (t * Real.log 2) * S N x y t) (Set.Ioi 0) := by
    refine hS.bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _
  have hsplit : (∫ t in Set.Ioi 0, ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π) * S N x y t)
      = (∫ t in Set.Ioi 0, Psi t * WeilZhuRed.Fx 0 N x t ^ 2) + (∫ t in Set.Ioi 0, Psi t * WeilZhuRed.Fx 1 N y t ^ 2)
        + Real.sqrt 2 * Real.log 2 * ∫ t in Set.Ioi 0, Real.cos (t * Real.log 2) * S N x y t := by
    have e : (fun t => ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π) * S N x y t)
        = fun t => (Psi t * WeilZhuRed.Fx 0 N x t ^ 2 + Psi t * WeilZhuRed.Fx 1 N y t ^ 2)
          + Real.sqrt 2 * Real.log 2 * (Real.cos (t * Real.log 2) * S N x y t) := by
      funext t; unfold Psi S; ring
    have pp : IntegrableOn (fun t => Psi t * WeilZhuRed.Fx 0 N x t ^ 2 + Psi t * WeilZhuRed.Fx 1 N y t ^ 2)
        (Set.Ioi 0) := p0.add p1
    rw [e, integral_add pp (hcos.const_mul _), integral_add p0 p1, integral_const_mul]
  have ha := arch_hx N x y
  have hc := WeilZhuRed.prime_coeff_L05
  have hac := acorr_hx N x y (v := Real.log 2) (by
    rw [abs_of_pos (Real.log_pos one_lt_two)]; exact ne_of_lt (by linarith [Real.log_two_lt_d9]))
  unfold WeilForm.weilQg WeilZhuRed.QF
  rw [poleR_hx, poleL_hx]
  have hp : WeilForm.primeS (hx N x y)
      = ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 * WeilForm.autocorr (hx N x y) (Real.log 2) := prime_hx N x y
  rw [hp, hac]
  unfold WeilForm.archE WeilForm.weilConst
  have hz : ∀ i, (2 * i + 0) = 2 * i := fun i => rfl
  simp only [hz]
  set Ic := ∫ t in Set.Ioi 0, Real.cos (t * Real.log 2) * S N x y t
  linear_combination ha + (1 / π) * hsplit - (1 / π) * Ic * hc

end WeilOdd
