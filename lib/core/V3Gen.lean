import Mathlib
import V3Main
import WeilGen

/-! # Weil positivity on `V'` for every `C¹` test function, at every support `L ≤ log 3 / 2`

For `f` of class `C¹` with `f(u) = 0` for `|u| > L`, `0 ≤ L ≤ log 3 / 2`, and `f ∈ V'` (`InVp L f`:
`∫ f e^{−u/2} = ∫ f e^{u/2} = ∫ f = 0` over `[−L, L]`):

  `weilQg L f ≥ 4·10⁻⁴ ‖f‖²`, and `weilQg L f > 0` for `f ≠ 0`  (`coer_vprime`, `pos_vprime`).

Proof. At support `L ≤ L* = log 3 / 2` the form and the three functionals are those at `L*` (`weilQg_shrink`). Write
`f = sc g` with `g` supported in `[−1/2, 1/2]`. `WeilGen.approx` gives cut polynomials `gₖ → g`, uniformly `Good`;
each is a Legendre mode sum. Subtracting `c₀(gₖ)T₀ + c₁(gₖ)T₂ + c₂(gₖ)T₁`, with coefficients linear in the three
functionals of `gₖ` (`corr`), puts it in `V'` (`corr_V`) while keeping it a mode sum, so `V3Main.vprime_hx` applies.
The functionals of `gₖ` tend to those of `g`, which vanish, so the corrected sequence still tends to `g` and stays
uniformly `Good`; and the rescaled form is continuous along such sequences (`tendsto_weilQg_sc`: the archimedean
term is dominated by `B(M+B)/λ · 8e^{−u/4}`). -/

namespace V3Gen

open Real Filter Topology MeasureTheory Set WeilForm WeilCont V3Scale

/-! ## The rescaled form is continuous along `Good` sequences -/

lemma autocorr_one {g : ℝ → ℝ} (hs : ∀ t, 1 / 2 < |t| → g t = 0) {u : ℝ} (hu : 1 ≤ |u|) : autocorr g u = 0 := by
  unfold autocorr
  refine integral_eq_zero_of_ae ?_
  filter_upwards [(Set.countable_singleton (-u / 2)).ae_notMem volume] with t ht
  simp only [Set.mem_singleton_iff] at ht
  by_cases h1 : 1 / 2 < |t|
  · simp [hs t h1]
  · by_cases h2 : 1 / 2 < |t + u|
    · simp [hs _ h2]
    · exfalso; push Not at h1 h2
      rcases abs_le.mp h1 with ⟨a1, a2⟩
      rcases abs_le.mp h2 with ⟨b1, b2⟩
      rcases le_abs'.mp hu with h | h
      · exact ht (by linarith)
      · exact ht (by linarith)

/-- The prime sum of `sc g`: only `n = 2`; `n = 3` sits on the boundary `log 3 / λ = 1`. -/
theorem primeS_sc_gen {g : ℝ → ℝ} (hs : ∀ t, 1 / 2 < |t| → g t = 0) :
    primeS (sc g) = ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 * autocorr g (Real.log 2 / V3Scale.lam) := by
  unfold primeS
  simp_rw [autocorr_sc]
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
      have hlog : V3Scale.lam ≤ Real.log n := Real.log_le_log (by norm_num) h3
      have : 1 ≤ |Real.log n / V3Scale.lam| := by
        rw [abs_of_nonneg (div_nonneg (by linarith [lam_pos]) lam_pos.le), le_div_iff₀ lam_pos]; linarith
      rw [autocorr_one hs this, mul_zero]

lemma sc_meas {g : ℝ → ℝ} (hm : Measurable g) : Measurable (sc g) := by
  unfold sc; exact (hm.comp (measurable_id.div_const _)).div_const _

theorem tendsto_archE_sc {B M : ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hg : ∀ k, Good B M (g k))
    (hlim : ∀ t, Tendsto (fun k => g k t) atTop (𝓝 (f t))) :
    Tendsto (fun k => archE (sc (g k))) atTop (𝓝 (archE (sc f))) := by
  unfold archE
  have hl := lam_pos
  have hint : Integrable (fun u => B * (M + B) / V3Scale.lam * (8 * Real.exp (-(u / 4)))) (volume.restrict (Ioi 0)) := by
    have : IntegrableOn (fun u : ℝ => Real.exp (-(1/4) * u)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 (by norm_num)
    have e : (fun u => B * (M + B) / V3Scale.lam * (8 * Real.exp (-(u / 4))))
        = fun u => B * (M + B) / V3Scale.lam * 8 * Real.exp (-(1/4) * u) := by
      funext u; ring_nf
    rw [e]; exact this.const_mul _
  refine tendsto_integral_of_dominated_convergence _ (fun k => arch_meas (sc_meas (hg k).meas)) hint
    (fun k => (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => ?_)) (ae_of_all _ fun u => ?_)
  · have hu' : 0 < u := hu
    simp only [archIntegrand, autocorr_sc, zero_div]
    have hK : 0 < Real.exp (u / 2) / Real.sinh u := div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu')
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK]
    have hd := diff_bd (hg k) (div_pos hu' hl)
    have hMB : 0 ≤ B * (M + B) := by
      have := (abs_nonneg _).trans hd; exact nonneg_of_mul_nonneg_left (by linarith) (div_pos hu' hl)
    calc _ ≤ B * (M + B) * (u / V3Scale.lam) * (Real.exp (u / 2) / Real.sinh u) := mul_le_mul_of_nonneg_right hd hK.le
      _ = B * (M + B) / V3Scale.lam * (u * (Real.exp (u / 2) / Real.sinh u)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_bd hu') (div_nonneg hMB hl.le)
  · simp only [archIntegrand, autocorr_sc, zero_div]
    exact ((tendsto_autocorr hg hlim _).sub (tendsto_autocorr hg hlim _)).mul_const _

lemma pR_eq (g : ℝ → ℝ) : ∫ y in (-(1 / 2):ℝ)..(1 / 2), g y * Real.exp (-(V3Scale.lam * y / 2))
    = ∫ y in (-(1/2):ℝ)..(1/2), g y * Real.exp ((-(V3Scale.lam / 2)) * y) := by
  congr 1; funext y; congr 2; ring

lemma pL_eq (g : ℝ → ℝ) : ∫ y in (-(1 / 2):ℝ)..(1 / 2), g y * Real.exp (V3Scale.lam * y / 2)
    = ∫ y in (-(1/2):ℝ)..(1/2), g y * Real.exp ((V3Scale.lam / 2) * y) := by
  congr 1; funext y; congr 2; ring

/-- **The rescaled form is continuous** along bounded, uniformly interior-Lipschitz pointwise convergence. -/
theorem tendsto_weilQg_sc {B M : ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hg : ∀ k, Good B M (g k))
    (hfs : ∀ t, 1 / 2 < |t| → f t = 0) (hlim : ∀ t, Tendsto (fun k => g k t) atTop (𝓝 (f t))) :
    Tendsto (fun k => weilQg (V3Scale.lam / 2) (sc (g k))) atTop (𝓝 (weilQg (V3Scale.lam / 2) (sc f))) := by
  unfold weilQg
  simp_rw [poleR_sc, poleL_sc, normSq_sc, primeS_sc_gen (hg _).supp, primeS_sc_gen hfs, pR_eq, pL_eq]
  exact ((((((tendsto_pole hg hlim _).const_mul (Real.sqrt V3Scale.lam)).const_mul 2).mul
    ((tendsto_pole hg hlim _).const_mul (Real.sqrt V3Scale.lam))).add
    ((tendsto_normSq hg hlim).const_mul _)).add (tendsto_archE_sc hg hlim)).sub
    (((tendsto_autocorr hg hlim _).const_mul _).const_mul 2)

/-! ## The three functionals of `V'` on `[−1/2, 1/2]` -/

noncomputable def PR (g : ℝ → ℝ) : ℝ := ∫ u in (-(1/2):ℝ)..(1/2), g u * Real.exp ((-(V3Scale.lam / 2)) * u)
noncomputable def PL (g : ℝ → ℝ) : ℝ := ∫ u in (-(1/2):ℝ)..(1/2), g u * Real.exp ((V3Scale.lam / 2) * u)
noncomputable def P0 (g : ℝ → ℝ) : ℝ := ∫ u in (-(1/2):ℝ)..(1/2), g u * Real.exp (0 * u)

lemma poleR_scP (g : ℝ → ℝ) : poleR (sc g) (V3Scale.lam / 2) = Real.sqrt V3Scale.lam * PR g := by rw [poleR_sc, pR_eq]; rfl

lemma poleL_scP (g : ℝ → ℝ) : poleL (sc g) (V3Scale.lam / 2) = Real.sqrt V3Scale.lam * PL g := by rw [poleL_sc, pL_eq]; rfl

lemma int_scP (g : ℝ → ℝ) : ∫ u in (-(V3Scale.lam / 2))..(V3Scale.lam / 2), sc g u = Real.sqrt V3Scale.lam * P0 g := by
  have hl : V3Scale.lam ≠ 0 := lam_pos.ne'
  have key := intervalIntegral.integral_comp_div (a := -(V3Scale.lam / 2)) (b := V3Scale.lam / 2)
    (fun v => g v / Real.sqrt V3Scale.lam) hl
  have e1 : -(V3Scale.lam / 2) / V3Scale.lam = -(1 / 2) := by field_simp
  have e2 : V3Scale.lam / 2 / V3Scale.lam = 1 / 2 := by field_simp
  rw [e1, e2, smul_eq_mul] at key
  unfold sc
  rw [key, intervalIntegral.integral_div]
  have hs : V3Scale.lam / Real.sqrt V3Scale.lam = Real.sqrt V3Scale.lam := by
    rw [div_eq_iff sqrt_lam_pos.ne', ← sq, sqrt_lam_sq]
  unfold P0
  simp only [zero_mul, Real.exp_zero, mul_one]
  calc V3Scale.lam * ((∫ y in (-(1/2):ℝ)..(1/2), g y) / Real.sqrt V3Scale.lam)
      = (V3Scale.lam / Real.sqrt V3Scale.lam) * ∫ y in (-(1/2):ℝ)..(1/2), g y := by ring
    _ = _ := by rw [hs]

lemma PR_hx (N : ℕ) (x y : ℕ → ℝ) : PR (WeilOdd.hx N x y)
    = ∑ i ∈ Finset.range N, x i * V3Zhu.pole3 (2 * i) + ∑ i ∈ Finset.range N, y i * V3Zhu.pole3 (2 * i + 1) := by
  have h := V3Pole.poleR_sc_hx N x y
  rw [poleR_scP] at h
  exact mul_left_cancel₀ sqrt_lam_pos.ne' h

lemma PL_hx (N : ℕ) (x y : ℕ → ℝ) : PL (WeilOdd.hx N x y)
    = ∑ i ∈ Finset.range N, x i * V3Zhu.pole3 (2 * i) - ∑ i ∈ Finset.range N, y i * V3Zhu.pole3 (2 * i + 1) := by
  have h := V3Pole.poleL_sc_hx N x y
  rw [poleL_scP] at h
  exact mul_left_cancel₀ sqrt_lam_pos.ne' h

lemma P0_hx (N : ℕ) (hN : 1 ≤ N) (x y : ℕ → ℝ) : P0 (WeilOdd.hx N x y) = x 0 := by
  have h := V3Pole.int_sc_hx N hN x y
  rw [int_scP] at h
  exact mul_left_cancel₀ sqrt_lam_pos.ne' h

/-! ## `Good` functions: the Legendre modes, linear combinations -/

lemma abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have := abs_add_le a (-b); rwa [abs_neg, ← sub_eq_add_neg] at this

lemma good_lin {B M B' M' C : ℝ} {f g : ℝ → ℝ} (c : ℝ) (hc : |c| ≤ C) (hf : Good B M f) (hg : Good B' M' g) :
    Good (B + C * B') (M + C * M') (fun u => f u - c * g u) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hc
  refine ⟨hf.meas.sub (measurable_const.mul hg.meas), fun u hu => by simp [hf.supp u hu, hg.supp u hu],
    fun u => ?_, fun s t hs ht => ?_⟩
  · have h1 : |f u - c * g u| ≤ |f u| + |c| * |g u| := by rw [← abs_mul]; exact abs_sub_le' _ _
    have h2 : |c| * |g u| ≤ C * B' := mul_le_mul hc (hg.bd u) (abs_nonneg _) hC
    linarith [hf.bd u]
  · have h1 : |(f s - c * g s) - (f t - c * g t)| ≤ |f s - f t| + |c| * |g s - g t| := by
      rw [← abs_mul, show (f s - c * g s) - (f t - c * g t) = (f s - f t) - c * (g s - g t) by ring]
      exact abs_sub_le' _ _
    have h2 : |c| * |g s - g t| ≤ C * (M' * |s - t|) := mul_le_mul hc (hg.lip s t hs ht) (abs_nonneg _) hC
    have h3 := hf.lip s t hs ht
    linarith

lemma good_legT (n : ℕ) : ∃ B M, Good B M (WeilPlanch.legT n) := by
  set φ : ℝ → ℝ := fun u => Real.sqrt (2 * n + 1) * Polynomial.aeval (u + 1 / 2) (Polynomial.shiftedLegendre n)
    with hφd
  have hφ : ContDiff ℝ 1 φ :=
    contDiff_const.mul ((Polynomial.contDiff_aeval _ _).comp (contDiff_id.add contDiff_const))
  have hc : Continuous φ := hφ.continuous
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.continuousOn (s := Icc (-(1/2):ℝ) (1/2)))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hdc.continuousOn (s := Icc (-(1/2):ℝ) (1/2)))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨by norm_num, by norm_num⟩)
  have hleg : ∀ u, WeilPlanch.legT n u = if |u| ≤ 1 / 2 then φ u else 0 := fun u => rfl
  refine ⟨B, M, ⟨?_, ?_, ?_, ?_⟩⟩
  · have : WeilPlanch.legT n = fun u => if |u| ≤ 1 / 2 then φ u else 0 := funext hleg
    rw [this]
    exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) hc.measurable
      measurable_const
  · intro u hu; rw [hleg, if_neg (by linarith)]
  · intro u; rw [hleg]; split_ifs with h
    · have := hB u (WeilGen.mem_Icc_of_abs h); rwa [Real.norm_eq_abs] at this
    · simpa using hB0
  · intro s t hs ht
    rw [hleg, hleg, if_pos hs, if_pos ht]
    have := (convex_Icc (-(1/2):ℝ) (1/2)).norm_image_sub_le_of_norm_deriv_le (f := φ) (fun x _ => hd x)
      (fun x hx => hM x hx) (WeilGen.mem_Icc_of_abs ht) (WeilGen.mem_Icc_of_abs hs)
    simpa [Real.norm_eq_abs] using this

/-! ## The correction onto `V'` -/

lemma iP_pos (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 < WeilTailB.iP n x := by
  unfold WeilTailB.iP
  apply mul_pos (by positivity)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (Continuous.intervalIntegrable (by fun_prop) _ _) _
    (by norm_num)
  intro t ht
  exact mul_pos (Real.cosh_pos _) (pow_pos (by nlinarith [ht.1, ht.2]) n)

lemma pole3_pos (n : ℕ) : 0 < V3Zhu.pole3 n := by
  rw [V3Pole.pole3_eq]
  exact mul_pos (Real.sqrt_pos.2 (by positivity)) (iP_pos n (by have := lam_pos; positivity))

noncomputable def c0 (g : ℝ → ℝ) : ℝ := P0 g
noncomputable def c1 (g : ℝ → ℝ) : ℝ := ((PR g + PL g) / 2 - P0 g * V3Zhu.pole3 0) / V3Zhu.pole3 2
noncomputable def c2 (g : ℝ → ℝ) : ℝ := ((PR g - PL g) / 2) / V3Zhu.pole3 1

/-- Subtract the three modes `T₀, T₂, T₁` with the coefficients that kill the functionals of `V'`. -/
noncomputable def corr (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  g u - c0 g * WeilPlanch.legT 0 u - c1 g * WeilPlanch.legT 2 u - c2 g * WeilPlanch.legT 1 u

noncomputable def xc (N : ℕ) (x y : ℕ → ℝ) (i : ℕ) : ℝ :=
  x i - (if i = 0 then c0 (WeilOdd.hx N x y) else 0) - (if i = 1 then c1 (WeilOdd.hx N x y) else 0)

noncomputable def yc (N : ℕ) (x y : ℕ → ℝ) (i : ℕ) : ℝ := y i - (if i = 0 then c2 (WeilOdd.hx N x y) else 0)

lemma corr_hx (N : ℕ) (hN : 2 ≤ N) (x y : ℕ → ℝ) :
    corr (WeilOdd.hx N x y) = WeilOdd.hx N (xc N x y) (yc N x y) := by
  funext u
  unfold corr xc yc
  generalize c0 (WeilOdd.hx N x y) = a
  generalize c1 (WeilOdd.hx N x y) = b
  generalize c2 (WeilOdd.hx N x y) = c
  unfold WeilOdd.hx WeilPlanch.fx WeilOdd.gx
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
    if_pos (show 0 < N by omega), if_pos (show 1 < N by omega)]
  norm_num
  ring

lemma corr_V (N : ℕ) (hN : 2 ≤ N) (x y : ℕ → ℝ) :
    xc N x y 0 = 0 ∧ ∑ i ∈ Finset.range N, xc N x y i * V3Zhu.pole3 (2 * i) = 0
      ∧ ∑ i ∈ Finset.range N, yc N x y i * V3Zhu.pole3 (2 * i + 1) = 0 := by
  have p2 := (pole3_pos 2).ne'
  have p1 := (pole3_pos 1).ne'
  have h0 := P0_hx N (by omega) x y
  have hR := PR_hx N x y
  have hL := PL_hx N x y
  refine ⟨?_, ?_, ?_⟩
  · unfold xc c0; rw [h0]; simp
  · unfold xc
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
      if_pos (show 0 < N by omega), if_pos (show 1 < N by omega)]
    unfold c0 c1
    rw [h0, hR, hL]
    norm_num
    field_simp
    ring
  · unfold yc
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
      if_pos (show 0 < N by omega)]
    unfold c2
    rw [hR, hL]
    norm_num
    field_simp
    ring

lemma hx_pad (N N' : ℕ) (h : N ≤ N') (x y : ℕ → ℝ) : WeilOdd.hx N x y
    = WeilOdd.hx N' (fun i => if i < N then x i else 0) (fun i => if i < N then y i else 0) := by
  funext u
  unfold WeilOdd.hx WeilPlanch.fx WeilOdd.gx
  have hs : Finset.range N ⊆ Finset.range N' := Finset.range_subset_range.2 h
  have z : ∀ i ∈ Finset.range N', i ∉ Finset.range N → ¬ i < N := fun i _ hi h => hi (Finset.mem_range.2 h)
  congr 1
  · rw [← Finset.sum_subset hs (fun i hi' hi => by simp [z i hi' hi])]
    exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.1 hi]
  · rw [← Finset.sum_subset hs (fun i hi' hi => by simp [z i hi' hi])]
    exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.1 hi]

/-! ## The limit -/

theorem coer_g {g : ℝ → ℝ} (hg : WeilGen.TestFn g) (hR : PR g = 0) (hL : PL g = 0) (h0 : P0 g = 0) :
    (4 / 10 ^ 4 : ℝ) * normSq (sc g) ≤ weilQg (V3Scale.lam / 2) (sc g) := by
  obtain ⟨B, M, gs, hgs, -, hlim, hp⟩ := WeilGen.approx hg
  have hmode : ∀ k, ∃ N x y, 28 ≤ N ∧ gs k = WeilOdd.hx N x y := by
    intro k
    obtain ⟨p, hpk⟩ := hp k
    obtain ⟨N, x, y, hxy⟩ := LegSpan.poly_hx p
    exact ⟨max N 28, _, _, le_max_right _ _, by rw [hpk, ← hxy]; exact hx_pad N (max N 28) (le_max_left _ _) x y⟩
  choose N x y hN hxy using hmode
  have tR : Tendsto (fun k => PR (gs k)) atTop (𝓝 0) := by rw [← hR]; exact tendsto_pole hgs hlim _
  have tL : Tendsto (fun k => PL (gs k)) atTop (𝓝 0) := by rw [← hL]; exact tendsto_pole hgs hlim _
  have t0 : Tendsto (fun k => P0 (gs k)) atTop (𝓝 0) := by rw [← h0]; exact tendsto_pole hgs hlim _
  have tc0 : Tendsto (fun k => c0 (gs k)) atTop (𝓝 0) := t0
  have tc1 : Tendsto (fun k => c1 (gs k)) atTop (𝓝 0) := by
    have := (((tR.add tL).div_const 2).sub (t0.mul_const (V3Zhu.pole3 0))).div_const (V3Zhu.pole3 2)
    simpa [c1] using this
  have tc2 : Tendsto (fun k => c2 (gs k)) atTop (𝓝 0) := by
    have := ((tR.sub tL).div_const 2).div_const (V3Zhu.pole3 1)
    simpa [c2] using this
  have bnd : ∀ {c : ℕ → ℝ}, Tendsto c atTop (𝓝 0) → ∃ C, ∀ k, |c k| ≤ C := by
    intro c hc
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hc)
    exact ⟨C, fun k => by have := hC _ ⟨k, rfl⟩; rwa [Real.norm_eq_abs] at this⟩
  obtain ⟨C0, hC0⟩ := bnd tc0
  obtain ⟨C1, hC1⟩ := bnd tc1
  obtain ⟨C2, hC2⟩ := bnd tc2
  obtain ⟨B0, M0, hT0⟩ := good_legT 0
  obtain ⟨B2, M2, hT2⟩ := good_legT 2
  obtain ⟨B1, M1, hT1⟩ := good_legT 1
  have hG : ∀ k, Good (B + C0 * B0 + C1 * B2 + C2 * B1) (M + C0 * M0 + C1 * M2 + C2 * M1) (corr (gs k)) :=
    fun k => good_lin _ (hC2 k) (good_lin _ (hC1 k) (good_lin _ (hC0 k) (hgs k) hT0) hT2) hT1
  have hlim' : ∀ t, Tendsto (fun k => corr (gs k) t) atTop (𝓝 (g t)) := by
    intro t
    have := (((hlim t).sub (tc0.mul_const (WeilPlanch.legT 0 t))).sub (tc1.mul_const (WeilPlanch.legT 2 t))).sub
      (tc2.mul_const (WeilPlanch.legT 1 t))
    simpa [corr] using this
  have hk : ∀ k, (4 / 10 ^ 4 : ℝ) * normSq (sc (corr (gs k))) ≤ weilQg (V3Scale.lam / 2) (sc (corr (gs k))) := by
    intro k
    rw [hxy k, corr_hx (N k) (by have := hN k; omega)]
    obtain ⟨h0', hA, hB⟩ := corr_V (N k) (by have := hN k; omega) (x k) (y k)
    refine V3Main.vprime_hx (N k) (hN k) _ _ ?_ ?_ ?_
    · rw [V3Pole.poleR_sc_hx, hA, hB]; ring
    · rw [V3Pole.poleL_sc_hx, hA, hB]; ring
    · rw [V3Pole.int_sc_hx _ (by have := hN k; omega), h0']; ring
  have lim1 := tendsto_weilQg_sc hG hg.2 hlim'
  have lim2 : Tendsto (fun k => (4 / 10 ^ 4 : ℝ) * normSq (sc (corr (gs k)))) atTop
      (𝓝 ((4 / 10 ^ 4) * normSq (sc g))) := by
    simp_rw [normSq_sc]; exact (tendsto_normSq hG hlim').const_mul _
  exact le_of_tendsto_of_tendsto' lim2 lim1 hk

/-! ## Every support `L ≤ log 3 / 2` -/

/-- **Connes–Consani's subspace `V'` at support `L`**: `∫ f e^{−u/2} = ∫ f e^{u/2} = ∫ f = 0` over `[−L, L]`. -/
def InVp (L : ℝ) (f : ℝ → ℝ) : Prop := poleR f L = 0 ∧ poleL f L = 0 ∧ ∫ u in (-L)..L, f u = 0

lemma int_shrink {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hs : ∀ u, L < |u| → φ u = 0) : ∫ u in (-a)..a, φ u = ∫ u in (-L)..L, φ u := by
  have i : ∀ p q : ℝ, IntervalIntegrable φ volume p q := fun p q => hφ.intervalIntegrable _ _
  have h1 : ∫ u in (-a)..(-L), φ u = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply integral_eq_zero_of_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(Set.countable_singleton (-L)).ae_notMem volume] with u hu hmem
    simp only [Set.mem_singleton_iff] at hu
    show φ u = 0
    have : u < -L := lt_of_le_of_ne hmem.2 hu
    exact hs u (by rw [abs_of_neg (by linarith)]; linarith)
  have h2 : ∫ u in L..a, φ u = 0 := by
    rw [intervalIntegral.integral_of_le ha]
    apply integral_eq_zero_of_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ fun u hmem => show φ u = 0 from
      hs u (by rw [abs_of_pos (by linarith [hmem.1])]; exact hmem.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals (i (-a) (-L)) (i (-L) a), h1, zero_add,
    ← intervalIntegral.integral_add_adjacent_intervals (i (-L) L) (i L a), h2, add_zero]

lemma weilQg_shrink {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) {f : ℝ → ℝ} (hf : Continuous f)
    (hs : ∀ u, L < |u| → f u = 0) : weilQg a f = weilQg L f := by
  unfold weilQg poleR poleL
  rw [int_shrink (φ := fun u => f u * Real.exp (-(u / 2))) hL ha (by fun_prop)
      (fun u hu => by rw [hs u hu, zero_mul]),
    int_shrink (φ := fun u => f u * Real.exp (u / 2)) hL ha (by fun_prop)
      (fun u hu => by rw [hs u hu, zero_mul])]

theorem coer_Lstar {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hs : ∀ u, V3Scale.lam / 2 < |u| → f u = 0)
    (hV : InVp (V3Scale.lam / 2) f) : (4 / 10 ^ 4 : ℝ) * normSq f ≤ weilQg (V3Scale.lam / 2) f := by
  set g : ℝ → ℝ := fun v => f (V3Scale.lam * v) * Real.sqrt V3Scale.lam with hgdef
  have hl := lam_pos
  have hs2 := sqrt_lam_pos
  have hfg : sc g = f := by
    funext u; simp only [sc, hgdef]; rw [mul_div_cancel₀ u hl.ne']; field_simp
  have hg : WeilGen.TestFn g := by
    refine ⟨(hf.comp (contDiff_const.mul contDiff_id)).mul contDiff_const, fun v hv => ?_⟩
    simp only [hgdef]
    rw [hs (V3Scale.lam * v) (by rw [abs_mul, abs_of_pos hl]; nlinarith), zero_mul]
  obtain ⟨hR, hL, hI⟩ := hV
  rw [← hfg] at hR hL hI ⊢
  rw [poleR_scP] at hR; rw [poleL_scP] at hL; rw [int_scP] at hI
  exact coer_g hg ((mul_eq_zero.1 hR).resolve_left hs2.ne') ((mul_eq_zero.1 hL).resolve_left hs2.ne')
    ((mul_eq_zero.1 hI).resolve_left hs2.ne')

/-- **Weil positivity on `V'` at every support `L ≤ log 3 / 2`, with a coercivity constant**: for `f` of class
`C¹`, zero outside `[−L, L]`, with `∫ f e^{−u/2} = ∫ f e^{u/2} = ∫ f = 0`, `weilQg L f ≥ 4·10⁻⁴ ‖f‖²`. -/
theorem coer_vprime {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ Real.log 3 / 2) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hs : ∀ u, L < |u| → f u = 0) (hV : InVp L f) : (4 / 10 ^ 4 : ℝ) * normSq f ≤ weilQg L f := by
  have hc := hf.continuous
  have ha : L ≤ V3Scale.lam / 2 := hL
  have hs' : ∀ u, V3Scale.lam / 2 < |u| → f u = 0 := fun u hu => hs u (by linarith)
  obtain ⟨hR, hLp, hI⟩ := hV
  have hV' : InVp (V3Scale.lam / 2) f := by
    refine ⟨?_, ?_, ?_⟩
    · unfold poleR at hR ⊢
      rw [int_shrink (φ := fun u => f u * Real.exp (-(u / 2))) hL0 ha (by fun_prop)
        (fun u hu => by rw [hs u hu, zero_mul])]; exact hR
    · unfold poleL at hLp ⊢
      rw [int_shrink (φ := fun u => f u * Real.exp (u / 2)) hL0 ha (by fun_prop)
        (fun u hu => by rw [hs u hu, zero_mul])]; exact hLp
    · rw [int_shrink hL0 ha hc hs]; exact hI
  rw [← weilQg_shrink hL0 ha hc hs]
  exact coer_Lstar hf hs' hV'

lemma normSq_pos' {L : ℝ} {f : ℝ → ℝ} (hc : Continuous f) (hs : ∀ u, L < |u| → f u = 0) (hne : f ≠ 0) :
    0 < normSq f := by
  obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by by_contra h; push Not at h; exact hne (funext h)
  unfold normSq
  have hc2 : Continuous fun t => f t ^ 2 := hc.pow 2
  refine hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := u) ?_ (fun t => sq_nonneg _) (pow_ne_zero 2 hu)
  refine HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun t ht => ?_
  have : L < |t| := by
    by_contra h; push Not at h
    exact ht ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  simp [hs t this]

/-- **Strict positivity on `V'`**, `L ≤ log 3 / 2`: `weilQg L f > 0` for every nonzero such `f`. -/
theorem pos_vprime {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ Real.log 3 / 2) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hs : ∀ u, L < |u| → f u = 0) (hV : InVp L f) (hne : f ≠ 0) : 0 < weilQg L f := by
  have h1 := coer_vprime hL0 hL hf hs hV
  have h2 := normSq_pos' hf.continuous hs hne
  nlinarith

end V3Gen
