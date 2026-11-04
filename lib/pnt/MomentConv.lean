import Mathlib

/-!
# Method of moments on `ℝ` (milestone B1, unconditional)

`MomentConv.tendsto_of_moments`: if all moments of a sequence of probability measures converge to those of a
probability measure `ν` with `∫ e^{s|x|} dν < ∞` (`s > 0`), the sequence converges weakly to `ν`.
Proof: bounded second moments give tightness (`MomentConv.tight`), Prokhorov gives a convergent subsequence,
limit moments pass to the limit (`MomentConv.moment_tendsto`), exponential integrability transfers
(`MomentConv.integrable_exp_of_moments`) and the analytic mgf pins the limit (`MomentConv.ext_of_moments`).
-/

namespace MomentConv
open MeasureTheory ProbabilityTheory Complex Filter Topology Set

theorem Ioo_subset_interior {μ : Measure ℝ} {s : ℝ}
    (h : Integrable (fun x => Real.exp (s * |x|)) μ) :
    Ioo (-s) s ⊆ interior (integrableExpSet id μ) := by
  apply interior_maximal _ isOpen_Ioo
  intro t ht
  simp only [integrableExpSet, mem_ofPred_eq, id_eq]
  refine h.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  have := neg_abs_le x; have := le_abs_self x
  rcases le_total 0 t with h0 | h0 <;> nlinarith [ht.1, ht.2, abs_nonneg x]

/-- **Determinacy by moments.** Two probability measures on `ℝ` with `∫ e^{s|x|} < ∞` for some `s > 0` and the same
moments are equal. -/
theorem ext_of_moments {ρ ν : Measure ℝ} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] {s : ℝ} (hs : 0 < s)
    (hρ : Integrable (fun x => Real.exp (s * |x|)) ρ) (hν : Integrable (fun x => Real.exp (s * |x|)) ν)
    (hm : ∀ n : ℕ, ∫ x, x ^ n ∂ρ = ∫ x, x ^ n ∂ν) : ρ = ν := by
  set T : Set ℂ := {z | z.re ∈ Ioo (-s) s}
  have hTρ : T ⊆ {z | z.re ∈ interior (integrableExpSet id ρ)} := fun z hz => Ioo_subset_interior hρ hz
  have hTν : T ⊆ {z | z.re ∈ interior (integrableExpSet id ν)} := fun z hz => Ioo_subset_interior hν hz
  have hF : AnalyticOnNhd ℂ (complexMGF id ρ) T := analyticOnNhd_complexMGF.mono hTρ
  have hG : AnalyticOnNhd ℂ (complexMGF id ν) T := analyticOnNhd_complexMGF.mono hTν
  have hball : Metric.ball (0:ℂ) s ⊆ T := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have := abs_re_le_norm z
    simp only [T, mem_ofPred_eq, mem_Ioo]; constructor <;> linarith [abs_le.1 this]
  have h0T : (0:ℂ) ∈ T := hball (Metric.mem_ball_self hs)
  have hder : ∀ n, iteratedDeriv n (complexMGF id ρ) 0 = iteratedDeriv n (complexMGF id ν) 0 := by
    intro n
    rw [iteratedDeriv_complexMGF (hTρ h0T), iteratedDeriv_complexMGF (hTν h0T)]
    simp only [zero_mul, Complex.exp_zero, mul_one, id_eq]
    have e : ∀ μ : Measure ℝ, ∫ x, (x : ℂ) ^ n ∂μ = ((∫ x, x ^ n ∂μ : ℝ) : ℂ) := by
      intro μ
      rw [show (fun x : ℝ => (x : ℂ) ^ n) = fun x => ((x ^ n : ℝ) : ℂ) by funext x; push_cast; rfl,
        integral_complex_ofReal]
    rw [e, e, hm]
  have hev : complexMGF id ρ =ᶠ[𝓝 0] complexMGF id ν := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hs] with z hz
    rw [← taylorSeries_eq_on_ball' hz (fun w hw => (hF w (hball hw)).differentiableAt.differentiableWithinAt),
      ← taylorSeries_eq_on_ball' hz (fun w hw => (hG w (hball hw)).differentiableAt.differentiableWithinAt)]
    simp only [hder]
  have hconv : IsPreconnected T := by
    have : T = (reLm : ℂ →ₗ[ℝ] ℝ) ⁻¹' Ioo (-s) s := rfl
    rw [this]; exact ((convex_Ioo _ _).linear_preimage _).isPreconnected
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG hconv h0T hev
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  apply heq
  simp [T, hs, neg_lt_zero.2 hs]

open scoped Nat ENNReal BoundedContinuousFunction

theorem even_pow_nonneg (y : ℝ) (k : ℕ) : 0 ≤ y ^ (2 * k) := by
  rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _

/-- `∫⁻ cosh(sx) = Σ s^{2k}/(2k)! ∫ x^{2k}`. -/
theorem lintegral_cosh (π : Measure ℝ) (s : ℝ) (hi : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ (2 * k)) π) :
    ∫⁻ x, ENNReal.ofReal (Real.cosh (s * x)) ∂π =
      ∑' k : ℕ, ENNReal.ofReal (s ^ (2 * k) / (2 * k)! * ∫ x, x ^ (2 * k) ∂π) := by
  have hnn : ∀ (y : ℝ) (k : ℕ), 0 ≤ y ^ (2 * k) / ((2 * k)! : ℝ) := fun y k =>
    div_nonneg (even_pow_nonneg y k) (by positivity)
  have hterm : ∀ x : ℝ, ENNReal.ofReal (Real.cosh (s * x)) =
      ∑' k : ℕ, ENNReal.ofReal ((s * x) ^ (2 * k) / (2 * k)!) := by
    intro x
    rw [← ENNReal.ofReal_tsum_of_nonneg (hnn _) (Real.hasSum_cosh _).summable, (Real.hasSum_cosh _).tsum_eq]
  simp_rw [hterm]
  rw [lintegral_tsum (fun k => by fun_prop)]
  congr 1; funext k
  have hf : ∀ x : ℝ, (s * x) ^ (2 * k) / ((2 * k)! : ℝ) = s ^ (2 * k) / (2 * k)! * x ^ (2 * k) := by
    intro x; rw [mul_pow]; ring
  simp_rw [hf]
  rw [← ofReal_integral_eq_lintegral_ofReal ((hi k).const_mul _)
    (Eventually.of_forall fun x => mul_nonneg (hnn s k) (even_pow_nonneg x k)), integral_const_mul]

theorem cosh_le_exp_abs (y : ℝ) : Real.cosh y ≤ Real.exp |y| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.2 (le_abs_self y)
  have h2 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.2 (neg_le_abs y)
  linarith

theorem exp_abs_le_two_cosh (y : ℝ) : Real.exp |y| ≤ 2 * Real.cosh y := by
  rw [Real.cosh_eq]
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-y)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos y]

/-- Exponential integrability passes to a measure with the same even moments. -/
theorem integrable_exp_of_moments {ρ ν : Measure ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hρi : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ (2 * k)) ρ) (hνi : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ (2 * k)) ν)
    (hm : ∀ k : ℕ, ∫ x, x ^ (2 * k) ∂ρ = ∫ x, x ^ (2 * k) ∂ν)
    (hν : Integrable (fun x => Real.exp (s * |x|)) ν) : Integrable (fun x => Real.exp (s * |x|)) ρ := by
  have habs : ∀ x : ℝ, s * |x| = |s * x| := fun x => by rw [abs_mul, abs_of_nonneg hs]
  have hνc : ∫⁻ x, ENNReal.ofReal (Real.cosh (s * x)) ∂ν < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) hν.lintegral_lt_top
    rw [habs]; exact cosh_le_exp_abs _
  have hρc : ∫⁻ x, ENNReal.ofReal (Real.cosh (s * x)) ∂ρ < ∞ := by
    rw [lintegral_cosh ρ s hρi]; rw [lintegral_cosh ν s hνi] at hνc
    simp_rw [hm]; exact hνc
  have hcρ : Integrable (fun x => 2 * Real.cosh (s * x)) ρ := by
    refine Integrable.const_mul ⟨by fun_prop, ?_⟩ 2
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.cosh_pos _).le)]
    exact hρc
  refine hcρ.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), habs]
  exact exp_abs_le_two_cosh _

/-- **Tightness** from a uniform bound on second moments. -/
theorem tight (μ : ℕ → ProbabilityMeasure ℝ) (C : ℝ)
    (h2 : ∀ n, Integrable (fun x : ℝ => x ^ 2) (μ n : Measure ℝ))
    (hC : ∀ n, ∫ x, x ^ 2 ∂(μ n : Measure ℝ) ≤ C) :
    IsTightMeasureSet {((m : ProbabilityMeasure ℝ) : Measure ℝ) | m ∈ range μ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, fun _ _ => by simp [htop]⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  set t := (|C| + 1) / ε.toReal with htdef
  have ht : 0 < t := by positivity
  refine ⟨Icc (-Real.sqrt t) (Real.sqrt t), isCompact_Icc, ?_⟩
  rintro m ⟨_, ⟨n, rfl⟩, rfl⟩
  have hsub : (Icc (-Real.sqrt t) (Real.sqrt t))ᶜ ⊆ {x : ℝ | t ≤ x ^ 2} := by
    intro x hx
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    show t ≤ x ^ 2
    rcases hx with hx | hx
    · have := Real.lt_sq_of_sqrt_lt (show Real.sqrt t < -x by linarith)
      nlinarith
    · exact (Real.lt_sq_of_sqrt_lt hx).le
  have hch := mul_meas_ge_le_integral_of_nonneg (μ := (μ n : Measure ℝ))
    (Eventually.of_forall fun x => sq_nonneg x) (h2 n) t
  have hreal : (μ n : Measure ℝ).real {x : ℝ | t ≤ x ^ 2} ≤ ε.toReal := by
    have h1 : t * (μ n : Measure ℝ).real {x : ℝ | t ≤ x ^ 2} ≤ |C| := (hch.trans (hC n)).trans (le_abs_self C)
    have hte : t * ε.toReal = |C| + 1 := by rw [htdef]; field_simp
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon ht
    linarith
  calc (μ n : Measure ℝ) (Icc (-Real.sqrt t) (Real.sqrt t))ᶜ ≤ (μ n : Measure ℝ) {x : ℝ | t ≤ x ^ 2} :=
        measure_mono hsub
    _ = ENNReal.ofReal ((μ n : Measure ℝ).real {x : ℝ | t ≤ x ^ 2}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hreal
    _ = ε := ENNReal.ofReal_toReal htop

theorem iSup_ofReal_min {a : ℝ} (_ha : 0 ≤ a) : ⨆ M : ℕ, ENNReal.ofReal (min a M) = ENNReal.ofReal a :=
  le_antisymm (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    (le_iSup_of_le ⌈a⌉₊ (by rw [min_eq_left (Nat.le_ceil a)]))

/-- The truncation `min(x^{2k}, M)` as a bounded continuous function. -/
noncomputable def trunc (k M : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => min (x ^ (2 * k)) M, by fun_prop⟩ M (by
    intro x y
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    have h1 := even_pow_nonneg x k; have h2 := even_pow_nonneg y k
    have h3 : (0:ℝ) ≤ M := Nat.cast_nonneg M
    rw [abs_le]; constructor <;>
      linarith [min_le_right (x ^ (2 * k)) (M:ℝ), min_le_right (y ^ (2 * k)) (M:ℝ),
        le_min h1 h3, le_min h2 h3])

/-- Even moments pass to weak limits as bounds. -/
theorem even_moment_limit {μ : ℕ → ProbabilityMeasure ℝ} {ρ : ProbabilityMeasure ℝ}
    (h : Tendsto μ atTop (𝓝 ρ)) (k : ℕ) (C : ℝ)
    (hi : ∀ n, Integrable (fun x : ℝ => x ^ (2 * k)) (μ n : Measure ℝ))
    (hC : ∀ n, ∫ x, x ^ (2 * k) ∂(μ n : Measure ℝ) ≤ C) :
    Integrable (fun x : ℝ => x ^ (2 * k)) (ρ : Measure ℝ) ∧ ∫ x, x ^ (2 * k) ∂(ρ : Measure ℝ) ≤ C := by
  have hC0 : 0 ≤ C := (integral_nonneg fun x => even_pow_nonneg x k).trans (hC 0)
  have hM : ∀ M : ℕ, ∫ x, trunc k M x ∂(ρ : Measure ℝ) ≤ C := by
    intro M
    refine le_of_tendsto' ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h) (trunc k M))
      fun n => ?_
    refine (integral_mono ((trunc k M).integrable _) (hi n) fun x => ?_).trans (hC n)
    exact min_le_left _ _
  have hlint : ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(ρ : Measure ℝ) ≤ ENNReal.ofReal C := by
    have e : ∀ x : ℝ, ENNReal.ofReal (x ^ (2 * k)) = ⨆ M : ℕ, ENNReal.ofReal (trunc k M x) := by
      intro x; rw [← iSup_ofReal_min (even_pow_nonneg x k)]; rfl
    simp_rw [e]
    rw [lintegral_iSup (f := fun M x => ENNReal.ofReal (trunc k M x))
      (fun M => (trunc k M).continuous.measurable.ennreal_ofReal)
      (fun M M' hMM x => ENNReal.ofReal_le_ofReal
        (show min (x ^ (2 * k)) (M:ℝ) ≤ min (x ^ (2 * k)) (M':ℝ) from
          min_le_min_left _ (by exact_mod_cast hMM)))]
    refine iSup_le fun M => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal ((trunc k M).integrable _)
      (Eventually.of_forall fun x => le_min (even_pow_nonneg x k) (Nat.cast_nonneg M))]
    exact ENNReal.ofReal_le_ofReal (hM M)
  have hint : Integrable (fun x : ℝ => x ^ (2 * k)) (ρ : Measure ℝ) := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => even_pow_nonneg x k)]
    exact hlint.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => even_pow_nonneg x k) (by fun_prop)]
  exact ENNReal.toReal_le_of_le_ofReal hC0 hlint

/-- `x^k` is integrable when `x^{2k}` is, for a finite measure. -/
theorem integrable_pow_of_even {π : Measure ℝ} [IsFiniteMeasure π] (k : ℕ)
    (h : Integrable (fun x : ℝ => x ^ (2 * k)) π) : Integrable (fun x : ℝ => x ^ k) π := by
  refine (h.add (integrable_const 1)).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  have e : |x| ^ k * |x| ^ k = x ^ (2 * k) := by
    rw [← pow_add, ← two_mul, (even_two_mul k).pow_abs]
  simp only [Pi.add_apply]
  nlinarith [pow_nonneg (abs_nonneg x) k]

/-- The clamp `max (-R) (min x R)`. -/
noncomputable def clamp (R x : ℝ) : ℝ := max (-R) (min x R)

theorem abs_clamp {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clamp R x| ≤ R := by
  unfold clamp; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem pow_clamp_err {R : ℝ} (hR : 0 < R) (k : ℕ) (x : ℝ) :
    |x ^ k - clamp R x ^ k| ≤ 2 * x ^ (2 * k) / R ^ k := by
  have hRk : 0 < R ^ k := pow_pos hR k
  have e : |x| ^ k * |x| ^ k = x ^ (2 * k) := by
    rw [← pow_add, ← two_mul, (even_two_mul k).pow_abs]
  by_cases h : |x| ≤ R
  · have : clamp R x = x := by
      unfold clamp; rw [abs_le] at h
      rw [min_eq_left h.2, max_eq_right h.1]
    rw [this, sub_self, abs_zero]
    exact div_nonneg (by linarith [even_pow_nonneg x k]) hRk.le
  · push Not at h
    have h1 : |x ^ k - clamp R x ^ k| ≤ |x| ^ k + R ^ k := by
      refine (abs_sub _ _).trans ?_
      rw [abs_pow, abs_pow]
      exact add_le_add le_rfl (pow_le_pow_left₀ (abs_nonneg _) (abs_clamp hR.le x) k)
    have h2 : R ^ k ≤ |x| ^ k := pow_le_pow_left₀ hR.le h.le k
    rw [le_div_iff₀ hRk]
    nlinarith [pow_nonneg (abs_nonneg x) k]

/-- `clamp(x)^k` as a bounded continuous function. -/
noncomputable def fR (R : ℝ) (hR : 0 ≤ R) (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => clamp R x ^ k, by unfold clamp; fun_prop⟩ (2 * R ^ k) (by
    intro x y
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    refine (abs_sub _ _).trans ?_
    rw [abs_pow, abs_pow]
    have := pow_le_pow_left₀ (abs_nonneg _) (abs_clamp hR x) k
    have := pow_le_pow_left₀ (abs_nonneg _) (abs_clamp hR y) k
    linarith)

theorem err_integral (π : Measure ℝ) [IsProbabilityMeasure π] {R : ℝ} (hR : 0 < R) (k : ℕ)
    (h2k : Integrable (fun x : ℝ => x ^ (2 * k)) π) :
    |∫ x, x ^ k ∂π - ∫ x, fR R hR.le k x ∂π| ≤ 2 * (∫ x, x ^ (2 * k) ∂π) / R ^ k := by
  have hk := integrable_pow_of_even k h2k
  rw [← integral_sub hk ((fR R hR.le k).integrable π)]
  refine (abs_integral_le_integral_abs).trans ?_
  have : ∫ x, 2 * x ^ (2 * k) / R ^ k ∂π = 2 * (∫ x, x ^ (2 * k) ∂π) / R ^ k := by
    rw [integral_div, integral_const_mul]
  rw [← this]
  exact integral_mono (hk.sub ((fR R hR.le k).integrable π)).abs ((h2k.const_mul 2).div_const _)
    fun x => pow_clamp_err hR k x

/-- **Moments along a weakly convergent sequence** with bounded `2k`-th moments. -/
theorem moment_tendsto {μ : ℕ → ProbabilityMeasure ℝ} {ρ : ProbabilityMeasure ℝ}
    (h : Tendsto μ atTop (𝓝 ρ)) (k : ℕ) (C : ℝ)
    (hi : ∀ n, Integrable (fun x : ℝ => x ^ (2 * k)) (μ n : Measure ℝ))
    (hC : ∀ n, ∫ x, x ^ (2 * k) ∂(μ n : Measure ℝ) ≤ C) :
    Integrable (fun x : ℝ => x ^ k) (ρ : Measure ℝ) ∧
      Tendsto (fun n => ∫ x, x ^ k ∂(μ n : Measure ℝ)) atTop (𝓝 (∫ x, x ^ k ∂(ρ : Measure ℝ))) := by
  obtain ⟨hρi, hρC⟩ := even_moment_limit h k C hi hC
  refine ⟨integrable_pow_of_even k hρi, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hC0 : 0 ≤ C := (integral_nonneg fun x => even_pow_nonneg x k).trans (hC 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R := max 1 (8 * (C + 1) / ε) with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have hRk : R ≤ R ^ k := le_self_pow₀ hR1 hk.ne'
  have hsmall : 2 * C / R ^ k < ε / 4 := by
    have h8 : 8 * (C + 1) / ε ≤ R := le_max_right _ _
    rw [div_le_iff₀ hε] at h8
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h) (fR R hR0.le k)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hw (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have e1 := err_integral (μ n : Measure ℝ) hR0 k (hi n)
  have e2 := err_integral (ρ : Measure ℝ) hR0 k hρi
  have e3 := hN n hn
  rw [Real.dist_eq] at e3 ⊢
  have b1 : 2 * (∫ x, x ^ (2 * k) ∂(μ n : Measure ℝ)) / R ^ k ≤ 2 * C / R ^ k := by
    gcongr; exact hC n
  have b2 : 2 * (∫ x, x ^ (2 * k) ∂(ρ : Measure ℝ)) / R ^ k ≤ 2 * C / R ^ k := by
    gcongr
  have t1 := abs_sub_le (∫ x, x ^ k ∂(μ n : Measure ℝ)) (∫ x, fR R hR0.le k x ∂(μ n : Measure ℝ))
    (∫ x, x ^ k ∂(ρ : Measure ℝ))
  have t2 := abs_sub_le (∫ x, fR R hR0.le k x ∂(μ n : Measure ℝ)) (∫ x, fR R hR0.le k x ∂(ρ : Measure ℝ))
    (∫ x, x ^ k ∂(ρ : Measure ℝ))
  rw [abs_sub_comm (∫ x, fR R hR0.le k x ∂(ρ : Measure ℝ))] at t2
  linarith

/-- **Method of moments (B1, unconditional).** If every moment of `μ n` converges to the corresponding moment
of a probability measure `ν` with `∫ e^{s|x|} dν < ∞` for some `s > 0`, then `μ n → ν` weakly. -/
theorem tendsto_of_moments (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hi : ∀ n k, Integrable (fun x : ℝ => x ^ k) (μ n : Measure ℝ))
    (hνi : ∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ))
    (hm : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μ n : Measure ℝ)) atTop (𝓝 (∫ x, x ^ k ∂(ν : Measure ℝ))))
    {s : ℝ} (hs : 0 < s) (hνe : Integrable (fun x => Real.exp (s * |x|)) (ν : Measure ℝ)) :
    Tendsto μ atTop (𝓝 ν) := by
  choose C hC using fun k => (hm (2 * k)).bddAbove_range
  have hb : ∀ k n, ∫ x, x ^ (2 * k) ∂(μ n : Measure ℝ) ≤ C k := fun k n => hC k ⟨n, rfl⟩
  have hK := isCompact_closure_of_isTightMeasureSet (S := range μ)
    (tight μ (C 1) (fun n => hi n 2) (fun n => by simpa using hb 1 n))
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ρ, -, g, hg, hρ⟩ := hK.isSeqCompact (x := μ ∘ ns) (fun n => subset_closure ⟨ns n, rfl⟩)
  refine ⟨g, ?_⟩
  suffices hρν : ρ = ν by subst hρν; exact hρ
  have hlim : ∀ k, ∫ x, x ^ k ∂(ρ : Measure ℝ) = ∫ x, x ^ k ∂(ν : Measure ℝ) := fun k =>
    tendsto_nhds_unique (moment_tendsto hρ k (C k) (fun n => hi _ _) (fun n => hb k _)).2
      ((hm k).comp (hns.comp hg.tendsto_atTop))
  have hρi : ∀ k, Integrable (fun x : ℝ => x ^ (2 * k)) (ρ : Measure ℝ) := fun k =>
    (even_moment_limit hρ k (C k) (fun n => hi _ _) (fun n => hb k _)).1
  have : IsProbabilityMeasure (ρ : Measure ℝ) := ρ.prop
  have : IsProbabilityMeasure (ν : Measure ℝ) := ν.prop
  exact Subtype.ext (ext_of_moments (ρ := (ρ : Measure ℝ)) (ν := (ν : Measure ℝ)) hs
    (integrable_exp_of_moments hs.le hρi (fun k => hνi (2 * k)) (fun k => hlim _) hνe) hνe hlim)

end MomentConv
