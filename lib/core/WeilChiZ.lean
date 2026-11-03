import Mathlib
import WeilChi

/-!
# `Ξ_χ` with a zero at the centre

For a primitive real `χ ≠ 1` (`PsiOmega.RealChar`, no hypothesis on `L(½, χ)`), let `m` be the order of `Ξ_χ` at `0`
(`PsiOmega.mC`, the order of `L(s, χ)` at `s = ½`). Then `Ξ_χ(t) = t^m Y(t)` with `Y` entire, `Y(0) ≠ 0`
(`PsiOmega.YC`, `PsiOmega.XiC_eq_pow_mul`). The functional equation `Ξ_χ(−t) = εΞ_χ(t)` forces `ε = (−1)^m`
(`PsiOmega.rootNumber_eq_neg_one_pow`), so `Y` is even (`PsiOmega.YC_even`) whatever the root number is, and `Y` has
Hadamard's product (`PsiOmega.hadamard_YC`). Unconditional. See `formalisations/d2-density.md`.
-/

open Real Complex MeasureTheory Filter Topology Set

noncomputable section

namespace PsiOmega

open LandauLaplace DirichletCharacter WeilForm WeilTest WeilStrip

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- A primitive real character `χ ≠ 1`, with no hypothesis on `L(½, χ)`. -/
structure RealChar (χ : DirichletCharacter ℂ N) : Prop where
  ne_one : χ ≠ 1
  quad : χ.IsQuadratic
  prim : χ.IsPrimitive

/-- The order of `Ξ_χ` at `0`. -/
def mC (χ : DirichletCharacter ℂ N) : ℕ := analyticOrderNatAt (XiC χ) 0

/-- `Y(t) = Ξ_χ(t)/t^m`, continued to `t = 0`. -/
def YC (χ : DirichletCharacter ℂ N) (t : ℂ) : ℂ :=
  if t = 0 then limUnder (𝓝[≠] (0 : ℂ)) (fun z => XiC χ z / z ^ mC χ) else XiC χ t / t ^ mC χ

variable (hR : RealChar χ)
include hR

theorem differentiable_XiC' : Differentiable ℂ (XiC χ) :=
  (differentiable_LamG hR.ne_one).comp ((differentiable_const _).add
    ((differentiable_const _).mul differentiable_id))

theorem XiC_negI_ne : XiC χ (-I) ≠ 0 := by
  unfold XiC
  refine LamG_ne_zero_of_one_le_re hR.ne_one ?_
  simp

theorem order_XiC_ne_top : analyticOrderAt (XiC χ) 0 ≠ ⊤ := by
  have hA : AnalyticOnNhd ℂ (XiC χ) univ := fun t _ => (differentiable_XiC' hR).analyticAt t
  refine hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ (-I)) (mem_univ 0) ?_
  rw [analyticOrderAt_eq_zero.2 (Or.inr (XiC_negI_ne hR))]; simp

theorem exists_fac : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧
    ∀ᶠ z in 𝓝 (0 : ℂ), XiC χ z = z ^ mC χ * g z := by
  obtain ⟨g, hg, hg0, he⟩ := ((differentiable_XiC' hR).analyticAt 0).analyticOrderAt_eq_natCast.1
    (Nat.cast_analyticOrderNatAt (order_XiC_ne_top hR)).symm
  exact ⟨g, hg, hg0, he.mono fun z hz => by rw [hz, sub_zero, smul_eq_mul]; rfl⟩

theorem YC_spec : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧ YC χ =ᶠ[𝓝 0] g ∧
    ∀ᶠ z in 𝓝 (0 : ℂ), XiC χ z = z ^ mC χ * g z := by
  obtain ⟨g, hg, hg0, he⟩ := exists_fac hR
  have hpunct : ∀ᶠ z in 𝓝[≠] (0 : ℂ), XiC χ z / z ^ mC χ = g z := by
    filter_upwards [nhdsWithin_le_nhds he, self_mem_nhdsWithin] with z hz hz0
    rw [hz]; field_simp [pow_ne_zero _ (hz0 : z ≠ 0)]
  have hlim : limUnder (𝓝[≠] (0 : ℂ)) (fun z => XiC χ z / z ^ mC χ) = g 0 :=
    (tendsto_nhdsWithin_of_tendsto_nhds hg.continuousAt.tendsto |>.congr' (hpunct.mono fun z hz => hz.symm)).limUnder_eq
  refine ⟨g, hg, hg0, ?_, he⟩
  filter_upwards [he] with z hz
  by_cases hz0 : z = 0
  · subst hz0; simp [YC, hlim]
  · simp only [YC, hz0, ite_false]; rw [hz]; field_simp [pow_ne_zero _ hz0]

theorem YC_zero_ne : YC χ 0 ≠ 0 := by
  obtain ⟨g, -, hg0, hY, -⟩ := YC_spec hR
  rw [hY.eq_of_nhds]; exact hg0

theorem XiC_eq_pow_mul (t : ℂ) : XiC χ t = t ^ mC χ * YC χ t := by
  by_cases ht : t = 0
  · subst ht
    obtain ⟨g, -, -, hY, he⟩ := YC_spec hR
    rw [he.self_of_nhds, hY.eq_of_nhds]
  · simp only [YC, ht, ite_false]; field_simp [pow_ne_zero _ ht]

theorem differentiable_YC : Differentiable ℂ (YC χ) := by
  intro t
  by_cases ht : t = 0
  · subst ht
    obtain ⟨g, hg, -, hY, -⟩ := YC_spec hR
    exact hg.differentiableAt.congr_of_eventuallyEq hY
  · have he : YC χ =ᶠ[𝓝 t] fun z => XiC χ z / z ^ mC χ := by
      filter_upwards [isOpen_ne.mem_nhds ht] with z hz
      simp [YC, hz]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ he
    exact ((differentiable_XiC' hR) t).div (differentiableAt_pow _) (pow_ne_zero _ ht)

theorem XiC_neg (t : ℂ) : XiC χ (-t) = rootNumber χ * XiC χ t := by
  unfold XiC
  rw [show 1 / 2 + I * -t = 1 - (1 / 2 + I * t) by ring, LamG_one_sub hR.quad hR.prim]

theorem YC_neg_aux (t : ℂ) : (-1) ^ mC χ * YC χ (-t) = rootNumber χ * YC χ t := by
  have key : ∀ z : ℂ, z ≠ 0 → (-1) ^ mC χ * YC χ (-z) = rootNumber χ * YC χ z := by
    intro z hz
    have h := XiC_neg hR z
    rw [XiC_eq_pow_mul hR, XiC_eq_pow_mul hR, neg_pow] at h
    have hz' : z ^ mC χ ≠ 0 := pow_ne_zero _ hz
    apply mul_left_cancel₀ hz'
    linear_combination h
  by_cases ht : t = 0
  · subst ht
    have hc : Continuous fun z => (-1) ^ mC χ * YC χ (-z) - rootNumber χ * YC χ z :=
      (continuous_const.mul ((differentiable_YC hR).continuous.comp continuous_neg)).sub
        (continuous_const.mul (differentiable_YC hR).continuous)
    have h1 : Tendsto (fun z => (-1) ^ mC χ * YC χ (-z) - rootNumber χ * YC χ z) (𝓝[≠] (0 : ℂ))
        (𝓝 ((-1) ^ mC χ * YC χ (-0) - rootNumber χ * YC χ 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto 0)
    have h2 : Tendsto (fun z => (-1) ^ mC χ * YC χ (-z) - rootNumber χ * YC χ z) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z hz => by
        simp only; rw [key z hz, sub_self])
    have := tendsto_nhds_unique h1 h2
    exact sub_eq_zero.1 this
  · exact key t ht

/-- **The root number is `(−1)^m`.** -/
theorem rootNumber_eq_neg_one_pow : rootNumber χ = (-1) ^ mC χ := by
  have h := YC_neg_aux hR 0
  rw [neg_zero] at h
  have h0 := YC_zero_ne hR
  exact (mul_right_cancel₀ h0 h).symm

/-- **`Y` is even.** -/
theorem YC_even (t : ℂ) : YC χ (-t) = YC χ t := by
  have h := YC_neg_aux hR t
  rw [rootNumber_eq_neg_one_pow hR] at h
  have h1 : ((-1 : ℂ) ^ mC χ) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ h1 h

theorem norm_rootNumber : ‖rootNumber χ‖ = 1 := by
  rw [rootNumber_eq_neg_one_pow hR, norm_pow, norm_neg, norm_one, one_pow]

theorem norm_XiC_le' (t : ℂ) : ‖XiC χ t‖ ≤ KC χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := by
  have hf := norm_fG_le hR.ne_one hR.quad hR.prim t
  rw [fG_eq hR.quad hR.prim, norm_mul, norm_rootNumber hR, one_mul, norm_pow] at hf
  have he := Real.one_le_exp (show (0 : ℝ) ≤ 36 * ‖t‖ ^ (3 / 2 : ℝ) by positivity)
  have hK : 1 ≤ KC χ := one_le_KC
  change ‖XiC χ t‖ ^ 2 ≤ _ at hf
  rcases le_total ‖XiC χ t‖ 1 with h | h
  · nlinarith
  · have : ‖XiC χ t‖ ≤ ‖XiC χ t‖ ^ 2 := by nlinarith
    unfold KC at hK ⊢
    rw [norm_rootNumber hR] at hK ⊢
    nlinarith [Real.exp_pos (36 * ‖t‖ ^ (3 / 2 : ℝ))]

/-- The growth constant of `Y`. -/
def KY (χ : DirichletCharacter ℂ N) : ℝ :=
  KC χ + sSup ((fun t => ‖YC χ t‖) '' Metric.closedBall 0 1)

theorem norm_YC_le (t : ℂ) : ‖YC χ t‖ ≤ KY χ * Real.exp (36 * ‖t‖ ^ (3 / 2 : ℝ)) := by
  have hc : ContinuousOn (fun t => ‖YC χ t‖) (Metric.closedBall 0 1) :=
    (differentiable_YC hR).continuous.norm.continuousOn
  have hbdd : BddAbove ((fun t => ‖YC χ t‖) '' Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).bddAbove_image hc
  have hS0 : 0 ≤ sSup ((fun t => ‖YC χ t‖) '' Metric.closedBall 0 1) :=
    (norm_nonneg _).trans (le_csSup hbdd ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩)
  have hK : 1 ≤ KC χ := one_le_KC
  have he := Real.one_le_exp (show (0 : ℝ) ≤ 36 * ‖t‖ ^ (3 / 2 : ℝ) by positivity)
  unfold KY
  rcases le_or_gt ‖t‖ 1 with h | h
  · have := le_csSup hbdd ⟨t, by simpa using h, rfl⟩
    nlinarith [norm_nonneg (YC χ t)]
  · have hx := norm_XiC_le' hR t
    rw [XiC_eq_pow_mul hR, norm_mul, norm_pow] at hx
    have h1 : 1 ≤ ‖t‖ ^ mC χ := one_le_pow₀ h.le
    have : ‖YC χ t‖ ≤ ‖t‖ ^ mC χ * ‖YC χ t‖ := le_mul_of_one_le_left (norm_nonneg _) h1
    nlinarith [Real.exp_pos (36 * ‖t‖ ^ (3 / 2 : ℝ))]

theorem one_le_KY : 1 ≤ KY χ := by
  have hbdd : BddAbove ((fun t => ‖YC χ t‖) '' Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).bddAbove_image (differentiable_YC hR).continuous.norm.continuousOn
  have hS0 : 0 ≤ sSup ((fun t => ‖YC χ t‖) '' Metric.closedBall 0 1) :=
    (norm_nonneg _).trans (le_csSup hbdd ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩)
  have : 1 ≤ KC χ := one_le_KC
  unfold KY; linarith

/-- **Hadamard's product for `Y`.** -/
theorem hadamard_YC : HadamardW (YC χ) (fun i : ZeroIdx (sqF (YC χ)) => i.1⁻¹) :=
  hadamardW_even (differentiable_YC hR) (YC_even hR) (YC_zero_ne hR) (one_le_KY hR) (by norm_num)
    (by norm_num) (by norm_num) (norm_YC_le hR)

/-- **The zeros of `Ξ_χ` lie in `|Im t| < ½`** (any root number). -/
theorem XiC_zero_im' {t : ℂ} (ht : XiC χ t = 0) : |t.im| < 1 / 2 := by
  have hre : (1 / 2 + I * t).re = 1 / 2 - t.im := by simp; ring
  rw [abs_lt]
  constructor
  · by_contra h; push Not at h
    exact LamG_ne_zero_of_one_le_re hR.ne_one (by rw [hre]; linarith) ht
  · by_contra h; push Not at h
    have h1 : 1 ≤ (1 - (1 / 2 + I * t)).re := by simp; linarith
    apply LamG_ne_zero_of_one_le_re hR.ne_one h1
    rw [LamG_one_sub hR.quad hR.prim]; simp only [XiC] at ht; rw [ht, mul_zero]

theorem YC_zero_im {t : ℂ} (ht : YC χ t = 0) : |t.im| < 1 / 2 :=
  XiC_zero_im' hR (by rw [XiC_eq_pow_mul hR, ht, mul_zero])

theorem ZeroIdxY_ne_zero (i : ZeroIdx (sqF (YC χ))) : i.1 ≠ 0 := by
  intro h
  have hz : sqF (YC χ) i.1 = 0 := (ordN_ne_zero_iff (sqF_differentiable (differentiable_YC hR)
    (YC_even hR)) (by rw [sqF_zero]; exact YC_zero_ne hR) i.1).1 (by
      intro h0; exact Fin.elim0 (h0 ▸ i.2))
  rw [h, sqF_zero] at hz
  exact YC_zero_ne hR hz

/-- **The logarithmic derivative of Hadamard's product**: off the zeros,
`Y′(t)/Y(t) = Σ_u 2t/(t² − u)`. -/
theorem hasSum_logDeriv_YC {t : ℂ} (ht : YC χ t ≠ 0) :
    HasSum (fun i : ZeroIdx (sqF (YC χ)) => 2 * t / (t ^ 2 - i.1)) (logDeriv (YC χ) t) :=
  hasSum_logDeriv_of_hadamardW (hadamard_YC hR) (YC_zero_ne hR) (ZeroIdxY_ne_zero hR) ht

/-- `Σ_i |u_i|^{−7/8} < ∞` over the zeros of `Y(√w)`. -/
theorem summable_YC_zeros_rpow :
    Summable (fun i : ZeroIdx (sqF (YC χ)) => (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹) := by
  have hF := sqF_differentiable (differentiable_YC hR) (YC_even hR)
  have hF0 : sqF (YC χ) 0 ≠ 0 := by rw [sqF_zero]; exact YC_zero_ne hR
  have hgF : ∀ w, ‖sqF (YC χ) w‖ ≤ KY χ * Real.exp (36 * ‖w‖ ^ (3 / 4 : ℝ)) := by
    intro w
    refine (norm_YC_le hR _).trans ?_
    have hn : ‖w ^ ((2 : ℂ)⁻¹)‖ = ‖w‖ ^ (2⁻¹ : ℝ) := by
      rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]
    rw [hn, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hs := summable_ord_div_rpow hF hF0 (one_le_KY hR) (by norm_num) (by norm_num)
    (by norm_num : (3 / 4 : ℝ) < 7 / 8) hgF
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  refine ⟨fun u => (hasSum_fintype _).summable, ?_⟩
  refine hs.congr fun u => ?_
  rw [tsum_fintype]
  show _ = ∑ _b : Fin (ordN (sqF (YC χ)) u), (‖u‖ ^ (7 / 8 : ℝ))⁻¹
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]


/-- A square root `τ` of the zero `u` of `Y(√w)`: a zero of `Y`. -/
def tauY (i : ZeroIdx (sqF (YC χ))) : ℂ := i.1 ^ ((2 : ℂ)⁻¹)

omit hR in
theorem tauY_sq (i : ZeroIdx (sqF (YC χ))) : tauY i ^ 2 = i.1 := sqrt_sq' i.1

theorem YC_tau (i : ZeroIdx (sqF (YC χ))) : YC χ (tauY i) = 0 :=
  (ordN_ne_zero_iff (sqF_differentiable (differentiable_YC hR) (YC_even hR))
    (by rw [sqF_zero]; exact YC_zero_ne hR) i.1).1 (by
      intro h0; exact Fin.elim0 (h0 ▸ i.2))

theorem tauY_im (i : ZeroIdx (sqF (YC χ))) : |(tauY i).im| < 1 / 2 := YC_zero_im hR (YC_tau hR i)

omit hR in
theorem norm_tauY (i : ZeroIdx (sqF (YC χ))) : ‖tauY i‖ = ‖i.1‖ ^ (2⁻¹ : ℝ) := by
  unfold tauY
  rw [show ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]

theorem countable_ZeroIdxY : Countable (ZeroIdx (sqF (YC χ))) := by
  have hs : Summable fun i : ZeroIdx (sqF (YC χ)) => ‖i.1⁻¹‖ := (hadamard_YC hR).summ
  have hc := hs.countable_support
  have e : Function.support (fun i : ZeroIdx (sqF (YC χ)) => ‖i.1⁻¹‖) = univ := by
    ext i; simp [ZeroIdxY_ne_zero hR i]
  rw [e] at hc
  exact Set.countable_univ_iff.1 hc

theorem YC_line_ne_zero (r : ℝ) : YC χ ((r : ℂ) - I) ≠ 0 := by
  intro h
  have := YC_zero_im hR h
  simp at this; norm_num at this

theorem summable_kernel_normsY {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) :
    Summable fun i : ZeroIdx (sqF (YC χ)) =>
      ∫ r : ℝ, ‖h (r - I) * (1 / ((r : ℂ) - I - tauY i) + 1 / ((r : ℂ) - I + tauY i))‖ := by
  refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun r => norm_nonneg _)
    (fun i => ?_) ((summable_YC_zeros_rpow hR).mul_left (600 * C * ∫ x, om x))
  refine (kernel_integral_le H (tauY_im hR i).le).trans ?_
  have hK : 0 ≤ 600 * C * ∫ x, om x :=
    mul_nonneg (by linarith [H.C_nonneg]) (integral_nonneg om_nonneg)
  apply mul_le_mul_of_nonneg_left _ hK
  have hu : 0 < ‖i.1‖ := norm_pos_iff.2 (ZeroIdxY_ne_zero hR i)
  have ht : 0 < ‖tauY i‖ := by rw [norm_tauY]; positivity
  calc (1 + ‖tauY i‖) ^ (-(7 / 4 : ℝ)) ≤ ‖tauY i‖ ^ (-(7 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
    _ = (‖i.1‖ ^ (7 / 8 : ℝ))⁻¹ := by
        rw [norm_tauY, ← Real.rpow_mul hu.le, ← Real.rpow_neg hu.le]; norm_num

theorem kernel_eqY (i : ZeroIdx (sqF (YC χ))) (r : ℝ) :
    2 * ((r : ℂ) - I) / (((r : ℂ) - I) ^ 2 - i.1)
      = 1 / ((r : ℂ) - I - tauY i) + 1 / ((r : ℂ) - I + tauY i) := by
  have him := tauY_im hR i
  have h1 : (r : ℂ) - I - tauY i ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this
    rw [abs_lt] at him; linarith
  have h2 : (r : ℂ) - I + tauY i ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this
    rw [abs_lt] at him; linarith
  have h3 : ((r : ℂ) - I) ^ 2 - tauY i ^ 2 ≠ 0 := by
    rw [show ((r : ℂ) - I) ^ 2 - tauY i ^ 2 = ((r : ℂ) - I - tauY i) * ((r : ℂ) - I + tauY i) by ring]
    exact mul_ne_zero h1 h2
  rw [← tauY_sq i]
  field_simp
  ring

/-- The zero side for `Y`: `∫_ℝ h(r − i)Y′/Y(r − i) dr = Σ_u 2πi h(τ_u)`. -/
theorem zero_sideY0 {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t) :
    HasSum (fun i : ZeroIdx (sqF (YC χ)) => 2 * π * I * h (tauY i))
      (∫ r : ℝ, h (r - I) * logDeriv (YC χ) (r - I)) := by
  have := countable_ZeroIdxY hR
  set F : ZeroIdx (sqF (YC χ)) → ℝ → ℂ := fun i r =>
    h (r - I) * (1 / ((r : ℂ) - I - tauY i) + 1 / ((r : ℂ) - I + tauY i))
  have hint : ∀ i, Integrable (F i) := fun i =>
    integrable_kernel H (by linarith [tauY_im hR i])
  have H1 := hasSum_integral_of_summable_integral_norm hint (summable_kernel_normsY hR H)
  have hval : ∀ i, ∫ r, F i r = 2 * π * I * h (tauY i) := fun i =>
    pole_pair H heven (by linarith [tauY_im hR i])
  simp_rw [hval] at H1
  convert H1 using 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  have hs := (hasSum_logDeriv_YC hR (YC_line_ne_zero hR r)).mul_left (h (r - I))
  simp only [kernel_eqY hR] at hs
  exact hs.tsum_eq.symm

theorem logDeriv_XiC_split {t : ℂ} (ht : t ≠ 0) (hY : YC χ t ≠ 0) :
    logDeriv (XiC χ) t = (mC χ : ℂ) / t + logDeriv (YC χ) t := by
  have e : XiC χ = fun z => z ^ mC χ * YC χ z := funext (XiC_eq_pow_mul hR)
  have hd : HasDerivAt (fun z => z ^ mC χ * YC χ z) _ t :=
    (hasDerivAt_pow (mC χ) t).mul ((differentiable_YC hR) t).hasDerivAt
  rw [e, logDeriv_apply, hd.deriv, logDeriv_apply]
  have hp : t ^ mC χ ≠ 0 := pow_ne_zero _ ht
  rcases Nat.eq_zero_or_pos (mC χ) with h0 | hpos
  · rw [h0]; simp
  · obtain ⟨k, hk⟩ : ∃ k, mC χ = k + 1 := ⟨mC χ - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]; push_cast
    field_simp
    ring

/-- **The zero side with a central zero**:
`∫_ℝ h(r − i)Ξ_χ′/Ξ_χ(r − i) dr = Σ_u 2πi h(τ_u) + mπi h(0)`, the sum over the zeros of `Y`. -/
theorem zero_sideZ {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t) :
    HasSum (fun i : ZeroIdx (sqF (YC χ)) => 2 * π * I * h (tauY i))
      ((∫ r : ℝ, h ((r : ℂ) - I) * logDeriv (XiC χ) ((r : ℂ) - I)) - mC χ * (π * I * h 0)) := by
  have hY := zero_sideY0 hR H heven
  have h0 : |(0 : ℂ).im| < 1 := by simp
  have hk := integrable_kernel H h0
  have hp := pole_pair H heven h0
  simp only [sub_zero, add_zero] at hk hp
  have hne : ∀ r : ℝ, (r : ℂ) - I ≠ 0 := fun r h => by
    have := congrArg Complex.im h; simp at this
  have e1 : ∀ r : ℝ, h ((r : ℂ) - I) * logDeriv (XiC χ) ((r : ℂ) - I)
      = (mC χ / 2 : ℂ) * (h ((r : ℂ) - I) * (1 / ((r : ℂ) - I) + 1 / ((r : ℂ) - I)))
        + h ((r : ℂ) - I) * logDeriv (YC χ) ((r : ℂ) - I) := by
    intro r
    rw [logDeriv_XiC_split hR (hne r) (YC_line_ne_zero hR r)]
    field_simp; ring
  have hint2 : Integrable fun r : ℝ => h ((r : ℂ) - I) * logDeriv (YC χ) ((r : ℂ) - I) := by
    refine ((integrable_line_logDeriv_XiC hR.ne_one hR.quad H).sub
      (hk.const_mul (mC χ / 2 : ℂ))).congr (Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply, e1]; ring
  have hsum : (∫ r : ℝ, h ((r : ℂ) - I) * logDeriv (XiC χ) ((r : ℂ) - I))
      = (mC χ / 2 : ℂ) * (2 * π * I * h 0)
        + ∫ r : ℝ, h ((r : ℂ) - I) * logDeriv (YC χ) ((r : ℂ) - I) := by
    simp_rw [e1]
    rw [integral_add (hk.const_mul _) hint2, integral_const_mul, hp]
  rw [hsum]
  convert hY using 1
  ring

/-- **Weil's explicit formula with a central zero of order `m`**: for any primitive real `χ ≠ 1`,
`Σ_u 2h(τ_u) = weilRHSC − m h(0)`, the sum over the zeros of `Y = Ξ_χ/t^m`. -/
theorem weil_XiZ {h : ℂ → ℂ} {C : ℝ} (H : StripTest h C) (heven : ∀ t, h (-t) = h t)
    {hR' : ℝ → ℝ} (hreal : ∀ r : ℝ, h r = hR' r) :
    HasSum (fun i : ZeroIdx (sqF (YC χ)) => 2 * h (tauY i))
      ((weilRHSC χ hR' - mC χ * hR' 0 : ℝ) : ℂ) := by
  have hZ := zero_sideZ hR H heven
  rw [line_logDeriv_XiC hR.ne_one hR.quad H heven hreal] at hZ
  have hZ' := hZ.mul_left ((π * I)⁻¹)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h0 : h 0 = hR' 0 := by simpa using hreal 0
  convert hZ' using 1
  · funext i; field_simp
  · rw [h0]; push_cast; field_simp

end PsiOmega

#print axioms PsiOmega.weil_XiZ
