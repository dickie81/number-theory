/-
# The truncated Eisenstein series of `SL(2, ℤ)`: boundedness, square-integrability, holomorphy in `s`

Milestone B of the scattering theory of `SL(2, ℤ)\ℍ²`, the analytic half. With `a₀(y, s) = ∫_0^1 E*(x + iy, s) dx`
the constant term of the completed Eisenstein series (`ModFourier`), the **truncated series** is
`E*^Y(z, s) = E*(z, s)` for `Im z ≤ Y` and `E*(z, s) − a₀(Im z, s)` for `Im z > Y`.
* **Coordinates** (`integral_eq_coords`, `integrable_iff_coords`): the invariant integral on `ℍ` is
  `∫_{y > 0} g(x + iy) y^{−2} dx dy`, for any `g` (Mathlib's measure is `dx dy/y²` on `ℍ ⊂ ℂ`).
* **Holomorphic parameter integrals** (`differentiableOn_integral`): a family holomorphic in `s`, measurable in the
  other variable and bounded on closed balls is integrated to a holomorphic function, for a finite measure (the
  derivative is dominated by the Cauchy estimate).
* **`E*` is measurable on `ℍ`** (`measurable_Estar`), for every `s`, as a Mellin transform in `t` of `θ_z(t)`.
* **Uniform decay of the non-constant part** (`norm_Estar_sub_ct_le`): for `Im z ≥ y₀ > 0` and `|Re s − ½| ≤ R`,
  `|E*(z, s) − a₀(Im z, s)| ≤ C e^{−π Im z/4}`, summing the Bessel bounds of `ModFourier` over `k ≠ 0`.
* **Boundedness and `L²`** (`exists_bound_EstarY`, `memLp_EstarY`, `integrable_EstarY_mul`): `E*^Y(·, s)` is bounded
  on `Im z ≥ ½` (so on the fundamental domain `𝒟`), locally uniformly in `s ∈ ℂ \ {0, ½, 1}`; so it lies in
  `L²(𝒟, dx dy/y²)`, and products of two are integrable on `𝒟`.
* **Holomorphy of the inner product** (`differentiableOn_integral_EstarY`): `s ↦ ∫_𝒟 E*^Y(z, s₁)E*^Y(z, s) dμ` is
  holomorphic on `ℂ \ {0, ½, 1}`.
The Maass–Selberg relation itself is `ModMaassSelberg`.
-/
import Mathlib
import ModFourier
import ModFD

open Complex Real Filter Topology Set MeasureTheory UpperHalfPlane Metric
open scoped MatrixGroups ENNReal NNReal

noncomputable section

namespace ModTruncation

open ModEisenstein ModContinuation ModFourier

/-! ## Coordinates on `ℍ` -/

/-- `z ↦ (re z, im z)`. -/
def coords (z : ℍ) : ℝ × ℝ := Complex.measurableEquivRealProd (z : ℂ)

lemma coords_apply (z : ℍ) : coords z = (z.re, z.im) := rfl

lemma measurableEmbedding_coords : MeasurableEmbedding coords :=
  Complex.measurableEquivRealProd.measurableEmbedding.comp measurableEmbedding_coe

lemma map_coords : Measure.map coords (volume.comap UpperHalfPlane.coe) =
    volume.restrict {p : ℝ × ℝ | 0 < p.2} := by
  have e : coords = Complex.measurableEquivRealProd ∘ UpperHalfPlane.coe := rfl
  rw [e, ← Measure.map_map Complex.measurableEquivRealProd.measurable measurable_coe,
    measurableEmbedding_coe.map_comap, range_coe,
    ← Complex.volume_preserving_equiv_real_prod.map_eq]
  rw [MeasurableEquiv.restrict_map]
  rfl

lemma dens_coe (z : ℍ) : (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ) = z.im ^ (-2 : ℝ) := by
  rw [Real.rpow_neg z.im_pos.le]
  push_cast
  simp

lemma measurable_dens : Measurable fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) := by
  have e : (fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)) =
      fun z => (⟨z.im ^ (-2 : ℝ), Real.rpow_nonneg z.im_pos.le _⟩ : ℝ≥0) := by
    funext z
    exact NNReal.eq (dens_coe z)
  rw [e]
  exact Measurable.subtype_mk ((Complex.measurable_im.comp measurable_coe).pow_const _)

/-- The point `x + iy` of `ℍ` from coordinates (junk if `y ≤ 0`). -/
def ofXY (p : ℝ × ℝ) : ℍ := UpperHalfPlane.ofComplex (⟨p.1, p.2⟩ : ℂ)

lemma ofXY_coords (z : ℍ) : ofXY (coords z) = z := by
  simp only [ofXY, coords_apply]
  exact UpperHalfPlane.ofComplex_apply z

lemma ofXY_eq_pt {x y : ℝ} (hy : 0 < y) : ofXY (x, y) = pt x y hy := by
  have : ((⟨x, y⟩ : ℂ)) = ((pt x y hy : ℍ) : ℂ) := by
    apply Complex.ext <;> simp [pt]
  simp only [ofXY]
  rw [this, UpperHalfPlane.ofComplex_apply]

/-- **The invariant integral in coordinates**: `∫_ℍ g dμ = ∫_{y > 0} g(x + iy) y^{−2} dx dy`. -/
theorem integral_eq_coords (g : ℍ → ℂ) :
    ∫ z, g z = ∫ p in {p : ℝ × ℝ | 0 < p.2}, (p.2 ^ (-2 : ℝ)) • g (ofXY p) := by
  rw [volume_def, integral_withDensity_eq_integral_smul measurable_dens, ← map_coords,
    measurableEmbedding_coords.integral_map]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, dens_coe]
  rw [ofXY_coords]
  rfl

theorem integrable_iff_coords (g : ℍ → ℂ) :
    Integrable g ↔ IntegrableOn (fun p : ℝ × ℝ => (p.2 ^ (-2 : ℝ)) • g (ofXY p)) {p : ℝ × ℝ | 0 < p.2} := by
  rw [volume_def, integrable_withDensity_iff_integrable_smul measurable_dens, IntegrableOn, ← map_coords,
    measurableEmbedding_coords.integrable_map_iff]
  refine integrable_congr (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, NNReal.smul_def, dens_coe]
  rw [ofXY_coords]
  rfl

/-! ## Holomorphic parameter integrals -/
/-- **Holomorphy of a parameter integral**: if `F(·, a)` is holomorphic on an open `U` for every `a`, measurable in
`a`, and bounded uniformly on a closed ball around each point of `U` (almost everywhere in `a`), then
`s ↦ ∫ F(s, a) dμ(a)` is holomorphic on `U`, for a finite measure `μ`. The derivative is dominated by the Cauchy
estimate on a ball of half the radius. -/
theorem differentiableOn_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → ℂ}
    (hmeas : ∀ s ∈ U, AEStronglyMeasurable (F s) μ)
    (hdiff : ∀ a, DifferentiableOn ℂ (fun s => F s a) U)
    (hbd : ∀ s₀ ∈ U, ∃ r > 0, closedBall s₀ r ⊆ U ∧ ∃ M, ∀ᵐ a ∂μ, ∀ s ∈ closedBall s₀ r, ‖F s a‖ ≤ M) :
    DifferentiableOn ℂ (fun s => ∫ a, F s a ∂μ) U := by
  intro s₀ hs₀
  obtain ⟨r, hr, hsub, M, hM⟩ := hbd s₀ hs₀
  have hr2 : 0 < r / 2 := half_pos hr
  have hball : ball s₀ (r / 2) ⊆ U := (ball_subset_closedBall.trans (closedBall_subset_closedBall
    (by linarith))).trans hsub
  have hderiv : ∀ a, ∀ s ∈ ball s₀ (r / 2), HasDerivAt (fun s => F s a) (deriv (fun s => F s a) s) s :=
    fun a s hs => ((hdiff a).differentiableAt (hU.mem_nhds (hball hs))).hasDerivAt
  -- measurability of the derivative at `s₀`, as a limit of difference quotients
  have hmeas' : AEStronglyMeasurable (fun a => deriv (fun s => F s a) s₀) μ := by
    set h : ℕ → ℂ := fun n => ((r / 2 / (n + 2) : ℝ) : ℂ)
    have hpos : ∀ n : ℕ, 0 < r / 2 / (n + 2) := fun n => div_pos hr2 (by positivity)
    have hmem : ∀ n, s₀ + h n ∈ U := fun n => hball (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (hpos n).le]
      exact div_lt_self hr2 (by linarith))
    have hh0 : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have : Tendsto (fun n : ℕ => r / 2 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
        rw [Complex.ofReal_zero] at h2
        exact h2
      · simp only [mem_compl_iff, mem_singleton_iff, h, Complex.ofReal_eq_zero]
        exact (hpos n).ne'
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n a => (h n)⁻¹ * (F (s₀ + h n) a - F s₀ a))
      (fun n => ((hmeas _ (hmem n)).sub (hmeas _ hs₀)).const_mul _) (Eventually.of_forall fun a => ?_)
    have hd := hasDerivAt_iff_tendsto_slope_zero.1 (hderiv a s₀ (mem_ball_self hr2))
    exact (hd.comp hh0).congr fun n => by simp [smul_eq_mul]
  have hint : Integrable (F s₀) μ := by
    refine Integrable.mono' (integrable_const M) (hmeas s₀ hs₀) ?_
    filter_upwards [hM] with a ha using ha s₀ (mem_closedBall_self hr.le)
  have hbound : ∀ᵐ a ∂μ, ∀ s ∈ ball s₀ (r / 2), ‖deriv (fun s => F s a) s‖ ≤ M / (r / 2) := by
    filter_upwards [hM] with a ha s hs
    have hsub' : closedBall s (r / 2) ⊆ closedBall s₀ r := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      rw [mem_ball] at hs
      linarith [dist_triangle w s s₀]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr2 ?_ fun w hw => ha w (hsub' (sphere_subset_closedBall hw))
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball s hr2.ne']
    exact (hdiff a).mono (hsub'.trans hsub)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (x₀ := s₀)
    (F' := fun s a => deriv (fun s => F s a) s) (bound := fun _ => M / (r / 2))
    (ball_mem_nhds s₀ hr2) (eventually_of_mem (hU.mem_nhds hs₀) fun s hs => hmeas s hs) hint hmeas'
    hbound (integrable_const _) (Eventually.of_forall fun a s hs => hderiv a s hs)
  exact key.2.differentiableAt.differentiableWithinAt

/-! ## Measurability of `E*` on `ℍ` -/

lemma continuous_qf (v : Fin 2 → ℤ) : Continuous fun z : ℍ => qf z v := by
  unfold qf nq
  exact (Complex.continuous_normSq.comp (continuous_const.mul continuous_coe |>.add continuous_const)).div
    UpperHalfPlane.continuous_im fun z => z.im_pos.ne'

lemma measurable_theta_H : Measurable fun p : ℍ × ℝ => theta p.1 p.2 := by
  unfold theta
  exact Measurable.tsum fun v => (Real.continuous_exp.comp
    ((continuous_const.mul ((continuous_qf v).comp continuous_fst)).mul continuous_snd)).measurable

lemma measurable_fmod_H : Measurable fun p : ℍ × ℝ => (thetaFEPair p.1).f_modif p.2 := by
  simp_rw [fmod_eq]
  have h := measurable_theta_H
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    (Complex.measurable_ofReal.comp (h.sub measurable_const))
    (Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const))
      (Complex.measurable_ofReal.comp (h.sub (measurable_snd.pow_const _))) measurable_const)

/-- **`z ↦ E*(z, s)` is measurable on `ℍ`**, for every `s`: `E*` is a Mellin transform of a jointly measurable
function of `(z, t)`. -/
theorem measurable_Estar (s : ℂ) : Measurable fun z : ℍ => Estar z s := by
  have e : (fun z : ℍ => Estar z s) = fun z => ((thetaFEPair z).Λ₀ s - 1 / s - 1 / (1 - s)) / 2 := by
    funext z
    simp only [Estar, Lambda, Λ_thetaFEPair]
  rw [e]
  refine Measurable.div_const (Measurable.sub_const (Measurable.sub_const ?_ _) _) _
  have hF : StronglyMeasurable fun p : ℍ × ℝ => ((p.2 : ℂ) ^ (s - 1)) • (thetaFEPair p.1).f_modif p.2 :=
    ((((Complex.measurable_ofReal.comp measurable_snd).pow_const _)).smul
      measurable_fmod_H).stronglyMeasurable
  exact (hF.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

/-! ## The constant term as a function of `y` -/

/-- **The constant term** `a₀(y, s) = ∫_0^1 E*(x + iy, s) dx` (`0` for `y ≤ 0`). -/
def ct (y : ℝ) (s : ℂ) : ℂ := if hy : 0 < y then ∫ x in (0 : ℝ)..1, Estar (pt x y hy) s else 0

/-- Its closed form `Λ(2s)y^s + Λ(2s − 1)y^{1−s}`. -/
def a0 (y : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta (2 * s) * (y : ℂ) ^ s + completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s)

lemma ct_pos {y : ℝ} (hy : 0 < y) (s : ℂ) : ct y s = ∫ x in (0 : ℝ)..1, Estar (pt x y hy) s := by
  simp [ct, hy]

theorem ct_eq_a0 {y : ℝ} (hy : 0 < y) {s : ℂ} (h0 : s ≠ 0) (hh : s ≠ 1 / 2) (h1 : s ≠ 1) : ct y s = a0 y s := by
  rw [ct_pos hy, constTerm_Estar_all hy h0 hh h1, a0]

theorem ct_eq_a0_of_one_lt {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) : ct y s = a0 y s := by
  rw [ct_pos hy, constTerm_Estar hy hs, a0]

lemma differentiableAt_ct {y : ℝ} (hy : 0 < y) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (ct y) s := by
  have e : ct y = fun s => ∫ x in (0 : ℝ)..1, Estar (pt x y hy) s := funext fun s => ct_pos hy s
  rw [e]
  exact differentiableAt_constTerm hy h0 h1

lemma pt_re_im (z : ℍ) : pt z.re z.im z.im_pos = z := by
  ext : 1
  apply Complex.ext <;> simp [pt]

/-! ## The non-constant part decays exponentially, uniformly in `s` on vertical strips -/

lemma bkR_anti {r x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x₀ ≤ x) : Eis.bkR r x ≤ Eis.bkR r x₀ := by
  unfold Eis.bkR
  refine setIntegral_mono_on (Eis.integrableOn_bkR (hx₀.trans_le hx) r) (Eis.integrableOn_bkR hx₀ r)
    measurableSet_Ioi fun t ht => ?_
  exact mul_le_mul_of_nonneg_left (Eis.bkK_anti hx ht) (Real.rpow_nonneg (le_of_lt ht) _)

lemma bkR_le_sum {r R x : ℝ} (hx : 0 < x) (hr : |r| ≤ R) : Eis.bkR r x ≤ Eis.bkR R x + Eis.bkR (-R) x := by
  unfold Eis.bkR
  rw [← integral_add (Eis.integrableOn_bkR hx R) (Eis.integrableOn_bkR hx (-R))]
  refine setIntegral_mono_on (Eis.integrableOn_bkR hx r)
    ((Eis.integrableOn_bkR hx R).add (Eis.integrableOn_bkR hx (-R))) measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hK := (Eis.bkK_pos x t).le
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ hK
  have a1 := Real.rpow_nonneg ht0.le (R - 1)
  have a2 := Real.rpow_nonneg ht0.le (-R - 1)
  have hr' := abs_le.1 hr
  rcases le_or_gt 1 t with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (show r - 1 ≤ R - 1 by linarith)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ht0 h.le (show -R - 1 ≤ r - 1 by linarith)
    linarith

lemma sqrt_mul_exp_le {y y₀ a : ℝ} (hy₀ : 0 < y₀) (hy : y₀ ≤ y) (ha : 1 ≤ a) :
    √y * rexp (-(π * y) * a) ≤ rexp (-(π * y₀ / 4) * a) * rexp (-(π / 4) * y) := by
  have hy0 : 0 < y := hy₀.trans_le hy
  have h1 : √y ≤ rexp y := by
    refine (Real.sqrt_le_iff.2 ⟨by linarith [Real.add_one_le_exp y], ?_⟩)
    nlinarith [Real.add_one_le_exp y, Real.exp_pos y]
  rw [← Real.exp_add]
  calc √y * rexp (-(π * y) * a) ≤ rexp y * rexp (-(π * y) * a) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = rexp (y + -(π * y) * a) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      have hpi := Real.pi_gt_three
      nlinarith [mul_le_mul_of_nonneg_left hy (show (0 : ℝ) ≤ π * a by positivity),
        mul_le_mul_of_nonneg_left ha (show (0 : ℝ) ≤ π * y by positivity)]

lemma hasSum_Estar_sub_ct (z : ℍ) (s : ℂ) :
    HasSum (Function.update (fun k : ℤ =>
      (∫ u in (0 : ℝ)..1, cexp (-(2 * π * Complex.I * k * u)) * Estar (pt u z.im z.im_pos) s) *
        cexp (2 * π * Complex.I * k * z.re)) 0 0) (Estar z s - ct z.im s) := by
  have h := (hasSum_fourier_Estar z.im_pos s z.re).update 0 0
  rw [pt_re_im] at h
  convert h using 1
  rw [ct_pos z.im_pos]
  simp only [Int.cast_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul, mul_one]
  ring

/-- **Uniform exponential decay of `E* − a₀`**: on `Im z ≥ y₀ > 0` and `|Re s − ½| ≤ R`,
`|E*(z, s) − a₀(Im z, s)| ≤ C e^{−π Im z/4}`. -/
theorem norm_Estar_sub_ct_le {y₀ R : ℝ} (hy₀ : 0 < y₀) :
    ∃ C, ∀ s : ℂ, |(s - 1 / 2).re| ≤ R → ∀ z : ℍ, y₀ ≤ z.im →
      ‖Estar z s - ct z.im s‖ ≤ C * rexp (-(π / 4) * z.im) := by
  set B := Eis.bkR R (2 * π * y₀ / 2) + Eis.bkR (-R) (2 * π * y₀ / 2)
  set N := ⌈1 + R⌉₊
  set g : ℤ → ℝ := fun k => B * (|(k : ℝ)| ^ N * rexp (-(π * y₀ / 4) * |(k : ℝ)|))
  have hg : Summable g := by
    have h := (Real.summable_pow_mul_exp_neg_nat_mul N (show 0 < π * y₀ / 4 by positivity)).mul_left B
    refine Summable.of_nat_of_neg ?_ ?_
    · refine h.congr fun n => ?_
      simp only [g, Int.cast_natCast, Nat.abs_cast]
    · refine h.congr fun n => ?_
      simp only [g, Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
  refine ⟨∑' k, g k, fun s hs z hz => ?_⟩
  have hy := z.im_pos
  have hB0 : 0 ≤ B := add_nonneg (Eis.bkR_nonneg _ _) (Eis.bkR_nonneg _ _)
  rw [← (hasSum_Estar_sub_ct z s).tsum_eq]
  refine tsum_of_norm_bounded (hg.hasSum.mul_right (rexp (-(π / 4) * z.im))) fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [Function.update_self, norm_zero]
    positivity
  rw [Function.update_of_ne hk, norm_mul]
  have he : ‖cexp (2 * π * Complex.I * k * z.re)‖ = 1 := by
    rw [show 2 * π * Complex.I * k * z.re = ((2 * π * k * z.re : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [he, mul_one]
  have hK1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hk)
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  refine (norm_fourierCoeff_Estar_le hy s hk).trans ?_
  have b1 : Eis.bkR (s - 1 / 2).re (2 * π * z.im / 2) ≤ B :=
    (bkR_anti (by positivity) (by nlinarith [Real.pi_pos])).trans (bkR_le_sum (by positivity) hs)
  have b2 : |(k : ℝ)| ^ ⌈1 + |(s - 1 / 2).re|⌉₊ ≤ |(k : ℝ)| ^ N :=
    pow_le_pow_right₀ hK1 (Nat.ceil_mono (by linarith))
  have b3 := sqrt_mul_exp_le hy₀ hz hK1
  have h0 : 0 ≤ Eis.bkR (s - 1 / 2).re (2 * π * z.im / 2) := Eis.bkR_nonneg _ _
  calc √z.im * Eis.bkR (s - 1 / 2).re (2 * π * z.im / 2) * |(k : ℝ)| ^ ⌈1 + |(s - 1 / 2).re|⌉₊ *
        rexp (-(π * z.im) * |(k : ℝ)|)
      = Eis.bkR (s - 1 / 2).re (2 * π * z.im / 2) * |(k : ℝ)| ^ ⌈1 + |(s - 1 / 2).re|⌉₊ *
        (√z.im * rexp (-(π * z.im) * |(k : ℝ)|)) := by ring
    _ ≤ B * |(k : ℝ)| ^ N * (rexp (-(π * y₀ / 4) * |(k : ℝ)|) * rexp (-(π / 4) * z.im)) := by gcongr
    _ = g k * rexp (-(π / 4) * z.im) := by simp only [g]; ring

/-! ## The truncated Eisenstein series -/

/-- The connected open set `ℂ \ {0, ½, 1}`, where `E*` and its closed-form constant term are holomorphic. -/
def U : Set ℂ := ({0, 1 / 2, 1} : Set ℂ)ᶜ

lemma mem_U {s : ℂ} : s ∈ U ↔ s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1 := by
  simp [U, not_or]

lemma isOpen_U : IsOpen U := (Set.toFinite _).isClosed.isOpen_compl

lemma isPreconnected_U : IsPreconnected U :=
  ((Set.toFinite _).countable.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected

/-- **The truncated completed Eisenstein series** `E*^Y(z, s)`: `E*(z, s)` where `Im z ≤ Y`, and `E*(z, s)` minus
its constant term `a₀(Im z, s)` where `Im z > Y`. On the fundamental domain with `Y ≥ 1` this is Arthur's truncation
`Λ^Y E*`. -/
def EstarY (Y : ℝ) (s : ℂ) (z : ℍ) : ℂ := if z.im ≤ Y then Estar z s else Estar z s - ct z.im s

lemma measurable_a0 (s : ℂ) : Measurable fun z : ℍ => a0 z.im s := by
  unfold a0
  have h : Measurable fun z : ℍ => ((z.im : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Complex.measurable_im.comp measurable_coe)
  exact (measurable_const.mul (h.pow_const _)).add (measurable_const.mul (h.pow_const _))

lemma measurable_EstarY (Y : ℝ) {s : ℂ} (hs : s ∈ U) : Measurable (EstarY Y s) := by
  obtain ⟨h0, hh, h1⟩ := mem_U.1 hs
  have e : EstarY Y s = fun z => if z.im ≤ Y then Estar z s else Estar z s - a0 z.im s := by
    funext z
    simp only [EstarY, ct_eq_a0 z.im_pos h0 hh h1]
  rw [e]
  exact Measurable.ite (measurableSet_le (Complex.measurable_im.comp measurable_coe) measurable_const)
    (measurable_Estar s) ((measurable_Estar s).sub (measurable_a0 s))

lemma differentiableAt_EstarY (Y : ℝ) (z : ℍ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => EstarY Y s z) s := by
  unfold EstarY
  split_ifs
  · exact differentiableAt_Estar z h0 h1
  · exact (differentiableAt_Estar z h0 h1).sub (differentiableAt_ct z.im_pos h0 h1)

lemma differentiableOn_EstarY (Y : ℝ) (z : ℍ) : DifferentiableOn ℂ (fun s => EstarY Y s z) U :=
  fun _ hs => (differentiableAt_EstarY Y z (mem_U.1 hs).1 (mem_U.1 hs).2.2).differentiableWithinAt

lemma rpow_le_of_mem {a K R : ℝ} (ha : 0 < a) (haK : a ≤ K) (hiK : a⁻¹ ≤ K) (hK : 1 ≤ K) {r : ℝ}
    (hr : |r| ≤ R) : a ^ r ≤ K ^ R :=
  (rpow_le_abs ha haK hiK hK r).trans (Real.rpow_le_rpow_of_exponent_le hK hr)

/-- **`E*^Y` is bounded on `Im z ≥ ½`, locally uniformly in `s ∈ ℂ \ {0, ½, 1}`**: below the horocycle by the
closed form of the constant term and the decay of the rest, above it by the decay of `E* − a₀`. -/
theorem exists_bound_EstarY (Y : ℝ) {s₀ : ℂ} (hs₀ : s₀ ∈ U) :
    ∃ r > 0, closedBall s₀ r ⊆ U ∧ ∃ M, ∀ s ∈ closedBall s₀ r, ∀ z : ℍ, 1 / 2 ≤ z.im → ‖EstarY Y s z‖ ≤ M := by
  obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 isOpen_U s₀ hs₀
  set r := r' / 2
  have hr : 0 < r := half_pos hr'
  have hsub : closedBall s₀ r ⊆ U := (closedBall_subset_ball (by simp only [r]; linarith)).trans hball
  refine ⟨r, hr, hsub, ?_⟩
  set R := |s₀.re| + 1 + r
  have hR : ∀ s ∈ closedBall s₀ r, |(s - 1 / 2).re| ≤ R ∧ |s.re| ≤ R ∧ |(1 - s).re| ≤ R := by
    intro s hs
    have h := (abs_re_le_norm (s - s₀)).trans (mem_closedBall_iff_norm.1 hs)
    simp only [sub_re, one_re] at h ⊢
    refine ⟨?_, ?_, ?_⟩ <;>
    · rw [abs_le] at h ⊢
      have := abs_le.1 (le_refl |s₀.re|)
      constructor <;> norm_num <;> linarith [abs_nonneg s₀.re]
  obtain ⟨C, hC⟩ := norm_Estar_sub_ct_le (R := R) (show (0 : ℝ) < 1 / 2 by norm_num)
  have hK : IsCompact (closedBall s₀ r) := isCompact_closedBall s₀ r
  have hc1 : ContinuousOn (fun s : ℂ => completedRiemannZeta (2 * s)) (closedBall s₀ r) := fun s hs => by
    obtain ⟨h0, hh, -⟩ := mem_U.1 (hsub hs)
    exact ((differentiableAt_completedZeta (by intro h; apply h0; linear_combination h / 2)
      (by intro h; apply hh; linear_combination h / 2)).comp s
      (differentiableAt_id.const_mul 2)).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (fun s : ℂ => completedRiemannZeta (2 * s - 1)) (closedBall s₀ r) := fun s hs => by
    obtain ⟨-, hh, h1⟩ := mem_U.1 (hsub hs)
    exact ((differentiableAt_completedZeta (by intro h; apply hh; linear_combination h / 2)
      (by intro h; apply h1; linear_combination h / 2)).comp s
      ((differentiableAt_id.const_mul 2).sub_const 1)).continuousAt.continuousWithinAt
  obtain ⟨A₁, hA₁⟩ := hK.exists_bound_of_continuousOn hc1
  obtain ⟨A₂, hA₂⟩ := hK.exists_bound_of_continuousOn hc2
  set K := |Y| + 3
  refine ⟨|C| + (A₁ * K ^ R + A₂ * K ^ R), fun s hs z hz => ?_⟩
  obtain ⟨hR1, hR2, hR3⟩ := hR s hs
  obtain ⟨h0, hh, h1⟩ := mem_U.1 (hsub hs)
  have hy := z.im_pos
  have htail : ‖Estar z s - ct z.im s‖ ≤ |C| := by
    refine (hC s hR1 z hz).trans ?_
    have : rexp (-(π / 4) * z.im) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    calc C * rexp (-(π / 4) * z.im) ≤ |C| * rexp (-(π / 4) * z.im) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg C)
      _ = |C| := mul_one _
  have hM0 : 0 ≤ A₁ * K ^ R + A₂ * K ^ R := by
    have : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ s hs)
    have : 0 ≤ A₂ := (norm_nonneg _).trans (hA₂ s hs)
    have : 0 ≤ K ^ R := Real.rpow_nonneg (by positivity) _
    positivity
  unfold EstarY
  split_ifs with hY
  · have hzK : z.im ≤ K := by have := le_abs_self Y; simp only [K]; linarith
    have hiK : z.im⁻¹ ≤ K := by
      have : z.im⁻¹ ≤ 2 := by rw [inv_le_comm₀ hy two_pos]; linarith
      simp only [K]; linarith [abs_nonneg Y]
    have hK1 : 1 ≤ K := by simp only [K]; linarith [abs_nonneg Y]
    have ha0 : ‖ct z.im s‖ ≤ A₁ * K ^ R + A₂ * K ^ R := by
      rw [ct_eq_a0 hy h0 hh h1, a0]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_cpow_eq_rpow_re_of_pos hy]
      have a1 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ s hs)
      have a2 : 0 ≤ A₂ := (norm_nonneg _).trans (hA₂ s hs)
      exact add_le_add (mul_le_mul (hA₁ s hs) (rpow_le_of_mem hy hzK hiK hK1 hR2) (by positivity) a1)
        (mul_le_mul (hA₂ s hs) (rpow_le_of_mem hy hzK hiK hK1 hR3) (by positivity) a2)
    calc ‖Estar z s‖ = ‖(Estar z s - ct z.im s) + ct z.im s‖ := by ring_nf
      _ ≤ ‖Estar z s - ct z.im s‖ + ‖ct z.im s‖ := norm_add_le _ _
      _ ≤ _ := add_le_add htail ha0
  · linarith

lemma half_le_im_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  nlinarith [z.im_pos]

instance : IsFiniteMeasure (volume.restrict (ModularGroup.fd : Set ℍ)) :=
  isFiniteMeasure_restrict.2 (by rw [ModFD.volume_fd]; exact ENNReal.ofReal_ne_top)

lemma exists_bound_EstarY_fd (Y : ℝ) {s : ℂ} (hs : s ∈ U) :
    ∃ M, ∀ z ∈ ModularGroup.fd, ‖EstarY Y s z‖ ≤ M := by
  obtain ⟨r, hr, -, M, hM⟩ := exists_bound_EstarY Y hs
  exact ⟨M, fun z hz => hM s (mem_closedBall_self hr.le) z (half_le_im_of_mem_fd hz)⟩

/-- **`E*^Y(·, s)` is square-integrable on the fundamental domain** (indeed bounded), for `s ≠ 0, ½, 1`. -/
theorem memLp_EstarY (Y : ℝ) {s : ℂ} (hs : s ∈ U) :
    MemLp (EstarY Y s) 2 (volume.restrict ModularGroup.fd) := by
  obtain ⟨M, hM⟩ := exists_bound_EstarY_fd Y hs
  exact MemLp.of_bound (measurable_EstarY Y hs).aestronglyMeasurable M
    ((ae_restrict_iff' ModFD.measurableSet_fd).2 (Eventually.of_forall hM))

lemma integrable_EstarY_mul (Y : ℝ) {s₁ s₂ : ℂ} (hs₁ : s₁ ∈ U) (hs₂ : s₂ ∈ U) :
    Integrable (fun z => EstarY Y s₁ z * EstarY Y s₂ z) (volume.restrict ModularGroup.fd) := by
  obtain ⟨M₁, hM₁⟩ := exists_bound_EstarY_fd Y hs₁
  obtain ⟨M₂, hM₂⟩ := exists_bound_EstarY_fd Y hs₂
  refine Integrable.mono' (integrable_const (M₁ * M₂))
    ((measurable_EstarY Y hs₁).mul (measurable_EstarY Y hs₂)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' ModFD.measurableSet_fd).2 (Eventually.of_forall fun z hz => ?_)
  rw [norm_mul]
  exact mul_le_mul (hM₁ z hz) (hM₂ z hz) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ z hz))

/-- **`s ↦ ∫_𝒟 E*^Y(z, s₁)E*^Y(z, s) dμ` is holomorphic on `ℂ \ {0, ½, 1}`.** -/
theorem differentiableOn_integral_EstarY (Y : ℝ) {s₁ : ℂ} (hs₁ : s₁ ∈ U) :
    DifferentiableOn ℂ (fun s => ∫ z in ModularGroup.fd, EstarY Y s₁ z * EstarY Y s z) U := by
  obtain ⟨M₁, hM₁⟩ := exists_bound_EstarY_fd Y hs₁
  refine differentiableOn_integral isOpen_U
    (fun s hs => ((measurable_EstarY Y hs₁).mul (measurable_EstarY Y hs)).aestronglyMeasurable)
    (fun z => (differentiableOn_EstarY Y z).const_mul _) fun s₀ hs₀ => ?_
  obtain ⟨r, hr, hsub, M, hM⟩ := exists_bound_EstarY Y hs₀
  refine ⟨r, hr, hsub, M₁ * M, (ae_restrict_iff' ModFD.measurableSet_fd).2
    (Eventually.of_forall fun z hz s hs => ?_)⟩
  rw [norm_mul]
  exact mul_le_mul (hM₁ z hz) (hM s hs z (half_le_im_of_mem_fd hz)) (norm_nonneg _)
    ((norm_nonneg _).trans (hM₁ z hz))

end ModTruncation
