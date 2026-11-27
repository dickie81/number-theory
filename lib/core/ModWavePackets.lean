/-
# Eisenstein wave packets on `SL(2, ℤ)\ℍ²`: the cusp transform and the Maass–Selberg inner product

Milestone C, geometric half. With `E*` the completed Eisenstein series, `a₀(y, s) = Λ(2s)y^s + Λ(2s − 1)y^{1−s}`
its constant term, `E^Y = E*^Y/Λ(2s)` the normalised truncation and `φ = PavlovFaddeev.scatteringMatrix`:
* **The Eisenstein transform of a cusp function** (`cuspFn`, `integral_cuspFn_Estar`, `integral_cuspFn_EY`): for
  `f` continuous, vanishing on `y > R`, and `F(z) = f(Im z)1_{Im z > 1}`,
  `∫_𝒟 F(z)E*(z, s) dμ = ∫_{y > 1} f(y)a₀(y, s)y^{−2} dy` for `s ≠ 0, ½, 1` (Fubini on `{|x| ≤ ½, y > 1} ⊂ 𝒟`), and
  for `Y ≥ R`, `Λ(2s) ≠ 0`, `∫_𝒟 F(z)E^Y(z, s) dμ = ∫_{y > 1} f(y)(y^s + φ(s)y^{1−s})y^{−2} dy`: an outgoing wave
  plus `φ(s)` times an incoming one, so `φ(½ + it)` is the scattering matrix between the two Mellin transforms.
* **Wave packets** (`wavePacket`, `memLp_wavePacket`): for `g` continuous and `0 < a ≤ b`,
  `Ψ_Y(g)(z) = ∫_a^b g(t)E^Y(z, ½ + it) dt` is in `L²(𝒟)` (indeed bounded).
* **Their Maass–Selberg inner product** (`msKernel`, `msKernel_eq`, `integral_wavePacket_mul_conj`): for `Y ≥ 1`,
  `∫_𝒟 Ψ_Y(g) conj Ψ_Y(h) dμ = ∫∫_{(a,b]²} g(t₁) conj h(t₂) K_Y(t₁, t₂) dt₁ dt₂` with
  `K_Y = (Y^{i(t₁−t₂)} − φ₁ conj φ₂ Y^{−i(t₁−t₂)})/(i(t₁ − t₂)) + (conj φ₂ Y^{i(t₁+t₂)} − φ₁ Y^{−i(t₁+t₂)})/(i(t₁ + t₂))`,
  `φ_j = φ(½ + it_j)`, by Fubini and `ModMaassSelberg.maass_selberg_phi` off the diagonal.
The limit `Y → ∞` (Plancherel for the continuous spectrum) and the spectral decomposition of `L²(𝒟)` are not
proved here.
-/
import Mathlib
import ModMaassSelberg

open Complex Real Filter Topology Set MeasureTheory UpperHalfPlane Metric ModularGroup
open scoped MatrixGroups ENNReal NNReal ComplexConjugate

noncomputable section

namespace ModWavePackets

open ModEisenstein ModContinuation ModFourier ModTruncation ModFD ModMaassSelberg

/-! ## Cusp functions and the Eisenstein transform -/

/-- **A cusp function**: `f(Im z)` above the horocycle `Im z = 1`, `0` below it. -/
def cuspFn (f : ℝ → ℂ) (z : ℍ) : ℂ := if 1 < z.im then f z.im else 0

lemma measurable_cuspFn {f : ℝ → ℂ} (hf : Continuous f) : Measurable (cuspFn f) :=
  Measurable.ite (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_coe))
    (hf.measurable.comp (Complex.measurable_im.comp measurable_coe)) measurable_const

lemma integrable_cuspFn_mul {f : ℝ → ℂ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, R < y → f y = 0) {s : ℂ}
    (hs : s ∈ U) : Integrable (fun z => cuspFn f z * Estar z s) (volume.restrict fd) := by
  obtain ⟨Mf, hMf⟩ := (isCompact_Icc (a := 1) (b := R)).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨r, hr, -, M, hM⟩ := exists_bound_EstarY R hs
  refine Integrable.mono' (integrable_const (|Mf| * |M|))
    ((measurable_cuspFn hf).mul (measurable_Estar s)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_fd).2 (Eventually.of_forall fun z hz => ?_)
  unfold cuspFn
  split_ifs with h1
  · by_cases hR' : z.im ≤ R
    · have b1 := hMf z.im ⟨h1.le, hR'⟩
      have b2 := hM s (mem_closedBall_self hr.le) z (half_le_im_of_mem_fd hz)
      simp only [EstarY, hR', ↓reduceIte] at b2
      rw [norm_mul]
      exact mul_le_mul (b1.trans (le_abs_self _)) (b2.trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)
    · rw [hR _ (not_le.1 hR'), zero_mul, norm_zero]; positivity
  · rw [zero_mul, norm_zero]; positivity

/-- **The Eisenstein transform of a cusp function is its constant-term transform**: for `f` continuous, vanishing
above `Im z = R`, and `s ≠ 0, ½, 1`,
`∫_𝒟 f(Im z)1_{Im z > 1} E*(z, s) dμ = ∫_{y > 1} f(y)(Λ(2s)y^s + Λ(2s − 1)y^{1−s}) y^{−2} dy`,
by Fubini on `{|x| ≤ ½, y > 1} ⊂ 𝒟` and `∫_{−1/2}^{1/2} E*(x + iy, s) dx = a₀(y, s)`. -/
theorem integral_cuspFn_Estar {f : ℝ → ℂ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, R < y → f y = 0) {s : ℂ}
    (hs : s ∈ U) :
    ∫ z in fd, cuspFn f z * Estar z s = ∫ y in Ioi (1 : ℝ), (y ^ (-2 : ℝ)) • (f y * a0 y s) := by
  obtain ⟨h0, hh, h1⟩ := mem_U.1 hs
  have hint := integrable_cuspFn_mul hf hR hs
  rw [← integral_indicator measurableSet_fd, integral_eq_coords]
  have hint' := (integrable_iff_coords _).1 ((integrable_indicator_iff measurableSet_fd).2 hint)
  set F := fun p : ℝ × ℝ => (p.2 ^ (-2 : ℝ)) • (fd.indicator (fun z => cuspFn f z * Estar z s)) (ofXY p)
  set T : Set (ℝ × ℝ) := Icc (-(1 / 2)) (1 / 2) ×ˢ Ioi 1
  have hT : T ⊆ {p : ℝ × ℝ | 0 < p.2} := fun p hp => by
    have : 1 < p.2 := hp.2
    show 0 < p.2
    linarith
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_lt measurable_const measurable_snd) hT
    (fun p hp => ?_)]
  swap
  · obtain ⟨hp1, hp2⟩ := hp
    have hp0 : 0 < p.2 := hp1
    try simp only [F]
    by_cases h1' : 1 < p.2
    · have : ofXY p ∉ fd := by
        rw [ofXY_mem_fd_iff le_rfl h1', abs_le]
        intro h
        exact hp2 ⟨h, h1'⟩
      rw [indicator_of_notMem this, smul_zero]
    · by_cases hm : ofXY p ∈ fd
      · rw [indicator_of_mem hm, cuspFn, ofXY_im hp0]
        simp only [h1', ↓reduceIte, zero_mul, smul_zero]
      · rw [indicator_of_notMem hm, smul_zero]
  have hintT : IntegrableOn F T := hint'.mono_set hT
  rw [show T = Icc (-(1 / 2)) (1 / 2) ×ˢ Ioi 1 from rfl, IntegrableOn, Measure.volume_eq_prod,
    ← Measure.prod_restrict] at hintT
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod_symm _ hintT]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  have hy : 1 < y := hy
  have hy0 : 0 < y := by linarith
  have hcont := continuous_Estar_x hy0 s
  have e : ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), F (x, y) = (y ^ (-2 : ℝ)) • (f y * Estar (pt x y hy0) s) := by
    intro x hx
    have hm : ofXY (x, y) ∈ fd := (ofXY_mem_fd_iff le_rfl hy).2 (abs_le.2 hx)
    simp only [F]
    rw [indicator_of_mem hm, cuspFn, ofXY_eq_pt hy0, pt_im]
    simp only [hy, ↓reduceIte]
  show ∫ x in Icc (-(1 / 2) : ℝ) (1 / 2), F (x, y) = _
  rw [setIntegral_congr_fun measurableSet_Icc e, integral_smul, integral_const_mul]
  have hper : ∫ x in Icc (-(1 / 2) : ℝ) (1 / 2), Estar (pt x y hy0) s = ct y s := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), ct_pos hy0]
    have := (Estar_periodic hy0 s).intervalIntegral_add_eq (-(1 / 2)) 0
    norm_num at this ⊢
    exact this
  rw [hper, ct_eq_a0 hy0 h0 hh h1]

/-- **The scattering matrix between incoming and outgoing cusp waves**: for `Y ≥ R`, `s ≠ 0, ½, 1` with
`Λ(2s) ≠ 0`, the pairing of the cusp function `f(Im z)` with the truncated Eisenstein series `E^Y(·, s)` on `𝒟` is
`∫_{y > 1} f(y)(y^s + φ(s)y^{1−s}) y^{−2} dy`: the outgoing wave `y^s` plus `φ(s)` times the incoming wave
`y^{1−s}`. On `s = ½ + it` these are the Mellin transforms `∫ f(y) y^{−3/2 ± it} dy`, and `φ(½ + it)` (of modulus
`1`) maps one to the other. -/
theorem integral_cuspFn_EY {f : ℝ → ℂ} (hf : Continuous f) {R : ℝ} (hR : ∀ y, R < y → f y = 0) {Y : ℝ}
    (hY : R ≤ Y) {s : ℂ} (hs : s ∈ U) (hΛ : completedRiemannZeta (2 * s) ≠ 0) :
    ∫ z in fd, cuspFn f z * EY Y s z =
      ∫ y in Ioi (1 : ℝ), (y ^ (-2 : ℝ)) • (f y * ((y : ℂ) ^ s + PavlovFaddeev.scatteringMatrix s *
        (y : ℂ) ^ (1 - s))) := by
  have e : ∀ z : ℍ, cuspFn f z * EY Y s z = cuspFn f z * Estar z s / completedRiemannZeta (2 * s) := by
    intro z
    unfold cuspFn
    split_ifs with h1
    · by_cases hz : z.im ≤ Y
      · simp only [EY, EstarY, hz, ↓reduceIte]; ring
      · rw [hR _ (by linarith [not_le.1 hz])]; simp
    · simp
  simp_rw [e]
  rw [integral_div, integral_cuspFn_Estar hf hR hs, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  simp only [a0, PavlovFaddeev.scatteringMatrix, Complex.real_smul]
  field_simp

/-! ## Eisenstein wave packets -/

/-- `E*^Y` is bounded on `Im z ≥ ½` uniformly for `s` in a compact subset of `ℂ \ {0, ½, 1}`. -/
lemma exists_bound_EstarY_compact (Y : ℝ) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M, ∀ s ∈ K, ∀ z : ℍ, 1 / 2 ≤ z.im → ‖EstarY Y s z‖ ≤ M := by
  have h : ∀ s ∈ K, ∃ r > 0, ∃ M, ∀ s' ∈ closedBall s r, ∀ z : ℍ, 1 / 2 ≤ z.im → ‖EstarY Y s' z‖ ≤ M := by
    intro s hs
    obtain ⟨r, hr, -, M, hM⟩ := exists_bound_EstarY Y (hKU hs)
    exact ⟨r, hr, M, hM⟩
  choose! r hr M hM using h
  obtain ⟨T, hTK, hcover⟩ := hK.elim_nhds_subcover (fun s => ball s (r s)) (fun s hs => ball_mem_nhds s (hr s hs))
  refine ⟨∑ s ∈ T, |M s|, fun s hs z hz => ?_⟩
  obtain ⟨s₀, hs₀T, hs₀⟩ := mem_iUnion₂.1 (hcover hs)
  calc ‖EstarY Y s z‖ ≤ M s₀ := hM s₀ (hTK s₀ hs₀T) s (ball_subset_closedBall hs₀) z hz
    _ ≤ |M s₀| := le_abs_self _
    _ ≤ ∑ s ∈ T, |M s| := Finset.single_le_sum (fun i _ => abs_nonneg (M i)) hs₀T

/-- The point `½ + it` of the critical line. -/
def line (t : ℝ) : ℂ := 1 / 2 + t * Complex.I

lemma line_mem_U {t : ℝ} (ht : t ≠ 0) : line t ∈ U := by
  refine mem_U.2 ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg Complex.re h; simp [line] at this
  · have := congrArg Complex.im h; simp [line] at this; exact ht this
  · have := congrArg Complex.re h; simp [line] at this

lemma completed_line_ne_zero (t : ℝ) : completedRiemannZeta (2 * line t) ≠ 0 :=
  PavlovFaddeev.completed_ne_zero_of_one_le_re (by simp [line])

lemma continuousAt_EY_line (Y : ℝ) (z : ℍ) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (fun s => EY Y s z) (line t) := by
  have hU := line_mem_U ht
  obtain ⟨h0, hh, h1⟩ := mem_U.1 hU
  have hE : ContinuousAt (fun s => EstarY Y s z) (line t) :=
    ((differentiableOn_EstarY Y z).differentiableAt (isOpen_U.mem_nhds hU)).continuousAt
  have hΛ : ContinuousAt (fun s : ℂ => completedRiemannZeta (2 * s)) (line t) :=
    ((differentiableAt_completedZeta (mul_ne_zero two_ne_zero h0)
      (fun h => hh (by linear_combination h / 2))).comp _ (differentiableAt_id.const_mul 2)).continuousAt
  exact hE.div hΛ (completed_line_ne_zero t)

/-- `E^Y` is bounded on `𝒟` uniformly for `s = ½ + it`, `t ∈ [a, b]`, `0 < a`. -/
lemma exists_bound_EY_line (Y : ℝ) {a b : ℝ} (ha : 0 < a) :
    ∃ M, ∀ t ∈ Icc a b, ∀ z ∈ fd, ‖EY Y (line t) z‖ ≤ M := by
  have hK : IsCompact (line '' Icc a b) := isCompact_Icc.image (by unfold line; fun_prop)
  have hKU : line '' Icc a b ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact line_mem_U (by linarith [ht.1])
  obtain ⟨M₁, hM₁⟩ := exists_bound_EstarY_compact Y hK hKU
  have hc : ContinuousOn (fun s : ℂ => (completedRiemannZeta (2 * s))⁻¹) (line '' Icc a b) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht0 : t ≠ 0 := by linarith [ht.1]
    obtain ⟨h0, hh, _⟩ := mem_U.1 (line_mem_U ht0)
    exact (((differentiableAt_completedZeta (mul_ne_zero two_ne_zero h0)
      (fun h => hh (by linear_combination h / 2))).comp _
        (differentiableAt_id.const_mul 2)).continuousAt.inv₀ (completed_line_ne_zero t)).continuousWithinAt
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨|M₁| * |M₂|, fun t ht z hz => ?_⟩
  have b1 := hM₁ _ ⟨t, ht, rfl⟩ z (half_le_im_of_mem_fd hz)
  have b2 := hM₂ _ ⟨t, ht, rfl⟩
  rw [EY, div_eq_mul_inv, norm_mul]
  exact mul_le_mul (b1.trans (le_abs_self _)) (b2.trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)

/-- **The Eisenstein wave packet** `Ψ_Y(g)(z) = ∫_a^b g(t) E^Y(z, ½ + it) dt`. -/
def wavePacket (Y : ℝ) (g : ℝ → ℂ) (a b : ℝ) (z : ℍ) : ℂ := ∫ t in a..b, g t * EY Y (line t) z

lemma aestronglyMeasurable_wavePacket (Y : ℝ) {g : ℝ → ℂ} (hg : Continuous g) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : AEStronglyMeasurable (wavePacket Y g a b) (volume.restrict fd) := by
  set c : ℝ → ℝ := fun t => max a (min t b)
  have hc : Continuous c := by fun_prop
  have hc0 : ∀ t, c t ≠ 0 := fun t => by
    have : a ≤ c t := le_max_left _ _
    linarith
  set u : ℝ → ℍ → ℂ := fun t z => g t * EY Y (line (c t)) z
  have hu : Measurable (Function.uncurry u) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun z => ?_) (fun t => ?_)
    · refine hg.mul (continuous_iff_continuousAt.2 fun t => ?_)
      have hl : Continuous line := by unfold line; fun_prop
      exact ContinuousAt.comp (f := fun i => line (c i)) (continuousAt_EY_line Y z (hc0 t))
        (hl.comp hc).continuousAt
    · refine measurable_const.mul ?_
      have := measurable_EstarY Y (line_mem_U (hc0 t))
      exact this.div_const _
  have hm := hu.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc a b))
  refine hm.aestronglyMeasurable.congr (Eventually.of_forall fun z => ?_)
  show ∫ t in Ioc a b, u t z = wavePacket Y g a b z
  rw [wavePacket, intervalIntegral.integral_of_le hab]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  simp only [u, c, min_eq_left ht.2, max_eq_right ht.1.le]

/-- **Eisenstein wave packets are square-integrable on `𝒟`**: for `g` continuous and `0 < a ≤ b`,
`Ψ_Y(g) ∈ L²(𝒟)` (indeed bounded), although no single `E(·, ½ + it)` is. -/
theorem memLp_wavePacket (Y : ℝ) {g : ℝ → ℂ} (hg : Continuous g) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MemLp (wavePacket Y g a b) 2 (volume.restrict fd) := by
  obtain ⟨M, hM⟩ := exists_bound_EY_line Y (b := b) ha
  obtain ⟨Mg, hMg⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hg.continuousOn
  refine MemLp.of_bound (aestronglyMeasurable_wavePacket Y hg ha hab) (|Mg| * |M| * |b - a|) ?_
  refine (ae_restrict_iff' measurableSet_fd).2 (Eventually.of_forall fun z hz => ?_)
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  rw [uIoc_of_le hab] at ht
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
  rw [norm_mul]
  exact mul_le_mul ((hMg t ht').trans (le_abs_self _)) ((hM t ht' z hz).trans (le_abs_self _)) (norm_nonneg _)
    (abs_nonneg _)

/-! ## The Maass–Selberg inner product of two wave packets -/

/-- `max a (min t b)`: the clamp of `t` to `[a, b]`. -/
def clamp (a b t : ℝ) : ℝ := max a (min t b)

lemma continuous_clamp (a b : ℝ) : Continuous (clamp a b) := by unfold clamp; fun_prop

lemma clamp_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clamp a b t ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

lemma clamp_of_mem {a b t : ℝ} (ht : t ∈ Ioc a b) : clamp a b t = t := by
  simp only [clamp, min_eq_left ht.2, max_eq_right ht.1.le]

lemma line_neg (t : ℝ) : line (-t) = conj (line t) := by
  apply Complex.ext <;> simp [line]

lemma measurable_EY_line_comp (Y : ℝ) {κ : ℝ → ℝ} (hκ : Continuous κ) (hκ0 : ∀ t, κ t ≠ 0) :
    Measurable fun q : ℝ × ℍ => EY Y (line (κ q.1)) q.2 := by
  have hl : Continuous line := by unfold line; fun_prop
  refine measurable_uncurry_of_continuous_of_measurable (u := fun t z => EY Y (line (κ t)) z)
    (fun z => continuous_iff_continuousAt.2 fun t => ?_) (fun t => ?_)
  · exact ContinuousAt.comp (f := fun i => line (κ i)) (continuousAt_EY_line Y z (hκ0 t)) (hl.comp hκ).continuousAt
  · exact (measurable_EstarY Y (line_mem_U (hκ0 t))).div_const _

/-- **The Maass–Selberg kernel** of two frequencies: the right side of `ModMaassSelberg.maass_selberg_phi` at
`s₁ = ½ + it₁`, `s₂ = ½ − it₂ = conj(½ + it₂)`. -/
def msKernel (Y t₁ t₂ : ℝ) : ℂ :=
  ((Y : ℂ) ^ (line t₁ + line (-t₂) - 1) - PavlovFaddeev.scatteringMatrix (line t₁) *
      PavlovFaddeev.scatteringMatrix (line (-t₂)) * (Y : ℂ) ^ (1 - line t₁ - line (-t₂))) /
      (line t₁ + line (-t₂) - 1) +
    (PavlovFaddeev.scatteringMatrix (line (-t₂)) * (Y : ℂ) ^ (line t₁ - line (-t₂)) -
      PavlovFaddeev.scatteringMatrix (line t₁) * (Y : ℂ) ^ (line (-t₂) - line t₁)) / (line t₁ - line (-t₂))

/-- **The kernel explicitly**: with `φ₁ = φ(½ + it₁)`, `φ₂ = φ(½ + it₂)`, `K_Y(t₁, t₂) =
(Y^{i(t₁−t₂)} − φ₁ conj φ₂ Y^{−i(t₁−t₂)})/(i(t₁ − t₂)) + (conj φ₂ Y^{i(t₁+t₂)} − φ₁ Y^{−i(t₁+t₂)})/(i(t₁ + t₂))`. -/
theorem msKernel_eq (Y t₁ t₂ : ℝ) : msKernel Y t₁ t₂ =
    ((Y : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * Complex.I) - PavlovFaddeev.scatteringMatrix (line t₁) *
        conj (PavlovFaddeev.scatteringMatrix (line t₂)) * (Y : ℂ) ^ (-(((t₁ - t₂ : ℝ) : ℂ) * Complex.I))) /
        (((t₁ - t₂ : ℝ) : ℂ) * Complex.I) +
      (conj (PavlovFaddeev.scatteringMatrix (line t₂)) * (Y : ℂ) ^ (((t₁ + t₂ : ℝ) : ℂ) * Complex.I) -
        PavlovFaddeev.scatteringMatrix (line t₁) * (Y : ℂ) ^ (-(((t₁ + t₂ : ℝ) : ℂ) * Complex.I))) /
        (((t₁ + t₂ : ℝ) : ℂ) * Complex.I) := by
  have e1 : line t₁ + line (-t₂) - 1 = ((t₁ - t₂ : ℝ) : ℂ) * Complex.I := by simp [line]; ring
  have e2 : 1 - line t₁ - line (-t₂) = -(((t₁ - t₂ : ℝ) : ℂ) * Complex.I) := by simp [line]; ring
  have e3 : line t₁ - line (-t₂) = ((t₁ + t₂ : ℝ) : ℂ) * Complex.I := by simp [line]; ring
  have e4 : line (-t₂) - line t₁ = -(((t₁ + t₂ : ℝ) : ℂ) * Complex.I) := by simp [line]; ring
  rw [msKernel, e1, e2, e3, e4, line_neg, PavlovFaddeev.scatteringMatrix_conj]

/-- **The Maass–Selberg relation for wave packets**: for `Y ≥ 1`, `g, h` continuous and `0 < a ≤ b`,
`∫_𝒟 Ψ_Y(g) conj Ψ_Y(h) dμ = ∫∫_{[a,b]²} g(t₁) conj h(t₂) K_Y(t₁, t₂) dt₁ dt₂` with the Maass–Selberg kernel
`K_Y` (`msKernel`, `msKernel_eq`): Fubini, and `ModMaassSelberg.maass_selberg_phi` off the diagonal `t₁ = t₂`. -/
theorem integral_wavePacket_mul_conj {Y : ℝ} (hY : 1 ≤ Y) {g h : ℝ → ℂ} (hg : Continuous g) (hh : Continuous h)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ z in fd, wavePacket Y g a b z * conj (wavePacket Y h a b z) =
      ∫ p in Ioc a b ×ˢ Ioc a b, g p.1 * conj (h p.2) * msKernel Y p.1 p.2 := by
  set κ := clamp a b
  have hκ : Continuous κ := continuous_clamp a b
  have hκ0 : ∀ t, κ t ≠ 0 := fun t => by have := (clamp_mem hab t).1; linarith
  have hκ0' : ∀ t, -κ t ≠ 0 := fun t => neg_ne_zero.2 (hκ0 t)
  set ν₁ : Measure ℝ := volume.restrict (Ioc a b)
  set A : ℝ → ℍ → ℂ := fun t z => g (κ t) * EY Y (line (κ t)) z
  set B : ℝ → ℍ → ℂ := fun t z => conj (h (κ t)) * EY Y (line (-κ t)) z
  have hA : ∀ z, wavePacket Y g a b z = ∫ t, A t z ∂ν₁ := fun z => by
    rw [wavePacket, intervalIntegral.integral_of_le hab]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    simp only [A, κ, clamp_of_mem ht]
  have hB : ∀ z, conj (wavePacket Y h a b z) = ∫ t, B t z ∂ν₁ := fun z => by
    rw [wavePacket, intervalIntegral.integral_of_le hab, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    simp only [B, κ, clamp_of_mem ht, map_mul, line_neg, EY_conj]
  -- the bounds
  obtain ⟨M, hM⟩ := exists_bound_EY_line Y (b := b) ha
  obtain ⟨Mg, hMg⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨Mh, hMh⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hh.continuousOn
  have hAb : ∀ t, ∀ z ∈ fd, ‖A t z‖ ≤ |Mg| * |M| := fun t z hz => by
    simp only [A, norm_mul]
    exact mul_le_mul ((hMg _ (clamp_mem hab t)).trans (le_abs_self _))
      ((hM _ (clamp_mem hab t) z hz).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)
  have hBb : ∀ t, ∀ z ∈ fd, ‖B t z‖ ≤ |Mh| * |M| := fun t z hz => by
    simp only [B, norm_mul, Complex.norm_conj, line_neg, EY_conj]
    exact mul_le_mul ((hMh _ (clamp_mem hab t)).trans (le_abs_self _))
      ((hM _ (clamp_mem hab t) z hz).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)
  -- measurability
  have mA : Measurable fun q : ℍ × (ℝ × ℝ) => A q.2.1 q.1 := by
    have h1 := (measurable_EY_line_comp Y hκ hκ0).comp (measurable_snd.fst.prodMk measurable_fst : Measurable fun q : ℍ × (ℝ × ℝ) => (q.2.1, q.1))
    exact ((hg.comp hκ).measurable.comp measurable_snd.fst).mul h1
  have mB : Measurable fun q : ℍ × (ℝ × ℝ) => B q.2.2 q.1 := by
    have h1 := (measurable_EY_line_comp Y hκ.neg hκ0').comp (measurable_snd.snd.prodMk measurable_fst : Measurable fun q : ℍ × (ℝ × ℝ) => (q.2.2, q.1))
    exact ((Complex.continuous_conj.comp (hh.comp hκ)).measurable.comp measurable_snd.snd).mul h1
  -- Fubini
  have hint : Integrable (Function.uncurry fun (z : ℍ) (p : ℝ × ℝ) => A p.1 z * B p.2 z)
      ((volume.restrict fd).prod (ν₁.prod ν₁)) := by
    refine Integrable.mono' (integrable_const ((|Mg| * |M|) * (|Mh| * |M|))) (mA.mul mB).aestronglyMeasurable ?_
    have hfst := Measure.quasiMeasurePreserving_fst (μ := volume.restrict fd) (ν := ν₁.prod ν₁) |>.ae
      (ae_restrict_mem measurableSet_fd)
    filter_upwards [hfst] with q hq
    simp only [Function.uncurry, norm_mul]
    rw [← norm_mul]
    simp only [norm_mul]
    exact mul_le_mul (hAb _ _ hq) (hBb _ _ hq) (norm_nonneg _) (by positivity)
  have hL : ∀ z, wavePacket Y g a b z * conj (wavePacket Y h a b z) = ∫ p, A p.1 z * B p.2 z ∂(ν₁.prod ν₁) :=
    fun z => by rw [hA, hB]; exact (integral_prod_mul (fun t => A t z) (fun t => B t z)).symm
  simp_rw [hL]
  rw [integral_integral_swap hint, Measure.volume_eq_prod, ← Measure.prod_restrict]
  -- the diagonal is null
  have hdiag : ∀ᵐ p ∂(ν₁.prod ν₁), p.1 ≠ p.2 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    refine (Measure.measure_prod_null (measurableSet_diagonal (α := ℝ))).2 (Eventually.of_forall fun x => ?_)
    have : (Prod.mk x ⁻¹' diagonal ℝ) = {x} := by ext y; simp [diagonal, eq_comm]
    simp only [Pi.zero_apply]
    rw [this]
    exact le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self {x}).trans (le_of_eq Real.volume_singleton))
      zero_le
  have hmem : ∀ᵐ p ∂(ν₁.prod ν₁), p ∈ Ioc a b ×ˢ Ioc a b := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  refine integral_congr_ae ?_
  filter_upwards [hdiag, hmem] with p hp hpm
  obtain ⟨h1, h2⟩ := hpm
  have ht1 : p.1 ≠ 0 := by linarith [h1.1]
  have ht2 : -p.2 ≠ 0 := neg_ne_zero.2 (by linarith [h2.1])
  simp only [A, B, κ, clamp_of_mem h1, clamp_of_mem h2]
  have e : ∀ z, g p.1 * EY Y (line p.1) z * (conj (h p.2) * EY Y (line (-p.2)) z) =
      g p.1 * conj (h p.2) * (EY Y (line p.1) z * EY Y (line (-p.2)) z) := fun z => by ring
  simp_rw [e]
  rw [integral_const_mul]
  congr 1
  have hs₁ := line_mem_U ht1
  have hs₂ := line_mem_U ht2
  have hne1 : line p.1 + line (-p.2) ≠ 1 := fun hc => by
    have := congrArg Complex.im hc; simp [line] at this; exact hp (by linarith)
  have hne2 : line p.1 ≠ line (-p.2) := fun hc => by
    have := congrArg Complex.im hc; simp [line] at this; linarith [h1.1, h2.1]
  rw [maass_selberg_phi hY hs₁ hs₂ hne1 hne2 (completed_line_ne_zero _) (completed_line_ne_zero _), msKernel]

end ModWavePackets
