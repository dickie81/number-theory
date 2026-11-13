import Mathlib
import BallSharp

/-! # The test function of the pivot inequality: `φ(s) = (999/1000)(1 − K(s/5))/s²`

Plain statement. `φ(s) = (999/1000)((4/3)F_{1/5}(s) − (1/3)F_{2/5}(s))`, with the atom `F_β(s) = (1 − sinc²(βs))/s²`, is
`(999/1000)(1 − K(s/5))/s²` with `K(x) = sinc²x·(1 + sin²x/3)` (`phi_eq`). It is the weight that `PivotSharp` puts on
the zeros at height `t`, as `φ(t/N)/N²`.

* **The transform** (`integral_phi_cos`): `∫φ(s)cos(sv) ds = φ̂(v) = (999/1000)π((25/9)((2/5 − |v|)⁺)³ −
  (25/144)((4/5 − |v|)⁺)³)`. It vanishes for `|v| ≥ 4/5` (`phiT_eq_zero`) and `φ̂(0) = (999/1000)·4π/45`
  (`phiT_zero`).
* **The bounds**: `0 ≤ K ≤ 1` (`kk_le_one`), so `φ ≥ 0` (`phi_nonneg`), and `φ(s)(s² + 1/16) ≤ 1` (`phi_mul_le`): `φ`
  lies below the weight `1/(¼ + t²)` of the zeros at every scale `N ≥ 2`. Near `0`, `φ(s) ≤ s²/3000` (`phi_le_sq`).
* **The entire extension** `φ_ℂ(z) = (999/1000)H(z)/z²` (`phiE`, made entire by `dslope`), with the strip bound
  `‖φ_ℂ(z)‖ ≤ K/(1 + (Re z)²)` on `|Im z| ≤ 1` (`phiE_strip`) and the pole bound `‖φ_ℂ(iy)‖ ≤ y²/3000` for
  `0 < y ≤ 1/4` (`norm_phiE_I_le`).

The proofs.

- **The triangle mixture.** `1 − sinc²y = ¼∫_{−2}^{2}(2 − |w|)(1 − cos(wy)) dw` (`fat_mix`, from the triangle's
  transform `integral_tri_cos`), and `∫(1 − cos(as))cos(sv)/s² ds = π(a − |v|)⁺` is the Fejér triangle
  (`integral_fejer_cos`, from `WeilForm.integral_hsq_cos` for the box). Fubini (`integral_fat_cos`) gives
  `∫F_β(s)cos(sv) ds = π((2β − |v|)⁺)³/(12β²)`, from the ramp integral `integral_ramp`.
- **`K ≤ 1`** is `sin²x(1 + sin²x/3) ≤ x²`: for `x² ≥ 4/3` it is `4/3 ≤ x²`; below, `|sin x| ≤ |x| − |x|³/6 + |x|⁵/120`
  and a polynomial inequality of degree 9.
- **The pole** is `−(999/1000)H(iy)/y²` with `H(iy) = 1 − (4/3)(sinh a/a)² + (1/3)(sinh 2a/2a)²`, `a = y/5`, whose
  terms of order `a²` cancel: `|H(iy)| ≤ a⁴/5` (`abs_hH_I_le`), from `sinh` to order 5 (`sinh_near`).
-/

open Real MeasureTheory WeilForm WeilTest DirMean BallDensity ShortWeil BallCutoff BallSharp

noncomputable section

namespace PivotPhi


/-- The triangle's cosine transform: `∫_{−2}^{2}(2 − |w|)cos(cw) dw = 4 sin²c/c²`. -/
lemma integral_tri_cos {c : ℝ} (hc : c ≠ 0) :
    ∫ w in (-2 : ℝ)..2, (2 - |w|) * Real.cos (c * w) = 4 * Real.sin c ^ 2 / c ^ 2 := by
  have hcont : Continuous fun w : ℝ => (2 - |w|) * Real.cos (c * w) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  have e1 : ∫ w in (-2 : ℝ)..0, (2 - |w|) * Real.cos (c * w) = ∫ w in (-2 : ℝ)..0, (2 + w) * Real.cos (c * w) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hw
    simp only [abs_of_nonpos hw.2]; ring
  have e2 : ∫ w in (0 : ℝ)..2, (2 - |w|) * Real.cos (c * w) = ∫ w in (0 : ℝ)..2, (2 - w) * Real.cos (c * w) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hw
    simp only [abs_of_nonneg hw.1]
  have d1 : ∀ w : ℝ, HasDerivAt (fun w => (2 + w) * Real.sin (c * w) / c + Real.cos (c * w) / c ^ 2)
      ((2 + w) * Real.cos (c * w)) w := by
    intro w
    have h1 := (((hasDerivAt_id w).const_add 2).mul ((hasDerivAt_id w).const_mul c).sin).div_const c
    have h2 := (((hasDerivAt_id w).const_mul c).cos).div_const (c ^ 2)
    refine (h1.add h2).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have d2 : ∀ w : ℝ, HasDerivAt (fun w => (2 - w) * Real.sin (c * w) / c - Real.cos (c * w) / c ^ 2)
      ((2 - w) * Real.cos (c * w)) w := by
    intro w
    have h1 := (((hasDerivAt_id w).const_sub 2).mul ((hasDerivAt_id w).const_mul c).sin).div_const c
    have h2 := (((hasDerivAt_id w).const_mul c).cos).div_const (c ^ 2)
    refine (h1.sub h2).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  rw [e1, e2, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => d1 w)
      ((by fun_prop : Continuous fun w : ℝ => (2 + w) * Real.cos (c * w)).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => d2 w)
      ((by fun_prop : Continuous fun w : ℝ => (2 - w) * Real.cos (c * w)).intervalIntegrable _ _)]
  have hcos : Real.cos (2 * c) = 1 - 2 * Real.sin c ^ 2 := by rw [Real.cos_two_mul, Real.cos_sq']; ring
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, mul_neg, Real.sin_neg, Real.cos_neg, add_zero, sub_zero,
    zero_div]
  rw [show c * 2 = 2 * c by ring, hcos]
  field_simp
  ring

/-- `∫_{−2}^{2}(2 − |w|) dw = 4`. -/
lemma integral_tri : ∫ w in (-2 : ℝ)..2, (2 - |w|) = 4 := by
  have h := intervalIntegral.integral_comp_neg (a := (-2 : ℝ)) (b := 0) (fun w : ℝ => 2 - |w|)
  have hcont : Continuous fun w : ℝ => 2 - |w| := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  have e1 : ∫ w in (-2 : ℝ)..0, (2 - |w|) = ∫ w in (-2 : ℝ)..0, (2 + w) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hw
    simp only [abs_of_nonpos hw.2]; ring
  have e2 : ∫ w in (0 : ℝ)..2, (2 - |w|) = ∫ w in (0 : ℝ)..2, (2 - w) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hw
    simp only [abs_of_nonneg hw.1]
  have c1 : Continuous fun _ : ℝ => (2 : ℝ) := continuous_const
  have c2 : Continuous fun w : ℝ => w := continuous_id
  rw [e1, e2, intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
    intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
  simp
  norm_num


/-- `(1 − cos(as))/s²` is half the squared transform of the box `1_{[−a/2, a/2]}`. -/
lemma one_sub_cos_div_sq_eq {a s : ℝ} (ha : 0 < a) (hs : s ≠ 0) :
    (1 - Real.cos (a * s)) / s ^ 2 = hsq (bx (a / 2)) (a / 2) s / 2 := by
  rw [hsq_bx_eq (by positivity) hs]
  have : Real.cos (a * s) = 1 - 2 * Real.sin (a / 2 * s) ^ 2 := by
    rw [show a * s = 2 * (a / 2 * s) by ring, Real.cos_two_mul, Real.cos_sq']; ring
  rw [this]; field_simp; ring

lemma ae_ne_zero : ∀ᵐ s : ℝ, s ≠ 0 := by
  have h := (Set.countable_singleton (0 : ℝ)).ae_notMem (μ := volume)
  filter_upwards [h] with s hs
  simpa using hs

lemma fejer_ae {a : ℝ} (ha : 0 < a) (v : ℝ) :
    (fun s => (1 - Real.cos (a * s)) / s ^ 2 * Real.cos (s * v)) =ᵐ[volume]
      fun s => 1 / 2 * (hsq (bx (a / 2)) (a / 2) s * Real.cos (s * v)) := by
  filter_upwards [ae_ne_zero] with s hs
  rw [one_sub_cos_div_sq_eq ha hs]; ring

/-- **The Fejér triangle**: `∫(1 − cos(as))cos(sv)/s² ds = π(a − |v|)⁺` for `a ≥ 0`. -/
lemma integral_fejer_cos {a : ℝ} (ha : 0 ≤ a) (v : ℝ) :
    ∫ s, (1 - Real.cos (a * s)) / s ^ 2 * Real.cos (s * v) = π * max (a - |v|) 0 := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  rw [integral_congr_ae (fejer_ae ha v), integral_const_mul,
    integral_hsq_cos (esupp_bx _) (by positivity), autocorr_bx]
  rw [show 2 * (a / 2) = a by ring]
  ring

/-- The triangle `(2 − |w|)⁺`. -/
def tri (w : ℝ) : ℝ := max (2 - |w|) 0

lemma tri_nonneg (w : ℝ) : 0 ≤ tri w := le_max_right _ _

lemma tri_le_two (w : ℝ) : tri w ≤ 2 := max_le (by linarith [abs_nonneg w]) (by norm_num)

lemma tri_eq {w : ℝ} (hw : |w| ≤ 2) : tri w = 2 - |w| := max_eq_left (by linarith)

lemma tri_eq_zero {w : ℝ} (hw : 2 ≤ |w|) : tri w = 0 := max_eq_right (by linarith)

lemma continuous_tri : Continuous tri := by unfold tri; fun_prop

lemma measurable_tri : Measurable tri := continuous_tri.measurable

lemma integral_tri' : ∫ w in (-2 : ℝ)..2, tri w = 4 := by
  rw [← integral_tri]
  refine intervalIntegral.integral_congr fun w hw => ?_
  rw [Set.uIcc_of_le (by norm_num)] at hw
  exact tri_eq (abs_le.2 hw)

/-- The atom `F_β(s) = (1 − sinc²(βs))/s²` (with Lean's `x/0 = 0`). -/
def fat (β s : ℝ) : ℝ := (1 - (Real.sin (β * s) / (β * s)) ^ 2) / s ^ 2

lemma cos_abs_mul (β w s : ℝ) : Real.cos (β * |w| * s) = Real.cos (β * s * w) := by
  rcases abs_cases w with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]; ring_nf
  · rw [h1, ← Real.cos_neg]; ring_nf

/-- **The triangle mixture**: `F_β(s) = ¼∫_{−2}^{2}(2 − |w|)⁺(1 − cos(β|w|s))/s² dw` for `s ≠ 0`. -/
lemma fat_mix {β s : ℝ} (hβ : β ≠ 0) (hs : s ≠ 0) :
    fat β s = 1 / 4 * ∫ w in (-2 : ℝ)..2, tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2) := by
  have hc : β * s ≠ 0 := mul_ne_zero hβ hs
  have e : ∀ w ∈ Set.uIcc (-2 : ℝ) 2, tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2) =
      (2 - |w|) / s ^ 2 - (2 - |w|) * Real.cos ((β * s) * w) / s ^ 2 := by
    intro w hw
    rw [Set.uIcc_of_le (by norm_num)] at hw
    rw [tri_eq (abs_le.2 hw), cos_abs_mul]
    ring
  have c1 : Continuous fun w : ℝ => (2 - |w|) / s ^ 2 := by fun_prop
  have c2 : Continuous fun w : ℝ => (2 - |w|) * Real.cos ((β * s) * w) / s ^ 2 := by fun_prop
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub (c1.intervalIntegrable _ _)
    (c2.intervalIntegrable _ _), intervalIntegral.integral_div, intervalIntegral.integral_div, integral_tri,
    integral_tri_cos hc]
  unfold fat
  field_simp

/-- `(1 − cos x)/s² ≤ 4max(1, β²)/(1 + s²)` when `x = β|w|s`, `|w| ≤ 2`. -/
lemma one_sub_cos_div_le {β w s : ℝ} (hw : |w| ≤ 2) :
    (1 - Real.cos (β * |w| * s)) / s ^ 2 ≤ 4 * max 1 (β ^ 2) / (1 + s ^ 2) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have hs2 : 0 < s ^ 2 := by positivity
  have h1 : 1 - Real.cos (β * |w| * s) ≤ (β * |w| * s) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := β * |w| * s); linarith
  have h2 : 1 - Real.cos (β * |w| * s) ≤ 2 := by linarith [Real.neg_one_le_cos (β * |w| * s)]
  have hw2 : |w| ^ 2 ≤ 4 := by nlinarith [abs_nonneg w]
  have hm1 : 1 ≤ max 1 (β ^ 2) := le_max_left _ _
  have hm2 : β ^ 2 ≤ max 1 (β ^ 2) := le_max_right _ _
  rw [div_le_div_iff₀ hs2 (by positivity)]
  have hx : (β * |w| * s) ^ 2 = β ^ 2 * |w| ^ 2 * s ^ 2 := by ring
  rw [hx] at h1
  have hb0 : 0 ≤ β ^ 2 := sq_nonneg β
  nlinarith [mul_le_mul_of_nonneg_left hw2 hb0, mul_le_mul_of_nonneg_left h1 hs2.le,
    mul_le_mul_of_nonneg_left h2 hs2.le]

/-- **The ramp integral**: `∫_0^2(2 − w)(βw − a)⁺ dw = ((2β − a)⁺)³/(6β²)` for `a ≥ 0`. -/
lemma integral_ramp {β : ℝ} (hβ : 0 < β) {a : ℝ} (ha : 0 ≤ a) :
    ∫ w in (0 : ℝ)..2, (2 - w) * max (β * w - a) 0 = max (2 * β - a) 0 ^ 3 / (6 * β ^ 2) := by
  rcases le_or_gt (2 * β) a with hab | hab
  · rw [max_eq_right (by linarith)]
    have : ∀ w ∈ Set.uIcc (0 : ℝ) 2, (2 - w) * max (β * w - a) 0 = 0 := by
      intro w hw
      rw [Set.uIcc_of_le (by norm_num)] at hw
      rw [max_eq_right (by nlinarith [hw.2]), mul_zero]
    rw [intervalIntegral.integral_congr this]; simp
  · set w0 := a / β with hw0
    have hw00 : 0 ≤ w0 := div_nonneg ha hβ.le
    have hw02 : w0 ≤ 2 := by rw [hw0, div_le_iff₀ hβ]; linarith
    have hcont : Continuous fun w : ℝ => (2 - w) * max (β * w - a) 0 := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := w0) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    have e1 : ∀ w ∈ Set.uIcc (0 : ℝ) w0, (2 - w) * max (β * w - a) 0 = 0 := by
      intro w hw
      rw [Set.uIcc_of_le hw00] at hw
      have : β * w ≤ a := by
        have := hw.2; rw [hw0, le_div_iff₀ hβ] at this; linarith
      rw [max_eq_right (by linarith), mul_zero]
    have e2 : ∀ w ∈ Set.uIcc w0 2, (2 - w) * max (β * w - a) 0 = (2 - w) * (β * w - a) := by
      intro w hw
      rw [Set.uIcc_of_le hw02] at hw
      have : a ≤ β * w := by
        have := hw.1; rw [hw0, div_le_iff₀ hβ] at this; linarith
      rw [max_eq_left (by linarith)]
    have hP : ∀ w : ℝ, HasDerivAt (fun w => -(β * w ^ 3 / 3) + (2 * β + a) * w ^ 2 / 2 - 2 * a * w)
        ((2 - w) * (β * w - a)) w := by
      intro w
      have h1 := ((hasDerivAt_pow 3 w).const_mul β).div_const 3
      have h2 := ((hasDerivAt_pow 2 w).const_mul (2 * β + a)).div_const 2
      have h3 := (hasDerivAt_id w).const_mul (2 * a)
      refine ((h1.neg.add h2).sub h3).congr_deriv ?_
      push_cast; ring
    rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hP w)
        ((by fun_prop : Continuous fun w : ℝ => (2 - w) * (β * w - a)).intervalIntegrable _ _),
      max_eq_left (by linarith)]
    simp only [intervalIntegral.integral_zero, zero_add]
    rw [hw0]
    field_simp
    ring

/-- **The symmetric ramp**: `∫_{−2}^{2}(2 − |w|)⁺(β|w| − a)⁺ dw = 2((2β − a)⁺)³/(6β²)`. -/
lemma integral_tri_ramp {β : ℝ} (hβ : 0 < β) {a : ℝ} (ha : 0 ≤ a) :
    ∫ w in (-2 : ℝ)..2, tri w * max (β * |w| - a) 0 = 2 * (max (2 * β - a) 0 ^ 3 / (6 * β ^ 2)) := by
  have hcont : Continuous fun w : ℝ => tri w * max (β * |w| - a) 0 := by
    have := continuous_tri; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  have hneg : ∫ w in (-2 : ℝ)..0, tri w * max (β * |w| - a) 0 = ∫ w in (0 : ℝ)..2, (2 - w) * max (β * w - a) 0 := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 2) (fun w : ℝ => tri w * max (β * |w| - a) 0)
    simp only [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hw
    rw [tri_eq (by rw [abs_neg, abs_of_nonneg hw.1]; exact hw.2), abs_neg, abs_of_nonneg hw.1]
  have hpos : ∫ w in (0 : ℝ)..2, tri w * max (β * |w| - a) 0 = ∫ w in (0 : ℝ)..2, (2 - w) * max (β * w - a) 0 := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hw
    rw [tri_eq (by rw [abs_of_nonneg hw.1]; exact hw.2), abs_of_nonneg hw.1]
  rw [hneg, hpos, integral_ramp hβ ha]
  ring


lemma one_sub_cos_div_nonneg (x s : ℝ) : 0 ≤ (1 - Real.cos x) / s ^ 2 :=
  div_nonneg (by linarith [Real.cos_le_one x]) (sq_nonneg s)

/-- The integrand of the mixture is dominated by `8max(1, β²)/(1 + s²)`. -/
lemma mix_bound (β v s w : ℝ) :
    ‖tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2) * Real.cos (s * v)‖ ≤
      8 * max 1 (β ^ 2) / (1 + s ^ 2) * 1 := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (tri_nonneg w),
    abs_of_nonneg (one_sub_cos_div_nonneg _ _), mul_one]
  have hc := Real.abs_cos_le_one (s * v)
  rcases le_or_gt |w| 2 with hw | hw
  · have h1 := one_sub_cos_div_le (β := β) (s := s) hw
    have h2 := tri_le_two w
    have h0 := one_sub_cos_div_nonneg (β * |w| * s) s
    calc tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2) * |Real.cos (s * v)|
        ≤ 2 * (4 * max 1 (β ^ 2) / (1 + s ^ 2)) * 1 := by
          gcongr
      _ = 8 * max 1 (β ^ 2) / (1 + s ^ 2) := by ring
  · rw [tri_eq_zero hw.le]; simp only [zero_mul]; positivity

/-- **The atom's transform**: `∫F_β(s)cos(sv) ds = π((2β − |v|)⁺)³/(12β²)`. -/
lemma integral_fat_cos {β : ℝ} (hβ : 0 < β) (v : ℝ) :
    ∫ s, fat β s * Real.cos (s * v) = π * max (2 * β - |v|) 0 ^ 3 / (12 * β ^ 2) := by
  set f : ℝ → ℝ → ℝ := fun s w => tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2) * Real.cos (s * v) with hf
  set ν := volume.restrict (Set.Ioc (-2 : ℝ) 2) with hν
  have hae : (fun s => fat β s * Real.cos (s * v)) =ᵐ[volume] fun s => 1 / 4 * ∫ w, f s w ∂ν := by
    filter_upwards [ae_ne_zero] with s hs
    rw [fat_mix hβ.ne' hs, intervalIntegral.integral_of_le (by norm_num), mul_assoc, ← integral_mul_const]
  have hM : Integrable (fun s : ℝ => 8 * max 1 (β ^ 2) / (1 + s ^ 2)) := by
    have := integrable_inv_one_add_sq.const_mul (8 * max 1 (β ^ 2))
    simpa [div_eq_mul_inv] using this
  have hint : Integrable (Function.uncurry f) (volume.prod ν) := by
    have hM2 := hM.mul_prod (integrable_const (1 : ℝ) (μ := ν))
    refine hM2.mono' ?_ (Filter.Eventually.of_forall fun p => mix_bound β v p.1 p.2)
    have htm := measurable_tri
    refine Measurable.aestronglyMeasurable ?_
    simp only [hf, Function.uncurry_def]
    fun_prop
  rw [integral_congr_ae hae, integral_const_mul, integral_integral_swap hint]
  have hinner : ∀ w, ∫ s, f s w = tri w * (π * max (β * |w| - |v|) 0) := by
    intro w
    simp only [hf]
    have e : ∀ s, tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2) * Real.cos (s * v) =
        tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2 * Real.cos (s * v)) := fun s => by ring
    simp_rw [e]
    rw [integral_const_mul, integral_fejer_cos (by positivity)]
  simp_rw [hinner]
  rw [hν, ← intervalIntegral.integral_of_le (by norm_num)]
  have e : ∀ w, tri w * (π * max (β * |w| - |v|) 0) = π * (tri w * max (β * |w| - |v|) 0) := fun w => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_tri_ramp hβ (abs_nonneg v)]
  field_simp
  ring

lemma integrable_fat_cos {β : ℝ} (hβ : 0 < β) (v : ℝ) : Integrable fun s => fat β s * Real.cos (s * v) := by
  have hM : Integrable (fun s : ℝ => 8 * max 1 (β ^ 2) / (1 + s ^ 2)) := by
    have := integrable_inv_one_add_sq.const_mul (8 * max 1 (β ^ 2))
    simpa [div_eq_mul_inv] using this
  refine hM.mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    unfold fat; fun_prop
  · filter_upwards [ae_ne_zero] with s hs
    have hc1 : Continuous fun w : ℝ => tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2) := by
      have := continuous_tri; fun_prop
    have hc2 : Continuous fun w : ℝ => tri w * (4 * max 1 (β ^ 2) / (1 + s ^ 2)) := by
      have := continuous_tri; fun_prop
    have hX : ∀ w ∈ Set.Icc (-2 : ℝ) 2, tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2) ≤
        tri w * (4 * max 1 (β ^ 2) / (1 + s ^ 2)) := fun w hw =>
      mul_le_mul_of_nonneg_left (one_sub_cos_div_le (abs_le.2 hw)) (tri_nonneg w)
    have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
      (hc1.intervalIntegrable (-2) 2) (hc2.intervalIntegrable (-2) 2) hX
    rw [intervalIntegral.integral_mul_const, integral_tri'] at hmono
    have hnn : 0 ≤ ∫ w in (-2 : ℝ)..2, tri w * ((1 - Real.cos (β * |w| * s)) / s ^ 2) :=
      intervalIntegral.integral_nonneg (by norm_num) fun w _ =>
        mul_nonneg (tri_nonneg w) (one_sub_cos_div_nonneg _ _)
    have hfat := fat_mix hβ.ne' hs
    rw [Real.norm_eq_abs, abs_mul]
    have hc := Real.abs_cos_le_one (s * v)
    have hpos : 0 ≤ 4 * max 1 (β ^ 2) / (1 + s ^ 2) := by positivity
    have hf0 : 0 ≤ fat β s := by rw [hfat]; positivity
    rw [abs_of_nonneg hf0]
    calc fat β s * |Real.cos (s * v)| ≤ fat β s * 1 := mul_le_mul_of_nonneg_left hc hf0
      _ ≤ 8 * max 1 (β ^ 2) / (1 + s ^ 2) := by
        rw [mul_one, hfat]
        have : 8 * max 1 (β ^ 2) / (1 + s ^ 2) = 2 * (4 * max 1 (β ^ 2) / (1 + s ^ 2)) := by ring
        rw [this]
        linarith


/-! ## The test function `φ` and its transform -/

/-- **The test function** `φ(s) = (999/1000)((4/3)F_{1/5}(s) − (1/3)F_{2/5}(s)) = (999/1000)(1 − K(s/5))/s²`,
`K(x) = sinc²x(1 + sin²x/3)`. -/
def phi (s : ℝ) : ℝ := 999 / 1000 * (4 / 3 * fat (1 / 5) s - 1 / 3 * fat (2 / 5) s)

/-- **Its cosine transform** `φ̂(v) = (999/1000)π((25/9)((2/5 − |v|)⁺)³ − (25/144)((4/5 − |v|)⁺)³)`. -/
def phiT (v : ℝ) : ℝ :=
  999 / 1000 * π * (25 / 9 * max (2 / 5 - |v|) 0 ^ 3 - 25 / 144 * max (4 / 5 - |v|) 0 ^ 3)

lemma integrable_phi_cos (v : ℝ) : Integrable fun s => phi s * Real.cos (s * v) := by
  have h1 := (integrable_fat_cos (β := 1 / 5) (by norm_num) v).const_mul (999 / 1000 * (4 / 3))
  have h2 := (integrable_fat_cos (β := 2 / 5) (by norm_num) v).const_mul (999 / 1000 * (1 / 3))
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.sub_apply, phi]; ring

/-- **The transform**: `∫φ(s)cos(sv) ds = φ̂(v)`. -/
lemma integral_phi_cos (v : ℝ) : ∫ s, phi s * Real.cos (s * v) = phiT v := by
  have h1 := integrable_fat_cos (β := 1 / 5) (by norm_num) v
  have h2 := integrable_fat_cos (β := 2 / 5) (by norm_num) v
  have e : (fun s => phi s * Real.cos (s * v)) = fun s =>
      999 / 1000 * (4 / 3) * (fat (1 / 5) s * Real.cos (s * v)) -
        999 / 1000 * (1 / 3) * (fat (2 / 5) s * Real.cos (s * v)) := by
    funext s; simp only [phi]; ring
  rw [e, integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
    integral_fat_cos (by norm_num), integral_fat_cos (by norm_num)]
  unfold phiT
  rw [show 2 * (1 / 5 : ℝ) = 2 / 5 by norm_num, show 2 * (2 / 5 : ℝ) = 4 / 5 by norm_num]
  ring

/-- **Compact support**: `φ̂(v) = 0` for `|v| ≥ 4/5`. -/
lemma phiT_eq_zero {v : ℝ} (hv : 4 / 5 ≤ |v|) : phiT v = 0 := by
  unfold phiT
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- **The mass**: `φ̂(0) = (999/1000)·4π/45`. -/
lemma phihat_zero : phiT 0 = 999 / 1000 * (4 * π / 45) := by
  unfold phiT
  rw [abs_zero, sub_zero, sub_zero, max_eq_left (by norm_num), max_eq_left (by norm_num)]
  ring

lemma phihat_neg (v : ℝ) : phiT (-v) = phiT v := by unfold phiT; rw [abs_neg]

/-! ## The closed form and the pointwise bounds -/

/-- `K(x) = sinc²x(1 + sin²x/3)`. -/
def kk (x : ℝ) : ℝ := (Real.sin x / x) ^ 2 * (1 + Real.sin x ^ 2 / 3)

/-- **The closed form**: `φ(s) = (999/1000)(1 − K(s/5))/s²` (for every `s`, with `x/0 = 0`). -/
lemma phi_eq (s : ℝ) : phi s = 999 / 1000 * ((1 - kk (s / 5)) / s ^ 2) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [phi, fat, kk]
  have h2 : Real.sin (2 / 5 * s) = 2 * Real.sin (s / 5) * Real.cos (s / 5) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hc : Real.cos (s / 5) ^ 2 = 1 - Real.sin (s / 5) ^ 2 := by rw [Real.cos_sq']
  unfold phi fat kk
  rw [h2, show 1 / 5 * s = s / 5 by ring]
  field_simp
  rw [hc]
  ring

lemma kk_nonneg (x : ℝ) : 0 ≤ kk x := by unfold kk; positivity

/-- `sin²x ≥ x²(1 − x²/6)²` for `x² ≤ 6`. -/
lemma sin_sq_ge' {x : ℝ} (hx : x ^ 2 ≤ 6) : x ^ 2 * (1 - x ^ 2 / 6) ^ 2 ≤ Real.sin x ^ 2 := by
  have key : ∀ y : ℝ, 0 ≤ y → y ^ 2 ≤ 6 → y ^ 2 * (1 - y ^ 2 / 6) ^ 2 ≤ Real.sin y ^ 2 := by
    intro y hy hy6
    have h1 := Real.sin_ge_sub_cube hy
    have h0 : 0 ≤ y - y ^ 3 / 6 := by nlinarith
    have := pow_le_pow_left₀ h0 h1 2
    have e : y ^ 2 * (1 - y ^ 2 / 6) ^ 2 = (y - y ^ 3 / 6) ^ 2 := by ring
    linarith
  rcases le_total 0 x with h | h
  · exact key x h hx
  · have := key (-x) (by linarith) (by rwa [neg_sq])
    rwa [neg_sq, Real.sin_neg, neg_sq] at this

/-- `sin²x ≥ x² − x⁴/3` for `x² ≤ 6`. -/
lemma sin_sq_ge {x : ℝ} (hx : x ^ 2 ≤ 6) : x ^ 2 - x ^ 4 / 3 ≤ Real.sin x ^ 2 := by
  have h := sin_sq_ge' hx
  have h6 : 0 ≤ x ^ 6 := by positivity
  nlinarith

/-- **`K ≤ 1`**: `sin²x(1 + sin²x/3) ≤ x²`. -/
lemma kk_le_one (x : ℝ) : kk x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [kk]
  have hx2 : 0 < x ^ 2 := by positivity
  have hs1 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  have hs0 : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  have key : Real.sin x ^ 2 * (1 + Real.sin x ^ 2 / 3) ≤ x ^ 2 := by
    rcases le_or_gt (4 / 3) (x ^ 2) with hbig | hsmall
    · nlinarith
    · -- `|sin x| ≤ |x| − |x|³/6 + |x|⁵/120` on `|x| ≤ 2`
      have hy : 0 ≤ |x| := abs_nonneg x
      have hy2 : |x| ^ 2 = x ^ 2 := sq_abs x
      have hsx : Real.sin x ^ 2 = Real.sin |x| ^ 2 := by
        rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [h1]
        · rw [h1, Real.sin_neg, neg_sq]
      have hsin0 : 0 ≤ Real.sin |x| :=
        Real.sin_nonneg_of_nonneg_of_le_pi hy (by nlinarith [Real.pi_gt_three, abs_nonneg x])
      have hsq0 : Real.sin x ^ 2 ≤ (|x| - |x| ^ 3 / 6 + |x| ^ 5 / 120) ^ 2 := by
        rw [hsx]
        exact pow_le_pow_left₀ hsin0 (sin_le_quintic hy) 2
      have hp0 : (|x| - |x| ^ 3 / 6 + |x| ^ 5 / 120) ^ 2 =
          |x| ^ 2 * (1 - |x| ^ 2 / 6 + (|x| ^ 2) ^ 2 / 120) ^ 2 := by ring
      rw [hp0, hy2] at hsq0
      set t := x ^ 2 with ht
      have hsq : Real.sin x ^ 2 ≤ t * (1 - t / 6 + t ^ 2 / 120) ^ 2 := hsq0
      have hq0 : 0 ≤ 1 - t / 6 + t ^ 2 / 120 := by nlinarith
      have hq1 : 1 - t / 6 + t ^ 2 / 120 ≤ 1 := by nlinarith
      set q := 1 - t / 6 + t ^ 2 / 120 with hq
      -- `u ≤ t q²` and `u + u²/3` is increasing in `u ≥ 0`
      have hu : Real.sin x ^ 2 * (1 + Real.sin x ^ 2 / 3) ≤ t * q ^ 2 * (1 + t * q ^ 2 / 3) := by
        have : 0 ≤ t * q ^ 2 := by positivity
        nlinarith
      have hpoly : t * q ^ 2 * (1 + t * q ^ 2 / 3) ≤ t := by
        have ht0 : 0 ≤ t := hx2.le
        have ht43 : t ≤ 4 / 3 := hsmall.le
        have p1 := pow_le_pow_left₀ ht0 ht43 3
        have p2 := pow_le_pow_left₀ ht0 ht43 5
        have p3 := pow_le_pow_left₀ ht0 ht43 7
        have hh : t ^ 7 - 80 * t ^ 6 + 2880 * t ^ 5 - 60800 * t ^ 4 + 822400 * t ^ 3 - 7252800 * t ^ 2
            + 39744000 * t - 110592000 ≤ 0 := by
          nlinarith [pow_nonneg ht0 6, pow_nonneg ht0 4, pow_nonneg ht0 2]
        have e : t * q ^ 2 * (1 + t * q ^ 2 / 3) - t = t ^ 3 * (t ^ 7 - 80 * t ^ 6 + 2880 * t ^ 5
            - 60800 * t ^ 4 + 822400 * t ^ 3 - 7252800 * t ^ 2 + 39744000 * t - 110592000) / 622080000 := by
          rw [hq]; ring
        have : t ^ 3 * (t ^ 7 - 80 * t ^ 6 + 2880 * t ^ 5 - 60800 * t ^ 4 + 822400 * t ^ 3 - 7252800 * t ^ 2
            + 39744000 * t - 110592000) / 622080000 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht0 3) hh) (by norm_num)
        linarith
      linarith
  unfold kk
  rw [div_pow, div_mul_eq_mul_div, div_le_one hx2]
  linarith

/-- **`φ ≥ 0`**. -/
lemma phi_nonneg (s : ℝ) : 0 ≤ phi s := by
  rw [phi_eq]
  have := kk_le_one (s / 5)
  have : 0 ≤ (1 - kk (s / 5)) / s ^ 2 := div_nonneg (by linarith) (sq_nonneg s)
  positivity

/-- **`φ ≤ w` for every `N ≥ 2`**: `φ(s)(s² + 1/16) ≤ 1`. -/
lemma phi_mul_le (s : ℝ) : phi s * (s ^ 2 + 1 / 16) ≤ 1 := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [phi, fat]
  have hs2 : 0 < s ^ 2 := by positivity
  rw [phi_eq]
  have hk0 := kk_nonneg (s / 5)
  have hk1 := kk_le_one (s / 5)
  have e : 999 / 1000 * ((1 - kk (s / 5)) / s ^ 2) * (s ^ 2 + 1 / 16) =
      999 / 1000 * ((1 - kk (s / 5)) + (1 - kk (s / 5)) / (16 * s ^ 2)) := by
    field_simp
  rw [e]
  rcases le_or_gt (999 / 16) (s ^ 2) with hbig | hsmall
  · have : (1 - kk (s / 5)) / (16 * s ^ 2) ≤ 1 / 999 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  · -- `x = s/5`, `x² < 5/2`: `1 − K ≤ 1 − sinc² ≤ min(x²/3, 2/3)`
    set x := s / 5 with hxdef
    have hx2 : x ^ 2 = s ^ 2 / 25 := by rw [hxdef]; ring
    clear_value x
    have hxpos : 0 < x ^ 2 := by rw [hx2]; positivity
    have hx6 : x ^ 2 ≤ 6 := by rw [hx2]; linarith
    have hsinlow := sin_sq_ge hx6
    have hsinlow' := sin_sq_ge' hx6
    have hsinc : 1 - kk x ≤ 1 - Real.sin x ^ 2 / x ^ 2 := by
      have : Real.sin x ^ 2 / x ^ 2 ≤ kk x := by
        unfold kk
        rw [div_pow]
        have : 0 ≤ Real.sin x ^ 2 / x ^ 2 := by positivity
        nlinarith [mul_nonneg this (sq_nonneg (Real.sin x))]
      linarith
    have hA : 1 - Real.sin x ^ 2 / x ^ 2 ≤ x ^ 2 / 3 := by
      have : 1 - x ^ 2 / 3 ≤ Real.sin x ^ 2 / x ^ 2 := by
        rw [le_div_iff₀ hxpos]; nlinarith
      linarith
    have hB : 1 - kk x ≤ 95 / 144 := by
      have h1 : (1 - x ^ 2 / 6) ^ 2 ≤ Real.sin x ^ 2 / x ^ 2 := by
        rw [le_div_iff₀ hxpos]; linarith
      have h2 : 7 / 12 ≤ 1 - x ^ 2 / 6 := by rw [hx2]; linarith
      have h3 : (7 / 12 : ℝ) ^ 2 ≤ (1 - x ^ 2 / 6) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      linarith
    have hC : (1 - kk x) / (16 * s ^ 2) ≤ 1 / 1200 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 1 - kk x ≤ x ^ 2 / 3 := le_trans hsinc hA
      rw [hx2] at this
      nlinarith
    nlinarith


/-- **Near `0`**: `1 − K(x) ≤ (7/36)x⁴` for `x² ≤ 1`. -/
lemma one_sub_kk_le {x : ℝ} (hx0 : x ≠ 0) (hx : x ^ 2 ≤ 1) : 1 - kk x ≤ 7 / 36 * x ^ 4 := by
  have hxpos : 0 < x ^ 2 := by positivity
  have h6 : x ^ 2 ≤ 6 := by linarith
  have hs := sin_sq_ge' h6
  have hsinc : (1 - x ^ 2 / 6) ^ 2 ≤ (Real.sin x / x) ^ 2 := by
    rw [div_pow, le_div_iff₀ hxpos]; linarith
  set a := x ^ 2 with ha
  have ha0 : 0 ≤ a := hxpos.le
  have hq0 : 0 ≤ (1 - a / 6) ^ 2 := sq_nonneg _
  have hK : (1 - a / 6) ^ 2 * (1 + a * (1 - a / 6) ^ 2 / 3) ≤ kk x := by
    unfold kk
    have h1 : 1 + a * (1 - a / 6) ^ 2 / 3 ≤ 1 + Real.sin x ^ 2 / 3 := by linarith
    have h2 : 0 ≤ 1 + a * (1 - a / 6) ^ 2 / 3 := by positivity
    calc (1 - a / 6) ^ 2 * (1 + a * (1 - a / 6) ^ 2 / 3)
        ≤ (Real.sin x / x) ^ 2 * (1 + a * (1 - a / 6) ^ 2 / 3) := mul_le_mul_of_nonneg_right hsinc h2
      _ ≤ (Real.sin x / x) ^ 2 * (1 + Real.sin x ^ 2 / 3) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hx4 : x ^ 4 = a ^ 2 := by rw [ha]; ring
  rw [hx4]
  have : 1 - (1 - a / 6) ^ 2 * (1 + a * (1 - a / 6) ^ 2 / 3) ≤ 7 / 36 * a ^ 2 := by
    have e : 1 - (1 - a / 6) ^ 2 * (1 + a * (1 - a / 6) ^ 2 / 3) =
        7 / 36 * a ^ 2 - a ^ 3 / 18 + a ^ 4 / 162 - a ^ 5 / 3888 := by ring
    rw [e]
    have ha1 : a ≤ 1 := hx
    nlinarith [pow_nonneg ha0 3, pow_nonneg ha0 4, pow_nonneg ha0 5, mul_le_mul_of_nonneg_left ha1 (pow_nonneg ha0 3)]
  linarith

/-- **`φ` is small at `0`**: `φ(s) ≤ s²/3000` for `s² ≤ 25`. -/
lemma phi_le_sq {s : ℝ} (hs : s ^ 2 ≤ 25) : phi s ≤ s ^ 2 / 3000 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp [phi, fat]
  have hs2 : 0 < s ^ 2 := by positivity
  rw [phi_eq]
  have h := one_sub_kk_le (x := s / 5) (div_ne_zero hs0 (by norm_num)) (by rw [div_pow]; linarith)
  have e : (s / 5) ^ 4 = s ^ 2 * s ^ 2 / 625 := by ring
  rw [e] at h
  have : (1 - kk (s / 5)) / s ^ 2 ≤ 7 / 36 * (s ^ 2 / 625) := by
    rw [div_le_iff₀ hs2]; nlinarith
  nlinarith

lemma tendsto_phi_zero : Filter.Tendsto phi (nhds 0) (nhds 0) := by
  have hle : ∀ᶠ s in nhds (0 : ℝ), phi s ≤ s ^ 2 / 3000 := by
    have : ∀ᶠ s in nhds (0 : ℝ), s ^ 2 ≤ 25 := by
      have hc : Continuous fun s : ℝ => s ^ 2 := by fun_prop
      have := hc.tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      exact this.eventually (ge_mem_nhds (by norm_num))
    filter_upwards [this] with s hs using phi_le_sq hs
  have hup : Filter.Tendsto (fun s : ℝ => s ^ 2 / 3000) (nhds 0) (nhds 0) := by
    have hc : Continuous fun s : ℝ => s ^ 2 / 3000 := by fun_prop
    simpa using hc.tendsto 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall phi_nonneg) hle

/-! ## The entire extension -/

/-- `S(w) = sin w/w`, entire, `S(0) = 1`. -/
def sincC (w : ℂ) : ℂ := dslope Complex.sin 0 w

lemma sincC_of_ne {w : ℂ} (hw : w ≠ 0) : sincC w = Complex.sin w / w := by
  unfold sincC; rw [dslope_of_ne _ hw, slope_def_field]; simp

lemma sincC_zero : sincC 0 = 1 := by
  unfold sincC; rw [dslope_same, Complex.deriv_sin]; simp

lemma differentiable_sincC : Differentiable ℂ sincC := by
  have h := (Complex.differentiableOn_dslope (f := Complex.sin) (c := 0) (s := Set.univ)
    Filter.univ_mem).2 Complex.differentiable_sin.differentiableOn
  exact differentiableOn_univ.1 h

lemma sincC_neg (w : ℂ) : sincC (-w) = sincC w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [sincC_of_ne (neg_ne_zero.2 hw), sincC_of_ne hw, Complex.sin_neg, neg_div_neg_eq]

lemma sincC_ofReal {x : ℝ} (hx : x ≠ 0) : sincC x = ((Real.sin x / x : ℝ) : ℂ) := by
  rw [sincC_of_ne (by exact_mod_cast hx)]; push_cast; rfl

/-- `H(z) = 1 − (4/3)S(z/5)² + (1/3)S(2z/5)²`, so that `φ = (999/1000)H(z)/z²`. -/
def hH (z : ℂ) : ℂ := 1 - 4 / 3 * sincC (z / 5) ^ 2 + 1 / 3 * sincC (2 * z / 5) ^ 2

lemma differentiable_hH : Differentiable ℂ hH := by
  have := differentiable_sincC
  unfold hH; fun_prop

lemma hH_zero : hH 0 = 0 := by unfold hH; simp [sincC_zero]; norm_num

lemma hH_neg (z : ℂ) : hH (-z) = hH z := by
  unfold hH
  rw [show -z / 5 = -(z / 5) by ring, show 2 * -z / 5 = -(2 * z / 5) by ring, sincC_neg, sincC_neg]

lemma deriv_hH_zero : deriv hH 0 = 0 := by
  have h1 : deriv (fun z => hH (-z)) 0 = -deriv hH (-0) := deriv_comp_neg (f := hH) 0
  have h2 : (fun z => hH (-z)) = hH := funext hH_neg
  rw [h2, neg_zero] at h1
  have : (2 : ℂ) * deriv hH 0 = 0 := by linear_combination h1
  simpa using this

/-- **The entire extension of `φ`**: `φ_ℂ(z) = (999/1000)H(z)/z²`, made entire by `dslope`. -/
def phiE (z : ℂ) : ℂ := 999 / 1000 * dslope (dslope hH 0) 0 z

lemma differentiable_phiE : Differentiable ℂ phiE := by
  have h1 := (Complex.differentiableOn_dslope (f := hH) (c := 0) (s := Set.univ) Filter.univ_mem).2
    differentiable_hH.differentiableOn
  have h2 := (Complex.differentiableOn_dslope (f := dslope hH 0) (c := 0) (s := Set.univ) Filter.univ_mem).2 h1
  have h3 := differentiableOn_univ.1 h2
  unfold phiE; fun_prop

lemma phiE_of_ne {z : ℂ} (hz : z ≠ 0) : phiE z = 999 / 1000 * (hH z / z ^ 2) := by
  unfold phiE
  rw [dslope_of_ne _ hz, slope_def_field, dslope_of_ne _ hz, slope_def_field, dslope_same, deriv_hH_zero,
    hH_zero]
  field_simp
  ring

lemma phiE_ofReal_of_ne {s : ℝ} (hs : s ≠ 0) : phiE s = (phi s : ℂ) := by
  rw [phiE_of_ne (by exact_mod_cast hs)]
  unfold hH phi fat
  rw [show (s : ℂ) / 5 = ((s / 5 : ℝ) : ℂ) by push_cast; ring,
    show 2 * (s : ℂ) / 5 = ((2 * s / 5 : ℝ) : ℂ) by push_cast; ring,
    sincC_ofReal (by positivity), sincC_ofReal (by positivity)]
  rw [show (1 / 5 : ℝ) * s = s / 5 by ring, show (2 / 5 : ℝ) * s = 2 * s / 5 by ring]
  push_cast
  field_simp
  ring

lemma phiE_zero : phiE 0 = 0 := by
  have hcont : Continuous fun s : ℝ => phiE (s : ℂ) := differentiable_phiE.continuous.comp Complex.continuous_ofReal
  have hc : Filter.Tendsto (fun s : ℝ => phiE s) (nhdsWithin 0 {0}ᶜ) (nhds (phiE 0)) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    simpa only [Complex.ofReal_zero] using this
  have hp : Filter.Tendsto (fun s : ℝ => phiE s) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have h0 : Filter.Tendsto (fun s : ℝ => ((phi s : ℝ) : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhds ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp (tendsto_phi_zero.mono_left nhdsWithin_le_nhds)
    refine (h0.congr' ?_).trans (by simp)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (phiE_ofReal_of_ne hs).symm
  exact tendsto_nhds_unique hc hp

/-- **`φ_ℂ` extends `φ`**. -/
lemma phiE_ofReal (s : ℝ) : phiE s = (phi s : ℂ) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [Complex.ofReal_zero, phiE_zero]; simp [phi, fat]
  · exact phiE_ofReal_of_ne hs

lemma phiE_neg (z : ℂ) : phiE (-z) = phiE z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [phiE_of_ne (neg_ne_zero.2 hz), phiE_of_ne hz, hH_neg, neg_sq]


/-! ## The strip bound -/

lemma norm_sin_le (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have h := WeilForm.norm_two_cos_le (w - (π / 2 : ℂ))
  rw [Complex.cos_sub_pi_div_two] at h
  have him : (w - (π / 2 : ℂ)).im = w.im := by simp
  rw [him, norm_mul, Complex.norm_two] at h
  linarith

lemma norm_sincC_le {w : ℂ} (hw : w ≠ 0) : ‖sincC w‖ ≤ Real.exp |w.im| / ‖w‖ := by
  rw [sincC_of_ne hw, norm_div]
  exact div_le_div_of_nonneg_right (norm_sin_le w) (norm_nonneg w)

lemma exp_le_three {x : ℝ} (hx : x ≤ 1) : Real.exp x ≤ 3 := by
  have := Real.exp_one_lt_d9
  calc Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.2 hx
    _ ≤ 3 := by linarith

/-- **Far from `0`** on the strip: `‖φ_ℂ(z)‖ ≤ 640/(1 + (Re z)²)` for `‖z‖ ≥ 1`. -/
lemma norm_phiE_le_far {z : ℂ} (hz : z ∈ WeilStrip.strip (-1) 1) (h1 : 1 ≤ ‖z‖) :
    ‖phiE z‖ ≤ 640 / (1 + z.re ^ 2) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have him : |z.im| ≤ 1 := abs_le.2 ⟨hz.1, hz.2⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hS1 : ‖sincC (z / 5)‖ ≤ 15 := by
    refine (norm_sincC_le (div_ne_zero hz0 (by norm_num))).trans ?_
    have hi : |(z / 5).im| ≤ 1 := by
      rw [show (z / 5).im = z.im / 5 by simp, abs_div]; norm_num; linarith
    rw [norm_div, show ‖(5 : ℂ)‖ = 5 by simp, div_le_iff₀ (by positivity)]
    have := exp_le_three hi
    nlinarith
  have hS2 : ‖sincC (2 * z / 5)‖ ≤ 15 / 2 := by
    refine (norm_sincC_le (div_ne_zero (mul_ne_zero two_ne_zero hz0) (by norm_num))).trans ?_
    have hi : |(2 * z / 5).im| ≤ 1 := by
      rw [show (2 * z / 5).im = 2 * z.im / 5 by simp, abs_div, abs_mul]; norm_num; linarith
    rw [norm_div, norm_mul, show ‖(5 : ℂ)‖ = 5 by simp, show ‖(2 : ℂ)‖ = 2 by simp,
      div_le_iff₀ (by positivity)]
    have := exp_le_three hi
    nlinarith
  have hHz : ‖hH z‖ ≤ 320 := by
    unfold hH
    calc ‖1 - 4 / 3 * sincC (z / 5) ^ 2 + 1 / 3 * sincC (2 * z / 5) ^ 2‖
        ≤ ‖(1 : ℂ)‖ + ‖4 / 3 * sincC (z / 5) ^ 2‖ + ‖1 / 3 * sincC (2 * z / 5) ^ 2‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ = 1 + 4 / 3 * ‖sincC (z / 5)‖ ^ 2 + 1 / 3 * ‖sincC (2 * z / 5)‖ ^ 2 := by
          simp [norm_pow]
      _ ≤ 1 + 4 / 3 * 15 ^ 2 + 1 / 3 * (15 / 2) ^ 2 := by gcongr
      _ ≤ 320 := by norm_num
  have hre : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    have := Complex.abs_re_le_norm z
    nlinarith [abs_nonneg z.re, sq_abs z.re]
  have hnorm : ‖phiE z‖ = 999 / 1000 * (‖hH z‖ / ‖z‖ ^ 2) := by
    rw [phiE_of_ne hz0, norm_mul, norm_div (hH z), norm_pow]; norm_num
  rw [hnorm]
  have h2 : 1 + z.re ^ 2 ≤ 2 * ‖z‖ ^ 2 := by nlinarith
  calc 999 / 1000 * (‖hH z‖ / ‖z‖ ^ 2) ≤ 320 / ‖z‖ ^ 2 := by
        rw [← mul_div_assoc]; gcongr; nlinarith [norm_nonneg (hH z), hHz]
    _ ≤ 640 / (1 + z.re ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

/-- **The strip test**: `‖φ_ℂ(z)‖ ≤ K/(1 + (Re z)²)` on `|Im z| ≤ 1`. -/
theorem phiE_strip : ∃ K, 0 ≤ K ∧ ∀ z ∈ WeilStrip.strip (-1) 1, ‖phiE z‖ ≤ K / (1 + z.re ^ 2) := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    differentiable_phiE.continuous.continuousOn
  refine ⟨640 + 2 * |B|, by positivity, fun z hz => ?_⟩
  rcases le_or_gt 1 ‖z‖ with h1 | h1
  · refine (norm_phiE_le_far hz h1).trans ?_
    gcongr; linarith [abs_nonneg B]
  · have hb := hB z (by simpa using h1.le)
    have hre : z.re ^ 2 ≤ 1 := by
      have := Complex.abs_re_le_norm z
      nlinarith [abs_nonneg z.re, sq_abs z.re, norm_nonneg z]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg (phiE z), le_abs_self B, abs_nonneg B]


/-! ## The pole -/

/-- `|sinh a − (a + a³/6 + a⁵/120)| ≤ a⁷/4000` for `|a| ≤ 1`. -/
lemma sinh_near {a : ℝ} (ha : |a| ≤ 1) :
    |Real.sinh a - (a + a ^ 3 / 6 + a ^ 5 / 120)| ≤ |a| ^ 7 / 4000 := by
  have h1 := Real.exp_bound ha (n := 7) (by norm_num)
  have h2 := Real.exp_bound (x := -a) (by rwa [abs_neg]) (n := 7) (by norm_num)
  rw [abs_neg] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one] at h1 h2
  norm_num at h1 h2
  rw [Real.sinh_eq]
  have n3 : (-a) ^ 3 = -a ^ 3 := by ring
  have n5 : (-a) ^ 5 = -a ^ 5 := by ring
  rw [n3, n5] at h2
  have ha7 : 0 ≤ |a| ^ 7 := by positivity
  obtain ⟨l1, u1⟩ := abs_le.1 h1
  obtain ⟨l2, u2⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

/-- `S(uI) = sinh u/u`. -/
lemma sincC_mul_I {u : ℝ} (hu : u ≠ 0) : sincC ((u : ℂ) * Complex.I) = ((Real.sinh u / u : ℝ) : ℂ) := by
  have hne : (u : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hu) Complex.I_ne_zero
  rw [sincC_of_ne hne, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  field_simp
  push_cast; ring

/-- `H(iy) = 1 − (4/3)σ(y/5) + (1/3)σ(2y/5)`, `σ(a) = (sinh a/a)²`. -/
lemma hH_I {y : ℝ} (hy : y ≠ 0) :
    hH (Complex.I * y) = ((1 - 4 / 3 * (Real.sinh (y / 5) / (y / 5)) ^ 2
      + 1 / 3 * (Real.sinh (2 * y / 5) / (2 * y / 5)) ^ 2 : ℝ) : ℂ) := by
  unfold hH
  rw [show Complex.I * (y : ℂ) / 5 = ((y / 5 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    show 2 * (Complex.I * (y : ℂ)) / 5 = ((2 * y / 5 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    sincC_mul_I (by positivity), sincC_mul_I (by positivity)]
  push_cast; ring

/-- `|2pe + e²| ≤ 5c` for `0 ≤ p ≤ 2`, `|e| ≤ c ≤ 1`. -/
lemma cross_err {p e c : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 2) (he : |e| ≤ c) (hc1 : c ≤ 1) :
    |2 * p * e + e ^ 2| ≤ 5 * c := by
  have hc0 : 0 ≤ c := (abs_nonneg e).trans he
  have h1 : |2 * p * e| ≤ 4 * c := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    nlinarith [abs_nonneg e]
  have h2 : e ^ 2 ≤ c := by
    have : e ^ 2 = |e| * |e| := by rw [← sq_abs, sq]
    rw [this]; nlinarith [abs_nonneg e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (sq_nonneg e)]
  linarith

/-- The algebra of the pole: with `sinh a/a = p(a) + e₁`, `sinh 2a/2a = p(2a) + e₂`. -/
lemma pole_poly {a e1 e2 : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 20) (h1 : |e1| ≤ a ^ 6 / 4000)
    (h2 : |e2| ≤ 64 * a ^ 6 / 4000) :
    |1 - 4 / 3 * ((1 + a ^ 2 / 6 + a ^ 4 / 120) + e1) ^ 2
      + 1 / 3 * ((1 + (2 * a) ^ 2 / 6 + (2 * a) ^ 4 / 120) + e2) ^ 2| ≤ a ^ 4 / 5 := by
  have ha2 : a ^ 2 ≤ 1 / 400 := by nlinarith
  have ha4 : 0 ≤ a ^ 4 := by positivity
  have ha6 : a ^ 6 ≤ a ^ 4 / 400 := by
    have : a ^ 6 = a ^ 4 * a ^ 2 := by ring
    rw [this]; nlinarith
  have ha8 : a ^ 8 ≤ a ^ 4 / 160000 := by
    have : a ^ 8 = a ^ 4 * (a ^ 2) ^ 2 := by ring
    rw [this]
    have : (a ^ 2) ^ 2 ≤ 1 / 160000 := by nlinarith [sq_nonneg (a ^ 2)]
    nlinarith
  have hp1 : 1 + a ^ 2 / 6 + a ^ 4 / 120 ≤ 2 := by nlinarith
  have hp2 : 1 + (2 * a) ^ 2 / 6 + (2 * a) ^ 4 / 120 ≤ 2 := by nlinarith
  have hc1 : a ^ 6 / 4000 ≤ 1 := by nlinarith
  have hc2 : 64 * a ^ 6 / 4000 ≤ 1 := by nlinarith
  have hX1 := cross_err (by positivity) hp1 h1 hc1
  have hX2 := cross_err (by positivity) hp2 h2 hc2
  have e : 1 - 4 / 3 * ((1 + a ^ 2 / 6 + a ^ 4 / 120) + e1) ^ 2
      + 1 / 3 * ((1 + (2 * a) ^ 2 / 6 + (2 * a) ^ 4 / 120) + e2) ^ 2 =
      (8 / 45 * a ^ 4 + a ^ 6 / 18 + 7 * a ^ 8 / 1200)
        - 4 / 3 * (2 * (1 + a ^ 2 / 6 + a ^ 4 / 120) * e1 + e1 ^ 2)
        + 1 / 3 * (2 * (1 + (2 * a) ^ 2 / 6 + (2 * a) ^ 4 / 120) * e2 + e2 ^ 2) := by ring
  rw [e]
  obtain ⟨l1, u1⟩ := abs_le.1 hX1
  obtain ⟨l2, u2⟩ := abs_le.1 hX2
  have hP0 : 0 ≤ 8 / 45 * a ^ 4 + a ^ 6 / 18 + 7 * a ^ 8 / 1200 := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- **The pole bound**: `|H(iy)| ≤ (y/5)⁴/5` for `0 < y ≤ 1/4`. -/
lemma abs_hH_I_le {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 4) :
    |1 - 4 / 3 * (Real.sinh (y / 5) / (y / 5)) ^ 2 + 1 / 3 * (Real.sinh (2 * y / 5) / (2 * y / 5)) ^ 2|
      ≤ (y / 5) ^ 4 / 5 := by
  have ha0 : 0 < y / 5 := by positivity
  have ha1 : y / 5 ≤ 1 / 20 := by linarith
  have e2 : 2 * y / 5 = 2 * (y / 5) := by ring
  rw [e2]
  generalize y / 5 = a at ha0 ha1 ⊢
  have s1 := sinh_near (a := a) (by rw [abs_of_pos ha0]; linarith)
  have s2 := sinh_near (a := 2 * a) (by rw [abs_of_pos (by positivity)]; linarith)
  rw [abs_of_pos ha0] at s1
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * a)] at s2
  have h2a : (0 : ℝ) < 2 * a := by positivity
  have he1 : |Real.sinh a / a - (1 + a ^ 2 / 6 + a ^ 4 / 120)| ≤ a ^ 6 / 4000 := by
    rw [show Real.sinh a / a - (1 + a ^ 2 / 6 + a ^ 4 / 120) =
      (Real.sinh a - (a + a ^ 3 / 6 + a ^ 5 / 120)) / a by field_simp, abs_div, abs_of_pos ha0,
      div_le_iff₀ ha0]
    calc |Real.sinh a - (a + a ^ 3 / 6 + a ^ 5 / 120)| ≤ a ^ 7 / 4000 := s1
      _ = a ^ 6 / 4000 * a := by ring
  have he2 : |Real.sinh (2 * a) / (2 * a) - (1 + (2 * a) ^ 2 / 6 + (2 * a) ^ 4 / 120)| ≤ 64 * a ^ 6 / 4000 := by
    rw [show Real.sinh (2 * a) / (2 * a) - (1 + (2 * a) ^ 2 / 6 + (2 * a) ^ 4 / 120) =
      (Real.sinh (2 * a) - (2 * a + (2 * a) ^ 3 / 6 + (2 * a) ^ 5 / 120)) / (2 * a) by field_simp,
      abs_div, abs_of_pos h2a, div_le_iff₀ h2a]
    calc |Real.sinh (2 * a) - (2 * a + (2 * a) ^ 3 / 6 + (2 * a) ^ 5 / 120)| ≤ (2 * a) ^ 7 / 4000 := s2
      _ = 64 * a ^ 6 / 4000 * (2 * a) := by ring
  have h := pole_poly ha0 ha1 he1 he2
  have r1 : (1 + a ^ 2 / 6 + a ^ 4 / 120) + (Real.sinh a / a - (1 + a ^ 2 / 6 + a ^ 4 / 120)) = Real.sinh a / a := by ring
  have r2 : (1 + (2 * a) ^ 2 / 6 + (2 * a) ^ 4 / 120) + (Real.sinh (2 * a) / (2 * a) - (1 + (2 * a) ^ 2 / 6
    + (2 * a) ^ 4 / 120)) = Real.sinh (2 * a) / (2 * a) := by ring
  rwa [r1, r2] at h

/-- **The pole**: `‖φ_ℂ(iy)‖ ≤ y²/3000` for `0 < y ≤ 1/4`. -/
theorem norm_phiE_I_le {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 4) : ‖phiE (Complex.I * y)‖ ≤ y ^ 2 / 3000 := by
  have hne : Complex.I * (y : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hy0.ne')
  have hy2 : 0 < y ^ 2 := by positivity
  have hval : phiE (Complex.I * y) = ((999 / 1000 * ((1 - 4 / 3 * (Real.sinh (y / 5) / (y / 5)) ^ 2
      + 1 / 3 * (Real.sinh (2 * y / 5) / (2 * y / 5)) ^ 2) / (-y ^ 2)) : ℝ) : ℂ) := by
    rw [phiE_of_ne hne, hH_I hy0.ne']
    have hsq : (Complex.I * (y : ℂ)) ^ 2 = -(y : ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
    rw [hsq]; push_cast; ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 999 / 1000),
    abs_div, abs_neg, abs_of_pos hy2]
  have h := abs_hH_I_le hy0 hy
  have e : (y / 5) ^ 4 / 5 = y ^ 2 * y ^ 2 / 3125 := by ring
  rw [e] at h
  rw [← mul_div_assoc, div_le_div_iff₀ hy2 (by norm_num)]
  nlinarith [abs_nonneg (1 - 4 / 3 * (Real.sinh (y / 5) / (y / 5)) ^ 2
    + 1 / 3 * (Real.sinh (2 * y / 5) / (2 * y / 5)) ^ 2)]

/-! ## Continuity -/

lemma phi_eq_re (s : ℝ) : phi s = (phiE s).re := by rw [phiE_ofReal]; simp

lemma continuous_phi : Continuous phi := by
  have : phi = fun s : ℝ => (phiE s).re := funext phi_eq_re
  rw [this]
  exact Complex.continuous_re.comp (differentiable_phiE.continuous.comp Complex.continuous_ofReal)

end PivotPhi
