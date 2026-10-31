import Mathlib

open Real MeasureTheory intervalIntegral
open Filter Topology

noncomputable section

namespace WeilForm

/-- Theorem 1bs's smooth count `N₀(r) = (r/2π)(ln(r/2π) − 1)`. -/
def N0 (r : ℝ) : ℝ := r / (2 * π) * (Real.log (r / (2 * π)) - 1)

theorem continuous_N0 : Continuous N0 := by
  unfold N0
  have : (fun r => r / (2 * π) * (Real.log (r / (2 * π)) - 1))
      = (fun r => (r / (2 * π)) * Real.log (r / (2 * π)) - r / (2 * π)) := by
    funext r; ring
  rw [this]
  exact (Real.continuous_mul_log.comp (continuous_id.div_const _)).sub (continuous_id.div_const _)

/-- `d/dT (T² − r²) = 2T`. -/
theorem hasDerivAt_sqsubT (r T : ℝ) : HasDerivAt (fun T => T ^ 2 - r ^ 2) (2 * T) T := by
  have := (hasDerivAt_pow 2 T).sub_const (r ^ 2)
  convert this using 1; push_cast; ring

/-- `d/dr (T² − r²) = −2r`. -/
theorem hasDerivAt_sqsubR (T r : ℝ) : HasDerivAt (fun r => T ^ 2 - r ^ 2) (-(2 * r)) r := by
  have := (hasDerivAt_pow 2 r).const_sub (T ^ 2)
  convert this using 1; push_cast; ring

/-- `x^p = x · x^{p−1}` for `x > 0`. -/
theorem rpow_eq_mul_rpow_sub_one {x : ℝ} (hx : 0 < x) (p : ℝ) : x ^ p = x * x ^ (p - 1) := by
  conv_lhs => rw [show p = 1 + (p - 1) by ring, Real.rpow_add hx, Real.rpow_one]

/-- 1ca(ii): `|N₀| ≤ 1` on `[0, 2πe]` (its minimum `−1` at `r = 2π`). -/
theorem abs_N0_le_one {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 2 * π * Real.exp 1) : |N0 r| ≤ 1 := by
  have h2pi : 0 < 2 * π := by positivity
  set s := r / (2 * π) with hs_def
  have hN : N0 r = s * (Real.log s - 1) := rfl
  have hs0 : 0 ≤ s := div_nonneg h0 h2pi.le
  have hse : s ≤ Real.exp 1 := by
    rw [hs_def, div_le_iff₀ h2pi]; linarith
  rw [hN]
  rcases hs0.eq_or_lt with hs | hs
  · rw [← hs]; simp
  · have hlog_le : Real.log s ≤ 1 := by
      rw [← Real.log_exp 1]; exact Real.log_le_log hs hse
    have hsl : s - 1 ≤ s * Real.log s := Real.self_sub_one_le_mul_log hs.le
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith

/-- The kernel of the rise, `12 r (3T² + 2r²)(T² − r²)^{−7/2}`. -/
def kern (T r : ℝ) : ℝ := 12 * r * (3 * T ^ 2 + 2 * r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(7 / 2 : ℝ))

/-- The kernel's antiderivative `4(T² + 2r²)(T² − r²)^{−5/2}` (1ca(ii): "the weight's integral is
elementary"). -/
theorem hasDerivAt_antider (T r : ℝ) (h : r ^ 2 < T ^ 2) :
    HasDerivAt (fun r => 4 * (T ^ 2 + 2 * r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ)))
      (kern T r) r := by
  have hpos : 0 < T ^ 2 - r ^ 2 := by linarith
  have h1 := hasDerivAt_sqsubR T r
  have h2 := h1.rpow_const (p := -(5 / 2 : ℝ)) (Or.inl hpos.ne')
  have h3 : HasDerivAt (fun r => 4 * (T ^ 2 + 2 * r ^ 2)) (16 * r) r := by
    have := (((hasDerivAt_pow 2 r).const_mul 2).const_add (T ^ 2)).const_mul 4
    convert this using 1; push_cast; ring
  have h4 := h3.mul h2
  convert h4 using 1
  have hsplit : (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ))
      = (T ^ 2 - r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(7 / 2 : ℝ)) := by
    rw [rpow_eq_mul_rpow_sub_one hpos]; norm_num
  have hexp : (-(5 / 2 : ℝ)) - 1 = -(7 / 2) := by norm_num
  rw [hexp, hsplit, kern]
  ring

theorem kern_continuousOn (T G : ℝ) (hGT : G ^ 2 < T ^ 2) (hG : 0 ≤ G) :
    ContinuousOn (kern T) (Set.uIcc 0 G) := by
  have hsub : ∀ r ∈ Set.uIcc 0 G, T ^ 2 - r ^ 2 ≠ 0 := by
    intro r hr
    rw [Set.uIcc_of_le hG] at hr
    have : r ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
    linarith
  unfold kern
  apply ContinuousOn.mul (by fun_prop)
  exact ContinuousOn.rpow_const (by fun_prop) (fun r hr => Or.inl (hsub r hr))

/-- `(T²)^{−5/2} · T² = 1/T³` for `T > 0`. -/
theorem antider_zero (T : ℝ) (hT : 0 < T) :
    4 * (T ^ 2 + 2 * 0 ^ 2) * (T ^ 2 - 0 ^ 2) ^ (-(5 / 2 : ℝ)) = 4 / T ^ 3 := by
  have h : (T ^ 2) ^ (-(5 / 2 : ℝ)) = (T ^ 5)⁻¹ := by
    rw [← Real.rpow_natCast T 2, ← Real.rpow_mul hT.le]
    rw [show ((2 : ℕ) : ℝ) * (-(5 / 2 : ℝ)) = -((5 : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_neg hT.le, Real.rpow_natCast]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    sub_zero]
  rw [h]
  field_simp

/-- 1ca(ii): the rise kernel integrates in closed form,
`∫₀^G 12r(3T²+2r²)(T²−r²)^{−7/2} dr = 4(T²+2G²)(T²−G²)^{−5/2} − 4/T³`. -/
theorem integral_kern (T G : ℝ) (hG : 0 ≤ G) (hGT : G < T) :
    ∫ r in (0 : ℝ)..G, kern T r
      = 4 * (T ^ 2 + 2 * G ^ 2) * (T ^ 2 - G ^ 2) ^ (-(5 / 2 : ℝ)) - 4 / T ^ 3 := by
  have hT : 0 < T := by linarith
  have hG2 : G ^ 2 < T ^ 2 := by nlinarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r =>
      4 * (T ^ 2 + 2 * r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ)))]
  · rw [antider_zero T hT]
  · intro r hr
    rw [Set.uIcc_of_le hG] at hr
    have : r ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
    exact hasDerivAt_antider T r (by linarith)
  · exact (kern_continuousOn T G hG2 hG).intervalIntegrable

theorem kern_nonneg (T r : ℝ) (hr : 0 ≤ r) (hrT : r ^ 2 ≤ T ^ 2) : 0 ≤ kern T r := by
  unfold kern
  have : 0 ≤ (T ^ 2 - r ^ 2) ^ (-(7 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have h3 : 0 ≤ 3 * T ^ 2 + 2 * r ^ 2 := by positivity
  positivity

/-- 1ca(ii): the rise is at most the elementary integral whenever `|N| ≤ 1` on `[0, G]`. -/
theorem rise_le (N : ℝ → ℝ) (T G : ℝ) (hG : 0 ≤ G) (hGT : G < T)
    (hN : ∀ r ∈ Set.Icc 0 G, |N r| ≤ 1)
    (hNi : IntervalIntegrable (fun r => |N r| * kern T r) volume 0 G) :
    ∫ r in (0 : ℝ)..G, |N r| * kern T r
      ≤ 4 * (T ^ 2 + 2 * G ^ 2) * (T ^ 2 - G ^ 2) ^ (-(5 / 2 : ℝ)) - 4 / T ^ 3 := by
  have hG2 : G ^ 2 < T ^ 2 := by nlinarith
  rw [← integral_kern T G hG hGT]
  apply intervalIntegral.integral_mono_on hG hNi
    (kern_continuousOn T G hG2 hG).intervalIntegrable
  intro r hr
  have hr2 : r ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
  have hk := kern_nonneg T r hr.1 (by linarith)
  calc |N r| * kern T r ≤ 1 * kern T r := mul_le_mul_of_nonneg_right (hN r hr) hk
    _ = kern T r := one_mul _

/-- `N₀ ≤ 0` on `[0, 2πe]` (so on `[0, γ₁]`, "as 2πe > γ₁"). -/
theorem N0_nonpos {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 2 * π * Real.exp 1) : N0 r ≤ 0 := by
  have h2pi : 0 < 2 * π := by positivity
  set s := r / (2 * π) with hs_def
  have hN : N0 r = s * (Real.log s - 1) := rfl
  have hs0 : 0 ≤ s := div_nonneg h0 h2pi.le
  have hse : s ≤ Real.exp 1 := by
    rw [hs_def, div_le_iff₀ h2pi]; linarith
  rw [hN]
  rcases hs0.eq_or_lt with hs | hs
  · rw [← hs]; simp
  · have hlog_le : Real.log s ≤ 1 := by
      rw [← Real.log_exp 1]; exact Real.log_le_log hs hse
    nlinarith

/-- `d/dT[T²(T² − r²)^{−p}] = 2T((1 − p)T² − r²)(T² − r²)^{−p−1}` for `r² < T²`
. -/
theorem hasDerivAt_sq_mul_rpow (r T p : ℝ) (h : r ^ 2 < T ^ 2) :
    HasDerivAt (fun T => T ^ 2 * (T ^ 2 - r ^ 2) ^ (-p))
      (2 * T * ((1 - p) * T ^ 2 - r ^ 2) * (T ^ 2 - r ^ 2) ^ (-p - 1)) T := by
  have hpos : 0 < T ^ 2 - r ^ 2 := by linarith
  have h2 := (hasDerivAt_sqsubT r T).rpow_const (p := -p) (Or.inl hpos.ne')
  have h3 : HasDerivAt (fun T => T ^ 2) (2 * T) T := by
    simpa using hasDerivAt_pow 2 T
  convert h3.mul h2 using 1
  rw [rpow_eq_mul_rpow_sub_one hpos (-p)]
  ring

/-- 1ca(ii), the holes' and the constant's terms: `T·d/dT[T²(T²−r²)^{−3/2}] = −T²(T²+2r²)(T²−r²)^{−5/2}`
(stated as the derivative `−T(T²+2r²)(T²−r²)^{−5/2}`), for `r² < T²`. -/
theorem hasDerivAt_fall (r T : ℝ) (h : r ^ 2 < T ^ 2) :
    HasDerivAt (fun T => T ^ 2 * (T ^ 2 - r ^ 2) ^ (-(3 / 2 : ℝ)))
      (-(T * (T ^ 2 + 2 * r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ)))) T := by
  convert hasDerivAt_sq_mul_rpow r T (3 / 2) h using 1
  rw [show -(3 / 2 : ℝ) - 1 = -(5 / 2) by norm_num]; ring

/-- 1ca(ii), the piece below γ₁: `d/dT[T²(T²−r²)^{−5/2}] = −T(3T²+2r²)(T²−r²)^{−7/2}`, so that
`T·d/dT` of `12T²∫₀^{γ₁} N₀ r (T²−r²)^{−5/2}` is the rise `12T²∫₀^{γ₁}|N₀| r(3T²+2r²)(T²−r²)^{−7/2}`
(with `N₀ ≤ 0`). -/
theorem hasDerivAt_rise (r T : ℝ) (h : r ^ 2 < T ^ 2) :
    HasDerivAt (fun T => T ^ 2 * (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ)))
      (-(T * (3 * T ^ 2 + 2 * r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(7 / 2 : ℝ)))) T := by
  convert hasDerivAt_sq_mul_rpow r T (5 / 2) h using 1
  rw [show -(5 / 2 : ℝ) - 1 = -(7 / 2) by norm_num]; ring

/-- The polynomial `p(x) = 64(x−1)⁵ − x³(x+2)² = 63x⁵ − 324x⁴ + 636x³ − 640x² + 320x − 64` is
positive for `x ≥ 2.28`: shifted to `x = 57/25 + s` every coefficient is positive. -/
theorem p_pos (x : ℝ) (hx : 57 / 25 ≤ x) : 0 < 64 * (x - 1) ^ 5 - x ^ 3 * (x + 2) ^ 2 := by
  set s := x - 57 / 25 with hs
  have hs0 : 0 ≤ s := by linarith
  have hx' : x = 57 / 25 + s := by rw [hs]; ring
  rw [hx']
  have : 64 * (57 / 25 + s - 1) ^ 5 - (57 / 25 + s) ^ 3 * (57 / 25 + s + 2) ^ 2
      = 63 * s ^ 5 + 1971 / 5 * s ^ 4 + 119514 / 125 * s ^ 3 + 3348538 / 3125 * s ^ 2
        + 36863923 / 78125 * s + 27208991 / 9765625 := by ring
  rw [this]
  positivity

/-- **1ca(ii), "R < 1 for T ≥ 1.51γ₁ by the bound alone."** For every `G ∈ (0, 2πe]` (the paper
takes `G = γ₁ = 14.13…`) and every `T` with `T² ≥ 2.2801 G²` (`T ≥ 1.51 G`), the rise of the piece
below `G`, `12 ∫₀^G |N₀| r(3T²+2r²)(T²−r²)^{−7/2} dr`, is strictly less than the count constant's
fall `(7/2)(T²+2G²)(T²−G²)^{−5/2}`, i.e. `R(T) < 1`. -/
theorem R_lt_one (G T : ℝ) (hG0 : 0 < G) (hGe : G ≤ 2 * π * Real.exp 1) (hT : 0 < T)
    (hx : 22801 / 10000 * G ^ 2 ≤ T ^ 2) :
    ∫ r in (0 : ℝ)..G, |N0 r| * kern T r
      < 7 / 2 * ((T ^ 2 + 2 * G ^ 2) * (T ^ 2 - G ^ 2) ^ (-(5 / 2 : ℝ))) := by
  have hG2pos : 0 < G ^ 2 := by positivity
  have hGT2 : G ^ 2 < T ^ 2 := by nlinarith
  have hGT : G < T := by nlinarith
  -- |N₀| ≤ 1 on [0, G]
  have hN : ∀ r ∈ Set.Icc 0 G, |N0 r| ≤ 1 := fun r hr =>
    abs_N0_le_one hr.1 (le_trans hr.2 hGe)
  -- integrability of |N₀| · kern
  have hN0c : Continuous N0 := continuous_N0
  have hNi : IntervalIntegrable (fun r => |N0 r| * kern T r) volume 0 G :=
    ((hN0c.abs.continuousOn).mul (kern_continuousOn T G hGT2 hG0.le)).intervalIntegrable
  have hrise := rise_le N0 T G hG0.le hGT hN hNi
  -- the elementary comparison: (T² + 2G²)·T³ < 8 (T² − G²)^{5/2}
  set u := T ^ 2 - G ^ 2 with hu
  have hupos : 0 < u := by rw [hu]; linarith
  set W := u ^ (5 / 2 : ℝ) with hW
  have hWpos : 0 < W := Real.rpow_pos_of_pos hupos _
  have hD : u ^ (-(5 / 2 : ℝ)) = W⁻¹ := by rw [Real.rpow_neg hupos.le]
  have hW2 : W ^ 2 = u ^ 5 := by
    rw [hW, ← Real.rpow_natCast, ← Real.rpow_mul hupos.le]
    norm_num
  have hkey : (T ^ 2 + 2 * G ^ 2) * T ^ 3 < 8 * W := by
    have hlhs : 0 ≤ (T ^ 2 + 2 * G ^ 2) * T ^ 3 := by positivity
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    -- square: (T²+2G²)² T⁶ < 64 u⁵, i.e. G¹⁰ · p(T²/G²) > 0
    set x := T ^ 2 / G ^ 2 with hxdef
    have hTx : T ^ 2 = x * G ^ 2 := by rw [hxdef]; field_simp
    have hx' : 57 / 25 ≤ x := by
      rw [hxdef, le_div_iff₀ hG2pos]; linarith
    have hp := p_pos x hx'
    have e1 : ((T ^ 2 + 2 * G ^ 2) * T ^ 3) ^ 2 = (T ^ 2 + 2 * G ^ 2) ^ 2 * (T ^ 2) ^ 3 := by ring
    have e2 : (8 * W) ^ 2 = 64 * u ^ 5 := by rw [mul_pow, hW2]; norm_num
    rw [e1, e2, hu, hTx]
    have e3 : 64 * (x * G ^ 2 - G ^ 2) ^ 5 - (x * G ^ 2 + 2 * G ^ 2) ^ 2 * (x * G ^ 2) ^ 3
        = (G ^ 2) ^ 5 * (64 * (x - 1) ^ 5 - x ^ 3 * (x + 2) ^ 2) := by ring
    have : 0 < (G ^ 2) ^ 5 * (64 * (x - 1) ^ 5 - x ^ 3 * (x + 2) ^ 2) := by positivity
    linarith
  -- conclude: 4(T²+2G²)/W − 4/T³ < (7/2)(T²+2G²)/W
  have hT3 : 0 < T ^ 3 := by positivity
  have hfin : 4 * (T ^ 2 + 2 * G ^ 2) * W⁻¹ - 4 / T ^ 3 < 7 / 2 * ((T ^ 2 + 2 * G ^ 2) * W⁻¹) := by
    have : (T ^ 2 + 2 * G ^ 2) * W⁻¹ / 2 < 4 / T ^ 3 := by
      rw [show (T ^ 2 + 2 * G ^ 2) * W⁻¹ / 2 = (T ^ 2 + 2 * G ^ 2) / (2 * W) by
        field_simp]
      rw [div_lt_div_iff₀ (by positivity) hT3]
      linarith
    linarith
  rw [hD] at hrise
  rw [hD]
  linarith

/-! ## The glue, part 1: differentiation under the integral sign -/

/-- Differentiation under the integral sign on `[0, G]`: an integrable weight `φ` against a kernel
`ψ T r` that is differentiable in `T` on a neighbourhood `s` of `T₀`, with `|∂_T ψ| ≤ B` there. -/
theorem hasDerivAt_integral_param {φ : ℝ → ℝ} {ψ ψ' : ℝ → ℝ → ℝ} {G T₀ B : ℝ} {s : Set ℝ}
    (hG : 0 ≤ G) (hs : s ∈ nhds T₀) (hφ : IntervalIntegrable φ volume 0 G)
    (hψc : ∀ T ∈ s, ContinuousOn (ψ T) (Set.Icc 0 G))
    (hψ'c : ContinuousOn (ψ' T₀) (Set.Icc 0 G))
    (hd : ∀ r ∈ Set.Icc 0 G, ∀ T ∈ s, HasDerivAt (fun T => ψ T r) (ψ' T r) T)
    (hb : ∀ r ∈ Set.Icc 0 G, ∀ T ∈ s, |ψ' T r| ≤ B) :
    HasDerivAt (fun T => ∫ r in (0 : ℝ)..G, φ r * ψ T r) (∫ r in (0 : ℝ)..G, φ r * ψ' T₀ r) T₀ := by
  have hT₀ : T₀ ∈ s := mem_of_mem_nhds hs
  have huIoc : Set.uIoc 0 G = Set.Ioc 0 G := Set.uIoc_of_le hG
  have huIcc : Set.uIcc 0 G = Set.Icc 0 G := Set.uIcc_of_le hG
  have hsub : Set.uIoc 0 G ⊆ Set.Icc 0 G := by rw [huIoc]; exact Set.Ioc_subset_Icc_self
  have hφm : AEStronglyMeasurable φ (volume.restrict (Set.uIoc 0 G)) := by
    rw [huIoc]; exact hφ.1.aestronglyMeasurable
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun T r => φ r * ψ T r) (F' := fun T r => φ r * ψ' T r) (μ := volume)
    (a := 0) (b := G) (bound := fun r => B * |φ r|) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with T hT
    exact hφm.mul (((hψc T hT).mono hsub).aestronglyMeasurable measurableSet_uIoc)
  · exact hφ.mul_continuousOn (by rw [huIcc]; exact hψc T₀ hT₀)
  · exact hφm.mul ((hψ'c.mono hsub).aestronglyMeasurable measurableSet_uIoc)
  · refine Filter.Eventually.of_forall (fun r hr T hT => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hb r (hsub hr) T hT) (abs_nonneg _)
  · exact hφ.abs.const_mul B
  · refine Filter.Eventually.of_forall (fun r hr T hT => ?_)
    exact (hd r (hsub hr) T hT).const_mul (φ r)

/-- On `s = ((T₀+G)/2, T₀+1)` the base `T² − r²` stays above `m₀ = ((T₀+G)/2)² − G² > 0`. -/
theorem base_pos {G T₀ : ℝ} (hG : 0 ≤ G) (hGT : G < T₀) : 0 < ((T₀ + G) / 2) ^ 2 - G ^ 2 := by
  nlinarith

theorem base_lower {G T₀ T r : ℝ} (hG : 0 ≤ G) (hGT : G < T₀)
    (hT : T ∈ Set.Ioo ((T₀ + G) / 2) (T₀ + 1)) (hr : r ∈ Set.Icc 0 G) :
    ((T₀ + G) / 2) ^ 2 - G ^ 2 ≤ T ^ 2 - r ^ 2 := by
  have hm0 : 0 ≤ (T₀ + G) / 2 := by linarith
  have h1 : ((T₀ + G) / 2) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hm0 hT.1.le 2
  have h2 : r ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
  linarith

theorem sq_lt_of_mem_nbhd {G T₀ T r : ℝ} (hG : 0 ≤ G) (hGT : G < T₀)
    (hT : T ∈ Set.Ioo ((T₀ + G) / 2) (T₀ + 1)) (hr : r ∈ Set.Icc 0 G) : r ^ 2 < T ^ 2 := by
  have := base_lower hG hGT hT hr
  have := base_pos hG hGT
  linarith

theorem rpow_base_continuousOn {G T p : ℝ} (_hG : 0 ≤ G) (hGT : G ^ 2 < T ^ 2) :
    ContinuousOn (fun r => (T ^ 2 - r ^ 2) ^ p) (Set.Icc 0 G) := by
  apply ContinuousOn.rpow_const (by fun_prop)
  intro r hr
  left
  have : r ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
  linarith

/-- The kernel of the piece of `F_k^s′` below `γ₁`, `r (T² − r²)^{−3/2}`, and its `T`-derivative. -/
def ψA (T r : ℝ) : ℝ := r * (T ^ 2 - r ^ 2) ^ (-(3 / 2 : ℝ))
def ψA' (T r : ℝ) : ℝ := -(3 * T * r * (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ)))

/-- The kernel of the piece of `T·G` below `γ₁`, `r T² (T² − r²)^{−5/2}`, and its `T`-derivative. -/
def ψB (T r : ℝ) : ℝ := r * (T ^ 2 * (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ)))
def ψB' (T r : ℝ) : ℝ := r * -(T * (3 * T ^ 2 + 2 * r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(7 / 2 : ℝ)))

theorem hasDerivAt_ψA (r T : ℝ) (h : r ^ 2 < T ^ 2) :
    HasDerivAt (fun T => ψA T r) (ψA' T r) T := by
  have hpos : 0 < T ^ 2 - r ^ 2 := by linarith
  have h1 := hasDerivAt_sqsubT r T
  have h2 := (h1.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hpos.ne')).const_mul r
  unfold ψA ψA'
  convert h2 using 1
  rw [show (-(3 / 2 : ℝ)) - 1 = -(5 / 2) by norm_num]
  ring

theorem hasDerivAt_ψB (r T : ℝ) (h : r ^ 2 < T ^ 2) :
    HasDerivAt (fun T => ψB T r) (ψB' T r) T :=
  (hasDerivAt_rise r T h).const_mul r

theorem ψA_continuousOn {G T : ℝ} (hG : 0 ≤ G) (hGT : G ^ 2 < T ^ 2) :
    ContinuousOn (ψA T) (Set.Icc 0 G) :=
  continuousOn_id.mul (rpow_base_continuousOn hG hGT)

theorem ψA'_continuousOn {G T : ℝ} (hG : 0 ≤ G) (hGT : G ^ 2 < T ^ 2) :
    ContinuousOn (ψA' T) (Set.Icc 0 G) :=
  ((continuousOn_const.mul continuousOn_id).mul (rpow_base_continuousOn hG hGT)).neg

theorem ψB_continuousOn {G T : ℝ} (hG : 0 ≤ G) (hGT : G ^ 2 < T ^ 2) :
    ContinuousOn (ψB T) (Set.Icc 0 G) :=
  continuousOn_id.mul (continuousOn_const.mul (rpow_base_continuousOn hG hGT))

theorem ψB'_continuousOn {G T : ℝ} (hG : 0 ≤ G) (hGT : G ^ 2 < T ^ 2) :
    ContinuousOn (ψB' T) (Set.Icc 0 G) :=
  continuousOn_id.mul ((continuousOn_const.mul (by fun_prop)).mul
    (rpow_base_continuousOn hG hGT)).neg

theorem ψA'_bound {G T₀ T r : ℝ} (hG : 0 ≤ G) (hGT : G < T₀)
    (hT : T ∈ Set.Ioo ((T₀ + G) / 2) (T₀ + 1)) (hr : r ∈ Set.Icc 0 G) :
    |ψA' T r| ≤ 3 * (T₀ + 1) * G * (((T₀ + G) / 2) ^ 2 - G ^ 2) ^ (-(5 / 2 : ℝ)) := by
  have hm := base_pos hG hGT
  have hb := base_lower hG hGT hT hr
  have hT0 : 0 ≤ T := by linarith [hT.1]
  have hD : (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ)) ≤ (((T₀ + G) / 2) ^ 2 - G ^ 2) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm hb (by norm_num)
  have hD0 : 0 ≤ (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hnn : 0 ≤ 3 * T * r * (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT0) hr.1) hD0
  unfold ψA'
  rw [abs_neg, abs_of_nonneg hnn]
  have h1 : 3 * T ≤ 3 * (T₀ + 1) := by linarith [hT.2]
  have h2 : 3 * T * r ≤ 3 * (T₀ + 1) * G :=
    mul_le_mul h1 hr.2 hr.1 (by linarith)
  exact mul_le_mul h2 hD hD0 (mul_nonneg (by linarith) hG)

theorem ψB'_bound {G T₀ T r : ℝ} (hG : 0 ≤ G) (hGT : G < T₀)
    (hT : T ∈ Set.Ioo ((T₀ + G) / 2) (T₀ + 1)) (hr : r ∈ Set.Icc 0 G) :
    |ψB' T r| ≤ G * ((T₀ + 1) * (3 * (T₀ + 1) ^ 2 + 2 * G ^ 2)
      * (((T₀ + G) / 2) ^ 2 - G ^ 2) ^ (-(7 / 2 : ℝ))) := by
  have hm := base_pos hG hGT
  have hb := base_lower hG hGT hT hr
  have hT0 : 0 ≤ T := by linarith [hT.1]
  have hT1 : T ≤ T₀ + 1 := hT.2.le
  have hD : (T ^ 2 - r ^ 2) ^ (-(7 / 2 : ℝ)) ≤ (((T₀ + G) / 2) ^ 2 - G ^ 2) ^ (-(7 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm hb (by norm_num)
  have hD0 : 0 ≤ (T ^ 2 - r ^ 2) ^ (-(7 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hq : 3 * T ^ 2 + 2 * r ^ 2 ≤ 3 * (T₀ + 1) ^ 2 + 2 * G ^ 2 := by
    have : T ^ 2 ≤ (T₀ + 1) ^ 2 := pow_le_pow_left₀ hT0 hT1 2
    have : r ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
    linarith
  have hq0 : 0 ≤ 3 * T ^ 2 + 2 * r ^ 2 := by positivity
  have hinner : T * (3 * T ^ 2 + 2 * r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(7 / 2 : ℝ))
      ≤ (T₀ + 1) * (3 * (T₀ + 1) ^ 2 + 2 * G ^ 2) * (((T₀ + G) / 2) ^ 2 - G ^ 2) ^ (-(7 / 2 : ℝ)) :=
    mul_le_mul (mul_le_mul hT1 hq hq0 (by linarith)) hD hD0
      (mul_nonneg (by linarith) (by positivity))
  have hinner0 : 0 ≤ T * (3 * T ^ 2 + 2 * r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(7 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg hT0 hq0) hD0
  unfold ψB'
  rw [abs_mul, abs_neg, abs_of_nonneg hinner0, abs_of_nonneg hr.1]
  exact mul_le_mul hr.2 hinner (hinner0) hG

/-- `∫₀^G N₀(r) r (T² − r²)^{−3/2} dr` and `∫₀^G N₀(r) r T² (T² − r²)^{−5/2} dr`. -/
def JA (G T : ℝ) : ℝ := ∫ r in (0 : ℝ)..G, N0 r * ψA T r
def JB (G T : ℝ) : ℝ := ∫ r in (0 : ℝ)..G, N0 r * ψB T r

theorem hasDerivAt_JA {G T : ℝ} (hG : 0 ≤ G) (hGT : G < T) :
    HasDerivAt (JA G) (∫ r in (0 : ℝ)..G, N0 r * ψA' T r) T := by
  have hs : Set.Ioo ((T + G) / 2) (T + 1) ∈ nhds T := Ioo_mem_nhds (by linarith) (by linarith)
  have hT2 : G ^ 2 < T ^ 2 := by nlinarith
  exact hasDerivAt_integral_param hG hs (continuous_N0.intervalIntegrable _ _)
    (fun T' hT' => ψA_continuousOn hG (by
      have := sq_lt_of_mem_nbhd hG hGT hT' ⟨hG, le_refl G⟩; linarith))
    (ψA'_continuousOn hG hT2)
    (fun r hr T' hT' => hasDerivAt_ψA r T' (sq_lt_of_mem_nbhd hG hGT hT' hr))
    (fun r hr T' hT' => ψA'_bound hG hGT hT' hr)

theorem hasDerivAt_JB {G T : ℝ} (hG : 0 ≤ G) (hGT : G < T) :
    HasDerivAt (JB G) (∫ r in (0 : ℝ)..G, N0 r * ψB' T r) T := by
  have hs : Set.Ioo ((T + G) / 2) (T + 1) ∈ nhds T := Ioo_mem_nhds (by linarith) (by linarith)
  have hT2 : G ^ 2 < T ^ 2 := by nlinarith
  exact hasDerivAt_integral_param hG hs (continuous_N0.intervalIntegrable _ _)
    (fun T' hT' => ψB_continuousOn hG (by
      have := sq_lt_of_mem_nbhd hG hGT hT' ⟨hG, le_refl G⟩; linarith))
    (ψB'_continuousOn hG hT2)
    (fun r hr T' hT' => hasDerivAt_ψB r T' (sq_lt_of_mem_nbhd hG hGT hT' hr))
    (fun r hr T' hT' => ψB'_bound hG hGT hT' hr)

/-! ## The glue, part 2: `T·F″ = 1 − T·G`, `(T·G)′ = T·(rise − fall) − holes`, and uniqueness -/

/-- The rise of the piece below `γ₁` and the count constant's fall (1ca(ii)); `R = rise/fall`. -/
def rise (G T : ℝ) : ℝ := ∫ r in (0 : ℝ)..G, |N0 r| * kern T r
def fall (G T : ℝ) : ℝ := 7 / 2 * ((T ^ 2 + 2 * G ^ 2) * (T ^ 2 - G ^ 2) ^ (-(5 / 2 : ℝ)))

/-- `F_k^s′` as the paper states it (1ca(ii)): `ln(T/2T₀) + 4Σ_h (T²−h²)^{−1/2}
+ (7/2)(T²−γ₁²)^{−1/2} + 4∫₀^{γ₁} N₀(r) r (T²−r²)^{−3/2} dr`. -/
def Fp (G T₀ : ℝ) (H : Finset ℝ) (T : ℝ) : ℝ :=
  Real.log (T / (2 * T₀)) + 4 * ∑ h ∈ H, (T ^ 2 - h ^ 2) ^ (-(1 / 2 : ℝ))
    + 7 / 2 * (T ^ 2 - G ^ 2) ^ (-(1 / 2 : ℝ)) + 4 * JA G T

/-- `F_k^s″`, the derivative of `Fp` computed term by term. -/
def Fpp (G : ℝ) (H : Finset ℝ) (T : ℝ) : ℝ :=
  1 / T + 4 * ∑ h ∈ H, -(T * (T ^ 2 - h ^ 2) ^ (-(3 / 2 : ℝ)))
    + 7 / 2 * -(T * (T ^ 2 - G ^ 2) ^ (-(3 / 2 : ℝ))) + 4 * ∫ r in (0 : ℝ)..G, N0 r * ψA' T r

/-- `T·G(T) = 4Σ_h T²(T²−h²)^{−3/2} + (7/2)T²(T²−γ₁²)^{−3/2} + 12T²∫₀^{γ₁} N₀ r (T²−r²)^{−5/2}`. -/
def TG (G : ℝ) (H : Finset ℝ) (T : ℝ) : ℝ :=
  4 * ∑ h ∈ H, T ^ 2 * (T ^ 2 - h ^ 2) ^ (-(3 / 2 : ℝ))
    + 7 / 2 * (T ^ 2 * (T ^ 2 - G ^ 2) ^ (-(3 / 2 : ℝ))) + 12 * JB G T

/-- `(T·G)′`, computed term by term. -/
def TGp (G : ℝ) (H : Finset ℝ) (T : ℝ) : ℝ :=
  4 * ∑ h ∈ H, -(T * (T ^ 2 + 2 * h ^ 2) * (T ^ 2 - h ^ 2) ^ (-(5 / 2 : ℝ)))
    + 7 / 2 * -(T * (T ^ 2 + 2 * G ^ 2) * (T ^ 2 - G ^ 2) ^ (-(5 / 2 : ℝ)))
    + 12 * ∫ r in (0 : ℝ)..G, N0 r * ψB' T r

theorem hasDerivAt_invsqrt (h T : ℝ) (hlt : h ^ 2 < T ^ 2) :
    HasDerivAt (fun T => (T ^ 2 - h ^ 2) ^ (-(1 / 2 : ℝ)))
      (-(T * (T ^ 2 - h ^ 2) ^ (-(3 / 2 : ℝ)))) T := by
  have hpos : 0 < T ^ 2 - h ^ 2 := by linarith
  have h1 := hasDerivAt_sqsubT h T
  have h2 := h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')
  convert h2 using 1
  rw [show (-(1 / 2 : ℝ)) - 1 = -(3 / 2) by norm_num]
  ring

/-- The domain `T > L`, with `L ≥ γ₁ ≥ 0` and every hole in `[0, L]` (the paper's left endpoint is
`max(h_max, γ₁)`). -/
structure Setup (G L : ℝ) (H : Finset ℝ) : Prop where
  hG : 0 ≤ G
  hLG : G ≤ L
  hH : ∀ h ∈ H, 0 ≤ h ∧ h ≤ L

theorem hasDerivAt_Fp {G T₀ L : ℝ} {H : Finset ℝ} (S : Setup G L H) (hT₀ : 0 < T₀) {T : ℝ}
    (hT : L < T) : HasDerivAt (Fp G T₀ H) (Fpp G H T) T := by
  have hT0 : 0 < T := by linarith [S.hG, S.hLG]
  have hGT : G < T := by linarith [S.hLG]
  have h1 : HasDerivAt (fun T => Real.log (T / (2 * T₀))) (1 / T) T := by
    have hd : HasDerivAt (fun T : ℝ => T / (2 * T₀)) (1 / (2 * T₀)) T :=
      (hasDerivAt_id T).div_const (2 * T₀)
    have h := hd.log (div_pos hT0 (by linarith)).ne'
    convert h using 1
    field_simp
  have h2 : HasDerivAt (fun T => ∑ h ∈ H, (T ^ 2 - h ^ 2) ^ (-(1 / 2 : ℝ)))
      (∑ h ∈ H, -(T * (T ^ 2 - h ^ 2) ^ (-(3 / 2 : ℝ)))) T := by
    apply HasDerivAt.fun_sum
    intro h hh
    obtain ⟨h0, hL⟩ := S.hH h hh
    exact hasDerivAt_invsqrt h T (by nlinarith)
  have h3 := hasDerivAt_invsqrt G T (by nlinarith [S.hG])
  have h4 := hasDerivAt_JA S.hG hGT
  exact ((h1.add (h2.const_mul 4)).add (h3.const_mul (7 / 2))).add (h4.const_mul 4)

theorem hasDerivAt_TG {G L : ℝ} {H : Finset ℝ} (S : Setup G L H) {T : ℝ} (hT : L < T) :
    HasDerivAt (TG G H) (TGp G H T) T := by
  have hGT : G < T := by linarith [S.hLG]
  have h2 : HasDerivAt (fun T => ∑ h ∈ H, T ^ 2 * (T ^ 2 - h ^ 2) ^ (-(3 / 2 : ℝ)))
      (∑ h ∈ H, -(T * (T ^ 2 + 2 * h ^ 2) * (T ^ 2 - h ^ 2) ^ (-(5 / 2 : ℝ)))) T := by
    apply HasDerivAt.fun_sum
    intro h hh
    obtain ⟨h0, hL⟩ := S.hH h hh
    exact hasDerivAt_fall h T (by nlinarith)
  have h3 := hasDerivAt_fall G T (by nlinarith [S.hG])
  have h4 := hasDerivAt_JB S.hG hGT
  exact ((h2.const_mul 4).add (h3.const_mul (7 / 2))).add (h4.const_mul 12)

/-- **1ca(ii): `T·F_k^s″ = 1 − T·G(T)`.** -/
theorem T_mul_Fpp (G : ℝ) (H : Finset ℝ) {T : ℝ} (hT : T ≠ 0) :
    T * Fpp G H T = 1 - TG G H T := by
  have hA : T * ∫ r in (0 : ℝ)..G, N0 r * ψA' T r = -3 * JB G T := by
    unfold JB
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    funext r
    unfold ψA' ψB
    ring
  have hS : T * ∑ h ∈ H, -(T * (T ^ 2 - h ^ 2) ^ (-(3 / 2 : ℝ)))
      = -∑ h ∈ H, T ^ 2 * (T ^ 2 - h ^ 2) ^ (-(3 / 2 : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    congr 1
    funext h
    ring
  have e1 : T * (1 / T) = 1 := by field_simp
  unfold Fpp TG
  calc T * (1 / T + 4 * ∑ h ∈ H, -(T * (T ^ 2 - h ^ 2) ^ (-(3 / 2 : ℝ)))
        + 7 / 2 * -(T * (T ^ 2 - G ^ 2) ^ (-(3 / 2 : ℝ))) + 4 * ∫ r in (0 : ℝ)..G, N0 r * ψA' T r)
      = T * (1 / T) + 4 * (T * ∑ h ∈ H, -(T * (T ^ 2 - h ^ 2) ^ (-(3 / 2 : ℝ))))
        + 7 / 2 * -(T ^ 2 * (T ^ 2 - G ^ 2) ^ (-(3 / 2 : ℝ)))
        + 4 * (T * ∫ r in (0 : ℝ)..G, N0 r * ψA' T r) := by ring
    _ = _ := by rw [e1, hS, hA]; ring

/-- **1ca(ii): `(T·G)′ = −4Σ_h T(T²+2h²)(T²−h²)^{−5/2} − T·fall + T·rise`** — the holes' and the
constant's falls against the rise of the piece below `γ₁` (using `N₀ ≤ 0` there). -/
theorem TGp_eq {G L : ℝ} {H : Finset ℝ} (S : Setup G L H) (hGe : G ≤ 2 * π * Real.exp 1)
    (T : ℝ) :
    TGp G H T = 4 * ∑ h ∈ H, -(T * (T ^ 2 + 2 * h ^ 2) * (T ^ 2 - h ^ 2) ^ (-(5 / 2 : ℝ)))
      - T * fall G T + T * rise G T := by
  have hI : 12 * ∫ r in (0 : ℝ)..G, N0 r * ψB' T r = T * rise G T := by
    unfold rise
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le S.hG] at hr
    have hN := N0_nonpos hr.1 (le_trans hr.2 hGe)
    simp only
    rw [abs_of_nonpos hN]
    unfold ψB' kern
    ring
  unfold TGp fall
  rw [hI]
  ring

theorem TGp_neg {G L : ℝ} {H : Finset ℝ} (S : Setup G L H) (hGe : G ≤ 2 * π * Real.exp 1)
    {T : ℝ} (hT : L < T) (hR : rise G T < fall G T) : TGp G H T < 0 := by
  have hT0 : 0 < T := by linarith [S.hG, S.hLG]
  rw [TGp_eq S hGe, Finset.sum_neg_distrib]
  have hsum : 0 ≤ ∑ h ∈ H, T * (T ^ 2 + 2 * h ^ 2) * (T ^ 2 - h ^ 2) ^ (-(5 / 2 : ℝ)) := by
    apply Finset.sum_nonneg
    intro h hh
    obtain ⟨h0, hL⟩ := S.hH h hh
    have hD : 0 ≤ (T ^ 2 - h ^ 2) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by nlinarith) _
    exact mul_nonneg (mul_nonneg hT0.le (by positivity)) hD
  have := mul_lt_mul_of_pos_left hR hT0
  linarith

/-- **`T·G` is strictly decreasing on the domain wherever `R < 1`** (1ca(ii)). -/
theorem TG_strictAntiOn {G L : ℝ} {H : Finset ℝ} (S : Setup G L H)
    (hGe : G ≤ 2 * π * Real.exp 1) (hR : ∀ T, L < T → rise G T < fall G T) :
    StrictAntiOn (TG G H) (Set.Ioi L) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi L) (f' := TGp G H)
  · intro x hx
    exact (hasDerivAt_TG S hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_TG S hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact TGp_neg S hGe hx (hR x hx)

/-! ## The glue, part 3: `R < 1` on `(γ₁, 1.51γ₁]` proved (the paper computes it) -/

/-- `N₀` is nondecreasing on `[2π, ∞)` (`d/ds (s ln s − s) = ln s ≥ 0` for `s ≥ 1`). -/
theorem N0_mono {r r' : ℝ} (hr : 2 * π ≤ r) (hrr' : r ≤ r') : N0 r ≤ N0 r' := by
  have h2pi : 0 < 2 * π := by positivity
  have hs1 : 1 ≤ r / (2 * π) := by rw [le_div_iff₀ h2pi]; linarith
  have hss' : r / (2 * π) ≤ r' / (2 * π) := div_le_div_of_nonneg_right hrr' h2pi.le
  set s := r / (2 * π) with hs
  set s' := r' / (2 * π) with hs'
  have hspos : 0 < s := by linarith
  have hs'pos : 0 < s' := by linarith
  show s * (Real.log s - 1) ≤ s' * (Real.log s' - 1)
  have hlog : 1 - s / s' ≤ Real.log s' - Real.log s := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hs'pos hspos)
    rwa [Real.log_div hs'pos.ne' hspos.ne', inv_div] at h
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg hs1
  have h1 : s' - s ≤ s' * (Real.log s' - Real.log s) := by
    have h := mul_le_mul_of_nonneg_left hlog hs'pos.le
    have e : s' * (1 - s / s') = s' - s := by field_simp
    linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hss') hlogs]

/-- `N₀(11.9) ≥ −0.701` (true value −0.68436), from `π` bounds and `exp 0.63 < 1.8939`. -/
theorem N0_119_ge : -(701 / 1000 : ℝ) ≤ N0 (119 / 10) := by
  have h2pi : 0 < 2 * π := by positivity
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hs_lo : (18939 / 10000 : ℝ) ≤ (119 / 10 : ℝ) / (2 * π) := by
    rw [le_div_iff₀ h2pi]; nlinarith
  have hs_hi : (119 / 10 : ℝ) / (2 * π) ≤ 1894 / 1000 := by
    rw [div_le_iff₀ h2pi]; nlinarith
  set s := (119 / 10 : ℝ) / (2 * π) with hs
  have hlog : (63 / 100 : ℝ) ≤ Real.log s := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have hb := Real.exp_bound (x := 63 / 100) (by rw [abs_of_pos (by norm_num)]; norm_num)
      (n := 5) (by norm_num)
    have hb' := (abs_sub_le_iff.1 hb).1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb'
    norm_num at hb'
    linarith
  have hlog1 : Real.log s ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < s)
    linarith
  show -(701 / 1000 : ℝ) ≤ s * (Real.log s - 1)
  nlinarith [mul_nonneg (sub_nonneg.2 hs_hi) (sub_nonneg.2 hlog1)]

/-- `|N₀| ≤ 0.701` on `[11.9, 2πe]`. -/
theorem abs_N0_le_c {r : ℝ} (hr1 : 119 / 10 ≤ r) (hr2 : r ≤ 2 * π * Real.exp 1) :
    |N0 r| ≤ 701 / 1000 := by
  have hN := N0_nonpos (by linarith) hr2
  have h2pi : 2 * π ≤ 119 / 10 := by nlinarith [Real.pi_lt_d6]
  have hmono := N0_mono h2pi hr1
  have := N0_119_ge
  rw [abs_of_nonpos hN]
  linarith

/-- The kernel's antiderivative `K(r) = 4(T²+2r²)(T²−r²)^{−5/2}`. -/
def Kant (T r : ℝ) : ℝ := 4 * (T ^ 2 + 2 * r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(5 / 2 : ℝ))

theorem integral_kern_between {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b < T) :
    ∫ r in a..b, kern T r = Kant T b - Kant T a := by
  have hb2 : b ^ 2 < T ^ 2 := by nlinarith
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r hr
    rw [Set.uIcc_of_le hab] at hr
    have : r ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by linarith [hr.1]) hr.2 2
    exact hasDerivAt_antider T r (by linarith)
  · apply ContinuousOn.intervalIntegrable
    apply (kern_continuousOn T b hb2 (by linarith)).mono
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ b)]
    exact Set.Icc_subset_Icc ha le_rfl

/-- **`R < 1` on `(γ₁, 1.51γ₁]`, for every `γ₁ ∈ [14, 2πe]`** — the part the paper computes and
gates. Split the rise at `r₁ = 0.85γ₁`: `|N₀| ≤ 1` below, `|N₀| ≤ |N₀(11.9)| ≤ 0.701` above (`N₀` is
nondecreasing and nonpositive on `[2π, 2πe]`), so `rise < K(r₁) + 0.701(K(γ₁) − K(r₁))`, and
`0.299 K(r₁) ≤ 0.174 K(γ₁)` for `T² ≤ 2.2801γ₁²` (squared, with `(T²+2r₁²) ≤ 0.8704(T²+2γ₁²)` and
`T²−γ₁² ≤ 0.8219(T²−r₁²)`); hence `rise < (7/8)K(γ₁) = fall`. The bound's worst case is
`R ≤ 0.983` at `T = 1.51γ₁` (the true `R` there is 0.68). -/
theorem R_lt_one_low (G T : ℝ) (hG14 : 14 ≤ G) (hGe : G ≤ 2 * π * Real.exp 1) (hGT : G < T)
    (hx : T ^ 2 ≤ 22801 / 10000 * G ^ 2) : rise G T < fall G T := by
  have hG0 : 0 < G := by linarith
  set r₁ := 17 / 20 * G with hr₁
  have hr₁0 : 0 ≤ r₁ := by positivity
  have hr₁G : r₁ ≤ G := by linarith
  have hr₁T : r₁ < T := by linarith
  have hT0 : 0 < T := by linarith
  have hG2 : G ^ 2 < T ^ 2 := by nlinarith
  have hcont : ContinuousOn (fun r => |N0 r| * kern T r) (Set.Icc 0 G) := by
    have := kern_continuousOn T G hG2 hG0.le
    rw [Set.uIcc_of_le hG0.le] at this
    exact (continuous_N0.abs.continuousOn).mul this
  have hi1 : IntervalIntegrable (fun r => |N0 r| * kern T r) volume 0 r₁ := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    rw [Set.uIcc_of_le hr₁0]; exact Set.Icc_subset_Icc le_rfl hr₁G
  have hi2 : IntervalIntegrable (fun r => |N0 r| * kern T r) volume r₁ G := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    rw [Set.uIcc_of_le hr₁G]; exact Set.Icc_subset_Icc hr₁0 le_rfl
  have hk2 : IntervalIntegrable (fun r => 701 / 1000 * kern T r) volume r₁ G := by
    apply ContinuousOn.intervalIntegrable
    have := kern_continuousOn T G hG2 hG0.le
    rw [Set.uIcc_of_le hG0.le] at this
    apply (continuousOn_const.mul this).mono
    rw [Set.uIcc_of_le hr₁G]; exact Set.Icc_subset_Icc hr₁0 le_rfl
  -- piece below r₁: |N₀| ≤ 1
  have hp1 : ∫ r in (0 : ℝ)..r₁, |N0 r| * kern T r ≤ Kant T r₁ - 4 / T ^ 3 :=
    rise_le N0 T r₁ hr₁0 hr₁T
      (fun r hr => abs_N0_le_one hr.1 (by linarith [hr.2])) hi1
  -- piece above r₁: |N₀| ≤ 0.701
  have hp2 : ∫ r in r₁..G, |N0 r| * kern T r ≤ 701 / 1000 * (Kant T G - Kant T r₁) := by
    rw [← integral_kern_between hr₁0 hr₁G hGT, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hr₁G hi2 hk2
    intro r hr
    have hr2 : r ^ 2 ≤ T ^ 2 := by nlinarith [hr.1, hr.2]
    have hk := kern_nonneg T r (by linarith [hr.1]) hr2
    have hN := abs_N0_le_c (r := r) (by linarith [hr.1]) (by linarith [hr.2])
    exact mul_le_mul_of_nonneg_right hN hk
  have hsplit : rise G T
      = (∫ r in (0 : ℝ)..r₁, |N0 r| * kern T r) + ∫ r in r₁..G, |N0 r| * kern T r := by
    unfold rise
    rw [intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  -- the key comparison 0.299 K(r₁) ≤ 0.174 K(γ₁)
  have hA0 : 0 < T ^ 2 - r₁ ^ 2 := by nlinarith
  have hB0 : 0 < T ^ 2 - G ^ 2 := by nlinarith
  have hr1sq : r₁ ^ 2 = 289 / 400 * G ^ 2 := by rw [hr₁]; ring
  have hpoly : (299 / 1000 : ℝ) ^ 2 * (T ^ 2 + 2 * r₁ ^ 2) ^ 2 * (T ^ 2 - G ^ 2) ^ 5
      ≤ (174 / 1000) ^ 2 * (T ^ 2 + 2 * G ^ 2) ^ 2 * (T ^ 2 - r₁ ^ 2) ^ 5 := by
    rw [hr1sq]
    have hY : 0 < G ^ 2 := by positivity
    have ha0 : 0 ≤ T ^ 2 + 2 * (289 / 400 * G ^ 2) := by positivity
    have hav : T ^ 2 + 2 * (289 / 400 * G ^ 2) ≤ 544 / 625 * (T ^ 2 + 2 * G ^ 2) := by linarith
    have hd0 : 0 ≤ T ^ 2 - G ^ 2 := hB0.le
    have hdu : T ^ 2 - G ^ 2 ≤ 8219 / 10000 * (T ^ 2 - 289 / 400 * G ^ 2) := by linarith
    have he0 : 0 ≤ T ^ 2 - 289 / 400 * G ^ 2 := by linarith
    have h1 : (T ^ 2 + 2 * (289 / 400 * G ^ 2)) ^ 2 ≤ ((544 / 625) * (T ^ 2 + 2 * G ^ 2)) ^ 2 :=
      pow_le_pow_left₀ ha0 hav 2
    have h2 : (T ^ 2 - G ^ 2) ^ 5 ≤ ((8219 / 10000) * (T ^ 2 - 289 / 400 * G ^ 2)) ^ 5 :=
      pow_le_pow_left₀ hd0 hdu 5
    have h3 : (T ^ 2 + 2 * (289 / 400 * G ^ 2)) ^ 2 * (T ^ 2 - G ^ 2) ^ 5
        ≤ ((544 / 625) * (T ^ 2 + 2 * G ^ 2)) ^ 2 * ((8219 / 10000) * (T ^ 2 - 289 / 400 * G ^ 2)) ^ 5 :=
      mul_le_mul h1 h2 (pow_nonneg hd0 5) (sq_nonneg _)
    have hnum : (299 / 1000 : ℝ) ^ 2 * ((544 / 625) ^ 2 * (8219 / 10000) ^ 5) ≤ (174 / 1000) ^ 2 := by
      norm_num
    have hpos : 0 ≤ (T ^ 2 + 2 * G ^ 2) ^ 2 * (T ^ 2 - 289 / 400 * G ^ 2) ^ 5 :=
      mul_nonneg (sq_nonneg _) (pow_nonneg he0 5)
    calc (299 / 1000 : ℝ) ^ 2 * (T ^ 2 + 2 * (289 / 400 * G ^ 2)) ^ 2 * (T ^ 2 - G ^ 2) ^ 5
        = (299 / 1000 : ℝ) ^ 2 * ((T ^ 2 + 2 * (289 / 400 * G ^ 2)) ^ 2 * (T ^ 2 - G ^ 2) ^ 5) := by
          ring
      _ ≤ (299 / 1000 : ℝ) ^ 2 * (((544 / 625) * (T ^ 2 + 2 * G ^ 2)) ^ 2
            * ((8219 / 10000) * (T ^ 2 - 289 / 400 * G ^ 2)) ^ 5) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = ((299 / 1000 : ℝ) ^ 2 * ((544 / 625) ^ 2 * (8219 / 10000) ^ 5))
            * ((T ^ 2 + 2 * G ^ 2) ^ 2 * (T ^ 2 - 289 / 400 * G ^ 2) ^ 5) := by ring
      _ ≤ (174 / 1000) ^ 2 * ((T ^ 2 + 2 * G ^ 2) ^ 2 * (T ^ 2 - 289 / 400 * G ^ 2) ^ 5) :=
          mul_le_mul_of_nonneg_right hnum hpos
      _ = (174 / 1000) ^ 2 * (T ^ 2 + 2 * G ^ 2) ^ 2 * (T ^ 2 - 289 / 400 * G ^ 2) ^ 5 := by ring
  set A := (T ^ 2 - r₁ ^ 2) ^ (5 / 2 : ℝ) with hA
  set B := (T ^ 2 - G ^ 2) ^ (5 / 2 : ℝ) with hB
  have hApos : 0 < A := Real.rpow_pos_of_pos hA0 _
  have hBpos : 0 < B := Real.rpow_pos_of_pos hB0 _
  have hA2 : A ^ 2 = (T ^ 2 - r₁ ^ 2) ^ 5 := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]; norm_num
  have hB2 : B ^ 2 = (T ^ 2 - G ^ 2) ^ 5 := by
    rw [hB, ← Real.rpow_natCast, ← Real.rpow_mul hB0.le]; norm_num
  have hsq : ((299 / 1000) * (T ^ 2 + 2 * r₁ ^ 2) * B) ^ 2
      ≤ ((174 / 1000) * (T ^ 2 + 2 * G ^ 2) * A) ^ 2 := by
    have e1 : ((299 / 1000) * (T ^ 2 + 2 * r₁ ^ 2) * B) ^ 2
        = (299 / 1000 : ℝ) ^ 2 * (T ^ 2 + 2 * r₁ ^ 2) ^ 2 * B ^ 2 := by ring
    have e2 : ((174 / 1000) * (T ^ 2 + 2 * G ^ 2) * A) ^ 2
        = (174 / 1000 : ℝ) ^ 2 * (T ^ 2 + 2 * G ^ 2) ^ 2 * A ^ 2 := by ring
    rw [e1, e2, hA2, hB2]
    exact hpoly
  have hlin : (299 / 1000) * (T ^ 2 + 2 * r₁ ^ 2) * B ≤ (174 / 1000) * (T ^ 2 + 2 * G ^ 2) * A :=
    le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  have hKr : Kant T r₁ = 4 * (T ^ 2 + 2 * r₁ ^ 2) * A⁻¹ := by
    unfold Kant; rw [Real.rpow_neg hA0.le]
  have hKG : Kant T G = 4 * (T ^ 2 + 2 * G ^ 2) * B⁻¹ := by
    unfold Kant; rw [Real.rpow_neg hB0.le]
  have hkey : (299 / 1000) * Kant T r₁ ≤ (174 / 1000) * Kant T G := by
    rw [hKr, hKG]
    have e1 : (299 / 1000) * (4 * (T ^ 2 + 2 * r₁ ^ 2) * A⁻¹)
        = 4 * ((299 / 1000) * (T ^ 2 + 2 * r₁ ^ 2) * B) / (A * B) := by
      field_simp
    have e2 : (174 / 1000) * (4 * (T ^ 2 + 2 * G ^ 2) * B⁻¹)
        = 4 * ((174 / 1000) * (T ^ 2 + 2 * G ^ 2) * A) / (A * B) := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hfall : fall G T = 7 / 8 * Kant T G := by unfold fall Kant; ring
  have hT3 : 0 < 4 / T ^ 3 := by positivity
  rw [hsplit, hfall]
  linarith

/-- **`R < 1` on all of `(γ₁, ∞)`** for `γ₁ ∈ [14, 2πe]`: the elementary bound beyond `1.51γ₁`
(`R_lt_one`) and the split bound below it (`R_lt_one_low`). -/
theorem rise_lt_fall {G T : ℝ} (hG14 : 14 ≤ G) (hGe : G ≤ 2 * π * Real.exp 1) (hGT : G < T) :
    rise G T < fall G T := by
  rcases le_or_gt (22801 / 10000 * G ^ 2) (T ^ 2) with h | h
  · exact R_lt_one G T (by linarith) hGe (by linarith) h
  · exact R_lt_one_low G T hG14 hGe hGT h.le

/-! ## The glue, part 4: `Fp` is the derivative of the paper's `F_k^s` -/

/-- The weight of 1bs(ii)'s Stieltjes integration, `w_T(r) = 4/(r√(1 − r²/T²))`. -/
def wT (T r : ℝ) : ℝ := 4 / (r * Real.sqrt (1 - r ^ 2 / T ^ 2))

/-- **The smooth functional of 1ca(i)**, `F_k^s(T) = I(T) − 2aT + 4Σ_h arccosh(T/h)
+ (7/2) arccosh(T/γ₁) − ∫₀^{γ₁} N₀(r) w_T(r) dr`, with `I(T) = T[ln(T/2π) − 1 − ln 2]`. -/
def Fs (G a : ℝ) (H : Finset ℝ) (T : ℝ) : ℝ :=
  T * (Real.log (T / (2 * π)) - 1 - Real.log 2) - 2 * a * T
    + 4 * ∑ h ∈ H, Real.arcosh (T / h) + 7 / 2 * Real.arcosh (T / G)
    - ∫ r in (0 : ℝ)..G, N0 r * wT T r

/-- `N₀(r)/r` and the regular part of the weight, `4T(T² − r²)^{−1/2}`, with its `T`-derivative. -/
def φC (r : ℝ) : ℝ := (Real.log (r / (2 * π)) - 1) / (2 * π)
def ψC (T r : ℝ) : ℝ := 4 * T * (T ^ 2 - r ^ 2) ^ (-(1 / 2 : ℝ))
def ψC' (T r : ℝ) : ℝ := -(4 * r ^ 2 * (T ^ 2 - r ^ 2) ^ (-(3 / 2 : ℝ)))

theorem sqrt_ratio {T r : ℝ} (hT : 0 < T) (hx : 0 < T ^ 2 - r ^ 2) :
    Real.sqrt (1 - r ^ 2 / T ^ 2) = Real.sqrt (T ^ 2 - r ^ 2) / T := by
  rw [show 1 - r ^ 2 / T ^ 2 = (T ^ 2 - r ^ 2) / T ^ 2 by field_simp,
    Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ T ^ 2), Real.sqrt_sq hT.le]

theorem rpow_neg_half {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]

theorem N0_wT_eq {T r : ℝ} (hr : 0 < r) (hrT : r < T) : N0 r * wT T r = φC r * ψC T r := by
  have hT : 0 < T := by linarith
  have hx : 0 < T ^ 2 - r ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (T ^ 2 - r ^ 2) := Real.sqrt_pos.2 hx
  unfold N0 wT φC ψC
  rw [sqrt_ratio hT hx, rpow_neg_half hx]
  field_simp

theorem intervalIntegrable_φC {G : ℝ} (hG : 0 ≤ G) : IntervalIntegrable φC volume 0 G := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hG]
  have hlog : IntegrableOn (fun r => (Real.log r - Real.log (2 * π) - 1) / (2 * π))
      (Set.Ioc 0 G) := by
    have h1 : IntervalIntegrable (fun r => (Real.log r - Real.log (2 * π) - 1) / (2 * π))
        volume 0 G :=
      (((intervalIntegrable_log' (a := 0) (b := G)).sub
        (intervalIntegrable_const (c := Real.log (2 * π)))).sub
        (intervalIntegrable_const (c := (1 : ℝ)))).div_const (2 * π)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hG] at h1
  apply hlog.congr_fun _ measurableSet_Ioc
  intro r hr
  simp only [φC]
  rw [Real.log_div hr.1.ne' (by positivity)]

theorem hasDerivAt_ψC (r T : ℝ) (h : r ^ 2 < T ^ 2) :
    HasDerivAt (fun T => ψC T r) (ψC' T r) T := by
  have hpos : 0 < T ^ 2 - r ^ 2 := by linarith
  have h1 := hasDerivAt_sqsubT r T
  have h2 := h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')
  have h3 : HasDerivAt (fun T => 4 * T) 4 T := by
    simpa using (hasDerivAt_id T).const_mul 4
  have h4 := h3.mul h2
  unfold ψC ψC'
  convert h4 using 1
  have hsplit : (T ^ 2 - r ^ 2) ^ (-(1 / 2 : ℝ))
      = (T ^ 2 - r ^ 2) * (T ^ 2 - r ^ 2) ^ (-(3 / 2 : ℝ)) := by
    rw [rpow_eq_mul_rpow_sub_one hpos]; norm_num
  rw [show (-(1 / 2 : ℝ)) - 1 = -(3 / 2) by norm_num, hsplit]
  ring

theorem ψC_continuousOn {G T : ℝ} (hG : 0 ≤ G) (hGT : G ^ 2 < T ^ 2) :
    ContinuousOn (ψC T) (Set.Icc 0 G) :=
  continuousOn_const.mul (rpow_base_continuousOn hG hGT)

theorem ψC'_continuousOn {G T : ℝ} (hG : 0 ≤ G) (hGT : G ^ 2 < T ^ 2) :
    ContinuousOn (ψC' T) (Set.Icc 0 G) :=
  ((continuousOn_const.mul (by fun_prop)).mul (rpow_base_continuousOn hG hGT)).neg

theorem ψC'_bound {G T₀ T r : ℝ} (hG : 0 ≤ G) (hGT : G < T₀)
    (hT : T ∈ Set.Ioo ((T₀ + G) / 2) (T₀ + 1)) (hr : r ∈ Set.Icc 0 G) :
    |ψC' T r| ≤ 4 * G ^ 2 * (((T₀ + G) / 2) ^ 2 - G ^ 2) ^ (-(3 / 2 : ℝ)) := by
  have hm := base_pos hG hGT
  have hb := base_lower hG hGT hT hr
  have hD : (T ^ 2 - r ^ 2) ^ (-(3 / 2 : ℝ)) ≤ (((T₀ + G) / 2) ^ 2 - G ^ 2) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm hb (by norm_num)
  have hD0 : 0 ≤ (T ^ 2 - r ^ 2) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hr2 : r ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
  unfold ψC'
  rw [abs_neg, abs_of_nonneg (by positivity)]
  exact mul_le_mul (by linarith) hD hD0 (by positivity)

/-- The piece below `γ₁` of `F_k^s` has derivative `−4∫₀^{γ₁} N₀ r (T² − r²)^{−3/2}` … as
`∫ N₀ w_T` has derivative `∫ N₀ ∂_T w_T = −4 JA`. -/
theorem hasDerivAt_int_N0_wT {G T : ℝ} (hG : 0 ≤ G) (hGT : G < T) :
    HasDerivAt (fun T => ∫ r in (0 : ℝ)..G, N0 r * wT T r) (-4 * JA G T) T := by
  have hs : Set.Ioo ((T + G) / 2) (T + 1) ∈ nhds T := Ioo_mem_nhds (by linarith) (by linarith)
  have hT2 : G ^ 2 < T ^ 2 := by nlinarith
  have hmain := hasDerivAt_integral_param hG hs (intervalIntegrable_φC hG)
    (fun T' hT' => ψC_continuousOn hG (by
      have := sq_lt_of_mem_nbhd hG hGT hT' ⟨hG, le_refl G⟩; linarith))
    (ψC'_continuousOn hG hT2)
    (fun r hr T' hT' => hasDerivAt_ψC r T' (sq_lt_of_mem_nbhd hG hGT hT' hr))
    (fun r hr T' hT' => ψC'_bound hG hGT hT' hr)
  -- the two integrands agree for r ∈ (0, G] whenever T' > G
  have heq : (fun T' => ∫ r in (0 : ℝ)..G, N0 r * wT T' r)
      =ᶠ[nhds T] (fun T' => ∫ r in (0 : ℝ)..G, φC r * ψC T' r) := by
    filter_upwards [Ioi_mem_nhds hGT] with T' hT'
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun r hr => ?_)
    rw [Set.uIoc_of_le hG] at hr
    exact N0_wT_eq hr.1 (lt_of_le_of_lt hr.2 hT')
  have hval : ∫ r in (0 : ℝ)..G, φC r * ψC' T r = -4 * JA G T := by
    unfold JA
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext r
    unfold φC ψC' N0 ψA
    ring
  rw [← hval]
  exact hmain.congr_of_eventuallyEq heq

theorem hasDerivAt_arcosh_div {h T : ℝ} (hh : 0 < h) (hT : h < T) :
    HasDerivAt (fun T => Real.arcosh (T / h)) ((T ^ 2 - h ^ 2) ^ (-(1 / 2 : ℝ))) T := by
  have h1 : T / h ∈ Set.Ioi 1 := by
    rw [Set.mem_Ioi, one_lt_div hh]; exact hT
  have hd : HasDerivAt (fun T : ℝ => T / h) (1 / h) T := (hasDerivAt_id T).div_const h
  have h2 := (Real.hasDerivAt_arcosh h1).comp T hd
  refine h2.congr_deriv ?_
  have hx : 0 < T ^ 2 - h ^ 2 := by nlinarith
  have hsq : Real.sqrt ((T / h) ^ 2 - 1) = Real.sqrt (T ^ 2 - h ^ 2) / h := by
    rw [show (T / h) ^ 2 - 1 = (T ^ 2 - h ^ 2) / h ^ 2 by field_simp,
      Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ h ^ 2), Real.sqrt_sq hh.le]
  have hs : 0 < Real.sqrt (T ^ 2 - h ^ 2) := Real.sqrt_pos.2 hx
  rw [rpow_neg_half hx, hsq]
  field_simp

/-- **`F_k^s′ = Fp`**: the paper's smooth functional has derivative `Fp` with `T₀ = 2πe^{2a}`
(`I′ − 2a = ln(T/4π) − 2a = ln(T/2T₀)`), for `T` above `γ₁` and every hole. -/
theorem hasDerivAt_Fs {G a L : ℝ} {H : Finset ℝ} (hG : 0 < G) (hLG : G ≤ L)
    (hH : ∀ h ∈ H, 0 < h ∧ h ≤ L) {T : ℝ} (hT : L < T) :
    HasDerivAt (Fs G a H) (Fp G (2 * π * Real.exp (2 * a)) H T) T := by
  have hT0 : 0 < T := by linarith
  have hGT : G < T := by linarith
  have h2pi : 0 < 2 * π := by positivity
  -- I(T) − 2aT
  have hlog : HasDerivAt (fun T => Real.log (T / (2 * π))) (1 / T) T := by
    have hd : HasDerivAt (fun T : ℝ => T / (2 * π)) (1 / (2 * π)) T :=
      (hasDerivAt_id T).div_const (2 * π)
    have h := hd.log (div_pos hT0 h2pi).ne'
    convert h using 1
    field_simp
  have hI : HasDerivAt (fun T => T * (Real.log (T / (2 * π)) - 1 - Real.log 2))
      (Real.log (T / (2 * π)) - Real.log 2) T := by
    have h := (hasDerivAt_id T).mul ((hlog.sub_const 1).sub_const (Real.log 2))
    refine h.congr_deriv ?_
    show 1 * (Real.log (T / (2 * π)) - 1 - Real.log 2) + T * (1 / T)
      = Real.log (T / (2 * π)) - Real.log 2
    rw [mul_one_div_cancel hT0.ne']
    ring
  have hlin : HasDerivAt (fun T => 2 * a * T) (2 * a) T := by
    simpa using (hasDerivAt_id T).const_mul (2 * a)
  have hsum : HasDerivAt (fun T => ∑ h ∈ H, Real.arcosh (T / h))
      (∑ h ∈ H, (T ^ 2 - h ^ 2) ^ (-(1 / 2 : ℝ))) T := by
    apply HasDerivAt.fun_sum
    intro h hh
    obtain ⟨h0, hL⟩ := hH h hh
    exact hasDerivAt_arcosh_div h0 (by linarith)
  have hG' := hasDerivAt_arcosh_div hG hGT
  have hint := hasDerivAt_int_N0_wT hG.le hGT
  have hall := (((hI.sub hlin).add (hsum.const_mul 4)).add (hG'.const_mul (7 / 2))).sub hint
  refine hall.congr_deriv ?_
  -- ln(T/2π) − ln 2 − 2a = ln(T/(2T₀)),  T₀ = 2πe^{2a}
  have hl : Real.log (T / (2 * (2 * π * Real.exp (2 * a))))
      = Real.log (T / (2 * π)) - Real.log 2 - 2 * a := by
    rw [Real.log_div hT0.ne' (by positivity), Real.log_div hT0.ne' h2pi.ne',
      Real.log_mul (by norm_num) (by positivity), Real.log_mul h2pi.ne' (by positivity),
      Real.log_exp]
    ring
  unfold Fp
  rw [hl]
  ring

end WeilForm

#print axioms WeilForm.abs_N0_le_one
#print axioms WeilForm.integral_kern
#print axioms WeilForm.rise_le
#print axioms WeilForm.p_pos
#print axioms WeilForm.R_lt_one
#print axioms WeilForm.N0_nonpos
#print axioms WeilForm.hasDerivAt_fall
#print axioms WeilForm.hasDerivAt_rise
#print axioms WeilForm.hasDerivAt_JA
#print axioms WeilForm.hasDerivAt_JB
#print axioms WeilForm.T_mul_Fpp
#print axioms WeilForm.TG_strictAntiOn
#print axioms WeilForm.R_lt_one_low
#print axioms WeilForm.rise_lt_fall
#print axioms WeilForm.hasDerivAt_Fs
#print axioms WeilForm.hasDerivAt_sq_mul_rpow
