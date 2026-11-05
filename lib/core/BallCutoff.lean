import Mathlib
import BallDensity

/-! # Sampling at the zeros up to height `T ≍ N`: `SamplingAtZeros c C 0` under RH

Plain statement. Under RH, for every `N ≥ 1`, every real `x` on `[1, N]` and every `T ≥ e²⁴N`,
`Σ_{|γ_ρ| ≤ T} |Σ_{n ≤ N} x_n n^ρ|² ≥ (T/100)·Σ_{n ≤ N} x_n² n`: the conjecture of `formalisations/ball-rate.md`,
`BallRate.SamplingAtZeros c C 0`, holds with `c = 1/100` and `C = e²⁴`. Then `BallRate.rate_of_sampling` gives
`λ_N ≥ 1/(200e²⁴N)`.

The proof tests Weil's explicit formula against `|D(t)|²Φ(t/T)` with the minorant
`Φ(y) = y²(1 − y²)sinc⁶(by)` of `¼·1_{[−1,1]}`, `b = 6`. It vanishes to second order at `0`, which makes the pole term
`O(NΣc_n²)` and the low-height mass of `|D|²` in the archimedean term `O(TΣc_n²)`. Its Fourier transform is supported
in `|v| ≤ 6b/T < 1/(2N)`, which makes the diagonal and the prime side exact: only the exact matches `j' = jn` survive
(Landau's form). On `|t| > T`, where `Φ < 0`, the archimedean weight grows like `log|t|`; it is paid for with Fejér
majorants `M_r(t) = (r/t)²sin²(πt/2r)` of `|D|²` on dyadic shells, whose masses `≍ 2^i TΣc_n²` are summable against
the shell weights `≍ i·4^{−i}`.
-/

open Real Complex Finset MeasureTheory WeilForm WeilTest DirMean BallDensity ShortWeil
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace BallCutoff

/-! ## The box and its autocorrelations -/

lemma bx_mul_bx (β t u : ℝ) :
    bx β t * bx β (t + u) = (Set.Icc (-β) β ∩ Set.Icc (-β - u) (β - u)).indicator 1 t := by
  have e : t ∈ Set.Icc (-β) β ∩ Set.Icc (-β - u) (β - u) ↔ |t| ≤ β ∧ |t + u| ≤ β := by
    simp only [Set.mem_inter_iff, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
  rw [bx_apply, bx_apply, Set.indicator_apply]
  by_cases h : |t| ≤ β ∧ |t + u| ≤ β
  · simp [h.1, h.2, e.2 h]
  · have hm : t ∉ Set.Icc (-β) β ∩ Set.Icc (-β - u) (β - u) := fun hm => h (e.1 hm)
    by_cases h1 : |t| ≤ β
    · have h2 : ¬ |t + u| ≤ β := fun h2 => h ⟨h1, h2⟩
      simp [h1, h2, hm]
    · simp [h1, hm]

/-- **The triangle**: `autocorr 1_{[−β,β]} (u) = (2β − |u|)⁺`. -/
lemma autocorr_bx (β u : ℝ) : autocorr (bx β) u = max (2 * β - |u|) 0 := by
  unfold autocorr
  simp_rw [bx_mul_bx β _ u]
  rw [integral_indicator_one (measurableSet_Icc.inter measurableSet_Icc), Set.Icc_inter_Icc,
    measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal']
  congr 1
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu, max_eq_left (by linarith : -β - u ≤ -β), min_eq_right (by linarith : β - u ≤ β)]
    ring
  · rw [abs_of_nonpos hu, max_eq_right (by linarith : -β ≤ -β - u), min_eq_left (by linarith : β ≤ β - u)]
    ring

lemma gI_one_eq (β t : ℝ) : gI β 1 t = max (2 * β - |t|) 0 := autocorr_bx β t

/-- The integrand of `autocorr (gI β 1)` vanishes off `[−2β, 2β]`. -/
lemma gI_one_mul_eq_zero {β t : ℝ} (u : ℝ) (ht : t ∉ Set.Icc (-(2 * β)) (2 * β)) :
    gI β 1 t * gI β 1 (t + u) = 0 := by
  have h : 2 * β < |t| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · linarith [neg_le_abs t]
    · linarith [le_abs_self t]
  rw [gI_one_eq, max_eq_right (by linarith), zero_mul]

lemma integral_gI_one_mul {β : ℝ} (hβ : 0 < β) (u : ℝ) :
    autocorr (gI β 1) u = ∫ t in (-(2 * β))..(2 * β), gI β 1 t * gI β 1 (t + u) := by
  unfold autocorr
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => gI_one_mul_eq_zero u ht]

lemma continuous_gI_one (β : ℝ) : Continuous (gI β 1) := by
  have e : gI β 1 = fun t => max (2 * β - |t|) 0 := funext (gI_one_eq β)
  rw [e]; fun_prop

lemma integral_poly_left {β : ℝ} (f F : ℝ → ℝ) (hF : ∀ t, HasDerivAt F (f t) t) (hf : Continuous f) :
    ∫ t in (-(2 * β))..0, f t = F 0 - F (-(2 * β)) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (hf.intervalIntegrable _ _)

lemma integral_poly_right {β : ℝ} (f F : ℝ → ℝ) (hF : ∀ t, HasDerivAt F (f t) t) (hf : Continuous f) :
    ∫ t in (0 : ℝ)..(2 * β), f t = F (2 * β) - F 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (hf.intervalIntegrable _ _)

/-- `autocorr g₁(0) = ∫(2β − |t|)₊² = 16β³/3`. -/
lemma autocorr_gI_one_zero {β : ℝ} (hβ : 0 < β) : autocorr (gI β 1) 0 = 16 * β ^ 3 / 3 := by
  have hc : Continuous fun t => gI β 1 t * gI β 1 (t + 0) :=
    (continuous_gI_one β).mul ((continuous_gI_one β).comp (by fun_prop))
  rw [integral_gI_one_mul hβ, ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ t in (-(2 * β))..0, gI β 1 t * gI β 1 (t + 0) = ∫ t in (-(2 * β))..0, (2 * β + t) ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [add_zero, gI_one_eq]
    rw [abs_of_nonpos ht.2, max_eq_left (by linarith [ht.1])]
    ring
  have e2 : ∫ t in (0 : ℝ)..(2 * β), gI β 1 t * gI β 1 (t + 0) = ∫ t in (0 : ℝ)..(2 * β), (2 * β - t) ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [add_zero, gI_one_eq]
    rw [abs_of_nonneg ht.1, max_eq_left (by linarith [ht.2])]
    ring
  rw [e1, e2, integral_poly_left (fun t => (2 * β + t) ^ 2) (fun t => (2 * β + t) ^ 3 / 3)
    (fun t => by
      have h := ((hasDerivAt_id' t).const_add (2 * β)).pow 3
      convert h.div_const 3 using 1; norm_num) (by fun_prop),
    integral_poly_right (fun t => (2 * β - t) ^ 2) (fun t => -(2 * β - t) ^ 3 / 3)
    (fun t => by
      have h := (((hasDerivAt_id' t).const_sub (2 * β)).pow 3).neg
      convert h.div_const 3 using 1; norm_num) (by fun_prop)]
  ring

/-- `autocorr g₁(2β) = ∫_{−2β}^{0}(2β + t)(−t) dt = 4β³/3`. -/
lemma autocorr_gI_one_two {β : ℝ} (hβ : 0 < β) : autocorr (gI β 1) (2 * β) = 4 * β ^ 3 / 3 := by
  have hc : Continuous fun t => gI β 1 t * gI β 1 (t + 2 * β) :=
    (continuous_gI_one β).mul ((continuous_gI_one β).comp (by fun_prop))
  rw [integral_gI_one_mul hβ, ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ t in (-(2 * β))..0, gI β 1 t * gI β 1 (t + 2 * β) =
      ∫ t in (-(2 * β))..0, (2 * β + t) * (-t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [gI_one_eq]
    rw [abs_of_nonpos ht.2, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t + 2 * β),
      max_eq_left (by linarith [ht.1]), max_eq_left (by linarith [ht.2])]
    ring
  have e2 : ∫ t in (0 : ℝ)..(2 * β), gI β 1 t * gI β 1 (t + 2 * β) = ∫ t in (0 : ℝ)..(2 * β), (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [gI_one_eq]
    rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t + 2 * β), max_eq_right (by linarith [ht.1] : 2 * β - (t + 2 * β) ≤ 0),
      mul_zero]
  rw [e1, e2, intervalIntegral.integral_zero, add_zero,
    integral_poly_left (fun t => (2 * β + t) * (-t)) (fun t => -(β * t ^ 2) - t ^ 3 / 3)
    (fun t => by
      have h1 := ((hasDerivAt_pow 2 t).const_mul β).neg
      have h2 := (hasDerivAt_pow 3 t).div_const 3
      convert h1.sub h2 using 1; simp; ring) (by fun_prop)]
  ring

/-- The triangle's values at the shifts used below. -/
lemma autocorr_bx_zero (β : ℝ) (hβ : 0 ≤ β) : autocorr (bx β) 0 = 2 * β := by
  rw [autocorr_bx, abs_zero, sub_zero, max_eq_left (by linarith)]

lemma autocorr_bx_eq_zero {β u : ℝ} (hu : 2 * β ≤ |u|) : autocorr (bx β) u = 0 := by
  rw [autocorr_bx, max_eq_right (by linarith)]

lemma autocorr_gI_one_eq_zero {β u : ℝ} (hβ : 0 < β) (hu : 4 * β < |u|) : autocorr (gI β 1) u = 0 := by
  have h := (gI_esupp hβ 2).supp u (by rw [show (2 : ℝ) ^ 2 * β = 4 * β by norm_num]; exact hu)
  exact h

/-! ## The transform of the box -/

/-- `ĝ_box(z) = 2 sin(βz)/z` for `z ≠ 0`. -/
lemma ghatC_bx_eq {β : ℝ} (hβ : 0 ≤ β) {z : ℂ} (hz : z ≠ 0) :
    ghatC (bx β) β z = 2 * Complex.sin (β * z) / z := by
  rw [ghatC_bx β hβ]
  have hc : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  rw [integral_exp_mul_complex hc, Complex.sin,
    show Complex.I * z * (β : ℂ) = (β : ℂ) * z * Complex.I by ring,
    show Complex.I * z * ((-β : ℝ) : ℂ) = -((β : ℂ) * z) * Complex.I by push_cast; ring]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma gH_bx_eq {β : ℝ} (hβ : 0 ≤ β) {r : ℝ} (hr : r ≠ 0) : gH (bx β) β r = 2 * Real.sin (β * r) / r := by
  unfold gH
  rw [ghatC_bx_eq hβ (by exact_mod_cast hr : (r : ℂ) ≠ 0),
    show (2 : ℂ) * Complex.sin ((β : ℂ) * (r : ℂ)) / (r : ℂ) = ((2 * Real.sin (β * r) / r : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]

lemma hsq_bx_eq {β : ℝ} (hβ : 0 ≤ β) {r : ℝ} (hr : r ≠ 0) :
    hsq (bx β) β r = 4 * Real.sin (β * r) ^ 2 / r ^ 2 := by
  unfold hsq; rw [gH_bx_eq hβ hr]; field_simp; ring

lemma esupp_gI_one {β : ℝ} (hβ : 0 < β) : ESupp (2 * β) (gI β 1) := by
  have h := gI_esupp hβ 1
  rwa [pow_one] at h

/-- `ĝ₁ = ĝ₀²` on the real line, so `hsq g₁ = (hsq g₀)²`. -/
lemma hsq_gI_one {β : ℝ} (hβ : 0 < β) (r : ℝ) : hsq (gI β 1) (2 * β) r = hsq (bx β) β r ^ 2 := by
  have h := ghatC_gI hβ (r : ℂ) 1
  rw [pow_one, pow_one] at h
  have h0 := ghatC_real (esupp_bx β) hβ.le r
  have h1 := ghatC_real (esupp_gI_one hβ) (by positivity) r
  rw [h0, h1] at h
  have h2 : gH (gI β 1) (2 * β) r = gH (bx β) β r ^ 2 := by exact_mod_cast h
  unfold hsq; rw [h2]

/-! ## The minorant

`Φ(r) = (r/T)²(1 − (r/T)²)·sinc⁶(βr)` with `β = b/T`, built from the box: `(1 − cos 2βr)ĝ₁(r)²/(32b²β⁴)
− (3 − 4cos 2βr + cos 4βr)ĝ₀(r)²/(32b⁴β²)`. -/

/-- The minorant of `¼·1_{[−T,T]}`. -/
def phiR (b T r : ℝ) : ℝ :=
  (1 - Real.cos (2 * (b / T) * r)) * hsq (gI (b / T) 1) (2 * (b / T)) r / (32 * b ^ 2 * (b / T) ^ 4)
    - (3 - 4 * Real.cos (2 * (b / T) * r) + Real.cos (4 * (b / T) * r)) * hsq (bx (b / T)) (b / T) r
      / (32 * b ^ 4 * (b / T) ^ 2)

lemma one_sub_cos_two (θ : ℝ) : 1 - Real.cos (2 * θ) = 2 * Real.sin θ ^ 2 := by
  rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq θ]

lemma three_sub_cos (θ : ℝ) :
    3 - 4 * Real.cos (2 * θ) + Real.cos (4 * θ) = 8 * Real.sin θ ^ 4 := by
  rw [show 4 * θ = 2 * (2 * θ) by ring, Real.cos_two_mul (2 * θ), Real.cos_two_mul θ]
  have := Real.sin_sq_add_cos_sq θ
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith
  rw [show (2 * Real.cos θ ^ 2 - 1) ^ 2 = (2 * Real.cos θ ^ 2 - 1) * (2 * Real.cos θ ^ 2 - 1) by ring, hc]
  ring

/-- **The closed form**: `Φ(r) = sin⁶θ/(b²θ⁴)·(1 − θ²/b²)`, `θ = βr`, for `r ≠ 0`. -/
lemma phiR_eq {b T : ℝ} (hb : 0 < b) (hT : 0 < T) {r : ℝ} (hr : r ≠ 0) :
    phiR b T r = Real.sin (b / T * r) ^ 6 / (b ^ 2 * (b / T * r) ^ 4) * (1 - (b / T * r) ^ 2 / b ^ 2) := by
  have hβ : 0 < b / T := div_pos hb hT
  unfold phiR
  rw [hsq_gI_one hβ, hsq_bx_eq hβ.le hr, show 2 * (b / T) * r = 2 * (b / T * r) by ring,
    show 4 * (b / T) * r = 4 * (b / T * r) by ring, one_sub_cos_two, three_sub_cos]
  have hθ : b / T * r ≠ 0 := mul_ne_zero hβ.ne' hr
  field_simp
  ring

lemma phiR_zero (b T : ℝ) : phiR b T 0 = 0 := by
  unfold phiR; simp only [mul_zero, Real.cos_zero]; ring

lemma sin_pow_six_le (θ : ℝ) : Real.sin θ ^ 6 ≤ θ ^ 6 := by
  have h : Real.sin θ ^ 2 ≤ θ ^ 2 := by
    rw [← sq_abs (Real.sin θ), ← sq_abs θ]
    exact pow_le_pow_left₀ (abs_nonneg _) Real.abs_sin_le_abs 2
  have h0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  calc Real.sin θ ^ 6 = (Real.sin θ ^ 2) ^ 3 := by ring
    _ ≤ (θ ^ 2) ^ 3 := pow_le_pow_left₀ h0 h 3
    _ = θ ^ 6 := by ring

/-- On `|r| ≤ T`: `0 ≤ Φ(r) ≤ (r/T)²(1 − (r/T)²) ≤ min((r/T)², ¼)`. -/
lemma phiR_bounds {b T : ℝ} (hb : 0 < b) (hT : 0 < T) {r : ℝ} (hr : |r| ≤ T) :
    0 ≤ phiR b T r ∧ phiR b T r ≤ (r / T) ^ 2 ∧ phiR b T r ≤ 1 / 4 := by
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [phiR_zero]; norm_num
  have hβ : 0 < b / T := div_pos hb hT
  set θ := b / T * r with hθ
  have hθ0 : θ ≠ 0 := mul_ne_zero hβ.ne' hr0
  have hy : θ / b = r / T := by rw [hθ]; field_simp
  have hy1 : (θ / b) ^ 2 ≤ 1 := by
    rw [hy, div_pow, div_le_one (by positivity), ← sq_abs r]
    exact pow_le_pow_left₀ (abs_nonneg r) hr 2
  rw [phiR_eq hb hT hr0, ← hθ]
  have hs := sin_pow_six_le θ
  have hs0 : 0 ≤ Real.sin θ ^ 6 := by positivity
  have hpos : 0 < b ^ 2 * θ ^ 4 := by positivity
  have h1 : 0 ≤ 1 - θ ^ 2 / b ^ 2 := by rw [← div_pow]; linarith
  have hq : Real.sin θ ^ 6 / (b ^ 2 * θ ^ 4) ≤ (θ / b) ^ 2 := by
    rw [div_le_iff₀ hpos]
    calc Real.sin θ ^ 6 ≤ θ ^ 6 := hs
      _ = (θ / b) ^ 2 * (b ^ 2 * θ ^ 4) := by field_simp
  have hq0 : 0 ≤ Real.sin θ ^ 6 / (b ^ 2 * θ ^ 4) := div_nonneg hs0 hpos.le
  have e2 : θ ^ 2 / b ^ 2 = (θ / b) ^ 2 := by rw [div_pow]
  refine ⟨mul_nonneg hq0 h1, ?_, ?_⟩
  · calc Real.sin θ ^ 6 / (b ^ 2 * θ ^ 4) * (1 - θ ^ 2 / b ^ 2) ≤ (θ / b) ^ 2 * 1 :=
          mul_le_mul hq (by linarith [div_nonneg (sq_nonneg θ) (sq_nonneg b)]) h1 (sq_nonneg _)
      _ = (r / T) ^ 2 := by rw [mul_one, hy]
  · calc Real.sin θ ^ 6 / (b ^ 2 * θ ^ 4) * (1 - θ ^ 2 / b ^ 2) ≤ (θ / b) ^ 2 * (1 - (θ / b) ^ 2) := by
          rw [e2]; exact mul_le_mul_of_nonneg_right hq (by rw [← e2]; exact h1)
      _ ≤ 1 / 4 := by nlinarith [sq_nonneg ((θ / b) ^ 2 - 1 / 2)]

/-- On `|r| ≥ T`: `Φ(r) ≤ 0` and `|Φ(r)| ≤ T²/(b⁶r²)`. -/
lemma phiR_tail {b T : ℝ} (hb : 0 < b) (hT : 0 < T) {r : ℝ} (hr : T ≤ |r|) :
    phiR b T r ≤ 0 ∧ |phiR b T r| ≤ T ^ 2 / (b ^ 6 * r ^ 2) := by
  have hr0 : r ≠ 0 := by intro h; rw [h, abs_zero] at hr; linarith
  have hβ : 0 < b / T := div_pos hb hT
  set θ := b / T * r with hθ
  have hθ0 : θ ≠ 0 := mul_ne_zero hβ.ne' hr0
  have hy : θ / b = r / T := by rw [hθ]; field_simp
  have hy1 : 1 ≤ (θ / b) ^ 2 := by
    rw [hy, div_pow, one_le_div (by positivity), ← sq_abs r]
    exact pow_le_pow_left₀ hT.le hr 2
  rw [phiR_eq hb hT hr0, ← hθ]
  have hs0 : 0 ≤ Real.sin θ ^ 6 := by positivity
  have hpos : 0 < b ^ 2 * θ ^ 4 := by positivity
  have e2 : θ ^ 2 / b ^ 2 = (θ / b) ^ 2 := by rw [div_pow]
  have h1 : 1 - θ ^ 2 / b ^ 2 ≤ 0 := by rw [e2]; linarith
  have hq0 : 0 ≤ Real.sin θ ^ 6 / (b ^ 2 * θ ^ 4) := div_nonneg hs0 hpos.le
  refine ⟨mul_nonpos_of_nonneg_of_nonpos hq0 h1, ?_⟩
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hq0 h1)]
  have hsin : Real.sin θ ^ 6 ≤ 1 := by
    have h := Real.sin_sq_le_one θ
    calc Real.sin θ ^ 6 = (Real.sin θ ^ 2) ^ 3 := by ring
      _ ≤ 1 := pow_le_one₀ (sq_nonneg _) h
  have key : -(Real.sin θ ^ 6 / (b ^ 2 * θ ^ 4) * (1 - θ ^ 2 / b ^ 2)) ≤ Real.sin θ ^ 6 / (b ^ 4 * θ ^ 2) := by
    have : -(Real.sin θ ^ 6 / (b ^ 2 * θ ^ 4) * (1 - θ ^ 2 / b ^ 2)) =
        Real.sin θ ^ 6 / (b ^ 4 * θ ^ 2) - Real.sin θ ^ 6 / (b ^ 2 * θ ^ 4) := by field_simp; ring
    rw [this]; linarith
  refine key.trans ?_
  have hθr : θ ^ 2 = b ^ 2 * r ^ 2 / T ^ 2 := by rw [hθ]; field_simp
  calc Real.sin θ ^ 6 / (b ^ 4 * θ ^ 2) ≤ 1 / (b ^ 4 * θ ^ 2) :=
        div_le_div_of_nonneg_right hsin (by positivity)
    _ = T ^ 2 / (b ^ 6 * r ^ 2) := by rw [hθr]; field_simp

/-! ## The cosine transform of the minorant -/

lemma integral_hsq_sum {a : ℝ} {g : ℝ → ℝ} (hp : ESupp a g) (ha : 0 < a) {n : ℕ} (p u : Fin n → ℝ) :
    ∫ r, hsq g a r * ∑ k, p k * Real.cos (r * u k) = 2 * π * ∑ k, p k * autocorr g (u k) := by
  have hi : ∀ k ∈ (Finset.univ : Finset (Fin n)), Integrable (fun r => hsq g a r * (p k * Real.cos (r * u k))) :=
    fun k _ => ((integrable_hsq_cos hp ha (u k)).const_mul (p k)).congr
      (Filter.Eventually.of_forall fun r => by ring)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (fun r => hsq g a r * (p k * Real.cos (r * u k))) = fun r => p k * (hsq g a r * Real.cos (r * u k)) by
    funext r; ring, integral_const_mul, integral_hsq_cos hp ha]
  ring

/-- The cosine transform `Φ̂(v) = ∫Φ(r)cos(rv) dr`, from the autocorrelations of the box. -/
def phihat (b T v : ℝ) : ℝ :=
  2 * π / (32 * b ^ 2 * (b / T) ^ 4) * (autocorr (gI (b / T) 1) v - autocorr (gI (b / T) 1) (v + 2 * (b / T)) / 2
      - autocorr (gI (b / T) 1) (v - 2 * (b / T)) / 2)
    - 2 * π / (32 * b ^ 4 * (b / T) ^ 2) * (3 * autocorr (bx (b / T)) v - 2 * autocorr (bx (b / T)) (v + 2 * (b / T))
      - 2 * autocorr (bx (b / T)) (v - 2 * (b / T)) + autocorr (bx (b / T)) (v + 4 * (b / T)) / 2
      + autocorr (bx (b / T)) (v - 4 * (b / T)) / 2)

lemma phiR_mul_cos (b T v r : ℝ) :
    phiR b T r * Real.cos (r * v) =
      1 / (32 * b ^ 2 * (b / T) ^ 4) * (hsq (gI (b / T) 1) (2 * (b / T)) r *
        ∑ k, ![1, -1 / 2, -1 / 2] k * Real.cos (r * ![v, v + 2 * (b / T), v - 2 * (b / T)] k))
      - 1 / (32 * b ^ 4 * (b / T) ^ 2) * (hsq (bx (b / T)) (b / T) r *
        ∑ k, ![3, -2, -2, 1 / 2, 1 / 2] k * Real.cos (r * ![v, v + 2 * (b / T), v - 2 * (b / T),
          v + 4 * (b / T), v - 4 * (b / T)] k)) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  unfold phiR
  rw [show r * (v + 2 * (b / T)) = r * v + 2 * (b / T) * r by ring,
    show r * (v - 2 * (b / T)) = r * v - 2 * (b / T) * r by ring,
    show r * (v + 4 * (b / T)) = r * v + 4 * (b / T) * r by ring,
    show r * (v - 4 * (b / T)) = r * v - 4 * (b / T) * r by ring]
  simp only [Real.cos_add, Real.cos_sub]
  ring

/-- **The transform**: `∫Φ(r)cos(rv) dr = Φ̂(v)`. -/
lemma integral_phiR_cos {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (v : ℝ) :
    ∫ r, phiR b T r * Real.cos (r * v) = phihat b T v := by
  have hβ : 0 < b / T := div_pos hb hT
  have h1 := integral_hsq_sum (esupp_gI_one hβ) (by positivity) ![1, -1 / 2, -1 / 2]
    ![v, v + 2 * (b / T), v - 2 * (b / T)]
  have h0 := integral_hsq_sum (esupp_bx (b / T)) hβ ![3, -2, -2, 1 / 2, 1 / 2]
    ![v, v + 2 * (b / T), v - 2 * (b / T), v + 4 * (b / T), v - 4 * (b / T)]
  have i1 : Integrable fun r => hsq (gI (b / T) 1) (2 * (b / T)) r *
      ∑ k, ![1, -1 / 2, -1 / 2] k * Real.cos (r * ![v, v + 2 * (b / T), v - 2 * (b / T)] k) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun k _ => ((integrable_hsq_cos (esupp_gI_one hβ) (by positivity) _).const_mul
      _).congr (Filter.Eventually.of_forall fun r => by ring)
  have i0 : Integrable fun r => hsq (bx (b / T)) (b / T) r *
      ∑ k, ![3, -2, -2, 1 / 2, 1 / 2] k * Real.cos (r * ![v, v + 2 * (b / T), v - 2 * (b / T),
        v + 4 * (b / T), v - 4 * (b / T)] k) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun k _ => ((integrable_hsq_cos (esupp_bx (b / T)) hβ _).const_mul
      _).congr (Filter.Eventually.of_forall fun r => by ring)
  simp_rw [phiR_mul_cos b T v]
  rw [integral_sub (i1.const_mul _) (i0.const_mul _), integral_const_mul, integral_const_mul, h1, h0]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  unfold phihat
  ring

lemma integrable_phiR_cos {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (v : ℝ) :
    Integrable fun r => phiR b T r * Real.cos (r * v) := by
  have hβ : 0 < b / T := div_pos hb hT
  have i1 : Integrable fun r => hsq (gI (b / T) 1) (2 * (b / T)) r *
      ∑ k, ![1, -1 / 2, -1 / 2] k * Real.cos (r * ![v, v + 2 * (b / T), v - 2 * (b / T)] k) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun k _ => ((integrable_hsq_cos (esupp_gI_one hβ) (by positivity) _).const_mul
      _).congr (Filter.Eventually.of_forall fun r => by ring)
  have i0 : Integrable fun r => hsq (bx (b / T)) (b / T) r *
      ∑ k, ![3, -2, -2, 1 / 2, 1 / 2] k * Real.cos (r * ![v, v + 2 * (b / T), v - 2 * (b / T),
        v + 4 * (b / T), v - 4 * (b / T)] k) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun k _ => ((integrable_hsq_cos (esupp_bx (b / T)) hβ _).const_mul
      _).congr (Filter.Eventually.of_forall fun r => by ring)
  exact ((i1.const_mul _).sub (i0.const_mul _)).congr
    (Filter.Eventually.of_forall fun r => (phiR_mul_cos b T v r).symm)

/-- **Compact support**: `Φ̂(v) = 0` for `|v| > 6β`. -/
lemma phihat_eq_zero {b T : ℝ} (hb : 0 < b) (hT : 0 < T) {v : ℝ} (hv : 6 * (b / T) < |v|) :
    phihat b T v = 0 := by
  have hβ : 0 < b / T := div_pos hb hT
  set β := b / T with hβdef
  have g1 : ∀ c : ℝ, 0 < c → |v| ≤ |v + c| + c := fun c hc => by
    have := abs_add_le (v + c) (-c); rw [show v + c + -c = v by ring, abs_neg, abs_of_pos hc] at this
    exact this
  have g2 : ∀ c : ℝ, 0 < c → |v| ≤ |v - c| + c := fun c hc => by
    have := abs_add_le (v - c) c; rw [show v - c + c = v by ring, abs_of_pos hc] at this
    exact this
  unfold phihat
  rw [autocorr_gI_one_eq_zero hβ (by linarith), autocorr_gI_one_eq_zero hβ (by linarith [g1 (2 * β) (by linarith)]),
    autocorr_gI_one_eq_zero hβ (by linarith [g2 (2 * β) (by linarith)]),
    autocorr_bx_eq_zero (by linarith), autocorr_bx_eq_zero (by linarith [g1 (2 * β) (by linarith)]),
    autocorr_bx_eq_zero (by linarith [g2 (2 * β) (by linarith)]),
    autocorr_bx_eq_zero (by linarith [g1 (4 * β) (by linarith)]),
    autocorr_bx_eq_zero (by linarith [g2 (4 * β) (by linarith)])]
  ring

/-- **The mass**: `Φ̂(0) = πT(2b² − 3)/(8b⁵)`. -/
lemma phihat_zero {b T : ℝ} (hb : 0 < b) (hT : 0 < T) : phihat b T 0 = π * T * (2 * b ^ 2 - 3) / (8 * b ^ 5) := by
  have hβ : 0 < b / T := div_pos hb hT
  unfold phihat
  rw [zero_add, zero_sub, zero_add, zero_sub, autocorr_neg, autocorr_neg, autocorr_neg, autocorr_gI_one_zero hβ,
    autocorr_gI_one_two hβ, autocorr_bx_zero _ hβ.le,
    autocorr_bx_eq_zero (by rw [abs_of_pos (by positivity : 0 < 2 * (b / T))]),
    autocorr_bx_eq_zero (by rw [abs_of_pos (by positivity : 0 < 4 * (b / T))]; linarith)]
  field_simp
  ring

lemma phihat_neg (b T v : ℝ) : phihat b T (-v) = phihat b T v := by
  have e1 : ∀ (g : ℝ → ℝ) (c : ℝ), autocorr g (-v + c) = autocorr g (v - c) := fun g c => by
    rw [← autocorr_neg g (v - c), neg_sub, sub_eq_neg_add]
  have e2 : ∀ (g : ℝ → ℝ) (c : ℝ), autocorr g (-v - c) = autocorr g (v + c) := fun g c => by
    rw [← autocorr_neg g (v + c), neg_add, sub_eq_add_neg]
  unfold phihat
  rw [e1, e2, e1, e2, e1, e2, autocorr_neg, autocorr_neg]
  ring

/-! ## The minorant on `ℂ` -/

/-- The entire extension of `Φ`. -/
def phiC (b T : ℝ) (z : ℂ) : ℂ :=
  (1 - Complex.cos (2 * ((b / T : ℝ) : ℂ) * z)) * ghatC (gI (b / T) 1) (2 * (b / T)) z ^ 2
      / ((32 * b ^ 2 * (b / T) ^ 4 : ℝ) : ℂ)
    - (3 - 4 * Complex.cos (2 * ((b / T : ℝ) : ℂ) * z) + Complex.cos (4 * ((b / T : ℝ) : ℂ) * z))
      * ghatC (bx (b / T)) (b / T) z ^ 2 / ((32 * b ^ 4 * (b / T) ^ 2 : ℝ) : ℂ)

lemma phiC_ofReal {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (r : ℝ) : phiC b T r = (phiR b T r : ℂ) := by
  have hβ : 0 < b / T := div_pos hb hT
  unfold phiC phiR hsq
  rw [ghatC_real (esupp_gI_one hβ) (by positivity) r, ghatC_real (esupp_bx (b / T)) hβ.le r]
  push_cast
  ring

lemma phiC_even (b T : ℝ) (hb : 0 < b) (hT : 0 < T) (z : ℂ) : phiC b T (-z) = phiC b T z := by
  have hβ : 0 < b / T := div_pos hb hT
  unfold phiC
  rw [ghatC_even (esupp_gI_one hβ).even, ghatC_even (esupp_bx (b / T)).even, mul_neg, mul_neg, Complex.cos_neg,
    Complex.cos_neg]

lemma differentiable_phiC {b T : ℝ} (hb : 0 < b) (hT : 0 < T) : Differentiable ℂ (phiC b T) := by
  have hβ : 0 < b / T := div_pos hb hT
  have d1 : Differentiable ℂ (ghatC (gI (b / T) 1) (2 * (b / T))) :=
    ghatC_differentiable (esupp_gI_one hβ).integrable.intervalIntegrable
  have d0 : Differentiable ℂ (ghatC (bx (b / T)) (b / T)) :=
    ghatC_differentiable (esupp_bx (b / T)).integrable.intervalIntegrable
  unfold phiC
  fun_prop

lemma norm_cos_strip {l : ℝ} (hl : 0 ≤ l) {z : ℂ} (hz : z ∈ WeilStrip.strip (-1) 1) :
    ‖Complex.cos (l * z)‖ ≤ Real.exp l := by
  have h := norm_two_cos_strip hl hz
  rw [norm_mul, Complex.norm_two] at h
  linarith

/-- **The strip bound**: `‖Φ(z)‖ ≤ K/(1 + (Re z)²)` on `|Im z| ≤ 1`, for `b ≤ T`. -/
lemma norm_phiC_le {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (hbT : b ≤ T) {z : ℂ} (hz : z ∈ WeilStrip.strip (-1) 1) :
    ‖phiC b T z‖ ≤ ((1 + Real.exp (2 * (b / T))) * (4 * (b / T) * Real.exp (b / T)) ^ 4 / (32 * b ^ 2 * (b / T) ^ 4)
      + (3 + 4 * Real.exp (2 * (b / T)) + Real.exp (4 * (b / T))) * (4 * (b / T) * Real.exp (b / T)) ^ 2
        / (32 * b ^ 4 * (b / T) ^ 2)) / (b / T) ^ 2 / (1 + z.re ^ 2) := by
  have hβ : 0 < b / T := div_pos hb hT
  have hβ1 : b / T ≤ 1 := (div_le_one hT).2 hbT
  set β := b / T with hβdef
  have him : |z.im| ≤ 1 := abs_le.2 ⟨hz.1, hz.2⟩
  set q := 1 + β * ‖z‖ with hq
  have hq1 : 1 ≤ q := by have := norm_nonneg z; nlinarith
  set G := 4 * β * Real.exp β with hG
  have hG0 : 0 ≤ G := by positivity
  have hg0 : ‖ghatC (bx β) β z‖ ≤ G / q := by
    refine (norm_ghatC_bx_le' β hβ.le z).trans ?_
    rw [hG]
    gcongr
    nlinarith
  have hg1 : ghatC (gI β 1) (2 * β) z = ghatC (bx β) β z ^ 2 := by
    have h := ghatC_gI hβ z 1; rwa [pow_one, pow_one] at h
  have hc2 : ‖Complex.cos (2 * (β : ℂ) * z)‖ ≤ Real.exp (2 * β) := by
    have := norm_cos_strip (l := 2 * β) (by positivity) hz; push_cast at this; exact this
  have hc4 : ‖Complex.cos (4 * (β : ℂ) * z)‖ ≤ Real.exp (4 * β) := by
    have := norm_cos_strip (l := 4 * β) (by positivity) hz; push_cast at this; exact this
  have hn1 : ‖1 - Complex.cos (2 * (β : ℂ) * z)‖ ≤ 1 + Real.exp (2 * β) :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hn3 : ‖3 - 4 * Complex.cos (2 * (β : ℂ) * z) + Complex.cos (4 * (β : ℂ) * z)‖ ≤
      3 + 4 * Real.exp (2 * β) + Real.exp (4 * β) := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) hc4)
    rw [norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num, show ‖(4 : ℂ)‖ = 4 by norm_num]
    linarith
  have hK1 : (0 : ℝ) < 32 * b ^ 2 * β ^ 4 := by positivity
  have hK2 : (0 : ℝ) < 32 * b ^ 4 * β ^ 2 := by positivity
  have hgq : ‖ghatC (bx β) β z‖ ^ 2 ≤ G ^ 2 / q ^ 2 := by
    rw [← div_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hg0 2
  have hgq4 : ‖ghatC (bx β) β z‖ ^ 4 ≤ G ^ 4 / q ^ 2 := by
    calc ‖ghatC (bx β) β z‖ ^ 4 ≤ (G / q) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hg0 4
      _ = G ^ 4 / q ^ 4 := by rw [div_pow]
      _ ≤ G ^ 4 / q ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_right₀ hq1 (by norm_num))
  have hre : β ^ 2 * (1 + z.re ^ 2) ≤ q ^ 2 := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h2 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hb2 : β ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm_nonneg z, mul_nonneg hβ.le (norm_nonneg z)]
  unfold phiC
  rw [← hβdef, hg1]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hK1.le, Real.norm_of_nonneg hK2.le]
  have hpos : 0 < 1 + z.re ^ 2 := by positivity
  have e1 : (1 + Real.exp (2 * β)) * G ^ 4 / (32 * b ^ 2 * β ^ 4) / β ^ 2 / (1 + z.re ^ 2) ≥
      (1 + Real.exp (2 * β)) * (G ^ 4 / q ^ 2) / (32 * b ^ 2 * β ^ 4) := by
    rw [ge_iff_le, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (1 + Real.exp (2 * β)) * G ^ 4 := by positivity
    calc (1 + Real.exp (2 * β)) * (G ^ 4 / q ^ 2) * (32 * b ^ 2 * β ^ 4 * (β ^ 2 * (1 + z.re ^ 2)))
        = (1 + Real.exp (2 * β)) * G ^ 4 * (32 * b ^ 2 * β ^ 4) * (β ^ 2 * (1 + z.re ^ 2) / q ^ 2) := by
          field_simp
      _ ≤ (1 + Real.exp (2 * β)) * G ^ 4 * (32 * b ^ 2 * β ^ 4) * 1 := by
          gcongr; rw [div_le_one (by positivity)]; exact hre
      _ = _ := by ring
  have e2 : (3 + 4 * Real.exp (2 * β) + Real.exp (4 * β)) * G ^ 2 / (32 * b ^ 4 * β ^ 2) / β ^ 2 / (1 + z.re ^ 2) ≥
      (3 + 4 * Real.exp (2 * β) + Real.exp (4 * β)) * (G ^ 2 / q ^ 2) / (32 * b ^ 4 * β ^ 2) := by
    rw [ge_iff_le, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (3 + 4 * Real.exp (2 * β) + Real.exp (4 * β)) * (G ^ 2 / q ^ 2) * (32 * b ^ 4 * β ^ 2 * (β ^ 2 * (1 + z.re ^ 2)))
        = (3 + 4 * Real.exp (2 * β) + Real.exp (4 * β)) * G ^ 2 * (32 * b ^ 4 * β ^ 2) *
            (β ^ 2 * (1 + z.re ^ 2) / q ^ 2) := by field_simp
      _ ≤ (3 + 4 * Real.exp (2 * β) + Real.exp (4 * β)) * G ^ 2 * (32 * b ^ 4 * β ^ 2) * 1 := by
          gcongr; rw [div_le_one (by positivity)]; exact hre
      _ = _ := by ring
  have t1 : ‖1 - Complex.cos (2 * (β : ℂ) * z)‖ * (‖ghatC (bx β) β z‖ ^ 2) ^ 2 / (32 * b ^ 2 * β ^ 4) ≤
      (1 + Real.exp (2 * β)) * (G ^ 4 / q ^ 2) / (32 * b ^ 2 * β ^ 4) := by
    rw [← pow_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul hn1 hgq4 (by positivity) (by positivity)) hK1.le
  have t2 : ‖3 - 4 * Complex.cos (2 * (β : ℂ) * z) + Complex.cos (4 * (β : ℂ) * z)‖ * ‖ghatC (bx β) β z‖ ^ 2
      / (32 * b ^ 4 * β ^ 2) ≤ (3 + 4 * Real.exp (2 * β) + Real.exp (4 * β)) * (G ^ 2 / q ^ 2) / (32 * b ^ 4 * β ^ 2) :=
    div_le_div_of_nonneg_right (mul_le_mul hn3 hgq (by positivity) (by positivity)) hK2.le
  rw [add_div, add_div]
  linarith

lemma sinh_le_mul_exp (x : ℝ) : Real.sinh x ≤ x * Real.exp x := by
  rw [Real.sinh_eq]
  have h := Real.add_one_le_exp (-(2 * x))
  have e : Real.exp (-x) = Real.exp x * Real.exp (-(2 * x)) := by rw [← Real.exp_add]; ring_nf
  rw [e]
  have := Real.exp_pos x
  nlinarith

lemma cosh_sub_one_le {x : ℝ} (hx : 0 ≤ x) : Real.cosh x - 1 ≤ x ^ 2 * Real.exp x / 2 := by
  have h2 : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
    rw [show x = 2 * (x / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]; ring_nf
  have hs := sinh_le_mul_exp (x / 2)
  have hs0 : 0 ≤ Real.sinh (x / 2) := Real.sinh_nonneg_iff.2 (by linarith)
  have hsq : Real.sinh (x / 2) ^ 2 ≤ (x / 2 * Real.exp (x / 2)) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have he : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; ring_nf
  rw [h2]
  calc 1 + 2 * Real.sinh (x / 2) ^ 2 - 1 ≤ 2 * (x / 2 * Real.exp (x / 2)) ^ 2 := by linarith
    _ = x ^ 2 * Real.exp x / 2 := by rw [mul_pow, he]; ring

/-- **The pole bound**: `‖Φ(i/2)‖ ≤ e^{3β}(β²/(4b²) + β⁴/(16b⁴))`, of order `1/T²`. -/
lemma norm_phiC_I_half {b T : ℝ} (hb : 0 < b) (hT : 0 < T) :
    ‖phiC b T (Complex.I / 2)‖ ≤ Real.exp (3 * (b / T)) * ((b / T) ^ 2 / (4 * b ^ 2) + (b / T) ^ 4 / (16 * b ^ 4)) := by
  have hβ : 0 < b / T := div_pos hb hT
  set β := b / T with hβdef
  have hg0 : ‖ghatC (bx β) β (Complex.I / 2)‖ ≤ 2 * β * Real.exp (β / 2) := by
    have h := norm_ghatC_bx_le β hβ.le (Complex.I / 2)
    have him : (Complex.I / 2).im = 1 / 2 := by simp
    rw [him, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    rwa [show β * (1 / 2) = β / 2 by ring] at h
  have hg1 : ghatC (gI β 1) (2 * β) (Complex.I / 2) = ghatC (bx β) β (Complex.I / 2) ^ 2 := by
    have h := ghatC_gI hβ (Complex.I / 2) 1; rwa [pow_one, pow_one] at h
  have hc2 : Complex.cos (2 * (β : ℂ) * (Complex.I / 2)) = (Real.cosh β : ℂ) := by
    rw [show 2 * (β : ℂ) * (Complex.I / 2) = (β : ℂ) * Complex.I by ring, Complex.cos_mul_I, Complex.ofReal_cosh]
  have hc4 : Complex.cos (4 * (β : ℂ) * (Complex.I / 2)) = (Real.cosh (2 * β) : ℂ) := by
    rw [show 4 * (β : ℂ) * (Complex.I / 2) = ((2 * β : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.cos_mul_I,
      Complex.ofReal_cosh]
  have hch := cosh_sub_one_le hβ.le
  have hch0 : 0 ≤ Real.cosh β - 1 := by linarith [Real.one_le_cosh β]
  have hc2b : Real.cosh (2 * β) = 2 * Real.cosh β ^ 2 - 1 := by rw [Real.cosh_two_mul, Real.cosh_sq]; ring
  have h3 : 3 - 4 * Real.cosh β + Real.cosh (2 * β) = 2 * (Real.cosh β - 1) ^ 2 := by rw [hc2b]; ring
  have h3b : 3 - 4 * Real.cosh β + Real.cosh (2 * β) ≤ β ^ 4 * Real.exp (2 * β) / 2 := by
    rw [h3]
    have := pow_le_pow_left₀ hch0 hch 2
    have he : Real.exp β ^ 2 = Real.exp (2 * β) := by rw [← Real.exp_nat_mul]; ring_nf
    calc 2 * (Real.cosh β - 1) ^ 2 ≤ 2 * (β ^ 2 * Real.exp β / 2) ^ 2 := by linarith
      _ = β ^ 4 * Real.exp β ^ 2 / 2 := by ring
      _ = β ^ 4 * Real.exp (2 * β) / 2 := by rw [he]
  have hK1 : (0 : ℝ) < 32 * b ^ 2 * β ^ 4 := by positivity
  have hK2 : (0 : ℝ) < 32 * b ^ 4 * β ^ 2 := by positivity
  unfold phiC
  rw [← hβdef, hg1, hc2, hc4]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hK1.le, Real.norm_of_nonneg hK2.le, ← pow_mul,
    show (1 : ℂ) - (Real.cosh β : ℂ) = ((1 - Real.cosh β : ℝ) : ℂ) by push_cast; ring,
    show (3 : ℂ) - 4 * (Real.cosh β : ℂ) + (Real.cosh (2 * β) : ℂ) =
      ((3 - 4 * Real.cosh β + Real.cosh (2 * β) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (by linarith),
    abs_of_nonneg (by rw [h3]; positivity)]
  have hg4 : ‖ghatC (bx β) β (Complex.I / 2)‖ ^ (2 * 2) ≤ (2 * β * Real.exp (β / 2)) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) hg0 4
  have hg2 : ‖ghatC (bx β) β (Complex.I / 2)‖ ^ 2 ≤ (2 * β * Real.exp (β / 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hg0 2
  have he1 : Real.exp (β / 2) ^ 4 = Real.exp (2 * β) := by rw [← Real.exp_nat_mul]; ring_nf
  have he2 : Real.exp (β / 2) ^ 2 = Real.exp β := by rw [← Real.exp_nat_mul]; ring_nf
  calc -(1 - Real.cosh β) * ‖ghatC (bx β) β (Complex.I / 2)‖ ^ (2 * 2) / (32 * b ^ 2 * β ^ 4)
        + (3 - 4 * Real.cosh β + Real.cosh (2 * β)) * ‖ghatC (bx β) β (Complex.I / 2)‖ ^ 2 / (32 * b ^ 4 * β ^ 2)
      ≤ (β ^ 2 * Real.exp β / 2) * (2 * β * Real.exp (β / 2)) ^ 4 / (32 * b ^ 2 * β ^ 4)
        + (β ^ 4 * Real.exp (2 * β) / 2) * (2 * β * Real.exp (β / 2)) ^ 2 / (32 * b ^ 4 * β ^ 2) := by
        gcongr
        linarith
    _ = Real.exp (3 * β) * (β ^ 2 / (4 * b ^ 2) + β ^ 4 / (16 * b ^ 4)) := by
        simp only [mul_pow]
        rw [he1, he2]
        field_simp
        rw [show β * 3 = β + β * 2 by ring, Real.exp_add]
        ring

/-! ## The test function and the explicit formula -/

/-- The strip constant of `Φ`. -/
def KPhi (b T : ℝ) : ℝ :=
  ((1 + Real.exp (2 * (b / T))) * (4 * (b / T) * Real.exp (b / T)) ^ 4 / (32 * b ^ 2 * (b / T) ^ 4)
    + (3 + 4 * Real.exp (2 * (b / T)) + Real.exp (4 * (b / T))) * (4 * (b / T) * Real.exp (b / T)) ^ 2
      / (32 * b ^ 4 * (b / T) ^ 2)) / (b / T) ^ 2

lemma differentiable_DC (N : ℕ) (c : ℕ → ℝ) : Differentiable ℂ (DC N c) := by unfold DC; fun_prop

/-- `h(z) = D(z)D(−z)Φ(z)`. -/
def htC (N : ℕ) (c : ℕ → ℝ) (b T : ℝ) (z : ℂ) : ℂ := DC N c z * DC N c (-z) * phiC b T z

/-- `h` on `ℝ`: `|D(t)|²Φ(t)`. -/
def hRC (N : ℕ) (c : ℕ → ℝ) (b T t : ℝ) : ℝ := Kc N c t * phiR b T t

lemma htC_ofReal {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (N : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    htC N c b T t = (hRC N c b T t : ℂ) := by
  unfold htC hRC
  rw [DC_ofReal, DC_neg_ofReal, phiC_ofReal hb hT, Kc_eq]
  push_cast
  linear_combination (-(Bc N c t : ℂ) ^ 2 * (phiR b T t : ℂ)) * Complex.I_sq

lemma htC_even {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (N : ℕ) (c : ℕ → ℝ) (z : ℂ) :
    htC N c b T (-z) = htC N c b T z := by
  unfold htC; rw [neg_neg, phiC_even b T hb hT]; ring

lemma striptest_htC {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (hbT : b ≤ T) (N : ℕ) (c : ℕ → ℝ) :
    WeilStrip.StripTest (htC N c b T) ((N * S1 N c) ^ 2 * KPhi b T) := by
  refine ⟨(((differentiable_DC N c).mul ((differentiable_DC N c).comp differentiable_neg)).mul
    (differentiable_phiC hb hT)).differentiableOn, fun t ht => ?_⟩
  have him : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have h1 := norm_DC_le N c him
  have h2 := norm_DC_le N c (z := -t) (by rwa [Complex.neg_im, abs_neg])
  have h3 : ‖phiC b T t‖ ≤ KPhi b T / (1 + t.re ^ 2) := norm_phiC_le hb hT hbT ht
  have hS := S1_nonneg N c
  have hpos : 0 < 1 + t.re ^ 2 := by positivity
  unfold htC
  rw [norm_mul, norm_mul]
  calc ‖DC N c t‖ * ‖DC N c (-t)‖ * ‖phiC b T t‖ ≤ (N * S1 N c) * (N * S1 N c) * (KPhi b T / (1 + t.re ^ 2)) := by
        gcongr
    _ = (N * S1 N c) ^ 2 * KPhi b T / (1 + t.re ^ 2) := by ring

/-- **Weil's explicit formula for `|D|²Φ`** (`weilExplicit_zeta`, no RH input). -/
lemma weil_htC {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (hbT : b ≤ T) (N : ℕ) (c : ℕ → ℝ) :
    WeilExplicit zetaZeroFamily (htC N c b T) (hRC N c b T) :=
  weilExplicit_zeta (striptest_htC hb hT hbT N c) (htC_even hb hT N c) (htC_ofReal hb hT N c)

/-! ## `|D|²` against a weight with a known cosine transform -/

lemma Kc_mul_mul_cos (N : ℕ) (c : ℕ → ℝ) (φ : ℝ → ℝ) (u r : ℝ) :
    Kc N c r * φ r * Real.cos (r * u) = ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' / 2 *
      (φ r * Real.cos (r * (Real.log j' - Real.log j + u)) + φ r * Real.cos (r * (Real.log j' - Real.log j - u))) := by
  unfold Kc
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [show r * (Real.log j' - Real.log j + u) = (Real.log j' - Real.log j) * r + r * u by ring,
    show r * (Real.log j' - Real.log j - u) = (Real.log j' - Real.log j) * r - r * u by ring,
    Real.cos_add, Real.cos_sub]
  ring

lemma integral_Kc_mul_cos (N : ℕ) (c : ℕ → ℝ) {φ φh : ℝ → ℝ}
    (hi : ∀ v, Integrable fun r => φ r * Real.cos (r * v)) (ht : ∀ v, ∫ r, φ r * Real.cos (r * v) = φh v)
    (u : ℝ) :
    ∫ r, Kc N c r * φ r * Real.cos (r * u) = ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' / 2 *
      (φh (Real.log j' - Real.log j + u) + φh (Real.log j' - Real.log j - u)) := by
  have hI : ∀ j j' : ℕ, Integrable fun r => c j * c j' / 2 *
      (φ r * Real.cos (r * (Real.log j' - Real.log j + u)) + φ r * Real.cos (r * (Real.log j' - Real.log j - u))) :=
    fun j j' => ((hi _).add (hi _)).const_mul _
  simp_rw [Kc_mul_mul_cos N c φ u]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => hI j j']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun j' _ => hI j j']
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [integral_const_mul, integral_add (hi _) (hi _), ht, ht]

lemma integrable_Kc_mul_cos (N : ℕ) (c : ℕ → ℝ) {φ : ℝ → ℝ}
    (hi : ∀ v, Integrable fun r => φ r * Real.cos (r * v)) (u : ℝ) :
    Integrable fun r => Kc N c r * φ r * Real.cos (r * u) := by
  have e : (fun r => Kc N c r * φ r * Real.cos (r * u)) = fun r => ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N,
      c j * c j' / 2 * (φ r * Real.cos (r * (Real.log j' - Real.log j + u))
        + φ r * Real.cos (r * (Real.log j' - Real.log j - u))) := funext (Kc_mul_mul_cos N c φ u)
  rw [e]
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => ((hi _).add (hi _)).const_mul _

lemma sum_symm_of_even (N : ℕ) (c : ℕ → ℝ) {φh : ℝ → ℝ} (he : ∀ v, φh (-v) = φh v) (u : ℝ) :
    ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' / 2 *
        (φh (Real.log j' - Real.log j + u) + φh (Real.log j' - Real.log j - u)) =
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * φh (Real.log j' - Real.log j - u) := by
  have hswap : ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * φh (Real.log j' - Real.log j + u) =
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * φh (Real.log j' - Real.log j - u) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [show Real.log j - Real.log j' + u = -(Real.log j' - Real.log j - u) by ring, he]
    ring
  calc ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' / 2 *
        (φh (Real.log j' - Real.log j + u) + φh (Real.log j' - Real.log j - u))
      = 1 / 2 * ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * φh (Real.log j' - Real.log j + u)
        + 1 / 2 * ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * φh (Real.log j' - Real.log j - u) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j' _ => ?_
        ring
    _ = _ := by rw [hswap]; ring

/-- `g_h(u) = (1/2π)Σ_{j,j'} c_j c_{j'} Φ̂(log j' − log j − u)`. -/
lemma gh_hRC {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (N : ℕ) (c : ℕ → ℝ) (u : ℝ) :
    gh (hRC N c b T) u = 1 / (2 * π) *
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * phihat b T (Real.log j' - Real.log j - u) := by
  unfold gh hRC
  rw [integral_Kc_mul_cos N c (integrable_phiR_cos hb hT) (integral_phiR_cos hb hT),
    sum_symm_of_even N c (phihat_neg b T)]

/-- **Exactness**: for `T > 12bN` only the exact matches `j' = jn` survive,
`Σ_{j,j'} c_j c_{j'} Φ̂(log j' − log j − log n) = Φ̂(0)e_n`. -/
lemma sum_phihat_exact {b T : ℝ} (hb : 0 < b) (hT : 0 < T) {N : ℕ} (hN : 1 ≤ N) (h12 : 12 * b * N < T)
    (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * phihat b T (Real.log j' - Real.log j - Real.log n) =
      phihat b T 0 * ex N c n := by
  rw [← sum_exact N c hn (phihat b T 0)]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h6 : 6 * (b / T) < 1 / (2 * N) := by
    rw [show 6 * (b / T) = 6 * b / T by ring, div_lt_div_iff₀ hT (by positivity)]
    nlinarith
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  congr 1
  by_cases h : j * n = j'
  · rw [ite_eq_left h, ← h, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      show Real.log j + Real.log n - Real.log j - Real.log n = 0 by ring]
  · rw [ite_eq_right h]
    apply phihat_eq_zero hb hT
    have hsep := sep_log hj hj' hn h
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at hsep
    rw [show Real.log j' - Real.log j - Real.log n = -(Real.log j + Real.log n - Real.log j') by ring, abs_neg]
    linarith

/-- **The diagonal**: `∫|D|²Φ = Φ̂(0)Σ c_n²` for `T > 12bN`. -/
lemma integral_hRC {b T : ℝ} (hb : 0 < b) (hT : 0 < T) {N : ℕ} (hN : 1 ≤ N) (h12 : 12 * b * N < T)
    (c : ℕ → ℝ) : ∫ r, hRC N c b T r = phihat b T 0 * S2 N c := by
  have h := integral_Kc_mul_cos N c (integrable_phiR_cos hb hT) (integral_phiR_cos hb hT) 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [sum_symm_of_even N c (phihat_neg b T) 0] at h
  have hx := sum_phihat_exact hb hT hN h12 c (n := 1) le_rfl
  rw [ex_one] at hx
  simp only [Nat.cast_one, Real.log_one, sub_zero] at hx h
  unfold hRC
  rw [h, hx]

lemma gh_hRC_log {b T : ℝ} (hb : 0 < b) (hT : 0 < T) {N : ℕ} (hN : 1 ≤ N) (h12 : 12 * b * N < T)
    (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    gh (hRC N c b T) (Real.log n) = phihat b T 0 / (2 * π) * ex N c n := by
  rw [gh_hRC hb hT, sum_phihat_exact hb hT hN h12 c hn]; ring

/-- **The prime side is Landau's form**, exactly: `2Σ_n Λ(n)n^{−1/2}g_h(log n) = (Φ̂(0)/2π)·2Σ_{n ≤ N}Λ(n)n^{−1/2}e_n`,
with `e_n = Σ_{jn ≤ N} c_j c_{jn}`. -/
lemma prime_eq_cut {b T : ℝ} (hb : 0 < b) (hT : 0 < T) {N : ℕ} (hN : 1 ≤ N) (h12 : 12 * b * N < T)
    (c : ℕ → ℝ) :
    2 * ∑' n : ℕ, Λ n / Real.sqrt n * gh (hRC N c b T) (Real.log n) =
      phihat b T 0 / (2 * π) * (2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n) := by
  have h0 : ∀ n ∉ Icc 1 N, Λ n / Real.sqrt n * gh (hRC N c b T) (Real.log n) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have : N < n := by
        by_contra h
        push Not at h
        exact hn (Finset.mem_Icc.2 ⟨hn0, h⟩)
      rw [gh_hRC_log hb hT hN h12 c hn0, ex_eq_zero N c this, mul_zero, mul_zero]
  rw [tsum_eq_sum h0]
  have e : ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * gh (hRC N c b T) (Real.log n) =
      phihat b T 0 / (2 * π) * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [gh_hRC_log hb hT hN h12 c (Finset.mem_Icc.1 hn).1]; ring
  rw [e]
  ring

/-- **The prime side is Landau's form**: `2Σ_n Λ(n)n^{−1/2}g_h(log n) ≤ (Φ̂(0)/2π)(log N + log 4 + 4)Σ c_n²`. -/
lemma prime_le_cut {b T : ℝ} (hb : 0 < b) (hT : 0 < T) {N : ℕ} (hN : 1 ≤ N) (h12 : 12 * b * N < T)
    (c : ℕ → ℝ) (hΦ : 0 ≤ phihat b T 0) :
    2 * ∑' n : ℕ, Λ n / Real.sqrt n * gh (hRC N c b T) (Real.log n) ≤
      phihat b T 0 / (2 * π) * (Real.log N + (Real.log 4 + 4)) * S2 N c := by
  rw [prime_eq_cut hb hT hN h12 c]
  have hland : 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n ≤
      (Real.log N + (Real.log 4 + 4)) * S2 N c := landau_le N c
  have hw : 0 ≤ phihat b T 0 / (2 * π) := div_nonneg hΦ (by positivity)
  have := mul_le_mul_of_nonneg_left hland hw
  linarith

/-! ## The mass of `|D|²` on `[−r, r]`

`M_r(t) = (r²/4)ĝ_{box(π/2r)}(t)² = (r/t)²sin²(πt/2r) ≥ 1_{[−r,r]}`, with transform `(πr²/2)(π/r − |v|)⁺`; a Schur
test and a count of the `j'` with `|log j' − log j| < π/r` give `∫_{|t| ≤ r}|D|² ≤ (π²/2)Σ_j (r + 8j)c_j²`. -/

/-- The majorant `M_r`. -/
def majR (r t : ℝ) : ℝ := r ^ 2 / 4 * hsq (bx (π / (2 * r))) (π / (2 * r)) t

/-- Its transform `(πr²/2)(π/r − |v|)⁺`. -/
def mhat (r v : ℝ) : ℝ := π * r ^ 2 / 2 * max (π / r - |v|) 0

lemma majR_nonneg (r t : ℝ) : 0 ≤ majR r t := by unfold majR; have := hsq_nonneg (g := bx (π / (2 * r))) (a := π / (2 * r)) t; positivity

lemma gH_bx_zero {a : ℝ} (ha : 0 ≤ a) : gH (bx a) a 0 = 2 * a := by
  unfold gH
  rw [ghatC_bx a ha]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const]
  simp
  ring

/-- `M_r ≥ 1` on `[−r, r]`. -/
lemma one_le_majR {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r) : 1 ≤ majR r t := by
  have ha : 0 < π / (2 * r) := by positivity
  unfold majR
  rcases eq_or_ne t 0 with rfl | ht0
  · unfold hsq; rw [gH_bx_zero ha.le]
    have hpi : (2 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    field_simp
    nlinarith
  · rw [hsq_bx_eq ha.le ht0]
    have hx : π / (2 * r) * |t| ≤ π / 2 := by
      rw [show π / 2 = π / (2 * r) * r by field_simp]
      exact mul_le_mul_of_nonneg_left ht ha.le
    have hj := Real.mul_le_sin (by positivity : 0 ≤ π / (2 * r) * |t|) hx
    have e1 : 2 / π * (π / (2 * r) * |t|) = |t| / r := by field_simp
    rw [e1] at hj
    have hsin : Real.sin (π / (2 * r) * |t|) ^ 2 = Real.sin (π / (2 * r) * t) ^ 2 := by
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, mul_neg, Real.sin_neg, neg_sq]
    have hq : (|t| / r) ^ 2 ≤ Real.sin (π / (2 * r) * t) ^ 2 := by
      rw [← hsin]; exact pow_le_pow_left₀ (by positivity) hj 2
    have ht2 : 0 < t ^ 2 := by positivity
    rw [div_pow, sq_abs] at hq
    rw [show r ^ 2 / 4 * (4 * Real.sin (π / (2 * r) * t) ^ 2 / t ^ 2) =
      r ^ 2 * Real.sin (π / (2 * r) * t) ^ 2 / t ^ 2 by ring, le_div_iff₀ ht2]
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ r ^ 2)
    rw [mul_div_assoc', mul_comm (r ^ 2) (t ^ 2), mul_div_assoc, div_self (by positivity), mul_one] at this
    linarith

lemma integral_majR_cos {r : ℝ} (hr : 0 < r) (v : ℝ) : ∫ t, majR r t * Real.cos (t * v) = mhat r v := by
  have ha : 0 < π / (2 * r) := by positivity
  unfold majR mhat
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_hsq_cos (esupp_bx _) ha, autocorr_bx]
  rw [show 2 * (π / (2 * r)) = π / r by field_simp]
  ring

lemma integrable_majR_cos {r : ℝ} (hr : 0 < r) (v : ℝ) : Integrable fun t => majR r t * Real.cos (t * v) := by
  have ha : 0 < π / (2 * r) := by positivity
  unfold majR
  simp_rw [mul_assoc]
  exact (integrable_hsq_cos (esupp_bx _) ha v).const_mul _

lemma mhat_neg (r v : ℝ) : mhat r (-v) = mhat r v := by unfold mhat; rw [abs_neg]

/-- **Schur's test** for a symmetric nonnegative kernel. -/
lemma schur_sym (N : ℕ) (c : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (hK0 : ∀ j j', 0 ≤ K j j') (hKs : ∀ j j', K j j' = K j' j) :
    ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * K j j' ≤ ∑ j ∈ Icc 1 N, c j ^ 2 * ∑ j' ∈ Icc 1 N, K j j' := by
  have h1 : ∀ j j', c j * c j' * K j j' ≤ (c j ^ 2 / 2 + c j' ^ 2 / 2) * K j j' := fun j j' =>
    mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (c j - c j')]) (hK0 j j')
  have e : ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, (c j ^ 2 / 2 + c j' ^ 2 / 2) * K j j' =
      ∑ j ∈ Icc 1 N, c j ^ 2 * ∑ j' ∈ Icc 1 N, K j j' := by
    have e1 : ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, (c j ^ 2 / 2 + c j' ^ 2 / 2) * K j j' =
        ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j ^ 2 / 2 * K j j' + ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j' ^ 2 / 2 * K j j' := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j' _ => by ring
    have e2 : ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j' ^ 2 / 2 * K j j' =
        ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j ^ 2 / 2 * K j j' := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by rw [hKs]
    rw [e1, e2, ← two_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by ring
  calc _ ≤ ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, (c j ^ 2 / 2 + c j' ^ 2 / 2) * K j j' :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => h1 j j'
    _ = _ := e

lemma exp_sub_exp_neg_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 2 / 5) :
    Real.exp ε - Real.exp (-ε) ≤ 12 / 5 * ε := by
  have ha := Real.abs_exp_sub_one_sub_id_le (x := ε) (by rw [abs_of_nonneg h0]; linarith)
  have hb := Real.add_one_le_exp (-ε)
  have := (abs_le.1 ha).2
  nlinarith

/-- **The count**: `#{j' ≤ N : |log j' − log j| < ε} ≤ 1 + (12/5)εj` for `0 ≤ ε ≤ 2/5`. -/
lemma card_near_le (N : ℕ) {j : ℕ} (hj : 1 ≤ j) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 2 / 5) :
    (((Icc 1 N).filter fun j' : ℕ => |Real.log j' - Real.log j| < ε).card : ℝ) ≤ 1 + 12 / 5 * ε * j := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set a := ⌊(j : ℝ) * Real.exp (-ε)⌋₊ with ha
  set b := ⌈(j : ℝ) * Real.exp ε⌉₊ with hb
  have hsub : (Icc 1 N).filter (fun j' : ℕ => |Real.log j' - Real.log j| < ε) ⊆ Finset.Ioo a b := by
    intro j' hj'
    rw [Finset.mem_filter, Finset.mem_Icc] at hj'
    obtain ⟨⟨hj'1, -⟩, hlt⟩ := hj'
    have hj'R : (0 : ℝ) < j' := by exact_mod_cast hj'1
    have hl := abs_lt.1 hlt
    rw [Finset.mem_Ioo]
    constructor
    · rw [ha, Nat.floor_lt (by positivity)]
      have : Real.log j - ε < Real.log j' := by linarith
      have h := Real.exp_lt_exp.2 this
      rw [Real.exp_sub, Real.exp_log (show (0 : ℝ) < j by positivity), Real.exp_log hj'R] at h
      calc (j : ℝ) * Real.exp (-ε) = j / Real.exp ε := by rw [Real.exp_neg]; ring
        _ < j' := h
    · rw [hb, Nat.lt_ceil]
      have : Real.log j' < Real.log j + ε := by linarith
      have h := Real.exp_lt_exp.2 this
      rw [Real.exp_add, Real.exp_log (show (0 : ℝ) < j by positivity), Real.exp_log hj'R] at h
      exact h
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioo] at hcard
  have hA : (j : ℝ) * Real.exp (-ε) < a + 1 := Nat.lt_floor_add_one _
  have hB : (b : ℝ) < j * Real.exp ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hE := exp_sub_exp_neg_le h0 h1
  have hcast : (((Icc 1 N).filter fun j' : ℕ => |Real.log j' - Real.log j| < ε).card : ℝ) ≤ ((b - a - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rcases Nat.lt_or_ge b (a + 1) with hlt | hge
  · have : b - a - 1 = 0 := by omega
    rw [this, Nat.cast_zero] at hcast
    have : 0 ≤ 12 / 5 * ε * j := by positivity
    linarith
  · have e : ((b - a - 1 : ℕ) : ℝ) = b - a - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e] at hcast
    have : (j : ℝ) * (Real.exp ε - Real.exp (-ε)) ≤ j * (12 / 5 * ε) := mul_le_mul_of_nonneg_left hE (by positivity)
    nlinarith

/-- **The mass bound**: for `r ≥ 8`, `∫ |D|² M_r ≤ (π²/2)Σ_j (r + 8j) c_j²`. -/
lemma integral_Kc_majR_le {N : ℕ} {r : ℝ} (hr : 8 ≤ r) (c : ℕ → ℝ) :
    ∫ t, Kc N c t * majR r t ≤ π ^ 2 / 2 * ∑ j ∈ Icc 1 N, (r + 8 * j) * c j ^ 2 := by
  have hr0 : 0 < r := by linarith
  have h := integral_Kc_mul_cos N c (integrable_majR_cos hr0) (integral_majR_cos hr0) 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [sum_symm_of_even N c (mhat_neg r) 0] at h
  simp only [sub_zero] at h
  rw [h]
  have hK0 : ∀ j j' : ℕ, 0 ≤ mhat r (Real.log j' - Real.log j) := fun j j' => by unfold mhat; positivity
  have hKs : ∀ j j' : ℕ, mhat r (Real.log j' - Real.log j) = mhat r (Real.log j - Real.log j') := fun j j' => by
    rw [← mhat_neg, neg_sub]
  refine (schur_sym N c (fun j j' => mhat r (Real.log j' - Real.log j)) hK0 hKs).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj1 := (Finset.mem_Icc.1 hj).1
  have hε0 : 0 ≤ π / r := by positivity
  have hε1 : π / r ≤ 2 / 5 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith [Real.pi_lt_d2]
  have hrow : ∑ j' ∈ Icc 1 N, mhat r (Real.log j' - Real.log j) ≤
      π ^ 2 * r / 2 * (((Icc 1 N).filter fun j' : ℕ => |Real.log j' - Real.log j| < π / r).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_le_sum fun j' _ => ?_
    unfold mhat
    split_ifs with hlt
    · push_cast
      have : max (π / r - |Real.log j' - Real.log j|) 0 ≤ π / r :=
        max_le (by linarith [abs_nonneg (Real.log j' - Real.log j)]) hε0
      calc π * r ^ 2 / 2 * max (π / r - |Real.log j' - Real.log j|) 0 ≤ π * r ^ 2 / 2 * (π / r) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = π ^ 2 * r / 2 * 1 := by field_simp
    · push Not at hlt
      rw [max_eq_right (by linarith)]
      simp
  have hcnt := card_near_le N hj1 hε0 hε1
  calc c j ^ 2 * ∑ j' ∈ Icc 1 N, mhat r (Real.log j' - Real.log j)
      ≤ c j ^ 2 * (π ^ 2 * r / 2 * (1 + 12 / 5 * (π / r) * j)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact hrow.trans (mul_le_mul_of_nonneg_left hcnt (by positivity))
    _ ≤ π ^ 2 / 2 * ((r + 8 * j) * c j ^ 2) := by
        have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have e : π ^ 2 * r / 2 * (1 + 12 / 5 * (π / r) * j) = π ^ 2 / 2 * (r + 12 / 5 * π * j) := by
          field_simp
        rw [e]
        have : 12 / 5 * π * j ≤ 8 * j := by nlinarith [Real.pi_lt_d2]
        calc c j ^ 2 * (π ^ 2 / 2 * (r + 12 / 5 * π * j)) = π ^ 2 / 2 * c j ^ 2 * (r + 12 / 5 * π * j) := by ring
          _ ≤ π ^ 2 / 2 * c j ^ 2 * (r + 8 * j) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = _ := by ring

/-! ## The archimedean weight

`L(t) = Re ψ(¼ + it/2) − log π` is compared with `L₁ = log(T/16π) − 3`, its floor on `|t| ≥ T/8`. The defect
`Φ(L − L₁)` is bounded below by `−W`, with `W` the low-height majorant `M_{T/8}/256`, the dyadic shells
`ε_i M_{2^{i+1}T}` (`2^i T < |t| ≤ 2^{i+1}T`, `i < 2J`, `ε_i = (i + 20)/(b⁶4^i)`) and the far weight
`(21T√T/b⁶)|t|^{−3/2}` on `|t| > 4^J T`. -/

/-- `L₁ = log(T/16π) − 3`. -/
def L1 (T : ℝ) : ℝ := Real.log (T / (16 * π)) - 3

lemma abs_psiRe_zero_le : |psiRe 0| ≤ 7 := by
  have hq := DigammaStirling.re_digamma_quarter 0 0
  have e0 : psiRe 0 = (Complex.digamma (1 / 4 + ((0 : ℝ) : ℂ) * Complex.I)).re := by
    unfold psiRe; rw [zB_eq]; norm_num
  rw [← e0] at hq
  have hval : DigammaStirling.psiApx 0 0 = Real.log (1 / 16) / 2 - 2 - 4 / 3 := by
    unfold DigammaStirling.psiApx; norm_num
  have herr : (1 : ℝ) / (120 * (((0 : ℕ) : ℝ) + 1 / 4) ^ 4) = 32 / 15 := by norm_num
  rw [hval, herr] at hq
  have hl16 : Real.log (1 / 16) = -(4 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  rw [hl16] at hq
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have h := abs_le.1 hq
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

lemma log_pi_le : Real.log π ≤ 2 * Real.log 2 := by
  calc Real.log π ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_le_four
    _ = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

lemma L1_eq {T : ℝ} (hT : 0 < T) : L1 T = Real.log T - 4 * Real.log 2 - Real.log π - 3 := by
  unfold L1
  rw [Real.log_div hT.ne' (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne',
    show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  push_cast; ring

/-- From above: `L(t) − L₁ ≤ log(1 + |t|) − log T + 18`. -/
lemma L_sub_L1_le {T : ℝ} (hT : 0 < T) (t : ℝ) :
    psiRe t - Real.log π - L1 T ≤ Real.log (1 + |t|) - Real.log T + 18 := by
  have h1 := (abs_le.1 (abs_psiRe_le t)).2
  have h2 := abs_psiRe_zero_le
  rw [L1_eq hT]
  have hl2 := Real.log_two_lt_d9
  linarith

/-- From below: `L(t) − L₁ ≥ log(8|t|/T)` for `|t| ≥ 8`. -/
lemma L_sub_L1_ge {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : 8 ≤ |t|) :
    Real.log (8 * |t| / T) ≤ psiRe t - Real.log π - L1 T := by
  have h := psiRe_ge_log ht
  have ht0 : 0 < |t| := by linarith
  rw [Real.log_div ht0.ne' (by norm_num)] at h
  rw [L1_eq hT, Real.log_div (by positivity) hT.ne', Real.log_mul (by norm_num) ht0.ne',
    show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast
  linarith

/-- **Low heights**: on `|t| ≤ T`, `(t/T)²(L₁ − L(t))⁺ ≤ M_{T/8}(t)/256` once `T ≥ 64` and `2¹⁴(L₁ + 9) ≤ T²`. -/
lemma low_le {T : ℝ} (hT : 64 ≤ T) (hbig : 16384 * (L1 T + 9) ≤ T ^ 2) (t : ℝ) :
    (t / T) ^ 2 * max (L1 T - (psiRe t - Real.log π)) 0 ≤ 1 / 256 * majR (T / 8) t := by
  have hT0 : 0 < T := by linarith
  have hM0 := majR_nonneg (T / 8) t
  rcases le_or_gt (T / 8) |t| with h1 | h1
  · have hge := L_sub_L1_ge hT0 (by linarith : 8 ≤ |t|)
    have h8 : 1 ≤ 8 * |t| / T := by rw [le_div_iff₀ hT0]; linarith
    have := Real.log_nonneg h8
    rw [max_eq_right (by linarith), mul_zero]
    positivity
  · have hM1 := one_le_majR (by linarith : 0 < T / 8) h1.le
    have hkey : (t / T) ^ 2 * max (L1 T - (psiRe t - Real.log π)) 0 ≤ 1 / 256 := by
      rcases le_or_gt 8 |t| with h2 | h2
      · have hge := L_sub_L1_ge hT0 h2
        have ht0 : 0 < |t| := by linarith
        have ht0' : |t| ≠ 0 := ht0.ne'
        set u := T / (8 * |t|) with hu
        have hu1 : 1 < u := by rw [hu, lt_div_iff₀ (by positivity)]; linarith
        have hlog : Real.log (8 * |t| / T) = -Real.log u := by
          rw [hu, ← Real.log_inv, inv_div]
        have hlu := Real.log_le_sub_one_of_pos (by linarith : 0 < u)
        have htT : (t / T) ^ 2 = 1 / (64 * u ^ 2) := by
          rw [hu, div_pow, ← sq_abs t]; field_simp; ring
        have hmax : max (L1 T - (psiRe t - Real.log π)) 0 ≤ u - 1 := max_le (by linarith) (by linarith)
        rw [htT]
        calc 1 / (64 * u ^ 2) * max (L1 T - (psiRe t - Real.log π)) 0 ≤ 1 / (64 * u ^ 2) * (u - 1) :=
              mul_le_mul_of_nonneg_left hmax (by positivity)
          _ ≤ 1 / 256 := by
              rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith [sq_nonneg (u - 2)]
      · have hlow := psiRe_sub_log_pi_ge t
        have hL1 : 0 ≤ L1 T + 9 := by
          rw [L1_eq hT0]
          have h64 : Real.log 64 ≤ Real.log T := Real.log_le_log (by norm_num) hT
          have e64 : Real.log 64 = 6 * Real.log 2 := by
            rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
          have := log_pi_le
          have hl2 := Real.log_two_gt_d9
          linarith
        have hmax : max (L1 T - (psiRe t - Real.log π)) 0 ≤ L1 T + 9 := max_le (by linarith) hL1
        have ht2 : (t / T) ^ 2 ≤ 64 / T ^ 2 := by
          rw [div_pow]
          apply div_le_div_of_nonneg_right _ (by positivity)
          have := sq_abs t
          nlinarith [abs_nonneg t]
        calc (t / T) ^ 2 * max (L1 T - (psiRe t - Real.log π)) 0 ≤ 64 / T ^ 2 * (L1 T + 9) :=
              mul_le_mul ht2 hmax (le_max_right _ _) (by positivity)
          _ ≤ 1 / 256 := by
              rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith
    linarith

lemma four_pow_eq (i : ℕ) : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num

/-- The shell weights `ε_i = (i + 20)/(b⁶4^i)`. -/
def epsS (b : ℝ) (i : ℕ) : ℝ := (i + 20) / (b ^ 6 * 4 ^ i)

lemma epsS_nonneg {b : ℝ} (hb : 0 < b) (i : ℕ) : 0 ≤ epsS b i := by unfold epsS; positivity

/-- **A shell**: for `T ≥ 1` and `2^i T < |t| ≤ 2^{i+1}T`, `Φ(t)(L(t) − L₁) ≥ −ε_i`. -/
lemma shell_ge {b T : ℝ} (hb : 0 < b) (hT : 1 ≤ T) {i : ℕ} {t : ℝ} (h1 : 2 ^ i * T < |t|)
    (h2 : |t| ≤ 2 ^ (i + 1) * T) :
    -epsS b i ≤ phiR b T t * (psiRe t - Real.log π - L1 T) := by
  have hT0 : 0 < T := by linarith
  have hi1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hTt : T ≤ |t| := by nlinarith
  obtain ⟨hneg, habs⟩ := phiR_tail hb hT0 hTt
  have hup := L_sub_L1_le hT0 t
  have hlog : Real.log (1 + |t|) ≤ (i + 2) * Real.log 2 + Real.log T := by
    have h3 : 1 + |t| ≤ 2 ^ (i + 2) * T := by
      have e : (2 : ℝ) ^ (i + 2) = 2 * 2 ^ (i + 1) := by ring
      have h4 : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ (by norm_num)
      have h5 : (1 : ℝ) ≤ 2 ^ (i + 1) * T := by nlinarith
      rw [e]; nlinarith
    calc Real.log (1 + |t|) ≤ Real.log (2 ^ (i + 2) * T) := Real.log_le_log (by positivity) h3
      _ = (i + 2) * Real.log 2 + Real.log T := by
        rw [Real.log_mul (by positivity) hT0.ne', Real.log_pow]; push_cast; ring
  have hL : psiRe t - Real.log π - L1 T ≤ i + 20 := by
    have hl2 := Real.log_two_lt_d9
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have := mul_nonneg hi0 (by linarith : (0 : ℝ) ≤ 1 - Real.log 2)
    nlinarith
  have hsq : 4 ^ i * T ^ 2 < t ^ 2 := by
    rw [four_pow_eq, ← sq_abs t]
    have h0 : 0 ≤ 2 ^ i * T := by positivity
    have := mul_self_lt_mul_self h0 h1
    calc (2 : ℝ) ^ i * 2 ^ i * T ^ 2 = (2 ^ i * T) * (2 ^ i * T) := by ring
      _ < |t| * |t| := this
      _ = |t| ^ 2 := by ring
  have hphi : |phiR b T t| ≤ 1 / (b ^ 6 * 4 ^ i) := by
    refine habs.trans ?_
    have ht2 : 0 < t ^ 2 := lt_of_le_of_lt (by positivity) hsq
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hb6 : 0 < b ^ 6 := by positivity
    have := mul_le_mul_of_nonneg_left hsq.le hb6.le
    calc T ^ 2 * (b ^ 6 * 4 ^ i) = b ^ 6 * (4 ^ i * T ^ 2) := by ring
      _ ≤ b ^ 6 * t ^ 2 := this
      _ = 1 * (b ^ 6 * t ^ 2) := by ring
  unfold epsS
  rcases le_or_gt (psiRe t - Real.log π - L1 T) 0 with hL0 | hL0
  · have h4 : 0 ≤ phiR b T t * (psiRe t - Real.log π - L1 T) := mul_nonneg_of_nonpos_of_nonpos hneg hL0
    have h5 : 0 ≤ ((i : ℝ) + 20) / (b ^ 6 * 4 ^ i) := by positivity
    linarith
  · have e : phiR b T t = -|phiR b T t| := by rw [abs_of_nonpos hneg, neg_neg]
    rw [e, neg_mul]
    apply neg_le_neg
    calc |phiR b T t| * (psiRe t - Real.log π - L1 T) ≤ 1 / (b ^ 6 * 4 ^ i) * (i + 20) :=
          mul_le_mul hphi hL hL0.le (by positivity)
      _ = (i + 20) / (b ^ 6 * 4 ^ i) := by ring

lemma rpow_neg_three_halves {x : ℝ} (hx : 0 < x) : x ^ (-(3 / 2 : ℝ)) = 1 / (x * Real.sqrt x) := by
  rw [Real.rpow_neg hx.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    ← Real.sqrt_eq_rpow, one_div]

/-- The far weight `|t|^{−3/2}` on `|t| > R`. -/
def farW (R t : ℝ) : ℝ := Set.indicator (Set.Ioi R) (fun s => s ^ (-(3 / 2 : ℝ))) |t|

lemma farW_nonneg {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : 0 ≤ farW R t := by
  unfold farW
  exact Set.indicator_nonneg (fun s hs => Real.rpow_nonneg (hR.trans (le_of_lt hs)) _) _

lemma farW_of_lt {R t : ℝ} (hR : 0 ≤ R) (ht : R < |t|) : farW R t = 1 / (|t| * Real.sqrt |t|) := by
  unfold farW
  rw [Set.indicator_of_mem (show |t| ∈ Set.Ioi R from ht)]
  exact rpow_neg_three_halves (by linarith)

lemma integrable_farW {R : ℝ} (hR : 0 < R) : Integrable (farW R) := by
  set g : ℝ → ℝ := Set.indicator (Set.Ioi R) (fun s => s ^ (-(3 / 2 : ℝ))) with hg
  have hgi : Integrable g :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hR).integrable_indicator measurableSet_Ioi
  have hIoi : IntegrableOn (fun x => g |x|) (Set.Ioi 0) :=
    hgi.integrableOn.congr_fun (fun x hx => by simp only [abs_of_pos (show (0 : ℝ) < x from hx)])
      measurableSet_Ioi
  have hIic : IntegrableOn (fun x => g |x|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi
  have h := hIic.union hIoi
  rw [Set.Iic_union_Ioi, integrableOn_univ] at h
  exact h

lemma integral_farW {R : ℝ} (hR : 0 < R) : ∫ t, farW R t = 4 / Real.sqrt R := by
  unfold farW
  rw [integral_comp_abs (f := Set.indicator (Set.Ioi R) (fun s => s ^ (-(3 / 2 : ℝ)))),
    setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hR.le,
    integral_Ioi_rpow_of_lt (by norm_num) hR,
    show (-(3 / 2 : ℝ) + 1) = -(1 / 2) by norm_num, Real.rpow_neg hR.le, ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  field_simp
  norm_num

lemma far_algebra {T x b : ℝ} (hT : 0 < T) (hx : 0 < x) (hb : 0 < b) :
    T ^ 2 / (b ^ 6 * x ^ 2) * (21 * Real.sqrt (x / T)) =
      21 * T * Real.sqrt T / b ^ 6 * (1 / (x * Real.sqrt x)) := by
  rw [Real.sqrt_div hx.le]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hq : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hss := Real.sq_sqrt hx.le
  have hqq := Real.sq_sqrt hT.le
  generalize Real.sqrt x = s at hs hss ⊢
  generalize Real.sqrt T = q at hq hqq ⊢
  subst hss hqq
  field_simp

/-- **The far tail**: for `1 ≤ T ≤ R < |t|`, `Φ(t)(L(t) − L₁) ≥ −(21T√T/b⁶)|t|^{−3/2}`. -/
lemma far_ge {b T R : ℝ} (hb : 0 < b) (hT : 1 ≤ T) (hTR : T ≤ R) {t : ℝ} (ht : R < |t|) :
    -(21 * T * Real.sqrt T / b ^ 6 * farW R t) ≤ phiR b T t * (psiRe t - Real.log π - L1 T) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < |t| := by linarith
  obtain ⟨hneg, habs⟩ := phiR_tail hb hT0 (by linarith : T ≤ |t|)
  have hup := L_sub_L1_le hT0 t
  have hx1 : 1 ≤ |t| / T := by rw [le_div_iff₀ hT0]; linarith
  have hlog1 : Real.log (1 + |t|) - Real.log T ≤ Real.log 2 + Real.log (|t| / T) := by
    rw [Real.log_div ht0.ne' hT0.ne']
    have h := Real.log_le_log (by positivity) (show 1 + |t| ≤ 2 * |t| by linarith)
    rw [Real.log_mul (by norm_num) ht0.ne'] at h
    linarith
  have hlogx : Real.log (|t| / T) ≤ 2 * Real.sqrt (|t| / T) := by
    have h := Real.log_le_rpow_div (x := |t| / T) (ε := 1 / 2) (by positivity) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hs1 : 1 ≤ Real.sqrt (|t| / T) := Real.one_le_sqrt.2 hx1
  have hL : psiRe t - Real.log π - L1 T ≤ 21 * Real.sqrt (|t| / T) := by
    have hl2 := Real.log_two_lt_d9
    linarith
  have hfar := farW_of_lt (by linarith) ht
  have key := far_algebra hT0 ht0 hb
  rw [sq_abs] at key
  rcases le_or_gt (psiRe t - Real.log π - L1 T) 0 with hL0 | hL0
  · have h4 : 0 ≤ phiR b T t * (psiRe t - Real.log π - L1 T) := mul_nonneg_of_nonpos_of_nonpos hneg hL0
    have h5 : 0 ≤ 21 * T * Real.sqrt T / b ^ 6 * farW R t :=
      mul_nonneg (by positivity) (farW_nonneg (by linarith) t)
    linarith
  · have e : phiR b T t = -|phiR b T t| := by rw [abs_of_nonpos hneg, neg_neg]
    rw [e, neg_mul, hfar]
    apply neg_le_neg
    calc |phiR b T t| * (psiRe t - Real.log π - L1 T) ≤ T ^ 2 / (b ^ 6 * t ^ 2) * (21 * Real.sqrt (|t| / T)) :=
          mul_le_mul habs hL hL0.le (by positivity)
      _ = _ := key

/-- The defect weight `W = M_{T/8}/256 + Σ_{i<2J} ε_i M_{2^{i+1}T} + (21T√T/b⁶)|t|^{−3/2}1_{|t| > 4^J T}`. -/
def tailW (b T : ℝ) (J : ℕ) (t : ℝ) : ℝ :=
  1 / 256 * majR (T / 8) t + ∑ i ∈ range (2 * J), epsS b i * majR (2 ^ (i + 1) * T) t
    + 21 * T * Real.sqrt T / b ^ 6 * farW (4 ^ J * T) t

/-- **The defect is bounded below**: `Φ(t)(L(t) − L₁) ≥ −W(t)` for every `t`. -/
lemma phiR_mul_L_ge {b T : ℝ} (hb : 0 < b) (hT : 64 ≤ T) (hbig : 16384 * (L1 T + 9) ≤ T ^ 2) (J : ℕ)
    (t : ℝ) : -tailW b T J t ≤ phiR b T t * (psiRe t - Real.log π - L1 T) := by
  have hT0 : 0 < T := by linarith
  have hM := majR_nonneg (T / 8) t
  have hS : 0 ≤ ∑ i ∈ range (2 * J), epsS b i * majR (2 ^ (i + 1) * T) t :=
    Finset.sum_nonneg fun i _ => mul_nonneg (epsS_nonneg hb i) (majR_nonneg _ _)
  have hF : 0 ≤ 21 * T * Real.sqrt T / b ^ 6 * farW (4 ^ J * T) t :=
    mul_nonneg (by positivity) (farW_nonneg (by positivity) t)
  unfold tailW
  rcases le_or_gt |t| T with h1 | h1
  · obtain ⟨h0, hle, -⟩ := phiR_bounds hb hT0 h1
    have hlow := low_le hT hbig t
    have hm : -((t / T) ^ 2 * max (L1 T - (psiRe t - Real.log π)) 0) ≤
        phiR b T t * (psiRe t - Real.log π - L1 T) := by
      rcases le_or_gt 0 (psiRe t - Real.log π - L1 T) with hL | hL
      · have h2 := mul_nonneg h0 hL
        have h3 := mul_nonneg (sq_nonneg (t / T)) (le_max_right (L1 T - (psiRe t - Real.log π)) 0)
        linarith
      · rw [max_eq_left (by linarith)]
        have h2 : phiR b T t * (L1 T - (psiRe t - Real.log π)) ≤
            (t / T) ^ 2 * (L1 T - (psiRe t - Real.log π)) :=
          mul_le_mul_of_nonneg_right hle (by linarith)
        linarith
    linarith
  rcases le_or_gt |t| (4 ^ J * T) with h2 | h2
  · have hJ : 1 ≤ J := by
      rcases Nat.eq_zero_or_pos J with h | h
      · rw [h, pow_zero, one_mul] at h2; linarith
      · exact h
    have e4 : (2 : ℝ) ^ (2 * J - 1 + 1) = 4 ^ J := by
      rw [show 2 * J - 1 + 1 = 2 * J by omega, pow_mul]; norm_num
    have hex : ∃ i, |t| ≤ 2 ^ (i + 1) * T := ⟨2 * J - 1, by rw [e4]; exact h2⟩
    have hup : |t| ≤ 2 ^ (Nat.find hex + 1) * T := Nat.find_spec hex
    have hlt : Nat.find hex < 2 * J := by
      have := Nat.find_min' hex (m := 2 * J - 1) (by rw [e4]; exact h2)
      omega
    have hlow : 2 ^ Nat.find hex * T < |t| := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
      · rw [h0, pow_zero, one_mul]; exact h1
      · have h3 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        push Not at h3
        rwa [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at h3
    have hsh := shell_ge hb (by linarith) hlow hup
    have hM1 := one_le_majR (by positivity : 0 < 2 ^ (Nat.find hex + 1) * T) hup
    have hsingle : epsS b (Nat.find hex) * majR (2 ^ (Nat.find hex + 1) * T) t ≤
        ∑ i ∈ range (2 * J), epsS b i * majR (2 ^ (i + 1) * T) t :=
      Finset.single_le_sum (f := fun i => epsS b i * majR (2 ^ (i + 1) * T) t)
        (fun i _ => mul_nonneg (epsS_nonneg hb i) (majR_nonneg _ _)) (Finset.mem_range.2 hlt)
    have he : epsS b (Nat.find hex) ≤ epsS b (Nat.find hex) * majR (2 ^ (Nat.find hex + 1) * T) t :=
      le_mul_of_one_le_right (epsS_nonneg hb _) hM1
    linarith
  · have h4 : T ≤ 4 ^ J * T := le_mul_of_one_le_left hT0.le (one_le_pow₀ (by norm_num))
    have hfar := far_ge hb (by linarith) h4 h2
    linarith

/-! ## The mass of the defect weight -/

lemma integrable_Kc_majR (N : ℕ) (c : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable fun t => Kc N c t * majR r t := by
  have h := integrable_Kc_mul_cos N c (integrable_majR_cos hr) 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  exact h

lemma integral_Kc_majR_le' {N : ℕ} {r : ℝ} (hr : 8 ≤ r) (c : ℕ → ℝ) :
    ∫ t, Kc N c t * majR r t ≤ π ^ 2 / 2 * (r + 8 * N) * S2 N c := by
  refine (integral_Kc_majR_le hr c).trans ?_
  have h : ∑ j ∈ Icc 1 N, (r + 8 * j) * c j ^ 2 ≤ (r + 8 * N) * S2 N c := by
    rw [S2, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.1 hj).2
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ π ^ 2 / 2)
  linarith

lemma sum_geom_aux (n : ℕ) : ∑ i ∈ range n, ((i : ℝ) + 20) / 2 ^ i = 42 - 2 * (n + 21) / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

lemma sum_geom_le (n : ℕ) : ∑ i ∈ range n, ((i : ℝ) + 20) / 2 ^ i ≤ 42 := by
  rw [sum_geom_aux]
  have : 0 ≤ 2 * ((n : ℝ) + 21) / 2 ^ n := by positivity
  linarith

lemma epsS_mul_le {b : ℝ} (hb : 0 < b) (i : ℕ) {T M : ℝ} (hM : 0 ≤ M) :
    epsS b i * (2 ^ (i + 1) * T + M) ≤ (2 * T + M) / b ^ 6 * (((i : ℝ) + 20) / 2 ^ i) := by
  unfold epsS
  rw [four_pow_eq, pow_succ (2 : ℝ) i]
  have h2 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hb6 : 0 < b ^ 6 := by positivity
  have e1 : ((i : ℝ) + 20) / (b ^ 6 * (2 ^ i * 2 ^ i)) * (2 ^ i * 2 * T + M) =
      ((i : ℝ) + 20) * (2 * T) / (b ^ 6 * 2 ^ i) + ((i : ℝ) + 20) * M / (b ^ 6 * 2 ^ i) / 2 ^ i := by
    field_simp
  have e2 : (2 * T + M) / b ^ 6 * (((i : ℝ) + 20) / 2 ^ i) =
      ((i : ℝ) + 20) * (2 * T) / (b ^ 6 * 2 ^ i) + ((i : ℝ) + 20) * M / (b ^ 6 * 2 ^ i) := by
    field_simp
  rw [e1, e2]
  have : ((i : ℝ) + 20) * M / (b ^ 6 * 2 ^ i) / 2 ^ i ≤ ((i : ℝ) + 20) * M / (b ^ 6 * 2 ^ i) :=
    div_le_self (by positivity) h2
  linarith

lemma sum_epsS_le {b : ℝ} (hb : 0 < b) (n : ℕ) {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) :
    ∑ i ∈ range n, epsS b i * (2 ^ (i + 1) * T + M) ≤ 42 * (2 * T + M) / b ^ 6 := by
  calc ∑ i ∈ range n, epsS b i * (2 ^ (i + 1) * T + M)
      ≤ ∑ i ∈ range n, (2 * T + M) / b ^ 6 * (((i : ℝ) + 20) / 2 ^ i) :=
        Finset.sum_le_sum fun i _ => epsS_mul_le hb i hM
    _ = (2 * T + M) / b ^ 6 * ∑ i ∈ range n, (((i : ℝ) + 20) / 2 ^ i) := by rw [Finset.mul_sum]
    _ ≤ (2 * T + M) / b ^ 6 * 42 := mul_le_mul_of_nonneg_left (sum_geom_le n) (by positivity)
    _ = 42 * (2 * T + M) / b ^ 6 := by ring

/-- `G = |D|²W`, with `|D|² ≤ S₁²` on the far weight. -/
def tailG (N : ℕ) (c : ℕ → ℝ) (b T : ℝ) (J : ℕ) (t : ℝ) : ℝ :=
  1 / 256 * (Kc N c t * majR (T / 8) t)
    + ∑ i ∈ range (2 * J), epsS b i * (Kc N c t * majR (2 ^ (i + 1) * T) t)
    + 21 * T * Real.sqrt T / b ^ 6 * S1 N c ^ 2 * farW (4 ^ J * T) t

lemma Kc_tailW_le (N : ℕ) (c : ℕ → ℝ) {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) (J : ℕ) (t : ℝ) :
    Kc N c t * tailW b T J t ≤ tailG N c b T J t := by
  unfold tailW tailG
  have hK := Kc_le N c t
  have hF := farW_nonneg (R := 4 ^ J * T) (by positivity) t
  have h1 : Kc N c t * (1 / 256 * majR (T / 8) t) = 1 / 256 * (Kc N c t * majR (T / 8) t) := by ring
  have h2 : Kc N c t * ∑ i ∈ range (2 * J), epsS b i * majR (2 ^ (i + 1) * T) t =
      ∑ i ∈ range (2 * J), epsS b i * (Kc N c t * majR (2 ^ (i + 1) * T) t) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hc : 0 ≤ 21 * T * Real.sqrt T / b ^ 6 * farW (4 ^ J * T) t := mul_nonneg (by positivity) hF
  have h3 : Kc N c t * (21 * T * Real.sqrt T / b ^ 6 * farW (4 ^ J * T) t) ≤
      21 * T * Real.sqrt T / b ^ 6 * S1 N c ^ 2 * farW (4 ^ J * T) t := by
    calc Kc N c t * (21 * T * Real.sqrt T / b ^ 6 * farW (4 ^ J * T) t)
        = 21 * T * Real.sqrt T / b ^ 6 * farW (4 ^ J * T) t * Kc N c t := by ring
      _ ≤ 21 * T * Real.sqrt T / b ^ 6 * farW (4 ^ J * T) t * S1 N c ^ 2 := mul_le_mul_of_nonneg_left hK hc
      _ = _ := by ring
  rw [mul_add, mul_add, h1, h2]
  linarith

lemma integrable_tailG (N : ℕ) (c : ℕ → ℝ) (b : ℝ) {T : ℝ} (hT : 0 < T) (J : ℕ) :
    Integrable (tailG N c b T J) :=
  (((integrable_Kc_majR N c (by positivity)).const_mul _).add
    (integrable_finsetSum _ fun i _ => (integrable_Kc_majR N c (by positivity)).const_mul _)).add
    ((integrable_farW (by positivity)).const_mul _)

/-- **The mass of the defect**: `∫G ≤ (π²/2)((T/8 + 8N)/256 + 42(2T + 8N)/b⁶)Σc_n² + 84T S₁²/(b⁶2^J)`. -/
lemma integral_tailG_le {N : ℕ} (c : ℕ → ℝ) {b T : ℝ} (hb : 0 < b) (hT : 64 ≤ T) (J : ℕ) :
    ∫ t, tailG N c b T J t ≤
      π ^ 2 / 2 * ((T / 8 + 8 * N) / 256 + 42 * (2 * T + 8 * N) / b ^ 6) * S2 N c
        + 84 * T * S1 N c ^ 2 / (b ^ 6 * 2 ^ J) := by
  have hT0 : 0 < T := by linarith
  have i1 : Integrable fun t => 1 / 256 * (Kc N c t * majR (T / 8) t) :=
    (integrable_Kc_majR N c (by positivity)).const_mul _
  have i2 : Integrable fun t => ∑ i ∈ range (2 * J), epsS b i * (Kc N c t * majR (2 ^ (i + 1) * T) t) :=
    integrable_finsetSum _ fun i _ => (integrable_Kc_majR N c (by positivity)).const_mul _
  have i12 : Integrable fun t => 1 / 256 * (Kc N c t * majR (T / 8) t)
      + ∑ i ∈ range (2 * J), epsS b i * (Kc N c t * majR (2 ^ (i + 1) * T) t) := i1.add i2
  have i3 : Integrable fun t => 21 * T * Real.sqrt T / b ^ 6 * S1 N c ^ 2 * farW (4 ^ J * T) t :=
    (integrable_farW (by positivity)).const_mul _
  unfold tailG
  rw [integral_add i12 i3, integral_add i1 i2,
    integral_finsetSum _ fun i _ => (integrable_Kc_majR N c (by positivity)).const_mul _]
  simp only [integral_const_mul]
  rw [integral_farW (by positivity)]
  have h0 := integral_Kc_majR_le' (N := N) (by linarith : 8 ≤ T / 8) c
  have hS2 := S2_nonneg N c
  have hsh : ∑ i ∈ range (2 * J), epsS b i * ∫ t, Kc N c t * majR (2 ^ (i + 1) * T) t ≤
      π ^ 2 / 2 * (42 * (2 * T + 8 * N) / b ^ 6) * S2 N c := by
    calc ∑ i ∈ range (2 * J), epsS b i * ∫ t, Kc N c t * majR (2 ^ (i + 1) * T) t
        ≤ ∑ i ∈ range (2 * J), epsS b i * (π ^ 2 / 2 * (2 ^ (i + 1) * T + 8 * N) * S2 N c) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (integral_Kc_majR_le' ?_ c) (epsS_nonneg hb i)
          have : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ (by norm_num)
          nlinarith
      _ = π ^ 2 / 2 * S2 N c * ∑ i ∈ range (2 * J), epsS b i * (2 ^ (i + 1) * T + 8 * N) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ π ^ 2 / 2 * S2 N c * (42 * (2 * T + 8 * N) / b ^ 6) :=
          mul_le_mul_of_nonneg_left (sum_epsS_le hb _ hT0.le (by positivity)) (by positivity)
      _ = _ := by ring
  have hfar : 21 * T * Real.sqrt T / b ^ 6 * S1 N c ^ 2 * (4 / Real.sqrt (4 ^ J * T)) =
      84 * T * S1 N c ^ 2 / (b ^ 6 * 2 ^ J) := by
    rw [Real.sqrt_mul (by positivity), show (4 : ℝ) ^ J = (2 ^ J) ^ 2 by
      rw [← pow_mul, mul_comm J 2, pow_mul]; norm_num, Real.sqrt_sq (by positivity)]
    have : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
    field_simp
    ring
  rw [hfar]
  have h0' := mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ 1 / 256)
  linarith

/-! ## The archimedean term -/

lemma integrable_hRC {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (N : ℕ) (c : ℕ → ℝ) :
    Integrable (hRC N c b T) := by
  have h := integrable_Kc_mul_cos N c (integrable_phiR_cos hb hT) 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  exact h

lemma integrable_hRC_psi {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (hbT : b ≤ T) (N : ℕ) (c : ℕ → ℝ) :
    Integrable (fun r => hRC N c b T r * psiRe r) := by
  refine (integrable_psi_real (striptest_htC hb hT hbT N c)).re.congr
    (Filter.Eventually.of_forall fun r => ?_)
  show RCLike.re (htC N c b T r * Complex.digamma (zB r)) = hRC N c b T r * psiRe r
  rw [htC_ofReal hb hT]
  simp [psiRe]

/-- **The archimedean term**: `−g_h(0)log π + (1/2π)∫h Re ψ ≥ (1/2π)(L₁Φ̂(0)Σc_n² − ∫G)`. -/
lemma arch_ge_cut {b T : ℝ} (hb : 0 < b) (hT : 64 ≤ T) (hbT : b ≤ T) (hbig : 16384 * (L1 T + 9) ≤ T ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (h12 : 12 * b * N < T) (c : ℕ → ℝ) (J : ℕ) :
    1 / (2 * π) * (L1 T * phihat b T 0 * S2 N c - ∫ t, tailG N c b T J t) ≤
      -(gh (hRC N c b T) 0 * Real.log π) + 1 / (2 * π) * ∫ r, hRC N c b T r * psiRe r := by
  have hT0 : 0 < T := by linarith
  have hiR := integrable_hRC hb hT0 N c
  have hiP := integrable_hRC_psi hb hT0 hbT N c
  have hiG := integrable_tailG N c b hT0 J
  have hpt : ∀ r, L1 T * hRC N c b T r - tailG N c b T J r ≤
      hRC N c b T r * psiRe r - Real.log π * hRC N c b T r := by
    intro r
    have h1 := phiR_mul_L_ge hb hT hbig J r
    have h2 := Kc_tailW_le N c hb hT0.le J r
    have h3 := mul_le_mul_of_nonneg_left h1 (Kc_nonneg N c r)
    unfold hRC
    nlinarith
  have hint : ∫ r, (L1 T * hRC N c b T r - tailG N c b T J r) ≤
      ∫ r, (hRC N c b T r * psiRe r - Real.log π * hRC N c b T r) :=
    integral_mono ((hiR.const_mul (L1 T)).sub hiG) (hiP.sub (hiR.const_mul (Real.log π))) hpt
  rw [integral_sub (hiR.const_mul _) hiG, integral_sub hiP (hiR.const_mul _), integral_const_mul,
    integral_const_mul, integral_hRC hb hT0 hN h12] at hint
  have hgh0 : gh (hRC N c b T) 0 = 1 / (2 * π) * ∫ r, hRC N c b T r := by
    unfold gh; simp only [mul_zero, Real.cos_zero, mul_one]
  rw [hgh0, integral_hRC hb hT0 hN h12]
  have hpi : 0 < 1 / (2 * π) := by positivity
  have := mul_le_mul_of_nonneg_left hint hpi.le
  linarith

/-! ## The pole and the zero side -/

/-- **The pole term**: `Re(h(i/2) + h(−i/2)) ≥ −2(N S₁)²‖Φ(i/2)‖`. -/
lemma pole_ge_cut {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (N : ℕ) (c : ℕ → ℝ) :
    -(2 * (N * S1 N c) ^ 2 * ‖phiC b T (I / 2)‖) ≤ (htC N c b T (I / 2) + htC N c b T (-(I / 2))).re := by
  rw [htC_even hb hT, ← two_mul]
  have h1 : ‖htC N c b T (I / 2)‖ ≤ (N * S1 N c) ^ 2 * ‖phiC b T (I / 2)‖ := by
    unfold htC
    rw [norm_mul, norm_mul]
    have hd1 := norm_DC_le N c (z := I / 2) (by norm_num)
    have hd2 := norm_DC_le N c (z := -(I / 2)) (by norm_num)
    have hS := S1_nonneg N c
    calc ‖DC N c (I / 2)‖ * ‖DC N c (-(I / 2))‖ * ‖phiC b T (I / 2)‖
        ≤ (N * S1 N c) * (N * S1 N c) * ‖phiC b T (I / 2)‖ := by gcongr
      _ = _ := by ring
  have h2 := Complex.abs_re_le_norm (2 * htC N c b T (I / 2))
  rw [norm_mul, Complex.norm_two] at h2
  have h3 := neg_abs_le (2 * htC N c b T (I / 2)).re
  linarith

/-- Under RH, `h(t_ρ) = |V_x(ρ)|²Φ(γ)` with the coefficients `c_n = x_n√n`. -/
lemma zero_term_cut (hRH : RiemannHypothesis) {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (N : ℕ) (x : ℕ → ℝ)
    (q : ZIdx) :
    htC N (fun n => x n * Real.sqrt n) b T ((zetaZeroFamily q - 1 / 2) / I) =
      ((‖BallRate.dpoly N x q‖ ^ 2 * phiR b T (zetaZeroFamily q).im : ℝ) : ℂ) := by
  have ht : (zetaZeroFamily q - 1 / 2) / I = ((zetaZeroFamily q).im : ℂ) := by
    rw [BallHadamard.zZF_sub_half hRH q, mul_div_cancel_left₀ _ Complex.I_ne_zero]
  rw [ht, htC_ofReal hb hT]
  congr 1
  unfold hRC
  rw [BallSampling.dpoly_eq_conj hRH, Complex.norm_conj, dp_eq_DC, norm_DC_ofReal_sq]

/-- **The zero side**: `Σ_ρ |V_x(ρ)|²Φ(γ) ≤ ¼Σ_{|γ| ≤ T}|V_x(ρ)|²`, as `Φ ≤ ¼` on `[−T, T]` and `Φ ≤ 0` off it. -/
lemma zero_side_cut {b T : ℝ} (hb : 0 < b) (hT : 0 < T) (N : ℕ) (x : ℕ → ℝ) {Z : ℝ}
    (hZ : HasSum (fun q => ‖BallRate.dpoly N x q‖ ^ 2 * phiR b T (zetaZeroFamily q).im) Z) :
    Z ≤ 1 / 4 * ∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 := by
  classical
  have hF : HasSum (fun q => if q ∈ BallRate.zerosUpTo T then 1 / 4 * ‖BallRate.dpoly N x q‖ ^ 2 else 0)
      (∑ q ∈ BallRate.zerosUpTo T,
        if q ∈ BallRate.zerosUpTo T then 1 / 4 * ‖BallRate.dpoly N x q‖ ^ 2 else 0) :=
    hasSum_sum_of_ne_finset_zero fun q hq => by simp [hq]
  rw [Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum] at hF
  refine hasSum_le (fun q => ?_) hZ hF
  by_cases hq : q ∈ BallRate.zerosUpTo T
  · rw [ite_eq_left hq]
    obtain ⟨-, -, h14⟩ := phiR_bounds hb hT (BallRate.mem_zerosUpTo.1 hq)
    calc ‖BallRate.dpoly N x q‖ ^ 2 * phiR b T (zetaZeroFamily q).im ≤ ‖BallRate.dpoly N x q‖ ^ 2 * (1 / 4) :=
          mul_le_mul_of_nonneg_left h14 (sq_nonneg _)
      _ = _ := by ring
  · rw [ite_eq_right hq]
    have h : T < |(zetaZeroFamily q).im| := by
      rw [BallRate.mem_zerosUpTo] at hq; push Not at hq; exact hq
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (phiR_tail hb hT h.le).1

/-- Cauchy–Schwarz: `(Σ|c_n|)² ≤ NΣc_n²`. -/
lemma S1_sq_le (N : ℕ) (c : ℕ → ℝ) : S1 N c ^ 2 ≤ N * S2 N c := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) (fun _ => (1 : ℝ)) (fun j => |c j|)
  simp only [one_mul, one_pow, Finset.sum_const, Nat.card_Icc, sq_abs, nsmul_eq_mul, mul_one,
    Nat.add_sub_cancel] at h
  unfold BallDensity.S1 BallDensity.S2
  exact h

/-! ## Sampling and the rate -/

lemma ten_pow_le_exp : (10 : ℝ) ^ 10 ≤ Real.exp 24 := by
  have h1 : Real.exp 24 = Real.exp 1 ^ 24 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  have h2 := Real.exp_one_gt_d9
  calc (10 : ℝ) ^ 10 ≤ 2.7 ^ 24 := by norm_num
    _ ≤ Real.exp 1 ^ 24 := pow_le_pow_left₀ (by norm_num) (by linarith) 24

/-- `‖Φ(i/2)‖ ≤ 1/T²` at `b = 6`, `T ≥ 64`. -/
lemma phiC_I_half_le {T : ℝ} (hT : 64 ≤ T) : ‖phiC 6 T (I / 2)‖ ≤ 1 / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  refine (norm_phiC_I_half (by norm_num) hT0).trans ?_
  have hx0 : 0 ≤ 3 * (6 / T) := by positivity
  have hx1 : 3 * (6 / T) ≤ 1 / 2 := by
    rw [show 3 * (6 / T) = 18 / T by ring, div_le_iff₀ hT0]; linarith
  have hexp : Real.exp (3 * (6 / T)) ≤ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := 3 * (6 / T)) (by rw [abs_of_nonneg hx0]; linarith)
    have := (abs_le.1 h).2
    nlinarith only [this, hx0, hx1]
  have e : (6 / T) ^ 2 / (4 * 6 ^ 2) + (6 / T) ^ 4 / (16 * 6 ^ 4) = 1 / (4 * T ^ 2) + 1 / (16 * T ^ 4) := by
    field_simp
  rw [e]
  have h4 : 1 / (16 * T ^ 4) ≤ 1 / (4 * T ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) ≤ T ^ 2 := by nlinarith only [hT]
    nlinarith only [this]
  have hpos : 0 ≤ 1 / (4 * T ^ 2) + 1 / (16 * T ^ 4) := by positivity
  calc Real.exp (3 * (6 / T)) * (1 / (4 * T ^ 2) + 1 / (16 * T ^ 4))
      ≤ 2 * (1 / (4 * T ^ 2) + 1 / (4 * T ^ 2)) := mul_le_mul hexp (by linarith) hpos (by norm_num)
    _ = 1 / T ^ 2 := by field_simp; ring

/-- **The pole term is `O(N Σc_n²)`**: `Re(h(i/2) + h(−i/2)) ≥ −2NΣc_n²` for `N ≤ T`, `T ≥ 64`. -/
lemma pole_ge_N {T : ℝ} (hT : 64 ≤ T) {N : ℕ} (hNT : (N : ℝ) ≤ T) (c : ℕ → ℝ) :
    -(2 * (N * S2 N c)) ≤ (htC N c 6 T (I / 2) + htC N c 6 T (-(I / 2))).re := by
  have hT0 : 0 < T := by linarith
  refine le_trans ?_ (pole_ge_cut (by norm_num) hT0 N c)
  have hS1 := S1_sq_le N c
  have hS2n := S2_nonneg N c
  have hNT2 : (N : ℝ) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg N) hNT 2
  have h1 : (N * S1 N c) ^ 2 * ‖phiC 6 T (I / 2)‖ ≤ (N * S1 N c) ^ 2 * (1 / T ^ 2) :=
    mul_le_mul_of_nonneg_left (phiC_I_half_le hT) (sq_nonneg _)
  have h2 : (N * S1 N c) ^ 2 * (1 / T ^ 2) ≤ N * S2 N c := by
    rw [mul_one_div, div_le_iff₀ (by positivity), mul_pow]
    calc (N : ℝ) ^ 2 * S1 N c ^ 2 ≤ N ^ 2 * (N * S2 N c) := mul_le_mul_of_nonneg_left hS1 (by positivity)
      _ = N * S2 N c * N ^ 2 := by ring
      _ ≤ N * S2 N c * T ^ 2 := mul_le_mul_of_nonneg_left hNT2 (by positivity)
  linarith

/-- **The defect at `b = 6`**: `(1/2π)∫G ≤ 0.7854((T/8 + 8N)/256 + 42(2T + 8N)/6⁶)Σc_n² + 10⁻⁶TΣc_n²`, given
`2^J ≥ 2¹⁰N`. -/
lemma defect_le {T : ℝ} (hT : 64 ≤ T) {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {J : ℕ} (hJ2 : (N : ℝ) * 1024 ≤ 2 ^ J) :
    1 / (2 * π) * ∫ t, tailG N c 6 T J t ≤
      0.7854 * ((T / 8 + 8 * N) / 256 + 42 * (2 * T + 8 * N) / 46656) * S2 N c
        + 1 / 1000000 * (T * S2 N c) := by
  have hT0 : 0 < T := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hS1 := S1_sq_le N c
  have hS2n := S2_nonneg N c
  have hU : 0 ≤ T * S2 N c := mul_nonneg hT0.le hS2n
  have hG := integral_tailG_le (N := N) c (by norm_num : (0 : ℝ) < 6) hT J
  have h66 : (6 : ℝ) ^ 6 = 46656 := by norm_num
  rw [h66] at hG
  have hG1 : 1 / (2 * π) * ∫ t, tailG N c 6 T J t ≤
      π / 4 * ((T / 8 + 8 * N) / 256 + 42 * (2 * T + 8 * N) / 46656) * S2 N c
        + 42 * T * S1 N c ^ 2 / (π * 46656 * 2 ^ J) := by
    have h := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
    have e : 1 / (2 * π) * (π ^ 2 / 2 * ((T / 8 + 8 * N) / 256 + 42 * (2 * T + 8 * N) / 46656) * S2 N c
        + 84 * T * S1 N c ^ 2 / (46656 * 2 ^ J)) =
        π / 4 * ((T / 8 + 8 * N) / 256 + 42 * (2 * T + 8 * N) / 46656) * S2 N c
          + 42 * T * S1 N c ^ 2 / (π * 46656 * 2 ^ J) := by
      field_simp; ring
    linarith only [h, e]
  have hQ : π / 4 * ((T / 8 + 8 * N) / 256 + 42 * (2 * T + 8 * N) / 46656) * S2 N c ≤
      0.7854 * ((T / 8 + 8 * N) / 256 + 42 * (2 * T + 8 * N) / 46656) * S2 N c := by
    have hq : 0 ≤ ((T / 8 + 8 * N) / 256 + 42 * (2 * T + 8 * N) / 46656) * S2 N c := by positivity
    have hpi := Real.pi_lt_d4
    have := mul_le_mul_of_nonneg_right (show π / 4 ≤ 0.7854 by linarith) hq
    linarith only [this]
  have hfar : 42 * T * S1 N c ^ 2 / (π * 46656 * 2 ^ J) ≤ 1 / 1000000 * (T * S2 N c) := by
    have hpi := Real.pi_gt_d2
    calc 42 * T * S1 N c ^ 2 / (π * 46656 * 2 ^ J) ≤ 42 * T * (N * S2 N c) / (3.14 * 46656 * (N * 1024)) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hS1 (by positivity)) (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_right hpi.le (by norm_num)) hJ2 (by positivity) (by positivity)
      _ = 42 / (3.14 * 46656 * 1024) * (T * S2 N c) := by field_simp
      _ ≤ 1 / 1000000 * (T * S2 N c) := mul_le_mul_of_nonneg_right (by norm_num) hU
  linarith only [hG1, hQ, hfar]

/-- **The bound at `b = 6`** (RH): for `N ≥ 1` and `T ≥ 10¹⁰N`, `(T/100)Σc_n² ≤ Σ_{|γ| ≤ T}|V_x(ρ)|²`, `c_n = x_n√n`. -/
theorem cutoff_bound (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : (10 : ℝ) ^ 10 * N ≤ T)
    (hlogTN : 24 + Real.log N ≤ Real.log T) (x : ℕ → ℝ) :
    1 / 100 * T * S2 N (fun n => x n * Real.sqrt n) ≤
      ∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT10 : (10 : ℝ) ^ 10 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hT64 : 64 ≤ T := by linarith
  have hb : (0 : ℝ) < 6 := by norm_num
  have hbT : (6 : ℝ) ≤ T := by linarith
  have h12 : 12 * 6 * (N : ℝ) < T := by linarith
  have hNT : (N : ℝ) ≤ T := by linarith
  have hbig : 16384 * (L1 T + 9) ≤ T ^ 2 := by
    rw [L1_eq hT0]
    have hlT : Real.log T ≤ T := (Real.log_le_sub_one_of_pos hT0).trans (by linarith)
    have hlp : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_left hT10 hT0.le, hlT, hlp, hl2, hT10]
  set c : ℕ → ℝ := fun n => x n * Real.sqrt n with hc
  set J := N + 10 with hJ
  have hJ2 : (N : ℝ) * 1024 ≤ 2 ^ J := by
    rw [hJ, pow_add]
    have : (N : ℝ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self
    norm_num
    linarith
  -- the explicit formula and its terms
  have hsum := (weil_htC hb hT0 hbT N c).2
  have hre := Complex.hasSum_re hsum
  have hterm : ∀ q, (htC N c 6 T ((zetaZeroFamily q - 1 / 2) / I)).re =
      ‖BallRate.dpoly N x q‖ ^ 2 * phiR 6 T (zetaZeroFamily q).im := fun q => by
    rw [hc, zero_term_cut hRH hb hT0 N x q, Complex.ofReal_re]
  simp only [hterm] at hre
  rw [Complex.add_re, Complex.ofReal_re] at hre
  have hZ := zero_side_cut hb hT0 N x hre
  have hpole := pole_ge_N hT64 hNT c
  have harch := arch_ge_cut hb hT64 hbT hbig hN h12 c J
  have hD := defect_le hT64 hN c hJ2
  have hΦ : phihat 6 T 0 = 69 * π * T / 62208 := by rw [phihat_zero hb hT0]; ring
  have hprime := prime_le_cut hb hT0 hN h12 c (by rw [hΦ]; positivity)
  have hS2n := S2_nonneg N c
  have eA : 1 / (2 * π) * (L1 T * phihat 6 T 0 * S2 N c - ∫ t, tailG N c 6 T J t) =
      69 / 124416 * (L1 T * (T * S2 N c)) - 1 / (2 * π) * ∫ t, tailG N c 6 T J t := by
    rw [hΦ]; field_simp; ring
  have eP : phihat 6 T 0 / (2 * π) * (Real.log N + (Real.log 4 + 4)) * S2 N c =
      69 / 124416 * ((Real.log N + (Real.log 4 + 4)) * (T * S2 N c)) := by
    rw [hΦ]; field_simp; ring
  rw [eA] at harch
  rw [eP] at hprime
  have hLL : 11.45 ≤ L1 T - Real.log N - (Real.log 4 + 4) := by
    rw [L1_eq hT0]
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have := log_pi_le
    have hl2 := Real.log_two_lt_d9
    linarith
  have hmainP := mul_le_mul_of_nonneg_left hLL (mul_nonneg hT0.le hS2n)
  have hV : (N : ℝ) * S2 N c ≤ 1 / 10 ^ 10 * (T * S2 N c) := by
    have h : (N : ℝ) ≤ 1 / 10 ^ 10 * T := by linarith
    have := mul_le_mul_of_nonneg_right h hS2n
    linarith only [this]
  linarith only [hZ, hpole, harch, hD, hprime, hmainP, hV, mul_nonneg hT0.le hS2n]

/-- **Sampling at the zeros up to height `T ≍ N`** (RH): `BallRate.SamplingAtZeros (1/100) e²⁴ 0`. For every
`N ≥ 1`, every real `x` on `[1, N]` and every `T ≥ e²⁴N`, `Σ_{|γ_ρ| ≤ T}|Σ_{n ≤ N} x_n n^ρ|² ≥ (T/100)Σ x_n² n`. -/
theorem sampling_rh (hRH : RiemannHypothesis) : BallRate.SamplingAtZeros (1 / 100) (Real.exp 24) 0 := by
  intro N x T hN hT
  rw [add_zero, Real.rpow_one] at hT
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hTN : (10 : ℝ) ^ 10 * N ≤ T :=
    le_trans (mul_le_mul_of_nonneg_right ten_pow_le_exp hN0.le) hT
  have hlogTN : 24 + Real.log N ≤ Real.log T := by
    have h := Real.log_le_log (mul_pos (Real.exp_pos 24) hN0) hT
    rwa [Real.log_mul (Real.exp_pos 24).ne' hN0.ne', Real.log_exp] at h
  have hS2 : ∑ n ∈ Icc 1 N, x n ^ 2 * n = S2 N (fun n => x n * Real.sqrt n) := by
    unfold BallDensity.S2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hS2]
  exact cutoff_bound hRH hN hTN hlogTN x

/-- **The rate under RH**: `λ_N ≥ 1/(200e²⁴N)` for every `N ≥ 1`. -/
theorem rate_cut (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    1 / (200 * Real.exp 24 * N) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x := by
  have hC : (1 : ℝ) ≤ Real.exp 24 := Real.one_le_exp (by norm_num)
  have h := BallRate.rate_of_sampling hRH (by norm_num : (0 : ℝ) < 1 / 100) hC le_rfl (sampling_rh hRH) hN x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : 1 / 100 / (2 * Real.exp 24) * (N : ℝ) ^ (-(1 + 0 : ℝ)) = 1 / (200 * Real.exp 24 * N) := by
    rw [add_zero, Real.rpow_neg_one]
    field_simp
    ring
  rw [e] at h
  exact h

end BallCutoff
