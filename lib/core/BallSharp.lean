import Mathlib
import BallCutoff

/-! # Sampling at the zeros in its natural form: `Σ_{|γ| ≤ T}|V_x(ρ)|² ≥ (T/11)(log(T/N) − 7)Σ x_n² n` under RH

Plain statement. Under RH, for every `N ≥ 1`, every real `x` on `[1, N]` and every `T ≥ 2000N`,
`Σ_{|γ_ρ| ≤ T} |Σ_{n ≤ N} x_n n^ρ|² ≥ (T/11)(log(T/N) − 7)·Σ_{n ≤ N} x_n² n` (`sampling_log`). The sampling mass
grows like `T log(T/N)`, the shape of the Landau–Gonek main term, where `BallCutoff.sampling_rh` has `T/100` from
`T ≥ e²⁴N`. At `T ≥ e¹⁴N` it is at least `(T/22)log(T/N)Σ x_n² n` (`sampling_log_clean`). At `T = e⁸N`, the
best point for the rate, it gives `BallRate.SamplingAtZeros (1/11) e⁸ 0` (`sampling_e8`), and so
`λ_N ≥ 1/(22e⁸N)` (`rate_sharp`), against `BallCutoff.rate_cut`'s `1/(200e²⁴N)`. Keeping Landau's slack
`G(c) = (log N + log 4 + 1)Σc_n² − L(c) ≥ 0` (`landauSlack`), with `c_n = x_n√n`, the frame bound is
`(T/11)((log(T/N) − 7)Σ x_n² n + G(c))` (`sharp_bound_slack`), and `Q_N(x) ≥ (Σ x_n² n + G(c))/(22e⁸N)` (`rate_slack`).

The proof is `BallCutoff`'s, with four changes.

- **The minorant** is `Φ(r) = (r/T)²(1 − (r/T)²)sinc⁶(3r/T)`, at `b = 3` in place of `6`. Its mass `5πT/648` is
  seven times `BallCutoff`'s, and on `[−T, T]` it stays below `1/25` (`phiR3_le`): `sinc θ ≤ 1/(1 + θ²/6)` on
  `[0, 3]` from the Taylor bound `sin θ ≤ θ − θ³/6 + θ⁵/120`.
- **Stirling with two terms of the recurrence**: `|Re ψ(¼ + it/2) − log(|t|/2)| ≤ 21/(2t²) + 1/3000` for `|t| ≥ 8`
  (`psiRe_near`), from `DigammaStirling.re_digamma_quarter 2`.
- **The archimedean tail by Fejér smoothing.** With `F` the Fejér kernel of transform `(1 − N|v|)⁺`, `|D|² ⋆ F` is
  the constant `Σc_n²` (`Kc_conv_fej`): the frequencies `log j' − log j` are at least `1/N` apart. So any weight
  dominated by `E ⋆ F` has `|D|²`-mass at most `Σc_n²·∫E` (`integral_Kc_conv`), with no loss. The tail weight is
  dominated by such a convolution once `E` majorises it on the windows `|u| ≤ T/10` (`conv_ge`, `tail_conv_le`).
- **Mertens' bound with the constant `log 4 + 1`** (`BallDensity.mertens_le_sharp`, from Stirling's bound for
  `log M!`), in place of `log 4 + 4`, in the bound for Landau's form (`BallDensity.landau_le_sharp`).
-/

open Real Complex Finset MeasureTheory WeilForm WeilTest DirMean BallDensity ShortWeil BallCutoff
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace BallSharp

/-! ## Taylor bounds for sine and cosine, and the height of the minorant -/

lemma cos_le_quartic {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) : ℝ := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv (t : ℝ) : deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have := Real.sin_ge_sub_cube (le_of_lt ht)
    linarith
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [f, Real.cos_zero] at h
  linarith

lemma sin_le_quintic {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f (t : ℝ) : ℝ := t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hderiv (t : ℝ) : deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have := cos_le_quartic (le_of_lt ht)
    linarith
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [f, Real.sin_zero] at h
  linarith

/-- `sinc θ ≤ 1/(1 + θ²/6)` for `0 < θ`, `θ² ≤ 14`. -/
lemma sinc_le {θ : ℝ} (h0 : 0 < θ) (h14 : θ ^ 2 ≤ 14) : Real.sin θ / θ ≤ 1 / (1 + θ ^ 2 / 6) := by
  have hs := sin_le_quintic h0.le
  rw [div_le_div_iff₀ h0 (by positivity)]
  have h1 : Real.sin θ * (1 + θ ^ 2 / 6) ≤ (θ - θ ^ 3 / 6 + θ ^ 5 / 120) * (1 + θ ^ 2 / 6) :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  have h2 : 0 ≤ θ ^ 5 * (14 - θ ^ 2) := mul_nonneg (pow_pos h0 5).le (by linarith)
  nlinarith [h1, h2]

lemma poly_A {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : v * (1 - v) ≤ 1 / 25 * (1 + 3 * v / 2) ^ 6 := by
  nlinarith [sq_nonneg (v - 1 / 9), mul_nonneg hv0 (sq_nonneg (v - 1 / 9)), pow_nonneg hv0 3,
    pow_nonneg hv0 4, pow_nonneg hv0 5, pow_nonneg hv0 6, mul_nonneg hv0 (sub_nonneg.2 hv1)]

/-- **The height of the minorant at `b = 3`**: `Φ ≤ 1/25` on `[−T, T]`. -/
lemma phiR3_le {T : ℝ} (hT : 0 < T) {r : ℝ} (hr : |r| ≤ T) : phiR 3 T r ≤ 1 / 25 := by
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [phiR_zero]; norm_num
  rw [phiR_eq (by norm_num) hT hr0]
  set θ := 3 / T * r with hθ
  have hθ0 : θ ≠ 0 := mul_ne_zero (div_ne_zero (by norm_num) hT.ne') hr0
  have hθ3 : |θ| ≤ 3 := by
    rw [hθ, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 / T)]
    calc 3 / T * |r| ≤ 3 / T * T := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 3 := by field_simp
  set a := |θ| with ha
  have ha0 : 0 < a := abs_pos.2 hθ0
  have hsin6 : Real.sin θ ^ 6 = Real.sin a ^ 6 := by
    rcases le_or_gt 0 θ with h | h
    · rw [ha, abs_of_nonneg h]
    · rw [ha, abs_of_neg h, Real.sin_neg]; ring
  have hθ2 : θ ^ 2 = a ^ 2 := (sq_abs θ).symm
  have hθ4 : θ ^ 4 = a ^ 4 := by
    rw [show θ ^ 4 = (θ ^ 2) ^ 2 by ring, hθ2]; ring
  rw [hsin6, hθ4, hθ2]
  have ha3 : a ≤ 3 := hθ3
  have hsinc := sinc_le ha0 (by nlinarith)
  have hsin0 : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha0.le (by linarith [Real.pi_gt_three])
  set s := Real.sin a / a with hs
  have hsa : Real.sin a = s * a := by rw [hs]; field_simp
  have hs0 : 0 ≤ s := div_nonneg hsin0 ha0.le
  rw [hsa]
  set v := a ^ 2 / 9 with hv
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 := by rw [hv, div_le_one (by norm_num)]; nlinarith
  have e : (s * a) ^ 6 / (3 ^ 2 * a ^ 4) * (1 - a ^ 2 / 3 ^ 2) = s ^ 6 * (v * (1 - v)) := by
    rw [hv]; field_simp; ring
  rw [e]
  have hsinc' : s ≤ 1 / (1 + 3 * v / 2) := by
    rw [hv, show 3 * (a ^ 2 / 9) / 2 = a ^ 2 / 6 by ring]; exact hsinc
  have hs6 : s ^ 6 ≤ (1 / (1 + 3 * v / 2)) ^ 6 := pow_le_pow_left₀ hs0 hsinc' 6
  have hvv : 0 ≤ v * (1 - v) := mul_nonneg hv0 (by linarith)
  have hpos : 0 < (1 + 3 * v / 2) ^ 6 := by positivity
  calc s ^ 6 * (v * (1 - v)) ≤ (1 / (1 + 3 * v / 2)) ^ 6 * (v * (1 - v)) := mul_le_mul_of_nonneg_right hs6 hvv
    _ = v * (1 - v) / (1 + 3 * v / 2) ^ 6 := by rw [div_pow, one_pow]; ring
    _ ≤ 1 / 25 := by rw [div_le_iff₀ hpos]; linarith [poly_A hv0 hv1]

/-! ## Stirling with two terms of the recurrence -/

lemma psiApx2_eq (b : ℝ) : DigammaStirling.psiApx 2 b =
    Real.log ((9 / 4) ^ 2 + b ^ 2) / 2 - 9 / 4 / (2 * ((9 / 4) ^ 2 + b ^ 2))
      - ((9 / 4) ^ 2 - b ^ 2) / (12 * ((9 / 4) ^ 2 + b ^ 2) ^ 2)
      - (1 / 4 / ((1 / 4) ^ 2 + b ^ 2) + 5 / 4 / ((5 / 4) ^ 2 + b ^ 2)) := by
  unfold DigammaStirling.psiApx
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, zero_add]
  norm_num

/-- **Stirling, two-sided**: `|Re ψ(¼ + it/2) − log(|t|/2)| ≤ 21/(2t²) + 1/3000` for `|t| ≥ 8`. -/
lemma psiRe_near {t : ℝ} (ht : 8 ≤ |t|) :
    Real.log (|t| / 2) - (21 / (2 * t ^ 2) + 1 / 3000) ≤ psiRe t ∧
      psiRe t ≤ Real.log (|t| / 2) + (21 / (2 * t ^ 2) + 1 / 3000) := by
  have hq := DigammaStirling.re_digamma_quarter 2 (t / 2)
  have e : psiRe t = (Complex.digamma (1 / 4 + ((t / 2 : ℝ) : ℂ) * Complex.I)).re := by
    unfold psiRe; rw [zB_eq]
  rw [← e, psiApx2_eq] at hq
  have herr : (1 : ℝ) / (120 * (((2 : ℕ) : ℝ) + 1 / 4) ^ 4) ≤ 1 / 3000 := by norm_num
  set b := t / 2 with hbdef
  have ht2 : 64 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have hb2 : 16 ≤ b ^ 2 := by rw [hbdef, div_pow]; linarith
  have hb0 : 0 < b ^ 2 := by linarith
  set r := (9 / 4 : ℝ) ^ 2 + b ^ 2 with hr
  have hr0 : 0 < r := by positivity
  have hrb : b ^ 2 ≤ r := by rw [hr]; nlinarith
  -- log terms: log r / 2 − log(|t|/2) = log(r/b²)/2 ∈ [0, 81/(32 b²)]
  have hlogt : Real.log (|t| / 2) = Real.log (b ^ 2) / 2 := by
    rw [hbdef, div_pow, show |t| / 2 = Real.sqrt (t ^ 2 / 2 ^ 2) by
      rw [Real.sqrt_div' _ (by norm_num), Real.sqrt_sq_eq_abs, Real.sqrt_sq (by norm_num)]]
    rw [Real.log_sqrt (by positivity)]
  have hl1 : Real.log (b ^ 2) ≤ Real.log r := Real.log_le_log hb0 hrb
  have hl2 : Real.log r - Real.log (b ^ 2) ≤ 81 / (16 * b ^ 2) := by
    rw [← Real.log_div hr0.ne' hb0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hr0 hb0)
    have e2 : r / b ^ 2 - 1 = 81 / (16 * b ^ 2) := by
      rw [hr, div_sub_one hb0.ne', add_sub_cancel_right]; ring
    linarith
  -- the rational terms
  set X := 1 / b ^ 2 with hX
  have hX0 : 0 < X := by positivity
  have hinv : 1 / r ≤ X := by rw [hX]; exact one_div_le_one_div_of_le hb0 hrb
  have t1 : 0 ≤ 9 / 4 / (2 * r) ∧ 9 / 4 / (2 * r) ≤ 9 / 8 * X := by
    refine ⟨by positivity, ?_⟩
    calc 9 / 4 / (2 * r) = 9 / 8 * (1 / r) := by field_simp; ring
      _ ≤ 9 / 8 * X := mul_le_mul_of_nonneg_left hinv (by norm_num)
  have t2 : 0 ≤ -(((9 / 4 : ℝ) ^ 2 - b ^ 2) / (12 * r ^ 2)) ∧
      -(((9 / 4 : ℝ) ^ 2 - b ^ 2) / (12 * r ^ 2)) ≤ 1 / 12 * X := by
    constructor
    · rw [neg_nonneg]; apply div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    · have hr2 : 0 < r ^ 2 := by positivity
      calc -(((9 / 4 : ℝ) ^ 2 - b ^ 2) / (12 * r ^ 2)) = (b ^ 2 - (9 / 4) ^ 2) / (12 * r ^ 2) := by ring
        _ ≤ b ^ 2 / (12 * r ^ 2) := div_le_div_of_nonneg_right (by nlinarith) (by positivity)
        _ = 1 / 12 * (b ^ 2 / r ^ 2) := by rw [div_mul_div_comm, one_mul]
        _ ≤ 1 / 12 * X := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [hX, div_le_div_iff₀ hr2 hb0]
          nlinarith [mul_le_mul hrb hrb hb0.le hr0.le]
  have t3 : 0 ≤ 1 / 4 / ((1 / 4 : ℝ) ^ 2 + b ^ 2) + 5 / 4 / ((5 / 4 : ℝ) ^ 2 + b ^ 2) ∧
      1 / 4 / ((1 / 4 : ℝ) ^ 2 + b ^ 2) + 5 / 4 / ((5 / 4 : ℝ) ^ 2 + b ^ 2) ≤ 3 / 2 * X := by
    refine ⟨by positivity, ?_⟩
    have u1 : 1 / 4 / ((1 / 4 : ℝ) ^ 2 + b ^ 2) ≤ 1 / 4 * X := by
      calc 1 / 4 / ((1 / 4 : ℝ) ^ 2 + b ^ 2) ≤ 1 / 4 / b ^ 2 :=
            div_le_div_of_nonneg_left (by norm_num) hb0 (by nlinarith)
        _ = 1 / 4 * X := by rw [hX]; ring
    have u2 : 5 / 4 / ((5 / 4 : ℝ) ^ 2 + b ^ 2) ≤ 5 / 4 * X := by
      calc 5 / 4 / ((5 / 4 : ℝ) ^ 2 + b ^ 2) ≤ 5 / 4 / b ^ 2 :=
            div_le_div_of_nonneg_left (by norm_num) hb0 (by nlinarith)
        _ = 5 / 4 * X := by rw [hX]; ring
    linarith
  have hXt : X = 4 / t ^ 2 := by rw [hX, hbdef, div_pow]; field_simp; norm_num
  have h21 : 21 / (2 * t ^ 2) = 21 / 8 * X := by rw [hXt]; field_simp; norm_num
  have hl81 : 81 / (16 * b ^ 2) = 81 / 16 * X := by rw [hX]; field_simp
  have hq' := abs_le.1 hq
  rw [hlogt, h21]
  constructor <;> linarith [hq'.1, hq'.2, herr, hl1, hl2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, hl81]

/-! ## The archimedean weight against `L₁ = log(T/8π) − ε₁` -/

/-- The Stirling error on `|t| ≥ 32`. -/
def eps1 : ℝ := 21 / (2 * 32 ^ 2) + 1 / 3000

lemma eps1_nonneg : 0 ≤ eps1 := by unfold eps1; norm_num

lemma eps_le {t : ℝ} (ht : 32 ≤ |t|) : 21 / (2 * t ^ 2) + 1 / 3000 ≤ eps1 := by
  unfold eps1
  have h : (32 : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have : 21 / (2 * t ^ 2) ≤ 21 / (2 * 32 ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  linarith

lemma log_div_two_pi {t : ℝ} (ht : 0 < |t|) : Real.log (|t| / (2 * π)) = Real.log (|t| / 2) - Real.log π := by
  rw [show |t| / (2 * π) = |t| / 2 / π by field_simp, Real.log_div (by positivity) Real.pi_ne_zero]

lemma L_lower {t : ℝ} (ht : 32 ≤ |t|) : Real.log (|t| / (2 * π)) - eps1 ≤ psiRe t - Real.log π := by
  have h := (psiRe_near (by linarith : 8 ≤ |t|)).1
  have he := eps_le ht
  rw [log_div_two_pi (by linarith)]
  linarith

lemma L_upper {t : ℝ} (ht : 32 ≤ |t|) : psiRe t - Real.log π ≤ Real.log (|t| / (2 * π)) + eps1 := by
  have h := (psiRe_near (by linarith : 8 ≤ |t|)).2
  have he := eps_le ht
  rw [log_div_two_pi (by linarith)]
  linarith

/-- `L₁ = log(T/8π) − ε₁`, the floor of `L(t) = Re ψ(¼ + it/2) − log π` on `|t| ≥ T/4`. -/
def L1s (T : ℝ) : ℝ := Real.log (T / (8 * π)) - eps1

lemma L1s_le_L {T : ℝ} (hT : 0 < T) {t : ℝ} (ht32 : 32 ≤ |t|) (htT : T / 4 ≤ |t|) :
    L1s T ≤ psiRe t - Real.log π := by
  have h := L_lower ht32
  have hl : Real.log (T / (8 * π)) ≤ Real.log (|t| / (2 * π)) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos]
  unfold L1s; linarith

/-- `w log(1/w) ≤ 1/e`. -/
lemma mul_log_inv_le {w : ℝ} (hw : 0 < w) : w * Real.log (1 / w) ≤ Real.exp (-1) := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 / w * Real.exp (-1) by positivity)
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h
  have h2 : Real.log (1 / w) ≤ 1 / w * Real.exp (-1) := by linarith
  calc w * Real.log (1 / w) ≤ w * (1 / w * Real.exp (-1)) := mul_le_mul_of_nonneg_left h2 hw.le
    _ = Real.exp (-1) := by field_simp

lemma exp_neg_one_le : Real.exp (-1) ≤ 0.3679 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  have := Real.exp_one_gt_d9
  norm_num at this ⊢
  linarith

lemma log_le_lin {T : ℝ} (hT : 2000 ≤ T) : Real.log T ≤ 7 + T / 2000 := by
  have h2000 : Real.log 2000 ≤ 8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h8]
    calc (2000 : ℝ) ≤ 2.718 ^ 8 := by norm_num
      _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
  have h := Real.log_le_sub_one_of_pos (show 0 < T / 2000 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  linarith

/-- The constant of the low-height majorant. -/
def Clow : ℝ := 23 / 2000

/-- **Low heights**: `(t/T)²(L₁ − L(t))⁺ ≤ (23/2000)·M_{T/4}(t)` for `T ≥ 2000`. -/
lemma low_le_s {T : ℝ} (hT : 2000 ≤ T) (t : ℝ) :
    (t / T) ^ 2 * max (L1s T - (psiRe t - Real.log π)) 0 ≤ Clow * majR (T / 4) t := by
  have hT0 : 0 < T := by linarith
  have hM0 := majR_nonneg (T / 4) t
  have hC0 : (0 : ℝ) ≤ Clow := by unfold Clow; norm_num
  rcases le_or_gt (T / 4) |t| with h1 | h1
  · have := L1s_le_L hT0 (by linarith) h1
    rw [max_eq_right (by linarith), mul_zero]
    exact mul_nonneg hC0 hM0
  · have hM1 := one_le_majR (by positivity : 0 < T / 4) h1.le
    have hkey : (t / T) ^ 2 * max (L1s T - (psiRe t - Real.log π)) 0 ≤ Clow := by
      rcases le_or_gt 32 |t| with h2 | h2
      · have hlow := L_lower h2
        have ht0 : 0 < |t| := by linarith
        have hlog : L1s T - (psiRe t - Real.log π) ≤ Real.log (T / (4 * |t|)) := by
          have e : Real.log (T / (4 * |t|)) = Real.log (T / (8 * π)) - Real.log (|t| / (2 * π)) := by
            rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp; ring
          unfold L1s; linarith
        have hpos : 0 ≤ Real.log (T / (4 * |t|)) :=
          Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
        have hmax : max (L1s T - (psiRe t - Real.log π)) 0 ≤ Real.log (T / (4 * |t|)) := max_le hlog hpos
        set y := |t| / T with hy
        have hy0 : 0 < y := by positivity
        have hyT : (t / T) ^ 2 = y ^ 2 := by rw [hy, div_pow, div_pow, sq_abs]
        have hlogy : Real.log (T / (4 * |t|)) = Real.log (1 / (4 * y)) := by
          rw [hy]; congr 1; field_simp
        set w := 16 * y ^ 2 with hw
        have hw0 : 0 < w := by positivity
        have hlw : Real.log (1 / w) = 2 * Real.log (1 / (4 * y)) := by
          rw [hw, show 1 / (16 * y ^ 2) = (1 / (4 * y)) ^ 2 by field_simp; ring, Real.log_pow]; push_cast; ring
        have hml := mul_log_inv_le hw0
        have hexp := exp_neg_one_le
        calc (t / T) ^ 2 * max (L1s T - (psiRe t - Real.log π)) 0 ≤ y ^ 2 * Real.log (1 / (4 * y)) := by
              rw [hyT, ← hlogy]; exact mul_le_mul_of_nonneg_left hmax (sq_nonneg _)
          _ = w * Real.log (1 / w) / 32 := by rw [hlw, hw]; ring
          _ ≤ Clow := by unfold Clow; linarith
      · have hlow := psiRe_sub_log_pi_ge t
        have hL1 : L1s T ≤ Real.log T := by
          unfold L1s
          have : Real.log (T / (8 * π)) ≤ Real.log T :=
            Real.log_le_log (by positivity) (div_le_self hT0.le (by nlinarith [Real.pi_gt_three]))
          linarith [eps1_nonneg]
        have hlogT := log_le_lin hT
        have hlT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        have hmax : max (L1s T - (psiRe t - Real.log π)) 0 ≤ Real.log T + 9 := max_le (by linarith) (by linarith)
        have ht2 : (t / T) ^ 2 ≤ 1024 / T ^ 2 := by
          rw [div_pow]
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [sq_abs t, abs_nonneg t]
        calc (t / T) ^ 2 * max (L1s T - (psiRe t - Real.log π)) 0 ≤ 1024 / T ^ 2 * (Real.log T + 9) :=
              mul_le_mul ht2 hmax (le_max_right _ _) (by positivity)
          _ ≤ Clow := by
              unfold Clow
              rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
              nlinarith [mul_le_mul hT hT (by norm_num) hT0.le]
    have := mul_le_mul_of_nonneg_left hM1 hC0
    linarith

/-- The constant of the tail weight, `log 4 + 2ε₁`. -/
def c1 : ℝ := Real.log 4 + 2 * eps1

lemma c1_ge : 1 / 2 ≤ c1 := by
  unfold c1
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_gt_d9
  linarith [eps1_nonneg]

lemma c1_le : c1 ≤ 1.408 := by
  unfold c1 eps1
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_lt_d9
  norm_num at this ⊢
  linarith

/-- **The tail weight**: for `|t| > T ≥ 2000`, `|Φ(t)|(L(t) − L₁)⁺ ≤ T²(log(|t|/T) + c₁)/(729t²)`. -/
lemma tail_w_le {T : ℝ} (hT : 2000 ≤ T) {t : ℝ} (htT : T < |t|) :
    |phiR 3 T t| * max (psiRe t - Real.log π - L1s T) 0 ≤
      T ^ 2 * (Real.log (|t| / T) + c1) / (729 * t ^ 2) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < |t| := by linarith
  obtain ⟨-, habs⟩ := phiR_tail (by norm_num : (0 : ℝ) < 3) hT0 htT.le
  have hup := L_upper (by linarith : 32 ≤ |t|)
  have hlog0 : 0 ≤ Real.log (|t| / T) := Real.log_nonneg (by rw [le_div_iff₀ hT0]; linarith)
  have hc1 := c1_ge
  have e : Real.log (|t| / (2 * π)) - Real.log (T / (8 * π)) = Real.log (|t| / T) + Real.log 4 := by
    rw [← Real.log_div (by positivity) (by positivity), ← Real.log_mul (by positivity) (by norm_num)]
    congr 1; field_simp; ring
  have hmax : max (psiRe t - Real.log π - L1s T) 0 ≤ Real.log (|t| / T) + c1 := by
    refine max_le ?_ (by linarith)
    unfold L1s c1; linarith
  rw [show (3 : ℝ) ^ 6 = 729 by norm_num] at habs
  calc |phiR 3 T t| * max (psiRe t - Real.log π - L1s T) 0 ≤ T ^ 2 / (729 * t ^ 2) * (Real.log (|t| / T) + c1) :=
        mul_le_mul habs hmax (le_max_right _ _) (by positivity)
    _ = T ^ 2 * (Real.log (|t| / T) + c1) / (729 * t ^ 2) := by ring

/-! ## Fejér smoothing: `|D|²` against a weight dominated by a convolution -/

/-- The Fejér kernel `F_a(u) = sin²(au)/(πau²)`, of mass `1` and transform `(1 − |v|/2a)⁺`. -/
def fej (a u : ℝ) : ℝ := hsq (bx a) a u / (4 * π * a)

lemma fej_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 ≤ fej a u := by
  unfold fej; have := hsq_nonneg (g := bx a) (a := a) u; positivity

lemma integral_fej_cos {a : ℝ} (ha : 0 < a) (v : ℝ) :
    ∫ u, fej a u * Real.cos (u * v) = max (2 * a - |v|) 0 / (2 * a) := by
  unfold fej
  have h := integral_hsq_cos (esupp_bx a) ha v
  rw [autocorr_bx] at h
  have e : ∀ u, hsq (bx a) a u / (4 * π * a) * Real.cos (u * v) =
      (1 / (4 * π * a)) * (hsq (bx a) a u * Real.cos (u * v)) := fun u => by ring
  simp_rw [e]
  rw [integral_const_mul, h]
  field_simp
  ring

lemma integrable_fej_cos {a : ℝ} (ha : 0 < a) (v : ℝ) : Integrable fun u => fej a u * Real.cos (u * v) := by
  unfold fej
  have e : (fun u => hsq (bx a) a u / (4 * π * a) * Real.cos (u * v)) =
      fun u => (1 / (4 * π * a)) * (hsq (bx a) a u * Real.cos (u * v)) := funext fun u => by ring
  rw [e]
  exact (integrable_hsq_cos (esupp_bx a) ha v).const_mul _

lemma integrable_fej {a : ℝ} (ha : 0 < a) : Integrable (fej a) := by
  have h := integrable_fej_cos ha 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  exact h

lemma integral_fej {a : ℝ} (ha : 0 < a) : ∫ u, fej a u = 1 := by
  have h := integral_fej_cos ha 0
  simp only [mul_zero, Real.cos_zero, mul_one, abs_zero, sub_zero] at h
  rw [h, max_eq_left (by linarith), div_self (by positivity)]

lemma fej_even {a : ℝ} (ha : 0 < a) (u : ℝ) : fej a (-u) = fej a u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  unfold fej
  rw [hsq_bx_eq ha.le hu, hsq_bx_eq ha.le (neg_ne_zero.2 hu), mul_neg, Real.sin_neg, neg_sq, neg_sq]

lemma fej_le_const {a : ℝ} (ha : 0 < a) (u : ℝ) : fej a u ≤ a / π := by
  unfold fej
  rcases eq_or_ne u 0 with rfl | hu
  · unfold hsq
    rw [gH_bx_zero ha.le, div_le_div_iff₀ (by positivity) Real.pi_pos]
    nlinarith [Real.pi_pos]
  · rw [hsq_bx_eq ha.le hu]
    have hs : Real.sin (a * u) ^ 2 ≤ (a * u) ^ 2 := by
      have h := Real.abs_sin_le_abs (x := a * u)
      nlinarith [abs_nonneg (Real.sin (a * u)), sq_abs (Real.sin (a * u)), sq_abs (a * u)]
    have hu2 : 0 < u ^ 2 := by positivity
    rw [div_div, div_le_div_iff₀ (by positivity) Real.pi_pos]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 4 * π)]

lemma fej_le {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : u ≠ 0) : fej a u ≤ 1 / (π * a * u ^ 2) := by
  unfold fej
  rw [hsq_bx_eq ha.le hu]
  have hs := Real.sin_sq_le_one (a * u)
  have hu2 : 0 < u ^ 2 := by positivity
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 4 * π * a * u ^ 2)
  linarith

/-- For distinct `j, j' ∈ [1, N]`, `|log j' − log j| ≥ 1/N`. -/
lemma log_sep {N j j' : ℕ} (hj : j ∈ Icc 1 N) (hj' : j' ∈ Icc 1 N) (hne : j ≠ j') :
    1 / (N : ℝ) ≤ |Real.log j' - Real.log j| := by
  wlog hlt : j < j' generalizing j j'
  · have h := this hj' hj (Ne.symm hne) (by omega)
    rwa [abs_sub_comm]
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  have hj'N : j' ≤ N := (Finset.mem_Icc.1 hj').2
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj1
  have hj1R : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hlt
  have hNR : (j' : ℝ) ≤ N := by exact_mod_cast hj'N
  have h1 : Real.log ((j + 1) / j) ≤ Real.log j' - Real.log j := by
    rw [← Real.log_div (by linarith : (0 : ℝ) < j').ne' hjR.ne']
    exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hj1R hjR.le)
  have h2 : 1 / ((j : ℝ) + 1) ≤ Real.log ((j + 1) / j) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (((j : ℝ) + 1) / j)⁻¹ by positivity)
    rw [Real.log_inv] at h
    have e : (((j : ℝ) + 1) / j)⁻¹ - 1 = -(1 / ((j : ℝ) + 1)) := by field_simp; ring
    linarith
  have h3 : 1 / (N : ℝ) ≤ 1 / ((j : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have h0 : 0 ≤ 1 / ((j : ℝ) + 1) := by positivity
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **The smoothed `|D|²` is constant**: `∫|D(s + u)|²F_a(u)du = Σc_j²` once `2aN ≤ 1`. -/
lemma Kc_conv_fej {N : ℕ} (c : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (haN : 2 * a * N ≤ 1) (s : ℝ) :
    ∫ u, Kc N c (s + u) * fej a u = S2 N c := by
  have hsinI : ∀ v : ℝ, Integrable fun u => Real.sin (v * u) * fej a u := fun v =>
    (integrable_fej ha).bdd_mul (c := 1) (by fun_prop : Continuous fun u : ℝ => Real.sin (v * u)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hsin : ∀ v : ℝ, ∫ u, Real.sin (v * u) * fej a u = 0 := by
    intro v
    have h := integral_neg_eq_self (fun u => Real.sin (v * u) * fej a u) volume
    simp only [mul_neg, Real.sin_neg, fej_even ha, neg_mul] at h
    rw [integral_neg] at h
    linarith
  have hterm : ∀ j j' : ℕ, ∫ u, c j * c j' * Real.cos ((Real.log j' - Real.log j) * (s + u)) * fej a u =
      c j * c j' * Real.cos ((Real.log j' - Real.log j) * s) *
        (max (2 * a - |Real.log j' - Real.log j|) 0 / (2 * a)) := by
    intro j j'
    set Δ := Real.log j' - Real.log j
    have e : ∀ u, c j * c j' * Real.cos (Δ * (s + u)) * fej a u =
        c j * c j' * Real.cos (Δ * s) * (fej a u * Real.cos (u * Δ)) -
          c j * c j' * Real.sin (Δ * s) * (Real.sin (Δ * u) * fej a u) := by
      intro u; rw [mul_add, Real.cos_add]; ring_nf
    simp_rw [e]
    rw [integral_sub ((integrable_fej_cos ha Δ).const_mul _) ((hsinI Δ).const_mul _), integral_const_mul,
      integral_const_mul, integral_fej_cos ha, hsin]
    ring
  have hI : ∀ j j' : ℕ, Integrable fun u => c j * c j' * Real.cos ((Real.log j' - Real.log j) * (s + u)) * fej a u :=
    fun j j' => (integrable_fej ha).bdd_mul (c := |c j * c j'|)
      (by fun_prop : Continuous fun u : ℝ =>
        c j * c j' * Real.cos ((Real.log j' - Real.log j) * (s + u))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  unfold Kc
  have e : (fun u => (∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * Real.cos ((Real.log j' - Real.log j) * (s + u)))
      * fej a u) = fun u => ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N,
        c j * c j' * Real.cos ((Real.log j' - Real.log j) * (s + u)) * fej a u := by
    funext u; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  rw [e, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => hI j j']
  unfold S2
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun j' _ => hI j j']
  simp_rw [hterm]
  rw [Finset.sum_eq_single j]
  · simp only [sub_self, zero_mul, Real.cos_zero, mul_one, abs_zero, sub_zero]
    rw [max_eq_left (by linarith), div_self (by positivity), mul_one, sq]
  · intro j' hj' hne
    have hsep := log_sep hj hj' (Ne.symm hne)
    have hN0 : (0 : ℝ) < N := by
      have := (Finset.mem_Icc.1 hj).2; have := (Finset.mem_Icc.1 hj).1
      exact_mod_cast (show 0 < N by omega)
    have h2a : 2 * a ≤ 1 / (N : ℝ) := by rw [le_div_iff₀ hN0]; linarith
    rw [max_eq_right (by linarith), zero_div, mul_zero]
  · intro hj'; exact absurd hj hj'

lemma conv_comm (E : ℝ → ℝ) (a t : ℝ) : ∫ u, E (t - u) * fej a u = ∫ s, E s * fej a (t - s) := by
  have := integral_sub_left_eq_self (fun s => E s * fej a (t - s)) volume t
  simp only [sub_sub_cancel] at this
  exact this

lemma conv_prod_integrable {N : ℕ} (c : ℕ → ℝ) {a : ℝ} (ha : 0 < a) {E : ℝ → ℝ} (hE : Integrable E) :
    Integrable (Function.uncurry fun t s => Kc N c t * (E s * fej a (t - s))) (volume.prod volume) := by
  have hconv : Integrable (fun p : ℝ × ℝ => E p.2 * fej a (p.1 - p.2)) (volume.prod volume) := by
    have h := hE.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (integrable_fej ha) (μ := volume)
      (ν := volume)
    simpa using h
  refine hconv.bdd_mul (c := BallDensity.S1 N c ^ 2) ?_ ?_
  · exact ((continuous_Kc N c).comp continuous_fst).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Kc_nonneg N c _)]; exact Kc_le N c _

lemma integrable_Kc_conv {N : ℕ} (c : ℕ → ℝ) {a : ℝ} (ha : 0 < a) {E : ℝ → ℝ} (hE : Integrable E) :
    Integrable fun t => Kc N c t * ∫ u, E (t - u) * fej a u := by
  simp_rw [conv_comm E a]
  refine (conv_prod_integrable (N := N) c ha hE).integral_prod_left.congr
    (Filter.Eventually.of_forall fun t => ?_)
  show ∫ s, Kc N c t * (E s * fej a (t - s)) = Kc N c t * ∫ s, E s * fej a (t - s)
  exact integral_const_mul _ _

/-- **The mass of `|D|²` against a smoothed weight**: `∫|D(t)|²(E ⋆ F_a)(t)dt = Σc_j²·∫E` once `2aN ≤ 1`. -/
lemma integral_Kc_conv {N : ℕ} (c : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (haN : 2 * a * N ≤ 1) {E : ℝ → ℝ}
    (hE : Integrable E) : ∫ t, Kc N c t * ∫ u, E (t - u) * fej a u = S2 N c * ∫ s, E s := by
  simp_rw [conv_comm E a]
  have h2 : ∀ t, Kc N c t * ∫ s, E s * fej a (t - s) = ∫ s, Kc N c t * (E s * fej a (t - s)) :=
    fun t => (integral_const_mul _ _).symm
  simp_rw [h2]
  rw [integral_integral_swap (conv_prod_integrable (N := N) c ha hE)]
  have h3 : ∀ s, ∫ t, Kc N c t * (E s * fej a (t - s)) = E s * S2 N c := by
    intro s
    have e : ∀ t, Kc N c t * (E s * fej a (t - s)) = E s * (Kc N c t * fej a (t - s)) := fun t => by ring
    simp_rw [e]
    rw [integral_const_mul]
    congr 1
    have := integral_sub_right_eq_self (fun u => Kc N c (u + s) * fej a u) s (μ := volume)
    simp only [sub_add_cancel] at this
    rw [this]
    have e2 : ∀ u, Kc N c (u + s) * fej a u = Kc N c (s + u) * fej a u := fun u => by rw [add_comm]
    simp_rw [e2]
    exact Kc_conv_fej c ha haN s
  simp_rw [h3]
  rw [integral_mul_const]
  ring

/-- Integrability of `x ↦ g(|x|)` from integrability of `g` on `(0, ∞)`. -/
lemma integrable_of_comp_abs {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi 0)) : Integrable fun x => g |x| := by
  have hIoi : IntegrableOn (fun x => g |x|) (Set.Ioi 0) :=
    hg.congr_fun (fun x hx => by simp only [abs_of_pos (show (0 : ℝ) < x from hx)]) measurableSet_Ioi
  have hIic : IntegrableOn (fun x => g |x|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi
  have h := hIic.union hIoi
  rw [Set.Iic_union_Ioi, integrableOn_univ] at h
  exact h

/-- The far weight `|t|^{−2}` on `|t| > R`. -/
def farW2 (R t : ℝ) : ℝ := Set.indicator (Set.Ioi R) (fun s => s ^ (-(2 : ℝ))) |t|

lemma farW2_nonneg {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : 0 ≤ farW2 R t := by
  unfold farW2
  exact Set.indicator_nonneg (fun s hs => Real.rpow_nonneg (hR.trans (le_of_lt hs)) _) _

lemma farW2_of_lt {R t : ℝ} (ht : R < |t|) : farW2 R t = 1 / t ^ 2 := by
  unfold farW2
  rw [Set.indicator_of_mem (show |t| ∈ Set.Ioi R from ht)]
  show |t| ^ (-(2 : ℝ)) = 1 / t ^ 2
  rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs,
    one_div]

lemma integrable_farW2 {R : ℝ} (hR : 0 < R) : Integrable (farW2 R) :=
  integrable_of_comp_abs
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hR).integrable_indicator measurableSet_Ioi).integrableOn

lemma integral_farW2 {R : ℝ} (hR : 0 < R) : ∫ t, farW2 R t = 2 / R := by
  unfold farW2
  rw [integral_comp_abs (f := Set.indicator (Set.Ioi R) (fun s => s ^ (-(2 : ℝ)))),
    setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hR.le,
    integral_Ioi_rpow_of_lt (by norm_num) hR,
    show (-(2 : ℝ) + 1) = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- **The window mass of the Fejér kernel**: `∫_{−δ}^{δ}F_a ≥ 1 − 2/(πaδ)`. -/
lemma fej_mass_ge {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    1 - 2 / (π * a * δ) ≤ ∫ u in Set.Icc (-δ) δ, fej a u := by
  have hsplit := integral_add_compl (measurableSet_Icc : MeasurableSet (Set.Icc (-δ) δ)) (integrable_fej ha)
  rw [integral_fej ha] at hsplit
  have hcompl : ∫ u in (Set.Icc (-δ) δ)ᶜ, fej a u ≤ 2 / (π * a * δ) := by
    rw [← integral_indicator measurableSet_Icc.compl]
    have hmaj : ∀ u, Set.indicator (Set.Icc (-δ) δ)ᶜ (fej a) u ≤ 1 / (π * a) * farW2 δ u := by
      intro u
      by_cases hu : u ∈ Set.Icc (-δ) δ
      · rw [Set.indicator_of_notMem (by simpa using hu)]
        exact mul_nonneg (by positivity) (farW2_nonneg hδ.le u)
      · rw [Set.indicator_of_mem hu]
        have hlt : δ < |u| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
          rcases hu with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; exact h
        have hu0 : u ≠ 0 := by rintro rfl; simp at hlt; linarith
        rw [farW2_of_lt hlt]
        calc fej a u ≤ 1 / (π * a * u ^ 2) := fej_le ha hu0
          _ = 1 / (π * a) * (1 / u ^ 2) := by field_simp
    calc ∫ u, Set.indicator (Set.Icc (-δ) δ)ᶜ (fej a) u ≤ ∫ u, 1 / (π * a) * farW2 δ u :=
          integral_mono ((integrable_fej ha).indicator measurableSet_Icc.compl)
            ((integrable_farW2 hδ).const_mul _) hmaj
      _ = 2 / (π * a * δ) := by rw [integral_const_mul, integral_farW2 hδ]; field_simp
  linarith

/-- **The window bound**: if `w ≤ E(t − u)` for `|u| ≤ δ`, then `(1 − 2/(πaδ))w ≤ (E ⋆ F_a)(t)`. -/
lemma conv_ge {E : ℝ → ℝ} {a δ w t : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hE0 : ∀ s, 0 ≤ E s) (hEi : Integrable E)
    (hw0 : 0 ≤ w) (hw : ∀ u ∈ Set.Icc (-δ) δ, w ≤ E (t - u)) :
    (1 - 2 / (π * a * δ)) * w ≤ ∫ u, E (t - u) * fej a u := by
  have hint : Integrable fun u => E (t - u) * fej a u :=
    (hEi.comp_sub_left t).mul_bdd (c := a / π) (integrable_fej ha).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (fej_nonneg ha u)]; exact fej_le_const ha u)
  have h1 : ∫ u in Set.Icc (-δ) δ, E (t - u) * fej a u ≤ ∫ u, E (t - u) * fej a u :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun u => mul_nonneg (hE0 _) (fej_nonneg ha u))
  have h2 : ∫ u in Set.Icc (-δ) δ, w * fej a u ≤ ∫ u in Set.Icc (-δ) δ, E (t - u) * fej a u :=
    setIntegral_mono_on ((integrable_fej ha).const_mul w).integrableOn hint.integrableOn measurableSet_Icc
      fun u hu => mul_le_mul_of_nonneg_right (hw u hu) (fej_nonneg ha u)
  rw [integral_const_mul] at h2
  have h3 := mul_le_mul_of_nonneg_left (fej_mass_ge ha hδ) hw0
  linarith

/-! ## The tail envelope `E(s) = K(log(|s|/R) + c₁)/s²` on `|s| > R` -/

lemma c1_nonneg : 0 ≤ c1 := by linarith [c1_ge]

lemma logw_nonneg {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c) :
    ∀ x ∈ Set.Ioi R, 0 ≤ (Real.log (x / R) + c) / x ^ 2 := fun x hx => by
  have hx' : R < x := hx
  have : 0 ≤ Real.log (x / R) := Real.log_nonneg (by rw [le_div_iff₀ hR]; linarith)
  exact div_nonneg (by linarith) (sq_nonneg x)

/-- The antiderivative `−(log(x/R) + c + 1)/x` of `(log(x/R) + c)/x²`. -/
lemma hasDerivAt_logw {R c x : ℝ} (hR : 0 < R) (hx : 0 < x) :
    HasDerivAt (fun y => -(Real.log (y / R) + (c + 1)) / y) ((Real.log (x / R) + c) / x ^ 2) x := by
  have h1 : HasDerivAt (fun y => Real.log (y / R)) (1 / R / (x / R)) x :=
    ((hasDerivAt_id' x).div_const R).log (by positivity)
  have h2 := ((h1.add_const (c + 1)).neg).div (hasDerivAt_id' x) hx.ne'
  convert h2 using 1
  simp only [Pi.neg_apply]
  field_simp
  ring

lemma tendsto_logw {R c : ℝ} (hR : 0 < R) :
    Filter.Tendsto (fun y => -(Real.log (y / R) + (c + 1)) / y) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun y : ℝ => Real.log y / y) Filter.atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h2 : Filter.Tendsto (fun y : ℝ => (c + 1 - Real.log R) / y) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h3 := (h1.add h2).neg
  rw [add_zero, neg_zero] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with y hy
  rw [Real.log_div hy.ne' hR.ne']
  field_simp
  ring

lemma integrableOn_logw {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c) :
    IntegrableOn (fun x => (Real.log (x / R) + c) / x ^ 2) (Set.Ioi R) :=
  integrableOn_Ioi_deriv_of_nonneg' (g := fun y => -(Real.log (y / R) + (c + 1)) / y)
    (fun _ hx => hasDerivAt_logw hR (hR.trans_le hx)) (logw_nonneg hR hc) (tendsto_logw hR)

lemma integral_logw {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c) :
    ∫ x in Set.Ioi R, (Real.log (x / R) + c) / x ^ 2 = (1 + c) / R := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun y => -(Real.log (y / R) + (c + 1)) / y)
    (g' := fun x => (Real.log (x / R) + c) / x ^ 2) (fun _ hx => hasDerivAt_logw hR (hR.trans_le hx))
    (logw_nonneg hR hc) (tendsto_logw hR)
  rw [h]
  simp only [div_self hR.ne', Real.log_one]
  ring

/-- The tail envelope. -/
def envT (K R s : ℝ) : ℝ := Set.indicator (Set.Ioi R) (fun x => K * ((Real.log (x / R) + c1) / x ^ 2)) |s|

lemma envT_nonneg {K R : ℝ} (hK : 0 ≤ K) (hR : 0 < R) (s : ℝ) : 0 ≤ envT K R s := by
  unfold envT
  exact Set.indicator_nonneg (fun x hx => mul_nonneg hK (logw_nonneg hR c1_nonneg x hx)) _

lemma integrable_envT (K : ℝ) {R : ℝ} (hR : 0 < R) : Integrable (envT K R) := by
  have h : IntegrableOn (fun x => K * ((Real.log (x / R) + c1) / x ^ 2)) (Set.Ioi R) :=
    (integrableOn_logw hR c1_nonneg).const_mul K
  exact integrable_of_comp_abs (h.integrable_indicator measurableSet_Ioi).integrableOn

lemma integral_envT (K : ℝ) {R : ℝ} (hR : 0 < R) : ∫ s, envT K R s = 2 * K * (1 + c1) / R := by
  unfold envT
  rw [integral_comp_abs (f := Set.indicator (Set.Ioi R) (fun x => K * ((Real.log (x / R) + c1) / x ^ 2))),
    setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hR.le, integral_const_mul,
    integral_logw hR c1_nonneg]
  ring

/-- **The envelope dominates the tail weight on windows**: for `|t| > T`, `|u| ≤ δ < T`,
`T²(log(|t|/T) + c₁)/(729t²) ≤ E(t − u)` with `K = (T + δ)²/729` and `R = T − δ`. -/
lemma envT_ge {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : δ < T) {t u : ℝ} (htT : T < |t|) (hu : |u| ≤ δ) :
    T ^ 2 * (Real.log (|t| / T) + c1) / (729 * t ^ 2) ≤ envT ((T + δ) ^ 2 / 729) (T - δ) (t - u) := by
  have hs1 : |t| - δ ≤ |t - u| := by have := abs_sub_abs_le_abs_sub t u; linarith
  have hs2 : |t - u| ≤ |t| + δ := by
    have := abs_add_le t (-u); rw [abs_neg, ← sub_eq_add_neg] at this; linarith
  have hR : 0 < T - δ := by linarith
  have hsR : T - δ < |t - u| := by linarith
  have hs0 : 0 < |t - u| := by linarith
  have ht0 : 0 < |t| := by linarith
  unfold envT
  rw [Set.indicator_of_mem (show |t - u| ∈ Set.Ioi (T - δ) from hsR)]
  have hlog : Real.log (|t| / T) ≤ Real.log (|t - u| / (T - δ)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hT hR]
    have e1 : |t| * (T - δ) ≤ (|t - u| + δ) * (T - δ) := mul_le_mul_of_nonneg_right (by linarith) hR.le
    have e2 : 0 < δ * (|t - u| - (T - δ)) := mul_pos hδ (by linarith)
    nlinarith
  have hA : 0 ≤ Real.log (|t| / T) + c1 := by
    have := Real.log_nonneg (show 1 ≤ |t| / T by rw [le_div_iff₀ hT]; linarith)
    linarith [c1_nonneg]
  have hB : T * |t - u| ≤ (T + δ) * |t| := by
    have e1 := mul_le_mul_of_nonneg_left hs2 hT.le
    have e2 := mul_le_mul_of_nonneg_left htT.le hδ.le
    linarith
  have key : T ^ 2 / (729 * |t| ^ 2) ≤ (T + δ) ^ 2 / 729 / |t - u| ^ 2 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := pow_le_pow_left₀ (by positivity) hB 2
    nlinarith
  rw [show t ^ 2 = |t| ^ 2 from (sq_abs t).symm]
  calc T ^ 2 * (Real.log (|t| / T) + c1) / (729 * |t| ^ 2)
      = T ^ 2 / (729 * |t| ^ 2) * (Real.log (|t| / T) + c1) := by ring
    _ ≤ (T + δ) ^ 2 / 729 / |t - u| ^ 2 * (Real.log (|t - u| / (T - δ)) + c1) :=
        mul_le_mul key (by linarith) hA (by positivity)
    _ = (T + δ) ^ 2 / 729 * ((Real.log (|t - u| / (T - δ)) + c1) / |t - u| ^ 2) := by ring

/-- The smoothed tail envelope `(E ⋆ F_a)(t)` at `a = 1/(2N)`, `δ = T/10`. -/
def EcS (N : ℕ) (T t : ℝ) : ℝ :=
  ∫ u, envT ((T + T / 10) ^ 2 / 729) (T - T / 10) (t - u) * fej (1 / (2 * N)) u

lemma EcS_nonneg {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 < T) (t : ℝ) : 0 ≤ EcS N T t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact integral_nonneg fun u => mul_nonneg (envT_nonneg (by positivity) (by linarith) _)
    (fej_nonneg (by positivity) u)

/-- **The smoothed envelope dominates the tail weight**: for `|t| > T ≥ 2000N`,
`T²(log(|t|/T) + c₁)/(729t²) ≤ (157/156)(E ⋆ F_a)(t)`. -/
lemma tail_conv_le {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T) {t : ℝ} (htT : T < |t|) :
    T ^ 2 * (Real.log (|t| / T) + c1) / (729 * t ^ 2) ≤ 157 / 156 * EcS N T t := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hT0 : 0 < T := by linarith
  have ha : 0 < 1 / (2 * (N : ℝ)) := by positivity
  have hδ : 0 < T / 10 := by positivity
  have hA : 0 ≤ Real.log (|t| / T) + c1 := by
    have := Real.log_nonneg (show 1 ≤ |t| / T by rw [le_div_iff₀ hT0]; linarith)
    linarith [c1_nonneg]
  have hw0 : 0 ≤ T ^ 2 * (Real.log (|t| / T) + c1) / (729 * t ^ 2) :=
    div_nonneg (mul_nonneg (sq_nonneg T) hA) (by positivity)
  have h := conv_ge ha hδ (envT_nonneg (K := (T + T / 10) ^ 2 / 729) (by positivity) (by linarith))
    (integrable_envT _ (by linarith)) hw0
    (fun u hu => envT_ge hT0 hδ (by linarith) htT (abs_le.2 ⟨hu.1, hu.2⟩))
  have hε : 2 / (π * (1 / (2 * N)) * (T / 10)) ≤ 1 / 157 := by
    have e : π * (1 / (2 * (N : ℝ))) * (T / 10) = π * T / (20 * N) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num), one_mul, le_div_iff₀ (by positivity)]
    have hpi := Real.pi_gt_d2
    nlinarith [mul_le_mul_of_nonneg_right hpi.le hT0.le]
  have h2 := mul_le_mul_of_nonneg_right hε hw0
  unfold EcS
  linarith

/-! ## The archimedean term -/

/-- **The pointwise bound**: `Φ(t)(L(t) − L₁) ≥ −(C_low M_{T/4}(t) + (157/156)(E ⋆ F_a)(t))`. -/
lemma phiR3_L_ge {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T) (t : ℝ) :
    -(Clow * majR (T / 4) t + 157 / 156 * EcS N T t) ≤ phiR 3 T t * (psiRe t - Real.log π - L1s T) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT : 2000 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hM0 := majR_nonneg (T / 4) t
  have hC0 : (0 : ℝ) ≤ Clow := by unfold Clow; norm_num
  have hE0 := EcS_nonneg hN hT0 t
  have hCM := mul_nonneg hC0 hM0
  rcases le_or_gt |t| T with h | h
  · obtain ⟨h0, h1, -⟩ := phiR_bounds (by norm_num : (0 : ℝ) < 3) hT0 h
    have hlow := low_le_s hT t
    set m := max (L1s T - (psiRe t - Real.log π)) 0 with hm
    have hm0 : 0 ≤ m := le_max_right _ _
    have hm1 : L1s T - (psiRe t - Real.log π) ≤ m := le_max_left _ _
    have e1 := mul_le_mul_of_nonneg_left hm1 h0
    have e2 := mul_le_mul_of_nonneg_right h1 hm0
    linarith
  · obtain ⟨h0, -⟩ := phiR_tail (by norm_num : (0 : ℝ) < 3) hT0 h.le
    have hw := tail_w_le hT h
    have hc := tail_conv_le hN hTN h
    set m := max (psiRe t - Real.log π - L1s T) 0 with hm
    have hm1 : psiRe t - Real.log π - L1s T ≤ m := le_max_left _ _
    have e1 := mul_le_mul_of_nonpos_left hm1 h0
    rw [abs_of_nonpos h0] at hw
    linarith

/-- The defect weight `G = |D|²(C_low M_{T/4} + (157/156)(E ⋆ F_a))`. -/
def defW (N : ℕ) (c : ℕ → ℝ) (T t : ℝ) : ℝ :=
  Clow * (Kc N c t * majR (T / 4) t) + 157 / 156 * (Kc N c t * EcS N T t)

lemma integrable_defW {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {T : ℝ} (hT : 0 < T) : Integrable (defW N c T) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := (integrable_Kc_majR N c (show 0 < T / 4 by positivity)).const_mul Clow
  have h2 := (integrable_Kc_conv (N := N) c (show 0 < 1 / (2 * (N : ℝ)) by positivity)
    (integrable_envT ((T + T / 10) ^ 2 / 729) (show 0 < T - T / 10 by linarith))).const_mul (157 / 156 : ℝ)
  exact h1.add h2

lemma integral_defW {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {T : ℝ} (hT : 0 < T) :
    ∫ t, defW N c T t = Clow * (∫ t, Kc N c t * majR (T / 4) t) +
      157 / 156 * (S2 N c * (2 * ((T + T / 10) ^ 2 / 729) * (1 + c1) / (T - T / 10))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < 1 / (2 * (N : ℝ)) := by positivity
  have haN : 2 * (1 / (2 * (N : ℝ))) * N ≤ 1 := le_of_eq (by field_simp)
  have hR : 0 < T - T / 10 := by linarith
  have h1 := (integrable_Kc_majR N c (show 0 < T / 4 by positivity)).const_mul Clow
  have h2 := (integrable_Kc_conv (N := N) c ha (integrable_envT ((T + T / 10) ^ 2 / 729) hR)).const_mul
    (157 / 156 : ℝ)
  unfold defW EcS
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_Kc_conv c ha haN (integrable_envT _ hR), integral_envT _ hR]

/-- **The defect**: `(1/2π)∫G ≤ 0.0038·TΣc_n²` for `T ≥ 2000N`. -/
lemma defect_sharp {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T) (c : ℕ → ℝ) :
    1 / (2 * π) * ∫ t, defW N c T t ≤ 0.0038 * (T * S2 N c) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  have hS2n := S2_nonneg N c
  have hU : 0 ≤ T * S2 N c := mul_nonneg hT0.le hS2n
  rw [integral_defW hN c hT0]
  have hM := integral_Kc_majR_le' (N := N) (r := T / 4) (by linarith) c
  have hpi1 := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  have hc1 := c1_le
  have hc0 := c1_nonneg
  have hC : Clow = 23 / 2000 := rfl
  have hinv : 1 / (2 * π) ≤ 0.1592 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hlow : 1 / (2 * π) * (Clow * ∫ t, Kc N c t * majR (T / 4) t) ≤ 0.0022942 * (T * S2 N c) := by
    have h1 := mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ 1 / (2 * π) * (23 / 2000))
    have e : 1 / (2 * π) * (23 / 2000) * (π ^ 2 / 2 * (T / 4 + 8 * N) * S2 N c) =
        23 / 2000 * (π / 4) * ((T / 4 + 8 * N) * S2 N c) := by
      field_simp; ring
    have h2 : (T / 4 + 8 * N) * S2 N c ≤ 0.254 * (T * S2 N c) := by
      have : T / 4 + 8 * N ≤ 0.254 * T := by linarith
      have := mul_le_mul_of_nonneg_right this hS2n
      linarith
    have h3 : 0 ≤ (T / 4 + 8 * N) * S2 N c := mul_nonneg (by positivity) hS2n
    have h4 : 23 / 2000 * (π / 4) * ((T / 4 + 8 * N) * S2 N c) ≤ 23 / 2000 * 0.7854 * (0.254 * (T * S2 N c)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by norm_num)) h2 h3 (by norm_num)
    rw [hC]
    linarith
  have htail : 1 / (2 * π) * (157 / 156 * (S2 N c * (2 * ((T + T / 10) ^ 2 / 729) * (1 + c1) / (T - T / 10)))) ≤
      0.0014231 * (T * S2 N c) := by
    have hT' : T ≠ 0 := hT0.ne'
    have e3 : 1 / (2 * π) * (157 / 156 * (S2 N c * (2 * ((T + T / 10) ^ 2 / 729) * (1 + c1) / (T - T / 10)))) =
        18997 / 5117580 * ((1 + c1) * (1 / (2 * π)) * (T * S2 N c)) := by
      rw [show T - T / 10 = 9 * T / 10 by ring, show T + T / 10 = 11 * T / 10 by ring]
      field_simp
      ring
    have h5 : (1 + c1) * (1 / (2 * π)) ≤ 2.408 * 0.1592 :=
      mul_le_mul (by linarith) hinv (by positivity) (by norm_num)
    have h6 := mul_le_mul_of_nonneg_right h5 hU
    rw [e3]
    linarith
  linarith

/-- **The archimedean term**: `−g_h(0)log π + (1/2π)∫h Re ψ ≥ (1/2π)(L₁Φ̂(0)Σc_n² − ∫G)`. -/
lemma arch_ge_sharp {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T) (c : ℕ → ℝ) :
    1 / (2 * π) * (L1s T * phihat 3 T 0 * S2 N c - ∫ t, defW N c T t) ≤
      -(gh (hRC N c 3 T) 0 * Real.log π) + 1 / (2 * π) * ∫ r, hRC N c 3 T r * psiRe r := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  have hb : (0 : ℝ) < 3 := by norm_num
  have hbT : (3 : ℝ) ≤ T := by linarith
  have h12 : 12 * 3 * (N : ℝ) < T := by linarith
  have hiR := integrable_hRC hb hT0 N c
  have hiP := integrable_hRC_psi hb hT0 hbT N c
  have hiG := integrable_defW hN c hT0
  have hpt : ∀ r, L1s T * hRC N c 3 T r - defW N c T r ≤
      hRC N c 3 T r * psiRe r - Real.log π * hRC N c 3 T r := by
    intro r
    have h1 := phiR3_L_ge hN hTN r
    have h3 := mul_le_mul_of_nonneg_left h1 (Kc_nonneg N c r)
    unfold hRC defW
    linarith
  have hint : ∫ r, (L1s T * hRC N c 3 T r - defW N c T r) ≤
      ∫ r, (hRC N c 3 T r * psiRe r - Real.log π * hRC N c 3 T r) :=
    integral_mono ((hiR.const_mul (L1s T)).sub hiG) (hiP.sub (hiR.const_mul (Real.log π))) hpt
  rw [integral_sub (hiR.const_mul _) hiG, integral_sub hiP (hiR.const_mul _), integral_const_mul,
    integral_const_mul, integral_hRC hb hT0 hN h12] at hint
  have hgh0 : gh (hRC N c 3 T) 0 = 1 / (2 * π) * ∫ r, hRC N c 3 T r := by
    unfold gh; simp only [mul_zero, Real.cos_zero, mul_one]
  rw [hgh0, integral_hRC hb hT0 hN h12]
  have hpi : 0 < 1 / (2 * π) := by positivity
  have := mul_le_mul_of_nonneg_left hint hpi.le
  linarith

/-! ## The pole and the zero side -/

/-- `‖Φ(i/2)‖ ≤ 1/T²` at `b = 3`, `T ≥ 64`. -/
lemma phiC3_I_half_le {T : ℝ} (hT : 64 ≤ T) : ‖phiC 3 T (I / 2)‖ ≤ 1 / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  refine (norm_phiC_I_half (by norm_num) hT0).trans ?_
  have hx0 : 0 ≤ 3 * (3 / T) := by positivity
  have hx1 : 3 * (3 / T) ≤ 1 / 2 := by
    rw [show 3 * (3 / T) = 9 / T by ring, div_le_iff₀ hT0]; linarith
  have hexp : Real.exp (3 * (3 / T)) ≤ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := 3 * (3 / T)) (by rw [abs_of_nonneg hx0]; linarith)
    have := (abs_le.1 h).2
    nlinarith only [this, hx0, hx1]
  have e : (3 / T) ^ 2 / (4 * 3 ^ 2) + (3 / T) ^ 4 / (16 * 3 ^ 4) = 1 / (4 * T ^ 2) + 1 / (16 * T ^ 4) := by
    field_simp
  rw [e]
  have h4 : 1 / (16 * T ^ 4) ≤ 1 / (4 * T ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) ≤ T ^ 2 := by nlinarith only [hT]
    nlinarith only [this]
  have hpos : 0 ≤ 1 / (4 * T ^ 2) + 1 / (16 * T ^ 4) := by positivity
  calc Real.exp (3 * (3 / T)) * (1 / (4 * T ^ 2) + 1 / (16 * T ^ 4))
      ≤ 2 * (1 / (4 * T ^ 2) + 1 / (4 * T ^ 2)) := mul_le_mul hexp (by linarith) hpos (by norm_num)
    _ = 1 / T ^ 2 := by field_simp; ring

/-- **The pole term is negligible**: `Re(h(i/2) + h(−i/2)) ≥ −10⁻⁶TΣc_n²` for `T ≥ 2000N`. -/
lemma pole_ge_sharp {N : ℕ} {T : ℝ} (hTN : 2000 * N ≤ T) (hT : 2000 ≤ T) (c : ℕ → ℝ) :
    -(1 / 1000000 * (T * S2 N c)) ≤ (htC N c 3 T (I / 2) + htC N c 3 T (-(I / 2))).re := by
  have hT0 : 0 < T := by linarith
  refine le_trans ?_ (pole_ge_cut (by norm_num) hT0 N c)
  have hS1 := S1_sq_le N c
  have hS2n := S2_nonneg N c
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNT : (N : ℝ) ≤ T / 2000 := by linarith
  have h1 : (N * BallDensity.S1 N c) ^ 2 * ‖phiC 3 T (I / 2)‖ ≤ (N * BallDensity.S1 N c) ^ 2 * (1 / T ^ 2) :=
    mul_le_mul_of_nonneg_left (phiC3_I_half_le (by linarith)) (sq_nonneg _)
  have h2 : (N * BallDensity.S1 N c) ^ 2 * (1 / T ^ 2) ≤ 1 / 2000000 * (T * S2 N c) := by
    rw [mul_one_div, div_le_iff₀ (by positivity), mul_pow]
    have hN2 : (N : ℝ) ^ 2 ≤ (T / 2000) ^ 2 := pow_le_pow_left₀ hN0 hNT 2
    have hU : 0 ≤ T ^ 3 * S2 N c := mul_nonneg (by positivity) hS2n
    calc (N : ℝ) ^ 2 * BallDensity.S1 N c ^ 2 ≤ (T / 2000) ^ 2 * (N * S2 N c) :=
          mul_le_mul hN2 hS1 (sq_nonneg _) (by positivity)
      _ ≤ (T / 2000) ^ 2 * (T / 2000 * S2 N c) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNT hS2n) (by positivity)
      _ ≤ 1 / 2000000 * (T * S2 N c) * T ^ 2 := by linarith
  linarith

/-- **The zero side**: `Σ_ρ |V_x(ρ)|²Φ(γ) ≤ (1/25)Σ_{|γ| ≤ T}|V_x(ρ)|²`, as `Φ ≤ 1/25` on `[−T, T]` and `Φ ≤ 0`
off it. -/
lemma zero_side_sharp {T : ℝ} (hT : 0 < T) (N : ℕ) (x : ℕ → ℝ) {Z : ℝ}
    (hZ : HasSum (fun q => ‖BallRate.dpoly N x q‖ ^ 2 * phiR 3 T (zetaZeroFamily q).im) Z) :
    Z ≤ 1 / 25 * ∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 := by
  classical
  have hF : HasSum (fun q => if q ∈ BallRate.zerosUpTo T then 1 / 25 * ‖BallRate.dpoly N x q‖ ^ 2 else 0)
      (∑ q ∈ BallRate.zerosUpTo T,
        if q ∈ BallRate.zerosUpTo T then 1 / 25 * ‖BallRate.dpoly N x q‖ ^ 2 else 0) :=
    hasSum_sum_of_ne_finset_zero fun q hq => by simp [hq]
  rw [Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum] at hF
  refine hasSum_le (fun q => ?_) hZ hF
  by_cases hq : q ∈ BallRate.zerosUpTo T
  · rw [ite_eq_left hq]
    have h25 := phiR3_le hT (BallRate.mem_zerosUpTo.1 hq)
    calc ‖BallRate.dpoly N x q‖ ^ 2 * phiR 3 T (zetaZeroFamily q).im ≤ ‖BallRate.dpoly N x q‖ ^ 2 * (1 / 25) :=
          mul_le_mul_of_nonneg_left h25 (sq_nonneg _)
      _ = _ := by ring
  · rw [ite_eq_right hq]
    have h : T < |(zetaZeroFamily q).im| := by
      rw [BallRate.mem_zerosUpTo] at hq; push Not at hq; exact hq
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (phiR_tail (by norm_num) hT h.le).1

/-! ## The theorem -/

/-- `log π ≤ π/e ≤ 1.1558`. -/
lemma log_pi_le_s : Real.log π ≤ 1.1558 := by
  have he := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (show 0 < π / Real.exp 1 by positivity)
  rw [Real.log_div Real.pi_ne_zero he.ne', Real.log_exp] at h
  have h2 : π / Real.exp 1 ≤ 1.1558 := by
    rw [div_le_iff₀ he]
    have := Real.exp_one_gt_d9
    have := Real.pi_lt_d4
    linarith
  linarith

/-- **Landau's slack** `G(c) = (log N + log 4 + 1)Σc_n² − L(c)`, with
`L(c) = 2Σ_{n ≤ N}Λ(n)n^{−1/2}Σ_{jn ≤ N}c_j c_{jn}` Landau's form. -/
def landauSlack (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  (Real.log N + (Real.log 4 + 1)) * S2 N c - 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n

lemma landauSlack_nonneg (N : ℕ) (c : ℕ → ℝ) : 0 ≤ landauSlack N c := by
  have h : 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n ≤ (Real.log N + (Real.log 4 + 1)) * S2 N c :=
    landau_le_sharp N c
  unfold landauSlack; linarith

/-- **The log-growth bound, keeping Landau's slack** (RH): for `N ≥ 1` and `T ≥ 2000N`,
`(T/11)((log(T/N) − 7)Σc_n² + G(c)) ≤ Σ_{|γ| ≤ T}|V_x(ρ)|²` with `c_n = x_n√n`. The prime side is
`(5T/1296)L(c)` exactly (`BallCutoff.prime_eq_cut`), and `L(c) = (log N + log 4 + 1)Σc_n² − G(c)`. -/
theorem sharp_bound_slack (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T)
    (x : ℕ → ℝ) :
    T / 11 * ((Real.log (T / N) - 7) * S2 N (fun n => x n * Real.sqrt n) +
      landauSlack N (fun n => x n * Real.sqrt n)) ≤
      ∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hT : 2000 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hb : (0 : ℝ) < 3 := by norm_num
  have hbT : (3 : ℝ) ≤ T := by linarith
  have h12 : 12 * 3 * (N : ℝ) < T := by linarith
  set c : ℕ → ℝ := fun n => x n * Real.sqrt n with hc
  have hsum := (weil_htC hb hT0 hbT N c).2
  have hre := Complex.hasSum_re hsum
  have hterm : ∀ q, (htC N c 3 T ((zetaZeroFamily q - 1 / 2) / I)).re =
      ‖BallRate.dpoly N x q‖ ^ 2 * phiR 3 T (zetaZeroFamily q).im := fun q => by
    rw [hc, zero_term_cut hRH hb hT0 N x q, Complex.ofReal_re]
  simp only [hterm] at hre
  rw [Complex.add_re, Complex.ofReal_re] at hre
  have hZ := zero_side_sharp hT0 N x hre
  have hpole := pole_ge_sharp hTN hT c
  have harch := arch_ge_sharp hN hTN c
  have hD := defect_sharp hN hTN c
  have hΦ : phihat 3 T 0 = 5 * π * T / 648 := by rw [phihat_zero hb hT0]; ring
  have hprime : 2 * ∑' n : ℕ, Λ n / Real.sqrt n * gh (hRC N c 3 T) (Real.log n) =
      phihat 3 T 0 / (2 * π) * ((Real.log N + (Real.log 4 + 1)) * S2 N c - landauSlack N c) := by
    rw [prime_eq_cut hb hT0 hN h12 c]
    unfold landauSlack
    ring
  have hS2n := S2_nonneg N c
  have hU : 0 ≤ T * S2 N c := mul_nonneg hT0.le hS2n
  have eA : 1 / (2 * π) * (L1s T * phihat 3 T 0 * S2 N c - ∫ t, defW N c T t) =
      5 / 1296 * (L1s T * (T * S2 N c)) - 1 / (2 * π) * ∫ t, defW N c T t := by
    rw [hΦ]; field_simp; ring
  have eP : phihat 3 T 0 / (2 * π) * ((Real.log N + (Real.log 4 + 1)) * S2 N c - landauSlack N c) =
      5 / 1296 * ((Real.log N + (Real.log 4 + 1)) * (T * S2 N c)) - 5 / 1296 * (T * landauSlack N c) := by
    rw [hΦ]; field_simp; ring
  rw [eA] at harch
  rw [eP] at hprime
  have hGT : 0 ≤ T * landauSlack N c := mul_nonneg hT0.le (landauSlack_nonneg N c)
  have hLL : Real.log (T / N) - 5.6322 ≤ L1s T - Real.log N - (Real.log 4 + 1) := by
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hlp := log_pi_le_s
    have hl2 := Real.log_two_lt_d9
    have heps : eps1 ≤ 0.010588 := by unfold eps1; norm_num
    unfold L1s
    rw [Real.log_div hT0.ne' hN0.ne', Real.log_div hT0.ne' (show (8 : ℝ) * π ≠ 0 by positivity),
      Real.log_mul (by norm_num) Real.pi_ne_zero, hl8, hl4]
    linarith
  have hmainP := mul_le_mul_of_nonneg_left hLL hU
  have hℓ : 7 ≤ Real.log (T / N) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h1 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 ^ 7 ≤ 2.72 ^ 7 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 7
    have h4 : (2000 : ℝ) ≤ T / N := by rw [le_div_iff₀ hN0]; linarith
    have h5 : (2.72 : ℝ) ^ 7 ≤ 2000 := by norm_num
    rw [h1]
    linarith
  have hℓU := mul_nonneg (sub_nonneg.2 hℓ) hU
  linarith only [hZ, hpole, harch, hD, hprime, hmainP, hℓU, hU, hGT]

/-- **The log-growth bound** (RH): for `N ≥ 1` and `T ≥ 2000N`,
`(T/11)(log(T/N) − 7)Σc_n² ≤ Σ_{|γ| ≤ T}|V_x(ρ)|²` with `c_n = x_n√n`. -/
theorem sharp_bound (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T)
    (x : ℕ → ℝ) :
    T / 11 * (Real.log (T / N) - 7) * S2 N (fun n => x n * Real.sqrt n) ≤
      ∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 := by
  have h := sharp_bound_slack hRH hN hTN x
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  have hG := mul_nonneg (div_nonneg hT0.le (by norm_num : (0 : ℝ) ≤ 11))
    (landauSlack_nonneg N (fun n => x n * Real.sqrt n))
  linarith

/-- **Sampling at the zeros in its natural form** (RH): for every `N ≥ 1`, every real `x` on `[1, N]` and every
`T ≥ 2000N`, `Σ_{|γ_ρ| ≤ T}|Σ_{n ≤ N} x_n n^ρ|² ≥ (T/11)(log(T/N) − 7)Σ x_n² n`. -/
theorem sampling_log (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T)
    (x : ℕ → ℝ) :
    T / 11 * (Real.log (T / N) - 7) * ∑ n ∈ Icc 1 N, x n ^ 2 * n ≤
      ∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 := by
  have hS2 : ∑ n ∈ Icc 1 N, x n ^ 2 * n = S2 N (fun n => x n * Real.sqrt n) := by
    unfold BallDensity.S2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hS2]
  exact sharp_bound hRH hN hTN x

/-- **The clean form** (RH): for `T ≥ e¹⁴N`, `Σ_{|γ_ρ| ≤ T}|V_x(ρ)|² ≥ (T/22)·log(T/N)·Σ x_n² n`. -/
theorem sampling_log_clean (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {T : ℝ}
    (hTN : Real.exp 14 * N ≤ T) (x : ℕ → ℝ) :
    T / 22 * Real.log (T / N) * ∑ n ∈ Icc 1 N, x n ^ 2 * n ≤
      ∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (2000 : ℝ) ≤ Real.exp 14 := by
    have h1 : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have h2 := Real.exp_one_gt_d9
    calc (2000 : ℝ) ≤ 2.7 ^ 14 := by norm_num
      _ ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) (by linarith) 14
  have h2000 : 2000 * (N : ℝ) ≤ T := le_trans (mul_le_mul_of_nonneg_right he hN0.le) hTN
  have hT0 : 0 < T := by linarith
  have hℓ : 14 ≤ Real.log (T / N) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hN0]; exact hTN
  have h := sampling_log hRH hN h2000 x
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * n := Finset.sum_nonneg fun n _ => by positivity
  have hk : T / 22 * Real.log (T / N) ≤ T / 11 * (Real.log (T / N) - 7) := by
    nlinarith [mul_nonneg hT0.le (sub_nonneg.2 hℓ)]
  calc T / 22 * Real.log (T / N) * ∑ n ∈ Icc 1 N, x n ^ 2 * n
      ≤ T / 11 * (Real.log (T / N) - 7) * ∑ n ∈ Icc 1 N, x n ^ 2 * n := mul_le_mul_of_nonneg_right hk hS
    _ ≤ _ := h

/-- **Sampling from `T ≥ e⁸N`** (RH): `BallRate.SamplingAtZeros (1/11) e⁸ 0`, so for every `N ≥ 1`, every real `x`
on `[1, N]` and every `T ≥ e⁸N`, `Σ_{|γ_ρ| ≤ T}|Σ_{n ≤ N} x_n n^ρ|² ≥ (T/11)Σ x_n² n`. -/
theorem sampling_e8 (hRH : RiemannHypothesis) : BallRate.SamplingAtZeros (1 / 11) (Real.exp 8) 0 := by
  intro N x T hN hT
  rw [add_zero, Real.rpow_one] at hT
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (2000 : ℝ) ≤ Real.exp 8 := by
    have h1 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have h2 := Real.exp_one_gt_d9
    calc (2000 : ℝ) ≤ 2.7 ^ 8 := by norm_num
      _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
  have h2000 : 2000 * (N : ℝ) ≤ T := le_trans (mul_le_mul_of_nonneg_right he hN0.le) hT
  have hT0 : 0 < T := by linarith
  have hℓ : 8 ≤ Real.log (T / N) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hN0]; exact hT
  have h := sampling_log hRH hN h2000 x
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * n := Finset.sum_nonneg fun n _ => by positivity
  have hk : 1 / 11 * T ≤ T / 11 * (Real.log (T / N) - 7) := by
    nlinarith [mul_nonneg hT0.le (sub_nonneg.2 hℓ)]
  calc 1 / 11 * T * ∑ n ∈ Icc 1 N, x n ^ 2 * n
      ≤ T / 11 * (Real.log (T / N) - 7) * ∑ n ∈ Icc 1 N, x n ^ 2 * n := mul_le_mul_of_nonneg_right hk hS
    _ ≤ _ := h

/-- **The rate under RH**: `λ_N ≥ 1/(22e⁸N)` for every `N ≥ 1`. -/
theorem rate_sharp (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    1 / (22 * Real.exp 8 * N) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x := by
  have hC : (1 : ℝ) ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  have h := BallRate.rate_of_sampling hRH (by norm_num : (0 : ℝ) < 1 / 11) hC le_rfl (sampling_e8 hRH) hN x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : 1 / 11 / (2 * Real.exp 8) * (N : ℝ) ^ (-(1 + 0 : ℝ)) = 1 / (22 * Real.exp 8 * N) := by
    rw [add_zero, Real.rpow_neg_one]
    field_simp
    ring
  rw [e] at h
  exact h

/-- **The rate, keeping Landau's slack** (RH): `Q_N(x) ≥ (Σ_{n ≤ N}x_n² n + G(c))/(22e⁸N)` for every `N ≥ 1` and every
real `x`, with `c_n = x_n√n`; `sharp_bound_slack` at `T = e⁸N`. As `Σx_n² n ≥ Σx_n²` and `G(c) ≥ 0` it contains
`rate_sharp`. A vector with `Σx_n² n + G(c) ≥ ε·log N·Σx_n²` has `Q_N(x) ≥ (ε/22e⁸)(log N/N)Σx_n²`, so `λ_N ≫ log N/N`
is a statement about the vectors with `Σx_n² n + G(c) = o(log N·Σx_n²)` only. -/
theorem rate_slack (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    1 / (22 * Real.exp 8 * N) *
        (∑ n ∈ Icc 1 N, x n ^ 2 * n + landauSlack N (fun n => x n * Real.sqrt n)) ≤ BallWeil.form N x := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have he : (2000 : ℝ) ≤ Real.exp 8 := by
    have h1 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have h2 := Real.exp_one_gt_d9
    calc (2000 : ℝ) ≤ 2.7 ^ 8 := by norm_num
      _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
  set T : ℝ := Real.exp 8 * N with hT
  have h2000 : 2000 * (N : ℝ) ≤ T := mul_le_mul_of_nonneg_right he hN0.le
  have hT1 : 1 ≤ T := by nlinarith
  have hT0 : 0 < T := by linarith
  have hℓ : Real.log (T / N) = 8 := by rw [hT, mul_div_assoc, div_self hN0.ne', mul_one, Real.log_exp]
  have hS2 : ∑ n ∈ Icc 1 N, x n ^ 2 * n = S2 N (fun n => x n * Real.sqrt n) := by
    unfold BallDensity.S2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have h := sharp_bound_slack hRH hN h2000 x
  rw [hℓ, ← hS2] at h
  have hsum := BallRate.hasSum_form hRH N x
  have hpart : ∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤
      BallWeil.form N x := by
    rw [← hsum.tsum_eq]
    exact Summable.sum_le_tsum _ (fun q _ => by positivity) hsum.summable
  have hterm : ∀ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 / (2 * T ^ 2) ≤
      ‖BallRate.dpoly N x q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2) := by
    intro q hq
    rw [BallRate.mem_zerosUpTo] at hq
    have h1 : (zetaZeroFamily q).im ^ 2 ≤ T ^ 2 := by
      have := sq_abs (zetaZeroFamily q).im
      nlinarith [abs_nonneg (zetaZeroFamily q).im]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith
  have hzeros := Finset.sum_le_sum hterm
  rw [← Finset.sum_div] at hzeros
  calc 1 / (22 * Real.exp 8 * N) *
        (∑ n ∈ Icc 1 N, x n ^ 2 * n + landauSlack N (fun n => x n * Real.sqrt n))
      = T / 11 * ((8 - 7) * ∑ n ∈ Icc 1 N, x n ^ 2 * n + landauSlack N (fun n => x n * Real.sqrt n)) /
          (2 * T ^ 2) := by
        rw [hT]; field_simp; ring
    _ ≤ (∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2) / (2 * T ^ 2) :=
        div_le_div_of_nonneg_right h (by positivity)
    _ ≤ _ := hzeros
    _ ≤ _ := hpart

end BallSharp
