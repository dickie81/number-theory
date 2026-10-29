/-
# Ingham's density estimate for `ζ` on `7/12 ≤ σ ≤ 3/4`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `ε > 0` there is `C` such that `N(σ, T) ≤ C T^{(12/5 + ε)(1−σ)}(log T)^{12}` for
`7/12 ≤ σ ≤ 3/4` and `T ≥ 2` (`nx_ingham`). This is Ingham's estimate `N(σ, T) ≪ T^{3(1−σ)/(2−σ)+ε}`, whose exponent
`3/(2 − σ)` is at most `12/5` exactly on `σ ≤ 3/4`. It is `InghamDensity.densityXi_of_zetaCrit`'s window argument with
the fourth moment of `ζ` at well-spaced points (`ZetaFourth.zeta_fourth_moment`) in place of a pointwise bound on the
critical line, as `LinnikIngham` does over the characters mod `q`.

* `Gfun_left_le_zeta`: on the line `Re w = ½ − β` of the detector, `|G(w)|(1 + |v|)⁴ ≤ KG(1 + 2U)Y^{½−σ}/δ·|M_X||ζ|`,
  with `ζ` kept instead of bounded (`|Z(s)| = |s − 1||ζ(s)|`).
* `class3_count_ingham`: a parity class of window representatives whose zeros have `|I(ρ)| ≥ U/4` has at most
  `2AλM₁ + A²M₂/λ²` members for every `λ > 0`, with `A = 3KG Y^{½−σ}/δ`, `M₁ = MV(X)(U + X + 1)` and
  `M₂ = C₄(2U + 2)^{1+ε}`: `ml ≤ (λ/2)m² + μl⁴/(4λ) + 1/(4λμ)` at `μ = A/λ`, the mean value of the mollifier
  (`InghamDensity.mean_value_moll`) and the fourth moment at the points `γ + v`.
* `window_classes_ingham`, `window_count_ingham`: at `X = ⌊U⌋`, `Y = U^{6/5}` (`Yw` at `c = 1/10`), `δ = 1/12` and
  `λ = U^{(2/5)(½−σ)+ε/4}`, the polynomial classes carry `U^{(12/5)(1−σ)}` and the integral class
  `U^{(8/5)(½−σ)+1+ε/4}`, and `(8/5)(½ − σ) + 1 ≤ (12/5)(1 − σ)` exactly when `σ ≤ 3/4`.
* `nx_le_of_windows`: dyadic windows above `U₀ = 8`, as in `densityXi_of_zetaCrit`, for any window bound.
-/
import ZetaFourth
import InghamDensity

open Complex Real Filter Topology MeasureTheory

noncomputable section

namespace ZetaIngham

open ShortWeil PsiOmega WeilForm WeilTest DirMean Finset InghamDensity

/-! ### The weight `(1 + |v|)^{−4}` -/

/-- The weight `(1 + |v|)^{−4}`. -/
def wt4 (v : ℝ) : ℝ := ((1 + |v|) ^ 4)⁻¹

theorem wt4_pos (v : ℝ) : 0 < wt4 v := by unfold wt4; positivity

theorem continuous_wt4 : Continuous wt4 := by
  unfold wt4
  exact (by fun_prop : Continuous fun v : ℝ => (1 + |v|) ^ 4).inv₀ fun v => by positivity

theorem wt4_mul_sq_le (v : ℝ) : wt4 v * (1 + |v|) ^ 2 ≤ (1 + v ^ 2)⁻¹ := by
  have h1 : 0 < 1 + |v| := by positivity
  have h2 : 1 + v ^ 2 ≤ (1 + |v|) ^ 2 := by nlinarith [abs_nonneg v, sq_abs v]
  unfold wt4
  rw [inv_mul_eq_div, div_le_iff₀ (by positivity), mul_comm, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (1 + |v|) ^ 2 * (1 + v ^ 2) ≤ (1 + |v|) ^ 2 * (1 + |v|) ^ 2 := by gcongr
    _ = (1 + |v|) ^ 4 := by ring

theorem wt4_mul_le (v : ℝ) : wt4 v * (1 + |v|) ≤ (1 + v ^ 2)⁻¹ := by
  refine le_trans ?_ (wt4_mul_sq_le v)
  have h0 := (wt4_pos v).le
  have h1 : 1 + |v| ≤ (1 + |v|) ^ 2 := le_self_pow₀ (by linarith [abs_nonneg v]) (by norm_num)
  exact mul_le_mul_of_nonneg_left h1 h0

theorem wt4_le (v : ℝ) : wt4 v ≤ (1 + v ^ 2)⁻¹ :=
  le_trans (le_mul_of_one_le_right (wt4_pos v).le (by linarith [abs_nonneg v])) (wt4_mul_le v)

/-! ### The integral class with the fourth moment -/

/-- **On the line `Re w = ½ − β`, with `ζ` kept**: `|G(w)|(1 + |v|)⁴ ≤ KG(1 + 2U)Y^{½−σ}/δ·|M_X(½ + i(γ + v))|·
|ζ(½ + i(γ + v))|` for a zero `ρ = β + iγ` of `ζ` with `σ ≤ β < 1`, `½ + δ ≤ σ` and `|γ| ≤ 2U`. -/
theorem Gfun_left_le_zeta (X : ℕ) {σ δ U Y β γ : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hσβ : σ ≤ β)
    (hβ1 : β < 1) (hU : 0 ≤ U) (hγ : |γ| ≤ 2 * U) (hY : 1 ≤ Y) (hz : Zr ((β : ℂ) + γ * I) = 0) (v : ℝ) :
    ‖Gfun X Y ((β : ℂ) + γ * I) (((1 / 2 - ((β : ℂ) + γ * I).re : ℝ) : ℂ) + v * I)‖ * (1 + |v|) ^ 4
      ≤ KG * (1 + 2 * U) * Y ^ (1 / 2 - σ) / δ * (‖moll X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ *
        ‖riemannZeta (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖) := by
  have hre : ((β : ℂ) + γ * I).re = β := by simp
  rw [hre]
  set w : ℂ := ((1 / 2 - β : ℝ) : ℂ) + v * I with hw
  have hwre : w.re = 1 / 2 - β := by simp [hw]
  have hwim : w.im = v := by simp [hw]
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwre; simp at hwre; linarith
  have hsum : (β : ℂ) + γ * I + w = 1 / 2 + ((γ + v : ℝ) : ℂ) * I := by
    rw [hw]; push_cast; ring
  rw [Gfun_eq_left X Y hz hw0, hsum, norm_mul, norm_mul, norm_mul, norm_div]
  set l := ‖riemannZeta (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ with hl
  have hl0 : 0 ≤ l := norm_nonneg _
  have hZ : ‖Zr (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ ≤ (1 + 2 * U) * (1 + |v|) * l := by
    have hs1 : (1 / 2 + ((γ + v : ℝ) : ℂ) * I) ≠ 1 := fun h => by
      have := congrArg Complex.re h; norm_num at this
    rw [Zr_of_ne hs1, norm_mul]
    have hsub : ‖(1 / 2 + ((γ + v : ℝ) : ℂ) * I) - 1‖ ≤ (1 + 2 * U) * (1 + |v|) := by
      calc ‖(1 / 2 + ((γ + v : ℝ) : ℂ) * I) - 1‖
          ≤ |((1 / 2 + ((γ + v : ℝ) : ℂ) * I) - 1).re| + |((1 / 2 + ((γ + v : ℝ) : ℂ) * I) - 1).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = 1 / 2 + |γ + v| := by norm_num [abs_of_neg]
        _ ≤ (1 + 2 * U) * (1 + |v|) := by
            have := abs_add_le γ v
            nlinarith [abs_nonneg γ, abs_nonneg v]
    exact mul_le_mul_of_nonneg_right hsub hl0
  have hG := norm_Gamma_le' (z := w + 1) (by simp [hwre]; linarith) (by simp [hwre]; linarith)
  have hGim : (w + 1).im = v := by simp [hwim]
  rw [hGim] at hG
  have hwn : δ ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hwre, abs_of_neg (by linarith)] at this
    linarith
  have hYw : ‖(Y : ℂ) ^ w‖ ≤ Y ^ (1 / 2 - σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), hwre]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  set m := ‖moll X (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ with hm
  set g := ‖Complex.Gamma (w + 1)‖ with hg
  have hm0 : 0 ≤ m := norm_nonneg _
  have hg0 : 0 ≤ g := norm_nonneg _
  have hdiv : g / ‖w‖ ≤ g / δ := div_le_div_of_nonneg_left hg0 hδ hwn
  calc m * ‖Zr (1 / 2 + ((γ + v : ℝ) : ℂ) * I)‖ * (g / ‖w‖) * ‖(Y : ℂ) ^ w‖ * (1 + |v|) ^ 4
      ≤ m * ((1 + 2 * U) * (1 + |v|) * l) * (g / δ) * Y ^ (1 / 2 - σ) * (1 + |v|) ^ 4 := by
        gcongr
    _ = (1 + 2 * U) * Y ^ (1 / 2 - σ) / δ * (m * l) * (g * (1 + |v|) ^ 5) := by ring
    _ ≤ (1 + 2 * U) * Y ^ (1 / 2 - σ) / δ * (m * l) * KG := by gcongr
    _ = KG * (1 + 2 * U) * Y ^ (1 / 2 - σ) / δ * (m * l) := by ring

/-- `|ζ(½ + it)| ≤ C(1 + |t|)²` for every `t`: `|ζ(½ + it)| ≤ 2 + 4|t|` for `|t| ≥ 2`
(`ZetaFourth.norm_zeta_le_strip`), and continuity on `|t| ≤ 2`. -/
theorem zeta_half_poly : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * (1 + |t|) ^ 2 := by
  have hc : ContinuousOn (fun t : ℝ => riemannZeta (1 / 2 + t * I)) (Set.Icc (-2) 2) := by
    intro t _
    have hne : (1 / 2 + (t : ℂ) * I) ≠ 1 := fun h => by
      have := congrArg Complex.re h; norm_num at this
    exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => 1 / 2 + (t : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨4 + |C₂|, by positivity, fun t => ?_⟩
  rcases le_or_gt 2 |t| with ht | ht
  · have h := ZetaFourth.norm_zeta_le_strip (σ := 1 / 2) (t := t) (by norm_num) (by norm_num) ht
    have e : ((1 / 2 : ℝ) : ℂ) + t * I = 1 / 2 + t * I := by push_cast; ring
    rw [e] at h
    calc ‖riemannZeta (1 / 2 + t * I)‖ ≤ 2 + 2 * |t| / (1 / 2) := h
      _ = 2 + 4 * |t| := by ring
      _ ≤ 4 * (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
      _ ≤ (4 + |C₂|) * (1 + |t|) ^ 2 := by gcongr; linarith [abs_nonneg C₂]
  · have h := hC₂ t ⟨by linarith [(abs_lt.1 ht).1], by linarith [(abs_lt.1 ht).2]⟩
    have h1 : (1 : ℝ) ≤ (1 + |t|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg t])
    calc ‖riemannZeta (1 / 2 + t * I)‖ ≤ |C₂| := h.trans (le_abs_self C₂)
      _ ≤ (4 + |C₂|) * 1 := by linarith
      _ ≤ (4 + |C₂|) * (1 + |t|) ^ 2 := by gcongr

/-- **The integral class, Ingham's way.** For a parity class of window representatives whose zeros `ρ` have
`σ ≤ β` and `|I(ρ)| ≥ U/4`: `|C| ≤ 2AλM₁ + A²M₂/λ²` for every `λ > 0`, with `A = 3KG Y^{½−σ}/δ`,
`M₁ = MV(X)(U + X + 1)` and `M₂ = C₄(2U + 2)^{1+ε}`, given the fourth moment `Σ_r |ζ(½ + it_r)|⁴ ≤ C₄(T + 2)^{1+ε}`
over 1-separated points `|t_r| ≤ T`. -/
theorem class3_count_ingham {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + ε))
    {X : ℕ} (hX : 1 ≤ X) {σ δ U Y lam : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hU : 2 ≤ U) (hY : 1 ≤ Y)
    (hlam : 0 < lam) (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi))
    (hC : ∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n)
    (hwin : ∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1)
    (hdet : ∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U ∧
      (σ ≤ βs (rep n) ∧ U / 4 ≤ ‖Iv X Y ((βs (rep n) : ℂ) + γs (rep n) * I)‖)) :
    (C.card : ℝ) ≤ 2 * (3 * KG * Y ^ (1 / 2 - σ) / δ) * lam * (MV X * (U + X + 1)) +
      (3 * KG * Y ^ (1 / 2 - σ) / δ) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + ε)) / lam ^ 2 := by
  classical
  obtain ⟨CP, hCP0, hCP⟩ := zeta_half_poly
  set A := 3 * KG * Y ^ (1 / 2 - σ) / δ with hA
  have hKG := KG_pos
  have hA0 : 0 < A := by
    have : 0 < Y := by linarith
    positivity
  have hU0 : 0 < U := by linarith
  set M₁ := MV X * (U + X + 1) with hM₁
  set M₂ := C₄ * (2 * U + 2) ^ (1 + ε) with hM₂
  set μ := A / lam with hμ
  have hμ0 : 0 < μ := div_pos hA0 hlam
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hMV0 : 0 ≤ MV X := by unfold MV; have := Real.log_nonneg hXr; positivity
  have hM₁0 : 0 ≤ M₁ := by rw [hM₁]; positivity
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  set m : ℕ → ℝ → ℝ := fun n v => ‖moll X (1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I)‖ with hm
  set l : ℕ → ℝ → ℝ := fun n v => ‖riemannZeta (1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I)‖ with hl
  have hmc : ∀ n, Continuous (m n) := fun n => continuous_moll_line X (γs (rep n))
  have hlc : ∀ n, Continuous (l n) := by
    intro n
    refine Continuous.norm (continuous_iff_continuousAt.2 fun v => ?_)
    have hne : (1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I) ≠ 1 := fun h => by
      have := congrArg Complex.re h; norm_num at this
    exact ContinuousAt.comp (g := riemannZeta) (f := fun v : ℝ => 1 / 2 + ((γs (rep n) + v : ℝ) : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)
  have hmX : ∀ n v, m n v ≤ X := fun n v => norm_moll_le_X X (by simp)
  have hm0 : ∀ n v, 0 ≤ m n v := fun n v => norm_nonneg _
  have hl0 : ∀ n v, 0 ≤ l n v := fun n v => norm_nonneg _
  have hγU : ∀ n ∈ C, |γs (rep n)| ≤ 2 * U := fun n hn => by rw [abs_γs]; exact (hdet n hn).1
  -- `l` grows at most quadratically
  have hlb : ∀ n ∈ C, ∀ v, l n v ≤ CP * (1 + 2 * U) ^ 2 * (1 + |v|) ^ 2 := by
    intro n hn v
    have h := hCP (γs (rep n) + v)
    have hb : 1 + |γs (rep n) + v| ≤ (1 + 2 * U) * (1 + |v|) := by
      have := abs_add_le (γs (rep n)) v
      nlinarith [abs_nonneg (γs (rep n)), abs_nonneg v, hγU n hn]
    calc l n v ≤ CP * (1 + |γs (rep n) + v|) ^ 2 := h
      _ ≤ CP * ((1 + 2 * U) * (1 + |v|)) ^ 2 := by gcongr
      _ = CP * (1 + 2 * U) ^ 2 * (1 + |v|) ^ 2 := by ring
  have hint : ∀ n ∈ C, Integrable fun v => m n v * l n v * wt4 v := by
    intro n hn
    refine integrable_real_of_le (((hmc n).mul (hlc n)).mul continuous_wt4)
      (K := X * (CP * (1 + 2 * U) ^ 2)) fun v => ?_
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hm0 n v) (hl0 n v)) (wt4_pos v).le)]
    have hw := (wt4_pos v).le
    calc m n v * l n v * wt4 v ≤ X * (CP * (1 + 2 * U) ^ 2 * (1 + |v|) ^ 2) * wt4 v := by
          gcongr
          · exact hmX n v
          · exact hlb n hn v
      _ = X * (CP * (1 + 2 * U) ^ 2) * (wt4 v * (1 + |v|) ^ 2) := by ring
      _ ≤ X * (CP * (1 + 2 * U) ^ 2) * (1 + v ^ 2)⁻¹ := by
          have : 0 ≤ (X : ℝ) * (CP * (1 + 2 * U) ^ 2) := by positivity
          exact mul_le_mul_of_nonneg_left (wt4_mul_sq_le v) this
  -- (i) each zero
  have hIv : ∀ n ∈ C, 1 / 4 ≤ A / (2 * π) * ∫ v, m n v * l n v * wt4 v := by
    intro n hn
    obtain ⟨hre, hσβ, hI⟩ := hdet n hn
    have hβ1 : βs (rep n) < 1 := βs_lt_one (rep n)
    have hρ1 : ((βs (rep n) : ℂ) + γs (rep n) * I) ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hz : Zr ((βs (rep n) : ℂ) + γs (rep n) * I) = 0 :=
      Zr_zero_of_zeta (DetectCore.zeta_βsγs (rep n)) hρ1
    unfold Iv at hI
    rw [norm_mul] at hI
    have hc2 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hc2] at hI
    set B := KG * (1 + 2 * U) * Y ^ (1 / 2 - σ) / δ with hB
    have hle : ‖∫ v : ℝ, Gfun X Y ((βs (rep n) : ℂ) + γs (rep n) * I)
        (((1 / 2 - ((βs (rep n) : ℂ) + γs (rep n) * I).re : ℝ) : ℂ) + v * I)‖
        ≤ ∫ v, B * (m n v * l n v * wt4 v) := by
      refine norm_integral_le_of_norm_le ((hint n hn).const_mul B) (Eventually.of_forall fun v => ?_)
      have h := Gfun_left_le_zeta X hδ hσδ hσβ hβ1 hU0.le (hγU n hn) hY hz v
      have hp : 0 < (1 + |v|) ^ 4 := by positivity
      have e : B * (m n v * l n v * wt4 v) = B * (m n v * l n v) / (1 + |v|) ^ 4 := by
        unfold wt4; ring
      rw [e, le_div_iff₀ hp]
      exact h
    rw [integral_const_mul] at hle
    have hBA : B ≤ U * A := by
      rw [hB, hA]
      have hY0 : 0 ≤ Y ^ (1 / 2 - σ) := Real.rpow_nonneg (by linarith) _
      have h3 : 1 + 2 * U ≤ 3 * U := by linarith
      calc KG * (1 + 2 * U) * Y ^ (1 / 2 - σ) / δ ≤ KG * (3 * U) * Y ^ (1 / 2 - σ) / δ := by gcongr
        _ = U * (3 * KG * Y ^ (1 / 2 - σ) / δ) := by ring
    have hI0 : 0 ≤ ∫ v, m n v * l n v * wt4 v :=
      integral_nonneg fun v => mul_nonneg (mul_nonneg (hm0 n v) (hl0 n v)) (wt4_pos v).le
    have hmain : U / 4 ≤ U * (A / (2 * π) * ∫ v, m n v * l n v * wt4 v) := by
      calc U / 4 ≤ 1 / (2 * π) * ‖∫ v : ℝ, Gfun X Y ((βs (rep n) : ℂ) + γs (rep n) * I)
            (((1 / 2 - ((βs (rep n) : ℂ) + γs (rep n) * I).re : ℝ) : ℂ) + v * I)‖ := hI
        _ ≤ 1 / (2 * π) * (B * ∫ v, m n v * l n v * wt4 v) := by gcongr
        _ ≤ 1 / (2 * π) * ((U * A) * ∫ v, m n v * l n v * wt4 v) := by gcongr
        _ = U * (A / (2 * π) * ∫ v, m n v * l n v * wt4 v) := by ring
    have h4' : U * (1 / 4) ≤ U * (A / (2 * π) * ∫ v, m n v * l n v * wt4 v) := by linarith
    exact le_of_mul_le_mul_left h4' hU0
  -- (ii) the sum over the class
  have hsum1 : (C.card : ℝ) * (1 / 4) ≤ A / (2 * π) * ∫ v, ∑ n ∈ C, m n v * l n v * wt4 v := by
    rw [integral_finsetSum C fun n hn => hint n hn, mul_sum, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hIv
  -- (iii) pointwise
  have hR := card_class_le hU0.le C rep hwin fun n hn => (hdet n hn).1
  have hsep := sep_of_windows C rep hC hwin
  set K' := lam / 2 * M₁ + μ / (4 * lam) * M₂ + (C.card : ℝ) * (1 / (4 * lam * μ)) with hK'
  have hpt : ∀ v : ℝ, ∑ n ∈ C, m n v * l n v * wt4 v ≤ K' * (1 + v ^ 2)⁻¹ := by
    intro v
    have hamgm : ∀ n, m n v * l n v ≤ lam / 2 * m n v ^ 2 + μ / (4 * lam) * l n v ^ 4 + 1 / (4 * lam * μ) := by
      intro n
      have h1 : m n v * l n v ≤ lam / 2 * m n v ^ 2 + l n v ^ 2 / (2 * lam) := by
        have e : lam / 2 * m n v ^ 2 + l n v ^ 2 / (2 * lam) - m n v * l n v =
            (lam * m n v - l n v) ^ 2 / (2 * lam) := by field_simp; ring
        have : 0 ≤ (lam * m n v - l n v) ^ 2 / (2 * lam) := by positivity
        linarith
      have h2 : l n v ^ 2 ≤ μ / 2 * l n v ^ 4 + 1 / (2 * μ) := by
        have e : μ / 2 * l n v ^ 4 + 1 / (2 * μ) - l n v ^ 2 = (μ * l n v ^ 2 - 1) ^ 2 / (2 * μ) := by
          field_simp; ring
        have : 0 ≤ (μ * l n v ^ 2 - 1) ^ 2 / (2 * μ) := by positivity
        linarith
      have h3 : l n v ^ 2 / (2 * lam) ≤ (μ / 2 * l n v ^ 4 + 1 / (2 * μ)) / (2 * lam) := by gcongr
      have e3 : (μ / 2 * l n v ^ 4 + 1 / (2 * μ)) / (2 * lam) =
          μ / (4 * lam) * l n v ^ 4 + 1 / (4 * lam * μ) := by field_simp; ring
      linarith
    have hsepv : ∀ n ∈ C, ∀ k ∈ C, n ≠ k → 1 ≤ |γs (rep n) + v - (γs (rep k) + v)| := by
      intro n hn k hk hnk
      rw [show γs (rep n) + v - (γs (rep k) + v) = γs (rep n) - γs (rep k) by ring]
      exact hsep n hn k hk hnk
    have hmv := mean_value_moll hX hU0.le (abs_nonneg v) C (fun n => γs (rep n) + v) hsepv
      (fun n hn => by
        have h1 := abs_add_le (γs (rep n)) v
        have h2 := hγU n hn
        linarith) hR
    have hS2 : ∑ n ∈ C, m n v ^ 2 ≤ M₁ * (1 + |v|) := by
      have hb : U + X + 1 + |v| ≤ (U + X + 1) * (1 + |v|) := by nlinarith [abs_nonneg v]
      calc ∑ n ∈ C, m n v ^ 2 ≤ MV X * (U + X + 1 + |v|) := hmv
        _ ≤ MV X * ((U + X + 1) * (1 + |v|)) := by gcongr
        _ = M₁ * (1 + |v|) := by rw [hM₁]; ring
    have h4v := h4 C (fun n => γs (rep n) + v) hsepv (2 * U + |v|) (by positivity)
      (fun n hn => by
        have h1 := abs_add_le (γs (rep n)) v
        have h2 := hγU n hn
        linarith)
    have hS4 : ∑ n ∈ C, l n v ^ 4 ≤ M₂ * (1 + |v|) ^ 2 := by
      have hb : 2 * U + |v| + 2 ≤ (2 * U + 2) * (1 + |v|) := by nlinarith [abs_nonneg v]
      have hv1 : (1 : ℝ) ≤ 1 + |v| := by linarith [abs_nonneg v]
      have hp1 : (2 * U + |v| + 2) ^ (1 + ε) ≤ (2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ 2 := by
        calc (2 * U + |v| + 2) ^ (1 + ε) ≤ ((2 * U + 2) * (1 + |v|)) ^ (1 + ε) :=
              Real.rpow_le_rpow (by positivity) hb (by linarith)
          _ = (2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ (1 + ε) := Real.mul_rpow (by positivity) (by positivity)
          _ ≤ (2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ (2 : ℝ) := by
              exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hv1 (by linarith))
                (by positivity)
          _ = (2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ 2 := by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc ∑ n ∈ C, l n v ^ 4 ≤ C₄ * (2 * U + |v| + 2) ^ (1 + ε) := h4v
        _ ≤ C₄ * ((2 * U + 2) ^ (1 + ε) * (1 + |v|) ^ 2) := by gcongr
        _ = M₂ * (1 + |v|) ^ 2 := by rw [hM₂]; ring
    have hw0 := (wt4_pos v).le
    have hw1 := wt4_mul_le v
    have hw2 := wt4_mul_sq_le v
    have hw := wt4_le v
    have ha0 : 0 ≤ lam / 2 * M₁ := by positivity
    have hb0 : 0 ≤ μ / (4 * lam) * M₂ := by positivity
    have hc0 : 0 ≤ (C.card : ℝ) * (1 / (4 * lam * μ)) := by positivity
    calc ∑ n ∈ C, m n v * l n v * wt4 v = wt4 v * ∑ n ∈ C, m n v * l n v := by
          rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
      _ ≤ wt4 v * ∑ n ∈ C, (lam / 2 * m n v ^ 2 + μ / (4 * lam) * l n v ^ 4 + 1 / (4 * lam * μ)) := by
          gcongr with n hn; exact hamgm n
      _ = wt4 v * (lam / 2 * ∑ n ∈ C, m n v ^ 2 + μ / (4 * lam) * ∑ n ∈ C, l n v ^ 4 +
            (C.card : ℝ) * (1 / (4 * lam * μ))) := by
          rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ wt4 v * (lam / 2 * (M₁ * (1 + |v|)) + μ / (4 * lam) * (M₂ * (1 + |v|) ^ 2) +
            (C.card : ℝ) * (1 / (4 * lam * μ))) := by gcongr
      _ = lam / 2 * M₁ * (wt4 v * (1 + |v|)) + μ / (4 * lam) * M₂ * (wt4 v * (1 + |v|) ^ 2) +
            (C.card : ℝ) * (1 / (4 * lam * μ)) * wt4 v := by ring
      _ ≤ lam / 2 * M₁ * (1 + v ^ 2)⁻¹ + μ / (4 * lam) * M₂ * (1 + v ^ 2)⁻¹ +
            (C.card : ℝ) * (1 / (4 * lam * μ)) * (1 + v ^ 2)⁻¹ := by gcongr
      _ = K' * (1 + v ^ 2)⁻¹ := by rw [hK']; ring
  -- (iv) integrate
  have hint_sum : Integrable fun v => ∑ n ∈ C, m n v * l n v * wt4 v :=
    integrable_finsetSum C fun n hn => hint n hn
  have hI2 : ∫ v, ∑ n ∈ C, m n v * l n v * wt4 v ≤ K' * π := by
    calc ∫ v, ∑ n ∈ C, m n v * l n v * wt4 v ≤ ∫ v, K' * (1 + v ^ 2)⁻¹ :=
          integral_mono hint_sum (integrable_inv_one_add_sq.const_mul K') hpt
      _ = K' * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hpi : 0 < π := Real.pi_pos
  have hfin : (C.card : ℝ) * (1 / 4) ≤ A / 2 * K' := by
    calc (C.card : ℝ) * (1 / 4) ≤ A / (2 * π) * ∫ v, ∑ n ∈ C, m n v * l n v * wt4 v := hsum1
      _ ≤ A / (2 * π) * (K' * π) := by gcongr
      _ = A / 2 * K' := by field_simp
  rw [hK'] at hfin
  have e : A / 2 * (lam / 2 * M₁ + μ / (4 * lam) * M₂ + (C.card : ℝ) * (1 / (4 * lam * μ))) =
      A * lam * M₁ / 4 + (A ^ 2 * M₂ / lam ^ 2) / 8 + (C.card : ℝ) / 8 := by
    rw [hμ]; field_simp; ring
  rw [e] at hfin
  linarith

/-! ### One window -/

/-- **The three classes in one window, Ingham's way.** `InghamDensity.window_classes` with `class3_count_ingham` for
the integral class. -/
theorem window_classes_ingham {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + ε))
    {σ δ U Y lam : ℝ} (hδ : 0 < δ) (hσδ : 1 / 2 + δ ≤ σ) (hσ1 : σ ≤ 1) (hU : 2 ≤ U) (hY : 8 ≤ Y) (hUY : U ≤ Y)
    (hlam : 0 < lam) {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (Z : Finset (ZeroIdx (sqF Xi)))
    (hZ : ∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) :
    (Z.card : ℝ) ≤ 2 * Kloc (2 * U + 1) * (2 * (((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * X * N)) ^ 6
        * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ))))
      + (2 * (3 * KG * Y ^ (1 / 2 - σ) / δ) * lam * (MV X * (U + X + 1)) +
        (3 * KG * Y ^ (1 / 2 - σ) / δ) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + ε)) / lam ^ 2)) := by
  classical
  have hU0 : 0 ≤ U := by linarith
  have hY0 : 0 < Y := by linarith
  set B1 := ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2 * (32 * Real.exp 1
      * (1 + Real.log (2 * X * N)) ^ 6 * (U * (X : ℝ) ^ (1 - 2 * σ) + ((X : ℝ) * N) ^ (2 - 2 * σ))) with hB1
  set B3 := 2 * (3 * KG * Y ^ (1 / 2 - σ) / δ) * lam * (MV X * (U + X + 1)) +
      (3 * KG * Y ^ (1 / 2 - σ) / δ) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + ε)) / lam ^ 2 with hB3
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB10 : 0 ≤ B1 := by
    have : 0 ≤ 1 + Real.log (2 * X * N) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * X * N by nlinarith)
      linarith
    positivity
  have hB30 : 0 ≤ B3 := by
    have : 0 ≤ MV X := by unfold MV; have := Real.log_nonneg hXr; positivity
    have := KG_pos
    positivity
  have htri : ∀ i ∈ Z, 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖ ∨ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
      ∨ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖ := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hZ i hi
    exact trichotomy hX hN hY hU hUY hM (by linarith) (βs_lt_one i) (by rw [abs_γs]; exact h1)
      (by rw [abs_γs]; exact h2) (DetectCore.zeta_βsγs i)
  set Z1 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖
  set Z2 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
  set Z3 := Z.filter fun i => U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖
  have hcover : Z ⊆ Z1 ∪ Z2 ∪ Z3 := by
    intro i hi
    rcases htri i hi with h | h | h
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_right _ (mem_filter.2 ⟨hi, h⟩)
  have hb1 : ∀ j, ‖b1 X Y j‖ ≤ (j.divisors.card : ℝ) := norm_b1_le X hY0
  have hb2 : ∀ j, ‖b2 X Y j‖ ≤ (j.divisors.card : ℝ) := norm_b2_le X hY0
  have hσ2 : 1 / 2 ≤ σ := by linarith
  have hZ1 : (Z1.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖) Z1
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet =>
        class_count_b (b1 X Y) hb1 hσ2 hσ1 hU hX hN (by norm_num) C rep hC hwin hdet
  have hZ2 : (Z2.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖) Z2
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet =>
        class_count_b (b2 X Y) hb2 hσ2 hσ1 hU hX hN (by norm_num) C rep hC hwin hdet
  have hZ3 : (Z3.card : ℝ) ≤ 2 * B3 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖) Z3
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB30 fun C rep hC hwin hdet =>
        class3_count_ingham hε0 hε1 hC₄ h4 hX hδ hσδ hU (by linarith) hlam C rep hC hwin hdet
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2 ∪ Z3).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card + Z3.card := by
        have h1 := card_union_le (Z1 ∪ Z2) Z3
        have h2 := card_union_le Z1 Z2
        exact_mod_cast h1.trans (by omega)
    _ ≤ 2 * B1 * Kloc (2 * U + 1) + 2 * B1 * Kloc (2 * U + 1) + 2 * B3 * Kloc (2 * U + 1) := by
        linarith
    _ = 2 * Kloc (2 * U + 1) * (2 * B1 + B3) := by ring

/-! ### The window bound at Ingham's parameters -/

/-- The window constant at `δ = 1/12`. -/
def Cwi (C₄ : ℝ) : ℝ :=
  2 * Kc * (2 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71) + (172800 * KG + 11664 * KG ^ 2 * C₄))

theorem Cwi_nonneg {C₄ : ℝ} (hC₄ : 0 ≤ C₄) : 0 ≤ Cwi C₄ := by
  unfold Cwi; have := Kc_nonneg; have := KG_pos; positivity

/-- **The integral class at Ingham's parameters**: at `X = ⌊U⌋`, `Y = U^{6/5}`, `δ = 1/12` and
`λ = U^{(2/5)(½−σ)+ε/4}`, with the fourth moment at `3ε/4`, `2AλM₁ + A²M₂/λ² ≤ (172800KG + 11664KG²C₄)(log U)⁵
U^{(8/5)(½−σ)+1+ε/4}`. -/
theorem bound_B3_ingham {ε C₄ σ U : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hC₄ : 0 ≤ C₄) (hU : 8 ≤ U) :
    2 * (3 * KG * (Yw (1 / 10) U) ^ (1 / 2 - σ) / (1 / 12)) * U ^ (2 / 5 * (1 / 2 - σ) + ε / 4) *
        (MV (Xw U) * (U + (Xw U) + 1)) +
      (3 * KG * (Yw (1 / 10) U) ^ (1 / 2 - σ) / (1 / 12)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) /
        (U ^ (2 / 5 * (1 / 2 - σ) + ε / 4)) ^ 2
      ≤ (172800 * KG + 11664 * KG ^ 2 * C₄) * Real.log U ^ 5 * U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hL := log_ge_two hU
  have hKG := KG_pos
  have hMV := bound_MV hU
  have hMV0 : 0 ≤ MV (Xw U) := by
    unfold MV; have := Real.log_nonneg (by exact_mod_cast Xw_one hU : (1 : ℝ) ≤ Xw U); positivity
  have hXU := Xw_le hU
  have hY : (Yw (1 / 10) U) ^ (1 / 2 - σ) = U ^ (6 / 5 * (1 / 2 - σ)) := by
    unfold Yw; rw [← Real.rpow_mul hU0.le]; norm_num
  set a := U ^ (6 / 5 * (1 / 2 - σ)) with ha
  set l := U ^ (2 / 5 * (1 / 2 - σ) + ε / 4) with hl
  have ha0 : 0 < a := by positivity
  have hl0 : 0 < l := by positivity
  rw [hY]
  -- the first term
  have hM₁ : MV (Xw U) * (U + (Xw U) + 1) ≤ 800 * Real.log U ^ 5 * (3 * U) := by
    have h3 : U + (Xw U : ℝ) + 1 ≤ 3 * U := by linarith
    gcongr
  have hal : a * l = U ^ (8 / 5 * (1 / 2 - σ) + ε / 4) := by
    rw [ha, hl, ← Real.rpow_add hU0]; congr 1; ring
  have hE1 : U ^ (8 / 5 * (1 / 2 - σ) + ε / 4) * U = U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by
    rw [← Real.rpow_add_one hU0.ne']; congr 1; ring
  have hT1 : 2 * (3 * KG * a / (1 / 12)) * l * (MV (Xw U) * (U + (Xw U) + 1))
      ≤ 172800 * KG * Real.log U ^ 5 * U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by
    calc 2 * (3 * KG * a / (1 / 12)) * l * (MV (Xw U) * (U + (Xw U) + 1))
        ≤ 2 * (3 * KG * a / (1 / 12)) * l * (800 * Real.log U ^ 5 * (3 * U)) := by gcongr
      _ = 172800 * KG * Real.log U ^ 5 * ((a * l) * U) := by ring
      _ = 172800 * KG * Real.log U ^ 5 * U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by rw [hal, hE1]
  -- the second term
  have hM₂ : (2 * U + 2) ^ (1 + 3 * ε / 4) ≤ 9 * U ^ (1 + 3 * ε / 4) := by
    calc (2 * U + 2) ^ (1 + 3 * ε / 4) ≤ (3 * U) ^ (1 + 3 * ε / 4) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (3 : ℝ) ^ (1 + 3 * ε / 4) * U ^ (1 + 3 * ε / 4) := Real.mul_rpow (by norm_num) hU0.le
      _ ≤ 9 * U ^ (1 + 3 * ε / 4) := by
          gcongr
          calc (3 : ℝ) ^ (1 + 3 * ε / 4) ≤ 3 ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 9 := by norm_num
  have hE2 : a ^ 2 * U ^ (1 + 3 * ε / 4) / l ^ 2 = U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by
    rw [ha, hl, ← Real.rpow_natCast (U ^ (6 / 5 * (1 / 2 - σ))), ← Real.rpow_natCast
      (U ^ (2 / 5 * (1 / 2 - σ) + ε / 4)), ← Real.rpow_mul hU0.le, ← Real.rpow_mul hU0.le,
      ← Real.rpow_add hU0, ← Real.rpow_sub hU0]
    congr 1; push_cast; ring
  have hT2 : (3 * KG * a / (1 / 12)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) / l ^ 2
      ≤ 11664 * KG ^ 2 * C₄ * U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by
    have hl2 : 0 < l ^ 2 := by positivity
    calc (3 * KG * a / (1 / 12)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) / l ^ 2
        ≤ (3 * KG * a / (1 / 12)) ^ 2 * (C₄ * (9 * U ^ (1 + 3 * ε / 4))) / l ^ 2 := by gcongr
      _ = 11664 * KG ^ 2 * C₄ * (a ^ 2 * U ^ (1 + 3 * ε / 4) / l ^ 2) := by ring
      _ = 11664 * KG ^ 2 * C₄ * U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by rw [hE2]
  have hL5 : 1 ≤ Real.log U ^ 5 := one_le_pow₀ (by linarith)
  have hP : 0 ≤ U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by positivity
  have hT2' : 11664 * KG ^ 2 * C₄ * U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4)
      ≤ 11664 * KG ^ 2 * C₄ * Real.log U ^ 5 * U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by
    have : 0 ≤ 11664 * KG ^ 2 * C₄ * U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) := by positivity
    nlinarith
  nlinarith

/-- **One window, Ingham's way**: for `7/12 ≤ σ ≤ 3/4` and `U ≥ 8`, at most
`Cwi(C₄)(log U)^{11}U^{(12/5)(1−σ)+ε/4}` zeros with `U ≤ |γ| ≤ 2U` and `β ≥ σ`, given the fourth moment of `ζ` at
`3ε/4` with constant `C₄`. -/
theorem window_count_ingham {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + 3 * ε / 4))
    {σ U : ℝ} (hσ : 7 / 12 ≤ σ) (hσ1 : σ ≤ 3 / 4) (hU : 8 ≤ U) (Z : Finset (ZeroIdx (sqF Xi)))
    (hZ : ∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) :
    (Z.card : ℝ) ≤ Cwi C₄ * Real.log U ^ 11 * U ^ (12 / 5 * (1 - σ) + ε / 4) := by
  have hc0 : (0 : ℝ) ≤ 1 / 10 := by norm_num
  have hc1 : (1 / 10 : ℝ) ≤ 1 := by norm_num
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hY := Yw_ge hc0 hU
  have hwc := window_classes_ingham (ε := 3 * ε / 4) (by linarith) (by linarith) hC₄ h4 (δ := 1 / 12)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith) hY
    (lam := U ^ (2 / 5 * (1 / 2 - σ) + ε / 4)) (by positivity) (Xw_one hU) Nw_one (XN_ge hU) Z hZ
  refine hwc.trans ?_
  set L := Real.log U with hLdef
  set E := 12 / 5 * (1 - σ) with hE
  have hL := log_ge_two hU
  have hL1 : 1 ≤ L := by linarith
  have hE' : (2 + 4 * (1 / 10 : ℝ)) * (1 - σ) = E := by rw [hE]; ring
  have hUE : 0 ≤ U ^ E := by positivity
  have hK := bound_K hc0 hc1 hU
  have hl := bound_ell hc0 hc1 hU
  have hS := bound_S1 hc0 hc1 (σ := σ) (by linarith) (by linarith) hU
  rw [hE'] at hS
  have hB3 := bound_B3_ingham (σ := σ) hε0 hε1 hC₄ hU
  have hKl := Kloc_le (U := U) (by linarith)
  have hKl0 : 0 ≤ Kloc (2 * U + 1) := Kloc_nonneg (by linarith)
  have he : 32 * Real.exp 1 ≤ 96 := by have := Real.exp_one_lt_d9; linarith
  have hK0 : (0 : ℝ) ≤ ((Nat.log 2 (Nw (1 / 10) U) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX1 : (1 : ℝ) ≤ Xw U := by exact_mod_cast Xw_one hU
  have hN1 : (1 : ℝ) ≤ Nw (1 / 10) U := by exact_mod_cast (Nw_one (c := 1 / 10) (U := U))
  have hl0 : 0 ≤ 1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 10) U)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (Xw U : ℝ) * (Nw (1 / 10) U) by nlinarith)
    linarith
  have hS0 : 0 ≤ U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 10) U)) ^ (2 - 2 * σ) := by positivity
  have e16 : ∀ x : ℝ, x / (1 / 4) ^ 2 = 16 * x := fun x => by norm_num [div_eq_mul_inv]; ring
  have hEe : U ^ E ≤ U ^ (E + ε / 4) := Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
  have hT1 : ((Nat.log 2 (Nw (1 / 10) U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 10) U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 10) U)) ^ (2 - 2 * σ)))
      ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ (E + ε / 4) := by
    rw [e16]
    calc 16 * ((Nat.log 2 (Nw (1 / 10) U) + 1 : ℕ) : ℝ) ^ 3
          * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 10) U))) ^ 6
            * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 10) U)) ^ (2 - 2 * σ)))
        ≤ 16 * (13 * L) ^ 3 * (96 * (9 * L) ^ 6 * (71 * L * U ^ E)) := by gcongr
      _ = 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ E := by ring
      _ ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ (E + ε / 4) := by gcongr
  have hexp : 8 / 5 * (1 / 2 - σ) + 1 + ε / 4 ≤ E + ε / 4 := by rw [hE]; linarith
  have hB3' : 2 * (3 * KG * (Yw (1 / 10) U) ^ (1 / 2 - σ) / (1 / 12)) * U ^ (2 / 5 * (1 / 2 - σ) + ε / 4) *
        (MV (Xw U) * (U + (Xw U) + 1)) +
      (3 * KG * (Yw (1 / 10) U) ^ (1 / 2 - σ) / (1 / 12)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) /
        (U ^ (2 / 5 * (1 / 2 - σ) + ε / 4)) ^ 2
      ≤ (172800 * KG + 11664 * KG ^ 2 * C₄) * L ^ 10 * U ^ (E + ε / 4) := by
    refine hB3.trans ?_
    have h510 : L ^ 5 ≤ L ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
    have := KG_pos
    have hU' : U ^ (8 / 5 * (1 / 2 - σ) + 1 + ε / 4) ≤ U ^ (E + ε / 4) :=
      Real.rpow_le_rpow_of_exponent_le hU1 hexp
    gcongr
  have hKlL : Kloc (2 * U + 1) ≤ Kc * L := hKl
  have hsum0 : 0 ≤ 2 * (((Nat.log 2 (Nw (1 / 10) U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 10) U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 10) U)) ^ (2 - 2 * σ))))
      + (2 * (3 * KG * (Yw (1 / 10) U) ^ (1 / 2 - σ) / (1 / 12)) * U ^ (2 / 5 * (1 / 2 - σ) + ε / 4) *
        (MV (Xw U) * (U + (Xw U) + 1)) +
      (3 * KG * (Yw (1 / 10) U) ^ (1 / 2 - σ) / (1 / 12)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) /
        (U ^ (2 / 5 * (1 / 2 - σ) + ε / 4)) ^ 2) := by
    have : 0 ≤ MV (Xw U) := by unfold MV; have := Real.log_nonneg hX1; positivity
    have := KG_pos
    have : 0 < Yw (1 / 10) U := by unfold Yw; positivity
    positivity
  have hKcL : 0 ≤ 2 * (Kc * L) := by have := Kc_nonneg; positivity
  calc 2 * Kloc (2 * U + 1) * (2 * (((Nat.log 2 (Nw (1 / 10) U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 10) U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 10) U)) ^ (2 - 2 * σ))))
      + (2 * (3 * KG * (Yw (1 / 10) U) ^ (1 / 2 - σ) / (1 / 12)) * U ^ (2 / 5 * (1 / 2 - σ) + ε / 4) *
        (MV (Xw U) * (U + (Xw U) + 1)) +
      (3 * KG * (Yw (1 / 10) U) ^ (1 / 2 - σ) / (1 / 12)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) /
        (U ^ (2 / 5 * (1 / 2 - σ) + ε / 4)) ^ 2))
      ≤ 2 * (Kc * L) * (2 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ (E + ε / 4))
          + (172800 * KG + 11664 * KG ^ 2 * C₄) * L ^ 10 * U ^ (E + ε / 4)) := by
        gcongr
    _ = Cwi C₄ * L ^ 11 * U ^ (E + ε / 4) := by unfold Cwi; ring

/-! ### Dyadic windows -/

/-- **Density from window counts.** If every window `[U, 2U]` with `U ≥ 8` holds at most `Cw(log U)^{11}U^e`
zeros with `β ≥ σ`, then `N(σ, T) ≤ (2^{12}C₀ + 4Cw)T^e(log T)^{12}` for `T ≥ 2`, with `C₀` the number of zeros with
`|γ| ≤ 8`: the dyadic windows above `U₀ = 8` of `InghamDensity.densityXi_of_zetaCrit`. -/
theorem nx_le_of_windows {σ e Cw : ℝ} (he : 0 ≤ e) (hCw : 0 ≤ Cw)
    (hwin : ∀ U : ℝ, 8 ≤ U → ∀ Z : Finset (ZeroIdx (sqF Xi)),
      (∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) →
        (Z.card : ℝ) ≤ Cw * Real.log U ^ 11 * U ^ e)
    {T : ℝ} (hT : 2 ≤ T) :
    (NX (σ - 1 / 2) T : ℝ) ≤
      (((finite_re_le 8).toFinset.card : ℝ) * 2 ^ 12 + 4 * Cw) * T ^ e * Real.log T ^ 12 := by
  classical
  set U₀ : ℝ := 8 with hU₀
  set C0 : ℝ := ((finite_re_le U₀).toFinset.card : ℝ) with hC0
  have hC00 : 0 ≤ C0 := Nat.cast_nonneg _
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlT := half_le_log hT
  have hTe : 1 ≤ T ^ e := Real.one_le_rpow hT1 he
  rw [NX_eq_card]
  set S := (finite_re_le T).toFinset.filter fun i => σ - 1 / 2 ≤ |(tau i).im| with hS
  set mm : ZeroIdx (sqF Xi) → ℕ := fun i => ⌊|(tau i).re| / U₀⌋₊ with hmm
  set kk : ZeroIdx (sqF Xi) → ℕ := fun i => Nat.log 2 (mm i) with hkk
  set L := Nat.log 2 ⌊T / U₀⌋₊ + 1 with hL
  set Slow := S.filter fun i => |(tau i).re| ≤ U₀ with hSlow
  set Z : ℕ → Finset (ZeroIdx (sqF Xi)) := fun k => S.filter fun i => U₀ < |(tau i).re| ∧ kk i = k
    with hZ
  have hU₀0 : 0 < U₀ := by rw [hU₀]; norm_num
  have hcover : S ⊆ Slow ∪ (range L).biUnion Z := by
    intro i hi
    by_cases hlow : |(tau i).re| ≤ U₀
    · exact mem_union_left _ (mem_filter.2 ⟨hi, hlow⟩)
    · push Not at hlow
      refine mem_union_right _ (mem_biUnion.2 ⟨kk i, mem_range.2 ?_, mem_filter.2 ⟨hi, hlow, rfl⟩⟩)
      have hiT : |(tau i).re| ≤ T := by
        have := (mem_filter.1 hi).1; simpa using this
      have hmT : mm i ≤ ⌊T / U₀⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_right hiT hU₀0.le)
      exact Nat.lt_succ_of_le (Nat.log_mono_right hmT)
  have hlowc : (Slow.card : ℝ) ≤ C0 := by
    rw [hC0]
    exact_mod_cast card_le_card fun i hi => by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; exact (mem_filter.1 hi).2
  have hwinb : ∀ k ∈ range L, ((Z k).card : ℝ) ≤ Cw * Real.log T ^ 11 * T ^ e := by
    intro k _
    rcases (Z k).eq_empty_or_nonempty with hZe | ⟨i1, hi1⟩
    · rw [hZe, card_empty, Nat.cast_zero]; positivity
    set U := (2 : ℝ) ^ k * U₀ with hUdef
    have hUU₀ : U₀ ≤ U := by
      rw [hUdef]; exact le_mul_of_one_le_left hU₀0.le (one_le_pow₀ (by norm_num))
    have hU8 : 8 ≤ U := by rw [hU₀] at hUU₀; exact hUU₀
    have hwinU : ∀ i ∈ Z k, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U := by
      intro i hi
      obtain ⟨_, hlow, hk⟩ := mem_filter.1 hi
      have hm1 : 1 ≤ mm i := by
        simp only [hmm]; rw [Nat.one_le_floor_iff, le_div_iff₀ hU₀0]; linarith
      have hmne : mm i ≠ 0 := by omega
      have h1 := Nat.pow_log_le_self 2 hmne
      have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (mm i)
      simp only [hkk] at hk
      rw [hk] at h1 h2
      have hr1 : ((2 ^ k : ℕ) : ℝ) ≤ mm i := by exact_mod_cast h1
      have hr2 : (mm i : ℝ) + 1 ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h2
      have hf1 := Nat.floor_le (div_nonneg (abs_nonneg (tau i).re) hU₀0.le)
      have hf2 := Nat.lt_floor_add_one (|(tau i).re| / U₀)
      simp only [hmm] at hr1 hr2
      push_cast at hr1 hr2
      rw [pow_succ] at hr2
      constructor
      · rw [hUdef]; rw [le_div_iff₀ hU₀0] at hf1; nlinarith
      · rw [hUdef]; rw [div_lt_iff₀ hU₀0] at hf2; nlinarith
    have hc := hwin U hU8 (Z k) fun i hi => by
      obtain ⟨hlo, hhi⟩ := hwinU i hi
      have hβ : σ ≤ βs i := by
        have := (mem_filter.1 (mem_filter.1 hi).1).2; unfold βs; linarith
      exact ⟨hlo, hhi, hβ⟩
    have hUT : U ≤ T := by
      have := (hwinU i1 hi1).1
      have hiT : |(tau i1).re| ≤ T := by
        have := (mem_filter.1 (mem_filter.1 hi1).1).1; simpa using this
      linarith
    have hlU : Real.log U ≤ Real.log T := Real.log_le_log (by linarith) hUT
    have hlU0 : 0 ≤ Real.log U := by linarith [log_ge_two hU8]
    calc ((Z k).card : ℝ) ≤ Cw * Real.log U ^ 11 * U ^ e := hc
      _ ≤ Cw * Real.log T ^ 11 * T ^ e := by gcongr
  have hLle : (L : ℝ) ≤ 4 * Real.log T := by
    have h1 : (Nat.log 2 ⌊T / U₀⌋₊ : ℝ) ≤ Real.log T / Real.log 2 := by
      rcases Nat.eq_zero_or_pos ⌊T / U₀⌋₊ with h0 | hpos
      · rw [h0, Nat.log_zero_right, Nat.cast_zero]
        exact div_nonneg (by linarith) (Real.log_nonneg (by norm_num))
      · refine (natLog_le _ hpos).trans ?_
        apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
        apply Real.log_le_log (by exact_mod_cast hpos)
        calc (⌊T / U₀⌋₊ : ℝ) ≤ T / U₀ := Nat.floor_le (by positivity)
          _ ≤ T := div_le_self hT0.le (by rw [hU₀]; norm_num)
    have h2 : Real.log T / Real.log 2 ≤ 3 / 2 * Real.log T := by
      rw [div_le_iff₀ (Real.log_pos (by norm_num))]
      have := Real.log_two_gt_d9
      nlinarith
    rw [hL]; push_cast; linarith
  have hsum : ((range L).biUnion Z).card ≤ ∑ k ∈ range L, (Z k).card := card_biUnion_le
  calc (S.card : ℝ) ≤ ((Slow ∪ (range L).biUnion Z).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Slow.card + ((range L).biUnion Z).card := by exact_mod_cast card_union_le _ _
    _ ≤ C0 + ∑ k ∈ range L, ((Z k).card : ℝ) := by
        gcongr
        exact_mod_cast hsum
    _ ≤ C0 + ∑ _k ∈ range L, Cw * Real.log T ^ 11 * T ^ e := by gcongr with k hk; exact hwinb k hk
    _ = C0 + L * (Cw * Real.log T ^ 11 * T ^ e) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ C0 * (2 ^ 12 * Real.log T ^ 12 * T ^ e) + (4 * Real.log T) * (Cw * Real.log T ^ 11 * T ^ e) := by
        have h1 := one_le_pow12 hT
        have h2 : (1 : ℝ) ≤ 2 ^ 12 * Real.log T ^ 12 * T ^ e := one_le_mul_of_one_le_of_one_le h1 hTe
        have hlT0 : 0 ≤ Real.log T := by linarith
        have hW0 : 0 ≤ Cw * Real.log T ^ 11 * T ^ e :=
          mul_nonneg (mul_nonneg hCw (pow_nonneg hlT0 11)) (by linarith)
        refine add_le_add ?_ (mul_le_mul_of_nonneg_right hLle hW0)
        calc C0 = C0 * 1 := by ring
          _ ≤ C0 * (2 ^ 12 * Real.log T ^ 12 * T ^ e) := mul_le_mul_of_nonneg_left h2 hC00
    _ = (C0 * 2 ^ 12 + 4 * Cw) * T ^ e * Real.log T ^ 12 := by ring

/-! ### Ingham's estimate on `7/12 ≤ σ ≤ 3/4` -/

/-- **Ingham's density estimate for `ζ` on `7/12 ≤ σ ≤ 3/4`**: for every `0 < ε ≤ 1` there is `C ≥ 0` with
`N(σ, T) ≤ C T^{(12/5 + ε)(1−σ)}(log T)^{12}` for `T ≥ 2`. -/
theorem nx_ingham {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 7 / 12 ≤ σ → σ ≤ 3 / 4 →
      (NX (σ - 1 / 2) T : ℝ) ≤ C * T ^ ((12 / 5 + ε) * (1 - σ)) * Real.log T ^ 12 := by
  obtain ⟨C₄, hC₄⟩ := ZetaFourth.zeta_fourth_moment (ε := 3 * ε / 4) (by positivity) (by linarith)
  set C₄' := max C₄ 0 with hC₄'
  have hC₄'0 : 0 ≤ C₄' := le_max_right _ _
  have h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄' * (T + 2) ^ (1 + 3 * ε / 4) := by
    intro C' t hsep T hT ht
    refine (hC₄ C' t hsep T hT ht).trans ?_
    gcongr
    exact le_max_left _ _
  refine ⟨((finite_re_le 8).toFinset.card : ℝ) * 2 ^ 12 + 4 * Cwi C₄', by
    have := Cwi_nonneg hC₄'0; positivity, fun T hT σ hσ hσ1 => ?_⟩
  have he0 : 0 ≤ 12 / 5 * (1 - σ) + ε / 4 := by nlinarith
  have hN := nx_le_of_windows he0 (Cwi_nonneg hC₄'0)
    (fun U hU Z hZ => window_count_ingham hε.le hε1 hC₄'0 h4 hσ hσ1 hU Z hZ) hT
  refine hN.trans ?_
  have hT1 : 1 ≤ T := by linarith
  have hexp : 12 / 5 * (1 - σ) + ε / 4 ≤ (12 / 5 + ε) * (1 - σ) := by nlinarith
  have hlog : 0 ≤ Real.log T ^ 12 := by have := Real.log_nonneg hT1; positivity
  have hc : 0 ≤ ((finite_re_le 8).toFinset.card : ℝ) * 2 ^ 12 + 4 * Cwi C₄' := by
    have := Cwi_nonneg hC₄'0; positivity
  gcongr

end ZetaIngham

#print axioms ZetaIngham.Gfun_left_le_zeta
#print axioms ZetaIngham.class3_count_ingham
#print axioms ZetaIngham.window_count_ingham
#print axioms ZetaIngham.nx_le_of_windows
#print axioms ZetaIngham.nx_ingham
