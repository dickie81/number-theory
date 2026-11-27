/-
# The hyperbolic Laplacian and the eigen-equation of the Eisenstein series of `SL(2, ℤ)`

With `Δf(x + iy) = −y²(∂²f/∂x² + ∂²f/∂y²)` (`lap`, in the coordinates `ofXY (x, y) = x + iy`), the completed
Eisenstein series `E*(z, s) = Λ(z, s)/2` of `ModTruncation` satisfies
* **`lap_Estar`**: `ΔE*(·, s) = s(1 − s)E*(·, s)` on `ℍ` for every `s ≠ 0, 1`;
* **`lap_Estar_div`**: the same for `E*(·, s)/Λ(2s)`, `s ≠ 0, 1`;
* **`lap_E`**: `ΔE(·, s) = s(1 − s)E(·, s)` for the Eisenstein series `E(z, s) = ½Σ_{(c,d) = 1}(y/|cz + d|²)^s`,
  `Re s > 1`.

The proof works with the theta/Mellin representation directly, so no analytic continuation of derivatives is needed:
* **The profile** `h_k(q) = ∫_1^∞ t^k(t^{s−1} + t^{−s})e^{−πtq} dt` has `h_k' = −πh_{k+1}` (`hasDerivAt_hk`) and
  satisfies the ODE `π²q²h₂ − 2πqh₁ + s(1 − s)h₀ = (2πq − 1)e^{−πq}` (`hk_ode`, integration by parts).
* **The lattice sum** (`Λ₀_eq_tsum`, `Estar_eq_tsum`): `E*(z, s) = (Σ_{v ≠ 0} h₀(q_z(v)) − 1/s − 1/(1 − s))/2`, with
  `q_z(v) = |v₀z + v₁|²/y`.
* **The boundary identity** (`tsum_boundary`): `Σ_{v ≠ 0}(2πq_z(v) − 1)e^{−πq_z(v)} = 1`, from differentiating
  `θ(1/t) = tθ(t)` at `t = 1`.
* With `q = q_v(x, y)`, `q_x² + q_y² = q²/y²` and `q_xx + q_yy = 2q/y²`, so termwise
  `−y²Δ_E h₀(q) = s(1 − s)h₀(q) − (2πq − 1)e^{−πq}`; differentiating the sum twice under `tsum` (`deriv2_tsum_hk`,
  with locally uniform bounds) and summing with the boundary identity gives the eigen-equation.

Green's identity is not formalised here.
-/
import Mathlib
import ModMaassSelberg

open Complex Real Filter Topology Set MeasureTheory UpperHalfPlane Metric ModularGroup
open scoped MatrixGroups ENNReal NNReal

noncomputable section

namespace ModLaplacian

open ModEisenstein ModContinuation ModFourier ModTruncation ModFD

/-! ## The one-dimensional profile `h_k(q) = ∫_1^∞ t^k(t^{s−1} + t^{−s})e^{−πtq} dt` -/

/-- The Mellin weight `t^{s−1} + t^{−s}`. -/
def wt (s : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (s - 1) + (t : ℂ) ^ (-s)

/-- The integrand of `h_k`. -/
def hI (s : ℂ) (k : ℕ) (q t : ℝ) : ℂ := ((t ^ k * rexp (-π * t * q) : ℝ) : ℂ) * wt s t

/-- `h_k(q) = ∫_1^∞ t^k(t^{s−1} + t^{−s})e^{−πtq} dt`. -/
def hk (s : ℂ) (k : ℕ) (q : ℝ) : ℂ := ∫ t in Ioi (1 : ℝ), hI s k q t

/-- The exponent `|Re s| + 1`. -/
def A (s : ℂ) : ℝ := |s.re| + 1

lemma A_nonneg (s : ℂ) : 0 ≤ A s := by unfold A; positivity

lemma norm_wt_le (s : ℂ) {t : ℝ} (ht : 1 ≤ t) : ‖wt s t‖ ≤ 2 * t ^ A s := by
  have ht0 : 0 < t := one_pos.trans_le ht
  unfold wt
  refine (norm_add_le _ _).trans ?_
  rw [norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0]
  have h1 : t ^ (s - 1).re ≤ t ^ A s :=
    Real.rpow_le_rpow_of_exponent_le ht (by simp [A]; linarith [le_abs_self s.re])
  have h2 : t ^ (-s).re ≤ t ^ A s :=
    Real.rpow_le_rpow_of_exponent_le ht (by simp [A]; linarith [neg_abs_le s.re])
  linarith

lemma measurable_wt (s : ℂ) : Measurable (wt s) :=
  (Complex.measurable_ofReal.pow_const _).add (Complex.measurable_ofReal.pow_const _)

lemma measurable_hI (s : ℂ) (k : ℕ) (q : ℝ) : Measurable (hI s k q) := by
  unfold hI
  refine Measurable.mul ?_ (measurable_wt s)
  exact Complex.measurable_ofReal.comp (by fun_prop)

lemma integrableOn_rpow_exp (a : ℝ) (ha : 0 ≤ a) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ a * rexp (-b * t)) (Ioi 1) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (by linarith : -1 < a) one_pos hb
  simp only [Real.rpow_one] at this
  exact this.mono_set (Ioi_subset_Ioi zero_le_one)

lemma norm_hI_le (s : ℂ) (k : ℕ) (q : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ‖hI s k q t‖ ≤ 2 * (t ^ ((k : ℝ) + A s) * rexp (-π * t * q)) := by
  have ht0 : 0 < t := one_pos.trans_le ht
  unfold hI
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hw := norm_wt_le s ht
  rw [Real.rpow_add ht0, Real.rpow_natCast]
  have : 0 ≤ t ^ k * rexp (-π * t * q) := by positivity
  calc t ^ k * rexp (-π * t * q) * ‖wt s t‖ ≤ t ^ k * rexp (-π * t * q) * (2 * t ^ A s) :=
        mul_le_mul_of_nonneg_left hw this
    _ = _ := by ring

/-- The uniform bound: for `q ≥ q₁ > 0` and `t ≥ 1`, `‖t^k w(t)e^{−πtq}‖ ≤ 2t^{k+A}e^{−πq₁t/2} · e^{−πq/2}`. -/
lemma norm_hI_le' (s : ℂ) (k : ℕ) {q₁ q : ℝ} (hq₁ : 0 < q₁) (hq : q₁ ≤ q) {t : ℝ} (ht : 1 ≤ t) :
    ‖hI s k q t‖ ≤ 2 * (t ^ ((k : ℝ) + A s) * rexp (-(π * q₁ / 2) * t)) * rexp (-(π * q / 2)) := by
  refine (norm_hI_le s k q ht).trans ?_
  have : rexp (-π * t * q) ≤ rexp (-(π * q₁ / 2) * t) * rexp (-(π * q / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : q₁ * t ≤ q * t := mul_le_mul_of_nonneg_right hq (by linarith)
    have h2 : q ≤ q * t := le_mul_of_one_le_right (by linarith) ht
    nlinarith [Real.pi_pos]
  have h0 : 0 ≤ t ^ ((k : ℝ) + A s) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this h0]

lemma integrableOn_hI (s : ℂ) (k : ℕ) {q : ℝ} (hq : 0 < q) : IntegrableOn (hI s k q) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_rpow_exp ((k : ℝ) + A s) (by positivity [A_nonneg s])
    (by positivity : 0 < π * q)).const_mul 2) (measurable_hI s k q).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 1 < t) => ?_))
  refine (norm_hI_le s k q ht.le).trans (le_of_eq ?_)
  ring_nf

/-- `∫_1^∞ ‖t^k w(t)e^{−πtq}‖ dt ≤ Ce^{−πq/2}` for `q ≥ q₁ > 0`. -/
lemma exists_integral_norm_hI_le (s : ℂ) (k : ℕ) {q₁ : ℝ} (hq₁ : 0 < q₁) :
    ∃ C, ∀ q, q₁ ≤ q → ∫ t in Ioi (1 : ℝ), ‖hI s k q t‖ ≤ C * rexp (-(π * q / 2)) := by
  have hb := integrableOn_rpow_exp ((k : ℝ) + A s) (by positivity [A_nonneg s]) (by positivity : 0 < π * q₁ / 2)
  refine ⟨2 * ∫ t in Ioi (1 : ℝ), t ^ ((k : ℝ) + A s) * rexp (-(π * q₁ / 2) * t), fun q hq => ?_⟩
  have hq0 : 0 < q := hq₁.trans_le hq
  calc ∫ t in Ioi (1 : ℝ), ‖hI s k q t‖
      ≤ ∫ t in Ioi (1 : ℝ), 2 * (t ^ ((k : ℝ) + A s) * rexp (-(π * q₁ / 2) * t)) * rexp (-(π * q / 2)) := by
        refine setIntegral_mono_on (integrableOn_hI s k hq0).norm ((hb.const_mul 2).mul_const _)
          measurableSet_Ioi fun t (ht : 1 < t) => norm_hI_le' s k hq₁ hq ht.le
    _ = _ := by rw [integral_mul_const, integral_const_mul]

lemma exists_norm_hk_le (s : ℂ) (k : ℕ) {q₁ : ℝ} (hq₁ : 0 < q₁) :
    ∃ C, ∀ q, q₁ ≤ q → ‖hk s k q‖ ≤ C * rexp (-(π * q / 2)) := by
  obtain ⟨C, hC⟩ := exists_integral_norm_hI_le s k hq₁
  exact ⟨C, fun q hq => (norm_integral_le_integral_norm _).trans (hC q hq)⟩

/-- **`h_k' = −πh_{k+1}`** on `q > 0`. -/
theorem hasDerivAt_hk (s : ℂ) (k : ℕ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (hk s k) (-π * hk s (k + 1) q) q := by
  have hb := integrableOn_rpow_exp ((k + 1 : ℕ) + A s) (by positivity [A_nonneg s]) (by positivity : 0 < π * q / 2)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun x t => hI s k x t) (F' := fun x t => -π * hI s (k + 1) x t) (x₀ := q)
    (bound := fun t => π * (2 * (t ^ (((k + 1 : ℕ) : ℝ) + A s) * rexp (-(π * q / 2) * t))))
    (ball_mem_nhds q (by positivity : 0 < q / 2))
    (Eventually.of_forall fun x => (measurable_hI s k x).aestronglyMeasurable)
    (integrableOn_hI s k hq) ((measurable_hI s (k + 1) q).aestronglyMeasurable.const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 1 < t) x hx => ?_))
    ((hb.const_mul 2).const_mul π)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 1 < t) x hx => ?_))
  · refine key.2.congr_deriv ?_
    simp only [hk]
    rw [integral_const_mul]
  · have hx : q / 2 < x := by
      have := Metric.mem_ball.1 hx; rw [Real.dist_eq] at this; linarith [neg_abs_le (x - q)]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    refine mul_le_mul_of_nonneg_left ((norm_hI_le s (k + 1) x ht.le).trans ?_) Real.pi_pos.le
    have : rexp (-π * t * x) ≤ rexp (-(π * q / 2) * t) := by
      have hpt : 0 < π * t := by have := Real.pi_pos; positivity
      have := mul_le_mul_of_nonneg_left hx.le hpt.le
      apply Real.exp_le_exp.2; linarith
    have h0 : 0 ≤ t ^ (((k + 1 : ℕ) : ℝ) + A s) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  · have ht0 : 0 < t := one_pos.trans ht
    unfold hI
    have h1 : HasDerivAt (fun x : ℝ => t ^ k * rexp (-π * t * x)) (t ^ k * (rexp (-π * t * x) * (-π * t))) x :=
      ((((hasDerivAt_id x).const_mul (-π * t)).exp).const_mul (t ^ k)).congr_deriv (by simp)
    have h2 := h1.ofReal_comp.mul_const (wt s t)
    refine h2.congr_deriv ?_
    push_cast
    ring

/-! ## The profile equation -/

lemma hasDerivAt_cpow_real (a : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ a) (a * (t : ℂ) ^ (a - 1)) t :=
  (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 ht)).hasDerivAt.comp_ofReal

lemma cpow_shift {t : ℝ} (ht : 0 < t) (a : ℂ) (n : ℕ) : (t : ℂ) ^ (a + n) = (t : ℂ) ^ n * (t : ℂ) ^ a := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast ht.ne'), Complex.cpow_natCast, mul_comm]

/-- **The profile equation**: `∫_1^∞ (π²q²t² − 2πqt + s(1 − s))(t^{s−1} + t^{−s})e^{−πtq} dt = (2πq − 1)e^{−πq}`,
i.e. `π²q²h₂ − 2πqh₁ + s(1 − s)h₀ = (2πq − 1)e^{−πq}`, for `q > 0`. -/
theorem hk_ode (s : ℂ) {q : ℝ} (hq : 0 < q) :
    (π : ℂ) ^ 2 * (q : ℂ) ^ 2 * hk s 2 q - 2 * π * q * hk s 1 q + s * (1 - s) * hk s 0 q =
      ((2 * π * q - 1) * rexp (-π * q) : ℝ) := by
  set F : ℝ → ℂ := fun t => ((π * q : ℝ) * ((t : ℂ) ^ (s + 1) + (t : ℂ) ^ (2 - s)) + (s - 1) * (t : ℂ) ^ s -
      s * (t : ℂ) ^ (1 - s)) * (rexp (-π * t * q) : ℂ) with hF
  set F' : ℝ → ℂ := fun t => -((π : ℂ) ^ 2 * (q : ℂ) ^ 2 * hI s 2 q t - 2 * π * q * hI s 1 q t +
      s * (1 - s) * hI s 0 q t) with hF'
  have hderiv : ∀ t ∈ Ici (1 : ℝ), HasDerivAt F (F' t) t := by
    intro t (ht : 1 ≤ t)
    have ht0 : 0 < t := one_pos.trans_le ht
    have he : HasDerivAt (fun t : ℝ => (rexp (-π * t * q) : ℂ)) (rexp (-π * t * q) * (-π * q) : ℝ) t :=
      (((hasDerivAt_id t).const_mul (-π) |>.mul_const q).exp.congr_deriv (by simp)).ofReal_comp
    have hP : HasDerivAt (fun t : ℝ => ((π * q : ℝ) : ℂ) * ((t : ℂ) ^ (s + 1) + (t : ℂ) ^ (2 - s)) +
        (s - 1) * (t : ℂ) ^ s - s * (t : ℂ) ^ (1 - s))
        (((π * q : ℝ) : ℂ) * ((s + 1) * (t : ℂ) ^ (s + 1 - 1) + (2 - s) * (t : ℂ) ^ (2 - s - 1)) +
          (s - 1) * (s * (t : ℂ) ^ (s - 1)) - s * ((1 - s) * (t : ℂ) ^ (1 - s - 1))) t :=
      ((((hasDerivAt_cpow_real (s + 1) ht0).add (hasDerivAt_cpow_real (2 - s) ht0)).const_mul
        ((π * q : ℝ) : ℂ)).add ((hasDerivAt_cpow_real s ht0).const_mul (s - 1))).sub
        ((hasDerivAt_cpow_real (1 - s) ht0).const_mul s)
    refine (hP.mul he).congr_deriv ?_
    simp only [hF', hI, wt]
    have e1 : (t : ℂ) ^ (s + 1) = (t : ℂ) ^ 2 * (t : ℂ) ^ (s - 1) := by
      rw [← cpow_shift ht0]; congr 1; push_cast; ring
    have e2 : (t : ℂ) ^ (2 - s) = (t : ℂ) ^ 2 * (t : ℂ) ^ (-s) := by
      rw [← cpow_shift ht0]; congr 1; push_cast; ring
    have e3 : (t : ℂ) ^ s = (t : ℂ) ^ 1 * (t : ℂ) ^ (s - 1) := by
      rw [← cpow_shift ht0]; congr 1; push_cast; ring
    have e4 : (t : ℂ) ^ (1 - s) = (t : ℂ) ^ 1 * (t : ℂ) ^ (-s) := by
      rw [← cpow_shift ht0]; congr 1; push_cast; ring
    have e5 : (t : ℂ) ^ (s + 1 - 1) = (t : ℂ) ^ 1 * (t : ℂ) ^ (s - 1) := by
      rw [← cpow_shift ht0]; congr 1; push_cast; ring
    have e6 : (t : ℂ) ^ (2 - s - 1) = (t : ℂ) ^ 1 * (t : ℂ) ^ (-s) := by
      rw [← cpow_shift ht0]; congr 1; push_cast; ring
    have e7 : (t : ℂ) ^ (1 - s - 1) = (t : ℂ) ^ (-s) := by congr 1; ring
    rw [e1, e2, e3, e4, e5, e6, e7]
    push_cast
    ring
  have hint : IntegrableOn F' (Ioi 1) := by
    simp only [hF']
    exact (((integrableOn_hI s 2 hq).const_mul _).sub ((integrableOn_hI s 1 hq).const_mul _)).add
      ((integrableOn_hI s 0 hq).const_mul _) |>.neg
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hb := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A s + 1) (π * q) (by positivity)).const_mul
      (2 * (π * q) + 2 * ‖s - 1‖ + 2 * ‖s‖)
    rw [mul_zero] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := one_pos.trans_le ht
    have hc : ∀ a : ℂ, a.re ≤ A s + 1 → ‖(t : ℂ) ^ a‖ ≤ t ^ (A s + 1) := fun a ha => by
      rw [norm_cpow_eq_rpow_re_of_pos ht0]; exact Real.rpow_le_rpow_of_exponent_le ht ha
    have hA : |s.re| + 1 = A s := rfl
    have c1 := hc (s + 1) (by simp; linarith [le_abs_self s.re, A_nonneg s, hA])
    have c2 := hc (2 - s) (by simp; linarith [neg_abs_le s.re, hA])
    have c3 := hc s (by linarith [le_abs_self s.re, hA])
    have c4 := hc (1 - s) (by simp; linarith [neg_abs_le s.re, hA])
    simp only [hF]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      show -π * t * q = -(π * q) * t by ring]
    have hpos : 0 ≤ rexp (-(π * q) * t) := (Real.exp_pos _).le
    have hnorm : ‖((π * q : ℝ) : ℂ) * ((t : ℂ) ^ (s + 1) + (t : ℂ) ^ (2 - s)) + (s - 1) * (t : ℂ) ^ s -
        s * (t : ℂ) ^ (1 - s)‖ ≤ (2 * (π * q) + 2 * ‖s - 1‖ + 2 * ‖s‖) * t ^ (A s + 1) := by
      refine (norm_sub_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have := norm_add_le ((t : ℂ) ^ (s + 1)) ((t : ℂ) ^ (2 - s))
      have hsum : ‖(t : ℂ) ^ (s + 1) + (t : ℂ) ^ (2 - s)‖ ≤ 2 * t ^ (A s + 1) := by linarith
      have hpq : 0 ≤ π * q := by have := Real.pi_pos; positivity
      have m1 := mul_le_mul_of_nonneg_left hsum hpq
      have m2 := mul_le_mul_of_nonneg_left c3 (norm_nonneg (s - 1))
      have m3 := mul_le_mul_of_nonneg_left c4 (norm_nonneg s)
      have h0 : 0 ≤ t ^ (A s + 1) := by positivity
      nlinarith [norm_nonneg (s - 1), norm_nonneg s]
    calc _ ≤ (2 * (π * q) + 2 * ‖s - 1‖ + 2 * ‖s‖) * t ^ (A s + 1) * rexp (-(π * q) * t) :=
          mul_le_mul_of_nonneg_right hnorm hpos
      _ = _ := by ring
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have hsplit : ∫ t in Ioi (1 : ℝ), F' t = -((π : ℂ) ^ 2 * (q : ℂ) ^ 2 * hk s 2 q - 2 * π * q * hk s 1 q +
      s * (1 - s) * hk s 0 q) := by
    have i2 : IntegrableOn (fun t => (π : ℂ) ^ 2 * (q : ℂ) ^ 2 * hI s 2 q t) (Ioi 1) :=
      (integrableOn_hI s 2 hq).const_mul _
    have i1 : IntegrableOn (fun t => 2 * (π : ℂ) * q * hI s 1 q t) (Ioi 1) := (integrableOn_hI s 1 hq).const_mul _
    have i0 : IntegrableOn (fun t => s * (1 - s) * hI s 0 q t) (Ioi 1) := (integrableOn_hI s 0 hq).const_mul _
    have i21 : IntegrableOn (fun t => (π : ℂ) ^ 2 * (q : ℂ) ^ 2 * hI s 2 q t - 2 * (π : ℂ) * q * hI s 1 q t)
      (Ioi 1) := i2.sub i1
    simp only [hF', hk]
    rw [integral_neg, integral_add i21 i0, integral_sub i2 i1, integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [hsplit] at hFTC
  have hF1 : F 1 = ((2 * π * q - 1) * rexp (-π * q) : ℝ) := by
    simp only [hF, Complex.ofReal_one, Complex.one_cpow]
    push_cast
    ring_nf
  rw [hF1] at hFTC
  linear_combination -hFTC


/-! ## `E*` as a lattice sum of profiles -/

/-- The nonzero lattice vectors. -/
abbrev NZ := ↥({0}ᶜ : Set (Fin 2 → ℤ))

lemma qf_pos (z : ℍ) (v : NZ) : 0 < qf z v :=
  lt_of_le_of_ne (qf_nonneg z v) (fun h => v.2 ((qf_eq_zero_iff z v).1 h.symm))

lemma cz_le_qf' (z : ℍ) (v : NZ) : cz z ≤ qf z v := by
  refine le_trans ?_ (cz_le_qf z v)
  have hv : (v : Fin 2 → ℤ) ≠ 0 := v.2
  have : (1 : ℝ) ≤ ((v : Fin 2 → ℤ) 0 : ℝ) ^ 2 + ((v : Fin 2 → ℤ) 1 : ℝ) ^ 2 := by
    by_cases h0 : (v : Fin 2 → ℤ) 0 = 0
    · have h1 : (v : Fin 2 → ℤ) 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
      have : (1 : ℝ) ≤ ((v : Fin 2 → ℤ) 1 : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ ((v : Fin 2 → ℤ) 1) ^ 2 := by
          have := Int.one_le_abs h1; nlinarith [sq_abs ((v : Fin 2 → ℤ) 1)]
        exact_mod_cast this
      nlinarith [sq_nonneg ((v : Fin 2 → ℤ) 0 : ℝ)]
    · have : (1 : ℝ) ≤ ((v : Fin 2 → ℤ) 0 : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ ((v : Fin 2 → ℤ) 0) ^ 2 := by
          have := Int.one_le_abs h0; nlinarith [sq_abs ((v : Fin 2 → ℤ) 0)]
        exact_mod_cast this
      nlinarith [sq_nonneg ((v : Fin 2 → ℤ) 1 : ℝ)]
  nlinarith [(cz_pos z).le]

lemma summable_exp_qf_NZ (z : ℍ) {c : ℝ} (hc : 0 < c) : Summable fun v : NZ => rexp (-π * qf z v * c) :=
  (summable_theta z hc).subtype _

lemma theta_sub_one (z : ℍ) {t : ℝ} (ht : 0 < t) : theta z t - 1 = ∑' v : NZ, rexp (-π * qf z v * t) := by
  have h := (summable_theta z ht).tsum_subtype_add_tsum_subtype_compl ({0} : Set (Fin 2 → ℤ))
  rw [tsum_singleton (0 : Fin 2 → ℤ) (fun v => rexp (-π * qf z v * t))] at h
  have h0 : qf z 0 = 0 := (qf_eq_zero_iff z 0).2 rfl
  rw [h0] at h
  simp only [mul_zero, zero_mul, Real.exp_zero] at h
  unfold theta
  rw [← h]; ring

/-- The part of `θ_z − 1` beyond `t = 1`. -/
def gθ (z : ℍ) (t : ℝ) : ℂ := (Ioi (1 : ℝ)).indicator (fun t => (theta z t : ℂ) - 1) t

lemma mellinConvergent_gθ (z : ℍ) (s : ℂ) : MellinConvergent (gθ z) s := by
  obtain ⟨a, ha⟩ := exists_gt s.re
  refine mellinConvergent_of_isBigO_rpow (a := a) (b := s.re - 1) ?_ ?_ ha ?_ (by linarith)
  · intro x hx
    obtain ⟨u, hu, hu'⟩ := (locallyIntegrableOn_theta z).sub (locallyIntegrableOn_const (1 : ℂ)) x hx
    exact ⟨u, hu, hu'.indicator measurableSet_Ioi⟩
  · refine (isBigO_theta_sub z (-a)).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    simp [gθ, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht)]
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    simp [gθ, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h => lt_irrefl _ (ht.2.trans h))]

lemma fmod_eq_gθ (z : ℍ) {t : ℝ} (ht : 0 < t) :
    (thetaFEPair z).f_modif t = gθ z t + (t : ℂ) ^ (-1 : ℂ) • gθ z t⁻¹ := by
  rw [fmod_eq, Complex.cpow_neg_one, smul_eq_mul]
  rcases lt_trichotomy 1 t with h | rfl | h
  · have h' : t⁻¹ ∉ Ioi (1 : ℝ) := fun h' => by
      have := (inv_lt_one₀ ht).2 h; exact lt_irrefl _ (this.trans h')
    simp [gθ, h, h']
  · simp [gθ]
  · have h' : t⁻¹ ∈ Ioi (1 : ℝ) := (one_lt_inv₀ ht).2 h
    have hti := theta_inv z ht
    rw [one_div] at hti
    simp only [show ¬ 1 < t from not_lt.2 h.le, ↓reduceIte, ht, h, and_self, gθ,
      indicator_of_mem h', indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.2 h.le), hti]
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [Real.rpow_neg_one]
    push_cast
    field_simp
    ring

lemma Λ₀_eq_mellin (z : ℍ) (s : ℂ) : (thetaFEPair z).Λ₀ s = mellin (gθ z) s + mellin (gθ z) (1 - s) := by
  have hh : MellinConvergent (fun t => (t : ℂ) ^ (-1 : ℂ) • gθ z t⁻¹) s := by
    rw [MellinConvergent.cpow_smul]
    have := (MellinConvergent.comp_rpow (f := gθ z) (s := s + -1) (a := -1) (by norm_num)).2
      (by rw [show (s + -1) / ((-1 : ℝ) : ℂ) = 1 - s by push_cast; ring]; exact mellinConvergent_gθ z _)
    refine this.congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    simp only [Real.rpow_neg_one]
  have hm : mellin (fun t => (t : ℂ) ^ (-1 : ℂ) • gθ z t⁻¹) s = mellin (gθ z) (1 - s) := by
    rw [mellin_cpow_smul, mellin_comp_inv]; congr 1; ring
  rw [← hm, WeakFEPair.Λ₀]
  unfold mellin
  rw [← integral_add (mellinConvergent_gθ z s) hh]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [fmod_eq_gθ z ht, smul_add]

lemma gθ_smul (z : ℍ) (s : ℂ) (t : ℝ) : (t : ℂ) ^ (s - 1) • gθ z t =
    (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ (s - 1) * ((theta z t : ℂ) - 1)) t := by
  simp only [gθ, indicator_apply, smul_eq_mul]
  split_ifs <;> simp

lemma mellin_gθ (z : ℍ) (s : ℂ) :
    mellin (gθ z) s = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * ((theta z t : ℂ) - 1) := by
  unfold mellin
  simp_rw [gθ_smul]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, sup_eq_left.2 zero_le_one]

lemma integrableOn_mellin_gθ (z : ℍ) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((theta z t : ℂ) - 1)) (Ioi 1) := by
  have h := mellinConvergent_gθ z s
  unfold MellinConvergent at h
  simp_rw [gθ_smul] at h
  have := (integrable_indicator_iff measurableSet_Ioi).1 h
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.2 zero_le_one] at this
  exact this

/-- **`Λ₀_z(s) = ∫_1^∞ (t^{s−1} + t^{−s})(θ_z(t) − 1) dt`**, for every `s`. -/
lemma Λ₀_eq_integral (z : ℍ) (s : ℂ) :
    (thetaFEPair z).Λ₀ s = ∫ t in Ioi (1 : ℝ), wt s t * ((theta z t : ℂ) - 1) := by
  rw [Λ₀_eq_mellin, mellin_gθ, mellin_gθ, ← integral_add (integrableOn_mellin_gθ z s)
    (integrableOn_mellin_gθ z (1 - s))]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [wt, show 1 - s - 1 = -s by ring]
  ring

/-- **`Λ₀_z(s) = Σ_{v ≠ 0} h₀(q_z(v))`**, for every `s`. -/
theorem Λ₀_eq_tsum (z : ℍ) (s : ℂ) : (thetaFEPair z).Λ₀ s = ∑' v : NZ, hk s 0 (qf z v) := by
  rw [Λ₀_eq_integral]
  obtain ⟨C, hC⟩ := exists_integral_norm_hI_le s 0 (cz_pos z)
  have hsum : Summable fun v : NZ => ∫ t in Ioi (1 : ℝ), ‖hI s 0 (qf z v) t‖ := by
    refine Summable.of_nonneg_of_le (fun v => integral_nonneg fun t => norm_nonneg _)
      (fun v => hC _ (cz_le_qf' z v)) ?_
    refine ((summable_exp_qf_NZ z (by norm_num : (0 : ℝ) < 1 / 2)).mul_left C).congr fun v => ?_
    congr 2; ring
  simp only [hk]
  rw [integral_tsum_of_summable_integral_norm (fun v => integrableOn_hI s 0 (qf_pos z v)) hsum]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) => ?_
  have ht0 : 0 < t := one_pos.trans ht
  have e : (theta z t : ℂ) - 1 = ((theta z t - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [e, theta_sub_one z ht0, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  simp only [hI, pow_zero, one_mul]
  rw [mul_comm]; congr 3; ring

/-- **`E*` as a lattice sum**: `E*(z, s) = ½(Σ_{v ≠ 0} h₀(q_z(v)) − 1/s − 1/(1 − s))`, for every `s`. -/
theorem Estar_eq_tsum (z : ℍ) (s : ℂ) :
    Estar z s = (∑' v : NZ, hk s 0 (qf z v) - 1 / s - 1 / (1 - s)) / 2 := by
  rw [Estar, Lambda, Λ_thetaFEPair, Λ₀_eq_tsum]


/-! ## The boundary identity `Σ_{v ≠ 0}(2πq_v − 1)e^{−πq_v} = 1` -/

lemma mul_exp_le (q : ℝ) (hq : 0 ≤ q) {y : ℝ} (hy : 1 / 2 < y) :
    π * q * rexp (-π * q * y) ≤ 4 * rexp (-π * q * (1 / 4)) := by
  have hpq : 0 ≤ π * q := mul_nonneg Real.pi_pos.le hq
  have hx : π * q / 4 + 1 ≤ rexp (π * q / 4) := Real.add_one_le_exp _
  have he : 0 < rexp (-π * q * (1 / 4)) := Real.exp_pos _
  have hk : π * q * rexp (-π * q * (1 / 4)) ≤ 4 := by
    have h0 : rexp (π * q / 4) * rexp (-π * q * (1 / 4)) = 1 := by
      rw [← Real.exp_add, show π * q / 4 + -π * q * (1 / 4) = 0 by ring, Real.exp_zero]
    nlinarith [mul_le_mul_of_nonneg_right (show π * q ≤ 4 * rexp (π * q / 4) by linarith) he.le]
  have h1 : rexp (-π * q * y) ≤ rexp (-π * q * (1 / 4)) * rexp (-π * q * (1 / 4)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2; nlinarith
  calc π * q * rexp (-π * q * y) ≤ π * q * (rexp (-π * q * (1 / 4)) * rexp (-π * q * (1 / 4))) :=
        mul_le_mul_of_nonneg_left h1 hpq
    _ = (π * q * rexp (-π * q * (1 / 4))) * rexp (-π * q * (1 / 4)) := by ring
    _ ≤ 4 * rexp (-π * q * (1 / 4)) := mul_le_mul_of_nonneg_right hk he.le

lemma hasDerivAt_theta (z : ℍ) {t : ℝ} (ht : 1 / 2 < t) :
    HasDerivAt (theta z) (∑' v, rexp (-π * qf z v * t) * (-π * qf z v)) t := by
  unfold theta
  refine hasDerivAt_tsum_of_isPreconnected (u := fun v => 4 * rexp (-π * qf z v * (1 / 4)))
    (g := fun v t => rexp (-π * qf z v * t)) (g' := fun v t => rexp (-π * qf z v * t) * (-π * qf z v))
    ((summable_theta z (by norm_num)).mul_left 4) isOpen_Ioi isPreconnected_Ioi
    (fun v y _ => ?_) (fun v y (hy : 1 / 2 < y) => ?_) ht (summable_theta z (by linarith)) ht
  · exact ((hasDerivAt_id y).const_mul (-π * qf z v)).exp.congr_deriv (by simp)
  · have hn : ‖-π * qf z v‖ = π * qf z v := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by have := Real.pi_pos; nlinarith [qf_nonneg z v])]; ring
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, hn]
    have := mul_exp_le (qf z v) (qf_nonneg z v) hy
    linarith

lemma summable_qf_exp (z : ℍ) : Summable fun v => qf z v * rexp (-π * qf z v * 1) := by
  refine Summable.of_nonneg_of_le (fun v => mul_nonneg (qf_nonneg z v) (Real.exp_pos _).le) (fun v => ?_)
    (((summable_theta z (by norm_num : (0 : ℝ) < 1 / 4)).mul_left 4).div_const π)
  have := mul_exp_le (qf z v) (qf_nonneg z v) (by norm_num : (1 : ℝ) / 2 < 1)
  rw [le_div_iff₀ Real.pi_pos]; linarith

/-- `θ_z(1) = 2πΣ_v q_z(v)e^{−πq_z(v)}`, from differentiating `θ_z(1/t) = tθ_z(t)` at `t = 1`. -/
lemma theta_one_eq (z : ℍ) : theta z 1 = 2 * π * ∑' v, qf z v * rexp (-π * qf z v * 1) := by
  have h1 := hasDerivAt_theta z (by norm_num : (1 : ℝ) / 2 < 1)
  set D := ∑' v, rexp (-π * qf z v * 1) * (-π * qf z v)
  have hf1 : HasDerivAt (fun t : ℝ => theta z t⁻¹) (D * (-(1 ^ 2 : ℝ)⁻¹)) 1 := by
    exact h1.comp_of_eq (1 : ℝ) (hasDerivAt_inv one_ne_zero) (by norm_num)
  have hf2 : HasDerivAt (fun t : ℝ => t * theta z t) (1 * theta z 1 + 1 * D) 1 := (hasDerivAt_id 1).mul h1
  have hev : (fun t : ℝ => theta z t⁻¹) =ᶠ[𝓝 1] fun t => t * theta z t := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [← one_div]; exact theta_inv z ht
  have := (hf1.congr_of_eventuallyEq hev.symm).unique hf2
  have hD : D = -π * ∑' v, qf z v * rexp (-π * qf z v * 1) := by
    simp only [D]; rw [← tsum_mul_left]; congr 1; ext v; ring
  rw [hD] at this
  linarith

lemma summable_boundary (z : ℍ) : Summable fun v : NZ => (2 * π * qf z v - 1) * rexp (-π * qf z v) := by
  have hs1 : Summable fun v : NZ => qf z v * rexp (-π * qf z v * 1) := (summable_qf_exp z).subtype _
  have hs2 := summable_exp_qf_NZ z one_pos
  refine ((hs1.mul_left (2 * π)).sub hs2).congr fun v => ?_
  simp only [mul_one]; ring

/-- **The boundary identity**: `Σ_{v ≠ 0}(2πq_z(v) − 1)e^{−πq_z(v)} = 1`. -/
theorem tsum_boundary (z : ℍ) : ∑' v : NZ, (2 * π * qf z v - 1) * rexp (-π * qf z v) = 1 := by
  have hs1 : Summable fun v : NZ => qf z v * rexp (-π * qf z v * 1) := (summable_qf_exp z).subtype _
  have hs2 := summable_exp_qf_NZ z one_pos
  have e1 : ∑' v : NZ, qf z v * rexp (-π * qf z v * 1) = ∑' v, qf z v * rexp (-π * qf z v * 1) := by
    refine tsum_subtype_eq_of_support_subset (f := fun v => qf z v * rexp (-π * qf z v * 1))
      (s := ({0}ᶜ : Set (Fin 2 → ℤ))) fun v hv h0 => hv ?_
    rw [Set.mem_singleton_iff] at h0
    simp [h0, (qf_eq_zero_iff z 0).2 rfl]
  have e2 := theta_sub_one z one_pos
  have e3 := theta_one_eq z
  calc ∑' v : NZ, (2 * π * qf z v - 1) * rexp (-π * qf z v)
      = ∑' v : NZ, (2 * π * (qf z v * rexp (-π * qf z v * 1)) - rexp (-π * qf z v * 1)) := by
        congr 1; ext v; rw [mul_one]; ring
    _ = 2 * π * ∑' v : NZ, qf z v * rexp (-π * qf z v * 1) - ∑' v : NZ, rexp (-π * qf z v * 1) := by
        rw [Summable.tsum_sub (hs1.mul_left _) hs2, tsum_mul_left]
    _ = 1 := by rw [e1, ← e2, ← e3]; ring


/-! ## Second derivatives of the lattice sum -/

lemma deriv2_tsum {ι : Type*} {g g' g'' : ι → ℝ → ℂ} {u : ι → ℝ} {x₀ δ : ℝ} (hδ : 0 < δ) (hu : Summable u)
    (hg : ∀ i x, x ∈ ball x₀ δ → HasDerivAt (g i) (g' i x) x)
    (hg' : ∀ i x, x ∈ ball x₀ δ → HasDerivAt (g' i) (g'' i x) x)
    (hb1 : ∀ i x, x ∈ ball x₀ δ → ‖g' i x‖ ≤ u i) (hb2 : ∀ i x, x ∈ ball x₀ δ → ‖g'' i x‖ ≤ u i)
    (h0 : Summable fun i => g i x₀) :
    deriv (deriv fun x => ∑' i, g i x) x₀ = ∑' i, g'' i x₀ := by
  have hx₀ : x₀ ∈ ball x₀ δ := mem_ball_self hδ
  have H1 : ∀ x ∈ ball x₀ δ, HasDerivAt (fun x => ∑' i, g i x) (∑' i, g' i x) x := fun x hx =>
    hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball x₀ δ).isPreconnected hg hb1 hx₀ h0 hx
  have hs' : Summable fun i => g' i x₀ := Summable.of_norm_bounded hu fun i => hb1 i x₀ hx₀
  have H2 : HasDerivAt (fun x => ∑' i, g' i x) (∑' i, g'' i x₀) x₀ :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball x₀ δ).isPreconnected hg' hb2 hx₀ hs' hx₀
  have hev : deriv (fun x => ∑' i, g i x) =ᶠ[𝓝 x₀] fun x => ∑' i, g' i x :=
    Filter.eventually_of_mem (ball_mem_nhds x₀ hδ) fun x hx => (H1 x hx).deriv
  rw [hev.deriv_eq]
  exact H2.deriv

lemma hasDerivAt_hk_comp (s : ℂ) (k : ℕ) {q q' : ℝ → ℝ} {x : ℝ} (hq : HasDerivAt q (q' x) x) (hpos : 0 < q x) :
    HasDerivAt (fun x => hk s k (q x)) (-π * hk s (k + 1) (q x) * (q' x : ℂ)) x :=
  ((hasDerivAt_hk s k hpos).scomp x hq).congr_deriv (by rw [Complex.real_smul]; ring)

lemma hasDerivAt_hk_comp2 (s : ℂ) {q q' q'' : ℝ → ℝ} {x : ℝ} (hq : HasDerivAt q (q' x) x)
    (hq' : HasDerivAt q' (q'' x) x) (hpos : 0 < q x) :
    HasDerivAt (fun x => -π * hk s 1 (q x) * (q' x : ℂ))
      (π ^ 2 * hk s 2 (q x) * (q' x : ℂ) ^ 2 - π * hk s 1 (q x) * (q'' x : ℂ)) x := by
  have h1 := ((hasDerivAt_hk_comp s 1 hq hpos).const_mul (-π : ℂ)).mul hq'.ofReal_comp
  refine h1.congr_deriv ?_
  ring

lemma mul_exp_bounds {q : ℝ} (hq : 0 ≤ q) :
    q * rexp (-(π * q / 2)) ≤ 4 / π * rexp (-(π * q / 4)) ∧
      q ^ 2 * rexp (-(π * q / 2)) ≤ 32 / π ^ 2 * rexp (-(π * q / 4)) := by
  have hπ := Real.pi_pos
  set x := π * q / 4 with hx
  have hx0 : 0 ≤ x := by positivity
  have e1 : x + 1 ≤ rexp x := Real.add_one_le_exp x
  have e2 : x ^ 2 / 2 ≤ rexp x := by
    have := Real.pow_div_factorial_le_exp x hx0 2
    simpa using this
  have hsplit : rexp (-(π * q / 2)) = rexp (-x) * rexp (-x) := by rw [← Real.exp_add]; congr 1; rw [hx]; ring
  have hinv : rexp x * rexp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hq' : q = 4 / π * x := by rw [hx]; field_simp
  have he : 0 < rexp (-x) := Real.exp_pos _
  rw [hsplit, show -(π * q / 4) = -x by rw [hx]]
  constructor
  · rw [hq']
    have : x * rexp (-x) ≤ 1 := by nlinarith
    have h4 : 0 ≤ 4 / π := by positivity
    calc 4 / π * x * (rexp (-x) * rexp (-x)) = 4 / π * (x * rexp (-x)) * rexp (-x) := by ring
      _ ≤ 4 / π * 1 * rexp (-x) := by gcongr
      _ = _ := by ring
  · rw [hq']
    have : x ^ 2 * rexp (-x) ≤ 2 := by nlinarith
    calc (4 / π * x) ^ 2 * (rexp (-x) * rexp (-x)) = 16 / π ^ 2 * (x ^ 2 * rexp (-x)) * rexp (-x) := by ring
      _ ≤ 16 / π ^ 2 * 2 * rexp (-x) := by gcongr
      _ = _ := by ring

/-- **Second derivative of `Σ_v h₀(q_v(x))` in one variable**, for a family `q_v` with uniform bounds near `x₀`. -/
theorem deriv2_tsum_hk (s : ℂ) {q q₁ q₂ : NZ → ℝ → ℝ} {q0 : NZ → ℝ} {x₀ δ L c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hL : 0 ≤ L) (hsum : Summable fun v => rexp (-(π * q0 v / 16))) (hq0 : ∀ v, c ≤ q0 v)
    (hd1 : ∀ v x, x ∈ ball x₀ δ → HasDerivAt (q v) (q₁ v x) x)
    (hd2 : ∀ v x, x ∈ ball x₀ δ → HasDerivAt (q₁ v) (q₂ v x) x)
    (hlow : ∀ v x, x ∈ ball x₀ δ → q0 v / 4 ≤ q v x)
    (hb1 : ∀ v x, x ∈ ball x₀ δ → |q₁ v x| ≤ L * q v x) (hb2 : ∀ v x, x ∈ ball x₀ δ → |q₂ v x| ≤ 2 * L ^ 2 * q v x) :
    deriv (deriv fun x => ∑' v, hk s 0 (q v x)) x₀ =
        ∑' v, (π ^ 2 * hk s 2 (q v x₀) * (q₁ v x₀ : ℂ) ^ 2 - π * hk s 1 (q v x₀) * (q₂ v x₀ : ℂ)) ∧
      Summable (fun v => (π ^ 2 * hk s 2 (q v x₀) * (q₁ v x₀ : ℂ) ^ 2 - π * hk s 1 (q v x₀) * (q₂ v x₀ : ℂ))) ∧
      Summable fun v => hk s 0 (q v x₀) := by
  have hc4 : 0 < c / 4 := by positivity
  obtain ⟨C0, hC0⟩ := exists_norm_hk_le s 0 hc4
  obtain ⟨C1, hC1⟩ := exists_norm_hk_le s 1 hc4
  obtain ⟨C2, hC2⟩ := exists_norm_hk_le s 2 hc4
  have hπ := Real.pi_pos
  have hCnn : ∀ {k C}, (∀ q, c / 4 ≤ q → ‖hk s k q‖ ≤ C * rexp (-(π * q / 2))) → 0 ≤ C := fun {k C} h => by
    have := (norm_nonneg _).trans (h (c / 4) le_rfl)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have h1nn := hCnn hC1
  have h2nn := hCnn hC2
  have hx₀ : x₀ ∈ ball x₀ δ := mem_ball_self hδ
  have hqpos : ∀ v x, x ∈ ball x₀ δ → c / 4 ≤ q v x := fun v x hx => by
    have := hlow v x hx; have := hq0 v; linarith
  set K := 4 * C1 * L + (32 * C2 + 8 * C1) * L ^ 2 with hK
  have hexp : ∀ v x, x ∈ ball x₀ δ → rexp (-(π * q v x / 4)) ≤ rexp (-(π * q0 v / 16)) := fun v x hx => by
    apply Real.exp_le_exp.2; have := hlow v x hx; nlinarith
  have bd1 : ∀ v x, x ∈ ball x₀ δ → ‖-π * hk s 1 (q v x) * (q₁ v x : ℂ)‖ ≤ K * rexp (-(π * q0 v / 16)) := by
    intro v x hx
    have hq := hqpos v x hx
    have hq0' : 0 ≤ q v x := by linarith
    obtain ⟨m1, -⟩ := mul_exp_bounds hq0'
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hπ.le,
      Real.norm_eq_abs]
    have a1 := hC1 _ hq
    have a2 := hb1 v x hx
    have he := hexp v x hx
    have : π * ‖hk s 1 (q v x)‖ * |q₁ v x| ≤ 4 * C1 * L * rexp (-(π * q0 v / 16)) := by
      calc π * ‖hk s 1 (q v x)‖ * |q₁ v x| ≤ π * (C1 * rexp (-(π * q v x / 2))) * (L * q v x) := by
            gcongr
        _ = π * C1 * L * (q v x * rexp (-(π * q v x / 2))) := by ring
        _ ≤ π * C1 * L * (4 / π * rexp (-(π * q v x / 4))) := by gcongr
        _ = 4 * C1 * L * rexp (-(π * q v x / 4)) := by field_simp
        _ ≤ 4 * C1 * L * rexp (-(π * q0 v / 16)) := by gcongr
    have : 0 ≤ (32 * C2 + 8 * C1) * L ^ 2 * rexp (-(π * q0 v / 16)) := by positivity
    rw [hK]; nlinarith
  have bd2 : ∀ v x, x ∈ ball x₀ δ →
      ‖π ^ 2 * hk s 2 (q v x) * (q₁ v x : ℂ) ^ 2 - π * hk s 1 (q v x) * (q₂ v x : ℂ)‖ ≤
        K * rexp (-(π * q0 v / 16)) := by
    intro v x hx
    have hq := hqpos v x hx
    have hq0' : 0 ≤ q v x := by linarith
    obtain ⟨m1, m2⟩ := mul_exp_bounds hq0'
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hπ.le, Real.norm_eq_abs, Real.norm_eq_abs]
    have a1 := hC1 _ hq
    have a2 := hC2 _ hq
    have b1 := hb1 v x hx
    have b2 := hb2 v x hx
    have he := hexp v x hx
    have t1 : π ^ 2 * ‖hk s 2 (q v x)‖ * |q₁ v x| ^ 2 ≤ 32 * C2 * L ^ 2 * rexp (-(π * q0 v / 16)) := by
      calc π ^ 2 * ‖hk s 2 (q v x)‖ * |q₁ v x| ^ 2 ≤ π ^ 2 * (C2 * rexp (-(π * q v x / 2))) * (L * q v x) ^ 2 := by
            gcongr
        _ = π ^ 2 * C2 * L ^ 2 * (q v x ^ 2 * rexp (-(π * q v x / 2))) := by ring
        _ ≤ π ^ 2 * C2 * L ^ 2 * (32 / π ^ 2 * rexp (-(π * q v x / 4))) := by gcongr
        _ = 32 * C2 * L ^ 2 * rexp (-(π * q v x / 4)) := by field_simp
        _ ≤ 32 * C2 * L ^ 2 * rexp (-(π * q0 v / 16)) := by gcongr
    have t2 : π * ‖hk s 1 (q v x)‖ * |q₂ v x| ≤ 8 * C1 * L ^ 2 * rexp (-(π * q0 v / 16)) := by
      calc π * ‖hk s 1 (q v x)‖ * |q₂ v x| ≤ π * (C1 * rexp (-(π * q v x / 2))) * (2 * L ^ 2 * q v x) := by
            gcongr
        _ = 2 * π * C1 * L ^ 2 * (q v x * rexp (-(π * q v x / 2))) := by ring
        _ ≤ 2 * π * C1 * L ^ 2 * (4 / π * rexp (-(π * q v x / 4))) := by gcongr
        _ = 8 * C1 * L ^ 2 * rexp (-(π * q v x / 4)) := by field_simp; ring
        _ ≤ 8 * C1 * L ^ 2 * rexp (-(π * q0 v / 16)) := by gcongr
    have : 0 ≤ 4 * C1 * L * rexp (-(π * q0 v / 16)) := by positivity
    rw [hK]; nlinarith
  have hu := hsum.mul_left K
  have h0 : Summable fun v => hk s 0 (q v x₀) := by
    refine Summable.of_norm_bounded (hsum.mul_left C0) fun v => ?_
    refine (hC0 _ (hqpos v x₀ hx₀)).trans ?_
    have := hlow v x₀ hx₀
    have hC0nn := hCnn hC0
    have hqx := hqpos v x₀ hx₀
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0nn
    nlinarith
  refine ⟨deriv2_tsum hδ hu (fun v x hx => hasDerivAt_hk_comp s 0 (hd1 v x hx) (by linarith [hqpos v x hx]))
    (fun v x hx => hasDerivAt_hk_comp2 s (hd1 v x hx) (hd2 v x hx) (by linarith [hqpos v x hx]))
    bd1 bd2 h0, Summable.of_norm_bounded hu fun v => bd2 v x₀ hx₀, h0⟩


/-! ## The model in coordinates -/

/-- `q_v(x, y) = ((v₀x + v₁)² + (v₀y)²)/y`, the value of `q_z(v)` at `z = x + iy`. -/
def qv (v : Fin 2 → ℤ) (x y : ℝ) : ℝ := (((v 0 : ℝ) * x + v 1) ^ 2 + ((v 0 : ℝ) * y) ^ 2) / y
def qx (v : Fin 2 → ℤ) (x y : ℝ) : ℝ := 2 * (v 0 : ℝ) * ((v 0 : ℝ) * x + v 1) / y
def qxx (v : Fin 2 → ℤ) (y : ℝ) : ℝ := 2 * (v 0 : ℝ) ^ 2 / y
def qy (v : Fin 2 → ℤ) (x y : ℝ) : ℝ := (v 0 : ℝ) ^ 2 - ((v 0 : ℝ) * x + v 1) ^ 2 / y ^ 2
def qyy (v : Fin 2 → ℤ) (x y : ℝ) : ℝ := 2 * ((v 0 : ℝ) * x + v 1) ^ 2 / y ^ 3

lemma qf_eq_qv (z : ℍ) (v : Fin 2 → ℤ) : qf z v = qv v z.re z.im := by
  unfold qf qv; rw [nq_re_im]

lemma qf_ofXY {x y : ℝ} (hy : 0 < y) (v : Fin 2 → ℤ) : qf (ofXY (x, y)) v = qv v x y := by
  rw [qf_eq_qv, ModMaassSelberg.ofXY_re (p := (x, y)) hy, ModMaassSelberg.ofXY_im (p := (x, y)) hy]

lemma hasDerivAt_qv_x (v : Fin 2 → ℤ) (x y : ℝ) : HasDerivAt (fun x => qv v x y) (qx v x y) x := by
  have h := ((((hasDerivAt_id x).const_mul (v 0 : ℝ)).add_const (v 1 : ℝ)).pow 2).add_const
    (((v 0 : ℝ) * y) ^ 2) |>.div_const y
  refine h.congr_deriv ?_
  simp [qx]; ring

lemma hasDerivAt_qx (v : Fin 2 → ℤ) (x y : ℝ) : HasDerivAt (fun x => qx v x y) (qxx v y) x := by
  have h := (((hasDerivAt_id x).const_mul (v 0 : ℝ)).add_const (v 1 : ℝ)).const_mul (2 * (v 0 : ℝ)) |>.div_const y
  refine h.congr_deriv ?_
  simp [qxx]; ring

lemma hasDerivAt_qv_y (v : Fin 2 → ℤ) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y => qv v x y) (qy v x y) y := by
  have h := (((hasDerivAt_id y).const_mul (v 0 : ℝ)).pow 2).const_add (((v 0 : ℝ) * x + v 1) ^ 2) |>.div
    (hasDerivAt_id y) hy
  refine h.congr_deriv ?_
  simp only [qy, id, Pi.pow_apply]
  field_simp
  ring

lemma hasDerivAt_qy (v : Fin 2 → ℤ) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y => qy v x y) (qyy v x y) y := by
  have h := ((hasDerivAt_const y (((v 0 : ℝ) * x + v 1) ^ 2)).div (hasDerivAt_pow 2 y) (pow_ne_zero 2 hy)).const_sub
    ((v 0 : ℝ) ^ 2)
  refine h.congr_deriv ?_
  simp only [qyy]
  field_simp
  ring

lemma qv_bounds (v : Fin 2 → ℤ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    |qx v x y| ≤ qv v x y / y ∧ |qy v x y| ≤ qv v x y / y ∧ |qxx v y| ≤ 2 * (qv v x y / y ^ 2) ∧
      |qyy v x y| ≤ 2 * (qv v x y / y ^ 2) := by
  set a := (v 0 : ℝ)
  set w := (a * x + v 1) / y
  have hq1 : qv v x y / y = w ^ 2 + a ^ 2 := by simp only [qv, w, a]; field_simp
  have hq2 : qv v x y / y ^ 2 = (w ^ 2 + a ^ 2) / y := by rw [← hq1]; field_simp
  have ex : qx v x y = 2 * a * w := by simp only [qx, w, a]; field_simp
  have ey : qy v x y = a ^ 2 - w ^ 2 := by simp only [qy, w, a]; field_simp
  have exx : qxx v y = 2 * a ^ 2 / y := rfl
  have eyy : qyy v x y = 2 * w ^ 2 / y := by simp only [qyy, w, a]; field_simp
  rw [hq1, hq2, ex, ey, exx, eyy]
  refine ⟨abs_le.2 ⟨by nlinarith [sq_nonneg (w + a)], by nlinarith [sq_nonneg (w - a)]⟩,
    abs_le.2 ⟨by nlinarith [sq_nonneg w], by nlinarith [sq_nonneg a]⟩, ?_, ?_⟩
  · rw [abs_of_nonneg (by positivity)]
    have : 2 * a ^ 2 ≤ 2 * (w ^ 2 + a ^ 2) := by nlinarith [sq_nonneg w]
    calc 2 * a ^ 2 / y ≤ 2 * (w ^ 2 + a ^ 2) / y := by gcongr
      _ = _ := by ring
  · rw [abs_of_nonneg (by positivity)]
    have : 2 * w ^ 2 ≤ 2 * (w ^ 2 + a ^ 2) := by nlinarith [sq_nonneg a]
    calc 2 * w ^ 2 / y ≤ 2 * (w ^ 2 + a ^ 2) / y := by gcongr
      _ = _ := by ring

lemma qv_box (v : Fin 2 → ℤ) {x₀ y₀ x y : ℝ} (hy₀ : 0 < y₀) (hx : |x - x₀| ≤ y₀ / 4) (hy : |y - y₀| ≤ y₀ / 4) :
    qv v x₀ y₀ / 4 ≤ qv v x y := by
  set a := (v 0 : ℝ)
  set A0 := a * x₀ + v 1
  set B0 := a * y₀
  set e1 := a * (x - x₀)
  set e2 := a * (y - y₀)
  have hu : a * x + v 1 = A0 + e1 := by simp only [A0, e1]; ring
  have hw : a * y = B0 + e2 := by simp only [B0, e2]; ring
  have hx2 : (x - x₀) ^ 2 ≤ (y₀ / 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 : (y - y₀) ^ 2 ≤ (y₀ / 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have he1 : e1 ^ 2 ≤ B0 ^ 2 / 16 := by
    simp only [e1, B0]; nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg a)]
  have he2 : e2 ^ 2 ≤ B0 ^ 2 / 16 := by
    simp only [e2, B0]; nlinarith [mul_le_mul_of_nonneg_left hy2 (sq_nonneg a)]
  have hN : 3 / 8 * (A0 ^ 2 + B0 ^ 2) ≤ (A0 + e1) ^ 2 + (B0 + e2) ^ 2 := by
    nlinarith [sq_nonneg (A0 + 2 * e1), sq_nonneg (B0 + 2 * e2), sq_nonneg A0]
  have hyle : y ≤ 5 / 4 * y₀ := by linarith [le_abs_self (y - y₀)]
  have hypos : 0 < y := by linarith [neg_abs_le (y - y₀)]
  unfold qv
  rw [hu, hw, div_div, div_le_div_iff₀ (by positivity) hypos]
  have h0 : 0 ≤ A0 ^ 2 + B0 ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hyle h0, mul_le_mul_of_nonneg_right hN hy₀.le]

/-! ## The hyperbolic Laplacian -/

/-- **The hyperbolic Laplacian** `Δf(x + iy) = −y²(∂²f/∂x² + ∂²f/∂y²)`, in the coordinates `ofXY (x, y) = x + iy`. -/
def lap (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  -(z.im : ℂ) ^ 2 * (deriv (deriv fun x => f (ofXY (x, z.im))) z.re + deriv (deriv fun y => f (ofXY (z.re, y))) z.im)

lemma deriv2_half (S : ℝ → ℂ) (a b : ℂ) (x₀ : ℝ) :
    deriv (deriv fun x => (S x - a - b) / 2) x₀ = deriv (deriv S) x₀ / 2 := by
  have : deriv (fun x => (S x - a - b) / 2) = fun x => deriv S x / 2 := funext fun x => by
    rw [deriv_div_const, deriv_sub_const, deriv_sub_const]
  rw [this, deriv_div_const]

/-- **`ΔE*(·, s) = s(1 − s)E*(·, s)`** on `ℍ`, for every `s ≠ 0, 1`. -/
theorem lap_Estar (z : ℍ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    lap (fun w => Estar w s) z = s * (1 - s) * Estar z s := by
  have hy₀ : 0 < z.im := z.im_pos
  set M : ℝ → ℝ → ℂ := fun x y => (∑' v : NZ, hk s 0 (qv v x y) - 1 / s - 1 / (1 - s)) / 2 with hM
  have hEx : (fun x => Estar (ofXY (x, z.im)) s) = fun x => M x z.im := funext fun x => by
    rw [Estar_eq_tsum]; simp only [hM, qf_ofXY hy₀]
  have hEy : (fun y => Estar (ofXY (z.re, y)) s) =ᶠ[𝓝 z.im] fun y => M z.re y := by
    filter_upwards [lt_mem_nhds hy₀] with y hy
    rw [Estar_eq_tsum]; simp only [hM, qf_ofXY hy]
  have hδ : 0 < z.im / 4 := by positivity
  set L := 4 / (3 * z.im) with hL
  have hL0 : 0 ≤ L := by positivity
  have hsum : Summable fun v : NZ => rexp (-(π * qv v z.re z.im / 16)) :=
    (summable_exp_qf_NZ z (by norm_num : (0 : ℝ) < 1 / 16)).congr fun v => by rw [qf_eq_qv]; ring_nf
  have hq0 : ∀ v : NZ, cz z ≤ qv v z.re z.im := fun v => (qf_eq_qv z v) ▸ cz_le_qf' z v
  have hball : ∀ {t c : ℝ}, t ∈ ball c (z.im / 4) → |t - c| ≤ z.im / 4 := fun ht => by
    rw [Metric.mem_ball, Real.dist_eq] at ht; exact ht.le
  have hinv : ∀ {y : ℝ}, |y - z.im| ≤ z.im / 4 → 0 < y ∧ 1 / y ≤ L := fun {y} hy => by
    have hyp : 3 / 4 * z.im ≤ y := by linarith [neg_abs_le (y - z.im)]
    refine ⟨by linarith, ?_⟩
    rw [hL, div_le_div_iff₀ (by linarith) (by positivity)]; linarith
  -- the `x`-direction
  obtain ⟨hX, hXs, hX0⟩ := deriv2_tsum_hk s (q := fun v x => qv v x z.im) (q₁ := fun v x => qx v x z.im)
    (q₂ := fun v _ => qxx v z.im) (q0 := fun v => qv v z.re z.im) (x₀ := z.re) hδ (cz_pos z) hL0 hsum hq0
    (fun v x _ => hasDerivAt_qv_x v x z.im) (fun v x _ => hasDerivAt_qx v x z.im)
    (fun v x hx => qv_box v hy₀ (hball hx) (by simp; positivity))
    (fun v x _ => by
      have := (qv_bounds v x hy₀).1
      have hq : 0 ≤ qv v x z.im := by unfold qv; positivity
      calc _ ≤ qv v x z.im / z.im := this
        _ = 1 / z.im * qv v x z.im := by ring
        _ ≤ L * qv v x z.im := mul_le_mul_of_nonneg_right (hinv (by simp; positivity)).2 hq)
    (fun v x _ => by
      have := (qv_bounds v x hy₀).2.2.1
      have hq : 0 ≤ qv v x z.im := by unfold qv; positivity
      have hl := (hinv (y := z.im) (by simp; positivity)).2
      have : (1 / z.im) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hl 2
      calc _ ≤ 2 * (qv v x z.im / z.im ^ 2) := by assumption
        _ = 2 * (1 / z.im) ^ 2 * qv v x z.im := by ring
        _ ≤ 2 * L ^ 2 * qv v x z.im := by gcongr)
  -- the `y`-direction
  obtain ⟨hY, hYs, -⟩ := deriv2_tsum_hk s (q := fun v y => qv v z.re y) (q₁ := fun v y => qy v z.re y)
    (q₂ := fun v y => qyy v z.re y) (q0 := fun v => qv v z.re z.im) (x₀ := z.im) hδ (cz_pos z) hL0 hsum hq0
    (fun v y hy => hasDerivAt_qv_y v z.re (hinv (hball hy)).1.ne')
    (fun v y hy => hasDerivAt_qy v z.re (hinv (hball hy)).1.ne')
    (fun v y hy => qv_box v hy₀ (by simp; positivity) (hball hy))
    (fun v y hy => by
      obtain ⟨hyp, hl⟩ := hinv (hball hy)
      have := (qv_bounds v z.re hyp).2.1
      have hq : 0 ≤ qv v z.re y := by unfold qv; positivity
      calc _ ≤ qv v z.re y / y := this
        _ = 1 / y * qv v z.re y := by ring
        _ ≤ L * qv v z.re y := mul_le_mul_of_nonneg_right hl hq)
    (fun v y hy => by
      obtain ⟨hyp, hl⟩ := hinv (hball hy)
      have := (qv_bounds v z.re hyp).2.2.2
      have hq : 0 ≤ qv v z.re y := by unfold qv; positivity
      have : (1 / y) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hl 2
      calc _ ≤ 2 * (qv v z.re y / y ^ 2) := by assumption
        _ = 2 * (1 / y) ^ 2 * qv v z.re y := by ring
        _ ≤ 2 * L ^ 2 * qv v z.re y := by gcongr)
  have hdx : deriv (deriv fun x => Estar (ofXY (x, z.im)) s) z.re =
      (∑' v : NZ, (π ^ 2 * hk s 2 (qv v z.re z.im) * (qx v z.re z.im : ℂ) ^ 2 - π * hk s 1 (qv v z.re z.im) * (qxx v z.im : ℂ))) / 2 := by
    rw [hEx]; simp only [hM]; rw [deriv2_half, hX]
  have hdy : deriv (deriv fun y => Estar (ofXY (z.re, y)) s) z.im =
      (∑' v : NZ, (π ^ 2 * hk s 2 (qv v z.re z.im) * (qy v z.re z.im : ℂ) ^ 2 -
        π * hk s 1 (qv v z.re z.im) * (qyy v z.re z.im : ℂ))) / 2 := by
    rw [hEy.deriv.deriv_eq]; simp only [hM]; rw [deriv2_half, hY]
  rw [lap, hdx, hdy, ← add_div, ← Summable.tsum_add hXs hYs]
  -- termwise
  have hterm : ∀ v : NZ, -(z.im : ℂ) ^ 2 * ((π ^ 2 * hk s 2 (qv v z.re z.im) * (qx v z.re z.im : ℂ) ^ 2 -
      π * hk s 1 (qv v z.re z.im) * (qxx v z.im : ℂ)) + (π ^ 2 * hk s 2 (qv v z.re z.im) * (qy v z.re z.im : ℂ) ^ 2 -
      π * hk s 1 (qv v z.re z.im) * (qyy v z.re z.im : ℂ))) =
      s * (1 - s) * hk s 0 (qv v z.re z.im) - ((2 * π * qf z v - 1) * rexp (-π * qf z v) : ℝ) := by
    intro v
    have hq := qf_pos z v
    rw [qf_eq_qv] at hq ⊢
    have hode := hk_ode s hq
    have e1 : (qx v z.re z.im) ^ 2 + (qy v z.re z.im) ^ 2 = (qv v z.re z.im) ^ 2 / z.im ^ 2 := by
      simp only [qx, qy, qv]; field_simp; ring
    have e2 : qxx v z.im + qyy v z.re z.im = 2 * qv v z.re z.im / z.im ^ 2 := by
      simp only [qxx, qyy, qv]; field_simp; ring
    have e1c : ((qx v z.re z.im : ℂ)) ^ 2 + (qy v z.re z.im : ℂ) ^ 2 = (qv v z.re z.im : ℂ) ^ 2 / (z.im : ℂ) ^ 2 := by
      exact_mod_cast e1
    have e2c : (qxx v z.im : ℂ) + (qyy v z.re z.im : ℂ) = 2 * (qv v z.re z.im : ℂ) / (z.im : ℂ) ^ 2 := by exact_mod_cast e2
    have hy0c : (z.im : ℂ) ≠ 0 := by exact_mod_cast hy₀.ne'
    have : -(z.im : ℂ) ^ 2 * ((π ^ 2 * hk s 2 (qv v z.re z.im) * (qx v z.re z.im : ℂ) ^ 2 -
      π * hk s 1 (qv v z.re z.im) * (qxx v z.im : ℂ)) + (π ^ 2 * hk s 2 (qv v z.re z.im) * (qy v z.re z.im : ℂ) ^ 2 -
      π * hk s 1 (qv v z.re z.im) * (qyy v z.re z.im : ℂ))) =
        -(z.im : ℂ) ^ 2 * (π ^ 2 * hk s 2 (qv v z.re z.im) * ((qx v z.re z.im : ℂ) ^ 2 + (qy v z.re z.im : ℂ) ^ 2) -
          π * hk s 1 (qv v z.re z.im) * ((qxx v z.im : ℂ) + (qyy v z.re z.im : ℂ))) := by ring
    have key : -(z.im : ℂ) ^ 2 * (π ^ 2 * hk s 2 (qv v z.re z.im) * ((qv v z.re z.im : ℂ) ^ 2 / (z.im : ℂ) ^ 2) -
        π * hk s 1 (qv v z.re z.im) * (2 * (qv v z.re z.im : ℂ) / (z.im : ℂ) ^ 2)) =
        -(π ^ 2 * (qv v z.re z.im : ℂ) ^ 2 * hk s 2 (qv v z.re z.im) -
          2 * π * (qv v z.re z.im : ℂ) * hk s 1 (qv v z.re z.im)) := by
      field_simp
    rw [this, e1c, e2c, key]
    linear_combination (-1 : ℂ) * hode
  have hS0 : Summable fun v : NZ => hk s 0 (qv v z.re z.im) := hX0
  have hB : Summable fun v : NZ => (((2 * π * qf z v - 1) * rexp (-π * qf z v) : ℝ) : ℂ) :=
    Complex.summable_ofReal.2 (summable_boundary z)
  have hsumc : ∑' v : NZ, (((2 * π * qf z v - 1) * rexp (-π * qf z v) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_tsum, tsum_boundary]; simp
  rw [mul_div_assoc', ← tsum_mul_left]
  simp_rw [hterm]
  rw [Summable.tsum_sub (hS0.mul_left _) hB, tsum_mul_left, hsumc, Estar_eq_tsum]
  simp_rw [qf_eq_qv]
  have h1' : 1 - s ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  field_simp
  ring

lemma lap_div_const (f : ℍ → ℂ) (c : ℂ) (z : ℍ) : lap (fun w => f w / c) z = lap f z / c := by
  unfold lap
  have hx : deriv (fun x => f (ofXY (x, z.im)) / c) = fun x => deriv (fun x => f (ofXY (x, z.im))) x / c :=
    funext fun x => deriv_div_const _
  have hy : deriv (fun y => f (ofXY (z.re, y)) / c) = fun y => deriv (fun y => f (ofXY (z.re, y))) y / c :=
    funext fun y => deriv_div_const _
  rw [hx, hy, deriv_div_const, deriv_div_const]
  ring

/-- **The normalised eigen-equation**: `Δ(E*(·, s)/Λ(2s)) = s(1 − s)E*(·, s)/Λ(2s)` for `s ≠ 0, 1`. -/
theorem lap_Estar_div (z : ℍ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    lap (fun w => Estar w s / completedRiemannZeta (2 * s)) z =
      s * (1 - s) * (Estar z s / completedRiemannZeta (2 * s)) := by
  rw [lap_div_const, lap_Estar z h0 h1, mul_div_assoc]

/-- **`ΔE(·, s) = s(1 − s)E(·, s)`** for the Eisenstein series `E(z, s) = ½Σ_{(c,d) = 1}(y/|cz + d|²)^s`,
`Re s > 1`. -/
theorem lap_E (z : ℍ) {s : ℂ} (hs : 1 < s.re) : lap (fun w => E w s) z = s * (1 - s) * E z s := by
  have hΛ : completedRiemannZeta (2 * s) ≠ 0 := PavlovFaddeev.completed_ne_zero_of_one_le_re (by simp; linarith)
  have hE : ∀ w, E w s = Estar w s / completedRiemannZeta (2 * s) := fun w => by
    rw [Estar_eq w hs]; field_simp
  have h0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have h1 : s ≠ 1 := by rintro rfl; simp at hs
  simp_rw [hE]
  exact lap_Estar_div z h0 h1

end ModLaplacian
