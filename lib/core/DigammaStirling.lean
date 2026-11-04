import Mathlib
import BinetProof

/-! # Explicit Stirling remainder for the digamma function

For `Re z > 0`:
`‖ψ(z) − (log z − 1/(2z) − 1/(12 z²))‖ ≤ 1/(120 (Re z)⁴)` (`digamma_stirling`).

Proof: from Binet's Laplace form `ψ(z) = log z − 1/(2z) − ∫₀^∞ e^{−zs}φ(s) ds` (`GammaIntegrals.digamma_eq_lap`),
the elementary bound `−s³/720 ≤ φ(s) − s/12 ≤ 0` for `s > 0` (`phiB_bounds`, via a chain of monotonicity
arguments for `x cosh x − sinh x`, …), `∫₀^∞ s e^{−zs} ds = 1/z²` and `∫₀^∞ s³e^{−cs} ds = 6/c⁴`.
-/

open Real MeasureTheory Set Filter Topology

noncomputable section

namespace DigammaStirling

/-! ## Elementary inequalities -/

lemma nonneg_of_deriv {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hd : ∀ x, 0 < x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun y _ => (hf y).continuousAt.continuousWithinAt
    · exact fun y _ => (hf y).differentiableAt.differentiableWithinAt
    · intro y hy; rw [interior_Ici] at hy; rw [(hf y).deriv]; exact hd y hy
  have := hm self_mem_Ici hx hx
  rw [← h0]; exact this

lemma xsinh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x * Real.sinh x :=
  mul_nonneg hx (Real.sinh_nonneg_iff.2 hx)

/-- `h₁(x) = x cosh x − sinh x`. -/
def h1 (x : ℝ) : ℝ := x * Real.cosh x - Real.sinh x

lemma h1_deriv (x : ℝ) : HasDerivAt h1 (x * Real.sinh x) x := by
  have := ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x)
  convert this using 1
  · ext y; simp [h1]
  · simp only [id]; ring

lemma h1_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ h1 x :=
  nonneg_of_deriv h1_deriv (by simp [h1]) (fun y hy => xsinh_nonneg hy.le) hx

/-- `g(x) = x cosh x − sinh x − (x²/3) sinh x ≤ 0`. -/
def g (x : ℝ) : ℝ := x * Real.cosh x - Real.sinh x - x ^ 2 / 3 * Real.sinh x

lemma g_nonpos {x : ℝ} (hx : 0 ≤ x) : g x ≤ 0 := by
  have hd : ∀ y, HasDerivAt (fun y => -g y) (y / 3 * h1 y) y := by
    intro y
    have := (((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)).sub
      (((hasDerivAt_pow 2 y).div_const 3).mul (Real.hasDerivAt_sinh y))
    convert this.neg using 1
    · ext; simp [g]
    · simp [h1]; ring
  have := nonneg_of_deriv hd (by simp [g]) (fun y hy => mul_nonneg (by linarith) (h1_nonneg hy.le)) hx
  linarith

/-- `m(x) = −15 h₁ + 4x² sinh x + x³ cosh x ≥ 0`. -/
def m (x : ℝ) : ℝ := -15 * h1 x + 4 * x ^ 2 * Real.sinh x + x ^ 3 * Real.cosh x

lemma m_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ m x := by
  have hd : ∀ y, HasDerivAt m (7 * y * h1 y + y ^ 3 * Real.sinh y) y := by
    intro y
    have := (((h1_deriv y).const_mul (-15)).add (((hasDerivAt_pow 2 y).const_mul 4).mul
      (Real.hasDerivAt_sinh y))).add ((hasDerivAt_pow 3 y).mul (Real.hasDerivAt_cosh y))
    convert this using 1
    · ext; simp [m]
    · simp [h1]; ring
  refine nonneg_of_deriv hd (by simp [m, h1]) (fun y hy => ?_) hx
  have := h1_nonneg hy.le
  have := xsinh_nonneg hy.le
  have : 0 ≤ y ^ 2 * (y * Real.sinh y) := mul_nonneg (sq_nonneg y) this
  nlinarith

lemma k_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ g x + x ^ 4 / 45 * Real.sinh x := by
  have hd : ∀ y, HasDerivAt (fun y => g y + y ^ 4 / 45 * Real.sinh y) (y / 45 * m y) y := by
    intro y
    have := ((((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)).sub
      (((hasDerivAt_pow 2 y).div_const 3).mul (Real.hasDerivAt_sinh y))).add
      (((hasDerivAt_pow 4 y).div_const 45).mul (Real.hasDerivAt_sinh y))
    convert this using 1
    · ext; simp [g]
    · simp [m, h1]; ring
  exact nonneg_of_deriv hd (by simp [g]) (fun y hy => mul_nonneg (by linarith) (m_nonneg hy.le)) hx

open GammaIntegrals in
lemma phiB_eq {s : ℝ} (hs : 0 < s) :
    phiB s - s / 12 = g (s / 2) / (2 * (s / 2) * Real.sinh (s / 2)) := by
  set x := s / 2 with hxdef
  have hx : 0 < x := by positivity
  have hsh : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx
  have hs2 : s = 2 * x := by rw [hxdef]; ring
  set a := Real.exp x with ha
  have ha1 : 1 < a := by rw [ha]; exact Real.one_lt_exp_iff.2 hx
  have hes : Real.exp (-s) = (a ^ 2)⁻¹ := by
    rw [hs2, Real.exp_neg, ha, show (2:ℝ) * x = x + x by ring, Real.exp_add]; ring
  have hc : Real.cosh x = (a + a⁻¹) / 2 := by rw [Real.cosh_eq, ha, Real.exp_neg]
  have hn : Real.sinh x = (a - a⁻¹) / 2 := by rw [Real.sinh_eq, ha, Real.exp_neg]
  unfold phiB g
  rw [hes, hc, hn, hs2]
  have : a ^ 2 - 1 ≠ 0 := by nlinarith
  have : a - a⁻¹ ≠ 0 := by
    have : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha1
    linarith
  have : (1:ℝ) - (a ^ 2)⁻¹ ≠ 0 := by
    have : (a ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    linarith
  have : a ≠ 0 := by linarith
  field_simp
  ring

open GammaIntegrals in
theorem phiB_bounds {s : ℝ} (hs : 0 < s) : |phiB s - s / 12| ≤ s ^ 3 / 720 := by
  rw [phiB_eq hs]
  have hx : 0 < s / 2 := by positivity
  have hsh : 0 < Real.sinh (s / 2) := Real.sinh_pos_iff.2 hx
  have hD : 0 < 2 * (s / 2) * Real.sinh (s / 2) := by positivity
  have g0 := g_nonpos hx.le
  have k0 := k_nonneg hx.le
  rw [abs_le]; constructor
  · rw [le_div_iff₀ hD]
    have : -(s ^ 3 / 720) * (2 * (s / 2) * Real.sinh (s / 2)) = -((s / 2) ^ 4 / 45 * Real.sinh (s / 2)) := by
      ring
    linarith
  · exact (div_nonpos_of_nonpos_of_nonneg g0 hD.le).trans (by positivity)

/-! ## Laplace integrals -/

lemma integrableOn_pow_exp {c : ℝ} (hc : 0 < c) (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(c * s))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k:ℝ)) (b := c) (by linarith [k.cast_nonneg (α := ℝ)])
    one_pos hc
  refine this.congr_fun (fun s hs => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]

lemma integral_pow3_exp {c : ℝ} (hc : 0 < c) :
    ∫ s in Ioi (0:ℝ), s ^ 3 * Real.exp (-(c * s)) = 6 / c ^ 4 := by
  have e : EqOn (fun t : ℝ => t ^ ((4 : ℝ) - 1) * Real.exp (-(c * t)))
      (fun t => t ^ 3 * Real.exp (-(c * t))) (Ioi 0) := fun t _ => by
    simp only; norm_num
  rw [← setIntegral_congr_fun measurableSet_Ioi e, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hc,
    show (4:ℝ) = (3:ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial,
    show ((3:ℕ):ℝ) + 1 = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  norm_num [Nat.factorial]; field_simp

lemma integral_s_cexp {z : ℂ} (hz : 0 < z.re) :
    ∫ s in Ioi (0:ℝ), Complex.exp (-(z * s)) * (s : ℂ) = 1 / z ^ 2 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  set F : ℝ → ℂ := fun s => -((s : ℂ) / z + 1 / z ^ 2) * Complex.exp (-(z * s))
  have hF : ∀ s ∈ Ici (0:ℝ), HasDerivAt F (Complex.exp (-(z * s)) * (s : ℂ)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (-(z * s))) (Complex.exp (-(z * s)) * (-(z * 1))) s :=
      ((h1.const_mul z).neg).cexp
    have h3 : HasDerivAt (fun s : ℝ => -((s : ℂ) / z + 1 / z ^ 2)) (-(1 / z)) s := by
      exact (((h1.div_const z).add_const (1 / z ^ 2)).neg).congr_deriv (by ring)
    convert h3.mul h2 using 1; field_simp; ring
  have hint : IntegrableOn (fun s : ℝ => Complex.exp (-(z * s)) * (s : ℂ)) (Ioi 0) := by
    refine Integrable.mono' (integrableOn_pow_exp hz 1) ?_ ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun s hs => ?_))
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · rw [norm_mul, GammaIntegrals.norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, pow_one, mul_comm]
  have hlim : Tendsto F atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ s : ℝ, 0 ≤ s → ‖F s‖ ≤ (s / ‖z‖ + 1 / ‖z‖ ^ 2) * Real.exp (-(z.re * s)) := by
      intro s hs
      simp only [F, norm_mul, norm_neg, GammaIntegrals.norm_cexp_neg_mul]
      gcongr
      refine (norm_add_le _ _).trans ?_
      simp [Complex.norm_real, abs_of_nonneg hs]
    have ht : Tendsto (fun s : ℝ => (s / ‖z‖ + 1 / ‖z‖ ^ 2) * Real.exp (-(z.re * s))) atTop (𝓝 0) := by
      have a1 : Tendsto (fun s : ℝ => s * Real.exp (-(z.re * s))) atTop (𝓝 0) := by
        have := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop hz)
        have := this.div_const z.re
        refine (this.congr fun s => ?_).trans (by simp)
        simp [Function.comp]; field_simp
      have a2 : Tendsto (fun s : ℝ => Real.exp (-(z.re * s))) atTop (𝓝 0) := by
        have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hz)
        exact this.congr fun s => by simp
      have := (a1.div_const ‖z‖).add (a2.const_mul (1 / ‖z‖ ^ 2))
      simp only [zero_div, mul_zero, add_zero] at this
      refine this.congr fun s => by ring
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
    filter_upwards [eventually_ge_atTop 0] with s hs using hb s hs
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hF hint hlim]
  simp [F]

/-! ## The Stirling remainder -/

open GammaIntegrals in
/-- **Explicit digamma Stirling bound.** For `Re z > 0`,
`‖ψ(z) − (log z − 1/(2z) − 1/(12z²))‖ ≤ 1/(120 (Re z)⁴)`. -/
theorem digamma_stirling {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.digamma z - (Complex.log z - 1 / (2 * z) - 1 / (12 * z ^ 2))‖ ≤ 1 / (120 * z.re ^ 4) := by
  rw [digamma_eq_lap hz]
  have hs : IntegrableOn (fun s : ℝ => Complex.exp (-(z * s)) * (s : ℂ)) (Ioi 0) := by
    refine Integrable.mono' (integrableOn_pow_exp hz 1) ?_ ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun s hs => ?_))
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · rw [norm_mul, GammaIntegrals.norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, pow_one, mul_comm]
  have hs12 := hs.const_mul (1 / 12 : ℂ)
  have hsplit : lap z - 1 / (12 * z ^ 2) =
      ∫ s in Ioi (0:ℝ), Complex.exp (-(z * s)) * (((phiB s - s / 12 : ℝ)) : ℂ) := by
    have e1 : (∫ s in Ioi (0:ℝ), (1/12 : ℂ) * (Complex.exp (-(z * s)) * (s : ℂ))) = 1 / (12 * z ^ 2) := by
      rw [integral_const_mul, integral_s_cexp hz]; ring
    rw [← e1, lap, ← integral_sub (integrableOn_lap hz) hs12]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    push_cast; ring
  have hb : IntegrableOn (fun s : ℝ => 1 / 720 * (s ^ 3 * Real.exp (-(z.re * s)))) (Ioi 0) :=
    (integrableOn_pow_exp hz 3).const_mul _
  have key : ‖lap z - 1 / (12 * z ^ 2)‖ ≤ 1 / (120 * z.re ^ 4) := by
    rw [hsplit]
    refine (norm_integral_le_of_norm_le hb ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun s hs => ?_))).trans_eq ?_
    · rw [norm_mul, GammaIntegrals.norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs]
      have := phiB_bounds hs
      have he := (Real.exp_pos (-(z.re * s))).le
      calc Real.exp (-(z.re * s)) * |phiB s - s / 12| ≤ Real.exp (-(z.re * s)) * (s ^ 3 / 720) :=
            mul_le_mul_of_nonneg_left this he
        _ = 1 / 720 * (s ^ 3 * Real.exp (-(z.re * s))) := by ring
    · rw [integral_const_mul, integral_pow3_exp hz]; field_simp; ring
  calc ‖Complex.log z - 1 / (2 * z) - lap z - (Complex.log z - 1 / (2 * z) - 1 / (12 * z ^ 2))‖
      = ‖lap z - 1 / (12 * z ^ 2)‖ := by rw [← norm_neg]; congr 1; ring
    _ ≤ _ := key

/-! ## Real part on the line `Re z = 1/4`, after `N` recurrence steps -/

/-- Shifted Stirling approximation of `Re ψ(1/4 + ib)`: with `a = N + 1/4`, `r = a² + b²`,
`½ log r − a/(2r) − (a² − b²)/(12 r²) − Σ_{k<N} (k + 1/4)/((k + 1/4)² + b²)`. -/
def psiApx (N : ℕ) (b : ℝ) : ℝ :=
  let a : ℝ := N + 1 / 4
  let r : ℝ := a ^ 2 + b ^ 2
  Real.log r / 2 - a / (2 * r) - (a ^ 2 - b ^ 2) / (12 * r ^ 2)
    - ∑ k ∈ Finset.range N, ((k:ℝ) + 1 / 4) / (((k:ℝ) + 1 / 4) ^ 2 + b ^ 2)

theorem re_digamma_quarter (N : ℕ) (b : ℝ) :
    |(Complex.digamma (1 / 4 + b * Complex.I)).re - psiApx N b| ≤ 1 / (120 * ((N:ℝ) + 1 / 4) ^ 4) := by
  set z : ℂ := 1 / 4 + b * Complex.I
  have hzre : z.re = 1 / 4 := by simp [z]
  have hs : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h; have := congrArg Complex.re h; simp [z] at this; linarith [m.cast_nonneg (α := ℝ)]
  have hrec := Complex.digamma_apply_add_nat hs N
  set w : ℂ := z + N
  have hwre : w.re = N + 1 / 4 := by simp [w, hzre]; ring
  have hwim : w.im = b := by simp [w, z]
  have hw : 0 < w.re := by rw [hwre]; positivity
  have hst := digamma_stirling hw
  have hre : (Complex.digamma z).re = (Complex.digamma w).re
      - (∑ k ∈ Finset.range N, (z + k)⁻¹).re := by rw [hrec]; simp
  have hnsq : Complex.normSq w = ((N:ℝ) + 1/4) ^ 2 + b ^ 2 := by
    rw [Complex.normSq_apply, hwre, hwim]; ring
  have hr : 0 < ((N:ℝ) + 1/4) ^ 2 + b ^ 2 := by positivity
  have hlog : (Complex.log w).re = Real.log (((N:ℝ) + 1/4) ^ 2 + b ^ 2) / 2 := by
    rw [Complex.log_re, ← hnsq, Complex.normSq_eq_norm_sq, Real.log_pow]; push_cast; ring
  have h2 : (1 / (2 * w)).re = ((N:ℝ) + 1/4) / (2 * (((N:ℝ) + 1/4) ^ 2 + b ^ 2)) := by
    rw [one_div, mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.inv_re, hnsq, hwre]
    simp [Complex.normSq_apply]; field_simp
  have h12 : (1 / (12 * w ^ 2)).re
      = (((N:ℝ) + 1/4) ^ 2 - b ^ 2) / (12 * (((N:ℝ) + 1/4) ^ 2 + b ^ 2) ^ 2) := by
    rw [one_div, mul_inv, Complex.mul_re, Complex.inv_re (w ^ 2), Complex.inv_im (w ^ 2)]
    have : Complex.normSq (w ^ 2) = (((N:ℝ) + 1/4) ^ 2 + b ^ 2) ^ 2 := by rw [map_pow, hnsq]
    rw [this]
    have e1 : (w ^ 2).re = ((N:ℝ) + 1/4) ^ 2 - b ^ 2 := by rw [pow_two, Complex.mul_re, hwre, hwim]; ring
    rw [e1]; simp; field_simp
  have hk : (∑ k ∈ Finset.range N, (z + k)⁻¹).re
      = ∑ k ∈ Finset.range N, ((k:ℝ) + 1 / 4) / (((k:ℝ) + 1 / 4) ^ 2 + b ^ 2) := by
    rw [Complex.re_sum]; apply Finset.sum_congr rfl; intro k _
    rw [Complex.inv_re, Complex.normSq_apply]; simp [z]; ring_nf
  have hre2 := Complex.re_le_norm (Complex.digamma w - (Complex.log w - 1 / (2 * w) - 1 / (12 * w ^ 2)))
  have hre3 := Complex.abs_re_le_norm (Complex.digamma w - (Complex.log w - 1 / (2 * w) - 1 / (12 * w ^ 2)))
  simp only [Complex.sub_re] at hre3
  rw [hlog, h2, h12] at hre3
  rw [hwre] at hst
  rw [hre, hk]
  unfold psiApx
  simp only
  have := hre3.trans hst
  calc _ = |(Complex.digamma w).re - (Real.log (((N:ℝ) + 1/4) ^ 2 + b ^ 2) / 2
        - ((N:ℝ) + 1/4) / (2 * (((N:ℝ) + 1/4) ^ 2 + b ^ 2))
        - (((N:ℝ) + 1/4) ^ 2 - b ^ 2) / (12 * (((N:ℝ) + 1/4) ^ 2 + b ^ 2) ^ 2))| := by congr 1; ring
    _ ≤ _ := this

end DigammaStirling
