import Mathlib

/-!
# Ramp sums of the von Mangoldt function and their Laplace transforms

For coefficients `f` with `‖f n‖ ≤ 1` (a Dirichlet character), the ramp sum
`R_f(x) = Σ_{n ≤ x} Λ(n) f(n) (x/n − 1)` is the smoothed prime sum whose error the frontier of the library's
proof of the Riemann hypothesis bounds (`WindowGRH.lean`). In the variable `u = log x` its Laplace transform is
`L(Λf, s)/(s(s − 1))`, since that of `(e^u/n − 1)⁺` is `n^{−s}/(s(s − 1))`.

* `rampSum`: `R_f(x)`.
* `laplace_rampSum`: `∫₀^∞ R_f(e^u) e^{−su} du = L(Λf, s)/(s(s − 1))` for `Re s > 1`.
* `laplace_exp`, `laplace_mul_exp`: the transforms of `e^u` and `u e^u`, `1/(s − 1)` and `1/(s − 1)²`, for
  `Re s > 1`: the main terms `x` and `x log x`.
* `norm_rampSum_le`: `‖R_f(x)‖ ≤ x³` for `x ≥ 1`; `measurable_rampSum`.
-/

open Complex MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt

namespace RampLaplace

/-- The ramp sum `Σ_{n ≤ x} Λ(n) f(n) (x/n − 1)`. -/
noncomputable def rampSum (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * f n * ((x / n - 1 : ℝ) : ℂ)

/-- The ramp sum as a sum over all `n` of the ramps `(x/n − 1)⁺`, which vanish for `n > x`. -/
lemma rampSum_eq_tsum (f : ℕ → ℂ) (x : ℝ) :
    rampSum f x = ∑' n, (Λ n : ℂ) * f n * ((max (x / n - 1) 0 : ℝ) : ℂ) := by
  rw [rampSum, tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    rw [Nat.le_floor_iff' (by omega)] at h2
    rw [max_eq_left (by rw [sub_nonneg, one_le_div₀ (by positivity)]; exact h2)]
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | h1
    · simp
    · have h2 : x < n := Nat.lt_of_floor_lt (by rw [Finset.mem_Icc] at hn; omega)
      rw [max_eq_right (by rw [sub_nonpos, div_le_one₀ (by positivity)]; exact h2.le)]
      simp

/-- The `n`-th ramp `(e^u/n − 1)⁺` against `e^{−su}`, for `Re s > 1`: integrable on `u > 0`, with transform
`n^{−s}/(s(s − 1))`. Both vanish for `n = 0`. -/
lemma ramp_laplace (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => ((max (Real.exp u / n - 1) 0 : ℝ) : ℂ) * cexp (-(s * u))) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), ((max (Real.exp u / n - 1) 0 : ℝ) : ℂ) * cexp (-(s * u)) =
        (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [hs0]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have ha : (1 - s).re < 0 := by simpa using hs
  have hb : (-s).re < 0 := by simp; linarith
  have hi1 := (integrableOn_exp_mul_complex_Ioi ha (Real.log n)).div_const (n : ℂ)
  have hi2 := integrableOn_exp_mul_complex_Ioi hb (Real.log n)
  have heq : EqOn (fun u : ℝ => ((max (Real.exp u / n - 1) 0 : ℝ) : ℂ) * cexp (-(s * u)))
      (fun u : ℝ => cexp ((1 - s) * u) / n - cexp (-s * u)) (Ioi (Real.log n)) := fun u hu => by
    dsimp only
    rw [max_eq_left (by rw [sub_nonneg, one_le_div₀ hn0, ← Real.exp_log hn0]; exact Real.exp_le_exp.2 hu.le)]
    push_cast
    rw [show (1 - s) * (u : ℂ) = u + -(s * u) by ring, Complex.exp_add, neg_mul]
    ring
  have hzero : ∀ u ∈ Ioi (0 : ℝ) \ Ioi (Real.log n),
      ((max (Real.exp u / n - 1) 0 : ℝ) : ℂ) * cexp (-(s * u)) = 0 := fun u hu => by
    have : Real.exp u ≤ n := Real.exp_log hn0 ▸ Real.exp_le_exp.2 (not_lt.1 hu.2)
    rw [max_eq_right (by rw [sub_nonpos, div_le_one₀ hn0]; exact this), Complex.ofReal_zero, zero_mul]
  refine ⟨(IntegrableOn.congr_fun (hi1.sub hi2) heq.symm measurableSet_Ioi).of_forall_sdiff_eq_zero
    measurableSet_Ioi hzero, ?_⟩
  have h1 : cexp (-s * Real.log n) = (n : ℂ) ^ (-s) := by
    rw [Complex.cpow_def_of_ne_zero hn', Complex.natCast_log, mul_comm]
  have h2 : cexp ((1 - s) * Real.log n) = n * (n : ℂ) ^ (-s) := by
    rw [show (1 - s) * (Real.log n : ℂ) = Real.log n + -s * Real.log n by ring, Complex.exp_add, h1,
      Complex.natCast_log, Complex.exp_log hn']
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 (by rintro rfl; norm_num at hs)
  have hs1' : 1 - s ≠ 0 := sub_ne_zero.2 (by rintro rfl; norm_num at hs)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi (Real.log_nonneg (by exact_mod_cast hn))) hzero,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hi1 hi2, integral_div,
    integral_exp_mul_complex_Ioi ha, integral_exp_mul_complex_Ioi hb, h1, h2]
  generalize (n : ℂ) ^ (-s) = E
  field_simp
  ring

/-- The real ramp transform: `∫₀^∞ (e^u/n − 1)⁺ e^{−σu} du = n^{−σ}/(σ(σ − 1))` for `σ > 1`. -/
lemma integral_ramp_real (n : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    ∫ u in Ioi (0 : ℝ), max (Real.exp u / n - 1) 0 * Real.exp (-(σ * u)) = (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
  have h := (ramp_laplace n (s := σ) (by simpa using hσ)).2
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg n)] at h
  exact_mod_cast h

/-- **The Laplace transform of a ramp sum**: `L(Λf, s)/(s(s − 1))` for `Re s > 1`. -/
theorem laplace_rampSum {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), rampSum f (Real.exp u) * cexp (-(s * u)) =
      LSeries (fun n => (Λ n : ℂ) * f n) s / (s * (s - 1)) := by
  -- the `n`-th term of the ramp sum against `e^{−su}`
  set F : ℕ → ℝ → ℂ := fun n u =>
    (Λ n : ℂ) * f n * (((max (Real.exp u / n - 1) 0 : ℝ) : ℂ) * cexp (-(s * u)))
  have hterm (n : ℕ) : LSeries.term (fun n => (Λ n : ℂ) * f n) s n = (Λ n : ℂ) * f n * (n : ℂ) ^ (-s) :=
    LSeries.term_def₀ (by simp) s n
  -- `∫ ‖F n‖` is the norm of the `n`-th term of `L(Λf, s)` over `σ(σ − 1)`, for `σ = Re s`
  have hnorm (n : ℕ) : ∫ u in Ioi 0, ‖F n u‖ =
      ‖LSeries.term (fun n => (Λ n : ℂ) * f n) s n‖ / (s.re * (s.re - 1)) := by
    have e (u : ℝ) : ‖F n u‖ = ‖(Λ n : ℂ) * f n‖ * (max (Real.exp u / n - 1) 0 * Real.exp (-(s.re * u))) := by
      simp [F, Complex.norm_exp, abs_of_nonneg]
    simp_rw [e]
    rw [integral_const_mul, integral_ramp_real n hs, hterm, norm_mul _ ((n : ℂ) ^ (-s)),
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simp; linarith), Complex.neg_re]
    ring
  have hsum : Summable fun n => ∫ u in Ioi 0, ‖F n u‖ := by
    refine (((summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => LSeries.norm_term_le s ?_).div_const _).congr fun n => (hnorm n).symm
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hf n)
  have hsum_eq (u : ℝ) : rampSum f (Real.exp u) * cexp (-(s * u)) = ∑' n, F n u := by
    rw [rampSum_eq_tsum, ← tsum_mul_right]
    simp only [F, mul_assoc]
  simp_rw [hsum_eq]
  rw [← integral_tsum_of_summable_integral_norm (fun n => (ramp_laplace n hs).1.const_mul _) hsum, LSeries,
    ← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [integral_const_mul, (ramp_laplace n hs).2, hterm]
  ring

/-- The transform of `e^u`: `1/(s − 1)` for `Re s > 1`. -/
theorem laplace_exp {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), (Real.exp u : ℂ) * cexp (-(s * u)) = 1 / (s - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, s = 1 - a := ⟨1 - s, by ring⟩
  have ha : a.re < 0 := by simp at hs; linarith
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have h (u : ℝ) : (Real.exp u : ℂ) * cexp (-((1 - a) * u)) = cexp (a * u) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    ring_nf
  simp_rw [h]
  rw [integral_exp_mul_complex_Ioi ha 0]
  simp
  field_simp

/-- The transform of `u e^u`: `1/(s − 1)²` for `Re s > 1`. -/
theorem laplace_mul_exp {s : ℂ} (hs : 1 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((u * Real.exp u : ℝ) : ℂ) * cexp (-(s * u)) = 1 / (s - 1) ^ 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, s = 1 - a := ⟨1 - s, by ring⟩
  have ha : a.re < 0 := by simp at hs; linarith
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have h (u : ℝ) : ((u * Real.exp u : ℝ) : ℂ) * cexp (-((1 - a) * u)) = u * cexp (a * u) := by
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  simp_rw [h]
  -- `u e^{au}` is integrable, and has the primitive `(u/a − 1/a²) e^{au}`
  have hi : IntegrableOn (fun u : ℝ => (u : ℂ) * cexp (a * u)) (Ioi 0) := by
    refine (integrable_norm_iff (Continuous.aestronglyMeasurable (by fun_prop))).1 ?_
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := -a.re) (by norm_num) one_pos
      (by linarith)).congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp [Complex.norm_exp, abs_of_pos (mem_Ioi.1 hu)]
  have he := integrableOn_exp_mul_complex_Ioi ha 0
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => a⁻¹ * (u * cexp (a * u)) - (a ^ 2)⁻¹ * cexp (a * u))
      (u * cexp (a * u)) u := by
    have h1 : HasDerivAt (fun z : ℂ => cexp (a * z)) (cexp (a * u) * a) u := by
      simpa using ((hasDerivAt_id (u : ℂ)).const_mul a).cexp
    refine ((((hasDerivAt_id (u : ℂ)).mul h1).const_mul a⁻¹).sub
      (h1.const_mul (a ^ 2)⁻¹)).comp_ofReal.congr_deriv ?_
    simp only [id_eq]
    field_simp
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hd u) hi
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun u _ => hd u) hi ((hi.const_mul _).sub (he.const_mul _)))]
  simp

/-- `‖R_f(x)‖ ≤ x³` for `x ≥ 1`. -/
theorem norm_rampSum_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 1 ≤ x) : ‖rampSum f x‖ ≤ x ^ 3 := by
  have hx0 : 0 ≤ x := by linarith
  calc ‖rampSum f x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, x * x := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
        have h1' : (1 : ℝ) ≤ n := by exact_mod_cast h1
        have h2' : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 h2
        -- `Λ(n) ≤ log n ≤ x` and `0 ≤ x/n − 1 ≤ x`
        have hΛ : ‖(Λ n : ℂ)‖ ≤ x := by
          rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact ArithmeticFunction.vonMangoldt_le_log.trans
            ((Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith))
        have hr : ‖((x / n - 1 : ℝ) : ℂ)‖ ≤ x := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [div_nonneg hx0 (by linarith : (0 : ℝ) ≤ n)], by linarith [div_le_self hx0 h1']⟩
        rw [norm_mul, norm_mul]
        exact mul_le_mul ((mul_le_of_le_one_right (norm_nonneg _) (hf n)).trans hΛ) hr (norm_nonneg _) hx0
    _ = ⌊x⌋₊ * (x * x) := by simp
    _ ≤ x * (x * x) := by gcongr; exact Nat.floor_le hx0
    _ = x ^ 3 := by ring

/-- The ramp sum is measurable in `x`. -/
theorem measurable_rampSum (f : ℕ → ℂ) : Measurable (rampSum f) := by
  have h : Measurable fun p : ℝ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, (Λ n : ℂ) * f n * ((p.1 / n - 1 : ℝ) : ℂ) :=
    measurable_from_prod_countable_left fun _ => by dsimp only; fun_prop
  exact (h.comp (measurable_id.prodMk Nat.measurable_floor) :)

end RampLaplace

#print axioms RampLaplace.laplace_rampSum
#print axioms RampLaplace.norm_rampSum_le
#print axioms RampLaplace.measurable_rampSum
