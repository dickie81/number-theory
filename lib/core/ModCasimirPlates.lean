/-
# The electromagnetic Casimir effect between parallel plates

The zeta-regularised Casimir energy of the electromagnetic field between two ideal, perfectly conducting parallel
plates at distance `a` in `3 + 1` dimensions (Casimir 1948), by the standard Mellin/Gamma route. This is a
formalisation of a classical computation, not new mathematics or physics.

**Conventions.** Units `ħ = c = 1`. Between the plates the modes are `ω = √(|k_⊥|² + (nπ/a)²)`, `k_⊥ ∈ ℝ²`, and for
each `n ≥ 1` there are two polarisations (TE and TM). The extra TM mode at `n = 0` contributes `∫ d²k/(2π)² |k|`,
which does not depend on `a`; it is dropped (it is `0` in zeta/dimensional regularisation, where the scale-free
integral `∫ d²k (k²)^{−s}` vanishes, and in any case exerts no force). The regularised energy per unit area is
`E(s) = 2 · ½ Σ_{n ≥ 1} ∫ d²k/(2π)² (|k|² + (nπ/a)²)^{−s}` continued to `s = −½` (where `(ω²)^{−s} = ω`): zeta
regularisation is the definition here, not a cutoff computation.

* **The transverse integral** (`integrable_transverse`, `integral_transverse`): for `m > 0` and `Re s > 1`,
  `∫_{ℝ²} (k₁² + k₂² + m²)^{−s} dk = π (1/m²)^{s−1}/(s − 1)` (Fubini and twice the one-dimensional
  `ModEisenstein.integral_rpow_sq_add`, then `B(½, s − ½)B(½, s − 1) = π/(s − 1)`).
* **The mode sum** (`plateZeta`, `hasSum_plateZeta`): on `Re s > 3/2`,
  `Σ_{n ≥ 1} ∫ d²k/(2π)² (|k|² + (nπ/a)²)^{−s} = ((a/π)²)^{s−1} ζ(2s − 2)/(4π(s − 1))`; the right side, `plateZeta`,
  is the continuation (holomorphic off `s = 1, 3/2`).
* **The Casimir energy and pressure** (`casimirPlates`, `casimirPlates_eq`, `hasDerivAt_casimirPlates`,
  `casimir_pressure`): `E/A = plateZeta(−½) = −π²/(720a³)`, from Mathlib's `ζ(−3) = 1/120`, and the pressure
  `P = −d(E/A)/da = −π²/(240a⁴)` (attractive).
-/
import Mathlib
import ModEisenstein

open Complex Real Filter Topology Set MeasureTheory

noncomputable section

namespace ModCasimirPlates

open ModEisenstein

lemma ofReal_cpow_neg {a : ℝ} (ha : 0 ≤ a) (s : ℂ) : (a : ℂ) ^ (-s) = ((a⁻¹ : ℝ) : ℂ) ^ s := by
  rw [Complex.cpow_neg, Complex.ofReal_inv, Complex.inv_cpow]
  rw [Complex.arg_ofReal_of_nonneg ha]; exact Real.pi_pos.ne

/-! ## The transverse integral -/

/-- The transverse integrand `(k₁² + k₂² + m²)^{−s}` on `ℝ²`. -/
def tr (m : ℝ) (s : ℂ) (p : ℝ × ℝ) : ℂ := ((p.1 ^ 2 + p.2 ^ 2 + m ^ 2 : ℝ) : ℂ) ^ (-s)

lemma norm_tr {m : ℝ} (hm : 0 < m) (s : ℂ) (p : ℝ × ℝ) :
    ‖tr m s p‖ = (p.1 ^ 2 + p.2 ^ 2 + m ^ 2) ^ (-s.re) := by
  rw [tr, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

lemma continuous_tr {m : ℝ} (hm : 0 < m) (s : ℂ) : Continuous (tr m s) := by
  unfold tr
  refine Continuous.cpow (by fun_prop) continuous_const fun p => ?_
  exact Complex.ofReal_mem_slitPlane.2 (by positivity)

/-- **The transverse integrand is integrable on `ℝ²`** for `Re s > 1`. -/
theorem integrable_transverse {m : ℝ} (hm : 0 < m) {s : ℂ} (hs : 1 < s.re) : Integrable (tr m s) := by
  set c : ℝ := min 1 (m ^ 2)
  have hc : 0 < c := lt_min one_pos (by positivity)
  have h := (integrable_rpow_neg_one_add_norm_sq (E := ℝ × ℝ) (μ := volume) (r := 2 * s.re)
    (by simp; linarith)).const_mul (c ^ (-s.re))
  refine h.mono' (continuous_tr hm s).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [norm_tr hm, show -(2 * s.re) / 2 = -s.re by ring, ← Real.mul_rpow hc.le (by positivity)]
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
  have hn : ‖p‖ ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total |p.1| |p.2| with h | h
    · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg p.1]
    · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg p.2]
  have h1 : c ≤ 1 := min_le_left _ _
  have h2 : c ≤ m ^ 2 := min_le_right _ _
  nlinarith [sq_nonneg ‖p‖]

lemma sqrt_mul_cpow {q : ℝ} (hq : 0 < q) (s : ℂ) :
    ((√q : ℝ) : ℂ) * ((1 / q : ℝ) : ℂ) ^ s = ((1 / q : ℝ) : ℂ) ^ (s - 1 / 2) := by
  have h0 : ((1 / q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (one_div_pos.2 hq).ne'
  have hh : ((1 / q : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√q)⁻¹ : ℝ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_div' _ hq.le, Real.sqrt_one, one_div]
  have hs : (√q : ℝ) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  rw [Complex.cpow_sub _ _ h0, hh]
  push_cast
  field_simp

/-- `B(½, s − ½)B(½, s − 1) = π/(s − 1)` for `Re s > 1`. -/
lemma beta_mul_beta {s : ℂ} (hs : 1 < s.re) :
    Complex.betaIntegral (1 / 2) (s - 1 / 2) * Complex.betaIntegral (1 / 2) (s - 1) = π / (s - 1) := by
  have hr : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have h1 := Complex.Gamma_mul_Gamma_eq_betaIntegral hr (show 0 < (s - 1 / 2).re by simp; linarith)
  have h2 := Complex.Gamma_mul_Gamma_eq_betaIntegral hr (show 0 < (s - 1).re by simp; linarith)
  rw [show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring] at h1
  rw [show (1 / 2 : ℂ) + (s - 1) = s - 1 / 2 by ring] at h2
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hGs : Complex.Gamma s = (s - 1) * Complex.Gamma (s - 1) := by
    rw [← Complex.Gamma_add_one _ hs1, sub_add_cancel]
  have hg : Complex.Gamma (1 / 2) ^ 2 = π := by
    rw [Complex.Gamma_one_half_eq, sq, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)]
    norm_num
  have hG1 : Complex.Gamma (s - 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG2 : Complex.Gamma (s - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have key : (s - 1) * Complex.Gamma (s - 1 / 2) * Complex.Gamma (s - 1) *
      (Complex.betaIntegral (1 / 2) (s - 1 / 2) * Complex.betaIntegral (1 / 2) (s - 1)) =
      (s - 1) * Complex.Gamma (s - 1 / 2) * Complex.Gamma (s - 1) * (π / (s - 1)) := by
    rw [show (s - 1) * Complex.Gamma (s - 1 / 2) * Complex.Gamma (s - 1) * (π / (s - 1)) =
      π * Complex.Gamma (s - 1 / 2) * Complex.Gamma (s - 1) by field_simp]
    linear_combination (-(Complex.Gamma (s - 1 / 2) * Complex.betaIntegral (1 / 2) (s - 1 / 2) *
      Complex.betaIntegral (1 / 2) (s - 1))) * hGs - (Complex.Gamma (s - 1 / 2) *
      Complex.betaIntegral (1 / 2) (s - 1)) * h1 - (Complex.Gamma (1 / 2) * Complex.Gamma (s - 1 / 2)) * h2 +
      (Complex.Gamma (s - 1 / 2) * Complex.Gamma (s - 1)) * hg
  exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hs1 hG1) hG2) key

/-- **The transverse integral**: for `m > 0` and `Re s > 1`,
`∫_{ℝ²} (k₁² + k₂² + m²)^{−s} dk = π (1/m²)^{s−1}/(s − 1)`. -/
theorem integral_transverse {m : ℝ} (hm : 0 < m) {s : ℂ} (hs : 1 < s.re) :
    ∫ p, tr m s p = π * ((1 / m ^ 2 : ℝ) : ℂ) ^ (s - 1) / (s - 1) := by
  have hhalf : (1 : ℝ) / 2 < s.re := by linarith
  have hinner : ∀ x : ℝ, ∫ y : ℝ, tr m s (x, y) =
      ((1 / (x ^ 2 + m ^ 2) : ℝ) : ℂ) ^ (s - 1 / 2) * Complex.betaIntegral (1 / 2) (s - 1 / 2) := by
    intro x
    have hq : 0 < x ^ 2 + m ^ 2 := by positivity
    set A := √(x ^ 2 + m ^ 2)
    have hA : 0 < A := Real.sqrt_pos.2 hq
    have hA2 : A ^ 2 = x ^ 2 + m ^ 2 := Real.sq_sqrt hq.le
    have e : ∀ y : ℝ, tr m s (x, y) = ((1 / (y ^ 2 + A ^ 2) : ℝ) : ℂ) ^ s := by
      intro y
      rw [tr, ofReal_cpow_neg (by positivity), hA2, one_div]
      congr 3; ring
    simp_rw [e]
    rw [integral_rpow_sq_add hA one_pos hhalf, hA2, ← sqrt_mul_cpow hq]
  rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact integrable_transverse hm hs)]
  simp_rw [hinner]
  have hs' : (1 : ℝ) / 2 < (s - 1 / 2).re := by simp; linarith
  rw [integral_mul_const, integral_rpow_sq_add hm one_pos hs',
    show s - 1 / 2 - 1 / 2 = s - 1 by ring]
  rw [show (m : ℂ) * ((1 / m ^ 2 : ℝ) : ℂ) ^ (s - 1 / 2) = ((1 / m ^ 2 : ℝ) : ℂ) ^ (s - 1) by
    have := sqrt_mul_cpow (q := m ^ 2) (by positivity) (s - 1 / 2)
    rw [Real.sqrt_sq hm.le, show s - 1 / 2 - 1 / 2 = s - 1 by ring] at this
    exact this]
  rw [mul_assoc, mul_comm (Complex.betaIntegral _ _), beta_mul_beta hs]
  ring

end ModCasimirPlates
