import Mathlib
import GapBound

/-! # Energy of a truncated `½`-Hölder function

If `φ² ≤ M` and `(φ(t) − φ(s))² ≤ D|t − s|` on `[−a, a]`, then `1_{[−a,a]}φ` has `f(0) − f(u) ≤ (aD + M)u`
(`ind_autocorr_le`). So `E_arch ≤ (aD + M)·∫16e^{−u/4}` and `‖·‖² ≤ 2aM` (`ind_energy`; `E0` is the integral).
The jump at `±a` costs only `M·u`.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace WeilForm

/-! ## Energy of a truncated `½`-Hölder function -/

/-- If `φ² ≤ M` and `(φ t − φ s)² ≤ D|t − s|` on `[−a, a]`, the truncation `1_{[−a,a]}φ` has
`f(0) − f(u) ≤ (aD + M)u`. -/
theorem ind_autocorr_le {a D M : ℝ} (ha : 0 ≤ a) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hM : ∀ t ∈ Icc (-a) a, φ t ^ 2 ≤ M)
    (hD : ∀ t ∈ Icc (-a) a, ∀ s ∈ Icc (-a) a, (φ t - φ s) ^ 2 ≤ D * |t - s|)
    (hD0 : 0 ≤ D) {u : ℝ} (hu : 0 < u) :
    autocorr ((Icc (-a) a).indicator φ) 0 - autocorr ((Icc (-a) a).indicator φ) u
      ≤ (a * D + M) * u := by
  set g := (Icc (-a) a).indicator φ with hg
  have hM0 : 0 ≤ M := le_trans (sq_nonneg _) (hM (-a) ⟨le_rfl, by linarith⟩)
  have hb : MemLp g 2 volume :=
    memLp_indicator_of_continuous hc measurableSet_Icc measure_Icc_lt_top.ne
      (C := Real.sqrt M) fun x hx => Real.abs_le_sqrt (hM x hx)
  rw [show autocorr g 0 - autocorr g u = normSq (fun t => g t - g (t + u)) / 2 by
    rw [normSq_sub_shift hb u]; ring]
  set B : ℝ → ℝ := fun t => D * u * (Icc (-a) a).indicator 1 t
    + M * ((Icc (a - u) a).indicator 1 t + (Icc (-a - u) (-a)).indicator 1 t) with hB
  have hi : ∀ p q : ℝ, Integrable ((Icc p q).indicator (1 : ℝ → ℝ)) := fun p q =>
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  have hBint : Integrable B :=
    ((hi _ _).const_mul (D * u)).add (((hi _ _).add (hi _ _)).const_mul M)
  have hpt : ∀ t, (g t - g (t + u)) ^ 2 ≤ B t := by
    intro t
    simp only [hB, hg, Set.indicator_apply, Pi.one_apply]
    by_cases h1 : t ∈ Icc (-a) a <;> by_cases h2 : t + u ∈ Icc (-a) a
    · simp only [h1, h2, ite_true]
      have := hD t h1 (t + u) h2
      rw [show t - (t + u) = -u by ring, abs_neg, abs_of_pos hu] at this
      have e1 : 0 ≤ M * ((if t ∈ Icc (a - u) a then (1 : ℝ) else 0)
          + (if t ∈ Icc (-a - u) (-a) then (1 : ℝ) else 0)) := by
        apply mul_nonneg hM0; split_ifs <;> norm_num
      nlinarith
    · simp only [h1, h2, ite_true, ite_false, sub_zero]
      have ht : t ∈ Icc (a - u) a := by
        simp only [Set.mem_Icc, not_and_or, not_le] at h1 h2 ⊢
        rcases h2 with h2 | h2 <;> [linarith [h1.1]; exact ⟨by linarith, h1.2⟩]
      simp only [ht, ite_true]
      have := hM t h1
      have e1 : 0 ≤ M * (if t ∈ Icc (-a - u) (-a) then (1 : ℝ) else 0) := by
        apply mul_nonneg hM0; split_ifs <;> norm_num
      nlinarith [mul_nonneg (mul_nonneg hD0 hu.le) (zero_le_one' ℝ)]
    · simp only [h1, h2, ite_true, ite_false, zero_sub, neg_sq]
      have ht : t ∈ Icc (-a - u) (-a) := by
        simp only [Set.mem_Icc, not_and_or, not_le] at h1 h2 ⊢
        rcases h1 with h1 | h1
        · exact ⟨by linarith [h2.1], h1.le⟩
        · linarith [h2.2]
      simp only [ht, ite_true]
      have := hM (t + u) h2
      have e1 : 0 ≤ M * (if t ∈ Icc (a - u) a then (1 : ℝ) else 0) := by
        apply mul_nonneg hM0; split_ifs <;> norm_num
      nlinarith
    · simp only [h1, h2, ite_false, sub_self]
      have e1 : 0 ≤ M * ((if t ∈ Icc (a - u) a then (1 : ℝ) else 0)
          + (if t ∈ Icc (-a - u) (-a) then (1 : ℝ) else 0)) := by
        apply mul_nonneg hM0; split_ifs <;> norm_num
      nlinarith
  have hle : normSq (fun t => g t - g (t + u)) ≤ ∫ t, B t :=
    integral_mono ((hb.sub (memLp_shift hb u)).integrable_sq) hBint hpt
  have hBv : ∫ t, B t = D * u * (2 * a) + M * (2 * u) := by
    have v : ∀ p q : ℝ, p ≤ q → ∫ t, (Icc p q).indicator (1 : ℝ → ℝ) t = q - p := by
      intro p q hpq
      rw [integral_indicator_one measurableSet_Icc, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)]
    have e1 : ∫ t, B t = D * u * (∫ t, (Icc (-a) a).indicator (1 : ℝ → ℝ) t)
        + M * ((∫ t, (Icc (a - u) a).indicator (1 : ℝ → ℝ) t)
          + ∫ t, (Icc (-a - u) (-a)).indicator (1 : ℝ → ℝ) t) := by
      have I1 : Integrable (fun t => D * u * (Icc (-a) a).indicator (1 : ℝ → ℝ) t) :=
        (hi _ _).const_mul _
      have I2 : Integrable (fun t => (Icc (a - u) a).indicator (1 : ℝ → ℝ) t) := hi _ _
      have I3 : Integrable (fun t => (Icc (-a - u) (-a)).indicator (1 : ℝ → ℝ) t) := hi _ _
      have I23 : Integrable (fun t => M * ((Icc (a - u) a).indicator (1 : ℝ → ℝ) t
          + (Icc (-a - u) (-a)).indicator (1 : ℝ → ℝ) t)) := (I2.add I3).const_mul M
      rw [hB, integral_add I1 I23, integral_const_mul, integral_const_mul, integral_add I2 I3]
    rw [e1, v _ _ (by linarith), v _ _ (by linarith), v _ _ (by linarith)]
    ring
  rw [hBv] at hle
  nlinarith

/-- The constant `E₀ = ∫_{u>0} 16e^{−u/4}`. -/
def E0 : ℝ := ∫ u in Ioi (0 : ℝ), 16 * Real.exp (-(1 / 4) * u)

/-- **Energy of a truncated `½`-Hölder function**: the archimedean integrand is integrable and
`archE ≤ (aD + M)E₀`; also `‖1_{[−a,a]}φ‖² ≤ 2aM`. -/
theorem ind_energy {a D M : ℝ} (ha : 0 ≤ a) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hM : ∀ t ∈ Icc (-a) a, φ t ^ 2 ≤ M)
    (hD : ∀ t ∈ Icc (-a) a, ∀ s ∈ Icc (-a) a, (φ t - φ s) ^ 2 ≤ D * |t - s|) (hD0 : 0 ≤ D) :
    MemLp ((Icc (-a) a).indicator φ) 2 volume ∧
    IntegrableOn (archIntegrand ((Icc (-a) a).indicator φ)) (Ioi 0) ∧
    archE ((Icc (-a) a).indicator φ) ≤ (a * D + M) * E0 ∧
    normSq ((Icc (-a) a).indicator φ) ≤ 2 * a * M := by
  set g := (Icc (-a) a).indicator φ with hg
  have hM0 : 0 ≤ M := le_trans (sq_nonneg _) (hM (-a) ⟨le_rfl, by linarith⟩)
  have hb : MemLp g 2 volume :=
    memLp_indicator_of_continuous hc measurableSet_Icc measure_Icc_lt_top.ne
      (C := Real.sqrt M) fun x hx => Real.abs_le_sqrt (hM x hx)
  have hC : 0 ≤ a * D + M := by positivity
  have hE : IntegrableOn (fun u => (a * D + M) * (16 * Real.exp (-(1 / 4) * u))) (Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 16).const_mul _
  have hpt : ∀ u ∈ Ioi (0 : ℝ), archIntegrand g u ≤ (a * D + M) * (16 * Real.exp (-(1 / 4) * u)) := by
    intro u hu
    have hu0 : 0 < u := hu
    have hK : 0 < Real.exp (u / 2) / Real.sinh u :=
      div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu0)
    unfold archIntegrand
    calc (autocorr g 0 - autocorr g u) * (Real.exp (u / 2) / Real.sinh u)
        ≤ ((a * D + M) * u) * (Real.exp (u / 2) / Real.sinh u) :=
          mul_le_mul_of_nonneg_right (ind_autocorr_le ha hc hM hD hD0 hu0) hK.le
      _ = (a * D + M) * (u * (Real.exp (u / 2) / Real.sinh u)) := by ring
      _ ≤ (a * D + M) * (16 * Real.exp (-(1 / 4) * u)) :=
          mul_le_mul_of_nonneg_left (u_archK_le hu0) hC
  have hint : IntegrableOn (archIntegrand g) (Ioi 0) :=
    archIntegrand_integrableOn_of_lin hb hC fun _ hu => ind_autocorr_le ha hc hM hD hD0 hu
  refine ⟨hb, hint, ?_, ?_⟩
  · have := setIntegral_Ioi_le hE (fun u hu => archIntegrand_nonneg hb hu) hpt
    unfold archE E0
    rw [integral_const_mul] at this
    exact this
  · unfold normSq
    have hsq : (fun t => g t ^ 2) ≤ (Icc (-a) a).indicator (fun _ => M) := by
      intro t
      simp only [hg, Set.indicator_apply]
      split_ifs with h
      · exact hM t h
      · norm_num
    calc (∫ t, g t ^ 2) ≤ ∫ t, (Icc (-a) a).indicator (fun _ => M) t :=
          integral_mono hb.integrable_sq
            ((integrable_indicator_iff measurableSet_Icc).2
              (integrableOn_const measure_Icc_lt_top.ne)) hsq
      _ = 2 * a * M := by
          rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]; ring

end WeilForm

#print axioms WeilForm.ind_energy
