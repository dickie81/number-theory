import Mathlib
import WeilCoer
import LegSpan

/-! # Fourier transforms of cut polynomials: integration by parts and Plancherel

For a real polynomial `q`, `Φ q t = ∫_{-1/2}^{1/2} q(u+1/2) e^{-itu} du`. -/

namespace GsFourier

open Real Complex Polynomial MeasureTheory Finset FourierTransform

noncomputable def Φ (q : ℝ[X]) (t : ℝ) : ℂ :=
  ∫ u in (-(1/2):ℝ)..(1/2), ((q.eval (u + 1/2) : ℝ) : ℂ) * cexp (((-(t * u) : ℝ) : ℂ) * I)

noncomputable def E (q : ℝ[X]) (t : ℝ) : ℂ :=
  (((q.eval 1 : ℝ) : ℂ) * cexp (((-(t * (1/2)) : ℝ) : ℂ) * I)
    - ((q.eval 0 : ℝ) : ℂ) * cexp (((-(t * (-(1/2))) : ℝ) : ℂ) * I)) / (((-t : ℝ) : ℂ) * I)

lemma ibp (q : ℝ[X]) {t : ℝ} (ht : t ≠ 0) :
    Φ q t = E q t + 1 / ((t : ℂ) * I) * Φ (derivative q) t := by
  set c : ℂ := ((-t : ℝ) : ℂ) * I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; refine mul_ne_zero ?_ I_ne_zero; exact_mod_cast neg_ne_zero.2 ht
  have hu : ∀ x ∈ Set.uIcc (-(1/2):ℝ) (1/2), HasDerivAt (fun u : ℝ => ((q.eval (u + 1/2) : ℝ) : ℂ))
      (((derivative q).eval (x + 1/2) : ℝ) : ℂ) x := fun x _ =>
    ((q.hasDerivAt (x + 1/2)).comp_add_const x (1/2)).ofReal_comp
  have hv : ∀ x ∈ Set.uIcc (-(1/2):ℝ) (1/2), HasDerivAt (fun u : ℝ => cexp (((-(t * u) : ℝ) : ℂ) * I) / c)
      (cexp (((-(t * x) : ℝ) : ℂ) * I)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => ((-(t * u) : ℝ) : ℂ) * I) (((-t : ℝ) : ℂ) * I) x := by
      have := (((hasDerivAt_id x).const_mul t).neg).ofReal_comp.mul_const I
      simpa using this
    have h2 := (h1.cexp).div_const c
    convert h2 using 1
    rw [← hc]; field_simp
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)
  unfold Φ
  rw [key]
  have e2 : ∫ x in (-(1/2):ℝ)..(1/2), (((derivative q).eval (x + 1/2) : ℝ) : ℂ) * (cexp (((-(t * x) : ℝ) : ℂ) * I) / c)
      = (∫ x in (-(1/2):ℝ)..(1/2), (((derivative q).eval (x + 1/2) : ℝ) : ℂ) * cexp (((-(t * x) : ℝ) : ℂ) * I)) / c := by
    rw [← intervalIntegral.integral_div]; congr 1; funext x; ring
  rw [e2]
  unfold E
  rw [← hc]
  have : (1:ℂ) / ((t:ℂ) * I) = -1 / c := by
    rw [hc]; push_cast; field_simp
  rw [this]
  norm_num
  ring

/-- iterated derivatives -/
noncomputable def D (q : ℝ[X]) (j : ℕ) : ℝ[X] := derivative^[j] q

lemma ibp_iter (q : ℝ[X]) {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    Φ q t = ∑ j ∈ range n, (1 / ((t : ℂ) * I)) ^ j * E (D q j) t + (1 / ((t : ℂ) * I)) ^ n * Φ (D q n) t := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    rw [ih, sum_range_succ, ibp (D q n) ht]
    have : derivative (D q n) = D q (n + 1) := by
      unfold D; rw [Function.iterate_succ_apply']
    rw [this, pow_succ]; ring

lemma norm_cexp_I (r : ℝ) : ‖cexp ((r : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I r

lemma norm_E (q : ℝ[X]) {t : ℝ} (ht : 0 < t) : ‖E q t‖ ≤ (|q.eval 1| + |q.eval 0|) / t := by
  unfold E
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one, abs_neg, abs_of_pos ht]
  gcongr
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_cexp_I, norm_cexp_I, Complex.norm_real, Complex.norm_real]
  simp

lemma norm_inv_tI {t : ℝ} (ht : 0 < t) : ‖1 / ((t : ℂ) * I)‖ = 1 / t := by
  rw [norm_div, norm_one, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

/-- six integrations by parts when `q, q', q⁽⁴⁾, q⁽⁵⁾` vanish at both ends -/
lemma six_ibp (q : ℝ[X]) {t : ℝ} (ht : 0 < t)
    (h0 : ∀ j ∈ ({0, 1, 4, 5} : Finset ℕ), (D q j).eval 1 = 0 ∧ (D q j).eval 0 = 0) :
    ‖Φ q t‖ ≤ (|(D q 2).eval 1| + |(D q 2).eval 0|) / t ^ 3 + (|(D q 3).eval 1| + |(D q 3).eval 0|) / t ^ 4
      + ‖Φ (D q 6) t‖ / t ^ 6 := by
  rw [ibp_iter q ht.ne' 6]
  have hz : ∀ j ∈ ({0, 1, 4, 5} : Finset ℕ), E (D q j) t = 0 := by
    intro j hj; obtain ⟨a, b⟩ := h0 j hj; unfold E; rw [a, b]; simp
  simp only [sum_range_succ, sum_range_zero, hz 0 (by simp), hz 1 (by simp), hz 4 (by simp), hz 5 (by simp),
    mul_zero, zero_add, add_zero]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_mul, norm_pow, norm_inv_tI ht]
    refine (mul_le_mul_of_nonneg_left (norm_E _ ht) (by positivity)).trans (le_of_eq ?_)
    field_simp
  · rw [norm_mul, norm_pow, norm_inv_tI ht]
    refine (mul_le_mul_of_nonneg_left (norm_E _ ht) (by positivity)).trans (le_of_eq ?_)
    field_simp
  · rw [norm_mul, norm_pow, norm_inv_tI ht]; field_simp; rfl

/-- the Fourier transform of a cut polynomial is `Φ` -/
lemma fourier_cutp (q : ℝ[X]) (t : ℝ) :
    𝓕 (fun u => ((LegSpan.cutp (fun u => q.eval (u + 1/2)) u : ℝ) : ℂ)) (t / (2 * π)) = Φ q t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e : (fun v : ℝ => cexp (((-2 * π * v * (t / (2 * π))) : ℝ) * I) •
      ((LegSpan.cutp (fun u => q.eval (u + 1/2)) v : ℝ) : ℂ))
      = (Set.Icc (-(1/2):ℝ) (1/2)).indicator
          (fun u => ((q.eval (u + 1/2) : ℝ) : ℂ) * cexp (((-(t * u) : ℝ) : ℂ) * I)) := by
    funext v
    unfold LegSpan.cutp Set.indicator
    simp only [Set.mem_Icc, abs_le, smul_eq_mul]
    split_ifs with h1
    · rw [mul_comm]; congr 3; field_simp
    · simp
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  rfl

lemma Φ_eq_hx (q : ℝ[X]) : ∃ N x y, ∀ t,
    Φ q t = (WeilZhuRed.Fx 0 N x t : ℂ) + I * (WeilZhuRed.Fx 1 N y t : ℂ) ∧
    LegSpan.cutp (fun u => q.eval (u + 1/2)) = WeilOdd.hx N x y := by
  obtain ⟨N, x, y, h⟩ := LegSpan.poly_hx (q.comp (X + C (1/2)))
  have ef : (fun u => (q.comp (X + C (1/2))).eval u) = fun u => q.eval (u + 1/2) := by funext u; simp
  rw [ef] at h
  refine ⟨N, x, y, fun t => ⟨?_, ?_⟩⟩
  · have hf := WeilOdd.fourier_hx N x y (t / (2 * π))
    have e1 : 2 * π * (t / (2 * π)) = t := by field_simp
    rw [e1] at hf
    rw [← hf, ← fourier_cutp q t, h]
  · rw [h]

lemma normSq_Φ (q : ℝ[X]) (t : ℝ) {N : ℕ} {x y : ℕ → ℝ}
    (h : Φ q t = (WeilZhuRed.Fx 0 N x t : ℂ) + I * (WeilZhuRed.Fx 1 N y t : ℂ)) :
    ‖Φ q t‖ ^ 2 = WeilZhuRed.Fx 0 N x t ^ 2 + WeilZhuRed.Fx 1 N y t ^ 2 := by
  rw [h, ← Complex.normSq_eq_norm_sq, mul_comm, Complex.normSq_add_mul_I]

lemma int_cutp_sq (q : ℝ[X]) :
    ∫ u, LegSpan.cutp (fun u => q.eval (u + 1/2)) u ^ 2 = ∫ w in (0:ℝ)..1, q.eval w ^ 2 := by
  have e : (fun u => LegSpan.cutp (fun u => q.eval (u + 1/2)) u ^ 2)
      = (Set.Icc (-(1/2):ℝ) (1/2)).indicator (fun u => q.eval (u + 1/2) ^ 2) := by
    funext v; unfold LegSpan.cutp Set.indicator
    simp only [Set.mem_Icc, abs_le]
    split_ifs <;> simp_all
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_comp_add_right (fun w => q.eval w ^ 2)]
  norm_num

/-- Plancherel for a cut polynomial -/
theorem plancherel (q : ℝ[X]) :
    IntegrableOn (fun t => ‖Φ q t‖ ^ 2) (Set.Ioi 0) ∧
    ∫ t in Set.Ioi 0, ‖Φ q t‖ ^ 2 = π * ∫ w in (0:ℝ)..1, q.eval w ^ 2 := by
  obtain ⟨N, x, y, h⟩ := Φ_eq_hx q
  have e : (fun t => ‖Φ q t‖ ^ 2) = fun t => WeilZhuRed.Fx 0 N x t ^ 2 + WeilZhuRed.Fx 1 N y t ^ 2 := by
    funext t; exact normSq_Φ q t (h t).1
  have P0 := WeilPlanch.modePlancherel_of WeilModes.modeDecay 0 (WeilFourier.modeOrth (by norm_num))
  have P1 := WeilPlanch.modePlancherel_of WeilModes.modeDecay 1 (WeilFourier.modeOrth (by norm_num))
  have i0 := (WeilZhuRed.expand_int 0 N x (fun _ => 1) (Set.Ioi 0) (fun i j => by simpa using P0.int1 i j)).1
  have i1 := (WeilZhuRed.expand_int 1 N y (fun _ => 1) (Set.Ioi 0) (fun i j => by simpa using P1.int1 i j)).1
  simp only [one_mul] at i0 i1
  refine ⟨by rw [e]; exact i0.add i1, ?_⟩
  rw [e, integral_add i0 i1]
  have s0 := WeilCoer.sq_mass 0 (by norm_num) N x
  have s1 := WeilCoer.sq_mass 1 (by norm_num) N y
  have hn := WeilCoer.normSq_hx N x y
  rw [← (h 0).2] at hn
  unfold WeilForm.normSq at hn
  rw [int_cutp_sq] at hn
  rw [hn, ← s0, ← s1]
  field_simp

end GsFourier
