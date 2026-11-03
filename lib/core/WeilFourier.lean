import Mathlib
import WeilModes

/-! # Fourier bridge: Legendre orthonormality, the Legendre–Fourier identity and Parseval -/

namespace WeilFourier

open Polynomial Real Finset WeilTailB WeilPlanch WeilModes MeasureTheory
open scoped Nat

/-! ## Beta integral and Legendre orthonormality -/

theorem beta_nat (b : ℕ) : ∀ a : ℕ,
    ∫ y in (0:ℝ)..1, y ^ a * (1 - y) ^ b = (a ! * b ! : ℝ) / (a + b + 1)! := by
  induction b with
  | zero =>
    intro a
    simp only [pow_zero, mul_one, integral_pow, one_pow, Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [Nat.factorial_succ]; push_cast
    rw [zero_pow (by omega)]; field_simp; norm_num
  | succ b ih =>
    intro a
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
      (u := fun y : ℝ => (1 - y) ^ (b + 1)) (u' := fun y : ℝ => -((b + 1 : ℝ) * (1 - y) ^ b))
      (v := fun y : ℝ => y ^ (a + 1) / (a + 1)) (v' := fun y : ℝ => y ^ a)
      (fun y _ => by
        have := ((hasDerivAt_id y).const_sub 1).pow (b + 1)
        convert this using 1
        · funext z; simp
        · simp)
      (fun y _ => by
        have := (hasDerivAt_pow (a + 1) y).div_const ((a:ℝ) + 1)
        convert this using 1; push_cast; field_simp)
      (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)
    simp only [sub_self, zero_pow (Nat.succ_ne_zero b), zero_mul, ne_eq, Nat.add_one_ne_zero,
      not_false_eq_true, zero_pow, zero_div, mul_zero, sub_zero, zero_sub] at h
    have e1 : ∫ y in (0:ℝ)..1, (1 - y) ^ (b + 1) * y ^ a = ∫ y in (0:ℝ)..1, y ^ a * (1 - y) ^ (b + 1) := by
      congr 1; funext y; ring
    have e2 : ∫ y in (0:ℝ)..1, -((b + 1 : ℝ) * (1 - y) ^ b) * (y ^ (a + 1) / (a + 1))
        = -((b + 1) / (a + 1) * ∫ y in (0:ℝ)..1, y ^ (a + 1) * (1 - y) ^ b) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]; congr 1; funext y; ring
    rw [e1, e2, ih (a + 1)] at h
    rw [h, show a + 1 + b + 1 = a + (b + 1) + 1 by ring]
    rw [Nat.factorial_succ a, Nat.factorial_succ b]; push_cast; field_simp

/-- Real integration by parts with vanishing boundary terms, polynomial weights. -/
lemma ibp_poly (r p : ℝ[X]) (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 0) :
    ∫ y in (0:ℝ)..1, r.eval y * (derivative p).eval y = -∫ y in (0:ℝ)..1, (derivative r).eval y * p.eval y := by
  have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun y => r.eval y) (u' := fun y => (derivative r).eval y)
    (v := fun y => p.eval y) (v' := fun y => (derivative p).eval y)
    (fun y _ => r.hasDerivAt y) (fun y _ => p.hasDerivAt y)
    ((derivative r).continuous.intervalIntegrable _ _) ((derivative p).continuous.intervalIntegrable _ _)
  rw [this, h0, h1]; simp

lemma ibp_poly_iter (r : ℝ[X]) (n : ℕ) : ∀ k, k ≤ n →
    ∫ y in (0:ℝ)..1, r.eval y * (derivative^[n] (wP n)).eval y
      = (-1) ^ k * ∫ y in (0:ℝ)..1, (derivative^[k] r).eval y * (derivative^[n - k] (wP n)).eval y := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega)]
    have e : n - k = (n - (k + 1)) + 1 := by omega
    rw [e, Function.iterate_succ_apply', ibp_poly _ _ (vanish n _ (by omega)).1 (vanish n _ (by omega)).2,
      Function.iterate_succ_apply']
    ring

lemma natDeg_sL (n : ℕ) : (sL n).natDegree ≤ n := by
  unfold sL; exact (natDegree_map_le).trans (by simp)

lemma iter_sL_self (n : ℕ) : derivative^[n] (sL n) = C ((n ! : ℝ) * ((-1) ^ n * ((2 * n).choose n))) := by
  have hd : (derivative^[n] (sL n)).natDegree = 0 := by
    have := natDegree_iterate_derivative (sL n) n
    have := natDeg_sL n; omega
  rw [eq_C_of_natDegree_eq_zero hd, coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  congr 1
  unfold sL; rw [coeff_map, coeff_shiftedLegendre]; simp [two_mul]

/-- `∫₀¹ P̃ₘ P̃ₙ = δₘₙ/(2n+1)`. -/
theorem sL_orth (m n : ℕ) :
    ∫ y in (0:ℝ)..1, (sL m).eval y * (sL n).eval y = if m = n then (1:ℝ) / (2 * n + 1) else 0 := by
  have key : ∀ m n, m ≤ n → (n ! : ℝ) * ∫ y in (0:ℝ)..1, (sL m).eval y * (sL n).eval y
      = (-1) ^ n * ∫ y in (0:ℝ)..1, (derivative^[n] (sL m)).eval y * (wP n).eval y := by
    intro m n _
    rw [← intervalIntegral.integral_const_mul]
    have := ibp_poly_iter (sL m) n n le_rfl
    rw [Nat.sub_self, Function.iterate_zero, id] at this
    rw [← this]; congr 1; funext y; rw [← rod_eval]; ring
  have hf : ∀ n, (n ! : ℝ) ≠ 0 := fun n => by positivity
  rcases lt_trichotomy m n with h | h | h
  · rw [if_neg h.ne]
    have := key m n h.le
    rw [iterate_derivative_eq_zero ((natDeg_sL m).trans_lt h)] at this
    simp only [eval_zero, zero_mul, intervalIntegral.integral_zero, mul_zero] at this
    exact_mod_cast (mul_eq_zero.mp this).resolve_left (hf n)
  · subst h; rw [if_pos rfl]
    have := key m m le_rfl
    rw [iter_sL_self] at this
    simp only [eval_C] at this
    rw [intervalIntegral.integral_const_mul] at this
    have hb : ∫ y in (0:ℝ)..1, (wP m).eval y = (m ! * m ! : ℝ) / (m + m + 1)! := by
      rw [← beta_nat]; congr 1; funext y; rw [wP_eval]
    rw [hb] at this
    have hc : ((2 * m).choose m : ℝ) = (2 * m)! / (m ! * m !) := by
      have := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
      rw [show 2 * m - m = m by omega] at this
      have h' : ((2 * m).choose m : ℝ) * m ! * m ! = (2 * m)! := by exact_mod_cast this
      have := hf m
      field_simp; linarith
    rw [hc, show m + m + 1 = 2 * m + 1 by ring, Nat.factorial_succ] at this
    have hm := hf m
    have h2 : ((2 * m)! : ℝ) ≠ 0 := by positivity
    have hp : ((-1:ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    apply mul_left_cancel₀ hm
    rw [this]; push_cast; field_simp
    exact hp
  · rw [if_neg h.ne']
    have := key n m h.le
    rw [iterate_derivative_eq_zero ((natDeg_sL n).trans_lt h)] at this
    simp only [eval_zero, zero_mul, intervalIntegral.integral_zero, mul_zero] at this
    have := (mul_eq_zero.mp this).resolve_left (hf m)
    have e : ∫ y in (0:ℝ)..1, (sL m).eval y * (sL n).eval y = ∫ y in (0:ℝ)..1, (sL n).eval y * (sL m).eval y := by
      congr 1; funext y; ring
    rw [e, this]

/-! ## Cut-off functions and their correlations -/

def I0 : Set ℝ := Set.Icc (-(1/2)) (1/2)

noncomputable def cut (p : ℝ → ℝ) : ℝ → ℝ := I0.indicator p

noncomputable def P (n : ℕ) (u : ℝ) : ℝ := Real.sqrt (2 * n + 1) * (sL n).eval (u + 1 / 2)

lemma P_cont (n : ℕ) : Continuous (P n) := by unfold P; have := (sL n).continuous; fun_prop

lemma legT_eq (n : ℕ) : legT n = cut (P n) := by
  funext u
  unfold legT cut P I0
  by_cases h : |u| ≤ 1 / 2
  · rw [if_pos h, Set.indicator_of_mem (by rw [Set.mem_Icc]; exact abs_le.mp h), aeval_eq]
  · rw [if_neg h, Set.indicator_of_notMem (by rw [Set.mem_Icc]; intro h'; exact h (abs_le.mpr h'))]

lemma cut_mul (p q : ℝ → ℝ) (w : ℝ) :
    (fun t => cut p t * cut q (t - w))
      = (Set.Icc (max (-(1/2)) (w - 1/2)) (min (1/2) (w + 1/2))).indicator (fun t => p t * q (t - w)) := by
  funext t
  have hiff : t ∈ Set.Icc (max (-(1/2)) (w - 1/2)) (min (1/2) (w + 1/2)) ↔ t ∈ I0 ∧ t - w ∈ I0 := by
    simp only [I0, Set.mem_Icc, max_le_iff, le_min_iff]
    constructor <;> intro h <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
  by_cases hA : t ∈ I0 ∧ t - w ∈ I0
  · rw [Set.indicator_of_mem (hiff.mpr hA)]; simp only [cut, Set.indicator_of_mem hA.1, Set.indicator_of_mem hA.2]
  · rw [Set.indicator_of_notMem (fun h => hA (hiff.mp h))]
    simp only [cut]
    by_cases h1 : t ∈ I0
    · rw [Set.indicator_of_notMem (fun h => hA ⟨h1, h⟩), mul_zero]
    · rw [Set.indicator_of_notMem h1, zero_mul]

lemma corr_eq (p q : ℝ → ℝ) {w : ℝ} (hw : |w| ≤ 1) :
    ∫ t, cut p t * cut q (t - w)
      = ∫ t in (max (-(1/2)) (w - 1/2))..(min (1/2) (w + 1/2)), p t * q (t - w) := by
  have hab : max (-(1/2)) (w - 1/2) ≤ min (1/2) (w + 1/2) := by
    obtain ⟨h1, h2⟩ := abs_le.mp hw
    simp only [max_le_iff, le_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  rw [cut_mul, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

lemma corr_contAt_lt (p q : ℝ → ℝ) (hp : Continuous p) (hq : Continuous q) {v : ℝ} (hv : |v| < 1) :
    ContinuousAt (fun w => ∫ t, cut p t * cut q (t - w)) v := by
  set F : ℝ → ℝ → ℝ := fun w t => p t * q (t - w)
  have hF : Continuous F.uncurry := by
    show Continuous fun z : ℝ × ℝ => p z.2 * q (z.2 - z.1); fun_prop
  have hb := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume) (a₀ := 0) hF
    (s := fun w => min (1/2) (w + 1/2)) (by fun_prop)
  have ha := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume) (a₀ := 0) hF
    (s := fun w => max (-(1/2)) (w - 1/2)) (by fun_prop)
  refine ((hb.sub ha).continuousAt).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hv] with w hw
  try simp only [Set.mem_setOf_eq] at hw
  rw [corr_eq p q hw.le]
  have hc : Continuous (F w) := by show Continuous fun t => p t * q (t - w); fun_prop
  exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm

lemma corr_zero (p q : ℝ → ℝ) {w : ℝ} (hw : 1 < |w|) : ∫ t, cut p t * cut q (t - w) = 0 := by
  rw [cut_mul, Set.Icc_eq_empty, Set.indicator_empty, integral_zero]
  intro h
  simp only [max_le_iff, le_min_iff] at h
  rcases lt_abs.mp hw with h' | h' <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]

lemma corr_contAt (p q : ℝ → ℝ) (hp : Continuous p) (hq : Continuous q) {v : ℝ} (hv : |v| ≠ 1) :
    ContinuousAt (fun w => ∫ t, cut p t * cut q (t - w)) v := by
  rcases lt_or_gt_of_ne hv with h | h
  · exact corr_contAt_lt p q hp hq h
  · refine (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds h] with w hw
    exact corr_zero p q hw

/-- **Legendre orthonormality on `[−1/2, 1/2]`** for the repo's `legT`. -/
theorem legT_orth (n m : ℕ) : ∫ t, legT n t * legT m t = if n = m then 1 else 0 := by
  have h := corr_eq (P n) (P m) (w := 0) (by norm_num)
  simp only [sub_zero, legT_eq] at h ⊢
  rw [h]
  norm_num
  have e : ∀ t : ℝ, P n t * P m t
      = (fun y => Real.sqrt (2 * n + 1) * Real.sqrt (2 * m + 1) * ((sL n).eval y * (sL m).eval y)) (t + 1/2) := by
    intro t; simp only [P]; ring
  simp_rw [e]
  have hs := intervalIntegral.integral_comp_add_right (a := -(1/2)) (b := 1/2)
    (fun y => Real.sqrt (2 * n + 1) * Real.sqrt (2 * m + 1) * ((sL n).eval y * (sL m).eval y)) (1/2)
  try simp only at hs
  rw [hs]; norm_num
  rw [sL_orth]
  split_ifs with hnm
  · subst hnm
    rw [Real.mul_self_sqrt (by positivity)]; field_simp
  · simp

/-! ## Parseval for cut-off functions via Mathlib's Fourier inversion -/

open FourierTransform in
lemma cutC_int (p : ℝ → ℝ) (hp : Continuous p) : Integrable (fun t => ((cut p t : ℝ) : ℂ)) := by
  have : Integrable (cut p) := (hp.integrableOn_Icc).integrable_indicator measurableSet_Icc
  exact this.ofReal

open FourierTransform in
/-- **Parseval / Wiener–Khinchin for cut-off functions.** If `𝓕f(ξ)·𝓕g(−ξ) = S(2πξ)` with `S` continuous,
even and `O(1/(1+t)²)`, then `∫ f(t) g(t−v) dt = (1/π)∫₀^∞ cos(tv) S(t) dt` for `|v| ≠ 1`. -/
theorem parseval (p q : ℝ → ℝ) (hp : Continuous p) (hq : Continuous q) (S : ℝ → ℝ) (hSc : Continuous S)
    (hSe : ∀ t, S (-t) = S t) (K : ℝ) (hK : ∀ t, 0 ≤ t → |S t| ≤ K / (1 + t) ^ 2)
    (hS : ∀ ξ : ℝ, 𝓕 (fun t => ((cut p t : ℝ) : ℂ)) ξ * 𝓕 (fun t => ((cut q t : ℝ) : ℂ)) (-ξ) = (S (2 * π * ξ) : ℂ))
    {v : ℝ} (hv : |v| ≠ 1) :
    ∫ t, cut p t * cut q (t - v) = (1 / π) * ∫ t in Set.Ioi 0, Real.cos (t * v) * S t := by
  set f₁ : ℝ → ℂ := fun t => ((cut p t : ℝ) : ℂ)
  set g : ℝ → ℂ := fun t => ((cut q t : ℝ) : ℂ)
  set f₂ : ℝ → ℂ := fun t => g (-t)
  have hf₁ : Integrable f₁ := cutC_int p hp
  have hg : Integrable g := cutC_int q hq
  have hf₂ : Integrable f₂ := hg.comp_neg
  set h := convolution f₁ f₂ (ContinuousLinearMap.mul ℂ ℂ) volume
  have hconv : ∀ w, h w = ((∫ t, cut p t * cut q (t - w) : ℝ) : ℂ) := by
    intro w
    show MeasureTheory.convolution f₁ f₂ (ContinuousLinearMap.mul ℂ ℂ) volume w = _
    rw [convolution_def]
    have e := integral_ofReal (𝕜 := ℂ) (f := fun t => cut p t * cut q (t - w)) (μ := volume)
    refine Eq.trans ?_ e
    congr 1; funext t
    simp [f₁, f₂, g, neg_sub]
  have hF : ∀ ξ, 𝓕 h ξ = (S (2 * π * ξ) : ℂ) := by
    intro ξ
    rw [Real.fourier_mul_convolution_eq hf₁ hf₂ ξ, ← hS ξ]
    congr 1
    show 𝓕 (fun t => g (-t)) ξ = 𝓕 g (-ξ)
    rw [← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_neg]
  have hK0 : 0 ≤ K := by have := hK 0 le_rfl; norm_num at this; exact (abs_nonneg _).trans this
  have hSb : ∀ ξ : ℝ, |S (2 * π * ξ)| ≤ K * (1 + ‖ξ‖) ^ (-(2:ℝ)) := by
    intro ξ
    have habs : S (2 * π * ξ) = S |2 * π * ξ| := by
      rcases abs_choice (2 * π * ξ) with e | e <;> rw [e]; rw [hSe]
    rw [habs, Real.rpow_neg (by positivity), Real.rpow_two, Real.norm_eq_abs, ← div_eq_mul_inv]
    refine (hK _ (abs_nonneg _)).trans ?_
    have : |ξ| ≤ |2 * π * ξ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
      nlinarith [abs_nonneg ξ, Real.pi_gt_three]
    gcongr
  have hSint : Integrable (fun ξ : ℝ => S (2 * π * ξ)) := by
    refine ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul K).mono'
      (hSc.comp (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards with ξ; rw [Real.norm_eq_abs]; exact hSb ξ
  have hint : Integrable (𝓕 h) := by
    rw [show 𝓕 h = fun ξ => (S (2 * π * ξ) : ℂ) from funext hF]; exact hSint.ofReal
  have hh : Integrable h := hf₁.integrable_convolution _ hf₂
  have hcont : ContinuousAt h v := by
    rw [show h = fun w => ((∫ t, cut p t * cut q (t - w) : ℝ) : ℂ) from funext hconv]
    exact Complex.continuous_ofReal.continuousAt.comp (corr_contAt p q hp hq hv)
  have hinv := hh.fourierInv_fourier_eq hint hcont
  rw [hconv, Real.fourierInv_eq'] at hinv
  simp_rw [hF, Real.inner_apply] at hinv
  have hre := congrArg Complex.re hinv
  rw [Complex.ofReal_re] at hre
  rw [← hre]
  have hI : Integrable (fun ξ : ℝ => Complex.exp (↑(2 * π * (ξ * v)) * Complex.I) • (S (2 * π * ξ) : ℂ)) := by
    have hc1 : Continuous fun ξ : ℝ => Complex.exp (↑(2 * π * (ξ * v)) * Complex.I) := by fun_prop
    have hc2 : Continuous fun ξ : ℝ => ((S (2 * π * ξ) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hSc.comp (by fun_prop))
    refine (show Integrable (fun ξ : ℝ => ((S (2 * π * ξ) : ℝ) : ℂ)) from hSint.ofReal).norm.mono'
      (hc1.smul hc2).aestronglyMeasurable ?_
    filter_upwards with ξ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  rw [← RCLike.re_to_complex, ← integral_re hI]
  have e1 : ∀ ξ : ℝ, RCLike.re (Complex.exp (↑(2 * π * (ξ * v)) * Complex.I) • (S (2 * π * ξ) : ℂ))
      = (fun t => Real.cos (t * v) * S t) (2 * π * ξ) := by
    intro ξ
    simp only [smul_eq_mul, RCLike.re_to_complex, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
    congr 2; ring
  simp_rw [e1]
  rw [Measure.integral_comp_mul_left (fun t => Real.cos (t * v) * S t) (2 * π)]
  have e2 : ∫ t, Real.cos (t * v) * S t = ∫ t, (fun t => Real.cos (t * v) * S t) |t| := by
    congr 1; funext t
    rcases abs_choice t with e | e <;> rw [e]
    simp [hSe, Real.cos_neg, neg_mul]
  rw [e2, integral_comp_abs (f := fun t => Real.cos (t * v) * S t), smul_eq_mul, abs_inv, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  field_simp
  congr 1; funext t; ring

/-! ## The Legendre–Fourier identity -/

lemma E_sym (n : ℕ) (c : ℂ) : E n c = Complex.exp c * E n (-c) := by
  unfold E
  have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
    (fun y : ℝ => Complex.exp (c * y) * (((wP n).eval y : ℝ) : ℂ)) 1
  simp only [sub_zero, sub_self] at this
  rw [← this, ← intervalIntegral.integral_const_mul]
  congr 1; funext y
  simp only [wP_eval]
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast; ring_nf

lemma jP_Ic (n : ℕ) (x : ℝ) :
    jP n x = x ^ n / (2 ^ (n + 1) * n !) * (2 * (4 ^ n * ∫ y in (0:ℝ)..1, Real.cos (x * (2 * y - 1)) * (wP n).eval y)) := by
  unfold jP
  rw [sub_m11]
  have e : ∀ y : ℝ, Real.cos (x * (2 * y - 1)) * (1 - (2 * y - 1) ^ 2) ^ n
      = 4 ^ n * (Real.cos (x * (2 * y - 1)) * (wP n).eval y) := by
    intro y; rw [one_sub_sq]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]

lemma Ic_E (n : ℕ) (x : ℝ) :
    ((∫ y in (0:ℝ)..1, Real.cos (x * (2 * y - 1)) * (wP n).eval y : ℝ) : ℂ)
      = Complex.exp ((x:ℂ) * Complex.I) * E n (((-(2 * x) : ℝ) : ℂ) * Complex.I) := by
  rw [cos_split, E_sym n (((2 * x : ℝ) : ℂ) * Complex.I)]
  have e1 : -(((2 * x : ℝ) : ℂ) * Complex.I) = ((-(2 * x) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have e2 : Complex.exp (-((x:ℂ) * Complex.I)) * Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((x:ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1, ← mul_assoc, e2]; ring

lemma legC_int (n : ℕ) : Integrable (fun t => ((legT n t : ℝ) : ℂ)) := by
  rw [legT_eq]; exact cutC_int _ (P_cont n)

open FourierTransform in
/-- **Legendre–Fourier identity** (Mathlib normalisation `𝓕f(ξ) = ∫ e^{−2πivξ} f(v) dv`):
`𝓕 T_n (ξ) = iⁿ √(2n+1) jₙ(πξ)`. -/
theorem LF (n : ℕ) (ξ : ℝ) :
    𝓕 (fun t => ((legT n t : ℝ) : ℂ)) ξ
      = Complex.I ^ n * ((Real.sqrt (2 * n + 1) * jP n (π * ξ) : ℝ) : ℂ) := by
  set x := π * ξ
  set c : ℂ := ((-(2 * x) : ℝ) : ℂ) * Complex.I
  rw [Real.fourier_real_eq_integral_exp_smul]
  -- restrict to the support
  have hind : (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • ((legT n v : ℝ) : ℂ))
      = I0.indicator (fun v => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) * ((P n v : ℝ) : ℂ)) := by
    funext v
    rw [legT_eq]; unfold cut
    by_cases hv : v ∈ I0
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, smul_eq_mul]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]; simp
  rw [hind]; unfold I0
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have hsh : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) * ((P n v : ℝ) : ℂ)
      = (fun y : ℝ => Complex.exp ((x:ℂ) * Complex.I) * (Real.sqrt (2 * n + 1) : ℂ)
          * (Complex.exp (c * y) * (((sL n).eval y : ℝ) : ℂ))) (v + 1 / 2) := by
    intro v
    simp only [P, c, x]
    rw [show Complex.exp (↑(-2 * π * v * ξ) * Complex.I)
        = Complex.exp (↑(π * ξ) * Complex.I) * Complex.exp (↑(-(2 * (π * ξ))) * Complex.I * ↑(v + 1 / 2)) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    push_cast; ring
  simp_rw [hsh]
  have hs := intervalIntegral.integral_comp_add_right (a := -(1/2)) (b := 1/2)
    (fun y : ℝ => Complex.exp ((x:ℂ) * Complex.I) * (Real.sqrt (2 * n + 1) : ℂ)
          * (Complex.exp (c * y) * (((sL n).eval y : ℝ) : ℂ))) (1/2)
  rw [hs]; norm_num
  have hr := rod_ibp c n
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hI : ∫ y in (0:ℝ)..1, Complex.exp (c * y) * (((sL n).eval y : ℝ) : ℂ) = (-c) ^ n * E n c / n ! := by
    rw [eq_div_iff hf, mul_comm]; exact hr
  rw [hI, jP_Ic]
  push_cast
  rw [Ic_E]
  have hc : -c = ((2 * x : ℝ) : ℂ) * Complex.I := by simp only [c]; push_cast; ring
  rw [hc]
  simp only [c]
  push_cast
  rw [show (4:ℂ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
  field_simp
  ring

/-! ## Sector form, parity and decay -/

lemma jP_neg (n : ℕ) (x : ℝ) : jP n (-x) = (-1) ^ n * jP n x := by
  unfold jP
  have : ∀ t : ℝ, Real.cos (-x * t) * (1 - t ^ 2) ^ n = Real.cos (x * t) * (1 - t ^ 2) ^ n := by
    intro t; rw [neg_mul, Real.cos_neg]
  simp_rw [this]; rw [neg_pow]; ring

lemma That_neg (n : ℕ) (t : ℝ) : That n (-t) = (-1) ^ n * That n t := by
  unfold That; rw [neg_div, jP_neg]; ring

lemma That_jP (n : ℕ) (ξ : ℝ) :
    That n (2 * π * ξ) = (-1) ^ (n / 2) * (Real.sqrt (2 * n + 1) * jP n (π * ξ)) := by
  unfold That
  have hs : 2 * Real.sqrt (1 / 2 * ((n:ℝ) + 1 / 2)) = Real.sqrt (2 * n + 1) := by
    rw [show (1 / 2 * ((n:ℝ) + 1 / 2)) = (2 * n + 1) / 4 by ring, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring
  rw [hs, show 2 * π * ξ / 2 = π * ξ by ring]

open FourierTransform in
/-- Sector form of the Legendre–Fourier identity: `𝓕 T_{2i+par}(ξ) = i^par · T̂_{2i+par}(2πξ)`. -/
theorem LF_sec {par : ℕ} (hp : par < 2) (i : ℕ) (ξ : ℝ) :
    𝓕 (fun t => ((legT (2 * i + par) t : ℝ) : ℂ)) ξ = Complex.I ^ par * (That (2 * i + par) (2 * π * ξ) : ℂ) := by
  rw [LF, That_jP, show (2 * i + par) / 2 = i by omega, pow_add, pow_mul, Complex.I_sq]
  push_cast; ring

lemma decay_sum (par N : ℕ) (x : ℕ → ℝ) : ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |WeilZhuRed.Fx par N x t| ≤ C / (1 + t) := by
  induction N with
  | zero => exact ⟨0, le_rfl, fun t _ => by simp [WeilZhuRed.Fx]⟩
  | succ N ih =>
    obtain ⟨C, hC, h⟩ := ih
    obtain ⟨D, hD, hd⟩ := modeDecay (2 * N + par)
    refine ⟨C + |x N| * D, by positivity, fun t ht => ?_⟩
    have h1 : 0 < 1 + t := by linarith
    unfold WeilZhuRed.Fx at h ⊢
    rw [Finset.sum_range_succ]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, add_div, mul_div_assoc]
    exact add_le_add (h t ht) (mul_le_mul_of_nonneg_left (hd t ht) (abs_nonneg _))

/-! ## Closing `ModeOrth` (both parities) -/

open FourierTransform in
/-- **`ModeOrth par` closed** for `par ∈ {0, 1}`: Legendre orthonormality + Legendre–Fourier identity +
Mathlib Fourier inversion (`parseval`). -/
theorem modeOrth {par : ℕ} (hp : par < 2) : ModeOrth par := by
  intro i j
  have hI : Complex.I ^ par * Complex.I ^ par * (-1) ^ par = 1 := by
    interval_cases par <;> simp [Complex.I_sq]
  set a := 2 * i + par
  set b := 2 * j + par
  obtain ⟨C1, hC1, h1⟩ := modeDecay a
  obtain ⟨C2, hC2, h2⟩ := modeDecay b
  have hpar : ((-1:ℝ) ^ a * (-1) ^ b) = 1 := by
    rw [← pow_add, show a + b = 2 * (i + j + par) by omega, pow_mul]; norm_num
  have key := parseval (P a) (P b) (P_cont a) (P_cont b) (WeilZhuRed.G par i j)
    ((That_cont _).mul (That_cont _))
    (fun t => by
      show That a (-t) * That b (-t) = That a t * That b t
      rw [That_neg, That_neg]; linear_combination (That a t * That b t) * hpar)
    (C1 * C2) (fun t ht => by
      show |That a t * That b t| ≤ C1 * C2 / (1 + t) ^ 2
      rw [abs_mul, pow_two, mul_div_mul_comm]
      exact mul_le_mul (h1 t ht) (h2 t ht) (abs_nonneg _) (div_nonneg hC1 (by linarith)))
    (fun ξ => by
      rw [← legT_eq, ← legT_eq, LF_sec hp i ξ, LF_sec hp j (-ξ), show 2 * π * -ξ = -(2 * π * ξ) by ring, That_neg]
      show _ = ((That a (2 * π * ξ) * That b (2 * π * ξ) : ℝ) : ℂ)
      have hb : ((-1:ℂ) ^ b) = (-1) ^ par := by
        rw [show b = 2 * j + par from rfl, pow_add, pow_mul]; norm_num
      push_cast
      rw [hb]
      linear_combination ((That a (2 * π * ξ) : ℂ) * (That b (2 * π * ξ) : ℂ)) * hI)
    (v := 0) (by norm_num)
  simp only [sub_zero, mul_zero, Real.cos_zero, one_mul, ← legT_eq] at key
  rw [← key, legT_orth]
  simp only [a, b]
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ## Closing `EvenBridge2.acorr` -/

noncomputable def Qx (N : ℕ) (x : ℕ → ℝ) (u : ℝ) : ℝ := ∑ i ∈ range N, x i * P (2 * i) u

lemma fx_eq (N : ℕ) (x : ℕ → ℝ) : fx N x = cut (Qx N x) := by
  funext u
  unfold fx Qx
  simp_rw [legT_eq]
  unfold cut
  by_cases hu : u ∈ I0
  · simp only [Set.indicator_of_mem hu]
  · simp only [Set.indicator_of_notMem hu, mul_zero, Finset.sum_const_zero]

open FourierTransform in
lemma fourier_fx (N : ℕ) (x : ℕ → ℝ) (ξ : ℝ) :
    𝓕 (fun t => ((cut (Qx N x) t : ℝ) : ℂ)) ξ = (WeilZhuRed.Fx 0 N x (2 * π * ξ) : ℂ) := by
  rw [← fx_eq]
  have e : (fun t => ((fx N x t : ℝ) : ℂ)) = fun t => ∑ i ∈ range N, (x i : ℂ) * ((legT (2 * i) t : ℝ) : ℂ) := by
    funext t; unfold fx; push_cast; rfl
  rw [e, Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [integral_finset_sum]
  · rw [WeilZhuRed.Fx, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h := LF_sec (par := 0) (by norm_num) i ξ
    simp only [add_zero, pow_zero, one_mul] at h
    rw [add_zero, Complex.ofReal_mul, ← h, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1; funext v; simp only [smul_eq_mul]; ring
  · intro i _
    have hl := (legC_int (2 * i)).const_mul (x i : ℂ)
    refine hl.norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul hl.aestronglyMeasurable) ?_
    filter_upwards with v
    simp only [Pi.mul_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- **Wiener–Khinchin** for `fx`: `h(v) = (1/π)∫₀^∞ cos(tv) F(t)² dt` for `|v| ≠ 1`. -/
theorem acorr_gen (N : ℕ) (x : ℕ → ℝ) {v : ℝ} (hv : |v| ≠ 1) : WeilForm.autocorr (fx N x) v
    = (1 / π) * ∫ t in Set.Ioi 0, Real.cos (t * v) * WeilZhuRed.Fx 0 N x t ^ 2 := by
  obtain ⟨C, hC, hd⟩ := decay_sum 0 N x
  have hev : ∀ t, WeilZhuRed.Fx 0 N x (-t) = WeilZhuRed.Fx 0 N x t := by
    intro t; unfold WeilZhuRed.Fx
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [That_neg, pow_add, pow_mul]; norm_num
  have hc : Continuous (WeilZhuRed.Fx 0 N x) := by
    unfold WeilZhuRed.Fx
    exact continuous_finset_sum _ (fun i _ => continuous_const.mul (That_cont _))
  have hl : |(-v)| ≠ 1 := by rw [abs_neg]; exact hv
  have hQ : Continuous (Qx N x) := by
    unfold Qx; exact continuous_finset_sum _ (fun i _ => continuous_const.mul (P_cont _))
  have key := parseval (Qx N x) (Qx N x) hQ hQ (fun t => WeilZhuRed.Fx 0 N x t ^ 2) (hc.pow 2)
    (fun t => by simp only [hev]) (C ^ 2) (fun t ht => by
      have h1 : 0 < 1 + t := by linarith
      rw [abs_pow, ← div_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hd t ht) 2)
    (fun ξ => by
      rw [fourier_fx, fourier_fx, show 2 * π * -ξ = -(2 * π * ξ) by ring, hev]; push_cast; ring)
    hl
  unfold WeilForm.autocorr
  rw [fx_eq]
  simp only [sub_neg_eq_add, mul_neg, Real.cos_neg] at key
  exact key

/-- **`EvenBridge2.acorr` closed** (Wiener–Khinchin at `log 2`). -/
theorem acorr (N : ℕ) (x : ℕ → ℝ) : WeilForm.autocorr (fx N x) (Real.log 2)
    = (1 / π) * ∫ t in Set.Ioi 0, Real.cos (t * Real.log 2) * WeilZhuRed.Fx 0 N x t ^ 2 :=
  acorr_gen N x (by
    rw [abs_of_pos (Real.log_pos one_lt_two)]; exact ne_of_lt (by linarith [Real.log_two_lt_d9]))

/-! ## Rewired final theorems -/

/-- **Remaining named input (Zhu analytic, Lemma 2.5)**: the archimedean term in frequency form. -/
def ArchBridge : Prop := ∀ N x, ((Complex.digamma (1 / 4)).re - Real.log π) * WeilForm.normSq (fx N x)
      + (∫ u in Set.Ioi (0:ℝ), WeilForm.archIntegrand (fx N x) u)
      = (1 / π) * ∫ t in Set.Ioi 0, ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π)
          * WeilZhuRed.Fx 0 N x t ^ 2

/-- **Even sector.** `0 < weilQ (1/2) (Σ_{i<N} xᵢ T_{2i})` for `N ≥ 28`, `x ≠ 0`.
Inputs: `EvenHead` (arb numerics) and `ArchBridge` (Zhu Lemma 2.5). `ModeOrth`, `acorr`, `pole`, `ModeDecay`
are proved. -/
theorem L05_even (A : ArchBridge) (H : EvenHead) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < WeilForm.weilQ (1 / 2) (fx N x) :=
  L05_even_final (modeOrth (by norm_num)) ⟨A, acorr⟩ H N hN x hx

/-- **Odd sector** (frequency form). Only input: `OddHead` (arb numerics). -/
theorem L05_odd (H : OddHead) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < WeilZhuRed.QF 1 (-1) N x :=
  L05_odd_final (modeOrth (by norm_num)) H N hN x hx

end WeilFourier
