import Mathlib
import WeilPlanch

/-! # Legendre modes: Rodrigues integration by parts, the pole identity and the decay of `T̂ₙ`

`sL n` is Mathlib's shifted Legendre polynomial over `ℝ`, `wP n = Xⁿ(1−X)ⁿ`. Mathlib's Rodrigues formula
`n!·sL n = Dⁿ wP n` and the vanishing of `Dʲ wP n` at `0, 1` for `j < n` give, by `n` integrations by parts,
`∫₀¹ e^{cy} sL n(y) dy = ((−c)ⁿ/n!) ∫₀¹ e^{cy} yⁿ(1−y)ⁿ dy` for every complex `c` (`rod_ibp`). Two consequences:
* `pole_bridge`: `∫_{−1/2}^{1/2} T_n(u) e^{−u/2} du = pₙ` for the repo's `legT` and Poisson-defined `iₙ`
  (closes `EvenBridge.pole`);
* `modeDecay`: `|T̂ₙ(t)| ≤ Cₙ/(1+t)` (closes `ModeDecay`).
-/

namespace WeilModes

open Polynomial Real Finset WeilTailB WeilPlanch
open scoped Nat

noncomputable def wP (n : ℕ) : ℝ[X] := X ^ n * (1 - X) ^ n
noncomputable def sL (n : ℕ) : ℝ[X] := (shiftedLegendre n).map (Int.castRingHom ℝ)

lemma rodrigues (n : ℕ) : (n ! : ℝ[X]) * sL n = derivative^[n] (wP n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) (factorial_mul_shiftedLegendre_eq n)
  rw [Polynomial.map_mul, Polynomial.map_natCast, ← Polynomial.iterate_derivative_map] at h
  simpa [sL, wP] using h

lemma rod_eval (n : ℕ) (y : ℝ) : (n ! : ℝ) * (sL n).eval y = (derivative^[n] (wP n)).eval y := by
  rw [← rodrigues]; simp [eval_mul]

lemma vanish (n j : ℕ) (hj : j < n) :
    (derivative^[j] (wP n)).eval 0 = 0 ∧ (derivative^[j] (wP n)).eval 1 = 0 := by
  constructor
  · obtain ⟨q, hq⟩ : (X : ℝ[X]) ^ (n - j) ∣ derivative^[j] (wP n) :=
      pow_sub_dvd_iterate_derivative_of_pow_dvd j (Dvd.intro _ rfl)
    rw [hq, eval_mul, eval_pow, eval_X, zero_pow (by omega), zero_mul]
  · obtain ⟨q, hq⟩ : ((1 : ℝ[X]) - X) ^ (n - j) ∣ derivative^[j] (wP n) :=
      pow_sub_dvd_iterate_derivative_of_pow_dvd j (Dvd.intro_left _ rfl)
    rw [hq, eval_mul, eval_pow, eval_sub, eval_one, eval_X, sub_self, zero_pow (by omega), zero_mul]

lemma hasDeriv_cexp (c : ℂ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * y)) (c * Complex.exp (c * y)) y := by
  have := (((hasDerivAt_id (y : ℂ)).const_mul c).cexp).comp_ofReal
  convert this using 1
  all_goals try rfl
  show c * Complex.exp (c * (y:ℂ)) = Complex.exp (c * (y:ℂ)) * (c * 1); ring

lemma cont_eval (p : ℝ[X]) : Continuous fun y : ℝ => ((p.eval y : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp p.continuous

/-- One integration by parts with vanishing boundary terms. -/
lemma ibp_zero (c : ℂ) (p : ℝ[X]) (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 0) :
    ∫ y in (0:ℝ)..1, Complex.exp (c * y) * (((derivative p).eval y : ℝ) : ℂ)
      = -c * ∫ y in (0:ℝ)..1, Complex.exp (c * y) * ((p.eval y : ℝ) : ℂ) := by
  have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun y : ℝ => Complex.exp (c * y)) (u' := fun y : ℝ => c * Complex.exp (c * y))
    (v := fun y : ℝ => ((p.eval y : ℝ) : ℂ)) (v' := fun y : ℝ => (((derivative p).eval y : ℝ) : ℂ))
    (fun y _ => hasDeriv_cexp c y) (fun y _ => (p.hasDerivAt y).ofReal_comp)
    ((continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable _ _)
    ((cont_eval _).intervalIntegrable _ _)
  rw [this, h0, h1]
  simp only [Complex.ofReal_zero, mul_zero, sub_zero, zero_sub]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  congr 1; funext y; ring

lemma ibp_iter (c : ℂ) (n : ℕ) : ∀ k, k ≤ n →
    ∫ y in (0:ℝ)..1, Complex.exp (c * y) * (((derivative^[n] (wP n)).eval y : ℝ) : ℂ)
      = (-c) ^ k * ∫ y in (0:ℝ)..1, Complex.exp (c * y) * (((derivative^[n - k] (wP n)).eval y : ℝ) : ℂ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega)]
    have e : n - k = (n - (k + 1)) + 1 := by omega
    rw [e, Function.iterate_succ_apply', ibp_zero c _ (vanish n _ (by omega)).1 (vanish n _ (by omega)).2]
    ring

/-- **Rodrigues integration by parts**: `∫₀¹ e^{cy} P̃ₙ = ((−c)ⁿ/n!) ∫₀¹ e^{cy} yⁿ(1−y)ⁿ`. -/
theorem rod_ibp (c : ℂ) (n : ℕ) :
    (n ! : ℂ) * ∫ y in (0:ℝ)..1, Complex.exp (c * y) * (((sL n).eval y : ℝ) : ℂ)
      = (-c) ^ n * ∫ y in (0:ℝ)..1, Complex.exp (c * y) * (((wP n).eval y : ℝ) : ℂ) := by
  have h := ibp_iter c n n le_rfl
  rw [Nat.sub_self, Function.iterate_zero, id] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  congr 1; funext y
  rw [← rod_eval]; push_cast; ring

/-! ## Real form and the substitution facts -/

lemma wP_eval (n : ℕ) (y : ℝ) : (wP n).eval y = y ^ n * (1 - y) ^ n := by simp [wP]

/-- Real Rodrigues identity. -/
theorem rod_ibp_real (c : ℝ) (n : ℕ) :
    (n ! : ℝ) * ∫ y in (0:ℝ)..1, Real.exp (c * y) * (sL n).eval y
      = (-c) ^ n * ∫ y in (0:ℝ)..1, Real.exp (c * y) * (wP n).eval y := by
  have h := rod_ibp (c : ℂ) n
  have e1 : ∫ y in (0:ℝ)..1, Complex.exp ((c:ℂ) * y) * (((sL n).eval y : ℝ) : ℂ)
      = ((∫ y in (0:ℝ)..1, Real.exp (c * y) * (sL n).eval y : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; congr 1; funext y; push_cast; ring
  have e2 : ∫ y in (0:ℝ)..1, Complex.exp ((c:ℂ) * y) * (((wP n).eval y : ℝ) : ℂ)
      = ((∫ y in (0:ℝ)..1, Real.exp (c * y) * (wP n).eval y : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; congr 1; funext y; push_cast; ring
  rw [e1, e2] at h
  exact_mod_cast h

lemma sub_m11 (f : ℝ → ℝ) : ∫ s in (-1:ℝ)..1, f s = 2 * ∫ y in (0:ℝ)..1, f (2 * y - 1) := by
  rw [intervalIntegral.integral_comp_mul_sub (f := f) (by norm_num : (2:ℝ) ≠ 0) 1]
  norm_num; ring

lemma one_sub_sq (y : ℝ) (n : ℕ) : (1 - (2 * y - 1) ^ 2) ^ n = 4 ^ n * (wP n).eval y := by
  rw [wP_eval, ← mul_pow, ← mul_pow]; congr 1; ring

lemma aeval_eq (n : ℕ) (y : ℝ) : Polynomial.aeval y (shiftedLegendre n) = (sL n).eval y := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; rfl

/-! ## The pole identity -/

theorem pole_mode (n : ℕ) :
    ∫ u in (-(1/2):ℝ)..(1/2), (Real.sqrt (2 * n + 1) * (sL n).eval (u + 1 / 2)) * Real.exp (-(u / 2)) = pole n := by
  set J := ∫ y in (0:ℝ)..1, Real.exp (-(1/2) * y) * (wP n).eval y
  set I := ∫ y in (0:ℝ)..1, Real.exp (-(1/2) * y) * (sL n).eval y
  have hIJ : (n ! : ℝ) * I = (1/2) ^ n * J := by
    have := rod_ibp_real (-(1/2)) n; rw [neg_neg] at this; exact this
  -- left side
  have hL : ∫ u in (-(1/2):ℝ)..(1/2), (Real.sqrt (2 * n + 1) * (sL n).eval (u + 1 / 2)) * Real.exp (-(u / 2))
      = Real.sqrt (2 * n + 1) * Real.exp (1 / 4) * I := by
    have e : ∀ u : ℝ, (Real.sqrt (2 * n + 1) * (sL n).eval (u + 1 / 2)) * Real.exp (-(u / 2))
        = (fun y => Real.sqrt (2 * n + 1) * Real.exp (1 / 4) * (Real.exp (-(1/2) * y) * (sL n).eval y)) (u + 1 / 2) := by
      intro u; simp only
      rw [mul_assoc (Real.sqrt _), mul_assoc (Real.sqrt _), ← mul_assoc (Real.exp (1/4)), ← Real.exp_add]
      rw [show (1:ℝ) / 4 + -(1 / 2) * (u + 1 / 2) = -(u / 2) by ring]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_comp_add_right (fun y => Real.sqrt (2 * n + 1) * Real.exp (1 / 4) * (Real.exp (-(1/2) * y) * (sL n).eval y)) (1/2)]
    norm_num [intervalIntegral.integral_const_mul, I]
  -- right side
  have hcosh : ∫ y in (0:ℝ)..1, Real.cosh (1 / 4 * (2 * y - 1)) * (wP n).eval y = Real.exp (1 / 4) * J := by
    have hc : Continuous fun y : ℝ => (wP n).eval y := (wP n).continuous
    have hsym : ∫ y in (0:ℝ)..1, Real.exp (1 / 4 * (2 * y - 1)) * (wP n).eval y
        = ∫ y in (0:ℝ)..1, Real.exp (-(1 / 4 * (2 * y - 1))) * (wP n).eval y := by
      have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
        (fun y : ℝ => Real.exp (1 / 4 * (2 * y - 1)) * (wP n).eval y) 1
      simp only [sub_zero, sub_self] at this
      rw [← this]; congr 1; funext y; simp only [wP_eval]
      rw [show 1 / 4 * (2 * (1 - y) - 1) = -(1 / 4 * (2 * y - 1)) by ring]; ring
    have e : ∀ y : ℝ, Real.cosh (1 / 4 * (2 * y - 1)) * (wP n).eval y
        = (Real.exp (1 / 4 * (2 * y - 1)) * (wP n).eval y + Real.exp (-(1 / 4 * (2 * y - 1))) * (wP n).eval y) / 2 := by
      intro y; rw [Real.cosh_eq]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop), hsym]
    have : ∫ y in (0:ℝ)..1, Real.exp (-(1 / 4 * (2 * y - 1))) * (wP n).eval y = Real.exp (1 / 4) * J := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext y
      rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [this]; ring
  have hR : pole n = Real.sqrt (2 * n + 1) * ((1 / 4) ^ n / (2 ^ (n + 1) * n !) * (2 * (4 ^ n * (Real.exp (1 / 4) * J)))) := by
    unfold pole iP
    rw [sub_m11]
    have e : ∀ y : ℝ, Real.cosh (1 / 4 * (2 * y - 1)) * (1 - (2 * y - 1) ^ 2) ^ n
        = 4 ^ n * (Real.cosh (1 / 4 * (2 * y - 1)) * (wP n).eval y) := by
      intro y; rw [one_sub_sq]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, hcosh]
    have hs : 2 * Real.sqrt (1 / 2 * ((n:ℝ) + 1 / 2)) = Real.sqrt (2 * n + 1) := by
      rw [show (1 / 2 * ((n:ℝ) + 1 / 2)) = (2 * n + 1) / 4 by ring, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
        show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      ring
    rw [← hs]
  rw [hL, hR]
  have hf : (n ! : ℝ) ≠ 0 := by positivity
  have hI : I = (1/2) ^ n * J / n ! := by field_simp; linarith [hIJ]
  rw [hI]
  rw [div_pow, one_pow, div_pow (1:ℝ) 4, one_pow]
  field_simp
  ring

/-- **`EvenBridge.pole` closed.** -/
theorem pole_bridge (N : ℕ) (x : ℕ → ℝ) :
    WeilForm.poleR (fx N x) (1 / 2) = ∑ i ∈ range N, x i * pole (2 * i + 0) := by
  unfold WeilForm.poleR
  have e : ∫ u in (-(1/2):ℝ)..(1/2), fx N x u * Real.exp (-(u / 2))
      = ∫ u in (-(1/2):ℝ)..(1/2), ∑ i ∈ range N, x i *
          ((Real.sqrt (2 * ((2 * i : ℕ) : ℝ) + 1) * (sL (2 * i)).eval (u + 1 / 2)) * Real.exp (-(u / 2))) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hu' : |u| ≤ 1 / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
    simp only [fx, legT, ite_eq_left hu', aeval_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [e, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_const_mul, pole_mode]; rfl
  · intro i _
    apply Continuous.intervalIntegrable
    have := (sL (2 * i)).continuous
    fun_prop

/-! ## Decay of `T̂ₙ` -/

lemma norm_cexp_rI (r y : ℝ) : ‖Complex.exp (((r:ℂ) * Complex.I) * (y:ℂ))‖ = 1 := by
  rw [show ((r:ℂ) * Complex.I) * (y:ℂ) = ((r * y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma cexp_cont (c : ℂ) : Continuous fun y : ℝ => Complex.exp (c * y) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- One integration by parts: `‖∫₀¹ e^{iry} p(y) dy‖ ≤ (|p(1)| + |p(0)| + M)/|r|`. -/
lemma ibp_bound (p : ℝ[X]) (r : ℝ) (hr : r ≠ 0) {M : ℝ}
    (hM : ∀ y ∈ Set.Icc (0:ℝ) 1, |(derivative p).eval y| ≤ M) :
    ‖∫ y in (0:ℝ)..1, Complex.exp (((r:ℂ) * Complex.I) * y) * ((p.eval y : ℝ) : ℂ)‖
      ≤ (|p.eval 1| + |p.eval 0| + M) / |r| := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun y : ℝ => Complex.exp (((r:ℂ) * Complex.I) * y))
    (u' := fun y : ℝ => ((r:ℂ) * Complex.I) * Complex.exp (((r:ℂ) * Complex.I) * y))
    (v := fun y : ℝ => ((p.eval y : ℝ) : ℂ)) (v' := fun y : ℝ => (((derivative p).eval y : ℝ) : ℂ))
    (fun y _ => hasDeriv_cexp _ y) (fun y _ => (p.hasDerivAt y).ofReal_comp)
    ((continuous_const.mul (cexp_cont _)).intervalIntegrable _ _) ((cont_eval _).intervalIntegrable _ _)
  have hcI : ∫ y in (0:ℝ)..1, ((r:ℂ) * Complex.I) * Complex.exp (((r:ℂ) * Complex.I) * y) * ((p.eval y : ℝ) : ℂ)
      = ((r:ℂ) * Complex.I) * ∫ y in (0:ℝ)..1, Complex.exp (((r:ℂ) * Complex.I) * y) * ((p.eval y : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext y; ring
  rw [hcI] at h
  have hB : ‖∫ y in (0:ℝ)..1, Complex.exp (((r:ℂ) * Complex.I) * y) * (((derivative p).eval y : ℝ) : ℂ)‖ ≤ M := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := M)
      (f := fun y : ℝ => Complex.exp (((r:ℂ) * Complex.I) * y) * (((derivative p).eval y : ℝ) : ℂ)) (fun y hy => by
        rw [Set.uIoc_of_le (by norm_num)] at hy
        rw [norm_mul, norm_cexp_rI, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact hM y ⟨hy.1.le, hy.2⟩)
    simpa using this
  have h1 : ‖Complex.exp (((r:ℂ) * Complex.I) * ((1:ℝ):ℂ)) * ((p.eval 1 : ℝ) : ℂ)‖ = |p.eval 1| := by
    rw [norm_mul, norm_cexp_rI, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have h0 : ‖Complex.exp (((r:ℂ) * Complex.I) * ((0:ℝ):ℂ)) * ((p.eval 0 : ℝ) : ℂ)‖ = |p.eval 0| := by
    rw [norm_mul, norm_cexp_rI, one_mul, Complex.norm_real, Real.norm_eq_abs]
  set A := ∫ y in (0:ℝ)..1, Complex.exp (((r:ℂ) * Complex.I) * y) * ((p.eval y : ℝ) : ℂ)
  set Bd := ∫ y in (0:ℝ)..1, Complex.exp (((r:ℂ) * Complex.I) * y) * (((derivative p).eval y : ℝ) : ℂ)
  have hA : ((r:ℂ) * Complex.I) * A = Complex.exp (((r:ℂ) * Complex.I) * ((1:ℝ):ℂ)) * ((p.eval 1 : ℝ) : ℂ)
      - Complex.exp (((r:ℂ) * Complex.I) * ((0:ℝ):ℂ)) * ((p.eval 0 : ℝ) : ℂ) - Bd := by
    rw [h]; ring
  have hc : ‖(r:ℂ) * Complex.I‖ = |r| := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hn : |r| * ‖A‖ ≤ |p.eval 1| + |p.eval 0| + M := by
    rw [← hc, ← norm_mul, hA]
    have a1 := norm_sub_le (Complex.exp (((r:ℂ) * Complex.I) * ((1:ℝ):ℂ)) * ((p.eval 1 : ℝ) : ℂ)
      - Complex.exp (((r:ℂ) * Complex.I) * ((0:ℝ):ℂ)) * ((p.eval 0 : ℝ) : ℂ)) Bd
    have a2 := norm_sub_le (Complex.exp (((r:ℂ) * Complex.I) * ((1:ℝ):ℂ)) * ((p.eval 1 : ℝ) : ℂ))
      (Complex.exp (((r:ℂ) * Complex.I) * ((0:ℝ):ℂ)) * ((p.eval 0 : ℝ) : ℂ))
    rw [h1, h0] at a2
    linarith
  rw [le_div_iff₀ (abs_pos.mpr hr)]; linarith [mul_comm ‖A‖ |r|]

noncomputable def E (n : ℕ) (c : ℂ) : ℂ := ∫ y in (0:ℝ)..1, Complex.exp (c * y) * (((wP n).eval y : ℝ) : ℂ)

lemma cos_split (n : ℕ) (x : ℝ) :
    ((∫ y in (0:ℝ)..1, Real.cos (x * (2 * y - 1)) * (wP n).eval y : ℝ) : ℂ)
      = (Complex.exp (-((x:ℂ) * Complex.I)) * E n (((2 * x : ℝ) : ℂ) * Complex.I)
        + Complex.exp ((x:ℂ) * Complex.I) * E n (((-(2 * x) : ℝ) : ℂ) * Complex.I)) / 2 := by
  rw [← intervalIntegral.integral_ofReal]
  unfold E
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add, ← intervalIntegral.integral_div]
  · congr 1; funext y
    have e1 : Complex.exp (-((x:ℂ) * Complex.I)) * Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I * y)
        = Complex.exp (((x * (2 * y - 1) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp ((x:ℂ) * Complex.I) * Complex.exp (((-(2 * x) : ℝ) : ℂ) * Complex.I * y)
        = Complex.exp (-(((x * (2 * y - 1) : ℝ) : ℂ)) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hc := Complex.two_cos (((x * (2 * y - 1) : ℝ) : ℂ))
    rw [Complex.ofReal_mul, Complex.ofReal_cos]
    rw [← mul_assoc, ← mul_assoc, e1, e2]
    linear_combination (((((wP n).eval y : ℝ) : ℂ)) / 2) * hc
  · exact ((continuous_const.mul ((cexp_cont _).mul (cont_eval _)))).intervalIntegrable _ _
  · exact ((continuous_const.mul ((cexp_cont _).mul (cont_eval _)))).intervalIntegrable _ _

/-- `‖E n (irs)‖ ≤ n! K / |r|^{n+1}` from Rodrigues plus one integration by parts. -/
lemma E_bound (n : ℕ) {K M : ℝ} (hM : ∀ y ∈ Set.Icc (0:ℝ) 1, |(derivative (sL n)).eval y| ≤ M)
    (hK : K = |(sL n).eval 1| + |(sL n).eval 0| + M) (r : ℝ) (hr : r ≠ 0) :
    ‖E n ((r:ℂ) * Complex.I)‖ ≤ n ! * (K / |r|) / |r| ^ n := by
  have h := rod_ibp ((r:ℂ) * Complex.I) n
  have hb := ibp_bound (sL n) r hr hM
  rw [← hK] at hb
  have hcn : ‖(-((r:ℂ) * Complex.I)) ^ n‖ = |r| ^ n := by
    rw [norm_pow, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < |r| ^ n := pow_pos (abs_pos.mpr hr) n
  unfold E
  rw [le_div_iff₀ hpos, ← hcn, ← norm_mul, mul_comm, ← h, norm_mul]
  have : ‖((n ! : ℕ) : ℂ)‖ = n ! := by rw [Complex.norm_natCast]
  rw [this]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- **`|jₙ(x)| ≤ K/(2x)`** for `x > 0`. -/
lemma jP_decay (n : ℕ) {K M : ℝ} (hM : ∀ y ∈ Set.Icc (0:ℝ) 1, |(derivative (sL n)).eval y| ≤ M)
    (hK : K = |(sL n).eval 1| + |(sL n).eval 0| + M) {x : ℝ} (hx : 0 < x) : |jP n x| ≤ K / (2 * x) := by
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
    rw [hK]; positivity
  have h2x : (2 * x) ≠ 0 := by positivity
  have b1 := E_bound n hM hK (2 * x) h2x
  have b2 := E_bound n hM hK (-(2 * x)) (neg_ne_zero.mpr h2x)
  rw [abs_neg] at b2
  rw [abs_of_pos (by positivity : 0 < 2 * x)] at b1 b2
  have hcos : |∫ y in (0:ℝ)..1, Real.cos (x * (2 * y - 1)) * (wP n).eval y| ≤ n ! * (K / (2 * x)) / (2 * x) ^ n := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, cos_split]
    rw [norm_div, Complex.norm_ofNat]
    refine div_le_of_le_mul₀ (by norm_num) (by positivity) ?_
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, show -((x:ℂ) * Complex.I) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, one_mul, one_mul]
    linarith
  unfold jP
  rw [sub_m11]
  have e : ∀ y : ℝ, Real.cos (x * (2 * y - 1)) * (1 - (2 * y - 1) ^ 2) ^ n
      = 4 ^ n * (Real.cos (x * (2 * y - 1)) * (wP n).eval y) := by
    intro y; rw [one_sub_sq]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]
  set Ic := ∫ y in (0:ℝ)..1, Real.cos (x * (2 * y - 1)) * (wP n).eval y
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ n / (2 ^ (n + 1) * n !)),
    abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_mul, abs_of_pos (by positivity : (0:ℝ) < 4 ^ n)]
  calc x ^ n / (2 ^ (n + 1) * n !) * (2 * (4 ^ n * |Ic|))
      ≤ x ^ n / (2 ^ (n + 1) * n !) * (2 * (4 ^ n * (n ! * (K / (2 * x)) / (2 * x) ^ n))) := by gcongr
    _ = K / (2 * x) := by
      rw [mul_pow, pow_succ, show (4:ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
      field_simp

/-- **`ModeDecay` closed**: `|T̂ₙ(t)| ≤ Cₙ/(1+t)` for `t ≥ 0`. -/
theorem modeDecay : ModeDecay := by
  intro n
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((derivative (sL n)).continuous.continuousOn)
  have hM' : ∀ y ∈ Set.Icc (0:ℝ) 1, |(derivative (sL n)).eval y| ≤ M := fun y hy => by
    have := hM y hy; rwa [Real.norm_eq_abs] at this
  set K := |(sL n).eval 1| + |(sL n).eval 0| + M with hK
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0 ⟨le_rfl, zero_le_one⟩)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set K' := max 1 K
  have hK'1 : 1 ≤ K' := le_max_left _ _
  have hKK : K ≤ K' := le_max_right _ _
  set S := 2 * Real.sqrt ((1 / 2) * (n + 1 / 2))
  have hS : 0 ≤ S := by positivity
  refine ⟨S * (3 * K'), by positivity, fun t ht => ?_⟩
  have hj : |jP n (t / 2)| ≤ 3 * K' / (1 + t) := by
    rcases le_or_gt (t / 2) 1 with h1 | h1
    · have hb := jP_bound n (by linarith : (0:ℝ) ≤ t / 2)
      have : (t / 2 / 2) ^ n / n ! ≤ 1 := by
        rw [div_le_one (by positivity)]
        calc (t / 2 / 2) ^ n ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
          _ ≤ n ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    · have hb := jP_decay n hM' hK (by linarith : (0:ℝ) < t / 2)
      refine hb.trans ?_
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
  unfold That
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul, abs_of_nonneg hS]
  calc S * |jP n (t / 2)| ≤ S * (3 * K' / (1 + t)) := mul_le_mul_of_nonneg_left hj hS
    _ = S * (3 * K') / (1 + t) := by ring

/-! ## Rewired final theorems -/

/-- Remaining even-sector bridge inputs after `pole_bridge`: `arch` (Zhu analytic, Lemma 2.5) and `acorr`
(Fourier, Wiener–Khinchin at `log 2`). -/
structure EvenBridge2 : Prop where
  arch : ∀ N x, ((Complex.digamma (1 / 4)).re - Real.log π) * WeilForm.normSq (fx N x)
      + (∫ u in Set.Ioi (0:ℝ), WeilForm.archIntegrand (fx N x) u)
      = (1 / π) * ∫ t in Set.Ioi 0, ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π) * WeilZhuRed.Fx 0 N x t ^ 2
  acorr : ∀ N x, WeilForm.autocorr (fx N x) (Real.log 2)
      = (1 / π) * ∫ t in Set.Ioi 0, Real.cos (t * Real.log 2) * WeilZhuRed.Fx 0 N x t ^ 2

theorem bridge_of (B : EvenBridge2) : EvenBridge := ⟨pole_bridge, B.arch, B.acorr⟩

/-- **Even sector, final.** `0 < weilQ (1/2) (Σ_{i<N} xᵢ T_{2i})` for `N ≥ 28`, `x ≠ 0`.
Inputs: `EvenHead` (arb numerics), `ModeOrth 0` (functional analysis), `EvenBridge2` (arch: Zhu analytic;
acorr: Fourier). `ModeDecay` and the pole identity are proved. -/
theorem L05_even_final (O : ModeOrth 0) (B : EvenBridge2) (H : EvenHead) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < WeilForm.weilQ (1 / 2) (fx N x) :=
  L05_even_weilQ modeDecay O (bridge_of B) H N hN x hx

/-- **Odd sector, final** (frequency form). Inputs: `OddHead`, `ModeOrth 1`. -/
theorem L05_odd_final (O : ModeOrth 1) (H : OddHead) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < WeilZhuRed.QF 1 (-1) N x :=
  L05_odd_QF modeDecay O H N hN x hx

end WeilModes
