import BallSilent

/-!
# The inverse theorem on the arithmetic class, first half: a vector that does not carry `ζ` is loud (RH)

The vectors that make the orbit form small are, numerically, of one kind: `n·x_n = Σ_{d ∣ n, d ≤ D₀} E_d(n/N)` with
fixed profiles `E_d` on `[0, 1]` (formalisations/ball-rate.md, "The inverse theorem on the arithmetic class"). For
such a vector put `G = Σ_d E_d/d`, the boundary function, and `Ĝ(s) = ∫_0^1 G(u)u^{s−1}du`. At a zero `ρ`,

`V_x(ρ) = Σ_{n ≤ N} x_n n^ρ = N^ρ·Ĝ(ρ) + O(1)`,

so that under RH, where `Q_N(x) = Σ_ρ |V_x(ρ)|²/(¼ + γ²)`, one zero with `Ĝ(ρ) ≠ 0` makes `Q_N(x) ≥ c·N`: the vector
is loud, against the `log N/N` of the quiet ones. So a vector of the class that is quiet has `Ĝ(ρ) = 0` at every
zero: it carries the zeros of `ζ`.

This is part 1 of Theorem A of that section, for profiles that are bounded and Lipschitz and vanish beyond `1`. The
`O(1)` is elementary: the sum `Σ_{m ≤ X} φ(m/X)m^{s−1}` is a Riemann sum of `X^s∫_0^1 φ(u)u^{s−1}du`, whose integrand
has an integrable singularity at `0`, and the two differ by a bounded amount (`sum_profile_sub_le`). No property of
`ζ` enters it; the zeros enter through `BallRate.hasSum_form`. Part 2 of the theorem, the asymptotic
`Q_N(x) ~ Λ(E)·log N/N` for the quiet vectors, is not formalised: it needs the approximate functional equation at
the zeros and a mean value over them.

* `Profile φ B K`: `|φ| ≤ B`, `φ` is `K`-Lipschitz, and `φ = 0` on `[1, ∞)`.
* `mellin01 G s`: `∫_0^1 G(u)u^{s−1}du`.
* `sum_profile_sub_le`: `|Σ_{m ≤ X} φ(m/X)m^{s−1} − X^s·φ̂(s)| ≤ 2B + K + 3B|s − 1|` on `Re s = ½`.
* `classVec D₀ E N`, `bdry D₀ E`: the vector and its boundary function.
* `norm_dpoly_classVec_ge`: `|V_x(ρ)| ≥ √N·|Ĝ(ρ)| − D₀(2B + K + 3B|ρ − 1|)` at a zero, under RH.
* `loud`: if `Ĝ(ρ) ≠ 0` at a zero, then `Q_N(x) ≥ (|Ĝ(ρ)|²/(4(¼ + γ²)))·N` for every large `N`.
* `carries_zeta`: if `Q_N(x) ≤ C(1 + log N)` for every `N`, then `Ĝ` vanishes at every zero.
* `quiet_carries_zeta`: the same from `Q_N(x) ≤ C·((1 + log N)/N)·Σx_n²`, the quiet vectors.
-/

open Complex Finset MeasureTheory

noncomputable section

namespace BallLoud

open BallRate BallWeil WeilForm WeilTest

/-! ## Two elementary sums -/

/-- `x^{-3/2} = 1/((√x)²·√x)`. -/
lemma rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 / 2 : ℝ)) = 1 / (Real.sqrt x ^ 2 * Real.sqrt x) := by
  have h : Real.sqrt x ^ 2 * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
    rw [Real.sq_sqrt hx.le, Real.sqrt_eq_rpow]
    nth_rewrite 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    norm_num
  rw [h, Real.rpow_neg hx.le, one_div]

/-- The telescoping step: `1/(a²·a) ≤ 2/b − 2/a` when `a² = b² + 1`. -/
lemma step_aux {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) (h : a ^ 2 = b ^ 2 + 1) :
    1 / (a ^ 2 * a) ≤ 2 / b - 2 / a := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have h1 : (a - b) * (a + b) = 1 := by nlinarith
  have h2 : a * b * (a + b) ≤ 2 * a ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 hab), mul_pos ha hb, ha.le]
  have key : a * b ≤ 2 * a ^ 3 * (a - b) := by
    calc a * b = a * b * (a + b) * (a - b) := by
          rw [mul_assoc (a * b), mul_comm (a + b), h1, mul_one]
      _ ≤ 2 * a ^ 3 * (a - b) := mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 hab)
  have e : 2 / b - 2 / a = 2 * (a - b) / (a * b) := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have e2 : 2 * (a - b) * (a ^ 2 * a) = 2 * a ^ 3 * (a - b) := by ring
  rw [e2, one_mul]
  exact key

/-- `Σ_{k < M} (k + 1)^{-3/2} ≤ 3`. -/
lemma sum_rpow_neg_three_halves_le (M : ℕ) :
    ∑ k ∈ range M, ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 3 := by
  have key : ∀ M : ℕ, ∑ k ∈ range (M + 1), ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      3 - 2 / Real.sqrt ((M + 1 : ℕ) : ℝ) := by
    intro M
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have hb0 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
      have ha0 : (0 : ℝ) < ((M + 1 + 1 : ℕ) : ℝ) := by positivity
      have hstep : ((M + 1 + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤
          2 / Real.sqrt ((M + 1 : ℕ) : ℝ) - 2 / Real.sqrt ((M + 1 + 1 : ℕ) : ℝ) := by
        rw [rpow_neg_three_halves ha0]
        refine step_aux (Real.sqrt_pos.2 hb0) (Real.sqrt_le_sqrt (by push_cast; linarith)) ?_
        rw [Real.sq_sqrt ha0.le, Real.sq_sqrt hb0.le]
        push_cast
        ring
      linarith
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have h := key M'
    have h0 : (0 : ℝ) ≤ 2 / Real.sqrt ((M' + 1 : ℕ) : ℝ) := by positivity
    linarith

/-- A sum over `1 ≤ m ≤ M` is a sum over `k < M` at `m = k + 1`. -/
lemma sum_Icc_one_eq_sum_range (M : ℕ) (f : ℕ → ℂ) :
    ∑ m ∈ Icc 1 M, f m = ∑ k ∈ range M, f (k + 1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- The multiples of `d` up to `N` are the `d·m` with `m ≤ N/d`. -/
lemma sum_Icc_dvd {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ Icc 1 N, (if d ∣ n then f n else 0) = ∑ m ∈ Icc 1 (N / d), f (d * m) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun n => n / d) (fun m => d * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn1, k, rfl⟩ := Finset.mem_filter.1 hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn1
    rw [Nat.mul_div_cancel_left k hd]
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h1
      · exact hk
    · rw [Nat.le_div_iff_mul_le hd, mul_comm]
      exact h2
  · intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hm
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, dvd_mul_right d m⟩
    · exact Nat.mul_pos hd h1
    · rw [Nat.le_div_iff_mul_le hd, mul_comm] at h2
      exact h2
  · intro n hn
    obtain ⟨-, hdvd⟩ := Finset.mem_filter.1 hn
    exact Nat.mul_div_cancel' hdvd
  · intro m _
    exact Nat.mul_div_cancel_left m hd
  · intro n hn
    obtain ⟨-, hdvd⟩ := Finset.mem_filter.1 hn
    show f n = f (d * (n / d))
    rw [Nat.mul_div_cancel' hdvd]

/-! ## Profiles and their Riemann sums -/

/-- A profile: a bounded Lipschitz function on the line that vanishes beyond `1`. -/
structure Profile (φ : ℝ → ℝ) (B K : ℝ) : Prop where
  /-- `|φ| ≤ B`. -/
  bound : ∀ u, |φ u| ≤ B
  /-- `φ` is `K`-Lipschitz. -/
  lip : ∀ u v, |φ u - φ v| ≤ K * |u - v|
  /-- `φ` vanishes on `[1, ∞)`. -/
  zero : ∀ u, 1 ≤ u → φ u = 0

namespace Profile

variable {φ : ℝ → ℝ} {B K : ℝ}

lemma B_nonneg (h : Profile φ B K) : 0 ≤ B := (abs_nonneg _).trans (h.bound 0)

lemma K_nonneg (h : Profile φ B K) : 0 ≤ K := by
  have h1 := h.lip 1 0
  rw [sub_zero, abs_one, mul_one] at h1
  exact (abs_nonneg _).trans h1

lemma continuous (h : Profile φ B K) : Continuous φ := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨K, h.K_nonneg⟩) fun u v => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  exact h.lip u v

end Profile

/-- The Mellin transform on `[0, 1]`: `Ĝ(s) = ∫_0^1 G(u)u^{s−1}du`. -/
def mellin01 (G : ℝ → ℝ) (s : ℂ) : ℂ := ∫ u in (0 : ℝ)..1, (G u : ℂ) * (u : ℂ) ^ (s - 1)

/-- The integrand of `mellin01` is integrable, for a continuous `G` and `Re s = ½`. -/
lemma intervalIntegrable_mellin {G : ℝ → ℝ} (hG : Continuous G) {s : ℂ} (hs : s.re = 1 / 2) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => (G u : ℂ) * (u : ℂ) ^ (s - 1)) volume a b := by
  have hre : -1 < (s - 1).re := by
    rw [Complex.sub_re, hs, Complex.one_re]
    norm_num
  exact (intervalIntegral.intervalIntegrable_cpow' hre).continuousOn_mul
    (Complex.continuous_ofReal.comp hG).continuousOn

/-- **A Riemann sum with an integrable singularity**: for a profile `φ`, `Re s = ½` and `X > 0`, the sum
`Σ_{m ≤ X} φ(m/X)m^{s−1}` is within `2B + K + 3B|s − 1|` of `X^s∫_0^1 φ(u)u^{s−1}du`. -/
theorem sum_profile_sub_le {φ : ℝ → ℝ} {B K : ℝ} (h : Profile φ B K) {s : ℂ} (hs : s.re = 1 / 2)
    {X : ℝ} (hX : 0 < X) :
    ‖∑ k ∈ range ⌊X⌋₊, (φ (((k + 1 : ℕ) : ℝ) / X) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) ^ (s - 1) -
        (X : ℂ) ^ s * mellin01 φ s‖ ≤ 2 * B + K + 3 * B * ‖s - 1‖ := by
  set M := ⌊X⌋₊ with hM
  have hMX : (M : ℝ) ≤ X := Nat.floor_le hX.le
  have hXM : X < ((M + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one X
    push_cast
    exact this
  have hB := h.B_nonneg
  have hK := h.K_nonneg
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hre : (s - 1).re = -(1 / 2) := by
    rw [Complex.sub_re, hs, Complex.one_re]
    norm_num
  have hre2 : (s - 1 - 1).re = -(3 / 2) := by
    rw [Complex.sub_re, hre, Complex.one_re]
    norm_num
  have hs1 : s - 1 ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hre
    norm_num at hre
  have hcφ : Continuous fun t : ℝ => φ (t / X) := h.continuous.comp (continuous_id.div_const X)
  -- the integrand, in the variable `t = Xu`
  set F : ℝ → ℂ := fun t => (φ (t / X) : ℂ) * (t : ℂ) ^ (s - 1) with hF
  have hint : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b =>
    intervalIntegrable_mellin hcφ hs a b
  have hzero : ∀ t, X ≤ t → F t = 0 := by
    intro t ht
    have h0 : φ (t / X) = 0 := h.zero _ (by rw [le_div_iff₀ hX]; linarith)
    simp only [hF, h0, Complex.ofReal_zero, zero_mul]
  -- the integral over `[0, M + 1]` is `X^s·φ̂(s)`
  have hmain : ∫ t in (0 : ℝ)..((M + 1 : ℕ) : ℝ), F t = (X : ℂ) ^ s * mellin01 φ s := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 X) (hint X _)]
    have h2 : ∫ t in X..((M + 1 : ℕ) : ℝ), F t = 0 := by
      have hc : ∫ t in X..((M + 1 : ℕ) : ℝ), F t = ∫ _t in X..((M + 1 : ℕ) : ℝ), (0 : ℂ) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hXM.le] at ht
        exact hzero t ht.1
      rw [hc, intervalIntegral.integral_zero]
    rw [h2, add_zero]
    have h3 := intervalIntegral.integral_comp_div (a := 0) (b := X)
      (fun u : ℝ => (φ u : ℂ) * (u : ℂ) ^ (s - 1)) hX.ne'
    rw [zero_div, div_self hX.ne'] at h3
    have h4 : ∫ t in (0 : ℝ)..X, F t =
        (X : ℂ) ^ (s - 1) * ∫ t in (0 : ℝ)..X, (φ (t / X) : ℂ) * ((t / X : ℝ) : ℂ) ^ (s - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hX.le] at ht
      have e : (t : ℂ) = ((X : ℝ) : ℂ) * ((t / X : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, mul_div_cancel₀ t hX.ne']
      show (φ (t / X) : ℂ) * (t : ℂ) ^ (s - 1) =
        (X : ℂ) ^ (s - 1) * ((φ (t / X) : ℂ) * ((t / X : ℝ) : ℂ) ^ (s - 1))
      nth_rewrite 1 [e]
      rw [Complex.mul_cpow_ofReal_nonneg hX.le (div_nonneg ht.1 hX.le)]
      ring
    rw [h4, h3, Complex.real_smul, mellin01, ← mul_assoc]
    congr 1
    rw [Complex.cpow_sub _ _ hX0, Complex.cpow_one, div_mul_cancel₀ _ hX0]
  -- the integral, cut at the integers
  have hsplit : ∫ t in (0 : ℝ)..((M + 1 : ℕ) : ℝ), F t =
      (∑ k ∈ range M, ∫ t in ((k + 1 : ℕ) : ℝ)..((k + 1 + 1 : ℕ) : ℝ), F t) + ∫ t in (0 : ℝ)..1, F t := by
    have h5 := intervalIntegral.sum_integral_adjacent_intervals (f := F) (μ := volume)
      (a := fun k : ℕ => (k : ℝ)) (n := M + 1) (fun k _ => hint _ _)
    rw [Finset.sum_range_succ'] at h5
    simp only [Nat.cast_zero, zero_add, Nat.cast_one] at h5
    exact h5.symm
  -- the singular piece
  have h01 : ‖∫ t in (0 : ℝ)..1, F t‖ ≤ 2 * B := by
    have hg : IntervalIntegrable (fun t : ℝ => B * t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul B
    refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall fun t ht => ?_) hg).trans ?_
    · show ‖(φ (t / X) : ℂ) * (t : ℂ) ^ (s - 1)‖ ≤ B * t ^ (-(1 / 2 : ℝ))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, hre]
      exact mul_le_mul_of_nonneg_right (h.bound _) (Real.rpow_nonneg ht.1.le _)
    · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
      have e0 : (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
      have e3 : ((1 : ℝ) - 0) / (-(1 / 2) + 1) = 2 := by norm_num
      rw [e0, Real.one_rpow, e3]
      linarith
  -- each other piece
  have hpiece : ∀ k ∈ range M,
      ‖(φ (((k + 1 : ℕ) : ℝ) / X) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) ^ (s - 1) -
          ∫ t in ((k + 1 : ℕ) : ℝ)..((k + 1 + 1 : ℕ) : ℝ), F t‖ ≤
        K / X + B * ‖s - 1‖ * ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro k _
    set m : ℝ := ((k + 1 : ℕ) : ℝ) with hm
    have hm1 : (1 : ℝ) ≤ m := by
      rw [hm]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hm0 : (0 : ℝ) < m := by linarith
    have hm' : ((k + 1 + 1 : ℕ) : ℝ) = m + 1 := by
      rw [hm]
      push_cast
      ring
    rw [hm']
    set c : ℂ := (φ (m / X) : ℂ) * (m : ℂ) ^ (s - 1) with hc
    have e1 : ∫ _t in m..(m + 1), c = c := by
      rw [intervalIntegral.integral_const]
      simp
    have e2 : c - ∫ t in m..(m + 1), F t = ∫ t in m..(m + 1), (c - F t) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint _ _), e1]
    rw [e2]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := K / X + B * ‖s - 1‖ * m ^ (-(3 / 2 : ℝ))) fun t ht => ?_).trans ?_
    · rw [Set.uIoc_of_le (by linarith)] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hdecomp : c - F t = ((φ (m / X) - φ (t / X) : ℝ) : ℂ) * (m : ℂ) ^ (s - 1) +
          (φ (t / X) : ℂ) * ((m : ℂ) ^ (s - 1) - (t : ℂ) ^ (s - 1)) := by
        simp only [hc, hF]
        push_cast
        ring
      rw [hdecomp]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hm0, hre]
        have h1 : |φ (m / X) - φ (t / X)| ≤ K / X := by
          refine (h.lip _ _).trans ?_
          rw [← sub_div, abs_div, abs_of_pos hX, ← mul_div_assoc]
          apply div_le_div_of_nonneg_right _ hX.le
          have h6 : |m - t| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [ht.1, ht.2]
          nlinarith
        have h2 : m ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
        calc |φ (m / X) - φ (t / X)| * m ^ (-(1 / 2 : ℝ)) ≤ K / X * 1 :=
              mul_le_mul h1 h2 (Real.rpow_nonneg hm0.le _) (by positivity)
          _ = K / X := mul_one _
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h3 : ‖(m : ℂ) ^ (s - 1) - (t : ℂ) ^ (s - 1)‖ ≤ ‖s - 1‖ * m ^ (-(3 / 2 : ℝ)) := by
          rw [norm_sub_rev]
          have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
            (f := fun τ : ℝ => (τ : ℂ) ^ (s - 1)) (f' := fun τ : ℝ => (s - 1) * (τ : ℂ) ^ (s - 1 - 1))
            (a := m) (b := m + 1) (C := ‖s - 1‖ * m ^ (-(3 / 2 : ℝ)))
            (fun τ hτ => (hasDerivAt_ofReal_cpow_const (by linarith [hτ.1] : τ ≠ 0) hs1).hasDerivWithinAt)
            (fun τ hτ => by
              have hτ0 : 0 < τ := by linarith [hτ.1]
              rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hτ0, hre2]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_nonpos hm0 hτ.1 (by norm_num)) (norm_nonneg _))
            t ⟨ht.1.le, ht.2⟩
          refine hmvt.trans ?_
          have h7 : t - m ≤ 1 := by linarith [ht.2]
          have hC : 0 ≤ ‖s - 1‖ * m ^ (-(3 / 2 : ℝ)) :=
            mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hm0.le _)
          nlinarith
        calc |φ (t / X)| * ‖(m : ℂ) ^ (s - 1) - (t : ℂ) ^ (s - 1)‖
            ≤ B * (‖s - 1‖ * m ^ (-(3 / 2 : ℝ))) := mul_le_mul (h.bound _) h3 (norm_nonneg _) hB
          _ = B * ‖s - 1‖ * m ^ (-(3 / 2 : ℝ)) := by ring
    · rw [show m + 1 - m = 1 by ring, abs_one, mul_one]
  -- the pieces together
  have hsum : ∑ k ∈ range M, (K / X + B * ‖s - 1‖ * ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      K + 3 * B * ‖s - 1‖ := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum, nsmul_eq_mul]
    have h8 : (M : ℝ) * (K / X) ≤ K := by
      rw [← mul_div_assoc, div_le_iff₀ hX]
      nlinarith
    have h9 : B * ‖s - 1‖ * ∑ k ∈ range M, ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ B * ‖s - 1‖ * 3 :=
      mul_le_mul_of_nonneg_left (sum_rpow_neg_three_halves_le M) (mul_nonneg hB (norm_nonneg _))
    linarith
  have hrew : ∑ k ∈ range M, (φ (((k + 1 : ℕ) : ℝ) / X) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) ^ (s - 1) -
      (X : ℂ) ^ s * mellin01 φ s =
      ∑ k ∈ range M, ((φ (((k + 1 : ℕ) : ℝ) / X) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) ^ (s - 1) -
        ∫ t in ((k + 1 : ℕ) : ℝ)..((k + 1 + 1 : ℕ) : ℝ), F t) - ∫ t in (0 : ℝ)..1, F t := by
    rw [← hmain, hsplit, Finset.sum_sub_distrib]
    ring
  rw [hrew]
  calc ‖∑ k ∈ range M, ((φ (((k + 1 : ℕ) : ℝ) / X) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) ^ (s - 1) -
          ∫ t in ((k + 1 : ℕ) : ℝ)..((k + 1 + 1 : ℕ) : ℝ), F t) - ∫ t in (0 : ℝ)..1, F t‖
      ≤ ‖∑ k ∈ range M, ((φ (((k + 1 : ℕ) : ℝ) / X) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) ^ (s - 1) -
          ∫ t in ((k + 1 : ℕ) : ℝ)..((k + 1 + 1 : ℕ) : ℝ), F t)‖ + ‖∫ t in (0 : ℝ)..1, F t‖ :=
        norm_sub_le _ _
    _ ≤ ∑ k ∈ range M, (K / X + B * ‖s - 1‖ * ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) + 2 * B :=
        add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum hpiece)) h01
    _ ≤ 2 * B + K + 3 * B * ‖s - 1‖ := by linarith

/-! ## The class, and its polynomial at a zero -/

/-- The vector of the class with the profiles `E_d`, `d ≤ D₀`, at the length `N`:
`n·x_n = Σ_{d ∣ n, d ≤ D₀} E_d(n/N)`. -/
def classVec (D₀ : ℕ) (E : ℕ → ℝ → ℝ) (N n : ℕ) : ℝ :=
  (∑ d ∈ Icc 1 D₀, if d ∣ n then E d ((n : ℝ) / N) else 0) / n

/-- The boundary function `G = Σ_{d ≤ D₀} E_d/d`. -/
def bdry (D₀ : ℕ) (E : ℕ → ℝ → ℝ) (u : ℝ) : ℝ := ∑ d ∈ Icc 1 D₀, E d u / d

/-- `Ĝ = Σ_d Ê_d/d`. -/
lemma mellin01_bdry {D₀ : ℕ} {E : ℕ → ℝ → ℝ} {B K : ℝ} (hE : ∀ d ∈ Icc 1 D₀, Profile (E d) B K) {s : ℂ}
    (hs : s.re = 1 / 2) : mellin01 (bdry D₀ E) s = ∑ d ∈ Icc 1 D₀, mellin01 (E d) s / d := by
  unfold mellin01
  have h1 : ∀ u : ℝ, (bdry D₀ E u : ℂ) * (u : ℂ) ^ (s - 1) =
      ∑ d ∈ Icc 1 D₀, (E d u : ℂ) * (u : ℂ) ^ (s - 1) / d := by
    intro u
    unfold bdry
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  rw [intervalIntegral.integral_congr fun u _ => h1 u, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [intervalIntegral.integral_div]
  · intro d hd
    exact (intervalIntegrable_mellin (hE d hd).continuous hs 0 1).div_const _

/-- **The polynomial of a class vector at a zero**, by the divisor `d`:
`V_x(ρ) = Σ_{d ≤ D₀} Σ_{m ≤ N/d} E_d(dm/N)(dm)^{ρ−1}`. -/
theorem dpoly_classVec (D₀ : ℕ) (E : ℕ → ℝ → ℝ) (N : ℕ) (q : ZIdx) :
    dpoly N (classVec D₀ E N) q = ∑ d ∈ Icc 1 D₀, ∑ m ∈ Icc 1 (N / d),
      (E d (((d * m : ℕ) : ℝ) / N) : ℂ) * ((d * m : ℕ) : ℂ) ^ (zetaZeroFamily q - 1) := by
  unfold dpoly
  have h1 : ∀ n ∈ Icc 1 N, (classVec D₀ E N n : ℂ) * BallLattice.pw q n =
      ∑ d ∈ Icc 1 D₀,
        if d ∣ n then (E d ((n : ℝ) / N) : ℂ) * (n : ℂ) ^ (zetaZeroFamily q - 1) else 0 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [BallSilent.pw_eq_cpow q hn1]
    unfold classVec
    rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs with hd
    · rw [Complex.cpow_sub _ _ hn0, Complex.cpow_one]
      ring
    · rw [Complex.ofReal_zero, zero_div, zero_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  exact sum_Icc_dvd (Finset.mem_Icc.1 hd).1 N
    fun n => (E d ((n : ℝ) / N) : ℂ) * (n : ℂ) ^ (zetaZeroFamily q - 1)

/-- One divisor's part: `Σ_{m ≤ N/d} φ(dm/N)(dm)^{s−1}` is within `2B + K + 3B|s − 1|` of `N^s·φ̂(s)/d`. -/
lemma norm_part_sub_le {φ : ℝ → ℝ} {B K : ℝ} (h : Profile φ B K) {s : ℂ} (hs : s.re = 1 / 2) {d N : ℕ}
    (hd : 1 ≤ d) (hN : 1 ≤ N) :
    ‖∑ m ∈ Icc 1 (N / d), (φ (((d * m : ℕ) : ℝ) / N) : ℂ) * ((d * m : ℕ) : ℂ) ^ (s - 1) -
        (N : ℂ) ^ s * (mellin01 φ s / d)‖ ≤ 2 * B + K + 3 * B * ‖s - 1‖ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  set X : ℝ := (N : ℝ) / d with hX
  have hXpos : 0 < X := div_pos hN0 hd0
  have key := sum_profile_sub_le h hs hXpos
  rw [hX, Nat.floor_div_eq_div N d, ← hX] at key
  have hsum : ∑ m ∈ Icc 1 (N / d), (φ (((d * m : ℕ) : ℝ) / N) : ℂ) * ((d * m : ℕ) : ℂ) ^ (s - 1) =
      (d : ℂ) ^ (s - 1) * ∑ k ∈ range (N / d),
        (φ (((k + 1 : ℕ) : ℝ) / X) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) ^ (s - 1) := by
    rw [sum_Icc_one_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ((d * (k + 1) : ℕ) : ℝ) / N = ((k + 1 : ℕ) : ℝ) / X := by
      rw [hX]
      push_cast
      field_simp
    have e2 : ((d * (k + 1) : ℕ) : ℂ) ^ (s - 1) =
        (d : ℂ) ^ (s - 1) * (((k + 1 : ℕ) : ℝ) : ℂ) ^ (s - 1) := by
      rw [Complex.ofReal_natCast, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    rw [e1, e2]
    ring
  have hmain : (d : ℂ) ^ (s - 1) * ((X : ℂ) ^ s * mellin01 φ s) = (N : ℂ) ^ s * (mellin01 φ s / d) := by
    have hds : (d : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h0 => hdc h0.1
    have e3 : (X : ℂ) ^ s * (d : ℂ) ^ s = (N : ℂ) ^ s := by
      have h3 := Complex.mul_cpow_ofReal_nonneg hXpos.le hd0.le s
      rw [← Complex.ofReal_mul, hX, div_mul_cancel₀ _ hd0.ne', Complex.ofReal_natCast,
        Complex.ofReal_natCast] at h3
      rw [hX]
      exact h3.symm
    rw [Complex.cpow_sub _ _ hdc, Complex.cpow_one, ← e3]
    field_simp
  have hnd : ‖(d : ℂ) ^ (s - 1)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd)
    rw [Complex.sub_re, hs, Complex.one_re]
    norm_num
  rw [hsum, ← hmain, ← mul_sub, norm_mul]
  calc ‖(d : ℂ) ^ (s - 1)‖ * ‖∑ k ∈ range (N / d),
          (φ (((k + 1 : ℕ) : ℝ) / X) : ℂ) * (((k + 1 : ℕ) : ℝ) : ℂ) ^ (s - 1) - (X : ℂ) ^ s * mellin01 φ s‖
      ≤ 1 * (2 * B + K + 3 * B * ‖s - 1‖) := mul_le_mul hnd key (norm_nonneg _) zero_le_one
    _ = 2 * B + K + 3 * B * ‖s - 1‖ := one_mul _

/-- **A class vector at a zero** (RH): `|V_x(ρ)| ≥ √N·|Ĝ(ρ)| − D₀(2B + K + 3B|ρ − 1|)`. -/
theorem norm_dpoly_classVec_ge (hRH : RiemannHypothesis) {D₀ : ℕ} {E : ℕ → ℝ → ℝ} {B K : ℝ}
    (hE : ∀ d ∈ Icc 1 D₀, Profile (E d) B K) (q : ZIdx) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt N * ‖mellin01 (bdry D₀ E) (zetaZeroFamily q)‖ -
        D₀ * (2 * B + K + 3 * B * ‖zetaZeroFamily q - 1‖) ≤ ‖dpoly N (classVec D₀ E N) q‖ := by
  have hs : (zetaZeroFamily q).re = 1 / 2 := line_of_RH hRH q
  have hnorm : ‖(N : ℂ) ^ zetaZeroFamily q‖ = Real.sqrt N := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), hs, Real.sqrt_eq_rpow]
  have hsumd : ‖dpoly N (classVec D₀ E N) q -
      (N : ℂ) ^ zetaZeroFamily q * mellin01 (bdry D₀ E) (zetaZeroFamily q)‖ ≤
      D₀ * (2 * B + K + 3 * B * ‖zetaZeroFamily q - 1‖) := by
    rw [dpoly_classVec, mellin01_bdry hE hs, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun d hd =>
      norm_part_sub_le (hE d hd) hs (Finset.mem_Icc.1 hd).1 hN).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
  have h2 := norm_sub_norm_le ((N : ℂ) ^ zetaZeroFamily q * mellin01 (bdry D₀ E) (zetaZeroFamily q))
    (dpoly N (classVec D₀ E N) q)
  rw [norm_mul, hnorm, norm_sub_rev] at h2
  linarith

/-! ## Loud, and what quiet implies -/

/-- **A vector of the class that does not carry `ζ` is loud** (RH): if `Ĝ(ρ) ≠ 0` at a zero `ρ = ½ + iγ`, then
`Q_N(x) ≥ (|Ĝ(ρ)|²/(4(¼ + γ²)))·N` for every large `N`. -/
theorem loud (hRH : RiemannHypothesis) {D₀ : ℕ} {E : ℕ → ℝ → ℝ} {B K : ℝ}
    (hE : ∀ d ∈ Icc 1 D₀, Profile (E d) B K) (q : ZIdx)
    (hG : mellin01 (bdry D₀ E) (zetaZeroFamily q) ≠ 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖mellin01 (bdry D₀ E) (zetaZeroFamily q)‖ ^ 2 / (4 * (1 / 4 + (zetaZeroFamily q).im ^ 2)) * N ≤
        form N (classVec D₀ E N) := by
  set g := ‖mellin01 (bdry D₀ E) (zetaZeroFamily q)‖ with hg
  have hg0 : 0 < g := norm_pos_iff.2 hG
  set C := (D₀ : ℝ) * (2 * B + K + 3 * B * ‖zetaZeroFamily q - 1‖) with hC
  refine ⟨max 1 ⌈(2 * C / g) ^ 2⌉₊, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : (2 * C / g) ^ 2 ≤ N := by
    have h1 : ⌈(2 * C / g) ^ 2⌉₊ ≤ N := le_trans (le_max_right _ _) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hsq : 2 * C / g ≤ Real.sqrt N := by
    calc 2 * C / g ≤ |2 * C / g| := le_abs_self _
      _ = Real.sqrt ((2 * C / g) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt hN2
  have hV := norm_dpoly_classVec_ge hRH hE q hN1
  have h3 : Real.sqrt N * g / 2 ≤ ‖dpoly N (classVec D₀ E N) q‖ := by
    rw [div_le_iff₀ hg0] at hsq
    linarith
  have h4 : (Real.sqrt N * g / 2) ^ 2 ≤ ‖dpoly N (classVec D₀ E N) q‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have h5 : (Real.sqrt N * g / 2) ^ 2 = g ^ 2 / 4 * N := by
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  have hden : (0 : ℝ) < 1 / 4 + (zetaZeroFamily q).im ^ 2 := by positivity
  have hterm := le_hasSum (hasSum_form hRH N (classVec D₀ E N)) q (fun j _ => by positivity)
  calc g ^ 2 / (4 * (1 / 4 + (zetaZeroFamily q).im ^ 2)) * N
      = g ^ 2 / 4 * N / (1 / 4 + (zetaZeroFamily q).im ^ 2) := by
        field_simp
    _ ≤ ‖dpoly N (classVec D₀ E N) q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2) :=
        div_le_div_of_nonneg_right (h5 ▸ h4) hden.le
    _ ≤ form N (classVec D₀ E N) := hterm

/-- `1 + log N ≤ 2√N` for `N ≥ 1`. -/
lemma one_add_log_le {N : ℕ} (hN : 1 ≤ N) : 1 + Real.log N ≤ 2 * Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hN0)
  rw [Real.log_sqrt hN0.le] at h1
  linarith

/-- **A quiet vector of the class carries `ζ`** (RH): if `Q_N(x) ≤ C(1 + log N)` for every `N`, then `Ĝ`
vanishes at every zero. -/
theorem carries_zeta (hRH : RiemannHypothesis) {D₀ : ℕ} {E : ℕ → ℝ → ℝ} {B K : ℝ}
    (hE : ∀ d ∈ Icc 1 D₀, Profile (E d) B K) {C : ℝ}
    (hquiet : ∀ N : ℕ, 1 ≤ N → form N (classVec D₀ E N) ≤ C * (1 + Real.log N)) (q : ZIdx) :
    mellin01 (bdry D₀ E) (zetaZeroFamily q) = 0 := by
  by_contra hG
  obtain ⟨N₀, hN₀⟩ := loud hRH hE q hG
  set c := ‖mellin01 (bdry D₀ E) (zetaZeroFamily q)‖ ^ 2 / (4 * (1 / 4 + (zetaZeroFamily q).im ^ 2)) with hc
  have hc0 : 0 < c := by
    have hg0 : 0 < ‖mellin01 (bdry D₀ E) (zetaZeroFamily q)‖ := norm_pos_iff.2 hG
    positivity
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set N := max (max N₀ 1) (⌈(2 * C' / c) ^ 2⌉₊ + 1) with hNdef
  have hN1 : 1 ≤ N := le_trans (le_max_right N₀ 1) (le_max_left _ _)
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left N₀ 1) (le_max_left _ _)
  have hNbig : (2 * C' / c) ^ 2 < N := by
    have h1 : ⌈(2 * C' / c) ^ 2⌉₊ + 1 ≤ N := le_max_right _ _
    have h2 : ((⌈(2 * C' / c) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
    have h3 := Nat.le_ceil ((2 * C' / c) ^ 2)
    push_cast at h2
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsq : 2 * C' / c < Real.sqrt N := by
    calc 2 * C' / c ≤ |2 * C' / c| := le_abs_self _
      _ = Real.sqrt ((2 * C' / c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt N := Real.sqrt_lt_sqrt (sq_nonneg _) hNbig
  rw [div_lt_iff₀ hc0] at hsq
  have hlow := hN₀ N hNN₀
  have hup := hquiet N hN1
  have hlog := one_add_log_le hN1
  have hlog0 : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
    linarith
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hNs : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0.le).symm
  have h1 : C * (1 + Real.log N) ≤ C' * (2 * Real.sqrt N) :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hlog0).trans (mul_le_mul_of_nonneg_left hlog hC'0)
  have h2 : C' * (2 * Real.sqrt N) < c * N := by
    rw [hNs]
    nlinarith
  linarith

/-- `Σ_{n ≤ N} x_n² ≤ 2(D₀B)²` for a vector of the class. -/
lemma sum_sq_classVec_le {D₀ : ℕ} {E : ℕ → ℝ → ℝ} {B K : ℝ} (hE : ∀ d ∈ Icc 1 D₀, Profile (E d) B K)
    (N : ℕ) : ∑ n ∈ Icc 1 N, classVec D₀ E N n ^ 2 ≤ 2 * (D₀ * B) ^ 2 := by
  have hterm : ∀ n ∈ Icc 1 N, classVec D₀ E N n ^ 2 ≤ (D₀ * B) ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    have habs : |∑ d ∈ Icc 1 D₀, if d ∣ n then E d ((n : ℝ) / N) else 0| ≤ D₀ * B := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∀ d ∈ Icc 1 D₀, |if d ∣ n then E d ((n : ℝ) / N) else 0| ≤ B := by
        intro d hd
        split_ifs
        · exact (hE d hd).bound _
        · rw [abs_zero]
          exact (hE d hd).B_nonneg
      refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    unfold classVec
    rw [div_pow, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ n ∈ Icc 1 N, ((n : ℝ) ^ 2)⁻¹ ≤ 2 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [← Finset.sum_Ioc_add_eq_sum_Icc hN]
      have h2 := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := N) one_ne_zero hN
      have h3 : (0 : ℝ) ≤ ((N : ℕ) : ℝ)⁻¹ := by positivity
      norm_num at h2 ⊢
      linarith
  have h0 : (0 : ℝ) ≤ (D₀ * B) ^ 2 := sq_nonneg _
  nlinarith

/-- **The quiet vectors of the class carry `ζ`** (RH): if `Q_N(x) ≤ C·((1 + log N)/N)·Σ_{n ≤ N} x_n²` for every
`N`, as for a vector whose Rayleigh quotient is of the order `log N/N` of `λ_N`, then `Ĝ` vanishes at every
zero. -/
theorem quiet_carries_zeta (hRH : RiemannHypothesis) {D₀ : ℕ} {E : ℕ → ℝ → ℝ} {B K : ℝ}
    (hE : ∀ d ∈ Icc 1 D₀, Profile (E d) B K) {C : ℝ}
    (hquiet : ∀ N : ℕ, 1 ≤ N → form N (classVec D₀ E N) ≤
      C * ((1 + Real.log N) / N) * ∑ n ∈ Icc 1 N, classVec D₀ E N n ^ 2) (q : ZIdx) :
    mellin01 (bdry D₀ E) (zetaZeroFamily q) = 0 := by
  refine carries_zeta hRH hE (C := max C 0 * (2 * (D₀ * B) ^ 2)) (fun N hN => ?_) q
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog0 : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg hN1
    linarith
  have hS := sum_sq_classVec_le hE N
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, classVec D₀ E N n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hfrac : (1 + Real.log N) / N ≤ 1 + Real.log N := div_le_self hlog0 hN1
  have hfrac0 : 0 ≤ (1 + Real.log N) / N := div_nonneg hlog0 hN0.le
  calc form N (classVec D₀ E N)
      ≤ C * ((1 + Real.log N) / N) * ∑ n ∈ Icc 1 N, classVec D₀ E N n ^ 2 := hquiet N hN
    _ ≤ max C 0 * (1 + Real.log N) * (2 * (D₀ * B) ^ 2) := by
        refine mul_le_mul ?_ hS hS0 (mul_nonneg hC0 hlog0)
        exact (mul_le_mul_of_nonneg_right (le_max_left C 0) hfrac0).trans
          (mul_le_mul_of_nonneg_left hfrac hC0)
    _ = max C 0 * (2 * (D₀ * B) ^ 2) * (1 + Real.log N) := by ring

end BallLoud

#print axioms BallLoud.sum_profile_sub_le
#print axioms BallLoud.loud
#print axioms BallLoud.carries_zeta
#print axioms BallLoud.quiet_carries_zeta
