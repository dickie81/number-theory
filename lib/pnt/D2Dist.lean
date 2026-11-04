import Mathlib
import D2Tail
import QuantMoments
import ModelTrunc

/-!
# The distribution of `L′/L(1, χ_d)` — CONDITIONAL on the half-plane

**CONDITIONAL.** The final results use the tail identity `GSTail.logDeriv_one_tail`, hence the half-plane
`Re s > 11/12` (`Eis.LFunction_ne_zero_of_re_gt`, see `formalisations/openai-half-plane.md`). Lean checks them with the
standard axioms only, but they must be cited as conditional on that input. The abstract assembly (`core`,
`emp_tendsto`) and the model-side pieces are unconditional.

* `D2Dist.core`: method-of-moments assembly with the cutoff `Y(x) = ⌈log(x + 2)⌉^48`.
* `D2Dist.moments_pos`, `D2Dist.moments_neg` (CONDITIONAL): for every `k`,
  `(1/x) Σ_{1<d≤x} (Re L′/L(1, χ_{±d}))^k → (3/π²) E[X^k]`, over fundamental discriminants.
* `D2Dist.dist_pos`, `D2Dist.dist_neg` (CONDITIONAL): the empirical laws converge weakly to the law
  `RandModel.ν` of the random model `X`.

See `formalisations/d2-density.md`.
-/
namespace D2Dist
open Finset Filter Topology ArithmeticFunction
open GSFund GSEven GSDens GSLink GSUncond GSDelta GSNu

/-- The Kronecker symbol as a real number. -/
noncomputable def kr (D : ℤ) (n : ℕ) : ℝ :=
  ((ZMod.χ₈ (D : ZMod 8) : ℤ) : ℝ) ^ (n.factorization 2) * (jacobiSym D (n / 2 ^ n.factorization 2) : ℝ)

theorem kron_eq (D : ℤ) (n : ℕ) : kron D n = ((kr D n : ℝ) : ℂ) := by
  simp [kron, kr]

theorem abs_kr_le (D : ℤ) (n : ℕ) : |kr D n| ≤ 1 := by
  unfold kr
  rw [abs_mul, abs_pow]
  have h1 : |((ZMod.χ₈ (D : ZMod 8) : ℤ) : ℝ)| ≤ 1 := by
    rcases ZMod.isQuadratic_χ₈ (D : ZMod 8) with h | h | h <;> rw [h] <;> norm_num
  have h2 : |(jacobiSym D (n / 2 ^ n.factorization 2) : ℝ)| ≤ 1 := by
    rcases jacobiSym.trichotomy D (n / 2 ^ n.factorization 2) with h | h | h <;> rw [h] <;> norm_num
  calc _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (abs_nonneg _) h1) h2 (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1


/-! ### Elementary estimates -/

theorem abs_pow_sub_pow_le {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) (k : ℕ) :
    |a ^ k - b ^ k| ≤ k * |a - b| * M ^ (k - 1) := by
  have hM : 0 ≤ M := (abs_nonneg a).trans ha
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_pow]
    have h1 : |a| * |a ^ k - b ^ k| ≤ M * (k * |a - b| * M ^ (k - 1)) :=
      mul_le_mul ha ih (abs_nonneg _) hM
    have h2 : |a - b| * |b| ^ k ≤ |a - b| * M ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hb k) (abs_nonneg _)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h1 h2 ⊢
    · have : M * (k * |a - b| * M ^ (k - 1)) = k * |a - b| * M ^ k := by
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk).symm]; push_cast; ring_nf
      simp only [Nat.add_sub_cancel]; push_cast
      nlinarith [abs_nonneg (a - b), pow_nonneg hM k]

theorem L1 (n : ℕ) : Tendsto (fun c : ℝ => (1 + 48 * Real.log c) ^ n / c) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero).const_mul ((49 : ℝ) ^ n)
  rw [mul_zero] at h
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
    have := Real.log_nonneg hc
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with c hc
    have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 1) hc
    have hl : 1 ≤ Real.log c := by rw [Real.le_log_iff_exp_le hc0]; exact hc
    have : (1 + 48 * Real.log c) ^ n ≤ (49 * Real.log c) ^ n :=
      pow_le_pow_left₀ (by linarith) (by linarith) n
    rw [mul_pow] at this
    simp only [one_mul, add_zero]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right this hc0.le

theorem L2 (m : ℕ) : Tendsto (fun x : ℕ => Real.log (x + 2) ^ m * (Real.sqrt x + 2) / x) atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.log t ^ (m : ℝ) / t ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (m : ℝ) (by norm_num : (0:ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun x : ℕ => ((x : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h2 := (h0.comp h1).const_mul (3 * Real.sqrt 3)
  rw [mul_zero] at h2
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have : (0:ℝ) ≤ Real.log (x + 2) := Real.log_nonneg (by have : (0:ℝ) ≤ x := Nat.cast_nonneg x; linarith)
    positivity
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hl : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
    simp only [Function.comp, Real.rpow_natCast]
    have hsx : 1 ≤ Real.sqrt x := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    have hs2 : (x + 2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (x + 2) := by rw [Real.sqrt_eq_rpow]
    rw [hs2]
    have hsq : Real.sqrt (x + 2) ≤ Real.sqrt 3 * Real.sqrt x := by
      rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (by linarith)
    have hxs : (x : ℝ) = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt (by linarith)).symm
    have hpos : 0 < Real.sqrt (x + 2) := Real.sqrt_pos.2 (by linarith)
    have hs3 : 0 < Real.sqrt 3 := by positivity
    set L := Real.log (x + 2) ^ m
    have hL : 0 ≤ L := pow_nonneg hl m
    rw [div_le_iff₀ (by linarith), show 3 * Real.sqrt 3 * (L / Real.sqrt (x + 2)) * x =
      3 * Real.sqrt 3 * L * x / Real.sqrt (x + 2) by ring, le_div_iff₀ hpos]
    calc L * (Real.sqrt x + 2) * Real.sqrt (x + 2) ≤ L * (3 * Real.sqrt x) * (Real.sqrt 3 * Real.sqrt x) := by
          gcongr; linarith
      _ = 3 * Real.sqrt 3 * L * (Real.sqrt x * Real.sqrt x) := by ring
      _ = 3 * Real.sqrt 3 * L * x := by rw [← hxs]


/-! ### The truncated Dirichlet series -/

/-- `log Y (1 + log Y)`, a bound for `Σ_{n ≤ Y} Λ(n)/n`. -/
noncomputable def Lb (Y : ℕ) : ℝ := Real.log Y * (1 + Real.log Y)

/-- `S_Y(D) = Σ_{n ≤ Y} (D|n) Λ(n)/n`. -/
noncomputable def S (Y : ℕ) (D : ℤ) : ℝ := ∑ n ∈ Icc 1 Y, kr D n * Λ n / n

theorem sum_vm_le (Y : ℕ) : ∑ n ∈ Icc 1 Y, Λ n / n ≤ Lb Y := by
  rcases Nat.eq_zero_or_pos Y with rfl | hY
  · simp [Lb]
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast hY)
  calc ∑ n ∈ Icc 1 Y, Λ n / n ≤ ∑ n ∈ Icc 1 Y, Real.log Y * (1 / (n : ℝ)) := by
        refine sum_le_sum fun n hn => ?_
        simp only [mem_Icc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (vonMangoldt_le_log.trans
          (Real.log_le_log hn0 (by exact_mod_cast hn.2))) hn0.le
    _ = Real.log Y * ∑ n ∈ Icc 1 Y, (1 / (n : ℝ)) := by rw [mul_sum]
    _ ≤ Lb Y := by
        unfold Lb
        refine mul_le_mul_of_nonneg_left ?_ hlY
        have := harmonic_le_one_add_log Y
        rw [harmonic_eq_sum_Icc] at this; push_cast at this
        simpa [one_div] using this

theorem abs_S_le (Y : ℕ) (D : ℤ) : |S Y D| ≤ Lb Y := by
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun n hn => ?_).trans (sum_vm_le Y))
  simp only [mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
  rw [abs_div, abs_mul, abs_of_nonneg vonMangoldt_nonneg, abs_of_pos hn0]
  exact div_le_div_of_nonneg_right (by
    have := abs_kr_le D n
    nlinarith [vonMangoldt_nonneg (n := n)]) hn0.le

theorem Lb_nonneg (Y : ℕ) : 0 ≤ Lb Y := (abs_nonneg _).trans (abs_S_le Y 0)


/-! ### The abstract assembly -/

/-- The cutoff: `c(x) = ⌈log(x+2)⌉`, `Y(x) = c(x)^48`. -/
noncomputable def cc (x : ℕ) : ℕ := ⌈Real.log (x + 2)⌉₊

theorem log_x2_pos (x : ℕ) : 0 < Real.log (x + 2) :=
  Real.log_pos (by have : (0:ℝ) ≤ x := Nat.cast_nonneg x; linarith)

theorem one_lt_log4 {x : ℕ} (hx : 2 ≤ x) : 1 < Real.log (x + 2) := by
  have h2 : (2:ℝ) ≤ x := by exact_mod_cast hx
  have hx' : (4 : ℝ) ≤ x + 2 := by linarith
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9; linarith

theorem two_le_cc {x : ℕ} (hx : 2 ≤ x) : 2 ≤ cc x := by
  have := one_lt_log4 hx
  have : 1 < cc x := Nat.lt_ceil.2 (by exact_mod_cast this)
  omega

theorem tendsto_cc : Tendsto (fun x => (cc x : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun x : ℕ => ((x : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono (fun x => Nat.le_ceil _) (Real.tendsto_log_atTop.comp h1)

theorem rpow_Y (c : ℕ) : (((c ^ 48 : ℕ) : ℝ)) ^ (-(1 / 24) : ℝ) = ((c : ℝ) ^ 2)⁻¹ := by
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  push_cast
  rw [← Real.rpow_natCast (c : ℝ) 48, ← Real.rpow_mul hc0, ← Real.rpow_natCast (c : ℝ) 2,
    ← Real.rpow_neg hc0]
  norm_num

theorem Lb_pow_le (c : ℕ) : Lb (c ^ 48) ≤ (1 + 48 * Real.log c) ^ 2 := by
  unfold Lb
  push_cast
  rw [Real.log_pow]
  push_cast
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have := Real.log_nonneg (show (1:ℝ) ≤ c by exact_mod_cast hc)
  nlinarith

theorem log_le_cc (x : ℕ) : Real.log (x + 2) ≤ cc x := Nat.le_ceil _

theorem cc_le (x : ℕ) (hx : 1 ≤ x) : (cc x : ℝ) ≤ 2 * Real.log (x + 2) := by
  have h := (Nat.ceil_lt_add_one (log_x2_pos x).le).le
  have : 1 ≤ Real.log (x + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : (1:ℝ) ≤ x := by exact_mod_cast hx
    have := Real.exp_one_lt_d9; linarith
  unfold cc; linarith


section Core
variable (F : ℕ → Prop) [DecidablePred F] (σ : ℕ → ℤ) (ℓ : ℕ → ℝ) (κ : ℝ) (E : ℕ → ℕ → ℝ) (m : ℕ → ℝ)

/-- The pointwise bound at a fixed `x ≥ 2`. -/
theorem main_bound
    (hquant : ∀ Y k x : ℕ, |∑ d ∈ Ioc 0 x, (if F d then (-S Y (σ d)) ^ k else 0) - x * κ * E k Y| ≤
      Lb Y ^ k * (2048 * (Y : ℝ) ^ (3 * k) * (Real.sqrt x + 2)))
    (C : ℝ) (hC : 0 ≤ C)
    (htail : ∀ d, F d → 1 < d → ∀ Y : ℕ, 2 ≤ Y → |ℓ d + S Y (σ d)| ≤ C * Real.log (d + 2) * (Y : ℝ) ^ (-(1 / 24) : ℝ))
    (k x : ℕ) (hx : 2 ≤ x) :
    |(∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ k else 0)) / x - κ * m k| ≤
      k * (C / cc x) * (Lb (cc x ^ 48) + C / cc x) ^ (k - 1) +
        2 * (Lb (cc x ^ 48) ^ k * (2048 * ((cc x ^ 48 : ℕ) : ℝ) ^ (3 * k) * (Real.sqrt x + 2)) / x) +
        |κ| * |E k (cc x ^ 48) - m k| := by
  set c := cc x
  set Y := c ^ 48
  set L := Lb Y
  have hc2 := two_le_cc hx
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hY2 : 2 ≤ Y := le_trans hc2 (Nat.le_self_pow (by norm_num) c)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hL : 0 ≤ L := Lb_nonneg Y
  set e := C / c
  have he : 0 ≤ e := div_nonneg hC hc0.le
  -- the tail error is at most `e` on `d ≤ x`
  have hte : ∀ d ∈ Ioc 0 x, F d → 1 < d → |ℓ d + S Y (σ d)| ≤ e := by
    intro d hd hF h1
    refine (htail d hF h1 Y hY2).trans ?_
    rw [rpow_Y c]
    have hd2 : Real.log (d + 2) ≤ c := by
      refine le_trans (Real.log_le_log (by positivity) ?_) (log_le_cc x)
      simp only [mem_Ioc] at hd; have : (d : ℝ) ≤ x := by exact_mod_cast hd.2
      linarith
    have hl0 : 0 ≤ Real.log (d + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    calc C * Real.log (d + 2) * ((c : ℝ) ^ 2)⁻¹ ≤ C * c * ((c : ℝ) ^ 2)⁻¹ := by gcongr
      _ = e := by simp only [e]; field_simp
  -- decomposition
  have hsplit : ∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ k else 0) =
      ∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ k - (-S Y (σ d)) ^ k else 0) +
      ∑ d ∈ Ioc 0 x, (if F d then (-S Y (σ d)) ^ k else 0) -
      ∑ d ∈ Ioc 0 x, (if d = 1 then (if F d then (-S Y (σ d)) ^ k else 0) else 0) := by
    rw [← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun d hd => ?_
    simp only [mem_Ioc] at hd
    by_cases h1 : d = 1
    · subst h1; simp
    · have : 1 < d := by omega
      by_cases hF : F d <;> simp [hF, h1, this]
  have b1 : |∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ k - (-S Y (σ d)) ^ k else 0)| ≤
      x * (k * e * (L + e) ^ (k - 1)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ d ∈ Ioc 0 x, |(if F d ∧ 1 < d then ℓ d ^ k - (-S Y (σ d)) ^ k else 0)| ≤
        k * e * (L + e) ^ (k - 1) := by
      intro d hd
      split_ifs with h
      · have h1 := hte d hd h.1 h.2
        have hS := abs_S_le Y (σ d)
        have hb : |-S Y (σ d)| ≤ L + e := by rw [abs_neg]; linarith
        have ha : |ℓ d| ≤ L + e := by
          have := abs_sub_abs_le_abs_sub (ℓ d) (-S Y (σ d))
          rw [sub_neg_eq_add] at this; rw [abs_neg] at this; linarith
        refine (abs_pow_sub_pow_le ha hb k).trans ?_
        rw [sub_neg_eq_add]
        have := pow_nonneg (add_nonneg hL he) (k - 1)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)) this
      · rw [abs_zero]; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k) he) (pow_nonneg (add_nonneg hL he) _)
    refine (sum_le_sum this).trans (le_of_eq ?_)
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]
  have b3 : |∑ d ∈ Ioc 0 x, (if d = 1 then (if F d then (-S Y (σ d)) ^ k else 0) else 0)| ≤ L ^ k := by
    rw [sum_ite_eq']
    split_ifs with h1 h2
    · rw [abs_pow, abs_neg]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_S_le Y _) k
    · simp; exact pow_nonneg hL k
    · simp; exact pow_nonneg hL k
  have b2 := hquant Y k x
  set Q := L ^ k * (2048 * (Y : ℝ) ^ (3 * k) * (Real.sqrt x + 2))
  have hQ1 : L ^ k ≤ Q := by
    have : (1 : ℝ) ≤ 2048 * (Y : ℝ) ^ (3 * k) * (Real.sqrt x + 2) := by
      have : (1 : ℝ) ≤ (Y : ℝ) ^ (3 * k) := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ Y))
      have := Real.sqrt_nonneg (x : ℝ); nlinarith
    calc L ^ k = L ^ k * 1 := (mul_one _).symm
      _ ≤ Q := mul_le_mul_of_nonneg_left this (pow_nonneg hL k)
  rw [hsplit]
  set A1 := ∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ k - (-S Y (σ d)) ^ k else 0)
  set A2 := ∑ d ∈ Ioc 0 x, (if F d then (-S Y (σ d)) ^ k else 0)
  set A3 := ∑ d ∈ Ioc 0 x, (if d = 1 then (if F d then (-S Y (σ d)) ^ k else 0) else 0)
  have e1 : (A1 + A2 - A3) / x - κ * m k = A1 / x + (A2 - x * κ * E k Y) / x - A3 / x + κ * (E k Y - m k) := by
    field_simp; ring
  rw [e1]
  have t1 : |A1 / x| ≤ k * e * (L + e) ^ (k - 1) := by
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; linarith
  have t2 : |(A2 - x * κ * E k Y) / x| ≤ Q / x := by
    rw [abs_div, abs_of_pos hx0]; exact div_le_div_of_nonneg_right b2 hx0.le
  have t3 : |A3 / x| ≤ Q / x := by
    rw [abs_div, abs_of_pos hx0]; exact div_le_div_of_nonneg_right (b3.trans hQ1) hx0.le
  have t4 : |κ * (E k Y - m k)| = |κ| * |E k Y - m k| := abs_mul _ _
  have := abs_add_le (A1 / x + (A2 - x * κ * E k Y) / x - A3 / x) (κ * (E k Y - m k))
  have := abs_sub (A1 / x + (A2 - x * κ * E k Y) / x) (A3 / x)
  have := abs_add_le (A1 / x) ((A2 - x * κ * E k Y) / x)
  have h2Q : 2 * (Q / x) = Q / x + Q / x := by ring
  linarith

/-- **The abstract assembly.** -/
theorem core
    (hquant : ∀ Y k x : ℕ, |∑ d ∈ Ioc 0 x, (if F d then (-S Y (σ d)) ^ k else 0) - x * κ * E k Y| ≤
      Lb Y ^ k * (2048 * (Y : ℝ) ^ (3 * k) * (Real.sqrt x + 2)))
    (C : ℝ) (hC : 0 ≤ C)
    (htail : ∀ d, F d → 1 < d → ∀ Y : ℕ, 2 ≤ Y → |ℓ d + S Y (σ d)| ≤ C * Real.log (d + 2) * (Y : ℝ) ^ (-(1 / 24) : ℝ))
    (hE : ∀ k, Tendsto (fun Y => E k Y) atTop (𝓝 (m k))) (k : ℕ) :
    Tendsto (fun x : ℕ => (∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ k else 0)) / x) atTop (𝓝 (κ * m k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hccN : Tendsto cc atTop atTop := tendsto_natCast_atTop_iff.1 tendsto_cc
  have hY : Tendsto (fun x => cc x ^ 48) atTop atTop :=
    tendsto_atTop_mono (fun x => Nat.le_self_pow (by norm_num) _) hccN
  -- the three error terms
  set K1 := (k : ℝ) * C * (1 + C) ^ k
  have hT1 : Tendsto (fun x => K1 * ((1 + 48 * Real.log (cc x)) ^ (2 * k) / cc x)) atTop (𝓝 0) := by
    simpa using ((L1 (2 * k)).comp tendsto_cc).const_mul K1
  set K2 := 2 * 2048 * (49 : ℝ) ^ (2 * k) * 2 ^ (146 * k)
  have hT2 : Tendsto (fun x : ℕ => K2 * (Real.log (x + 2) ^ (146 * k) * (Real.sqrt x + 2) / x)) atTop (𝓝 0) := by
    simpa using (L2 (146 * k)).const_mul K2
  have hT3 : Tendsto (fun x => |κ| * |E k (cc x ^ 48) - m k|) atTop (𝓝 0) := by
    have := (((hE k).comp hY).sub_const (m k)).abs.const_mul |κ|
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ ((hT1.add hT2).add hT3 |>.trans (by simp))
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [Real.norm_eq_abs]
  refine (main_bound F σ ℓ κ E m hquant C hC htail k x hx).trans ?_
  have hc2 := two_le_cc hx
  set c := cc x
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (by omega : 1 ≤ c)
  have hc0 : (0 : ℝ) < c := by linarith
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc1
  set A := (1 + 48 * Real.log c) ^ 2
  have hA1 : 1 ≤ A := one_le_pow₀ (by linarith)
  have hLA : Lb (c ^ 48) ≤ A := Lb_pow_le c
  have hL0 := Lb_nonneg (c ^ 48)
  have hCc : C / c ≤ C := div_le_self hC hc1
  have hCc0 : 0 ≤ C / c := div_nonneg hC hc0.le
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  refine add_le_add (add_le_add ?_ ?_) le_rfl
  · -- first term
    have h1 : Lb (c ^ 48) + C / c ≤ (1 + C) * A := by nlinarith
    have h2 : (Lb (c ^ 48) + C / c) ^ (k - 1) ≤ ((1 + C) * A) ^ k := by
      calc (Lb (c ^ 48) + C / c) ^ (k - 1) ≤ ((1 + C) * A) ^ (k - 1) :=
            pow_le_pow_left₀ (by positivity) h1 _
        _ ≤ ((1 + C) * A) ^ k := pow_le_pow_right₀ (by nlinarith) (Nat.sub_le k 1)
    have hA : A ^ k = (1 + 48 * Real.log c) ^ (2 * k) := by rw [pow_mul]
    calc (k : ℝ) * (C / c) * (Lb (c ^ 48) + C / c) ^ (k - 1) ≤ (k : ℝ) * (C / c) * ((1 + C) * A) ^ k := by
          gcongr
      _ = K1 * ((1 + 48 * Real.log c) ^ (2 * k) / c) := by
          rw [mul_pow, hA]; simp only [K1]; field_simp
  · -- second term
    have h49 : 1 + 48 * Real.log c ≤ 49 * c := by
      have := Real.log_le_sub_one_of_pos hc0; linarith
    have hLc : Lb (c ^ 48) ≤ (49 * c) ^ 2 := hLA.trans (pow_le_pow_left₀ (by linarith) h49 2)
    have hcl := cc_le x (by omega)
    have hlog0 := (log_x2_pos x).le
    have hYc : ((c ^ 48 : ℕ) : ℝ) ^ (3 * k) = (c : ℝ) ^ (144 * k) := by
      push_cast; rw [← pow_mul]; ring_nf
    rw [hYc]
    have hs : 0 ≤ Real.sqrt x + 2 := by positivity
    have step1 : Lb (c ^ 48) ^ k * (2048 * (c : ℝ) ^ (144 * k) * (Real.sqrt x + 2)) ≤
        ((49 * c) ^ 2) ^ k * (2048 * (c : ℝ) ^ (144 * k) * (Real.sqrt x + 2)) := by
      gcongr
    have step2 : ((49 * (c : ℝ)) ^ 2) ^ k * (2048 * (c : ℝ) ^ (144 * k)) =
        2048 * (49 : ℝ) ^ (2 * k) * (c : ℝ) ^ (146 * k) := by
      rw [← pow_mul, mul_pow, show 146 * k = 2 * k + 144 * k by ring, pow_add]; ring
    have step3 : (c : ℝ) ^ (146 * k) ≤ (2 * Real.log (x + 2)) ^ (146 * k) :=
      pow_le_pow_left₀ hc0.le hcl _
    rw [mul_pow] at step3
    calc 2 * (Lb (c ^ 48) ^ k * (2048 * (c : ℝ) ^ (144 * k) * (Real.sqrt x + 2)) / x)
        ≤ 2 * (((49 * c) ^ 2) ^ k * (2048 * (c : ℝ) ^ (144 * k) * (Real.sqrt x + 2)) / x) := by gcongr
      _ = 2 * (2048 * (49 : ℝ) ^ (2 * k) * (c : ℝ) ^ (146 * k) * (Real.sqrt x + 2) / x) := by
          rw [← step2]; ring
      _ ≤ 2 * (2048 * (49 : ℝ) ^ (2 * k) * (2 ^ (146 * k) * Real.log (x + 2) ^ (146 * k)) *
            (Real.sqrt x + 2) / x) := by gcongr
      _ = K2 * (Real.log (x + 2) ^ (146 * k) * (Real.sqrt x + 2) / x) := by simp only [K2]; ring

end Core


/-! ### The empirical distribution -/

section Emp
open MeasureTheory
variable (F : ℕ → Prop) [DecidablePred F] (ℓ : ℕ → ℝ)

/-- The discriminants counted up to `x`. -/
noncomputable def St (x : ℕ) : Finset ℕ := (Ioc 0 x).filter (fun d => F d ∧ 1 < d)

/-- The (unnormalised-by-`x`) counting measure of `ℓ` over `St F x`, normalised to mass one. -/
noncomputable def empM (x : ℕ) : Measure ℝ :=
  ((St F x).card : ENNReal)⁻¹ • ∑ d ∈ St F x, Measure.dirac (ℓ d)

theorem empM_univ {x : ℕ} (h : (St F x).Nonempty) : empM F ℓ x Set.univ = 1 := by
  rw [empM, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using h.ne_empty) (by simp)

/-- The empirical law of `ℓ d` for `d ∈ St F x` (a point mass at `0` when `St F x = ∅`). -/
noncomputable def emp (x : ℕ) : ProbabilityMeasure ℝ :=
  if h : (St F x).Nonempty then ⟨empM F ℓ x, ⟨empM_univ F ℓ h⟩⟩ else ⟨Measure.dirac 0, inferInstance⟩

theorem coe_emp (x : ℕ) : (emp F ℓ x : Measure ℝ) =
    if (St F x).Nonempty then empM F ℓ x else Measure.dirac 0 := by
  unfold emp; by_cases h : (St F x).Nonempty <;> simp [h]

theorem integrable_emp (x k : ℕ) : Integrable (fun t : ℝ => t ^ k) (emp F ℓ x : Measure ℝ) := by
  rw [coe_emp]
  split_ifs with h
  · have hc : ((St F x).card : ENNReal) ≠ 0 := by
      simpa using h.ne_empty
    exact (integrable_finsetSum_measure.2 fun d _ => integrable_dirac enorm_lt_top).smul_measure
      (ENNReal.inv_ne_top.2 hc)
  · exact integrable_dirac enorm_lt_top

theorem integral_emp {x : ℕ} (h : (St F x).Nonempty) (k : ℕ) :
    ∫ t, t ^ k ∂(emp F ℓ x : Measure ℝ) = (∑ d ∈ St F x, ℓ d ^ k) / (St F x).card := by
  simp only [coe_emp, h, ite_true]
  rw [empM, integral_smul_measure,
    integral_finsetSum_measure fun d _ => integrable_dirac enorm_lt_top]
  simp [integral_dirac, div_eq_inv_mul]

theorem sum_St (x k : ℕ) : ∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ k else 0) = ∑ d ∈ St F x, ℓ d ^ k := by
  rw [St, sum_filter]

/-- **Method of moments for the empirical laws.** If `(1/x) Σ_{d ∈ St F x} ℓ(d)^k → κ ∫ t^k dν` for every
`k`, with `κ > 0`, and `ν` has finite exponential moment, the empirical laws converge weakly to `ν`. -/
theorem emp_tendsto (κ : ℝ) (hκ : 0 < κ) (ν : ProbabilityMeasure ℝ)
    (hνi : ∀ k, Integrable (fun t : ℝ => t ^ k) (ν : Measure ℝ))
    {s : ℝ} (hs : 0 < s) (hνe : Integrable (fun t => Real.exp (s * |t|)) (ν : Measure ℝ))
    (hmom : ∀ k, Tendsto (fun x : ℕ => (∑ d ∈ Ioc 0 x, (if F d ∧ 1 < d then ℓ d ^ k else 0)) / x) atTop
      (𝓝 (κ * ∫ t, t ^ k ∂(ν : Measure ℝ)))) :
    Tendsto (emp F ℓ) atTop (𝓝 ν) := by
  have hcard : Tendsto (fun x : ℕ => ((St F x).card : ℝ) / x) atTop (𝓝 κ) := by
    have h0 := hmom 0
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one] at h0
    refine h0.congr fun x => ?_
    rw [St, sum_boole]
  have hev : ∀ᶠ x in atTop, (St F x).Nonempty ∧ 0 < x := by
    have := hcard.eventually (lt_mem_nhds hκ)
    filter_upwards [this, eventually_gt_atTop 0] with x hx hx0
    refine ⟨?_, hx0⟩
    rw [← Finset.card_pos]; by_contra hc; simp_all
  refine MomentConv.tendsto_of_moments _ ν (integrable_emp F ℓ) hνi (fun k => ?_) hs hνe
  have hk := (hmom k).div hcard hκ.ne'
  rw [mul_div_cancel_left₀ _ hκ.ne'] at hk
  refine hk.congr' ?_
  filter_upwards [hev] with x ⟨hx, hx0⟩
  simp only [Pi.div_apply]
  rw [integral_emp F ℓ hx, sum_St]
  have : (0 : ℝ) < x := by exact_mod_cast hx0
  field_simp

end Emp


/-! ### The concrete instances — CONDITIONAL (the tail bound uses `GSTail.logDeriv_one_tail`) -/

section Concrete
open MeasureTheory

/-- The coefficients `a n = -Λ(n)/n`. -/
noncomputable def a (n : ℕ) : ℝ := -(Λ n / n)

theorem inner_eq (Y : ℕ) (D : ℤ) : ∑ p ∈ Icc 1 Y, ((a p : ℝ) : ℂ) * kron D p = ((-S Y D : ℝ) : ℂ) := by
  simp only [kron_eq, S, a]; push_cast
  rw [← sum_neg_distrib]; exact sum_congr rfl fun n _ => by ring

theorem sum_abs_a (Y : ℕ) : ∑ p ∈ Icc 1 Y, |a p| ≤ Lb Y := by
  refine le_trans (le_of_eq (sum_congr rfl fun n _ => ?_)) (sum_vm_le Y)
  rw [a, abs_neg, abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))]

/-- The model moments at cutoff `Y`. -/
noncomputable def E (k Y : ℕ) : ℝ := ∫ ω, (∑ n ∈ Icc 1 Y, a n * ModelMoments.Xm n ω) ^ k ∂(RandModel.P)

/-- The moments of the limit law `RandModel.ν`. -/
noncomputable def mν (k : ℕ) : ℝ := ∫ t, t ^ k ∂(RandModel.ν : Measure ℝ)

theorem mν_eq (k : ℕ) : mν k = ∫ ω, RandModel.X ω ^ k ∂(RandModel.P) := by
  rw [mν, RandModel.ν, ProbabilityMeasure.coe_mk,
    integral_map RandModel.aemeasurable_X (by fun_prop)]

theorem tendsto_E (k : ℕ) : Tendsto (fun Y => E k Y) atTop (𝓝 (mν k)) := by
  have hE : ∀ Y, E k Y = (-1) ^ k * ∫ ω, ModelTrunc.A Y ω ^ k ∂(RandModel.P) := by
    intro Y
    rw [E, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have : ∑ n ∈ Icc 1 Y, a n * ModelMoments.Xm n ω = -ModelTrunc.A Y ω := by
      rw [ModelTrunc.A, ← sum_neg_distrib]; exact sum_congr rfl fun n _ => by rw [a]; ring
    dsimp only; rw [this, neg_pow]
  have hm : mν k = (-1) ^ k * ∫ ω, (-RandModel.X ω) ^ k ∂(RandModel.P) := by
    rw [mν_eq, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    dsimp only; rw [← mul_pow, neg_one_mul, neg_neg]
  simp only [hE, hm]
  exact (ModelTrunc.moment_A_tendsto k).const_mul _

/-- The real quantity `κ = 3/π²`. -/
noncomputable def κ : ℝ := 3 / Real.pi ^ 2

theorem hquant_pos (Y k x : ℕ) :
    |∑ d ∈ Ioc 0 x, (if fundPos d then (-S Y (d : ℤ)) ^ k else 0) - x * κ * E k Y| ≤
      Lb Y ^ k * (2048 * (Y : ℝ) ^ (3 * k) * (Real.sqrt x + 2)) := by
  have h := QuantMoments.moment_quant_pos (Icc 1 Y) (fun p hp => (mem_Icc.1 hp).1)
    (fun p hp => (mem_Icc.1 hp).2) a k x
  simp only [inner_eq] at h
  have e : (∑ d ∈ Ioc 0 x, (if fundPos d then (((-S Y (d : ℤ) : ℝ) : ℂ)) ^ k else 0) -
      (x : ℂ) * ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ Icc 1 Y, a n * ModelMoments.Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ)) =
      (((∑ d ∈ Ioc 0 x, (if fundPos d then (-S Y (d : ℤ)) ^ k else 0) - x * κ * E k Y : ℝ)) : ℂ) := by
    push_cast [apply_ite (fun r : ℝ => (r : ℂ)), κ, E]; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (sum_abs_a Y) k

theorem hquant_neg (Y k x : ℕ) :
    |∑ d ∈ Ioc 0 x, (if fundNeg d then (-S Y (-(d : ℤ))) ^ k else 0) - x * κ * E k Y| ≤
      Lb Y ^ k * (2048 * (Y : ℝ) ^ (3 * k) * (Real.sqrt x + 2)) := by
  have h := QuantMoments.moment_quant_neg (Icc 1 Y) (fun p hp => (mem_Icc.1 hp).1)
    (fun p hp => (mem_Icc.1 hp).2) a k x
  simp only [inner_eq] at h
  have e : (∑ d ∈ Ioc 0 x, (if fundNeg d then (((-S Y (-(d : ℤ)) : ℝ) : ℂ)) ^ k else 0) -
      (x : ℂ) * ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ Icc 1 Y, a n * ModelMoments.Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ)) =
      (((∑ d ∈ Ioc 0 x, (if fundNeg d then (-S Y (-(d : ℤ))) ^ k else 0) - x * κ * E k Y : ℝ)) : ℂ) := by
    push_cast [apply_ite (fun r : ℝ => (r : ℂ)), κ, E]; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (sum_abs_a Y) k

open Classical in
/-- `ℓ⁺(d) = Re L′/L(1, χ_d)` for a positive fundamental discriminant `d > 1` (`0` otherwise). -/
noncomputable def lpos (d : ℕ) : ℝ :=
  if h : fundPos d ∧ 1 < d then
    haveI : NeZero d := ⟨by omega⟩
    (deriv (DirichletCharacter.LFunction (GSPrim.primitive_pos h.1 h.2).choose) 1 /
      DirichletCharacter.LFunction (GSPrim.primitive_pos h.1 h.2).choose 1).re
  else 0

open Classical in
/-- `ℓ⁻(d) = Re L′/L(1, χ_{-d})` for a negative fundamental discriminant `-d` (`0` otherwise). -/
noncomputable def lneg (d : ℕ) : ℝ :=
  if h : fundNeg d ∧ 1 < d then
    haveI : NeZero d := ⟨by omega⟩
    (deriv (DirichletCharacter.LFunction (GSPrim.primitive_neg h.1).choose) 1 /
      DirichletCharacter.LFunction (GSPrim.primitive_neg h.1).choose 1).re
  else 0

theorem S_cast (Y : ℕ) (D : ℤ) :
    ∑ n ∈ Icc 1 ⌊((Y : ℕ) : ℝ)⌋₊, kron D n * (Λ n : ℂ) / n = ((S Y D : ℝ) : ℂ) := by
  rw [Nat.floor_natCast, S]; push_cast; simp only [kron_eq]

theorem re_tail {z : ℂ} {s : ℝ} {B : ℝ} (h : ‖z + (s : ℂ)‖ ≤ B) : |z.re + s| ≤ B :=
  (show |z.re + s| ≤ ‖z + s‖ by simpa using Complex.abs_re_le_norm (z + s)).trans h

/-- **CONDITIONAL (half-plane).** The tail bound for `ℓ⁺` (exponent `-1/24`). -/
theorem tail_pos : ∃ C : ℝ, 0 ≤ C ∧ ∀ d, fundPos d → 1 < d → ∀ Y : ℕ, 2 ≤ Y →
    |lpos d + S Y (d : ℤ)| ≤ C * Real.log (d + 2) * (Y : ℝ) ^ (-(1 / 24) : ℝ) := by
  obtain ⟨C, hC, hT⟩ := GSTail.logDeriv_one_tail (η := 1 / 48) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun d hd h1 Y hY => ?_⟩
  have : NeZero d := ⟨by omega⟩
  have hs := (GSPrim.primitive_pos hd h1).choose_spec
  have := GSTail.tail_of h1 (d : ℤ) _ hs.1 hs.2 hT (Y : ℝ) (by exact_mod_cast hY)
  rw [S_cast] at this
  have he : (2 * (1 / 48 : ℝ) - 1 / 12) = -(1 / 24) := by norm_num
  rw [he] at this
  simp only [lpos, hd, h1, and_self, dite_true]; exact re_tail this

/-- **CONDITIONAL (half-plane).** The tail bound for `ℓ⁻` (exponent `-1/24`). -/
theorem tail_neg : ∃ C : ℝ, 0 ≤ C ∧ ∀ d, fundNeg d → 1 < d → ∀ Y : ℕ, 2 ≤ Y →
    |lneg d + S Y (-(d : ℤ))| ≤ C * Real.log (d + 2) * (Y : ℝ) ^ (-(1 / 24) : ℝ) := by
  obtain ⟨C, hC, hT⟩ := GSTail.logDeriv_one_tail (η := 1 / 48) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun d hd h1 Y hY => ?_⟩
  have : NeZero d := ⟨by omega⟩
  have hs := (GSPrim.primitive_neg hd).choose_spec
  have := GSTail.tail_of h1 (-(d : ℤ)) _ hs.1 hs.2 hT (Y : ℝ) (by exact_mod_cast hY)
  rw [S_cast] at this
  have he : (2 * (1 / 48 : ℝ) - 1 / 12) = -(1 / 24) := by norm_num
  rw [he] at this
  simp only [lneg, hd, h1, and_self, dite_true]; exact re_tail this

theorem κ_pos : 0 < κ := by unfold κ; positivity

/-- **CONDITIONAL (half-plane). Moments of `L′/L(1, χ_d)`, d > 0.** For every `k`,
`(1/x) Σ_{1<d≤x, d fund. disc.} (Re L′/L(1,χ_d))^k → (3/π²) E[X^k]`. -/
theorem moments_pos (k : ℕ) :
    Tendsto (fun x : ℕ => (∑ d ∈ Ioc 0 x, (if fundPos d ∧ 1 < d then lpos d ^ k else 0)) / x) atTop
      (𝓝 (κ * mν k)) := by
  obtain ⟨C, hC, ht⟩ := tail_pos
  exact core fundPos (fun d => (d : ℤ)) lpos κ E mν hquant_pos C hC ht tendsto_E k

/-- **CONDITIONAL (half-plane).** The same for negative discriminants `-d`, with `ℓ⁻`. -/
theorem moments_neg (k : ℕ) :
    Tendsto (fun x : ℕ => (∑ d ∈ Ioc 0 x, (if fundNeg d ∧ 1 < d then lneg d ^ k else 0)) / x) atTop
      (𝓝 (κ * mν k)) := by
  obtain ⟨C, hC, ht⟩ := tail_neg
  exact core fundNeg (fun d => -(d : ℤ)) lneg κ E mν hquant_neg C hC ht tendsto_E k

/-- **CONDITIONAL (half-plane). Distribution of `L′/L(1, χ_d)`, d > 0.** The empirical laws converge weakly to `RandModel.ν`. -/
theorem dist_pos : Tendsto (emp fundPos lpos) atTop (𝓝 RandModel.ν) :=
  emp_tendsto fundPos lpos κ κ_pos RandModel.ν RandModel.integrable_pow_ν one_pos
    (RandModel.integrable_exp_abs_ν 1) moments_pos

/-- **CONDITIONAL (half-plane).** The same for negative discriminants: the empirical laws of `ℓ⁻` converge
weakly to `RandModel.ν`. -/
theorem dist_neg : Tendsto (emp fundNeg lneg) atTop (𝓝 RandModel.ν) :=
  emp_tendsto fundNeg lneg κ κ_pos RandModel.ν RandModel.integrable_pow_ν one_pos
    (RandModel.integrable_exp_abs_ν 1) moments_neg

end Concrete

end D2Dist
