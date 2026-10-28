/-
# Buchstab's `ω` on `[2, 3]`, and the logarithm's bounds of the certificate's cells

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements, about real numbers. `SieveCert.lean` uses them for the certificate's bounds (`omegaC_le_w`,
`bound2_ge`) and `SieveRough.lean` for Buchstab's induction (`psi_le`) and the cells' prime sums.

* `log_le_half_sub_inv`, `two_mul_div_le_log`: for `y ≥ 1`, `2(y − 1)/(y + 1) ≤ log y ≤ (y − 1/y)/2`, from
  `x ≤ sinh x` at `x = log y` and from the first term of `log((1 + z)/(1 − z)) = 2(z + z³/3 + ⋯)` at
  `z = (y − 1)/(y + 1)`. At `y = 1 + w/a` they are `2w/(2a + w) ≤ log(1 + w/a) ≤ w(2a + w)/(2a(a + w))`, the bounds of
  a cell's `Σ 1/p` from below and above (the trapezoid rule for `∫ dt/t`).
* `omB u = (1 + log(u − 1))/u`, Buchstab's `ω` on `[2, 3]`: `omB_le_w1` (`omB ≤ 0.5671433` for `u > 1`, by the tangent
  line of `log` at `1/0.5671433`, since `0.5671433·e^{0.5671433} ≥ 1`); `omB_mono` (it increases on `[2, 2.76]`, from
  `log 1.76 ≤ 1/1.76`) and `omB_anti` (it decreases from `2.77` on, from `log 1.77 ≥ 1/1.77`).
* `lnT_ge`: `log((16 + k)/16) ≤ lnT k/LD` for `k ≤ 16`, each from the exponential's series to degree `13`.
* `omB_le_tab`, `omF_ge`: for `2Q ≤ P ≤ 3Q`, `omB(P/Q) ≤ omF P Q/K`: with `v = P/Q` and `r = (16 + k)/16 ≤ v − 1`
  (`k = ⌊16(v − 2)⌋`), `log(v − 1) = log r + log y ≤ lnT k/LD + (y − 1/y)/2` for `y = (v − 1)/r`.

The file imports Mathlib and `SieveCertDefs.lean` (for `lnT`, `omF` and `K`).
-/
import Mathlib
import SieveCertDefs

open Real

namespace SieveOmegaB

/-! ### The logarithm between two rational functions -/

/-- `log y ≤ (y − 1/y)/2` for `y ≥ 1`: `x ≤ sinh x` at `x = log y`. -/
theorem log_le_half_sub_inv {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ (y - y⁻¹) / 2 := by
  have hy0 : 0 < y := by linarith
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hy)
  rwa [Real.sinh_eq, Real.exp_neg, Real.exp_log hy0] at h

/-- `2(y − 1)/(y + 1) ≤ log y` for `y ≥ 1`: the first term of `log(1 + z) − log(1 − z) = 2(z + z³/3 + ⋯)` at
`z = (y − 1)/(y + 1)`. -/
theorem two_mul_div_le_log {y : ℝ} (hy : 1 ≤ y) : 2 * (y - 1) / (y + 1) ≤ Real.log y := by
  have hy1 : 0 < y + 1 := by linarith
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = (y - 1) / (y + 1) := ⟨_, rfl⟩
  have hz0 : 0 ≤ z := by rw [hz]; exact div_nonneg (by linarith) hy1.le
  have hz1 : z < 1 := by rw [hz, div_lt_one hy1]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one (x := z) (by rw [abs_lt]; constructor <;> linarith)
  have h0 := le_hasSum hs 0 (fun k _ => mul_nonneg (by positivity) (pow_nonneg hz0 _))
  have hl : Real.log (1 + z) - Real.log (1 - z) = Real.log y := by
    rw [← Real.log_div (by linarith) (by linarith)]
    congr 1
    rw [hz]
    field_simp
    ring
  rw [hl] at h0
  norm_num at h0
  calc 2 * (y - 1) / (y + 1) = 2 * z := by rw [hz]; ring
    _ ≤ _ := h0

/-! ### Buchstab's `ω` on `[2, 3]` -/

/-- Buchstab's `ω` on `[2, 3]`: `(1 + log(u − 1))/u`. -/
noncomputable def omB (u : ℝ) : ℝ := (1 + Real.log (u - 1)) / u

/-- `log 0.5671433 ≥ −0.5671433`, from `0.5671433·e^{0.5671433} ≥ 1` (the exponential's series to degree `12`). -/
theorem log_w1_ge : -(5671433 / 10000000 : ℝ) ≤ Real.log (5671433 / 10000000) := by
  have hc : (0 : ℝ) ≤ 5671433 / 10000000 := by norm_num
  have hexp := Real.sum_le_exp_of_nonneg hc 13
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hexp
  norm_num at hexp
  have h1 : (10000000 / 5671433 : ℝ) ≤ Real.exp (5671433 / 10000000) := by linarith
  have h2 : Real.log (10000000 / 5671433) ≤ 5671433 / 10000000 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; exact h1
  have h3 : Real.log (10000000 / 5671433 : ℝ) = -Real.log (5671433 / 10000000) := by
    rw [show (10000000 / 5671433 : ℝ) = (5671433 / 10000000)⁻¹ by norm_num, Real.log_inv]
  linarith

/-- `1 + log(u − 1) ≤ 0.5671433u` for `u > 1`, by the tangent line of `log` at `1/0.5671433`. -/
theorem one_add_log_le_w1 {u : ℝ} (hu : 1 < u) : 1 + Real.log (u - 1) ≤ 5671433 / 10000000 * u := by
  have hc : (0 : ℝ) < 5671433 / 10000000 := by norm_num
  have h1 : Real.log (5671433 / 10000000 * (u - 1)) ≤ 5671433 / 10000000 * (u - 1) - 1 :=
    Real.log_le_sub_one_of_pos (by nlinarith)
  rw [Real.log_mul hc.ne' (by linarith)] at h1
  linarith [log_w1_ge]

/-- **The maximum of Buchstab's `ω` on `[2, 3]`**: `omB u ≤ 0.5671433` for `u > 1`. -/
theorem omB_le_w1 {u : ℝ} (hu : 1 < u) : omB u ≤ 5671433 / 10000000 := by
  rw [omB, div_le_iff₀ (by linarith)]
  linarith [one_add_log_le_w1 hu]

/-- `ω(3) = (1 + log 2)/3 ≤ 0.565073`. -/
theorem omB_three_le : omB 3 ≤ 565073 / 1000000 := by
  have h := Real.log_two_lt_d9
  rw [omB, div_le_iff₀ (by norm_num)]
  norm_num at h ⊢
  linarith

/-- `omB u ≥ 0` for `u ≥ 2`. -/
theorem omB_nonneg {u : ℝ} (hu : 2 ≤ u) : 0 ≤ omB u := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ u - 1 by linarith)
  rw [omB]; positivity

/-- `log 1.76 ≤ 1/1.76`, from `e^{1/1.76} ≥ 1.76` (the exponential's series to degree `7`). -/
theorem log_176_le : Real.log (176 / 100) ≤ 100 / 176 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 100 / 176 by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- `1/1.77 ≤ log 1.77`, from `e^{1/1.77} ≤ 1.77` (Mathlib's `Real.exp_bound'` at degree `8`). -/
theorem log_177_ge : 100 / 177 ≤ Real.log (177 / 100) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_bound' (x := 100 / 177) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- **Buchstab's `ω` increases on `[2, 2.76]`.** For `2 ≤ u ≤ v ≤ 2.76`, `(v − u)(1 + log(u − 1)) ≤
u·log((v − 1)/(u − 1))`: the left side is at most `(v − u)u/1.76` (the tangent line of `log` at `1.76`, and
`log 1.76 ≤ 1/1.76`), and the right side at least `u(v − u)/(v − 1)`. -/
theorem omB_mono {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) (hv : v ≤ 276 / 100) : omB u ≤ omB v := by
  have hu1 : 0 < u - 1 := by linarith
  have hv1 : 0 < v - 1 := by linarith
  have hA : 1 + Real.log (u - 1) ≤ u * (100 / 176) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (u - 1) / (176 / 100) by positivity)
    rw [Real.log_div hu1.ne' (by norm_num)] at h
    have := log_176_le
    have e : (u - 1) / (176 / 100) = (u - 1) * (100 / 176) := by ring
    rw [e] at h
    linarith
  have hB : (v - u) / (v - 1) ≤ Real.log (v - 1) - Real.log (u - 1) := by
    rw [← Real.log_div hv1.ne' hu1.ne']
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < (v - 1) / (u - 1) by positivity)
    have e : 1 - ((v - 1) / (u - 1))⁻¹ = (v - u) / (v - 1) := by field_simp; ring
    linarith
  have hC : u * (100 / 176) ≤ u / (v - 1) := by
    rw [le_div_iff₀ hv1]; nlinarith
  have hD : (v - u) * (1 + Real.log (u - 1)) ≤ u * (Real.log (v - 1) - Real.log (u - 1)) := by
    have h1 : (v - u) * (1 + Real.log (u - 1)) ≤ (v - u) * (u / (v - 1)) :=
      mul_le_mul_of_nonneg_left (hA.trans hC) (by linarith)
    have h2 : (v - u) * (u / (v - 1)) = u * ((v - u) / (v - 1)) := by ring
    have h3 : u * ((v - u) / (v - 1)) ≤ u * (Real.log (v - 1) - Real.log (u - 1)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    linarith
  rw [omB, omB, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Buchstab's `ω` decreases from `2.77` on.** For `2.77 ≤ u ≤ v`, `u·log((v − 1)/(u − 1)) ≤
(v − u)(1 + log(u − 1))`: the left side is at most `u(v − u)/(u − 1)`, and `1/(u − 1) ≤ log(u − 1)` there. -/
theorem omB_anti {u v : ℝ} (hu : 277 / 100 ≤ u) (huv : u ≤ v) : omB v ≤ omB u := by
  have hu1 : 0 < u - 1 := by linarith
  have hv1 : 0 < v - 1 := by linarith
  have hA : 1 / (u - 1) ≤ Real.log (u - 1) := by
    have h1 : 1 / (u - 1) ≤ 100 / 177 := by rw [div_le_div_iff₀ hu1 (by norm_num)]; linarith
    have h2 : Real.log (177 / 100) ≤ Real.log (u - 1) := Real.log_le_log (by norm_num) (by linarith)
    linarith [log_177_ge]
  have hB : Real.log (v - 1) - Real.log (u - 1) ≤ (v - u) / (u - 1) := by
    rw [← Real.log_div hv1.ne' hu1.ne']
    have h := Real.log_le_sub_one_of_pos (show 0 < (v - 1) / (u - 1) by positivity)
    have e : (v - 1) / (u - 1) - 1 = (v - u) / (u - 1) := by field_simp; ring
    linarith
  have hD : u * (Real.log (v - 1) - Real.log (u - 1)) ≤ (v - u) * (1 + Real.log (u - 1)) := by
    have h1 : u * (Real.log (v - 1) - Real.log (u - 1)) ≤ u * ((v - u) / (u - 1)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have h2 : u * ((v - u) / (u - 1)) = (v - u) * (1 + 1 / (u - 1)) := by field_simp; ring
    have h3 : (v - u) * (1 + 1 / (u - 1)) ≤ (v - u) * (1 + Real.log (u - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  rw [omB, omB, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ### The table of `log((16 + k)/16)` and the bound `omF` -/

/-- `log r ≤ x` when `r` is at most the exponential's series at `x ≥ 0` to degree `13`. -/
theorem log_le_of_series {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x)
    (h : r ≤ ∑ i ∈ Finset.range 14, x ^ i / (i.factorial : ℝ)) : Real.log r ≤ x :=
  (Real.log_le_iff_le_exp hr).2 (h.trans (Real.sum_le_exp_of_nonneg hx 14))

/-- **The table**: `log((16 + k)/16) ≤ lnT k/LD` for `k ≤ 16`. -/
theorem lnT_ge {k : ℕ} (hk : k ≤ 16) :
    Real.log ((16 + k) / 16) ≤ (SieveCert.lnT k : ℝ) / SieveCert.LD := by
  interval_cases k <;>
    exact log_le_of_series (by norm_num) (by positivity)
      (by norm_num [SieveCert.lnT, SieveCert.LD, Finset.sum_range_succ, Nat.factorial])

/-- **Buchstab's `ω` from the table**, in the reals: for `v ≥ 2` and `1 ≤ r ≤ v − 1` with `log r ≤ ℓ`,
`omB v ≤ (1 + ℓ + (y − 1/y)/2)/v`, `y = (v − 1)/r`. -/
theorem omB_le_tab {v r ℓ : ℝ} (hv : 2 ≤ v) (hr : 1 ≤ r) (hrv : r ≤ v - 1) (hℓ : Real.log r ≤ ℓ) :
    omB v ≤ (1 + ℓ + ((v - 1) / r - r / (v - 1)) / 2) / v := by
  have hv1 : 0 < v - 1 := by linarith
  have hr0 : 0 < r := by linarith
  have hy : 1 ≤ (v - 1) / r := by rw [le_div_iff₀ hr0]; linarith
  have h1 := log_le_half_sub_inv hy
  rw [inv_div] at h1
  have h2 : Real.log (v - 1) = Real.log r + Real.log ((v - 1) / r) := by
    rw [Real.log_div hv1.ne' hr0.ne']; ring
  rw [omB]
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

/-- Division rounded up bounds the quotient. -/
theorem div_le_cdiv (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ SieveCert.cdiv a b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have h2 : a ≤ SieveCert.cdiv a b * b := by
    unfold SieveCert.cdiv
    have := Nat.lt_div_mul_add (a := a + b - 1) hb
    omega
  exact_mod_cast h2

/-- **`omF` bounds Buchstab's `ω`**: for `0 < Q` and `2Q ≤ P ≤ 3Q`, `omB(P/Q) ≤ omF P Q/K`. -/
theorem omF_ge {P Q : ℕ} (hQ : 0 < Q) (h2 : 2 * Q ≤ P) (h3 : P ≤ 3 * Q) :
    omB ((P : ℝ) / Q) ≤ (SieveCert.omF P Q : ℝ) / SieveCert.K := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hP0 : 0 < P := by omega
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP0
  have hK : (0 : ℝ) < SieveCert.K := by norm_num [SieveCert.K]
  have hLD0 : 0 < SieveCert.LD := by norm_num [SieveCert.LD]
  have hLD : (0 : ℝ) < SieveCert.LD := by exact_mod_cast hLD0
  obtain ⟨k, hk⟩ : ∃ k, k = 16 * (P - 2 * Q) / Q := ⟨_, rfl⟩
  have hkQ : k * Q ≤ 16 * (P - 2 * Q) := by rw [hk]; exact Nat.div_mul_le_self _ _
  have hk16 : k ≤ 16 := by
    rw [hk]; apply Nat.div_le_of_le_mul; omega
  have hPQ : ((P - 2 * Q : ℕ) : ℝ) = (P : ℝ) - 2 * Q := by rw [Nat.cast_sub h2]; push_cast; ring
  have hPQ1 : ((P - Q : ℕ) : ℝ) = (P : ℝ) - Q := by rw [Nat.cast_sub (by omega)]
  have hkQ' : (k : ℝ) * Q ≤ 16 * ((P : ℝ) - 2 * Q) := by
    have : ((k * Q : ℕ) : ℝ) ≤ ((16 * (P - 2 * Q) : ℕ) : ℝ) := by exact_mod_cast hkQ
    rw [Nat.cast_mul, Nat.cast_mul, hPQ] at this
    push_cast at this
    linarith
  have hQP : (Q : ℝ) < P := by
    have : ((2 * Q : ℕ) : ℝ) ≤ P := by exact_mod_cast h2
    push_cast at this; linarith
  have hv2 : 2 ≤ (P : ℝ) / Q := by
    rw [le_div_iff₀ hQ']
    have : ((2 * Q : ℕ) : ℝ) ≤ P := by exact_mod_cast h2
    push_cast at this; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr1 : (1 : ℝ) ≤ (16 + k) / 16 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hsub : (P : ℝ) / Q - 1 = ((P : ℝ) - Q) / Q := by field_simp
  have hrv : (16 + (k : ℝ)) / 16 ≤ (P : ℝ) / Q - 1 := by
    rw [hsub, div_le_div_iff₀ (by norm_num) hQ']
    nlinarith
  have hmain := omB_le_tab hv2 hr1 hrv (lnT_ge hk16)
  -- the naturals `A = 16(P − Q)` and `B = (16 + k)Q` of `omFk`
  obtain ⟨A, hA⟩ : ∃ A, A = 16 * (P - Q) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (16 + k) * Q := ⟨_, rfl⟩
  have hBA : B ≤ A := by rw [hA, hB, add_mul]; omega
  have hBBAA : B * B ≤ A * A := Nat.mul_le_mul hBA hBA
  have hA0 : 0 < A := by rw [hA]; omega
  have hB0 : 0 < B := by rw [hB]; positivity
  have hAR : (A : ℝ) = 16 * ((P : ℝ) - Q) := by rw [hA, Nat.cast_mul, hPQ1]; norm_num
  have hBR : (B : ℝ) = (16 + k) * Q := by rw [hB]; push_cast; ring
  have homF : SieveCert.omF P Q = SieveCert.cdiv
      (SieveCert.K * Q * (2 * A * B * (SieveCert.LD + SieveCert.lnT k) + (A * A - B * B) * SieveCert.LD))
      (2 * A * B * SieveCert.LD * P) := by
    simp only [SieveCert.omF, SieveCert.omFk]
    rw [← hk, ← hA, ← hB]
  have hden : 0 < 2 * A * B * SieveCert.LD * P := by positivity
  rw [homF]
  refine hmain.trans (le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (div_le_cdiv _ _ hden) hK.le))
  have hPQ0 : (P : ℝ) - Q ≠ 0 := by linarith
  have h16k : (16 : ℝ) + k ≠ 0 := by linarith
  rw [hsub]
  push_cast [Nat.cast_sub hBBAA]
  rw [hAR, hBR]
  field_simp

end SieveOmegaB
