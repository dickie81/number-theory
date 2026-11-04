import Mathlib

/-! # Rational bounds on `log 3` to twenty digits

`log 2` comes from the series of `-log (1 - 1/2)` and `log (9/8)` from that of `-log (1 - 1/9)`, both through
Mathlib's `Real.abs_log_sub_add_sum_range_le`; then `log 3 = (3 log 2 + log (9/8)) / 2`. The partial sums are exact
rationals (list sums), compared with the stated bounds by kernel evaluation. -/

namespace V3Log

open Finset

/-- A list-based finite sum of rationals, which the kernel evaluates directly. -/
def lsum (n : ℕ) (f : ℕ → ℚ) : ℚ := ((List.range n).map f).sum

lemma cast_lsum (n : ℕ) (f : ℕ → ℚ) : ((lsum n f : ℚ) : ℝ) = ∑ k ∈ range n, (f k : ℝ) := by
  unfold lsum
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Rat.cast_add, ih, sum_range_succ]; simp

/-- The partial sum `∑_{i<n} x^{i+1}/(i+1)` of the series of `-log (1 - x)`. -/
def lser (x : ℚ) (n : ℕ) : ℚ := lsum n fun i => x ^ (i + 1) / (i + 1)

lemma lser_err {x : ℚ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    |(lser x n : ℝ) + Real.log (1 - x)| ≤ (x : ℝ) ^ (n + 1) / (1 - x) := by
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hx : |(x : ℝ)| < 1 := by rw [abs_of_nonneg hx0]; exact_mod_cast h1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg hx0] at h
  unfold lser; rw [cast_lsum]; push_cast; exact h

/-- `log 2 = -log (1 - 1/2)`, to within `2⁻⁸⁰`. -/
lemma log_two_near : |(lser (1 / 2) 80 : ℝ) - Real.log 2| ≤ (1 / 2 : ℝ) ^ 80 := by
  have h := lser_err (x := 1 / 2) (by norm_num) (by norm_num) 80
  have hl : Real.log (1 - ((1 / 2 : ℚ) : ℝ)) = -Real.log 2 := by
    rw [show (1 : ℝ) - ((1 / 2 : ℚ) : ℝ) = 2⁻¹ by push_cast; norm_num, Real.log_inv]
  rw [hl, ← sub_eq_add_neg] at h
  calc _ ≤ _ := h
    _ = _ := by push_cast; norm_num

/-- `log (9/8) = -log (1 - 1/9)`, to within `9⁻³⁰/8`. -/
lemma log_nine_eighths_near : |(lser (1 / 9) 30 : ℝ) - Real.log (9 / 8)| ≤ (1 / 9 : ℝ) ^ 30 / 8 := by
  have h := lser_err (x := 1 / 9) (by norm_num) (by norm_num) 30
  have hl : Real.log (1 - ((1 / 9 : ℚ) : ℝ)) = -Real.log (9 / 8) := by
    rw [show (1 : ℝ) - ((1 / 9 : ℚ) : ℝ) = (9 / 8)⁻¹ by push_cast; norm_num, Real.log_inv]
  rw [hl, ← sub_eq_add_neg] at h
  calc _ ≤ _ := h
    _ = _ := by push_cast; norm_num

/-- The bounds, twenty decimal digits apart. -/
def l3lo : ℚ := 109861228866810969139 / 10 ^ 20
def l3hi : ℚ := 109861228866810969140 / 10 ^ 20

theorem log_chk : (decide (l3lo ≤ (3 * (lser (1 / 2) 80 - (1 / 2) ^ 80) + (lser (1 / 9) 30 - (1 / 9) ^ 30 / 8)) / 2)
    && decide ((3 * (lser (1 / 2) 80 + (1 / 2) ^ 80) + (lser (1 / 9) 30 + (1 / 9) ^ 30 / 8)) / 2 ≤ l3hi)) = true := by
  decide +kernel

lemma log_three_eq : Real.log 3 = (3 * Real.log 2 + Real.log (9 / 8)) / 2 := by
  rw [Real.log_div (by norm_num) (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
    show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow, Real.log_pow]
  push_cast; ring

theorem log_three_mem : (l3lo : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ l3hi := by
  have h2 := abs_le.mp log_two_near
  have h9 := abs_le.mp log_nine_eighths_near
  have hc := log_chk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨c1, c2⟩ := hc
  have c1' := (Rat.cast_le (K := ℝ)).mpr c1
  have c2' := (Rat.cast_le (K := ℝ)).mpr c2
  push_cast at c1' c2'
  rw [log_three_eq]
  constructor <;> linarith [h2.1, h2.2, h9.1, h9.2]

end V3Log
