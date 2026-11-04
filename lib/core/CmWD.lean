import Mathlib
import CmGlob
import CmLhChk3

/-! # The piecewise model with data coefficients, and the uniform pointwise bound `εw` -/

namespace CmWD

open CmW CmPoly CmLhD WeilTailB

theorem gh_chk : decide (Gh = GD) = true := by decide +kernel

def εw : ℚ := 16 / 10 ^ 10

theorem epw_chk : ((List.range 128).all fun p => decide (epw p ≤ εw)) = true := by decide +kernel

lemma epw_le (p : ℕ) (hp : p < NP) : epw p ≤ εw := by
  have h := epw_chk
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h p (List.mem_range.2 hp))

theorem w_data (p : ℕ) (hp : p < NP) {s : ℝ} (h1 : (p:ℝ) / NP ≤ s) (h2 : s ≤ ((p:ℝ) + 1) / NP) :
    |wψ (30 * s) - (hev GD (s ^ 2) - hev (LD p) s)| ≤ (εw : ℝ) := by
  have h := CmGlob.w_model p hp h1 h2
  rw [of_decide_eq_true gh_chk, CmLhChk.Lh_eq p hp] at h
  exact h.trans (by exact_mod_cast epw_le p hp)

end CmWD
