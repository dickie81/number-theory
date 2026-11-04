import Mathlib

/-! Real-character form of Theorem B: closed-form thresholds and the exact criterion. -/

namespace D2Criterion
open Real

/-- Even tail: `T0 = 1/2 + (1/4) log (1/2) - (3/4) log (3/2)`, `C0 = 1 - log 2`,
`c0 = ½(ψ(½)+γ+log 2) + (½ - ½ log 2) - C0 + T0` with `ψ(½)+γ = -2 log 2`. -/
theorem c0_closed :
    (1/2) * (-2 * log 2 + log 2) + (1/2 - 1/2 * log 2) - (1 - log 2)
      + (1/2 + 1/4 * log (1/2) - 3/4 * log (3/2)) = -(1/4) * log (27/4) := by
  have h1 : log (1/2 : ℝ) = - log 2 := by rw [one_div, log_inv]
  have h2 : log (3/2 : ℝ) = log 3 - log 2 := log_div (by norm_num) (by norm_num)
  have h3 : log (27/4 : ℝ) = 3 * log 3 - 2 * log 2 := by
    rw [log_div (by norm_num) (by norm_num), show (27:ℝ) = 3^3 by norm_num,
      show (4:ℝ) = 2^2 by norm_num, log_pow, log_pow]; push_cast; ring
  rw [h1, h2, h3]; ring

/-- Odd: `c1 = ½(ψ(1)+γ+log 2) - log 2 + T1`, `T1 = ½ artanh ½ + ½ log (3/4)`,
with `artanh ½ = ½ log 3`. -/
theorem c1_closed :
    (1/2) * (0 + log 2) - log 2 + (1/2 * (1/2 * log 3) + 1/2 * log (3/4))
      = (3/4) * log (3/4) := by
  have h : log (3/4 : ℝ) = log 3 - 2 * log 2 := by
    rw [log_div (by norm_num) (by norm_num), show (4:ℝ) = 2^2 by norm_num, log_pow]; push_cast; ring
  rw [h]; ring

/-- Theorem B for a real character: with `K1 > 0` and `K2 = √2 (K1/2 + c + ℓ/2)`,
`d₂/d₁ = 2(1 - K2²/K1²) ≥ 1` iff `-2K1 - 2c ≤ ℓ ≤ -2c`. -/
theorem criterion (K1 c l : ℝ) (hK : 0 < K1) :
    1 ≤ 2 * (1 - (√2 * (K1/2 + c + l/2))^2 / K1^2) ↔ -2*K1 - 2*c ≤ l ∧ l ≤ -2*c := by
  have hs : (√2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  rw [mul_pow, hs]
  have hK2 : 0 < K1^2 := by positivity
  constructor
  · intro h
    have : 2 * (K1/2 + c + l/2)^2 ≤ K1^2 / 2 := by
      have := h; rw [show 2 * (1 - 2 * (K1/2+c+l/2)^2 / K1^2)
        = 2 - 4 * (K1/2+c+l/2)^2 / K1^2 by ring] at this
      have h' : 4 * (K1/2+c+l/2)^2 / K1^2 ≤ 1 := by linarith
      rw [div_le_one hK2] at h'; linarith
    have hsq : (K1 + 2*c + l)^2 ≤ K1^2 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (K1 + 2*c + l - K1), sq_nonneg (K1+2*c+l+K1)]
  · rintro ⟨h1, h2⟩
    have hsq : (K1 + 2*c + l)^2 ≤ K1^2 := by nlinarith
    rw [show 2 * (1 - 2 * (K1/2+c+l/2)^2 / K1^2)
        = 2 - (K1 + 2*c + l)^2 / K1^2 by field_simp]
    have : (K1 + 2*c + l)^2 / K1^2 ≤ 1 := (div_le_one hK2).2 hsq
    linarith

end D2Criterion

#print axioms D2Criterion.criterion
#print axioms D2Criterion.c0_closed
#print axioms D2Criterion.c1_closed
