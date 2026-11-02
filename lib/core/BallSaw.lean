/-
# The fractional-part correction as a sawtooth sum

Plain statement. With the centred sawtooth `s(y) = {y} − 1/2`, `|s| ≤ 1/2`, the correction `C(k) = Σ_{j ≤ k} Λ(j){k/j}`
of `BallFract` is `C(k) = ψ(k)/2 + Σ_{j ≤ k} Λ(j)·s(k/j)` (`fracPart_saw`), with `|C(k) − ψ(k)/2| ≤ ψ(k)/2`
(`abs_fracPart_sub_le`). The Fourier series `s(y) = −Σ_{h ≥ 1} sin(2πhy)/(πh)` (not formalised) converges to `0`, not
`−1/2`, at the integers, where `j ∣ k`; the total jump is `Σ_{j ∣ k} Λ(j)/2 = (log k)/2` (`jump_eq`), so the Fourier
expansion of `C(k)` carries the exact correction `−(log k)/2`.
-/
import Mathlib
import BallFract

open Real Finset

noncomputable section

namespace BallSaw

open BallFract ArithmeticFunction

/-- The centred sawtooth at `k/j`: `k/j − ⌊k/j⌋ − 1/2`. -/
def saw (k j : ℕ) : ℝ := (k : ℝ) / j - ((k / j : ℕ) : ℝ) - 1 / 2

lemma abs_saw_le {k j : ℕ} (hj : 0 < j) : |saw k j| ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := frac_bounds (k := k) hj
  unfold saw
  rw [abs_le]
  constructor <;> linarith

/-- **`C(k) = ψ(k)/2 + Σ_{j ≤ k} Λ(j)·s(k/j)`.** -/
theorem fracPart_saw (k : ℕ) : fracPart k = Chebyshev.psi k / 2 + ∑ j ∈ Ioc 0 k, Λ j * saw k j := by
  rw [psi_nat, sum_div, ← sum_add_distrib]
  unfold fracPart saw
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **`|C(k) − ψ(k)/2| ≤ ψ(k)/2`.** -/
theorem abs_fracPart_sub_le (k : ℕ) : |fracPart k - Chebyshev.psi k / 2| ≤ Chebyshev.psi k / 2 := by
  rw [fracPart_saw, add_sub_cancel_left, psi_nat, sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
  have := abs_saw_le (k := k) (mem_Ioc.1 hj).1
  nlinarith [vonMangoldt_nonneg (n := j)]

/-- **The jump at the integers**: `Σ_{j ≤ k, j ∣ k} Λ(j) = log k`. -/
theorem jump_eq (k : ℕ) : ∑ j ∈ (Ioc 0 k).filter (· ∣ k), Λ j = Real.log k := by
  rw [← vonMangoldt_sum]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  congr 1

end BallSaw

#print axioms BallSaw.fracPart_saw
#print axioms BallSaw.abs_fracPart_sub_le
#print axioms BallSaw.jump_eq
