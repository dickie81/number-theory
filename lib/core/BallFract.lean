/-
# The prime part of the Gram matrix: an integral part and the fractional parts

Plain statement. For `k ≥ 1` the prime part `P(k) = Σ_{j ≤ k} Λ(j)(k/j − 1)` of `G(k, 1)` (`BallPrimes.primePart`)
splits as `P(k) = log k! − ψ(k) + C(k)` (`primePart_split`), where
* `log k! = Σ_{j ≤ k} Λ(j)⌊k/j⌋` (`log_factorial_eq`, Chebyshev's identity), the logarithm of an integer, like
  `ψ(k) = log lcm(1, …, k)`;
* `C(k) = Σ_{j ≤ k} Λ(j)·{k/j}` (`fracPart`) collects the fractional parts, with `0 ≤ C(k) ≤ ψ(k)`
  (`fracPart_nonneg`, `fracPart_le_psi`), so `C(k) ≤ k·log 4 + 2√k·log k` (`fracPart_le`, from Mathlib's Chebyshev
  bound).
So `G(k, 1) = log k! − ψ(k) + C(k) + ((k + 1)/2)K₁ + ((k − 1)/2)(log π − 2 log k) + √k·A(log k)` (`gram_split`): an
integral part (`log k!` and `ψ(k)`, logarithms of integers), the explicit pole and archimedean terms, and the
fractional-part correction `C(k)`.
-/
import Mathlib
import BallPrimes

open Real Finset

noncomputable section

namespace BallFract

open BallWeil BallPsi BallPrimes ArithmeticFunction

lemma log_factorial_sum (k : ℕ) : Real.log (k.factorial : ℝ) = ∑ n ∈ Ioc 0 k, Real.log n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Ioc_succ_top (Nat.zero_le k), add_comm]

/-- **Chebyshev's identity**: `log k! = Σ_{j ≤ k} Λ(j)⌊k/j⌋`. -/
theorem log_factorial_eq (k : ℕ) :
    Real.log (k.factorial : ℝ) = ∑ j ∈ Ioc 0 k, Λ j * ((k / j : ℕ) : ℝ) := by
  rw [log_factorial_sum]
  have h : ∀ n ∈ Ioc 0 k, Real.log n = ∑ d ∈ Ioc 0 k, if d ∣ n then Λ d else 0 := by
    intro n hn
    obtain ⟨h0, hk⟩ := mem_Ioc.1 hn
    rw [← vonMangoldt_sum, ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd h0, (Nat.le_of_dvd h0 hd).trans hk⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, h0.ne'⟩
  rw [sum_congr rfl h, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

/-- The fractional-part correction `C(k) = Σ_{j ≤ k} Λ(j)·(k/j − ⌊k/j⌋)`. -/
def fracPart (k : ℕ) : ℝ := ∑ j ∈ Ioc 0 k, Λ j * ((k : ℝ) / j - ((k / j : ℕ) : ℝ))

lemma frac_bounds {k j : ℕ} (hj : 0 < j) :
    0 ≤ (k : ℝ) / j - ((k / j : ℕ) : ℝ) ∧ (k : ℝ) / j - ((k / j : ℕ) : ℝ) ≤ 1 := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  refine ⟨sub_nonneg.2 Nat.cast_div_le, ?_⟩
  have h : k < k / j * j + j := Nat.lt_div_mul_add hj
  have h' : (k : ℝ) ≤ ((k / j : ℕ) : ℝ) * j + j := by exact_mod_cast h.le
  rw [sub_le_iff_le_add, div_le_iff₀ hj0]
  linarith

theorem fracPart_nonneg (k : ℕ) : 0 ≤ fracPart k :=
  sum_nonneg fun _ hj => mul_nonneg vonMangoldt_nonneg (frac_bounds (mem_Ioc.1 hj).1).1

lemma psi_nat (k : ℕ) : Chebyshev.psi (k : ℝ) = ∑ j ∈ Ioc 0 k, Λ j := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have e : Icc 0 k = insert 0 (Ioc 0 k) := by ext; simp
  rw [e, sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]

theorem fracPart_le_psi (k : ℕ) : fracPart k ≤ Chebyshev.psi k := by
  rw [psi_nat]
  refine sum_le_sum fun j hj => ?_
  have := frac_bounds (k := k) (mem_Ioc.1 hj).1
  nlinarith [vonMangoldt_nonneg (n := j)]

/-- **An explicit bound**: `C(k) ≤ k·log 4 + 2√k·log k` for `k ≥ 1`. -/
theorem fracPart_le {k : ℕ} (hk : 1 ≤ k) :
    fracPart k ≤ Real.log 4 * k + 2 * Real.sqrt k * Real.log k :=
  (fracPart_le_psi k).trans (Chebyshev.psi_le (by exact_mod_cast hk))

/-- **The split**: `P(k) = log k! − ψ(k) + C(k)`. -/
theorem primePart_split (k : ℕ) :
    primePart k = Real.log (k.factorial : ℝ) - Chebyshev.psi k + fracPart k := by
  rw [log_factorial_eq, psi_nat]
  unfold primePart fracPart
  rw [← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **`G(k, 1)` as an integral part plus the fractional-part correction.** -/
theorem gram_split {k : ℕ} (hk : 1 ≤ k) :
    gram k 1 = Real.log (k.factorial : ℝ) - Chebyshev.psi k + fracPart k +
      (k + 1) / 2 * (2 + eulerMascheroniConstant - Real.log (4 * π)) +
      (k - 1) / 2 * (Real.log π - 2 * Real.log k) + Real.sqrt k * archH (Real.log k) := by
  rw [gram_explicit_int hk, primePart_split]

end BallFract

#print axioms BallFract.log_factorial_eq
#print axioms BallFract.fracPart_nonneg
#print axioms BallFract.fracPart_le
#print axioms BallFract.primePart_split
#print axioms BallFract.gram_split
