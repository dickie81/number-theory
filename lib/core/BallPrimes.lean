/-
# The Gram matrix of the orbit from the primes, at integer ratios

Plain statement. For integers `k ≥ 1` and `n ≥ 1`, with `K₁ = K_H(1) = 2 + γ − log 4π`:
* `G(kn, n) = n·G(k, 1)` (`gram_mul`), so the Gram matrix at integer ratios is fixed by `G(k, 1)`;
* `G(k, 1) = P(k) + ((k + 1)/2)·K₁ + ((k − 1)/2)·(log π − 2 log k) + √k·A(log k)` (`gram_explicit_int`), where
  `P(k) = Σ_{j ≤ k} Λ(j)(k/j − 1)` is the prime part (`primePart`) and `A = BallPsi.archH` the archimedean term;
* the prime part is additive over the primes, `P(k) = Σ_{p^a ≤ k} log p·(k/p^a − 1)`, a sum of nonnegative terms
  (`primePart_nonneg`; the regrouping by primes is the definition of `Λ`, not a separate lemma); it is a combination of
  the `log p` with rational, not integer, coefficients.
So the Gram matrix is a sum of per-prime pieces plus pole and archimedean terms, not a tensor product over the primes;
and the prime pieces enter `D_m·D_n = m + n − G(m, n)` with a fixed sign. This is the obstruction recorded in
`docs/positivity-search.md`.
-/
import Mathlib
import BallWeil

open Real Finset

noncomputable section

namespace BallPrimes

open BallWeil BallPsi

/-- **`G(jm, jn) = j·G(m, n)`.** -/
theorem gram_mul (j m n : ℕ) : gram (j * m) (j * n) = j * gram m n := by
  unfold gram
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  push_cast
  rw [show (j : ℝ) * m * (j * n) = j ^ 2 * (m * n) by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hj0.le,
    mul_div_mul_left _ _ hj0.ne']
  ring

/-- The prime part `P(k) = Σ_{j ≤ k} Λ(j)(k/j − 1)`. -/
def primePart (k : ℕ) : ℝ :=
  ∑ j ∈ Ioc 0 k, ArithmeticFunction.vonMangoldt j * ((k : ℝ) / j - 1)

/-- **The prime part is nonnegative**, termwise. -/
theorem primePart_nonneg (k : ℕ) : 0 ≤ primePart k := by
  unfold primePart
  refine sum_nonneg fun j hj => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ?_
  obtain ⟨h0, hk⟩ := mem_Ioc.1 hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast h0
  have : (1 : ℝ) ≤ k / j := by rw [le_div_iff₀ hj0]; simpa using (show (j : ℝ) ≤ k by exact_mod_cast hk)
  linarith

lemma sqrt_cosh {k : ℝ} (hk : 0 < k) : Real.sqrt k * Real.cosh (Real.log k / 2) = (k + 1) / 2 := by
  have e : Real.exp (Real.log k / 2) = Real.sqrt k := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hk]; ring_nf
  rw [Real.cosh_eq, Real.exp_neg, e]
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  field_simp
  rw [Real.sq_sqrt hk.le]

lemma sqrt_sinh {k : ℝ} (hk : 0 < k) : Real.sqrt k * Real.sinh (Real.log k / 2) = (k - 1) / 2 := by
  have e : Real.exp (Real.log k / 2) = Real.sqrt k := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hk]; ring_nf
  rw [Real.sinh_eq, Real.exp_neg, e]
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  field_simp
  rw [Real.sq_sqrt hk.le]

/-- **The Gram matrix at integer ratios from the primes**: for `k ≥ 1`,
`G(k, 1) = P(k) + ((k + 1)/2)K₁ + ((k − 1)/2)(log π − 2 log k) + √k·A(log k)`. -/
theorem gram_explicit_int {k : ℕ} (hk : 1 ≤ k) :
    gram k 1 = primePart k + (k + 1) / 2 * (2 + eulerMascheroniConstant - Real.log (4 * π)) +
      (k - 1) / 2 * (Real.log π - 2 * Real.log k) + Real.sqrt k * archH (Real.log k) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have h := kerH_explicit hk1
  rw [kerH_eq_kψ hk0] at h
  have h' := Complex.ofReal_injective h
  unfold gram
  rw [Nat.cast_one, mul_one, div_one, h', Nat.floor_natCast]
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hss : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
  have hpsi : Chebyshev.psi (k : ℝ) = ∑ j ∈ Ioc 0 k, ArithmeticFunction.vonMangoldt j := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    have e : Icc 0 k = insert 0 (Ioc 0 k) := by ext; simp
    rw [e, sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
  have hP : primePart k = k * ∑ j ∈ Ioc 0 k, ArithmeticFunction.vonMangoldt j / j -
      ∑ j ∈ Ioc 0 k, ArithmeticFunction.vonMangoldt j := by
    unfold primePart
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hP, hpsi]
  set S := ∑ j ∈ Ioc 0 k, ArithmeticFunction.vonMangoldt j / (j : ℝ)
  set P := ∑ j ∈ Ioc 0 k, ArithmeticFunction.vonMangoldt j
  set K := 2 + eulerMascheroniConstant - Real.log (4 * π)
  set L := Real.log π - 2 * Real.log k
  have e3 : Real.sqrt k * (P / Real.sqrt k) = P := mul_div_cancel₀ _ hs.ne'
  calc Real.sqrt k * (Real.cosh (Real.log k / 2) * K + Real.sinh (Real.log k / 2) * L + archH (Real.log k) +
        Real.sqrt k * S - P / Real.sqrt k)
      = (Real.sqrt k * Real.cosh (Real.log k / 2)) * K + (Real.sqrt k * Real.sinh (Real.log k / 2)) * L +
          Real.sqrt k * archH (Real.log k) + (Real.sqrt k * Real.sqrt k) * S - Real.sqrt k * (P / Real.sqrt k) := by
        ring
    _ = _ := by rw [sqrt_cosh hk0, sqrt_sinh hk0, hss, e3]; ring

end BallPrimes

#print axioms BallPrimes.gram_mul
#print axioms BallPrimes.primePart_nonneg
#print axioms BallPrimes.gram_explicit_int
