/-
# Lucas's primality test with small witnesses

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `ε > 0` there is `C` such that an integer `n ≥ 2` is prime if and only if some `a ≤ Cn^ε`
passes Lucas's test: `a^{n−1} ≡ 1` and `a^{(n−1)/r} ≢ 1 (mod n)` for every prime `r ∣ n − 1`
(`prime_iff_exists_lucas_le_rpow`). For `n = 2r + 1` with `r` an odd prime, `a ≤ C(log(n + 2))^A` suffices, for every
`A > 12` (`prime_iff_exists_lucas_le_safe`). No hypothesis.

Given the prime factors of `n − 1`, this is a deterministic primality test that tries the `a ≤ Cn^ε`; for
`n = 2r + 1` it tries `C(log n)^A` of them, in polynomial time. Under GRH the witnesses are at most `(log n)^6`
(V. Shoup, 1992).

* `lucas_of_orderOf_eq`: a primitive root mod `n` passes the test, since `(n − 1)/r < n − 1` cannot be a multiple of
  its order.
* Mathlib's `lucas_primality` is the other direction: an `a` that passes the test has order `n − 1`, so `n` is prime.
* The witnesses are the prime primitive roots of `LeastPrimitiveRoot.exists_prime_primRoot_le_rpow_prime` and
  `LeastPrimitiveRoot.exists_prime_primRoot_le_safe`.
-/
import LeastPrimitiveRoot

namespace LucasWitness

/-- A primitive root mod `n` passes Lucas's test: `a^{n−1} = 1`, and `a^{(n−1)/r} ≠ 1` for every prime `r ∣ n − 1`. -/
lemma lucas_of_orderOf_eq {n : ℕ} (hn : 2 ≤ n) {a : ZMod n} (h : orderOf a = n - 1) :
    a ^ (n - 1) = 1 ∧ ∀ r : ℕ, r.Prime → r ∣ n - 1 → a ^ ((n - 1) / r) ≠ 1 := by
  refine ⟨by rw [← h]; exact pow_orderOf_eq_one a, fun r hr hrn h1 ↦ ?_⟩
  have hpos : 0 < n - 1 := by omega
  have hdvd : n - 1 ∣ (n - 1) / r := by
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rwa [h] at h2
  have hq : 0 < (n - 1) / r := Nat.div_pos (Nat.le_of_dvd hpos hrn) hr.pos
  exact absurd (Nat.le_of_dvd hq hdvd) (not_le.2 (Nat.div_lt_self hpos hr.one_lt))

/-- **Lucas's test with small witnesses.** For every `ε > 0` there is `C > 0` such that an integer `n ≥ 2` is prime if
and only if some `a ≤ Cn^ε` has `a^{n−1} ≡ 1 (mod n)` and `a^{(n−1)/r} ≢ 1 (mod n)` for every prime `r ∣ n − 1`. -/
theorem prime_iff_exists_lucas_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → (n.Prime ↔ ∃ a : ℕ, (a : ℝ) ≤ C * (n : ℝ) ^ ε ∧
      (a : ZMod n) ^ (n - 1) = 1 ∧ ∀ r : ℕ, r.Prime → r ∣ n - 1 → (a : ZMod n) ^ ((n - 1) / r) ≠ 1) := by
  obtain ⟨C, hC, h⟩ := LeastPrimitiveRoot.exists_prime_primRoot_le_rpow_prime hε
  refine ⟨C, hC, fun n hn ↦ ⟨fun hp ↦ ?_, fun ⟨a, _, ha, hd⟩ ↦ lucas_primality n a ha hd⟩⟩
  obtain ⟨ℓ, -, -, hord, hle⟩ := h n hp
  exact ⟨ℓ, hle, lucas_of_orderOf_eq hn hord⟩

/-- **Lucas's test for `2r + 1` in polynomial time.** For every `A > 12` there is `C > 0` such that for every odd prime
`r`, `n = 2r + 1` is prime if and only if some `a ≤ C(log(n + 2))^A` has `a^{n−1} ≡ 1 (mod n)` and
`a^{(n−1)/s} ≢ 1 (mod n)` for every prime `s ∣ n − 1`, that is for `s = 2` and `s = r`. -/
theorem prime_iff_exists_lucas_le_safe {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n r : ℕ, r.Prime → r ≠ 2 → n = 2 * r + 1 → (n.Prime ↔ ∃ a : ℕ,
      (a : ℝ) ≤ C * Real.log (n + 2) ^ A ∧
      (a : ZMod n) ^ (n - 1) = 1 ∧ ∀ s : ℕ, s.Prime → s ∣ n - 1 → (a : ZMod n) ^ ((n - 1) / s) ≠ 1) := by
  obtain ⟨C, hC, h⟩ := LeastPrimitiveRoot.exists_prime_primRoot_le_safe hA
  refine ⟨C, hC, fun n r hr hr2 hnr ↦ ⟨fun hp ↦ ?_, fun ⟨a, _, ha, hd⟩ ↦ lucas_primality n a ha hd⟩⟩
  obtain ⟨ℓ, -, hord, hle⟩ := h n r hr hr2 hnr hp
  exact ⟨ℓ, hle, lucas_of_orderOf_eq hp.two_le hord⟩

end LucasWitness

#print axioms LucasWitness.prime_iff_exists_lucas_le_rpow
#print axioms LucasWitness.prime_iff_exists_lucas_le_safe
