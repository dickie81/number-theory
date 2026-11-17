/-
# The number of primes in a class at the exponents `2100/1000` and `2150/1000`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. The two theorems of the library's searches led by hints, `Linnik21000.linnik_21000` and
`Linnik21500.linnik_21500`, each say that a class prime to `q` has a prime below `K·q^L`. The searches prove more
(`SieveAdCount.lean`): the primes of the class number a fixed fraction of `x/(φ(q) log x)`, at `x = q^L` for large `q`
and then for every `x ≥ K·q^L`.

* `Linnik21000.count_21000`: there are `c > 0` and `K` such that for every `q ≥ 1`, every `a` prime to `q` and every
  `x ≥ K·q^{2100/1000}` the primes `p ≤ x` with `p ≡ a (mod q)` number at least `c·x/(φ(q) log x)`.
* `Linnik21000.count_large_21000`: for large `q` and every `a` prime to `q`, the primes `p ≡ a (mod q)` with
  `q^{2100/1000} < p ≤ 2q^{2100/1000}` number at least `(1 − C)/2·x/(φ(q) log x)` at `x = q^{2100/1000}`, with
  `C = 1126600180626425749/2^60` the cost of the search (`Linnik21000.tree21000`): `(1 − C)/2 > 0.0114`.
* `Linnik21500.count_21500`, `Linnik21500.count_large_21500`: the same at `2150/1000`, with
  `C = 1093510193343867034/2^60` (`Linnik21500.tree21500`): `(1 − C)/2 > 0.0257`.

The file imports `SieveAdCount.lean`, `Linnik21000.lean` and `Linnik21500.lean`.
-/
import SieveAdCount
import Linnik21000
import Linnik21500

namespace Linnik21000

open SieveCert SieveRoute SieveQ SieveAd

section

attribute [local instance] route21000 routeOK21000 ibPar21000 ibFits21000

/-- **Primes in every class, in number, at the exponent `2100/1000`**: there are `c > 0` and `K` such that for every
`q ≥ 1`, every `a` prime to `q` and every `x ≥ K·q^{2100/1000}` the primes `p ≤ x` with `p ≡ a (mod q)` number at
least `c·x/(φ(q) log x)`. -/
theorem count_21000 : ∃ c K : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q → ∀ x : ℝ,
    K * (q : ℝ) ^ (2100 / 1000 : ℝ) ≤ x →
      c * x / (q.totient * Real.log x) ≤
        (((Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]).card : ℝ) :=
  count_pr sound21000 33536647203 ⟨2, 0, 0, 0, true⟩ (by decide) (by decide +kernel) tree21000 (by decide)

/-- **The primes of a class in `(q^L, 2q^L]` at `L = 2100/1000`**: for large `q` and every `a` prime to `q` they
number at least `(1 − C)/2·q^L/(φ(q) log q^L)`, with `C = 1126600180626425749/2^60` the cost of the search. -/
theorem count_large_21000 : ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ a : ℕ, a.Coprime q →
    (1 - 1126600180626425749 / 2 ^ 60) / 2 * (q : ℝ) ^ (2100 / 1000 : ℝ) /
        (q.totient * Real.log ((q : ℝ) ^ (2100 / 1000 : ℝ))) ≤
      (((Finset.Ioc ⌊(q : ℝ) ^ (2100 / 1000 : ℝ)⌋₊ ⌊2 * (q : ℝ) ^ (2100 / 1000 : ℝ)⌋₊).filter
        fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]).card : ℝ) := by
  obtain ⟨q₀, h⟩ := count_large_pr sound21000 33536647203 ⟨2, 0, 0, 0, true⟩ (by decide) (by decide +kernel)
    tree21000 (by decide)
  refine ⟨q₀, fun q _ hq a ha => le_trans (le_of_eq ?_) (h q hq a ha)⟩
  rw [show ((K : ℕ) : ℝ) = 2 ^ 60 by norm_num [SieveCert.K], Nat.cast_ofNat]
  rfl

end

end Linnik21000

namespace Linnik21500

open SieveCert SieveRoute SieveQ SieveAd

section

attribute [local instance] route21500 routeOK21500 ibPar21500 ibFits21500

/-- **Primes in every class, in number, at the exponent `2150/1000`**: there are `c > 0` and `K` such that for every
`q ≥ 1`, every `a` prime to `q` and every `x ≥ K·q^{2150/1000}` the primes `p ≤ x` with `p ≡ a (mod q)` number at
least `c·x/(φ(q) log x)`. -/
theorem count_21500 : ∃ c K : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q → ∀ x : ℝ,
    K * (q : ℝ) ^ (2150 / 1000 : ℝ) ≤ x →
      c * x / (q.totient * Real.log x) ≤
        (((Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]).card : ℝ) :=
  count_pr sound21500 49170839016 ⟨2, 0, 0, 0, true⟩ (by decide) (by decide +kernel) tree21500 (by decide)

/-- **The primes of a class in `(q^L, 2q^L]` at `L = 2150/1000`**: for large `q` and every `a` prime to `q` they
number at least `(1 − C)/2·q^L/(φ(q) log q^L)`, with `C = 1093510193343867034/2^60` the cost of the search. -/
theorem count_large_21500 : ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ a : ℕ, a.Coprime q →
    (1 - 1093510193343867034 / 2 ^ 60) / 2 * (q : ℝ) ^ (2150 / 1000 : ℝ) /
        (q.totient * Real.log ((q : ℝ) ^ (2150 / 1000 : ℝ))) ≤
      (((Finset.Ioc ⌊(q : ℝ) ^ (2150 / 1000 : ℝ)⌋₊ ⌊2 * (q : ℝ) ^ (2150 / 1000 : ℝ)⌋₊).filter
        fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]).card : ℝ) := by
  obtain ⟨q₀, h⟩ := count_large_pr sound21500 49170839016 ⟨2, 0, 0, 0, true⟩ (by decide) (by decide +kernel)
    tree21500 (by decide)
  refine ⟨q₀, fun q _ hq a ha => le_trans (le_of_eq ?_) (h q hq a ha)⟩
  rw [show ((K : ℕ) : ℝ) = 2 ^ 60 by norm_num [SieveCert.K], Nat.cast_ofNat]
  rfl

end

end Linnik21500

#print axioms Linnik21000.count_21000
#print axioms Linnik21000.count_large_21000
#print axioms Linnik21500.count_21500
#print axioms Linnik21500.count_large_21500
