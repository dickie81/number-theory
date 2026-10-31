/-
# A reindexing for the tuples of a rough cofactor

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

* `sum_Icc_one`: `Σ_{n∈[1, K]} g(n) = Σ_{n<K} g(n + 1)`. `SieveChain.sum_rough_tuples` uses it with
  `SieveRoughTuple.sum_rough_eq` to write the rough `k` as the products of tuples of primes.

The file imports `SieveTypeIIU.lean` and `SieveRoughTuple.lean`.
-/
import SieveTypeIIU
import SieveRoughTuple

open Real Finset Filter SieveFamily SieveRoute

namespace SieveTypeIIR

/-! ### The reindexing -/

theorem sum_Icc_one {M : Type*} [AddCommMonoid M] (K : ℕ) (g : ℕ → M) :
    ∑ n ∈ Finset.Icc 1 K, g n = ∑ n ∈ Finset.range K, g (n + 1) := by
  have h : Finset.Icc 1 K = (Finset.range K).map (addRightEmbedding 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
    constructor
    · intro h
      exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [h, Finset.sum_map]
  rfl

section Main

open Classical

end Main

end SieveTypeIIR
