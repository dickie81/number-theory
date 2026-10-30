/-
# Type II for a variable times a rough cofactor

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement (`typeII_rough`). Let `L`, `w₁` and `w₂` be a route's parameters (`SieveRoute.Route`) with `RouteOK`,
and assume its Type II estimate (`hII : SieveRoute.TypeIIAt`). Fix `e₀ > 0`. There are `δ > 0` and `q₀` such that for
`q ≥ q₀` and a unit `a` mod `q`: let `m` run over `S ⊆ (P₁, P₂]` with `q^{w₁L} ≤ P₁` and `P₂ ≤ q^{w₂L}`, with
coefficients `|a_m| ≤ 1`, and let `z(m) ≥ q^{e₀}` on `S`. Then the sum over `m ∈ S` of `a_m` times the sum, over the
`k ≥ 2` with no prime factor below `z(m)` and `⌊q^L⌋ < mk ≤ ⌊2q^L⌋`, of `1[mk ≡ a] − 1[(mk, q) = 1]/φ(q)` is at most
`q^{L−δ}/φ(q)` in absolute value.

This is the stop of a branch of Buchstab's tree inside the lower window: `m` is the branch's product and the rest
of `n` is rough.

The proof:

* `rough_sum_eq_box`: by `SieveRoughTuple.sum_rough_eq`, with `K = ⌈(L + 1)/e₀⌉`, the rough `k` are the products of
  the non-increasing tuples of at most `K` primes, each at least `z(m)`. These are cut out of the box of all the
  primes up to `⌊2q^L⌋` by the sharp comparisons `PrR` (`PrR_all_iff`): the order of the tuple, its last entry at
  least `z(m)`, and the range `⌊q^L⌋ < m∏x_i ≤ ⌊2q^L⌋`.
* `SieveTypeIIU.typeII_unw` for each length, with `E₀ = 1`, `Λ₁ = L + 1` and `e₁ = e₀/2`.

The case `SieveRoute.route2333`, with `SieveRoute.typeII2333` for `hII`, gives the statements with the parameters
`L = 2333/1000` fixed.

The file imports `SieveTypeIIU.lean` and `SieveRoughTuple.lean`.
-/
import SieveTypeIIU
import SieveRoughTuple

open Real Finset Filter SieveFamily SieveRoute

namespace SieveTypeIIR

/-! ### The comparisons of a rough cofactor: order, roughness and range -/

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
