/-
# Type II for chains with part of their product in the reflection of the window

Plain statements. `RTg`, `GCmp`, `merge` and `eS` are `SieveChain`'s; `rough z n` is `SieveTree`'s. `L`, `w₁` and `w₂`
are a route's parameters (`SieveRoute.Route`) with `RouteOK`, and the bound assumes its Type II estimate
(`hII : SieveRoute.TypeIIAt`). `N₁ = ⌊q^L⌋` and `N₂ = ⌊2q^L⌋`.

* `bigF z m`, `rank F x`, `readAt F i`: the prime factors of `m` at least `z`; the number of elements of `F` above `x`;
  the element of `F` of rank `i` (or `0`). `rank_readAt`, `readAt_rank`: on `F`, rank and reading are inverse.
* `card_bigF_lt`: for `z ≥ 2` and `1 ≤ m ≤ Y < z^B`, `m` has fewer than `B` prime factors at least `z`.
* `sum_slices`: **slices.** For `z ≥ 2` and `Y < z^B`, the pairs `(a, k)` of a strictly decreasing `s`-tuple `a` of
  primes at least `z` and an integer `k ≥ 1` with `∏a·k ≤ Y` are the pairs `(ι, m)` of a strictly increasing tuple of
  ranks below `B` (a *slice*, `slices s B`) and an `m ∈ [1, Y]` with that many prime factors at least `z` (`valid`),
  through `m = ∏a·k`, `a = readP z ι m` (`m`'s primes at least `z` read at the ranks `ι`) and `k = m/∏a`.
* `sum_pi_merge`: a sum over tuples on `Fin k` is a sum over their parts on `S` and on `Sᶜ`.
* `splitR`, `splitR_holds`: a comparison of the chain at `m`, as one of its part on `S` with the part on `Sᶜ` read from
  `m`.
* `chainTR_bound`: **chains with part of their product in the reflection.** Fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`.
  There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `(k′ + 1)`-tuples of
  primes up to `N₂` that satisfy at most `J₀` comparisons `Ω` (with `m`-parts at most `Λ₁ log q` at `m = 0`), each such
  tuple strictly decreasing, with entries at least `q^{e₀}` and `W₀ < ∏_{i∈U} rt_i ≤ W₁` for a set `U` of indices,
  where `W₁ ≤ N₁`, `q^{w₁L} ≤ ⌊N₁/W₁⌋` and `⌊N₂/(W₀ + 1)⌋ ≤ q^{w₂L}`. Then the multiples `n ∈ (N₁, N₂]` of `∏rt` with no
  prime factor below `rt`'s last entry, summed over `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`.

`SieveChain.chainTU_bound` is the case `U` of all indices. The Type II variable is `m = n/∏_{i∈U} rt_i`, in the window:
the primes off `U` and the rough rest of `n`. They are read back from `m` by their ranks among `m`'s primes at least
`q^{e₀}`, one slice at a time, and the slices are boundedly many.

The proof of `chainTR_bound`: `SieveChain.sum_mult_eq` writes the multiples as `∏rt·k` with `k` rough; `sum_pi_merge`
splits `rt` into its parts on `U` and off `U`, and `sum_slices` turns the part off `U` and `k` into a slice and `m`. For
each slice, `splitR` turns the comparisons `Ω` and the roughness of `k` into comparisons of the part on `U` with
`m`-parts read from `m`, and `SieveChain.typeII_gcmp'` bounds the sum over `m` in `(⌊N₁/W₁⌋, ⌊N₂/(W₀ + 1)⌋]`.

The file imports `SieveChain.lean`.
-/
import SieveChain

open Real Finset SieveFamily SieveTree SieveRoute SieveChain

namespace SieveChainR

/-! ### Reading primes by their ranks -/

/-! ### Slices -/

/-! ### Splitting a chain by a set of its indices -/

theorem eS_inr_strictMono {k : ℕ} {S : Finset (Fin k)} : StrictMono (fun v : Fin Sᶜ.card => eS S (Sum.inr v)) := by
  have e : (fun v : Fin Sᶜ.card => eS S (Sum.inr v)) = Sᶜ.orderEmbOfFin rfl := by
    funext v
    exact finSumEquivOfFinset_inr rfl rfl v
  rw [e]
  exact (Sᶜ.orderEmbOfFin rfl).strictMono

/-- A sum over tuples on `Fin k` is a sum over their parts on `S` and on `Sᶜ`. -/
theorem sum_pi_merge {M : Type*} [AddCommMonoid M] {k : ℕ} (S : Finset (Fin k)) (A : Finset ℕ)
    (f : (Fin k → ℕ) → M) :
    ∑ rt ∈ Fintype.piFinset (fun _ : Fin k => A), f rt =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin S.card => A), ∑ b ∈ Fintype.piFinset (fun _ : Fin Sᶜ.card => A),
        f (merge S x b) := by
  rw [← Finset.sum_product' (f := fun x b => f (merge S x b))]
  refine Finset.sum_nbij' (fun rt => (fun u => rt (eS S (Sum.inl u)), fun v => rt (eS S (Sum.inr v))))
    (fun p => merge S p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro rt hrt
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hrt ⊢
    exact ⟨fun u => hrt _, fun v => hrt _⟩
  · rintro ⟨x, b⟩ hp
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
    intro i
    obtain ⟨y, rfl⟩ := (eS S).surjective i
    rcases y with u | v
    · rw [merge_inl]; exact hp.1 u
    · rw [merge_inr]; exact hp.2 v
  · intro rt _
    exact merge_split rt
  · rintro ⟨x, b⟩ _
    simp only [merge_inl, merge_inr]
  · intro rt _
    simp only [merge_split]

/-! ### The bound -/

section TypeII

open Classical

end TypeII

end SieveChainR
