/-
# The stops of Buchstab's tree above the threshold

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `RT j Y Ω` is the set of `j`-tuples of primes up to `Y` that satisfy the comparisons `Ω` at
`m = 0`.

* `typeII_cmp`: `SieveTypeIIU.typeII_unw` (with its hypotheses `RouteOK` and `hII`) with the comparisons given as a list
  of `SieveCmp.Cmp`s.
* `sum_stops_eq`: for `1 ≤ w ≤ z₀ ≤ Y`, `X' ≥ 1`, `N₁, N₂ ≥ 1` and `k ≥ 1`, the stops `W = r_1⋯r_j·∏P·p` of the tree
  at the threshold `X'` (`r` over `RT`, `p ∈ [w, z₀)`, `P` an `s`-set of primes of `(p, z₀)`), with `p ≤ minFac k`
  and `N₁ < Wk ≤ N₂`, are the tuples `(r, P in decreasing order, p)` of primes up to `Y` that satisfy the
  comparisons `cmps` at `k`.
* `stops2_bound`: let `L`, `w₁` and `w₂` be a route's parameters with `RouteOK`, assume its Type II estimate
  (`hII : SieveRoute.TypeIIAt`), and fix `e₀ > 0`, `j`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for
  `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `j`-tuples of primes up to `N₂ = ⌊2q^L⌋` satisfying at most
  `J₀` comparisons `Ω` (taken at `m = 0`, with `m`-parts `c(0)` at most `Λ₁ log q`) that force every `rt_i ≥ z₀`, and
  let `q^{e₀} ≤ w ≤ z₀`, `1 ≤ X'`, `X'z₀ ≤ N₁ = ⌊q^L⌋`, `q^{w₁L} ≤ ⌊N₁/(X'z₀)⌋` and `⌊N₂/(X' + 1)⌋ ≤ q^{w₂L}`. Then the
  stops of Buchstab's tree at the threshold `X'` (`SieveDiff.tree_weighted` with `r = ∏rt`), summed over `rt`, have
  `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`.

This is the evaluation of the stops in Proposition 6 for one tree
at the threshold `X'`. A stop `W` lies in `(X', X'z₀)`, so its cofactor `k` lies in `(N₁/(X'z₀), N₂/(X' + 1)]`, inside
the lower window. The roles swap: `k` is the Type II variable and the stop's primes are the family's.

The proof: `sum_cofactor_window` writes a stop's multiples as `Wk` with `k` in that range and `p ≤ minFac k`
(`rough_iff_le_minFac`). For each size `s ≤ ⌈L/e₀⌉` of `P` (a larger `P` has `∏P > X'`), `sum_stops_eq` turns the stops
into a family of `(j + s + 1)`-tuples with the comparisons `cmps`: the region `Ω`, the order `y_1 > ⋯ > y_s > p`,
`y_1 < z₀` (or `p < z₀`), `p ≥ w`, the threshold, the cofactor's roughness and the range (`cmps_iff`). Their
`m`-parts are at most `(Λ₁ + L + 1) log q` (`cmps_c_le`), and `typeII_cmp` bounds each size.

`L`, `w₁` and `w₂` are a route's parameters and the Type II estimate is a hypothesis (`hII`).

The file imports `SieveCmp.lean` and `SieveStops1.lean`.
-/
import SieveCmp
import SieveStops1

open Real Finset SieveFamily SieveTree SieveCmp SieveRoute

namespace SieveStops2

/-! ### A set of `s` naturals as a strictly decreasing `s`-tuple -/

/-- The elements of `P` in decreasing order, when `P` has `s` elements. -/
noncomputable def desc (s : ℕ) (P : Finset ℕ) : Fin s → ℕ :=
  fun u => if h : P.card = s then P.orderEmbOfFin h (Fin.rev u) else 0

theorem desc_eq {s : ℕ} {P : Finset ℕ} (h : P.card = s) (u : Fin s) :
    desc s P u = P.orderEmbOfFin h (Fin.rev u) := by
  simp [desc, h]

theorem desc_strictAnti {s : ℕ} {P : Finset ℕ} (h : P.card = s) : StrictAnti (desc s P) := by
  intro u v huv
  rw [desc_eq h, desc_eq h]
  exact (P.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.2 huv)

theorem desc_mem {s : ℕ} {P : Finset ℕ} (h : P.card = s) (u : Fin s) : desc s P u ∈ P := by
  rw [desc_eq h]
  exact P.orderEmbOfFin_mem h _

theorem image_desc {s : ℕ} {P : Finset ℕ} (h : P.card = s) : Finset.univ.image (desc s P) = P := by
  conv_rhs => rw [← P.image_orderEmbOfFin_univ h]
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨Fin.rev u, (desc_eq h u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Fin.rev u, by rw [desc_eq h, Fin.rev_rev]⟩

theorem desc_image {s : ℕ} {y : Fin s → ℕ} (hy : StrictAnti y) : desc s (Finset.univ.image y) = y := by
  have hc : (Finset.univ.image y).card = s := by
    rw [Finset.card_image_of_injective _ hy.injective, Finset.card_univ, Fintype.card_fin]
  have hu := Finset.orderEmbOfFin_unique hc (f := y ∘ Fin.rev)
    (fun u => Finset.mem_image_of_mem _ (Finset.mem_univ _)) (hy.comp Fin.rev_strictAnti)
  funext u
  rw [desc_eq hc, ← hu]
  simp [Fin.rev_rev]

/-! ### The tuple `(r_1, …, r_j, y_1, …, y_s, p)` -/

variable {j s : ℕ}

/-! ### The comparisons of a stop above the threshold -/

section Sums

open Classical

end Sums

/-! ### The bound -/

theorem rough_iff_le_minFac {p k : ℕ} (hk : 2 ≤ k) : (∀ p' < p, p'.Prime → ¬ p' ∣ k) ↔ p ≤ Nat.minFac k := by
  constructor
  · intro h
    by_contra hlt
    exact h _ (not_le.1 hlt) (Nat.minFac_prime (by omega)) (Nat.minFac_dvd k)
  · intro h p' hp' hpp hd
    have := Nat.minFac_le_of_dvd hpp.two_le hd
    omega

section Bound

open Classical

end Bound

end SieveStops2
