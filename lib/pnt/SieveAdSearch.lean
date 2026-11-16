/-
# The search for a tree is sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdSearchDefs.lean` defines a search (`SieveAd.solveF`) that returns a cost and no tree. Here:

* `Has τ bl par c`: some tree passes `SieveAd.ok` on the box `bl`, for a term of the sign `par`, with cost at most `c`.
  `has_vanish`, `has_eval`, `has_drop`, `has_dropB`, `has_split`, `has_buch`: the nodes of a tree, in this form.
* `kids_sound`: if every box that `rec` searches to a cost below its limit has a tree at that cost (`RecOK`), then
  so has the box of the new prime's whole range when the cells' costs sum to less than the limit.
* `step_sound`, `solveF_sound`: **the search is sound.** A cost that `solveF` returns below the limit it was given
  is the cost of a tree. The strategy that proposes the nodes is any: the search uses a node only after its check
  has passed.
* `has_of_kids`: a part of a search, as the kernel checks it: if the costs of the cells of the new prime between
  `a` and `top`, searched with the limit `K`, sum to at most `c < K`, the box of the whole range has a tree at
  cost `c`.
* `linnik_has`: **the theorem from the tree of a search.** For a route and sound tests: if the terms at the floor of
  the box with no prime pass `okJ` and the box of one prime has a tree at a cost below `K`, then every class prime
  to `q` has a prime at most `K'q^L`.

The file imports `SieveAdSearchDefs.lean` and `SieveAdTree.lean`.
-/
import SieveAdSearchDefs
import SieveAdTree

namespace SieveAd

open SieveCert (DEN K)

/-- Some tree passes on the box, for a term of the sign `par`, with cost at most `c`. -/
def Has (τ : Tests) (bl : List Cell) (par : Bool) (c : ℕ) : Prop :=
  ∃ T : Tree, ok τ T bl par = true ∧ cost T bl ≤ c

/-- A box with no term. -/
theorem has_vanish {τ : Tests} {bl : List Cell} {par : Bool} (h : vanishOK bl = true) : Has τ bl par 0 :=
  ⟨.vanish, by simp [ok, h], by simp [cost]⟩

/-- A box that a test evaluates. -/
theorem has_eval {τ : Tests} {x : Cell} {b : List Cell} {par : Bool} {cfg : Cfg} (h : τ.okI (x :: b) cfg = true) :
    Has τ (x :: b) par 0 :=
  ⟨.evalI cfg, by simp [ok, h], by simp [cost]⟩

/-- A box that is dropped. -/
theorem has_drop {τ : Tests} {bl : List Cell} (h : dropOK bl = true) : Has τ bl true (dropCost bl) :=
  ⟨.drop, by simp [ok, h], by simp [cost]⟩

/-- A box that is dropped for its products. -/
theorem has_dropB {τ : Tests} {bl : List Cell} (h : dropBOK bl = true) : Has τ bl true (dropBCost bl) :=
  ⟨.dropB, by simp [ok, h], by simp [cost]⟩

theorem dropC_spec {τ : Tests} {bl : List Cell} {par : Bool} {dc : ℕ} (h : dropC bl par = some dc) :
    Has τ bl par dc := by
  unfold dropC at h
  cases par with
  | false => simp at h
  | true =>
    simp only [Bool.cond_true] at h
    by_cases h1 : dropOK bl = true
    · simp only [h1, Bool.cond_true, Option.some.injEq] at h
      subst h
      exact has_drop h1
    · rw [Bool.not_eq_true] at h1
      simp only [h1, Bool.cond_false] at h
      by_cases h2 : dropBOK bl = true
      · simp only [h2, Bool.cond_true, Option.some.injEq] at h
        subst h
        exact has_dropB h2
      · rw [Bool.not_eq_true] at h2
        simp [h2] at h

end SieveAd

