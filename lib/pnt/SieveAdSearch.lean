/-
# A tree that passes on a box, and its leaves

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdDefs.lean` checks a tree of Buchstab steps on a box (`SieveAd.ok`) and gives it a cost
(`SieveAd.cost`). Here:

* `Has τ bl par c`: some tree passes `SieveAd.ok` on the box `bl`, for a term of the sign `par`, with cost at most `c`.
* `has_vanish`, `has_eval`, `has_drop`, `has_dropB`: the leaves of a tree, in this form: a box with no term and a box
  that a test evaluates have a tree at the cost `0`, for either sign; a box that is dropped, or dropped for its
  products, has one for the sign `true` at the cost of the drop.
* `dropC_spec`: a box has a tree at the cost that `SieveAd.dropC` gives it.

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

