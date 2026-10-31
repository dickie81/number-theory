/-
# The tree's weights

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveFamily.dw q a n = 1[n ≡ a] − 1[(n, q) = 1]/φ(q)`.

* `tree_weighted`: for any weights `f`, `SieveTree.tree_pt` summed over a finite set.
* `sum_dw_eq`: a sum of `dw` over a set is the count of its `n ≡ a` minus the count of its `n` prime to `q`, divided
  by `φ(q)`.

The file imports `SieveTree.lean`, `SieveLeaf.lean` and `SieveFamily.lean`.
-/
import SieveTree
import SieveLeaf
import SieveFamily

open Real Finset SieveFamily SieveTree

namespace SieveDiff

/-- **The Buchstab tree, weighted.** For `w ≤ z₀`, `r ≤ X` with every prime factor of `r` at least `z₀`, and any
weights `f`: the tree identity `tree_pt` summed over a finite set. -/
theorem tree_weighted (C : Finset ℕ) (f : ℕ → ℂ) {r X w z₀ : ℕ} (hwz : w ≤ z₀)
    (hr : ∀ p : ℕ, p.Prime → p ∣ r → z₀ ≤ p) (hrX : r ≤ X) :
    ∑ n ∈ C, f n * (if r ∣ n ∧ rough z₀ n then 1 else 0) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℂ) ^ P.card *
          (if r * ∏ p ∈ P, p ≤ X then ∑ n ∈ C, f n * (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0)
            else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
            ∑ n ∈ C, f n * (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
  have hptC : ∀ n, (if r ∣ n ∧ rough z₀ n then (1 : ℂ) else 0) =
      ∑ P ∈ (primesIco w z₀).powerset, (-1 : ℂ) ^ P.card *
          (if r * ∏ p ∈ P, p ≤ X then (if r * ∏ p ∈ P, p ∣ n ∧ rough w n then 1 else 0) else 0) +
        ∑ p ∈ primesIco w z₀, ∑ P ∈ (primesIco (p + 1) z₀).powerset, (-1 : ℂ) ^ (P.card + 1) *
          (if r * ∏ p' ∈ P, p' ≤ X ∧ X < r * (∏ p' ∈ P, p') * p then
            (if r * (∏ p' ∈ P, p') * p ∣ n ∧ rough p n then 1 else 0) else 0) := by
    intro n
    have h := congrArg (Int.cast : ℤ → ℂ) (tree_pt n hwz hr hrX)
    push_cast at h
    convert h using 1
  simp_rw [hptC, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    split_ifs with h
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    · simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    split_ifs with h
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    · simp

/-- A weighted sum of `dw` as two counts: the `n ≡ a` and, divided by `φ(q)`, the `n` prime to `q`. -/
theorem sum_dw_eq {q : ℕ} [NeZero q] (a : ZMod q) (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ∑ n ∈ s, dw q a n * (if c n then 1 else 0) =
      ((s.filter (fun n => n ≡ a.val [MOD q] ∧ c n)).card : ℂ) -
        ((s.filter (fun n => Nat.Coprime n q ∧ c n)).card : ℂ) / q.totient := by
  have h1 : ∀ n : ℕ, ((n : ZMod q) = a) ↔ n ≡ a.val [MOD q] := fun n => by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  have h2 : ∀ n : ℕ, IsUnit (n : ZMod q) ↔ Nat.Coprime n q := fun n => ZMod.isUnit_iff_coprime n q
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold dw
  simp only [h1, h2]
  by_cases hc : c n <;> by_cases ha : n ≡ a.val [MOD q] <;> by_cases hu : n.Coprime q <;> simp [hc, ha, hu]

end SieveDiff
