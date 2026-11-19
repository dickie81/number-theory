/-
# A sum of `dw` as two counts

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveFamily.dw q a n = 1[n ≡ a] − 1[(n, q) = 1]/φ(q)`.

* `sum_dw_eq`: a sum of `dw` over a set is the count of its `n ≡ a` minus the count of its `n` prime to `q`, divided
  by `φ(q)`.

The file imports `SieveTree.lean`, `SieveLeaf.lean` and `SieveFamily.lean`.
-/
import SieveTree
import SieveLeaf
import SieveFamily

open Real Finset SieveFamily SieveTree

namespace SieveDiff

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
