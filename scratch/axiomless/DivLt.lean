import Tower

/-!
# `n / k < n` with no axiom

Core proves `Nat.div_lt_self` with `simp`, so with `propext`. The termination proof of `Nat.bitwise` uses it,
so core's `Nat.land`, `Nat.lor`, `Nat.xor` and `Nat.testBit` depend on `propext`, and so does every certificate
part of this library's Linnik theorems, which read their hints with `&&&` (LOG.md, entry 11). That lemma is the
only route: without it the parts depend on no axiom.

This file proves the same statement from the definition of core's division, with no axiom. So the dependence is
an accident of one proof in core, not a need.
-/

namespace Ax

/-- One step of core's division, which recurses on a bound: by definition. -/
theorem div_go_succ (y : Nat) (hy : 0 < y) (fuel x : Nat) (h : x < fuel + 1) :
    Nat.div.go y hy (fuel + 1) x h =
      if hle : y ≤ x then Nat.div.go y hy fuel (x - y) (Nat.div_rec_fuel_lemma hy hle h) + 1 else 0 := rfl

/-- Core's division is its recursion with the bound `x + 1`. -/
theorem div_eq_go (x y : Nat) (hy : 0 < y) : x / y = Nat.div.go y hy (x + 1) x (Nat.lt_succ_self x) := by
  show Nat.div x y = _
  unfold Nat.div
  split
  · rfl
  · contradiction

theorem div_go_le (y : Nat) (hy : 0 < y) : ∀ (fuel x : Nat) (h : x < fuel), Nat.div.go y hy fuel x h ≤ x
  | 0, x, h => absurd h (Nat.not_lt_zero x)
  | fuel + 1, x, h => by
    rw [div_go_succ]
    split
    · rename_i hle
      have hx : 0 < x := Nat.lt_of_lt_of_le hy hle
      exact Nat.le_trans (Nat.succ_le_succ (div_go_le y hy fuel (x - y) _)) (Nat.succ_le_of_lt (Nat.sub_lt hx hy))
    · exact Nat.zero_le x

/-- The statement of core's `Nat.div_lt_self`. -/
theorem div_lt_self {n k : Nat} (hn : 0 < n) (hk : 1 < k) : n / k < n := by
  have hk0 : 0 < k := Nat.lt_trans Nat.zero_lt_one hk
  rw [div_eq_go n k hk0, div_go_succ]
  split
  · rename_i hle
    -- n = k + j, and the quotient of j is at most j, so the result is at most j + 1 < k + j
    obtain ⟨j, hj⟩ := Nat.le.dest hle
    have hsub : n - k = j := by rw [← hj, Nat.add_comm k j, add_sub_cancel]
    have hle' := div_go_le k hk0 n (n - k) (Nat.div_rec_fuel_lemma hk0 hle (Nat.lt_succ_self n))
    have h1 : j + 1 < j + k := Nat.add_lt_add_left hk j
    have hlt : n - k + 1 < n := by rw [hsub, ← hj, Nat.add_comm k j]; exact h1
    exact Nat.lt_of_le_of_lt (Nat.succ_le_succ hle') hlt
  · exact hn

end Ax

#axiom_free Ax.div_go_succ Ax.div_eq_go Ax.div_go_le Ax.div_lt_self
#print axioms Nat.div_lt_self
#print axioms Ax.div_lt_self
