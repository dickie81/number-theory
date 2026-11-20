import AxiomTools

/-!
# A proof as fuel, and an axiom as a term that does not compute

`Search.find` takes a decidable predicate on `Nat` and a proof, in `Prop`, that it holds somewhere, and returns
the least number where it holds. There is no bound: the search runs for as long as the proof says it may. This is
possible with no axiom because `Acc`, alone among the recursive propositions, can be eliminated into data.

When the proof is free of axioms, the kernel runs the search. When the proof comes from an axiom, the search is
still a theorem's worth of definition, with the same value provably, but the kernel cannot run it: the axiom is a
term with no rule of computation. The file ends with a closed term of type `Nat`, built with `propext`, that is
equal to `5` and does not compute to it, and one, built with `Classical.choice`, that is not provably equal to any
numeral.
-/

namespace Search

variable (P : Nat → Prop)

/-- `m` is the next number to try after `n`. -/
def Next (m n : Nat) : Prop := m = n + 1 ∧ ¬ P n

/-- If `P` holds at `n + d`, the search from `n` ends. By induction on `d`. -/
theorem acc_of_add : ∀ (d n : Nat), P (n + d) → Acc (Next P) n
  | 0, n, h => Acc.intro n (fun _ hm => absurd h hm.2)
  | d + 1, n, h => Acc.intro n (fun m hm => by
      rw [hm.1]
      exact acc_of_add d (n + 1) (by rw [Nat.add_assoc, Nat.add_comm 1 d]; exact h))

theorem acc_zero (h : ∃ n, P n) : Acc (Next P) 0 :=
  let ⟨n, hn⟩ := h
  acc_of_add P n 0 (by rw [Nat.zero_add]; exact hn)

/-- The search from `n`, by recursion on the proof that it ends. -/
noncomputable def findFrom [DecidablePred P] (n : Nat) (a : Acc (Next P) n) :
    (∀ k, k < n → ¬ P k) → {m : Nat // P m ∧ ∀ k, k < m → ¬ P k} :=
  Acc.rec (motive := fun n _ => (∀ k, k < n → ¬ P k) → {m : Nat // P m ∧ ∀ k, k < m → ¬ P k})
    (fun n _ ih hmin =>
      if hp : P n then ⟨n, hp, hmin⟩
      else ih (n + 1) ⟨rfl, hp⟩ (fun k hk hpk =>
        (Nat.lt_succ_iff_lt_or_eq.mp hk).elim (fun hlt => hmin k hlt hpk) (fun heq => hp (heq ▸ hpk))))
    a

/-- The least number where `P` holds, from a proof that there is one. -/
noncomputable def find [DecidablePred P] (h : ∃ n, P n) : {m : Nat // P m ∧ ∀ k, k < m → ¬ P k} :=
  findFrom P 0 (acc_zero P h) (fun k hk => absurd hk (Nat.not_lt_zero k))

/-- The value does not depend on the proof: the least such number is unique. -/
theorem find_eq [DecidablePred P] (h : ∃ n, P n) {m : Nat} (hm : P m) (hmin : ∀ k, k < m → ¬ P k) :
    (find P h).val = m :=
  match Nat.lt_trichotomy (find P h).val m with
  | .inl hlt => absurd (find P h).2.1 (hmin _ hlt)
  | .inr (.inl heq) => heq
  | .inr (.inr hgt) => absurd hm ((find P h).2.2 m hgt)

end Search

open Search

/-! ## The kernel runs the search when the proof is free of axioms -/

/-- The proof says that `1000` works; the search finds the least, `32`. -/
theorem sq_gt : ∃ n : Nat, 1000 < n * n := ⟨1000, by decide⟩

theorem find_sq : (find (fun n => 1000 < n * n) sq_gt).val = 32 := by decide +kernel

/-! ## It does not when the proof comes from an axiom -/

/-- The same proposition, proved by contradiction: `Classical.choice`, `propext`, `Quot.sound`. -/
theorem sq_gt_classical : ∃ n : Nat, 1000 < n * n :=
  Classical.byContradiction fun h => h ⟨1000, by decide⟩

/-- The kernel cannot evaluate the search: the proof is not a pair of a number and a proof. -/
example : True := by
  fail_if_success
    have : (find (fun n => 1000 < n * n) sq_gt_classical).val = 32 := by decide +kernel
  trivial

/-- The value is still `32`, by a proof instead of a computation. -/
theorem find_sq_classical : (find (fun n => 1000 < n * n) sq_gt_classical).val = 32 :=
  find_eq _ _ (by decide) (by decide)

/-! ## A natural number that is equal to 5 and does not compute to 5 -/

/-- `5`, carried along an equality of propositions that `propext` provides. -/
noncomputable def five : Nat :=
  @Eq.rec Prop True (fun _ _ => Nat) 5 (0 = 0) (propext ⟨fun _ => rfl, fun _ => trivial⟩)

example : True := by
  fail_if_success
    have : five = 5 := by decide +kernel
  trivial

theorem five_eq : five = 5 := by
  have h : ∀ (q : Prop) (e : True = q), @Eq.rec Prop True (fun _ _ => Nat) 5 q e = 5 := by
    intro q e; cases e; rfl
  exact h _ _

/-! ## A natural number that no proof identifies -/

/-- An element of `Nat`, chosen. It is a closed term of type `Nat`. It is not a numeral, it does not reduce to
one, and nothing proves which number it is: `chosen = 5` and `chosen ≠ 5` are both unprovable. -/
noncomputable def chosen : Nat := Classical.choice ⟨5⟩

#axiom_free Search.acc_of_add Search.findFrom Search.find Search.find_eq sq_gt find_sq
#print axioms find_sq_classical
#print axioms five_eq
#print axioms chosen
