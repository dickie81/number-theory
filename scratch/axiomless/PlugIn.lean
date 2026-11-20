import Mathlib
import Tower
import Principles
import Ladder
import Stuck
import DivLt
import Compute

/-!
# The files of this directory, imported together with Mathlib

Nothing in the library imports this directory. This file checks what would happen if something did: it imports
Mathlib and the directory's modules together, and checks that Mathlib behaves as it does without them. LOG.md,
entry 13, has what was found and changed.

It needs Mathlib, so `check.sh` does not run it:

    scratch/axiomless/check.sh
    LEAN_PATH="$(lake env printenv LEAN_PATH):scratch/axiomless/build" lean scratch/axiomless/PlugIn.lean

It compiles without output if all is well.
-/

/-! The modules load together: no constant is declared twice. That is checked by the imports above. -/

/-- Divisibility on `ℕ` is still decided by core's instance. `Ax.decDvd` is an instance inside `Tower.lean` only. -/
example (a b : ℕ) : (inferInstance : Decidable (a ∣ b)) = Nat.decidable_dvd a b := rfl

/-- So a lemma of Mathlib whose statement holds that instance still applies to a goal written here. With
`Ax.decDvd` an instance everywhere, this failed with a mismatch between two types that print the same. -/
example (n : ℕ) (h : n ≠ 0) : {d ∈ Finset.range n.succ | d ∣ n} = n.divisors := Nat.filter_dvd_eq_divisors h

example (n : ℕ) (h : n ≠ 0) : {d ∈ Finset.range n.succ | d ∣ n} = n.divisors := by
  rw [Nat.filter_dvd_eq_divisors h]

/-- The instance of this directory is still there by name, for a proof that should have no axiom. -/
theorem three_dvd_twelve : (3 : ℕ) ∣ 12 := @of_decide_eq_true _ (Ax.decDvd 3 12) rfl

#axiom_free three_dvd_twelve

/-- Mathlib's `Prime` and this directory's `Ax.Prime` are different predicates. Inside the namespace `Ax`, or
after `open Ax`, the name `Prime` is ambiguous or means `Ax.Prime`; write `_root_.Prime` or `Nat.Prime` for
Mathlib's. -/
example : Ax.Prime 7 := by decide +kernel
example : Nat.Prime 7 := by norm_num
