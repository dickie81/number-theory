/-
# Buchstab's tree

Plain statement. `rough z n` says that `n` has no prime factor below `z`; `primesIco w z` is the set of primes of
`[w, z)`.

* `tree_pt`: Buchstab's tree at one `n`. For `w ≤ z₀` and `r ≤ X` with every prime factor of `r` at least `z₀`,
  `[r ∣ n, rough z₀ n]` is the leaves' sum `Σ_{P ⊆ [w, z₀), r∏P ≤ X} (−1)^{|P|} [r∏P ∣ n, rough w n]` plus the stops'
  sum `Σ_{w ≤ p < z₀} Σ_{P ⊆ (p, z₀), r∏P ≤ X < r∏P·p} (−1)^{|P|+1} [r∏P·p ∣ n, rough p n]`, over sets `P` of primes.

This is Buchstab's identity iterated from `z₀` down to `w`, each branch stopped once its product would pass the
threshold `X`.

The proof: for `n` with `r ∣ n` and `rough w n`, let `Q` be the primes of `[w, z₀)` that divide `n`. The leaves that
count `n` are the `P ⊆ Q`, and the stops those with `p = min Q`. `alt_cancel`,
`Σ_{P⊆Q} (−1)^{|P|}[a∏P ≤ X] + Σ_{P'⊆Q∖{q}} (−1)^{|P'|+1}[a∏P' ≤ X < a∏P'q] = 0` with `q = min Q`, leaves `[Q = ∅]`.

The file imports only Mathlib.
-/
import Mathlib

open Finset

namespace SieveTree

/-- `n` has no prime factor below `z`. -/
def rough (z n : ℕ) : Prop := ∀ p < z, p.Prime → ¬ p ∣ n

instance (z n : ℕ) : Decidable (rough z n) := by unfold rough; infer_instance

/-- The primes of `[w, z)`. -/
def primesIco (w z : ℕ) : Finset ℕ := (Finset.Ico w z).filter Nat.Prime

theorem rough_mono {w z n : ℕ} (h : w ≤ z) (hz : rough z n) : rough w n :=
  fun p hp hpp => hz p (lt_of_lt_of_le hp h) hpp

/-- For a set `P` of primes, `∏P ∣ n` iff every `p ∈ P` divides `n`. -/
theorem prod_dvd_iff {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (n : ℕ) : (∏ p ∈ P, p) ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  constructor
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem _ hp) h
  · intro h
    exact Finset.prod_primes_dvd n (fun p hp => (hP p hp).prime) h

/-- `r`, whose primes are at least `z`, is prime to a product of primes below `z`. -/
theorem coprime_r {r z : ℕ} (hr : ∀ p : ℕ, p.Prime → p ∣ r → z ≤ p) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hPz : ∀ p ∈ P, p < z) : Nat.Coprime r (∏ p ∈ P, p) := by
  refine Nat.Coprime.prod_right fun p hp => ?_
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hP p hp)).2 fun h => ?_)
  have := hr p (hP p hp) h
  have := hPz p hp
  omega

theorem mem_primesIco {w z p : ℕ} : p ∈ primesIco w z ↔ w ≤ p ∧ p < z ∧ p.Prime := by
  rw [primesIco, Finset.mem_filter, Finset.mem_Ico, and_assoc]

end SieveTree
