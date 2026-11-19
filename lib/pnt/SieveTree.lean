/-
# Buchstab's tree: rough numbers and the primes of an interval

Plain statements. `rough z n` says that `n` has no prime factor below `z`; `primesIco w z` is the set of primes of
`[w, z)`.

* `rough_mono`: for `w ≤ z`, `rough z n` implies `rough w n`.
* `prod_dvd_iff`: for a set `P` of primes, `∏P ∣ n` iff every `p ∈ P` divides `n`.
* `coprime_r`: `r`, whose prime factors are at least `z`, is prime to a product of primes below `z`.
* `mem_primesIco`: `p ∈ primesIco w z` iff `w ≤ p < z` and `p` is prime.

All four are used in the proof of `SieveTreeStop.tree_pt_stop`, Buchstab's tree with a stopping rule at one `n`:
Buchstab's identity iterated from `z₀` down to `w` over the sets `P` of primes of `[w, z₀)`.

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
