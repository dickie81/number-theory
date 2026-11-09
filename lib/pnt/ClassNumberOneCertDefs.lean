/-
# The finite search of the class number one problem: the definitions

Imports `Mathlib.Data.Nat.Notation` only, so that the certificate's parts (`ClassNumberOneCertP0`, …, `P3`) are checked
by the kernel without Mathlib in memory. Written by `scripts/gen_class_number_cert.py`.

Plain statement. For a natural number `n`, `good n` says that some odd prime `p ≤ 67` has `4p < n` and `−n` a square
modulo `p`. If `K` is an imaginary quadratic field of discriminant `−n`, `n ≡ 3 (mod 8)`, such a `p` splits or ramifies
in `K`, and the prime ideal above it, of norm `p < n/4`, is not principal: `K` does not have class number one
(`ClassNumberOne`). The parts check `good n` for every `n ≡ 3 (mod 8)` from `171` to `25 600 163`.

* `primeMasks`: the odd primes `p ≤ 67`, each with the set of the squares modulo `p` as a bit mask: bit `i` is set if
  and only if `i ≡ r² (mod p)` for some `r`. `ClassNumberOne.masks_ok` proves this of each mask, and that each `p` is
  prime, so the masks are not trusted.
* `sq n p m`: bit `(p − n mod p) mod p` of the mask `m`, that is, whether `−n` is a square modulo `p`.
* `good n`: some `(p, m)` of the list has `4p < n` and `sq n p m`.
* `checkDown base k`: `good (base + 8j)` for every `j < k`. The recursion is on the counter, so that the kernel
  evaluates `base + 8j` from a literal at each step.
* `good_of_checkDown`: `checkDown base k = true` gives `good (base + 8j) = true` for `j < k`.

Only the primes up to `67` are needed: `−n` is a non-square modulo every odd prime `p ≤ 67` for no `n ≡ 3 (mod 8)` in
this range.
-/
import Mathlib.Data.Nat.Notation

namespace ClassNumberOneCert

/-- The odd primes `p ≤ 67`, each with the bit mask of the squares modulo `p`. -/
def primeMasks : List (ℕ × ℕ) :=
  [(3, 3),
   (5, 19),
   (7, 23),
   (11, 571),
   (13, 5659),
   (17, 107287),
   (19, 199411),
   (23, 340831),
   (29, 332473075),
   (31, 303908791),
   (37, 96068509339),
   (41, 1870503675703),
   (43, 3678700564051),
   (47, 4626135339999),
   (53, 5310023542746835),
   (59, 156326468341437115),
   (61, 1662926210933060155),
   (67, 61808106872519771731)]

/-- Whether `−n` is a square modulo `p`, read from the mask `m` of the squares modulo `p`. -/
def sq (n p m : ℕ) : Bool := Nat.testBit m ((p - n % p) % p)

/-- Some odd prime `p ≤ 67` has `4p < n` and `−n` a square modulo `p`. -/
def good (n : ℕ) : Bool := primeMasks.any fun pm => decide (4 * pm.1 < n) && sq n pm.1 pm.2

/-- `good (base + 8j)` for every `j < k`. -/
def checkDown (base : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => good (base + 8 * k) && checkDown base k

/-- `checkDown base k = true` gives `good (base + 8j) = true` for every `j < k`. -/
theorem good_of_checkDown {base k : ℕ} (h : checkDown base k = true) {j : ℕ} (hj : j < k) :
    good (base + 8 * j) = true := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    rw [checkDown, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge j k with hlt | hge
    · exact ih h.2 hlt
    · have hjk : j = k := Nat.le_antisymm (Nat.lt_succ_iff.1 hj) hge
      rw [hjk]
      exact h.1

end ClassNumberOneCert
