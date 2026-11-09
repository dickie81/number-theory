"""Writes the certificate of the finite search of the class number one problem.

    python3 scripts/gen_class_number_cert.py           # writes lib/pnt/ClassNumberOneCertDefs.lean and …CertP0–P3.lean
    python3 scripts/gen_class_number_cert.py --check   # fails unless the files in lib/pnt are the ones it writes

The files hold no data beyond the bit masks of the squares modulo the odd primes p ≤ 67, which
ClassNumberOne.masks_ok proves correct in Lean, and the ranges of the 32 kernel computations: checkDown base 100000
for base = 171 + 800000·i, i < 32, that is, good n for every n ≡ 3 (mod 8) with 171 ≤ n ≤ 25 600 163. See
formalisations/class-number-one.md.
"""

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]
CHUNK = 100000
PARTS = 4
PER_PART = 8


def mask(p):
    m = 0
    for r in range(p):
        m |= 1 << (r * r % p)
    return m


DEFS = '''/-
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
  [%s]

/-- Whether `−n` is a square modulo `p`, read from the mask `m` of the squares modulo `p`. -/
def sq (n p m : ℕ) : Bool := Nat.testBit m ((p - n %% p) %% p)

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
'''

PART = '''/-
# The finite search of the class number one problem: part %d

Imports `ClassNumberOneCertDefs` only. Written by `scripts/gen_class_number_cert.py`. Each theorem is one kernel
computation, `decide +kernel`: `good n` for the `100 000` numbers `n = base + 8j`, `j < 100 000`. Parts `0` to `3`
together cover every `n ≡ 3 (mod 8)` from `171` to `25 600 163` (`ClassNumberOne.good_of_mod`).
-/
import ClassNumberOneCertDefs

namespace ClassNumberOneCert

%s

end ClassNumberOneCert
'''


def files():
    out = {}
    masks = ",\n   ".join(f"({p}, {mask(p)})" for p in PRIMES)
    out["ClassNumberOneCertDefs.lean"] = DEFS % masks
    for part in range(PARTS):
        thms = "\n".join(
            f"theorem check_{i} : checkDown {171 + 8 * CHUNK * i} {CHUNK} = true := by decide +kernel"
            for i in range(PER_PART * part, PER_PART * (part + 1)))
        out[f"ClassNumberOneCertP{part}.lean"] = PART % (part, thms)
    return out


def main():
    check = "--check" in sys.argv[1:]
    bad = []
    for name, text in files().items():
        path = ROOT / "lib" / "pnt" / name
        if check:
            if not path.exists() or path.read_text() != text:
                bad.append(name)
        else:
            path.write_text(text)
            print("wrote", path.relative_to(ROOT))
    if check:
        if bad:
            print("the certificate files differ from the generator's:", ", ".join(bad))
            sys.exit(1)
        print("the class number one certificate files are the generator's")


if __name__ == "__main__":
    main()
