/-
# The tests of the tree over the frozen part of a reversal, without Mathlib

The tree of a reversed term over the frozen part `SieveAd.frozS` (the tuples `a` of a box `β` with a cofactor,
`∏a·m` in the slab `(x^{e₁/DEN}, x^{e₂/DEN}]`) reads a box `bl = ch ++ β`: the chain's cells and then `β`'s. A set
of the primes of a term is given by the bits of a number: the low bits for the cells of `ch`, in the list's order,
the next for the cells of `β`, and the bit after them for the cofactor.

* `loR e₁ β ch m`, `hiR e₂ β ch m`: bounds for the exponent of the product over the set of `m`: without the
  cofactor the sums of the lower and upper ends; with it `e₁` less the upper ends of the cells of `β` outside the
  set, plus the lower ends of the chain's, and `e₂` less the lower ends, plus the upper ends. `hiRc e₂ β ch m`:
  the upper bound for the complement of the set.
* `okIF`: the test of the term of the chain's box by the estimate in two variables (`coreI2`), for the first
  variable `s0` and the rest `sr`.
* `okJF3`, `okJF2`: the tests of its terms at a floor by the comparison with the rest among the tree's primes
  (`coreJ3`) and among the tuple's (`coreJ2`), with `Kb` cells of room for the cofactor's primes.
* `frozTests e₁ e₂ Kb β`: the tests.

The file imports `SieveAdCoreDefs.lean`, `SieveAdFullDefs.lean` and `SieveAdRevDefs.lean`.
-/
import SieveAdCoreDefs
import SieveAdFullDefs
import SieveAdRevDefs

namespace SieveAd

open SieveCert (DEN cdiv)

/-- A lower bound for the exponent of the product over the set of `m`. -/
def loR (e₁ : ℕ) (β ch : List Cell) (m : ℕ) : ℕ :=
  cond (Nat.testBit (m / 2 ^ ch.length) β.length)
      (e₁ - (hiSum β - mSum (fun c => c.2) β (m / 2 ^ ch.length)))
      (mSum (fun c => c.1) β (m / 2 ^ ch.length)) +
    mSum (fun c => c.1) ch m

/-- An upper bound for the exponent of the product over the set of `m`. -/
def hiR (e₂ : ℕ) (β ch : List Cell) (m : ℕ) : ℕ :=
  cond (Nat.testBit (m / 2 ^ ch.length) β.length)
      (e₂ - (loSum β - mSum (fun c => c.1) β (m / 2 ^ ch.length)))
      (mSum (fun c => c.2) β (m / 2 ^ ch.length)) +
    mSum (fun c => c.2) ch m

/-- An upper bound for the exponent of the product over the complement of the set of `m`. -/
def hiRc (e₂ : ℕ) (β ch : List Cell) (m : ℕ) : ℕ :=
  cond (Nat.testBit (m / 2 ^ ch.length) β.length)
      (hiSum β - mSum (fun c => c.2) β (m / 2 ^ ch.length))
      (e₂ - mSum (fun c => c.1) β (m / 2 ^ ch.length)) +
    (hiSum ch - mSum (fun c => c.2) ch m)

variable [SieveCert.IBPar]

/-- **The test of the term of a chain's box over the frozen part**, by the estimate in two variables: the cells
have `1 ≤ lo ≤ hi ≤ DEN`, the sets `s0` and `sr` have no common bit, the rest's exponent has a positive lower bound,
and the exponents pass `coreI2`. -/
def okIF (e₁ e₂ : ℕ) (β bl : List Cell) (cfg : Cfg) : Bool :=
  cellsFrom 1 bl && Nat.beq (Nat.land cfg.s0 cfg.sr) 0 &&
    Nat.blt 0 (loR e₁ β (chainOf β.length bl) cfg.sr) &&
    coreI2 (loR e₁ β (chainOf β.length bl) cfg.s0) (hiR e₂ β (chainOf β.length bl) cfg.s0)
      (loR e₁ β (chainOf β.length bl) cfg.sr) (hiR e₂ β (chainOf β.length bl) cfg.sr)

/-- **The test of the terms at a floor over the frozen part, with the rest among the tree's primes**: `coreJ3`
at the rests, the window and the growth that the floor gives, on the exponents of the sets `s0` and `s1` and of the
complement of `s1`, with `Kb` cells of room. -/
def okJF3 (e₁ e₂ Kb : ℕ) (β bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  Nat.blt 0 f && cellsFrom f bl &&
    coreJ3 f cfg.e (uOf fillLo) (vOf (fillLo + f + 1))
      (uOf fillLo - (loR e₁ β (chainOf β.length bl) cfg.s0 - Kb)) fillLo (fillLo + f + 1)
      (loR e₁ β (chainOf β.length bl) cfg.s0 - Kb) (hiR e₂ β (chainOf β.length bl) cfg.s0 + Kb)
      (hiR e₂ β (chainOf β.length bl) cfg.s1 + Kb) (hiRc e₂ β (chainOf β.length bl) cfg.s1 + Kb)

/-- **The test of the terms at a floor over the frozen part, with the rest among the tuple's primes**: `coreJ2`
at the window and the growth that the rest's set `sr` gives, with `Kb` cells of room. -/
def okJF2 (e₁ e₂ Kb : ℕ) (β bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  Nat.blt 0 f && cellsFrom f bl && Nat.beq (Nat.land cfg.s0 cfg.sr) 0 &&
    Nat.blt 0 (loR e₁ β (chainOf β.length bl) cfg.sr) &&
    coreJ2 f cfg.e (uOf (loR e₁ β (chainOf β.length bl) cfg.sr - Kb))
      (vOf (hiR e₂ β (chainOf β.length bl) cfg.sr + Kb))
      (uOf (loR e₁ β (chainOf β.length bl) cfg.sr - Kb) - (loR e₁ β (chainOf β.length bl) cfg.s0 - Kb))
      (loR e₁ β (chainOf β.length bl) cfg.sr - Kb) (hiR e₂ β (chainOf β.length bl) cfg.sr + Kb)
      (loR e₁ β (chainOf β.length bl) cfg.s0 - Kb) (hiR e₂ β (chainOf β.length bl) cfg.s0 + Kb)
      (hiR e₂ β (chainOf β.length bl) cfg.s1 + Kb) (hiRc e₂ β (chainOf β.length bl) cfg.s1 + Kb)

/-- **The tests of the tree over the frozen part**: the estimate in two variables for the term of a chain's box;
at a floor, the comparison with the rest among the tree's primes for the configurations of kind `2`, and among the
tuple's for the others. -/
def frozTests (e₁ e₂ Kb : ℕ) (β : List Cell) : Tests :=
  ⟨okIF e₁ e₂ β, fun bl f cfg => cond (Nat.beq cfg.kind 2) (okJF3 e₁ e₂ Kb β bl f cfg) (okJF2 e₁ e₂ Kb β bl f cfg)⟩

end SieveAd
