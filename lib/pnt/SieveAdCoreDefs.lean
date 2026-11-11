/-
# The checks of the tests on the sums of a box, without Mathlib

The tests of `SieveAdTwoDefs.lean` and `SieveAdFillDefs.lean` read a box through a few sums of the ends of its
cells over sets of its primes. Here the checks are functions of those sums, for the boxes whose sums are not the
sums of a list: the terms of a reversed term, whose frozen part carries a cofactor of many primes.

* `coreJ3`: the checks of `chkJ3` (the comparison in two variables with the rest among the tree's primes), on the
  sums `c0lo`, `c0hi` of the lower and upper ends over the set that enters the window, and `h1s`, `h2s` of the
  upper ends over the first side of the leaves and over the other primes.
* `coreJ2`: the checks of `chkJ2` (the comparison in two variables with the rest among the box's primes), on those
  sums and on `ρ₁`, `ρ₂`, the sums of the lower and upper ends over the rest's set.

The file imports `SieveAdFillDefs.lean`.
-/
import SieveAdFillDefs

namespace SieveAd

open SieveCert (DEN cdiv)

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- The checks of the comparison in two variables with the rest among the tree's primes at the floor `f`, on the
sums of a box: `c0lo` at most the sum of the lower ends over the set that enters the window and `c0hi` at least
that of the upper ends, `h1s` at least the sum of the upper ends over the first side of the leaves and `h2s` at
least that over the other primes; the flag `e`, the window `[u, v]`, the growth `t` and the rests of exponent in
`[r₁ − 1, r₂ + 1]`. -/
def coreJ3 (f : ℕ) (e : Bool) (u v t r1 r2 c0lo c0hi h1s h2s : ℕ) : Bool :=
  let D₁ := h1s + cond e (t + r2) 0
  let D₂ := h2s + cond e 0 (t + r2)
  Nat.blt 0 f &&
    Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * r1) &&
    Nat.ble (2 * Lden * DEN) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (r2 + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 27637 * Lnum) (62500 * Lnum * u + 27637 * Lnum * r1) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (r2 + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (r2 + 1)) (62500 * Lnum * DEN) &&
    Nat.blt (r1 + f) r2 &&
    Nat.blt (u + f) v &&
    Nat.ble u (t + c0lo) &&
    Nat.blt c0hi v &&
    Nat.blt (Lnum * D₁ + Lden * DEN) (Lnum * DEN) &&
    Nat.blt (2 * Lnum * (D₁ + D₂) + Lden * DEN) (2 * Lnum * DEN) &&
    Nat.blt (Lnum * (D₁ + 2 * D₂) + 2 * Lden * DEN) (2 * Lnum * DEN)

/-- The checks of the comparison in two variables at the floor `f`, on the sums of a box: the rest's exponent in
`[ρ₁ − 1, ρ₂ + 1]`, `ρ₁` at most the sum of the lower ends over the rest's set and `ρ₂` at least that of the upper
ends; `c0lo`, `c0hi`, `h1s`, `h2s` as for `coreJ3`; the flag `e`, the window `[u, v]` and the growth `t`. -/
def coreJ2 (f : ℕ) (e : Bool) (u v t ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ) : Bool :=
  let D₁ := h1s + cond e t 0
  let D₂ := h2s + cond e 0 t
  Nat.blt 0 f &&
    Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * ρ₁) &&
    Nat.ble (2 * Lden * DEN) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (ρ₂ + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 27637 * Lnum) (62500 * Lnum * u + 27637 * Lnum * ρ₁) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.blt (u + f) v &&
    Nat.ble u (t + c0lo) &&
    Nat.blt c0hi v &&
    Nat.blt (Lnum * D₁ + Lden * DEN) (Lnum * DEN) &&
    Nat.blt (2 * Lnum * (D₁ + D₂) + Lden * DEN) (2 * Lnum * DEN) &&
    Nat.blt (Lnum * (D₁ + 2 * D₂) + 2 * Lden * DEN) (2 * Lnum * DEN)

end SieveAd
