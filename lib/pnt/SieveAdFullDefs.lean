/-
# The checks of the estimate in two variables on the exponents of two products, without Mathlib

The test `chkI2` of `SieveAdTwoDefs.lean` reads a box through the sums of the ends of its cells over two sets of
its primes. Here the checks are a function of four numbers, for the tuples whose products are not sums over a
list: the full tuples of a reversed term, whose frozen part carries a cofactor of many primes.

* `coreI2 u v ρ₁ ρ₂`: the region's six inequalities for a first variable of exponent in `[u − 1, v]` and a rest
  of exponent in `[ρ₁ − 1, ρ₂ + 1]`, in units of `1/DEN` of exponents of `x`.

The file imports `SieveAdTwoDefs.lean`.
-/
import SieveAdTwoDefs

namespace SieveAd

open SieveCert (DEN)

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- The checks of the estimate in two variables: the region's six inequalities for a first variable of exponent in
`[u − 1, v]` and a rest of exponent in `[ρ₁ − 1, ρ₂ + 1]`. -/
def coreI2 (u v ρ₁ ρ₂ : ℕ) : Bool :=
  Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * ρ₁) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (ρ₂ + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 90137 * Lnum) (62500 * Lnum * u + 27637 * Lnum * ρ₁) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN)

end SieveAd
