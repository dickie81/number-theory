/-
# The exponent of the bilinear Type I estimate, without Mathlib

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`IBPar` holds the exponent `L = Lnum/Lden` at which the searches of the `SieveAd` files take the bilinear Type I
estimate: a term with `e` of exponent `T` on one side is evaluated where `a₁ < (1 − 1/L)DEN` and `a₁ + 2a₂ < DEN`
at the upper ends, in units of `1/DEN`. A certificate's file gives the instance for its exponent (`ibPar21500` in
`SieveHint21500.lean`, `ibPar21000` in `SieveHint21000.lean`).

The class is two natural numbers, and the file imports only `SieveCertDefs.lean`, so a part file that imports no
more than this one runs its kernel checks without `Mathlib`.
-/
import SieveCertDefs

namespace SieveCert

/-- The exponent `L = Lnum/Lden` of the bilinear Type I rule. -/
class IBPar where
  /-- The numerator of `L`. -/
  Lnum : ℕ
  /-- The denominator of `L`. -/
  Lden : ℕ

end SieveCert
