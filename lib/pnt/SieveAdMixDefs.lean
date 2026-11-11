/-
# The window's tests and the estimate's, together, without Mathlib

`mixTests`: the tests of `SieveAdDefs.lean`'s trees that a decomposition below `11/5` uses while the window is open.
A configuration of kind `0` asks for the window's test (`SieveAdWinDefs.lean`), and any other for the test of the
estimate in two variables (`SieveAdTwoDefs.lean`), with the configuration's sets.

The file imports `SieveAdWinDefs.lean` and `SieveAdTwoDefs.lean`.
-/
import SieveAdWinDefs
import SieveAdTwoDefs

namespace SieveAd

variable [SieveCert.Grid] [SieveCert.IBPar]

/-- **The window's tests for the configurations of kind `0`, and the estimate's for the others.** -/
def mixTests : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 0) (okIW bl) (okI2 bl cfg),
    fun bl f cfg => cond (Nat.beq cfg.kind 0) (okJW bl f) (okJ2 bl f cfg)⟩

end SieveAd
