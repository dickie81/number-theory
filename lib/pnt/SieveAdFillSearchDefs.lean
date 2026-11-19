/-
# The largest floor of the comparison with the rest among the tree's primes, without Mathlib

`SieveAdFillDefs.lean`'s test `okJ3` of a box at a floor takes the rest of the comparison among the primes of the
comparison's own tree, in a window that it computes from the floor. The search led by hints
(`SieveAdDirDefs.lean`) counts the floors of that comparison down from the largest floor at which the window is
wider than the floor.

* `u3`: the lower end of the window of `okJ3`.
* `fmax3`: the largest floor at which the window that `okJ3` computes is wider than the floor.

These are arithmetic on natural numbers, and the file imports only `SieveAdRevDefs.lean` and
`SieveAdFillDefs.lean`.
-/
import SieveAdRevDefs
import SieveAdFillDefs

namespace SieveAd

open SieveCert (DEN cdiv)

variable [SieveCert.IBPar]

/-- The lower end of the window of `okJ3`. -/
def u3 : ℕ := uOfF restLo

/-- The largest floor `f` with `u3 + f < vOfF (restLo + f + 1)`. -/
def fmax3 : ℕ :=
  minN (Nat.div (Nat.sub vA (Nat.add (Nat.add restLo 3) u3)) 2)
    (Nat.div (Nat.sub vB (Nat.add (Nat.mul vC (Nat.add restLo 2)) (Nat.mul (Nat.succ u3) uC))) (Nat.add uC vC))

end SieveAd
