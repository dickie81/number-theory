/-
# The window's tests for a tree of Buchstab steps, without Mathlib

The tests of `SieveAdDefs.lean`'s trees that use the window alone, on a grid of the certificate (`SieveCert.Grid`,
whose window is `(U1, U2)` and whose floor is the window's width `V`), with the bilinear Type I rule's exponent
(`SieveCert.IBPar`):

* `okIW`: the term of a box is evaluated when its cells lie in `[V, DEN]` and the box is surely evaluable
  (`SieveCert.surelyEval`: a set of its primes has its product in the window, or in the reflected one, on the whole
  box);
* `okJW`: the terms of a box at the floor `x^{V/DEN}` are evaluated when its cells lie in `[V, DEN]` and the
  bilinear rule passes the box (`SieveCert.ibOK`: a set of its primes stops every point at the window, and a split
  of the leaves satisfies the estimate).

The boxes of `SieveAdDefs.lean` have the newest prime first, and those of `SieveCert` the oldest, so the tests
reverse the list. `winTests` is the pair. The file imports `SieveAdDefs.lean` and `SieveRuleDefs.lean`, which load no
more of `Mathlib` than the notation `ℕ`; `SieveAdWin.lean` proves the tests sound.
-/
import SieveAdDefs
import SieveRuleDefs

namespace SieveAd

open SieveCert (DEN V surelyEval ibOK)

/-- Every cell has its lower end at least `lo` and both ends at most `DEN`. -/
def cellsIn (lo : ℕ) : List Cell → Bool
  | [] => true
  | c :: b => Nat.ble lo c.1 && Nat.ble c.1 DEN && Nat.ble c.2 DEN && cellsIn lo b

variable [SieveCert.Grid]

/-- The window's test of a term: at most 13 primes, cells in `[V, DEN]`, and the box surely evaluable. -/
def okIW (bl : List Cell) : Bool := Nat.ble bl.length 13 && cellsIn V bl && surelyEval bl.reverse

variable [SieveCert.IBPar]

/-- The window's test of the terms at a floor: the floor is `V`, at most 13 primes, cells in `[V, DEN]`, and the
bilinear rule passes the box. -/
def okJW (bl : List Cell) (f : ℕ) : Bool :=
  Nat.beq f V && Nat.ble bl.length 13 && cellsIn V bl && ibOK bl.reverse

/-- **The window's tests.** -/
def winTests : Tests := ⟨fun bl _ => okIW bl, fun bl f _ => okJW bl f⟩

end SieveAd
