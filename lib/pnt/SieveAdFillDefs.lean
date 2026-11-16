/-
# The test of the comparison with the rest among the tree's primes, and the tests with no window, without Mathlib

The test of `SieveAdDefs.lean`'s trees for Harman's comparison in two variables whose rest is a product of the
primes of the tree below the floor (`SieveFillComp.prop6_fill`), for the region `SieveTwoZone7D.Zone7d` and the
exponent `L = Lnum/Lden` (`SieveCert.IBPar`). It is for a box with no prime of the rest's size. A configuration
gives two sets of the box's primes, by the bits of their positions in the list: `s0`, whose product enters the
window with the small primes, and `s1`, the primes on the first side of the leaves; and the flag `e`, the side of
the small primes. In units of `1/DEN` of exponents of `x`:

* the rest is the product of the tree's primes after the window is entered, from the first product that reaches
  `x^{r₁/DEN}`, with `r₁ = fillLo` the least exponent that the region takes; it is below `x^{(r₁+f)/DEN}`, and
  `r₂ = r₁ + f + 1`;
* the window `[u, v]` of the first variable is the largest that the region allows for the rests of exponent in
  `[r₁ − 1, r₂ + 1]` (`uOf`, `vOf`), and `t = u − Σ_{s0} lo` is the growth of the tree to the window;
* `chkJ3` checks the region's six inequalities at these, that the window is wider than the floor (`u + f < v`),
  that the primes of `s0` stay below its upper end, and the paper's two conditions on the leaves' sizes with the
  growth `t + r₂` or, where they fail, the leaves cut in three (`SieveAdLeafDefs.lean`'s `leavesL`, `leavesE`).

`fillTests` are the tests of a decomposition with no window: the estimate in two variables for a box
(`okI2`), and at a floor the comparison with the rest among the box's primes (`okJ2`) or, for a configuration of
kind `2`, among the tree's (`okJ3`).

The file imports `SieveAdTwoDefs.lean`.
-/
import SieveAdTwoDefs

namespace SieveAd

open SieveCert (DEN cdiv)

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- The least exponent of a rest: the least `ρ₁` with `1/2000 + L/DEN ≤ Lρ₁/DEN`. -/
def fillLo : ℕ := cdiv (Lden * DEN + 2000 * Lnum) (2000 * Lnum)

/-- The checks of the comparison in two variables with the rest among the tree's primes, on a box at the floor
`f`, for the sets `s0`, `s1`, the flag `e`, the window `[u, v]`, the growth `t` and the rests of exponent in
`[r₁ − 1, r₂ + 1]`. -/
def chkJ3 (bl : List Cell) (f s0 s1 : ℕ) (e : Bool) (u v t r1 r2 : ℕ) : Bool :=
  let D₁ := mSum (fun c => c.2) bl s1 + cond e (t + r2) 0
  let D₂ := hiSum bl - mSum (fun c => c.2) bl s1 + cond e 0 (t + r2)
  Nat.blt 0 f && Nat.ble bl.length 13 && cellsFrom f bl &&
    Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * r1) &&
    Nat.ble (2 * Lden * DEN) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (r2 + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 27637 * Lnum) (62500 * Lnum * u + 27637 * Lnum * r1) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (r2 + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (r2 + 1)) (62500 * Lnum * DEN) &&
    Nat.blt (r1 + f) r2 &&
    Nat.blt (u + f) v &&
    Nat.ble u (t + mSum (fun c => c.1) bl s0) &&
    Nat.blt (mSum (fun c => c.2) bl s0) v &&
    (leavesL D₁ D₂ || leavesE D₁ D₂)

/-- **The test of the comparison with the rest among the tree's primes**: `chkJ3` at the rests, the window and the
growth that the box and the floor give. -/
def okJ3 (bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  let u := uOf fillLo
  let v := vOf (fillLo + f + 1)
  chkJ3 bl f cfg.s0 cfg.s1 cfg.e u v (u - mSum (fun c => c.1) bl cfg.s0) fillLo (fillLo + f + 1)

/-- **The tests with no window**: the estimate in two variables for a box; at a floor, the comparison with the
rest among the tree's primes for the configurations of kind `2`, and among the box's for the others. -/
def fillTests : Tests :=
  ⟨okI2, fun bl f cfg => cond (Nat.beq cfg.kind 2) (okJ3 bl f cfg) (okJ2 bl f cfg)⟩

end SieveAd
