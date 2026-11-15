/-
# The tests of the estimate in two variables for a tree of Buchstab steps, without Mathlib

The test of `SieveAdDefs.lean`'s trees for Harman's comparison with stops in two variables
(`SieveTwoComp.prop6_two`), for the region `SieveTwoZone7D.Zone7d` and the exponent `L = Lnum/Lden`
(`SieveCert.IBPar`). A configuration gives three sets of the box's primes, by the bits of their positions in the
list: `s0`, whose product enters the window with the small primes; `sr`, the rest; `s1`, the primes on the first
side of the leaves; and the flag `e`, the side of the small primes. In units of `1/DEN` of exponents of `x`, with
`ρ₁`, `ρ₂` the sums of the lower and upper ends over `sr`:

* the window `[u, v]` of the first variable is the largest that the region allows for the rests of exponent in
  `[ρ₁ − 1, ρ₂ + 1]` (`uOf`, `vOf`), and `t = u − Σ_{s0} lo` is the growth of the tree (`tOf`);
* `chkJ2` checks the region's six inequalities at these, that the window is wider than the floor (`u + f < v`),
  that the primes of `s0` stay below its upper end, and the paper's two conditions on the leaves' sizes or, where
  they fail, the leaves cut in three (`SieveAdLeafDefs.lean`'s `leavesL`, `leavesE`);
* `chkI2` is the test of a box evaluated outright (`SieveTwoTerm.chain2_bound`): the first variable is the product
  of the primes of `s0`, the rest that of `sr`, and the second variable the other primes and the cofactor; it
  checks the region's six inequalities for the box's ranges.

`mSum F bl m` is the sum of `F` over the cells of the list at the positions whose bit is set in `m`. The file imports
`SieveAdDefs.lean` and `SieveAdLeafDefs.lean` (and through it `SieveRuleDefs.lean`, for `SieveCert.IBPar`).
-/
import SieveAdDefs
import SieveAdLeafDefs

namespace SieveAd

open SieveCert (DEN cdiv)

/-- The sum of `F` over the cells at the positions whose bit is set in `m`. -/
def mSum (F : Cell → ℕ) : List Cell → ℕ → ℕ
  | [], _ => 0
  | c :: b, m => cond (Nat.testBit m 0) (F c) 0 + mSum F b (m / 2)

/-- Every cell has `f ≤ lo ≤ hi ≤ DEN`. -/
def cellsFrom (f : ℕ) : List Cell → Bool
  | [] => true
  | c :: b => Nat.ble f c.1 && Nat.ble c.1 c.2 && Nat.ble c.2 DEN && cellsFrom f b

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- The least lower end of the first variable's window for a rest of exponent at least `ρ₁ − 1`: the least `u`
with `2/3 ≤ Lu/DEN` and `1 − Lu/DEN + 1/12500 ≤ (27637/62500)·L(ρ₁ − 1)/DEN`. -/
def uOf (ρ₁ : ℕ) : ℕ :=
  max (cdiv (2 * Lden * DEN) (3 * Lnum))
    (cdiv (62505 * Lden * DEN + 27637 * Lnum - 27637 * Lnum * ρ₁) (62500 * Lnum))

/-- The largest upper end of the first variable's window for a rest of exponent at most `ρ₂ + 1`. -/
def vOf (ρ₂ : ℕ) : ℕ :=
  min ((3 * Lnum * DEN - 2 * Lden * DEN) / (3 * Lnum) - (ρ₂ + 1))
    ((62500 * Lnum * DEN - 62505 * Lden * DEN - 34863 * Lnum * (ρ₂ + 1)) / (62500 * Lnum))

/-- The checks of the comparison in two variables on a box, at the floor `f`, for the sets `s0`, `sr`, `s1`, the
flag `e`, the window `[u, v]` and the growth `t`; the leaves by the paper's conditions or cut in three. -/
def chkJ2 (bl : List Cell) (f s0 sr s1 : ℕ) (e : Bool) (u v t : ℕ) : Bool :=
  let ρ₁ := mSum (fun c => c.1) bl sr
  let ρ₂ := mSum (fun c => c.2) bl sr
  let D₁ := mSum (fun c => c.2) bl s1 + cond e t 0
  let D₂ := hiSum bl - mSum (fun c => c.2) bl s1 + cond e 0 t
  Nat.blt 0 f && Nat.ble bl.length 13 && cellsFrom f bl && Nat.beq (Nat.land s0 sr) 0 &&
    Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * ρ₁) &&
    Nat.ble (2 * Lden * DEN) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (ρ₂ + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 27637 * Lnum) (62500 * Lnum * u + 27637 * Lnum * ρ₁) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.blt (u + f) v &&
    Nat.ble u (t + mSum (fun c => c.1) bl s0) &&
    Nat.blt (mSum (fun c => c.2) bl s0) v &&
    (leavesL D₁ D₂ || leavesE D₁ D₂)

/-- **The test of the comparison in two variables**: `chkJ2` at the window and the growth that the box gives. -/
def okJ2 (bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  let u := uOf (mSum (fun c => c.1) bl cfg.sr)
  let v := vOf (mSum (fun c => c.2) bl cfg.sr)
  chkJ2 bl f cfg.s0 cfg.sr cfg.s1 cfg.e u v (u - mSum (fun c => c.1) bl cfg.s0)

/-- The checks of the estimate in two variables on a box, for the first variable `s0` and the rest `sr`: the
region's six inequalities for a first variable of exponent in `[u − 1, v]`, `u` and `v` the sums of the lower and
upper ends over `s0`, and a rest of exponent in `[ρ₁ − 1, ρ₂ + 1]`. The second variable is the other primes and
the cofactor. -/
def chkI2 (bl : List Cell) (s0 sr : ℕ) : Bool :=
  let ρ₁ := mSum (fun c => c.1) bl sr
  let ρ₂ := mSum (fun c => c.2) bl sr
  let u := mSum (fun c => c.1) bl s0
  let v := mSum (fun c => c.2) bl s0
  Nat.ble bl.length 13 && cellsFrom 1 bl && Nat.beq (Nat.land s0 sr) 0 &&
    Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * ρ₁) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (ρ₂ + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 90137 * Lnum) (62500 * Lnum * u + 27637 * Lnum * ρ₁) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN)

/-- **The test of a box by the estimate in two variables.** -/
def okI2 (bl : List Cell) (cfg : Cfg) : Bool := chkI2 bl cfg.s0 cfg.sr

/-- **The tests of the estimate in two variables.** -/
def twoTests : Tests := ⟨okI2, okJ2⟩

end SieveAd
