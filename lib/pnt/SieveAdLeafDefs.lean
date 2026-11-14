/-
# The leaves of the comparison in two variables cut in three, without Mathlib

The comparison in two variables (`SieveAdTwoDefs.lean`'s `chkJ2`, `SieveAdCoreDefs.lean`'s `coreJ2`) checks the
leaves' sizes `D₁`, `D₂`, in units of `1/DEN` of exponents of `x`, so that `κD` is an exponent of `q` with
`κ = L/DEN`. The paper's two conditions, `κD₁ < L − 1` and `max(κD₁, 1) + κD₁ + 2κD₂ < 2L − 1`, are three
inequalities (`leavesL`). Where they fail, the leaves may be cut in three (`SieveTwoCompE.prop6_two3`): the leaves
with `d₁ ≤ q^{κP}`, `P = pStar D₂`, by the paper's conditions at `(P, D₂)`; the others with `d₂ ≤ q^{κθ}`,
`θ = thetaL D₁`, by those at `(D₁, θ)`; and the rest by the estimate in two variables with the cofactor as the second
variable (`SieveLeafTwo.leaf2_bound`), which asks the region `SieveLeafZoneX.LeafZoneXL` on the rectangle
`[κ(P − 1), κ(D₁ + 1)] × [κ(θ − 1), κ(D₂ + 1)]` of the exponents of `d₁` and `d₂`: each of its half-planes at the
corner where it is tightest (`SieveLeafZoneX.leafXR`).

* `leavesL`: the paper's conditions. The arithmetic of `ℕ` is written out here, as in `SieveAdFastDefs.lean`: the
  kernel evaluates these tests at the boxes of a certificate.
* `pStar`, `thetaL`: the largest `P` with the conditions at `(P, D₂)` and the largest `θ` with them at `(D₁, θ)`, by
  division. `leavesE` checks the conditions at them, so nothing rests on these values being the largest.
* `leavesE`: **the leaves cut in three**: the conditions at `(P, D₂)` and at `(D₁, θ)`, `D₁ + D₂ < DEN`, and the
  region on the rectangle.

The file imports `SieveRuleDefs.lean` (for `SieveCert.IBPar`) and `SieveLeafZoneXDefs.lean`.
-/
import SieveRuleDefs
import SieveLeafZoneXDefs

namespace SieveAd

open SieveCert (DEN)

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- The paper's conditions on the leaves' sizes `D₁`, `D₂`: `κD₁ + 1 < L`, `2κ(D₁ + D₂) + 1 < 2L` and
`κ(D₁ + 2D₂) + 2 < 2L`, each times `Lden·DEN` (the second and third are the two cases of `max(κD₁, 1)`), with the
arithmetic of `ℕ` written out. -/
def leavesL (D₁ D₂ : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul Lnum D₁) (Nat.mul Lden DEN)) (Nat.mul Lnum DEN) &&
    Nat.blt (Nat.add (Nat.mul (Nat.mul 2 Lnum) (Nat.add D₁ D₂)) (Nat.mul Lden DEN)) (Nat.mul (Nat.mul 2 Lnum) DEN) &&
    Nat.blt (Nat.add (Nat.mul Lnum (Nat.add D₁ (Nat.mul 2 D₂))) (Nat.mul (Nat.mul 2 Lden) DEN))
      (Nat.mul (Nat.mul 2 Lnum) DEN)

/-- The smaller of two numbers. -/
def minN (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

/-- The cut of `d₁`: the largest `P` with `leavesL P D₂`, when there is one. -/
def pStar (D₂ : ℕ) : ℕ :=
  minN (Nat.div (Nat.sub (Nat.sub (Nat.mul Lnum DEN) (Nat.mul Lden DEN)) 1) Lnum)
    (minN (Nat.sub (Nat.div (Nat.sub (Nat.sub (Nat.mul (Nat.mul 2 Lnum) DEN) (Nat.mul Lden DEN)) 1) (Nat.mul 2 Lnum)) D₂)
      (Nat.sub (Nat.div (Nat.sub (Nat.sub (Nat.mul (Nat.mul 2 Lnum) DEN) (Nat.mul (Nat.mul 2 Lden) DEN)) 1) Lnum)
        (Nat.mul 2 D₂)))

/-- The cut of `d₂`: the largest `θ` with `leavesL D₁ θ`, when there is one. -/
def thetaL (D₁ : ℕ) : ℕ :=
  minN (Nat.sub (Nat.div (Nat.sub (Nat.sub (Nat.mul (Nat.mul 2 Lnum) DEN) (Nat.mul Lden DEN)) 1) (Nat.mul 2 Lnum)) D₁)
    (Nat.div
      (Nat.sub (Nat.sub (Nat.sub (Nat.mul (Nat.mul 2 Lnum) DEN) (Nat.mul (Nat.mul 2 Lden) DEN)) 1) (Nat.mul Lnum D₁))
      (Nat.mul 2 Lnum))

/-- **The leaves of sizes `D₁`, `D₂` cut in three**: the paper's conditions at `(P, D₂)` and at `(D₁, θ)`, with
`P = pStar D₂` and `θ = thetaL D₁`, `D₁ + D₂ < DEN`, `P, θ ≥ 1`, and the region `LeafZoneXL` on the rectangle
`[P − 1, D₁ + 1] × [θ − 1, D₂ + 1]` (`SieveLeafZoneX.leafXR`). -/
def leavesE (D₁ D₂ : ℕ) : Bool :=
  (fun P θ =>
    leavesL P D₂ && leavesL D₁ θ && Nat.blt (Nat.add D₁ D₂) DEN && Nat.ble 1 P && Nat.ble 1 θ &&
      SieveLeafZoneX.leafXR Lnum Lden DEN (Nat.sub P 1) (Nat.succ D₁) (Nat.sub θ 1) (Nat.succ D₂))
    (pStar D₂) (thetaL D₁)

end SieveAd
