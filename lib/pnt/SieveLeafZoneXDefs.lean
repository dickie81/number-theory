/-
# The test of the leaves' region above `√q` on a rectangle, in natural numbers, without Mathlib

Written by `tools/linnik/gen_leafzone.py`; do not edit.

`leafXR Ln Ld D P₁ P₂ R₁ R₂`: the 19 inequalities of `SieveLeafZoneX.LeafZoneXL` for `m₁ = κP`, `ρ = κR`, `L = κD`
with `Ln = Ld·D·κ` (exponents of `x` in units of `1/D`, `L = Ln/Ld`), each times `Ld·D` and its denominator, each at
the corner of the rectangle `[P₁, P₂] × [R₁, R₂]` where its linear form is largest, so that it holds on the whole
rectangle. Its soundness is `SieveLeafZoneX.leafXR_sound`. The arithmetic of `ℕ` is written out, and the products
`Ln·P₁`, `Ln·P₂`, `Ln·R₁`, `Ln·R₂`, `Ld·D`, `Ln·D` are computed once: the kernel evaluates the test where the sieve's
leaves are cut in three.
-/

namespace SieveLeafZoneX

/-- **The test of `LeafZoneXL` on a rectangle in natural numbers**: `m₁ = κP` for `P` in `[P₁, P₂]`, `ρ = κR` for `R`
in `[R₁, R₂]`, `L = κD`, each inequality times `Ld·D` and its denominator, with `Ln = Ld·D·κ`, at its worst corner. -/
def leafXR (Ln Ld D P₁ P₂ R₁ R₂ : Nat) : Bool :=
  (fun lp1 lp2 lr1 lr2 ld ln =>
    Nat.ble (Nat.mul 9 ld) (Nat.mul 10 lp1) &&
      Nat.ble (Nat.mul 5 lp2) (Nat.mul 6 ld) &&
      Nat.ble (Nat.add (Nat.add (Nat.mul 5 lp2) (Nat.mul 5 lr2)) (Nat.mul 2 ld)) (Nat.mul 5 ln) &&
      Nat.ble (Nat.mul 3 ld) (Nat.mul 10 lr1) &&
      Nat.ble lr2 ld &&
      Nat.ble (Nat.add (Nat.mul 125007 lr2) (Nat.mul 1750070 ld)) (Nat.mul 875000 ln) &&
      Nat.ble (Nat.add (Nat.add (Nat.mul 875000 lp2) (Nat.mul 125007 lr2)) (Nat.mul 875070 ld))
        (Nat.mul 875000 ln) &&
      Nat.ble (Nat.add (Nat.mul 23200336 lr2) (Nat.mul 73693427 ld)) (Nat.mul 42000000 ln) &&
      Nat.ble (Nat.add (Nat.add (Nat.mul 750000 lp2) (Nat.mul 625006 lr2)) (Nat.mul 439685 ld))
        (Nat.mul 750000 ln) &&
      Nat.ble (Nat.add (Nat.mul 36100672 lr2) (Nat.mul 154117185 ld)) (Nat.mul 84000000 ln) &&
      Nat.ble (Nat.add (Nat.add (Nat.mul 84000000 lp2) (Nat.mul 36100672 lr2)) (Nat.mul 70117185 ld))
        (Nat.mul 84000000 ln) &&
      Nat.ble (Nat.add (Nat.add (Nat.mul 3458000 lp2) (Nat.mul 23200336 lr2)) (Nat.mul 70467547 ld))
        (Nat.mul 42000000 ln) &&
      Nat.ble (Nat.mul 1312570 ld) (Nat.add (Nat.mul 875000 lp1) (Nat.mul 749993 lr1)) &&
      Nat.ble (Nat.mul 437570 ld) (Nat.mul 749993 lr1) &&
      Nat.ble (Nat.mul 52693427 ld) (Nat.add (Nat.mul 42000000 lp1) (Nat.mul 18799664 lr1)) &&
      Nat.ble (Nat.mul 64685 ld) (Nat.mul 124994 lr1) &&
      Nat.ble (Nat.mul 112117185 ld) (Nat.add (Nat.mul 84000000 lp1) (Nat.mul 47899328 lr1)) &&
      Nat.ble (Nat.mul 28117185 ld) (Nat.mul 47899328 lr1) &&
      Nat.ble (Nat.mul 49467547 ld) (Nat.add (Nat.mul 38542000 lp1) (Nat.mul 18799664 lr1)))
    (Nat.mul Ln P₁) (Nat.mul Ln P₂) (Nat.mul Ln R₁) (Nat.mul Ln R₂) (Nat.mul Ld D) (Nat.mul Ln D)

end SieveLeafZoneX
