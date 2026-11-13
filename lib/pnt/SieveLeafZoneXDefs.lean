/-
# The test of the leaves' region above `√q` at a point, in natural numbers, without Mathlib

Written by `tools/linnik/gen_leafzone.py`; do not edit.

`leafXN Ln Ld D P R`: the 19 inequalities of `SieveLeafZoneX.LeafZoneXL` at `m₁ = κP`, `ρ = κR`, `L = κD` with
`Ln = Ld·D·κ` (exponents of `x` in units of `1/D`, `L = Ln/Ld`), each times `Ld·D` and its denominator. Its soundness
is `SieveLeafZoneX.leafXN_sound`.
-/

namespace SieveLeafZoneX

/-- **The test of `LeafZoneXL` at a point in natural numbers**: `m₁ = κP`, `ρ = κR`, `L = κD`, each inequality times
`Ld·D` and its denominator, with `Ln = Ld·D·κ`. -/
def leafXN (Ln Ld D P R : Nat) : Bool :=
  Nat.ble (9 * Ld * D) (10 * Ln * P) &&
    Nat.ble (5 * Ln * P) (6 * Ld * D) &&
    Nat.ble (5 * Ln * P + 5 * Ln * R + 2 * Ld * D) (5 * Ln * D) &&
    Nat.ble (3 * Ld * D) (10 * Ln * R) &&
    Nat.ble (Ln * R) (Ld * D) &&
    Nat.ble (125007 * Ln * R + 1750070 * Ld * D) (875000 * Ln * D) &&
    Nat.ble (875000 * Ln * P + 125007 * Ln * R + 875070 * Ld * D) (875000 * Ln * D) &&
    Nat.ble (23200336 * Ln * R + 73693427 * Ld * D) (42000000 * Ln * D) &&
    Nat.ble (750000 * Ln * P + 625006 * Ln * R + 439685 * Ld * D) (750000 * Ln * D) &&
    Nat.ble (36100672 * Ln * R + 154117185 * Ld * D) (84000000 * Ln * D) &&
    Nat.ble (84000000 * Ln * P + 36100672 * Ln * R + 70117185 * Ld * D) (84000000 * Ln * D) &&
    Nat.ble (3458000 * Ln * P + 23200336 * Ln * R + 70467547 * Ld * D) (42000000 * Ln * D) &&
    Nat.ble (1312570 * Ld * D) (875000 * Ln * P + 749993 * Ln * R) &&
    Nat.ble (437570 * Ld * D) (749993 * Ln * R) &&
    Nat.ble (52693427 * Ld * D) (42000000 * Ln * P + 18799664 * Ln * R) &&
    Nat.ble (64685 * Ld * D) (124994 * Ln * R) &&
    Nat.ble (112117185 * Ld * D) (84000000 * Ln * P + 47899328 * Ln * R) &&
    Nat.ble (28117185 * Ld * D) (47899328 * Ln * R) &&
    Nat.ble (49467547 * Ld * D) (38542000 * Ln * P + 18799664 * Ln * R)

end SieveLeafZoneX
