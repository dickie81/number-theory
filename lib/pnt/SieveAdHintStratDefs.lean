/-
# Guides for the search led by hints, without Mathlib

`SieveAdHintDefs.lean`'s search takes Buchstab's identity at the floor and with the configuration that a guide
gives for four bits of its hints. The strategies of `SieveAdSearchDefs.lean` and `SieveAdFillSearchDefs.lean`
propose a floor by trying every prime of the box as the rest, and eight floors for a rest among the tree's
primes; a guide computes one of these proposals, the one that the four bits name.

* `tryJ2`: `propJ2`'s proposal for the rest at one cell: the floor that the window of that rest allows, the set
  with the largest lower sum below the window's upper end, and a split of the leaves.
* `floorJ3`: the floor of `propJ3` after a number of steps.
* `guideJ`: for the bits `2j`, `tryJ2` at the cell of index `j`; for `2i + 1`, `tryJ3` at the floor after `i`
  steps.
* `guideG`: the guide of the main search. `guideF`: the guide of a tree over the frozen part of a box, on the box
  with the cofactor as one more cell, widened by the room of the tests, as `propJFF` has it.

These are arithmetic on natural numbers, lists and booleans, and the file imports only
`SieveAdFlipStratDefs.lean` and `SieveAdHintDefs.lean`.
-/
import SieveAdFlipStratDefs
import SieveAdHintDefs

namespace SieveAd

open SieveCert (DEN cdiv)

variable [SieveCert.IBPar]

/-- `propJ2`'s proposal for the rest at the cell `c`, of the bit `bit`: the floor `min(lomin, v − u − 1)` for the
window `[u, v]` of that rest, with the set of largest lower sum below `v` and a split of the leaves, if there is
one. -/
def tryJ2 (bl : List Cell) (lomin ls hs : ℕ) (c : Cell) (bit : ℕ) : Option (ℕ × Cfg) :=
  cond (restOK c)
    ((fun u v =>
      (fun f =>
        cond (Nat.blt 0 f && Nat.ble (Nat.add hs (Nat.sub u (Nat.sub ls c.1))) T5)
          ((fun b =>
            match leavesOf bl hs (Nat.sub u b.1) with
            | some sp => some (f, ⟨1, b.2, bit, sp.1, sp.2⟩)
            | none => none) (bestSub v bit bl 1 0 0 0 (Nat.sub ls c.1) (0, 0)))
          none) (minN lomin (Nat.sub v (Nat.succ u)))) (uOfF c.1) (vOfF c.2))
    none

/-- `f` after `i` steps of `propJ3`: `⌊3f/4⌋`, `i` times. -/
def floorJ3 : ℕ → ℕ → ℕ
  | 0, f => f
  | i + 1, f => floorJ3 i (Nat.div (Nat.mul 3 f) 4)

/-- **A guide** for the box `bl` and floors at most `lomin`: for `sel = 2j`, the comparison with the rest at the
cell of index `j`; for `sel = 2i + 1`, the comparison with the rest among the tree's primes at the floor after `i`
steps from `min(lomin, fmax3)`. -/
def guideJ (bl : List Cell) (lomin sel : ℕ) : Option (ℕ × Cfg) :=
  (fun ls hs =>
    cond (Nat.blt T5 hs) none
      (cond (Nat.beq (Nat.mod sel 2) 0)
        (tryJ2 bl lomin ls hs (getC bl (Nat.div sel 2)) (Nat.pow 2 (Nat.div sel 2)))
        (tryJ3 bl ls hs (floorJ3 (Nat.div sel 2) (minN lomin fmax3)))))
    (loSum bl) (hiSum bl)

/-- **The guide of the main search.** -/
def guideG (bl : List Cell) (sel : ℕ) : Option (ℕ × Cfg) := guideJ bl (lominOf bl) sel

/-- **The guide of a tree over the frozen part** of a box `β ++ [ctx]`: `guideJ` on the box with the cofactor,
its cells widened by the room `12 + DEN/lo_s` of the tests, a floor at most the least lower end of the widened
cells of the chain and of the frozen primes. -/
def guideF (ctx : Cell) (β bl : List Cell) (sel : ℕ) : Option (ℕ × Cfg) :=
  (fun Kb => guideJ (widen Kb (vboxF ctx β bl)) (lominOf (widen Kb bl)) sel)
    (Nat.add 12 (Nat.div DEN (getC β 0).1))

end SieveAd
