/-
# Strategies for the search with the reversal through the largest prime, without Mathlib

`SieveAdFlipDefs.lean`'s search reverses a box of the sign `−` through its largest prime, and searches a tree over
the frozen part with the tests `frozTests`, by a strategy given for the box. This file has such a strategy, and
the main search's strategy with one more cut.

* `vboxF`: a box of a tree over the frozen part with the frozen part's cofactor as one more cell, after the cells
  of the chain and of the frozen primes: the cofactor's exponent lies between the slab's lower end less the upper
  ends of the frozen primes' cells and the slab's upper end less their lower ends. A set of bits of this box is a
  set of `frozTests`.
* `widen`: the cells widened by the room `Kb` that the tests at a floor ask for.
* `propIF`: the configurations to try on a box of the tree: `propI2`'s on `vboxF`.
* `propJFl`, `propJFF`: the floors to try: `propJF`'s on the widened `vboxF`, a floor at most the least lower end
  of the widened cells of the chain and of the frozen primes.
* `stratFF`: the strategy of the tree over the frozen part of a box: those proposals, chains of fewer than
  `depthR` primes, and `cutsK`'s cuts, from the level `flipT ctx` for the chain's first prime.
* `insCut`, `cutsOfGF`, `stratGFF`: `stratGF` with one more cut of the new prime's range, one unit below the
  largest prime's cell: a box whose second prime is below that cut may pass `flipOK`.

These are arithmetic on natural numbers, lists and booleans, and the file imports only
`SieveAdFillSearchDefs.lean` and `SieveAdFlipDefs.lean`.
-/
import SieveAdFillSearchDefs
import SieveAdFlipDefs

namespace SieveAd

open SieveCert (DEN cdiv)

/-- A box of a tree over the frozen part of `β` with the slab of `ctx`, and the cofactor as one more cell. -/
def vboxF (ctx : Cell) (β bl : List Cell) : List Cell :=
  (fun hi => cond (Nat.blt hi 2) bl (bl ++ [(maxN 1 (Nat.sub (Nat.sub DEN ctx.2) (hiSum β)), hi)]))
    (Nat.sub (Nat.succ (Nat.sub DEN ctx.1)) (loSum β))

/-- The cells widened by `Kb` at each end, the lower ends at least `1`. -/
def widen (Kb : ℕ) : List Cell → List Cell
  | [] => []
  | c :: b => (maxN 1 (Nat.sub c.1 Kb), Nat.add c.2 Kb) :: widen Kb b

variable [SieveCert.IBPar]

/-- The configurations to try on a box of a tree over the frozen part: those of the box with the cofactor. -/
def propIF (ctx : Cell) (β bl : List Cell) : List Cfg :=
  (fun blv => propI2 blv (loSum blv) blv 1) (vboxF ctx β bl)

/-- `propJF`'s floors for the box `bl`, a floor at most `lomin`. -/
def propJFl (bl : List Cell) (lomin : ℕ) : List (ℕ × Cfg) :=
  (fun ls hs =>
    cond (Nat.blt T5 hs) []
      ((fun r =>
        (match cond (Nat.blt r.1 lomin) (propJ3 bl ls hs 8 (minN lomin fmax3)) none with
          | some r3 => cond (Nat.blt r.1 r3.1) [r3] []
          | none => []) ++
        (match r.2 with
          | some cfg => [(r.1, cfg)]
          | none => [])) (propJ2 bl lomin ls hs bl 1 (0, none))))
    (loSum bl) (hiSum bl)

/-- The floors to try on a box of a tree over the frozen part: those of the box with the cofactor, its cells
widened by the room `12 + DEN/lo_s` of the tests, a floor at most the least lower end of the widened cells of the
chain and of the frozen primes. -/
def propJFF (ctx : Cell) (β bl : List Cell) : List (ℕ × Cfg) :=
  (fun Kb => propJFl (widen Kb (vboxF ctx β bl)) (lominOf (widen Kb bl))) (Nat.add 12 (Nat.div DEN (getC β 0).1))

/-- **A strategy for the tree over the frozen part** of a box `β ++ [ctx]`, its chains of fewer than `depthR`
primes, in cells of side at most `hR` and at most the exponent over `κ`. -/
def stratFF (κ hR depthR wmin : ℕ) (ctx : Cell) (β : List Cell) : Strat :=
  ⟨depthR + β.length, wmin, propIF ctx β, propJFF ctx β,
    fun bl f =>
      (fun ch =>
        cutsK κ hR ctx ch
          (match ch with
            | [] => flipT ctx
            | x :: _ => x.2) f) (chainOf β.length bl)⟩

/-- A cut put in its place among increasing cuts, if it is not there. -/
def insCut (c : ℕ) : List ℕ → List ℕ
  | [] => [c]
  | x :: r => cond (Nat.blt c x) (c :: x :: r) (cond (Nat.beq c x) (x :: r) (x :: insCut c r))

/-- `cutsOfG`'s cuts and one more, one unit below the largest prime's cell, if it is above the floor. -/
def cutsOfGF (κ hI : ℕ) (bl : List Cell) (f : ℕ) : List ℕ :=
  (fun c cs => cond (Nat.blt f c) (insCut c cs) cs) (Nat.sub (lastC bl).1 1) (cutsOfG κ hI bl f)

/-- **A strategy for `fillTests`** with the reversal through the largest prime: `stratGF` with `cutsOfGF`'s
cuts. -/
def stratGFF (κ hI depth wmin : ℕ) : Strat :=
  ⟨depth, wmin, fun bl => propI2 bl (loSum bl) bl 1, propJF, cutsOfGF κ hI⟩

end SieveAd
