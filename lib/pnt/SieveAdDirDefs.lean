/-
# The search led by hints, without Mathlib

`SieveAdRevDefs.lean`'s search tries, at each box, what its strategy proposes: the configurations that may
evaluate the box, then the box dropped against Buchstab's identity below it, then one more bound. Most of what the
kernel does in it is lost: trees searched below a box that is then dropped or bounded otherwise, the search for a
configuration that evaluates a box or the terms at a floor among the sets of the box's cells, and traversals of
the box, one for each sum read from it, with the arithmetic of the type classes. Here the search is told what to
do at each box by a number, the **hints**, read from its low end in the order in which the search visits the
boxes; the hints carry the configuration of each step and the cuts of each new prime's range; and what is left
for the kernel is written for it: one pass over a box by the recursor of lists for each thing read from it, and
the arithmetic of `ℕ` written out. A step whose test fails returns its limit, which says nothing: the hints
choose among bounds that hold, and the cost returned is a bound whatever they are (`SieveAdDir.lean`).

The hints are read from the low end. At a box:

* `0`, the cell `j` of the rest (`0` for the first, or `1` and three bits) and a set `m` of the box's cells: the
  configuration `⟨1, m, 2^j, 0, false⟩` evaluates the box (cost `0`);
* `10`, four bits `sel`, a set `s0`, and `0` (for the set `s1` of all the cells but the last and the side
  `true`) or `1`, a set `s1` and a bit: Buchstab's identity, with the rest at the cell
  `sel/2` (`sel` even: the floor is the least of the lower ends and of the window's width for that rest) or among
  the tree's primes (`sel` odd: the floor after `sel/2` steps from the largest), and the cells of the new prime,
  each cut a code (`kidsCS`): the number of steps of the grid from the last cut, or one of three cuts off it;
* `110`: the box is dropped;
* `1110`: a bound that reads hints itself;
* `11110`: the last prime's cell cut in two;
* `111110`: the box has no term;
* `111111`: the bound `Ops.alt`.

A set is as many bits as the box has cells (one more over a frozen part, for the cofactor).

* `lnTP`, `omFkP`, `omFP`, `invKwP`, `omKwP`, `trFP`, `exFP`, `cdivP`: `SieveCert.omKw` and the factors of a
  cell, with the arithmetic of `ℕ` written out.
* `tailP`, `drpMP`: the cost of a dropped box of the main tree in one pass. `chainP`, `drpKP`, `opsKP`: the same
  for the chain of a box of a tree over a frozen part.
* `gridP`, `cutK`, `kidsCS`, `kidsC`: the cells of the new prime, their cuts read from the hints as numbers of
  steps of the grid. `sumsP`, `kidsM`: those of the main tree, with the grid and the other cuts of `cutsOfGF`.
  `headP`, `kidsF`: those of a tree over a frozen part, with the grid and the other cuts of `stratFF`, from a
  pass over the chain's cells, the cells of the box before the frozen primes'.
* `partDS`, `partD`: the cells of the new prime cut at given cuts, for a part of the search.
* `stepD`, `solveD`: the search. `noAltH`: no bound that reads hints.
* `pickP`, `cfgIM`, `cfgJM`: the configurations of the main tree, read from the hints. `cfgIF`, `pickC`, `cfgJF`:
  those of a tree over a frozen part. A box of such a tree is a chain's cells followed by the frozen primes of
  the tree: `cfgJF` reads the chain in a pass, and what it takes from the frozen primes does not depend on the
  box, so the kernel computes it once for a tree (`canonN`), as for the tests `frozTestsC`.
* `lastP`, `initP`, `flipOKP`, `flipTreeD`, `flipCostB`, `flipCostD`, `altFD`: the reversal of a box through its
  largest prime, its tree searched this way.

`SieveAdDir.lean` proves what a cost returned below its limit gives. The file imports `SieveAdFastDefs.lean` and
`SieveAdFlipStratDefs.lean`.
-/
import SieveAdFastDefs
import SieveAdFlipStratDefs

namespace SieveAd

open SieveCert (DEN K cdiv topK w1K LD)

/-! ### Buchstab's function and the factors of a cell, with the arithmetic written out -/

/-- `SieveCert.cdiv`. -/
def cdivP (a b : ℕ) : ℕ := Nat.div (Nat.sub (Nat.add a b) 1) b

/-- `SieveCert.lnT`. -/
def lnTP (k : ℕ) : ℕ :=
  cond (Nat.blt k 8)
    (cond (Nat.blt k 4)
      (cond (Nat.blt k 2) (cond (Nat.blt k 1) 0 60624623) (cond (Nat.blt k 3) 117783037 171850258))
      (cond (Nat.blt k 6) (cond (Nat.blt k 5) 223143553 271933717) (cond (Nat.blt k 7) 318453733 362905495)))
    (cond (Nat.blt k 16)
      (cond (Nat.blt k 12)
        (cond (Nat.blt k 10) (cond (Nat.blt k 9) 405465110 446287104) (cond (Nat.blt k 11) 485507817 523248145))
        (cond (Nat.blt k 14) (cond (Nat.blt k 13) 559615789 594707109) (cond (Nat.blt k 15) 628608661 661398484)))
      693147182)

/-- `SieveCert.omFk`. -/
def omFkP (P Q k A B : ℕ) : ℕ :=
  cdivP
    (Nat.mul (Nat.mul K Q)
      (Nat.add (Nat.mul (Nat.mul (Nat.mul 2 A) B) (Nat.add LD (lnTP k)))
        (Nat.mul (Nat.sub (Nat.mul A A) (Nat.mul B B)) LD)))
    (Nat.mul (Nat.mul (Nat.mul (Nat.mul 2 A) B) LD) P)

/-- `SieveCert.omF`. -/
def omFP (P Q : ℕ) : ℕ :=
  (fun k => omFkP P Q k (Nat.mul 16 (Nat.sub P Q)) (Nat.mul (Nat.add 16 k) Q))
    (Nat.div (Nat.mul 16 (Nat.sub P (Nat.mul 2 Q))) Q)

/-- `SieveCert.invKw`. -/
def invKwP (s t W w : ℕ) : ℕ :=
  cond (Nat.ble DEN (Nat.add (Nat.add (Nat.add s (Nat.mul 2 t)) W) w)) K
    (cdivP (Nat.mul K (Nat.add t w)) (Nat.sub (Nat.sub (Nat.sub DEN s) t) W))

/-- `SieveCert.omKw`. -/
def omKwP (s t W w : ℕ) : ℕ :=
  cond (Nat.blt DEN (Nat.add s (Nat.mul 2 t))) 0
    (cond (Nat.ble (Nat.add (Nat.add (Nat.add s (Nat.mul 4 t)) W) (Nat.mul 3 w)) DEN) topK
      (cond (Nat.blt DEN (Nat.add s (Nat.mul 3 t))) (invKwP s t W w)
        (maxN
          (maxN
            (cond (Nat.ble (Nat.add (Nat.add (Nat.add s (Nat.mul 3 t)) W) (Nat.mul 2 w)) DEN) 0 (invKwP s t W w))
            (cond (Nat.ble (Nat.mul 100 (Nat.sub (Nat.sub (Nat.add DEN 1) s) t)) (Nat.mul 276 t))
              (omFP (Nat.sub (Nat.sub (Nat.add DEN 1) s) t) t)
              (cond (Nat.ble (Nat.mul 277 (Nat.add t w)) (Nat.mul 100 (Nat.sub (Nat.sub (Nat.sub DEN s) t) W)))
                (omFP (Nat.sub (Nat.sub (Nat.sub DEN s) t) W) (Nat.add t w)) w1K)))
          (cond (Nat.ble (Nat.add s (Nat.mul 4 t)) DEN) topK 0))))

/-- `trF`. -/
def trFP (a w : ℕ) : ℕ :=
  cdivP (Nat.mul SC (Nat.mul w (Nat.add (Nat.mul 2 a) w))) (Nat.mul (Nat.mul 2 a) (Nat.add a w))

/-- `exF`. -/
def exFP (a w : ℕ) : ℕ := cdivP (Nat.mul SC (Nat.mul DEN w)) (Nat.mul a (Nat.add a w))

/-- `1` for a cell with `0 < lo < hi`, else `0`. -/
def cellI (x : Cell) : ℕ := Nat.mul (Nat.sub 1 (Nat.sub 1 x.1)) (Nat.sub 1 (Nat.sub 1 (Nat.sub x.2 x.1)))

/-! ### The cost of a dropped box in one pass -/

/-- **One pass over the cells of a box after the first**: `k` is given the sums of their lower and of their upper
ends, the product of their factors `trF`, the product of `cellI` over them, their number, and the upper end of
the last, added to or multiplied into the values they start from. -/
noncomputable def tailP {α : Type} : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → α) → α :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → α) → α)
    (fun ls hs tp ok n lh k => k ls hs tp ok n lh)
    (fun x _ ih ls hs tp ok n _ k =>
      ih (Nat.add ls x.1) (Nat.add hs x.2) (Nat.mul tp (trFP x.1 (Nat.sub x.2 x.1))) (Nat.mul ok (cellI x))
        (Nat.succ n) x.2 k)

/-- `dropCost`'s formula for a box whose first cell is `c` and whose other cells have the sums `ls`, `hs`, the
product of factors `tp` and the number `n`. -/
def dropF (c : Cell) (ls hs tp n : ℕ) : ℕ :=
  cdivP
    (Nat.mul (omKwP ls c.1 (Nat.sub (Nat.add c.2 hs) (Nat.add c.1 ls)) (Nat.sub c.2 c.1))
      (Nat.mul (exFP c.1 (Nat.sub c.2 c.1)) tp))
    (Nat.pow SC (Nat.succ n))

/-- **`dropC` in one pass.** -/
noncomputable def drpMP (bl : List Cell) (par : Bool) : Option ℕ :=
  match bl with
  | [] => none
  | c :: b =>
    cond par
      (tailP b 0 0 1 (cellI c) 0 0 fun ls hs tp ok n _ =>
        cond (Nat.beq ok 1 && Nat.ble (Nat.add c.2 hs) DEN) (some (dropF c ls hs tp n))
          (cond
            (Nat.blt 0 n && Nat.beq ok 1 && Nat.ble (Nat.add DEN 1) (Nat.add (Nat.add c.1 ls) c.1) &&
              Nat.blt hs DEN)
            (some (cdivP (Nat.mul (Nat.mul K DEN) tp) (Nat.mul (Nat.sub DEN hs) (Nat.pow SC n)))) none))
      none

/-- The nodes of the main tree, a dropped box's cost in one pass. -/
noncomputable def opsMP : Ops := ⟨fun _ => true, vanishOK, drpMP, fun _ _ l => l⟩

/-- `tailP` over the first `j` cells. -/
noncomputable def chainP {α : Type} :
    List Cell → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → α) → α :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → α) → α)
    (fun _ ls hs tp ok n k => k ls hs tp ok n)
    (fun x _ ih j ls hs tp ok n k =>
      cond (Nat.beq j 0) (k ls hs tp ok n)
        (ih (Nat.sub j 1) (Nat.add ls x.1) (Nat.add hs x.2) (Nat.mul tp (trFP x.1 (Nat.sub x.2 x.1)))
          (Nat.mul ok (cellI x)) (Nat.succ n) k))

/-- **`dropK` of the first `j` cells of a box, in one pass.** -/
noncomputable def drpKP (ctx : Cell) (j : ℕ) (bl : List Cell) (par : Bool) : Option ℕ :=
  match bl with
  | [] => none
  | c :: b =>
    cond (Nat.beq j 0) none
      (chainP b (Nat.sub j 1) 0 0 1 (cellI c) 0 fun ls hs tp ok n =>
        cond (par && Nat.beq ok 1 && Nat.ble (Nat.add (Nat.add c.2 hs) 1) ctx.1)
          (some
            (cdivP
              (Nat.mul
                (omKwP (Nat.add ls (Nat.sub DEN ctx.2)) c.1
                  (Nat.add (Nat.sub (Nat.add c.2 hs) (Nat.add c.1 ls)) (Nat.add (Nat.sub ctx.2 ctx.1) 1))
                  (Nat.sub c.2 c.1))
                (Nat.mul (exFP c.1 (Nat.sub c.2 c.1)) tp))
              (Nat.pow SC (Nat.succ n))))
          none)

/-- `opsK`, a dropped box's cost in one pass. -/
noncomputable def opsKP (ctx : Cell) (na : ℕ) : Ops :=
  ⟨fun bl => Nat.blt na (lenR bl) && Nat.ble (lenR bl) 12, fun bl => vanishK ctx (chainOf na bl),
    fun bl par => drpKP ctx (Nat.sub (lenR bl) na) bl par, fun _ _ l => l⟩

/-! ### The search -/

/-- No bound that reads hints. -/
def noAltH (_ : List Cell) (_ : Bool) (l h : ℕ) : ℕ × ℕ := (l, h)


/-- The step of the grid at `c`: `max(1, min(st, ⌊c/κ⌋))`. -/
def stpP (κ st c : ℕ) : ℕ := (fun m => Nat.add m (Nat.sub 1 m)) (Nat.sub st (Nat.sub st (Nat.div c κ)))

/-- The grid's point `k` steps after `c`: `geoCuts`'s points, without their end. -/
noncomputable def gridP (κ st k c : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun c => c) (fun _ ih c => ih (Nat.add c (stpP κ st c))) k c

/-- **A cut** at `p` of the new prime's range, of which `a` begins the part not yet searched: `p` must lie
strictly between `a` and `top`; the cell from `a` to `p` is searched, and what follows, `kont`, starts from `p`
with the limit and the hints that it leaves. -/
noncomputable def cutK (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (top : ℕ) (bl : List Cell) (par : Bool)
    (p : ℕ) (kont : ℕ → ℕ → ℕ → ℕ × ℕ) (a lim h : ℕ) : ℕ × ℕ :=
  Bool.rec (motive := fun _ => ℕ × ℕ) (lim, h)
    (Bool.rec (motive := fun _ => ℕ × ℕ) (lim, h)
      ((fun r =>
        Bool.rec (motive := fun _ => ℕ × ℕ)
          ((fun r2 => (Nat.add r.1 r2.1, r2.2)) (kont p (Nat.sub lim r.1) r.2)) r (Nat.ble lim r.1))
        (rec ((a, p) :: bl) par lim h))
      (Nat.ble (Nat.succ p) top))
    (Nat.ble (Nat.succ a) p)

/-- **The next cell of the new prime**, its cut read from the hints as a code: `0`, no more cut, the last cell,
from `a` to `top`, is searched; `1` and two bits `j < 3`, a cut at the grid's point `j + 1` steps after the last
one used, `c`; `1`, `11` and three bits `t`: for `t < 4` a cut `t + 4` steps after; for `t = 4` seven steps and
no cut; for `t = 5`, `6`, `7` a cut at `reg`, at `e`, at `last`, the grid where it was. What follows a cut is
`ih` at the grid's point last used. -/
noncomputable def kidsCS (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (top : ℕ) (bl : List Cell) (par : Bool)
    (κ st reg e last : ℕ) (ih : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ) (c a lim h : ℕ) : ℕ × ℕ :=
  Bool.rec (motive := fun _ => ℕ × ℕ) (rec ((a, top) :: bl) par lim (Nat.div h 2))
    ((fun j h1 =>
      Bool.rec (motive := fun _ => ℕ × ℕ)
        ((fun p => cutK rec top bl par p (ih p) a lim h1) (gridP κ st (Nat.succ j) c))
        ((fun t h2 =>
          Bool.rec (motive := fun _ => ℕ × ℕ)
            (Bool.rec (motive := fun _ => ℕ × ℕ)
              (cutK rec top bl par
                (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) last e (Nat.beq t 6)) reg
                  (Nat.beq t 5))
                (ih c) a lim h2)
              (ih (gridP κ st 7 c) a lim h2) (Nat.beq t 4))
            ((fun p => cutK rec top bl par p (ih p) a lim h2) (gridP κ st (Nat.add t 4) c)) (Nat.ble t 3))
          (Nat.land h1 7) (Nat.div h1 8))
        (Nat.beq j 3))
      (Nat.land (Nat.div h 2) 3) (Nat.div h 8))
    (Nat.beq (Nat.land h 1) 1)

/-- **The cells of the new prime from `a` to `top`**, their cuts read from the hints (`kidsCS`), at most `n` of
them. -/
noncomputable def kidsC (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (top : ℕ) (bl : List Cell) (par : Bool)
    (κ st reg e last : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ × ℕ) (fun _ _ lim h => (lim, h))
    (fun _ ih => kidsCS rec top bl par κ st reg e last ih)

/-- One pass over a box: the sums of the lower and of the upper ends, the number of cells and the lower end of
the last. -/
noncomputable def sumsP {α : Type} : List Cell → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → α) → α :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → α) → α) (fun ls hs n ll k => k ls hs n ll)
    (fun x _ ih ls hs n _ k => ih (Nat.add ls x.1) (Nat.add hs x.2) (Nat.succ n) x.1 k)

/-- **The cells of the new prime in the main tree**, from the floor `f` to `top`: the grid and the three other
cuts are `cutsOfGF`'s, the cut where the new prime's square is too large for a term with a cofactor, the cut one
unit below the largest prime's cell, and the cut where the product of all the primes reaches `x`. -/
noncomputable def kidsM (κ hI : ℕ) (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (top : ℕ) (bl : List Cell)
    (par : Bool) (f lim h : ℕ) : ℕ × ℕ :=
  sumsP bl 0 0 0 0 fun ls hs n ll =>
    kidsC rec top bl par κ (stepOf hI (Nat.succ n)) (minN top (Nat.add (Nat.div (Nat.sub DEN ls) 2) 2))
      (Nat.sub ll 1) (Nat.sub (Nat.sub DEN 1) hs) 4096 f f lim h

/-- One pass over the first `j` cells of a box: the sums of their lower and of their upper ends. -/
noncomputable def headP {α : Type} : List Cell → ℕ → ℕ → ℕ → (ℕ → ℕ → α) → α :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → (ℕ → ℕ → α) → α) (fun _ ls hs k => k ls hs)
    (fun x _ ih j ls hs k =>
      Bool.rec (motive := fun _ => α) (ih (Nat.sub j 1) (Nat.add ls x.1) (Nat.add hs x.2) k) (k ls hs)
        (Nat.beq j 0))

/-- **The cells of the new prime in a tree over a frozen part** of `nb` frozen primes, from the floor `f` to
`top`: the grid and the two other cuts are `stratFF`'s, from the sums of the chain's cells, the cells of the box
before the frozen primes'. -/
noncomputable def kidsF (κ hR : ℕ) (ctx : Cell) (nb : ℕ) (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (top : ℕ)
    (bl : List Cell) (par : Bool) (f lim h : ℕ) : ℕ × ℕ :=
  (fun nch =>
    headP bl nch 0 0 fun lsc hsc =>
      kidsC rec top bl par κ (cond (Nat.blt nch 2) hR (Nat.mul 2 hR))
        (minN top (Nat.add (Nat.div (Nat.sub (Nat.succ ctx.2) lsc) 2) 2)) 0 (Nat.sub (Nat.sub ctx.1 1) hsc) 4096 f f
        lim h)
    (Nat.sub (lenR bl) nb)

/-- A cell of the new prime from `a` to the cut `c`, which must lie strictly between `a` and `top`, and what
follows, `ih`, from `c` with the limit and the hints that the cell leaves. -/
noncomputable def partDS (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (top : ℕ) (bl : List Cell) (par : Bool) (c : ℕ)
    (ih : ℕ → ℕ → ℕ → ℕ × ℕ) (a lim h : ℕ) : ℕ × ℕ :=
  Bool.rec (motive := fun _ => ℕ × ℕ) (lim, h)
    ((fun r =>
      Bool.rec (motive := fun _ => ℕ × ℕ)
        ((fun r2 => (Nat.add r.1 r2.1, r2.2)) (ih c (Nat.sub lim r.1) r.2)) r (Nat.ble lim r.1))
      (rec ((a, c) :: bl) par lim h))
    (Nat.blt a c && Nat.blt c top)

/-- **The cells of the new prime between `a` and `top`, cut at the cuts given**: the sum of their costs, each
searched with the limit and the hints that the cells before it leave. A cut that does not lie strictly inside what
is left of the range gives the limit. -/
noncomputable def partD (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (top : ℕ) (bl : List Cell) (par : Bool) :
    List ℕ → ℕ → ℕ → ℕ → ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ × ℕ) (fun a lim h => rec ((a, top) :: bl) par lim h)
    (fun c _ ih => partDS rec top bl par c ih)

/-- **One step of the search led by hints**: `dI` and `dJ` read a configuration, and a
floor and a configuration, from the hints, and return the hints left; `kd` is the search of the cells of the new
prime above a floor. -/
noncomputable def stepD (O : Ops) (τ : Tests) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ)
    (kd : (List Cell → Bool → ℕ → ℕ → ℕ × ℕ) → ℕ → List Cell → Bool → ℕ → ℕ → ℕ → ℕ × ℕ)
    (altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (bl : List Cell)
    (par : Bool) (lim h : ℕ) : ℕ × ℕ :=
  match bl with
  | [] => (lim, h)
  | x :: b =>
    Bool.rec (motive := fun _ => ℕ × ℕ) (lim, h)
      (Bool.rec (motive := fun _ => ℕ × ℕ)
        (Bool.rec (motive := fun _ => ℕ × ℕ)
          (Bool.rec (motive := fun _ => ℕ × ℕ)
            (Bool.rec (motive := fun _ => ℕ × ℕ)
              (Bool.rec (motive := fun _ => ℕ × ℕ)
                (Bool.rec (motive := fun _ => ℕ × ℕ) (O.alt (x :: b) par lim, Nat.div h 64)
                  (Bool.rec (motive := fun _ => ℕ) lim 0 (O.van (x :: b)), Nat.div h 64)
                  (Nat.beq (Nat.land h 63) 31))
                ((fun mid =>
                  Bool.rec (motive := fun _ => ℕ × ℕ) (lim, Nat.div h 32)
                    ((fun r =>
                      Bool.rec (motive := fun _ => ℕ × ℕ)
                        ((fun r2 => (Nat.add r.1 r2.1, r2.2)) (rec ((mid, x.2) :: b) par (Nat.sub lim r.1) r.2))
                        r (Nat.ble lim r.1))
                      (rec ((x.1, mid) :: b) par lim (Nat.div h 32)))
                    (Nat.blt x.1 mid && Nat.blt mid x.2))
                  (Nat.div (Nat.add x.1 x.2) 2))
                (Nat.beq (Nat.land h 31) 15))
              (altH (x :: b) par lim (Nat.div h 16)) (Nat.beq (Nat.land h 15) 7))
            (Option.rec (motive := fun _ => ℕ × ℕ) (lim, Nat.div h 8) (fun dc => (dc, Nat.div h 8))
              (O.drp (x :: b) par))
            (Nat.beq (Nat.land h 7) 3))
          ((fun p =>
            Bool.rec (motive := fun _ => ℕ × ℕ) (lim, p.2)
              (Bool.rec (motive := fun _ => ℕ × ℕ) (lim, p.2)
                (Bool.rec (motive := fun _ => ℕ × ℕ) (lim, p.2) (kd rec x.2 (x :: b) (!par) p.1.1 lim p.2)
                  (τ.okJ (x :: b) p.1.1 p.1.2))
                (Nat.ble p.1.1 x.1))
              (Nat.ble 1 p.1.1))
            (dJ (x :: b) (Nat.div h 4)))
          (Nat.beq (Nat.land h 3) 1))
        ((fun p => (Bool.rec (motive := fun _ => ℕ) lim 0 (τ.okI (x :: b) p.1), p.2))
          (dI (x :: b) (Nat.div h 2)))
        (Nat.beq (Nat.land h 1) 0))
      (O.grd (x :: b))

/-- **The search led by hints**, to a depth of recursion `n`: a cost for the term of the
box `bl` with the sign `par`, and the hints left; a cost at least `lim` says nothing. -/
noncomputable def solveD (O : Ops) (τ : Tests) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ)
    (kd : (List Cell → Bool → ℕ → ℕ → ℕ × ℕ) → ℕ → List Cell → Bool → ℕ → ℕ → ℕ → ℕ × ℕ)
    (altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) : ℕ → List Cell → Bool → ℕ → ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun _ => List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (fun _ _ lim h => (lim, h))
    (fun _ ih => stepD O τ dI dJ kd altH ih)

/-! ### The configurations, read from the hints -/

/-- **One pass over a box for a Buchstab step**: `k` is given what is left of the set `m` after the box's cells,
the least of `lm` and of the cells' lower ends, the sums of the lower and of the upper ends of the cells of `m`,
and `pw` doubled for each cell. -/
noncomputable def pickP {α : Type} : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → α) → α :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → α) → α)
    (fun m lm lo hi pw k => k m lm lo hi pw)
    (fun x _ ih m lm lo hi pw k =>
      ih (Nat.div m 2) (Nat.sub lm (Nat.sub lm x.1)) (Nat.add lo (Nat.mul (Nat.land m 1) x.1))
        (Nat.add hi (Nat.mul (Nat.land m 1) x.2)) (Nat.mul pw 2) k)

/-- `f` after `i` steps `f ↦ ⌊3f/4⌋`. -/
noncomputable def floorP (i f : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun f => f) (fun _ ih f => ih (Nat.div (Nat.mul 3 f) 4)) i f

/-- The configuration of an evaluation, from the hints: `0` for the rest at the first cell, or `1` and three bits
for its cell; then a set of `pw` values. -/
noncomputable def cfgIP (pw h : ℕ) : Cfg × ℕ :=
  Bool.rec (motive := fun _ => Cfg × ℕ)
    ((fun h1 => (⟨1, Nat.mod h1 pw, 1, 0, false⟩, Nat.div h1 pw)) (Nat.div h 2))
    ((fun h1 => (⟨1, Nat.mod h1 pw, Nat.pow 2 (Nat.land (Nat.div h 2) 7), 0, false⟩, Nat.div h1 pw))
      (Nat.div h 16))
    (Nat.beq (Nat.land h 1) 1)

section

variable [SieveCert.IBPar]

/-- The floor and the configuration of a Buchstab step, from the hints `h` after their four bits `sel`: for the
rest at a cell of ends `lo`, `hi` (`sel` even) the floor `min(lm, vOfF hi − uOfF lo − 1)`; for the rest among the
tree's primes the floor after `sel/2` steps from `min(lm, fmax3)`. The hints give a set `s0` of `pw` values, then
`0` for the set `s1` of all the cells but the last and the side `true`, or `1`, a set `s1` and a bit. -/
noncomputable def cfgJP (sel lm lo hi pw h : ℕ) : (ℕ × Cfg) × ℕ :=
  (fun s0 h2 =>
    (fun s1 e h4 =>
      (cond (Nat.beq (Nat.land sel 1) 0)
          (minN lm (Nat.sub (vOfF hi) (Nat.succ (uOfF lo))), (⟨1, s0, Nat.pow 2 (Nat.div sel 2), s1, e⟩ : Cfg))
          (floorP (Nat.div sel 2) (minN lm fmax3), (⟨2, s0, 0, s1, e⟩ : Cfg)), h4))
      (Bool.rec (motive := fun _ => ℕ) (Nat.sub (Nat.div pw 2) 1) (Nat.mod (Nat.div h2 2) pw)
        (Nat.beq (Nat.land h2 1) 1))
      (Bool.rec (motive := fun _ => Bool) true (Nat.beq (Nat.land (Nat.div (Nat.div h2 2) pw) 1) 1)
        (Nat.beq (Nat.land h2 1) 1))
      (Bool.rec (motive := fun _ => ℕ) (Nat.div h2 2) (Nat.div (Nat.div (Nat.div h2 2) pw) 2)
        (Nat.beq (Nat.land h2 1) 1)))
    (Nat.mod h pw) (Nat.div h pw)

/-- **The configuration of an evaluation in the main tree**, from the hints. -/
noncomputable def cfgIM (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIP (Nat.pow 2 (lenR bl)) h

/-- **The floor and the configuration of a Buchstab step in the main tree**, from the hints. -/
noncomputable def cfgJM (bl : List Cell) (h : ℕ) : (ℕ × Cfg) × ℕ :=
  pickP bl (Nat.pow 2 (Nat.div (Nat.land h 15) 2)) DEN 0 0 1 fun _ lm lo hi pw =>
    cfgJP (Nat.land h 15) lm lo hi pw (Nat.div h 16)

/-- **The configuration of an evaluation in a tree over a frozen part**, from the hints: the sets have one more
bit, the cofactor's. -/
noncomputable def cfgIF (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIP (Nat.pow 2 (Nat.succ (lenR bl))) h

/-- `pickP` over the first `j` cells of a box. -/
noncomputable def pickC {α : Type} : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → α) → α :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → α) → α) (fun _ m lm lo hi k => k m lm lo hi)
    (fun x _ ih j m lm lo hi k =>
      Bool.rec (motive := fun _ => α)
        (ih (Nat.sub j 1) (Nat.div m 2) (Nat.sub lm (Nat.sub lm x.1)) (Nat.add lo (Nat.mul (Nat.land m 1) x.1))
          (Nat.add hi (Nat.mul (Nat.land m 1) x.2)) k)
        (k m lm lo hi) (Nat.beq j 0))

/-- **The floor and the configuration of a Buchstab step in a tree over a frozen part**, from the hints: the
rest's cell is one of the chain's, read in a pass over the chain, or one of the `nb` frozen primes `β`, or the
cofactor's, of ends `cl`, `ch`; each is widened by `Kb`. `lomβ` is the least lower end of the frozen primes. What
is read from the frozen primes does not depend on the box. -/
noncomputable def cfgJF (Kb cl ch : ℕ) (β : List Cell) (nb lomβ : ℕ) (bl : List Cell) (h : ℕ) : (ℕ × Cfg) × ℕ :=
  (fun n =>
    pickC bl (Nat.sub n nb) (Nat.pow 2 (Nat.div (Nat.land h 15) 2)) DEN 0 0 fun m lm lo hi =>
      canonN m fun mc =>
        (fun p cofb =>
          cfgJP (Nat.land h 15) (maxN 1 (Nat.sub (Nat.sub lm (Nat.sub lm lomβ)) Kb))
            (maxN 1 (Nat.sub (Nat.add (Nat.add lo p.1) (Nat.mul cofb cl)) Kb))
            (Nat.add (Nat.add (Nat.add hi p.2) (Nat.mul cofb ch)) Kb) (Nat.pow 2 (Nat.succ n)) (Nat.div h 16))
          (msumP β mc 0 0) (Nat.land (Nat.div mc (Nat.pow 2 nb)) 1))
    (lenR bl)

end

/-! ### The reversal through the largest prime -/

/-- `lastC`, by the recursor: the last cell, or `d` for no cell. -/
noncomputable def lastP : List Cell → Cell → Cell :=
  List.rec (motive := fun _ => Cell → Cell) (fun d => d) (fun x _ ih _ => ih x)

/-- `initC`, by the recursor. -/
noncomputable def initP : List Cell → List Cell :=
  List.rec (motive := fun _ => List Cell) []
    (fun x r ih => List.casesOn (motive := fun _ => List Cell) r [] (fun _ _ => x :: ih))

/-- `bdK`. -/
def bdKP (ctx : Cell) (y : ℕ) : ℕ :=
  cdivP (Nat.mul (omKwP (Nat.sub (Nat.sub (Nat.sub DEN ctx.2) y) 1) y (Nat.add (Nat.sub ctx.2 ctx.1) 2) 1) DEN) y

/-- `dropCost` of a box whose first cell is `c`, whose last is `d`, and whose cells between have the sums `ls`,
`hs`, the product of factors `tp` and the number `n`. -/
def dropL (c d : Cell) (ls hs tp n : ℕ) : ℕ :=
  dropF c (Nat.add ls d.1) (Nat.add hs d.2) (Nat.mul tp (trFP d.1 (Nat.sub d.2 d.1))) (Nat.succ n)

/-- `flipOK`, for a box whose last cell is `ctx`, whose first is `c`, and whose cells between have the sum of
upper ends `hs` and the number `n`; `ok` is the product of `cellI` over the cells but the last, and `lh` the upper
end of the last but one. -/
def flipOKP (maxlen : ℕ) (ctx c : Cell) (hs ok n lh : ℕ) : Bool :=
  Nat.ble (Nat.add n 2) maxlen && Nat.ble maxlen 11 && Nat.beq (Nat.mul ok (cellI ctx)) 1 &&
    Nat.ble (Nat.add (Nat.add (Nat.add c.2 hs) ctx.2) 2) DEN && Nat.ble (Nat.add lh 1) ctx.1 && Nat.ble 3 ctx.1 &&
    Nat.ble (flipT ctx) ctx.1 && Nat.ble (Nat.add (Nat.add ctx.2 (flipT ctx)) 1) DEN

variable [SieveCert.IBPar]

/-- **The tree over the frozen part of a reversal**, searched by hints: the terms of the frozen part at the floor
and with the configuration read from the hints, and the cells of the chain's first prime by the hints after them.
The frozen primes `c :: b` have the sums `lsβ`, `hsβ` and the number `nb`; what the tests and the search read from
them is computed once for the tree (`frozTestsC`, `cfgJF`). -/
noncomputable def flipTreeD (κ hR fuel : ℕ) (ctx c : Cell) (b : List Cell) (lsβ hsβ nb lim h : ℕ) : ℕ × ℕ :=
  (fun τ t Kb cl ch =>
    (fun p =>
      cond (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c.1 t) && τ.okJ (c :: b) p.1.1 p.1.2)
        (kidsF κ hR ctx nb
          (solveD (opsKP ctx nb) τ cfgIF (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN)) (kidsF κ hR ctx nb) noAltH
            fuel)
          t (c :: b) true p.1.1 lim p.2)
        (lim, p.2))
      (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN) (c :: b) h))
    (frozTestsC (Nat.sub DEN ctx.2) (Nat.add (Nat.sub DEN ctx.1) 1) (Nat.add 12 (Nat.div DEN c.1)) (c :: b) lsβ hsβ
      nb (lomP (c :: b) DEN))
    (flipT ctx) (Nat.add 12 (Nat.div DEN c.1)) (maxN 1 (Nat.sub (Nat.sub DEN ctx.2) hsβ))
    (Nat.sub (Nat.succ (Nat.sub DEN ctx.1)) lsβ)

/-- **The cost of the reversal of a box through its largest prime**, from the sums of the frozen primes after the
first, `c`: the test `flipOKP`, and the formula of `flipCost` on the cost of the tree, which is searched by hints
with the limit `CAPK`. -/
noncomputable def flipCostB (κ hR fuel maxlen : ℕ) (ctx c : Cell) (b : List Cell)
    (ls hs tp ok n lh lim h : ℕ) : ℕ × ℕ :=
  cond (flipOKP maxlen ctx c hs ok n lh)
    ((fun E r =>
      (cond (Nat.ble CAPK r.1) lim
        (cdivP
          (Nat.add (Nat.mul r.1 (Nat.add (Nat.mul ctx.2 (dropL c ctx ls hs tp n)) E))
            (Nat.mul (bdKP ctx (flipT ctx)) E))
          (Nat.mul DEN K)), r.2))
      (Nat.add (Nat.mul (Nat.add ctx.2 1) (dropL c (Nat.sub ctx.2 1, Nat.add ctx.2 1) ls hs tp n))
        (Nat.mul (Nat.add ctx.1 1) (dropL c (Nat.sub ctx.1 1, Nat.add ctx.1 1) ls hs tp n)))
      (flipTreeD κ hR fuel ctx c b (Nat.add c.1 ls) (Nat.add c.2 hs) (Nat.succ n) CAPK h))
    (lim, h)

/-- **The cost of the reversal of a box of the sign `−` through its largest prime, the tree over the frozen part
searched by hints**: the box's last cell and the others by the recursor, and the sums of the others in one
pass. -/
noncomputable def flipCostD (κ hR fuel maxlen : ℕ) (bl : List Cell) (lim h : ℕ) : ℕ × ℕ :=
  (fun ctx =>
    List.casesOn (motive := fun _ => ℕ × ℕ) (initP bl) (lim, h) fun c b =>
      tailP b 0 0 1 (cellI c) 0 c.2 fun ls hs tp ok n lh =>
        flipCostB κ hR fuel maxlen ctx c b ls hs tp ok n lh lim h)
    (lastP bl (0, 0))

/-- **The bound that reads hints**: for a box of the sign `−` that may be reversed through its largest prime,
that reversal's cost. -/
noncomputable def altFD (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ) : ℕ × ℕ :=
  cond par (l, h) (flipCostD κ hR fuel maxlen bl l h)

end SieveAd
