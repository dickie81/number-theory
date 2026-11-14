/-
# A search for a tree of Buchstab steps, without Mathlib

`SieveAdDefs.lean` checks a tree that it is given. A tree for an exponent below `11/5` has several hundred thousand
nodes, too many to write out; so the kernel runs the search itself. `solveF` is a search for a tree on a box that
returns a cost and no tree: `SieveAdSearch.lean` proves that when the cost it returns is below the limit it was
given, a tree exists that passes `SieveAd.ok` on the box at that cost (`SieveAd.solveF_sound`). The search uses a
node only after the check of `SieveAd.ok` for it has passed, so what proposes the nodes needs no proof:

* a **strategy** (`Strat`) proposes the configurations to try for a box (`propI`), the floors of Buchstab's
  identity with theirs (`propJ`), and the cuts of the new prime's range into cells (`cuts`);
* `step` treats a box: one with no term, or that a proposed configuration evaluates, costs `0`; otherwise the box
  is dropped, if its sign allows (`dropC`), or decomposed at the first proposed floor that passes (`buchC`, the
  cells of the new prime by `kids`), whichever is cheaper; a box that can be neither dropped nor decomposed is cut
  in two (`splitC`);
* a **limit** stops the search of a subtree whose cost reaches it: a value at least the limit says nothing;
* a search is checked in parts: `kids` on a range of the new prime's cells is one part.

`mixStrat` is a strategy for the tests `SieveAd.mixTests`: the window's configuration first; for the estimate in
two variables the rest is one prime, the first variable the set of the others with the largest lower sum that stays
below the window's top (`bestSub`), and the leaves are split by a set with its sum in range (`findSub1`). The
window's floor is proposed only where a copy of the bilinear rule's test without its lists passes (`ibFast`).

These are arithmetic on natural numbers, lists and booleans, and the file imports only `SieveAdMixDefs.lean`.
-/
import SieveAdMixDefs

namespace SieveAd

open SieveCert (DEN cdiv V)

/-! ### The search, for any tests and any strategy -/

/-- What proposes the nodes of a tree. -/
structure Strat where
  /-- The greatest number of primes of a box that is decomposed, plus one. -/
  depth : ℕ
  /-- The least width of a cell that is cut for want of a test. -/
  wmin : ℕ
  /-- The configurations to try on a box. -/
  propI : List Cell → List Cfg
  /-- The floors to try on a box, with their configurations. -/
  propJ : List Cell → List (ℕ × Cfg)
  /-- The cuts of the new prime's range above a floor. -/
  cuts : List Cell → ℕ → List ℕ

/-- A cost that no tree has. -/
def BIG : ℕ := 2 ^ 70

/-- Some proposed configuration evaluates the box. -/
def anyI (τ : Tests) (bl : List Cell) : List Cfg → Bool
  | [] => false
  | cfg :: cs => τ.okI bl cfg || anyI τ bl cs

/-- The first proposed floor that passes, at most `lo0`. -/
def firstJ (τ : Tests) (bl : List Cell) (lo0 : ℕ) : List (ℕ × Cfg) → Option ℕ
  | [] => none
  | p :: ps => cond (Nat.blt 0 p.1 && Nat.ble p.1 lo0 && τ.okJ bl p.1 p.2) (some p.1) (firstJ τ bl lo0 ps)

/-- The cost of dropping the box, for a term of the sign `+`. -/
def dropC (bl : List Cell) (par : Bool) : Option ℕ :=
  cond par (cond (dropOK bl) (some (dropCost bl)) (cond (dropBOK bl) (some (dropBCost bl)) none)) none

/-- The cells of the new prime from `a` to `top`, cut at the proposed cuts that lie inside: the sum of their costs,
each searched with the limit that the cells before it leave. -/
def kids (rec : List Cell → Bool → ℕ → ℕ) (top : ℕ) (bl : List Cell) (par : Bool) : List ℕ → ℕ → ℕ → ℕ
  | [], a, lim => rec ((a, top) :: bl) par lim
  | c :: cs, a, lim =>
    cond (Nat.blt a c && Nat.blt c top)
      ((fun c1 => cond (Nat.ble lim c1) c1 (Nat.add c1 (kids rec top bl par cs c (Nat.sub lim c1))))
        (rec ((a, c) :: bl) par lim))
      (kids rec top bl par cs a lim)

/-- Buchstab's identity on the box `x :: b`, at the first proposed floor that passes. -/
def buchC (τ : Tests) (S : Strat) (rec : List Cell → Bool → ℕ → ℕ) (x : Cell) (b : List Cell) (par : Bool)
    (lim : ℕ) : ℕ :=
  cond (Nat.blt (Nat.succ b.length) S.depth)
    (match firstJ τ (x :: b) x.1 (S.propJ (x :: b)) with
      | some f => kids rec x.2 (x :: b) (!par) (S.cuts (x :: b) f) f lim
      | none => Nat.add lim BIG)
    (Nat.add lim BIG)

/-- The box `x :: b` cut in two at the middle of its last prime's cell. -/
def splitC (S : Strat) (rec : List Cell → Bool → ℕ → ℕ) (x : Cell) (b : List Cell) (par : Bool) (lim : ℕ) : ℕ :=
  (fun mid =>
    cond (Nat.blt S.wmin (Nat.sub x.2 x.1) && Nat.blt x.1 mid && Nat.blt mid x.2)
      ((fun c1 => cond (Nat.ble lim c1) c1 (Nat.add c1 (rec ((mid, x.2) :: b) par (Nat.sub lim c1))))
        (rec ((x.1, mid) :: b) par lim))
      (Nat.add lim BIG)) (Nat.div (Nat.add x.1 x.2) 2)

/-- A box that nothing evaluates: dropped or decomposed, whichever is cheaper, or cut in two. -/
def node (τ : Tests) (S : Strat) (rec : List Cell → Bool → ℕ → ℕ) (x : Cell) (b : List Cell) (par : Bool)
    (lim : ℕ) : ℕ :=
  match dropC (x :: b) par with
  | some dc => (fun bc => cond (Nat.ble dc bc) dc bc) (buchC τ S rec x b par (cond (Nat.ble dc lim) dc lim))
  | none => (fun bc => cond (Nat.blt bc BIG) bc (splitC S rec x b par lim)) (buchC τ S rec x b par lim)

/-- One step of the search on a box, the boxes below it by `rec`. -/
def step (τ : Tests) (S : Strat) (rec : List Cell → Bool → ℕ → ℕ) (bl : List Cell) (par : Bool) (lim : ℕ) : ℕ :=
  match bl with
  | [] => lim
  | x :: b => cond (vanishOK (x :: b) || anyI τ (x :: b) (S.propI (x :: b))) 0 (node τ S rec x b par lim)

/-- **The search**, to a depth of recursion `n`: a cost for the term of the box `bl` with the sign `par`; a value
at least `lim` says nothing. -/
def solveF (τ : Tests) (S : Strat) : ℕ → List Cell → Bool → ℕ → ℕ
  | 0 => fun _ _ lim => lim
  | n + 1 => step τ S (solveF τ S n)

/-! ### A strategy for the window's tests and the estimate's

What follows proposes nodes, and is written for the kernel's speed: arithmetic by `Nat.add`, `Nat.mul`, `Nat.sub`,
`Nat.div` and `Nat.ble`, with no instance to unfold, and the route's constants as definitions, which the kernel
evaluates once. -/

/-- The window's configuration. -/
def cfgW : Cfg := ⟨0, 0, 0, 0, false⟩

/-- The larger of two numbers (the smaller, `minN`, is `SieveAdLeafDefs.lean`'s). -/
def maxN (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

/-- The least lower end of the cells (`DEN` for no cell). -/
def lominOf : List Cell → ℕ
  | [] => DEN
  | c :: b => minN c.1 (lominOf b)

/-! The four searches over the sets of a box's cells are by the recursor of lists, which the kernel evaluates
about three times faster than a definition by structural recursion; each has a twin by structural recursion, equal
to it (`findSub2_eq`, …), which compiled code uses. -/

/-- `findSub2`, by structural recursion. -/
def findSub2S (umin vmax skip : ℕ) : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ → Option ℕ
  | [], _, slo, shi, mask, _ => cond (Nat.blt vmax shi) none (cond (Nat.ble umin slo) (some mask) none)
  | c :: cs, bit, slo, shi, mask, rem =>
    cond (Nat.blt vmax shi) none
      (cond (Nat.ble umin slo) (some mask)
        (cond (Nat.blt (Nat.add slo rem) umin) none
          (cond (Nat.beq bit skip) (findSub2S umin vmax skip cs (Nat.mul 2 bit) slo shi mask rem)
            (match findSub2S umin vmax skip cs (Nat.mul 2 bit) (Nat.add slo c.1) (Nat.add shi c.2)
                (Nat.add mask bit) (Nat.sub rem c.1) with
              | some m => some m
              | none => findSub2S umin vmax skip cs (Nat.mul 2 bit) slo shi mask (Nat.sub rem c.1)))))

/-- A set of the cells, but the one at the bit `skip`, with lower sum at least `umin` and upper sum at most `vmax`,
as a mask: the sums so far are `slo` and `shi`, and `rem` is the lower sum of the cells still to choose. -/
noncomputable def findSub2 (umin vmax skip : ℕ) : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ → Option ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → Option ℕ)
    (fun _ slo shi mask _ => cond (Nat.blt vmax shi) none (cond (Nat.ble umin slo) (some mask) none))
    (fun c _ ih bit slo shi mask rem =>
      cond (Nat.blt vmax shi) none
        (cond (Nat.ble umin slo) (some mask)
          (cond (Nat.blt (Nat.add slo rem) umin) none
            (cond (Nat.beq bit skip) (ih (Nat.mul 2 bit) slo shi mask rem)
              (match ih (Nat.mul 2 bit) (Nat.add slo c.1) (Nat.add shi c.2) (Nat.add mask bit) (Nat.sub rem c.1) with
                | some m => some m
                | none => ih (Nat.mul 2 bit) slo shi mask (Nat.sub rem c.1))))))

@[csimp] theorem findSub2_eq : @findSub2 = @findSub2S := by
  funext umin vmax skip l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    funext bit slo shi mask rem
    show cond _ none (cond _ _ (cond _ none (cond _ (findSub2 umin vmax skip cs _ _ _ _ _)
      (match findSub2 umin vmax skip cs _ _ _ _ _ with
        | some m => some m
        | none => findSub2 umin vmax skip cs _ _ _ _ _)))) = _
    rw [ih]
    rfl

/-- `bestSub`, by structural recursion. -/
def bestSubS (v skip : ℕ) : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ → ℕ × ℕ
  | [], _, slo, _, mask, rem, best => cond (Nat.ble (Nat.add slo rem) best.1) best (slo, mask)
  | c :: cs, bit, slo, shi, mask, rem, best =>
    cond (Nat.ble (Nat.add slo rem) best.1) best
      (cond (Nat.beq bit skip) (bestSubS v skip cs (Nat.mul 2 bit) slo shi mask rem best)
        (bestSubS v skip cs (Nat.mul 2 bit) slo shi mask (Nat.sub rem c.1)
          (cond (Nat.blt (Nat.add shi c.2) v)
            (bestSubS v skip cs (Nat.mul 2 bit) (Nat.add slo c.1) (Nat.add shi c.2) (Nat.add mask bit)
              (Nat.sub rem c.1) best) best)))

/-- Among the sets of the cells, but the one at the bit `skip`, with upper sum below `v`: one with the largest
lower sum, as its sum and its mask, if that beats `best`. -/
noncomputable def bestSub (v skip : ℕ) : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ → ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ → ℕ × ℕ)
    (fun _ slo _ mask rem best => cond (Nat.ble (Nat.add slo rem) best.1) best (slo, mask))
    (fun c _ ih bit slo shi mask rem best =>
      cond (Nat.ble (Nat.add slo rem) best.1) best
        (cond (Nat.beq bit skip) (ih (Nat.mul 2 bit) slo shi mask rem best)
          (ih (Nat.mul 2 bit) slo shi mask (Nat.sub rem c.1)
            (cond (Nat.blt (Nat.add shi c.2) v)
              (ih (Nat.mul 2 bit) (Nat.add slo c.1) (Nat.add shi c.2) (Nat.add mask bit) (Nat.sub rem c.1) best)
              best))))

@[csimp] theorem bestSub_eq : @bestSub = @bestSubS := by
  funext v skip l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    funext bit slo shi mask rem best
    show cond _ best (cond _ (bestSub v skip cs _ _ _ _ _ _)
      (bestSub v skip cs _ _ _ _ _ (cond _ (bestSub v skip cs _ _ _ _ _ _) best))) = _
    rw [ih]
    rfl

/-- `findSub1`, by structural recursion. -/
def findSub1S (lo hi : ℕ) : List Cell → ℕ → ℕ → ℕ → ℕ → Option ℕ
  | [], _, s, mask, rem => cond (Nat.blt hi s || Nat.blt (Nat.add s rem) lo) none (some mask)
  | c :: cs, bit, s, mask, rem =>
    cond (Nat.blt hi s || Nat.blt (Nat.add s rem) lo) none
      (match findSub1S lo hi cs (Nat.mul 2 bit) (Nat.add s c.2) (Nat.add mask bit) (Nat.sub rem c.2) with
        | some m => some m
        | none => findSub1S lo hi cs (Nat.mul 2 bit) s mask (Nat.sub rem c.2))

/-- A set of the cells with upper sum in `[lo, hi]`, as a mask: the sum so far is `s`, and `rem` is the upper sum of
the cells still to choose. -/
noncomputable def findSub1 (lo hi : ℕ) : List Cell → ℕ → ℕ → ℕ → ℕ → Option ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Option ℕ)
    (fun _ s mask rem => cond (Nat.blt hi s || Nat.blt (Nat.add s rem) lo) none (some mask))
    (fun c _ ih bit s mask rem =>
      cond (Nat.blt hi s || Nat.blt (Nat.add s rem) lo) none
        (match ih (Nat.mul 2 bit) (Nat.add s c.2) (Nat.add mask bit) (Nat.sub rem c.2) with
          | some m => some m
          | none => ih (Nat.mul 2 bit) s mask (Nat.sub rem c.2)))

@[csimp] theorem findSub1_eq : @findSub1 = @findSub1S := by
  funext lo hi l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    funext bit s mask rem
    show cond _ none (match findSub1 lo hi cs _ _ _ _ with
      | some m => some m
      | none => findSub1 lo hi cs _ _ _ _) = _
    rw [ih]
    rfl

variable [SieveCert.Grid] [SieveCert.IBPar]

open SieveCert (U1 U2)
open SieveCert.IBPar (Lnum Lden)

/-- The least lower end of a prime that may be the rest. -/
def restLo : ℕ := cdiv (Lden * DEN + 2000 * Lnum) (2000 * Lnum)
/-- The largest upper end of a prime that may be the rest. -/
def restHi : ℕ := (62500 * Lnum * DEN - 125005 * Lden * DEN) / (34863 * Lnum) - 1

/-- A prime may be the rest: the region's two inequalities on the rest alone. -/
def restOK (c : Cell) : Bool := Nat.ble restLo c.1 && Nat.ble c.2 restHi

/-- The constants of `uOf`, `vOf` and of the least lower sum that `chkI2` passes. -/
def uC0 : ℕ := cdiv (2 * Lden * DEN) (3 * Lnum)
@[inherit_doc uC0] def uA : ℕ := 62505 * Lden * DEN + 27637 * Lnum
@[inherit_doc uC0] def uB : ℕ := 27637 * Lnum
@[inherit_doc uC0] def uC : ℕ := 62500 * Lnum
@[inherit_doc uC0] def vA : ℕ := (3 * Lnum * DEN - 2 * Lden * DEN) / (3 * Lnum)
@[inherit_doc uC0] def vB : ℕ := 62500 * Lnum * DEN - 62505 * Lden * DEN
@[inherit_doc uC0] def vC : ℕ := 34863 * Lnum
@[inherit_doc uC0] def umC0 : ℕ := cdiv (2 * Lden * DEN + 3 * Lnum) (3 * Lnum)
@[inherit_doc uC0] def umA : ℕ := 62505 * Lden * DEN + 90137 * Lnum

/-- `uOf`, by the constants. -/
def uOfF (ρ₁ : ℕ) : ℕ := maxN uC0 (Nat.div (Nat.sub (Nat.add (Nat.sub uA (Nat.mul uB ρ₁)) uC) 1) uC)
/-- `vOf`, by the constants. -/
def vOfF (ρ₂ : ℕ) : ℕ :=
  minN (Nat.sub vA (Nat.succ ρ₂)) (Nat.div (Nat.sub vB (Nat.mul vC (Nat.succ ρ₂))) uC)
/-- The least lower sum of a first variable that `chkI2` passes, for a rest of lower end `ρ₁`. -/
def uminOf (ρ₁ : ℕ) : ℕ := maxN umC0 (Nat.div (Nat.sub (Nat.add (Nat.sub umA (Nat.mul uB ρ₁)) uC) 1) uC)

/-- A configuration of the estimate in two variables that may evaluate the box: the first prime that may be the
rest and leaves a set of the others in the window it gives. -/
def propI2 (bl : List Cell) (ls : ℕ) : List Cell → ℕ → List Cfg
  | [], _ => []
  | c :: cs, bit =>
    cond (restOK c)
      (match findSub2 (uminOf c.1) (vOfF c.2) bit bl 1 0 0 0 (Nat.sub ls c.1) with
        | some m => [⟨1, m, bit, 0, false⟩]
        | none => propI2 bl ls cs (Nat.mul 2 bit))
      (propI2 bl ls cs (Nat.mul 2 bit))

/-- The largest sizes of the leaves: `D₁ ≤ D1max`, `D₁ + D₂ ≤ T5` and `D₁ + 2D₂ ≤ T6`. -/
def D1max : ℕ := ((Lnum - Lden) * DEN - 1) / Lnum
@[inherit_doc D1max] def T5 : ℕ := (2 * Lnum * DEN - (Lden * DEN + 1)) / (2 * Lnum)
@[inherit_doc D1max] def T6 : ℕ := (2 * Lnum * DEN - (2 * Lden * DEN + 1)) / Lnum

/-- A split of the leaves for a box of upper sum `hs` and a growth `t`: a set `s1` and the side `e` of the growth. -/
def leavesOf (bl : List Cell) (hs t : ℕ) : Option (ℕ × Bool) :=
  cond (Nat.blt T5 (Nat.add hs t)) none
    ((fun lo =>
      match cond (Nat.ble t D1max) (findSub1 (Nat.sub lo t) (Nat.sub D1max t) bl 1 0 0 hs) none with
      | some m => some (m, true)
      | none =>
        match findSub1 lo D1max bl 1 0 0 hs with
        | some m => some (m, false)
        | none => none) (Nat.sub (Nat.mul 2 (Nat.add hs t)) T6))

/-- The largest floor at which the comparison in two variables may pass, with its configuration, over the primes
that may be the rest: `acc` is the best so far. A floor is at most `lomin`, and the leaves' sizes sum to at least
`hs` plus the growth, which is at least `u` less the others' lower sum. -/
def propJ2 (bl : List Cell) (lomin ls hs : ℕ) : List Cell → ℕ → ℕ × Option Cfg → ℕ × Option Cfg
  | [], _, acc => acc
  | c :: cs, bit, acc =>
    cond (Nat.ble lomin acc.1) acc
      (propJ2 bl lomin ls hs cs (Nat.mul 2 bit)
        (cond (restOK c)
          ((fun u v =>
            (fun f =>
              cond (Nat.blt acc.1 f && Nat.ble (Nat.add hs (Nat.sub u (Nat.sub ls c.1))) T5)
                ((fun b =>
                  match leavesOf bl hs (Nat.sub u b.1) with
                  | some sp => (f, some ⟨1, b.2, bit, sp.1, sp.2⟩)
                  | none => acc) (bestSub v bit bl 1 0 0 0 (Nat.sub ls c.1) (0, 0)))
                acc) (minN lomin (Nat.sub v (Nat.succ u)))) (uOfF c.1) (vOfF c.2))
          acc))

/-- `cIB` of the sums `slo`, `shi` of a set. -/
def cIBF (slo shi : ℕ) : ℕ :=
  maxN (Nat.sub U1 slo) (cond (Nat.ble U2 shi) (Nat.sub (Nat.sub DEN U2) (maxN slo U2)) 0)

/-- `tstarF`, by structural recursion. -/
def tstarFS (lim : ℕ) : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ
  | [], slo, shi, rem, best => cond (Nat.ble best (Nat.sub U1 (Nat.add slo rem))) best (minN best (cIBF slo shi))
  | c :: cs, slo, shi, rem, best =>
    cond (Nat.ble best (Nat.sub U1 (Nat.add slo rem))) best
      (tstarFS lim cs slo shi (Nat.sub rem c.1)
        (cond (Nat.blt (Nat.add shi c.2) lim)
          (tstarFS lim cs (Nat.add slo c.1) (Nat.add shi c.2) (Nat.sub rem c.1) best) best))

/-- The least `cIBF` over the sets of the cells with upper sum below `lim`, if below `best`: the sums so far are
`slo` and `shi`, with `shi < lim`, and `rem` is the lower sum of the cells still to choose. A set's `cIBF` is at
least `U1` less its lower sum, which stops the search of the sets that cannot beat `best`. -/
noncomputable def tstarF (lim : ℕ) : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ)
    (fun slo shi rem best => cond (Nat.ble best (Nat.sub U1 (Nat.add slo rem))) best (minN best (cIBF slo shi)))
    (fun c _ ih slo shi rem best =>
      cond (Nat.ble best (Nat.sub U1 (Nat.add slo rem))) best
        (ih slo shi (Nat.sub rem c.1)
          (cond (Nat.blt (Nat.add shi c.2) lim) (ih (Nat.add slo c.1) (Nat.add shi c.2) (Nat.sub rem c.1) best)
            best)))

omit [SieveCert.Grid] [SieveCert.IBPar] in
@[csimp] theorem tstarF_eq : @tstarF = @tstarFS := by
  funext g lim l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    funext slo shi rem best
    show cond _ best (tstarF lim cs _ _ _ (cond _ (tstarF lim cs _ _ _ _) best)) = _
    rw [ih]
    rfl

/-- What `ibOK` computes, without its lists: the growth `T` by `tstarF`, and a split of the leaves by `findSub1`.
No split has its size in range if `D1max < 2hs + 1 − DEN`. -/
def ibFast (bl : List Cell) (ls hs : ℕ) : Bool :=
  Nat.ble (Nat.sub (Nat.succ (Nat.mul 2 hs)) DEN) D1max &&
  (fun T =>
    (match cond (Nat.ble T D1max)
        (findSub1 (Nat.sub (Nat.succ (Nat.add (Nat.mul 2 hs) T)) DEN) (Nat.sub D1max T) bl 1 0 0 hs) none with
      | some _ => true
      | none =>
        match findSub1 (Nat.sub (Nat.succ (Nat.mul 2 (Nat.add hs T))) DEN) D1max bl 1 0 0 hs with
        | some _ => true
        | none => false)) (tstarF (Nat.sub DEN U1) bl 0 0 ls DEN)

/-- The floors to try: the window's width, if the estimate's floor is below it and the bilinear rule may pass;
then the estimate's. -/
def propJ (bl : List Cell) : List (ℕ × Cfg) :=
  (fun lomin ls hs =>
    (fun r =>
      cond (Nat.blt r.1 V && Nat.ble V lomin && ibFast bl ls hs) [(V, cfgW)] [] ++
        (match r.2 with
          | some cfg => [(r.1, cfg)]
          | none => [])) (cond (Nat.blt T5 hs) (0, none) (propJ2 bl lomin ls hs bl 1 (0, none))))
    (lominOf bl) (loSum bl) (hiSum bl)

/-- The side of the cells of the `d`-th prime: `hI` for the first four, then coarser. -/
def stepOf (hI d : ℕ) : ℕ := cond (Nat.ble d 4) hI (Nat.mul hI (Nat.succ (Nat.div (Nat.sub d 3) 2)))

/-- The cuts `f + w·j/n` for `j = 1, …, m`, before `acc`. -/
def cutList (f w n : ℕ) : ℕ → List ℕ → List ℕ
  | 0, acc => acc
  | j + 1, acc => cutList f w n j (Nat.add f (Nat.div (Nat.mul w (Nat.succ j)) n) :: acc)

/-- The cuts of the new prime's range above the floor `f`: cells of side at most `stepOf` up to where the new
prime's square is too large for a term with a cofactor, and a cut where the product of all the primes reaches `x`. -/
def cutsOf (hI : ℕ) (bl : List Cell) (f : ℕ) : List ℕ :=
  match bl with
  | [] => []
  | x :: b =>
    (fun reg last =>
      cond (Nat.blt f reg)
        ((fun n => cutList f (Nat.sub reg f) n n [last])
          (maxN 1 (Nat.div (Nat.sub (Nat.add (Nat.sub reg f) (stepOf hI (Nat.add b.length 2))) 1)
            (stepOf hI (Nat.add b.length 2)))))
        [last])
      (minN x.2 (Nat.add (Nat.div (Nat.sub DEN (loSum (x :: b))) 2) 2)) (Nat.sub (Nat.sub DEN 1) (hiSum (x :: b)))

/-- **A strategy for `mixTests`**, with cells of side `hI`, boxes of fewer than `depth` primes decomposed, and
cells wider than `wmin` cut for want of a test. -/
def mixStrat (hI depth wmin : ℕ) : Strat :=
  ⟨depth, wmin, fun bl => cfgW :: propI2 bl (loSum bl) bl 1, propJ, cutsOf hI⟩

end SieveAd

#print axioms SieveAd.findSub2_eq
#print axioms SieveAd.bestSub_eq
#print axioms SieveAd.findSub1_eq
#print axioms SieveAd.tstarF_eq
