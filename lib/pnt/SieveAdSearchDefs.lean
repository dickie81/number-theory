/-
# The parts of a search for a tree of Buchstab steps, without Mathlib

`SieveAdDefs.lean` checks a tree that it is given. A search instead runs in the kernel and returns a cost and no
tree; it uses a node only after the check of `SieveAd.ok` for it has passed, so what proposes the nodes needs no
proof. This file defines its parts:

* a **strategy** (`Strat`) proposes the configurations to try for a box (`propI`), the floors of Buchstab's
  identity with theirs (`propJ`), and the cuts of the new prime's range into cells (`cuts`);
* the steps of a search on a box: a proposed configuration that evaluates it (`anyI`), its drop, if its sign
  allows (`dropC`), Buchstab's identity at the first proposed floor that passes (`buchC`, the cells of the new
  prime by `kids`), and its cut in two (`splitC`);
* a **limit** stops the search of a subtree whose cost reaches it: a value at least the limit says nothing;
* a search is checked in parts: `kids` on a range of the new prime's cells is one part.

`SieveAdRevDefs.lean`'s search `solveG` treats a box with `anyI`, `buchC` and `splitC`.

The second part is written for the kernel's speed: searches over the sets of a box's cells (`findSub2`, `bestSub`,
`findSub1`, `tstarF`, the last over the window cost `cIBF` of a set), each with a twin by structural recursion for
compiled code; the route's constants and `uOf`, `vOf` by them (`restLo`, `uC0`, …, `uOfF`, `vOfF`); and the side
of a prime's cells (`stepOf`).

These are arithmetic on natural numbers, lists and booleans, and the file imports `SieveAdDefs.lean`,
`SieveRuleDefs.lean` and `SieveAdTwoDefs.lean`.
-/
import SieveAdDefs
import SieveRuleDefs
import SieveAdTwoDefs

namespace SieveAd

open SieveCert (DEN cdiv)

/-! ### The parts of the search, for any tests and any strategy -/

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

/-! ### Searches over the sets of a box's cells, and the route's constants

What follows is written for the kernel's speed: arithmetic by `Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.div` and
`Nat.ble`, with no instance to unfold, and the route's constants as definitions, which the kernel evaluates once. -/

/-- The larger of two numbers (the smaller, `minN`, is `SieveAdLeafDefs.lean`'s). -/
def maxN (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

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

/-- The constants of `uOf` and `vOf`. -/
def uC0 : ℕ := cdiv (2 * Lden * DEN) (3 * Lnum)
@[inherit_doc uC0] def uA : ℕ := 62505 * Lden * DEN + 27637 * Lnum
@[inherit_doc uC0] def uB : ℕ := 27637 * Lnum
@[inherit_doc uC0] def uC : ℕ := 62500 * Lnum
@[inherit_doc uC0] def vA : ℕ := (3 * Lnum * DEN - 2 * Lden * DEN) / (3 * Lnum)
@[inherit_doc uC0] def vB : ℕ := 62500 * Lnum * DEN - 62505 * Lden * DEN
@[inherit_doc uC0] def vC : ℕ := 34863 * Lnum

/-- `uOf`, by the constants. -/
def uOfF (ρ₁ : ℕ) : ℕ := maxN uC0 (Nat.div (Nat.sub (Nat.add (Nat.sub uA (Nat.mul uB ρ₁)) uC) 1) uC)
/-- `vOf`, by the constants. -/
def vOfF (ρ₂ : ℕ) : ℕ :=
  minN (Nat.sub vA (Nat.succ ρ₂)) (Nat.div (Nat.sub vB (Nat.mul vC (Nat.succ ρ₂))) uC)

/-- For a set with lower sum `slo` and upper sum `shi`: the larger of `U1 − slo` and, if `U2 ≤ shi`,
`DEN − U2 − max(slo, U2)`. -/
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

/-- The side of the cells of the `d`-th prime: `hI` for the first four, then coarser. -/
def stepOf (hI d : ℕ) : ℕ := cond (Nat.ble d 4) hI (Nat.mul hI (Nat.succ (Nat.div (Nat.sub d 3) 2)))

end SieveAd

#print axioms SieveAd.findSub2_eq
#print axioms SieveAd.bestSub_eq
#print axioms SieveAd.findSub1_eq
#print axioms SieveAd.tstarF_eq
