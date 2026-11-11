/-
# Role reversal in a tree of Buchstab steps, without Mathlib

A term of three primes `p₁ > p₂ > p₃` in cells, of the sign `−`, needs an upper bound. Its numbers are
`n = p₁p₂p₃m` with `m` rough at `p₃`, and here `1 < m < p₃³`, so `m` is a prime `Q` or a product `q₂Q` of two.
**Role reversal** sums over `r' = p₂p₃m` instead, and sieves `n/r'` for the prime `p₁`: a prime at least
`z = x^{l₃/DEN}` is rough at `z`, so the term is at most the sum over the `r'` of the numbers `n ≡ a` with `r' | n`
that are rough at `z`, up to the `n` with a square factor. The `r'` are the tuples of three or four primes, the
**atoms**, in order, in five kinds of boxes (`p₂` above or below `Q`; with `q₂`, three places for `p₂`), under a
condition on their product (`x/r'` in the range of `p₁`), and that sum is a term of the usual kind for each box.

What this file defines, as arithmetic on natural numbers, lists and booleans:

* `Ops`, `nodeG`, `stepG`, `solveG`: `SieveAdSearchDefs.lean`'s search with the tests of its nodes as parameters:
  the boxes it treats, the test of a box with no term, the cost of dropping a box, and one more bound (`alt`).
* `vanishK`, `dropK`, `opsK`: the nodes of the tree of a reversed term. Its boxes are the atoms' cells with, before
  them, the cells of the chain, the primes of `n/r'` that Buchstab's identity has brought out. `n/r'` lies between
  `x^{(l₁−1)/DEN}` and `x^{(h₁+1)/DEN}`, for the cell `(l₁, h₁)` of the prime that is reversed (`ctx`).
* `rootJ`: the cost of the terms of an atoms' box at the level `z`, in units of the sum of `1/r'` over the box:
  Buchstab's identity at the first proposed floor that passes, the new prime's range cut into cells.
* `famCost`: the cost of one atoms' box: its tree's cost, and what the numbers rough at `z` exceed the primes by in
  the comparison set (`penK`), times the bounds of `Σ 1/r'` over the `r'` for which every `n` has `n/r'` in the cell
  of `p₁` and over the others (the `r'` near the two ends, where nothing is subtracted: `bdK`).
* `revOK`, `revCost`: the test of a box that may be reversed, and the cost: the two boxes with `m` prime, and for
  each cell of `q₂` the three boxes with `m = q₂Q`.
* `opsR`: the search of `SieveAdDefs.lean`'s trees with the reversal as one more bound for a box of the sign `−`.
* `geoCuts`, `cutsOfG`, `cutsK`, `cutsQ`, `stratG`, `stratK`: a strategy whose cells shrink with the exponent.

`SieveAdRev.lean` proves what a cost returned below its limit gives. The file imports `SieveAdSearchDefs.lean`.
-/
import SieveAdSearchDefs

namespace SieveAd

open SieveCert (DEN K omKw cdiv)

/-! ### A search with the tests of its nodes as parameters -/

/-- What a search does at a box, beyond the tests of the evaluations. -/
structure Ops where
  /-- The boxes that the search treats. -/
  grd : List Cell → Bool
  /-- The box has no term. -/
  van : List Cell → Bool
  /-- The cost of dropping the box, for a term of the given sign. -/
  drp : List Cell → Bool → Option ℕ
  /-- One more bound for the box, given a limit: a value at least the limit says nothing. -/
  alt : List Cell → Bool → ℕ → ℕ

/-- A box that nothing evaluates: dropped or decomposed, whichever is cheaper; or bounded by `alt` if that is
cheaper than the decomposition; or cut in two. -/
def nodeG (O : Ops) (τ : Tests) (S : Strat) (rec : List Cell → Bool → ℕ → ℕ) (x : Cell) (b : List Cell)
    (par : Bool) (lim : ℕ) : ℕ :=
  match O.drp (x :: b) par with
  | some dc => (fun bc => cond (Nat.ble dc bc) dc bc) (buchC τ S rec x b par (cond (Nat.ble dc lim) dc lim))
  | none =>
    (fun bc =>
      (fun l2 =>
        (fun rc => cond (Nat.blt rc l2) rc (cond (Nat.blt bc BIG) bc (splitC S rec x b par lim)))
          (O.alt (x :: b) par l2)) (cond (Nat.ble bc lim) bc lim))
      (buchC τ S rec x b par lim)

/-- One step of the search on a box, the boxes below it by `rec`. -/
def stepG (O : Ops) (τ : Tests) (S : Strat) (rec : List Cell → Bool → ℕ → ℕ) (bl : List Cell) (par : Bool)
    (lim : ℕ) : ℕ :=
  match bl with
  | [] => lim
  | x :: b =>
    cond (O.grd (x :: b))
      (cond (O.van (x :: b) || anyI τ (x :: b) (S.propI (x :: b))) 0 (nodeG O τ S rec x b par lim)) lim

/-- **The search**, to a depth of recursion `n`: a cost for the term of the box `bl` with the sign `par`; a value
at least `lim` says nothing. -/
def solveG (O : Ops) (τ : Tests) (S : Strat) : ℕ → List Cell → Bool → ℕ → ℕ
  | 0 => fun _ _ lim => lim
  | n + 1 => stepG O τ S (solveG O τ S n)

/-! ### The tree of a reversed term -/

/-- The cells of the chain: the box without its last `na` cells, the atoms'. -/
def chainOf (na : ℕ) (bl : List Cell) : List Cell := bl.take (bl.length - na)

/-- The chain's box has no term: the product of its primes is below `x^{(l₁−1)/DEN}`, and times the last prime it
is at least `x^{(h₁+1)/DEN}`. -/
def vanishK (ctx : Cell) : List Cell → Bool
  | [] => false
  | c :: b => Nat.ble (c.2 + hiSum b + 1) ctx.1 && Nat.ble (ctx.2 + 1) (c.1 + loSum b + c.1)

/-- The cost of dropping the chain's box, for a term of the sign `+`, in units of `1/K` of the sum of `1/r'`: the
bound of `SieveRough.shareBox` with `r'` among the primes before the last, when the chain's primes have a product
below `x^{(l₁−1)/DEN}`. -/
def dropK (ctx : Cell) (ch : List Cell) (par : Bool) : Option ℕ :=
  match ch with
  | [] => none
  | c :: b =>
    cond (par && cellsOK (c :: b) && Nat.ble (c.2 + hiSum b + 1) ctx.1)
      (some (cdiv (omKw (loSum b + (DEN - ctx.2)) c.1 (c.2 + hiSum b - (c.1 + loSum b) + (ctx.2 - ctx.1 + 1))
          (c.2 - c.1) * (exF c.1 (c.2 - c.1) * trProd b)) (SC ^ (b.length + 1))))
      none

/-- The nodes of the tree of a reversed term: boxes of at most twelve cells with a chain. -/
def opsK (ctx : Cell) (na : ℕ) : Ops :=
  ⟨fun bl => Nat.blt na bl.length && Nat.ble bl.length 12, fun bl => vanishK ctx (chainOf na bl),
    fun bl par => dropK ctx (chainOf na bl) par, fun _ _ l => l⟩

/-- The cost of the terms of the atoms' box `β` at the level of its least prime's lower end, in units of `1/K` of
the sum of `1/r'`: nothing if a proposed floor at that level passes; else Buchstab's identity at the first proposed
floor that passes, the new prime's range from the floor to the level cut into cells. -/
def rootJ (τ : Tests) (S : Strat) (ctx : Cell) (fuel : ℕ) (β : List Cell) (lim : ℕ) : ℕ :=
  match β with
  | [] => lim
  | c :: b =>
    match firstJ τ (c :: b) c.1 (S.propJ (c :: b)) with
    | some f =>
      cond (Nat.ble c.1 f) 0
        (kids (solveG (opsK ctx (Nat.succ b.length)) τ S fuel) c.1 (c :: b) true (S.cuts (c :: b) f) f lim)
    | none => lim

/-! ### The cost of a reversal -/

/-- Some prime's cell is empty, or wholly at or above the next older prime's: the box has no tuple. -/
def emptyBox : List Cell → Bool
  | [] => false
  | c :: b =>
    Nat.ble c.2 c.1 ||
      (match b with
        | [] => false
        | d :: _ => Nat.ble d.2 c.1 || emptyBox b)

/-- The product of `trF` over the cells but the one at the position `i`. -/
def trBut : ℕ → List Cell → ℕ
  | _, [] => 1
  | 0, _ :: b => trProd b
  | i + 1, c :: b => trF c.1 (c.2 - c.1) * trBut i b

/-- What the numbers of `(x/r', 2x/r']` rough at `x^{y/DEN}` exceed its primes by, in units of `1/K` of
`(x/r')/log x`, for `r'` between `x^{(DEN−h₁+1)/DEN}` and `x^{(DEN−l₁)/DEN}`. -/
def penK (ctx : Cell) (y : ℕ) : ℕ := cdiv (omKw (DEN - ctx.2 - y) y (ctx.2 - ctx.1) 1 * DEN) y - K * DEN / ctx.2

/-- The numbers of `(x/r', 2x/r']` rough at `x^{y/DEN}`, in units of `1/K` of `(x/r')/log x`, for `r'` between
`x^{(DEN−h₁)/DEN}` and `x^{(DEN−l₁+1)/DEN}`. -/
def bdK (ctx : Cell) (y : ℕ) : ℕ := cdiv (omKw (DEN - ctx.2 - y - 1) y (ctx.2 - ctx.1 + 2) 1 * DEN) y

/-- A cost of a tree, in units of the sum of `1/r'`, that no reversal uses. -/
def CAPK : ℕ := 64 * K

/-- **The cost of an atoms' box** `β`, in units of `1/K`, for the prime at the position `iq` as the one that the
condition on the product confines: nothing for a box with no tuple; else the cost `C` of its tree plus `penK`, times
the bound of `Σ 1/r'` over the `r'` between `x^{(DEN−h₁+1)/DEN}` and `x^{(DEN−l₁)/DEN}`, and `C` plus `bdK`, times
the bound over the `r'` within a factor `x^{1/DEN}` of the two ends. -/
def famCost (τ : Tests) (SK : Cell → ℕ → Strat) (fuel : ℕ) (ctx : Cell) (β : List Cell) (iq : ℕ) (lim : ℕ) : ℕ :=
  cond (emptyBox β) 0
    ((fun C =>
      cond (Nat.ble CAPK C) lim
        ((fun y q tr sc =>
          cdiv (trF q (ctx.2 - ctx.1 - 1) * tr * (C + penK ctx y)) sc +
            cdiv (2 * trF q 1 * tr * (C + bdK ctx y)) sc)
          (getC β 0).1 (getC β iq).1 (trBut iq β) (SC ^ β.length)))
      (rootJ τ (SK ctx β.length) ctx fuel β CAPK))

/-- `c1`, and what follows it with the limit that `c1` leaves. -/
def addL (c1 : ℕ) (rest : ℕ → ℕ) (lim : ℕ) : ℕ := cond (Nat.ble lim c1) c1 (c1 + rest (lim - c1))

/-- A box of three primes that may be reversed through its first prime: cells with `0 < lo < hi`; the second
prime's cell below the first's; the product of the three below `x`; the cofactor below the cube of the third prime;
and the third prime's least exponent at most the first's. -/
def revOK : List Cell → Bool
  | [c3, c2, c1] =>
    cellsOK [c3, c2, c1] && Nat.ble c2.2 c1.1 && Nat.ble (c1.2 + c2.2 + c3.2) DEN &&
      Nat.ble (DEN + 1 - (c1.1 + c2.1 + c3.1)) (3 * c3.1) && Nat.ble c3.1 c1.1
  | _ => false

/-- The cost of the three atoms' boxes with a cofactor of two primes, the smaller in the cell `d`. -/
def cellQ (τ : Tests) (SK : Cell → ℕ → Strat) (fuel : ℕ) (c1 c2 c3 : Cell) (μlo μhi : ℕ) (bl : List Cell)
    (_ : Bool) (lim : ℕ) : ℕ :=
  match bl with
  | [d] =>
    (fun iq2 =>
      addL (famCost τ SK fuel c1 [c3, d, iq2, c2] 2 lim)
        (fun l1 =>
          addL (famCost τ SK fuel c1 [c3, d, c2, iq2] 3 l1) (fun l2 => famCost τ SK fuel c1 [c3, c2, d, iq2] 3 l2)
            l1) lim)
      (maxN (μlo - d.2) d.1, μhi - d.1 + 1)
  | _ => lim

/-- **The cost of a reversal** of the box `[c3, c2, c1]` through its first prime, in units of `1/K`: the two
atoms' boxes with a prime cofactor, and the three with a cofactor of two primes for each cell of the smaller, its
range cut at the cuts that `cq` proposes. A value at least `lim` says nothing. -/
def revCost (τ : Tests) (SK : Cell → ℕ → Strat) (fuel : ℕ) (cq : ℕ → ℕ → List ℕ) : List Cell → ℕ → ℕ
  | [c3, c2, c1], lim =>
    (fun μlo μhi =>
      (fun iq1 top =>
        addL (famCost τ SK fuel c1 [c3, c2, iq1] 2 lim)
          (fun l1 =>
            addL (famCost τ SK fuel c1 [c3, iq1, c2] 1 l1)
              (fun l2 => kids (cellQ τ SK fuel c1 c2 c3 μlo μhi) top [] false (cq c3.1 top) c3.1 l2) l1) lim)
        (maxN μlo c3.1, μhi) ((μhi + 1) / 2))
      (DEN - (c1.2 + c2.2 + c3.2)) (DEN + 1 - (c1.1 + c2.1 + c3.1))
  | _, lim => lim

/-- **The search with role reversal**: `SieveAdDefs.lean`'s nodes, and for a box of the sign `−` that may be
reversed, the reversal's cost as one more bound. -/
def opsR (τ : Tests) (SK : Cell → ℕ → Strat) (fuel : ℕ) (cq : ℕ → ℕ → List ℕ) : Ops :=
  ⟨fun _ => true, vanishOK, dropC, fun bl par l => cond (!par && revOK bl) (revCost τ SK fuel cq bl l) l⟩

/-! ### A strategy with cells that shrink with the exponent -/

/-- The cuts from `c` up to `reg`, each step at most `st` and at most the exponent over `κ`. -/
def geoCuts (κ st reg : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, c =>
    cond (Nat.blt c reg)
      ((fun c' => minN c' reg :: geoCuts κ st reg n c') (Nat.add c (maxN 1 (minN st (Nat.div c κ)))))
      []

/-- The cuts of the new prime's range above the floor `f`, as `cutsOf`'s with cells that shrink. -/
def cutsOfG (κ hI : ℕ) (bl : List Cell) (f : ℕ) : List ℕ :=
  match bl with
  | [] => []
  | x :: b =>
    (fun reg last =>
      cond (Nat.blt f reg) (geoCuts κ (stepOf hI (Nat.add b.length 2)) reg 4096 f ++ [last]) [last])
      (minN x.2 (Nat.add (Nat.div (Nat.sub DEN (loSum (x :: b))) 2) 2)) (Nat.sub (Nat.sub DEN 1) (hiSum (x :: b)))

/-- The cuts of the new prime's range in the tree of a reversed term, above the floor `f` and below `top`: cells up
to where the new prime's square is too large for `n/r'`, and a cut where the chain's product reaches the range of
`n/r'`. -/
def cutsK (κ hR : ℕ) (ctx : Cell) (ch : List Cell) (top f : ℕ) : List ℕ :=
  (fun reg last =>
    cond (Nat.blt f reg) (geoCuts κ (cond (Nat.blt ch.length 2) hR (Nat.mul 2 hR)) reg 4096 f ++ [last]) [last])
    (minN top (Nat.add (Nat.div (Nat.sub (Nat.succ ctx.2) (loSum ch)) 2) 2))
    (Nat.sub (Nat.sub ctx.1 1) (hiSum ch))

/-- The cuts of the range `[a, top)` into cells of side at most `hQ`. -/
def cutsQ (hQ a top : ℕ) : List ℕ :=
  (fun n => cutList a (Nat.sub top a) n n []) (maxN 1 (cdiv (Nat.sub top a) hQ))

variable [SieveCert.Grid] [SieveCert.IBPar]

/-- **A strategy for `mixTests`** with cells of side at most `hI` and at most the exponent over `κ`. -/
def stratG (κ hI depth wmin : ℕ) : Strat :=
  ⟨depth, wmin, fun bl => cfgW :: propI2 bl (loSum bl) bl 1, propJ, cutsOfG κ hI⟩

/-- **A strategy for the tree of a reversed term** with `na` atoms, its chains of fewer than `depthR` primes. -/
def stratK (κ hR depthR wmin : ℕ) (ctx : Cell) (na : ℕ) : Strat :=
  ⟨depthR + na, wmin, fun bl => cfgW :: propI2 bl (loSum bl) bl 1, propJ,
    fun bl f =>
      (fun ch =>
        cutsK κ hR ctx ch
          (match ch with
            | [] => (getC bl 0).1
            | x :: _ => x.2) f) (chainOf na bl)⟩

end SieveAd
