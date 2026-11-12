/-
# The cost of the reversal of a box through its largest prime, without Mathlib

The search of `SieveAdRevDefs.lean` has one more bound for a box, `Ops.alt`. Here it is the reversal of a box of
two primes or more through its largest prime, as `SieveAdFlipSum.lean` proves it for a term of the sign `−`: the
box is `β ++ [ctx]`, the cell `ctx = (l₁, h₁)` of its largest prime at least one unit above the next prime's cell.
The frozen part is the numbers `R = ∏a·m`, `a` in the cells `β` and `m` rough at the least prime of `a`, with `R`
between `x^{(DEN−h₁)/DEN}` and `x^{(DEN−l₁+1)/DEN}`, and the term of the box is at most the terms of `n/R` at the
level `x^{t/DEN}`, `t = ⌈h₁/2⌉`, over it.

* `lastC`, `initC`: the cell of the largest prime, and the box without it. `flipT`: the level.
* `flipTree`: the cost of the tree over the frozen part, in units of `1/K` of the sum of `1/R`: the terms at the
  first proposed floor that passes the tests `frozTests`, and Buchstab's identity from the floor to the level, the
  chain's first prime in cells searched by `solveG` with the nodes `opsK`.
* `flipOK`: a box that may be reversed. `flipCost`: the cost of the box, in units of `1/K`: with the tree's cost
  `c`, the share `D₀ = dropCost bl` of the box and the shares `E` of the two ends,
  `⌈(c·(h₁·D₀ + E) + bdK·E)/(DEN·K)⌉`.
* `opsF`: the nodes of the search with this bound and the reversal of `opsR`, whichever is less.

The file imports `SieveAdFrozDefs.lean`.
-/
import SieveAdFrozDefs

namespace SieveAd

open SieveCert (DEN K cdiv)

/-- The cell of the largest prime of a box: the last of its list. -/
def lastC : List Cell → Cell
  | [] => (0, 0)
  | [c] => c
  | _ :: c :: b => lastC (c :: b)

/-- The box without its largest prime. -/
def initC : List Cell → List Cell
  | [] => []
  | [_] => []
  | x :: c :: b => x :: initC (c :: b)

/-- The level of a reversal through a prime of exponent below `h₁/DEN`: the least `t` with `h₁ ≤ 2t`. -/
def flipT (ctx : Cell) : ℕ := (ctx.2 + 1) / 2

/-- A box that may be reversed through its largest prime: from two to `maxlen ≤ 11` primes, cells with
`0 < lo < hi` whose upper ends sum to at most `DEN − 2`, the second prime's cell at least one unit below the first's,
and the level at most the first prime's lower end, with room above. -/
def flipOK (maxlen : ℕ) (bl : List Cell) : Bool :=
  Nat.ble 2 bl.length && Nat.ble bl.length maxlen && Nat.ble maxlen 11 && cellsOK bl &&
    Nat.ble (hiSum bl + 2) DEN && Nat.ble ((lastC (initC bl)).2 + 1) (lastC bl).1 && Nat.ble 3 (lastC bl).1 &&
    Nat.ble (flipT (lastC bl)) (lastC bl).1 && Nat.ble ((lastC bl).2 + flipT (lastC bl) + 1) DEN

variable [SieveCert.IBPar]

/-- The cost of the tree over the frozen part of `β` and the slab of `ctx`, for the chain of one prime from a floor
to the level, in units of `1/K` of the sum of `1/R`: nothing is known (`lim`) if no proposed floor passes; else
the cells of the chain's prime from the first floor that passes to the level, cut at the proposed cuts. -/
def flipTree (SK : Cell → List Cell → Strat) (fuel : ℕ) (ctx : Cell) (β : List Cell) (lim : ℕ) : ℕ :=
  match β with
  | [] => lim
  | c :: b =>
    (fun τ S t =>
      match firstJ τ (c :: b) (minN c.1 t) (S.propJ (c :: b)) with
      | some f => kids (solveG (opsK ctx (Nat.succ b.length)) τ S fuel) t (c :: b) true (S.cuts (c :: b) f) f lim
      | none => lim)
      (frozTests (DEN - ctx.2) (DEN - ctx.1 + 1) (12 + DEN / c.1) (c :: b)) (SK ctx (c :: b)) (flipT ctx)

/-- **The cost of the reversal of a box of the sign `−` through its largest prime**, in units of `1/K`: with the
cost `c` of the tree over the frozen part, the share `D₀` of the box and the shares
`E = (h₁ + 1)·D₁ + (l₁ + 1)·D₂` of the boxes whose largest prime is within one unit of the ends of its cell,
`⌈(c·(h₁·D₀ + E) + bdK·E)/(DEN·K)⌉`. A value at least `lim` says nothing. -/
def flipCost (SK : Cell → List Cell → Strat) (fuel : ℕ) (bl : List Cell) (lim : ℕ) : ℕ :=
  (fun ctx β =>
    (fun c =>
      cond (Nat.ble CAPK c) lim
        ((fun E => cdiv (c * (ctx.2 * dropCost bl + E) + bdK ctx (flipT ctx) * E) (DEN * K))
          ((ctx.2 + 1) * dropCost (β ++ [(ctx.2 - 1, ctx.2 + 1)]) +
            (ctx.1 + 1) * dropCost (β ++ [(ctx.1 - 1, ctx.1 + 1)]))))
      (flipTree SK fuel ctx β CAPK))
    (lastC bl) (initC bl)

/-- **The search with the reversal through the largest prime**: the nodes of `opsR`, and for a box of the sign `−`
that may be reversed through its largest prime, that reversal's cost if it is less. -/
def opsF (τ : Tests) (SK₀ : Cell → ℕ → Strat) (fuel₀ : ℕ) (cq : ℕ → ℕ → List ℕ) (SK : Cell → List Cell → Strat)
    (fuel maxlen : ℕ) : Ops :=
  ⟨fun _ => true, vanishOK, dropC, fun bl par l =>
    (fun r => cond (!par && flipOK maxlen bl) ((fun c => cond (Nat.blt c r) c r) (flipCost SK fuel bl r)) r)
      (cond (!par && revOK bl) (revCost τ SK₀ fuel₀ cq bl l) l)⟩

end SieveAd
