/-
# The search led by hints, without Mathlib

`SieveAdRevDefs.lean`'s search tries, at each box, what its strategy proposes: the configurations that may
evaluate the box, then the box dropped against Buchstab's identity below it, then one more bound. Most of what the
kernel does in it is lost: trees searched below a box that is then dropped or bounded otherwise, and the search
for a floor and its configuration among every proposal, which over a frozen part costs ten times the test of the
floor. Here the search is told what to do at each box by a number, the **hints**, read from its low end in the
order in which the search visits the boxes. The action is a run of ones closed by a zero:

* `0`: the box has no term, or a proposed configuration evaluates it (cost `0`);
* `10`, then four bits `sel`: Buchstab's identity at the floor and with the configuration that the guide `gJ`
  gives for `sel`, the new prime's range cut at the proposed cuts, and its cells by the hints that follow;
* `110`: the box is dropped, at the cost `Ops.drp` gives;
* `1110`: the bound `Ops.alt`;
* `11110`: a bound that reads hints itself (`altH`);
* `111110`: the last prime's cell cut in two, and the halves by the hints that follow.

A step whose test fails returns its limit, which says nothing; so does `111111`. The hints choose among bounds
that hold, and the cost returned is a bound whatever they are and whatever the guide is (`SieveAdHint.lean`).

* `kidsH`: `kids` with the hints passed from a cell to the next, and one bit at each proposed cut: the range is
  cut there, or the cells on its two sides are one.
* `stepH`, `solveH`: the step and the search. A value is a cost and the hints left.
* `noAltH`: no bound that reads hints.
* `flipTreeH`, `flipCostH`, `altFH`: `SieveAdFlipDefs.lean`'s reversal of a box through its largest prime, the tree
  over the frozen part searched by hints: four bits for the floor of the terms of the frozen part, then the hints
  of the cells of the chain's first prime.

The file imports `SieveAdFlipDefs.lean`.
-/
import SieveAdFlipDefs

namespace SieveAd

open SieveCert (DEN K cdiv)

/-- `kids` for a search led by hints: the cells of the new prime from `a` to `top`. At each proposed cut that lies
inside, one bit of the hints says whether the range is cut there (`1`) or not (`0`); the costs of the cells are
summed, each searched with the limit that the cells before it leave and the hints that they leave. -/
def kidsH (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (top : ℕ) (bl : List Cell) (par : Bool) :
    List ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | [], a, lim, h => rec ((a, top) :: bl) par lim h
  | c :: cs, a, lim, h =>
    cond (Nat.blt a c && Nat.blt c top)
      (cond (Nat.beq (Nat.mod h 2) 1)
        ((fun r =>
          cond (Nat.ble lim r.1) r
            ((fun r2 => (Nat.add r.1 r2.1, r2.2)) (kidsH rec top bl par cs c (Nat.sub lim r.1) r.2)))
          (rec ((a, c) :: bl) par lim (Nat.div h 2)))
        (kidsH rec top bl par cs a lim (Nat.div h 2)))
      (kidsH rec top bl par cs a lim h)

/-- One step of the search led by hints on a box: what the low bits of the hints say, the boxes below it by
`rec`, a floor and its configuration by the guide `gJ`. -/
def stepH (O : Ops) (τ : Tests) (S : Strat) (gJ : List Cell → ℕ → Option (ℕ × Cfg))
    (altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (bl : List Cell)
    (par : Bool) (lim h : ℕ) : ℕ × ℕ :=
  match bl with
  | [] => (lim, h)
  | x :: b =>
    cond (O.grd (x :: b))
      (cond (Nat.beq (Nat.mod h 2) 0)
        (cond (O.van (x :: b) || anyI τ (x :: b) (S.propI (x :: b))) (0, Nat.div h 2) (lim, Nat.div h 2))
        (cond (Nat.beq (Nat.mod h 4) 1)
          (match gJ (x :: b) (Nat.mod (Nat.div h 4) 16) with
            | some p =>
              cond (Nat.blt 0 p.1 && Nat.ble p.1 x.1 && τ.okJ (x :: b) p.1 p.2)
                (kidsH rec x.2 (x :: b) (!par) (S.cuts (x :: b) p.1) p.1 lim (Nat.div h 64))
                (lim, Nat.div h 64)
            | none => (lim, Nat.div h 64))
          (cond (Nat.beq (Nat.mod h 8) 3)
            (match O.drp (x :: b) par with
              | some dc => (dc, Nat.div h 8)
              | none => (lim, Nat.div h 8))
            (cond (Nat.beq (Nat.mod h 16) 7) (O.alt (x :: b) par lim, Nat.div h 16)
              (cond (Nat.beq (Nat.mod h 32) 15) (altH (x :: b) par lim (Nat.div h 32))
                (cond (Nat.beq (Nat.mod h 64) 31)
                  ((fun mid =>
                    cond (Nat.blt x.1 mid && Nat.blt mid x.2)
                      ((fun r =>
                        cond (Nat.ble lim r.1) r
                          ((fun r2 => (Nat.add r.1 r2.1, r2.2))
                            (rec ((mid, x.2) :: b) par (Nat.sub lim r.1) r.2)))
                        (rec ((x.1, mid) :: b) par lim (Nat.div h 64)))
                      (lim, Nat.div h 64))
                    (Nat.div (Nat.add x.1 x.2) 2))
                  (lim, Nat.div h 64)))))))
      (lim, h)

/-- **The search led by hints**, to a depth of recursion `n`: a cost for the term of the box `bl` with the sign
`par`, and the hints left; a cost at least `lim` says nothing. -/
def solveH (O : Ops) (τ : Tests) (S : Strat) (gJ : List Cell → ℕ → Option (ℕ × Cfg))
    (altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) : ℕ → List Cell → Bool → ℕ → ℕ → ℕ × ℕ
  | 0 => fun _ _ lim h => (lim, h)
  | n + 1 => stepH O τ S gJ altH (solveH O τ S gJ altH n)

/-- No bound that reads hints. -/
def noAltH (_ : List Cell) (_ : Bool) (l h : ℕ) : ℕ × ℕ := (l, h)

variable [SieveCert.IBPar]

/-- `flipTree` with the tree searched by hints: the terms of the frozen part at the floor and with the
configuration that the guide gives for the four low bits of the hints, and the cells of the chain's first prime by
the hints after them. -/
def flipTreeH (SK : Cell → List Cell → Strat) (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg))
    (fuel : ℕ) (ctx : Cell) (β : List Cell) (lim h : ℕ) : ℕ × ℕ :=
  match β with
  | [] => (lim, h)
  | c :: b =>
    (fun τ S t =>
      match GK ctx (c :: b) (c :: b) (Nat.mod h 16) with
      | some p =>
        cond (Nat.blt 0 p.1 && Nat.ble p.1 (minN c.1 t) && τ.okJ (c :: b) p.1 p.2)
          (kidsH (solveH (opsK ctx (Nat.succ b.length)) τ S (GK ctx (c :: b)) noAltH fuel) t (c :: b) true
            (S.cuts (c :: b) p.1) p.1 lim (Nat.div h 16))
          (lim, Nat.div h 16)
      | none => (lim, Nat.div h 16))
      (frozTests (DEN - ctx.2) (DEN - ctx.1 + 1) (12 + DEN / c.1) (c :: b)) (SK ctx (c :: b)) (flipT ctx)

/-- **The cost of the reversal of a box of the sign `−` through its largest prime, the tree over the frozen part
searched by hints**: `flipCost`'s formula on the tree's cost, the tree searched with the limit `CAPK`. -/
def flipCostH (SK : Cell → List Cell → Strat) (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg))
    (fuel : ℕ) (bl : List Cell) (lim h : ℕ) : ℕ × ℕ :=
  (fun ctx β =>
    (fun E =>
      (fun r =>
        (cond (Nat.ble CAPK r.1) lim
          (cdiv (r.1 * (ctx.2 * dropCost bl + E) + bdK ctx (flipT ctx) * E) (DEN * K)), r.2))
        (flipTreeH SK GK fuel ctx β CAPK h))
      ((ctx.2 + 1) * dropCost (β ++ [(ctx.2 - 1, ctx.2 + 1)]) +
        (ctx.1 + 1) * dropCost (β ++ [(ctx.1 - 1, ctx.1 + 1)])))
    (lastC bl) (initC bl)

/-- **The bound that reads hints**: for a box of the sign `−` that may be reversed through its largest prime,
that reversal's cost, its tree searched by hints. -/
def altFH (SK : Cell → List Cell → Strat) (GK : Cell → List Cell → List Cell → ℕ → Option (ℕ × Cfg))
    (fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ) : ℕ × ℕ :=
  cond (!par && flipOK maxlen bl) (flipCostH SK GK fuel bl l h) (l, h)

end SieveAd
