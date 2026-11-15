/-
# The search led by hints with a cut of any cell of a box at any point, without Mathlib

`SieveAdDirDefs.lean`'s search cuts a box at the midpoint of its newest cell alone (`stepD`, the code `11110`). A
box that the edge of a test's zone crosses gets nothing of the zone that way: the zone is a condition on sums of
exponents, and the part of it inside the box is reached only by cuts of the older cells too, at the zone's edge
and not at a midpoint. The trees (`SieveAd.Tree.split`) and the terms (`SieveAd.bd_split`, `SieveAd.bdF_split`)
allow a cut of any cell at any point; here the search led by hints gets it, with no change to `stepD`: the cut is
read where `stepD` reads its hinted bound.

* `altC nb altH rec`: **a hinted bound that is a cut, or the bound `altH`**. One bit `0`: `altH` reads the rest.
  One bit `1`, four bits `t` and forty bits `c`: the cell at the position `t` of the box (the newest is `0`), one of
  the first `bl.length − nb`, is cut at the exponent `c` strictly inside it, and the cost is the sum of what `rec`
  returns for the box with that cell's upper end at `c` and for the box with its lower end at `c`, the second with
  what the first leaves of the limit.
* `solveDS O τ dI dJ kd nb altH n`: **the search led by hints with cuts of any cell**: `solveD` with, at each
  depth, the hinted bound `altC nb altH` of the search one level down.
* `flipTreeDYS`, `flipCostBYS`, `flipCostDYS`, `altFDYS`: `flipTreeDY`, `flipCostBY`, `flipCostDY` and `altFDY`
  with `solveDS` in the trees over the frozen parts, where a cut is of a cell of the chain (`nb` the number of
  frozen primes).

Their soundness is `SieveAdCut.lean`'s. The file imports `SieveAdResYDefs.lean`.
-/
import SieveAdResYDefs

namespace SieveAd

open SieveCert (DEN K)

/-- **A cut of a cell of the box, or the hinted bound `altH`**, read from the hints: `0` and `altH` reads on; or
`1`, four bits for the position `t` of a cell among the first `bl.length − nb`, and forty bits for an exponent `c`
strictly inside it: the sum of the costs of the two boxes that the cut leaves, by `rec`. -/
noncomputable def altC (nb : ℕ) (altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ)
    (rec : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (bl : List Cell) (par : Bool) (l h : ℕ) : ℕ × ℕ :=
  cond (Nat.beq (Nat.land h 1) 0) (altH bl par l (Nat.div h 2))
    ((fun t c h' =>
      cond (Nat.blt t (Nat.sub (lenR bl) nb) && splitOK bl t c)
        ((fun r =>
          cond (Nat.ble l r.1) (l, r.2)
            ((fun r2 => (Nat.add r.1 r2.1, r2.2)) (rec (setLo bl t c) par (Nat.sub l r.1) r.2)))
          (rec (setHi bl t c) par l h'))
        (l, h'))
      (Nat.land (Nat.div h 2) 15) (Nat.land (Nat.div h 32) 1099511627775) (Nat.div h 35184372088832))

/-- **The search led by hints with cuts of any cell**, to a depth of recursion `n`: `solveD`, its hinted bound at
each depth the cut `altC nb altH` over the search one level down. -/
noncomputable def solveDS (O : Ops) (τ : Tests) (dI : List Cell → ℕ → Cfg × ℕ)
    (dJ : List Cell → ℕ → (ℕ × Cfg) × ℕ)
    (kd : (List Cell → Bool → ℕ → ℕ → ℕ × ℕ) → ℕ → List Cell → Bool → ℕ → ℕ → ℕ → ℕ × ℕ) (nb : ℕ)
    (altH : List Cell → Bool → ℕ → ℕ → ℕ × ℕ) : ℕ → List Cell → Bool → ℕ → ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun _ => List Cell → Bool → ℕ → ℕ → ℕ × ℕ) (fun _ _ lim h => (lim, h))
    (fun _ ih => stepD O τ dI dJ kd (altC nb altH ih) ih)

variable [SieveCert.IBPar]

/-- **The tree over the frozen part of a reversal, searched with cuts of any cell of the chain**: `flipTreeDY`
with `solveDS` in the place of `solveD`; the frozen primes' cells, the last `nb` of a box, are not cut. -/
noncomputable def flipTreeDYS (κ hR fuel : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
    (lsβ hsβ nb lim h : ℕ) : ℕ × ℕ :=
  (fun e₁ e₂ t Kb =>
    (fun τ cl ch =>
      (fun p =>
        cond (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c.1 t) && τ.okJ (c :: b) p.1.1 p.1.2)
          (kidsF κ hR ctx nb
            (solveDS (opsKP ctx nb) τ cfgIFY (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN)) (kidsF κ hR ctx nb)
              nb noAltH fuel)
            t (c :: b) (!pos) p.1.1 lim p.2)
          (lim, p.2))
        (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN) (c :: b) h))
      (frozResTestsY e₁ e₂ Kb (c :: b) lsβ hsβ nb (lomP (c :: b) DEN)) (maxN 1 (Nat.sub e₁ hsβ))
      (Nat.sub e₂ lsβ))
    (cond pos (Nat.add (Nat.sub DEN ctx.2) 1) (Nat.sub DEN ctx.2))
    (cond pos (Nat.sub DEN ctx.1) (Nat.add (Nat.sub DEN ctx.1) 1)) (flipT ctx) (Nat.add 12 (Nat.div DEN c.1))

/-- `flipCostBY` with the tree `flipTreeDYS`. -/
noncomputable def flipCostBYS (κ hR fuel maxlen : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
    (ls hs tp ok n lh lim h : ℕ) : ℕ × ℕ :=
  cond (flipOKP maxlen ctx c hs ok n lh)
    ((fun E r =>
      (cond (Nat.ble CAPK r.1) lim
        (cdivP
          (Nat.add
            (Nat.mul r.1
              (cond pos (Nat.mul ctx.2 (dropL c ctx ls hs tp n))
                (Nat.add (Nat.mul ctx.2 (dropL c ctx ls hs tp n)) E)))
            (Nat.mul (bdKP ctx (flipT ctx)) E))
          (Nat.mul DEN K)), r.2))
      (Nat.add (Nat.mul (Nat.add ctx.2 1) (dropL c (Nat.sub ctx.2 1, Nat.add ctx.2 1) ls hs tp n))
        (Nat.mul (Nat.add ctx.1 1) (dropL c (Nat.sub ctx.1 1, Nat.add ctx.1 1) ls hs tp n)))
      (flipTreeDYS κ hR fuel pos ctx c b (Nat.add c.1 ls) (Nat.add c.2 hs) (Nat.succ n) CAPK h))
    (lim, h)

/-- `flipCostDY` with the tree `flipTreeDYS`. -/
noncomputable def flipCostDYS (κ hR fuel maxlen : ℕ) (pos : Bool) (bl : List Cell) (lim h : ℕ) : ℕ × ℕ :=
  (fun ctx =>
    List.casesOn (motive := fun _ => ℕ × ℕ) (initP bl) (lim, h) fun c b =>
      tailP b 0 0 1 (cellI c) 0 c.2 fun ls hs tp ok n lh =>
        flipCostBYS κ hR fuel maxlen pos ctx c b ls hs tp ok n lh lim h)
    (lastP bl (0, 0))

/-- **The reversal as a bound that reads hints, its trees searched with cuts of any cell**: `altFDY` with
`flipCostDYS`. -/
noncomputable def altFDYS (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ) : ℕ × ℕ :=
  flipCostDYS κ hR fuel maxlen par bl l h

end SieveAd
