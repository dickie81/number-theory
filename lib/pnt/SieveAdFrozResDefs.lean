/-
# The resonant window's test in the trees over the frozen parts, without Mathlib

`SieveAdResDefs.lean` has the resonant window's test of a box of the main tree, `chkIR`, read from the hints by
`cfgIMR`. A box of a tree over a frozen part is the chain's cells followed by the frozen primes' (`ch ++ β`), and the
same test applies to it: a rest among its primes, the frozen ones included, each in its cell. This file is the
kernel's side of the search with it:

* `frozResTestsC`: **the tests of a tree over a frozen part with the resonant window**: `okIR` for an evaluation of
  kind `3`, `frozTestsC`'s otherwise.
* `cfgIFR`: the configuration of an evaluation in a tree over a frozen part, from the hints: `0` and `cfgIF`'s
  code, or `1`, the rest, ten bits `nb` and the test's hint (`cfgIPR` with the cofactor's bit).
* `flipTreeDR`, `flipCostBR`, `flipCostDR`, `altFDR`: `flipTreeD`, `flipCostB`, `flipCostD` and `altFD` with these
  tests and this configuration in the trees over the frozen parts.

Their soundness is `SieveAdFrozResTree.lean`'s. The file imports `SieveAdResDefs.lean`.
-/
import SieveAdResDefs

namespace SieveAd

open SieveCert (DEN K)

section

variable [SieveCert.IBPar]

/-- **The tests of a tree over a frozen part, with the resonant window**: `okIR` on the box `ch ++ β` for an
evaluation of kind `3`, `frozTestsC`'s otherwise. -/
noncomputable def frozResTestsC (e₁ e₂ Kb : ℕ) (β : List Cell) (lsβ hsβ nb lomβ : ℕ) : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 3) (okIR bl cfg) ((frozTestsC e₁ e₂ Kb β lsβ hsβ nb lomβ).okI bl cfg),
    (frozTestsC e₁ e₂ Kb β lsβ hsβ nb lomβ).okJ⟩

end

/-- **The configuration of an evaluation in a tree over a frozen part, with the resonant window**, from the hints:
`cfgIPR` with a set of as many bits as the box has cells and one more, for the cofactor. -/
noncomputable def cfgIFR (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIPR (Nat.pow 2 (Nat.succ (lenR bl))) h

variable [SieveCert.IBPar]

/-- **The tree over the frozen part of a reversal, with the resonant window**: `flipTreeD` with the tests
`frozResTestsC` and the configurations `cfgIFR`. -/
noncomputable def flipTreeDR (κ hR fuel : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
    (lsβ hsβ nb lim h : ℕ) : ℕ × ℕ :=
  (fun e₁ e₂ t Kb =>
    (fun τ cl ch =>
      (fun p =>
        cond (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c.1 t) && τ.okJ (c :: b) p.1.1 p.1.2)
          (kidsF κ hR ctx nb
            (solveD (opsKP ctx nb) τ cfgIFR (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN)) (kidsF κ hR ctx nb)
              noAltH fuel)
            t (c :: b) (!pos) p.1.1 lim p.2)
          (lim, p.2))
        (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN) (c :: b) h))
      (frozResTestsC e₁ e₂ Kb (c :: b) lsβ hsβ nb (lomP (c :: b) DEN)) (maxN 1 (Nat.sub e₁ hsβ))
      (Nat.sub e₂ lsβ))
    (cond pos (Nat.add (Nat.sub DEN ctx.2) 1) (Nat.sub DEN ctx.2))
    (cond pos (Nat.sub DEN ctx.1) (Nat.add (Nat.sub DEN ctx.1) 1)) (flipT ctx) (Nat.add 12 (Nat.div DEN c.1))

/-- `flipCostB` with the tree `flipTreeDR`. -/
noncomputable def flipCostBR (κ hR fuel maxlen : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
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
      (flipTreeDR κ hR fuel pos ctx c b (Nat.add c.1 ls) (Nat.add c.2 hs) (Nat.succ n) CAPK h))
    (lim, h)

/-- `flipCostD` with the tree `flipTreeDR`. -/
noncomputable def flipCostDR (κ hR fuel maxlen : ℕ) (pos : Bool) (bl : List Cell) (lim h : ℕ) : ℕ × ℕ :=
  (fun ctx =>
    List.casesOn (motive := fun _ => ℕ × ℕ) (initP bl) (lim, h) fun c b =>
      tailP b 0 0 1 (cellI c) 0 c.2 fun ls hs tp ok n lh =>
        flipCostBR κ hR fuel maxlen pos ctx c b ls hs tp ok n lh lim h)
    (lastP bl (0, 0))

/-- **The bound that reads hints, with the resonant window over the frozen parts**: `altFD` with `flipCostDR`. -/
noncomputable def altFDR (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ) : ℕ × ℕ :=
  flipCostDR κ hR fuel maxlen par bl l h

end SieveAd
