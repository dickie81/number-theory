/-
# The window's test at the two corners of a box and the lines named by the hint, in the search, without Mathlib

`SieveAdResYDefs.lean` has the search with the window's test at the two corners of a box (`SieveResTest.resYH`, an
evaluation of kind `4`) besides the resonant window's (`SieveResTest.resX`, kind `3`), and `SieveAdResHDefs.lean`
the resonant window's tests with the lines named by the hint (`SieveResTest.resXH`). These are the search with both:
the names end in `YH`.

* `resTestsFYH`, `frozResTestsYH`: the tests: `chkIRY` (`chkIRFY`) for an evaluation of kind `4`, `resTestsFCH`'s
  (`frozResTestsCH`'s) otherwise.
* `cfgIPYH`, `cfgIMYH`, `cfgIFYH`: the configuration of an evaluation from the hints, as `cfgIPY`, with `cfgIPRH`'s
  where the window's code has an interval: its records name the lines.
* `flipTreeDYH`, `flipCostBYH`, `flipCostDYH`, `altFDYH`: `flipTreeDY` … `altFDY` with these tests and this
  configuration in the trees over the frozen parts.

Their soundness is `SieveAdResYH.lean`'s. The file imports `SieveAdResYDefs.lean` and `SieveAdResHDefs.lean`.
-/
import SieveAdResYDefs
import SieveAdResHDefs

namespace SieveAd

open SieveCert (DEN K)

section

variable [SieveCert.IBPar]

/-- **The tests with the window's test at the two corners and the lines named by the hint**: `chkIRY` for an
evaluation of kind `4`, the rest `sr` and the hints `s1`; `resTestsFCH`'s otherwise. -/
noncomputable def resTestsFYH : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 4) (chkIRY bl cfg.sr cfg.s1) (resTestsFCH.okI bl cfg), resTestsFCH.okJ⟩

/-- **The tests of a tree over a frozen part, with the window's test at the two corners and the lines named by the
hint**: `chkIRFY` on the box `ch ++ β` for an evaluation of kind `4`, `frozResTestsCH`'s otherwise. -/
noncomputable def frozResTestsYH (e₁ e₂ Kb : ℕ) (β : List Cell) (lsβ hsβ nb lomβ : ℕ) : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 4) (chkIRFY e₁ e₂ β bl cfg.sr cfg.s1)
      ((frozResTestsCH e₁ e₂ Kb β lsβ hsβ nb lomβ).okI bl cfg),
    (frozResTestsCH e₁ e₂ Kb β lsβ hsβ nb lomβ).okJ⟩

end

/-- The configuration of an evaluation, from the hints: `cfgIPY`'s, with `cfgIPRH`'s in place of `cfgIPR`'s where
the window's code has an interval, so that its records name the lines: where the code has no interval in either
form (`1`, the rest and eight bits `0`), the hints of `SieveResTest.resYH` follow, as the configuration of kind `4`. -/
noncomputable def cfgIPYH (pw h : ℕ) : Cfg × ℕ :=
  cond (Nat.beq (Nat.land h 1) 1 && Nat.beq (Nat.mod (Nat.div (Nat.div h 2) pw) 256) 0)
    ((fun h1 =>
      (fun sr h2 =>
        (fun p => (⟨4, 0, sr, Nat.mod h2 p, false⟩, Nat.div h2 p))
          (Nat.pow 2 (Nat.add 12 (Nat.mul (Nat.add 15 (Nat.mul 3 (Nat.mod h2 16)))
            (Nat.add (Nat.mod (Nat.div h2 16) 16) (Nat.mod (Nat.div h2 256) 16))))))
        (Nat.mod h1 pw) (Nat.div (Nat.div h1 pw) 256))
      (Nat.div h 2))
    (cfgIPRH pw h)

/-- **The configuration of an evaluation in the main tree, with the window's test at the two corners and the lines
named by the hint**: `cfgIPYH` with a set of as many bits as the box has cells and one more, for the cofactor. -/
noncomputable def cfgIMYH (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIPYH (Nat.pow 2 (Nat.succ (lenR bl))) h

/-- **The configuration of an evaluation in a tree over a frozen part, with the window's test at the two corners and
the lines named by the hint**: `cfgIPYH` with a set of as many bits as the box has cells and one more, for the
cofactor. -/
noncomputable def cfgIFYH (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIPYH (Nat.pow 2 (Nat.succ (lenR bl))) h

variable [SieveCert.IBPar]

/-- **The tree over the frozen part of a reversal, with the window's test at the two corners and the lines named by
the hint**: `flipTreeD` with the tests `frozResTestsYH` and the configurations `cfgIFYH`. -/
noncomputable def flipTreeDYH (κ hR fuel : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
    (lsβ hsβ nb lim h : ℕ) : ℕ × ℕ :=
  (fun e₁ e₂ t Kb =>
    (fun τ cl ch =>
      (fun p =>
        cond (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c.1 t) && τ.okJ (c :: b) p.1.1 p.1.2)
          (kidsF κ hR ctx nb
            (solveD (opsKP ctx nb) τ cfgIFYH (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN)) (kidsF κ hR ctx nb)
              noAltH fuel)
            t (c :: b) (!pos) p.1.1 lim p.2)
          (lim, p.2))
        (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN) (c :: b) h))
      (frozResTestsYH e₁ e₂ Kb (c :: b) lsβ hsβ nb (lomP (c :: b) DEN)) (maxN 1 (Nat.sub e₁ hsβ))
      (Nat.sub e₂ lsβ))
    (cond pos (Nat.add (Nat.sub DEN ctx.2) 1) (Nat.sub DEN ctx.2))
    (cond pos (Nat.sub DEN ctx.1) (Nat.add (Nat.sub DEN ctx.1) 1)) (flipT ctx) (Nat.add 12 (Nat.div DEN c.1))

/-- `flipCostB` with the tree `flipTreeDYH`. -/
noncomputable def flipCostBYH (κ hR fuel maxlen : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
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
      (flipTreeDYH κ hR fuel pos ctx c b (Nat.add c.1 ls) (Nat.add c.2 hs) (Nat.succ n) CAPK h))
    (lim, h)

/-- `flipCostD` with the tree `flipTreeDYH`. -/
noncomputable def flipCostDYH (κ hR fuel maxlen : ℕ) (pos : Bool) (bl : List Cell) (lim h : ℕ) : ℕ × ℕ :=
  (fun ctx =>
    List.casesOn (motive := fun _ => ℕ × ℕ) (initP bl) (lim, h) fun c b =>
      tailP b 0 0 1 (cellI c) 0 c.2 fun ls hs tp ok n lh =>
        flipCostBYH κ hR fuel maxlen pos ctx c b ls hs tp ok n lh lim h)
    (lastP bl (0, 0))

/-- **The bound that reads hints, with the window's test at the two corners and the lines named by the hint over the
frozen parts**: `altFD` with `flipCostDYH`. -/
noncomputable def altFDYH (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ) : ℕ × ℕ :=
  flipCostDYH κ hR fuel maxlen par bl l h

end SieveAd
