/-
# The resonant window's test at the two corners of a box, in the search, without Mathlib

`SieveAdResDefs.lean` and `SieveAdFrozResDefs.lean` have the resonant window's test of a box, `chkIRC` in the main
tree and `chkIRF` in the trees over the frozen parts: `SieveResTest.resX` on the rest's lower ends and the sum of
its upper ends. `SieveResTest.resYH` (`SieveResTestYDefs.lean`) tests the box of the rest's cells at its two
corners, the variable tied to the rest. This file is the kernel's side of the search with both:

* `rpassY bl m k`: one pass over the box: the cells at the set bits of `m` (in the list's order), how many they
  are, whether every cell has `1 ≤ lo ≤ hi ≤ DEN`, and the number of cells, passed to `k`.
* `chkIRY bl sr s`: **the test at the two corners of a box of the main tree**: at most `13` cells, each from `1`, a
  rest `sr` with at least one cell, and `resYH` on the rest's cells with the hints `s`; when the bit of `sr` after
  the box's cells is set, with the cofactor's cell `(max(DEN − Σhi − 1, lo₀), DEN − Σlo + 1)` after them, under
  `chkIRC`'s conditions. `chkIRFY`: the same on a box `ch ++ β` of a tree over a frozen part, as `chkIRF`.
* `resTestsFY`, `frozResTestsY`: the tests: `chkIRY` (`chkIRFY`) for an evaluation of kind `4`, `resTestsFC`'s
  (`frozResTestsC`'s) otherwise.
* `cfgIPY`, `cfgIMY`, `cfgIFY`: the configuration of an evaluation from the hints, by the two low bits: `0` in the
  first, `cfgIPR`'s code (`cfgIP`'s); `1` then `0`, `cfgIPR`'s window code after them; `1` and `1`, the rest (a set
  of `pw` values) and `resYH`'s hints, `12 + (15 + 3n)(kH + kL)` bits with `n`, `kH`, `kL` in the low twelve, as the
  configuration of kind `4`.
* `flipTreeDY`, `flipCostBY`, `flipCostDY`, `altFDY`: `flipTreeDR`, `flipCostBR`, `flipCostDR` and `altFDR` with
  these tests and this configuration in the trees over the frozen parts.

Their soundness is `SieveAdResY.lean`'s and `SieveAdFrozResYTree.lean`'s. The file imports
`SieveAdFrozResDefs.lean` and `SieveResTestYDefs.lean`.
-/
import SieveAdFrozResDefs
import SieveResTestYDefs

namespace SieveAd

open SieveCert (DEN K)

/-- **One pass over a box for the test at the two corners**: for the set of bits `m`, its cells in the list's
order, how many they are, whether every cell of the box has `1 ≤ lo ≤ hi ≤ DEN`, and the number of cells. -/
noncomputable def rpassY {α : Type} : List Cell → ℕ → (List Cell → ℕ → Bool → ℕ → α) → α :=
  List.rec (motive := fun _ => ℕ → (List Cell → ℕ → Bool → ℕ → α) → α) (fun _ k => k [] 0 true 0)
    (fun x _ ih m k =>
      ih (Nat.div m 2) fun cs ns ok n =>
        k (cond (Nat.beq (Nat.land m 1) 1) (x :: cs) cs) (Nat.add (Nat.land m 1) ns)
          (ok && Nat.ble 1 x.1 && Nat.ble x.1 x.2 && Nat.ble x.2 DEN) (Nat.succ n))

section

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- **The test at the two corners of a box, with its cofactor**: at most `13` cells, each with
`1 ≤ lo ≤ hi ≤ DEN`, a rest `sr` with at least one cell, and `SieveResTest.resYH` on the rest's cells with the hints
`s`; when the bit of `sr` after the box's cells is set, the cofactor in the rest after the box's primes: when the
box's upper ends sum to at most `DEN − 2` and its lower ends with twice its least prime's reach `DEN + 1`, in the
cell `(max(DEN − Σhi − 1, lo₀), DEN − Σlo + 1)`. -/
noncomputable def chkIRY (bl : List Cell) (sr s : ℕ) : Bool :=
  rpassY bl sr fun cs ns ok n =>
    Nat.ble n 13 && ok && Nat.blt 0 ns &&
      cond (Nat.beq (Nat.land (Nat.shiftRight sr n) 1) 1)
        (Nat.ble (Nat.add (hiSum bl) 2) DEN && Nat.ble (Nat.add DEN 1) (Nat.add (loSum bl) (Nat.mul 2 (headLo bl))) &&
          SieveResTest.resYH Lnum Lden
            (cs ++ [(maxN (Nat.sub (Nat.sub DEN (hiSum bl)) 1) (headLo bl), Nat.add (Nat.sub DEN (loSum bl)) 1)]) s)
        (SieveResTest.resYH Lnum Lden cs s)

/-- **The tests with the window's test at the two corners too**: `chkIRY` for an evaluation of kind `4`, the rest
`sr` and the hints `s1`; `resTestsFC`'s otherwise. -/
noncomputable def resTestsFY : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 4) (chkIRY bl cfg.sr cfg.s1) (resTestsFC.okI bl cfg), resTestsFC.okJ⟩

/-- **The test at the two corners of a box `ch ++ β` of a tree over a frozen part, with the chain's cofactor**: as
`chkIRY`, the cofactor's cell and its conditions those of `chkIRF`: with the slab `(x^{e₁/DEN}, x^{e₂/DEN}]`, when
the chain's upper ends with `e₂` sum to at most `DEN − 2` and its lower ends with `e₁` and twice its least prime's
reach `DEN + 1`, the cell `(max(DEN − e₂ − Σhi − 1, lo₀), DEN − e₁ − Σlo + 1)`. -/
noncomputable def chkIRFY (e₁ e₂ : ℕ) (β bl : List Cell) (sr s : ℕ) : Bool :=
  (fun slo shi =>
    rpassY bl sr fun cs ns ok n =>
      Nat.ble n 13 && ok && Nat.blt 0 ns &&
        cond (Nat.beq (Nat.land (Nat.shiftRight sr n) 1) 1)
          (Nat.ble (Nat.add (Nat.add e₂ shi) 2) DEN &&
            Nat.ble (Nat.add DEN 1) (Nat.add (Nat.add e₁ slo) (Nat.mul 2 (headLo bl))) &&
            SieveResTest.resYH Lnum Lden
              (cs ++ [(maxN (Nat.sub (Nat.sub (Nat.sub DEN e₂) shi) 1) (headLo bl),
                Nat.add (Nat.sub (Nat.sub DEN e₁) slo) 1)]) s)
          (SieveResTest.resYH Lnum Lden cs s))
    (Nat.sub (loSum bl) (loSum β)) (Nat.sub (hiSum bl) (hiSum β))

/-- **The tests of a tree over a frozen part, with the window's test at the two corners too**: `chkIRFY` on the box
`ch ++ β` for an evaluation of kind `4`, `frozResTestsC`'s otherwise. -/
noncomputable def frozResTestsY (e₁ e₂ Kb : ℕ) (β : List Cell) (lsβ hsβ nb lomβ : ℕ) : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 4) (chkIRFY e₁ e₂ β bl cfg.sr cfg.s1)
      ((frozResTestsC e₁ e₂ Kb β lsβ hsβ nb lomβ).okI bl cfg),
    (frozResTestsC e₁ e₂ Kb β lsβ hsβ nb lomβ).okJ⟩

end

/-- The configuration of an evaluation, from the hints, by the two low bits: `0` in the first, `cfgIPR`'s code
(`cfgIP`'s); `1` then `0`, `cfgIPR`'s window code after them; `1` and `1`, the rest (a set of `pw` values) and the
hints of `SieveResTest.resYH`, `12 + (15 + 3n)(kH + kL)` bits with `n`, `kH` and `kL` in the low twelve, as the
configuration of kind `4` with the hints in `s1`. -/
noncomputable def cfgIPY (pw h : ℕ) : Cfg × ℕ :=
  cond (Nat.beq (Nat.land h 3) 3)
    ((fun h1 =>
      (fun sr h2 =>
        (fun p => (⟨4, 0, sr, Nat.mod h2 p, false⟩, Nat.div h2 p))
          (Nat.pow 2 (Nat.add 12 (Nat.mul (Nat.add 15 (Nat.mul 3 (Nat.mod h2 16)))
            (Nat.add (Nat.mod (Nat.div h2 16) 16) (Nat.mod (Nat.div h2 256) 16))))))
        (Nat.mod h1 pw) (Nat.div h1 pw))
      (Nat.div h 4))
    (cond (Nat.beq (Nat.land h 3) 1) (cfgIPR pw (Nat.add 1 (Nat.mul 2 (Nat.div h 4)))) (cfgIPR pw h))

/-- **The configuration of an evaluation in the main tree, with the window's test at the two corners too**:
`cfgIPY` with a set of as many bits as the box has cells and one more, for the cofactor. -/
noncomputable def cfgIMY (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIPY (Nat.pow 2 (Nat.succ (lenR bl))) h

/-- **The configuration of an evaluation in a tree over a frozen part, with the window's test at the two corners
too**: `cfgIPY` with a set of as many bits as the box has cells and one more, for the cofactor. -/
noncomputable def cfgIFY (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIPY (Nat.pow 2 (Nat.succ (lenR bl))) h

variable [SieveCert.IBPar]

/-- **The tree over the frozen part of a reversal, with the window's test at the two corners too**: `flipTreeD`
with the tests `frozResTestsY` and the configurations `cfgIFY`. -/
noncomputable def flipTreeDY (κ hR fuel : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
    (lsβ hsβ nb lim h : ℕ) : ℕ × ℕ :=
  (fun e₁ e₂ t Kb =>
    (fun τ cl ch =>
      (fun p =>
        cond (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c.1 t) && τ.okJ (c :: b) p.1.1 p.1.2)
          (kidsF κ hR ctx nb
            (solveD (opsKP ctx nb) τ cfgIFY (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN)) (kidsF κ hR ctx nb)
              noAltH fuel)
            t (c :: b) (!pos) p.1.1 lim p.2)
          (lim, p.2))
        (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN) (c :: b) h))
      (frozResTestsY e₁ e₂ Kb (c :: b) lsβ hsβ nb (lomP (c :: b) DEN)) (maxN 1 (Nat.sub e₁ hsβ))
      (Nat.sub e₂ lsβ))
    (cond pos (Nat.add (Nat.sub DEN ctx.2) 1) (Nat.sub DEN ctx.2))
    (cond pos (Nat.sub DEN ctx.1) (Nat.add (Nat.sub DEN ctx.1) 1)) (flipT ctx) (Nat.add 12 (Nat.div DEN c.1))

/-- `flipCostB` with the tree `flipTreeDY`. -/
noncomputable def flipCostBY (κ hR fuel maxlen : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
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
      (flipTreeDY κ hR fuel pos ctx c b (Nat.add c.1 ls) (Nat.add c.2 hs) (Nat.succ n) CAPK h))
    (lim, h)

/-- `flipCostD` with the tree `flipTreeDY`. -/
noncomputable def flipCostDY (κ hR fuel maxlen : ℕ) (pos : Bool) (bl : List Cell) (lim h : ℕ) : ℕ × ℕ :=
  (fun ctx =>
    List.casesOn (motive := fun _ => ℕ × ℕ) (initP bl) (lim, h) fun c b =>
      tailP b 0 0 1 (cellI c) 0 c.2 fun ls hs tp ok n lh =>
        flipCostBY κ hR fuel maxlen pos ctx c b ls hs tp ok n lh lim h)
    (lastP bl (0, 0))

/-- **The bound that reads hints, with the window's test at the two corners over the frozen parts too**: `altFD`
with `flipCostDY`. -/
noncomputable def altFDY (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ) : ℕ × ℕ :=
  flipCostDY κ hR fuel maxlen par bl l h

end SieveAd
