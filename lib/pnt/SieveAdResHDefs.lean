/-
# The resonant window's tests with the lines named by the hint, without Mathlib

`SieveAdResDefs.lean` and `SieveAdFrozResDefs.lean` have the resonant window's tests of a box, of the main tree
(`chkIRC`) and of a tree over a frozen part (`chkIRF`), with `SieveResTest.resX`, which picks each interval's lines
at the interval's midpoint. These are the same tests with `SieveResTest.resXH`, which reads them from the hint
(`SieveResTestHDefs.lean`), and the same search with them; the names end in `H`. The search's tests, `chkIRCH` and
`chkIRFH`, call it as `SieveResTest.resXHF` (`SieveResTestFDefs.lean`), the same function in the form that the kernel
evaluates fastest (`SieveResTest.resXHF_eq`).

* `popc`, `cfgIPRH`, `cfgIMRCH`, `cfgIFRH`: the configuration of an evaluation from the hints, its intervals'
  records of `15 + 2n` bits (`15 + 3n` with the large values' terms) for the `n` terms that the rest names.
* `chkIRH`, `chkIRCH`, `okIRCH`, `resTestsFCH`: the main tree's test without and with the cofactor, and its tests.
* `chkIRFH`, `okIRFH`, `frozResTestsCH`: the test of a box `ch ++ β` of a tree over a frozen part, and its tests.
* `flipTreeDRH`, `flipCostBRH`, `flipCostDRH`, `altFDRH`: the hinted bound with these tests in the trees over the
  frozen parts.

Their soundness is `SieveAdResH.lean`'s. The file imports `SieveAdFrozResDefs.lean` and `SieveResTestFDefs.lean`.
-/
import SieveAdFrozResDefs
import SieveResTestFDefs

namespace SieveAd

open SieveCert (DEN K)

/-- The number of set bits of `m` below `2^16`: the number of the rest's terms that a mask names. -/
def popc (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih x => Nat.add (Nat.land x 1) (ih (Nat.shiftRight x 1))) 16 m

/-- An interval's record for `n` terms: `15 + 2n` bits. -/
def recW2 (n : ℕ) : ℕ := Nat.add 15 (Nat.mul 2 n)

/-- An interval's record for `n` terms with the large values' terms: `15 + 3n` bits. -/
def recW3 (n : ℕ) : ℕ := Nat.add 15 (Nat.mul 3 n)

/-- The configuration of an evaluation, from the hints: `0` and `cfgIP`'s code; or `1`, the rest (a set of `pw`
values), four bits `k` and the test's `k` intervals' records, each `15 + 2n` bits for the `n` terms that the rest
names (`resTH`); for `k = 0`, four more bits `k₂` and `k₂` records of `15 + 3n` bits (`resT2H`). As `cfgIPR`, with
`k + 16·records` (or `16·(k₂ + 16·records)`) in `s1`. -/
noncomputable def cfgIPRH (pw h : ℕ) : Cfg × ℕ :=
  Bool.rec (motive := fun _ => Cfg × ℕ) (cfgIP pw (Nat.div h 2))
    ((fun h1 =>
      (fun k h2 =>
        cond (Nat.beq k 0)
          ((fun k2 h3 =>
            (⟨3, 0, Nat.mod h1 pw,
                Nat.mul 16 (Nat.add k2
                  (Nat.mul 16 (Nat.mod h3 (Nat.pow 2 (Nat.mul (recW3 (popc (Nat.mod h1 pw))) k2))))),
                false⟩,
              Nat.div h3 (Nat.pow 2 (Nat.mul (recW3 (popc (Nat.mod h1 pw))) k2))))
            (Nat.mod h2 16) (Nat.div h2 16))
          (⟨3, 0, Nat.mod h1 pw,
              Nat.add k (Nat.mul 16 (Nat.mod h2 (Nat.pow 2 (Nat.mul (recW2 (popc (Nat.mod h1 pw))) k)))),
              false⟩,
            Nat.div h2 (Nat.pow 2 (Nat.mul (recW2 (popc (Nat.mod h1 pw))) k))))
        (Nat.mod (Nat.div h1 pw) 16) (Nat.div (Nat.div h1 pw) 16))
      (Nat.div h 2))
    (Nat.beq (Nat.land h 1) 1)

/-- The configuration of an evaluation in the main tree with the cofactor's bit, its window's lines named by the
hint: `cfgIPRH` with a set of as many bits as the box has cells and one more. -/
noncomputable def cfgIMRCH (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIPRH (Nat.pow 2 (Nat.succ (lenR bl))) h

/-- The configuration of an evaluation in a tree over a frozen part, its window's lines named by the hint: `cfgIPRH`
with a set of as many bits as the box has cells and one more, for the cofactor. -/
noncomputable def cfgIFRH (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIPRH (Nat.pow 2 (Nat.succ (lenR bl))) h

section

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- **The resonant window's test of a box, its lines named by the hint**: at most `13` cells, each with
`1 ≤ lo ≤ hi ≤ DEN`, a rest `sr` with at least one cell, and `SieveResTest.resXH` on the rest's lower ends and the
sum of its upper ends, led by the hint's `k` intervals' records `h` (`k = 0`: the test with the large values of the
powers). -/
noncomputable def chkIRH (bl : List Cell) (sr k h : ℕ) : Bool :=
  rpass bl sr fun los hs ns ok n =>
    Nat.ble n 13 && ok && Nat.blt 0 ns && SieveResTest.resXH Lnum Lden los hs k h

/-- **The resonant window's test of a box with its cofactor, its lines named by the hint**: `chkIRH`, and when the
bit of `sr` after the box's cells is set, the cofactor in the rest after the box's primes, one part: when the box's
upper ends sum to at most `DEN − 2`, in the cell `(max(DEN − Σhi − 1, lo₀), DEN − Σlo + 1)`. -/
noncomputable def chkIRCH (bl : List Cell) (sr k h : ℕ) : Bool :=
  rpass bl sr fun los hs ns ok n =>
    Nat.ble n 13 && ok && Nat.blt 0 ns &&
      cond (Nat.beq (Nat.land (Nat.shiftRight sr n) 1) 1)
        (Nat.ble (Nat.add (hiSum bl) 2) DEN &&
          SieveResTest.resXHF Lnum Lden (los ++ [maxN (Nat.sub (Nat.sub DEN (hiSum bl)) 1) (headLo bl)])
            (Nat.add hs (Nat.add (Nat.sub DEN (loSum bl)) 1)) k h)
        (SieveResTest.resXHF Lnum Lden los hs k h)

/-- The test of an evaluation of kind `3` with the cofactor: `chkIRCH`. -/
noncomputable def okIRCH (bl : List Cell) (cfg : Cfg) : Bool :=
  chkIRCH bl cfg.sr (Nat.land cfg.s1 15) (Nat.div cfg.s1 16)

/-- **The tests with the resonant window, its lines named by the hint, and the cofactor**: `okIRCH` for an
evaluation of kind `3`, `fillTestsF`'s otherwise. -/
noncomputable def resTestsFCH : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 3) (okIRCH bl cfg) (fillTestsF.okI bl cfg), fillTestsF.okJ⟩

/-- **The resonant window's test of a box `ch ++ β` of a tree over a frozen part, with the chain's cofactor in the
rest** at the bit after the box's cells: with the slab `(x^{e₁/DEN}, x^{e₂/DEN}]`, when the chain's upper ends (the
box's less `β`'s) with `e₂` sum to at most `DEN − 2` and its lower ends with `e₁` and twice its least prime's reach
`DEN + 1`, every multiple's chain cofactor is one prime, in the cell
`(max(DEN − e₂ − Σhi − 1, lo₀), DEN − e₁ − Σlo + 1)`. Without the bit, `chkIRH`. -/
noncomputable def chkIRFH (e₁ e₂ : ℕ) (β bl : List Cell) (sr k h : ℕ) : Bool :=
  (fun slo shi =>
    rpass bl sr fun los hs ns ok n =>
      Nat.ble n 13 && ok && Nat.blt 0 ns &&
        cond (Nat.beq (Nat.land (Nat.shiftRight sr n) 1) 1)
          (Nat.ble (Nat.add (Nat.add e₂ shi) 2) DEN &&
            Nat.ble (Nat.add DEN 1) (Nat.add (Nat.add e₁ slo) (Nat.mul 2 (headLo bl))) &&
            SieveResTest.resXHF Lnum Lden (los ++ [maxN (Nat.sub (Nat.sub (Nat.sub DEN e₂) shi) 1) (headLo bl)])
              (Nat.add hs (Nat.add (Nat.sub (Nat.sub DEN e₁) slo) 1)) k h)
          (SieveResTest.resXHF Lnum Lden los hs k h))
    (Nat.sub (loSum bl) (loSum β)) (Nat.sub (hiSum bl) (hiSum β))

/-- The test of an evaluation of kind `3` in a tree over a frozen part: `chkIRFH` with the rest `sr` and the hint in
`s1`. -/
noncomputable def okIRFH (e₁ e₂ : ℕ) (β bl : List Cell) (cfg : Cfg) : Bool :=
  chkIRFH e₁ e₂ β bl cfg.sr (Nat.land cfg.s1 15) (Nat.div cfg.s1 16)

/-- **The tests of a tree over a frozen part, with the resonant window, its lines named by the hint**: `okIRFH` on
the box `ch ++ β` for an evaluation of kind `3`, `frozTestsC`'s otherwise. -/
noncomputable def frozResTestsCH (e₁ e₂ Kb : ℕ) (β : List Cell) (lsβ hsβ nb lomβ : ℕ) : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 3) (okIRFH e₁ e₂ β bl cfg)
      ((frozTestsC e₁ e₂ Kb β lsβ hsβ nb lomβ).okI bl cfg),
    (frozTestsC e₁ e₂ Kb β lsβ hsβ nb lomβ).okJ⟩

end

variable [SieveCert.IBPar]

/-- **The tree over the frozen part of a reversal, with the resonant window**: `flipTreeD` with the tests
`frozResTestsCH` and the configurations `cfgIFRH`. -/
noncomputable def flipTreeDRH (κ hR fuel : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
    (lsβ hsβ nb lim h : ℕ) : ℕ × ℕ :=
  (fun e₁ e₂ t Kb =>
    (fun τ cl ch =>
      (fun p =>
        cond (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c.1 t) && τ.okJ (c :: b) p.1.1 p.1.2)
          (kidsF κ hR ctx nb
            (solveD (opsKP ctx nb) τ cfgIFRH (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN)) (kidsF κ hR ctx nb)
              noAltH fuel)
            t (c :: b) (!pos) p.1.1 lim p.2)
          (lim, p.2))
        (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN) (c :: b) h))
      (frozResTestsCH e₁ e₂ Kb (c :: b) lsβ hsβ nb (lomP (c :: b) DEN)) (maxN 1 (Nat.sub e₁ hsβ))
      (Nat.sub e₂ lsβ))
    (cond pos (Nat.add (Nat.sub DEN ctx.2) 1) (Nat.sub DEN ctx.2))
    (cond pos (Nat.sub DEN ctx.1) (Nat.add (Nat.sub DEN ctx.1) 1)) (flipT ctx) (Nat.add 12 (Nat.div DEN c.1))

/-- `flipCostB` with the tree `flipTreeDRH`. -/
noncomputable def flipCostBRH (κ hR fuel maxlen : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
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
      (flipTreeDRH κ hR fuel pos ctx c b (Nat.add c.1 ls) (Nat.add c.2 hs) (Nat.succ n) CAPK h))
    (lim, h)

/-- `flipCostD` with the tree `flipTreeDRH`. -/
noncomputable def flipCostDRH (κ hR fuel maxlen : ℕ) (pos : Bool) (bl : List Cell) (lim h : ℕ) : ℕ × ℕ :=
  (fun ctx =>
    List.casesOn (motive := fun _ => ℕ × ℕ) (initP bl) (lim, h) fun c b =>
      tailP b 0 0 1 (cellI c) 0 c.2 fun ls hs tp ok n lh =>
        flipCostBRH κ hR fuel maxlen pos ctx c b ls hs tp ok n lh lim h)
    (lastP bl (0, 0))

/-- **The bound that reads hints, with the resonant window over the frozen parts**: `altFD` with `flipCostDRH`. -/
noncomputable def altFDRH (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ) : ℕ × ℕ :=
  flipCostDRH κ hR fuel maxlen par bl l h

end SieveAd
