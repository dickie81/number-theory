/-
# The resonant window's test of a box in the main tree, without Mathlib

The resonant window evaluates a box's term with one variable, the product of all but a rest of the box's primes,
the rest's primes in their cells (`SieveTypeIIHM.chain_res_exp`), where its condition `SieveTypeIIHM.ResBox` holds
on the rest's cells; `SieveResTest.resX` checks that condition, led by a hint (`resT`, or `resT2` with the large
values of the powers). This file is the kernel's side:

* `rpass bl m k`: one pass over the box by the recursor of lists: the lower ends of the cells at the set bits of `m`
  (in the list's order), the sum of their upper ends, how many they are, whether every cell has
  `1 ≤ lo ≤ hi ≤ DEN`, and the number of cells, passed to `k`.
* `chkIR bl sr k h`: **the resonant window's test of a box**: at most `13` cells, each from `1`, a rest `sr` with at
  least one cell, and `resX` on the rest, led by the hint's `k` intervals `h` (`k = 0`: `resT2`, its number of
  intervals in the low four bits of `h`).
* `okIR`, `resTestsF`: the test of an evaluation of kind `3`, its hint in `s1` (the intervals' number in the low
  four bits); with `fillTestsF`'s tests for the other kinds.
* `cfgIPR`, `cfgIMR`: the configuration of an evaluation from the hints: `0` and `cfgIP`'s code, or `1`, the rest
  (a set of `pw` values), four bits `k` and the test's `k` intervals' ends, thirteen bits each; or, for `k = 0`
  (`resT2`), four more bits `k₂` and `k₂` ends.
* `headLo`, `chkIRC`, `okIRC`, `resTestsFC`, `cfgIMRC`: the same with the box's cofactor in the rest, at the bit
  after the box's cells: when the box's upper ends sum to at most `DEN − 2` and its lower ends with twice its least
  prime's reach `DEN + 1`, every multiple's cofactor is one prime, in the cell
  `(max(DEN − Σhi − 1, lo₀), DEN − Σlo + 1)` (`lo₀` the least prime's lower end).

Its soundness is `SieveAdRes.lean`'s. The file imports `SieveAdDirDefs.lean` and `SieveResTestDefs.lean`.
-/
import SieveAdDirDefs
import SieveResTestDefs

namespace SieveAd

open SieveCert (DEN)

/-- **One pass over a box for the resonant window**: for the set of bits `m`, the lower ends of its cells in the
list's order, the sum of their upper ends, how many they are, whether every cell of the box has
`1 ≤ lo ≤ hi ≤ DEN`, and the number of cells. -/
noncomputable def rpass {α : Type} : List Cell → ℕ → (List ℕ → ℕ → ℕ → Bool → ℕ → α) → α :=
  List.rec (motive := fun _ => ℕ → (List ℕ → ℕ → ℕ → Bool → ℕ → α) → α) (fun _ k => k [] 0 0 true 0)
    (fun x _ ih m k =>
      ih (Nat.div m 2) fun los hs ns ok n =>
        k (cond (Nat.beq (Nat.land m 1) 1) (x.1 :: los) los) (Nat.add (Nat.mul (Nat.land m 1) x.2) hs)
          (Nat.add (Nat.land m 1) ns) (ok && Nat.ble 1 x.1 && Nat.ble x.1 x.2 && Nat.ble x.2 DEN) (Nat.succ n))

section

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- **The resonant window's test of a box**: at most `13` cells, each with `1 ≤ lo ≤ hi ≤ DEN`, a rest `sr` with at
least one cell, and `SieveResTest.resX` on the rest's lower ends and the sum of its upper ends, led by the hint's
`k` intervals `h` (`k = 0`: the test with the large values of the powers). -/
noncomputable def chkIR (bl : List Cell) (sr k h : ℕ) : Bool :=
  rpass bl sr fun los hs ns ok n =>
    Nat.ble n 13 && ok && Nat.blt 0 ns && SieveResTest.resX Lnum Lden los hs k h

/-- The test of an evaluation of kind `3`: the rest `sr`, and the hint's number of intervals in the low four bits of
`s1`, its records above. -/
noncomputable def okIR (bl : List Cell) (cfg : Cfg) : Bool :=
  chkIR bl cfg.sr (Nat.land cfg.s1 15) (Nat.div cfg.s1 16)

/-- **The tests with the resonant window**: `okIR` for an evaluation of kind `3`, `fillTestsF`'s otherwise. -/
noncomputable def resTestsF : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 3) (okIR bl cfg) (fillTestsF.okI bl cfg), fillTestsF.okJ⟩

end

/-- The configuration of an evaluation, from the hints: `0` and `cfgIP`'s code; or `1`, the rest (a set of `pw`
values), four bits `k`, and the resonant window's `k` intervals' ends in the next `13k` bits, as the configuration of
kind `3` with `k + 16·ends` in `s1`; for `k = 0`, the test with the large values of the powers: four more bits `k₂`
and `k₂` ends, with `16·(k₂ + 16·ends)` in `s1`. -/
noncomputable def cfgIPR (pw h : ℕ) : Cfg × ℕ :=
  Bool.rec (motive := fun _ => Cfg × ℕ) (cfgIP pw (Nat.div h 2))
    ((fun h1 =>
      (fun k h2 =>
        cond (Nat.beq k 0)
          ((fun k2 h3 =>
            (⟨3, 0, Nat.mod h1 pw,
                Nat.mul 16 (Nat.add k2 (Nat.mul 16 (Nat.mod h3 (Nat.pow 2 (Nat.mul 13 k2))))), false⟩,
              Nat.div h3 (Nat.pow 2 (Nat.mul 13 k2))))
            (Nat.mod h2 16) (Nat.div h2 16))
          (⟨3, 0, Nat.mod h1 pw, Nat.add k (Nat.mul 16 (Nat.mod h2 (Nat.pow 2 (Nat.mul 13 k)))), false⟩,
            Nat.div h2 (Nat.pow 2 (Nat.mul 13 k))))
        (Nat.mod (Nat.div h1 pw) 16) (Nat.div (Nat.div h1 pw) 16))
      (Nat.div h 2))
    (Nat.beq (Nat.land h 1) 1)

/-- **The configuration of an evaluation in the main tree, with the resonant window**, from the hints. -/
noncomputable def cfgIMR (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIPR (Nat.pow 2 (lenR bl)) h

/-- The lower end of a box's first cell, its least prime's (`0` for no cell). -/
def headLo : List Cell → ℕ
  | [] => 0
  | c :: _ => c.1

section

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- **The resonant window's test of a box, with its cofactor**: `chkIR`, and when the bit of `sr` after the box's
cells is set, the cofactor in the rest after the box's primes: when the box's upper ends sum to at most `DEN − 2`
and its lower ends with twice its least prime's reach `DEN + 1`, in the cell `(max(DEN − Σhi − 1, lo₀),
DEN − Σlo + 1)`. -/
noncomputable def chkIRC (bl : List Cell) (sr k h : ℕ) : Bool :=
  rpass bl sr fun los hs ns ok n =>
    Nat.ble n 13 && ok && Nat.blt 0 ns &&
      cond (Nat.beq (Nat.land (Nat.shiftRight sr n) 1) 1)
        (Nat.ble (Nat.add (hiSum bl) 2) DEN && Nat.ble (Nat.add DEN 1) (Nat.add (loSum bl) (Nat.mul 2 (headLo bl))) &&
          SieveResTest.resX Lnum Lden (los ++ [maxN (Nat.sub (Nat.sub DEN (hiSum bl)) 1) (headLo bl)])
            (Nat.add hs (Nat.add (Nat.sub DEN (loSum bl)) 1)) k h)
        (SieveResTest.resX Lnum Lden los hs k h)

/-- The test of an evaluation of kind `3` with the cofactor: `chkIRC`. -/
noncomputable def okIRC (bl : List Cell) (cfg : Cfg) : Bool :=
  chkIRC bl cfg.sr (Nat.land cfg.s1 15) (Nat.div cfg.s1 16)

/-- **The tests with the resonant window and the cofactor**: `okIRC` for an evaluation of kind `3`, `fillTestsF`'s
otherwise. -/
noncomputable def resTestsFC : Tests :=
  ⟨fun bl cfg => cond (Nat.beq cfg.kind 3) (okIRC bl cfg) (fillTestsF.okI bl cfg), fillTestsF.okJ⟩

end

/-- The configuration of an evaluation in the main tree with the cofactor's bit: `cfgIPR` with a set of as many bits
as the box has cells and one more. -/
noncomputable def cfgIMRC (bl : List Cell) (h : ℕ) : Cfg × ℕ := cfgIPR (Nat.pow 2 (Nat.succ (lenR bl))) h

end SieveAd
