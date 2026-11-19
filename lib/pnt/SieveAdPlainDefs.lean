/-
# The tests, the reversal and its tree with the paper's conditions on the leaves alone, without Mathlib

The tests of a comparison at a floor (`SieveAdTwoDefs.lean`'s `chkJ2`, `SieveAdFillDefs.lean`'s `chkJ3`,
`SieveAdCoreDefs.lean`'s `coreJ2` and `coreJ3`, and `SieveAdFastDefs.lean`'s forms in one pass) accept the leaves by
the paper's conditions or cut in three (`SieveAdLeafDefs.lean`'s `leavesL`, `leavesE`). Here are those definitions,
and the ones that are built on them, as they stood at commit `40411d7`, before the leaves could be cut in three: with
the paper's conditions alone, in the namespace `SieveAd.Plain`. A definition that is not repeated here is the
library's own (`SieveAd.okI2`, `SieveAd.uOf`, `SieveAd.solveD`, ...), which does not read the leaves' test.

The definitions: `chkJ2`, `okJ2`, `chkJ3`, `okJ3`, `fillTests`, `coreJ3`, `coreJ2`, `okJF3`, `okJF2`, `frozTests`,
`coreJ3P`, `coreJ2P`, `okJ2F`, `okJ3F`, `fillTestsF`, `okJF3C`, `okJF2C`, `frozTestsC`, `flipTreeD`, `flipCostB`,
`flipCostD`, `altFD`.

They are the tests, the reversal and the tree over a frozen part of the search led by hints at `2150/1000`
(`SieveAd.solve21500`, `SieveHint21500.lean`), whose soundness (`SieveAdPlainDir.lean`) does not rest on the leaves
cut in three. The file imports `SieveAdDirDefs.lean`; so neither it nor the part files of that search load more of
`Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import SieveAdDirDefs

namespace SieveAd.Plain

open SieveCert (DEN K cdiv topK w1K LD)

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-! ### From `SieveAdTwoDefs.lean` -/

/-- The checks of the comparison in two variables on a box, at the floor `f`, for the sets `s0`, `sr`, `s1`, the
flag `e`, the window `[u, v]` and the growth `t`. -/
def chkJ2 (bl : List Cell) (f s0 sr s1 : ℕ) (e : Bool) (u v t : ℕ) : Bool :=
  let ρ₁ := mSum (fun c => c.1) bl sr
  let ρ₂ := mSum (fun c => c.2) bl sr
  let D₁ := mSum (fun c => c.2) bl s1 + cond e t 0
  let D₂ := hiSum bl - mSum (fun c => c.2) bl s1 + cond e 0 t
  Nat.blt 0 f && Nat.ble bl.length 13 && cellsFrom f bl && Nat.beq (Nat.land s0 sr) 0 &&
    Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * ρ₁) &&
    Nat.ble (2 * Lden * DEN) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (ρ₂ + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 27637 * Lnum) (62500 * Lnum * u + 27637 * Lnum * ρ₁) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.blt (u + f) v &&
    Nat.ble u (t + mSum (fun c => c.1) bl s0) &&
    Nat.blt (mSum (fun c => c.2) bl s0) v &&
    Nat.blt (Lnum * D₁ + Lden * DEN) (Lnum * DEN) &&
    Nat.blt (2 * Lnum * (D₁ + D₂) + Lden * DEN) (2 * Lnum * DEN) &&
    Nat.blt (Lnum * (D₁ + 2 * D₂) + 2 * Lden * DEN) (2 * Lnum * DEN)

/-- **The test of the comparison in two variables**: `chkJ2` at the window and the growth that the box gives. -/
def okJ2 (bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  let u := uOf (mSum (fun c => c.1) bl cfg.sr)
  let v := vOf (mSum (fun c => c.2) bl cfg.sr)
  chkJ2 bl f cfg.s0 cfg.sr cfg.s1 cfg.e u v (u - mSum (fun c => c.1) bl cfg.s0)

/-! ### From `SieveAdFillDefs.lean` -/

/-- The checks of the comparison in two variables with the rest among the tree's primes, on a box at the floor
`f`, for the sets `s0`, `s1`, the flag `e`, the window `[u, v]`, the growth `t` and the rests of exponent in
`[r₁ − 1, r₂ + 1]`. -/
def chkJ3 (bl : List Cell) (f s0 s1 : ℕ) (e : Bool) (u v t r1 r2 : ℕ) : Bool :=
  let D₁ := mSum (fun c => c.2) bl s1 + cond e (t + r2) 0
  let D₂ := hiSum bl - mSum (fun c => c.2) bl s1 + cond e 0 (t + r2)
  Nat.blt 0 f && Nat.ble bl.length 13 && cellsFrom f bl &&
    Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * r1) &&
    Nat.ble (2 * Lden * DEN) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (r2 + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 27637 * Lnum) (62500 * Lnum * u + 27637 * Lnum * r1) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (r2 + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (r2 + 1)) (62500 * Lnum * DEN) &&
    Nat.blt (r1 + f) r2 &&
    Nat.blt (u + f) v &&
    Nat.ble u (t + mSum (fun c => c.1) bl s0) &&
    Nat.blt (mSum (fun c => c.2) bl s0) v &&
    Nat.blt (Lnum * D₁ + Lden * DEN) (Lnum * DEN) &&
    Nat.blt (2 * Lnum * (D₁ + D₂) + Lden * DEN) (2 * Lnum * DEN) &&
    Nat.blt (Lnum * (D₁ + 2 * D₂) + 2 * Lden * DEN) (2 * Lnum * DEN)

/-- **The test of the comparison with the rest among the tree's primes**: `chkJ3` at the rests, the window and the
growth that the box and the floor give. -/
def okJ3 (bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  let u := uOf fillLo
  let v := vOf (fillLo + f + 1)
  chkJ3 bl f cfg.s0 cfg.s1 cfg.e u v (u - mSum (fun c => c.1) bl cfg.s0) fillLo (fillLo + f + 1)

/-- **The tests with no window**: the estimate in two variables for a box; at a floor, the comparison with the
rest among the tree's primes for the configurations of kind `2`, and among the box's for the others. -/
def fillTests : Tests :=
  ⟨okI2, fun bl f cfg => cond (Nat.beq cfg.kind 2) (okJ3 bl f cfg) (okJ2 bl f cfg)⟩

/-! ### From `SieveAdCoreDefs.lean` -/

/-- The checks of the comparison in two variables with the rest among the tree's primes at the floor `f`, on the
sums of a box: `c0lo` at most the sum of the lower ends over the set that enters the window and `c0hi` at least
that of the upper ends, `h1s` at least the sum of the upper ends over the first side of the leaves and `h2s` at
least that over the other primes; the flag `e`, the window `[u, v]`, the growth `t` and the rests of exponent in
`[r₁ − 1, r₂ + 1]`. -/
def coreJ3 (f : ℕ) (e : Bool) (u v t r1 r2 c0lo c0hi h1s h2s : ℕ) : Bool :=
  let D₁ := h1s + cond e (t + r2) 0
  let D₂ := h2s + cond e 0 (t + r2)
  Nat.blt 0 f &&
    Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * r1) &&
    Nat.ble (2 * Lden * DEN) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (r2 + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 27637 * Lnum) (62500 * Lnum * u + 27637 * Lnum * r1) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (r2 + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (r2 + 1)) (62500 * Lnum * DEN) &&
    Nat.blt (r1 + f) r2 &&
    Nat.blt (u + f) v &&
    Nat.ble u (t + c0lo) &&
    Nat.blt c0hi v &&
    Nat.blt (Lnum * D₁ + Lden * DEN) (Lnum * DEN) &&
    Nat.blt (2 * Lnum * (D₁ + D₂) + Lden * DEN) (2 * Lnum * DEN) &&
    Nat.blt (Lnum * (D₁ + 2 * D₂) + 2 * Lden * DEN) (2 * Lnum * DEN)

/-- The checks of the comparison in two variables at the floor `f`, on the sums of a box: the rest's exponent in
`[ρ₁ − 1, ρ₂ + 1]`, `ρ₁` at most the sum of the lower ends over the rest's set and `ρ₂` at least that of the upper
ends; `c0lo`, `c0hi`, `h1s`, `h2s` as for `coreJ3`; the flag `e`, the window `[u, v]` and the growth `t`. -/
def coreJ2 (f : ℕ) (e : Bool) (u v t ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ) : Bool :=
  let D₁ := h1s + cond e t 0
  let D₂ := h2s + cond e 0 t
  Nat.blt 0 f &&
    Nat.ble (Lden * DEN + 2000 * Lnum) (2000 * Lnum * ρ₁) &&
    Nat.ble (2 * Lden * DEN) (3 * Lnum * u) &&
    Nat.ble (2 * Lden * DEN + 3 * Lnum * (ρ₂ + 1 + v)) (3 * Lnum * DEN) &&
    Nat.ble (62505 * Lden * DEN + 27637 * Lnum) (62500 * Lnum * u + 27637 * Lnum * ρ₁) &&
    Nat.ble (62505 * Lden * DEN + 62500 * Lnum * v + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.ble (125005 * Lden * DEN + 34863 * Lnum * (ρ₂ + 1)) (62500 * Lnum * DEN) &&
    Nat.blt (u + f) v &&
    Nat.ble u (t + c0lo) &&
    Nat.blt c0hi v &&
    Nat.blt (Lnum * D₁ + Lden * DEN) (Lnum * DEN) &&
    Nat.blt (2 * Lnum * (D₁ + D₂) + Lden * DEN) (2 * Lnum * DEN) &&
    Nat.blt (Lnum * (D₁ + 2 * D₂) + 2 * Lden * DEN) (2 * Lnum * DEN)

/-! ### From `SieveAdFrozDefs.lean` -/

/-- **The test of the terms at a floor over the frozen part, with the rest among the tree's primes**: `coreJ3`
at the rests, the window and the growth that the floor gives, on the exponents of the sets `s0` and `s1` and of the
complement of `s1`, with `Kb` cells of room. -/
def okJF3 (e₁ e₂ Kb : ℕ) (β bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  Nat.blt 0 f && cellsFrom f bl &&
    coreJ3 f cfg.e (uOf fillLo) (vOf (fillLo + f + 1))
      (uOf fillLo - (loR e₁ β (chainOf β.length bl) cfg.s0 - Kb)) fillLo (fillLo + f + 1)
      (loR e₁ β (chainOf β.length bl) cfg.s0 - Kb) (hiR e₂ β (chainOf β.length bl) cfg.s0 + Kb)
      (hiR e₂ β (chainOf β.length bl) cfg.s1 + Kb) (hiRc e₂ β (chainOf β.length bl) cfg.s1 + Kb)

/-- **The test of the terms at a floor over the frozen part, with the rest among the tuple's primes**: `coreJ2`
at the window and the growth that the rest's set `sr` gives, with `Kb` cells of room. -/
def okJF2 (e₁ e₂ Kb : ℕ) (β bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  Nat.blt 0 f && cellsFrom f bl && Nat.beq (Nat.land cfg.s0 cfg.sr) 0 &&
    Nat.blt 0 (loR e₁ β (chainOf β.length bl) cfg.sr) &&
    coreJ2 f cfg.e (uOf (loR e₁ β (chainOf β.length bl) cfg.sr - Kb))
      (vOf (hiR e₂ β (chainOf β.length bl) cfg.sr + Kb))
      (uOf (loR e₁ β (chainOf β.length bl) cfg.sr - Kb) - (loR e₁ β (chainOf β.length bl) cfg.s0 - Kb))
      (loR e₁ β (chainOf β.length bl) cfg.sr - Kb) (hiR e₂ β (chainOf β.length bl) cfg.sr + Kb)
      (loR e₁ β (chainOf β.length bl) cfg.s0 - Kb) (hiR e₂ β (chainOf β.length bl) cfg.s0 + Kb)
      (hiR e₂ β (chainOf β.length bl) cfg.s1 + Kb) (hiRc e₂ β (chainOf β.length bl) cfg.s1 + Kb)

/-- **The tests of the tree over the frozen part**: the estimate in two variables for the term of a chain's box;
at a floor, the comparison with the rest among the tree's primes for the configurations of kind `2`, and among the
tuple's for the others. -/
def frozTests (e₁ e₂ Kb : ℕ) (β : List Cell) : Tests :=
  ⟨okIF e₁ e₂ β, fun bl f cfg => cond (Nat.beq cfg.kind 2) (okJF3 e₁ e₂ Kb β bl f cfg) (okJF2 e₁ e₂ Kb β bl f cfg)⟩

/-! ### From `SieveAdFastDefs.lean` -/

/-- `coreJ3` but for its first check `0 < f`: the checks of the comparison with the rest among the tree's primes
on numbers. -/
def coreJ3P (f : ℕ) (e : Bool) (u v t r1 r2 c0lo c0hi h1s h2s : ℕ) : Bool :=
  zoneJP u v r1 r2 && Nat.blt (Nat.add r1 f) r2 && Nat.blt (Nat.add u f) v && Nat.ble u (Nat.add t c0lo) &&
    Nat.blt c0hi v &&
    leavesP (Nat.add h1s (cond e (Nat.add t r2) 0)) (Nat.add h2s (cond e 0 (Nat.add t r2)))

/-- `coreJ2` but for its first check `0 < f`: the checks of the comparison with the rest among the box's primes on
numbers. -/
def coreJ2P (f : ℕ) (e : Bool) (u v t ρ₁ ρ₂ c0lo c0hi h1s h2s : ℕ) : Bool :=
  zoneJP u v ρ₁ ρ₂ && Nat.blt (Nat.add u f) v && Nat.ble u (Nat.add t c0lo) && Nat.blt c0hi v &&
    leavesP (Nat.add h1s (cond e t 0)) (Nat.add h2s (cond e 0 t))

/-- **`okJ2` in one pass.** -/
noncomputable def okJ2F (bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  bpass f bl 13 cfg.s0 cfg.sr cfg.s1 0 0 0 0 0 0 0 0 0 0 fun lo0 hi0 ρ₁ ρ₂ _ hi1 _ hiT e n =>
    Nat.blt 0 f && Nat.ble n 13 && cellsP f e n && Nat.beq (Nat.land cfg.s0 cfg.sr) 0 &&
      coreJ2P f cfg.e (uOfP ρ₁) (vOfP ρ₂) (Nat.sub (uOfP ρ₁) lo0) ρ₁ ρ₂ lo0 hi0 hi1 (Nat.sub hiT hi1)

/-- **`okJ3` in one pass.** -/
noncomputable def okJ3F (bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  bpass f bl 13 cfg.s0 0 cfg.s1 0 0 0 0 0 0 0 0 0 0 fun lo0 hi0 _ _ _ hi1 _ hiT e n =>
    Nat.blt 0 f && Nat.ble n 13 && cellsP f e n &&
      coreJ3P f cfg.e (uOfP fillLo) (vOfP (Nat.add (Nat.add fillLo f) 1)) (Nat.sub (uOfP fillLo) lo0) fillLo
        (Nat.add (Nat.add fillLo f) 1) lo0 hi0 hi1 (Nat.sub hiT hi1)

/-- **The tests with no window, each in one pass.** -/
noncomputable def fillTestsF : Tests :=
  ⟨okI2F, fun bl f cfg => cond (Nat.beq cfg.kind 2) (okJ3F bl f cfg) (okJ2F bl f cfg)⟩

/-- **`okJF3` with the frozen primes read once for each tree**; `lomβ` is at most their lower ends. -/
noncomputable def okJF3C (e₁ e₂ Kb : ℕ) (β : List Cell) (lsβ hsβ nb lomβ : ℕ) (bl : List Cell) (f : ℕ)
    (cfg : Cfg) : Bool :=
  (fun nch =>
    cpass f bl nch cfg.s0 0 cfg.s1 0 0 0 0 0 0 0 0 0 fun a0 b0 _ _ _ b1 bT e n =>
      canonN (Nat.div cfg.s0 (Nat.pow 2 nch)) fun m0 =>
        canonN (Nat.div cfg.s1 (Nat.pow 2 nch)) fun m1 =>
          (fun R0 R1 =>
            Nat.blt 0 f && cellsP f e n && Nat.ble f lomβ &&
              coreJ3P f cfg.e (uOfP fillLo) (vOfP (Nat.add (Nat.add fillLo f) 1))
                (Nat.sub (uOfP fillLo) (Nat.sub (Nat.add R0.1 a0) Kb)) fillLo (Nat.add (Nat.add fillLo f) 1)
                (Nat.sub (Nat.add R0.1 a0) Kb) (Nat.add (Nat.add R0.2.1 b0) Kb) (Nat.add (Nat.add R1.2.1 b1) Kb)
                (Nat.add (Nat.add R1.2.2 (Nat.sub bT b1)) Kb))
            (roleB e₁ e₂ β lsβ hsβ nb m0) (roleB e₁ e₂ β lsβ hsβ nb m1))
    (Nat.sub (lenR bl) nb)

/-- **`okJF2` with the frozen primes read once for each tree**; `lomβ` is at most their lower ends. -/
noncomputable def okJF2C (e₁ e₂ Kb : ℕ) (β : List Cell) (lsβ hsβ nb lomβ : ℕ) (bl : List Cell) (f : ℕ)
    (cfg : Cfg) : Bool :=
  (fun nch =>
    cpass f bl nch cfg.s0 cfg.sr cfg.s1 0 0 0 0 0 0 0 0 0 fun a0 b0 ar br _ b1 bT e n =>
      canonN (Nat.div cfg.s0 (Nat.pow 2 nch)) fun m0 =>
        canonN (Nat.div cfg.sr (Nat.pow 2 nch)) fun mr =>
          canonN (Nat.div cfg.s1 (Nat.pow 2 nch)) fun m1 =>
            (fun R0 Rr R1 =>
              Nat.blt 0 f && cellsP f e n && Nat.ble f lomβ && Nat.beq (Nat.land cfg.s0 cfg.sr) 0 &&
                Nat.blt 0 (Nat.add Rr.1 ar) &&
                coreJ2P f cfg.e (uOfP (Nat.sub (Nat.add Rr.1 ar) Kb)) (vOfP (Nat.add (Nat.add Rr.2.1 br) Kb))
                  (Nat.sub (uOfP (Nat.sub (Nat.add Rr.1 ar) Kb)) (Nat.sub (Nat.add R0.1 a0) Kb))
                  (Nat.sub (Nat.add Rr.1 ar) Kb) (Nat.add (Nat.add Rr.2.1 br) Kb) (Nat.sub (Nat.add R0.1 a0) Kb)
                  (Nat.add (Nat.add R0.2.1 b0) Kb) (Nat.add (Nat.add R1.2.1 b1) Kb)
                  (Nat.add (Nat.add R1.2.2 (Nat.sub bT b1)) Kb))
              (roleB e₁ e₂ β lsβ hsβ nb m0) (roleB e₁ e₂ β lsβ hsβ nb mr) (roleB e₁ e₂ β lsβ hsβ nb m1))
    (Nat.sub (lenR bl) nb)

/-- **The tests of the tree over the frozen part, the frozen primes read once for each tree.** -/
noncomputable def frozTestsC (e₁ e₂ Kb : ℕ) (β : List Cell) (lsβ hsβ nb lomβ : ℕ) : Tests :=
  ⟨okIFC e₁ e₂ β lsβ hsβ nb,
    fun bl f cfg =>
      cond (Nat.beq cfg.kind 2) (okJF3C e₁ e₂ Kb β lsβ hsβ nb lomβ bl f cfg)
        (okJF2C e₁ e₂ Kb β lsβ hsβ nb lomβ bl f cfg)⟩

/-! ### From `SieveAdDirDefs.lean` -/

/-- **The tree over the frozen part of a reversal**, searched by hints: the terms of the frozen part at the floor
and with the configuration read from the hints, and the cells of the chain's first prime by the hints after them.
The frozen primes `c :: b` have the sums `lsβ`, `hsβ` and the number `nb`; what the tests and the search read from
them is computed once for the tree (`frozTestsC`, `cfgJF`). For a box of the sign `−` (`pos = false`) the frozen
numbers are those of the slab of `ctx` and the chain's cells have the sign `+`; for a box of the sign `+` they are
those of the slab one unit narrower at each end, and the chain's cells have the sign `−`. -/
noncomputable def flipTreeD (κ hR fuel : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
    (lsβ hsβ nb lim h : ℕ) : ℕ × ℕ :=
  (fun e₁ e₂ t Kb =>
    (fun τ cl ch =>
      (fun p =>
        cond (Nat.blt 0 p.1.1 && Nat.ble p.1.1 (minN c.1 t) && τ.okJ (c :: b) p.1.1 p.1.2)
          (kidsF κ hR ctx nb
            (solveD (opsKP ctx nb) τ cfgIF (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN)) (kidsF κ hR ctx nb)
              noAltH fuel)
            t (c :: b) (!pos) p.1.1 lim p.2)
          (lim, p.2))
        (cfgJF Kb cl ch (c :: b) nb (lomP (c :: b) DEN) (c :: b) h))
      (frozTestsC e₁ e₂ Kb (c :: b) lsβ hsβ nb (lomP (c :: b) DEN)) (maxN 1 (Nat.sub e₁ hsβ)) (Nat.sub e₂ lsβ))
    (cond pos (Nat.add (Nat.sub DEN ctx.2) 1) (Nat.sub DEN ctx.2))
    (cond pos (Nat.sub DEN ctx.1) (Nat.add (Nat.sub DEN ctx.1) 1)) (flipT ctx) (Nat.add 12 (Nat.div DEN c.1))

/-- **The cost of the reversal of a box through its largest prime**, from the sums of the frozen primes after the
first, `c`: the test `flipOKP`, and the formula of `flipCost` on the cost of the tree, which is searched by hints
with the limit `CAPK`. For a box of the sign `+` the tree's cost weighs on the share of the box alone, and not on
the shares of the slab's two ends. -/
noncomputable def flipCostB (κ hR fuel maxlen : ℕ) (pos : Bool) (ctx c : Cell) (b : List Cell)
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
      (flipTreeD κ hR fuel pos ctx c b (Nat.add c.1 ls) (Nat.add c.2 hs) (Nat.succ n) CAPK h))
    (lim, h)

/-- **The cost of the reversal of a box through its largest prime, the tree over the frozen part searched by
hints**, for a box of the sign `−` (`pos = false`) or `+`: the box's last cell and the others by the recursor, and
the sums of the others in one pass. -/
noncomputable def flipCostD (κ hR fuel maxlen : ℕ) (pos : Bool) (bl : List Cell) (lim h : ℕ) : ℕ × ℕ :=
  (fun ctx =>
    List.casesOn (motive := fun _ => ℕ × ℕ) (initP bl) (lim, h) fun c b =>
      tailP b 0 0 1 (cellI c) 0 c.2 fun ls hs tp ok n lh =>
        flipCostB κ hR fuel maxlen pos ctx c b ls hs tp ok n lh lim h)
    (lastP bl (0, 0))

/-- **The bound that reads hints**: for a box that may be reversed through its largest prime, that reversal's
cost, with the box's sign. -/
noncomputable def altFD (κ hR fuel maxlen : ℕ) (bl : List Cell) (par : Bool) (l h : ℕ) : ℕ × ℕ :=
  flipCostD κ hR fuel maxlen par bl l h

end SieveAd.Plain
