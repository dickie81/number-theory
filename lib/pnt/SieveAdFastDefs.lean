/-
# The tests of the trees in one pass over the box, without Mathlib

The tests of `SieveAdTwoDefs.lean`, `SieveAdFillDefs.lean` and `SieveAdFrozDefs.lean` read a box through sums of
the ends of its cells over sets of its primes, each sum a traversal of the list by structural recursion, with the
arithmetic of the type classes. The kernel spends two to five milliseconds on one of them, most of it on those
traversals. Here the same tests are computed in one pass over the box by the recursor of lists, with no branch
inside the pass: a sum over a set is `Σ (bit of the set)·(end of the cell)`, and the check `f ≤ lo ≤ hi ≤ DEN` of
the cells is a sum of deviations compared with its least value. The kernel takes a tenth of a millisecond.
`SieveAdFast.lean` proves that they are the same functions.

* `bpass f bl j m0 mr m1 … k`: one pass. For the sets of bits `m0`, `mr`, `m1`: the sums of the lower and upper
  ends over them among the first `j` cells, the sums of all the lower and upper ends of the first `j` cells, the
  sum over all the cells of `(lo − f) + (hi − lo) + (DEN − hi)`, and the number of cells, passed to `k`.
* `cellsP f e n`: the cells' check from that sum `e` and their number `n`.
* `uOfP`, `vOfP`, `coreI2P`, `coreJ2P`, `coreJ3P`: `uOf`, `vOf` and the checks on numbers, with the arithmetic of
  `ℕ` written out.
* `okI2F`, `okJ2F`, `okJ3F`, `fillTestsF`: the tests with no window.
* `lenR`: the length of a list, by the recursor. `okIFF`, `okJF3F`, `okJF2F`, `frozTestsF`: the tests of the tree
  over a frozen part, in a pass over the box and one over the frozen primes.

The file imports `SieveAdFrozDefs.lean`.
-/
import SieveAdFrozDefs

namespace SieveAd

open SieveCert (DEN cdiv)

/-- **One pass over a box**, by the recursor of lists. With `j` the number of cells that the sums take, from the
front, and `m0`, `mr`, `m1` three sets of bits: `k` is given the sums of the lower and of the upper ends over
each set, the sums of all the lower and of all the upper ends, among those first cells, added to the values they
start from; and, over all the cells, the sum of `(lo − f) + (hi − lo) + (DEN − hi)` and the number of cells. -/
noncomputable def bpass (f : ℕ) : List Cell → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ →
    (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → Bool :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ →
      (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → Bool)
    (fun _ _ _ _ a0 b0 ar br a1 b1 aT bT e n k => k a0 b0 ar br a1 b1 aT bT e n)
    (fun x _ ih j m0 mr m1 a0 b0 ar br a1 b1 aT bT e n k =>
      ih (Nat.sub j 1) (Nat.div m0 2) (Nat.div mr 2) (Nat.div m1 2)
        (Nat.add a0 (Nat.mul (Nat.mul (Nat.sub 1 (Nat.sub 1 j)) (Nat.land m0 1)) x.1))
        (Nat.add b0 (Nat.mul (Nat.mul (Nat.sub 1 (Nat.sub 1 j)) (Nat.land m0 1)) x.2))
        (Nat.add ar (Nat.mul (Nat.mul (Nat.sub 1 (Nat.sub 1 j)) (Nat.land mr 1)) x.1))
        (Nat.add br (Nat.mul (Nat.mul (Nat.sub 1 (Nat.sub 1 j)) (Nat.land mr 1)) x.2))
        (Nat.add a1 (Nat.mul (Nat.mul (Nat.sub 1 (Nat.sub 1 j)) (Nat.land m1 1)) x.1))
        (Nat.add b1 (Nat.mul (Nat.mul (Nat.sub 1 (Nat.sub 1 j)) (Nat.land m1 1)) x.2))
        (Nat.add aT (Nat.mul (Nat.sub 1 (Nat.sub 1 j)) x.1))
        (Nat.add bT (Nat.mul (Nat.sub 1 (Nat.sub 1 j)) x.2))
        (Nat.add e (Nat.add (Nat.add (Nat.sub x.1 f) (Nat.sub x.2 x.1)) (Nat.sub DEN x.2)))
        (Nat.succ n) k)

/-- The cells' check `f ≤ lo ≤ hi ≤ DEN`, from the sum `e` of `(lo − f) + (hi − lo) + (DEN − hi)` over the `n`
cells: each term is at least `DEN − f` when `f ≤ DEN`, with equality for the cells that pass. -/
def cellsP (f e n : ℕ) : Bool :=
  (Nat.beq n 0 || Nat.ble f DEN) && Nat.beq e (Nat.mul n (Nat.sub DEN f))

/-- The length of a list, by the recursor. -/
noncomputable def lenR : List Cell → ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih)

variable [SieveCert.IBPar]

open SieveCert.IBPar (Lnum Lden)

/-- `uOf`, with the arithmetic of `ℕ` written out. -/
def uOfP (ρ₁ : ℕ) : ℕ :=
  (fun A B => cond (Nat.ble A B) B A)
    (Nat.div (Nat.sub (Nat.add (Nat.mul (Nat.mul 2 Lden) DEN) (Nat.mul 3 Lnum)) 1) (Nat.mul 3 Lnum))
    (Nat.div
      (Nat.sub
        (Nat.add
          (Nat.sub (Nat.add (Nat.mul (Nat.mul 62505 Lden) DEN) (Nat.mul 27637 Lnum)) (Nat.mul (Nat.mul 27637 Lnum) ρ₁))
          (Nat.mul 62500 Lnum)) 1)
      (Nat.mul 62500 Lnum))

/-- `vOf`, with the arithmetic of `ℕ` written out. -/
def vOfP (ρ₂ : ℕ) : ℕ :=
  (fun A B => cond (Nat.ble A B) A B)
    (Nat.sub (Nat.div (Nat.sub (Nat.mul (Nat.mul 3 Lnum) DEN) (Nat.mul (Nat.mul 2 Lden) DEN)) (Nat.mul 3 Lnum))
      (Nat.add ρ₂ 1))
    (Nat.div
      (Nat.sub (Nat.sub (Nat.mul (Nat.mul 62500 Lnum) DEN) (Nat.mul (Nat.mul 62505 Lden) DEN))
        (Nat.mul (Nat.mul 34863 Lnum) (Nat.add ρ₂ 1)))
      (Nat.mul 62500 Lnum))

/-- `coreI2`, with the arithmetic of `ℕ` written out. -/
def coreI2P (u v ρ₁ ρ₂ : ℕ) : Bool :=
  Nat.ble (Nat.add (Nat.mul Lden DEN) (Nat.mul 2000 Lnum)) (Nat.mul (Nat.mul 2000 Lnum) ρ₁) &&
    Nat.ble (Nat.add (Nat.mul (Nat.mul 2 Lden) DEN) (Nat.mul 3 Lnum)) (Nat.mul (Nat.mul 3 Lnum) u) &&
    Nat.ble (Nat.add (Nat.mul (Nat.mul 2 Lden) DEN) (Nat.mul (Nat.mul 3 Lnum) (Nat.add (Nat.add ρ₂ 1) v)))
      (Nat.mul (Nat.mul 3 Lnum) DEN) &&
    Nat.ble (Nat.add (Nat.mul (Nat.mul 62505 Lden) DEN) (Nat.mul 90137 Lnum))
      (Nat.add (Nat.mul (Nat.mul 62500 Lnum) u) (Nat.mul (Nat.mul 27637 Lnum) ρ₁)) &&
    Nat.ble
      (Nat.add (Nat.add (Nat.mul (Nat.mul 62505 Lden) DEN) (Nat.mul (Nat.mul 62500 Lnum) v))
        (Nat.mul (Nat.mul 34863 Lnum) (Nat.add ρ₂ 1)))
      (Nat.mul (Nat.mul 62500 Lnum) DEN) &&
    Nat.ble (Nat.add (Nat.mul (Nat.mul 125005 Lden) DEN) (Nat.mul (Nat.mul 34863 Lnum) (Nat.add ρ₂ 1)))
      (Nat.mul (Nat.mul 62500 Lnum) DEN)

/-- The six inequalities of the region for a window `[u, v]` and rests of exponent in `[r₁ − 1, r₂ + 1]`, as the
comparisons at a floor ask them, with the arithmetic of `ℕ` written out. -/
def zoneJP (u v r1 r2 : ℕ) : Bool :=
  Nat.ble (Nat.add (Nat.mul Lden DEN) (Nat.mul 2000 Lnum)) (Nat.mul (Nat.mul 2000 Lnum) r1) &&
    Nat.ble (Nat.mul (Nat.mul 2 Lden) DEN) (Nat.mul (Nat.mul 3 Lnum) u) &&
    Nat.ble (Nat.add (Nat.mul (Nat.mul 2 Lden) DEN) (Nat.mul (Nat.mul 3 Lnum) (Nat.add (Nat.add r2 1) v)))
      (Nat.mul (Nat.mul 3 Lnum) DEN) &&
    Nat.ble (Nat.add (Nat.mul (Nat.mul 62505 Lden) DEN) (Nat.mul 27637 Lnum))
      (Nat.add (Nat.mul (Nat.mul 62500 Lnum) u) (Nat.mul (Nat.mul 27637 Lnum) r1)) &&
    Nat.ble
      (Nat.add (Nat.add (Nat.mul (Nat.mul 62505 Lden) DEN) (Nat.mul (Nat.mul 62500 Lnum) v))
        (Nat.mul (Nat.mul 34863 Lnum) (Nat.add r2 1)))
      (Nat.mul (Nat.mul 62500 Lnum) DEN) &&
    Nat.ble (Nat.add (Nat.mul (Nat.mul 125005 Lden) DEN) (Nat.mul (Nat.mul 34863 Lnum) (Nat.add r2 1)))
      (Nat.mul (Nat.mul 62500 Lnum) DEN)

/-- The three conditions on the leaves' sizes `D₁`, `D₂`, with the arithmetic of `ℕ` written out. -/
def leavesP (D₁ D₂ : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul Lnum D₁) (Nat.mul Lden DEN)) (Nat.mul Lnum DEN) &&
    Nat.blt (Nat.add (Nat.mul (Nat.mul 2 Lnum) (Nat.add D₁ D₂)) (Nat.mul Lden DEN)) (Nat.mul (Nat.mul 2 Lnum) DEN) &&
    Nat.blt (Nat.add (Nat.mul Lnum (Nat.add D₁ (Nat.mul 2 D₂))) (Nat.mul (Nat.mul 2 Lden) DEN))
      (Nat.mul (Nat.mul 2 Lnum) DEN)

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

/-! ### The tests with no window -/

/-- **`okI2` in one pass.** -/
noncomputable def okI2F (bl : List Cell) (cfg : Cfg) : Bool :=
  bpass 1 bl 13 cfg.s0 cfg.sr 0 0 0 0 0 0 0 0 0 0 0 fun u v ρ₁ ρ₂ _ _ _ _ e n =>
    Nat.ble n 13 && cellsP 1 e n && Nat.beq (Nat.land cfg.s0 cfg.sr) 0 && coreI2P u v ρ₁ ρ₂

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

/-! ### The tests of the tree over a frozen part -/

/-- The sums of the roles of a set of bits `m` over the chain, the frozen primes and the cofactor, passed to `k`:
`loR`, `hiR` and `hiRc`, from the chain's sums `a`, `b` (lower, upper) and `bT` (all the upper ends), the frozen
primes' sums `c`, `d` (lower, upper) and `cT`, `dT` (all of them), and whether the set has the cofactor. -/
def roleP (e₁ e₂ : ℕ) (cof : Bool) (a b bT c d cT dT : ℕ) (k : ℕ → ℕ → ℕ → Bool) : Bool :=
  k (Nat.add (cond cof (Nat.sub e₁ (Nat.sub dT d)) c) a) (Nat.add (cond cof (Nat.sub e₂ (Nat.sub cT c)) d) b)
    (Nat.add (cond cof (Nat.sub dT d) (Nat.sub e₂ c)) (Nat.sub bT b))

/-- Whether the set of bits `m` has the cofactor: the bit after the `nch` cells of the chain and the `nb` frozen
primes. -/
def cofP (m nch nb : ℕ) : Bool := Nat.beq (Nat.land (Nat.div (Nat.div m (Nat.pow 2 nch)) (Nat.pow 2 nb)) 1) 1

/-- **`okIF` in a pass over the box and one over the frozen primes.** -/
noncomputable def okIFF (e₁ e₂ : ℕ) (β bl : List Cell) (cfg : Cfg) : Bool :=
  (fun nb nch =>
    bpass 1 bl nch cfg.s0 cfg.sr 0 0 0 0 0 0 0 0 0 0 0 fun a0 b0 ar br _ _ _ bT e n =>
      bpass 0 β nb (Nat.div cfg.s0 (Nat.pow 2 nch)) (Nat.div cfg.sr (Nat.pow 2 nch)) 0 0 0 0 0 0 0 0 0 0 0
        fun c0 d0 cr dr _ _ cT dT _ _ =>
          roleP e₁ e₂ (cofP cfg.s0 nch nb) a0 b0 bT c0 d0 cT dT fun lo0 hi0 _ =>
            roleP e₁ e₂ (cofP cfg.sr nch nb) ar br bT cr dr cT dT fun lor hir _ =>
              cellsP 1 e n && Nat.beq (Nat.land cfg.s0 cfg.sr) 0 && Nat.blt 0 lor && coreI2P lo0 hi0 lor hir)
    (lenR β) (Nat.sub (lenR bl) (lenR β))

/-- **`okJF3` in a pass over the box and one over the frozen primes.** -/
noncomputable def okJF3F (e₁ e₂ Kb : ℕ) (β bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  (fun nb nch =>
    bpass f bl nch cfg.s0 0 cfg.s1 0 0 0 0 0 0 0 0 0 0 fun a0 b0 _ _ _ b1 _ bT e n =>
      bpass 0 β nb (Nat.div cfg.s0 (Nat.pow 2 nch)) 0 (Nat.div cfg.s1 (Nat.pow 2 nch)) 0 0 0 0 0 0 0 0 0 0
        fun c0 d0 _ _ c1 d1 cT dT _ _ =>
          roleP e₁ e₂ (cofP cfg.s0 nch nb) a0 b0 bT c0 d0 cT dT fun lo0 hi0 _ =>
            roleP e₁ e₂ (cofP cfg.s1 nch nb) 0 b1 bT c1 d1 cT dT fun _ hi1 hc1 =>
              Nat.blt 0 f && cellsP f e n &&
                coreJ3P f cfg.e (uOfP fillLo) (vOfP (Nat.add (Nat.add fillLo f) 1))
                  (Nat.sub (uOfP fillLo) (Nat.sub lo0 Kb)) fillLo (Nat.add (Nat.add fillLo f) 1) (Nat.sub lo0 Kb)
                  (Nat.add hi0 Kb) (Nat.add hi1 Kb) (Nat.add hc1 Kb))
    (lenR β) (Nat.sub (lenR bl) (lenR β))

/-- **`okJF2` in a pass over the box and one over the frozen primes.** -/
noncomputable def okJF2F (e₁ e₂ Kb : ℕ) (β bl : List Cell) (f : ℕ) (cfg : Cfg) : Bool :=
  (fun nb nch =>
    bpass f bl nch cfg.s0 cfg.sr cfg.s1 0 0 0 0 0 0 0 0 0 0 fun a0 b0 ar br _ b1 _ bT e n =>
      bpass 0 β nb (Nat.div cfg.s0 (Nat.pow 2 nch)) (Nat.div cfg.sr (Nat.pow 2 nch))
        (Nat.div cfg.s1 (Nat.pow 2 nch)) 0 0 0 0 0 0 0 0 0 0
        fun c0 d0 cr dr c1 d1 cT dT _ _ =>
          roleP e₁ e₂ (cofP cfg.s0 nch nb) a0 b0 bT c0 d0 cT dT fun lo0 hi0 _ =>
            roleP e₁ e₂ (cofP cfg.sr nch nb) ar br bT cr dr cT dT fun lor hir _ =>
              roleP e₁ e₂ (cofP cfg.s1 nch nb) 0 b1 bT c1 d1 cT dT fun _ hi1 hc1 =>
                Nat.blt 0 f && cellsP f e n && Nat.beq (Nat.land cfg.s0 cfg.sr) 0 && Nat.blt 0 lor &&
                  coreJ2P f cfg.e (uOfP (Nat.sub lor Kb)) (vOfP (Nat.add hir Kb))
                    (Nat.sub (uOfP (Nat.sub lor Kb)) (Nat.sub lo0 Kb)) (Nat.sub lor Kb) (Nat.add hir Kb)
                    (Nat.sub lo0 Kb) (Nat.add hi0 Kb) (Nat.add hi1 Kb) (Nat.add hc1 Kb))
    (lenR β) (Nat.sub (lenR bl) (lenR β))

/-- **The tests of the tree over the frozen part, in two passes.** -/
noncomputable def frozTestsF (e₁ e₂ Kb : ℕ) (β : List Cell) : Tests :=
  ⟨okIFF e₁ e₂ β,
    fun bl f cfg => cond (Nat.beq cfg.kind 2) (okJF3F e₁ e₂ Kb β bl f cfg) (okJF2F e₁ e₂ Kb β bl f cfg)⟩

end SieveAd
