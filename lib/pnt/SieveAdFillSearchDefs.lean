/-
# A strategy for the tests with no window, without Mathlib

`SieveAdRevDefs.lean`'s search proposes its nodes by a strategy (`SieveAd.Strat`). This one is for
`SieveAdFillDefs.lean`'s tests `fillTests`: it proposes no window, and for a box at a floor it proposes the
comparison with the rest among the tree's primes (`okJ3`) when that passes at a higher floor than the comparison
with the rest among the box's primes (`propJ2`).

* `fmax3`: the largest floor at which the window that `okJ3` computes is wider than the floor.
* `tryJ3`: at a floor, the set `s0` of the box's cells with the largest lower sum that stays below the window's
  upper end (`bestSub`), and a split of the leaves with the growth `t + r₂` (`leavesOf`).
* `propJ3`: the first of the floors `f₀ = min(lomin, fmax3)`, `3f₀/4`, `9f₀/16`, …, eight of them, that has such
  a split.
* `propJF`: the floors to try on a box; `stratGF`, `stratKF`: the strategies of the search and of the tree of a
  reversed term, `SieveAdRevDefs.lean`'s `stratG` and `stratK` with these proposals.

These are arithmetic on natural numbers, lists and booleans, and the file imports only `SieveAdRevDefs.lean` and
`SieveAdFillDefs.lean`.
-/
import SieveAdRevDefs
import SieveAdFillDefs

namespace SieveAd

open SieveCert (DEN cdiv)

variable [SieveCert.IBPar]

/-- The lower end of the window of `okJ3`. -/
def u3 : ℕ := uOfF restLo

/-- The largest floor `f` with `u3 + f < vOfF (restLo + f + 1)`. -/
def fmax3 : ℕ :=
  minN (Nat.div (Nat.sub vA (Nat.add (Nat.add restLo 3) u3)) 2)
    (Nat.div (Nat.sub vB (Nat.add (Nat.mul vC (Nat.add restLo 2)) (Nat.mul (Nat.succ u3) uC))) (Nat.add uC vC))

/-- The configuration of `okJ3` at the floor `f`, if the leaves have a split: the set `s0` with the largest lower
sum below the window's upper end, and the leaves' split for the growth `u3 − Σ_{s0} lo + r₂`. -/
def tryJ3 (bl : List Cell) (ls hs f : ℕ) : Option (ℕ × Cfg) :=
  (fun r2 =>
    (fun b =>
      match leavesOf bl hs (Nat.add (Nat.sub u3 b.1) r2) with
      | some sp => some (f, ⟨2, b.2, 0, sp.1, sp.2⟩)
      | none => none) (bestSub (vOfF r2) 0 bl 1 0 0 0 ls (0, 0))) (Nat.add restLo (Nat.succ f))

/-- A floor for the comparison with the rest among the tree's primes, with its configuration: the first of `f`,
`3f/4`, `9f/16`, …, `n` of them, at which the leaves have a split. -/
def propJ3 (bl : List Cell) (ls hs : ℕ) : ℕ → ℕ → Option (ℕ × Cfg)
  | 0, _ => none
  | n + 1, f =>
    match tryJ3 bl ls hs f with
    | some r => some r
    | none => propJ3 bl ls hs n (Nat.div (Nat.mul 3 f) 4)

/-- The floors to try: the comparison with the rest among the tree's primes, if its floor is above that of the
comparison with the rest among the box's; then the latter. -/
def propJF (bl : List Cell) : List (ℕ × Cfg) :=
  (fun lomin ls hs =>
    cond (Nat.blt T5 hs) []
      ((fun r =>
        (match cond (Nat.blt r.1 lomin) (propJ3 bl ls hs 8 (minN lomin fmax3)) none with
          | some r3 => cond (Nat.blt r.1 r3.1) [r3] []
          | none => []) ++
        (match r.2 with
          | some cfg => [(r.1, cfg)]
          | none => [])) (propJ2 bl lomin ls hs bl 1 (0, none))))
    (lominOf bl) (loSum bl) (hiSum bl)

/-- **A strategy for `fillTests`** with cells of side at most `hI` and at most the exponent over `κ`. -/
def stratGF (κ hI depth wmin : ℕ) : Strat :=
  ⟨depth, wmin, fun bl => propI2 bl (loSum bl) bl 1, propJF, cutsOfG κ hI⟩

/-- **A strategy for the tree of a reversed term** with `na` atoms, its chains of fewer than `depthR` primes, for
`fillTests`. -/
def stratKF (κ hR depthR wmin : ℕ) (ctx : Cell) (na : ℕ) : Strat :=
  ⟨depthR + na, wmin, fun bl => propI2 bl (loSum bl) bl 1, propJF,
    fun bl f =>
      (fun ch =>
        cutsK κ hR ctx ch
          (match ch with
            | [] => (getC bl 0).1
            | x :: _ => x.2) f) (chainOf na bl)⟩

end SieveAd
