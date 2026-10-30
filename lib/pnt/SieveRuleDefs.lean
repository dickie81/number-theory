/-
# The certificate's decomposition rule, without Mathlib

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

A **rule** (`Rule`) says which boxes of cells may be split and decomposed (`Rule.ok`, on a box given as the list of its
cells' ranges `(lo, hi)` in units of `1/DEN`). `allowedR` and `allowed4R` are the tests of a box at depths 2 and 4: the
box and the boxes of its counted cells one level deeper are `ok`. (The certificates of the earlier routes, which tested
`Σ hi < lim` in place of `Rule.ok`, are in the git history.)

* `limOK`: the box's upper sum is below `lim = DEN − U1`.
* `ibRule`: `limOK`, or the bilinear Type I rule `ibOK` with no boundary term (`nbOK`). For `L = Lnum/Lden`
  (`IBPar`), `ibOK` takes `tstar`, the least over the subsets `S` of the box whose upper sum is below `DEN − U1` of
  `cIB S`, the largest exponent at which a product `p_S·e` still enters the window `(U1, U2)` or its reflection
  `(DEN − U2, DEN − U1)` (from at or below `U1`, or from `[U2, DEN − U2]`), and asks for a split of the box's primes
  (a subset `S₁`, with `e` on its side or the other) with `a₁ < (1 − 1/L)DEN` and `a₁ + 2a₂ < DEN` at the upper ends
  (`leafIB`). `nbOK`: the box's upper sum plus its last cell's upper end is below `DEN`.

These are `tools/linnik/typeib_payoff.py`'s `ok`, `tstar`, `ib_leaf` and `ib` for the estimate `parseval`, with its
no-boundary test. They are arithmetic on natural numbers, lists and booleans, and the file imports only
`SieveCertDefs.lean`, so a part file that imports no more than this one runs its kernel checks without `Mathlib`.
-/
import SieveCertDefs

namespace SieveCert

/-- **A decomposition rule**: may the term over a box of cells (their ranges `(lo, hi)`) be split and decomposed. -/
class Rule where
  /-- The box may be split and decomposed. -/
  ok : List (ℕ × ℕ) → Bool

/-- The upper sum of a box. -/
def hiSum : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: rest => p.2 + hiSum rest

/-- The upper end of a box's last cell (`0` for no cell). -/
def lastHi : List (ℕ × ℕ) → ℕ
  | [] => 0
  | [p] => p.2
  | _ :: q :: rest => lastHi (q :: rest)

section Grid

variable [Grid]

/-- The certificate's own test: the box's upper sum is below `lim = DEN − U1`. -/
def limOK (xs : List (ℕ × ℕ)) : Bool := decide (hiSum xs < lim)

/-- No boundary term: the box's upper sum plus its last cell's upper end is below `DEN`. -/
def nbOK (xs : List (ℕ × ℕ)) : Bool := decide (hiSum xs + lastHi xs < DEN)

/-- The largest exponent of `e` at which `p_S·e`, `S` with sums `s = (lo, hi)`, still enters the window from at or
below `U1`, or its reflection from `[U2, DEN − U2]`. -/
def cIB (s : ℕ × ℕ) : ℕ := max (U1 - s.1) (if U2 ≤ s.2 then (DEN - U2) - max s.1 U2 else 0)

/-- `min a v`, or `v` for no `a`. -/
def optMin : Option ℕ → ℕ → ℕ
  | none, v => v
  | some a, v => min a v

/-- The least `cIB` over the subsets of the box whose upper sum is below `DEN − U1`; `none` if there is none. -/
def tstar (xs : List (ℕ × ℕ)) : Option ℕ :=
  (subsetSums xs).foldl (fun acc s => if s.2 < DEN - U1 then some (optMin acc (cIB s)) else acc) none

/-! ### The bilinear Type I rule -/

/-- The exponent `L = Lnum/Lden` of the bilinear Type I rule. -/
class IBPar where
  /-- The numerator of `L`. -/
  Lnum : ℕ
  /-- The denominator of `L`. -/
  Lden : ℕ

variable [IBPar]

/-- The estimate at `(a₁, a₂)`, in units of `1/DEN`: `a₁ < (1 − 1/L)DEN` and `a₁ + 2a₂ < DEN`. -/
def condIB (a₁ a₂ : ℕ) : Bool :=
  decide (a₁ * IBPar.Lnum < (IBPar.Lnum - IBPar.Lden) * DEN) && decide (a₁ + 2 * a₂ < DEN)

/-- Some split of the box's primes satisfies the estimate at the upper ends, with `e` of exponent `T` on one side. -/
def leafIB (xs : List (ℕ × ℕ)) (T : ℕ) : Bool :=
  (subsetSums xs).any (fun s => condIB (s.2 + T) (hiSum xs - s.2) || condIB s.2 (hiSum xs - s.2 + T))

/-- **The bilinear Type I test**: some subset stops every point of the box, and a split of its leaves satisfies the
estimate at the upper ends. -/
def ibOK (xs : List (ℕ × ℕ)) : Bool :=
  match tstar xs with
  | none => false
  | some T => leafIB xs T

/-- `limOK`, or `ibOK` with no boundary term. -/
def okIB (xs : List (ℕ × ℕ)) : Bool := limOK xs || (ibOK xs && nbOK xs)

/-- **The bilinear Type I rule**, `okIB`. -/
@[instance_reducible] def ibRule : Rule := ⟨okIB⟩

end Grid

/-! ### The certificate under a rule -/

section Cert

variable [Grid] [Rule]

/-- The rule's `allowed`: the box `(i, j)` and the boxes `(i, j, k)` of the counted rows are `ok`. -/
def allowedR (i j : ℕ) : Bool :=
  Rule.ok [cell i, cell j] &&
    (List.range n).all (fun k => !(inKK i j k && ne3 i j k) || Rule.ok [cell i, cell j, cell k])

/-- The rule's `allowed4`: the box `(i, j, k, l)` and the boxes of its counted cells of depth 5 are `ok`. -/
def allowed4R (i j k l : ℕ) : Bool :=
  Rule.ok [cell i, cell j, cell k, cell l] &&
    (List.range nC).all (fun b => !(inKK5 i j k l b && ne5 i j k l b) ||
      Rule.ok [cell i, cell j, cell k, cell l, cellC b])

end Cert

end SieveCert
