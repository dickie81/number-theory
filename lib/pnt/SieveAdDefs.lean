/-
# A tree of Buchstab steps on boxes of cells, without Mathlib

The certificate of a sieve whose decomposition is chosen term by term. A **box** is a list of cells, one for each
prime of a term `Σ S(A_{p₁⋯p_k}, p_k)`, the newest prime first; a cell `(lo, hi)` is the range `[lo, hi)` of the
prime's exponent `log p/log x`, in units of `1/DEN`. A **tree** (`Tree`) says what is done with the term over a box:

* `vanish`: nothing, for a box that has no term (`vanishOK`: the product of its primes is below `x`, and times the
  last prime it is above `2x`);
* `drop`: the term is dropped, for one that enters the sieve with the sign `+`, at the cost of its count in the
  comparison set (`dropOK`, `dropCost`: the bound of `SieveRough.shareBox`, in units of `1/K`);
* `dropB`: the same for a box of two primes at least whose only terms are the products `n = p₁⋯p_k` themselves
  (`dropBOK`: the product times the last prime is above `2x`, and the product of the primes but the last is below
  `x`), at a bound for their number (`dropBCost`): the last prime is then a prime of `(x/r', 2x/r']`;
* `evalI cfg`: the term is evaluated by a test `okI` on the box;
* `split t c l r`: the box is cut at the exponent `c` of the prime at position `t`, into the boxes of `l` (below
  `c`) and of `r`;
* `buch f cfg ch`: Buchstab's identity with the floor `x^{f/DEN}`, at most the least exponent of the last prime:
  `Σ S(A_r, p_k) = Σ S(A_r, x^{f/DEN}) − Σ S(A_{rp}, p)` over the primes `p ∈ [x^{f/DEN}, p_k)`. The first sum is
  evaluated by a test `okJ` on the box and the floor; the second is the term of the box with the cell
  `(f, hi_k)` for the new prime, treated by `ch`, with the opposite sign.

`ok` checks a tree on a box, and `cost` adds the costs of the dropped boxes. The tests of the evaluations are a
parameter (`Tests`); a configuration (`Cfg`) carries what a test needs beyond the box, as sets of positions in
binary.

These are arithmetic on natural numbers, lists and booleans, with the tests by `Nat.ble` and `Nat.blt`, and the
file imports only `SieveCertDefs.lean`, so a file that imports no more than this one runs its kernel checks without
`Mathlib`. `SieveAdTree.lean` proves what a tree that passes `ok` gives.
-/
import SieveCertDefs

namespace SieveAd

open SieveCert (DEN K omKw cdiv)

/-- A cell: the range `[lo, hi)` of a prime's exponent, in units of `1/DEN`. -/
abbrev Cell := ℕ × ℕ

/-- What a test of an evaluation takes beyond the box: its kind, three sets of positions in binary, and a flag. -/
structure Cfg where
  kind : ℕ
  s0 : ℕ
  sr : ℕ
  s1 : ℕ
  e : Bool

/-- The tests of the evaluations: of the term over a box, and of its terms at a floor. -/
structure Tests where
  /-- The term `Σ S(A_r, p_last)` over the box is evaluated. -/
  okI : List Cell → Cfg → Bool
  /-- The terms `Σ S(A_r, x^{f/DEN})` over the box are evaluated. -/
  okJ : List Cell → ℕ → Cfg → Bool

/-- What is done with the term over a box. -/
inductive Tree where
  | vanish : Tree
  | drop : Tree
  | dropB : Tree
  | evalI : Cfg → Tree
  | split : ℕ → ℕ → Tree → Tree → Tree
  | buch : ℕ → Cfg → Tree → Tree

/-! ### Boxes -/

/-- The sum of the cells' lower ends. -/
def loSum : List Cell → ℕ
  | [] => 0
  | c :: b => c.1 + loSum b

/-- The sum of the cells' upper ends. -/
def hiSum : List Cell → ℕ
  | [] => 0
  | c :: b => c.2 + hiSum b

/-- Every cell has `0 < lo < hi`. -/
def cellsOK : List Cell → Bool
  | [] => true
  | c :: b => Nat.blt 0 c.1 && Nat.blt c.1 c.2 && cellsOK b

/-- The cell at position `t` (`(0, 0)` beyond the box). -/
def getC (b : List Cell) (t : ℕ) : Cell := b.getD t (0, 0)

/-- The box with the upper end of the cell at position `t` set to `c`. -/
def setHi (b : List Cell) (t c : ℕ) : List Cell := b.set t ((getC b t).1, c)

/-- The box with the lower end of the cell at position `t` set to `c`. -/
def setLo (b : List Cell) (t c : ℕ) : List Cell := b.set t (c, (getC b t).2)

/-! ### The tests of the nodes that need no estimate -/

/-- The box has no term: the product of its primes is at most `x^{(DEN−1)/DEN}`, and the product times the last
prime is at least `x^{(DEN+1)/DEN}`. -/
def vanishOK : List Cell → Bool
  | [] => false
  | c :: b => Nat.ble (c.2 + hiSum b + 1) DEN && Nat.ble (DEN + 1) (c.1 + loSum b + c.1)

/-- The box may be dropped: its cells have `0 < lo < hi`, and the product of its primes is below `x`. -/
def dropOK : List Cell → Bool
  | [] => false
  | c :: b => cellsOK (c :: b) && Nat.ble (c.2 + hiSum b) DEN

/-- The box has two primes at least and no term with a cofactor: its cells have `0 < lo < hi`, the product of its
primes times the last is at least `x^{(DEN+1)/DEN}`, and the product of the primes but the last is below `x`. -/
def dropBOK : List Cell → Bool
  | [] => false
  | c :: b =>
    Nat.blt 0 b.length && cellsOK (c :: b) && Nat.ble (DEN + 1) (c.1 + loSum b + c.1) && Nat.blt (hiSum b) DEN

/-- A cut of the cell at position `t`, strictly inside it. -/
def splitOK (b : List Cell) (t c : ℕ) : Bool :=
  Nat.blt t b.length && Nat.blt (getC b t).1 c && Nat.blt c (getC b t).2

/-! ### The cost of a dropped box -/

/-- The fixed point's scale for the factors of the primes. -/
def SC : ℕ := 2 ^ 64

/-- `⌈SC·w(2a + w)/(2a(a + w))⌉`, `SC` times the trapezoid bound of `Σ 1/p` over the cell `[a, a + w)`. -/
def trF (a w : ℕ) : ℕ := cdiv (SC * (w * (2 * a + w))) (2 * a * (a + w))

/-- `⌈SC·w·DEN/(a(a + w))⌉`, `SC` times the bound of the last cell's `log x · Σ 1/(p log p)`. -/
def exF (a w : ℕ) : ℕ := cdiv (SC * (DEN * w)) (a * (a + w))

/-- The product of `trF` over the cells. -/
def trProd : List Cell → ℕ
  | [] => 1
  | c :: b => trF c.1 (c.2 - c.1) * trProd b

/-- The cost of a dropped box, in units of `1/K`: the bound for Buchstab's `ω` on the box, times the factors of
its primes, rounded up. -/
def dropCost : List Cell → ℕ
  | [] => 0
  | c :: b =>
    cdiv (omKw (loSum b) c.1 (c.2 + hiSum b - (c.1 + loSum b)) (c.2 - c.1) * (exF c.1 (c.2 - c.1) * trProd b))
      (SC ^ (b.length + 1))

/-- The cost of a box dropped for its products alone, in units of `1/K`: the factors of the primes but the last,
over the least exponent `1 − Σ hi/DEN` of `x/r'`, rounded up. -/
def dropBCost : List Cell → ℕ
  | [] => 0
  | _ :: b => cdiv (K * DEN * trProd b) ((DEN - hiSum b) * SC ^ b.length)

/-! ### The check and the cost of a tree -/

/-- The tree is valid on the box; `par` says that the term enters the sieve with the sign `+`, so that it may be
dropped. -/
def ok (τ : Tests) : Tree → List Cell → Bool → Bool
  | .vanish, b, _ => vanishOK b
  | .drop, b, par => par && dropOK b
  | .dropB, b, par => par && dropBOK b
  | .evalI cfg, b, _ => Nat.blt 0 b.length && τ.okI b cfg
  | .split t c l r, b, par => splitOK b t c && ok τ l (setHi b t c) par && ok τ r (setLo b t c) par
  | .buch f cfg ch, b, par =>
    match b with
    | [] => false
    | x :: b' => Nat.blt 0 f && Nat.ble f x.1 && τ.okJ (x :: b') f cfg && ok τ ch ((f, x.2) :: x :: b') (!par)

/-- The cost of the tree on the box, in units of `1/K`: the costs of its dropped boxes. -/
def cost : Tree → List Cell → ℕ
  | .vanish, _ => 0
  | .drop, b => dropCost b
  | .dropB, b => dropBCost b
  | .evalI _, _ => 0
  | .split t c l r, b => cost l (setHi b t c) + cost r (setLo b t c)
  | .buch f _ ch, b =>
    match b with
    | [] => 0
    | x :: b' => cost ch ((f, x.2) :: x :: b')

end SieveAd
