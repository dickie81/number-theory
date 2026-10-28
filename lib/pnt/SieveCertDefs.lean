/-
# The certificate's definitions, without Mathlib

The definitions of the loss certificate of `SieveCert.lean`
 and of its class `GridOK`,
and `rows` (from the earlier `SieveCert232.lean`, removed; see the git history), moved here from those files: verbatim, except that `rows` takes the
section's `[Grid]` in place of its own binder and `GridOK`'s docstring is rewrapped and names `SieveCert.lean`. They are
arithmetic on natural numbers, lists and booleans, and the file imports only `Mathlib.Data.Nat.Notation` (the notation
`ℕ`), whose closure is `Mathlib.Init`'s: 1,339 modules, loaded in about 0.9 GiB, not the whole of Mathlib.
So a file that imports no more than this one, such as a certificate's part files (`SieveCert22250RP1.lean` …
`SieveCert22250RP351.lean`), runs its kernel checks without the environment of `import Mathlib`, which loads about 6.3 GiB
into every process. The lemmas about these definitions, in the reals and over `Finset`, stay in `SieveCert.lean`, which
imports this file and Mathlib.
-/
import Mathlib.Data.Nat.Notation

namespace SieveCert

/-! ### The grid and the certificate, in natural numbers -/

/-- The denominator of the coordinates. -/
def DEN : ℕ := 2 ^ 40
/-- **A grid of the certificate**: the window's ends `U1 < U2`, in units of `1/DEN`, and the number `n` of cells a
side. -/
class Grid where
  /-- The window's left end. -/
  U1 : ℕ
  /-- The window's right end. -/
  U2 : ℕ
  /-- The number of cells a side. -/
  n : ℕ

export Grid (U1 U2 n)

/-- The fixed point's scale: bounds are in units of `1/K = 2^{−60}`. -/
def K : ℕ := 2 ^ 60
/-- `⌈0.5672 K⌉`. -/
def topK : ℕ := (K * 5672 + 9999) / 10000

/-- The ranges of the subset sums of a box, the empty subset included. -/
def subsetSums : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | p :: rest => subsetSums rest ++ (subsetSums rest).map (fun s => (s.1 + p.1, s.2 + p.2))

/-- Division rounded up. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `f 0 + ⋯ + f (m − 1)`, by the recursor of `ℕ`, which the kernel evaluates faster than a list's fold
(`SieveCert.sumTo_eq`). -/
def sumTo (m : ℕ) (f : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc + f k) m

variable [Grid]

/-- The window's width, the least exponent of a sifted prime. -/
def V : ℕ := U2 - U1
/-- The cells' side, `⌈(DEN/2 − V)/n⌉`. -/
def H : ℕ := (DEN / 2 - V + n - 1) / n
/-- The lower end of cell `k`. -/
def e (k : ℕ) : ℕ := V + H * k
/-- `DEN − U1`, the right end of the complement window. -/
def lim : ℕ := DEN - U1

/-- A range `[lo, hi]` of sums lies inside `U`. -/
def inside (lo hi : ℕ) : Bool :=
  (decide (U1 < lo) && decide (hi < U2)) || (decide (DEN - U2 < lo) && decide (hi < DEN - U1))

/-- Some subset sum of the box lies inside `U`, by the list of all of them (the specification of `surelyEval`). -/
def surelyEvalSpec (xs : List (ℕ × ℕ)) : Bool := (subsetSums xs).any (fun s => inside s.1 s.2)

/-- `inside` by the kernel's primitive `Nat.blt` (`SieveCert.insideF_eq`). -/
def insideF (lo hi : ℕ) : Bool :=
  (Nat.blt U1 lo && Nat.blt hi U2) || (Nat.blt (DEN - U2) lo && Nat.blt hi (DEN - U1))

/-- Some subset of the boxes `xs`, added to the range `[a, b]`, has its sum inside `U`: a search with no list of sums
(`SieveCert.anySub_eq`). -/
def anySub : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], a, b => insideF a b
  | p :: rest, a, b => anySub rest a b || anySub rest (a + p.1) (b + p.2)

/-! The search of `anySub` unrolled for `k ≤ 6` boxes, `sub k`: the same tree of `||`, with `Nat.add` and no recursion,
which the kernel evaluates several times faster than the recursion; `SieveCert.surelyEval_eq` proves `surelyEval` equal to
`surelyEvalSpec`. -/

/-- The search on no box. -/
def sub0 (a b : ℕ) : Bool := insideF a b
/-- The search on one box. -/
def sub1 (p : ℕ × ℕ) (a b : ℕ) : Bool := sub0 a b || sub0 (Nat.add a p.1) (Nat.add b p.2)
/-- The search on two boxes. -/
def sub2' (p q : ℕ × ℕ) (a b : ℕ) : Bool := sub1 q a b || sub1 q (Nat.add a p.1) (Nat.add b p.2)
/-- The search on three boxes. -/
def sub3 (p q r : ℕ × ℕ) (a b : ℕ) : Bool := sub2' q r a b || sub2' q r (Nat.add a p.1) (Nat.add b p.2)
/-- The search on four boxes. -/
def sub4 (p q r s : ℕ × ℕ) (a b : ℕ) : Bool := sub3 q r s a b || sub3 q r s (Nat.add a p.1) (Nat.add b p.2)
/-- The search on five boxes. -/
def sub5 (p q r s t : ℕ × ℕ) (a b : ℕ) : Bool :=
  sub4 q r s t a b || sub4 q r s t (Nat.add a p.1) (Nat.add b p.2)
/-- The search on six boxes. -/
def sub6 (p q r s t u : ℕ × ℕ) (a b : ℕ) : Bool :=
  sub5 q r s t u a b || sub5 q r s t u (Nat.add a p.1) (Nat.add b p.2)

/-- Some subset sum of the box lies inside `U` on the whole box: `surelyEvalSpec` by the unrolled search, for up to six
boxes (`SieveCert.surelyEval_eq`). -/
def surelyEval (xs : List (ℕ × ℕ)) : Bool :=
  match xs with
  | [] => sub0 0 0
  | p :: xs1 =>
    match xs1 with
    | [] => sub1 p 0 0
    | q :: xs2 =>
      match xs2 with
      | [] => sub2' p q 0 0
      | r :: xs3 =>
        match xs3 with
        | [] => sub3 p q r 0 0
        | s :: xs4 =>
          match xs4 with
          | [] => sub4 p q r s 0 0
          | t :: xs5 =>
            match xs5 with
            | [] => sub5 p q r s t 0 0
            | u :: xs6 =>
              match xs6 with
              | [] => sub6 p q r s t u 0 0
              | _ :: _ => surelyEvalSpec xs

/-- `K/max(lo, 1)` rounded up, with `lo = (DEN − s − t − mH)/(t + H)`. -/
def invK (s t m : ℕ) : ℕ :=
  if DEN ≤ s + 2 * t + (m + 1) * H then K else cdiv (K * (t + H)) (DEN - s - t - m * H)

/-- `K` times an upper bound for the crude `ω` on the arguments `[lo, hi]` of a cell, rounded up, where
`lo = (DEN − s − t − mH)/(t + H)` and `hi = (DEN − s − t)/t`: `0` if `hi < 1`, `0.5672` if `lo ≥ 2`, `1/max(lo, 1)`
if `hi < 2`, and the larger of the last two otherwise. -/
def omK (s t m : ℕ) : ℕ :=
  if DEN < s + 2 * t then 0
  else if s + 3 * t + (m + 2) * H ≤ DEN then topK
  else if DEN < s + 3 * t then invK s t m else max (invK s t m) topK

/-- The bound of a cell of depth 2 with lower corner `(a, b)`, in units of `1/K`. -/
def bound2 (a b : ℕ) : ℕ := cdiv (H * H * DEN * omK a b 2) (a * b * b)

/-- The bound of a cell of depth 4 with lower corner `(a, b, c, d)`, in units of `1/K`. -/
def bound4 (a b c d : ℕ) : ℕ := cdiv (H ^ 4 * DEN * omK (a + b + c) d 4) (a * b * c * d * d)

/-- The range of cell `k`. -/
def cell (k : ℕ) : ℕ × ℕ := (e k, e k + H)

/-! ### The coarse grid of the primes `p₅` and `p₆`, and the cells of depths 5 and 6 -/

/-- The **coarse grid**: the same window and `n / 4` cells a side, so cells four times as wide. Its cells hold the primes
`p₅` and `p₆` of the deepest levels. -/
@[instance_reducible] def Gc : Grid := ⟨U1, U2, n / 4⟩

/-- The number of cells of the coarse grid. -/
def nC : ℕ := n / 4
/-- The side of a coarse cell, `⌈(DEN/2 − V)/nC⌉`. -/
def HC : ℕ := @H Gc
/-- The lower end of the coarse cell `b`. -/
def eC (b : ℕ) : ℕ := @e Gc b
/-- The range of the coarse cell `b`. -/
def cellC (b : ℕ) : ℕ × ℕ := (eC b, eC b + HC)

/-- `invK` with the boxes' total width `W` and the last box's width `w`: `K/max(lo, 1)` rounded up for
`lo = (DEN − s − t − W)/(t + w)`. -/
def invKw (s t W w : ℕ) : ℕ :=
  if DEN ≤ s + 2 * t + W + w then K else cdiv (K * (t + w)) (DEN - s - t - W)

/-- `omK` with the boxes' total width `W` and the last box's width `w`. -/
def omKw (s t W w : ℕ) : ℕ :=
  if DEN < s + 2 * t then 0
  else if s + 3 * t + W + 2 * w ≤ DEN then topK
  else if DEN < s + 3 * t then invKw s t W w else max (invKw s t W w) topK

/-- The bound of a cell of depth 6 with lower corner `(a, b, c, d)` in the fine grid and `(f, g)` in the coarse grid,
in units of `1/K`. -/
def bound6 (a b c d f g : ℕ) : ℕ :=
  cdiv (H ^ 4 * HC ^ 2 * DEN * omKw (a + b + c + d + f) g (4 * H + 2 * HC) HC) (a * b * c * d * f * g * g)

/-- The cell `(i, j)` may meet the region of depth 2 and may be non-evaluable. -/
def cand (i j : ℕ) : Bool :=
  decide (e j < e i + H) && decide (2 * e i < DEN) && decide (e i + 2 * e j ≤ DEN) &&
    !(decide (U1 < e i) && decide (e i + H < U2)) && !surelyEval [cell i, cell j]

/-- The cell `k` of `α₃` may meet the region of depth 3 over the cell `(i, j)`. -/
def inKK (i j k : ℕ) : Bool := decide (e k < e j + H) && decide (e i + e j + 2 * e k ≤ DEN)

/-- The cell `(i, j, k)` may be non-evaluable. -/
def ne3 (i j k : ℕ) : Bool := !surelyEval [cell i, cell j, cell k]

/-- The sharp rule: the sums `α₁ + α₂`, and `α₁ + α₂ + α₃` over the counted rows, stay below `1 − u₁`. -/
def allowed (i j : ℕ) : Bool :=
  decide (e i + H + (e j + H) < lim) &&
    (List.range n).all (fun k => !(inKK i j k && ne3 i j k) || decide (e i + H + (e j + H) + (e k + H) < lim))

/-- The cell `(i, j, k, l)` may be non-evaluable, and for `l ≤ k`, which `row` imposes, it may meet the region of
depth 4. -/
def counted4 (i j k l : ℕ) : Bool :=
  decide (e i + e j + e k + 2 * e l ≤ DEN) && !surelyEval [cell i, cell j, cell k, cell l]

/-- The cell `f` of the coarse grid for `p₅` may meet the region of depth 5 over the cell `(i, j, k, l)`. -/
def inKK5 (i j k l b : ℕ) : Bool :=
  decide (eC b < e l + H) && decide (e i + e j + e k + e l + 2 * eC b ≤ DEN)

/-- The cell `(i, j, k, l, b)` may be non-evaluable. -/
def ne5 (i j k l b : ℕ) : Bool := !surelyEval [cell i, cell j, cell k, cell l, cellC b]

/-- The cell `(i, j, k, l, b, c)` may be non-evaluable, and for `c ≤ b`, which `row6` imposes, it may meet the region of
depth 6. -/
def counted6 (i j k l b c : ℕ) : Bool :=
  decide (e i + e j + e k + e l + eC b + 2 * eC c ≤ DEN) &&
    !surelyEval [cell i, cell j, cell k, cell l, cellC b, cellC c]

/-- The row `(i, j, k, l, b)`: the counted cells of `α₆`, which have `c ≤ b`. -/
def row6 (i j k l b : ℕ) : ℕ :=
  sumTo (b + 1) (fun c => if counted6 i j k l b c then bound6 (e i) (e j) (e k) (e l) (eC b) (eC c) else 0)

/-- The cost of decomposing the counted cell `(i, j, k, l)` one level further: its counted cells of depth 6. -/
def refcost5 (i j k l : ℕ) : ℕ :=
  sumTo nC (fun b => if inKK5 i j k l b && ne5 i j k l b then row6 i j k l b else 0)

/-- The sharp rule at depth 4: the sum `α₁ + α₂ + α₃ + α₄`, and `α₁ + ⋯ + α₅` over the counted cells of depth 5, stay
below `1 − u₁`. -/
def allowed4 (i j k l : ℕ) : Bool :=
  decide (e i + H + (e j + H) + (e k + H) + (e l + H) < lim) &&
    (List.range nC).all (fun b => !(inKK5 i j k l b && ne5 i j k l b) ||
      decide (e i + H + (e j + H) + (e k + H) + (e l + H) + (eC b + HC) < lim))

/-- The counted cell `(i, j, k, l)` of depth 4 is decomposed one level further. -/
def dec4 (i j k l : ℕ) : Bool :=
  allowed4 i j k l && decide (refcost5 i j k l ≤ bound4 (e i) (e j) (e k) (e l))

/-- The cost of the cell `(i, j, k, l)` of depth 4. -/
def cost4 (i j k l : ℕ) : ℕ :=
  if counted4 i j k l then
    (if dec4 i j k l then refcost5 i j k l else bound4 (e i) (e j) (e k) (e l)) else 0

/-- The row `(i, j, k)`: the costs of the cells of `α₄`, which have `l ≤ k`. -/
def row (i j k : ℕ) : ℕ := sumTo (k + 1) (fun l => cost4 i j k l)

/-- The cost of decomposing the cell `(i, j)`: its cells of depth 4. -/
def refcost (i j : ℕ) : ℕ := sumTo n (fun k => if inKK i j k && ne3 i j k then row i j k else 0)

/-- The cell `(i, j)` is decomposed. -/
def dec (i j : ℕ) : Bool := allowed i j && decide (refcost i j ≤ bound2 (e i) (e j))

/-- The cost of the cell `(i, j)`. -/
def cost (i j : ℕ) : ℕ := if cand i j then (if dec i j then refcost i j else bound2 (e i) (e j)) else 0

/-- The certificate's total, in units of `1/K`. -/
def total : ℕ := sumTo n (fun i => sumTo n (fun j => cost i j))

/-- The sum of the rows `a ≤ i < b` of the total. -/
def rows (a b : ℕ) : ℕ := sumTo (b - a) (fun i => sumTo n (fun j => cost (a + i) j))

/-! ### Facts about the grid -/

/-- **The facts about a grid** that the lemmas of `SieveCert.lean` and the route's proofs use. For a given grid each
is checked by `decide`. -/
class GridOK : Prop where
  H_pos : 0 < H
  U1_lt_U2 : U1 < U2
  two_U2_lt : 2 * U2 < DEN
  two_e_lt : 2 * e (n - 1) < DEN
  four_H_le_V : 4 * H ≤ V
  DEN_lt_top : DEN < 2 * (V + n * H)

/-- **The facts about the coarse grid** (`Gc`, with its cells `eC`, `HC`) that the deepest levels use: its own `GridOK`,
`4H + 2HC ≤ V`, which keeps the boxes of depth 6 inside `DEN`, and `nH ≤ nC·HC`, which makes the coarse cells cover the
range of the fine ones. For a given grid each is checked by `decide`. -/
class GridOKC : Prop where
  /-- The coarse grid's own facts. -/
  ok : @GridOK Gc
  /-- The boxes of depth 6 fit. -/
  fit : 4 * H + 2 * HC ≤ V
  /-- The coarse cells cover the range of the fine ones: `nH ≤ nC·HC`. -/
  cover : n * H ≤ nC * HC

end SieveCert
