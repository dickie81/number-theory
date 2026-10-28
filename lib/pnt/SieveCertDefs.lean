/-
# The certificate's definitions, without Mathlib

The definitions of the loss certificate of `SieveCert.lean`, of its bound `ω*` for Buchstab's `ω` on a box (`omKw`, with
its table `lnT` and `omF`), and of its classes `GridOK` and `GridOKC`. They are arithmetic on natural numbers, lists and
booleans, and the file imports only `Mathlib.Data.Nat.Notation` (the notation `ℕ`), whose closure is `Mathlib.Init`'s:
1,339 modules, loaded in about 0.9 GiB, not the whole of Mathlib. So a file that imports no more than this one, such as a
certificate's part files (`SieveCert22240RP1.lean` … `SieveCert22240RP387.lean`), runs its kernel checks without the
environment of `import Mathlib`, which loads about 6.3 GiB into every process. The lemmas about these definitions, in the
reals and over `Finset`, are in `SieveCert.lean` and `SieveOmegaB.lean`, which import this file and Mathlib.
-/
import Mathlib.Data.Nat.Notation

namespace SieveCert

/-! ### The grid and the certificate, in natural numbers -/

/-- The denominator of the coordinates. -/
def DEN : ℕ := 2 ^ 40
/-- **A grid of the certificate**: the window's ends `U1 < U2`, in units of `1/DEN`, the number `n` of cells a side,
and the cells' multiplier `μ`: a cell is `μ` consecutive cells of the grid of `μn` cells (`μ = 1` for a certificate's
grid; its coarse grid `Gc` has `n/4` cells of four). -/
class Grid where
  /-- The window's left end. -/
  U1 : ℕ
  /-- The window's right end. -/
  U2 : ℕ
  /-- The number of cells a side. -/
  n : ℕ
  /-- The cells' multiplier `μ`. -/
  mult : ℕ

export Grid (U1 U2 n)

/-- The fixed point's scale: bounds are in units of `1/K = 2^{−60}`. -/
def K : ℕ := 2 ^ 60
/-- `⌈0.565073 K⌉`: `K` times `ω* = 0.565073`, the bound above `3`. -/
def topK : ℕ := (K * 565073 + 999999) / 1000000
/-- `⌈0.5671433 K⌉`: `K` times an upper bound for Buchstab's `ω` on `[2, 3]`, whose maximum is `Ω = 0.56714329…`
(`Ω e^Ω = 1`), at `u = 1 + 1/Ω`. -/
def w1K : ℕ := (K * 5671433 + 9999999) / 10000000

/-- The ranges of the subset sums of a box, the empty subset included. -/
def subsetSums : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | p :: rest => subsetSums rest ++ (subsetSums rest).map (fun s => (s.1 + p.1, s.2 + p.2))

/-- Division rounded up. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `f 0 + ⋯ + f (m − 1)`, by the recursor of `ℕ`, which the kernel evaluates faster than a list's fold
(`SieveCert.sumTo_eq`). -/
def sumTo (m : ℕ) (f : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc + f k) m

/-! ### Buchstab's `ω` on the arguments of a box -/

/-- The denominator of `lnT`. -/
def LD : ℕ := 10 ^ 9

/-- `LD` times an upper bound for `log((16 + k)/16)`, for `k ≤ 16` (`SieveOmegaB.lnT_ge`), by a tree of tests. -/
def lnT (k : ℕ) : ℕ :=
  if k < 8 then
    if k < 4 then
      if k < 2 then (if k < 1 then 0 else 60624623) else (if k < 3 then 117783037 else 171850258)
    else
      if k < 6 then (if k < 5 then 223143553 else 271933717) else (if k < 7 then 318453733 else 362905495)
  else if k < 16 then
    if k < 12 then
      if k < 10 then (if k < 9 then 405465110 else 446287104) else (if k < 11 then 485507817 else 523248145)
    else
      if k < 14 then (if k < 13 then 559615789 else 594707109) else (if k < 15 then 628608661 else 661398484)
  else 693147182

/-- `omF` at the table's index `k`, with `A = 16(P − Q)` and `B = (16 + k)Q`: `K` times
`(Q/P)(1 + lnT k/LD + (A/B − B/A)/2)`, rounded up. -/
def omFk (P Q k A B : ℕ) : ℕ :=
  cdiv (K * Q * (2 * A * B * (LD + lnT k) + (A * A - B * B) * LD)) (2 * A * B * LD * P)

/-- `K` times an upper bound for Buchstab's `ω(v) = (1 + log(v − 1))/v` at `v = P/Q ∈ [2, 3]`, rounded up
(`SieveOmegaB.omF_ge`): with `k = ⌊16(v − 2)⌋` and `r = (16 + k)/16 ≤ v − 1`, `log(v − 1) ≤ lnT k/LD + (y − 1/y)/2` for
`y = (v − 1)/r = A/B`. -/
def omF (P Q : ℕ) : ℕ :=
  omFk P Q (16 * (P - 2 * Q) / Q) (16 * (P - Q)) ((16 + 16 * (P - 2 * Q) / Q) * Q)

/-- `K/max(lo, 1)` rounded up, for `lo = (DEN − s − t − W)/(t + w)`: the boxes' total width is `W` and the last box's
width `w`. -/
def invKw (s t W w : ℕ) : ℕ :=
  if DEN ≤ s + 2 * t + W + w then K else cdiv (K * (t + w)) (DEN - s - t - W)

/-- `K` times an upper bound for `ω*` (`SieveCert.omegaC`) on the arguments of a box, rounded up: the other exponents
sum to at least `s`, the last lies in `[t, t + w]`, and all of them sum to at most `s + t + W`, so the arguments lie in
`[lo, hi)` with `lo = (DEN − s − t − W)/(t + w)` and `hi = (DEN + 1 − s − t)/t`. It is `0` if `hi ≤ 1`, `0.565073` if
`lo ≥ 3`, `1/max(lo, 1)` if `hi ≤ 2`, and otherwise the largest of `1/max(lo, 1)` (if `lo < 2`), the bound on `[2, 3]`
and `0.565073` (if `hi > 3`). On `[2, 3]` the bound is Buchstab's `ω` at `hi` if `hi ≤ 2.76`, where `ω` increases, at
`lo` if `lo ≥ 2.77`, where it decreases, and its maximum otherwise. -/
def omKw (s t W w : ℕ) : ℕ :=
  if DEN < s + 2 * t then 0
  else if s + 4 * t + W + 3 * w ≤ DEN then topK
  else if DEN < s + 3 * t then invKw s t W w
  else max (max (if s + 3 * t + W + 2 * w ≤ DEN then 0 else invKw s t W w)
      (if 100 * (DEN + 1 - s - t) ≤ 276 * t then omF (DEN + 1 - s - t) t
        else if 277 * (t + w) ≤ 100 * (DEN - s - t - W) then omF (DEN - s - t - W) (t + w) else w1K))
    (if s + 4 * t ≤ DEN then topK else 0)

variable [Grid]

/-- The window's width, the least exponent of a sifted prime. -/
def V : ℕ := U2 - U1
/-- The cells' side, `μ⌈(DEN/2 − V)/(μn)⌉`: for `μ = 1`, `⌈(DEN/2 − V)/n⌉`. -/
def H : ℕ := Grid.mult * ((DEN / 2 - V + n * Grid.mult - 1) / (n * Grid.mult))
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

/-- `omKw` for a cell of `m` variables, all of width `H`. -/
def omK (s t m : ℕ) : ℕ := omKw s t (m * H) H

/-- The bound of a cell of depth 2 with lower corner `(a, b)`, in units of `1/K`: `omK` times `H(2a + H)/(2a(a + H))`,
the trapezoid bound of the first cell's `Σ 1/p`, times `DEN·H/(b(b + H))`, the last cell's `log x · Σ 1/(p log p)`,
rounded up. -/
def bound2 (a b : ℕ) : ℕ := cdiv (H * H * (2 * a + H) * DEN * omK a b 2) (2 * a * (a + H) * (b * (b + H)))

/-- The bound of a cell of depth 4 with lower corner `(a, b, c, d)`, in units of `1/K`: as `bound2`, with a trapezoid
factor for each of the first three cells. -/
def bound4 (a b c d : ℕ) : ℕ :=
  cdiv (H ^ 4 * ((2 * a + H) * (2 * b + H) * (2 * c + H)) * DEN * omK (a + b + c) d 4)
    (8 * (a * (a + H)) * (b * (b + H)) * (c * (c + H)) * (d * (d + H)))

/-- The range of cell `k`. -/
def cell (k : ℕ) : ℕ × ℕ := (e k, e k + H)

/-! ### The coarse grid of the primes `p₅` and `p₆`, and the cells of depths 5 and 6 -/

/-- The **coarse grid**: the same window and `n / 4` cells a side, each four consecutive cells of the grid: for `4 ∣ n`
and `μ = 1` its side is `HC = 4H` and its cell `b` is the cells `4b, …, 4b + 3`. Its cells hold the primes `p₅` and `p₆`
of the deepest levels. -/
@[instance_reducible] def Gc : Grid := ⟨U1, U2, n / 4, 4 * Grid.mult⟩

/-- The number of cells of the coarse grid. -/
def nC : ℕ := n / 4
/-- The side of a coarse cell, `4μ⌈(DEN/2 − V)/(4μ·nC)⌉`: `4H` for `4 ∣ n`. -/
def HC : ℕ := @H Gc
/-- The lower end of the coarse cell `b`. -/
def eC (b : ℕ) : ℕ := @e Gc b
/-- The range of the coarse cell `b`. -/
def cellC (b : ℕ) : ℕ × ℕ := (eC b, eC b + HC)

/-- The bound of a cell of depth 6 with lower corner `(a, b, c, d)` in the fine grid and `(f, g)` in the coarse grid,
in units of `1/K`: as `bound4`, with trapezoid factors for the first five cells (the fifth of width `HC`). -/
def bound6 (a b c d f g : ℕ) : ℕ :=
  cdiv (H ^ 4 * HC ^ 2 * ((2 * a + H) * (2 * b + H) * (2 * c + H) * (2 * d + H) * (2 * f + HC)) * DEN *
      omKw (a + b + c + d + f) g (4 * H + 2 * HC) HC)
    (32 * (a * (a + H)) * (b * (b + H)) * (c * (c + H)) * (d * (d + H)) * (f * (f + HC)) * (g * (g + HC)))

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
range of the fine ones (with equality for `4 ∣ n` and multiplier `1`, where a coarse cell is four fine ones). For a given
grid each is checked by `decide`. -/
class GridOKC : Prop where
  /-- The coarse grid's own facts. -/
  ok : @GridOK Gc
  /-- The boxes of depth 6 fit. -/
  fit : 4 * H + 2 * HC ≤ V
  /-- The coarse cells cover the range of the fine ones: `nH ≤ nC·HC`. -/
  cover : n * H ≤ nC * HC

end SieveCert
