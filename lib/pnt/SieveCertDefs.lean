/-
# The certificate's definitions, without Mathlib

The definitions that the certificates build on: the grid of cells (`Grid`, `V`, `H`, `e`, `cell`) and the bound `ω*`
for Buchstab's `ω` on a box (`omKw`, with its table `lnT` and `omF`). They are arithmetic on natural numbers, and the
file imports only `Mathlib.Data.Nat.Notation` (the notation `ℕ`), whose closure is `Mathlib.Init`'s: 1,339 modules,
loaded in about 0.9 GiB, not the whole of Mathlib. So a file that imports no more than this one and the other
Mathlib-free definitions, such as the certificate's parts `SieveHint21500P1.lean` … `SieveHint21500P17.lean`, runs its
kernel checks without the environment of `import Mathlib`, which loads about 6.3 GiB into every process. The lemmas
about these definitions, in the reals, are in `SieveCert.lean` and `SieveOmegaB.lean`, which import this file and
Mathlib.

* The grid. Coordinates are multiples of `1/DEN`, `DEN = 2^40`. A grid (`Grid`) has the window's ends `U1 < U2`, in
  units of `1/DEN`, the number `n` of cells a side and the cells' multiplier `μ`. The window's width is `V = U2 − U1`,
  the cells' side is `H = μ⌈(DEN/2 − V)/(μn)⌉` (for `μ = 1`, `⌈(DEN/2 − V)/n⌉`), and cell `k` is
  `cell k = (e k, e k + H)` with `e k = V + Hk`.
-/
import Mathlib.Data.Nat.Notation

namespace SieveCert

/-! ### The grid, in natural numbers -/

/-- The denominator of the coordinates. -/
def DEN : ℕ := 2 ^ 40
/-- **A grid of the certificate**: the window's ends `U1 < U2`, in units of `1/DEN`, the number `n` of cells a side,
and the cells' multiplier `μ`: a cell is `μ` consecutive cells of the grid of `μn` cells. -/
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

/-- Division rounded up. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

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

/-- The range of cell `k`. -/
def cell (k : ℕ) : ℕ × ℕ := (e k, e k + H)

end SieveCert
