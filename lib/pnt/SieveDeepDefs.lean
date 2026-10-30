/-
# The certificate to depth 8, without Mathlib

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The certificate of the decomposition to depth 8 (`SieveBuch8.lean`) under the bilinear Type I rule. A candidate cell
`(i, j)` that is decomposed costs the refined cost of its counted cells of depth 3 (`refcost`); one that is not costs
`bound2`. Below a counted cell `(i, j, k)` of depth 3, a counted cell `l` of depth 4 is dropped, at its depth-4 bound,
or decomposed to depth 6 over the coarse cells `b` and `c` of `p₅` and `p₆`; a counted cell of depth 6 is dropped, at
its depth-6 bound, or decomposed to depth 8 over the coarse cells of `p₇` and `p₈`, whose cells are all dropped. Each
cell takes the cheaper of the two. The values are in fixed point, `SC = 2^64`, with each prime's factor rounded up:
`trapF` the trapezoid bound of a cell's `Σ 1/p` (`SieveCert.trB`), `lastF` the last cell's `log x · Σ 1/(p log p)`
(`SieveCert.exB`), and `omKw` the bound for Buchstab's `ω` in units of `1/K`.

With `HC = 4H`, a cell's lower end `V + Hk` and a coarse cell's `V + HC b` make a box's lower sum `mV + H·I` for its `m`
cells and the index sum `I` (a coarse cell's index counting four), so the bounds of the dropped cells are memoised by
their index sums (`Q4`, `q6`, `R8in`, `R8`, `vR`, `vRpre`, `Fpure`, `Gpure`); `lit` evaluates a key to a numeral, so
that the kernel's cache of an expression's value serves equal keys.

* `lmask`, `emask`: the cells `l` of `p₄` with the box `(i, j, k, l)` surely evaluable, and the coarse index sums of
  `m = 1, 2` coarse cells with the box surely evaluable, as bit masks: a set of the box's cells whose sum lies in a
  window `(wl, wh)` gives an interval of the index sum, shifted from global masks (`lbase`, `sbase`).
* `creg`, `lreg`, `bcnt`: the number of cells of a region, in closed form.
* `dcp`, `dmax3`, `okD`: **the block test.** For the box `(i, j, k)` and `T = tstar` of it, `dmax3` is one more than
  the largest sum `D` of the upper ends of deeper primes at which some split of the box, with `e` on one side and the
  deeper primes all on one side, satisfies the estimate `condIB`; a deeper box passes `okD` when its upper sum is below
  `lim`, or it has no boundary term and its deeper sum is below `dmax3`. Then the rule passes it
  (`SieveDeep.okIB_of_okD`).
* `cstar`: the number of cells `c` of `p₆` below `(…, b)` whose worst box of depth 7 (`p₇` in the cell `c`) passes
  `okD`; `pureOK`: every box of depth 5, 6 and 7 below the cell `l` passes, so its cost depends on `(i + j + k, l)`
  alone (`Gpure`).
* `cost4`, `row`, `refcost`: the cost of the cell `l` below `(i, j, k)`, the row `(i, j, k)` and the refined cost of
  `(i, j)`, in units of `SC⁵/K`, `SC⁵/K` and `1/K`.
* `ok3D`, `allowedD`, `decD`, `costD`, `totalD`, `rowsJD`: the rule on the boxes of depths 2 and 3 (`okD` on a box of
  depth 3), the decision, the cost of a cell of depth 2, and the total and its parts, in units of `1/K`.

These are arithmetic on natural numbers, lists and booleans, with the tests by `Nat.ble` and `Nat.blt`, and the file
imports only `SieveRuleDefs.lean`, so a part file that imports no more than this one runs its kernel checks without
`Mathlib`. `tools/linnik/mirror8.py` mirrors them in exact integers.
-/
import SieveRuleDefs

namespace SieveDeep

open SieveCert

/-! ### Fixed point -/

/-- The fixed point's scale. -/
def SC : ℕ := 2 ^ 64

/-- `f n`, with `n` evaluated to a numeral first, so that equal keys share the kernel's cache. -/
def lit (n : ℕ) (f : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (f 0) (fun k _ => f (Nat.succ k)) n

/-- `min` by `Nat.ble`. -/
def nmin (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

/-- `max` by `Nat.ble`. -/
def nmax (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

/-- Bits `a, …, b` (none if `b < a`). -/
def bits (a b : ℕ) : ℕ := cond (Nat.blt b a) 0 ((2 ^ (b + 1 - a) - 1) <<< a)

/-- The bit `s` of `M`. -/
def bit (M s : ℕ) : Bool := Nat.beq ((M >>> s) % 2) 1

/-- The least `t` with `y + d·t > x`: `⌊(x − y)/d⌋ + 1` for `y ≤ x`, and `0` otherwise. -/
def above (x y d : ℕ) : ℕ := cond (Nat.ble y x) ((x - y) / d + 1) 0

section

variable [Grid]

/-- `⌈SC·w(2x + w)/(2x(x + w))⌉`, `SC` times the trapezoid bound of the `Σ 1/p` of the cell `[x, x + w]`. -/
def trapF (x w : ℕ) : ℕ := cdiv (SC * w * (2 * x + w)) (2 * x * (x + w))

/-- `⌈SC·w·DEN/(x(x + w))⌉`, `SC` times the bound of the last cell's `log x · Σ 1/(p log p)`. -/
def lastF (x w : ℕ) : ℕ := cdiv (SC * w * DEN) (x * (x + w))

/-! ### The dropped cells' bounds, by index sums -/

/-- The bound of the last prime of a cell of depth 4: its cell `l`, the others' lower sum `3V + H·I3`. -/
def Q4 (I3 l : ℕ) : ℕ := lastF (e l) H * omKw (3 * V + H * I3) (e l) (4 * H) H

/-- The bound of the last prime of a cell of depth 6: its coarse cell `c`, the others' lower sum `5V + H·I5`. -/
def q6 (I5 c : ℕ) : ℕ := lastF (eC c) HC * omKw (5 * V + H * I5) (eC c) (4 * H + 2 * HC) HC

/-- The cells of `p₈` below a cell of depth 7 (`p₇` in the coarse cell `c7`, the lower sum `7V + H·I7` with it): the
coarse cells `c8 ≤ c7` with `7V + H·I7 + 2eC c8 ≤ DEN`. -/
def R8in (I7 c7 : ℕ) : ℕ :=
  sumTo (c7 + 1) (fun c8 => cond (Nat.ble (7 * V + H * I7 + 2 * eC c8) DEN)
    (lastF (eC c8) HC * omKw (7 * V + H * I7) (eC c8) (4 * H + 4 * HC) HC) 0)

/-- The cells of depth 7 and 8 below a cell of depth 6 (`p₆` in the coarse cell `c`, the lower sum `6V + H·I6` with
it): the coarse cells `c7 ≤ c` with `6V + H·I6 + 2eC c7 ≤ DEN`. -/
def R8 (I6 c : ℕ) : ℕ :=
  sumTo (c + 1) (fun c7 => cond (Nat.ble (6 * V + H * I6 + 2 * eC c7) DEN)
    (trapF (eC c7) HC * lit (I6 + 4 * c7) (fun I7 => R8in I7 c7)) 0)

/-- A cell of depth 6, dropped or decomposed, whichever is cheaper: the lower sum `5V + H·I5` without it. -/
def vR (I5 c : ℕ) : ℕ := nmin (q6 I5 c * SC * SC) (trapF (eC c) HC * lit (I5 + 4 * c) (fun I6 => R8 I6 c))

/-- `vR I5 0 + ⋯ + vR I5 c`. -/
def vRpre (I5 c : ℕ) : ℕ := sumTo (c + 1) (fun c' => vR I5 c')

/-! ### The surely evaluable boxes, as bit masks -/

/-- Over `u`, the boxes of `m + 1` cells of the grid with index sum `u` whose range `((m + 1)V + Hu, (m + 1)(V + H)
+ Hu)` lies in `(wl, wh)`. -/
def lbase1 (m wl wh : ℕ) : ℕ :=
  cond (Nat.blt ((m + 1) * (V + H)) wh) (bits (above wl ((m + 1) * V) H) ((wh - (m + 1) * (V + H) - 1) / H)) 0

/-- `lbase1` for the window `(U1, U2)` and its reflection. -/
def lbase (m : ℕ) : ℕ := lbase1 m U1 U2 ||| lbase1 m (DEN - U2) (DEN - U1)

/-- Over `t`, the boxes of `mr` cells of the grid with index sum `ρ + 4t'` and `m` coarse cells with index sum `t − t'`
whose range `((mr + m)V + Hρ + HC t, (mr + m)V + Hρ + mr·H + m·HC + HC t)` lies in `(wl, wh)`. -/
def sbase1 (mr m ρ wl wh : ℕ) : ℕ :=
  cond (Nat.blt ((mr + m) * V + H * ρ + mr * H + m * HC) wh)
    (bits (above wl ((mr + m) * V + H * ρ) HC) ((wh - (mr + m) * V - H * ρ - mr * H - m * HC - 1) / HC)) 0

/-- `sbase1` for the window `(U1, U2)` and its reflection. -/
def sbase (mr m ρ : ℕ) : ℕ := sbase1 mr m ρ U1 U2 ||| sbase1 mr m ρ (DEN - U2) (DEN - U1)

/-- Over the coarse index sum `s`, the boxes of `mr` cells of the grid with index sum `N` and `m` coarse cells with
index sum `s` whose range lies in a window. -/
def smask (mr m N : ℕ) : ℕ := lit (N % 4) (fun ρ => sbase mr m ρ) >>> (N / 4)

/-- The cells `l` of `p₄` for which a set of the cells of `(i, j, k, l)` with `l` has its range in a window. -/
def lmask (i j k : ℕ) : ℕ :=
  lbase 0 ||| (lbase 1 >>> i) ||| (lbase 1 >>> j) ||| (lbase 1 >>> k) ||| (lbase 2 >>> (i + j)) |||
    (lbase 2 >>> (i + k)) ||| (lbase 2 >>> (j + k)) ||| (lbase 3 >>> (i + j + k))

/-- Over the coarse index sum, the sets of cells of `(i, j, k)` and `m` coarse cells with their range in a window. -/
def emask3 (m i j k : ℕ) : ℕ :=
  smask 0 m 0 ||| smask 1 m i ||| smask 1 m j ||| smask 1 m k ||| smask 2 m (i + j) ||| smask 2 m (i + k) |||
    smask 2 m (j + k) ||| smask 3 m (i + j + k)

/-- As `emask3`, for the sets with the cell `l` of `p₄`, `l ≡ ρ (mod 4)`, before the shift by `⌊l/4⌋`. -/
def fmask3 (m i j k ρ : ℕ) : ℕ :=
  smask 1 m ρ ||| smask 2 m (i + ρ) ||| smask 2 m (j + ρ) ||| smask 2 m (k + ρ) ||| smask 3 m (i + j + ρ) |||
    smask 3 m (i + k + ρ) ||| smask 3 m (j + k + ρ) ||| smask 4 m (i + j + k + ρ)

/-- Over the coarse index sum, the sets of cells of `(i, j, k, l)` and `m` coarse cells with their range in a
window. -/
def emask (m i j k l : ℕ) : ℕ := emask3 m i j k ||| (lit (l % 4) (fun ρ => fmask3 m i j k ρ) >>> (l / 4))

/-! ### The regions -/

/-- The number of coarse cells `c` with `S + 2eC c ≤ DEN`. -/
def creg (S : ℕ) : ℕ := cond (Nat.ble (S + 2 * V) DEN) ((DEN - S - 2 * V) / (2 * HC) + 1) 0

/-- The number of cells `l` with `S + 2e l ≤ DEN`. -/
def lreg (S : ℕ) : ℕ := cond (Nat.ble (S + 2 * V) DEN) ((DEN - S - 2 * V) / (2 * H) + 1) 0

/-- The number of the region's coarse cells `b` of `p₅` below the cell `l` of `p₄`, the lower sum `4V + H·I4`:
`4b ≤ l` and `4V + H·I4 + 2eC b ≤ DEN`. -/
def bcnt (I4 l : ℕ) : ℕ := nmin (l / 4 + 1) (creg (4 * V + H * I4))

/-! ### The cells of depth 4 whose boxes below all pass -/

/-- Below the cell `l` of depth 4 (the lower sum `4V + H·I4`), every cell of depth 6 of its region at `vR`. -/
def Fpure (I4 l : ℕ) : ℕ :=
  sumTo (bcnt I4 l) (fun b =>
    let cm := nmin (b + 1) (creg (4 * V + H * I4 + eC b))
    cond (Nat.beq cm 0) 0 (trapF (eC b) HC * lit (I4 + 4 * b) (fun I5 => lit (cm - 1) (fun c => vRpre I5 c))))

/-- The cell `l` of depth 4 below a box with index sum `I3`, dropped or decomposed with `Fpure`, whichever is
cheaper. -/
def Gpure (I3 l : ℕ) : ℕ :=
  nmin (lit I3 (fun I => Q4 I l) * SC ^ 4) (trapF (e l) H * lit (I3 + l) (fun I4 => Fpure I4 l))

/-! ### The block test -/

variable [IBPar]

/-- The block test with the deeper primes on the side of `a₁`: one more than the largest `D` with
`(a₁ + D)·Lnum < (Lnum − Lden)·DEN` and `a₁ + D + 2a₂ < DEN`, or `0` for none. -/
def dcpT (a1 a2 : ℕ) : ℕ :=
  nmin (cond (Nat.blt (a1 * IBPar.Lnum) ((IBPar.Lnum - IBPar.Lden) * DEN))
      (((IBPar.Lnum - IBPar.Lden) * DEN - a1 * IBPar.Lnum - 1) / IBPar.Lnum + 1) 0)
    (cond (Nat.blt (a1 + 2 * a2) DEN) (DEN - a1 - 2 * a2) 0)

/-- The block test with the deeper primes on the side of `a₂`: one more than the largest `D` with
`a₁·Lnum < (Lnum − Lden)·DEN` and `a₁ + 2(a₂ + D) < DEN`, or `0` for none. -/
def dcpF (a1 a2 : ℕ) : ℕ :=
  cond (Nat.blt (a1 * IBPar.Lnum) ((IBPar.Lnum - IBPar.Lden) * DEN))
    (cond (Nat.blt (a1 + 2 * a2) DEN) ((DEN - a1 - 2 * a2 - 1) / 2 + 1) 0) 0

/-- The block test at a split with sums `(a₁, a₂)` without the deeper primes: either side. -/
def dcp (a1 a2 : ℕ) : ℕ := nmax (dcpT a1 a2) (dcpF a1 a2)

/-- The block test's bound for a box `xs` with `T = tstar` of it: the largest over its subset sums `s` of `dcp` with
`e` on the side of `s` or the other. -/
def dmaxL (xs : List (ℕ × ℕ)) (T : ℕ) : ℕ :=
  (subsetSums xs).foldl (fun acc s => nmax acc (nmax (dcp (s.2 + T) (hiSum xs - s.2)) (dcp s.2 (hiSum xs - s.2 + T))))
    0

/-- **The block test's bound** for the box `(i, j, k)`: `dmaxL` at `T = tstar` of it, or `0` if it has none. -/
def dmax3 (i j k : ℕ) : ℕ :=
  match tstar [cell i, cell j, cell k] with
  | none => 0
  | some T => dmaxL [cell i, cell j, cell k] T

/-- **The block test** for a box below `(i, j, k)`: its upper sum `hi3 + D` (`hi3` that of `(i, j, k)`, `D` that of
the deeper primes) is below `lim`, or it has no boundary term (`h` its last cell's upper end) and `D < Dm`. -/
def okD (hi3 Dm D h : ℕ) : Bool := Nat.blt (hi3 + D) lim || (Nat.blt (hi3 + D + h) DEN && Nat.blt D Dm)

/-- The number of coarse cells `c` with `V + HC(c + 1) ≤ X`. -/
def cntH (X : ℕ) : ℕ := cond (Nat.ble (V + HC) X) ((X - V) / HC) 0

/-- The number of coarse cells `c` whose worst box of depth 7, `p₇` in the cell `c`, passes `okD` below the cells `l`
and `b` (their upper ends `hl` and `hb`): the deeper sum `hl + hb + 2hc`, with `hc = eC c + HC`. -/
def cstar (hi3 Dm hl hb : ℕ) : ℕ :=
  nmax (cond (Nat.blt (hi3 + hl + hb) lim) (cntH ((lim - hi3 - hl - hb - 1) / 2)) 0)
    (nmin (cond (Nat.blt (hi3 + hl + hb) DEN) (cntH ((DEN - hi3 - hl - hb - 1) / 3)) 0)
      (cond (Nat.blt (hl + hb) Dm) (cntH ((Dm - hl - hb - 1) / 2)) 0))

/-! ### The costs -/

/-- The cells `cs ≤ c < cm` of depth 6 below `(…, b)` that the masks leave, at their bound `q6`. -/
def tail6 (I5 b cs cm E1 E2 : ℕ) : ℕ :=
  sumTo (cm - cs) (fun t => cond (bit E1 (cs + t) || bit E2 (b + cs + t)) 0
    (lit (cs + t) (fun c => q6 I5 c) * SC * SC))

/-- The cells of depth 6 below `(…, b)`: those whose boxes of depth 7 pass at `vR`, the rest at `q6`. -/
def cost6b (hi3 Dm I4 l b E1 E2 : ℕ) : ℕ :=
  let cm := nmin (b + 1) (creg (4 * V + H * I4 + eC b))
  let cs := nmin cm (cstar hi3 Dm (e l + H) (eC b + HC))
  trapF (eC b) HC * lit (I4 + 4 * b) (fun I5 =>
    cond (Nat.beq cs 0) 0 (lit (cs - 1) (fun c => vRpre I5 c)) +
      cond (Nat.blt cs cm) (tail6 I5 b cs cm E1 E2) 0)

/-- The number of the region's boxes of depth 5 below the cell `l` that the mask leaves and `okD` fails. -/
def bad5 (hi3 Dm I4 l E1 : ℕ) : ℕ :=
  sumTo (bcnt I4 l) (fun b => cond (!bit E1 b && !okD hi3 Dm (e l + H + eC b + HC) (eC b + HC)) 1 0)

/-- The cells of depth 5 below the cell `l` that the mask leaves. -/
def cost6 (hi3 Dm I4 l E1 E2 : ℕ) : ℕ :=
  sumTo (bcnt I4 l) (fun b => cond (bit E1 b) 0 (cost6b hi3 Dm I4 l b E1 E2))

/-- Every box of depth 5, 6 and 7 below the cell `l` passes `okD`: the box of its region's last `b`, and the worst box
of depth 7 there for every `c` that a `b` of its region has. -/
def pureOK (hi3 Dm I4 l : ℕ) : Bool :=
  let bc := bcnt I4 l
  let hbm := eC (bc - 1) + HC
  !Nat.beq bc 0 && okD hi3 Dm (e l + H + hbm) hbm &&
    Nat.ble (nmin bc (creg (4 * V + H * I4 + V))) (cstar hi3 Dm (e l + H) hbm)

/-- **The cost of the cell `l` of depth 4** below `(i, j, k)`, in units of `SC⁵/K`: its bound `q4`, or, if its box
passes `okD`, the cheaper of `q4` and its cells of depths 5 and 6 when those not surely evaluable pass. -/
def cost4 (i j k l : ℕ) : ℕ :=
  let I3 := i + j + k
  let q4 := lit I3 (fun I => Q4 I l) * SC ^ 4
  let hi3 := e i + e j + e k + 3 * H
  let Dm := dmax3 i j k
  cond (okD hi3 Dm (e l + H) (e l + H))
    (cond (pureOK hi3 Dm (I3 + l) l) (lit I3 (fun I => Gpure I l))
      (let E1 := emask 1 i j k l
       let E2 := emask 2 i j k l
       cond (Nat.beq (bad5 hi3 Dm (I3 + l) l E1) 0) (nmin q4 (trapF (e l) H * cost6 hi3 Dm (I3 + l) l E1 E2)) q4))
    q4

/-- The row `(i, j, k)`: the region's cells `l ≤ k` of depth 4 that the mask leaves, in units of `SC⁵/K`. -/
def row (i j k : ℕ) : ℕ :=
  let M := lmask i j k
  sumTo (nmin (k + 1) (lreg (e i + e j + e k))) (fun l => cond (bit M l) 0 (cost4 i j k l))

/-- The trapezoid factors of `(i, j, k)`, in units of `SC³`. -/
def P3 (i j k : ℕ) : ℕ := trapF (e i) H * trapF (e j) H * trapF (e k) H

/-- **The refined cost of the cell `(i, j)`**, in units of `1/K`: its counted cells of depth 3, rounded up. -/
def refcost (i j : ℕ) : ℕ :=
  cdiv (sumTo n (fun k => cond (inKK i j k && ne3 i j k) (P3 i j k * row i j k) 0)) (SC ^ 8)

/-! ### The cells of depth 2 -/

/-- The rule on the box `(i, j, k)`: `okD` with no deeper prime. -/
def ok3D (i j k : ℕ) : Bool := okD (e i + e j + e k + 3 * H) (dmax3 i j k) 0 (e k + H)

/-- The rule on the box `(i, j)` (`okIB`) and on the boxes `(i, j, k)` of its counted rows (`ok3D`). -/
def allowedD (i j : ℕ) : Bool :=
  okIB [cell i, cell j] && (List.range n).all (fun k => !(inKK i j k && ne3 i j k) || ok3D i j k)

/-- **The cell `(i, j)` is decomposed**: the rule passes its boxes and its refined cost is at most `bound2`. -/
def decD (i j : ℕ) : Bool := allowedD i j && Nat.ble (refcost i j) (bound2 (e i) (e j))

/-- The cost of the cell `(i, j)`, in units of `1/K`. -/
def costD (i j : ℕ) : ℕ := cond (cand i j) (cond (decD i j) (refcost i j) (bound2 (e i) (e j))) 0

/-- **The certificate's total**, in units of `1/K`. -/
def totalD : ℕ := sumTo n (fun i => sumTo n (fun j => costD i j))

/-- The sum of the costs of the rows `a ≤ i < b` over the columns `j₀ ≤ j < j₁`. -/
def rowsJD (a b j₀ j₁ : ℕ) : ℕ := sumTo (b - a) (fun i => sumTo (j₁ - j₀) (fun j => costD (a + i) (j₀ + j)))

end

end SieveDeep
