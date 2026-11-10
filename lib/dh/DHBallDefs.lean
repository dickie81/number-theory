import Mathlib.Data.Nat.Notation

/-!
# A fixed-point evaluator for Dirichlet polynomials at a complex point: the definitions

Integer arithmetic that the kernel can run (`decide +kernel`), for the zero of the Davenport–Heilbronn function at
height `24415` (`DHLocate5`) and the zero of the second Davenport–Heilbronn function at height `1650`
(`DHSecondZero`). A real number is held as a ball: a centre `c / S` and a radius `e / S`, with `S = 2^80`.
`DHBall` proves that each operation encloses what it should; this file has the definitions and the lemma that runs
compose (`run_trans`), so that the certificate files import nothing else.

* `B`, `CB`: real and complex balls, with `add`, `sub`, `mul`, `divNat`, `mulRat`.
* `expLoop`, `sqLoop`: the Taylor polynomial of `exp` of degree `13`, and repeated squaring.
* `Ctr`: the centre `c = reN/reD + i·imN/imD` of an evaluation, with the number `sq` of squarings.
* `redArg`, `expBall`, `term`: a ball for `n^{-c}` from a ball `L` for `log n`.
* `logStep n`: a ball for `log (n + 1) − log n`, from the series of `−log (1 − 1/(n + 1))`.
* `step`, `run`: the sums over the blocks `5m + 1, …, 5m + 4`, with the logarithm carried from block to block.
* `forceNat`, …, `St.force`: identities that make the kernel evaluate the state after each block.
-/

namespace DHBall

/-- The scale `2^80`. -/
def S : ℕ := 1208925819614629174706176

/-- A real ball: the reals `x` with `|x·S − c| ≤ e`. -/
structure B where
  /-- The centre, times `S`. -/
  c : Int
  /-- The radius, times `S`. -/
  e : ℕ
deriving DecidableEq

/-- The sum of two balls. -/
def B.add (a b : B) : B := ⟨a.c + b.c, a.e + b.e⟩

/-- The difference of two balls. -/
def B.sub (a b : B) : B := ⟨a.c - b.c, a.e + b.e⟩

/-- The negative of a ball. -/
def B.neg (a : B) : B := ⟨-a.c, a.e⟩

/-- The product of two balls, rounded down to the scale. -/
def B.mul (a b : B) : B :=
  ⟨a.c * b.c / (S : Int), (a.c.natAbs * b.e + b.c.natAbs * a.e + a.e * b.e) / S + 2⟩

/-- A ball divided by a positive natural number. -/
def B.divNat (a : B) (k : ℕ) : B := ⟨a.c / (k : Int), a.e / k + 2⟩

/-- A ball times the rational `p / q`. -/
def B.mulRat (a : B) (p q : ℕ) : B := ⟨a.c * (p : Int) / (q : Int), a.e * p / q + 2⟩

/-- A complex ball: a ball for the real part and one for the imaginary part. -/
structure CB where
  /-- The real part. -/
  re : B
  /-- The imaginary part. -/
  im : B
deriving DecidableEq

/-- The sum of two complex balls. -/
def CB.add (a b : CB) : CB := ⟨a.re.add b.re, a.im.add b.im⟩

/-- The difference of two complex balls. -/
def CB.sub (a b : CB) : CB := ⟨a.re.sub b.re, a.im.sub b.im⟩

/-- The product of two complex balls. -/
def CB.mul (a b : CB) : CB :=
  ⟨(a.re.mul b.re).sub (a.im.mul b.im), (a.re.mul b.im).add (a.im.mul b.re)⟩

/-- A complex ball divided by a positive natural number. -/
def CB.divNat (a : CB) (k : ℕ) : CB := ⟨a.re.divNat k, a.im.divNat k⟩

/-- A real ball times a complex ball. -/
def CB.smul (l : B) (a : CB) : CB := ⟨l.mul a.re, l.mul a.im⟩

/-- The ball of `1`. -/
def one : CB := ⟨⟨S, 0⟩, ⟨0, 0⟩⟩

/-- The ball of `0`. -/
def zero : CB := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩

/-- `expLoop v m fuel term sum` adds the terms `v^j / j!`, `m ≤ j < m + fuel`, to `sum`, where `term` holds
`v^m / m!`. -/
def expLoop (v : CB) : ℕ → ℕ → CB → CB → CB
  | _, 0, _, sum => sum
  | m, fuel + 1, term, sum => expLoop v (m + 1) fuel ((term.mul v).divNat (m + 1)) (sum.add term)

/-- `sqLoop j z` squares `z`, `j` times. -/
def sqLoop : ℕ → CB → CB
  | 0, z => z
  | j + 1, z => sqLoop j (z.mul z)

/-- A ball for `2π`, from Mathlib's twenty decimals of `π`. -/
def twoPi : B := ⟨7595904947272677161581685, 12091⟩

/-- The centre `c = reN/reD + i·imN/imD` of an evaluation, and the number `sq` of squarings: `n^{-c}` is computed as
`exp(−c·log n / 2^sq)` to the power `2^sq`, and the exponent has to lie in the unit disc for the ball to be a good
one, so `sq` is chosen with `Re c·log n ≤ 0.9·2^sq` for the `n` that occur. -/
structure Ctr where
  /-- The numerator of the real part. -/
  reN : ℕ
  /-- The denominator of the real part. -/
  reD : ℕ
  /-- The numerator of the imaginary part. -/
  imN : ℕ
  /-- The denominator of the imaginary part. -/
  imD : ℕ
  /-- The number of squarings. -/
  sq : ℕ

/-- The exponent `−c·log n`, reduced and divided by `2^sq`, from a ball `L` for `log n`: the real part is
`−σ·log n / 2^sq`, and the imaginary part `−(t·log n − 2πk) / 2^sq` with `k` the integer nearest to `t·log n / 2π`. -/
def redArg (p : Ctr) (L : B) : CB :=
  let y := L.mulRat p.imN p.imD
  let k : Int := (2 * y.c + twoPi.c) / (2 * twoPi.c)
  ⟨((L.mulRat p.reN p.reD).neg).divNat (2 ^ p.sq),
    (B.neg ⟨y.c - k * twoPi.c, y.e + k.natAbs * twoPi.e⟩).divNat (2 ^ p.sq)⟩

/-- The remainder of the Taylor polynomial of `exp` of degree `13` on the unit disc, times `S`, rounded up:
`15/(14·14!)·S ≤ 14857800560707`, about `1.2·10⁻¹¹`. -/
def expRem : ℕ := 14857800560707

/-- The ball `p` with `expRem` added to each radius. -/
def widen (p : CB) : CB := ⟨⟨p.re.c, p.re.e + expRem⟩, ⟨p.im.c, p.im.e + expRem⟩⟩

/-- A ball for `exp(v)^(2^j)`: the Taylor polynomial of degree `13` at `v`, squared `j` times. If `v` is not in the
unit disc, the ball is the unit square (which holds `exp(v)^(2^j)` whenever that has modulus at most `1`). -/
def expBall (j : ℕ) (v : CB) : CB :=
  if (v.re.c.natAbs + v.re.e) ^ 2 + (v.im.c.natAbs + v.im.e) ^ 2 ≤ S ^ 2 then
    sqLoop j (widen (expLoop v 0 14 one zero))
  else ⟨⟨0, S⟩, ⟨0, S⟩⟩

/-- A ball for `n^{-c}`, from a ball `L` for `log n`. -/
def term (p : Ctr) (L : B) : CB := expBall p.sq (redArg p L)

/-- `logSum n1 fuel i p acc` adds `⌊⌊S / n1^{j+1}⌋ / (j + 1)⌋`, `i ≤ j < i + fuel`, to `acc`, where `p = n1^i`. -/
def logSum (n1 : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, i, p, acc => logSum n1 fuel (i + 1) (p * n1) (acc + S / (p * n1) / (i + 1))

/-- The number of terms of the series for `log (n + 1) − log n`. -/
def logTerms (n : ℕ) : ℕ := if n < 16 then 64 else if n < 256 then 16 else if n < 4096 then 8 else 6

/-- A ball for `log (n + 1) − log n = −log (1 − 1/(n + 1))`. -/
def logStep (n : ℕ) : B :=
  ⟨((logSum (n + 1) (logTerms n) 0 1 0 + logTerms n : ℕ) : Int),
    logTerms n + S / ((n + 1) ^ logTerms n * n) + 1⟩

/-- An upper bound for `log² n · |n^{-c}| · S`, from balls for `log n` and `n^{-c}`. -/
def up (L : B) (T : CB) : ℕ :=
  (L.c.natAbs + L.e) ^ 2 * (T.re.c.natAbs + T.re.e + T.im.c.natAbs + T.im.e) / (S * S) + 1

/-- The state after the blocks `0, …, m − 1`: a ball for `log (5m + 1)`, balls for the four sums, and upper bounds
for the two sums of `log² n · |n^{-c}|`. -/
structure St where
  /-- `log (5m + 1)`. -/
  L : B
  /-- `Σ_{k<m} ((5k+1)^{-c} − (5k+4)^{-c})`. -/
  A : CB
  /-- `Σ_{k<m} ((5k+2)^{-c} − (5k+3)^{-c})`. -/
  B' : CB
  /-- `Σ_{k<m} (−log(5k+1)·(5k+1)^{-c} + log(5k+4)·(5k+4)^{-c})`. -/
  A1 : CB
  /-- `Σ_{k<m} (−log(5k+2)·(5k+2)^{-c} + log(5k+3)·(5k+3)^{-c})`. -/
  B1 : CB
  /-- An upper bound for `S·Σ_{k<m} (log²(5k+1)·|(5k+1)^{-c}| + log²(5k+4)·|(5k+4)^{-c}|)`. -/
  d2a : ℕ
  /-- The same for `5k + 2` and `5k + 3`. -/
  d2b : ℕ
deriving DecidableEq

/-- The block `5m + 1, …, 5m + 5`, at the centre `p`. -/
def step (p : Ctr) (m : ℕ) (st : St) : St :=
  let L1 := st.L
  let T1 := term p L1
  let L2 := L1.add (logStep (5 * m + 1))
  let T2 := term p L2
  let L3 := L2.add (logStep (5 * m + 2))
  let T3 := term p L3
  let L4 := L3.add (logStep (5 * m + 3))
  let T4 := term p L4
  let L5 := L4.add (logStep (5 * m + 4))
  { L := L5.add (logStep (5 * m + 5))
    A := (st.A.add T1).sub T4
    B' := (st.B'.add T2).sub T3
    A1 := (st.A1.sub (CB.smul L1 T1)).add (CB.smul L4 T4)
    B1 := (st.B1.sub (CB.smul L2 T2)).add (CB.smul L3 T3)
    d2a := st.d2a + up L1 T1 + up L4 T4
    d2b := st.d2b + up L2 T2 + up L3 T3 }

/-- `forceNat x f` is `f x`. The kernel evaluates `x` to a numeral before it applies `f`: without that, the state
after a thousand blocks is a thousand nested unevaluated terms, too deep for the kernel to evaluate at the end. -/
def forceNat {α : Type} (x : ℕ) (f : ℕ → α) : α :=
  match x with
  | 0 => f 0
  | k + 1 => f (k + 1)

/-- `forceInt x f` is `f x`, with `x` evaluated first. -/
def forceInt {α : Type} (x : Int) (f : Int → α) : α :=
  match x with
  | Int.ofNat n => forceNat n fun n => f (Int.ofNat n)
  | Int.negSucc n => forceNat n fun n => f (Int.negSucc n)

/-- `b.force f` is `f b`, with the centre and the radius evaluated first. -/
def B.force {α : Type} (b : B) (f : B → α) : α :=
  forceInt b.c fun c => forceNat b.e fun e => f ⟨c, e⟩

/-- `z.force f` is `f z`, with the two balls evaluated first. -/
def CB.force {α : Type} (z : CB) (f : CB → α) : α :=
  z.re.force fun re => z.im.force fun im => f ⟨re, im⟩

/-- `st.force f` is `f st`, with every number of the state evaluated first. -/
def St.force {α : Type} (st : St) (f : St → α) : α :=
  st.L.force fun L => st.A.force fun A => st.B'.force fun B' => st.A1.force fun A1 =>
    st.B1.force fun B1 => forceNat st.d2a fun d2a => forceNat st.d2b fun d2b =>
      f ⟨L, A, B', A1, B1, d2a, d2b⟩

/-- `run p m n st` applies the blocks `m, …, m + n − 1` to `st`, at the centre `p`, evaluating the state after each
block. -/
def run (p : Ctr) : ℕ → ℕ → St → St
  | _, 0, st => st
  | m, n + 1, st => (step p m st).force fun st' => run p (m + 1) n st'

/-- The state before the first block. -/
def init : St := ⟨⟨0, 0⟩, zero, zero, zero, zero, 0, 0⟩

theorem forceNat_eq {α : Type} (x : ℕ) (f : ℕ → α) : forceNat x f = f x := by
  cases x <;> rfl

theorem forceInt_eq {α : Type} (x : Int) (f : Int → α) : forceInt x f = f x := by
  cases x <;> simp only [forceInt, forceNat_eq]

theorem B.force_eq {α : Type} (b : B) (f : B → α) : b.force f = f b := by
  simp only [B.force, forceInt_eq, forceNat_eq]

theorem CB.force_eq {α : Type} (z : CB) (f : CB → α) : z.force f = f z := by
  simp only [CB.force, B.force_eq]

theorem St.force_eq {α : Type} (st : St) (f : St → α) : st.force f = f st := by
  simp only [St.force, B.force_eq, CB.force_eq, forceNat_eq]

theorem run_succ (p : Ctr) (m n : ℕ) (st : St) : run p m (n + 1) st = run p (m + 1) n (step p m st) := by
  rw [run, St.force_eq]

/-- Blocks run one after the other. -/
theorem run_add (p : Ctr) : ∀ (n1 m n2 : ℕ) (st : St),
    run p m (n1 + n2) st = run p (m + n1) n2 (run p m n1 st)
  | 0, m, n2, st => by rw [Nat.zero_add, Nat.add_zero, run]
  | n1 + 1, m, n2, st => by
    have e1 : n1 + 1 + n2 = n1 + n2 + 1 := by omega
    have e2 : m + (n1 + 1) = m + 1 + n1 := by omega
    rw [e1, run_succ, run_succ, run_add p n1, e2]

/-- Two runs, one after the other, are one run. -/
theorem run_trans {p : Ctr} {m n1 n2 : ℕ} {st st1 st2 : St} (h1 : run p m n1 st = st1)
    (h2 : run p (m + n1) n2 st1 = st2) : run p m (n1 + n2) st = st2 := by
  rw [run_add, h1, h2]

end DHBall
