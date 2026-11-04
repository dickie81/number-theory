# Lagarias's criterion for the Riemann hypothesis

**Lean:** `LagariasCriterion.lagarias_criterion` and `LagariasCriterion.lagarias_upto_5040`
(`lib/core/LagariasCriterion.lean`):

```lean
theorem lagarias_criterion (hF : RobinForward) (hC : RobinConverse) :
    RiemannHypothesis ↔ LagariasInequality

theorem lagarias_upto_5040 {n : ℕ} (hn : 1 ≤ n) (h : n ≤ 5040) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ lagariasBound n
```

with `lagariasBound n = H_n + e^{H_n} log H_n` for `H_n = Σ_{k ≤ n} 1/k` (Mathlib's `harmonic n`), `LagariasInequality`
the statement `σ(n) ≤ lagariasBound n` for every `n ≥ 1`, `σ = ArithmeticFunction.sigma 1` the sum of divisors,
`RiemannHypothesis` Mathlib's, and the two hypotheses

```lean
def RobinForward : Prop :=
  RiemannHypothesis → ∀ n : ℕ, 5040 < n →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp eulerMascheroniConstant * n * Real.log (Real.log n)

def RobinConverse : Prop :=
  ¬ RiemannHypothesis → ∃ b c : ℝ, b < 1 ∧ 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N < n ∧
    Real.exp eulerMascheroniConstant * n * Real.log (Real.log n) + c * n / Real.log n ^ b ≤
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ)
```

In words: given Robin's theorem in its two directions, the Riemann hypothesis holds if and only if
`σ(n) ≤ H_n + e^{H_n} log H_n` for every `n ≥ 1`; and, with no hypothesis, that inequality holds for every
`1 ≤ n ≤ 5040`. The theorems depend on `propext`, `Classical.choice` and `Quot.sound` only
(`lib/check/CheckAll.lean`).

## Source

- J. C. Lagarias, *An elementary problem equivalent to the Riemann hypothesis*, Amer. Math. Monthly 109 (2002),
  534–543. Theorem 1.1 is the criterion; its proof deduces it from Robin's theorem, with the inequality for small `n`
  checked by computation.
- G. Robin, *Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann*, J. Math. Pures Appl. (9) 63
  (1984), 187–213. Théorème 1: RH holds if and only if `σ(n) < e^γ n log log n` for every `n ≥ 5041`. Its proof of
  the converse shows that if RH fails there are `β < 1/2` and `C > 0` with
  `σ(n) ≥ e^γ n log log n + C n log log n/(log n)^β` for infinitely many `n`.

Nothing in this library claims either result as its own. Robin's theorem is not proved here: the direction under RH
needs explicit bounds for `θ(x) − x` under RH (Schoenfeld's), and the converse an Ω-argument on the error term of
Mertens' product formula at the colossally abundant numbers; both are hypotheses, `RobinForward` and `RobinConverse`.

## How the Lean statement differs

- **Robin's theorem is assumed, not proved**, as the two statements above. `RobinConverse` is weaker than what
  Robin proves: it asks for some `b < 1` and no factor `log log n`, which Robin's `β < 1/2` with the factor implies
  (`log log n ≥ 1` for `n ≥ 16`). Lagarias's deduction needs only `b < 1`, because the gap between his bound and
  Robin's is `O(n/log n)`.
- **Equality.** Lagarias states that equality holds only for `n = 1`; this is not formalised.
- **The strict inequality.** `RobinForward` is stated for `n > 5040` with `<`, as in Robin; the criterion itself uses
  `≤`, as in Lagarias.

## How it was done

- **The certificate for `1 ≤ n ≤ 5040`** (`check_all`, from twenty pieces of `252` values, `checkFrom_1`, …,
  `checkFrom_4789`, each a `decide +kernel`, joined by `checkFrom_append`). `lagariasLower n` is a rational below
  `H_n + e^{H_n} log H_n`: from a rational `L ≤ H_n` with `L ≥ 1`, it is `L + expLower L · logLower L`, where
  `expLower` is the Taylor polynomial of `e^x` with twenty-five terms (`Real.sum_le_exp_of_nonneg`) and `logLower y`
  is `k·0.6931471803 + 2 Σ_{j < 8} t^{2j+1}/(2j+1)` for `y = 2^k y'`, `1 ≤ y' < 2`, `t = (y' − 1)/(y' + 1)`
  (Mathlib's `Real.log_two_gt_d9` and `Real.hasSum_log_sub_log_of_abs_lt_one`). The rational `L` is `H_n` itself for
  `n ≤ 12`, where the margin is small (at `n = 2, 4, 6, 12` the bound below fails), and beyond it is
  `logLower n + 0.57672` rounded down to a multiple of `2^{−40}`, from `H_n > log n + γ` (Mathlib's
  `eulerMascheroniConstant_lt_eulerMascheroniSeq'`) and `γ > H_1023 − log 1024 > 0.57672`
  (`eulerMascheroniSeq_lt_eulerMascheroniConstant`, with `H_1023` evaluated by the kernel). Monotonicity of `e^x` and
  `log` then gives `lagariasLower n ≤ lagariasBound n` (`lagariasLower_le`), and the kernel checks
  `σ(n) ≤ lagariasLower n` for each `n ≤ 5040` in exact rational arithmetic, with `σ(n)` by trial division up to `√n`
  (`sigmaFast`, proved equal to Mathlib's `σ` in `sigmaFast_eq_sigma`). The margin is smallest at `n = 1` (equality)
  and then about `0.5%` at `n = 24`. The check takes about ten minutes of one core and about 2 GiB of private
  memory for a piece, so the module is marked heavy for `scripts/build.sh`.
- **Beyond `5040`, under RH** (`robin_le_lagarias`): `e^γ n log log n ≤ e^{H_n} log H_n` for `n ≥ 3`, since
  `H_n > log n + γ`, so Robin's inequality gives Lagarias's.
- **Beyond `5040`, without RH** (`lagariasBound_le`, `rh_of_lagarias`): `H_n < log n + γ + 1/n` (Mathlib's
  `eulerMascheroniSeq_lt_eulerMascheroniConstant`), `e^{1/n} ≤ 1 + 2/n` and `log(log n + 1) ≤ log log n + 1/log n`
  give `H_n + e^{H_n} log H_n ≤ e^γ n log log n + 60 n/log n` for `n ≥ 16`, with `(log n)² ≤ 4n` to absorb the lower
  terms. For `n > exp((60/c)^{1/(1−b)})` the leftover `60 n/log n` is below `c n/(log n)^b`, so an `n` from
  `RobinConverse` beyond that height violates Lagarias's inequality.

## What is not here

Robin's theorem, in either direction. Its direction under RH would need an explicit form of the prime number theorem
under RH, such as Schoenfeld's `|θ(x) − x| < √x log² x/(8π)` for `x ≥ 599`, and Robin's analysis of the colossally
abundant numbers; the library has neither. Its unconditional companion, `σ(n) ≤ e^γ n log log n + 0.6483 n/log log n`
for `n ≥ 3`, is not here either. What the half-plane `Re s > 11/12` gives unconditionally,
`σ(n) ≤ e^γ n log log n (1 + O((log n)^{−1/12+ε}))`, improves on that companion only for `n` beyond about `e^{10²²}`,
so it was not taken.
