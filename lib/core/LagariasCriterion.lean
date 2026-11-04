import Mathlib
-- heavy: a kernel check in twenty pieces, each about 2 GiB of private memory; scripts/build.sh runs at most two heavy modules at once

/-! # Lagarias's criterion for the Riemann hypothesis, from Robin's theorem

Plain statement. Let `H_n = Σ_{k ≤ n} 1/k` and `σ(n) = Σ_{d ∣ n} d`. J. C. Lagarias (2002) proved that the Riemann
hypothesis holds if and only if `σ(n) ≤ H_n + e^{H_n} log H_n` for every `n ≥ 1`, from G. Robin's theorem (1984):
under RH, `σ(n) < e^γ n log log n` for every `n > 5040`, and if RH fails, `σ(n) ≥ e^γ n log log n + c n/(log n)^b`
for infinitely many `n`, for some `b < 1` and `c > 0`. Here Robin's two statements are hypotheses (`RobinForward`,
`RobinConverse`) and Lagarias's deduction is the theorem (`lagarias_criterion`). Its pieces are unconditional:

* `lagarias_upto_5040`: the inequality for `1 ≤ n ≤ 5040`, by a certificate the kernel checks in twenty pieces
  (`checkFrom_1`, …, `checkFrom_4789`, joined by `checkFrom_append`): a rational lower bound `lagariasLower n` for
  `H_n + e^{H_n} log H_n`, from the exact `H_n` for `n ≤ 12` and from `H_n > log n + γ` beyond, with `log` by the
  series of `artanh` after a reduction by powers of `2`, `γ` from below by `H_1023 − 10 log 2`, and `e^x` by its
  Taylor polynomial, compared in exact arithmetic with `σ(n)` by trial division up to `√n` (`sigmaFast`, proved
  equal to `σ`);
* `robin_le_lagarias`: `e^γ n log log n ≤ e^{H_n} log H_n` for `n ≥ 3`, since `H_n > log n + γ`;
* `lagariasBound_le`: `H_n + e^{H_n} log H_n ≤ e^γ n log log n + 60 n/log n` for `n ≥ 16`, since
  `H_n < log n + γ + 1/n`; and `60 n/log n` is below `c n/(log n)^b` once `log n > (60/c)^{1/(1−b)}`.
-/

open Real Finset

namespace LagariasCriterion

/-! ## The statement -/

/-- Lagarias's bound `H_n + e^{H_n} log H_n`. -/
noncomputable def lagariasBound (n : ℕ) : ℝ :=
  (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n)

/-- **Lagarias's inequality**: `σ(n) ≤ H_n + e^{H_n} log H_n` for every `n ≥ 1`. -/
def LagariasInequality : Prop :=
  ∀ n : ℕ, 1 ≤ n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ lagariasBound n

/-- **Robin's theorem under RH**: `σ(n) < e^γ n log log n` for every `n > 5040`. A hypothesis. -/
def RobinForward : Prop :=
  RiemannHypothesis → ∀ n : ℕ, 5040 < n →
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) <
      Real.exp eulerMascheroniConstant * n * Real.log (Real.log n)

/-- **Robin's theorem without RH**, in the form Lagarias's deduction needs: if RH fails, there are `b < 1` and
`c > 0` with `σ(n) ≥ e^γ n log log n + c n/(log n)^b` for infinitely many `n`. A hypothesis. -/
def RobinConverse : Prop :=
  ¬ RiemannHypothesis → ∃ b c : ℝ, b < 1 ∧ 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N < n ∧
    Real.exp eulerMascheroniConstant * n * Real.log (Real.log n) + c * n / Real.log n ^ b ≤
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ)

/-! ## Rational lower bounds that the kernel can evaluate -/

/-- `0.6931471803 < log 2` (Mathlib's `Real.log_two_gt_d9`). -/
def log2Lo : ℚ := 6931471803 / 10000000000

/-- `log 2 < 0.6931471808` (Mathlib's `Real.log_two_lt_d9`). -/
def log2Hi : ℚ := 6931471808 / 10000000000

theorem log2Lo_lt : (log2Lo : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9
  norm_num [log2Lo] at this ⊢
  linarith

theorem log_two_lt_log2Hi : Real.log 2 < (log2Hi : ℝ) := by
  have := Real.log_two_lt_d9
  norm_num [log2Hi] at this ⊢
  linarith

/-- `(2 Σ_{j < J} t^{2j+1}/(2j+1), t^{2J+1})`: the partial sums of the series of `log(1 + t) − log(1 − t) = 2 artanh t`
with the next odd power of `t` carried along, so that each step is one multiplication by `t²`. -/
def atanhPair (t : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, t)
  | J + 1 =>
    ((atanhPair t J).1 + 2 * (atanhPair t J).2 / ((2 * J + 1 : ℕ) : ℚ), (atanhPair t J).2 * (t * t))

/-- The partial sums `2 Σ_{j < J} t^{2j+1}/(2j+1)` of the series of `log(1 + t) − log(1 − t) = 2 artanh t`. -/
def atanhSeries (t : ℚ) (J : ℕ) : ℚ := (atanhPair t J).1

theorem atanhPair_snd (t : ℚ) (J : ℕ) : (atanhPair t J).2 = t ^ (2 * J + 1) := by
  induction J with
  | zero => simp [atanhPair]
  | succ J ih => simp only [atanhPair, ih]; ring

theorem atanhSeries_eq (t : ℚ) (J : ℕ) :
    (atanhSeries t J : ℝ) = ∑ j ∈ range J, (2 : ℝ) * (1 / (2 * (j : ℝ) + 1)) * (t : ℝ) ^ (2 * j + 1) := by
  induction J with
  | zero => simp [atanhSeries, atanhPair]
  | succ J ih =>
    rw [sum_range_succ, ← ih]
    simp only [atanhSeries, atanhPair, atanhPair_snd]
    push_cast
    ring

theorem atanhSeries_nonneg {t : ℚ} (ht : 0 ≤ t) (J : ℕ) : 0 ≤ atanhSeries t J := by
  induction J with
  | zero => simp [atanhSeries, atanhPair]
  | succ J ih =>
    simp only [atanhSeries, atanhPair, atanhPair_snd] at ih ⊢
    exact add_nonneg ih (by positivity)

/-- The partial sums are below the series: `atanhSeries t J ≤ log(1 + t) − log(1 − t)` for `0 ≤ t < 1`. -/
theorem atanhSeries_le {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t < 1) (J : ℕ) :
    (atanhSeries t J : ℝ) ≤ Real.log (1 + t) - Real.log (1 - t) := by
  rw [atanhSeries_eq]
  have h0 : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have h : |(t : ℝ)| < 1 := by rw [abs_of_nonneg h0]; exact_mod_cast ht1
  exact sum_le_hasSum (range J) (fun j _ => by positivity) (Real.hasSum_log_sub_log_of_abs_lt_one h)

/-- The `k` with `2^k ≤ y < 2^{k+1}`, for `y ≥ 1`. -/
def dyadic (y : ℚ) : ℕ := Nat.log 2 (Int.toNat ⌊y⌋)

theorem dyadic_spec {y : ℚ} (hy : 1 ≤ y) : (2 : ℚ) ^ dyadic y ≤ y ∧ y < 2 ^ (dyadic y + 1) := by
  have hfl : (1 : ℤ) ≤ ⌊y⌋ := Int.le_floor.2 (by simpa using hy)
  set m := Int.toNat ⌊y⌋ with hm
  have hm1 : 1 ≤ m := by omega
  have hmz : (m : ℤ) = ⌊y⌋ := Int.toNat_of_nonneg (by omega)
  have hmq : (m : ℚ) ≤ y := by
    have := Int.floor_le y
    rw [← hmz] at this
    exact_mod_cast this
  have hym : y < m + 1 := by
    have := Int.lt_floor_add_one y
    rw [← hmz] at this
    exact_mod_cast this
  constructor
  · have := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
    calc (2 : ℚ) ^ dyadic y = ((2 ^ Nat.log 2 m : ℕ) : ℚ) := by simp [dyadic, hm]
      _ ≤ m := by exact_mod_cast this
      _ ≤ y := hmq
  · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    calc y < m + 1 := hym
      _ ≤ ((2 ^ (Nat.log 2 m + 1) : ℕ) : ℚ) := by exact_mod_cast this
      _ = 2 ^ (dyadic y + 1) := by simp [dyadic, hm]

/-- A rational lower bound for `log y`, `y ≥ 1`: `k log 2 + 2 artanh((y' − 1)/(y' + 1))` with `y' = y/2^k ∈ [1, 2)`,
`log 2` from below by `log2Lo` and `artanh` by eight terms of its series. -/
def logLower (y : ℚ) : ℚ :=
  dyadic y * log2Lo + atanhSeries ((y / 2 ^ dyadic y - 1) / (y / 2 ^ dyadic y + 1)) 8

theorem logLower_nonneg {y : ℚ} (hy : 1 ≤ y) : 0 ≤ logLower y := by
  have h := (dyadic_spec hy).1
  have hy' : 1 ≤ y / 2 ^ dyadic y := by rw [le_div_iff₀ (by positivity)]; linarith
  unfold logLower
  have : 0 ≤ (y / 2 ^ dyadic y - 1) / (y / 2 ^ dyadic y + 1) := by
    apply div_nonneg <;> linarith
  have := atanhSeries_nonneg this 8
  have : (0 : ℚ) ≤ log2Lo := by norm_num [log2Lo]
  positivity

theorem logLower_le {y : ℚ} (hy : 1 ≤ y) : (logLower y : ℝ) ≤ Real.log y := by
  obtain ⟨h1, h2⟩ := dyadic_spec hy
  set k := dyadic y with hk
  have hy' : 1 ≤ y / 2 ^ k := by rw [le_div_iff₀ (by positivity)]; linarith
  have hy'2 : y / 2 ^ k < 2 := by rw [div_lt_iff₀ (by positivity)]; rw [pow_succ] at h2; linarith
  set t : ℚ := (y / 2 ^ k - 1) / (y / 2 ^ k + 1) with ht
  have ht0 : 0 ≤ t := by apply div_nonneg <;> linarith
  have ht1 : t < 1 := by rw [ht, div_lt_one (by linarith)]; linarith
  have hy'pos : (0 : ℝ) < ((y / 2 ^ k : ℚ) : ℝ) := by exact_mod_cast (by linarith : (0 : ℚ) < y / 2 ^ k)
  -- `log y = k log 2 + log y'` and `log y' = log (1 + t) − log (1 − t)`
  have hyR : (y : ℝ) = 2 ^ k * ((y / 2 ^ k : ℚ) : ℝ) := by push_cast; field_simp
  have hlog : Real.log y = k * Real.log 2 + Real.log ((y / 2 ^ k : ℚ) : ℝ) := by
    rw [hyR, Real.log_mul (by positivity) hy'pos.ne', Real.log_pow]
  have hlog' : Real.log ((y / 2 ^ k : ℚ) : ℝ) = Real.log (1 + (t : ℝ)) - Real.log (1 - (t : ℝ)) := by
    have hpos : (0 : ℝ) < 1 - t := by
      have : (t : ℝ) < 1 := by exact_mod_cast ht1
      linarith
    rw [← Real.log_div (by positivity) hpos.ne']
    congr 1
    rw [ht]; push_cast
    have : ((y / 2 ^ k : ℚ) : ℝ) + 1 ≠ 0 := by
      have : (1 : ℝ) ≤ ((y / 2 ^ k : ℚ) : ℝ) := by exact_mod_cast hy'
      linarith
    field_simp
    ring
  have hser := atanhSeries_le ht0 ht1 8
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have h2 := log2Lo_lt
  unfold logLower
  rw [← hk, ← ht, hlog, hlog']
  push_cast
  nlinarith

/-- `(Σ_{i < K} x^i/i!, x^K/K!)`: the partial sums of the series of `e^x` with the next term carried along, so
that each step is one multiplication by `x` and one division. -/
def expPair (x : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 1)
  | K + 1 => ((expPair x K).1 + (expPair x K).2, (expPair x K).2 * x / ((K + 1 : ℕ) : ℚ))

/-- The Taylor polynomial `Σ_{i < K} x^i/i!`, a lower bound for `e^x` when `x ≥ 0`. -/
def expLower (x : ℚ) (K : ℕ) : ℚ := (expPair x K).1

theorem expPair_snd (x : ℚ) (K : ℕ) : (expPair x K).2 = x ^ K / K.factorial := by
  induction K with
  | zero => simp [expPair]
  | succ K ih =>
    simp only [expPair, ih, Nat.factorial_succ, pow_succ]
    push_cast
    rw [div_mul_eq_mul_div, div_div]
    ring

theorem expLower_eq (x : ℚ) (K : ℕ) :
    (expLower x K : ℝ) = ∑ i ∈ range K, (x : ℝ) ^ i / (i.factorial : ℝ) := by
  induction K with
  | zero => simp [expLower, expPair]
  | succ K ih =>
    rw [sum_range_succ, ← ih]
    simp only [expLower, expPair, expPair_snd]
    push_cast
    ring

theorem expLower_le {x : ℚ} (hx : 0 ≤ x) (K : ℕ) : (expLower x K : ℝ) ≤ Real.exp x := by
  rw [expLower_eq]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hx) K

/-- A rational below `γ`: `γ > H_1023 − log 1024 > 0.57672`. -/
def gammaLower : ℚ := 57672 / 100000

theorem gammaLower_lt : (gammaLower : ℝ) < eulerMascheroniConstant := by
  have h := eulerMascheroniSeq_lt_eulerMascheroniConstant 1023
  unfold eulerMascheroniSeq at h
  have hlog : Real.log ((1023 : ℕ) + 1) < 10 * (log2Hi : ℝ) := by
    have : ((1023 : ℕ) : ℝ) + 1 = 2 ^ 10 := by norm_num
    rw [this, Real.log_pow]
    have := log_two_lt_log2Hi
    push_cast
    linarith
  have hq : gammaLower ≤ harmonic 1023 - 10 * log2Hi := by decide +kernel
  have hq' : (gammaLower : ℝ) ≤ (harmonic 1023 : ℝ) - 10 * (log2Hi : ℝ) := by exact_mod_cast hq
  linarith

/-- `x` rounded down to a multiple of `2^{-40}`, to keep the numbers of the certificate small. -/
def roundDown (x : ℚ) : ℚ := (⌊x * 2 ^ 40⌋ : ℚ) / 2 ^ 40

theorem roundDown_le (x : ℚ) : roundDown x ≤ x := by
  unfold roundDown
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

/-- A rational lower bound for `H_n`: `H_n` itself for `n ≤ 12`, else `logLower n + gammaLower` rounded down. -/
def harmonicLower (n : ℕ) : ℚ :=
  if n ≤ 12 then harmonic n else roundDown (logLower n + gammaLower)

/-- `H_n > log n + γ` for `n ≥ 1` (Mathlib's `eulerMascheroniConstant_lt_eulerMascheroniSeq'`). -/
theorem log_add_gamma_lt_harmonic {n : ℕ} (hn : 1 ≤ n) :
    Real.log n + eulerMascheroniConstant < harmonic n := by
  have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [eulerMascheroniSeq', show n ≠ 0 by omega, ite_false] at h
  linarith

theorem harmonicLower_le {n : ℕ} (hn : 1 ≤ n) : (harmonicLower n : ℝ) ≤ harmonic n := by
  unfold harmonicLower
  split_ifs with h
  · exact le_rfl
  · have h0 : (roundDown (logLower n + gammaLower) : ℝ) ≤ ((logLower n + gammaLower : ℚ) : ℝ) := by
      exact_mod_cast roundDown_le _
    have h1 := logLower_le (y := n) (by exact_mod_cast hn)
    have h2 := gammaLower_lt
    have h3 := log_add_gamma_lt_harmonic hn
    push_cast at h0 h1 ⊢
    linarith

/-- The lower bound for `H_n + e^{H_n} log H_n` from `harmonicLower n`, with twenty-five Taylor terms. -/
def lagariasLower (n : ℕ) : ℚ :=
  harmonicLower n + expLower (harmonicLower n) 25 * logLower (harmonicLower n)

theorem lagariasLower_le {n : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ harmonicLower n) :
    (lagariasLower n : ℝ) ≤ lagariasBound n := by
  have hLH : (harmonicLower n : ℝ) ≤ harmonic n := harmonicLower_le hn
  have hL1 : (1 : ℝ) ≤ harmonicLower n := by exact_mod_cast hL
  have he : (expLower (harmonicLower n) 25 : ℝ) ≤ Real.exp (harmonic n) :=
    (expLower_le (by linarith) 25).trans (Real.exp_le_exp.2 hLH)
  have hl : (logLower (harmonicLower n) : ℝ) ≤ Real.log (harmonic n) :=
    (logLower_le hL).trans (Real.log_le_log (by linarith) hLH)
  have hl0 : (0 : ℝ) ≤ logLower (harmonicLower n) := by exact_mod_cast logLower_nonneg hL
  have hprod := mul_le_mul he hl hl0 (Real.exp_pos _).le
  unfold lagariasLower lagariasBound
  push_cast
  linarith

/-! ## The sum of the divisors by trial division up to `√n` -/

/-- The contribution of `d` to `σ(n)`: `d` and its cofactor `n/d`, the latter dropped when `d² = n`, and `0` unless
`d ∣ n`. -/
def divPair (n d : ℕ) : ℕ := if d ∣ n then d + (if d * d = n then 0 else n / d) else 0

/-- `Σ_j divPair n (d + j)` over `j < fuel` with `(d + j)² ≤ n`, stopping at the first `d` with `d² > n`. -/
def sigmaLoop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, d => if n < d * d then 0 else divPair n d + sigmaLoop n fuel (d + 1)

/-- `σ(n)` by trial division up to `√n`. -/
def sigmaFast (n : ℕ) : ℕ := sigmaLoop n n 1

theorem sigmaLoop_eq (n : ℕ) : ∀ (fuel d : ℕ),
    sigmaLoop n fuel d = ∑ j ∈ range fuel, if n < (d + j) * (d + j) then 0 else divPair n (d + j)
  | 0, _ => by simp [sigmaLoop]
  | fuel + 1, d => by
    rw [sum_range_succ', sigmaLoop, sigmaLoop_eq n fuel (d + 1)]
    simp only [add_zero]
    have e : ∀ k : ℕ, d + 1 + k = d + (k + 1) := fun k => by omega
    simp only [e]
    split_ifs with h
    · symm
      rw [add_zero]
      refine sum_eq_zero fun j _ => ?_
      have hle : d * d ≤ (d + (j + 1)) * (d + (j + 1)) := Nat.mul_le_mul (by omega) (by omega)
      have hj : n < (d + (j + 1)) * (d + (j + 1)) := lt_of_lt_of_le h hle
      simp [hj]
    · rw [add_comm]

theorem sigmaFast_eq_sum (n : ℕ) :
    sigmaFast n = ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (d + if d * d = n then 0 else n / d) := by
  unfold sigmaFast
  rw [sigmaLoop_eq, Nat.divisors, Finset.sum_filter, Finset.sum_filter, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  refine sum_congr rfl fun j _ => ?_
  unfold divPair
  split_ifs <;> first | rfl | omega

/-- The divisors above `√n` are the cofactors of those below: `Σ_{d ∣ n, d² > n} d = Σ_{d ∣ n, d² < n} n/d`. -/
theorem sum_divisors_above_eq (n : ℕ) :
    ∑ d ∈ n.divisors, (if n < d * d then d else 0) = ∑ d ∈ n.divisors, (if d * d < n then n / d else 0) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  rw [← Nat.sum_div_divisors n (fun d => if d * d < n then n / d else 0)]
  refine sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  obtain ⟨e, rfl⟩ := hdn
  have he0 : 0 < e := Nat.pos_of_mul_pos_left hn
  have h1 : d * e / d = e := Nat.mul_div_cancel_left e hd0
  rw [h1, Nat.mul_div_cancel d he0]
  have : e * e < d * e ↔ d * e < d * d := by
    rw [Nat.mul_lt_mul_right he0, Nat.mul_lt_mul_left hd0]
  by_cases h : e * e < d * e
  · simp [h, this.1 h]
  · have h' : ¬ d * e < d * d := fun h' => h (this.2 h')
    simp [h, h']

/-- **`sigmaFast` is `σ`.** -/
theorem sigmaFast_eq_sigma (n : ℕ) : sigmaFast n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply, sigmaFast_eq_sum, Finset.sum_filter]
  have h1 : ∑ d ∈ n.divisors, (if d * d ≤ n then d else 0) + ∑ d ∈ n.divisors, (if n < d * d then d else 0)
      = ∑ d ∈ n.divisors, d := by
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    split_ifs <;> omega
  have h2 : ∑ d ∈ n.divisors, (if d * d ≤ n then (if d * d = n then 0 else n / d) else 0)
      = ∑ d ∈ n.divisors, (if d * d < n then n / d else 0) := by
    refine sum_congr rfl fun d _ => ?_
    split_ifs <;> omega
  calc ∑ d ∈ n.divisors, (if d * d ≤ n then d + (if d * d = n then 0 else n / d) else 0)
      = ∑ d ∈ n.divisors, (if d * d ≤ n then d else 0) +
          ∑ d ∈ n.divisors, (if d * d ≤ n then (if d * d = n then 0 else n / d) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine sum_congr rfl fun d _ => ?_
        split_ifs <;> omega
    _ = ∑ d ∈ n.divisors, (if d * d ≤ n then d else 0) + ∑ d ∈ n.divisors, (if n < d * d then d else 0) := by
        rw [h2, sum_divisors_above_eq]
    _ = ∑ d ∈ n.divisors, d := h1

/-! ## The certificate: `1 ≤ n ≤ 5040` -/

/-- The check for one `m`: `1 ≤ harmonicLower m` and `σ(m) ≤ lagariasLower m`, in exact arithmetic. -/
def check (m : ℕ) : Bool :=
  decide (1 ≤ harmonicLower m) && decide ((sigmaFast m : ℚ) ≤ lagariasLower m)

/-- The check for `a ≤ m ≤ a + k`. -/
def checkFrom (a : ℕ) : ℕ → Bool
  | 0 => check a
  | k + 1 => checkFrom a k && check (a + k + 1)

theorem checkFrom_spec {a k : ℕ} (h : checkFrom a k = true) {m : ℕ} (hm1 : a ≤ m) (hm2 : m ≤ a + k) :
    check m = true := by
  induction k with
  | zero => obtain rfl : m = a := by omega
            simpa [checkFrom] using h
  | succ k ih =>
    simp only [checkFrom, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge m (a + k + 1) with h' | h'
    · exact ih h.1 (by omega)
    · obtain rfl : m = a + k + 1 := by omega
      exact h.2

theorem check_spec {m : ℕ} (h : check m = true) :
    1 ≤ harmonicLower m ∧ ((ArithmeticFunction.sigma 1 m : ℕ) : ℚ) ≤ lagariasLower m := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, sigmaFast_eq_sigma] at h
  exact h

/-- Two consecutive pieces of the check join. -/
theorem checkFrom_append {a k k' : ℕ} (h1 : checkFrom a k = true) (h2 : checkFrom (a + k + 1) k' = true) :
    checkFrom a (k + k' + 1) = true := by
  induction k' with
  | zero =>
    simp only [checkFrom, Bool.and_eq_true] at h2 ⊢
    exact ⟨h1, h2⟩
  | succ k' ih =>
    simp only [checkFrom, Bool.and_eq_true] at h2
    have e : k + (k' + 1) + 1 = k + k' + 1 + 1 := by omega
    rw [e, checkFrom, Bool.and_eq_true]
    refine ⟨ih h2.1, ?_⟩
    have e' : a + (k + k' + 1) + 1 = a + k + 1 + k' + 1 := by omega
    rw [e']
    exact h2.2

/-- **The certificate**, checked by the kernel in twenty pieces of `252`. -/
theorem checkFrom_1 : checkFrom 1 251 = true := by decide +kernel
theorem checkFrom_253 : checkFrom 253 251 = true := by decide +kernel
theorem checkFrom_505 : checkFrom 505 251 = true := by decide +kernel
theorem checkFrom_757 : checkFrom 757 251 = true := by decide +kernel
theorem checkFrom_1009 : checkFrom 1009 251 = true := by decide +kernel
theorem checkFrom_1261 : checkFrom 1261 251 = true := by decide +kernel
theorem checkFrom_1513 : checkFrom 1513 251 = true := by decide +kernel
theorem checkFrom_1765 : checkFrom 1765 251 = true := by decide +kernel
theorem checkFrom_2017 : checkFrom 2017 251 = true := by decide +kernel
theorem checkFrom_2269 : checkFrom 2269 251 = true := by decide +kernel
theorem checkFrom_2521 : checkFrom 2521 251 = true := by decide +kernel
theorem checkFrom_2773 : checkFrom 2773 251 = true := by decide +kernel
theorem checkFrom_3025 : checkFrom 3025 251 = true := by decide +kernel
theorem checkFrom_3277 : checkFrom 3277 251 = true := by decide +kernel
theorem checkFrom_3529 : checkFrom 3529 251 = true := by decide +kernel
theorem checkFrom_3781 : checkFrom 3781 251 = true := by decide +kernel
theorem checkFrom_4033 : checkFrom 4033 251 = true := by decide +kernel
theorem checkFrom_4285 : checkFrom 4285 251 = true := by decide +kernel
theorem checkFrom_4537 : checkFrom 4537 251 = true := by decide +kernel
theorem checkFrom_4789 : checkFrom 4789 251 = true := by decide +kernel

theorem checkFrom_all : checkFrom 1 5039 = true := by
  have h := checkFrom_append checkFrom_1 checkFrom_253
  have h := checkFrom_append h checkFrom_505
  have h := checkFrom_append h checkFrom_757
  have h := checkFrom_append h checkFrom_1009
  have h := checkFrom_append h checkFrom_1261
  have h := checkFrom_append h checkFrom_1513
  have h := checkFrom_append h checkFrom_1765
  have h := checkFrom_append h checkFrom_2017
  have h := checkFrom_append h checkFrom_2269
  have h := checkFrom_append h checkFrom_2521
  have h := checkFrom_append h checkFrom_2773
  have h := checkFrom_append h checkFrom_3025
  have h := checkFrom_append h checkFrom_3277
  have h := checkFrom_append h checkFrom_3529
  have h := checkFrom_append h checkFrom_3781
  have h := checkFrom_append h checkFrom_4033
  have h := checkFrom_append h checkFrom_4285
  have h := checkFrom_append h checkFrom_4537
  have h := checkFrom_append h checkFrom_4789
  exact h

theorem check_all {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 5040) : check n = true :=
  checkFrom_spec checkFrom_all h1 (by omega)

/-- **Lagarias's inequality for `1 ≤ n ≤ 5040`.** -/
theorem lagarias_upto_5040 {n : ℕ} (hn : 1 ≤ n) (h : n ≤ 5040) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ lagariasBound n := by
  obtain ⟨hL, hσ⟩ := check_spec (check_all hn h)
  have h1 := lagariasLower_le hn hL
  have h2 : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (lagariasLower n : ℝ) := by exact_mod_cast hσ
  exact h2.trans h1

/-! ## Beyond `5040`: the comparison with Robin's bound -/

theorem harmonic_nonneg' (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
  have h1 := log_add_one_le_harmonic n
  have h2 : (0 : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 n)
  linarith

/-- `log n > 1` for `n ≥ 3`. -/
theorem one_lt_log {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- **Robin's bound is below Lagarias's**: `e^γ n log log n ≤ e^{H_n} log H_n` for `n ≥ 3`. -/
theorem robin_le_lagarias {n : ℕ} (hn : 3 ≤ n) :
    Real.exp eulerMascheroniConstant * n * Real.log (Real.log n) ≤
      Real.exp (harmonic n) * Real.log (harmonic n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog1 := one_lt_log hn
  have hH := log_add_gamma_lt_harmonic (by omega : 1 ≤ n)
  have hγ := one_half_lt_eulerMascheroniConstant
  have h1 : Real.exp eulerMascheroniConstant * n = Real.exp (Real.log n + eulerMascheroniConstant) := by
    rw [Real.exp_add, Real.exp_log hn0]; ring
  have h2 : Real.exp (Real.log n + eulerMascheroniConstant) ≤ Real.exp (harmonic n) :=
    Real.exp_le_exp.2 hH.le
  have h3 : Real.log (Real.log n) ≤ Real.log (harmonic n) :=
    Real.log_le_log (by linarith) (by linarith)
  have h4 : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlog1.le
  rw [h1]
  exact mul_le_mul h2 h3 h4 (Real.exp_pos _).le

/-- **Under RH, with Robin's theorem, Lagarias's inequality holds for every `n ≥ 1`.** -/
theorem lagarias_of_robinForward (hF : RobinForward) (hRH : RiemannHypothesis) : LagariasInequality := by
  intro n hn
  rcases le_or_gt n 5040 with h | h
  · exact lagarias_upto_5040 hn h
  · have hR := hF hRH n h
    have hc := robin_le_lagarias (by omega : 3 ≤ n)
    have hH0 := harmonic_nonneg' n
    unfold lagariasBound
    linarith

/-- `H_n < log n + γ + 1/n` for `n ≥ 1` (Mathlib's `eulerMascheroniSeq_lt_eulerMascheroniConstant`). -/
theorem harmonic_lt {n : ℕ} (hn : 1 ≤ n) :
    (harmonic n : ℝ) < Real.log n + eulerMascheroniConstant + 1 / n := by
  have h := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  unfold eulerMascheroniSeq at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log n + 1 / n := by
    have e : (n : ℝ) + 1 = n * (1 + 1 / n) := by field_simp
    rw [e, Real.log_mul hn0.ne' (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / n by positivity)
    linarith
  linarith

/-- `e^x ≤ 1 + 2x` for `0 ≤ x ≤ 1`. -/
theorem exp_le_one_add_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have h := Real.exp_bound' h0 h1 (by norm_num : 0 < 2)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial, pow_one] at h
  norm_num at h
  nlinarith

/-- `e^γ < 2`. -/
theorem exp_gamma_lt_two : Real.exp eulerMascheroniConstant < 2 := by
  have h := eulerMascheroniConstant_lt_two_thirds
  have h2 := Real.log_two_gt_d9
  have h3 : Real.exp (2 / 3) < 2 := by
    rw [← Real.lt_log_iff_exp_lt (by norm_num)]
    norm_num at h2 ⊢
    linarith
  exact (Real.exp_lt_exp.2 h).trans h3

/-- `(log n)² ≤ 4n`, from `log n ≤ 2 √n`. -/
theorem log_sq_le (n : ℕ) : Real.log n ^ 2 ≤ 4 * n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h := Real.log_le_rpow_div hn0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hs : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have hs0 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hn0 _
  have hl : Real.log n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by linarith [h]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  · have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast h0)
    calc Real.log n ^ 2 ≤ (2 * (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ hl0 hl 2
      _ = 4 * (n : ℝ) := by rw [mul_pow, hs]; norm_num

/-- **Lagarias's bound is close to Robin's**: `H_n + e^{H_n} log H_n ≤ e^γ n log log n + 60 n/log n` for `n ≥ 16`. -/
theorem lagariasBound_le {n : ℕ} (hn : 16 ≤ n) :
    lagariasBound n ≤
      Real.exp eulerMascheroniConstant * n * Real.log (Real.log n) + 60 * n / Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  set L := Real.log n with hL
  have hL2 : 2 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hn0]
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h3 := mul_self_lt_mul_self (Real.exp_pos 1).le h1
    rw [h2]
    norm_num at h3 ⊢
    linarith
  have hLpos : 0 < L := by linarith
  have hγ := one_half_lt_eulerMascheroniConstant
  have hγ' := eulerMascheroniConstant_lt_two_thirds
  have hγ2 := exp_gamma_lt_two
  have hH := harmonic_lt (by omega : 1 ≤ n)
  have hHlow := log_add_gamma_lt_harmonic (by omega : 1 ≤ n)
  have hinv : 1 / (n : ℝ) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
  have hH1 : (harmonic n : ℝ) ≤ L + 1 := by linarith
  have hHpos : (1 : ℝ) < harmonic n := by linarith
  -- `e^{H_n} ≤ e^γ (n + 2)`
  have hexp : Real.exp (harmonic n) ≤ Real.exp eulerMascheroniConstant * (n + 2) := by
    have h1 : Real.exp (harmonic n) ≤ Real.exp (L + eulerMascheroniConstant + 1 / n) :=
      Real.exp_le_exp.2 hH.le
    have h2 : Real.exp (L + eulerMascheroniConstant + 1 / n) =
        Real.exp eulerMascheroniConstant * n * Real.exp (1 / n) := by
      rw [Real.exp_add, Real.exp_add, hL, Real.exp_log hn0]; ring
    have h3 : Real.exp (1 / n) ≤ 1 + 2 * (1 / n) :=
      exp_le_one_add_two_mul (by positivity) (by linarith)
    have h4 : (n : ℝ) * (1 + 2 * (1 / n)) = n + 2 := by field_simp
    calc Real.exp (harmonic n) ≤ Real.exp eulerMascheroniConstant * n * Real.exp (1 / n) := by
          rw [← h2]; exact h1
      _ ≤ Real.exp eulerMascheroniConstant * n * (1 + 2 * (1 / n)) := by gcongr
      _ = Real.exp eulerMascheroniConstant * (n + 2) := by rw [mul_assoc, h4]
  -- `log H_n ≤ log L + 1/L`
  have hlogH : Real.log (harmonic n) ≤ Real.log L + 1 / L := by
    have h1 : Real.log (harmonic n) ≤ Real.log (L + 1) := Real.log_le_log (by linarith) hH1
    have h2 : Real.log (L + 1) = Real.log L + Real.log (1 + 1 / L) := by
      rw [← Real.log_mul hLpos.ne' (by positivity)]
      congr 1
      field_simp
    have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / L by positivity)
    linarith
  have hlogH0 : 0 ≤ Real.log (harmonic n) := Real.log_nonneg hHpos.le
  have hprod : Real.exp (harmonic n) * Real.log (harmonic n) ≤
      Real.exp eulerMascheroniConstant * (n + 2) * (Real.log L + 1 / L) :=
    mul_le_mul hexp hlogH hlogH0 (by positivity)
  -- the leftover is at most `60 n/L`
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogL : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hLpos]
  have hLn : L ≤ n := by linarith [Real.log_le_sub_one_of_pos hn0]
  have hsq := log_sq_le n
  have h2L : 2 / L ≤ 1 := by rw [div_le_iff₀ hLpos]; linarith
  have hnL0 : 0 ≤ (n : ℝ) / L := by positivity
  have hX : 0 ≤ 2 * Real.log L + n / L + 2 / L := by positivity
  have hprod2 : Real.exp eulerMascheroniConstant * (2 * Real.log L + n / L + 2 / L) ≤
      2 * (2 * Real.log L + n / L + 2 / L) := mul_le_mul_of_nonneg_right hγ2.le hX
  have h58 : 5 * L + 3 ≤ 58 * n / L := by
    rw [le_div_iff₀ hLpos]; nlinarith
  have key : Real.exp eulerMascheroniConstant * (2 * Real.log L + n / L + 2 / L) + L + 1 ≤ 60 * n / L := by
    have e : (60 : ℝ) * n / L = 58 * n / L + 2 * (n / L) := by ring
    rw [e]
    linarith
  calc lagariasBound n = (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n) := rfl
    _ ≤ (L + 1) + Real.exp eulerMascheroniConstant * (n + 2) * (Real.log L + 1 / L) := by linarith
    _ = Real.exp eulerMascheroniConstant * n * Real.log L +
        (Real.exp eulerMascheroniConstant * (2 * Real.log L + n / L + 2 / L) + L + 1) := by ring
    _ ≤ Real.exp eulerMascheroniConstant * n * Real.log L + 60 * n / L := by linarith

/-- **Lagarias's inequality, with Robin's theorem, gives RH.** -/
theorem rh_of_lagarias (hC : RobinConverse) (hLag : LagariasInequality) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨b, c, hb, hc, hseq⟩ := hC hRH
  have hb' : 0 < 1 - b := by linarith
  set T : ℝ := (60 / c) ^ (1 - b)⁻¹ with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  obtain ⟨n, hn, hσ⟩ := hseq (⌈Real.exp T⌉₊ + 16)
  have hn16 : 16 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnT : Real.exp T < n := by
    have h1 := Nat.le_ceil (Real.exp T)
    have h2 : ((⌈Real.exp T⌉₊ + 16 : ℕ) : ℝ) < n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hlogT : T < Real.log n := (Real.lt_log_iff_exp_lt hn0).2 hnT
  set L := Real.log n with hL
  have hLpos : 0 < L := lt_of_le_of_lt hT0 hlogT
  have hLb : 0 < L ^ b := Real.rpow_pos_of_pos hLpos b
  -- `c L^{1−b} > 60`, that is `c L > 60 L^b`
  have hT' : T ^ (1 - b) = 60 / c := by
    rw [hT, ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hb'.ne', Real.rpow_one]
  have h1 : 60 / c < L ^ (1 - b) := hT' ▸ Real.rpow_lt_rpow hT0 hlogT hb'
  have h2 : L ^ (1 - b) = L / L ^ b := by rw [Real.rpow_sub hLpos, Real.rpow_one]
  have h3 : 60 * L ^ b < c * L := by
    have h1' := h1
    rw [h2, div_lt_iff₀ hc] at h1'
    rw [← lt_div_iff₀ hLb]
    calc (60 : ℝ) < L / L ^ b * c := h1'
      _ = c * L / L ^ b := by ring
  have key : 60 * n / L < c * n / L ^ b := by
    rw [div_lt_div_iff₀ hLpos hLb]
    nlinarith [mul_lt_mul_of_pos_left h3 hn0]
  have hbound := lagariasBound_le hn16
  have hLn := hLag n (by omega)
  linarith

/-- **Lagarias's criterion**, from Robin's theorem: RH holds if and only if `σ(n) ≤ H_n + e^{H_n} log H_n` for every
`n ≥ 1`. -/
theorem lagarias_criterion (hF : RobinForward) (hC : RobinConverse) :
    RiemannHypothesis ↔ LagariasInequality :=
  ⟨lagarias_of_robinForward hF, rh_of_lagarias hC⟩

end LagariasCriterion
