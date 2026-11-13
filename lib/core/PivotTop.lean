import Mathlib
import BallPivot

/-! # The top vertex keeps `13/10` of its diagonal: `(log N + d)Σc_n² − L(c) ≥ (13/10)c_N²` for `d ≥ 17/20`

Plain statement. `L(c) = 2Σ_{n ≤ N}Λ(n)n^{−1/2}Σ_{jn ≤ N}c_j c_{jn}` is Landau's form (`BallDensity.ex`). For every
`N ≥ 2`, every `d ≥ 17/20` and every real `c`, `(log N + d)Σ_{n ≤ N}c_n² − L(c) ≥ (13/10)c_N²` (`top_bound`): under
the diagonal `log N + d`, the top vertex `N` of the divisibility graph keeps `13/10` of its diagonal. The diagonal of
`BallSharp.landauSlack` is `log N + log 4 + 1`; the constant `17/20` comes from sharper bounds for Mertens' sums
`M(y) = Σ_{n ≤ y}Λ(n)/n`:
* `mertens_le_small`: `M(y) ≤ log y + (log 3 − 1) + (1 + log y)/y` for `1 ≤ y ≤ 2000`;
* `mertens_le_large`: `M(y) ≤ log y + (log 4 − 1) + (1 + log y)/y + 2 log y/√y` for every `y ≥ 1`;
* `mertens_le_uniform`: `M(y) ≤ log y + 81/100` for every `y`; `mertens_one`, …, `mertens_six` are the first values.

The proofs.

- **Chebyshev on the small range.** `ψ(n) = log lcm(1, …, n)` (`Chebyshev.psi_eq_log_lcmUpto`), and
  `lcm(1, …, n) ≤ 3ⁿ` for `n ≤ 2000` by one kernel computation that carries `(lcm(1, …, n), 3ⁿ)` along
  (`lcmCheck_ok`); the largest `ψ(n)/n` there is `1.039 < log 3`. With `yM(y) ≤ Σ_{m ≤ y}log m + ψ(y)`
  (`BallDensity.mul_mertens_le`) and Stirling's `Σ_{m ≤ y}log m ≤ y log y − y + log y + 1` this is the small-range
  bound; Chebyshev's `ψ(y) ≤ y log 4 + 2√y log y` (`Chebyshev.psi_le`) gives the other, below `log y + 81/100` from
  `y = 1600` on.
- **Schur's test, row by row** (`landau_le_rows`). As in `BallDensity.landau_le_of`,
  `L(b) ≤ Σ_{j ≤ N}b_j²(M(⌊N/j⌋) + log j)`, before a uniform Mertens bound is applied to the rows.
- **The top vertex** (`top_ge`). With `c′ = BallPivot.cut N c`, `L(c) = L(c′) + 2c_N Σ_{q ∣ N}Λ(q)q^{−1/2}c_{N/q}`
  (`BallPivot.landau_cut`), and `L(c′)` lives on `[1, N − 1]`. There Schur's test leaves row `j` the part
  `ρ_j = log N + d − M(⌊(N − 1)/j⌋) − log j ≥ 0` of its diagonal; at a parent `j = N/q`, `⌊(N − 1)/j⌋ = q − 1` and
  `ρ_j = room_d(q) = d + log q − M(q − 1)`. Completing the square at each parent costs `c_N²Λ(q)²/(q·room_d(q))`,
  and the parents are distinct.
- **The numbers.** By `Σ_{q ∣ N}Λ(q) = log N` the bracket `log N + d − Σ_{q ∣ N}Λ(q)²/(q·room_d(q))` is
  `d + Σ_{q ∣ N}Λ(q)(1 − Λ(q)/(q·room_d(q)))`. Every term is `≥ 0` (`term_le`) and a prime `p ∣ N` contributes
  `≥ 45/100` (`prime_term_ge`): `room_d(q)` is computed exactly for `q = 2, 3, 4, 5, 7` (`Λ(6) = 0`), it is at least
  `d − 0.52` on `[8, 2001]` and `d − 0.43` on `[11, 2001]` (small range), and at least `d − 0.81` everywhere (uniform
  bound). So the bracket is at least `17/20 + 45/100 = 13/10`.
-/

open Real Finset BallDensity BallSharp
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace PivotTop

/-! ## `ψ(n) ≤ n log 3` for `n ≤ 2000`, by one kernel computation -/

/-- `lcm(1, …, n)`, by structural recursion. -/
def lcmTo : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmTo n) (n + 1)

/-- `lcmTo n = lcm(1, …, n)`. -/
lemma lcmTo_eq (n : ℕ) : lcmTo n = Nat.lcmUpto n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lcmTo, ih, Nat.lcmUpto, Nat.lcmUpto, ← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
      Finset.lcm_insert, id, Nat.lcm_comm]
    rfl

/-- `lcmCheck k n l t` checks `l ≤ t` along `k` steps of `(n, l, t) ↦ (n + 1, lcm(l, n + 1), 3t)`. -/
def lcmCheck : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | k + 1, n, l, t => Nat.ble l t && lcmCheck k (n + 1) (Nat.lcm l (n + 1)) (3 * t)

/-- A passed check started at `(n, lcm(1, …, n), 3ⁿ)` gives `lcm(1, …, m) ≤ 3^m` for `n ≤ m < n + k`. -/
lemma lcmCheck_spec (k : ℕ) : ∀ n, lcmCheck k n (lcmTo n) (3 ^ n) = true →
    ∀ m, n ≤ m → m < n + k → lcmTo m ≤ 3 ^ m := by
  induction k with
  | zero => intro n _ m h1 h2; omega
  | succ k ih =>
    intro n h m h1 h2
    simp only [lcmCheck, Bool.and_eq_true, Nat.ble_eq] at h
    rcases h1.lt_or_eq with h1 | rfl
    · refine ih (n + 1) ?_ m h1 (by omega)
      rw [lcmTo, pow_succ']
      exact h.2
    · exact h.1

/-- The kernel computation: `lcm(1, …, n) ≤ 3ⁿ` for `n ≤ 2000`, in one pass. -/
theorem lcmCheck_ok : lcmCheck 2001 0 (lcmTo 0) (3 ^ 0) = true := by decide +kernel

/-- `lcm(1, …, n) ≤ 3ⁿ` for `n ≤ 2000`. -/
lemma lcmUpto_le {n : ℕ} (hn : n ≤ 2000) : Nat.lcmUpto n ≤ 3 ^ n := by
  rw [← lcmTo_eq]
  exact lcmCheck_spec 2001 0 lcmCheck_ok n (Nat.zero_le n) (by omega)

/-- **Chebyshev's bound on the small range**: `ψ(n) ≤ n log 3` for `n ≤ 2000`. -/
lemma psi_le_small {n : ℕ} (hn : n ≤ 2000) : Chebyshev.psi n ≤ n * Real.log 3 := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have h0 : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  have h1 : (Nat.lcmUpto n : ℝ) ≤ (3 : ℝ) ^ n := by exact_mod_cast lcmUpto_le hn
  calc Real.log (Nat.lcmUpto n) ≤ Real.log ((3 : ℝ) ^ n) := Real.log_le_log h0 h1
    _ = n * Real.log 3 := by rw [Real.log_pow]

/-! ## Mertens' bounds -/

/-- `M(y) = Σ_{n ≤ y}Λ(n)/n`. -/
def mertens (y : ℕ) : ℝ := ∑ n ∈ Icc 1 y, Λ n / n

/-- **Mertens' bound from a Chebyshev bound**: if `ψ(y) ≤ B`, then `M(y) ≤ log y − 1 + (1 + log y)/y + B/y`, from
`yM(y) ≤ Σ_{m ≤ y}log m + ψ(y)` and Stirling's `Σ_{m ≤ y}log m ≤ y log y − y + log y + 1`. -/
lemma mertens_le_of_psi {y : ℕ} (hy : 1 ≤ y) {B : ℝ} (hB : Chebyshev.psi y ≤ B) :
    mertens y ≤ Real.log y - 1 + (1 + Real.log y) / y + B / y := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < y := by linarith
  have h1 := mul_mertens_le y
  have h2 : ∑ m ∈ Icc 1 y, Real.log m ≤ y * Real.log y - y + Real.log y + 1 := by
    have h := Real.sum_log_le hy1
    rwa [Nat.floor_natCast, ← Icc_one_eq_Ioc] at h
  have e : (y : ℝ) * (Real.log y - 1 + (1 + Real.log y) / y + B / y) =
      y * Real.log y - y + Real.log y + 1 + B := by
    field_simp
    ring
  have h3 : (y : ℝ) * mertens y ≤ y * (Real.log y - 1 + (1 + Real.log y) / y + B / y) := by
    rw [e]
    unfold mertens
    linarith
  exact le_of_mul_le_mul_left h3 hy0

/-- **Mertens' bound, small range**: `M(y) ≤ log y + (log 3 − 1) + (1 + log y)/y` for `1 ≤ y ≤ 2000`. -/
lemma mertens_le_small {y : ℕ} (hy1 : 1 ≤ y) (hy : y ≤ 2000) :
    mertens y ≤ Real.log y + (Real.log 3 - 1) + (1 + Real.log y) / y := by
  have h := mertens_le_of_psi hy1 (psi_le_small hy)
  have hy0 : (y : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hy0] at h
  linarith

/-- **Mertens' bound, every `y ≥ 1`**: `M(y) ≤ log y + (log 4 − 1) + (1 + log y)/y + 2 log y/√y`, from Chebyshev's
`ψ(y) ≤ y log 4 + 2√y log y` (`Chebyshev.psi_le`). -/
lemma mertens_le_large {y : ℕ} (hy1 : 1 ≤ y) :
    mertens y ≤ Real.log y + (Real.log 4 - 1) + (1 + Real.log y) / y + 2 * Real.log y / Real.sqrt y := by
  have hy : (1 : ℝ) ≤ y := by exact_mod_cast hy1
  have h := mertens_le_of_psi hy1 (Chebyshev.psi_le hy)
  have hy0 : (0 : ℝ) < y := by linarith
  have hs := Real.sqrt_pos.2 hy0
  have hss := Real.mul_self_sqrt hy0.le
  have e1 : (Real.log 4 * y + 2 * Real.sqrt y * Real.log y) / y =
      Real.log 4 + 2 * Real.sqrt y * Real.log y / y := by
    field_simp
  have e2 : 2 * Real.sqrt y * Real.log y / y = 2 * Real.log y / Real.sqrt y := by
    rw [div_eq_div_iff hy0.ne' hs.ne']
    calc 2 * Real.sqrt y * Real.log y * Real.sqrt y = 2 * Real.log y * (Real.sqrt y * Real.sqrt y) := by ring
      _ = 2 * Real.log y * y := by rw [hss]
  rw [e1, e2] at h
  linarith

/-- `(1 + log y)/y` decreases on `[1, ∞)`: `(1 + log y)/y ≤ (1 + log a)/a` for `1 ≤ a ≤ y`. -/
lemma one_add_log_div_le {a y : ℝ} (ha : 1 ≤ a) (hay : a ≤ y) :
    (1 + Real.log y) / y ≤ (1 + Real.log a) / a := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < y := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < y / a by positivity)
  rw [Real.log_div hy0.ne' ha0.ne'] at h
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have h2 : a * Real.log y ≤ a * Real.log a + y - a := by
    have h' := mul_le_mul_of_nonneg_left h ha0.le
    have e : a * (y / a - 1) = y - a := by field_simp
    nlinarith
  rw [div_le_div_iff₀ hy0 ha0]
  nlinarith [mul_le_mul_of_nonneg_left hay hla]

/-- `log 40 < 3.689`. -/
lemma log_forty_lt : Real.log 40 < 3.689 := by
  have e : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
    rw [show (40 : ℝ) = 2 ^ 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  rw [e]
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  linarith

/-- For `y ≥ 1600`: `2 log y/√y ≤ 37/100` and `(1 + log y)/y ≤ 1/100`. -/
lemma tail_le {y : ℝ} (hy : 1600 ≤ y) :
    2 * Real.log y / Real.sqrt y ≤ 37 / 100 ∧ (1 + Real.log y) / y ≤ 1 / 100 := by
  have hy0 : 0 < y := by linarith
  have h40 := log_forty_lt
  constructor
  · set s := Real.sqrt y with hs
    have hs40 : 40 ≤ s := (Real.le_sqrt (by norm_num) hy0.le).2 (by norm_num; linarith)
    have hs0 : 0 < s := by linarith
    have hlog : Real.log y = 2 * Real.log s := by
      rw [hs, Real.log_sqrt hy0.le]
      ring
    have h := Real.log_le_sub_one_of_pos (show 0 < s / 40 by positivity)
    rw [Real.log_div hs0.ne' (by norm_num)] at h
    rw [hlog, div_le_iff₀ hs0]
    linarith
  · have h := one_add_log_div_le (a := 1600) (by norm_num) hy
    have e : Real.log 1600 = 2 * Real.log 40 := by
      rw [show (1600 : ℝ) = 40 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    refine h.trans ?_
    rw [e, div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith

/-! ## The first values of `M` -/

/-- `Λ(4) = log 2`. -/
lemma vonMangoldt_four : Λ 4 = Real.log 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- `Λ(6) = 0`. -/
lemma vonMangoldt_six : Λ 6 = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.2 (by decide)

/-- `M(0) = 0`. -/
lemma mertens_zero : mertens 0 = 0 := by simp [mertens]

/-- `M(y + 1) = M(y) + Λ(y + 1)/(y + 1)`. -/
lemma mertens_succ (y : ℕ) : mertens (y + 1) = mertens y + Λ (y + 1) / ((y + 1 : ℕ) : ℝ) := by
  unfold mertens
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- `M(1) = 0`. -/
lemma mertens_one : mertens 1 = 0 := by
  have h := mertens_succ 0
  simpa [mertens_zero, ArithmeticFunction.vonMangoldt_apply_one] using h

/-- `M(2) = log 2/2`. -/
lemma mertens_two : mertens 2 = Real.log 2 / 2 := by
  have h := mertens_succ 1
  norm_num at h
  rw [h, mertens_one, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- `M(3) = log 2/2 + log 3/3`. -/
lemma mertens_three : mertens 3 = Real.log 2 / 2 + Real.log 3 / 3 := by
  have h := mertens_succ 2
  norm_num at h
  rw [h, mertens_two, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  norm_num

/-- `M(4) = M(3) + log 2/4`. -/
lemma mertens_four : mertens 4 = mertens 3 + Real.log 2 / 4 := by
  have h := mertens_succ 3
  norm_num at h
  rw [h, vonMangoldt_four]

/-- `M(5) = M(4) + log 5/5`. -/
lemma mertens_five : mertens 5 = mertens 4 + Real.log 5 / 5 := by
  have h := mertens_succ 4
  norm_num at h
  rw [h, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_five]
  norm_num

/-- `M(6) = M(5)`. -/
lemma mertens_six : mertens 6 = mertens 5 := by
  have h := mertens_succ 5
  norm_num at h
  rw [h, vonMangoldt_six, zero_div, add_zero]

/-- **Mertens' bound, uniform**: `M(y) ≤ log y + 81/100` for every `y`: the small-range bound at `3 ≤ y ≤ 2000`,
where `log 3 − 1 + (1 + log y)/y ≤ (4 log 3 − 2)/3 < 0.7982`, and Chebyshev's beyond, where it is `< 0.767`. -/
lemma mertens_le_uniform (y : ℕ) : mertens y ≤ Real.log y + 81 / 100 := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl3 := Real.log_three_lt_d9
  rcases Nat.lt_or_ge y 3 with hy | hy
  · interval_cases y
    · rw [mertens_zero]
      norm_num
    · rw [mertens_one]
      norm_num
    · rw [mertens_two]
      push_cast
      linarith
  rcases Nat.lt_or_ge y 2001 with hy' | hy'
  · have h := mertens_le_small (by omega : 1 ≤ y) (by omega : y ≤ 2000)
    have h3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
    have hmono := one_add_log_div_le (a := 3) (by norm_num) h3
    have h3' : (1 + Real.log 3) / 3 ≤ 0.6996 := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
  · have h := mertens_le_large (by omega : 1 ≤ y)
    have hy1600 : (1600 : ℝ) ≤ y := by exact_mod_cast (show 1600 ≤ y by omega)
    obtain ⟨t1, t2⟩ := tail_le hy1600
    have hl4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
    linarith

/-! ## Schur's test, row by row -/

/-- **Schur's test, row by row**: for every real `b`,
`2Σ_{n ≤ N}(Λ(n)/√n)Σ_{jn ≤ N} b_j b_{jn} ≤ Σ_{j ≤ N} b_j²(M(⌊N/j⌋) + log j)`. The proof of
`BallDensity.landau_le_of`, stopped before a uniform Mertens bound is applied to the rows. -/
lemma landau_le_rows (N : ℕ) (b : ℕ → ℝ) :
    2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N b n ≤
      ∑ j ∈ Icc 1 N, b j ^ 2 * (mertens (N / j) + Real.log j) := by
  unfold ex
  have hamgm : ∀ n ∈ Icc 1 N, ∀ j, Λ n / Real.sqrt n * (b j * b (j * n)) ≤
      (b j ^ 2 * (Λ n / n) + b (j * n) ^ 2 * Λ n) / 2 := by
    intro n hn j
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.1 hn).1; omega)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    have hss : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
    have hL := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    set s := Real.sqrt n
    have hsq : 0 ≤ Λ n * (b j - s * b (j * n)) ^ 2 := mul_nonneg hL (sq_nonneg _)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hs two_pos, ← hss]
    have e : (b j ^ 2 * (Λ n / s ^ 2) + b (j * n) ^ 2 * Λ n) * s =
        Λ n * (b j ^ 2 + s ^ 2 * b (j * n) ^ 2) / s := by
      field_simp
    rw [e, le_div_iff₀ hs]
    nlinarith [hsq]
  -- the rows
  have hA : ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b j ^ 2 * (Λ n / n) =
      ∑ j ∈ Icc 1 N, b j ^ 2 * ∑ n ∈ Icc 1 (N / j), Λ n / n := by
    rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun j => Icc 1 (N / j))]
    · exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    · intro n j
      simp only [Finset.mem_Icc, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, ⟨hj1, hjN⟩, hjn⟩
        exact ⟨⟨hn1, (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hjn)⟩, hj1, hjN⟩
      · rintro ⟨⟨hn1, hnj⟩, hj1, hjN⟩
        have hjn : n * j ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hnj
        exact ⟨⟨hn1, by nlinarith⟩, ⟨hj1, hjN⟩, by rw [mul_comm]; exact hjn⟩
  -- the columns
  have hB : ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b (j * n) ^ 2 * Λ n =
      ∑ m ∈ Icc 1 N, b m ^ 2 * Real.log m := by
    have h1 : ∀ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b (j * n) ^ 2 * Λ n =
        ∑ m ∈ (Icc 1 N).filter (n ∣ ·), b m ^ 2 * Λ n := fun n hn =>
      sum_mul_eq_sum_dvd N (Finset.mem_Icc.1 hn).1 (fun m => b m ^ 2 * Λ n)
    rw [Finset.sum_congr rfl h1, Finset.sum_comm' (t' := Icc 1 N) (s' := fun m => m.divisors)]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
    · intro n m
      simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, ⟨hm1, hmN⟩, hnm⟩
        exact ⟨⟨hnm, by omega⟩, hm1, hmN⟩
      · rintro ⟨⟨hnm, -⟩, hm1, hmN⟩
        have hn1 : 1 ≤ n := Nat.pos_of_dvd_of_pos hnm (by omega)
        exact ⟨⟨hn1, (Nat.le_of_dvd (by omega) hnm).trans hmN⟩, ⟨hm1, hmN⟩, hnm⟩
  calc 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b j * b (j * n)
      = 2 * ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N),
          Λ n / Real.sqrt n * (b j * b (j * n)) := by
        simp_rw [Finset.mul_sum]
    _ ≤ 2 * ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N),
          (b j ^ 2 * (Λ n / n) + b (j * n) ^ 2 * Λ n) / 2 := by
        gcongr with n hn j _
        exact hamgm n hn j
    _ = ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b j ^ 2 * (Λ n / n) +
          ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b (j * n) ^ 2 * Λ n := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j ∈ Icc 1 N, b j ^ 2 * ∑ n ∈ Icc 1 (N / j), Λ n / n +
          ∑ m ∈ Icc 1 N, b m ^ 2 * Real.log m := by
        rw [hA, hB]
    _ = ∑ j ∈ Icc 1 N, b j ^ 2 * (mertens (N / j) + Real.log j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold mertens
        ring

/-! ## Without its top coefficient, the form lives on `[1, N − 1]` -/

/-- If `c_N = 0`, the inner sums of Landau's form over `[1, N]` and over `[1, N − 1]` agree. -/
lemma ex_eq_pred {N : ℕ} {c : ℕ → ℝ} (hc : c N = 0) {n : ℕ} (hn : 1 ≤ n) : ex N c n = ex (N - 1) c n := by
  unfold ex
  symm
  refine Finset.sum_subset (fun j hj => ?_) (fun j hj hj' => ?_)
  · simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    omega
  · simp only [Finset.mem_filter, Finset.mem_Icc, not_and, not_le] at hj hj'
    have hjn : j ≤ j * n := Nat.le_mul_of_pos_right j hn
    have h : j * n = N := by omega
    rw [h, hc, mul_zero]

/-- If `c_N = 0`, Landau's form over `[1, N]` is that over `[1, N − 1]`. -/
lemma landau_pred {N : ℕ} {c : ℕ → ℝ} (hc : c N = 0) :
    ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n =
      ∑ n ∈ Icc 1 (N - 1), Λ n / Real.sqrt n * ex (N - 1) c n := by
  have h : ∀ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n = Λ n / Real.sqrt n * ex (N - 1) c n :=
    fun n hn => by rw [ex_eq_pred hc (Finset.mem_Icc.1 hn).1]
  rw [Finset.sum_congr rfl h]
  symm
  refine Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)
  · simp only [Finset.mem_Icc] at hn ⊢
    omega
  · simp only [Finset.mem_Icc, not_and, not_le] at hn hn'
    rw [ex_eq_zero _ _ (show N - 1 < n by omega), mul_zero]

/-- If `c_N = 0`, `Σ_{j ≤ N}c_j² = Σ_{j ≤ N − 1}c_j²`. -/
lemma S2_pred {N : ℕ} {c : ℕ → ℝ} (hc : c N = 0) : S2 N c = S2 (N - 1) c := by
  unfold S2
  symm
  refine Finset.sum_subset (fun j hj => ?_) (fun j hj hj' => ?_)
  · simp only [Finset.mem_Icc] at hj ⊢
    omega
  · simp only [Finset.mem_Icc, not_and, not_le] at hj hj'
    rw [show j = N by omega, hc]
    ring

/-! ## The parents of the top vertex -/

/-- **The parents are distinct and below `N`**: for `w ≥ 0` on `[1, N − 1]`,
`Σ_{q ∣ N, 2 ≤ q ≤ N}w(N/q) ≤ Σ_{j ≤ N − 1}w(j)`. -/
lemma sum_parents_le_of_nonneg {N : ℕ} (hN : 1 ≤ N) (w : ℕ → ℝ) (hw : ∀ j ∈ Icc 1 (N - 1), 0 ≤ w j) :
    ∑ q ∈ (Icc 2 N).filter (· ∣ N), w (N / q) ≤ ∑ j ∈ Icc 1 (N - 1), w j := by
  have hN0 : 0 < N := hN
  have hinj : Set.InjOn (fun n => N / n) ((Icc 2 N).filter (· ∣ N) : Finset ℕ) := by
    intro a ha b hb hab
    have had : a ∣ N := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
    have hbd : b ∣ N := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
    have h1 : N / (N / a) = a := Nat.div_div_self had hN0.ne'
    have h2 : N / (N / b) = b := Nat.div_div_self hbd hN0.ne'
    have hab' : N / a = N / b := hab
    rw [← h1, ← h2, hab']
  have hsub : ((Icc 2 N).filter (· ∣ N)).image (fun n => N / n) ⊆ Icc 1 (N - 1) := by
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj
    have hnd : n ∣ N := (Finset.mem_filter.1 hn).2
    have hn2 : 2 ≤ n := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    have hlt : N / n < N := Nat.div_lt_self hN0 (by omega)
    exact Finset.mem_Icc.2 ⟨Nat.div_pos (Nat.le_of_dvd hN0 hnd) (by omega), by omega⟩
  rw [← Finset.sum_image (f := w) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hw j hj

/-- At a parent `N/q` of the top vertex: `⌊(N − 1)/(N/q)⌋ = q − 1`. -/
lemma pred_div_parent {N q : ℕ} (hN : 1 ≤ N) (hq : q ∣ N) : (N - 1) / (N / q) = q - 1 := by
  obtain ⟨j, rfl⟩ := hq
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hj0 : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  rw [Nat.mul_div_cancel_left j hq0]
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.div_eq_of_lt_le
  · rw [add_mul, one_mul]
    omega
  · rw [add_mul, one_mul]
    omega

/-- At a parent: `log(N/q) = log N − log q`. -/
lemma log_parent {N q : ℕ} (hN : 1 ≤ N) (hq : q ∣ N) :
    Real.log ((N / q : ℕ) : ℝ) = Real.log N - Real.log q := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hq
    omega
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [Nat.cast_div hq hqR, Real.log_div hNR hqR]

/-! ## The top vertex -/

/-- The room at the parent `N/q` of the top vertex: `room_d(q) = d + log q − M(q − 1)`. -/
def room (d : ℝ) (q : ℕ) : ℝ := d + Real.log q - mertens (q - 1)

/-- **The top vertex, with general rooms**: if `M(y) ≤ log y + d` for every `y`, then for `N ≥ 2` and every real
`c`, `(log N + d)Σ_{n ≤ N}c_n² − L(c) ≥ c_N²(log N + d − Σ_{q ∣ N, q ≥ 2}Λ(q)²/(q·room_d(q)))`. Row `j < N` of
Schur's test keeps `ρ_j = log N + d − M(⌊(N − 1)/j⌋) − log j ≥ 0` of its diagonal, `ρ_{N/q} = room_d(q)` at a
parent, and the edge `(N/q, N)` costs at most `c_N²Λ(q)²/(q·room_d(q))` there. -/
theorem top_ge {N : ℕ} (hN : 2 ≤ N) {d : ℝ} (hM : ∀ y : ℕ, mertens y ≤ Real.log y + d) (c : ℕ → ℝ) :
    c N ^ 2 * (Real.log N + d - ∑ q ∈ (Icc 2 N).filter (· ∣ N), Λ q ^ 2 / (q * room d q)) ≤
      (Real.log N + d) * S2 N c - 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n := by
  have hN1 : 1 ≤ N := by omega
  have hL := BallPivot.landau_cut hN1 c
  have hS := BallPivot.S2_cut hN1 c
  have hcN : BallPivot.cut N c N = 0 := BallPivot.cut_self N c
  have hLp := landau_pred hcN
  have hSp := S2_pred hcN
  have hrows := landau_le_rows (N - 1) (BallPivot.cut N c)
  set c' := BallPivot.cut N c with hc'
  set P := (Icc 2 N).filter (· ∣ N)
  -- every row keeps a nonnegative part of its diagonal
  have hρ0 : ∀ j ∈ Icc 1 (N - 1),
      0 ≤ (Real.log N + d - mertens ((N - 1) / j) - Real.log j) * c' j ^ 2 := by
    intro j hj
    obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.1 hj
    refine mul_nonneg ?_ (sq_nonneg _)
    have hy := hM ((N - 1) / j)
    have hy1 : 1 ≤ (N - 1) / j := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have hyj : (N - 1) / j * j ≤ N - 1 := Nat.div_mul_le_self (N - 1) j
    have hy0 : (0 : ℝ) < ((N - 1) / j : ℕ) := by exact_mod_cast hy1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hlog : Real.log ((N - 1) / j : ℕ) + Real.log j ≤ Real.log N := by
      rw [← Real.log_mul hy0.ne' hj0.ne']
      exact Real.log_le_log (by positivity) (by exact_mod_cast (show (N - 1) / j * j ≤ N by omega))
    linarith
  -- at a parent, the row keeps the room
  have hρP : ∀ q ∈ P, (Real.log N + d - mertens ((N - 1) / (N / q)) - Real.log ((N / q : ℕ) : ℝ)) *
      c' (N / q) ^ 2 = room d q * c' (N / q) ^ 2 := by
    intro q hq
    have hqd : q ∣ N := (Finset.mem_filter.1 hq).2
    rw [pred_div_parent hN1 hqd, log_parent hN1 hqd, room]
    ring
  have hpar := sum_parents_le_of_nonneg hN1
    (fun j => (Real.log N + d - mertens ((N - 1) / j) - Real.log j) * c' j ^ 2) hρ0
  rw [Finset.sum_congr rfl hρP] at hpar
  -- the rows sum to the diagonal minus Schur's bound
  have hρsum : ∑ j ∈ Icc 1 (N - 1), (Real.log N + d - mertens ((N - 1) / j) - Real.log j) * c' j ^ 2 =
      (Real.log N + d) * S2 (N - 1) c' -
        ∑ j ∈ Icc 1 (N - 1), c' j ^ 2 * (mertens ((N - 1) / j) + Real.log j) := by
    unfold S2
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the edges at the top vertex
  have hX : ∑ n ∈ Icc 1 N, (if n ∣ N then Λ n / Real.sqrt n * c (N / n) else 0) =
      ∑ q ∈ P, Λ q / Real.sqrt q * c' (N / q) := by
    rw [← Finset.sum_filter]
    have h1 : ∑ q ∈ P, Λ q / Real.sqrt q * c' (N / q) = ∑ q ∈ P, Λ q / Real.sqrt q * c (N / q) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq2 : 2 ≤ q := (Finset.mem_Icc.1 (Finset.mem_filter.1 hq).1).1
      rw [hc', BallPivot.cut_of_ne c (Nat.div_lt_self (by omega) (by omega)).ne]
    rw [h1]
    refine (Finset.sum_subset (fun q hq => ?_) (fun n hn hn' => ?_)).symm
    · obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      have := Finset.mem_Icc.1 hq1
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, this.2⟩, hq2⟩
    · obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
      have h1 : n = 1 := by
        by_contra hne
        apply hn'
        have := Finset.mem_Icc.1 hn1
        exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, this.2⟩, hn2⟩
      rw [h1, ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul]
  -- completing the square at each parent
  have hsq : ∀ q ∈ P, -(c N ^ 2 * (Λ q ^ 2 / (q * room d q))) ≤
      room d q * c' (N / q) ^ 2 - 2 * c N * (Λ q / Real.sqrt q * c' (N / q)) := by
    intro q hq
    have hq2 : 2 ≤ q := (Finset.mem_Icc.1 (Finset.mem_filter.1 hq).1).1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hR : 0 < room d q := by
      have h := hM (q - 1)
      have hlt : Real.log ((q - 1 : ℕ) : ℝ) < Real.log q :=
        Real.log_lt_log (by exact_mod_cast (show 0 < q - 1 by omega))
          (by exact_mod_cast (show q - 1 < q by omega))
      unfold room
      linarith
    have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
    set R := room d q
    set x := c' (N / q)
    set a := c N * (Λ q / Real.sqrt q) with ha
    have ha2 : a ^ 2 / R = c N ^ 2 * (Λ q ^ 2 / (q * R)) := by
      rw [ha, mul_pow, div_pow, hs]
      field_simp
    have key : 0 ≤ (R * x - a) ^ 2 / R := div_nonneg (sq_nonneg _) hR.le
    have e : (R * x - a) ^ 2 / R = R * x ^ 2 - 2 * a * x + a ^ 2 / R := by
      field_simp
      ring
    have e2 : 2 * a * x = 2 * c N * (Λ q / Real.sqrt q * x) := by
      rw [ha]
      ring
    linarith
  have hsum := Finset.sum_le_sum hsq
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hL, hS, hLp, hSp, hX]
  linarith

/-! ## The numbers -/

/-- `1.9458 < log 7 < 1.9461`, from `2 log 7 = log 2 + 2 log 5 − log(50/49)` and `1/50 ≤ log(50/49) ≤ 1/49`. -/
lemma log_seven_bounds : 1.9458 < Real.log 7 ∧ Real.log 7 < 1.9461 := by
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have h5 := Real.log_five_gt_d9
  have h5' := Real.log_five_lt_d9
  have e : 2 * Real.log 7 = Real.log 2 + 2 * Real.log 5 - Real.log (50 / 49) := by
    rw [Real.log_div (by norm_num) (by norm_num), show (50 : ℝ) = 2 * 5 ^ 2 by norm_num,
      show (49 : ℝ) = 7 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hu : Real.log (50 / 49) ≤ 1 / 49 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 50 / 49 by norm_num)
    linarith
  have hl : 1 / 50 ≤ Real.log (50 / 49) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 50 / 49 by norm_num)
    have e' : (1 : ℝ) - (50 / 49)⁻¹ = 1 / 50 := by norm_num
    linarith
  constructor <;> linarith

/-- `log x ≤ log a + x/a − 1` for `a, x > 0`. -/
lemma log_le_tangent {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : Real.log x ≤ Real.log a + x / a - 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / a by positivity)
  rw [Real.log_div hx.ne' ha.ne'] at h
  linarith

/-- `room_d(2) = d + log 2`. -/
lemma room_two (d : ℝ) : room d 2 = d + Real.log 2 := by
  rw [room, show (2 : ℕ) - 1 = 1 from rfl, mertens_one]
  push_cast
  ring

/-- `room_d(3) = d + log 3 − log 2/2`. -/
lemma room_three (d : ℝ) : room d 3 = d + Real.log 3 - Real.log 2 / 2 := by
  rw [room, show (3 : ℕ) - 1 = 2 from rfl, mertens_two]
  push_cast
  ring

/-- `room_d(4) = d + log 4 − (log 2/2 + log 3/3)`. -/
lemma room_four (d : ℝ) : room d 4 = d + Real.log 4 - (Real.log 2 / 2 + Real.log 3 / 3) := by
  rw [room, show (4 : ℕ) - 1 = 3 from rfl, mertens_three]
  push_cast
  ring

/-- `room_d(5) = d + log 5 − (log 2/2 + log 3/3 + log 2/4)`. -/
lemma room_five (d : ℝ) :
    room d 5 = d + Real.log 5 - (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 2 / 4) := by
  rw [room, show (5 : ℕ) - 1 = 4 from rfl, mertens_four, mertens_three]
  push_cast
  ring

/-- `room_d(7) = d + log 7 − (log 2/2 + log 3/3 + log 2/4 + log 5/5)`. -/
lemma room_seven (d : ℝ) :
    room d 7 = d + Real.log 7 - (Real.log 2 / 2 + Real.log 3 / 3 + Real.log 2 / 4 + Real.log 5 / 5) := by
  rw [room, show (7 : ℕ) - 1 = 6 from rfl, mertens_six, mertens_five, mertens_four, mertens_three]
  push_cast
  ring

/-- `room_d(q) ≥ d − 81/100` for every `q ≥ 2` (the uniform Mertens bound). -/
lemma room_ge_uniform (d : ℝ) {q : ℕ} (hq : 2 ≤ q) : d - 81 / 100 ≤ room d q := by
  have h := mertens_le_uniform (q - 1)
  have hle : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast (show 0 < q - 1 by omega)) (by exact_mod_cast (show q - 1 ≤ q by omega))
  unfold room
  linarith

/-- For `8 ≤ q ≤ 2001`: `room_d(q) ≥ d − (log 3 − 1) − (1 + log 7)/7 ≥ d − 52/100` (Mertens' bound on the small
range at `q − 1 ≥ 7`). -/
lemma room_ge_mid (d : ℝ) {q : ℕ} (hq : 8 ≤ q) (hq' : q ≤ 2001) : d - 52 / 100 ≤ room d q := by
  have h := mertens_le_small (y := q - 1) (by omega) (by omega)
  have hq7 : (7 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show 7 ≤ q - 1 by omega)
  have hmono := one_add_log_div_le (a := 7) (by norm_num) hq7
  have hle : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q :=
    Real.log_le_log (by linarith) (by exact_mod_cast (show q - 1 ≤ q by omega))
  have h7 := log_seven_bounds.2
  have h3 := Real.log_three_lt_d9
  have h7' : (1 + Real.log 7) / 7 ≤ 0.4209 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  unfold room
  linarith

/-- For `11 ≤ q ≤ 2001`: `room_d(q) ≥ d − (log 3 − 1) − (1 + log 10)/10 ≥ d − 43/100`. -/
lemma room_ge_eleven (d : ℝ) {q : ℕ} (hq : 11 ≤ q) (hq' : q ≤ 2001) : d - 43 / 100 ≤ room d q := by
  have h := mertens_le_small (y := q - 1) (by omega) (by omega)
  have hq10 : (10 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show 10 ≤ q - 1 by omega)
  have hmono := one_add_log_div_le (a := 10) (by norm_num) hq10
  have hle : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q :=
    Real.log_le_log (by linarith) (by exact_mod_cast (show q - 1 ≤ q by omega))
  have h10 : Real.log 10 = Real.log 2 + Real.log 5 := Real.log_ten_eq
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  have h3 := Real.log_three_lt_d9
  have h10' : (1 + Real.log 10) / 10 ≤ 0.3303 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  unfold room
  linarith

/-- `L²/D ≤ L` for `0 ≤ L ≤ D`. -/
lemma sq_div_le {L D : ℝ} (hD : 0 < D) (hL0 : 0 ≤ L) (hL : L ≤ D) : L ^ 2 / D ≤ L := by
  rw [div_le_iff₀ hD]
  nlinarith

/-- `L − L²/(pR) ≥ 45/100` as soon as `p > 0`, `0 < r ≤ R`, `45/100 ≤ L ≤ kp` and `kL ≤ (L − 45/100)r`. -/
lemma term_ge_of {L R p r k : ℝ} (hp : 0 < p) (hr : 0 < r) (hR : r ≤ R) (hL : 45 / 100 ≤ L)
    (hLk : L ≤ k * p) (hkey : k * L ≤ (L - 45 / 100) * r) : 45 / 100 ≤ L - L ^ 2 / (p * R) := by
  have hR0 : 0 < R := hr.trans_le hR
  have hpR : 0 < p * R := mul_pos hp hR0
  have h1 : L ^ 2 ≤ p * (k * L) := by nlinarith [mul_le_mul_of_nonneg_left hLk (by linarith : (0 : ℝ) ≤ L)]
  have h2 : p * (k * L) ≤ p * ((L - 45 / 100) * r) := mul_le_mul_of_nonneg_left hkey hp.le
  have h3 : (L - 45 / 100) * r ≤ (L - 45 / 100) * R := mul_le_mul_of_nonneg_left hR (by linarith)
  have h4 : p * ((L - 45 / 100) * r) ≤ p * ((L - 45 / 100) * R) := mul_le_mul_of_nonneg_left h3 hp.le
  have h5 : L ^ 2 / (p * R) ≤ L - 45 / 100 := by
    rw [div_le_iff₀ hpR]
    linarith
  linarith

/-- **The rooms are wide enough**: `Λ(q) ≤ q·room_d(q)` for every `q ≥ 2` and `d ≥ 17/20`. -/
lemma vonMangoldt_le_room {d : ℝ} (hd : 17 / 20 ≤ d) {q : ℕ} (hq : 2 ≤ q) : Λ q ≤ q * room d q := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl3 := Real.log_three_gt_d9
  have hl3' := Real.log_three_lt_d9
  have hl5 := Real.log_five_gt_d9
  have hl5' := Real.log_five_lt_d9
  have hl7 := log_seven_bounds
  have hl4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rcases Nat.lt_or_ge q 8 with h8 | h8
  · interval_cases q
    · rw [room_two, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      push_cast
      linarith
    · rw [room_three, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
      push_cast
      linarith
    · rw [room_four, vonMangoldt_four]
      push_cast
      linarith
    · rw [room_five, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_five]
      push_cast
      linarith
    · rw [vonMangoldt_six]
      have h := room_ge_uniform d (show 2 ≤ 6 by norm_num)
      push_cast
      linarith
    · rw [room_seven, ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7)]
      push_cast
      linarith
  have hΛ : Λ q ≤ Real.log q := ArithmeticFunction.vonMangoldt_le_log
  rcases Nat.lt_or_ge q 2002 with h2002 | h2002
  · -- `log q ≤ 33q/100 ≤ q·room_d(q)`
    have hR := room_ge_mid d h8 (by omega)
    have hq8 : (8 : ℝ) ≤ q := by exact_mod_cast h8
    have hlog := log_le_tangent (a := 8) (by norm_num) hq0
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    have hm := mul_le_mul_of_nonneg_left hR hq0.le
    nlinarith
  · -- `log q ≤ q/100 ≤ q·room_d(q)`
    have hR := room_ge_uniform d hq
    have hq2 : (2002 : ℝ) ≤ q := by exact_mod_cast h2002
    have hlog := log_le_tangent (a := 1024) (by norm_num) hq0
    have hl1024 : Real.log 1024 = 10 * Real.log 2 := by
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
      push_cast
      ring
    have hm := mul_le_mul_of_nonneg_left hR hq0.le
    nlinarith

/-- `room_d(q) > 0` for `q ≥ 2` and `d ≥ 17/20`. -/
lemma room_pos {d : ℝ} (hd : 17 / 20 ≤ d) {q : ℕ} (hq : 2 ≤ q) : 0 < room d q := by
  have h := room_ge_uniform d hq
  linarith

/-- **Every parent term is nonnegative**: `Λ(q)²/(q·room_d(q)) ≤ Λ(q)` for `q ≥ 2` and `d ≥ 17/20`. -/
lemma term_le {d : ℝ} (hd : 17 / 20 ≤ d) {q : ℕ} (hq : 2 ≤ q) : Λ q ^ 2 / (q * room d q) ≤ Λ q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  exact sq_div_le (mul_pos hq0 (room_pos hd hq)) ArithmeticFunction.vonMangoldt_nonneg
    (vonMangoldt_le_room hd hq)

/-- **A prime parent leaves `45/100`**: `Λ(p) − Λ(p)²/(p·room_d(p)) ≥ 45/100` for every prime `p` and
`d ≥ 17/20`. -/
lemma prime_term_ge {d : ℝ} (hd : 17 / 20 ≤ d) {p : ℕ} (hp : p.Prime) :
    45 / 100 ≤ Λ p - Λ p ^ 2 / (p * room d p) := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hp2 := hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl3 := Real.log_three_gt_d9
  have hl3' := Real.log_three_lt_d9
  have hl5 := Real.log_five_gt_d9
  have hl5' := Real.log_five_lt_d9
  have hl7 := log_seven_bounds
  rcases Nat.lt_or_ge p 8 with h8 | h8
  · interval_cases p
    · rw [room_two]
      push_cast
      exact term_ge_of (k := 35 / 100) (r := 154 / 100) (by norm_num) (by norm_num) (by linarith)
        (by linarith) (by linarith) (by linarith)
    · rw [room_three]
      push_cast
      exact term_ge_of (k := 37 / 100) (r := 160 / 100) (by norm_num) (by norm_num) (by linarith)
        (by linarith) (by linarith) (by linarith)
    · norm_num at hp
    · rw [room_five]
      push_cast
      exact term_ge_of (k := 33 / 100) (r := 157 / 100) (by norm_num) (by norm_num) (by linarith)
        (by linarith) (by linarith) (by linarith)
    · norm_num at hp
    · rw [room_seven]
      push_cast
      exact term_ge_of (k := 28 / 100) (r := 158 / 100) (by norm_num) (by norm_num) (by linarith)
        (by linarith) (by linarith) (by linarith)
  have hp8 : (8 : ℝ) ≤ p := by exact_mod_cast h8
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlo : Real.log 8 ≤ Real.log p := Real.log_le_log (by norm_num) hp8
  rcases Nat.lt_or_ge p 2002 with h2002 | h2002
  · -- `11 ≤ p ≤ 2001`: `room_d(p) ≥ 42/100` and `log p ≤ p/4`
    have h11 : 11 ≤ p := by
      by_contra h
      interval_cases p <;> norm_num at hp
    have hR := room_ge_eleven d h11 (by omega)
    have hp11 : (11 : ℝ) ≤ p := by exact_mod_cast h11
    have hlog := log_le_tangent (a := 8) (by norm_num) hp0
    exact term_ge_of (k := 1 / 4) (r := 42 / 100) hp0 (by norm_num) (by linarith) (by linarith)
      (by linarith) (by linarith)
  · -- `p ≥ 2002`: `room_d(p) ≥ 4/100` and `log p ≤ p/100`
    have hR := room_ge_uniform d hp2
    have hp2' : (2002 : ℝ) ≤ p := by exact_mod_cast h2002
    have hlog := log_le_tangent (a := 1024) (by norm_num) hp0
    have hl1024 : Real.log 1024 = 10 * Real.log 2 := by
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
      push_cast
      ring
    exact term_ge_of (k := 1 / 100) (r := 4 / 100) hp0 (by norm_num) (by linarith) (by linarith)
      (by linarith) (by linarith)

/-! ## The top vertex keeps `13/10` of its diagonal -/

/-- **The top vertex keeps 13/10 of its diagonal**: under the diagonal `log N + d`, `d ≥ 17/20`, the quadratic form
`(log N + d)Σc_n² − L(c)` is at least `(13/10)c_N²`. By `top_ge` with the uniform Mertens bound, the bracket is
`d + Σ_{q ∣ N}Λ(q)(1 − Λ(q)/(q·room_d(q)))`, every term is `≥ 0` and a prime `p ∣ N` gives `≥ 45/100`. -/
theorem top_bound {N : ℕ} (hN : 2 ≤ N) {d : ℝ} (hd : 17 / 20 ≤ d) (c : ℕ → ℝ) :
    13 / 10 * c N ^ 2 ≤
      (Real.log N + d) * S2 N c - 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n := by
  have hM : ∀ y : ℕ, mertens y ≤ Real.log y + d := fun y => (mertens_le_uniform y).trans (by linarith)
  refine le_trans ?_ (top_ge hN hM c)
  set P := (Icc 2 N).filter (· ∣ N)
  have hlog : Real.log N = ∑ q ∈ P, Λ q := by
    rw [← ArithmeticFunction.vonMangoldt_sum]
    symm
    refine Finset.sum_subset (fun q hq => ?_) (fun q hq hq' => ?_)
    · obtain ⟨-, hq2⟩ := Finset.mem_filter.1 hq
      exact Nat.mem_divisors.2 ⟨hq2, by omega⟩
    · have hqd := Nat.mem_divisors.1 hq
      have hq1 : q = 1 := by
        by_contra hne
        apply hq'
        have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqd.1 (by omega)
        exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, Nat.le_of_dvd (by omega) hqd.1⟩, hqd.1⟩
      rw [hq1, ArithmeticFunction.vonMangoldt_apply_one]
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd (show N ≠ 1 by omega)
  have hpP : p ∈ P :=
    Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hp.two_le, Nat.le_of_dvd (by omega) hpN⟩, hpN⟩
  have hnonneg : ∀ q ∈ P, 0 ≤ Λ q - Λ q ^ 2 / (q * room d q) := fun q hq =>
    sub_nonneg.2 (term_le hd (Finset.mem_Icc.1 (Finset.mem_filter.1 hq).1).1)
  have h1 : Λ p - Λ p ^ 2 / (p * room d p) ≤ ∑ q ∈ P, (Λ q - Λ q ^ 2 / (q * room d q)) :=
    Finset.single_le_sum hnonneg hpP
  have h2 := prime_term_ge hd hp
  have hB : 13 / 10 ≤ Real.log N + d - ∑ q ∈ P, Λ q ^ 2 / (q * room d q) := by
    rw [Finset.sum_sub_distrib] at h1
    rw [hlog]
    linarith
  calc 13 / 10 * c N ^ 2 = c N ^ 2 * (13 / 10) := by ring
    _ ≤ c N ^ 2 * (Real.log N + d - ∑ q ∈ P, Λ q ^ 2 / (q * room d q)) :=
        mul_le_mul_of_nonneg_left hB (sq_nonneg _)

end PivotTop
