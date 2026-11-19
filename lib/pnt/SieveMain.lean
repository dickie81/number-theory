/-
# The primes of `(x, 2x]`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements.

* `primes_dyadic_ge`: for `ε > 0`, the primes of `(⌊x⌋, ⌊2x⌋]` number at least `(1 − ε)x/log x` for large `x`.
* `ev_log_le`: for `c > 0` and `r > 0`, `log q ≤ c q^r` for large `q`.

The proof of `primes_dyadic_ge` is `SieveRough.theta_near` at `x` and `2x`.

The file imports `SieveDrop.lean`.
-/
import SieveDrop

open Real Finset Filter SieveFamily SieveChain SieveDecomp SieveLeaves SieveQ SieveRough SieveDrop SieveRoute
open scoped Chebyshev

namespace SieveMain

open Classical

variable [Route] [RouteOK] [SieveCert.Grid]

/-! ### The primes of `(x, 2x]` -/

omit [Route] [RouteOK] [SieveCert.Grid] in
/-- For `ε > 0`, the primes of `(⌊x⌋, ⌊2x⌋]` number at least `(1 − ε)x/log x` for large `x`. -/
theorem primes_dyadic_ge {ε : ℝ} (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop,
    (1 - ε) * (x / Real.log x) ≤ (((Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime).card : ℝ) := by
  have hT := theta_near (ε := 1) one_pos
  have hT2 : ∀ᶠ x : ℝ in atTop, |θ (2 * x) - 2 * x| ≤ 1 * (2 * x) / Real.log (2 * x) :=
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually hT
  filter_upwards [hT, hT2, eventually_ge_atTop (Real.exp (4 / ε)), eventually_ge_atTop (Real.exp 1)]
    with x h1 h2 h3 h4
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) h4
  have hlx1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) h4
  have hlx : 4 / ε ≤ Real.log x := by
    rw [← Real.log_exp (4 / ε)]
    exact Real.log_le_log (Real.exp_pos _) h3
  have hl2 : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2x : Real.log x ≤ Real.log (2 * x) := by linarith
  -- `Σ log p = θ(2x) − θ(x) ≥ x − 3x/log x`
  have hsum := sum_log_primes_dyadic hx0.le
  set P := (Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime with hP
  have hθ : x - 3 * x / Real.log x ≤ θ (2 * x) - θ x := by
    have e1 := (abs_le.1 h1).2
    have e2 := (abs_le.1 h2).1
    have e3 : 1 * (2 * x) / Real.log (2 * x) ≤ 2 * x / Real.log x := by
      rw [one_mul]
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) hl2x
    have e4 : 1 * x / Real.log x = x / Real.log x := by ring
    have e5 : 3 * x / Real.log x = 2 * x / Real.log x + x / Real.log x := by ring
    linarith
  have hle : ∑ p ∈ P, Real.log p ≤ (P.card : ℝ) * Real.log (2 * x) := by
    have : ∀ p ∈ P, Real.log p ≤ Real.log (2 * x) := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
      exact Real.log_le_log hp0 ((Nat.cast_le.2 hp.1.2).trans (Nat.floor_le (by linarith)))
    calc ∑ p ∈ P, Real.log p ≤ ∑ _p ∈ P, Real.log (2 * x) := Finset.sum_le_sum this
      _ = (P.card : ℝ) * Real.log (2 * x) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hlx0 : 0 < Real.log x := by linarith
  have h2x0 : 0 < Real.log (2 * x) := by linarith
  -- `(1 − ε)(x/log x)·log 2x ≤ x − 3x/log x`
  have hkey : (1 - ε) * (x / Real.log x) * Real.log (2 * x) ≤ x - 3 * x / Real.log x := by
    rw [hl2]
    have h5 : (1 - ε) * (x / Real.log x) * (Real.log 2 + Real.log x) =
        (1 - ε) * x + (1 - ε) * x * Real.log 2 / Real.log x := by
      field_simp
      ring
    rw [h5]
    have h6 : ε * Real.log x ≥ 4 := by
      rw [div_le_iff₀ hε] at hlx
      linarith
    have h7 : (1 - ε) * x * Real.log 2 / Real.log x + 3 * x / Real.log x ≤ ε * x := by
      rw [← add_div, div_le_iff₀ hlx0]
      have hA : x * 4 ≤ x * (ε * Real.log x) := mul_le_mul_of_nonneg_left h6 hx0.le
      have hB : (1 - ε) * Real.log 2 ≤ 1 := by
        by_cases hε1 : ε ≤ 1
        · have : (1 - ε) * Real.log 2 ≤ 1 * Real.log 2 :=
            mul_le_mul_of_nonneg_right (by linarith) hlog20.le
          linarith
        · have : (1 - ε) * Real.log 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog20.le
          linarith
      have hC : x * ((1 - ε) * Real.log 2) ≤ x * 1 := mul_le_mul_of_nonneg_left hB hx0.le
      nlinarith
    linarith
  rw [hsum] at hle
  rw [← div_le_iff₀ h2x0] at hle
  have : (1 - ε) * (x / Real.log x) ≤ (x - 3 * x / Real.log x) / Real.log (2 * x) := by
    rw [le_div_iff₀ h2x0]
    exact hkey
  linarith [this, (div_le_div_of_nonneg_right hθ h2x0.le)]

/-! ### `log q` against a power of `q` -/

omit [Route] [RouteOK] [SieveCert.Grid] in
/-- `log q ≤ c q^r` for large `q`, any `c > 0`, `r > 0`. -/
theorem ev_log_le {c r : ℝ} (hc : 0 < c) (hr : 0 < r) : ∀ᶠ q : ℕ in atTop, Real.log q ≤ c * (q : ℝ) ^ r := by
  have h := (isLittleO_log_rpow_atTop hr).bound hc
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 1] with q hq hq1
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  rw [Real.norm_of_nonneg (Real.log_nonneg hq0), Real.norm_of_nonneg (by positivity)] at hq
  exact hq

end SieveMain
