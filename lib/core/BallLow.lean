import Mathlib
import BallUpper

/-! # The low zeros: what the zeros above height `8N` can give, and the short vectors

Plain statement. Under RH, with `Q_N(x) = Σ_ρ |V_x(ρ)|²/(¼ + γ²)` (`BallWeil.form`, `BallRate.hasSum_form`),
`V_x(ρ) = Σ_{n ≤ N} x_n n^ρ`, `c_n = x_n√n` and Landau's slack `G(c) = (log N + log 4 + 1)Σc_n² − L(c)`
(`BallSharp.landauSlack`):

- **The zeros above `8N` give at most `(4Σx_n² n + G(c)/2)/N`** plus a pole term (`high_le`): for every finite set
  `F` of zeros of height `|γ| > 8N`, `Σ_{ρ ∈ F}|V_x(ρ)|²/(¼ + γ²) ≤ (4Σc_n² + G(c)/2)/N + (Σ|c_j|√j)(Σ|c_j|/√j)/N²`.
  It is `BallUpper.upper_mean` on the dyadic shells `2^k·8N < |γ| ≤ 2^{k+1}·8N`. With the spread
  `A = Σx_n² n/Σx_n²` and the slack `B = G(c)/Σx_n²`, the zeros above `8N` contribute `O((A + B)/N)·Σx_n²` (and the
  pole term, `(Σ|x_j| j)(Σ|x_j|)/N²`, which is small for the vectors that matter). `BallSharp.rate_slack` gets
  `(A + B)/(22e⁸N)` from the zeros up to `e⁸N`. So for the vectors with `A + B = o(log N)`, a lower bound
  `λ_N ≫ log N/N` has to come from the zeros below height `8N`.
- **Short vectors are seen** (`short_le`): a vector supported on `[1, M]` has `Q_N(x) ≥ Σx_n²/(22e⁸M)` for every
  `N ≥ M` (`BallUpper.form_extend`, then `BallSharp.rate_sharp` at `M`). So a vector with `Q_N(x) ≤ ε(log N/N)Σx_n²`
  is not supported below `N/(22e⁸ε log N)`.
-/

open Real Finset WeilForm WeilTest BallDensity BallSharp BallUpper
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace BallLow

/-- **Short vectors** (RH): if `x_n = 0` for `n > M`, then `Q_N(x) ≥ Σ_{n ≤ N}x_n²/(22e⁸M)` for every `N ≥ M ≥ 1`. -/
theorem short_le (hRH : RiemannHypothesis) {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) (x : ℕ → ℝ)
    (hx : ∀ n, M < n → x n = 0) :
    1 / (22 * Real.exp 8 * M) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x := by
  rw [form_extend hMN hx]
  have hs : ∑ n ∈ Icc 1 N, x n ^ 2 = ∑ n ∈ Icc 1 M, x n ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hMN) fun n hn hnM => ?_
    have : M < n := by
      simp only [Finset.mem_Icc, not_and, not_le] at hn hnM
      exact hnM hn.1
    simp [hx n this]
  rw [hs]
  exact rate_sharp hRH hM x

lemma sum_inv_two_pow (K : ℕ) : ∑ k ∈ range K, (1 : ℝ) / 2 ^ k = 2 - 2 / 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    field_simp
    ring

lemma sum_k_div_two_pow (K : ℕ) : ∑ k ∈ range K, (k : ℝ) / 2 ^ k = 2 - 2 * ((K : ℝ) + 1) / 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    field_simp
    ring

lemma sum_inv_four_pow (K : ℕ) : ∑ k ∈ range K, (1 : ℝ) / 4 ^ k = 4 / 3 - 4 / 3 / 4 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    field_simp
    ring

/-- The shell `2^k·8N < |γ| ≤ 2^{k+1}·8N`: `upper_mean` at `r = 2^{k+1}·8N`, divided by `(2^k·8N)²`. -/
lemma shell_bound (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) (k : ℕ) :
    1 / (2 ^ k * (8 * N)) ^ 2 * ∑ q ∈ BallRate.zerosUpTo (2 ^ (k + 1) * (8 * N)), ‖BallRate.dpoly N x q‖ ^ 2 ≤
      π / (16 * N) * (1 / 2 ^ k) * ((((k : ℝ) + 4) * Real.log 2 + (1 / 5 + 22 / π - Real.log 4 - 1)) *
        S2 N (fun n => x n * Real.sqrt n) + landauSlack N (fun n => x n * Real.sqrt n)) +
      46 / (64 * N ^ 2) * (1 / 4 ^ k) * ((∑ j ∈ Icc 1 N, |x j * Real.sqrt j| * Real.sqrt j) *
        ∑ j ∈ Icc 1 N, |x j * Real.sqrt j| / Real.sqrt j) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set r : ℝ := 2 ^ (k + 1) * (8 * N) with hr
  have h2k : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ one_le_two
  have hr8 : 8 * (N : ℝ) ≤ r := by rw [hr]; nlinarith
  have hUM := upper_mean hRH hN hr8 x
  set S := S2 N (fun n => x n * Real.sqrt n) with hS
  set G := landauSlack N (fun n => x n * Real.sqrt n) with hG
  set P := (∑ j ∈ Icc 1 N, |x j * Real.sqrt j| * Real.sqrt j) * ∑ j ∈ Icc 1 N, |x j * Real.sqrt j| / Real.sqrt j
    with hP
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hland : 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N (fun n => x n * Real.sqrt n) n =
      (Real.log N + (Real.log 4 + 1)) * S - G := by
    rw [hG]; unfold landauSlack; ring
  rw [hland] at hUM
  -- `log(r/2π) ≤ (k + 4)log 2 + log N`
  have hlogr : Real.log (r / (2 * π)) ≤ ((k : ℝ) + 4) * Real.log 2 + Real.log N := by
    have h1 : Real.log (r / (2 * π)) ≤ Real.log r :=
      Real.log_le_log (by positivity) (div_le_self (by positivity) (by linarith [Real.pi_gt_three]))
    have h2 : Real.log r = ((k : ℝ) + 4) * Real.log 2 + Real.log N := by
      rw [hr, show (2 : ℝ) ^ (k + 1) * (8 * N) = 2 ^ (k + 4) * N by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num]; ring]
      rw [Real.log_mul (by positivity) hN0.ne', Real.log_pow]
      push_cast; ring
    linarith
  have hcoef : (Real.log (r / (2 * π)) + 1 / 5 + 22 / π) * S - ((Real.log N + (Real.log 4 + 1)) * S - G) ≤
      (((k : ℝ) + 4) * Real.log 2 + (1 / 5 + 22 / π - Real.log 4 - 1)) * S + G := by
    nlinarith
  have hpr : 0 ≤ π * r / 4 := by positivity
  have hstep : ∑ q ∈ BallRate.zerosUpTo r, ‖BallRate.dpoly N x q‖ ^ 2 ≤
      π * r / 4 * ((((k : ℝ) + 4) * Real.log 2 + (1 / 5 + 22 / π - Real.log 4 - 1)) * S + G) + 46 * P :=
    hUM.trans (by nlinarith [mul_le_mul_of_nonneg_left hcoef hpr])
  have hw : (0 : ℝ) ≤ 1 / (2 ^ k * (8 * (N : ℝ))) ^ 2 := by positivity
  refine (mul_le_mul_of_nonneg_left hstep hw).trans (le_of_eq ?_)
  have h4 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hr, pow_succ, h4]
  field_simp
  ring

/-- The sum over the shells: with `κ = 1/5 + 22/π − log 4 − 1`, `S, G, P ≥ 0`,
`Σ_{k < K}(π/(16·2^k N))(((k + 4)log 2 + κ)S + G) + 46P/(64·4^k N²) ≤ (4S + G/2)/N + P/N²`. -/
lemma assemble {N : ℕ} (hN0 : (0 : ℝ) < N) {S G P : ℝ} (hS0 : 0 ≤ S) (hG0 : 0 ≤ G) (hP0 : 0 ≤ P) (K : ℕ) :
    ∑ k ∈ range K, (π / (16 * N) * (1 / 2 ^ k) *
        ((((k : ℝ) + 4) * Real.log 2 + (1 / 5 + 22 / π - Real.log 4 - 1)) * S + G) +
      46 / (64 * N ^ 2) * (1 / 4 ^ k) * P) ≤ (4 * S + G / 2) / N + P / N ^ 2 := by
  set κ : ℝ := 1 / 5 + 22 / π - Real.log 4 - 1 with hκ
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hπ22 : 0 ≤ 22 / π := by positivity
  have hc4 : 0 ≤ 4 * Real.log 2 + κ := by rw [hκ, hl4]; linarith
  rw [Finset.sum_add_distrib]
  have e1 : ∑ k ∈ range K, π / (16 * N) * (1 / 2 ^ k) * ((((k : ℝ) + 4) * Real.log 2 + κ) * S + G) =
      π / (16 * N) * (Real.log 2 * S * ∑ k ∈ range K, (k : ℝ) / 2 ^ k +
        ((4 * Real.log 2 + κ) * S + G) * ∑ k ∈ range K, (1 : ℝ) / 2 ^ k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k ∈ range K, 46 / (64 * N ^ 2) * (1 / 4 ^ k) * P =
      46 / (64 * N ^ 2) * P * ∑ k ∈ range K, (1 : ℝ) / 4 ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2]
  -- the geometric sums
  have g1 : ∑ k ∈ range K, (k : ℝ) / 2 ^ k ≤ 2 := by
    rw [sum_k_div_two_pow]; have : 0 ≤ 2 * ((K : ℝ) + 1) / 2 ^ K := by positivity
    linarith
  have g2 : ∑ k ∈ range K, (1 : ℝ) / 2 ^ k ≤ 2 := by
    rw [sum_inv_two_pow]; have : 0 ≤ 2 / (2 : ℝ) ^ K := by positivity
    linarith
  have g3 : ∑ k ∈ range K, (1 : ℝ) / 4 ^ k ≤ 4 / 3 := by
    rw [sum_inv_four_pow]; have : 0 ≤ 4 / 3 / (4 : ℝ) ^ K := by positivity
    linarith
  have hlS : 0 ≤ Real.log 2 * S := mul_nonneg (by linarith) hS0
  have hcS : 0 ≤ (4 * Real.log 2 + κ) * S + G := add_nonneg (mul_nonneg hc4 hS0) hG0
  have hin : Real.log 2 * S * ∑ k ∈ range K, (k : ℝ) / 2 ^ k +
      ((4 * Real.log 2 + κ) * S + G) * ∑ k ∈ range K, (1 : ℝ) / 2 ^ k ≤
      Real.log 2 * S * 2 + ((4 * Real.log 2 + κ) * S + G) * 2 :=
    add_le_add (mul_le_mul_of_nonneg_left g1 hlS) (mul_le_mul_of_nonneg_left g2 hcS)
  have hT1 := mul_le_mul_of_nonneg_left hin (show 0 ≤ π / (16 * N) by positivity)
  -- `(π/16)(10 log 2 + 2κ) = (π/16)(6 log 2 − 8/5) + 11/4 ≤ 4` and `π/8 ≤ 1/2`
  have e3 : π / (16 * N) * (Real.log 2 * S * 2 + ((4 * Real.log 2 + κ) * S + G) * 2) =
      (π / 16 * (6 * Real.log 2 - 8 / 5) + 11 / 4) * (S / N) + π / 8 * (G / N) := by
    rw [hκ, hl4]; field_simp; ring
  have hcoef : π / 16 * (6 * Real.log 2 - 8 / 5) + 11 / 4 ≤ 4 := by
    have h1 : 6 * Real.log 2 - 8 / 5 ≤ 3 := by linarith
    have h2 : π / 16 * (6 * Real.log 2 - 8 / 5) ≤ π / 16 * 3 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hSN : 0 ≤ S / N := div_nonneg hS0 hN0.le
  have hGN : 0 ≤ G / N := div_nonneg hG0 hN0.le
  have hT1' : (π / 16 * (6 * Real.log 2 - 8 / 5) + 11 / 4) * (S / N) + π / 8 * (G / N) ≤
      4 * (S / N) + 1 / 2 * (G / N) :=
    add_le_add (mul_le_mul_of_nonneg_right hcoef hSN)
      (mul_le_mul_of_nonneg_right (by linarith) hGN)
  have hT2 : 46 / (64 * N ^ 2) * P * ∑ k ∈ range K, (1 : ℝ) / 4 ^ k ≤ 46 / (64 * N ^ 2) * P * (4 / 3) :=
    mul_le_mul_of_nonneg_left g3 (by positivity)
  have e4 : 46 / (64 * (N : ℝ) ^ 2) * P * (4 / 3) = 23 / 24 * (P / N ^ 2) := by field_simp; ring
  have hPN : 0 ≤ P / N ^ 2 := by positivity
  have e5 : (4 * S + G / 2) / N = 4 * (S / N) + 1 / 2 * (G / N) := by ring
  rw [e3] at hT1
  rw [e5]
  linarith

/-- **The zeros above `8N`** (RH): for every finite set `F` of zeros of height `|γ| > 8N`,
`Σ_{ρ ∈ F}|V_x(ρ)|²/(¼ + γ²) ≤ (4Σc_n² + G(c)/2)/N + (Σ|c_j|√j)(Σ|c_j|/√j)/N²` with `c_n = x_n√n`: the shells
`2^k·8N < |γ| ≤ 2^{k+1}·8N` cost `π/(16·2^k N)·(((k + 4)log 2 + κ)Σc² + G)` and a pole term each (`shell_bound`),
`κ = 1/5 + 22/π − log 4 − 1`, and `Σ_k 2^{−k} ≤ 2`, `Σ_k k2^{−k} ≤ 2`, `Σ_k 4^{−k} ≤ 4/3`. -/
theorem high_le (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) (F : Finset ZIdx)
    (hF : ∀ q ∈ F, 8 * (N : ℝ) < |(zetaZeroFamily q).im|) :
    ∑ q ∈ F, ‖BallRate.dpoly N x q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤
      (4 * S2 N (fun n => x n * Real.sqrt n) + landauSlack N (fun n => x n * Real.sqrt n) / 2) / N +
        (∑ j ∈ Icc 1 N, |x j * Real.sqrt j| * Real.sqrt j) *
          (∑ j ∈ Icc 1 N, |x j * Real.sqrt j| / Real.sqrt j) / N ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set S := S2 N (fun n => x n * Real.sqrt n) with hS
  set G := landauSlack N (fun n => x n * Real.sqrt n) with hG
  set P := (∑ j ∈ Icc 1 N, |x j * Real.sqrt j| * Real.sqrt j) * ∑ j ∈ Icc 1 N, |x j * Real.sqrt j| / Real.sqrt j
    with hP
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hG0 : 0 ≤ G := landauSlack_nonneg N _
  have hP0 : 0 ≤ P := mul_nonneg (Finset.sum_nonneg fun j _ => by positivity)
    (Finset.sum_nonneg fun j _ => by positivity)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((∑ q ∈ F, |(zetaZeroFamily q).im|) / (8 * N)) one_lt_two
  have hFK : ∀ q ∈ F, |(zetaZeroFamily q).im| ≤ 2 ^ K * (8 * N) := by
    intro q hq
    have h1 : |(zetaZeroFamily q).im| ≤ ∑ q ∈ F, |(zetaZeroFamily q).im| :=
      Finset.single_le_sum (f := fun q => |(zetaZeroFamily q).im|) (fun q _ => abs_nonneg _) hq
    rw [div_lt_iff₀ (by positivity)] at hK
    linarith
  set V : ZIdx → ℝ := fun q => ‖BallRate.dpoly N x q‖ ^ 2 with hV
  have hV0 : ∀ q, 0 ≤ V q := fun q => sq_nonneg _
  have hTn : ∀ q k, 0 ≤ (if |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) then
      V q * (1 / (2 ^ k * (8 * N)) ^ 2) else 0) := by
    intro q k
    split_ifs
    · exact mul_nonneg (hV0 q) (by positivity)
    · exact le_rfl
  -- each zero lies in one shell
  have hpt : ∀ q ∈ F, V q / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤
      ∑ k ∈ range K, (if |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) then
        V q * (1 / (2 ^ k * (8 * N)) ^ 2) else 0) := by
    intro q hq
    have hy : 1 < |(zetaZeroFamily q).im| / (8 * N) := by
      rw [lt_div_iff₀ (by positivity)]; linarith [hF q hq]
    have hyK : |(zetaZeroFamily q).im| / (8 * N) ≤ 2 ^ K := by
      rw [div_le_iff₀ (by positivity)]; exact hFK q hq
    obtain ⟨k, hk, hk1, hk2⟩ := exists_dyadic hy hyK
    have hRk : 2 ^ k * (8 * N) < |(zetaZeroFamily q).im| := by
      rw [lt_div_iff₀ (by positivity)] at hk1; linarith
    have hRk1 : |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) := by
      rw [div_le_iff₀ (by positivity)] at hk2; linarith
    have hsingle := Finset.single_le_sum (f := fun k => if |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) then
      V q * (1 / (2 ^ k * (8 * N)) ^ 2) else 0) (fun k _ => hTn q k) (Finset.mem_range.2 hk)
    simp only [ite_eq_left hRk1] at hsingle
    have hR0 : (0 : ℝ) < 2 ^ k * (8 * N) := by positivity
    have : V q / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤ V q * (1 / (2 ^ k * (8 * N)) ^ 2) := by
      rw [mul_one_div]
      refine div_le_div_of_nonneg_left (hV0 q) (by positivity) ?_
      nlinarith [abs_nonneg (zetaZeroFamily q).im, sq_abs (zetaZeroFamily q).im]
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_comm]
  -- each shell
  have hshell : ∀ k ∈ range K, ∑ q ∈ F, (if |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) then
      V q * (1 / (2 ^ k * (8 * N)) ^ 2) else 0) ≤
      π / (16 * N) * (1 / 2 ^ k) * ((((k : ℝ) + 4) * Real.log 2 + (1 / 5 + 22 / π - Real.log 4 - 1)) * S + G) +
        46 / (64 * N ^ 2) * (1 / 4 ^ k) * P := by
    intro k _
    refine (sum_ite_le F (by positivity) V hV0).trans ?_
    exact shell_bound hRH hN x k
  refine (Finset.sum_le_sum hshell).trans ?_
  exact assemble hN0 hS0 hG0 hP0 K

end BallLow
