import Mathlib
import PrimeNumberTheoremAnd.ZetaBounds
import BallUpper

/-! # The alternating vector at the low zeros, and the rate from above

Plain statement. Under RH, the alternating vector `x_n = (−1)^{n+1}/n` has `|V_x(ρ)| ≤ 20/√N` at every zero of height
`|γ| ≤ 2N` (`dpoly_xa_le`), hence `Q_N(x) ≤ (400K_H(1) + 45)H_N/N` (`form_xa_rh`) and `λ_N ≤ 67(1 + log N)/N` for every
`N ≥ 1` (`rate_upper_rh`). Unconditionally there is a constant `C` with `λ_N ≤ C(1 + log N)/N` for every `N ≥ 1`
(`rate_upper`): if RH fails, the orbit form has a negative integer vector at some level (`BallWeil.rh_iff_form`).

At a zero, `V_x(ρ) = Σ_{n ≤ N}(−1)^{n+1}n^{−s}` with `s = 1 − ρ = ρ̄`, a zero of `ζ` on the line. PNT+'s `ζ₀`
(`Zeta0EqZeta`, `ZetaBnd_aux1b`) gives `Σ_{n ≤ X}n^{−s} = ζ(s) + X^{1−s}/(1 − s) + X^{−s}/2 − sI(X)` with
`|I(X)| ≤ 2/√X`. In the alternating sum to `2K` the main terms at `X = 2K` and `X = K` cancel, so its partial sums
tend to `(1 − 2^{1−s})ζ(s) = 0` (`eta_partial`, `norm_eta_le`), and the tail beyond `N` is at most `20/√N` once
`|Im s| ≤ 2N` (`BallUpper.tail_le`).
-/

open Real Complex Finset MeasureTheory Filter Topology WeilForm WeilTest
open scoped ComplexConjugate

noncomputable section

namespace BallUpperEta

open BallUpper

/-- The Euler–Maclaurin remainder in PNT+'s `ζ₀`. -/
def Iz (X : ℕ) (s : ℂ) : ℂ := ∫ x in Set.Ioi (X : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

lemma sum_eq_zeta0 (X : ℕ) (s : ℂ) :
    ∑ n ∈ Finset.range (X + 1), 1 / (n : ℂ) ^ s =
      riemannZeta0 X s + (X : ℂ) ^ (1 - s) / (1 - s) + (X : ℂ) ^ (-s) / 2 - s * Iz X s := by
  unfold riemannZeta0 Iz
  ring

lemma norm_Iz_le {X : ℕ} (hX : 1 ≤ X) {s : ℂ} (hs : s.re = 1 / 2) : ‖Iz X s‖ ≤ 2 / Real.sqrt X := by
  have hs' : s = ((1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * I := by
    rw [← hs]; exact (Complex.re_add_im s).symm
  have h := ZetaBnd_aux1b X hX (σ := 1 / 2) (t := s.im) (by norm_num)
  rw [← hs'] at h
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have e : (X : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2) = 2 / Real.sqrt X := by
    rw [Real.rpow_neg hX0.le, ← Real.sqrt_eq_rpow]; field_simp
  rw [e] at h
  exact h

lemma norm_natCast_cpow_neg {s : ℂ} (hs : s.re = 1 / 2) {n : ℕ} (hn : 0 < n) :
    ‖(n : ℂ) ^ (-s)‖ = 1 / Real.sqrt n := by
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re, hs, Real.rpow_neg (Nat.cast_nonneg n),
    ← Real.sqrt_eq_rpow, one_div]

/-- `Σ_{n ≤ 2K}(−1)^{n+1}a_n = Σ_{n ≤ 2K}a_n − 2Σ_{m ≤ K}a_{2m}`. -/
lemma sum_alt (a : ℕ → ℂ) (K : ℕ) :
    ∑ n ∈ range (2 * K + 1), (-1) ^ (n + 1) * a n =
      ∑ n ∈ range (2 * K + 1), a n - 2 * ∑ m ∈ range (K + 1), a (2 * m) := by
  induction K with
  | zero => simp only [mul_zero, zero_add, Finset.sum_range_one, pow_one]; ring
  | succ K ih =>
    rw [show 2 * (K + 1) + 1 = 2 * K + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ _ (K + 1), Finset.sum_range_succ a (2 * K + 1 + 1), Finset.sum_range_succ a (2 * K + 1)]
    have h1 : (-1 : ℂ) ^ (2 * K + 1 + 1) = 1 := by
      rw [show 2 * K + 1 + 1 = 2 * (K + 1) by ring, pow_mul]; norm_num
    have h2 : (-1 : ℂ) ^ (2 * K + 1 + 1 + 1) = -1 := by
      rw [show 2 * K + 1 + 1 + 1 = 2 * (K + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
    rw [h1, h2, show 2 * (K + 1) = 2 * K + 1 + 1 by ring]
    ring

/-- **The alternating partial sums at a zero**: for `ζ(s) = 0`, `Re s > 0`, `s ≠ 1` and `K ≥ 1`,
`Σ_{n ≤ 2K}(−1)^{n+1}n^{−s} = −(2K)^{−s}/2 − sI(2K) + 2·2^{−s}sI(K)`, from `ζ₀` at `2K` and at `K`: the main terms
`X^{1−s}/(1 − s)` cancel. -/
lemma eta_partial {s : ℂ} (hz : riemannZeta s = 0) (hs : 0 < s.re) (hs1 : s ≠ 1) {K : ℕ} (hK : 1 ≤ K) :
    ∑ n ∈ range (2 * K + 1), (-1) ^ (n + 1) * (1 / (n : ℂ) ^ s) =
      -((2 : ℂ) ^ (-s) * (K : ℂ) ^ (-s)) / 2 - s * Iz (2 * K) s + 2 * (2 : ℂ) ^ (-s) * (s * Iz K s) := by
  rw [sum_alt (fun n => 1 / (n : ℂ) ^ s) K]
  have h2K := sum_eq_zeta0 (2 * K) s
  have hK' := sum_eq_zeta0 K s
  rw [Zeta0EqZeta (N := 2 * K) (by omega) hs hs1, hz] at h2K
  rw [Zeta0EqZeta (N := K) (by omega) hs hs1, hz] at hK'
  have e : ∀ m : ℕ, 1 / ((2 * m : ℕ) : ℂ) ^ s = (2 : ℂ) ^ (-s) * (1 / (m : ℂ) ^ s) := by
    intro m
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Complex.cpow_neg, one_div, one_div, mul_inv]
    simp
  have hsum2 : ∑ m ∈ range (K + 1), 1 / ((2 * m : ℕ) : ℂ) ^ s =
      (2 : ℂ) ^ (-s) * ∑ m ∈ range (K + 1), 1 / (m : ℂ) ^ s := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => e m
  have hc1 : ((2 * K : ℕ) : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) * (K : ℂ) ^ (1 - s) := by
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, sub_eq_add_neg,
      Complex.cpow_add (x := ((2 : ℕ) : ℂ)) 1 (-s) (by norm_num), Complex.cpow_one]
    push_cast; ring
  have hc2 : ((2 * K : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (K : ℂ) ^ (-s) := by
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]; push_cast; ring
  rw [hc1, hc2] at h2K
  rw [hsum2]
  linear_combination h2K - 2 * (2 : ℂ) ^ (-s) * hK'

lemma norm_eta_le {s : ℂ} (hz : riemannZeta s = 0) (hs : s.re = 1 / 2) {K : ℕ} (hK : 1 ≤ K) :
    ‖∑ n ∈ range (2 * K + 1), (-1) ^ (n + 1) * (1 / (n : ℂ) ^ s)‖ ≤ (1 + 6 * ‖s‖) / Real.sqrt K := by
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  rw [eta_partial hz hs0 hs1 hK]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsK := Real.sqrt_pos.2 hK0
  have h2 : ‖(2 : ℂ) ^ (-s)‖ ≤ 1 := by
    have := norm_natCast_cpow_neg hs (n := 2) (by norm_num)
    rw [Nat.cast_ofNat] at this
    rw [this, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
    exact this
  have hKs : ‖(K : ℂ) ^ (-s)‖ = 1 / Real.sqrt K := norm_natCast_cpow_neg hs (by omega)
  have hI1 : ‖Iz (2 * K) s‖ ≤ 2 / Real.sqrt K := by
    refine (norm_Iz_le (X := 2 * K) (by omega) hs).trans ?_
    refine div_le_div_of_nonneg_left (by norm_num) hsK (Real.sqrt_le_sqrt ?_)
    push_cast; linarith
  have hI2 : ‖Iz K s‖ ≤ 2 / Real.sqrt K := norm_Iz_le hK hs
  have hs0' := norm_nonneg s
  have t1 : ‖-((2 : ℂ) ^ (-s) * (K : ℂ) ^ (-s)) / 2‖ ≤ 1 / 2 * (1 / Real.sqrt K) := by
    rw [norm_div, norm_neg, norm_mul, hKs, Complex.norm_two]
    have := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 1 / Real.sqrt K by positivity)
    linarith
  have t2 : ‖s * Iz (2 * K) s‖ ≤ ‖s‖ * (2 / Real.sqrt K) := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hI1 hs0'
  have t3 : ‖2 * (2 : ℂ) ^ (-s) * (s * Iz K s)‖ ≤ 2 * 1 * (‖s‖ * (2 / Real.sqrt K)) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_two]
    have := mul_le_mul_of_nonneg_left hI2 hs0'
    have h3 : 0 ≤ ‖s‖ * ‖Iz K s‖ := by positivity
    calc 2 * ‖(2 : ℂ) ^ (-s)‖ * (‖s‖ * ‖Iz K s‖) ≤ 2 * 1 * (‖s‖ * ‖Iz K s‖) := by gcongr
      _ ≤ 2 * 1 * (‖s‖ * (2 / Real.sqrt K)) := by gcongr
  calc ‖-((2 : ℂ) ^ (-s) * (K : ℂ) ^ (-s)) / 2 - s * Iz (2 * K) s + 2 * (2 : ℂ) ^ (-s) * (s * Iz K s)‖
      ≤ ‖-((2 : ℂ) ^ (-s) * (K : ℂ) ^ (-s)) / 2‖ + ‖s * Iz (2 * K) s‖ + ‖2 * (2 : ℂ) ^ (-s) * (s * Iz K s)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 1 / 2 * (1 / Real.sqrt K) + ‖s‖ * (2 / Real.sqrt K) + 2 * 1 * (‖s‖ * (2 / Real.sqrt K)) := by linarith
    _ ≤ (1 + 6 * ‖s‖) / Real.sqrt K := by
        rw [show 1 / 2 * (1 / Real.sqrt K) + ‖s‖ * (2 / Real.sqrt K) + 2 * 1 * (‖s‖ * (2 / Real.sqrt K)) =
          (1 / 2 + 6 * ‖s‖) / Real.sqrt K by ring]
        exact div_le_div_of_nonneg_right (by linarith) hsK.le

/-- **The alternating sum vanishes at the zeros up to `20/√N`**: for `ζ(s) = 0`, `Re s = ½` and `|Im s| ≤ 2N`,
`|Σ_{n ≤ N}(−1)^{n+1}n^{−s}| ≤ 20/√N`. The partial sums to `2K` tend to `(1 − 2^{1−s})ζ(s) = 0`
(`norm_eta_le`), and the tails beyond `N` are at most `20/√N` (`BallUpper.tail_le`). -/
theorem alt_le {s : ℂ} (hz : riemannZeta s = 0) (hs : s.re = 1 / 2) {N : ℕ} (hN : 1 ≤ N)
    (him : |s.im| ≤ 2 * N) : ‖∑ n ∈ Icc 1 N, ua s n‖ ≤ 20 / Real.sqrt N := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hterm : ∀ n : ℕ, 1 ≤ n → (-1) ^ (n + 1) * (1 / (n : ℂ) ^ s) = ua s n := by
    intro n hn
    unfold ua
    congr 1
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)), one_div, ← Complex.exp_neg]
    congr 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    ring
  have hsplit : ∀ K : ℕ, N ≤ K → ∑ n ∈ range (2 * K + 1), (-1) ^ (n + 1) * (1 / (n : ℂ) ^ s) =
      ∑ n ∈ Icc 1 N, ua s n + ∑ i ∈ range (2 * K - N), ua s (N + 1 + i) := by
    intro K hK
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (show 1 ≤ 2 * K + 1 by omega),
      ← Finset.sum_Ico_consecutive _ (show 1 ≤ N + 1 by omega) (show N + 1 ≤ 2 * K + 1 by omega),
      Finset.sum_Ico_eq_sum_range _ (N + 1), show 2 * K + 1 - (N + 1) = 2 * K - N by omega,
      Finset.Ico_add_one_right_eq_Icc]
    have h0 : ∑ n ∈ Ico (0 : ℕ) 1, (-1 : ℂ) ^ (n + 1) * (1 / (n : ℂ) ^ s) = 0 := by
      simp [Complex.zero_cpow hs0]
    rw [h0, zero_add]
    congr 1
    · exact Finset.sum_congr rfl fun n hn => hterm n (Finset.mem_Icc.1 hn).1
    · exact Finset.sum_congr rfl fun i _ => hterm (N + 1 + i) (by omega)
  have hbound : ∀ K : ℕ, N ≤ K →
      ‖∑ n ∈ Icc 1 N, ua s n‖ ≤ (1 + 6 * ‖s‖) / Real.sqrt K + 20 / Real.sqrt N := by
    intro K hK
    have he := norm_eta_le hz hs (K := K) (by omega)
    have ht := tail_le hs hN him (2 * K - N)
    rw [hsplit K hK] at he
    have := norm_sub_le (∑ n ∈ Icc 1 N, ua s n + ∑ i ∈ range (2 * K - N), ua s (N + 1 + i))
      (∑ i ∈ range (2 * K - N), ua s (N + 1 + i))
    rw [add_sub_cancel_right] at this
    linarith
  have hlim : Tendsto (fun K : ℕ => (1 + 6 * ‖s‖) / Real.sqrt K + 20 / Real.sqrt N) atTop
      (𝓝 (0 + 20 / Real.sqrt N)) :=
    (tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).add
      tendsto_const_nhds
  rw [zero_add] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨N, hbound⟩)

/-- **The low zeros**: under RH, `|V_x(ρ)| ≤ 20/√N` for the alternating vector `x_n = (−1)^{n+1}/n` at every zero
of height `|γ| ≤ 2N`. Here `V_x(ρ) = Σ_{n ≤ N}(−1)^{n+1}n^{−(1−ρ)}` and `ζ(1 − ρ) = ζ(ρ̄) = 0`. -/
theorem dpoly_xa_le (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {q : ZIdx}
    (hq : |(zetaZeroFamily q).im| ≤ 2 * N) : ‖BallRate.dpoly N xa q‖ ≤ 20 / Real.sqrt N := by
  rw [dpoly_xa]
  have hre := line_of_RH hRH q
  have hconj : 1 - zetaZeroFamily q = conj (zetaZeroFamily q) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hre]; norm_num
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub]
  have hz : riemannZeta (1 - zetaZeroFamily q) = 0 := by
    rw [hconj, riemannZeta_conj]
    have h0 : riemannZeta (zetaZeroFamily q) = 0 := q.1.2.1
    rw [h0, map_zero]
  refine alt_le hz ?_ hN ?_
  · simp only [Complex.sub_re, Complex.one_re, hre]; norm_num
  · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]; exact hq

/-- **The form of the alternating vector** (RH): `Q_N(x) ≤ (400K_H(1) + 45)H_N/N` for `x_n = (−1)^{n+1}/n`. -/
theorem form_xa_rh (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) :
    BallWeil.form N xa ≤ (400 * BallWeil.kψ 1 + 45) * Hn N / N := by
  refine form_xa_le hRH hN fun q hq => ?_
  have h := dpoly_xa_le hRH hN hq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc ‖BallRate.dpoly N xa q‖ ^ 2 ≤ (20 / Real.sqrt N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 400 / N := by rw [div_pow, Real.sq_sqrt hN0.le]; norm_num

/-- **The upper bound `λ_N ≤ 67(1 + log N)/N`** (RH): for every `N ≥ 1`, the alternating vector `x_n = (−1)^{n+1}/n`
has `Q_N(x) ≤ 67(1 + log N)/N·Σ_{n ≤ N}x_n²`. With `BallSharp.rate_sharp`, `λ_N` lies between `1/(22e⁸N)` and
`67(1 + log N)/N`. -/
theorem rate_upper_rh (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) :
    BallWeil.form N xa ≤ 67 * (1 + Real.log N) / N * ∑ n ∈ Icc 1 N, xa n ^ 2 := by
  have h := form_xa_rh hRH hN
  have hH := Hn_le N
  have hH0 := Hn_nonneg N
  have hS := sum_xa_sq_ge hN
  have hk : BallWeil.kψ 1 < 0.0539 := by rw [BallWeil.kψ_one]; exact WeilTest.hadamard_const_lt
  have hk0 := BallWeil.kψ_one_pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hC : 0 ≤ 67 * (1 + Real.log N) / N := by positivity
  calc BallWeil.form N xa ≤ (400 * BallWeil.kψ 1 + 45) * Hn N / N := h
    _ ≤ 67 * (1 + Real.log N) / N := by
        refine div_le_div_of_nonneg_right ?_ hN0.le
        exact mul_le_mul (by linarith) hH hH0 (by norm_num)
    _ = 67 * (1 + Real.log N) / N * 1 := (mul_one _).symm
    _ ≤ 67 * (1 + Real.log N) / N * ∑ n ∈ Icc 1 N, xa n ^ 2 := mul_le_mul_of_nonneg_left hS hC

/-- **`λ_N ≪ log N/N`, unconditionally**: there is a constant `C` such that for every `N ≥ 1` some real `x` with
`Σ_{n ≤ N}x_n² > 0` has `Q_N(x) ≤ C(1 + log N)/N·Σ_{n ≤ N}x_n²`. Under RH this is `rate_upper_rh` with `C = 67`. If RH
fails, some integer vector has `Q_{N₀}(x) < 0` (`BallWeil.rh_iff_form`); extended by zero it serves every `N ≥ N₀`,
and `δ₁` serves `N < N₀` with `C = N₀K_H(1)`. -/
theorem rate_upper : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∃ x : ℕ → ℝ, 0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
    BallWeil.form N x ≤ C * (1 + Real.log N) / N * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  by_cases hRH : RiemannHypothesis
  · refine ⟨67, fun N hN => ⟨xa, ?_, rate_upper_rh hRH hN⟩⟩
    linarith [sum_xa_sq_ge hN]
  · have h : ¬∀ (N : ℕ) (x : ℕ → ℤ), 0 ≤ BallWeil.form N (fun n => (x n : ℝ)) :=
      fun h => hRH (BallWeil.rh_iff_form.2 h)
    push Not at h
    obtain ⟨N₀, x₀, hx₀⟩ := h
    have hk := BallWeil.kψ_one_pos
    refine ⟨N₀ * BallWeil.kψ 1, fun N hN => ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    by_cases hNN : N₀ ≤ N
    · set y : ℕ → ℝ := fun n => if n ≤ N₀ then (x₀ n : ℝ) else 0 with hy
      have hform : BallWeil.form N y = BallWeil.form N₀ (fun n => (x₀ n : ℝ)) := by
        rw [form_extend hNN (fun n hn => by simp only [hy]; exact ite_eq_right (by omega))]
        exact BallWeil.form_congr fun n hn => by
          simp only [hy]; exact ite_eq_left (Finset.mem_Icc.1 hn).2
      have hne : ∃ n ∈ Icc 1 N₀, (x₀ n : ℝ) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have h0 : BallWeil.form N₀ (fun n => (x₀ n : ℝ)) = BallWeil.form N₀ (fun _ => 0) :=
          BallWeil.form_congr hcon
        have h00 : BallWeil.form N₀ (fun _ => (0 : ℝ)) = 0 := by unfold BallWeil.form; simp
        linarith
      obtain ⟨n, hn, hxn⟩ := hne
      have hmem : n ∈ Icc 1 N := Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hn).1, (Finset.mem_Icc.1 hn).2.trans hNN⟩
      have hyn : y n = (x₀ n : ℝ) := by simp only [hy]; exact ite_eq_left (Finset.mem_Icc.1 hn).2
      have hpos : 0 < ∑ m ∈ Icc 1 N, y m ^ 2 := by
        have h1 := Finset.single_le_sum (f := fun m => y m ^ 2) (fun m _ => sq_nonneg _) hmem
        have h2 : 0 < y n ^ 2 := by
          rw [hyn]; exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hxn))
        linarith
      refine ⟨y, hpos, ?_⟩
      have hC : 0 ≤ (N₀ : ℝ) * BallWeil.kψ 1 * (1 + Real.log N) / N * ∑ m ∈ Icc 1 N, y m ^ 2 := by
        have : 0 ≤ (N₀ : ℝ) * BallWeil.kψ 1 * (1 + Real.log N) / N := by positivity
        exact mul_nonneg this hpos.le
      rw [hform]
      linarith
    · have hlt : (N : ℝ) < N₀ := by exact_mod_cast lt_of_not_ge hNN
      have hS : ∑ n ∈ Icc 1 N, (if n = 1 then (1 : ℝ) else 0) ^ 2 = 1 := by
        rw [Finset.sum_eq_single 1 (fun b _ hb => by simp [hb])
          (fun h => absurd (Finset.mem_Icc.2 ⟨le_rfl, hN⟩) h)]
        simp
      have hF : BallWeil.form N (fun n => if n = 1 then 1 else 0) = BallWeil.kψ 1 := by
        rw [form_extend hN (fun n hn => ite_eq_right (by omega)), form_delta]
      refine ⟨fun n => if n = 1 then 1 else 0, by rw [hS]; norm_num, ?_⟩
      rw [hS, hF, mul_one, le_div_iff₀ hN0]
      have h1 := mul_le_mul_of_nonneg_left hlt.le hk.le
      have h2 := mul_nonneg (mul_nonneg (Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀) hk.le) hlog
      nlinarith

end BallUpperEta
