import Mathlib
import BallSampling
import ShortWeil
import DigammaStirling

/-! # The density of the zeros samples the Dirichlet polynomials: `λ_N ≥ 10⁻¹²/(N log³N)` under RH

Plain statement. Under RH the orbit form is `Q_N(x) = Σ_ρ |V_x(ρ)|²/(¼ + γ²)` with `V_x(ρ) = Σ_{n ≤ N} x_n n^ρ`
(`BallRate.hasSum_form`). This module bounds it below with no hypothesis on the zeros beyond RH, by testing Weil's
explicit formula (`WeilForm.weilExplicit_zeta`, proved, no RH input) against
`h(z) = D(z)D(−z)(w(z − T₀) + w(z + T₀))`, where `D(z) = Σ_{n ≤ N} c_n e^{−iz log n}`, `c_n = x_n√n`, and
`w(z) = e^{−z²/(2σ²)}`. It is even, holomorphic and Gaussian-small in the strip (`striptest_htest`), and on the real
line `h(t) = |D(t)|²W(t)`, so under RH the zero side is `Σ_ρ |V_x(ρ)|²W(γ) ≤ 2(1 + 2T₀² + 4σ²)Q_N(x)`
(`zero_side_le`). On the other side:
* the archimedean term is the density of the zeros, `(1/2π)log(t/2π)` per unit height, against `|D|²W`: at least
  `(1/2π)(log(T₀/4π) − 3)∫|D|²W` up to a Gaussian tail (`arch_ge`, from Stirling for `Re ψ(¼ + ir/2)`);
* `∫|D|²W = Ŵ(0)Σc_n² + O(e^{−σ²/(16N²)})`, `Ŵ(0) = 2σ√(2π)` (`integral_htestR_ge`), since distinct
  frequencies `log j` are `1/N` apart;
* the prime side is Landau's form `(Ŵ(0)/2π)·2Σ_n Λ(n)n^{−1/2}Σ_{jn ≤ N} c_j c_{jn}` on the exact matches
  `j' = jn`, plus the near misses, `|log j' − log(jn)| ≥ 1/(2N)` (`sep_log`, `prime_le`); a Schur test bounds
  Landau's form by `(log N + log 4 + 4)Σc_n²` (`landau_le`, from Mertens' bound `mertens_le`).
So the zeros near height `T₀` sample the polynomials of length `N` as soon as `log(T₀/4π) − 3` exceeds
`log N + log 4 + 4` (`density_bound`): density against bandwidth, the Beurling–Landau condition, with the arithmetic
of the prime powers made explicit. At `σ = 32N log N` and `T₀ = 10⁶N log²N` the errors are below `σ/(2N)`
(`errD_le`) and `λ_N ≥ 10⁻¹²/(N log³N)` for every `N ≥ 3` (`rate_rh`): the rate of
`BallRate.rate_of_sampling` at `θ = 0`, up to logarithms, with RH as the only hypothesis.
-/

open Real Complex Finset MeasureTheory WeilForm WeilTest DirMean
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace BallDensity

/-! ## Mertens' bound and the Landau form -/

lemma Icc_one_eq_Ioc (M : ℕ) : Icc 1 M = Ioc 0 M := by
  simpa using Finset.Icc_add_one_left_eq_Ioc 0 M

/-- `Σ_{m ≤ M} log m = Σ_{n ≤ M} Λ(n)·⌊M/n⌋`. -/
lemma sum_log_eq (M : ℕ) :
    ∑ m ∈ Icc 1 M, Real.log m = ∑ n ∈ Icc 1 M, Λ n * ((M / n : ℕ) : ℝ) := by
  have h1 : ∑ m ∈ Icc 1 M, Real.log m = ∑ m ∈ Icc 1 M, ∑ n ∈ m.divisors, Λ n :=
    Finset.sum_congr rfl fun m _ => ArithmeticFunction.vonMangoldt_sum.symm
  rw [h1, Finset.sum_comm' (t' := Icc 1 M) (s' := fun n => (Icc 1 M).filter (n ∣ ·))]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    have e : (Icc 1 M).filter (n ∣ ·) = (Ioc 0 M).filter (n ∣ ·) := by rw [Icc_one_eq_Ioc]
    rw [e]
    exact_mod_cast Nat.Ioc_filter_dvd_card_eq_div M n
  · intro m n
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hm1, hmM⟩, hnm, -⟩
      have hn1 : 1 ≤ n := Nat.pos_of_dvd_of_pos hnm (by omega)
      exact ⟨⟨⟨hm1, hmM⟩, hnm⟩, hn1, (Nat.le_of_dvd (by omega) hnm).trans hmM⟩
    · rintro ⟨⟨⟨hm1, hmM⟩, hnm⟩, -, -⟩
      exact ⟨⟨hm1, hmM⟩, hnm, by omega⟩

/-- `M·Σ_{n ≤ M} Λ(n)/n ≤ Σ_{m ≤ M} log m + ψ(M)`, from `Σ_{m ≤ M} log m = Σ_n Λ(n)⌊M/n⌋` and
`⌊M/n⌋ ≥ M/n − 1`. -/
lemma mul_mertens_le (M : ℕ) :
    (M : ℝ) * ∑ n ∈ Icc 1 M, Λ n / n ≤ ∑ m ∈ Icc 1 M, Real.log m + Chebyshev.psi M := by
  have h3 : ∀ n ∈ Icc 1 M, Λ n * ((M : ℝ) / n - 1) ≤ Λ n * ((M / n : ℕ) : ℝ) := by
    intro n hn
    refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
    have hn0 : 0 < n := by have := (Finset.mem_Icc.1 hn).1; omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hdm := Nat.div_add_mod M n
    have hmod := Nat.mod_lt M hn0
    have e : (M : ℝ) = n * ((M / n : ℕ) : ℝ) + ((M % n : ℕ) : ℝ) := by exact_mod_cast hdm.symm
    have hr : ((M % n : ℕ) : ℝ) < n := by exact_mod_cast hmod
    rw [e, sub_le_iff_le_add, div_le_iff₀ hnR]
    nlinarith
  have h4 : ∑ n ∈ Icc 1 M, Λ n = Chebyshev.psi M := by
    unfold Chebyshev.psi
    rw [Nat.floor_natCast, Icc_one_eq_Ioc]
  have h6 : ∑ n ∈ Icc 1 M, Λ n * ((M : ℝ) / n - 1) = M * ∑ n ∈ Icc 1 M, Λ n / n - ∑ n ∈ Icc 1 M, Λ n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have h7 := Finset.sum_le_sum h3
  rw [h6, ← sum_log_eq, h4] at h7
  linarith

/-- **Mertens' bound**: `Σ_{n ≤ M} Λ(n)/n ≤ log M + log 4 + 4`, from `Σ_{m ≤ M} log m ≤ M log M`,
`⌊M/n⌋ ≥ M/n − 1` and Chebyshev's `ψ(M) ≤ (log 4 + 4)M` (Mathlib's `Chebyshev.psi_le_const_mul_self`). -/
lemma mertens_le (M : ℕ) : ∑ n ∈ Icc 1 M, Λ n / n ≤ Real.log M + (Real.log 4 + 4) := by
  have hc : 0 ≤ Real.log 4 + 4 := by positivity
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Finset.Icc_eq_empty_of_lt one_pos, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact hc
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h2 : ∑ m ∈ Icc 1 M, Real.log m ≤ M * Real.log M := by
    calc ∑ m ∈ Icc 1 M, Real.log m ≤ ∑ m ∈ Icc 1 M, Real.log M :=
          Finset.sum_le_sum fun m hm => Real.log_le_log
            (by exact_mod_cast (show 0 < m by have := (Finset.mem_Icc.1 hm).1; omega))
            (by exact_mod_cast (Finset.mem_Icc.1 hm).2)
      _ = M * Real.log M := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have h5 := Chebyshev.psi_le_const_mul_self hM0.le
  have h7 := mul_mertens_le M
  have h8 : (M : ℝ) * ∑ n ∈ Icc 1 M, Λ n / n ≤ M * (Real.log M + (Real.log 4 + 4)) := by nlinarith
  exact le_of_mul_le_mul_left h8 hM0

/-- **Mertens' bound with the constant `log 4 + 1`**: `Σ_{n ≤ M} Λ(n)/n ≤ log M + log 4 + 1`. As `mertens_le`,
with Stirling's `Σ_{m ≤ M} log m ≤ M log M − M + log M + 1` (Mathlib's `Real.sum_log_le`) in place of `M log M`,
and Chebyshev's `ψ(M) ≤ M log 4 + 2√M log M` (`Chebyshev.psi_le`); `2√M log M ≤ 4M/e` since `log y ≤ y/e`. The
constant is `log 4 − 1` plus what the small `M` cost; the truth is `−γ`. -/
lemma mertens_le_sharp (M : ℕ) : ∑ n ∈ Icc 1 M, Λ n / n ≤ Real.log M + (Real.log 4 + 1) := by
  have he := Real.exp_one_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlogM : 0 ≤ Real.log M := Real.log_natCast_nonneg M
  -- `log y ≤ y/e`
  have hle : ∀ y : ℝ, 0 < y → Real.log y ≤ y / Real.exp 1 := fun y hy => by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / Real.exp 1 by positivity)
    rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    linarith
  rcases Nat.lt_or_ge M 6 with hM6 | hM6
  · -- at most five terms, each `Λ(n)/n ≤ log n/n ≤ 1/e`
    have hterm : ∀ n ∈ Icc 1 M, Λ n / n ≤ 1 / Real.exp 1 := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.1 hn).1; omega)
      have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      have h2 := hle n hn0
      rw [div_le_div_iff₀ hn0 (Real.exp_pos 1), one_mul]
      have h3 : Real.log n * Real.exp 1 ≤ n := by rwa [le_div_iff₀ (Real.exp_pos 1)] at h2
      nlinarith [Real.exp_pos 1]
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
    have hcard : ((M + 1 - 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show M + 1 - 1 ≤ 5 by omega)
    have hinv : 1 / Real.exp 1 ≤ 0.368 := by rw [div_le_iff₀ (Real.exp_pos 1)]; linarith
    have : ((M + 1 - 1 : ℕ) : ℝ) * (1 / Real.exp 1) ≤ 5 * 0.368 :=
      mul_le_mul hcard hinv (by positivity) (by norm_num)
    linarith
  · have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hM6' : (6 : ℝ) ≤ M := by exact_mod_cast hM6
    have h7 := mul_mertens_le M
    have hfac : ∑ m ∈ Icc 1 M, Real.log m ≤ M * Real.log M - M + Real.log M + 1 := by
      have h := Real.sum_log_le (x := (M : ℝ)) hM1
      rwa [Nat.floor_natCast, ← Icc_one_eq_Ioc] at h
    have hpsi := Chebyshev.psi_le hM1
    have hs0 : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
    have hss : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM0.le
    have hlog1 : Real.log M ≤ 2 * (Real.sqrt M / Real.exp 1) := by
      have h := hle (Real.sqrt M) hs0
      rw [Real.log_sqrt hM0.le] at h
      linarith
    have hlog2 : Real.log M ≤ Real.log 4 + M / 4 - 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < M / 4 by positivity)
      rw [Real.log_div hM0.ne' (by norm_num)] at h
      linarith
    have hA : 2 * Real.sqrt M * Real.log M ≤ 4 * M / Real.exp 1 := by
      have h := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt M)
      calc 2 * Real.sqrt M * Real.log M ≤ 2 * Real.sqrt M * (2 * (Real.sqrt M / Real.exp 1)) := h
        _ = 4 * Real.sqrt M ^ 2 / Real.exp 1 := by ring
        _ = 4 * M / Real.exp 1 := by rw [hss]
    have hB : 4 * (M : ℝ) / Real.exp 1 ≤ 1.4716 * M := by
      rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
    have hkey : (M : ℝ) * ∑ n ∈ Icc 1 M, Λ n / n ≤ M * (Real.log M + (Real.log 4 + 1)) := by
      have hpsi' : Chebyshev.psi M ≤ Real.log 4 * M + 1.4716 * M := by linarith
      nlinarith
    exact le_of_mul_le_mul_left hkey hM0

/-- `Σ_{j ≤ N, jn ≤ N} f(jn) = Σ_{m ≤ N, n ∣ m} f(m)` for `n ≥ 1`. -/
lemma sum_mul_eq_sum_dvd (N : ℕ) {n : ℕ} (hn : 1 ≤ n) (f : ℕ → ℝ) :
    ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), f (j * n) = ∑ m ∈ (Icc 1 N).filter (n ∣ ·), f m := by
  refine Finset.sum_bij' (fun j _ => j * n) (fun m _ => m / n) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    exact ⟨⟨by nlinarith, hj.2⟩, dvd_mul_left n j⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    obtain ⟨⟨hm1, hmN⟩, k, rfl⟩ := hm
    rw [Nat.mul_div_cancel_left k (by omega)]
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hm1
      · exact h
    refine ⟨⟨hk, ?_⟩, ?_⟩
    · nlinarith
    · rw [mul_comm]; exact hmN
  · intro j _
    exact Nat.mul_div_cancel j (by omega)
  · intro m hm
    simp only [Finset.mem_filter] at hm
    exact Nat.div_mul_cancel hm.2
  · intro j _
    rfl

/-- **The Landau form, from any Mertens bound**: if `Σ_{n ≤ M} Λ(n)/n ≤ log M + c` for every `M`, then for every
real `b`, `2Σ_{n ≤ N}(Λ(n)/√n)Σ_{jn ≤ N} b_j b_{jn} ≤ (log N + c)Σ_{j ≤ N} b_j²`. Schur's test with the weights
`j^{−1/2}`: `b_j b_{jn}Λ(n)/√n ≤ ½(b_j²Λ(n)/n + b_{jn}²Λ(n))`, then the Mertens bound in `n ≤ N/j` and
`Σ_{n ∣ m} Λ(n) = log m`. -/
lemma landau_le_of {c : ℝ} (hc : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n / n ≤ Real.log M + c) (N : ℕ) (b : ℕ → ℝ) :
    2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b j * b (j * n) ≤
      (Real.log N + c) * ∑ j ∈ Icc 1 N, b j ^ 2 := by
  have hamgm : ∀ n ∈ Icc 1 N, ∀ j, Λ n / Real.sqrt n * (b j * b (j * n)) ≤
      (b j ^ 2 * (Λ n / n) + b (j * n) ^ 2 * Λ n) / 2 := by
    intro n hn j
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.1 hn).1; omega)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    have hss : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
    have hL := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    set s := Real.sqrt n with hsdef
    have hsq : 0 ≤ Λ n * (b j - s * b (j * n)) ^ 2 := mul_nonneg hL (sq_nonneg _)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hs two_pos, ← hss]
    have e : (b j ^ 2 * (Λ n / s ^ 2) + b (j * n) ^ 2 * Λ n) * s =
        Λ n * (b j ^ 2 + s ^ 2 * b (j * n) ^ 2) / s := by
      field_simp
    rw [e, le_div_iff₀ hs]
    nlinarith [hsq]
  -- the two sums
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
  have hM : ∀ j ∈ Icc 1 N, b j ^ 2 * ∑ n ∈ Icc 1 (N / j), Λ n / n ≤ b j ^ 2 * (Real.log N - Real.log j + c) := by
    intro j hj
    obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.1 hj
    refine mul_le_mul_of_nonneg_left ((hc (N / j)).trans ?_) (sq_nonneg _)
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hNj : ((N / j : ℕ) : ℝ) ≤ (N : ℝ) / j := Nat.cast_div_le
    have hNj1 : 1 ≤ N / j := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have hpos : (0 : ℝ) < ((N / j : ℕ) : ℝ) := by exact_mod_cast (show 0 < N / j by omega)
    have := Real.log_le_log hpos hNj
    rw [Real.log_div (by exact_mod_cast (show N ≠ 0 by omega)) hj0.ne'] at this
    linarith
  calc 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b j * b (j * n)
      = 2 * ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), Λ n / Real.sqrt n * (b j * b (j * n)) := by
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
    _ = ∑ j ∈ Icc 1 N, b j ^ 2 * ∑ n ∈ Icc 1 (N / j), Λ n / n + ∑ m ∈ Icc 1 N, b m ^ 2 * Real.log m := by
        rw [hA, hB]
    _ ≤ ∑ j ∈ Icc 1 N, b j ^ 2 * (Real.log N - Real.log j + c) + ∑ m ∈ Icc 1 N, b m ^ 2 * Real.log m :=
        add_le_add (Finset.sum_le_sum fun j hj => hM j hj) le_rfl
    _ = (Real.log N + c) * ∑ j ∈ Icc 1 N, b j ^ 2 := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- **The Landau form**: for every real `b`,
`2Σ_{n ≤ N}(Λ(n)/√n)Σ_{jn ≤ N} b_j b_{jn} ≤ (log N + log 4 + 4)Σ_{j ≤ N} b_j²` (`landau_le_of` with `mertens_le`). -/
lemma landau_le (N : ℕ) (b : ℕ → ℝ) :
    2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b j * b (j * n) ≤
      (Real.log N + (Real.log 4 + 4)) * ∑ j ∈ Icc 1 N, b j ^ 2 :=
  landau_le_of mertens_le N b

/-- **The Landau form with the constant `log 4 + 1`**: `2Σ_{n ≤ N}(Λ(n)/√n)Σ_{jn ≤ N} b_j b_{jn} ≤
(log N + log 4 + 1)Σ_{j ≤ N} b_j²` (`landau_le_of` with `mertens_le_sharp`). -/
lemma landau_le_sharp (N : ℕ) (b : ℕ → ℝ) :
    2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), b j * b (j * n) ≤
      (Real.log N + (Real.log 4 + 1)) * ∑ j ∈ Icc 1 N, b j ^ 2 :=
  landau_le_of mertens_le_sharp N b

/-- **The near misses are separated**: for `j, j' ∈ [1, N]` and `n ≥ 1` with `jn ≠ j'`,
`|log(jn) − log j'| ≥ 1/(2N)`. -/
lemma sep_log {N j j' n : ℕ} (hj : j ∈ Icc 1 N) (hj' : j' ∈ Icc 1 N) (hn : 1 ≤ n) (hne : j * n ≠ j') :
    1 / (2 * (N : ℝ)) ≤ |Real.log ((j * n : ℕ) : ℝ) - Real.log j'| := by
  obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.1 hj
  obtain ⟨hj'1, hj'N⟩ := Finset.mem_Icc.1 hj'
  have hm1 : 1 ≤ j * n := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h12 : 1 / (2 * (N : ℝ)) ≤ 1 / N := by
    rw [div_le_div_iff₀ (by positivity) hN0]; linarith
  rcases lt_or_gt_of_ne hne with h | h
  · have hk := BallSampling.inv_le_log_sub hm1 h hj'N
    rw [abs_sub_comm, abs_of_pos (lt_of_lt_of_le (by positivity) hk)]
    linarith
  · by_cases hm2 : j * n ≤ 2 * N
    · have hk := BallSampling.inv_le_log_sub (N := 2 * N) hj'1 h hm2
      have e2 : ((2 * N : ℕ) : ℝ) = 2 * N := by push_cast; ring
      rw [e2] at hk
      rw [abs_of_pos (lt_of_lt_of_le (by positivity) hk)]
      exact hk
    · have hj'0 : (0 : ℝ) < j' := by exact_mod_cast (show 0 < j' by omega)
      have hlt : (2 : ℝ) * j' < ((j * n : ℕ) : ℝ) := by
        have : 2 * j' < j * n := by omega
        exact_mod_cast this
      have hlog : Real.log 2 + Real.log j' < Real.log ((j * n : ℕ) : ℝ) := by
        rw [← Real.log_mul two_ne_zero hj'0.ne']
        exact Real.log_lt_log (by positivity) hlt
      have hl2 : 1 / 2 < Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      have h2N : 1 / (2 * (N : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) two_pos]
        have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        linarith
      rw [abs_of_pos (by linarith)]
      linarith

/-! ## The Gaussian window -/

/-- `w_{σ,T}(t) = e^{−(t − T)²/(2σ²)}`. -/
def gw (σ T t : ℝ) : ℝ := Real.exp (-(t - T) ^ 2 / (2 * σ ^ 2))

lemma gw_pos (σ T t : ℝ) : 0 < gw σ T t := Real.exp_pos _

lemma gw_le_one (σ T t : ℝ) : gw σ T t ≤ 1 := by
  unfold gw
  rw [Real.exp_le_one_iff, neg_div]
  have : 0 ≤ (t - T) ^ 2 / (2 * σ ^ 2) := by positivity
  linarith

lemma integrable_gw {σ : ℝ} (hσ : 0 < σ) (T : ℝ) : Integrable (gw σ T) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / (2 * σ ^ 2)) (by positivity)).comp_sub_right T
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [gw]
  congr 1
  ring

/-- **The Gaussian cosine transform**: `∫ w_{σ,T}(t)cos(vt) dt = σ√(2π)e^{−σ²v²/2}cos(Tv)`, from Mathlib's
`integral_cexp_quadratic`. -/
lemma integral_gw_cos {σ : ℝ} (hσ : 0 < σ) (T v : ℝ) :
    ∫ t, gw σ T t * Real.cos (v * t) =
      σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 * v ^ 2) / 2) * Real.cos (T * v) := by
  have hσ2 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  set b : ℂ := ((-(1 / (2 * σ ^ 2)) : ℝ) : ℂ) with hb
  set c : ℂ := ((T / σ ^ 2 : ℝ) : ℂ) + (v : ℂ) * I with hc
  set d : ℂ := ((-(T ^ 2 / (2 * σ ^ 2)) : ℝ) : ℂ) with hd
  have hbre : b.re < 0 := by
    rw [hb, Complex.ofReal_re]
    have : 0 < 1 / (2 * σ ^ 2) := by positivity
    linarith
  have hq := integral_cexp_quadratic hbre c d
  have hint := integrable_cexp_quadratic' hbre c d
  have hpt : ∀ t : ℝ, gw σ T t * Real.cos (v * t) = (cexp (b * (t : ℂ) ^ 2 + c * t + d)).re := by
    intro t
    have e : b * (t : ℂ) ^ 2 + c * t + d = ((-(t - T) ^ 2 / (2 * σ ^ 2) : ℝ) : ℂ) + ((v * t : ℝ) : ℂ) * I := by
      rw [hb, hc, hd]
      push_cast
      field_simp
      ring
    rw [e, Complex.exp_add, ← Complex.ofReal_exp, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    rfl
  have hre : ∫ t : ℝ, (cexp (b * (t : ℂ) ^ 2 + c * t + d)).re =
      (∫ t : ℝ, cexp (b * (t : ℂ) ^ 2 + c * t + d)).re := integral_re hint
  rw [show (fun t => gw σ T t * Real.cos (v * t)) = fun t : ℝ => (cexp (b * (t : ℂ) ^ 2 + c * t + d)).re from
    funext hpt, hre, hq]
  have e1 : (π : ℂ) / -b = ((2 * π * σ ^ 2 : ℝ) : ℂ) := by
    rw [hb]
    push_cast
    field_simp
  have e2 : ((2 * π * σ ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((σ * Real.sqrt (2 * π) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, show 2 * π * σ ^ 2 = σ ^ 2 * (2 * π) by ring, Real.sqrt_mul (sq_nonneg σ),
      Real.sqrt_sq hσ.le]
  have e3 : d - c ^ 2 / (4 * b) = ((-(σ ^ 2 * v ^ 2) / 2 : ℝ) : ℂ) + ((T * v : ℝ) : ℂ) * I := by
    rw [hb, hc, hd]
    push_cast
    field_simp
    linear_combination (4 * (σ : ℂ) ^ 4 * (v : ℂ) ^ 2) * Complex.I_sq
  rw [e1, e2, e3, Complex.exp_add, ← Complex.ofReal_exp, ← mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The window `W(t) = w_{σ,T₀}(t) + w_{σ,−T₀}(t)`, even in `t`. -/
def Wd (σ T₀ t : ℝ) : ℝ := gw σ T₀ t + gw σ (-T₀) t

/-- `Ŵ(v) = ∫ W(t)cos(vt) dt = 2σ√(2π)e^{−σ²v²/2}cos(T₀v)`. -/
def What (σ T₀ v : ℝ) : ℝ := 2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 * v ^ 2) / 2) * Real.cos (T₀ * v)

lemma integrable_Wd_mul {σ : ℝ} (hσ : 0 < σ) (T₀ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ t, |f t| ≤ C) : Integrable (fun t => Wd σ T₀ t * f t) := by
  have hW : Integrable (Wd σ T₀) := (integrable_gw hσ T₀).add (integrable_gw hσ (-T₀))
  refine hW.mul_bdd (c := C) hf.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  exact hC t

lemma integral_Wd_cos {σ : ℝ} (hσ : 0 < σ) (T₀ v : ℝ) : ∫ t, Wd σ T₀ t * Real.cos (v * t) = What σ T₀ v := by
  have h1 := integral_gw_cos hσ T₀ v
  have h2 := integral_gw_cos hσ (-T₀) v
  have hi1 : Integrable (fun t => gw σ T₀ t * Real.cos (v * t)) :=
    (integrable_gw hσ T₀).mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hi2 : Integrable (fun t => gw σ (-T₀) t * Real.cos (v * t)) :=
    (integrable_gw hσ (-T₀)).mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have e : (fun t => Wd σ T₀ t * Real.cos (v * t)) =
      fun t => gw σ T₀ t * Real.cos (v * t) + gw σ (-T₀) t * Real.cos (v * t) := by
    funext t; unfold Wd; ring
  rw [e, integral_add hi1 hi2, h1, h2, neg_mul, Real.cos_neg]
  unfold What
  ring

lemma abs_What_le (σ T₀ v : ℝ) (hσ : 0 ≤ σ) :
    |What σ T₀ v| ≤ 2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 * v ^ 2) / 2) := by
  unfold What
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 * v ^ 2) / 2))]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

lemma What_zero (σ T₀ : ℝ) : What σ T₀ 0 = 2 * σ * Real.sqrt (2 * π) := by
  unfold What; simp

lemma What_neg (σ T₀ v : ℝ) : What σ T₀ (-v) = What σ T₀ v := by
  unfold What; rw [neg_sq, mul_neg, Real.cos_neg]

lemma integrable_Wd_cos {σ : ℝ} (hσ : 0 < σ) (T₀ v : ℝ) :
    Integrable (fun t => Wd σ T₀ t * Real.cos (v * t)) :=
  integrable_Wd_mul hσ T₀ (by fun_prop) (C := 1) fun t => Real.abs_cos_le_one _

lemma Wd_pos (σ T₀ t : ℝ) : 0 < Wd σ T₀ t := add_pos (gw_pos _ _ _) (gw_pos _ _ _)

/-- `w_{σ,T}(x)(1 + x²) ≤ 1 + 2T² + 4σ²`. -/
lemma gw_mul_le {σ : ℝ} (hσ : 0 < σ) (T x : ℝ) : gw σ T x * (1 + x ^ 2) ≤ 1 + 2 * T ^ 2 + 4 * σ ^ 2 := by
  have hs : 0 < 2 * σ ^ 2 := by positivity
  set u := (x - T) ^ 2 / (2 * σ ^ 2) with hu
  have hu0 : 0 ≤ u := by positivity
  have hg : gw σ T x = Real.exp (-u) := by unfold gw; rw [hu, neg_div]
  have hue : u * Real.exp (-u) ≤ 1 := by
    have h1 := Real.add_one_le_exp u
    have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-u)]
  have hxT : (x - T) ^ 2 = 2 * σ ^ 2 * u := by rw [hu]; field_simp
  have h1 : 1 + x ^ 2 ≤ 1 + 2 * T ^ 2 + 2 * (x - T) ^ 2 := by nlinarith [sq_nonneg (x - 2 * T)]
  have hg1 := gw_le_one σ T x
  have hg0 := (gw_pos σ T x).le
  calc gw σ T x * (1 + x ^ 2) ≤ gw σ T x * (1 + 2 * T ^ 2 + 2 * (x - T) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hg0
    _ = gw σ T x * (1 + 2 * T ^ 2) + 4 * σ ^ 2 * (u * Real.exp (-u)) := by rw [hxT, hg]; ring
    _ ≤ 1 * (1 + 2 * T ^ 2) + 4 * σ ^ 2 * 1 := by
        gcongr
    _ = 1 + 2 * T ^ 2 + 4 * σ ^ 2 := by ring

lemma Wd_mul_le {σ : ℝ} (hσ : 0 < σ) (T₀ x : ℝ) :
    Wd σ T₀ x * (1 + x ^ 2) ≤ 2 * (1 + 2 * T₀ ^ 2 + 4 * σ ^ 2) := by
  have h1 := gw_mul_le hσ T₀ x
  have h2 := gw_mul_le hσ (-T₀) x
  rw [neg_sq] at h2
  unfold Wd
  linarith

/-! ## The test function -/

/-- `D(z) = Σ_{j ≤ N} c_j e^{−iz log j}`. -/
def DC (N : ℕ) (c : ℕ → ℝ) (z : ℂ) : ℂ := ∑ j ∈ Icc 1 N, (c j : ℂ) * cexp (-(I * z * Real.log j))

/-- The Gaussian `e^{−(z − T)²/(2σ²)}` on `ℂ`. -/
def gwC (σ T : ℝ) (z : ℂ) : ℂ := cexp (-(z - T) ^ 2 / (2 * σ ^ 2))

/-- **The test function** `h(z) = D(z)D(−z)(w(z − T₀) + w(z + T₀))`. -/
def htest (N : ℕ) (c : ℕ → ℝ) (σ T₀ : ℝ) (z : ℂ) : ℂ :=
  DC N c z * DC N c (-z) * (gwC σ T₀ z + gwC σ (-T₀) z)

/-- `A(t) = Σ c_j cos(t log j)`. -/
def Ac (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ := ∑ j ∈ Icc 1 N, c j * Real.cos (t * Real.log j)

/-- `B(t) = Σ c_j sin(t log j)`. -/
def Bc (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ := ∑ j ∈ Icc 1 N, c j * Real.sin (t * Real.log j)

/-- `|D(t)|² = Σ_{j, j'} c_j c_{j'} cos((log j' − log j)t)`. -/
def Kc (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * Real.cos ((Real.log j' - Real.log j) * t)

/-- `h` on the real line: `h(t) = |D(t)|²W(t)`. -/
def htestR (N : ℕ) (c : ℕ → ℝ) (σ T₀ t : ℝ) : ℝ := Kc N c t * Wd σ T₀ t

/-- `S₁ = Σ_{j ≤ N} |c_j|`. -/
def S1 (N : ℕ) (c : ℕ → ℝ) : ℝ := ∑ j ∈ Icc 1 N, |c j|

lemma S1_nonneg (N : ℕ) (c : ℕ → ℝ) : 0 ≤ S1 N c := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma DC_ofReal (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : DC N c t = (Ac N c t : ℂ) - (Bc N c t : ℂ) * I := by
  unfold DC Ac Bc
  rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  generalize Real.log (j : ℝ) = L
  rw [show -(I * (t : ℂ) * (L : ℂ)) = ((-(t * L) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma DC_neg_ofReal (N : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    DC N c (-(t : ℂ)) = (Ac N c t : ℂ) + (Bc N c t : ℂ) * I := by
  have h := DC_ofReal N c (-t)
  rw [Complex.ofReal_neg] at h
  rw [h]
  unfold Ac Bc
  simp only [neg_mul, Real.cos_neg, Real.sin_neg, mul_neg, Finset.sum_neg_distrib, Complex.ofReal_neg]
  ring

lemma Kc_eq (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : Kc N c t = Ac N c t ^ 2 + Bc N c t ^ 2 := by
  unfold Kc Ac Bc
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [sub_mul, Real.cos_sub, mul_comm (Real.log j') t, mul_comm (Real.log j) t]
  ring

lemma Kc_nonneg (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : 0 ≤ Kc N c t := by rw [Kc_eq]; positivity

lemma Kc_le (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : Kc N c t ≤ S1 N c ^ 2 := by
  unfold Kc S1
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => ?_
  calc c j * c j' * Real.cos ((Real.log j' - Real.log j) * t)
      ≤ |c j * c j' * Real.cos ((Real.log j' - Real.log j) * t)| := le_abs_self _
    _ ≤ |c j| * |c j'| := by
        rw [abs_mul, abs_mul]
        exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

lemma norm_DC_ofReal_sq (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : ‖DC N c t‖ ^ 2 = Kc N c t := by
  rw [DC_ofReal, Kc_eq, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma htestR_nonneg (N : ℕ) (c : ℕ → ℝ) (σ T₀ t : ℝ) : 0 ≤ htestR N c σ T₀ t :=
  mul_nonneg (Kc_nonneg N c t) (Wd_pos σ T₀ t).le

lemma htestR_le (N : ℕ) (c : ℕ → ℝ) (σ T₀ t : ℝ) : htestR N c σ T₀ t ≤ S1 N c ^ 2 * Wd σ T₀ t :=
  mul_le_mul_of_nonneg_right (Kc_le N c t) (Wd_pos σ T₀ t).le

lemma continuous_Kc (N : ℕ) (c : ℕ → ℝ) : Continuous (Kc N c) := by unfold Kc; fun_prop

lemma gwC_ofReal (σ T t : ℝ) : gwC σ T t = (gw σ T t : ℂ) := by
  unfold gwC gw
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma gwC_neg (σ T : ℝ) (z : ℂ) : gwC σ T (-z) = gwC σ (-T) z := by
  unfold gwC; congr 1; push_cast; ring

/-- `h` is real on the real line. -/
lemma htest_ofReal (N : ℕ) (c : ℕ → ℝ) (σ T₀ t : ℝ) : htest N c σ T₀ t = (htestR N c σ T₀ t : ℂ) := by
  unfold htest htestR Wd
  rw [DC_ofReal, DC_neg_ofReal, gwC_ofReal, gwC_ofReal, Kc_eq]
  push_cast
  linear_combination (-(Bc N c t : ℂ) ^ 2 * ((gw σ T₀ t : ℂ) + (gw σ (-T₀) t : ℂ))) * Complex.I_sq

/-- `h` is even. -/
lemma htest_even (N : ℕ) (c : ℕ → ℝ) (σ T₀ : ℝ) (z : ℂ) : htest N c σ T₀ (-z) = htest N c σ T₀ z := by
  unfold htest
  rw [neg_neg, gwC_neg, gwC_neg, neg_neg]
  ring

lemma differentiable_htest (N : ℕ) (c : ℕ → ℝ) (σ T₀ : ℝ) : Differentiable ℂ (htest N c σ T₀) := by
  unfold htest DC gwC; fun_prop

lemma norm_DC_le (N : ℕ) (c : ℕ → ℝ) {z : ℂ} (hz : |z.im| ≤ 1) : ‖DC N c z‖ ≤ N * S1 N c := by
  unfold DC S1
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have hlog : 0 ≤ Real.log j := Real.log_nonneg hj1
  have hexp : Real.exp (z.im * Real.log j) ≤ j := by
    calc Real.exp (z.im * Real.log j) ≤ Real.exp (Real.log j) :=
          Real.exp_le_exp.2 (by nlinarith [abs_le.1 hz])
      _ = j := Real.exp_log (by linarith)
  have hre : (-(I * z * ((Real.log j : ℝ) : ℂ))).re = z.im * Real.log j := by
    generalize Real.log (j : ℝ) = L
    simp [Complex.mul_re]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]
  calc |c j| * Real.exp (z.im * Real.log j) ≤ |c j| * N :=
        mul_le_mul_of_nonneg_left (hexp.trans hjN) (abs_nonneg _)
    _ = N * |c j| := mul_comm _ _

lemma norm_gwC_le {σ : ℝ} (hσ : 0 < σ) (T : ℝ) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖gwC σ T z‖ ≤ Real.exp (1 / (2 * σ ^ 2)) * gw σ T z.re := by
  have hs : 0 < 2 * σ ^ 2 := by positivity
  have hy : z.im ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg z.im]
  have hre : (-(z - T) ^ 2 / (2 * σ ^ 2) : ℂ).re = -((z.re - T) ^ 2 - z.im ^ 2) / (2 * σ ^ 2) := by
    rw [show (-(z - T) ^ 2 / (2 * σ ^ 2) : ℂ) = ((-1 / (2 * σ ^ 2) : ℝ) : ℂ) * (z - T) ^ 2 by
      push_cast; ring, Complex.re_ofReal_mul]
    simp [sq, Complex.mul_re]
    ring
  unfold gwC gw
  rw [Complex.norm_exp, hre, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith) hs.le

/-- `|h(z)| ≤ (N S₁)²e^{1/(2σ²)}W(Re z)` on `|Im z| ≤ 1`. -/
lemma norm_htest_le {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) (T₀ : ℝ) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖htest N c σ T₀ z‖ ≤ (N * S1 N c) ^ 2 * Real.exp (1 / (2 * σ ^ 2)) * Wd σ T₀ z.re := by
  have h1 := norm_DC_le N c hz
  have h2 := norm_DC_le N c (z := -z) (by rwa [Complex.neg_im, abs_neg])
  have h3 : ‖gwC σ T₀ z + gwC σ (-T₀) z‖ ≤ Real.exp (1 / (2 * σ ^ 2)) * Wd σ T₀ z.re := by
    refine (norm_add_le _ _).trans ?_
    rw [Wd, mul_add]
    exact add_le_add (norm_gwC_le hσ T₀ hz) (norm_gwC_le hσ (-T₀) hz)
  have hS := S1_nonneg N c
  unfold htest
  rw [norm_mul, norm_mul]
  calc ‖DC N c z‖ * ‖DC N c (-z)‖ * ‖gwC σ T₀ z + gwC σ (-T₀) z‖
      ≤ (N * S1 N c) * (N * S1 N c) * (Real.exp (1 / (2 * σ ^ 2)) * Wd σ T₀ z.re) := by
        gcongr
    _ = _ := by ring

/-- **`h` is a strip test function**. -/
lemma striptest_htest {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) (T₀ : ℝ) :
    WeilStrip.StripTest (htest N c σ T₀)
      ((N * S1 N c) ^ 2 * Real.exp (1 / (2 * σ ^ 2)) * (2 * (1 + 2 * T₀ ^ 2 + 4 * σ ^ 2))) := by
  refine ⟨(differentiable_htest N c σ T₀).differentiableOn, fun t ht => ?_⟩
  have him : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  rw [le_div_iff₀ (by positivity)]
  calc ‖htest N c σ T₀ t‖ * (1 + t.re ^ 2)
      ≤ (N * S1 N c) ^ 2 * Real.exp (1 / (2 * σ ^ 2)) * Wd σ T₀ t.re * (1 + t.re ^ 2) :=
        mul_le_mul_of_nonneg_right (norm_htest_le hσ N c T₀ him) (by positivity)
    _ = (N * S1 N c) ^ 2 * Real.exp (1 / (2 * σ ^ 2)) * (Wd σ T₀ t.re * (1 + t.re ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Wd_mul_le hσ T₀ t.re) (by positivity)

/-- **Weil's explicit formula for `h`** (`weilExplicit_zeta`, no RH input). -/
lemma weil_htest {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) (T₀ : ℝ) :
    WeilExplicit zetaZeroFamily (htest N c σ T₀) (htestR N c σ T₀) :=
  weilExplicit_zeta (striptest_htest hσ N c T₀) (htest_even N c σ T₀) (htest_ofReal N c σ T₀)

/-! ## The cosine integrals of `h` -/

lemma htestR_mul_cos (N : ℕ) (c : ℕ → ℝ) (σ T₀ u r : ℝ) :
    htestR N c σ T₀ r * Real.cos (r * u) =
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' / 2 *
        (Wd σ T₀ r * Real.cos ((Real.log j' - Real.log j + u) * r)
          + Wd σ T₀ r * Real.cos ((Real.log j' - Real.log j - u) * r)) := by
  unfold htestR Kc
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [show (Real.log j' - Real.log j + u) * r = (Real.log j' - Real.log j) * r + r * u by ring,
    show (Real.log j' - Real.log j - u) * r = (Real.log j' - Real.log j) * r - r * u by ring,
    Real.cos_add, Real.cos_sub]
  ring

/-- `∫ h(r)cos(ru) dr = Σ_{j,j'} c_j c_{j'}(Ŵ(α + u) + Ŵ(α − u))/2` with `α = log j' − log j`. -/
lemma integral_htestR_cos {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) (T₀ u : ℝ) :
    ∫ r, htestR N c σ T₀ r * Real.cos (r * u) =
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' / 2 *
        (What σ T₀ (Real.log j' - Real.log j + u) + What σ T₀ (Real.log j' - Real.log j - u)) := by
  have hI : ∀ (j j' : ℕ), Integrable (fun r => c j * c j' / 2 *
      (Wd σ T₀ r * Real.cos ((Real.log j' - Real.log j + u) * r)
        + Wd σ T₀ r * Real.cos ((Real.log j' - Real.log j - u) * r))) := fun j j' =>
    ((integrable_Wd_cos hσ T₀ _).add (integrable_Wd_cos hσ T₀ _)).const_mul _
  simp_rw [htestR_mul_cos N c σ T₀ u]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => hI j j']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun j' _ => hI j j']
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [integral_const_mul, integral_add (integrable_Wd_cos hσ T₀ _) (integrable_Wd_cos hσ T₀ _),
    integral_Wd_cos hσ, integral_Wd_cos hσ]

/-- The two shifts contribute equally (`Ŵ` is even and the sum is symmetric in `j, j'`). -/
lemma sum_What_symm (N : ℕ) (c : ℕ → ℝ) (σ T₀ u : ℝ) :
    ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' / 2 *
        (What σ T₀ (Real.log j' - Real.log j + u) + What σ T₀ (Real.log j' - Real.log j - u)) =
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j - u) := by
  have hswap : ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j + u) =
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j - u) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [show Real.log j - Real.log j' + u = -(Real.log j' - Real.log j - u) by ring, What_neg]
    ring
  calc ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' / 2 *
        (What σ T₀ (Real.log j' - Real.log j + u) + What σ T₀ (Real.log j' - Real.log j - u))
      = 1 / 2 * ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j + u)
        + 1 / 2 * ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j - u) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j' _ => ?_
        ring
    _ = _ := by rw [hswap]; ring

/-- **The prime-side kernel**: `g_h(u) = (1/2π)Σ_{j,j'} c_j c_{j'} Ŵ(log j' − log j − u)`. -/
lemma gh_htestR {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) (T₀ u : ℝ) :
    gh (htestR N c σ T₀) u = 1 / (2 * π) *
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j - u) := by
  unfold gh
  rw [integral_htestR_cos hσ, sum_What_symm]

/-- `∫ h = Σ_{j,j'} c_j c_{j'} Ŵ(log j' − log j)`. -/
lemma integral_htestR {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) (T₀ : ℝ) :
    ∫ r, htestR N c σ T₀ r =
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j) := by
  have h := integral_htestR_cos hσ N c T₀ 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [h, sum_What_symm]
  simp only [sub_zero]

lemma integrable_htestR {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) (T₀ : ℝ) :
    Integrable (htestR N c σ T₀) := by
  refine (integrable_Wd_mul hσ T₀ (continuous_Kc N c) (C := S1 N c ^ 2) fun t => ?_).congr
    (Filter.Eventually.of_forall fun t => ?_)
  · rw [abs_of_nonneg (Kc_nonneg N c t)]; exact Kc_le N c t
  · show Wd σ T₀ t * Kc N c t = htestR N c σ T₀ t
    unfold htestR; ring

lemma integrable_htestR_psi {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) (T₀ : ℝ) :
    Integrable (fun r => htestR N c σ T₀ r * psiRe r) := by
  refine (integrable_psi_real (striptest_htest hσ N c T₀)).re.congr
    (Filter.Eventually.of_forall fun r => ?_)
  show RCLike.re (htest N c σ T₀ r * Complex.digamma (zB r)) = htestR N c σ T₀ r * psiRe r
  rw [htest_ofReal]
  simp [psiRe]

/-! ## Exact matches and near misses -/

/-- The exact matches `e_n = Σ_{jn ≤ N} c_j c_{jn}`. -/
def ex (N : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), c j * c (j * n)

/-- `S₂ = Σ_{j ≤ N} c_j²`. -/
def S2 (N : ℕ) (c : ℕ → ℝ) : ℝ := ∑ j ∈ Icc 1 N, c j ^ 2

lemma S2_nonneg (N : ℕ) (c : ℕ → ℝ) : 0 ≤ S2 N c := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma ex_one (N : ℕ) (c : ℕ → ℝ) : ex N c 1 = S2 N c := by
  unfold ex S2
  rw [Finset.filter_true_of_mem fun j hj => by simpa using (Finset.mem_Icc.1 hj).2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_one, sq]

lemma ex_eq_zero (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : N < n) : ex N c n = 0 := by
  unfold ex
  rw [Finset.filter_false_of_mem fun j hj => ?_, Finset.sum_empty]
  have hj1 := (Finset.mem_Icc.1 hj).1
  have : n ≤ j * n := by nlinarith
  omega

lemma sum_exact (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (W : ℝ) :
    ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * (if j * n = j' then W else 0) = W * ex N c n := by
  unfold ex
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 := (Finset.mem_Icc.1 hj).1
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases h : j * n ≤ N
  · rw [ite_eq_left (Finset.mem_Icc.2 ⟨by nlinarith, h⟩), ite_eq_left h]
    ring
  · rw [ite_eq_right (fun hm => h (Finset.mem_Icc.1 hm).2), ite_eq_right h]

lemma abs_double_sum_le (N : ℕ) (c : ℕ → ℝ) (f : ℕ → ℕ → ℝ) {B : ℝ}
    (hf : ∀ j ∈ Icc 1 N, ∀ j' ∈ Icc 1 N, |f j j'| ≤ B) :
    |∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * f j j'| ≤ B * S1 N c ^ 2 := by
  unfold S1
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j' hj' => ?_)
  rw [abs_mul, abs_mul]
  calc |c j| * |c j'| * |f j j'| ≤ |c j| * |c j'| * B :=
        mul_le_mul_of_nonneg_left (hf j hj j' hj') (by positivity)
    _ = B * (|c j| * |c j'|) := by ring

/-- **Near misses decay**: for `j, j' ≤ N`, `n ≥ 1`, `jn ≠ j'` and `σ² ≥ 16N`,
`e^{−σ²(log j' − log j − log n)²/2} ≤ e^{−σ²/(16N²)}·N²/n²`. -/
lemma near_miss_le {N j j' n : ℕ} (hj : j ∈ Icc 1 N) (hj' : j' ∈ Icc 1 N) (hn : 1 ≤ n) (hne : j * n ≠ j')
    {σ : ℝ} (hσN : 16 * (N : ℝ) ≤ σ ^ 2) :
    Real.exp (-(σ ^ 2 * (Real.log j' - Real.log j - Real.log n) ^ 2) / 2) ≤
      Real.exp (-(σ ^ 2 / (16 * N ^ 2))) * (N ^ 2 / n ^ 2) := by
  have hsep := sep_log hj hj' hn hne
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have hj'N : (j' : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.1 hj').2
  have hj'1 : (1 : ℝ) ≤ j' := by exact_mod_cast (Finset.mem_Icc.1 hj').1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by linarith
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at hsep
  set β := Real.log j + Real.log n - Real.log j' with hβ
  have hv : (Real.log j' - Real.log j - Real.log n) ^ 2 = β ^ 2 := by rw [hβ]; ring
  rw [hv]
  have hβ2 : 1 / (4 * (N : ℝ) ^ 2) ≤ β ^ 2 := by
    have h0 : 0 ≤ 1 / (2 * (N : ℝ)) := by positivity
    calc 1 / (4 * (N : ℝ) ^ 2) = (1 / (2 * N)) ^ 2 := by field_simp; ring
      _ ≤ |β| ^ 2 := pow_le_pow_left₀ h0 hsep 2
      _ = β ^ 2 := sq_abs β
  have hfirst : σ ^ 2 / (16 * N ^ 2) ≤ σ ^ 2 * β ^ 2 / 4 := by
    have : σ ^ 2 * (1 / (4 * (N : ℝ) ^ 2)) ≤ σ ^ 2 * β ^ 2 := mul_le_mul_of_nonneg_left hβ2 (sq_nonneg σ)
    calc σ ^ 2 / (16 * N ^ 2) = σ ^ 2 * (1 / (4 * (N : ℝ) ^ 2)) / 4 := by field_simp; ring
      _ ≤ σ ^ 2 * β ^ 2 / 4 := by linarith
  have hsq0 : 0 ≤ σ ^ 2 * β ^ 2 := by positivity
  by_cases hnN : n ≤ N
  · have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have hratio : 1 ≤ (N : ℝ) ^ 2 / n ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ (by linarith) hnN' 2
    calc Real.exp (-(σ ^ 2 * β ^ 2) / 2) ≤ Real.exp (-(σ ^ 2 / (16 * N ^ 2))) := by
          apply Real.exp_le_exp.2
          linarith
      _ ≤ _ := le_mul_of_one_le_right (Real.exp_pos _).le hratio
  · push Not at hnN
    have hnN' : (N : ℝ) < n := by exact_mod_cast hnN
    have hlogj : 0 ≤ Real.log j := Real.log_nonneg hj1
    have hlogj' : Real.log j' ≤ Real.log N := Real.log_le_log (by linarith) hj'N
    have hlnN : 0 < Real.log n - Real.log N := by have := Real.log_lt_log hN0 hnN'; linarith
    have hβ1 : Real.log n - Real.log N ≤ β := by rw [hβ]; linarith
    have hβpos : 0 < β := lt_of_lt_of_le hlnN hβ1
    have hβN : 1 / (2 * N) ≤ β := by rwa [abs_of_pos hβpos] at hsep
    have h8 : 8 ≤ σ ^ 2 * β := by
      calc (8 : ℝ) = 16 * N * (1 / (2 * N)) := by field_simp; ring
        _ ≤ σ ^ 2 * β := mul_le_mul hσN hβN (by positivity) (sq_nonneg σ)
    have h8' := mul_le_mul_of_nonneg_right h8 hβpos.le
    have hsecond : 2 * β ≤ σ ^ 2 * β ^ 2 / 4 := by
      calc 2 * β = 8 * β / 4 := by ring
        _ ≤ σ ^ 2 * β * β / 4 := by linarith
        _ = σ ^ 2 * β ^ 2 / 4 := by ring
    have hexp2 : Real.exp (-(2 * (Real.log n - Real.log N))) = N ^ 2 / n ^ 2 := by
      rw [show -(2 * (Real.log n - Real.log N)) = Real.log ((N : ℝ) ^ 2 / n ^ 2) by
        rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity)]
    calc Real.exp (-(σ ^ 2 * β ^ 2) / 2)
        ≤ Real.exp (-(σ ^ 2 / (16 * N ^ 2)) + -(2 * (Real.log n - Real.log N))) := by
          apply Real.exp_le_exp.2
          linarith
      _ = _ := by rw [Real.exp_add, hexp2]

/-- **Exact matches plus near misses**: `Σ_{j,j'} c_j c_{j'}Ŵ(log j' − log j − log n) = Ŵ(0)e_n + O(…)`. -/
lemma sum_What_log_sub {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hσN : 16 * (N : ℝ) ≤ σ ^ 2) (c : ℕ → ℝ) (T₀ : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    |∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j - Real.log n)
      - What σ T₀ 0 * ex N c n| ≤
      2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2))) * (N ^ 2 / n ^ 2) * S1 N c ^ 2 := by
  rw [← sum_exact N c hn (What σ T₀ 0)]
  have e : ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j - Real.log n)
      - ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * (if j * n = j' then What σ T₀ 0 else 0) =
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' *
        (What σ T₀ (Real.log j' - Real.log j - Real.log n) - if j * n = j' then What σ T₀ 0 else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    ring
  rw [e]
  refine abs_double_sum_le N c _ fun j hj j' hj' => ?_
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases h : j * n = j'
  · rw [ite_eq_left h, ← h, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      show Real.log j + Real.log n - Real.log j - Real.log n = 0 by ring, sub_self, abs_zero]
    positivity
  · rw [ite_eq_right h, sub_zero]
    refine (abs_What_le σ T₀ _ hσ.le).trans ?_
    have := near_miss_le hj hj' hn h hσN
    calc 2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 * (Real.log j' - Real.log j - Real.log n) ^ 2) / 2)
        ≤ 2 * σ * Real.sqrt (2 * π) * (Real.exp (-(σ ^ 2 / (16 * N ^ 2))) * (N ^ 2 / n ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

/-- **The diagonal**: `∫ h ≥ Ŵ(0)S₂ − 2σ√(2π)e^{−σ²/(16N²)}N²S₁²`. -/
lemma integral_htestR_ge {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hσN : 16 * (N : ℝ) ≤ σ ^ 2) (c : ℕ → ℝ) (T₀ : ℝ) :
    What σ T₀ 0 * S2 N c - 2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2))) * N ^ 2 * S1 N c ^ 2
      ≤ ∫ r, htestR N c σ T₀ r := by
  have h := sum_What_log_sub hσ hσN c T₀ (n := 1) le_rfl
  rw [ex_one] at h
  simp only [Nat.cast_one, Real.log_one, sub_zero, one_pow, div_one] at h
  rw [integral_htestR hσ]
  have := (abs_le.1 h).1
  linarith

/-! ## Bounds for `Re ψ(¼ + ir/2)` -/

lemma zB_eq (r : ℝ) : zB r = 1 / 4 + ((r / 2 : ℝ) : ℂ) * Complex.I := by
  unfold zB; push_cast; ring

/-- `Re ψ(¼ + ir/2) − log π ≥ −9` for every `r`. -/
lemma psiRe_sub_log_pi_ge (r : ℝ) : -9 ≤ psiRe r - Real.log π := by
  have h0 := psiRe_ge r
  have hq := DigammaStirling.re_digamma_quarter 0 0
  have e0 : psiRe 0 = (Complex.digamma (1 / 4 + ((0 : ℝ) : ℂ) * Complex.I)).re := by
    unfold psiRe; rw [zB_eq]; norm_num
  rw [← e0] at hq
  have hval : DigammaStirling.psiApx 0 0 = Real.log (1 / 16) / 2 - 2 - 4 / 3 := by
    unfold DigammaStirling.psiApx; norm_num
  have herr : (1 : ℝ) / (120 * (((0 : ℕ) : ℝ) + 1 / 4) ^ 4) = 32 / 15 := by norm_num
  rw [hval, herr] at hq
  have hl16 : Real.log (1 / 16) = -(4 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  have hpi : Real.log π ≤ 2 * Real.log 2 := by
    calc Real.log π ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_le_four
      _ = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_lt_d9
  have := (abs_le.1 hq).1
  rw [hl16] at this
  linarith

/-- **Stirling from below**: `Re ψ(¼ + ir/2) ≥ log(|r|/2) − 3` for `|r| ≥ 8`. -/
lemma psiRe_ge_log {r : ℝ} (hr : 8 ≤ |r|) : Real.log (|r| / 2) - 3 ≤ psiRe r := by
  have hq := DigammaStirling.re_digamma_quarter 0 (r / 2)
  have e : psiRe r = (Complex.digamma (1 / 4 + ((r / 2 : ℝ) : ℂ) * Complex.I)).re := by
    unfold psiRe; rw [zB_eq]
  rw [← e] at hq
  have herr : (1 : ℝ) / (120 * (((0 : ℕ) : ℝ) + 1 / 4) ^ 4) = 32 / 15 := by norm_num
  rw [herr] at hq
  set b := r / 2 with hbdef
  have hb2 : b ^ 2 = (|r| / 2) ^ 2 := by rw [hbdef, div_pow, div_pow, sq_abs]
  have hb : 16 ≤ b ^ 2 := by rw [hb2]; nlinarith
  have hr2 : 0 < |r| / 2 := by linarith
  have happx : Real.log (|r| / 2) - 1 / 128 ≤ DigammaStirling.psiApx 0 b := by
    unfold DigammaStirling.psiApx
    simp only [Nat.cast_zero, zero_add, Finset.range_zero, Finset.sum_empty, sub_zero]
    have h1 : Real.log (|r| / 2) ≤ Real.log ((1 / 4) ^ 2 + b ^ 2) / 2 := by
      have hl : Real.log ((|r| / 2) ^ 2) ≤ Real.log ((1 / 4) ^ 2 + b ^ 2) :=
        Real.log_le_log (by positivity) (by rw [← hb2]; nlinarith)
      rw [Real.log_pow] at hl
      push_cast at hl
      linarith
    have h2 : (1 / 4) / (2 * ((1 / 4) ^ 2 + b ^ 2)) ≤ 1 / 128 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h3 : ((1 / 4) ^ 2 - b ^ 2) / (12 * ((1 / 4) ^ 2 + b ^ 2) ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    linarith
  have := (abs_le.1 hq).1
  linarith

/-- On `|r| ≥ T₀/2 ≥ 8`: `Re ψ(¼ + ir/2) − log π ≥ log(T₀/4π) − 3`. -/
lemma psiRe_good {T₀ r : ℝ} (hT : 16 ≤ T₀) (hr : T₀ / 2 ≤ |r|) :
    Real.log (T₀ / (4 * π)) - 3 ≤ psiRe r - Real.log π := by
  have h := psiRe_ge_log (by linarith : 8 ≤ |r|)
  have hl : Real.log (T₀ / 4) ≤ Real.log (|r| / 2) := Real.log_le_log (by linarith) (by linarith)
  have e : Real.log (T₀ / (4 * π)) = Real.log (T₀ / 4) - Real.log π := by
    rw [show T₀ / (4 * π) = T₀ / 4 / π by field_simp,
      Real.log_div (div_pos (by linarith) (by norm_num)).ne' Real.pi_pos.ne']
  linarith

/-! ## The archimedean term -/

/-- Away from the window the Gaussian is small: `|r − T| ≥ T₀/2` gives
`w_{σ,T}(r) ≤ e^{−T₀²/(16σ²)}w_{√2σ,T}(r)`. -/
lemma gw_tail {σ : ℝ} (hσ : 0 < σ) {T₀ T r : ℝ} (h : T₀ ^ 2 / 4 ≤ (r - T) ^ 2) :
    gw σ T r ≤ Real.exp (-(T₀ ^ 2 / (16 * σ ^ 2))) * gw (Real.sqrt 2 * σ) T r := by
  unfold gw
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : 0 < σ ^ 2 := by positivity
  have key : -(r - T) ^ 2 / (2 * σ ^ 2) = -(T₀ ^ 2 / (16 * σ ^ 2)) + -(r - T) ^ 2 / (2 * (2 * σ ^ 2))
      - ((r - T) ^ 2 - T₀ ^ 2 / 4) / (4 * σ ^ 2) := by
    field_simp; ring
  rw [key]
  have : 0 ≤ ((r - T) ^ 2 - T₀ ^ 2 / 4) / (4 * σ ^ 2) := div_nonneg (by linarith) (by positivity)
  linarith

/-- **The archimedean term**: with `L₀ = log(T₀/4π) − 3`,
`−g_h(0)log π + (1/2π)∫h Re ψ ≥ (1/2π)(L₀∫h − (L₀ + 9)S₁²e^{−T₀²/(16σ²)}Ŵ_{√2σ}(0))`. -/
lemma arch_ge {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) {T₀ : ℝ} (hT : 16 ≤ T₀)
    (hL : 0 ≤ Real.log (T₀ / (4 * π)) - 3) :
    1 / (2 * π) * ((Real.log (T₀ / (4 * π)) - 3) * (∫ r, htestR N c σ T₀ r)
        - (Real.log (T₀ / (4 * π)) - 3 + 9) * S1 N c ^ 2 * Real.exp (-(T₀ ^ 2 / (16 * σ ^ 2)))
          * What (Real.sqrt 2 * σ) T₀ 0) ≤
      -(gh (htestR N c σ T₀) 0 * Real.log π) + 1 / (2 * π) * ∫ r, htestR N c σ T₀ r * psiRe r := by
  set L₀ := Real.log (T₀ / (4 * π)) - 3 with hL₀
  set E := Real.exp (-(T₀ ^ 2 / (16 * σ ^ 2))) with hE
  set K := (L₀ + 9) * S1 N c ^ 2 * E with hK
  have hσ' : 0 < Real.sqrt 2 * σ := by positivity
  have hiR := integrable_htestR hσ N c T₀
  have hiP := integrable_htestR_psi hσ N c T₀
  have hiW : Integrable (Wd (Real.sqrt 2 * σ) T₀) :=
    (integrable_gw hσ' T₀).add (integrable_gw hσ' (-T₀))
  have hgh0 : gh (htestR N c σ T₀) 0 = 1 / (2 * π) * ∫ r, htestR N c σ T₀ r := by
    unfold gh; simp only [mul_zero, Real.cos_zero, mul_one]
  have hW0 : ∫ r, Wd (Real.sqrt 2 * σ) T₀ r = What (Real.sqrt 2 * σ) T₀ 0 := by
    have := integral_Wd_cos hσ' T₀ 0
    simpa using this
  have hpt : ∀ r, L₀ * htestR N c σ T₀ r - K * Wd (Real.sqrt 2 * σ) T₀ r ≤
      htestR N c σ T₀ r * psiRe r - Real.log π * htestR N c σ T₀ r := by
    intro r
    have hh0 := htestR_nonneg N c σ T₀ r
    have hW' := (Wd_pos (Real.sqrt 2 * σ) T₀ r).le
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hK0 : 0 ≤ K := by rw [hK]; have := sq_nonneg (S1 N c); positivity
    by_cases hr : T₀ / 2 ≤ |r|
    · have hg := psiRe_good hT hr
      have h1 : L₀ * htestR N c σ T₀ r ≤ htestR N c σ T₀ r * psiRe r - Real.log π * htestR N c σ T₀ r := by
        have := mul_le_mul_of_nonneg_left hg hh0
        linarith
      have h2 : 0 ≤ K * Wd (Real.sqrt 2 * σ) T₀ r := mul_nonneg hK0 hW'
      linarith
    · push Not at hr
      have hr' := abs_lt.1 hr
      have hlow := psiRe_sub_log_pi_ge r
      have hWt : Wd σ T₀ r ≤ E * Wd (Real.sqrt 2 * σ) T₀ r := by
        unfold Wd
        rw [mul_add]
        refine add_le_add (gw_tail hσ ?_) (gw_tail hσ ?_)
        · nlinarith [mul_pos (by linarith : 0 < T₀ / 2 - r) (by linarith : 0 < 3 * T₀ / 2 - r)]
        · nlinarith [mul_pos (by linarith : 0 < r + T₀ / 2) (by linarith : 0 < r + 3 * T₀ / 2)]
      have hbound : htestR N c σ T₀ r ≤ S1 N c ^ 2 * (E * Wd (Real.sqrt 2 * σ) T₀ r) :=
        (htestR_le N c σ T₀ r).trans (mul_le_mul_of_nonneg_left hWt (sq_nonneg _))
      have h1 : -9 * htestR N c σ T₀ r ≤ htestR N c σ T₀ r * psiRe r - Real.log π * htestR N c σ T₀ r := by
        have := mul_le_mul_of_nonneg_left hlow hh0
        linarith
      have h2 : (L₀ + 9) * htestR N c σ T₀ r ≤ (L₀ + 9) * (S1 N c ^ 2 * (E * Wd (Real.sqrt 2 * σ) T₀ r)) :=
        mul_le_mul_of_nonneg_left hbound (by linarith)
      have h3 : (L₀ + 9) * (S1 N c ^ 2 * (E * Wd (Real.sqrt 2 * σ) T₀ r)) = K * Wd (Real.sqrt 2 * σ) T₀ r := by
        rw [hK]; ring
      linarith
  have hint : ∫ r, (L₀ * htestR N c σ T₀ r - K * Wd (Real.sqrt 2 * σ) T₀ r) ≤
      ∫ r, (htestR N c σ T₀ r * psiRe r - Real.log π * htestR N c σ T₀ r) :=
    integral_mono ((hiR.const_mul L₀).sub (hiW.const_mul K)) (hiP.sub (hiR.const_mul _)) hpt
  rw [integral_sub (hiR.const_mul L₀) (hiW.const_mul K), integral_sub hiP (hiR.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, hW0] at hint
  rw [hgh0]
  have hpi : 0 < 1 / (2 * π) := by positivity
  have := mul_le_mul_of_nonneg_left hint hpi.le
  refine this.trans (le_of_eq ?_)
  ring

/-! ## The prime side -/

lemma vonMangoldt_div_sqrt_le (n : ℕ) : Λ n / Real.sqrt n ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  rw [div_le_iff₀ hs]
  have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h2 : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt (by linarith)] at h2
  linarith

/-- **The prime side**: `2Σ_n Λ(n)n^{−1/2}g_h(log n) ≤ (Ŵ(0)/2π)(log N + log 4 + 4)S₂ + (π/3)E₁N²S₁²`,
`E₁ = 2σ√(2π)e^{−σ²/(16N²)}`: Landau's form on the exact matches, plus the near misses. -/
lemma prime_le {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hσN : 16 * (N : ℝ) ≤ σ ^ 2) (c : ℕ → ℝ) (T₀ : ℝ) :
    2 * ∑' n : ℕ, Λ n / Real.sqrt n * gh (htestR N c σ T₀) (Real.log n) ≤
      What σ T₀ 0 / (2 * π) * (Real.log N + (Real.log 4 + 4)) * S2 N c
        + π / 3 * (2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2)))) * N ^ 2 * S1 N c ^ 2 := by
  set E₁ := 2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2))) with hE₁
  set f : ℕ → ℝ := fun n => Λ n / Real.sqrt n * gh (htestR N c σ T₀) (Real.log n) with hf
  set a : ℕ → ℝ := fun n => Λ n / Real.sqrt n * (What σ T₀ 0 / (2 * π) * ex N c n) with ha
  set M := E₁ * N ^ 2 * S1 N c ^ 2 / π with hM
  have hE0 : 0 ≤ E₁ := by positivity
  have ha0 : ∀ n ∉ Icc 1 N, a n = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [ha]
    · have : N < n := by
        by_contra h
        push Not at h
        exact hn (Finset.mem_Icc.2 ⟨hn0, h⟩)
      simp [ha, ex_eq_zero N c this]
  have hb : ∀ n : ℕ, |f n - a n| ≤ M * (1 / (n : ℝ) ^ 2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [hf, ha]
    have hd := sum_What_log_sub hσ hσN c T₀ hn0
    have hΛ := vonMangoldt_div_sqrt_le n
    have hΛ0 : 0 ≤ Λ n / Real.sqrt n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    have hn1 : (0 : ℝ) < n := by exact_mod_cast hn0
    have e : f n - a n = Λ n / Real.sqrt n * (1 / (2 * π)) *
        (∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j - Real.log n)
          - What σ T₀ 0 * ex N c n) := by
      simp only [hf, ha]
      rw [gh_htestR hσ]
      ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg hΛ0, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
    calc Λ n / Real.sqrt n * (1 / (2 * π)) *
          |∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * What σ T₀ (Real.log j' - Real.log j - Real.log n)
            - What σ T₀ 0 * ex N c n|
        ≤ 2 * (1 / (2 * π)) * (E₁ * (N ^ 2 / n ^ 2) * S1 N c ^ 2) := by
          gcongr
      _ = M * (1 / (n : ℝ) ^ 2) := by
          rw [hM]
          field_simp
  have hsum2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.2 one_lt_two
  have hsumM : Summable (fun n : ℕ => M * (1 / (n : ℝ) ^ 2)) := hsum2.mul_left M
  have hsb : Summable (fun n => f n - a n) :=
    Summable.of_norm_bounded hsumM fun n => by rw [Real.norm_eq_abs]; exact hb n
  have hsa : Summable a := summable_of_ne_finset_zero ha0
  have hsplit : ∑' n, f n = ∑' n, a n + ∑' n, (f n - a n) := by
    rw [← hsa.tsum_add hsb]
    congr 1
    funext n
    ring
  have hta : ∑' n, a n = ∑ n ∈ Icc 1 N, a n := tsum_eq_sum ha0
  have htb : ∑' n, (f n - a n) ≤ M * (π ^ 2 / 6) := by
    calc ∑' n, (f n - a n) ≤ ∑' n : ℕ, M * (1 / (n : ℝ) ^ 2) :=
          hsb.tsum_le_tsum (fun n => (le_abs_self _).trans (hb n)) hsumM
      _ = M * (π ^ 2 / 6) := by rw [hsum2.tsum_mul_left M, hasSum_zeta_two.tsum_eq]
  have hland : 2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n ≤
      (Real.log N + (Real.log 4 + 4)) * S2 N c := landau_le N c
  have hsumA : ∑ n ∈ Icc 1 N, a n =
      What σ T₀ 0 / (2 * π) * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha]
    ring
  have hW0 : 0 ≤ What σ T₀ 0 / (2 * π) := by rw [What_zero]; positivity
  have hmul := mul_le_mul_of_nonneg_left hland hW0
  have hMe : 2 * (M * (π ^ 2 / 6)) = π / 3 * E₁ * N ^ 2 * S1 N c ^ 2 := by
    rw [hM]
    field_simp
    ring
  rw [hsplit, hta, hsumA]
  nlinarith

/-! ## The pole term -/

lemma pole_ge {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (c : ℕ → ℝ) (T₀ : ℝ) :
    -(2 * (N * S1 N c) ^ 2 * Real.exp (1 / (2 * σ ^ 2)) * Wd σ T₀ 0) ≤
      (htest N c σ T₀ (I / 2) + htest N c σ T₀ (-(I / 2))).re := by
  have h1 := norm_htest_le hσ N c T₀ (z := I / 2) (by norm_num)
  have h2 := norm_htest_le hσ N c T₀ (z := -(I / 2)) (by norm_num)
  have hre1 : (I / 2 : ℂ).re = 0 := by simp
  have hre2 : (-(I / 2) : ℂ).re = 0 := by simp
  rw [hre1] at h1
  rw [hre2] at h2
  have h3 := Complex.abs_re_le_norm (htest N c σ T₀ (I / 2) + htest N c σ T₀ (-(I / 2)))
  have h4 := norm_add_le (htest N c σ T₀ (I / 2)) (htest N c σ T₀ (-(I / 2)))
  have h5 := neg_abs_le (htest N c σ T₀ (I / 2) + htest N c σ T₀ (-(I / 2))).re
  linarith

/-! ## The zero side under RH -/

lemma dp_eq_DC (N : ℕ) (x : ℕ → ℝ) (t : ℝ) :
    dp (Icc 1 N) (fun n => ((x n * Real.sqrt n : ℝ) : ℂ)) t = DC N (fun n => x n * Real.sqrt n) t := by
  unfold dp DC
  refine Finset.sum_congr rfl fun j _ => ?_
  generalize Real.log (j : ℝ) = L
  rw [show I * ((t * L : ℝ) : ℂ) = I * (t : ℂ) * (L : ℂ) by push_cast; ring]

/-- Under RH, `h(t_ρ) = |V_x(ρ)|²W(γ)` with the coefficients `c_n = x_n√n`. -/
lemma zero_term_eq (hRH : RiemannHypothesis) (N : ℕ) (x : ℕ → ℝ) (σ T₀ : ℝ) (q : ZIdx) :
    htest N (fun n => x n * Real.sqrt n) σ T₀ ((zetaZeroFamily q - 1 / 2) / I) =
      ((‖BallRate.dpoly N x q‖ ^ 2 * Wd σ T₀ (zetaZeroFamily q).im : ℝ) : ℂ) := by
  have ht : (zetaZeroFamily q - 1 / 2) / I = ((zetaZeroFamily q).im : ℂ) := by
    rw [BallHadamard.zZF_sub_half hRH q, mul_div_cancel_left₀ _ Complex.I_ne_zero]
  rw [ht, htest_ofReal]
  congr 1
  unfold htestR
  rw [BallSampling.dpoly_eq_conj hRH, Complex.norm_conj, dp_eq_DC, norm_DC_ofReal_sq]

/-- **The zero side is dominated by the orbit form**: `W(γ)(¼ + γ²) ≤ 2(1 + 2T₀² + 4σ²)`. -/
lemma zero_side_le (hRH : RiemannHypothesis) (N : ℕ) (x : ℕ → ℝ) {σ : ℝ} (hσ : 0 < σ) (T₀ : ℝ) {Z : ℝ}
    (hZ : HasSum (fun q => ‖BallRate.dpoly N x q‖ ^ 2 * Wd σ T₀ (zetaZeroFamily q).im) Z) :
    Z ≤ 2 * (1 + 2 * T₀ ^ 2 + 4 * σ ^ 2) * BallWeil.form N x := by
  have hF := (BallRate.hasSum_form hRH N x).mul_left (2 * (1 + 2 * T₀ ^ 2 + 4 * σ ^ 2))
  refine hasSum_le (fun q => ?_) hZ hF
  set γ := (zetaZeroFamily q).im
  have hpos : 0 < 1 / 4 + γ ^ 2 := by positivity
  have hWle : Wd σ T₀ γ ≤ 2 * (1 + 2 * T₀ ^ 2 + 4 * σ ^ 2) / (1 / 4 + γ ^ 2) := by
    rw [le_div_iff₀ hpos]
    have h1 := Wd_mul_le hσ T₀ γ
    have h2 := (Wd_pos σ T₀ γ).le
    have e : Wd σ T₀ γ * (1 / 4 + γ ^ 2) = Wd σ T₀ γ * (1 + γ ^ 2) - 3 / 4 * Wd σ T₀ γ := by ring
    linarith
  calc ‖BallRate.dpoly N x q‖ ^ 2 * Wd σ T₀ γ
      ≤ ‖BallRate.dpoly N x q‖ ^ 2 * (2 * (1 + 2 * T₀ ^ 2 + 4 * σ ^ 2) / (1 / 4 + γ ^ 2)) :=
        mul_le_mul_of_nonneg_left hWle (sq_nonneg _)
    _ = 2 * (1 + 2 * T₀ ^ 2 + 4 * σ ^ 2) * (‖BallRate.dpoly N x q‖ ^ 2 / (1 / 4 + γ ^ 2)) := by ring

/-! ## The density bound -/

/-- The error coefficient of `density_bound`: pole, off-diagonal, archimedean tail and prime tail. -/
def errD (N : ℕ) (σ T₀ : ℝ) : ℝ :=
  2 * N ^ 2 * Real.exp (1 / (2 * σ ^ 2)) * Wd σ T₀ 0
    + (Real.log (T₀ / (4 * π)) - 3) / (2 * π)
        * (2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2)))) * N ^ 2
    + (Real.log (T₀ / (4 * π)) - 3 + 9) / (2 * π) * Real.exp (-(T₀ ^ 2 / (16 * σ ^ 2)))
        * What (Real.sqrt 2 * σ) T₀ 0
    + π / 3 * (2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2)))) * N ^ 2

/-- **The density bound** (RH). For `σ² ≥ 16N`, `T₀ ≥ 16` and `L₀ = log(T₀/4π) − 3 ≥ 0`, every real `x` on
`[1, N]` with `c_n = x_n√n` satisfies
`(Ŵ(0)/2π)(L₀ − log N − log 4 − 4)Σc_n² − errD·(Σ|c_n|)² ≤ 2(1 + 2T₀² + 4σ²)Q_N(x)`, `Ŵ(0) = 2σ√(2π)`:
the zeros near height `T₀`, of density `(1/2π)log(T₀/2π)`, sample the Dirichlet polynomials of length `N`
once their density beats the bandwidth `(1/2π)log N` plus Landau's arithmetic term. -/
theorem density_bound (hRH : RiemannHypothesis) {N : ℕ} {σ T₀ : ℝ} (hσ : 0 < σ)
    (hσN : 16 * (N : ℝ) ≤ σ ^ 2) (hT : 16 ≤ T₀) (hL : 0 ≤ Real.log (T₀ / (4 * π)) - 3) (x : ℕ → ℝ) :
    What σ T₀ 0 / (2 * π) * (Real.log (T₀ / (4 * π)) - 3 - Real.log N - (Real.log 4 + 4))
        * S2 N (fun n => x n * Real.sqrt n)
      - errD N σ T₀ * S1 N (fun n => x n * Real.sqrt n) ^ 2
      ≤ 2 * (1 + 2 * T₀ ^ 2 + 4 * σ ^ 2) * BallWeil.form N x := by
  set c : ℕ → ℝ := fun n => x n * Real.sqrt n with hc
  have hsum := (weil_htest hσ N c T₀).2
  have hre := Complex.hasSum_re hsum
  have hterm : ∀ q, (htest N c σ T₀ ((zetaZeroFamily q - 1 / 2) / I)).re =
      ‖BallRate.dpoly N x q‖ ^ 2 * Wd σ T₀ (zetaZeroFamily q).im := fun q => by
    rw [hc, zero_term_eq hRH N x σ T₀ q, Complex.ofReal_re]
  simp only [hterm] at hre
  rw [Complex.add_re, Complex.ofReal_re] at hre
  have hZ := zero_side_le hRH N x hσ T₀ hre
  have hpole := pole_ge hσ N c T₀
  have harch := arch_ge hσ N c hT hL
  have hint := integral_htestR_ge hσ hσN c T₀
  have hprime := prime_le hσ hσN c T₀
  have hpi : 0 < 1 / (2 * π) := by positivity
  have hL' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hint hL) hpi.le
  have e1 : What σ T₀ 0 / (2 * π) = 1 / (2 * π) * What σ T₀ 0 := by ring
  have e2 : (Real.log (T₀ / (4 * π)) - 3) / (2 * π) = 1 / (2 * π) * (Real.log (T₀ / (4 * π)) - 3) := by ring
  have e3 : (Real.log (T₀ / (4 * π)) - 3 + 9) / (2 * π) =
      1 / (2 * π) * (Real.log (T₀ / (4 * π)) - 3 + 9) := by ring
  unfold errD
  rw [e1] at hprime ⊢
  rw [e2, e3]
  linarith

/-! ## The rate -/

lemma one_le_log_nat {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma exp_neg_le_inv_pow {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 64 * Real.log N ≤ a) :
    Real.exp (-a) ≤ 1 / (N : ℝ) ^ 64 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : Real.exp (64 * Real.log N) = (N : ℝ) ^ 64 := by
    rw [show (64 : ℝ) * Real.log N = Real.log ((N : ℝ) ^ 64) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [one_div, ← e, ← Real.exp_neg]
  exact Real.exp_le_exp.2 (by linarith)

/-- **The error is negligible** at `σ = 32N log N`, `T₀ = 10⁶N log²N`: `N·errD ≤ σ/2`. -/
lemma errD_le {N : ℕ} (hN : 3 ≤ N) {σ T₀ : ℝ} (hσdef : σ = 32 * N * Real.log N)
    (hT₀def : T₀ = 10 ^ 6 * N * Real.log N ^ 2) (hL : 0 ≤ Real.log (T₀ / (4 * π)) - 3)
    (hL0up : Real.log (T₀ / (4 * π)) - 3 ≤ 10 ^ 6 * N ^ 3) :
    errD N σ T₀ * N ≤ σ / 2 := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hℓ1 : 1 ≤ Real.log N := one_le_log_nat hN
  have hσ0 : 0 ≤ σ := by rw [hσdef]; exact mul_nonneg (by positivity) (by linarith)
  have hσ96 : 96 ≤ σ := by rw [hσdef]; nlinarith only [hN3, hℓ1]
  have hσ1 : 1 ≤ σ := by linarith
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hπ6 : (6 : ℝ) ≤ 2 * π := by linarith
  have hsq0 : 0 ≤ Real.sqrt (2 * π) := Real.sqrt_nonneg _
  have hsq3 : Real.sqrt (2 * π) ≤ 3 := by
    calc Real.sqrt (2 * π) ≤ Real.sqrt (3 ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 3 := Real.sqrt_sq (by norm_num)
  have hsq2 : Real.sqrt 2 ≤ 2 := by
    calc Real.sqrt 2 ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := Real.sqrt_sq (by norm_num)
  set δ : ℝ := 1 / (N : ℝ) ^ 64 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hS : 64 * Real.log N ≤ σ ^ 2 / (16 * N ^ 2) := by
    rw [hσdef, show (32 * (N : ℝ) * Real.log N) ^ 2 / (16 * N ^ 2) = 64 * Real.log N ^ 2 by
      field_simp; ring]
    nlinarith only [hℓ1]
  have hTT : 64 * Real.log N ≤ T₀ ^ 2 / (16 * σ ^ 2) := by
    rw [hσdef, hT₀def, show (10 ^ 6 * (N : ℝ) * Real.log N ^ 2) ^ 2 / (16 * (32 * N * Real.log N) ^ 2)
      = 10 ^ 12 * Real.log N ^ 2 / 16384 by field_simp; ring]
    nlinarith only [hℓ1]
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hT2 : T₀ ^ 2 / (16 * σ ^ 2) ≤ T₀ ^ 2 / (2 * σ ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have heS := exp_neg_le_inv_pow (by omega : 1 ≤ N) hS
  have heT := exp_neg_le_inv_pow (by omega : 1 ≤ N) hTT
  have heT2 := exp_neg_le_inv_pow (by omega : 1 ≤ N) (hTT.trans hT2)
  rw [← hδ] at heS heT heT2
  have heS0 := (Real.exp_pos (-(σ ^ 2 / (16 * N ^ 2)))).le
  have heT0 := (Real.exp_pos (-(T₀ ^ 2 / (16 * σ ^ 2)))).le
  have heT20 := (Real.exp_pos (-(T₀ ^ 2 / (2 * σ ^ 2)))).le
  have he3 : Real.exp (1 / (2 * σ ^ 2)) ≤ 3 := by
    have h1 : 1 / (2 * σ ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith only [hσ1]
    have h2 := Real.exp_one_lt_d9
    calc Real.exp (1 / (2 * σ ^ 2)) ≤ Real.exp 1 := Real.exp_le_exp.2 h1
      _ ≤ 3 := by linarith
  have hWd0 : Wd σ T₀ 0 = 2 * Real.exp (-(T₀ ^ 2 / (2 * σ ^ 2))) := by
    unfold Wd gw
    rw [show ((0 : ℝ) - T₀) ^ 2 = T₀ ^ 2 by ring, show ((0 : ℝ) - -T₀) ^ 2 = T₀ ^ 2 by ring, neg_div]
    ring
  -- the four terms
  have ht1 : 2 * (N : ℝ) ^ 2 * Real.exp (1 / (2 * σ ^ 2)) * Wd σ T₀ 0 ≤ 12 * N ^ 2 * δ := by
    rw [hWd0]
    have h := mul_le_mul he3 heT2 heT20 (by norm_num)
    have h' := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4 * N ^ 2)
    linarith only [h']
  have hB : 2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2))) ≤ 2 * σ * 3 * δ := by
    have h := mul_le_mul hsq3 heS heS0 (by norm_num)
    have h' := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * σ)
    linarith only [h']
  have hB0 : 0 ≤ 2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2))) :=
    mul_nonneg (mul_nonneg (by linarith) hsq0) heS0
  have ht2 : (Real.log (T₀ / (4 * π)) - 3) / (2 * π)
      * (2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2)))) * N ^ 2
      ≤ 10 ^ 6 * σ * N ^ 5 * δ := by
    have hA : (Real.log (T₀ / (4 * π)) - 3) / (2 * π) ≤ 10 ^ 6 * N ^ 3 / 6 := by
      calc (Real.log (T₀ / (4 * π)) - 3) / (2 * π) ≤ (Real.log (T₀ / (4 * π)) - 3) / 6 :=
            div_le_div_of_nonneg_left hL (by norm_num) hπ6
        _ ≤ 10 ^ 6 * N ^ 3 / 6 := div_le_div_of_nonneg_right hL0up (by norm_num)
    calc (Real.log (T₀ / (4 * π)) - 3) / (2 * π)
          * (2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2)))) * N ^ 2
        ≤ 10 ^ 6 * N ^ 3 / 6 * (2 * σ * 3 * δ) * N ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul hA hB hB0 (by positivity)
      _ = 10 ^ 6 * σ * N ^ 5 * δ := by ring
  have ht3 : (Real.log (T₀ / (4 * π)) - 3 + 9) / (2 * π) * Real.exp (-(T₀ ^ 2 / (16 * σ ^ 2)))
      * What (Real.sqrt 2 * σ) T₀ 0 ≤ 2 * (10 ^ 6 * N ^ 3 + 9) * σ * δ := by
    rw [What_zero]
    have hA : (Real.log (T₀ / (4 * π)) - 3 + 9) / (2 * π) ≤ (10 ^ 6 * N ^ 3 + 9) / 6 := by
      calc (Real.log (T₀ / (4 * π)) - 3 + 9) / (2 * π) ≤ (Real.log (T₀ / (4 * π)) - 3 + 9) / 6 :=
            div_le_div_of_nonneg_left (by linarith) (by norm_num) hπ6
        _ ≤ (10 ^ 6 * N ^ 3 + 9) / 6 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have hC : Real.exp (-(T₀ ^ 2 / (16 * σ ^ 2))) * (2 * (Real.sqrt 2 * σ) * Real.sqrt (2 * π))
        ≤ δ * (12 * σ) := by
      have h1 := mul_le_mul hsq2 hsq3 hsq0 (by norm_num)
      have h2 : 2 * (Real.sqrt 2 * σ) * Real.sqrt (2 * π) ≤ 12 * σ := by
        have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * σ)
        linarith only [this]
      exact mul_le_mul heT h2 (by positivity) hδ0
    have hC0 : 0 ≤ Real.exp (-(T₀ ^ 2 / (16 * σ ^ 2))) * (2 * (Real.sqrt 2 * σ) * Real.sqrt (2 * π)) :=
      mul_nonneg heT0 (by positivity)
    calc (Real.log (T₀ / (4 * π)) - 3 + 9) / (2 * π) * Real.exp (-(T₀ ^ 2 / (16 * σ ^ 2)))
          * (2 * (Real.sqrt 2 * σ) * Real.sqrt (2 * π))
        = (Real.log (T₀ / (4 * π)) - 3 + 9) / (2 * π)
          * (Real.exp (-(T₀ ^ 2 / (16 * σ ^ 2))) * (2 * (Real.sqrt 2 * σ) * Real.sqrt (2 * π))) := by ring
      _ ≤ (10 ^ 6 * N ^ 3 + 9) / 6 * (δ * (12 * σ)) := mul_le_mul hA hC hC0 (by positivity)
      _ = 2 * (10 ^ 6 * N ^ 3 + 9) * σ * δ := by ring
  have ht4 : π / 3 * (2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2)))) * N ^ 2
      ≤ 7 * σ * N ^ 2 * δ := by
    have hA : π / 3 ≤ 7 / 6 := by linarith
    calc π / 3 * (2 * σ * Real.sqrt (2 * π) * Real.exp (-(σ ^ 2 / (16 * N ^ 2)))) * N ^ 2
        ≤ 7 / 6 * (2 * σ * 3 * δ) * N ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul hA hB hB0 (by norm_num)
      _ = 7 * σ * N ^ 2 * δ := by ring
  -- powers of `N` against `δ = N^{−64}`
  have hP : (N : ℝ) ^ 6 * δ ≤ 1 / 10 ^ 8 := by
    rw [hδ, show (N : ℝ) ^ 6 * (1 / (N : ℝ) ^ 64) = 1 / (N : ℝ) ^ 58 by field_simp]
    apply one_div_le_one_div_of_le (by norm_num)
    calc (10 : ℝ) ^ 8 ≤ 3 ^ 58 := by norm_num
      _ ≤ (N : ℝ) ^ 58 := pow_le_pow_left₀ (by norm_num) hN3 58
  have hk : ∀ k ≤ 6, (N : ℝ) ^ k * δ ≤ (N : ℝ) ^ 6 * δ := fun k hk =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 hk) hδ0
  have h3 := hk 3 (by norm_num)
  have h4 := hk 4 (by norm_num)
  have h1 := hk 1 (by norm_num)
  have hs3 := mul_le_mul_of_nonneg_left h3 hσ0
  have hs4 := mul_le_mul_of_nonneg_left h4 hσ0
  have hs1 := mul_le_mul_of_nonneg_left h1 hσ0
  have hs6 := mul_le_mul_of_nonneg_left hP hσ0
  unfold errD
  have hsum := add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4
  have hNmul := mul_le_mul_of_nonneg_right hsum hN0.le
  linarith only [hNmul, h3, hs3, hs4, hs1, hs6, hP, hσ96]

/-- **The rate under RH**: `λ_N ≥ 10⁻¹²/(N log³N)` for every `N ≥ 3`, i.e.
`Q_N(x) ≥ Σ x_n²/(10¹²N log³N)`. The exponent `1` of `N` is the Nyquist exponent; the sampling hypothesis of
`BallRate.rate_of_sampling` is replaced by the density of the zeros (`density_bound`). -/
theorem rate_rh (hRH : RiemannHypothesis) {N : ℕ} (hN : 3 ≤ N) (x : ℕ → ℝ) :
    1 / (10 ^ 12 * N * Real.log N ^ 3) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hℓ1 : 1 ≤ Real.log N := one_le_log_nat hN
  have hℓN : Real.log N ≤ N := by have := Real.log_le_sub_one_of_pos hN0; linarith
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 32 * N * Real.log N := ⟨_, rfl⟩
  obtain ⟨T₀, hT₀def⟩ : ∃ T₀ : ℝ, T₀ = 10 ^ 6 * N * Real.log N ^ 2 := ⟨_, rfl⟩
  have hσ : 0 < σ := by rw [hσdef]; exact mul_pos (by positivity) (by linarith)
  have hl2 : 1 ≤ Real.log N ^ 2 := by nlinarith only [hℓ1]
  have hσN : 16 * (N : ℝ) ≤ σ ^ 2 := by
    rw [hσdef]
    have h1 : (N : ℝ) ≤ N ^ 2 := by nlinarith only [hN1]
    have h2 : (N : ℝ) ^ 2 ≤ N ^ 2 * Real.log N ^ 2 := le_mul_of_one_le_right (by positivity) hl2
    nlinarith only [h1, h2]
  have hT0 : 0 < T₀ := by rw [hT₀def]; exact mul_pos (by positivity) (pow_pos (by linarith) 2)
  have hT : 16 ≤ T₀ := by rw [hT₀def]; nlinarith only [hN3, hl2]
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hexp9 : Real.exp 9 ≤ 8104 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc Real.exp 1 ^ 9 ≤ 2.7182818286 ^ 9 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 9
      _ ≤ 8104 := by norm_num
  have hlogT : 9 + (Real.log 4 + Real.log N) ≤ Real.log (T₀ / (4 * π)) := by
    have hpos : 0 < Real.exp 9 * (4 * N) := by positivity
    have hle : Real.exp 9 * (4 * N) ≤ T₀ / (4 * π) := by
      rw [le_div_iff₀ (by positivity), hT₀def]
      have h1 : Real.exp 9 * (4 * N) * (4 * π) ≤ 8104 * (4 * N) * (4 * 3.15) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hexp9 (by positivity)) (by linarith)
          (by positivity) (by positivity)
      nlinarith only [h1, hl2, hN0]
    have := Real.log_le_log hpos hle
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_mul (by norm_num) (by positivity)] at this
    exact this
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ Real.log (T₀ / (4 * π)) - 3 := by linarith
  have hmargin : 2 ≤ Real.log (T₀ / (4 * π)) - 3 - Real.log N - (Real.log 4 + 4) := by linarith
  have hL0up : Real.log (T₀ / (4 * π)) - 3 ≤ 10 ^ 6 * N ^ 3 := by
    have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < T₀ / (4 * π))
    have h2 : T₀ / (4 * π) ≤ T₀ := div_le_self hT0.le (by nlinarith)
    have h3 : T₀ ≤ 10 ^ 6 * N ^ 3 := by
      rw [hT₀def]
      have : Real.log N ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hℓN 2
      nlinarith only [this, hN0]
    linarith
  have hD := density_bound hRH hσ hσN hT hL x
  have herr := errD_le hN hσdef hT₀def hL hL0up
  set c : ℕ → ℝ := fun n => x n * Real.sqrt n with hc
  -- the main coefficient
  have hsqrt : 2.5 ≤ Real.sqrt (2 * π) := ((Real.lt_sqrt (by norm_num)).2 (by nlinarith)).le
  have hA : 3 / 4 * σ ≤ What σ T₀ 0 / (2 * π) := by
    rw [What_zero, le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hsqrt hσ.le
    have h2 := mul_le_mul_of_nonneg_left hpi2.le hσ.le
    linarith only [h1, h2, hσ]
  have hS2 := S2_nonneg N c
  have hmain : 3 / 2 * σ * S2 N c ≤
      What σ T₀ 0 / (2 * π) * (Real.log (T₀ / (4 * π)) - 3 - Real.log N - (Real.log 4 + 4)) * S2 N c := by
    apply mul_le_mul_of_nonneg_right _ hS2
    calc 3 / 2 * σ = 3 / 4 * σ * 2 := by ring
      _ ≤ _ := mul_le_mul hA hmargin (by norm_num) (by linarith)
  -- Cauchy–Schwarz: `S₁² ≤ N S₂`
  have hCS : S1 N c ^ 2 ≤ N * S2 N c := by
    have h := sq_sum_le_card_mul_sum_sq (s := Icc 1 N) (f := fun j => |c j|)
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h
    simpa [S1, S2, sq_abs] using h
  have hErr : errD N σ T₀ * S1 N c ^ 2 ≤ σ / 2 * S2 N c := by
    by_cases h0 : 0 ≤ errD N σ T₀
    · calc errD N σ T₀ * S1 N c ^ 2 ≤ errD N σ T₀ * (N * S2 N c) := mul_le_mul_of_nonneg_left hCS h0
        _ = errD N σ T₀ * N * S2 N c := by ring
        _ ≤ σ / 2 * S2 N c := mul_le_mul_of_nonneg_right herr hS2
    · push Not at h0
      have : errD N σ T₀ * S1 N c ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0.le (sq_nonneg _)
      have : 0 ≤ σ / 2 * S2 N c := mul_nonneg (by linarith) hS2
      linarith
  -- `Σ x_n² ≤ S₂`
  have hx : ∑ n ∈ Icc 1 N, x n ^ 2 ≤ S2 N c := by
    unfold S2
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    simp only [hc]
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    nlinarith only [sq_nonneg (x n), hn1]
  have hx0 : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set K := 2 * (1 + 2 * T₀ ^ 2 + 4 * σ ^ 2) with hK
  have hK0 : 0 < K := by positivity
  have hform : σ * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ K * BallWeil.form N x := by
    have := mul_le_mul_of_nonneg_left hx hσ.le
    linarith only [hD, hmain, hErr, this]
  have hKb : K ≤ 10 ^ 12 * N * Real.log N ^ 3 * σ := by
    rw [hK, hT₀def, hσdef]
    have hN2 : 9 ≤ (N : ℝ) ^ 2 := by nlinarith only [hN3]
    have h1 : 9 ≤ (N : ℝ) ^ 2 * Real.log N ^ 2 := by nlinarith only [hN2, hl2]
    have h2 : (N : ℝ) ^ 2 * Real.log N ^ 2 ≤ (N : ℝ) ^ 2 * Real.log N ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [hl2]
    nlinarith only [h1, h2]
  have hpos : 0 < 10 ^ 12 * (N : ℝ) * Real.log N ^ 3 := by
    have : 0 < Real.log N := by linarith
    positivity
  calc 1 / (10 ^ 12 * N * Real.log N ^ 3) * ∑ n ∈ Icc 1 N, x n ^ 2
      ≤ σ / K * ∑ n ∈ Icc 1 N, x n ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hx0
        rw [div_le_div_iff₀ hpos hK0]
        linarith only [hKb]
    _ ≤ BallWeil.form N x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hK0]
        linarith only [hform]

end BallDensity
