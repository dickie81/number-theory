import BallSharp

/-! # No Dirichlet polynomial of length `N` vanishes at every zero up to height `2000N` (RH)

`BallSharp.sampling_log` gives, for `T ≥ 2000N`,
`Σ_{|γ_ρ| ≤ T}|Σ_{n ≤ N} x_n n^ρ|² ≥ (T/11)(log(T/N) − 7)Σ_{n ≤ N} x_n² n`, and `log 2000 > 7`. So a polynomial of
length `N` that vanishes at every zero up to height `T` is zero.

* `eq_zero_of_silent`: real `x`, in the form `Σ_{n ≤ N} x_n n^ρ` of the sampling theorems.
* `dirichlet_eq_zero`: complex `b`, in the usual form `Σ_{n ≤ N} b_n n^{−s}`. Under RH `1 − ρ = ρ̄`, so
  `Σ b_n n^{−ρ}` vanishing at every zero makes `Σ (b_n/n) n^ρ` vanish there; so do its real and imaginary parts,
  because the zeros are closed under conjugation; and the real case applies to each.

The constant `2000` is not the truth. Smoothed partial sums of `ζ` are nearly silent at the zeros up to height
about `2πN` (formalisations/ball-rate.md, "What silence costs"), and with `N` coefficients a polynomial can vanish
exactly at any `N − 1` points, which the zeros up to a height `≍ N/log N` are.
-/

open Complex ComplexConjugate Finset

namespace BallSilent

open BallRate WeilForm WeilTest

/-- `log(T/N) > 7` once `T ≥ 2000N`, since `e⁷ < 1097`. -/
lemma seven_lt_log {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T) : 7 < Real.log (T / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h2000 : (2000 : ℝ) ≤ T / N := by
    rw [le_div_iff₀ hN0]
    linarith
  have he : Real.exp 7 < 2000 := by
    have h := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    have e : Real.exp 7 = Real.exp 1 ^ 7 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    calc Real.exp 1 ^ 7 < 2.7182818286 ^ 7 := by gcongr
      _ < 2000 := by norm_num
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

/-- `BallLattice.pw q n` is `n^ρ`. -/
lemma pw_eq_cpow (q : ZIdx) {n : ℕ} (hn : 1 ≤ n) :
    BallLattice.pw q n = (n : ℂ) ^ zetaZeroFamily q := by
  unfold BallLattice.pw
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hn0, mul_comm]
  congr 2
  rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]

/-- **No real polynomial of length `N` is silent at the zeros up to height `2000N`** (RH): for `N ≥ 1`, `T ≥ 2000N`
and real `x`, if `Σ_{n ≤ N} x_n n^ρ = 0` at every nontrivial zero `ρ` of `ζ` with `|Im ρ| ≤ T`, then `x_n = 0` for
`1 ≤ n ≤ N`. -/
theorem eq_zero_of_silent (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T)
    (x : ℕ → ℝ) (h : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
      ∑ n ∈ Icc 1 N, (x n : ℂ) * (n : ℂ) ^ ρ = 0) :
    ∀ n ∈ Icc 1 N, x n = 0 := by
  have hS := BallSharp.sampling_log hRH hN hTN x
  have hzero : ∑ q ∈ zerosUpTo T, ‖dpoly N x q‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    have hT := mem_zerosUpTo.1 hq
    have hz : IsNontrivialZero (zetaZeroFamily q) := q.1.2
    have hd : dpoly N x q = 0 := by
      unfold dpoly
      rw [← h _ hz.1 hz.re_pos hz.re_lt_one hT]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [pw_eq_cpow q (Finset.mem_Icc.1 hn).1]
    rw [hd, norm_zero]
    norm_num
  rw [hzero] at hS
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  have hc : 0 < T / 11 * (Real.log (T / N) - 7) :=
    mul_pos (div_pos hT0 (by norm_num)) (by linarith [seven_lt_log hN hTN])
  have hnn : ∀ n ∈ Icc 1 N, 0 ≤ x n ^ 2 * (n : ℝ) := fun n _ => by positivity
  have hsum : ∑ n ∈ Icc 1 N, x n ^ 2 * (n : ℝ) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg hnn)
    by_contra hpos
    have := mul_pos hc (not_le.1 hpos)
    linarith
  intro n hn
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
  have hx2 : x n ^ 2 = 0 := by
    rcases mul_eq_zero.1 hterm with h2 | h2
    · exact h2
    · linarith
  exact pow_eq_zero_iff (by norm_num) |>.1 hx2

/-- `n^ρ̄` is the conjugate of `n^ρ`. -/
lemma natCast_cpow_conj (n : ℕ) (ρ : ℂ) : (n : ℂ) ^ conj ρ = conj ((n : ℂ) ^ ρ) := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne), Complex.conj_natCast]

/-- **No Dirichlet polynomial of length `N` vanishes at every zero up to height `2000N`** (RH): for `N ≥ 1`,
`T ≥ 2000N` and complex `b`, if `Σ_{n ≤ N} b_n n^{−ρ} = 0` at every nontrivial zero `ρ` of `ζ` with `|Im ρ| ≤ T`,
then `b_n = 0` for `1 ≤ n ≤ N`. -/
theorem dirichlet_eq_zero (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hTN : 2000 * N ≤ T)
    (b : ℕ → ℂ) (h : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
      ∑ n ∈ Icc 1 N, b n * (n : ℂ) ^ (-ρ) = 0) :
    ∀ n ∈ Icc 1 N, b n = 0 := by
  -- the zeros up to height `T` are closed under conjugation
  have hzc : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
      riemannZeta (conj ρ) = 0 ∧ 0 < (conj ρ).re ∧ (conj ρ).re < 1 ∧ |(conj ρ).im| ≤ T :=
    fun ρ hρ h0 h1 hT => ⟨by rw [riemannZeta_conj, hρ, map_zero], by simpa using h0, by simpa using h1,
      by simpa using hT⟩
  -- `Σ (b_n/n) n^ρ = Σ b_n n^{−(1−ρ)} = Σ b_n n^{−ρ̄} = 0`, since `Re ρ = ½` under RH
  have hx : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
      ∑ n ∈ Icc 1 N, b n / n * (n : ℂ) ^ ρ = 0 := by
    intro ρ hρ h0 h1 hT
    have hre : ρ.re = 1 / 2 := by
      refine hRH ρ hρ ?_ ?_
      · rintro ⟨k, rfl⟩
        have : (0 : ℝ) < ((-2 : ℂ) * ((k : ℂ) + 1)).re := h0
        simp at this
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      · rintro rfl
        norm_num at h1
    have hcj : conj ρ = 1 - ρ := Complex.ext (by simp [hre]; norm_num) (by simp)
    obtain ⟨c0, c1, c2, c3⟩ := hzc ρ hρ h0 h1 hT
    rw [← h (conj ρ) c0 c1 c2 c3]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.1 hn).1; omega)
    rw [hcj, neg_sub, Complex.cpow_sub _ _ hn0, Complex.cpow_one]
    field_simp
  -- the real and imaginary parts of `b_n/n`
  set a : ℕ → ℝ := fun n => (b n / n).re with ha
  set c : ℕ → ℝ := fun n => (b n / n).im with hc
  have hsplit : ∀ ρ : ℂ, ∑ n ∈ Icc 1 N, b n / n * (n : ℂ) ^ ρ =
      ∑ n ∈ Icc 1 N, (a n : ℂ) * (n : ℂ) ^ ρ + I * ∑ n ∈ Icc 1 N, (c n : ℂ) * (n : ℂ) ^ ρ := by
    intro ρ
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have e : b n / n = (a n : ℂ) + (c n : ℂ) * I := (Complex.re_add_im _).symm
    rw [e]
    ring
  have hconj_sum : ∀ (y : ℕ → ℝ) (ρ : ℂ), ∑ n ∈ Icc 1 N, (y n : ℂ) * (n : ℂ) ^ conj ρ =
      conj (∑ n ∈ Icc 1 N, (y n : ℂ) * (n : ℂ) ^ ρ) := by
    intro y ρ
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [natCast_cpow_conj, map_mul, Complex.conj_ofReal]
  have hparts : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
      ∑ n ∈ Icc 1 N, (a n : ℂ) * (n : ℂ) ^ ρ = 0 ∧ ∑ n ∈ Icc 1 N, (c n : ℂ) * (n : ℂ) ^ ρ = 0 := by
    intro ρ hρ h0 h1 hT
    obtain ⟨c0, c1, c2, c3⟩ := hzc ρ hρ h0 h1 hT
    have e1 := hx ρ hρ h0 h1 hT
    have e2 := hx (conj ρ) c0 c1 c2 c3
    rw [hsplit] at e1 e2
    rw [hconj_sum a, hconj_sum c] at e2
    set A := ∑ n ∈ Icc 1 N, (a n : ℂ) * (n : ℂ) ^ ρ
    set C := ∑ n ∈ Icc 1 N, (c n : ℂ) * (n : ℂ) ^ ρ
    have e3 : A - I * C = 0 := by
      have := congrArg conj e2
      rw [map_add, map_mul, Complex.conj_conj, Complex.conj_conj, Complex.conj_I, map_zero] at this
      linear_combination this
    have hA : A = 0 := by linear_combination (e1 + e3) / 2
    have hC : C = 0 := by
      have : I * C = 0 := by linear_combination (e1 - e3) / 2
      exact (mul_eq_zero.1 this).resolve_left Complex.I_ne_zero
    exact ⟨hA, hC⟩
  have ha0 := eq_zero_of_silent hRH hN hTN a fun ρ hρ h0 h1 hT => (hparts ρ hρ h0 h1 hT).1
  have hc0 := eq_zero_of_silent hRH hN hTN c fun ρ hρ h0 h1 hT => (hparts ρ hρ h0 h1 hT).2
  intro n hn
  have hq : b n / n = 0 := Complex.ext (by simpa [ha] using ha0 n hn) (by simpa [hc] using hc0 n hn)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.1 hn).1; omega)
  exact (div_eq_zero_iff.1 hq).resolve_right hn0

end BallSilent

#print axioms BallSilent.eq_zero_of_silent
#print axioms BallSilent.dirichlet_eq_zero
