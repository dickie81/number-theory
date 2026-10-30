/-
# Linnik's theorem with exponent `2.3334 + ε` from the curve `g7d`, by the classical deduction

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements.

* `charDensity_g7d`: there is `C ≥ 0` with `Linnik.CharDensity (11667/5000) 10 C`: for every `q ≥ 1`, `1/2 ≤ σ ≤ 1`
  and `T ≥ 2` at most `C(qT)^{(11667/5000)(1−σ)}(log qT)^{10}` characters mod `q` have a zero of `L(·, χ)` in
  `Re s ≥ σ`, `|Im s| ≤ T`. It is `SieveCurve7D.counts_7d` with `g7d σ ≤ (11667/5000)(1 − σ)`
  (`SieveCurve7D.g7d_le_lin`) and `1 + log qT ≤ 3 log qT` for `qT ≥ 2`.
* `linnik_g7d`: for every `η > 0` there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
  `p ≡ a (mod q)` with `p ≤ K q^{11667/5000 + η}`: `Linnik.linnik_of_charDensity` at `charDensity_g7d`.

The exponent `11667/5000 = 2.3334` is the curve's largest, that of the first Chen–Gupta–Li step; the Linnik paper's
Section 8 sets this deduction beside the sieve's `278/125`. No hypothesis.

The file imports `SieveCurve7D.lean` and `LinnikDeduction.lean`.
-/
import SieveCurve7D
import LinnikDeduction

open Real

namespace LinnikG7

/-- **The density estimate of the curve `g7d`** in the form of the classical deduction: `CharDensity (11667/5000) 10 C`,
with no hypothesis. -/
theorem charDensity_g7d : ∃ C : ℝ, 0 ≤ C ∧ Linnik.CharDensity (11667 / 5000) 10 C := by
  obtain ⟨C, hC0, hC⟩ := SieveCurve7D.counts_7d
  refine ⟨3 ^ 10 * C, by positivity, fun q _ σ T hσ hσ1 hT => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : (2 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * T := by linarith
  have hl2 : (1 / 2 : ℝ) ≤ Real.log ((q : ℝ) * T) := by
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    exact h2.trans (Real.log_le_log (by norm_num) hqT)
  have h1 := hC q σ T hσ hσ1 hT
  have hexp : ((q : ℝ) * T) ^ SieveCurve7D.g7d σ ≤ ((q : ℝ) * T) ^ ((11667 / 5000) * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hqT1 (SieveCurve7D.g7d_le_lin hσ1)
  have hlog : (1 + Real.log ((q : ℝ) * T)) ^ 10 ≤ 3 ^ 10 * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 10
  calc _ ≤ C * ((q : ℝ) * T) ^ SieveCurve7D.g7d σ * (1 + Real.log ((q : ℝ) * T)) ^ 10 := h1
    _ ≤ C * ((q : ℝ) * T) ^ ((11667 / 5000) * (1 - σ)) * (3 ^ 10 * Real.log ((q : ℝ) * T) ^ (10 : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp hC0) hlog (by positivity) (mul_nonneg hC0 (by positivity))
    _ = 3 ^ 10 * C * ((q : ℝ) * T) ^ ((11667 / 5000) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ) := by ring

/-- **Linnik's theorem with exponent `11667/5000 + η`**, from the curve `g7d` by the classical deduction, with no
hypothesis: for every `η > 0` there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K q^{11667/5000 + η}`. -/
theorem linnik_g7d {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (11667 / 5000 + η) := by
  obtain ⟨C, hC0, hD⟩ := charDensity_g7d
  exact Linnik.linnik_of_charDensity (by norm_num) (by norm_num) hC0 hD hη

end LinnikG7

#print axioms LinnikG7.charDensity_g7d
#print axioms LinnikG7.linnik_g7d
