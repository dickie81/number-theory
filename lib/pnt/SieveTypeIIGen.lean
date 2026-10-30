/-
# Parts of the Type II estimate for a curve and a window (Proposition 3′ with parameters)

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The counts of a curve `g` (`CurveCounts g`): for some `C`, at most `C(qT)^{g(σ)}(1 + log qT)^{10}` characters mod `q`
have a zero with `Re s ≥ σ` and `|Im s| ≤ T`, for every `q ≥ 1`, `1/2 ≤ σ ≤ 1` and `T ≥ 2`. This file has that
hypothesis, the count of one bin for `g` and the product of Lemma 1's bounds at `L`; `SieveTypeIIHM.typeII_gen_hm`
states the estimate for a curve on a window, with the Halász–Montgomery branch.

* `CurveCounts`: the hypothesis.
* `card_bin_gen`, `prod_MB_le_gen`: the count of one bin for `g` with `g(1/2) = 1`, and the product of Lemma 1's
  bounds at `L`.

The file imports `SieveTypeII.lean`.
-/
import SieveTypeII

open Complex Finset

noncomputable section

namespace SieveTypeIIGen

open DirMean LinnikHybrid DirichletCharacter SieveTypeII

section Gen

open scoped Classical ContDiff

/-- **The counts of a curve `g`**: there is `C ≥ 0` such that for every `q ≥ 1`, `1/2 ≤ σ ≤ 1` and `T ≥ 2` at most
`C(qT)^{g(σ)}(1 + log qT)^{10}` characters mod `q` have a zero with `Re s ≥ σ` and `|Im s| ≤ T`. -/
def CurveCounts (g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
        C * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10

/-- **The count of a bin of the grid** for a curve `g` with `g(1/2) = 1`: with the counts `C(qT)^{g(σ)}(…)` for the
zeros, every bin `i < N` of a grid with `N > 0`, `β_0 = 1/2` and `1/2 ≤ β_i ≤ 1` holds, for `T ≥ 2`, at most
`max(C, 1)(qT)^{g(β_i)}(1 + log qT)^{10}` characters `χ ≠ 1`. -/
lemma card_bin_gen {g : ℝ → ℝ} (hg0 : g (1 / 2) = 1) {q : ℕ} [NeZero q] {β : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (hβ0 : β 0 = 1 / 2) (hβ : ∀ i < N, 1 / 2 ≤ β i ∧ β i ≤ 1) {T Cd : ℝ} (hT : 2 ≤ T)
    (hCd : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          Cd * ((q : ℝ) * T) ^ g σ * (1 + Real.log ((q : ℝ) * T)) ^ 10) {i : ℕ} (hi : i < N) :
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card : ℝ) ≤
      max Cd 1 * ((q : ℝ) * T) ^ g (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqT : 1 ≤ (q : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ (1 + Real.log ((q : ℝ) * T)) ^ 10 := one_le_pow₀ (by linarith [Real.log_nonneg hqT])
  have hM1 : 1 ≤ max Cd 1 := le_max_right _ _
  have hMC : Cd ≤ max Cd 1 := le_max_left _ _
  have hP : 0 ≤ ((q : ℝ) * T) ^ g (β i) := Real.rpow_nonneg (by linarith) _
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have hc := LinnikDensity.card_chars_le (q := q)
      (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = 0)
    have hg : g (β 0) = 1 := by rw [hβ0, hg0]
    rw [hg, Real.rpow_one]
    calc _ ≤ (q : ℝ) := hc
      _ ≤ 1 * ((q : ℝ) * T) * 1 := by
          rw [one_mul, mul_one]; exact le_mul_of_one_le_right (by linarith) (by linarith)
      _ ≤ max Cd 1 * ((q : ℝ) * T) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hM1 (by linarith)) hl1 (by norm_num)
          exact mul_nonneg (by linarith) (by linarith)
  · have hc1 := card_bin_le (q := q) (β := β) (T := T) hN hpos
    have hc2 := hCd (β i) (hβ i hi).1 (hβ i hi).2
    calc _ ≤ ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
          ∃ s : ℂ, β i ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) := by exact_mod_cast hc1
      _ ≤ Cd * ((q : ℝ) * T) ^ g (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := hc2
      _ ≤ max Cd 1 * ((q : ℝ) * T) ^ g (β i) * (1 + Real.log ((q : ℝ) * T)) ^ 10 := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMC hP) (by linarith)

/-- **The product of Lemma 1's bounds**, at `L`. For `q > 0` and `P > 0`: if each factor's
bound is at most `2Q_j^{θ′}` and nonnegative, `Q_j ≥ 1` and `∏ Q_j ≤ 2^{K₀}q^L/P` with `K ≤ K₀`, then the product is at
most `2^{K₀}·2^{K₀}(q^L/P)^{θ′}` when `0 ≤ θ′ ≤ 1`. -/
lemma prod_MB_le_gen {L : ℝ} {K K₀ : ℕ} {M Q : ℕ → ℝ} {q P θ' : ℝ} (hK : K ≤ K₀) (hq : 0 < q) (hP : 0 < P)
    (hθ0 : 0 ≤ θ') (hθ1 : θ' ≤ 1) (hM0 : ∀ j < K, 0 ≤ M j) (hM : ∀ j < K, M j ≤ 2 * Q j ^ θ')
    (hQ1 : ∀ j < K, 1 ≤ Q j) (hprod : ∏ j ∈ Finset.range K, Q j ≤ 2 ^ K₀ * q ^ L / P) :
    ∏ j ∈ Finset.range K, M j ≤ 2 ^ K₀ * 2 ^ K₀ * (q ^ L / P) ^ θ' := by
  have hQ0 : ∀ j ∈ Finset.range K, 0 ≤ Q j := fun j hj => by linarith [hQ1 j (Finset.mem_range.1 hj)]
  have h2K : (2 : ℝ) ^ K ≤ 2 ^ K₀ := pow_le_pow_right₀ (by norm_num) hK
  have hA : 0 ≤ ∏ j ∈ Finset.range K, Q j := Finset.prod_nonneg hQ0
  have h2K₀ : (1 : ℝ) ≤ 2 ^ K₀ := one_le_pow₀ (by norm_num)
  have hqL : 0 ≤ q ^ L / P := div_nonneg (Real.rpow_nonneg hq.le _) hP.le
  calc ∏ j ∈ Finset.range K, M j ≤ ∏ j ∈ Finset.range K, (2 * Q j ^ θ') :=
        Finset.prod_le_prod₀ (fun j hj => hM0 j (Finset.mem_range.1 hj)) fun j hj => hM j (Finset.mem_range.1 hj)
    _ = 2 ^ K * (∏ j ∈ Finset.range K, Q j) ^ θ' := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Real.finsetProd_rpow _ _ hQ0]
    _ ≤ 2 ^ K₀ * (2 ^ K₀ * q ^ L / P) ^ θ' := by
        apply mul_le_mul h2K (Real.rpow_le_rpow hA hprod hθ0) (Real.rpow_nonneg hA _) (by positivity)
    _ = 2 ^ K₀ * ((2 ^ K₀) ^ θ' * (q ^ L / P) ^ θ') := by
        rw [mul_div_assoc, Real.mul_rpow (by positivity) hqL]
    _ ≤ 2 ^ K₀ * (2 ^ K₀ * (q ^ L / P) ^ θ') := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hqL _)
        calc ((2 : ℝ) ^ K₀) ^ θ' ≤ ((2 : ℝ) ^ K₀) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2K₀ hθ1
          _ = 2 ^ K₀ := Real.rpow_one _
    _ = 2 ^ K₀ * 2 ^ K₀ * (q ^ L / P) ^ θ' := by ring

end Gen

end SieveTypeIIGen

#print axioms SieveTypeIIGen.card_bin_gen
#print axioms SieveTypeIIGen.prod_MB_le_gen
