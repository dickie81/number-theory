import EllipticDivPoly

/-!
# The torsion values of `℘` are integral away from the order

For a period pair with `ι`-integral `g₂`, `g₃` (`ι : ℂ → ℂ_ℓ`, `ℓ ≠ 2`) and a torsion point `q ∉ Λ`, `Nq ∈ Λ`, with
`ℓ ∤ N`, the values `℘(q)` and `℘′(q)` are `ι`-integral (`norm_iota_weierstrassP_le_one`,
`norm_iota_derivWeierstrassP_le_one`). Neither good reduction nor `Δ = 1` enters.

**The division polynomials are integral.** The curve `EllipticDivPoly.curve Λ` is the base change of a curve over the
ring `intSub ι` of `ι`-integral numbers (`curveInt`, using `‖ι 4‖ = 1`), so the coefficients of every `ΨSq_n` are
`ι`-integral (`coeff_ΨSq_mem`, by `WeierstrassCurve.map_ΨSq`).

**A root is integral.** If `p` has `ι`-integral coefficients and an `ι`-unit coefficient in a degree `D ≥ deg p`, every
root `x` of `p` is `ι`-integral: otherwise the term of degree `D` strictly dominates the others in the ultrametric
norm (`norm_le_one_of_eval_eq_zero`). For `p = ΨSq_N`, `D = N² − 1` and the coefficient is `N²`
(`WeierstrassCurve.coeff_ΨSq`), a unit as `ℓ ∤ N`; `℘(q)` is a root by `EllipticDivPoly.eval_ΨSq_eq_zero`. Then
`℘′(q)² = 4℘(q)³ − g₂℘(q) − g₃` is integral.

**Main declarations:** `coeff_ΨSq_mem`, `norm_le_one_of_eval_eq_zero`, `norm_iota_weierstrassP_le_one`,
`norm_iota_derivWeierstrassP_le_one`; the definition `curveInt`.
-/

namespace TorsionInt

noncomputable section

open Polynomial PeriodPair CMThetaOne EllipticDivPoly

section Curve

variable (Λ : PeriodPair) {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The curve over the `ι`-integral numbers** `intSub ι`, with the coefficients of `curve Λ` (for `ι`-integral
`g₂/4`, `g₃/4`). -/
def curveInt (ι : ℂ →+* K) (h2 : ‖ι (Λ.g₂ / 4)‖ ≤ 1) (h3 : ‖ι (Λ.g₃ / 4)‖ ≤ 1) : WeierstrassCurve (intSub ι) :=
  ⟨0, 0, 0, ⟨-Λ.g₂ / 4, by simpa [mem_intSub, neg_div] using h2⟩,
    ⟨-Λ.g₃ / 4, by simpa [mem_intSub, neg_div] using h3⟩⟩

/-- **`curve Λ` is the base change of `curveInt`.** -/
theorem curveInt_map (ι : ℂ →+* K) (h2 : ‖ι (Λ.g₂ / 4)‖ ≤ 1) (h3 : ‖ι (Λ.g₃ / 4)‖ ≤ 1) :
    (curveInt Λ ι h2 h3).map (intSub ι).subtype = curve Λ := by
  simp [curveInt, curve, WeierstrassCurve.map]

/-- **The division polynomials are `ι`-integral** (`map_ΨSq`). -/
theorem coeff_ΨSq_mem (ι : ℂ →+* K) (h2 : ‖ι (Λ.g₂ / 4)‖ ≤ 1) (h3 : ‖ι (Λ.g₃ / 4)‖ ≤ 1) (n : ℤ) (i : ℕ) :
    ((curve Λ).ΨSq n).coeff i ∈ intSub ι := by
  rw [← curveInt_map Λ ι h2 h3, WeierstrassCurve.map_ΨSq, coeff_map]
  exact (((curveInt Λ ι h2 h3).ΨSq n).coeff i).2

/-- **A root of an `ι`-integral polynomial with an `ι`-unit coefficient in a degree `D ≥ natDegree` is
`ι`-integral** (if `‖ι x‖ > 1`, the term of degree `D` dominates; the generalisation of `norm_le_one_of_monic`). -/
theorem norm_le_one_of_eval_eq_zero (ι : ℂ →+* K) {p : ℂ[X]} {D : ℕ} (hD : p.natDegree ≤ D)
    (hlead : ‖ι (p.coeff D)‖ = 1) (hc : ∀ i, p.coeff i ∈ intSub ι) {x : ℂ} (hx : p.eval x = 0) :
    ‖ι x‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hs := eval_eq_sum_range' (Nat.lt_succ_of_le hD) x
  rw [hx, Finset.sum_range_succ] at hs
  have h := congrArg ι hs
  rw [map_zero, map_add, map_sum] at h
  have e : ι (p.coeff D * x ^ D) = -∑ i ∈ Finset.range D, ι (p.coeff i * x ^ i) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)
  have heq : ‖ι x‖ ^ D = ‖∑ i ∈ Finset.range D, ι (p.coeff i * x ^ i)‖ := by
    rw [← norm_neg (∑ i ∈ Finset.range D, ι (p.coeff i * x ^ i)), ← e, map_mul, norm_mul, hlead, one_mul, map_pow,
      norm_pow]
  rcases D with _ | D
  · simp at heq
  · have hb : ‖∑ i ∈ Finset.range (D + 1), ι (p.coeff i * x ^ i)‖ ≤ ‖ι x‖ ^ D := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
      rw [map_mul, map_pow, norm_mul, norm_pow]
      have hi' : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc ‖ι (p.coeff i)‖ * ‖ι x‖ ^ i ≤ 1 * ‖ι x‖ ^ D :=
            mul_le_mul (hc i) (pow_le_pow_right₀ hlt.le hi') (by positivity) zero_le_one
        _ = ‖ι x‖ ^ D := one_mul _
    have := pow_lt_pow_right₀ hlt (Nat.lt_add_one D)
    linarith

end Curve

section Torsion

variable (Λ : PeriodPair) {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`‖ι 4‖ = 1`** for `ℓ ≠ 2`. -/
theorem norm_iota_four (hℓ2 : ℓ ≠ 2) (ι : ℂ →+* ℂ_[ℓ]) : ‖ι 4‖ = 1 := by
  rw [show (4 : ℂ) = ((2 ^ 2 : ℕ) : ℂ) by norm_num, map_natCast]
  exact norm_natCast_padicComplex (Nat.Coprime.pow_right 2 ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hℓ2))

/-- **Torsion values of `℘` are integral away from the order**: for `ι`-integral `g₂`, `g₃`, `ℓ ≠ 2`, `q ∉ Λ`,
`Nq ∈ Λ` and `ℓ ∤ N`, `‖ι ℘(q)‖ ≤ 1` (`℘(q)` is a root of `ΨSq_N`, whose coefficients are integral and whose
coefficient of degree `N² − 1` is the unit `N²`). -/
theorem norm_iota_weierstrassP_le_one (hℓ2 : ℓ ≠ 2) (ι : ℂ →+* ℂ_[ℓ]) (h2 : ‖ι Λ.g₂‖ ≤ 1) (h3 : ‖ι Λ.g₃‖ ≤ 1)
    {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ} (hNℓ : ¬ ℓ ∣ N) (hN : (N : ℂ) * q ∈ Λ.lattice) : ‖ι (℘[Λ] q)‖ ≤ 1 := by
  have h4 := norm_iota_four hℓ2 ι
  have h2' : ‖ι (Λ.g₂ / 4)‖ ≤ 1 := by rw [map_div₀, norm_div, h4, div_one]; exact h2
  have h3' : ‖ι (Λ.g₃ / 4)‖ ≤ 1 := by rw [map_div₀, norm_div, h4, div_one]; exact h3
  have hNn : ‖(N : ℂ_[ℓ])‖ = 1 := norm_natCast_padicComplex ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hNℓ)
  refine norm_le_one_of_eval_eq_zero ι (p := (curve Λ).ΨSq N) (D := N ^ 2 - 1) ?_ ?_ (coeff_ΨSq_mem Λ ι h2' h3' N)
    (eval_ΨSq_eq_zero Λ hq hN)
  · simpa using (curve Λ).natDegree_ΨSq_le N
  · have h := (curve Λ).coeff_ΨSq N
    rw [Int.natAbs_natCast] at h
    rw [h, Int.cast_natCast, map_pow, map_natCast, norm_pow, hNn, one_pow]

/-- **Torsion values of `℘′` are integral away from the order** (`℘′(q)² = 4℘(q)³ − g₂℘(q) − g₃`). -/
theorem norm_iota_derivWeierstrassP_le_one (hℓ2 : ℓ ≠ 2) (ι : ℂ →+* ℂ_[ℓ]) (h2 : ‖ι Λ.g₂‖ ≤ 1)
    (h3 : ‖ι Λ.g₃‖ ≤ 1) {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ} (hNℓ : ¬ ℓ ∣ N) (hN : (N : ℂ) * q ∈ Λ.lattice) :
    ‖ι (℘'[Λ] q)‖ ≤ 1 := by
  have hp := norm_iota_weierstrassP_le_one Λ hℓ2 ι h2 h3 hq hNℓ hN
  have h4 : (4 : ℂ) ∈ intSub ι := mem_intSub.mpr (norm_iota_four hℓ2 ι).le
  have h : ‖ι (℘'[Λ] q)‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, ← map_pow, ← mem_intSub, Λ.derivWeierstrassP_sq q hq]
    exact sub_mem (sub_mem (mul_mem h4 (pow_mem hp 3)) (mul_mem h2 hp)) h3
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

end Torsion

end

end TorsionInt
