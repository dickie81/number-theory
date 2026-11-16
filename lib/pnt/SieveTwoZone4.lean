/-
# One bin in two variables with the fourth moment, as powers of `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoZone` turns the bound of a bin for two variables into a power of `q`, with an exponent `M` for each mean
square by orthogonality or by the Halász–Montgomery inequality (`SqExp`). This file adds the third bound of
`SieveTwoFourth`, `cnt^{1/2}((3P² + q)F)^{1/2}V`, for which `M` is an exponent as soon as
`M ≥ m` and `M ≥ g/2 + max(m, 1/2) + 2e`: the bin's count enters as `q^{g/2}`, the fourth moment as
`q^{max(m, 1/2)}`, and the divisor bound `F ≤ C_F q^{2e}` as `q^e`.

* `SqExp4 d e g m M`: `M` is an exponent by one of the three bounds.
* `twoBound4 L d e g β m₁ m₂ w`: `SieveTwoZone.twoBound` with `SqExp4`.
* `sqTerm4_le_pow`: `sqTerm4 cnt P q V B F ≤ (e(2 + 12C_dC_K) + (12C_dC_F)^{1/2})(1 + log qT)^{10} q^{M + η}V`.
* `bin_bound_two4`, **one bin in two variables with the fourth moment**: `SieveTwoZone.bin_bound_two` under
  `twoBound4`, with that constant.

The file imports `SieveTwoZone.lean` and `SieveTwoFourth.lean`.
-/
import SieveTwoZone
import SieveTwoFourth

open Real

noncomputable section

namespace SieveTypeIIHM

/-- `M` is an exponent for the mean square of a polynomial of length `q^m` over a bin with about `q^g` characters by
one of three bounds: `SqExp`'s two (orthogonality, Halász–Montgomery), or the fourth moment's (`M ≥ m` and
`M ≥ g/2 + max(m, 1/2) + 2e`). -/
def SqExp4 (d e g m M : ℝ) : Prop :=
  SqExp d e g m M ∨ (m ≤ M ∧ g / 2 + max m (1 / 2) + 2 * e ≤ M)

/-- The exponent bound of the estimate in two variables at `(β, m₁, m₂, w)` with the three bounds: exponents `M₁` and
`M₂` (`SqExp4`) with `(L − m₁ − m₂)(β + w) + (m₁ + M₁)/2 + (m₂ + M₂)/2 ≤ L − 1/25000`. -/
def twoBound4 (L d e g β m₁ m₂ w : ℝ) : Prop :=
  ∃ M₁ M₂ : ℝ, SqExp4 d e g m₁ M₁ ∧ SqExp4 d e g m₂ M₂ ∧
    (L - m₁ - m₂) * (β + w) + (m₁ + M₁) / 2 + (m₂ + M₂) / 2 ≤ L - 1 / 25000

/-- **The mean square over a bin as a power of `q`, with the fourth moment.** As `SieveTwoZone.sqTerm_le_pow`, for
`sqTerm4` and an exponent `M` by one of the three bounds (`SqExp4`), given `0 ≤ F ≤ C_F q^{2e}`:
`sqTerm4 cnt P q V B F ≤ (e(2 + 12C_dC_K) + (12C_dC_F)^{1/2})(1 + log qT)^{10} q^{M + η}V`. -/
lemma sqTerm4_le_pow {d e : ℝ} (he : e ≤ 3 / 4) (he0 : 0 ≤ e) {q P m M T η g cnt V Cd CK CF B F : ℝ} (hq : 1 < q)
    (hPm : P = q ^ m) (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hη : 0 ≤ η) (hg1 : g ≤ 1) (hM : SqExp4 d e g m M)
    (hCd : 0 ≤ Cd) (hCK : 0 ≤ CK) (hCF : 0 ≤ CF) (hV : 0 ≤ V)
    (hcnt : cnt ≤ Cd * (q * T) ^ g * (1 + Real.log (q * T)) ^ 10)
    (hB : B ≤ CK * (2 * P) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB0 : 0 ≤ B)
    (hF0 : 0 ≤ F) (hF : F ≤ CF * q ^ (2 * e)) :
    sqTerm4 cnt P q V B F ≤
      (Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF)) * (1 + Real.log (q * T)) ^ 10 *
        q ^ (M + η) * V := by
  have hq0 : 0 < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have hqM0 : 0 ≤ q ^ (M + η) := by positivity
  have hs0 : 0 ≤ Real.sqrt (12 * Cd * CF) := Real.sqrt_nonneg _
  have hK0 : 0 ≤ Real.exp 1 * (2 + 12 * Cd * CK) := by positivity
  rcases hM with h2 | ⟨hmM, hgM⟩
  · -- orthogonality or Halász–Montgomery: `SieveTwoZone.sqTerm_le_pow`
    have h := sqTerm_le_pow he hq hPm hT1 hT hη hg1 h2 hCd hCK hV hcnt hB hB0
    calc sqTerm4 cnt P q V B F ≤ sqTerm cnt P q V B := min_le_left _ _
      _ ≤ Real.exp 1 * (2 + 12 * Cd * CK) * (1 + Real.log (q * T)) ^ 10 * q ^ (M + η) * V := h
      _ ≤ (Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF)) * (1 + Real.log (q * T)) ^ 10 *
            q ^ (M + η) * V := by
          gcongr
          linarith
  · -- the fourth moment: `cnt^{1/2} ≤ (3C_d)^{1/2}q^{(g+η)/2}ℓ^5` and `((3P² + q)F)^{1/2} ≤ 2C_F^{1/2}q^{max(m,1/2)+e}`
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log (q * T) := ⟨_, rfl⟩
    rw [← hℓ] at hcnt ⊢
    have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
    have hℓ0 : 0 ≤ ℓ := by linarith
    set x := max m (1 / 2) with hx
    have hgT : (q * T) ^ g ≤ 3 * q ^ (g + η) := by
      have hTg : T ^ g ≤ 3 * q ^ η :=
        ((Real.rpow_le_rpow_of_exponent_le hT1 hg1).trans (Real.rpow_one T).le).trans hT
      rw [Real.mul_rpow hq0.le hT0.le, Real.rpow_add hq0]
      calc q ^ g * T ^ g ≤ q ^ g * (3 * q ^ η) := mul_le_mul_of_nonneg_left hTg (by positivity)
        _ = 3 * (q ^ g * q ^ η) := by ring
    have hc : cnt ≤ 3 * Cd * q ^ (g + η) * ℓ ^ 10 := by
      calc cnt ≤ Cd * (q * T) ^ g * ℓ ^ 10 := hcnt
        _ ≤ Cd * (3 * q ^ (g + η)) * ℓ ^ 10 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgT hCd) (by positivity)
        _ = 3 * Cd * q ^ (g + η) * ℓ ^ 10 := by ring
    have hsc : Real.sqrt cnt ≤ Real.sqrt (3 * Cd) * q ^ ((g + η) / 2) * ℓ ^ 5 := by
      calc Real.sqrt cnt ≤ Real.sqrt (3 * Cd * q ^ (g + η) * ℓ ^ 10) := Real.sqrt_le_sqrt hc
        _ = Real.sqrt (3 * Cd) * q ^ ((g + η) / 2) * ℓ ^ 5 := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
              Real.sqrt_eq_rpow (q ^ (g + η)), ← Real.rpow_mul hq0.le,
              show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
            ring_nf
    have hP2 : 3 * P ^ 2 + q ≤ 4 * q ^ (2 * x) := by
      have hPx : P ^ 2 ≤ q ^ (2 * x) := by
        rw [hPm, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by push_cast; have := le_max_left m (1 / 2); linarith)
      have hqx : q ≤ q ^ (2 * x) := by
        calc q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
          _ ≤ q ^ (2 * x) := Real.rpow_le_rpow_of_exponent_le hq.le
              (by have := le_max_right m (1 / 2); linarith)
      linarith
    have hsF : Real.sqrt ((3 * P ^ 2 + q) * F) ≤ 2 * Real.sqrt CF * q ^ (x + e) := by
      have hPF : (3 * P ^ 2 + q) * F ≤ 4 * q ^ (2 * x) * (CF * q ^ (2 * e)) :=
        mul_le_mul hP2 hF hF0 (by positivity)
      calc Real.sqrt ((3 * P ^ 2 + q) * F) ≤ Real.sqrt (4 * q ^ (2 * x) * (CF * q ^ (2 * e))) :=
            Real.sqrt_le_sqrt hPF
        _ = Real.sqrt (4 * CF * (q ^ (x + e)) ^ 2) := by
            have hsqx : (q ^ (x + e)) ^ 2 = q ^ (2 * x) * q ^ (2 * e) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
              congr 1; push_cast; ring
            rw [hsqx]
            congr 1
            ring
        _ = 2 * Real.sqrt CF * q ^ (x + e) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul (by norm_num),
              show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have hexp : q ^ ((g + η) / 2) * q ^ (x + e) ≤ q ^ (M + η) := by
      rw [← Real.rpow_add hq0]
      exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
    have h12 : Real.sqrt (12 * Cd * CF) = Real.sqrt (3 * Cd) * (2 * Real.sqrt CF) := by
      have h4 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [show (12 : ℝ) * Cd * CF = (3 * Cd) * (4 * CF) by ring,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3 * Cd), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
    have hℓ5 : ℓ ^ 5 ≤ ℓ ^ 10 := pow_le_pow_right₀ hℓ1 (by norm_num)
    calc sqTerm4 cnt P q V B F ≤ Real.sqrt cnt * Real.sqrt ((3 * P ^ 2 + q) * F) * V := min_le_right _ _
      _ ≤ (Real.sqrt (3 * Cd) * q ^ ((g + η) / 2) * ℓ ^ 5) * (2 * Real.sqrt CF * q ^ (x + e)) * V := by
          gcongr
      _ = Real.sqrt (3 * Cd) * (2 * Real.sqrt CF) * ℓ ^ 5 * (q ^ ((g + η) / 2) * q ^ (x + e)) * V := by ring
      _ ≤ Real.sqrt (12 * Cd * CF) * ℓ ^ 10 * q ^ (M + η) * V := by
          rw [h12]
          gcongr
      _ ≤ (Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF)) * ℓ ^ 10 * q ^ (M + η) * V := by
          gcongr
          linarith

/-- The square root of `sqTerm4_le_pow`, with `V^{1/2} = (V/P)^{1/2} q^{m/2}`. -/
lemma sqrt_sqTerm4_le {d e : ℝ} (he : e ≤ 3 / 4) (he0 : 0 ≤ e) {q P m M T η g cnt V Cd CK CF B F : ℝ} (hq : 1 < q)
    (hPm : P = q ^ m) (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hη : 0 ≤ η) (hg1 : g ≤ 1) (hM : SqExp4 d e g m M)
    (hCd : 0 ≤ Cd) (hCK : 0 ≤ CK) (hCF : 0 ≤ CF) (hV : 0 ≤ V)
    (hcnt : cnt ≤ Cd * (q * T) ^ g * (1 + Real.log (q * T)) ^ 10)
    (hB : B ≤ CK * (2 * P) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB0 : 0 ≤ B)
    (hF0 : 0 ≤ F) (hF : F ≤ CF * q ^ (2 * e)) :
    Real.sqrt (sqTerm4 cnt P q V B F) ≤
      Real.sqrt (Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF)) * (1 + Real.log (q * T)) ^ 5 *
        q ^ ((m + M + η) / 2) * Real.sqrt (V / P) := by
  have hq0 : 0 < q := by linarith
  have hP0 : 0 < P := by rw [hPm]; positivity
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have h := sqTerm4_le_pow he he0 hq hPm hT1 hT hη hg1 hM hCd hCK hCF hV hcnt hB hB0 hF0 hF
  have hsq : ∀ x : ℝ, Real.sqrt (q ^ x) = q ^ (x / 2) := fun x => by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]; congr 1; ring
  have e10 : Real.sqrt ((1 + Real.log (q * T)) ^ 10) = (1 + Real.log (q * T)) ^ 5 := by
    rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
  have hVP : Real.sqrt V = Real.sqrt (V / P) * q ^ (m / 2) := by
    rw [← hsq, ← hPm, ← Real.sqrt_mul' _ hP0.le, div_mul_cancel₀ V hP0.ne']
  have hK0 : 0 ≤ Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF) := by positivity
  calc Real.sqrt (sqTerm4 cnt P q V B F)
      ≤ Real.sqrt ((Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF)) * (1 + Real.log (q * T)) ^ 10 *
          q ^ (M + η) * V) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF)) * (1 + Real.log (q * T)) ^ 5 *
          q ^ ((M + η) / 2) * Real.sqrt V := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hK0, e10, hsq]
    _ = Real.sqrt (Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF)) * (1 + Real.log (q * T)) ^ 5 *
          q ^ ((m + M + η) / 2) * Real.sqrt (V / P) := by
        rw [hVP, show (m + M + η) / 2 = (M + η) / 2 + m / 2 by ring, Real.rpow_add hq0]
        ring

/-- **One bin in two variables with the fourth moment, as a power of `q`**: `SieveTwoZone.bin_bound_two` for
`sqTerm4`, under `twoBound4`, given `0 ≤ F_i ≤ C_F q^{2e}`, with the constant `e(2 + 12C_dC_K) + (12C_dC_F)^{1/2}`. -/
theorem bin_bound_two4 {L d e : ℝ} (he : e ≤ 3 / 4) (he0 : 0 ≤ e)
    {q T η β w g Mp cnt C₀ Cd CK CF P₁ P₂ m₁ m₂ V₁ V₂ B₁ B₂ F₁ F₂ : ℝ} (hq : 1 < q) (hP₁ : P₁ = q ^ m₁)
    (hP₂ : P₂ = q ^ m₂) (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hη : 0 ≤ η) (hg1 : g ≤ 1)
    (hzone : twoBound4 L d e g β m₁ m₂ w) (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd) (hCK : 0 ≤ CK) (hCF : 0 ≤ CF)
    (hMp : Mp ≤ C₀ * (q ^ L / (P₁ * P₂)) ^ (β + w))
    (hcnt : cnt ≤ Cd * (q * T) ^ g * (1 + Real.log (q * T)) ^ 10)
    (hB₁ : B₁ ≤ CK * (2 * P₁) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB₁0 : 0 ≤ B₁)
    (hB₂ : B₂ ≤ CK * (2 * P₂) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB₂0 : 0 ≤ B₂)
    (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂) (hF₁0 : 0 ≤ F₁) (hF₁ : F₁ ≤ CF * q ^ (2 * e)) (hF₂0 : 0 ≤ F₂)
    (hF₂ : F₂ ≤ CF * q ^ (2 * e)) :
    Mp * (Real.sqrt (sqTerm4 cnt P₁ q V₁ B₁ F₁) * Real.sqrt (sqTerm4 cnt P₂ q V₂ B₂ F₂)) ≤
      C₀ * (Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF)) * (1 + Real.log (q * T)) ^ 10 *
        q ^ (L - 1 / 25000 + η) * (Real.sqrt (V₁ / P₁) * Real.sqrt (V₂ / P₂)) := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hexp⟩ := hzone
  have hq0 : 0 < q := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have hK0 : 0 ≤ Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF) := by positivity
  have h1 := sqrt_sqTerm4_le he he0 hq hP₁ hT1 hT hη hg1 hM₁ hCd hCK hCF hV₁ hcnt hB₁ hB₁0 hF₁0 hF₁
  have h2 := sqrt_sqTerm4_le he he0 hq hP₂ hT1 hT hη hg1 hM₂ hCd hCK hCF hV₂ hcnt hB₂ hB₂0 hF₂0 hF₂
  have hMq : Mp ≤ C₀ * q ^ ((L - m₁ - m₂) * (β + w)) := by
    have e : q ^ L / (P₁ * P₂) = q ^ (L - m₁ - m₂) := by
      rw [hP₁, hP₂, ← Real.rpow_add hq0, ← Real.rpow_sub hq0]; congr 1; ring
    rw [e, ← Real.rpow_mul hq0.le] at hMp
    exact hMp
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log (q * T) := ⟨_, rfl⟩
  rw [← hℓ] at h1 h2 ⊢
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.exp 1 * (2 + 12 * Cd * CK) + Real.sqrt (12 * Cd * CF) := ⟨_, rfl⟩
  rw [← hK] at h1 h2 hK0 ⊢
  have hKK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK0
  have hx : q ^ ((L - m₁ - m₂) * (β + w)) * (q ^ ((m₁ + M₁ + η) / 2) * q ^ ((m₂ + M₂ + η) / 2)) ≤
      q ^ (L - 1 / 25000 + η) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
  have hs1 : 0 ≤ Real.sqrt (V₁ / P₁) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (V₂ / P₂) := Real.sqrt_nonneg _
  calc Mp * (Real.sqrt (sqTerm4 cnt P₁ q V₁ B₁ F₁) * Real.sqrt (sqTerm4 cnt P₂ q V₂ B₂ F₂))
      ≤ (C₀ * q ^ ((L - m₁ - m₂) * (β + w))) *
          ((Real.sqrt K * ℓ ^ 5 * q ^ ((m₁ + M₁ + η) / 2) * Real.sqrt (V₁ / P₁)) *
            (Real.sqrt K * ℓ ^ 5 * q ^ ((m₂ + M₂ + η) / 2) * Real.sqrt (V₂ / P₂))) :=
        mul_le_mul hMq (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
    _ = C₀ * (Real.sqrt K * Real.sqrt K) * ℓ ^ 10 *
          (q ^ ((L - m₁ - m₂) * (β + w)) * (q ^ ((m₁ + M₁ + η) / 2) * q ^ ((m₂ + M₂ + η) / 2))) *
          (Real.sqrt (V₁ / P₁) * Real.sqrt (V₂ / P₂)) := by ring
    _ ≤ C₀ * K * ℓ ^ 10 * q ^ (L - 1 / 25000 + η) * (Real.sqrt (V₁ / P₁) * Real.sqrt (V₂ / P₂)) := by
        rw [hKK]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity)) (mul_nonneg hs1 hs2)

end SieveTypeIIHM

#print axioms SieveTypeIIHM.sqTerm4_le_pow
#print axioms SieveTypeIIHM.bin_bound_two4
