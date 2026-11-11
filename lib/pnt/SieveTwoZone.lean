/-
# One bin in two variables, as powers of `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTypeIIHM.bin_bound_gen_hm` turns the bound of a bin for one polynomial into a power of `q`, under the window's
inequalities. This file does the same for `SieveTwoBins.sum_bin_two`, the bound of a bin for two polynomials. For a
polynomial of length `P = q^m` and a bin with at most `C_d(qT)^{g}(1 + log qT)^{10}` characters, the mean square
`sqTerm` is at most a constant times `(1 + log qT)^{10} q^{M + η}Σ|a|²` for every `M` that is an exponent for it:

* by orthogonality, `M ≥ max(m, 1)`;
* by the Halász–Montgomery inequality, `M ≥ max(m, g + b)`, with `b = 5/12 + m/12 + d(1 − m) + 2e` the exponent of
  the kernel bound `C_K(2P)^{1/12−d}(2q)^{5/12+d+2e}`.

So the bin's contribution, `Mp` times the two square roots, with `Mp ≤ C₀(q^L/(P₁P₂))^{β+w}` the bound for the third
factor, is at most a constant times `(1 + log qT)^{10} q^{E + η}(Σ|a|²/P₁)^{1/2}(Σ|b|²/P₂)^{1/2}` with
`E = (L − m₁ − m₂)(β + w) + (m₁ + M₁)/2 + (m₂ + M₂)/2`. No `g/2` enters, as it does in the window's exponents: the
number of characters of the bin is felt only through the Halász–Montgomery exponent.

* `SqExp d e g m M`: `M` is an exponent for the mean square, by one of the two bounds.
* `twoBound L d e g β m₁ m₂ w`: there are exponents `M₁`, `M₂` with `E ≤ L − 1/25000`.
* `sqTerm_le_pow`: `sqTerm cnt P q V B ≤ e(2 + 12C_dC_K)(1 + log qT)^{10} q^{M + η}V`.
* `sqrt_sqTerm_le`: its square root, `(e(2 + 12C_dC_K))^{1/2}(1 + log qT)^5 q^{(m + M + η)/2}(V/P)^{1/2}`.
* `bin_bound_two`, **one bin in two variables**: under `twoBound`,
  `Mp·(sqTerm cnt P₁ q V₁ B₁)^{1/2}(sqTerm cnt P₂ q V₂ B₂)^{1/2} ≤
  C₀e(2 + 12C_dC_K)(1 + log qT)^{10} q^{L − 1/25000 + η}(V₁/P₁)^{1/2}(V₂/P₂)^{1/2}`.
* `twoBound_of_long`, **two variables of length at least `q`**: if `m₁, m₂ ≥ 1` and `m₁ + m₂ + 1/2000 ≤ L`, then
  `twoBound` holds at every `β ≤ 11/12` and `w ≤ 4·10⁻⁶`, for every value of the curve. Here orthogonality loses
  nothing in either variable, and the third factor, of length at least `q^{1/2000}`, saves `(L − m₁ − m₂)(1 − β − w)`.
  In exponents of `x = q^L` this is two variables in `[1/L, 1 − 1/L]` and a rest: it needs no density estimate, and
  it does not close at `L = 13/6`, where the window does.

The file imports `SieveTwoBins.lean`.
-/
import SieveTwoBins

namespace SieveTypeIIHM

/-- `M` is an exponent for the mean square of a polynomial of length `q^m` over a bin with about `q^g` characters:
by orthogonality (`M ≥ 1` and `M ≥ m`), or by the Halász–Montgomery inequality (`M ≥ m` and
`M ≥ g + 5/12 + m/12 + d(1 − m) + 2e`, the bin's count times the kernel bound). -/
def SqExp (d e g m M : ℝ) : Prop :=
  (1 ≤ M ∧ m ≤ M) ∨ (m ≤ M ∧ g + (5 / 12 + m / 12 + d * (1 - m) + 2 * e) ≤ M)

/-- The exponent bound of the estimate in two variables at `(β, m₁, m₂, w)`, for a curve value `g`: exponents `M₁`
and `M₂` for the two mean squares with `(L − m₁ − m₂)(β + w) + (m₁ + M₁)/2 + (m₂ + M₂)/2 ≤ L − 1/25000`. -/
def twoBound (L d e g β m₁ m₂ w : ℝ) : Prop :=
  ∃ M₁ M₂ : ℝ, SqExp d e g m₁ M₁ ∧ SqExp d e g m₂ M₂ ∧
    (L - m₁ - m₂) * (β + w) + (m₁ + M₁) / 2 + (m₂ + M₂) / 2 ≤ L - 1 / 25000

/-- **The mean square over a bin as a power of `q`.** For `q > 1`, `P = q^m`, `1 ≤ T ≤ 3q^η`, `η ≥ 0`, `g ≤ 1`,
`e ≤ 3/4`, `cnt ≤ C_d(qT)^g(1 + log qT)^{10}`, `0 ≤ B ≤ C_K(2P)^{1/12−d}(2q)^{5/12+d+2e}`, `V ≥ 0` and an
exponent `M` (`SqExp`): `sqTerm cnt P q V B ≤ e(2 + 12C_dC_K)(1 + log qT)^{10} q^{M + η}V`. -/
lemma sqTerm_le_pow {d e : ℝ} (he : e ≤ 3 / 4) {q P m M T η g cnt V Cd CK B : ℝ} (hq : 1 < q) (hPm : P = q ^ m)
    (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hη : 0 ≤ η) (hg1 : g ≤ 1) (hM : SqExp d e g m M)
    (hCd : 0 ≤ Cd) (hCK : 0 ≤ CK) (hV : 0 ≤ V)
    (hcnt : cnt ≤ Cd * (q * T) ^ g * (1 + Real.log (q * T)) ^ 10)
    (hB : B ≤ CK * (2 * P) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB0 : 0 ≤ B) :
    sqTerm cnt P q V B ≤
      Real.exp 1 * (2 + 12 * Cd * CK) * (1 + Real.log (q * T)) ^ 10 * q ^ (M + η) * V := by
  have hq0 : 0 < q := by linarith
  have hP0 : 0 < P := by rw [hPm]; positivity
  have hT0 : 0 < T := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log (q * T) := ⟨_, rfl⟩
  rw [← hℓ] at hcnt ⊢
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hℓ10 : 1 ≤ ℓ ^ 10 := one_le_pow₀ hℓ1
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hCC : 0 ≤ 12 * Cd * CK := by positivity
  have hqη : q ^ M ≤ q ^ (M + η) := Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
  have hqM0 : 0 ≤ q ^ (M + η) := by positivity
  rcases hM with ⟨h1M, hmM⟩ | ⟨hmM, hbM⟩
  · -- orthogonality: `P + q ≤ 2q^M`
    have hP : P ≤ q ^ M := by rw [hPm]; exact Real.rpow_le_rpow_of_exponent_le hq.le hmM
    have hq1 : q ≤ q ^ M := by
      calc q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
        _ ≤ q ^ M := Real.rpow_le_rpow_of_exponent_le hq.le h1M
    have h2 : (2 : ℝ) ≤ Real.exp 1 * (2 + 12 * Cd * CK) * ℓ ^ 10 := by
      have h2' : (1 : ℝ) * 2 * 1 ≤ Real.exp 1 * (2 + 12 * Cd * CK) * ℓ ^ 10 :=
        mul_le_mul (mul_le_mul he1 (by linarith) (by norm_num) (by positivity)) hℓ10 (by norm_num)
          (by positivity)
      linarith
    calc sqTerm cnt P q V B ≤ (P + q) * V := min_le_left _ _
      _ ≤ (2 * q ^ (M + η)) * V := mul_le_mul_of_nonneg_right (by linarith) hV
      _ ≤ (Real.exp 1 * (2 + 12 * Cd * CK) * ℓ ^ 10 * q ^ (M + η)) * V :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hqM0) hV
  · -- Halász–Montgomery: `2P + cnt·B ≤ (2 + 12C_dC_K)ℓ^{10}q^{M+η}`
    have hgT : (q * T) ^ g ≤ 3 * q ^ (g + η) := by
      have hTg : T ^ g ≤ 3 * q ^ η :=
        ((Real.rpow_le_rpow_of_exponent_le hT1 hg1).trans (Real.rpow_one T).le).trans hT
      rw [Real.mul_rpow hq0.le hT0.le, Real.rpow_add hq0]
      calc q ^ g * T ^ g ≤ q ^ g * (3 * q ^ η) := mul_le_mul_of_nonneg_left hTg (by positivity)
        _ = 3 * (q ^ g * q ^ η) := by ring
    have hc : cnt ≤ Cd * 3 * q ^ (g + η) * ℓ ^ 10 := by
      calc cnt ≤ Cd * (q * T) ^ g * ℓ ^ 10 := hcnt
        _ ≤ Cd * (3 * q ^ (g + η)) * ℓ ^ 10 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgT hCd) (by positivity)
        _ = Cd * 3 * q ^ (g + η) * ℓ ^ 10 := by ring
    have hB' : B ≤ CK * 4 * q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) := by
      have h22 : (2 : ℝ) ^ (1 / 12 - d) * 2 ^ (5 / 12 + d + 2 * e) ≤ 4 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        calc (2 : ℝ) ^ (1 / 12 - d + (5 / 12 + d + 2 * e)) ≤ 2 ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by rw [Real.rpow_two]; norm_num
      calc B ≤ CK * (2 * P) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e) := hB
        _ = CK * (2 ^ (1 / 12 - d) * 2 ^ (5 / 12 + d + 2 * e)) *
              q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) := by
            rw [Real.mul_rpow (by norm_num) hP0.le, Real.mul_rpow (by norm_num) hq0.le, hPm,
              ← Real.rpow_mul hq0.le, Real.rpow_add hq0 (m * (1 / 12 - d))]
            ring
        _ ≤ CK * 4 * q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h22 hCK) (by positivity)
    have hcB : cnt * B ≤ 12 * Cd * CK * ℓ ^ 10 * q ^ (M + η) := by
      have hx : q ^ (g + η) * q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) ≤ q ^ (M + η) := by
        rw [← Real.rpow_add hq0]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
      calc cnt * B ≤ (Cd * 3 * q ^ (g + η) * ℓ ^ 10) *
            (CK * 4 * q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e))) :=
            mul_le_mul hc hB' hB0 (by positivity)
        _ = 12 * Cd * CK * ℓ ^ 10 * (q ^ (g + η) * q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e))) := by ring
        _ ≤ 12 * Cd * CK * ℓ ^ 10 * q ^ (M + η) := mul_le_mul_of_nonneg_left hx (by positivity)
    have h2P : 2 * P ≤ 2 * ℓ ^ 10 * q ^ (M + η) := by
      have hP : P ≤ q ^ (M + η) := by
        rw [hPm]; exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
      calc 2 * P ≤ 2 * q ^ (M + η) := by linarith
        _ = 2 * 1 * q ^ (M + η) := by ring
        _ ≤ 2 * ℓ ^ 10 * q ^ (M + η) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ10 (by norm_num)) hqM0
    have hEV : 0 ≤ Real.exp 1 * V := mul_nonneg (Real.exp_pos 1).le hV
    calc sqTerm cnt P q V B ≤ Real.exp 1 * V * (2 * P + cnt * B) := min_le_right _ _
      _ ≤ Real.exp 1 * V * (2 * ℓ ^ 10 * q ^ (M + η) + 12 * Cd * CK * ℓ ^ 10 * q ^ (M + η)) :=
          mul_le_mul_of_nonneg_left (add_le_add h2P hcB) hEV
      _ = Real.exp 1 * (2 + 12 * Cd * CK) * ℓ ^ 10 * q ^ (M + η) * V := by ring

/-- The square root of `sqTerm_le_pow`, with `V^{1/2} = (V/P)^{1/2} q^{m/2}`:
`(sqTerm cnt P q V B)^{1/2} ≤ (e(2 + 12C_dC_K))^{1/2}(1 + log qT)^5 q^{(m + M + η)/2}(V/P)^{1/2}`. -/
lemma sqrt_sqTerm_le {d e : ℝ} (he : e ≤ 3 / 4) {q P m M T η g cnt V Cd CK B : ℝ} (hq : 1 < q) (hPm : P = q ^ m)
    (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hη : 0 ≤ η) (hg1 : g ≤ 1) (hM : SqExp d e g m M)
    (hCd : 0 ≤ Cd) (hCK : 0 ≤ CK) (hV : 0 ≤ V)
    (hcnt : cnt ≤ Cd * (q * T) ^ g * (1 + Real.log (q * T)) ^ 10)
    (hB : B ≤ CK * (2 * P) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB0 : 0 ≤ B) :
    Real.sqrt (sqTerm cnt P q V B) ≤
      Real.sqrt (Real.exp 1 * (2 + 12 * Cd * CK)) * (1 + Real.log (q * T)) ^ 5 * q ^ ((m + M + η) / 2) *
        Real.sqrt (V / P) := by
  have hq0 : 0 < q := by linarith
  have hP0 : 0 < P := by rw [hPm]; positivity
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have h := sqTerm_le_pow he hq hPm hT1 hT hη hg1 hM hCd hCK hV hcnt hB hB0
  have hsq : ∀ x : ℝ, Real.sqrt (q ^ x) = q ^ (x / 2) := fun x => by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]; congr 1; ring
  have e10 : Real.sqrt ((1 + Real.log (q * T)) ^ 10) = (1 + Real.log (q * T)) ^ 5 := by
    rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
  have hVP : Real.sqrt V = Real.sqrt (V / P) * q ^ (m / 2) := by
    rw [← hsq, ← hPm, ← Real.sqrt_mul' _ hP0.le, div_mul_cancel₀ V hP0.ne']
  have hK0 : 0 ≤ Real.exp 1 * (2 + 12 * Cd * CK) := by positivity
  calc Real.sqrt (sqTerm cnt P q V B)
      ≤ Real.sqrt (Real.exp 1 * (2 + 12 * Cd * CK) * (1 + Real.log (q * T)) ^ 10 * q ^ (M + η) * V) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt (Real.exp 1 * (2 + 12 * Cd * CK)) * (1 + Real.log (q * T)) ^ 5 * q ^ ((M + η) / 2) *
          Real.sqrt V := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hK0, e10, hsq]
    _ = Real.sqrt (Real.exp 1 * (2 + 12 * Cd * CK)) * (1 + Real.log (q * T)) ^ 5 * q ^ ((m + M + η) / 2) *
          Real.sqrt (V / P) := by
        rw [hVP, show (m + M + η) / 2 = (M + η) / 2 + m / 2 by ring, Real.rpow_add hq0]
        ring

/-- **One bin in two variables, as a power of `q`.** For `q > 1`, `P₁ = q^{m₁}`, `P₂ = q^{m₂}`, `1 ≤ T ≤ 3q^η`,
`η ≥ 0`, a curve value `g ≤ 1` with `twoBound L d e g β m₁ m₂ w` (`hzone`), `e ≤ 3/4`, `C₀, C_d, C_K ≥ 0`,
`Mp ≤ C₀(q^L/(P₁P₂))^{β+w}`, `cnt ≤ C_d(qT)^g(1 + log qT)^{10}`,
`0 ≤ B_i ≤ C_K(2P_i)^{1/12−d}(2q)^{5/12+d+2e}` and `V₁, V₂ ≥ 0`:
`Mp·(sqTerm cnt P₁ q V₁ B₁)^{1/2}(sqTerm cnt P₂ q V₂ B₂)^{1/2}` is at most
`C₀e(2 + 12C_dC_K)(1 + log qT)^{10} q^{L − 1/25000 + η}(V₁/P₁)^{1/2}(V₂/P₂)^{1/2}`. -/
theorem bin_bound_two {L d e : ℝ} (he : e ≤ 3 / 4)
    {q T η β w g Mp cnt C₀ Cd CK P₁ P₂ m₁ m₂ V₁ V₂ B₁ B₂ : ℝ} (hq : 1 < q) (hP₁ : P₁ = q ^ m₁)
    (hP₂ : P₂ = q ^ m₂) (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hη : 0 ≤ η) (hg1 : g ≤ 1)
    (hzone : twoBound L d e g β m₁ m₂ w) (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd) (hCK : 0 ≤ CK)
    (hMp : Mp ≤ C₀ * (q ^ L / (P₁ * P₂)) ^ (β + w))
    (hcnt : cnt ≤ Cd * (q * T) ^ g * (1 + Real.log (q * T)) ^ 10)
    (hB₁ : B₁ ≤ CK * (2 * P₁) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB₁0 : 0 ≤ B₁)
    (hB₂ : B₂ ≤ CK * (2 * P₂) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB₂0 : 0 ≤ B₂)
    (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂) :
    Mp * (Real.sqrt (sqTerm cnt P₁ q V₁ B₁) * Real.sqrt (sqTerm cnt P₂ q V₂ B₂)) ≤
      C₀ * (Real.exp 1 * (2 + 12 * Cd * CK)) * (1 + Real.log (q * T)) ^ 10 * q ^ (L - 1 / 25000 + η) *
        (Real.sqrt (V₁ / P₁) * Real.sqrt (V₂ / P₂)) := by
  obtain ⟨M₁, M₂, hM₁, hM₂, hexp⟩ := hzone
  have hq0 : 0 < q := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have hK0 : 0 ≤ Real.exp 1 * (2 + 12 * Cd * CK) := by positivity
  have h1 := sqrt_sqTerm_le he hq hP₁ hT1 hT hη hg1 hM₁ hCd hCK hV₁ hcnt hB₁ hB₁0
  have h2 := sqrt_sqTerm_le he hq hP₂ hT1 hT hη hg1 hM₂ hCd hCK hV₂ hcnt hB₂ hB₂0
  -- the third factor as a power of `q`
  have hMq : Mp ≤ C₀ * q ^ ((L - m₁ - m₂) * (β + w)) := by
    have e : q ^ L / (P₁ * P₂) = q ^ (L - m₁ - m₂) := by
      rw [hP₁, hP₂, ← Real.rpow_add hq0, ← Real.rpow_sub hq0]; congr 1; ring
    rw [e, ← Real.rpow_mul hq0.le] at hMp
    exact hMp
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log (q * T) := ⟨_, rfl⟩
  rw [← hℓ] at h1 h2 ⊢
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.exp 1 * (2 + 12 * Cd * CK) := ⟨_, rfl⟩
  rw [← hK] at h1 h2 hK0 ⊢
  have hKK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK0
  have hx : q ^ ((L - m₁ - m₂) * (β + w)) * (q ^ ((m₁ + M₁ + η) / 2) * q ^ ((m₂ + M₂ + η) / 2)) ≤
      q ^ (L - 1 / 25000 + η) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
  have hs1 : 0 ≤ Real.sqrt (V₁ / P₁) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (V₂ / P₂) := Real.sqrt_nonneg _
  calc Mp * (Real.sqrt (sqTerm cnt P₁ q V₁ B₁) * Real.sqrt (sqTerm cnt P₂ q V₂ B₂))
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

/-- **Two variables of length at least `q`.** If `m₁, m₂ ≥ 1` and `m₁ + m₂ + 1/2000 ≤ L`, the exponent bound of the
estimate in two variables holds at every `β ≤ 11/12` and `w ≤ 4·10⁻⁶`, whatever the value `g` of the curve: both
mean squares are orthogonality's, with no loss, and the third factor saves `(L − m₁ − m₂)(1 − β − w) ≥ 1/25000`. -/
theorem twoBound_of_long {L d e g β m₁ m₂ w : ℝ} (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂) (hL : m₁ + m₂ + 1 / 2000 ≤ L)
    (hβ1 : β ≤ 11 / 12) (hw1 : w ≤ 4 / 10 ^ 6) : twoBound L d e g β m₁ m₂ w := by
  refine ⟨m₁, m₂, Or.inl ⟨h₁, le_rfl⟩, Or.inl ⟨h₂, le_rfl⟩, ?_⟩
  have hr : (1 : ℝ) / 2000 ≤ L - m₁ - m₂ := by linarith
  have hb : (1 : ℝ) / 12 - 4 / 10 ^ 6 ≤ 1 - (β + w) := by linarith
  have hprod : (1 : ℝ) / 2000 * (1 / 12 - 4 / 10 ^ 6) ≤ (L - m₁ - m₂) * (1 - (β + w)) :=
    mul_le_mul hr hb (by norm_num) (by linarith)
  nlinarith [hprod]

end SieveTypeIIHM

#print axioms SieveTypeIIHM.sqTerm_le_pow
#print axioms SieveTypeIIHM.bin_bound_two
#print axioms SieveTypeIIHM.twoBound_of_long
