/-
# One class of characters, its exponents given: the bound of a class for the resonant window

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTypeIIHM.bin_bound_gen_hm` bounds the contribution of one bin of the characters' zeros, `Mp·binTerm cnt P q V B`,
when the prime sums are at most `C₀(q^L/P)^{β+w}` on the bin and the bin has at most `C_d(qT)^{g(β)}(1 + log qT)^{10}`
characters. The resonant window classes the characters by the sizes of the rest's prime sums as well, and a class's
bounds are then powers `q^E` and `(qT)^γ` that are not the zone's: this file is the bound of one class with the
exponents `E` (the rest's) and `γ` (the count's) given.

* `momExp k s t = max(1, ks) + ks(1 − 2t)`: the exponent of the number of characters at which a prime sum of length
  `q^s` exceeds `q^{st}`, by its `2k`-th moment (`SieveResMoment`).
* `ResBinOK L d e E γ m`: the class's exponents fit, by orthogonality
  (`E + γ/2 + (m + max(m, 1))/2 ≤ L − 1/25000`) or by the Halász–Montgomery inequality
  (`E + γ/2 + m ≤ L − 1/25000` and `E + m/2 + γ + (m(1/12 − d) + 5/12 + d + 2e)/2 ≤ L − 1/25000`).
* `qpow_combine_exp`, `bin_bound_pt_exp`: `SieveTypeII.qpow_combine` and `SieveTypeIIHM.bin_bound_pt` with `q^E`.
* `bin_bound_exp`, **one class**: `SieveTypeIIHM.bin_bound_gen_hm` with `Mp ≤ C₀q^E`,
  `cnt ≤ C_d(qT)^γ(1 + log qT)^{10}` and `ResBinOK L d e E γ m`, with the same constant.

The file imports `SieveTypeIIHM.lean`.
-/
import SieveTypeIIHM

namespace SieveTypeIIHM

open Finset SieveTypeII

/-- The exponent of the number of characters at which a prime sum of length `q^s` exceeds `q^{st}`, by its `2k`-th
moment: `max(1, ks) + ks(1 − 2t)`. -/
noncomputable def momExp (k : ℕ) (s t : ℝ) : ℝ := max 1 (k * s) + k * s * (1 - 2 * t)

/-- **A class's exponents fit**: with the rest's exponent `E`, the count's `γ` and the variable's `m`, by orthogonality
or by the Halász–Montgomery inequality (both of its inequalities). -/
def ResBinOK (L d e E γ m : ℝ) : Prop :=
  E + γ / 2 + (m + max m 1) / 2 ≤ L - 1 / 25000 ∨
    (E + γ / 2 + m ≤ L - 1 / 25000 ∧
      E + m / 2 + γ + (m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2 ≤ L - 1 / 25000)

/-- `SieveTypeII.qpow_combine` with `q^E` in place of `(q^L/P)^{θ′}`: `q^E(qT)^{γ/2}((P + q)V)^{1/2}` is at most
`2√3·q^{E + γ/2 + (1 + m)/2 + η/2}(V/P)^{1/2}` for `m ≤ 1`, and with `m` in place of `(1 + m)/2` for `m ≥ 1`. -/
lemma qpow_combine_exp {q P V T η γ E m : ℝ} (hq : 1 < q) (hPm : P = q ^ m) (hT1 : 1 ≤ T)
    (hT : T ≤ 3 * q ^ η) (hγ1 : γ ≤ 1) :
    (m ≤ 1 → q ^ E * Real.sqrt ((q * T) ^ γ) * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * q ^ (E + γ / 2 + (1 + m) / 2 + η / 2) * Real.sqrt (V / P)) ∧
    (1 ≤ m → q ^ E * Real.sqrt ((q * T) ^ γ) * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * q ^ (E + γ / 2 + m + η / 2) * Real.sqrt (V / P)) := by
  have hq0 : 0 < q := by linarith
  have hP0 : 0 < P := by rw [hPm]; positivity
  have hT0 : 0 < T := by linarith
  have h2 : Real.sqrt ((q * T) ^ γ) ≤ Real.sqrt 3 * q ^ (γ / 2 + η / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.mul_rpow hq0.le hT0.le]
    rcases le_total 0 γ with hγ0 | hγ0
    · have hTg : T ^ (γ * (1 / 2)) ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
      have hT3 : T ^ (1 / 2 : ℝ) ≤ (3 * q ^ η) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hT0.le hT (by norm_num)
      have e3 : (3 * q ^ η) ^ (1 / 2 : ℝ) = Real.sqrt 3 * q ^ (η / 2) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]; ring_nf
      have eq : q ^ (γ * (1 / 2)) * q ^ (η / 2) = q ^ (γ / 2 + η / 2) := by
        rw [← Real.rpow_add hq0]; ring_nf
      calc q ^ (γ * (1 / 2)) * T ^ (γ * (1 / 2)) ≤ q ^ (γ * (1 / 2)) * (Real.sqrt 3 * q ^ (η / 2)) := by
            gcongr; exact (hTg.trans hT3).trans e3.le
        _ = Real.sqrt 3 * q ^ (γ / 2 + η / 2) := by rw [← eq]; ring
    · -- a negative exponent: `T^{γ/2} ≤ 1 ≤ (3q^η)^{1/2} = √3·q^{η/2}`
      have hTg : T ^ (γ * (1 / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 (by nlinarith)
      have e3 : (3 * q ^ η) ^ (1 / 2 : ℝ) = Real.sqrt 3 * q ^ (η / 2) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]; ring_nf
      have h1 : 1 ≤ Real.sqrt 3 * q ^ (η / 2) := by
        rw [← e3]; exact Real.one_le_rpow (by linarith) (by norm_num)
      have eq : q ^ (γ * (1 / 2)) * q ^ (η / 2) = q ^ (γ / 2 + η / 2) := by
        rw [← Real.rpow_add hq0]; ring_nf
      calc q ^ (γ * (1 / 2)) * T ^ (γ * (1 / 2)) ≤ q ^ (γ * (1 / 2)) * 1 :=
            mul_le_mul_of_nonneg_left hTg (by positivity)
        _ ≤ q ^ (γ * (1 / 2)) * (Real.sqrt 3 * q ^ (η / 2)) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Real.sqrt 3 * q ^ (γ / 2 + η / 2) := by rw [← eq]; ring
  have hsplit : Real.sqrt ((P + q) * V) = Real.sqrt ((P + q) * P) * Real.sqrt (V / P) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hA : 0 ≤ q ^ E := by positivity
  have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
  constructor
  · intro hm1
    have hPq : P ≤ q := by
      rw [hPm]; calc q ^ m ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq.le hm1
        _ = q := Real.rpow_one q
    have h3 : Real.sqrt ((P + q) * P) ≤ 2 * q ^ ((1 + m) / 2) := by
      have hb : (P + q) * P ≤ 2 * q ^ (1 + m) := by
        rw [Real.rpow_add hq0, Real.rpow_one, ← hPm]; nlinarith
      calc Real.sqrt ((P + q) * P) ≤ Real.sqrt (2 * q ^ (1 + m)) := Real.sqrt_le_sqrt hb
        _ = Real.sqrt 2 * q ^ ((1 + m) / 2) := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (q ^ (1 + m)), ← Real.rpow_mul hq0.le]; ring_nf
        _ ≤ 2 * q ^ ((1 + m) / 2) := by gcongr
    have eq : q ^ E * q ^ (γ / 2 + η / 2) * q ^ ((1 + m) / 2) = q ^ (E + γ / 2 + (1 + m) / 2 + η / 2) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; ring_nf
    rw [hsplit]
    calc q ^ E * Real.sqrt ((q * T) ^ γ) * (Real.sqrt ((P + q) * P) * Real.sqrt (V / P))
        ≤ q ^ E * (Real.sqrt 3 * q ^ (γ / 2 + η / 2)) * (2 * q ^ ((1 + m) / 2) * Real.sqrt (V / P)) := by
          gcongr
      _ = 2 * Real.sqrt 3 * (q ^ E * q ^ (γ / 2 + η / 2) * q ^ ((1 + m) / 2)) * Real.sqrt (V / P) := by ring
      _ = _ := by rw [eq]
  · intro hm1
    have hPq : q ≤ P := by
      rw [hPm]; calc q = q ^ (1 : ℝ) := (Real.rpow_one q).symm
        _ ≤ q ^ m := Real.rpow_le_rpow_of_exponent_le hq.le hm1
    have h3 : Real.sqrt ((P + q) * P) ≤ 2 * q ^ m := by
      have hb : (P + q) * P ≤ 2 * (q ^ m) ^ 2 := by rw [← hPm]; nlinarith
      calc Real.sqrt ((P + q) * P) ≤ Real.sqrt (2 * (q ^ m) ^ 2) := Real.sqrt_le_sqrt hb
        _ = Real.sqrt 2 * q ^ m := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
        _ ≤ 2 * q ^ m := by gcongr
    have eq : q ^ E * q ^ (γ / 2 + η / 2) * q ^ m = q ^ (E + γ / 2 + m + η / 2) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; ring_nf
    rw [hsplit]
    calc q ^ E * Real.sqrt ((q * T) ^ γ) * (Real.sqrt ((P + q) * P) * Real.sqrt (V / P))
        ≤ q ^ E * (Real.sqrt 3 * q ^ (γ / 2 + η / 2)) * (2 * q ^ m * Real.sqrt (V / P)) := by
          gcongr
      _ = 2 * Real.sqrt 3 * (q ^ E * q ^ (γ / 2 + η / 2) * q ^ m) * Real.sqrt (V / P) := by ring
      _ = _ := by rw [eq]

/-- `SieveTypeIIHM.bin_bound_pt` with `q^E`: under the orthogonality inequalities (`hexp`), for `γ ≤ 1` (`hg1`),
`q > 1`, `P = q^m`, `1 ≤ T ≤ 3q^η`, `C₀, C_d ≥ 0`, `Mp ≤ C₀q^E` and `cnt ≤ C_d(qT)^γ(1 + log qT)^{10}`:
`Mp·cnt^{1/2}((P + q)V)^{1/2} ≤ 2√3·C₀C_d^{1/2}(1 + log qT)^5 q^{L − 1/25000 + η/2}(V/P)^{1/2}`. -/
lemma bin_bound_pt_exp {L q P m T η E γ Mp cnt V C₀ Cd : ℝ} (hg1 : γ ≤ 1)
    (hexp : (m ≤ 1 → E + γ / 2 + (1 + m) / 2 ≤ L - 1 / 25000) ∧
      (1 ≤ m → E + γ / 2 + m ≤ L - 1 / 25000))
    (hq : 1 < q) (hPm : P = q ^ m) (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd)
    (hMp : Mp ≤ C₀ * q ^ E)
    (hcnt : cnt ≤ Cd * (q * T) ^ γ * (1 + Real.log (q * T)) ^ 10) :
    Mp * Real.sqrt cnt * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
        q ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P) := by
  have hq0 : 0 < q := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have hcomb := qpow_combine_exp (V := V) (E := E) hq hPm hT1 hT hg1
  have hsq : Real.sqrt cnt ≤ Real.sqrt Cd * Real.sqrt ((q * T) ^ γ) * (1 + Real.log (q * T)) ^ 5 := by
    have e : Real.sqrt ((1 + Real.log (q * T)) ^ 10) = (1 + Real.log (q * T)) ^ 5 := by
      rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
    calc Real.sqrt cnt ≤ Real.sqrt (Cd * (q * T) ^ γ * (1 + Real.log (q * T)) ^ 10) := Real.sqrt_le_sqrt hcnt
      _ = Real.sqrt Cd * Real.sqrt ((q * T) ^ γ) * (1 + Real.log (q * T)) ^ 5 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCd, e]
  have hA : 0 ≤ q ^ E := by positivity
  have hpow : ∀ E : ℝ, E ≤ L - 1 / 25000 → q ^ (E + η / 2) ≤ q ^ (L - 1 / 25000 + η / 2) :=
    fun E hE => Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
  have key : q ^ E * Real.sqrt ((q * T) ^ γ) * Real.sqrt ((P + q) * V) ≤
      2 * Real.sqrt 3 * q ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P) := by
    have hs3 : 0 ≤ 2 * Real.sqrt 3 := by positivity
    have hVP : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
    rcases le_total m 1 with hm | hm
    · refine (hcomb.1 hm).trans ?_
      have h := hpow _ (hexp.1 hm)
      gcongr
    · refine (hcomb.2 hm).trans ?_
      have h := hpow _ (hexp.2 hm)
      gcongr
  have hs1 : 0 ≤ Real.sqrt ((q * T) ^ γ) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt ((P + q) * V) := Real.sqrt_nonneg _
  calc Mp * Real.sqrt cnt * Real.sqrt ((P + q) * V)
      ≤ (C₀ * q ^ E) *
          (Real.sqrt Cd * Real.sqrt ((q * T) ^ γ) * (1 + Real.log (q * T)) ^ 5) *
            Real.sqrt ((P + q) * V) := by gcongr
    _ = C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
          (q ^ E * Real.sqrt ((q * T) ^ γ) * Real.sqrt ((P + q) * V)) := by
        ring
    _ ≤ C₀ * Real.sqrt Cd * (1 + Real.log (q * T)) ^ 5 *
          (2 * Real.sqrt 3 * q ^ (L - 1 / 25000 + η / 2) * Real.sqrt (V / P)) := by gcongr
    _ = _ := by ring

/-- **One class**: `SieveTypeIIHM.bin_bound_gen_hm` with the exponents given. For `e ≤ 3/4` (`he`), `q > 1` (`hq`),
`P = q^m` (`hPm`), `1 ≤ T ≤ 3q^η` (`hT1`, `hT`), `η ≥ 0` (`hη`), `γ ≤ 1` (`hg1`), `C₀, C_d, C_K ≥ 0` (`hC₀`, `hCd`,
`hCK`), `0 ≤ Mp ≤ C₀q^E` (`hMp0`, `hMp`), `0 ≤ cnt ≤ C_d(qT)^γ(1 + log qT)^{10}` (`hcnt0`, `hcnt`),
`0 ≤ B ≤ C_K(2P)^{1/12−d}(2q)^{5/12+d+2e}` (`hB0`, `hB`) and `ResBinOK L d e E γ m` (`hok`):
`Mp · binTerm cnt P q V B ≤ C′(1 + log qT)^{10} q^{L − 1/25000 + η}(V/P)^{1/2}`, with `bin_bound_gen_hm`'s
`C′ = 2√3·(exp 1)^{1/2}C₀C_d^{1/2} + 3(exp 1)^{1/2}C₀C_dC_K^{1/2}·2`. By orthogonality `binTerm` is at most its first
term and `bin_bound_pt_exp` applies; by the Halász–Montgomery inequality its second term is at most
`(exp 1)^{1/2}(V/P)^{1/2}(√2·cnt^{1/2}P + P^{1/2}cnt·B^{1/2})`, whose summands carry `q` to the exponents of
`ResBinOK`'s two inequalities plus `η/2` and `η`. -/
theorem bin_bound_exp {L d e : ℝ} (he : e ≤ 3 / 4)
    {q P m T η E γ Mp cnt V C₀ Cd CK B : ℝ} (hq : 1 < q) (hPm : P = q ^ m)
    (hT1 : 1 ≤ T) (hT : T ≤ 3 * q ^ η) (hη : 0 ≤ η) (hg1 : γ ≤ 1) (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd) (hCK : 0 ≤ CK)
    (hMp : Mp ≤ C₀ * q ^ E) (hMp0 : 0 ≤ Mp)
    (hcnt : cnt ≤ Cd * (q * T) ^ γ * (1 + Real.log (q * T)) ^ 10) (hcnt0 : 0 ≤ cnt)
    (hB : B ≤ CK * (2 * P) ^ (1 / 12 - d) * (2 * q) ^ (5 / 12 + d + 2 * e)) (hB0 : 0 ≤ B)
    (hok : ResBinOK L d e E γ m) :
    Mp * binTerm cnt P q V B ≤
      (2 * Real.sqrt 3 * Real.sqrt (Real.exp 1) * C₀ * Real.sqrt Cd +
          3 * Real.sqrt (Real.exp 1) * C₀ * Cd * Real.sqrt CK * 2) *
        (1 + Real.log (q * T)) ^ 10 * q ^ (L - 1 / 25000 + η) * Real.sqrt (V / P) := by
  have hq0 : 0 < q := by linarith
  have hP0 : 0 < P := by rw [hPm]; positivity
  have hT0 : 0 < T := by linarith
  have hqT : 1 ≤ q * T := by nlinarith
  have hl : 0 ≤ Real.log (q * T) := Real.log_nonneg hqT
  have hs : 0 ≤ Real.sqrt (V / P) := Real.sqrt_nonneg _
  rcases hok with hok1 | ⟨hHM1, hHM2⟩
  · have hexp : (m ≤ 1 → E + γ / 2 + (1 + m) / 2 ≤ L - 1 / 25000) ∧ (1 ≤ m → E + γ / 2 + m ≤ L - 1 / 25000) := by
      refine ⟨fun hm => ?_, fun hm => ?_⟩
      · rw [max_eq_right hm] at hok1; linarith
      · rw [max_eq_left hm] at hok1; linarith
    -- orthogonality: `binTerm` is at most its first term, and `bin_bound_pt_exp`
    have h1 : Mp * binTerm cnt P q V B ≤ Mp * Real.sqrt cnt * Real.sqrt ((P + q) * V) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) hMp0
    refine h1.trans ((bin_bound_pt_exp (V := V) hg1 hexp hq hPm hT1 hT hC₀ hCd hMp hcnt).trans ?_)
    have hse : 1 ≤ Real.sqrt (Real.exp 1) := Real.one_le_sqrt.2 (Real.one_le_exp zero_le_one)
    have hC : 2 * Real.sqrt 3 * C₀ * Real.sqrt Cd ≤ 2 * Real.sqrt 3 * Real.sqrt (Real.exp 1) * C₀ * Real.sqrt Cd +
        3 * Real.sqrt (Real.exp 1) * C₀ * Cd * Real.sqrt CK * 2 := by
      have h0 : 0 ≤ 2 * Real.sqrt 3 * C₀ * Real.sqrt Cd := by positivity
      have h3 : 0 ≤ 3 * Real.sqrt (Real.exp 1) * C₀ * Cd * Real.sqrt CK * 2 := by positivity
      linarith [mul_le_mul_of_nonneg_left hse h0]
    have hℓ : (1 + Real.log (q * T)) ^ 5 ≤ (1 + Real.log (q * T)) ^ 10 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have hE : q ^ (L - 1 / 25000 + η / 2) ≤ q ^ (L - 1 / 25000 + η) :=
      Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
    refine mul_le_mul_of_nonneg_right ?_ hs
    refine mul_le_mul ?_ hE (by positivity) (by positivity)
    exact mul_le_mul hC hℓ (by positivity) (by positivity)
  · -- Halász–Montgomery: `binTerm` is at most its second term
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = 1 + Real.log (q * T) := ⟨_, rfl⟩
    rw [← hℓ] at hcnt ⊢
    have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
    have hsq : ∀ x : ℝ, Real.sqrt (q ^ x) = q ^ (x / 2) := fun x => by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]; congr 1; ring
    -- the factors as powers of `q`
    have hMq : Mp ≤ C₀ * q ^ E := hMp
    have hgT : (q * T) ^ γ ≤ 3 * q ^ (γ + η) := by
      have hTg : T ^ γ ≤ 3 * q ^ η :=
        ((Real.rpow_le_rpow_of_exponent_le hT1 hg1).trans (Real.rpow_one T).le).trans hT
      rw [Real.mul_rpow hq0.le hT0.le, Real.rpow_add hq0]
      calc q ^ γ * T ^ γ ≤ q ^ γ * (3 * q ^ η) := mul_le_mul_of_nonneg_left hTg (by positivity)
        _ = 3 * (q ^ γ * q ^ η) := by ring
    have hc : cnt ≤ Cd * 3 * q ^ (γ + η) * ℓ ^ 10 := by
      calc cnt ≤ Cd * (q * T) ^ γ * ℓ ^ 10 := hcnt
        _ ≤ Cd * (3 * q ^ (γ + η)) * ℓ ^ 10 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgT hCd) (by positivity)
        _ = Cd * 3 * q ^ (γ + η) * ℓ ^ 10 := by ring
    have hsc : Real.sqrt cnt ≤ Real.sqrt Cd * Real.sqrt 3 * q ^ ((γ + η) / 2) * ℓ ^ 5 := by
      have e10 : Real.sqrt (ℓ ^ 10) = ℓ ^ 5 := by
        rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, Real.sqrt_sq (by positivity)]
      calc Real.sqrt cnt ≤ Real.sqrt (Cd * 3 * q ^ (γ + η) * ℓ ^ 10) := Real.sqrt_le_sqrt hc
        _ = Real.sqrt Cd * Real.sqrt 3 * q ^ ((γ + η) / 2) * ℓ ^ 5 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul hCd, hsq, e10]
    have hsP : Real.sqrt P = q ^ (m / 2) := by rw [hPm, hsq]
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
    have hsB : Real.sqrt B ≤ Real.sqrt CK * 2 * q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2) := by
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      calc Real.sqrt B ≤ Real.sqrt (CK * 4 * q ^ (m * (1 / 12 - d) + (5 / 12 + d + 2 * e))) :=
            Real.sqrt_le_sqrt hB'
        _ = Real.sqrt CK * 2 * q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCK, h4, hsq]
    -- the second term of `binTerm`, split
    have hsplit : Real.sqrt (Real.exp 1 * V * (cnt * (2 * P) + cnt ^ 2 * B)) ≤
        Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
          (Real.sqrt 2 * Real.sqrt cnt * P + Real.sqrt P * (cnt * Real.sqrt B)) := by
      have hX : 0 ≤ cnt * (2 * P) := by positivity
      have hY : 0 ≤ cnt ^ 2 * B := by positivity
      have hsum : Real.sqrt (cnt * (2 * P) + cnt ^ 2 * B) ≤
          Real.sqrt (cnt * (2 * P)) + Real.sqrt (cnt ^ 2 * B) := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [Real.sq_sqrt hX, Real.sq_sqrt hY,
          mul_nonneg (Real.sqrt_nonneg (cnt * (2 * P))) (Real.sqrt_nonneg (cnt ^ 2 * B))]
      have e1 : Real.sqrt (cnt * (2 * P)) = Real.sqrt 2 * Real.sqrt cnt * Real.sqrt P := by
        rw [Real.sqrt_mul hcnt0, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; ring
      have e2 : Real.sqrt (cnt ^ 2 * B) = cnt * Real.sqrt B := by
        rw [Real.sqrt_mul (sq_nonneg cnt), Real.sqrt_sq hcnt0]
      have e3 : Real.sqrt (Real.exp 1 * V * (cnt * (2 * P) + cnt ^ 2 * B)) =
          Real.sqrt (Real.exp 1) * (Real.sqrt (V / P) * Real.sqrt P) *
            Real.sqrt (cnt * (2 * P) + cnt ^ 2 * B) := by
        rw [← Real.sqrt_mul' _ hP0.le, div_mul_cancel₀ V hP0.ne', ← Real.sqrt_mul (Real.exp_pos 1).le,
          ← Real.sqrt_mul' _ (by positivity)]
      have hPP : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP0.le
      rw [e3]
      calc Real.sqrt (Real.exp 1) * (Real.sqrt (V / P) * Real.sqrt P) *
            Real.sqrt (cnt * (2 * P) + cnt ^ 2 * B)
          ≤ Real.sqrt (Real.exp 1) * (Real.sqrt (V / P) * Real.sqrt P) *
              (Real.sqrt (cnt * (2 * P)) + Real.sqrt (cnt ^ 2 * B)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
              (Real.sqrt 2 * Real.sqrt cnt * (Real.sqrt P * Real.sqrt P) +
                Real.sqrt P * (cnt * Real.sqrt B)) := by
            rw [e1, e2]; ring
        _ = Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
              (Real.sqrt 2 * Real.sqrt cnt * P + Real.sqrt P * (cnt * Real.sqrt B)) := by rw [hPP]
    -- the first summand: the exponent of `hmBound`'s first inequality, plus `η/2`
    have hT1b : Mp * Real.sqrt cnt * P ≤
        C₀ * Real.sqrt Cd * Real.sqrt 3 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η) := by
      have hx : q ^ E * q ^ ((γ + η) / 2) * q ^ m ≤ q ^ (L - 1 / 25000 + η) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
      have hℓ5 : ℓ ^ 5 ≤ ℓ ^ 10 := pow_le_pow_right₀ hℓ1 (by norm_num)
      calc Mp * Real.sqrt cnt * P = Mp * Real.sqrt cnt * q ^ m := by rw [hPm]
        _ ≤ C₀ * q ^ E * (Real.sqrt Cd * Real.sqrt 3 * q ^ ((γ + η) / 2) * ℓ ^ 5) *
              q ^ m := by gcongr
        _ = C₀ * Real.sqrt Cd * Real.sqrt 3 * ℓ ^ 5 *
              (q ^ E * q ^ ((γ + η) / 2) * q ^ m) := by ring
        _ ≤ C₀ * Real.sqrt Cd * Real.sqrt 3 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η) := by gcongr
    -- the second summand: the exponent of `hmBound`'s second inequality, plus `η`
    have hT2b : Mp * Real.sqrt P * cnt * Real.sqrt B ≤
        C₀ * Cd * 3 * Real.sqrt CK * 2 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η) := by
      have hx : q ^ E * q ^ (m / 2) * q ^ (γ + η) *
          q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2) ≤ q ^ (L - 1 / 25000 + η) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
      calc Mp * Real.sqrt P * cnt * Real.sqrt B
          ≤ C₀ * q ^ E * q ^ (m / 2) * (Cd * 3 * q ^ (γ + η) * ℓ ^ 10) *
              (Real.sqrt CK * 2 * q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2)) := by
            rw [hsP]; gcongr
        _ = C₀ * Cd * 3 * Real.sqrt CK * 2 * ℓ ^ 10 * (q ^ E * q ^ (m / 2) *
              q ^ (γ + η) * q ^ ((m * (1 / 12 - d) + (5 / 12 + d + 2 * e)) / 2)) := by ring
        _ ≤ C₀ * Cd * 3 * Real.sqrt CK * 2 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η) := by gcongr
    have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc Mp * binTerm cnt P q V B ≤ Mp * Real.sqrt (Real.exp 1 * V * (cnt * (2 * P) + cnt ^ 2 * B)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hMp0
      _ ≤ Mp * (Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
            (Real.sqrt 2 * Real.sqrt cnt * P + Real.sqrt P * (cnt * Real.sqrt B))) :=
          mul_le_mul_of_nonneg_left hsplit hMp0
      _ = Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
            (Real.sqrt 2 * (Mp * Real.sqrt cnt * P) + Mp * Real.sqrt P * cnt * Real.sqrt B) := by ring
      _ ≤ Real.sqrt (Real.exp 1) * Real.sqrt (V / P) *
            (2 * (C₀ * Real.sqrt Cd * Real.sqrt 3 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η)) +
              C₀ * Cd * 3 * Real.sqrt CK * 2 * ℓ ^ 10 * q ^ (L - 1 / 25000 + η)) := by gcongr
      _ = _ := by ring

end SieveTypeIIHM
