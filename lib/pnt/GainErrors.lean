import GainOrbit
import GainSums

/-!
# The gain's errors

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain`; module M-G7d of the gain's numbers, less
its assembly `gain_numbers`): the error exponents summed against `log N(ϖ)`, the rounding loss and the closed-form
constant, each against `c_G = x^{1+2ε}·|A|·e^{x^ε}` (`Setting.cGform`). The definitions are `GainExponents`'.

**The error data's bounds** (`ErrOK`): what the providers of a word's error data `ED` (the pins and the divisibility
theorems) must prove, each with room `x^{1+3ε/2}|A|b`: `log(g₀g₁)·(Σ_j ν(j) + 2Σ_j FTypeG(j) − m·Σ_t a_t)`,
`log d·Σ_j degD(j) ≤ x^{1+3ε/2}|A|b`, `Σ_ρ W_ρ ≤ 4|A|b`, `D_Γ > 0` and `log D_Γ ≤ (N_m·[E:ℚ])²`.

**The errors** (`errors_le`): at an admissible design, under the growth package `GainBig`, for a 2-adic `κ`
(`S.TwoAdic κ e`) and error data with `ErrOK`,
`Σ_ϖ (Σ_j E_j(ϖ))·log N(ϖ) − m(Σ_t a_t)·log(g₀g₁) ≤ c_G/4`. By kinds (`sum_Eexp_logN_eq`), with eight parts of at most
`c_G/40` each:
* the error data's two terms, `≤ x^{1+3ε/2}|A|b` (`ErrOK.ν_le`, `ErrOK.degD_le`), and `40x^{1+3ε/2} ≤ x^{1+2ε}`;
* the inert and signal `p ≤ X″` (three parts, `errors_inert_le`). Per prime and lift (`two_log_mul_Einert_le`),
  `2 log p·Einert(j, p) ≤ 600|A|N_m²x^{2ε} + 2 log p·(60|A|b/p + 6|A|b/p² + [ord h_p odd]·4k|A|b/p³)`: the forced order
  on the plus-sign places is `≤ γ_p·2|A|·k·3b′` (`Fplus_le`: the orbit of a plus-sign place stays at the plus sign
  at an inert `p`, where the weights are `≤ 3b′`, `wt_le_of_plus`), and `8kb′ ≤ b`; the other `1/p` terms read
  `Σ_{Φ_p⁻} w ≤ 4|A|b` (`sum_wt_le`); the terms with `log_p` are `2 log p·log_p y = 2 log y ≤ 6x^ε`
  (`Einert_logb_le`). Summed (`sum_Einert_le`): `#inertPrimes ≤ X″ = x|A|X′`, `Σ log p/p ≤ log X″(1 + log X″)`,
  `Σ log p/p² ≤ log X″`, and the primes of odd order are `≥ 2|A|/ord κ` (`Setting.TwoAdic.le_of_odd`), so
  `Σ_{odd} log p/p³ ≤ log X″·(ord κ)²/(2|A|²)`;
* the stabiliser denominators, `2m·Σ_p v_p(D_Γ) log p ≤ 2m·log D_Γ` (`errors_denom_le`,
  `GainErr.sum_padicValNat_mul_log_le`);
* the constant at `g₀, g₁`, `2m·c_E·f·(N_m² + m²η)·log(g₀g₁)` (`errors_g_le`);
* the cut, `m·err_T·log T ≤ m·9|A|b·25mx^ε` (`errors_cut_le`), with `log T ≤ Λ_u + log 2 ≤ 24mx^ε + 1`
  (`log_sharpT_le_lam`: `SharpCores.log_sharpT_le`'s proof before its last step; `log T ≤ x` would be `x^{1/2}` over
  the budget).

**The exponent sum and the forced orders** (exact): `Σ_ϖ s_ϖ·log N(ϖ) = Σ_{p ∈ inertPrimes(X″)} 2 log p·(Σ_j G_j(p) −
τ_p) + Σ_ϖ (Σ_j F_j(ϖ))·log N(ϖ) − Σ_ϖ (Σ_j E_j(ϖ))·log N(ϖ)` (`sum_sExp_logN`), and
`Σ_ϖ (Σ_j F_j(ϖ))·log N(ϖ) = Fo` (`sum_Fexp_eq_Fo`, termwise `2·FoLib`).

**The rounding** (`rounding_le`): `Σ_ϖ log N(ϖ) ≤ c_G/12`: `2X″ log X″ + 2 log D_Γ + 3 log(g₀g₁) + log T + log d` with
`X″ = x|A|X′`, `X′ = e^{x^{ε/3}}`.

**The constant** (`cG_le`): `0 ≤ c_G ≤ x^{4ε}Σ_t a_t/8` at every admissible design (`|TT| ≥ δ₁|A|/2`,
`a_t ≥ x·e^{x^ε}`, `x^{15ε/8} ≥ 16`).

**The sizes** (`ErrSizes`, from `Adm` and `GainBig`: `errSizes`). Every part is a polynomial in `x`, `|A|`, `N_m`,
`X′` against `b = e^{x^ε}`, compared once and for all: `N_m ≤ x^{403}` (`GainErr.N_le`), `log X″ ≤ 2x^ε`,
`8k·b′ ≤ b`, `10⁶x^{811}·X′ ≤ b` (`GainErr.poly_le`), and four comparisons with `x^{1+2ε}` (`GainErr.half_le`,
`GainErr.cut_le`, `GainErr.sum_le`, `GainErr.odd_le`), each a power `x^c`, `c ≥ ε/50`, against a constant
`≤ 1.2·10⁵` (`GainErr.big_le_rpow`).

**Against the spec.**
* `errors_le` is one-sided, as the study found: the error data's bounds are upper bounds, and only the upper bound is
  used.
* The growth package enters through `X′·x^{1000} ≤ b` alone (`GainBig.G'_le`): the terms with `log_p` at the
  `≈ X″` primes cost `≈ m|A|N_m²x^{2ε}·X″`, and `N_m² > x^{750}` exceeds the `X′ ≥ x^{410}` of `DesignBig`, so `b`
  must beat `N_m²X′`; `DesignBig`'s `b ≥ X′²x^{30}` does not.
* The forced order on the plus-sign places reads `FamAt` (the windows of the families at the tops and thin places):
  with the cruder `w ≤ 2b` it would be `≈ mk|A|b·log² X″`, far over the budget.
* The study's per-term budget `c_G/40` is kept; the parts are grouped as eight (the terms of `Einert` are bounded per
  prime and summed in three groups).
-/

open Finset NumberField

namespace ZetaBalance

noncomputable section

namespace GainErr

/-! ## Elementary facts -/

/-- **`16777216 ≤ x^c`** for `c ≥ ε/50`, at a growth package: two factors `x^{c/2} ≥ 4096` (`DesignBig.le_rpow`). -/
theorem big_le_rpow {ε x : ℝ} (h : DesignBig ε x) {c : ℝ} (hc : ε / 50 ≤ c) : 16777216 ≤ x ^ c := by
  have h1 := h.le_rpow (c := c / 2) (by linarith)
  have e : x ^ c = x ^ (c / 2) * x ^ (c / 2) := by rw [← Real.rpow_add h.pos]; ring_nf
  rw [e]
  nlinarith

/-- **`log p·log_p y = log y`** for `p ≥ 2`. -/
theorem log_mul_logb {p : ℕ} (hp : 2 ≤ p) (y : ℝ) : Real.log p * Real.logb p y = Real.log y := by
  have h : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  rw [Real.logb]
  field_simp

/-- **`log p ≥ 1/2`** for `p ≥ 2`, as `log 2 > 0.69`. -/
theorem half_le_log {p : ℕ} (hp : 2 ≤ p) : 1 / 2 ≤ Real.log p := by
  have h1 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  linarith [Real.log_two_gt_d9]

/-- **`Σ_{p ∈ P} log p ≤ log n`** over the prime factors of `n > 0`: their product divides `n`. -/
theorem sum_log_primeFactors_le {n : ℕ} (hn : 0 < n) : ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
  have hne : ∀ p ∈ n.primeFactors, (p : ℝ) ≠ 0 := fun p hp =>
    Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hpos : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p : ℝ) :=
    prod_pos fun p hp => Nat.cast_pos.2 (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Real.log_prod hne]
  refine Real.log_le_log hpos ?_
  rw [← Nat.cast_prod]
  exact Nat.cast_le.2 (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n))

/-- **`Σ_{p ∈ P} v_p(n)·log p ≤ log n`** for `n > 0` and a set `P` of primes: the terms off the prime factors vanish,
and over the prime factors the sum is `log n` (`Real.log_nat_eq_sum_factorization`). -/
theorem sum_padicValNat_mul_log_le {n : ℕ} (hn : 0 < n) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  classical
  have h0 : ∀ p ∈ P, (padicValNat p n : ℝ) * Real.log p ≠ 0 → p ∈ n.primeFactors := by
    intro p hp hne
    refine Nat.mem_primeFactors.2 ⟨hP p hp, ?_, hn.ne'⟩
    by_contra hd
    exact hne (by rw [padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero, zero_mul])
  rw [← sum_filter_of_ne h0]
  have hlog : Real.log n = ∑ p ∈ n.primeFactors, (padicValNat p n : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    refine sum_congr rfl fun p hp => ?_
    rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
  rw [hlog]
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_filter.1 hp).2) fun p hp _ => ?_
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

/-- **The members of `inertPrimes(X″)`**: primes `p ≤ X″` that do not split. -/
theorem mem_inertPrimes {S : Setting} {X'' : ℝ} (hX : 0 ≤ X'') {p : ℕ}
    (hp : p ∈ Setting.Ranks.inertPrimes (S := S) X'') : p.Prime ∧ (p : ℝ) ≤ X'' ∧ S.cls p ≠ .split := by
  simp only [Setting.Ranks.inertPrimes, mem_filter, mem_range] at hp
  refine ⟨hp.2.1, ?_, hp.2.2.2⟩
  have h1 : p ≤ ⌊X''⌋₊ := by omega
  exact (Nat.cast_le.2 h1).trans (Nat.floor_le hX)

/-- **The constants of the error exponents**: `c_E ≤ 10`, `c_E′ ≤ 3`, `c_E″ ≤ 12`, `c_{dl,1} ≤ 5`, `c_{dl,2} ≤ 4`. -/
theorem Kg_le : (Kg.cE : ℝ) ≤ 10 ∧ (Kg.cE' : ℝ) ≤ 3 ∧ (Kg.cE'' : ℝ) ≤ 12 ∧ (Kg.cdl₁ : ℝ) ≤ 5 ∧
    (Kg.cdl₂ : ℝ) ≤ 4 := by
  norm_num [Kg]

/-! ## The sizes at an admissible design -/

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X}

/-- **`N_m = k + m(t + 1) ≤ x^{403}`**: `k ≤ 2x⁵`, `m ≤ 2x`, `t ≤ x^{401}`. -/
theorem N_le (hA : Dg.Adm) : (Dg.R.N Dg.R.m : ℝ) ≤ x ^ 403 := by
  have hx := hA.big.x_ge
  have hx0 := hA.big.pos
  have hx1 : 1 ≤ x := hA.big.one_lt.le
  have hm2 : (Dg.R.m : ℝ) ≤ 2 * x := by rw [hA.m_eq]; exact hA.big.designM_le
  have hk : (Dg.R.k : ℝ) ≤ 2 * x ^ 5 := by rw [hA.k_eq]; exact hA.big.designK_le.2
  have ht : (Dg.R.t : ℝ) ≤ x ^ 401 := by rw [hA.t_eq]; exact designT_le S hA.big hA.card_le
  simp only [Setting.Ranks.N]
  push_cast
  have h5 : x ^ 5 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
  have h1 : x ≤ x ^ 401 := le_self_pow₀ hx1 (by norm_num)
  have hp : 0 ≤ x ^ 401 := by positivity
  have hmt : (Dg.R.m : ℝ) * (Dg.R.t + 1) ≤ 2 * x * (x ^ 401 + x ^ 401) :=
    mul_le_mul hm2 (by linarith) (by positivity) (by positivity)
  have e1 : x ^ 402 = x * x ^ 401 := by ring
  have e2 : x ^ 403 = x * x ^ 402 := by ring
  have h4 : 4 * x ^ 401 ≤ x ^ 402 := by rw [e1]; exact mul_le_mul_of_nonneg_right (by linarith) hp
  have h5' : 5 * x ^ 402 ≤ x ^ 403 := by
    rw [e2]; exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hx0.le 402)
  have e3 : 2 * x * (x ^ 401 + x ^ 401) = 4 * x ^ 402 := by ring
  linarith

/-- **`X″ ≥ 1`** for `x ≥ 1`. -/
theorem one_le_cutX {S : Setting} {x : ℝ} (ε : ℝ) (hx1 : 1 ≤ x) : 1 ≤ S.cutX x ε := by
  unfold Setting.cutX
  have h1 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have h2 : 1 ≤ Real.exp (x ^ (ε / 3)) := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hx1 h1) h2

/-- **`log X″ = log x + log|A| + x^{ε/3} ≤ 2x^ε`**, as `|A| ≤ x³` and `log x ≤ x^ε/1000`. -/
theorem logX_le (hA : Dg.Adm) : Real.log (S.cutX x ε) ≤ 2 * x ^ ε := by
  have hx0 := hA.big.pos
  have hx1 : 1 ≤ x := hA.big.one_lt.le
  have hA0 : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
  have e : Real.log (S.cutX x ε) = Real.log x + Real.log (Fintype.card S.A) + x ^ (ε / 3) := by
    unfold Setting.cutX
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hx0.ne' hA0.ne', Real.log_exp]
  have hlA : Real.log (Fintype.card S.A) ≤ 3 * Real.log x := by
    calc _ ≤ Real.log (x ^ 3) := Real.log_le_log hA0 hA.card_le_cube
      _ = 3 * Real.log x := by rw [Real.log_pow]; norm_num
  have h3 : x ^ (ε / 3) ≤ x ^ ε := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hA.big.ε_pos])
  have := hA.log_le
  have := Real.log_nonneg hx1
  linarith

/-- **`8k·b′ ≤ b`**: `b′ = x·b/X′` and `8kx ≤ 16x⁶ ≤ x^{410} ≤ X′`. -/
theorem b'_le (hA : Dg.Adm) : 8 * Dg.R.k * scB' x ε ≤ scB x ε := by
  have hx := hA.big.x_ge
  have hx0 := hA.big.pos
  have hx1 : 1 ≤ x := hA.big.one_lt.le
  have hk : (Dg.R.k : ℝ) ≤ 2 * x ^ 5 := by rw [hA.k_eq]; exact hA.big.designK_le.2
  have hX0 : 0 < scX' x ε := Real.exp_pos _
  have hb0 : 0 < scB x ε := Real.exp_pos _
  have h16 : 8 * (Dg.R.k : ℝ) * x ≤ scX' x ε := by
    have e : x ^ 410 = x ^ 6 * x ^ 404 := by ring
    have h1 : 16 ≤ x ^ 404 := le_trans (by linarith) (le_self_pow₀ hx1 (by norm_num))
    have h2 : 16 * x ^ 6 ≤ x ^ 410 := by
      rw [e, mul_comm 16]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (Dg.R.k : ℝ) * x ≤ 2 * x ^ 5 * x := mul_le_mul_of_nonneg_right hk hx0.le
    have e2 : 2 * x ^ 5 * x = 2 * x ^ 6 := by ring
    linarith [hA.big.X'_ge]
  rw [scB'_eq]
  calc 8 * (Dg.R.k : ℝ) * (x * (scB x ε / scX' x ε)) = (8 * Dg.R.k * x) * scB x ε / scX' x ε := by ring
    _ ≤ scX' x ε * scB x ε / scX' x ε := by gcongr
    _ = scB x ε := by field_simp

/-- **`10⁶x^{811}·X′ ≤ b`** under the growth package: `x^{ε/3} + 1000 log x ≤ x^ε` (`GainBig.G'_le`), so
`X′·x^{1000} ≤ b`. -/
theorem poly_le (hA : Dg.Adm) (hB : GainBig ε x) : 10 ^ 6 * x ^ 811 * scX' x ε ≤ scB x ε := by
  have hx := hA.big.x_ge
  have hx0 := hA.big.pos
  have hx1 : 1 ≤ x := hA.big.one_lt.le
  have hXb : scX' x ε * x ^ 1000 ≤ scB x ε := by
    have hG : 0 ≤ ((tilePar x ε (designK x ε)).G' : ℝ) := Nat.cast_nonneg _
    have hxe3 : 0 ≤ x ^ (ε / 3) := Real.rpow_nonneg hx0.le _
    have h0 : 0 ≤ ((tilePar x ε (designK x ε)).G' : ℝ) * x ^ (ε / 3) := mul_nonneg hG hxe3
    have h1 : x ^ (ε / 3) + 1000 * Real.log x ≤ x ^ ε := by
      have := hB.G'_le
      have e : (((tilePar x ε (designK x ε)).G' : ℝ) + 2) * x ^ (ε / 3) =
          ((tilePar x ε (designK x ε)).G' : ℝ) * x ^ (ε / 3) + 2 * x ^ (ε / 3) := by ring
      have := Real.rpow_nonneg hx0.le ε
      linarith
    have e : x ^ 1000 = Real.exp (1000 * Real.log x) := by
      rw [show (1000 : ℝ) * Real.log x = Real.log (x ^ 1000) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    unfold scX' scB scL
    rw [e, ← Real.exp_add]
    exact Real.exp_le_exp.2 h1
  have e : x ^ 1000 = x ^ 811 * x ^ 189 := by ring
  have h1 : 10 ^ 6 ≤ x ^ 189 := by
    have h2 : x ^ 2 ≤ x ^ 189 := pow_le_pow_right₀ hx1 (by norm_num)
    have h3 : (10 : ℝ) ^ 6 ≤ x ^ 2 := by nlinarith
    linarith
  have h2 : 10 ^ 6 * x ^ 811 ≤ x ^ 1000 := by
    rw [e, mul_comm (x ^ 811)]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hX0 : 0 < scX' x ε := Real.exp_pos _
  calc 10 ^ 6 * x ^ 811 * scX' x ε ≤ x ^ 1000 * scX' x ε := mul_le_mul_of_nonneg_right h2 hX0.le
    _ = scX' x ε * x ^ 1000 := by ring
    _ ≤ _ := hXb

/-- **`40x^{1+3ε/2} ≤ x^{1+2ε}`**: `x^{ε/2} ≥ 4096`. -/
theorem half_le (h : DesignBig ε x) : 40 * x ^ (1 + 3 * ε / 2) ≤ x ^ (1 + 2 * ε) := by
  have hx0 := h.pos
  have h1 : 40 ≤ x ^ (ε / 2) := le_trans (by norm_num) (h.le_rpow (by linarith [h.ε_pos]))
  have e : x ^ (1 + 2 * ε) = x ^ (1 + 3 * ε / 2) * x ^ (ε / 2) := by rw [← Real.rpow_add hx0]; ring_nf
  rw [e, mul_comm 40]
  exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx0.le _)

/-- **`9000m²x^ε ≤ x^{1+2ε}`**: `m² ≤ 4x^{1−ε/8}` and `x^{9ε/8} ≥ 36000`. -/
theorem cut_le (hA : Dg.Adm) : 9000 * (Dg.R.m : ℝ) ^ 2 * x ^ ε ≤ x ^ (1 + 2 * ε) := by
  have hx0 := hA.big.pos
  set u₁ := x ^ (1 / 2 - ε / 16) with hu₁
  have hu₁0 : 0 < u₁ := Real.rpow_pos_of_pos hx0 _
  have hmu : (Dg.R.m : ℝ) ≤ 2 * u₁ := (hA.m_mem).2
  have hm0 : (0 : ℝ) ≤ Dg.R.m := Nat.cast_nonneg _
  have h1 := big_le_rpow hA.big (c := 9 * ε / 8) (by linarith [hA.big.ε_pos])
  have e : x ^ (1 + 2 * ε) = u₁ * u₁ * x ^ ε * x ^ (9 * ε / 8) := by
    rw [hu₁, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
  have hm2' : (Dg.R.m : ℝ) ^ 2 ≤ 4 * (u₁ * u₁) := by
    rw [sq]; nlinarith [mul_le_mul hmu hmu hm0 (by linarith)]
  have hP : 0 < u₁ * u₁ * x ^ ε := by have := Real.rpow_pos_of_pos hx0 ε; positivity
  rw [e]
  calc 9000 * (Dg.R.m : ℝ) ^ 2 * x ^ ε ≤ 9000 * (4 * (u₁ * u₁)) * x ^ ε := by gcongr
    _ = (u₁ * u₁ * x ^ ε) * 36000 := by ring
    _ ≤ (u₁ * u₁ * x ^ ε) * x ^ (9 * ε / 8) := mul_le_mul_of_nonneg_left (by linarith) hP.le

/-- **`10⁴m·log X″·(1 + log X″) ≤ x^{1+2ε}`**: `m ≤ 2x^{1/2−ε/16}`, `log X″ ≤ 2x^ε`, and `x^{1/2+ε/16} ≥ 1.2·10⁵`. -/
theorem sum_le (hA : Dg.Adm) :
    10 ^ 4 * Dg.R.m * Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε)) ≤ x ^ (1 + 2 * ε) := by
  have hx0 := hA.big.pos
  set u₁ := x ^ (1 / 2 - ε / 16) with hu₁
  have hu₁0 : 0 < u₁ := Real.rpow_pos_of_pos hx0 _
  have hmu : (Dg.R.m : ℝ) ≤ 2 * u₁ := (hA.m_mem).2
  have hm0 : (0 : ℝ) ≤ Dg.R.m := Nat.cast_nonneg _
  have hlX := logX_le hA
  have hlX0 : 0 ≤ Real.log (S.cutX x ε) := Real.log_nonneg (one_le_cutX ε hA.big.one_lt.le)
  have hxe0 : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  have hxe : 4096 ≤ x ^ ε := hA.big.le_rpow (by linarith [hA.big.ε_pos])
  have h1 := big_le_rpow hA.big (c := 1 / 2 + ε / 16) (by linarith [hA.big.ε_pos])
  have e : x ^ (1 + 2 * ε) = u₁ * x ^ ε * x ^ ε * x ^ (1 / 2 + ε / 16) := by
    rw [hu₁, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
  have h2 : 1 + Real.log (S.cutX x ε) ≤ 3 * x ^ ε := by linarith
  have h3 : Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε)) ≤ 2 * x ^ ε * (3 * x ^ ε) :=
    mul_le_mul hlX h2 (by linarith) (by linarith)
  have hP : 0 < u₁ * x ^ ε * x ^ ε := by positivity
  rw [e]
  calc 10 ^ 4 * (Dg.R.m : ℝ) * Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε)) =
      10 ^ 4 * (Dg.R.m : ℝ) * (Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε))) := by ring
    _ ≤ 10 ^ 4 * (2 * u₁) * (2 * x ^ ε * (3 * x ^ ε)) := by gcongr
    _ = (u₁ * x ^ ε * x ^ ε) * 120000 := by ring
    _ ≤ (u₁ * x ^ ε * x ^ ε) * x ^ (1 / 2 + ε / 16) := mul_le_mul_of_nonneg_left (by linarith) hP.le

/-- **`200mk·log X″·(ord κ)² ≤ x^{1+2ε}|A|²`**: `m ≤ 2x^{1/2−ε/16}`, `k ≤ 2x^{9/2+10ε}`, `log X″ ≤ 2x^ε`,
`ord κ ≤ x^{ε/100}` and `|A| ≥ x^{2+8ε}`, so the ratio is at most `1600x^{−(7ε + ε/16 − ε/50)}`. -/
theorem odd_le (hA : Dg.Adm) :
    200 * Dg.R.m * Dg.R.k * Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 ≤
      x ^ (1 + 2 * ε) * (Fintype.card S.A : ℝ) ^ 2 := by
  have hx0 := hA.big.pos
  have hε := hA.big.ε_pos
  set u₁ := x ^ (1 / 2 - ε / 16) with hu₁
  have hu₁0 : 0 < u₁ := Real.rpow_pos_of_pos hx0 _
  have hmu : (Dg.R.m : ℝ) ≤ 2 * u₁ := (hA.m_mem).2
  have hm0 : (0 : ℝ) ≤ Dg.R.m := Nat.cast_nonneg _
  have hlX := logX_le hA
  have hlX0 : 0 ≤ Real.log (S.cutX x ε) := Real.log_nonneg (one_le_cutX ε hA.big.one_lt.le)
  have hxe0 : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  have h1 := big_le_rpow hA.big (c := 7 * ε + ε / 16 - ε / 50) (by linarith)
  have hkm := (designK_mem hA.big).2
  rw [← hA.k_eq] at hkm
  set v := x ^ (9 / 2 + 10 * ε) with hv
  set w := x ^ (ε / 100) with hw
  have hv0 : 0 < v := Real.rpow_pos_of_pos hx0 _
  have hw0 : 0 < w := Real.rpow_pos_of_pos hx0 _
  have ho := hA.orderOf_le
  have ho0 : (0 : ℝ) ≤ orderOf κ := Nat.cast_nonneg _
  have e : x ^ (1 + 2 * ε) * (x ^ (2 + 8 * ε)) ^ 2 =
      u₁ * v * x ^ ε * (w * w) * x ^ (7 * ε + ε / 16 - ε / 50) := by
    rw [hu₁, hv, hw, sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0,
      ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    ring_nf
  have hA2 : (x ^ (2 + 8 * ε)) ^ 2 ≤ (Fintype.card S.A : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hA.card_ge 2
  have hmk : (Dg.R.m : ℝ) * Dg.R.k ≤ (2 * u₁) * (2 * v) := mul_le_mul hmu hkm (Nat.cast_nonneg _) (by positivity)
  have hlo : Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 ≤ (2 * x ^ ε) * (w * w) := by
    rw [sq]
    exact mul_le_mul hlX (mul_le_mul ho ho ho0 hw0.le) (by positivity) (by positivity)
  have hP : 0 < u₁ * v * x ^ ε * (w * w) := by positivity
  calc 200 * (Dg.R.m : ℝ) * Dg.R.k * Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 =
      200 * ((Dg.R.m : ℝ) * Dg.R.k) * (Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2) := by ring
    _ ≤ 200 * ((2 * u₁) * (2 * v)) * ((2 * x ^ ε) * (w * w)) := by gcongr
    _ = (u₁ * v * x ^ ε * (w * w)) * 1600 := by ring
    _ ≤ (u₁ * v * x ^ ε * (w * w)) * x ^ (7 * ε + ε / 16 - ε / 50) :=
        mul_le_mul_of_nonneg_left (by linarith) hP.le
    _ = x ^ (1 + 2 * ε) * (x ^ (2 + 8 * ε)) ^ 2 := e.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hA2 (Real.rpow_nonneg hx0.le _)

end GainErr

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-! ## The error data's bounds and the sizes -/

/-- **The error data's bounds**: what the providers of the error data (the pins and the divisibility theorems) must
prove of `ED` at the translate `u`, each with room `x^{1+3ε/2}·|A|·b`. -/
structure ErrOK (u : S.A) (ED : ErrData S Dg.R) : Prop where
  /-- `log(g₀g₁)·(Σ_j ν(j) + 2Σ_j FTypeG(j) − m·Σ_t a_t) ≤ x^{1+3ε/2}·|A|·b`: the word's weighted degrees. -/
  ν_le : Real.log (Dg.g₀ * Dg.g₁) * (∑ J, ED.ν J + 2 * ∑ J, Dg.R.FTypeG (Dg.hc u) J -
    Dg.R.m * ∑ t ∈ Dg.TT, Dg.a t) ≤ x ^ (1 + 3 * ε / 2) * Fintype.card S.A * scB x ε
  /-- `Σ_ρ W_ρ ≤ 4|A|·b`: the word's weight deviations. -/
  W_le : ∑ ρ, ED.W ρ ≤ 4 * Fintype.card S.A * scB x ε
  /-- `log d·Σ_j degD(j) ≤ x^{1+3ε/2}·|A|·b`: the error at `√−d`. -/
  degD_le : Real.log S.d * ∑ J, ED.degD J ≤ x ^ (1 + 3 * ε / 2) * Fintype.card S.A * scB x ε
  /-- `D_Γ > 0`. -/
  DΓ_pos : 0 < ED.DΓ
  /-- `log D_Γ ≤ (N_m·[E:ℚ])²`: the stabiliser denominators. -/
  DΓ_le : Real.log ED.DΓ ≤ ((Dg.R.N Dg.R.m : ℝ) * Module.finrank ℚ S.E) ^ 2

/-- **The sizes the errors read**, at an admissible design under the growth package (`errSizes`): the polynomial
sizes `|A| ≤ x³`, `1 ≤ m ≤ 2x`, `t ≤ x^{401}`, `N_m ≤ x^{403}`, `η + 1 ≤ x^{410}`, `c₀ ≤ x^{437}`; the
logarithms `x^ε ≥ 4096`, `log x ≤ x^ε/1000`, `log X″ ≤ 2x^ε`; the scales `8k·b′ ≤ b` and `10⁶x^{811}·X′ ≤ b` (the growth
package); and the four comparisons with `x^{1+2ε}` that the errors' budget reads. -/
structure ErrSizes : Prop where
  /-- `ε > 0`. -/
  ε_pos : 0 < ε
  /-- `x ≥ 4096`. -/
  x_ge : 4096 ≤ x
  /-- `|A| ≤ x³`. -/
  A_le : (Fintype.card S.A : ℝ) ≤ x ^ 3
  /-- `m ≥ 1`. -/
  m_ge : 1 ≤ (Dg.R.m : ℝ)
  /-- `m ≤ 2x`. -/
  m_le : (Dg.R.m : ℝ) ≤ 2 * x
  /-- `t ≤ x^{401}`. -/
  t_le : (Dg.R.t : ℝ) ≤ x ^ 401
  /-- `N_m ≤ x^{403}`. -/
  N_le : (Dg.R.N Dg.R.m : ℝ) ≤ x ^ 403
  /-- `η + 1 ≤ x^{410}`. -/
  eta_le : Dg.eta + 1 ≤ x ^ 410
  /-- `c₀ ≤ x^{437}`. -/
  c0_le : Dg.c0 ≤ x ^ 437
  /-- `x^ε ≥ 4096`. -/
  xε_ge : 4096 ≤ x ^ ε
  /-- `log x ≤ x^ε/1000`. -/
  log_le : Real.log x ≤ x ^ ε / 1000
  /-- `log X″ ≤ 2x^ε`. -/
  logX_le : Real.log (S.cutX x ε) ≤ 2 * x ^ ε
  /-- `8k·b′ ≤ b`. -/
  b'_le : 8 * Dg.R.k * scB' x ε ≤ scB x ε
  /-- `10⁶x^{811}·X′ ≤ b` (the growth package). -/
  poly_le : 10 ^ 6 * x ^ 811 * scX' x ε ≤ scB x ε
  /-- `40x^{1+3ε/2} ≤ x^{1+2ε}`: the error data's room. -/
  half_le : 40 * x ^ (1 + 3 * ε / 2) ≤ x ^ (1 + 2 * ε)
  /-- `9000m²x^ε ≤ x^{1+2ε}`: the cut. -/
  cut_le : 9000 * (Dg.R.m : ℝ) ^ 2 * x ^ ε ≤ x ^ (1 + 2 * ε)
  /-- `10⁴m·log X″·(1 + log X″) ≤ x^{1+2ε}`: the sums `Σ log p/p` of the errors at inert and signal `p`. -/
  sum_le : 10 ^ 4 * Dg.R.m * Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε)) ≤ x ^ (1 + 2 * ε)
  /-- `200mk·log X″·(ord κ)² ≤ x^{1+2ε}|A|²`: the primes of odd order. -/
  odd_le : 200 * Dg.R.m * Dg.R.k * Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 ≤
    x ^ (1 + 2 * ε) * (Fintype.card S.A : ℝ) ^ 2

variable {Dg}

/-- **`log T ≤ Λ_u + log 2`** for the auxiliary prime: `log T ≤ Λ_u − x^{2ε} + log 2` in its window, or `T = 2`, with
`Λ_u ≥ 16mx^ε ≥ 0` (`Adm.lam_ge`). The proof of `log_sharpT_le` before its last step. -/
theorem log_sharpT_le_lam (hA : Dg.Adm) (u : S.A) :
    Real.log (sharpT Dg u) ≤ S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) + Real.log 2 := by
  classical
  unfold sharpT
  split_ifs with h
  · have h0 : 0 ≤ sharpCT x ε := Real.rpow_nonneg hA.big.pos.le _
    linarith [(Nat.find_spec h).2.2.2]
  · rw [Nat.cast_ofNat]
    have h1 := hA.lam_ge u
    have h2 : 0 ≤ 16 * (Dg.m : ℝ) * x ^ ε := by have := Real.rpow_nonneg hA.big.pos.le ε; positivity
    linarith

/-- **The sizes hold** at an admissible design under the growth package (`GainErr.N_le`, `GainErr.logX_le`,
`GainErr.b'_le`, `GainErr.poly_le`, `GainErr.half_le`, `GainErr.cut_le`, `GainErr.sum_le`, `GainErr.odd_le`, and
`SharpAdm`'s polynomial sizes). -/
theorem errSizes (hA : Dg.Adm) (hB : GainBig ε x) : Dg.ErrSizes where
  ε_pos := hA.big.ε_pos
  x_ge := hA.big.x_ge
  A_le := hA.card_le_cube
  m_ge := hA.one_le_m
  m_le := by rw [hA.m_eq]; exact hA.big.designM_le
  t_le := by rw [hA.t_eq]; exact designT_le S hA.big hA.card_le
  N_le := GainErr.N_le hA
  eta_le := by
    have := hA.toDesignAdm.eta_le (m := Dg.R.m) (by rw [hA.m_eq]; exact hA.big.designM_le)
    unfold eta
    linarith
  c0_le := hA.c0_le
  xε_ge := hA.big.le_rpow (by linarith [hA.big.ε_pos])
  log_le := hA.log_le
  logX_le := GainErr.logX_le hA
  b'_le := GainErr.b'_le hA
  poly_le := GainErr.poly_le hA hB
  half_le := GainErr.half_le hA.big
  cut_le := GainErr.cut_le hA
  sum_le := GainErr.sum_le hA
  odd_le := GainErr.odd_le hA

/-! ## The error exponent at an inert or signal prime -/

/-- **The weights at the plus-sign places are at most `3b′`**: the gain reads `hc u` at `(1, c·t)` for `z = (1, t)`,
a plus-sign place, which is a top (`≤ 3b′`) or thin (`≤ 2w″ ≤ 2b′`), as the thick places have the sign `−1`
(`Setting.DesignAdm.e_window`). -/
theorem wt_le_of_plus (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m)
    {z : Φ S.A} (hz : z.1 = 1) : Dg.wt u J z ≤ 3 * scB' x ε := by
  have hm : (Dg.R.m : ℝ) ≤ 2 * x := by rw [hA.m_eq]; exact hA.big.designM_le
  set z' : Φ S.A := (z.1, S.twA κ * z.2) with hz'
  have hz1 : z'.1 = 1 := hz
  obtain ⟨Wt, Wn, -, -⟩ := hA.toDesignAdm.e_window (T2 := Dg.T2) (ρstar := designStar pr.a₀ pr.sstar)
    (bT := pr.bT ∘ (S.twA κ * ·)) hm hF.σ_lt (hA.bT_le_tw hF) hF.hyp u z' J
  have hw := hA.toDesignAdm.w''_le_b'
  have hwt : Dg.wt u J z = ((designFam S x ε Dg.R (Dg.TT.image (S.twA κ * ·)) Dg.T2 (pr.aZ ∘ (S.twA κ * ·))
      (pr.bT ∘ (S.twA κ * ·)) (designStar pr.a₀ pr.sstar) pr.σ hF.hyp u z').e J : ℝ) := by
    unfold wt
    rw [Setting.Ranks.wj, hF.hc_eq u]
  rw [hwt]
  rcases hk : placeKind (Dg.TT.image (S.twA κ * ·)) Dg.T2 u z' with _ | _ | _
  · exact Wt hk
  · exfalso
    obtain ⟨s, -, hs⟩ := mem_image.1 (placeKind_eq_thick.1 hk)
    rw [← hs] at hz1
    exact (by decide : (-1 : ℤˣ) ≠ 1) hz1
  · have := Wn hk
    have := scB'_pos ε hA.big.pos
    linarith

/-- **A set of places has at most `2|A|` elements** (`|Φ| = f = 2|A|`). -/
theorem card_places_le (P : Finset (Φ S.A)) : (P.card : ℝ) ≤ 2 * Fintype.card S.A := by
  have h1 := card_le_univ P
  have h2 : Fintype.card (Φ S.A) = 2 * Fintype.card S.A := S.f_eq
  rw [h2] at h1
  exact_mod_cast h1

/-- **The weights over a set of places sum to at most `4|A|·b`**: at most `2|A|` places, each of weight `≤ 2b`. -/
theorem sum_wt_le (hA : Dg.Adm) (u : S.A) (J : Fin Dg.R.m) (P : Finset (Φ S.A)) :
    ∑ z ∈ P, Dg.wt u J z ≤ 4 * Fintype.card S.A * scB x ε := by
  have hb0 : 0 < scB x ε := Real.exp_pos _
  calc ∑ z ∈ P, Dg.wt u J z ≤ ∑ _z ∈ P, 2 * scB x ε :=
        sum_le_sum fun z _ => (hA.e_mem u (z.1, S.twA κ * z.2) J).2
    _ = P.card * (2 * scB x ε) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * Fintype.card S.A) * (2 * scB x ε) := by gcongr; exact card_places_le P
    _ = _ := by ring

/-- **The forced order on the plus-sign places** is at most `γ_p·2|A|·k·3b′`: at a signal `p` there are none, and at
an inert `p` the orbit of a plus-sign place stays at the plus sign, where the weights are `≤ 3b′`
(`wt_le_of_plus`); `lpF(p, n, D) ≤ γ_p·Σ_s D(s)` (`Setting.lpF_nonneg_le`). -/
theorem Fplus_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (hp : 2 ≤ p) : max 0 (Dg.Fplus u J p) ≤ gamP p * (2 * Fintype.card S.A) * (Dg.R.k * (3 * scB' x ε)) := by
  have hn : (1 : ℝ) ≤ S.nP (S.twA κ) p := by exact_mod_cast S.one_le_nP _ p
  have hk := Dg.one_le_k
  have hB' : 0 < scB' x ε := scB'_pos ε hA.big.pos
  have hg := gamP_nonneg p
  have key : ∀ z ∈ (S.minusPlaces p)ᶜ, Setting.lpF p (S.nP (S.twA κ) p)
      (fun s => ((Dg.R.k : ℝ) - 1) * Dg.wt u J (S.pos (S.twA κ) p z s)) ≤
        gamP p * (S.nP (S.twA κ) p * (Dg.R.k * (3 * scB' x ε))) := by
    intro z hz
    have hz' : S.cls p ≠ .signal ∧ z.1 = 1 := by
      rw [mem_compl, Setting.minusPlaces] at hz
      by_cases hs : S.cls p = .signal
      · rw [ite_eq_left hs] at hz
        exact absurd (mem_univ z) hz
      · rw [ite_eq_right hs, mem_filter] at hz
        refine ⟨hs, ?_⟩
        rcases Int.units_eq_one_or z.1 with h | h
        · exact h
        · exact absurd ⟨mem_univ z, h⟩ hz
    have hpos : ∀ s : ℕ, (S.pos (S.twA κ) p z s).1 = 1 := fun s => by
      simp [Setting.pos, hz'.1, hz'.2]
    have hD : 0 ≤ fun s : Fin (S.nP (S.twA κ) p) => ((Dg.R.k : ℝ) - 1) * Dg.wt u J (S.pos (S.twA κ) p z s) :=
      fun s => mul_nonneg (by linarith) (Dg.wt_pos u J _).le
    refine (Setting.lpF_nonneg_le (ℓ := (p : ℝ)) (by exact_mod_cast hp) hD).2.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hg
    calc ∑ s : Fin (S.nP (S.twA κ) p), ((Dg.R.k : ℝ) - 1) * Dg.wt u J (S.pos (S.twA κ) p z s) ≤
        ∑ _s : Fin (S.nP (S.twA κ) p), (Dg.R.k : ℝ) * (3 * scB' x ε) := sum_le_sum fun s _ => by
          have h1 := wt_le_of_plus hA hF u J (hpos s)
          have h2 := (Dg.wt_pos u J (S.pos (S.twA κ) p z s)).le
          nlinarith
      _ = S.nP (S.twA κ) p * (Dg.R.k * (3 * scB' x ε)) := by simp
  have hF' : Dg.Fplus u J p ≤ gamP p * (2 * Fintype.card S.A) * (Dg.R.k * (3 * scB' x ε)) := by
    unfold Fplus
    have hc := card_places_le (S.minusPlaces p)ᶜ
    have hK : 0 ≤ gamP p * ((Dg.R.k : ℝ) * (3 * scB' x ε)) := by positivity
    calc (S.nP (S.twA κ) p : ℝ)⁻¹ * ∑ z ∈ (S.minusPlaces p)ᶜ, Setting.lpF p (S.nP (S.twA κ) p)
          (fun s => ((Dg.R.k : ℝ) - 1) * Dg.wt u J (S.pos (S.twA κ) p z s)) ≤
        (S.nP (S.twA κ) p : ℝ)⁻¹ * ∑ _z ∈ (S.minusPlaces p)ᶜ,
          gamP p * (S.nP (S.twA κ) p * (Dg.R.k * (3 * scB' x ε))) :=
          mul_le_mul_of_nonneg_left (sum_le_sum key) (by positivity)
      _ = ((S.minusPlaces p)ᶜ.card : ℝ) * (gamP p * ((Dg.R.k : ℝ) * (3 * scB' x ε))) := by
          rw [sum_const, nsmul_eq_mul]
          field_simp
      _ ≤ (2 * Fintype.card S.A) * (gamP p * ((Dg.R.k : ℝ) * (3 * scB' x ε))) :=
          mul_le_mul_of_nonneg_right hc hK
      _ = _ := by ring
  exact max_le (by positivity) hF'

/-- **The logarithms of the scales**: `0 ≤ log a ≤ 2x^ε` and `0 ≤ log 2a ≤ 3x^ε`, as `log a = log x + x^ε`. -/
theorem ErrSizes.log_scA (hs : Dg.ErrSizes) :
    0 ≤ Real.log (scA x ε) ∧ Real.log (scA x ε) ≤ 2 * x ^ ε ∧ 0 ≤ Real.log (2 * scA x ε) ∧
      Real.log (2 * scA x ε) ≤ 3 * x ^ ε := by
  have hx := hs.x_ge
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have ha1 := one_le_scA ε hx1
  have e : Real.log (scA x ε) = Real.log x + x ^ ε := by
    unfold scA scB scL
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have e2 : Real.log (2 * scA x ε) = Real.log 2 + Real.log (scA x ε) :=
    Real.log_mul (by norm_num) (by linarith)
  have hl0 := Real.log_nonneg hx1
  have hl := hs.log_le
  have hxe := hs.xε_ge
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  refine ⟨Real.log_nonneg ha1, by linarith, Real.log_nonneg (by linarith), by linarith⟩

/-- **`b ≥ 10⁶x^{811}`** (`ErrSizes.poly_le`, `X′ ≥ 1`). -/
theorem ErrSizes.b_ge (hs : Dg.ErrSizes) : 10 ^ 6 * x ^ 811 ≤ scB x ε := by
  have hx0 : 0 < x := by linarith [hs.x_ge]
  have h1 : 1 ≤ scX' x ε := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  exact le_trans (le_mul_of_one_le_right (by positivity) h1) hs.poly_le

/-- **`n_p ≤ 2|A|`**: an order in `A`, or twice one. -/
theorem nP_le_two_card (c : S.A) (p : ℕ) : (S.nP c p : ℝ) ≤ 2 * Fintype.card S.A := by
  have h1 := orderOf_le_card_univ (x := S.hPtw c p ^ 2)
  have h2 := orderOf_le_card_univ (x := S.hPtw c p)
  unfold Setting.nP
  split_ifs
  · push_cast; exact_mod_cast Nat.mul_le_mul_left 2 h1
  · have h3 : (orderOf (S.hPtw c p) : ℝ) ≤ Fintype.card S.A := by exact_mod_cast h2
    have h4 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
    linarith

/-- **`N_j ≤ N_m`** for `j ≤ m`. -/
theorem N_le_N_m {j : ℕ} (hj : j ≤ Dg.R.m) : (Dg.R.N j : ℝ) ≤ Dg.R.N Dg.R.m := by
  unfold Setting.Ranks.N
  exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _

/-- **The terms `1/p` of the error exponent** at `p ≥ 2`: `max(0, F⁺) + γ_p·#(tops in Φ_p⁻)·(b + η + 1 + 3S_c) +
c_E″Σ_{Φ_p⁻}w/p ≤ (1 + 6 + 48)|A|b/p`, by `Fplus_le` and `8kb′ ≤ b`, `γ_p ≤ 4/(3p)`, `b + η + 1 + 3S_c ≤ 2b`, and
`Σ_{Φ_p⁻}w ≤ 4|A|b`. -/
theorem Einert_inv_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (hs : Dg.ErrSizes) (u : S.A)
    (J : Fin Dg.R.m) {p : ℕ} (hp : 2 ≤ p) :
    max 0 (Dg.Fplus u J p) + gamP p * Dg.topsMinus p * (scB x ε + Dg.eta + 1 + 3 * Dg.cloud) +
      Kg.cE'' * (∑ z ∈ S.minusPlaces p, Dg.wt u J z / p) ≤ 55 * Fintype.card S.A * scB x ε / p := by
  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hb0 : 0 < scB x ε := Real.exp_pos _
  have hB' : 0 < scB' x ε := scB'_pos ε (by linarith [hs.x_ge])
  have hA0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ Dg.R.k := Nat.cast_nonneg _
  have hη := Dg.eta_nonneg
  have hcl := Dg.cloud_nonneg
  have hg := gamP_le hp
  have hM : max 0 (Dg.Fplus u J p) ≤ Fintype.card S.A * scB x ε / p := by
    calc max 0 (Dg.Fplus u J p) ≤ gamP p * (2 * Fintype.card S.A) * (Dg.R.k * (3 * scB' x ε)) :=
          Fplus_le hA hF u J hp
      _ ≤ 4 / (3 * p) * (2 * Fintype.card S.A) * (Dg.R.k * (3 * scB' x ε)) := by gcongr
      _ = Fintype.card S.A * (8 * Dg.R.k * scB' x ε) / p := by field_simp; ring
      _ ≤ Fintype.card S.A * scB x ε / p := by gcongr; exact hs.b'_le
  have hT : gamP p * Dg.topsMinus p * (scB x ε + Dg.eta + 1 + 3 * Dg.cloud) ≤
      6 * Fintype.card S.A * scB x ε / p := by
    have htm : (Dg.topsMinus p : ℝ) ≤ 2 * Fintype.card S.A := card_places_le _
    have hcl3 : 3 * Dg.cloud ≤ Dg.c0 := by
      unfold cloud c0
      have : (0 : ℝ) ≤ Dg.R.k * designΔ x := by positivity
      linarith
    have hbig := hs.b_ge
    have hx1 : 1 ≤ x := by linarith [hs.x_ge]
    have h1 : x ^ 410 ≤ x ^ 811 := pow_le_pow_right₀ hx1 (by norm_num)
    have h2 : x ^ 437 ≤ x ^ 811 := pow_le_pow_right₀ hx1 (by norm_num)
    have h3 : 0 ≤ x ^ 811 := by positivity
    have hsum : scB x ε + Dg.eta + 1 + 3 * Dg.cloud ≤ 2 * scB x ε := by
      linarith [hs.eta_le, hs.c0_le]
    calc gamP p * Dg.topsMinus p * (scB x ε + Dg.eta + 1 + 3 * Dg.cloud) ≤
        4 / (3 * p) * (2 * Fintype.card S.A) * (2 * scB x ε) := by
          gcongr
      _ = 16 / 3 * (Fintype.card S.A * scB x ε / p) := by field_simp; ring
      _ ≤ 6 * (Fintype.card S.A * scB x ε / p) := by gcongr; norm_num
      _ = _ := by ring
  have hE : (Kg.cE'' : ℝ) * (∑ z ∈ S.minusPlaces p, Dg.wt u J z / p) ≤ 48 * Fintype.card S.A * scB x ε / p := by
    rw [← sum_div]
    have hw := sum_wt_le hA u J (S.minusPlaces p)
    have hw0 : 0 ≤ ∑ z ∈ S.minusPlaces p, Dg.wt u J z := sum_nonneg fun z _ => (Dg.wt_pos u J z).le
    calc (Kg.cE'' : ℝ) * ((∑ z ∈ S.minusPlaces p, Dg.wt u J z) / p) ≤
        12 * ((4 * Fintype.card S.A * scB x ε) / p) := by gcongr; exact GainErr.Kg_le.2.2.1
      _ = _ := by ring
  have e : 55 * (Fintype.card S.A : ℝ) * scB x ε / p = Fintype.card S.A * scB x ε / p +
      6 * Fintype.card S.A * scB x ε / p + 48 * Fintype.card S.A * scB x ε / p := by ring
  linarith

/-- **The terms with `log_p` of the error exponent**, weighted by `2 log p`, at `p ∈ inertPrimes(X″)`:
`2 log p·(|Φ_p⁻|N_jN_{j+1}(log_p(4n_pN_m a) + 1) + c_{dl,1}|Φ_p⁻|N_m² log_p 2a + c_{dl,2}·#(tops in Φ_p⁻)·(log_p 2a)²)
≤ 368|A|N_m²x^{2ε}`, as `2 log p·log_p y = 2 log y`, `log p ≥ 1/2`, `log(4n_pN_m a) ≤ 3x^ε`, `log 2a ≤ 3x^ε` and
`log p ≤ log X″ ≤ 2x^ε`. -/
theorem Einert_logb_le (hs : Dg.ErrSizes) (J : Fin Dg.R.m) {p : ℕ}
    (hp : p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) :
    2 * Real.log p * ((S.minusPlaces p).card * (Dg.R.N J : ℝ) * Dg.R.N ((J : ℕ) + 1) *
        (Real.logb p (4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m * scA x ε) + 1) +
      Kg.cdl₁ * (S.minusPlaces p).card * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
      Kg.cdl₂ * Dg.topsMinus p * Real.logb p (2 * scA x ε) ^ 2) ≤
    368 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * (x ^ ε * x ^ ε) := by
  have hx := hs.x_ge
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hpp, hpX, -⟩ := GainErr.mem_inertPrimes (by linarith [GainErr.one_le_cutX (S := S) ε hx1]) hp
  have hp2 := hpp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
  have hlp2 := GainErr.half_le_log hp2
  have hlpL : Real.log p ≤ 2 * x ^ ε := (Real.log_le_log hp0 hpX).trans hs.logX_le
  obtain ⟨hla0, hla, hl2a0, hl2a⟩ := hs.log_scA
  obtain ⟨-, -, -, hcdl₁, hcdl₂⟩ := GainErr.Kg_le
  have hy := hs.xε_ge
  have hA1 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have hN1 : (1 : ℝ) ≤ Dg.R.N Dg.R.m := by exact_mod_cast Dg.one_le_N
  have hc := card_places_le (S.minusPlaces p)
  have htm : (Dg.topsMinus p : ℝ) ≤ 2 * Fintype.card S.A := card_places_le _
  have hNJ : (Dg.R.N J : ℝ) ≤ Dg.R.N Dg.R.m := N_le_N_m (le_of_lt J.2)
  have hNJ1 : (Dg.R.N ((J : ℕ) + 1) : ℝ) ≤ Dg.R.N Dg.R.m := N_le_N_m J.2
  have ha1 := one_le_scA ε hx1
  have hn1 : (1 : ℝ) ≤ S.nP (S.twA κ) p := by exact_mod_cast S.one_le_nP _ p
  have hn := nP_le_two_card (S.twA κ) p
  -- the logarithm of `4n_pN_m a`
  have hY1 : 1 ≤ 4 * (S.nP (S.twA κ) p : ℝ) * Dg.R.N Dg.R.m * scA x ε := by
    have h1 : 1 ≤ 4 * (S.nP (S.twA κ) p : ℝ) := by linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 hN1) ha1
  have hlY : Real.log (4 * (S.nP (S.twA κ) p : ℝ) * Dg.R.N Dg.R.m * scA x ε) ≤ 3 * x ^ ε := by
    have hY : 4 * (S.nP (S.twA κ) p : ℝ) * Dg.R.N Dg.R.m * scA x ε ≤ 8 * x ^ 406 * scA x ε := by
      have h1 : 4 * (S.nP (S.twA κ) p : ℝ) * Dg.R.N Dg.R.m ≤ 4 * (2 * x ^ 3) * x ^ 403 := by
        gcongr
        · linarith [hs.A_le]
        · exact hs.N_le
      have ha0 : 0 ≤ scA x ε := by linarith
      calc 4 * (S.nP (S.twA κ) p : ℝ) * Dg.R.N Dg.R.m * scA x ε ≤ 4 * (2 * x ^ 3) * x ^ 403 * scA x ε :=
            mul_le_mul_of_nonneg_right h1 ha0
        _ = 8 * x ^ 406 * scA x ε := by ring
    have e : Real.log (8 * x ^ 406 * scA x ε) = Real.log 8 + 406 * Real.log x + Real.log (scA x ε) := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    have h8 : Real.log 8 ≤ 3 := by
      have : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_lt_d9]
    have := Real.log_le_log (by linarith) hY
    linarith [hs.log_le]
  have hlY0 : 0 ≤ Real.log (4 * (S.nP (S.twA κ) p : ℝ) * Dg.R.N Dg.R.m * scA x ε) := Real.log_nonneg hY1
  -- the three terms
  have t1 : 2 * Real.log p * ((S.minusPlaces p).card * (Dg.R.N J : ℝ) * Dg.R.N ((J : ℕ) + 1) *
      (Real.logb p (4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m * scA x ε) + 1)) ≤
      20 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε := by
    have e : 2 * Real.log p * ((S.minusPlaces p).card * (Dg.R.N J : ℝ) * Dg.R.N ((J : ℕ) + 1) *
        (Real.logb p (4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m * scA x ε) + 1)) =
        2 * (S.minusPlaces p).card * (Dg.R.N J : ℝ) * Dg.R.N ((J : ℕ) + 1) *
          (Real.log p * Real.logb p (4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m * scA x ε) + Real.log p) := by ring
    rw [e, GainErr.log_mul_logb hp2]
    calc 2 * ((S.minusPlaces p).card : ℝ) * (Dg.R.N J : ℝ) * Dg.R.N ((J : ℕ) + 1) *
          (Real.log (4 * S.nP (S.twA κ) p * Dg.R.N Dg.R.m * scA x ε) + Real.log p) ≤
        2 * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) * Dg.R.N Dg.R.m * (3 * x ^ ε + 2 * x ^ ε) := by
          gcongr
      _ = _ := by ring
  have t2 : 2 * Real.log p * (Kg.cdl₁ * (S.minusPlaces p).card * (Dg.R.N Dg.R.m : ℝ) ^ 2 *
      Real.logb p (2 * scA x ε)) ≤ 60 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε := by
    have e : 2 * Real.log p * (Kg.cdl₁ * (S.minusPlaces p).card * (Dg.R.N Dg.R.m : ℝ) ^ 2 *
        Real.logb p (2 * scA x ε)) = 2 * Kg.cdl₁ * (S.minusPlaces p).card * (Dg.R.N Dg.R.m : ℝ) ^ 2 *
          (Real.log p * Real.logb p (2 * scA x ε)) := by ring
    rw [e, GainErr.log_mul_logb hp2]
    calc 2 * (Kg.cdl₁ : ℝ) * (S.minusPlaces p).card * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.log (2 * scA x ε) ≤
        2 * 5 * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * (3 * x ^ ε) := by gcongr
      _ = _ := by ring
  have t3 : 2 * Real.log p * (Kg.cdl₂ * Dg.topsMinus p * Real.logb p (2 * scA x ε) ^ 2) ≤
      288 * Fintype.card S.A * (x ^ ε * x ^ ε) := by
    have hlb : Real.logb p (2 * scA x ε) ≤ 2 * Real.log (2 * scA x ε) := by
      rw [Real.logb, div_le_iff₀ hlp0]
      have := mul_le_mul_of_nonneg_left hlp2 hl2a0
      linarith
    have e : 2 * Real.log p * (Kg.cdl₂ * Dg.topsMinus p * Real.logb p (2 * scA x ε) ^ 2) =
        2 * Kg.cdl₂ * Dg.topsMinus p * ((Real.log p * Real.logb p (2 * scA x ε)) *
          Real.logb p (2 * scA x ε)) := by ring
    rw [e, GainErr.log_mul_logb hp2]
    have hlb0 : 0 ≤ Real.logb p (2 * scA x ε) := Real.logb_nonneg (by exact_mod_cast hpp.one_lt) (by linarith)
    have hlb' : Real.logb p (2 * scA x ε) ≤ 2 * (3 * x ^ ε) := by linarith
    calc 2 * (Kg.cdl₂ : ℝ) * Dg.topsMinus p * (Real.log (2 * scA x ε) * Real.logb p (2 * scA x ε)) ≤
        2 * 4 * (2 * Fintype.card S.A) * ((3 * x ^ ε) * (2 * (3 * x ^ ε))) := by
          gcongr
      _ = _ := by ring
  have hq1 : (Fintype.card S.A : ℝ) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε ≤
      Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * (x ^ ε * x ^ ε) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith) (by linarith)) (by positivity)
  have hq2 : (Fintype.card S.A : ℝ) * (x ^ ε * x ^ ε) ≤
      Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * (x ^ ε * x ^ ε) := by
    have h1 : (1 : ℝ) ≤ (Dg.R.N Dg.R.m : ℝ) ^ 2 := one_le_pow₀ hN1
    have h2 : 0 ≤ (Fintype.card S.A : ℝ) * (x ^ ε * x ^ ε) := by positivity
    calc (Fintype.card S.A : ℝ) * (x ^ ε * x ^ ε) = 1 * (Fintype.card S.A * (x ^ ε * x ^ ε)) := by ring
      _ ≤ (Dg.R.N Dg.R.m : ℝ) ^ 2 * (Fintype.card S.A * (x ^ ε * x ^ ε)) := mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  rw [mul_add, mul_add]
  linarith only [t1, t2, t3, hq1, hq2]

/-- **The odd-order terms of the error exponent**, weighted by `2 log p`, at `p ≥ 2`:
`2 log p·[ord h_p odd]·((k − 1)Σ_{Φ_p⁻}w/p³ + c_E″fN_m² log_p a) ≤ 96|A|N_m²x^ε + 2 log p·[ord h_p odd]·4k|A|b/p³`,
as `Σ_{Φ_p⁻}w ≤ 4|A|b` and `2 log p·log_p a = 2 log a ≤ 4x^ε`. -/
theorem Einert_odd_le (hA : Dg.Adm) (hs : Dg.ErrSizes) (u : S.A) (J : Fin Dg.R.m) {p : ℕ} (hp : 2 ≤ p) :
    2 * Real.log p * (if Odd (orderOf (S.hPtw (S.twA κ) p)) then
        ((Dg.R.k : ℝ) - 1) * (∑ z ∈ S.minusPlaces p, Dg.wt u J z) / (p : ℝ) ^ 3 +
          Kg.cE'' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (scA x ε)
      else 0) ≤
      96 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε + 2 * Real.log p *
        (if Odd (orderOf (S.hPtw (S.twA κ) p)) then 4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3
        else 0) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 (by omega)
  have hlp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hy := hs.xε_ge
  have hA0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
  have hq : 0 ≤ 96 * (Fintype.card S.A : ℝ) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε := by positivity
  split_ifs with ho
  · obtain ⟨hla0, hla, -, -⟩ := hs.log_scA
    have hk := Dg.one_le_k
    have hw := sum_wt_le hA u J (S.minusPlaces p)
    have hw0 : 0 ≤ ∑ z ∈ S.minusPlaces p, Dg.wt u J z := sum_nonneg fun z _ => (Dg.wt_pos u J z).le
    have hf : (S.f : ℝ) = 2 * Fintype.card S.A := by rw [Setting.f_eq]; push_cast; ring
    have t1 : ((Dg.R.k : ℝ) - 1) * (∑ z ∈ S.minusPlaces p, Dg.wt u J z) / (p : ℝ) ^ 3 ≤
        4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3 := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc ((Dg.R.k : ℝ) - 1) * (∑ z ∈ S.minusPlaces p, Dg.wt u J z) ≤
          Dg.R.k * (4 * Fintype.card S.A * scB x ε) := mul_le_mul (by linarith) hw hw0 (by positivity)
        _ = 4 * Dg.R.k * Fintype.card S.A * scB x ε := by ring
    have t2 : 2 * Real.log p * (Kg.cE'' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (scA x ε)) ≤
        96 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε := by
      have e : 2 * Real.log p * (Kg.cE'' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (scA x ε)) =
          2 * Kg.cE'' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * (Real.log p * Real.logb p (scA x ε)) := by ring
      rw [e, GainErr.log_mul_logb hp]
      calc 2 * (Kg.cE'' : ℝ) * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.log (scA x ε) ≤
          2 * 12 * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * (2 * x ^ ε) := by
            gcongr
            · exact GainErr.Kg_le.2.2.1
            · exact hf.le
        _ = _ := by ring
    have t1' := mul_le_mul_of_nonneg_left t1 (by linarith : 0 ≤ 2 * Real.log p)
    rw [mul_add]
    linarith only [t1', t2]
  · simp only [mul_zero, add_zero]
    exact hq

/-- **The error exponent at an inert `p` with `h_p = 1`**, weighted by `2 log p`:
`2 log p·(c_E′fN_m² log_p a + Σ_ρ w/(p² − 1)) ≤ 24|A|N_m²x^ε + 2 log p·6|A|b/p²`, as `Σ_ρ w ≤ 4|A|b` and
`4/(p² − 1) ≤ 6/p²` for `p ≥ 2`. -/
theorem Einert_one_le (hA : Dg.Adm) (hs : Dg.ErrSizes) (u : S.A) (J : Fin Dg.R.m) {p : ℕ} (hp : 2 ≤ p) :
    2 * Real.log p * (Kg.cE' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (scA x ε) +
      ∑ ρ, Dg.wt u J ρ / ((p : ℝ) ^ 2 - 1)) ≤
      24 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε +
        2 * Real.log p * (6 * Fintype.card S.A * scB x ε / (p : ℝ) ^ 2) := by
  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  obtain ⟨hla0, hla, -, -⟩ := hs.log_scA
  have hf : (S.f : ℝ) = 2 * Fintype.card S.A := by rw [Setting.f_eq]; push_cast; ring
  have hA0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
  have t1 : 2 * Real.log p * (Kg.cE' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (scA x ε)) ≤
      24 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε := by
    have e : 2 * Real.log p * (Kg.cE' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (scA x ε)) =
        2 * Kg.cE' * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * (Real.log p * Real.logb p (scA x ε)) := by ring
    rw [e, GainErr.log_mul_logb hp]
    calc 2 * (Kg.cE' : ℝ) * S.f * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.log (scA x ε) ≤
        2 * 3 * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * (2 * x ^ ε) := by
          gcongr
          · exact GainErr.Kg_le.2.1
          · exact hf.le
      _ = _ := by ring
  have t2 : ∑ ρ, Dg.wt u J ρ / ((p : ℝ) ^ 2 - 1) ≤ 6 * Fintype.card S.A * scB x ε / (p : ℝ) ^ 2 := by
    have hp3 : 4 ≤ (p : ℝ) ^ 2 := by
      have := mul_le_mul hp2' hp2' (by norm_num) (by linarith)
      rw [sq]; linarith
    rw [← sum_div]
    have hw : ∑ ρ, Dg.wt u J ρ ≤ 4 * Fintype.card S.A * scB x ε := sum_wt_le hA u J univ
    have hw0 : 0 ≤ ∑ ρ, Dg.wt u J ρ := sum_nonneg fun ρ _ => (Dg.wt_pos u J ρ).le
    have hb0 : 0 < scB x ε := Real.exp_pos _
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have h1 : (∑ ρ, Dg.wt u J ρ) * (p : ℝ) ^ 2 ≤ 4 * Fintype.card S.A * scB x ε * (p : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    have h2 : 0 ≤ (Fintype.card S.A : ℝ) * scB x ε * ((p : ℝ) ^ 2 - 3) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have t2' := mul_le_mul_of_nonneg_left t2 (by linarith : 0 ≤ 2 * Real.log p)
  rw [mul_add]
  linarith only [t1, t2']

/-- **The error exponent at an inert or signal `p ≤ X″`**, weighted by `2 log p`: at most
`600|A|N_m²x^{2ε} + 2 log p·(60|A|b/p + 6|A|b/p² + [ord h_p odd]·4k|A|b/p³)`. At an inert `p` with `h_p = 1` this is
`Einert_one_le`; otherwise the terms `1/p` (`Einert_inv_le`), the terms with `log_p` (`Einert_logb_le`) and the
odd-order terms (`Einert_odd_le`). -/
theorem two_log_mul_Einert_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (hs : Dg.ErrSizes) (u : S.A)
    (J : Fin Dg.R.m) {p : ℕ} (hp : p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) :
    2 * Real.log p * Dg.Einert u J p ≤ 600 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ (2 * ε) +
      2 * Real.log p * (60 * Fintype.card S.A * scB x ε / p + 6 * Fintype.card S.A * scB x ε / (p : ℝ) ^ 2 +
        if Odd (orderOf (S.hPtw (S.twA κ) p)) then 4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3
        else 0) := by
  have hx := hs.x_ge
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp2 := (GainErr.mem_inertPrimes (by linarith [GainErr.one_le_cutX (S := S) ε hx1]) hp).1.two_le
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 (by omega)
  have hlp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp2)
  have hy := hs.xε_ge
  have hy2 : x ^ (2 * ε) = x ^ ε * x ^ ε := by rw [← Real.rpow_add hx0]; ring_nf
  have hA0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
  have hb0 : 0 < scB x ε := Real.exp_pos _
  have hN1 : (1 : ℝ) ≤ Dg.R.N Dg.R.m := by exact_mod_cast Dg.one_le_N
  have hq1 : (Fintype.card S.A : ℝ) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε ≤
      Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * (x ^ ε * x ^ ε) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith) (by linarith)) (by positivity)
  have hq0 : 0 ≤ (Fintype.card S.A : ℝ) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ ε := by positivity
  have hite : 0 ≤ if Odd (orderOf (S.hPtw (S.twA κ) p)) then
      4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3 else 0 := by
    split_ifs <;> positivity
  have hP1 : 0 ≤ 2 * Real.log p * (Fintype.card S.A * scB x ε / p) := by positivity
  have hP2 : 0 ≤ 2 * Real.log p * (Fintype.card S.A * scB x ε / (p : ℝ) ^ 2) := by positivity
  have hP3 : 0 ≤ 2 * Real.log p * (if Odd (orderOf (S.hPtw (S.twA κ) p)) then
      4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3 else 0) := mul_nonneg (by linarith) hite
  rw [hy2]
  unfold Einert
  by_cases hc : S.cls p = .inert ∧ S.hPtw (S.twA κ) p = 1
  · rw [ite_eq_left hc]
    have h1 := Einert_one_le hA hs u J hp2
    have e : 2 * Real.log p * (60 * Fintype.card S.A * scB x ε / p + 6 * Fintype.card S.A * scB x ε / (p : ℝ) ^ 2 +
        if Odd (orderOf (S.hPtw (S.twA κ) p)) then 4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3
        else 0) = 60 * (2 * Real.log p * (Fintype.card S.A * scB x ε / p)) +
          2 * Real.log p * (6 * Fintype.card S.A * scB x ε / (p : ℝ) ^ 2) +
          2 * Real.log p * (if Odd (orderOf (S.hPtw (S.twA κ) p)) then
            4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3 else 0) := by ring
    rw [e]
    linarith only [h1, hq1, hq0, hP1, hP3]
  · rw [ite_eq_right hc]
    have h1 := mul_le_mul_of_nonneg_left (Einert_inv_le hA hF hs u J hp2) (by linarith : 0 ≤ 2 * Real.log p)
    have h2 := Einert_logb_le hs J hp
    have h3 := Einert_odd_le hA hs u J hp2
    have e : 2 * Real.log p * (60 * Fintype.card S.A * scB x ε / p + 6 * Fintype.card S.A * scB x ε / (p : ℝ) ^ 2 +
        if Odd (orderOf (S.hPtw (S.twA κ) p)) then 4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3
        else 0) = 60 * (2 * Real.log p * (Fintype.card S.A * scB x ε / p)) +
          6 * (2 * Real.log p * (Fintype.card S.A * scB x ε / (p : ℝ) ^ 2)) +
          2 * Real.log p * (if Odd (orderOf (S.hPtw (S.twA κ) p)) then
            4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3 else 0) := by ring
    have e1 : 2 * Real.log p * (55 * Fintype.card S.A * scB x ε / p) =
        55 * (2 * Real.log p * (Fintype.card S.A * scB x ε / p)) := by ring
    rw [e]
    linarith only [h1, h2, h3, e1, hq1, hq0, hP1, hP2, hP3]

/-- **The errors at the inert and signal primes**, summed with the weights `2 log p` over `p ∈ inertPrimes(X″)` and
over the lifts: at most `m·(X″·600|A|N_m²x^{2ε} + 132|A|b·log X″(1 + log X″) + 4kb·log X″·(ord κ)²/|A|)`. The
per-prime bound (`two_log_mul_Einert_le`) is summed with `#inertPrimes ≤ X″` (`card_le_of_mem_Icc`),
`Σ log p/p ≤ log X″(1 + log X″)`, `Σ log p/p² ≤ log X″` (`sum_log_div_le_of_mem`, `sum_log_div_sq_le_of_mem`), and
over the primes of odd order, which are `≥ P = 2|A|/ord κ` (`Setting.TwoAdic.le_of_odd`),
`Σ log p/p³ ≤ P⁻¹·2 log X″/P`. -/
theorem sum_Einert_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (hs : Dg.ErrSizes) {e : ℕ}
    (h2 : S.TwoAdic κ e) (u : S.A) :
    ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), 2 * Real.log p * ∑ J, Dg.Einert u J p ≤
      Dg.R.m * (S.cutX x ε * (600 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ (2 * ε)) +
        132 * Fintype.card S.A * scB x ε * (Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε))) +
        4 * Dg.R.k * scB x ε * Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 / Fintype.card S.A) := by
  classical
  have hx := hs.x_ge
  have hx1 : 1 ≤ x := by linarith
  have hX1 := GainErr.one_le_cutX (S := S) ε hx1
  have hmem := fun {p : ℕ} (hp : p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) =>
    GainErr.mem_inertPrimes (S := S) (by linarith) hp
  have hA1 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have hb0 : 0 < scB x ε := Real.exp_pos _
  have hk0 : (0 : ℝ) ≤ Dg.R.k := Nat.cast_nonneg _
  have ho0 : (0 : ℝ) < orderOf κ := by exact_mod_cast orderOf_pos κ
  have hL0 : 0 ≤ Real.log (S.cutX x ε) := Real.log_nonneg hX1
  have hC0 : 0 ≤ 600 * (Fintype.card S.A : ℝ) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ (2 * ε) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) (2 * ε)
    positivity
  have hpt : ∀ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), 2 * Real.log p * ∑ J, Dg.Einert u J p ≤
      Dg.R.m * (600 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ (2 * ε) +
        120 * Fintype.card S.A * scB x ε * (Real.log p / p) +
        12 * Fintype.card S.A * scB x ε * (Real.log p / (p : ℝ) ^ 2) +
        8 * Dg.R.k * Fintype.card S.A * scB x ε *
          (if Odd (orderOf (S.hPtw (S.twA κ) p)) then Real.log p / (p : ℝ) ^ 3 else 0)) := by
    intro p hp
    rw [mul_sum]
    calc ∑ J, 2 * Real.log p * Dg.Einert u J p ≤ ∑ _J : Fin Dg.R.m,
        (600 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ (2 * ε) +
          2 * Real.log p * (60 * Fintype.card S.A * scB x ε / p + 6 * Fintype.card S.A * scB x ε / (p : ℝ) ^ 2 +
            if Odd (orderOf (S.hPtw (S.twA κ) p)) then 4 * Dg.R.k * Fintype.card S.A * scB x ε / (p : ℝ) ^ 3
            else 0)) := sum_le_sum fun J _ => two_log_mul_Einert_le hA hF hs u J hp
      _ = _ := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        split_ifs <;> ring
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, ← mul_sum, ← mul_sum]
  -- the four sums
  have hs1 : ((Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)).card : ℝ) ≤ S.cutX x ε := by
    have := card_le_of_mem_Icc (α := 1) hX1 fun n hn =>
      ⟨by exact_mod_cast (hmem hn).1.one_lt.le, (hmem hn).2.1⟩
    linarith
  have hs2 := sum_log_div_le_of_mem (P := Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) hX1 fun n hn =>
    ⟨(hmem hn).1.one_lt.le, (hmem hn).2.1⟩
  have hs3 := sum_log_div_sq_le_of_mem (P := Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) (P₀ := 2)
    (by norm_num) hX1 fun n hn => ⟨by exact_mod_cast (hmem hn).1.two_le, (hmem hn).2.1⟩
  have hs4 : ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
      (if Odd (orderOf (S.hPtw (S.twA κ) p)) then Real.log p / (p : ℝ) ^ 3 else 0) ≤
      Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 / (2 * (Fintype.card S.A : ℝ) ^ 2) := by
    rw [← sum_filter]
    set P := 2 * (Fintype.card S.A : ℝ) / orderOf κ with hP
    have hP0 : 0 < P := by positivity
    have hge : ∀ p ∈ (Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)).filter
        (fun p => Odd (orderOf (S.hPtw (S.twA κ) p))), P ≤ p ∧ (p : ℝ) ≤ S.cutX x ε := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
      obtain ⟨hpp, hpX, hcls⟩ := hmem hp1
      refine ⟨?_, hpX⟩
      have h := h2.le_of_odd hpp hcls hp2
      have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
      have e : P = (4 * (Fintype.card S.A : ℝ) / orderOf κ) / 2 := by rw [hP]; ring
      rw [e]
      linarith
    have hsq := sum_log_div_sq_le_of_mem hP0 hX1 hge
    calc ∑ p ∈ (Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)).filter
          (fun p => Odd (orderOf (S.hPtw (S.twA κ) p))), Real.log p / (p : ℝ) ^ 3 ≤
        ∑ p ∈ (Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)).filter
          (fun p => Odd (orderOf (S.hPtw (S.twA κ) p))), P⁻¹ * (Real.log p / (p : ℝ) ^ 2) := by
          refine sum_le_sum fun p hp => ?_
          have hPp := (hge p hp).1
          have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le hP0 hPp
          have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          rw [show Real.log p / (p : ℝ) ^ 3 = (p : ℝ)⁻¹ * (Real.log p / (p : ℝ) ^ 2) by field_simp]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hP0 hPp) (by positivity)
      _ = P⁻¹ * ∑ p ∈ (Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)).filter
          (fun p => Odd (orderOf (S.hPtw (S.twA κ) p))), Real.log p / (p : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ P⁻¹ * (2 * Real.log (S.cutX x ε) / P) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by rw [hP]; field_simp
  have hL1 : Real.log (S.cutX x ε) ≤ Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε)) := by
    have := mul_nonneg hL0 hL0
    linarith [mul_add (Real.log (S.cutX x ε)) 1 (Real.log (S.cutX x ε))]
  have hAb : 0 ≤ (Fintype.card S.A : ℝ) * scB x ε := by positivity
  have t2 := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ 120 * Fintype.card S.A * scB x ε)
  have t3 := mul_le_mul_of_nonneg_left hs3 (by positivity : (0 : ℝ) ≤ 12 * Fintype.card S.A * scB x ε)
  have t4 := mul_le_mul_of_nonneg_left hs4 (by positivity : (0 : ℝ) ≤ 8 * Dg.R.k * Fintype.card S.A * scB x ε)
  have t1 := mul_le_mul_of_nonneg_right hs1 hC0
  have e4 : 8 * (Dg.R.k : ℝ) * Fintype.card S.A * scB x ε *
      (Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 / (2 * (Fintype.card S.A : ℝ) ^ 2)) =
      4 * Dg.R.k * scB x ε * Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 / Fintype.card S.A := by
    field_simp; ring
  have e3 : 12 * (Fintype.card S.A : ℝ) * scB x ε * (2 * Real.log (S.cutX x ε) / 2) =
      12 * (Fintype.card S.A * scB x ε) * Real.log (S.cutX x ε) := by ring
  have t3' := mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ 12 * (Fintype.card S.A * scB x ε))
  linarith

/-! ## The exponent sum and the forced orders -/

/-- **The exponent sum**: `Σ_ϖ s_ϖ·log N(ϖ) = Σ_{p ∈ inertPrimes(X″)} 2 log p·(Σ_j G_j(p) − τ_p) +
Σ_ϖ (Σ_j F_j(ϖ))·log N(ϖ) − Σ_ϖ (Σ_j E_j(ϖ))·log N(ϖ)`: `G` and `τ` live at the rational primes and vanish off
`inertPrimes(X″)` (`gainG_eq_zero`, `tau_eq_zero`), where `log N(p) = 2 log p`. -/
theorem sum_sExp_logN (pr : DesignPar S) (u : S.A) (ED : ErrData S Dg.R) :
    ∑ ϖ ∈ Dg.primeSet ED, Dg.sExp pr u ED ϖ * Dg.logN u ϖ =
      ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
          2 * Real.log p * (∑ J, Dg.gainG pr u J p - Dg.tau pr p) +
        ∑ ϖ ∈ Dg.primeSet ED, (∑ J, Dg.Fexp u J ϖ) * Dg.logN u ϖ -
        ∑ ϖ ∈ Dg.primeSet ED, (∑ J, Dg.Eexp u ED J ϖ) * Dg.logN u ϖ := by
  classical
  have h1 : ∀ ϖ, Dg.sExp pr u ED ϖ * Dg.logN u ϖ =
      (∑ J, Dg.Gexp pr u J ϖ - Dg.tauE pr ϖ) * Dg.logN u ϖ +
        (∑ J, Dg.Fexp u J ϖ) * Dg.logN u ϖ - (∑ J, Dg.Eexp u ED J ϖ) * Dg.logN u ϖ := by
    intro ϖ
    simp only [sExp, sum_add_distrib, sum_sub_distrib]
    ring
  simp only [h1, sum_sub_distrib, sum_add_distrib]
  congr 2
  rw [Dg.sum_primeSet]
  simp only [Gexp, tauE, logN, sum_const_zero, Nat.cast_zero, sub_zero, zero_mul, add_zero]
  symm
  rw [← sum_subset subset_union_left fun p _ hp => ?_]
  · exact sum_congr rfl fun p _ => by ring
  · rw [sum_eq_zero fun J _ => Dg.gainG_eq_zero pr u J fun h => hp h.1, Dg.tau_eq_zero pr hp]
    simp

/-- **The forced orders**: `Σ_ϖ (Σ_j F_j(ϖ))·log N(ϖ) = Fo`, termwise: `FInert(j, p)·2 log p` at the inert and
signal `p ≤ X″`, `FTypeG(j)·2 log g_i` at `g_i` (`log g₀ + log g₁ = log(g₀g₁)`), `2·FRamD(j)·log d` at `√−d`, and
`0` elsewhere, which is `2·FoLib`. -/
theorem sum_Fexp_eq_Fo (u : S.A) (ED : ErrData S Dg.R) :
    ∑ ϖ ∈ Dg.primeSet ED, (∑ J, Dg.Fexp u J ϖ) * Dg.logN u ϖ =
      Dg.R.Fo (Dg.hc u) (S.twA κ) Dg.g₀ Dg.g₁ (S.cutX x ε) := by
  classical
  have hg : Real.log ((Dg.g₀ : ℝ) * Dg.g₁) = Real.log Dg.g₀ + Real.log Dg.g₁ :=
    Real.log_mul (Nat.cast_ne_zero.2 Dg.g₀_prime.ne_zero) (Nat.cast_ne_zero.2 Dg.g₁_prime.ne_zero)
  have hrat : ∀ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∪ ED.DΓ.primeFactors,
      (∑ J, Dg.Fexp u J (.rat p)) * Dg.logN u (.rat p) =
        if p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) then
          2 * ∑ J, Dg.R.FInert (Dg.hc u) (S.twA κ) J p * Real.log p else 0 := by
    intro p _
    simp only [Fexp, logN]
    split_ifs
    · rw [sum_mul, mul_sum]
      exact sum_congr rfl fun J _ => by ring
    · simp
  rw [Dg.sum_primeSet, sum_congr rfl hrat, sum_ite_mem, union_inter_cancel_left]
  simp only [Fexp, logN, gs, Matrix.cons_val_zero, Matrix.cons_val_one, sum_const_zero, zero_mul, zero_add]
  have e1 : ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
      2 * ∑ J, Dg.R.FInert (Dg.hc u) (S.twA κ) J p * Real.log p =
      2 * ∑ J, ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
        Dg.R.FInert (Dg.hc u) (S.twA κ) J p * Real.log p := by
    rw [← mul_sum, sum_comm]
  have e2 : ∑ J, (2 : ℝ) * Dg.R.FRamD (Dg.hc u) (S.twA κ) J = 2 * ∑ J, Dg.R.FRamD (Dg.hc u) (S.twA κ) J := by
    rw [mul_sum]
  rw [e1, e2, Setting.Ranks.Fo, Setting.Ranks.FoLib, sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, hg]
  ring

/-! ## The errors, the rounding and the constant -/

/-- **The errors by kinds** (`sum_primeSet`): `Σ_ϖ (Σ_j E_j(ϖ))·log N(ϖ)` is the sum of the errors at the inert and
signal `p ≤ X″` (`Σ_p 2 log p·Σ_j Einert(j, p)`), the stabiliser denominators (`2m·Σ_p v_p(D_Γ)·log p`), the
weighted degrees and the forced orders at `g₀, g₁, π̄₀, π̄₁` (`log(g₀g₁)·(Σ_j ν(j) + 2Σ_j FTypeG(j))`), the constant at
`g₀, g₁` (`2m·c_E·f·(N_m² + m²η)·log(g₀g₁)`), the cut (`m·err_T·log T`) and `√−d` (`log d·Σ_j degD(j)`). -/
theorem sum_Eexp_logN_eq (u : S.A) (ED : ErrData S Dg.R) :
    ∑ ϖ ∈ Dg.primeSet ED, (∑ J, Dg.Eexp u ED J ϖ) * Dg.logN u ϖ =
      ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), 2 * Real.log p * ∑ J, Dg.Einert u J p +
        2 * Dg.R.m * ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∪ ED.DΓ.primeFactors,
          (padicValNat p ED.DΓ : ℝ) * Real.log p +
        Real.log (Dg.g₀ * Dg.g₁) * (∑ J, ED.ν J + 2 * ∑ J, Dg.R.FTypeG (Dg.hc u) J) +
        2 * Dg.R.m * (Kg.cE * S.f * ((Dg.R.N Dg.R.m : ℝ) ^ 2 + (Dg.R.m : ℝ) ^ 2 * Dg.eta)) *
          Real.log (Dg.g₀ * Dg.g₁) +
        Dg.R.m * Dg.errT ED * Real.log (sharpT Dg u) + Real.log S.d * ∑ J, ED.degD J := by
  classical
  rw [Dg.sum_primeSet]
  have hg : Real.log ((Dg.g₀ : ℝ) * Dg.g₁) = Real.log Dg.g₀ + Real.log Dg.g₁ :=
    Real.log_mul (Nat.cast_ne_zero.2 Dg.g₀_prime.ne_zero) (Nat.cast_ne_zero.2 Dg.g₁_prime.ne_zero)
  have hrat : ∀ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∪ ED.DΓ.primeFactors,
      (∑ J, Dg.Eexp u ED J (.rat p)) * Dg.logN u (.rat p) =
        (if p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) then 2 * Real.log p * ∑ J, Dg.Einert u J p
          else 0) + 2 * Dg.R.m * ((padicValNat p ED.DΓ : ℝ) * Real.log p) := by
    intro p _
    simp only [Eexp, logN, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    split_ifs
    · ring
    · simp only [sum_const_zero]; ring
  rw [sum_congr rfl hrat, sum_add_distrib, sum_ite_mem, union_inter_cancel_left, ← mul_sum]
  simp only [Eexp, logN, gs, Matrix.cons_val_zero, Matrix.cons_val_one, sum_add_distrib,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hg]
  ring

/-- **`m·A·N_m² ≤ 2x^{810}`** and **`x^{1+2ε} = x·x^ε·x^ε`**: the shapes the budget reads. -/
theorem ErrSizes.mAN_le (hs : Dg.ErrSizes) :
    (Dg.R.m : ℝ) * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 ≤ 2 * x ^ 810 ∧
      x ^ (1 + 2 * ε) = x * x ^ ε * x ^ ε := by
  have hx0 : 0 < x := by linarith [hs.x_ge]
  refine ⟨?_, by rw [Real.rpow_add hx0, Real.rpow_one, mul_assoc, ← Real.rpow_add hx0]; ring_nf⟩
  calc (Dg.R.m : ℝ) * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 ≤ (2 * x) * x ^ 3 * (x ^ 403) ^ 2 := by
        gcongr
        · exact hs.m_le
        · exact hs.A_le
        · exact hs.N_le
    _ = 2 * x ^ 810 := by ring

/-- **The errors at the inert and signal primes are at most `3c_G/40`** (`sum_Einert_le`): the three parts are each
at most `c_G/40`, by `10⁶x^{811}X′ ≤ b` (with `X″ = x|A|X′`), `ErrSizes.sum_le` and `ErrSizes.odd_le`. -/
theorem errors_inert_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (hs : Dg.ErrSizes) {e : ℕ}
    (h2 : S.TwoAdic κ e) (u : S.A) :
    ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), 2 * Real.log p * ∑ J, Dg.Einert u J p ≤
      3 * (S.cGform x ε / 40) := by
  refine (sum_Einert_le hA hF hs h2 u).trans ?_
  have hx := hs.x_ge
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hmAN, e⟩ := hs.mAN_le
  have hA0 : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
  have hb0 : 0 < scB x ε := Real.exp_pos _
  have hX0 : 0 < scX' x ε := Real.exp_pos _
  have hm0 : (0 : ℝ) ≤ Dg.R.m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ Dg.R.k := Nat.cast_nonneg _
  have hxe0 : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  have hL0 : 0 ≤ Real.log (S.cutX x ε) := Real.log_nonneg (GainErr.one_le_cutX ε hx1)
  have hy2 : x ^ (2 * ε) = x ^ ε * x ^ ε := by rw [← Real.rpow_add hx0]; ring_nf
  have ha : (Dg.R.m : ℝ) * (S.cutX x ε * (600 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ (2 * ε))) ≤
      S.cGform x ε / 40 := by
    have h1 : 600 * (2 * x ^ 810) * scX' x ε ≤ scB x ε / 40 := by
      have h2 : x ^ 810 ≤ x ^ 811 := pow_le_pow_right₀ hx1 (by norm_num)
      have := hs.poly_le
      nlinarith
    calc (Dg.R.m : ℝ) * (S.cutX x ε * (600 * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 * x ^ (2 * ε))) =
        (x * x ^ ε * x ^ ε * Fintype.card S.A) *
          (600 * ((Dg.R.m : ℝ) * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2) * scX' x ε) := by
          unfold Setting.cutX scX'; rw [hy2]; ring
      _ ≤ (x * x ^ ε * x ^ ε * Fintype.card S.A) * (600 * (2 * x ^ 810) * scX' x ε) := by gcongr
      _ ≤ (x * x ^ ε * x ^ ε * Fintype.card S.A) * (scB x ε / 40) := by gcongr
      _ = S.cGform x ε / 40 := by unfold Setting.cGform; rw [e]; ring
  have hb : (Dg.R.m : ℝ) * (132 * Fintype.card S.A * scB x ε *
      (Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε)))) ≤ S.cGform x ε / 40 := by
    have h1 := hs.sum_le
    have h0 : 0 ≤ (Dg.R.m : ℝ) * Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε)) := by positivity
    calc (Dg.R.m : ℝ) * (132 * Fintype.card S.A * scB x ε *
          (Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε)))) =
        (Fintype.card S.A * scB x ε) *
          (132 * ((Dg.R.m : ℝ) * Real.log (S.cutX x ε) * (1 + Real.log (S.cutX x ε)))) := by ring
      _ ≤ (Fintype.card S.A * scB x ε) * (x ^ (1 + 2 * ε) / 40) := by gcongr; linarith
      _ = S.cGform x ε / 40 := by unfold Setting.cGform; ring
  have hc : (Dg.R.m : ℝ) * (4 * Dg.R.k * scB x ε * Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 /
      Fintype.card S.A) ≤ S.cGform x ε / 40 := by
    have h1 := hs.odd_le
    have h0 : 0 ≤ (Dg.R.m : ℝ) * Dg.R.k * Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 := by positivity
    calc (Dg.R.m : ℝ) * (4 * Dg.R.k * scB x ε * Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2 /
          Fintype.card S.A) =
        (scB x ε / Fintype.card S.A) *
          (4 * ((Dg.R.m : ℝ) * Dg.R.k * Real.log (S.cutX x ε) * (orderOf κ : ℝ) ^ 2)) := by ring
      _ ≤ (scB x ε / Fintype.card S.A) * (x ^ (1 + 2 * ε) * (Fintype.card S.A : ℝ) ^ 2 / 40) := by
          gcongr; linarith
      _ = S.cGform x ε / 40 := by unfold Setting.cGform; field_simp
  rw [mul_add, mul_add]
  linarith

/-- **The stabiliser denominators cost at most `c_G/40`**: `2m·Σ_p v_p(D_Γ)·log p ≤ 2m·log D_Γ ≤ 2m(4|A|N_m)²`
(`GainErr.sum_padicValNat_mul_log_le`, `ErrOK.DΓ_le`, `[E:ℚ] = 4|A|`). -/
theorem errors_denom_le (hs : Dg.ErrSizes) (u : S.A) (ED : ErrData S Dg.R) (hED : Dg.ErrOK u ED) :
    2 * Dg.R.m * ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∪ ED.DΓ.primeFactors,
      (padicValNat p ED.DΓ : ℝ) * Real.log p ≤ S.cGform x ε / 40 := by
  have hx := hs.x_ge
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hmAN, -⟩ := hs.mAN_le
  have hA0 : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
  have hm0 : (0 : ℝ) ≤ Dg.R.m := Nat.cast_nonneg _
  have hP : ∀ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∪ ED.DΓ.primeFactors, p.Prime := by
    intro p hp
    rcases mem_union.1 hp with h | h
    · exact (GainErr.mem_inertPrimes (by linarith [GainErr.one_le_cutX (S := S) ε hx1]) h).1
    · exact Nat.prime_of_mem_primeFactors h
  have h1 := (GainErr.sum_padicValNat_mul_log_le hED.DΓ_pos hP).trans hED.DΓ_le
  have hE : (Module.finrank ℚ S.E : ℝ) = 4 * Fintype.card S.A := by
    rw [← IsGalois.card_aut_eq_finrank, S.card_gal]; push_cast; ring
  rw [hE] at h1
  have hb := hs.b_ge
  have hxe : 1 ≤ x ^ (1 + 2 * ε) := Real.one_le_rpow hx1 (by linarith [hs.ε_pos])
  have h2 : 64 * x ^ 810 ≤ x ^ (1 + 2 * ε) * scB x ε / 40 := by
    have h3 : x ^ 810 ≤ x ^ 811 := pow_le_pow_right₀ hx1 (by norm_num)
    have h4 : scB x ε ≤ x ^ (1 + 2 * ε) * scB x ε := le_mul_of_one_le_left (Real.exp_pos _).le hxe
    have h5 : (0 : ℝ) ≤ x ^ 810 := by positivity
    linarith
  calc 2 * (Dg.R.m : ℝ) * ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∪ ED.DΓ.primeFactors,
        (padicValNat p ED.DΓ : ℝ) * Real.log p ≤ 2 * Dg.R.m * (((Dg.R.N Dg.R.m : ℝ) * (4 * Fintype.card S.A)) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Fintype.card S.A * (32 * ((Dg.R.m : ℝ) * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2)) := by ring
    _ ≤ Fintype.card S.A * (32 * (2 * x ^ 810)) := by gcongr
    _ ≤ Fintype.card S.A * (x ^ (1 + 2 * ε) * scB x ε / 40) := by gcongr; linarith
    _ = S.cGform x ε / 40 := by unfold Setting.cGform; ring

/-- **The constant at `g₀, g₁` costs at most `c_G/40`**: `2m·c_E·f·(N_m² + m²η)·log(g₀g₁) ≤ 2720x^{807}·|A|·x^ε`,
as `c_E ≤ 10`, `f = 2|A|`, `N_m² + m²η ≤ 2x^{806}` and `log(g₀g₁) ≤ 17x^ε` (`Adm.log_g_mem`). -/
theorem errors_g_le (hA : Dg.Adm) (hs : Dg.ErrSizes) :
    2 * Dg.R.m * (Kg.cE * S.f * ((Dg.R.N Dg.R.m : ℝ) ^ 2 + (Dg.R.m : ℝ) ^ 2 * Dg.eta)) *
      Real.log (Dg.g₀ * Dg.g₁) ≤ S.cGform x ε / 40 := by
  have hx := hs.x_ge
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨-, e⟩ := hs.mAN_le
  obtain ⟨hlg0, hlg⟩ := hA.log_g_mem
  have hxe := hs.xε_ge
  have hA0 : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
  have hη := Dg.eta_nonneg
  have hf : (S.f : ℝ) = 2 * Fintype.card S.A := by rw [Setting.f_eq]; push_cast; ring
  have hNη : (Dg.R.N Dg.R.m : ℝ) ^ 2 + (Dg.R.m : ℝ) ^ 2 * Dg.eta ≤ 2 * x ^ 806 := by
    have h1 : (Dg.R.N Dg.R.m : ℝ) ^ 2 ≤ (x ^ 403) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hs.N_le 2
    have h2 : (Dg.R.m : ℝ) ^ 2 * Dg.eta ≤ (2 * x) ^ 2 * x ^ 410 := by
      gcongr
      · exact hs.m_le
      · linarith [hs.eta_le]
    have h3 : (2 * x) ^ 2 * x ^ 410 ≤ x ^ 806 := by
      have e1 : (2 * x) ^ 2 * x ^ 410 = 4 * x ^ 412 := by ring
      have h4 : 4 ≤ x ^ 394 := le_trans (by linarith) (le_self_pow₀ hx1 (by norm_num))
      have e2 : x ^ 806 = x ^ 412 * x ^ 394 := by ring
      rw [e1, e2, mul_comm 4]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have e3 : (x ^ 403) ^ 2 = x ^ 806 := by ring
    linarith
  have hb : 108800 * x ^ 806 ≤ x ^ ε * scB x ε := by
    have h1 := hs.b_ge
    have h2 : x ^ 806 ≤ x ^ 811 := pow_le_pow_right₀ hx1 (by norm_num)
    have h3 : scB x ε ≤ x ^ ε * scB x ε := le_mul_of_one_le_left (Real.exp_pos _).le (by linarith)
    have h4 : (0 : ℝ) ≤ x ^ 806 := by positivity
    linarith
  have hm2 := hs.m_le
  have hm0 : (0 : ℝ) ≤ Dg.R.m := Nat.cast_nonneg _
  have hcE := GainErr.Kg_le.1
  have hf' : (S.f : ℝ) ≤ 2 * Fintype.card S.A := hf.le
  have hNη0 : 0 ≤ (Dg.R.N Dg.R.m : ℝ) ^ 2 + (Dg.R.m : ℝ) ^ 2 * Dg.eta := by positivity
  have hlg00 : 0 ≤ Real.log (Dg.g₀ * Dg.g₁) := by linarith
  calc 2 * (Dg.R.m : ℝ) * (Kg.cE * S.f * ((Dg.R.N Dg.R.m : ℝ) ^ 2 + (Dg.R.m : ℝ) ^ 2 * Dg.eta)) *
        Real.log (Dg.g₀ * Dg.g₁) ≤ 2 * (2 * x) * (10 * (2 * Fintype.card S.A) * (2 * x ^ 806)) * (17 * x ^ ε) := by
        gcongr
    _ = (x * x ^ ε * Fintype.card S.A) * (2720 * x ^ 806) := by ring
    _ ≤ (x * x ^ ε * Fintype.card S.A) * (x ^ ε * scB x ε / 40) := by gcongr; linarith
    _ = S.cGform x ε / 40 := by unfold Setting.cGform; rw [e]; ring

/-- **The cut costs at most `c_G/40`**: `m·err_T·log T ≤ m·9|A|b·25mx^ε`, as `err_T ≤ 8|A|b + 4|A|x^{403} ≤ 9|A|b`
(`ErrOK.W_le`) and `0 ≤ log T ≤ Λ_u + log 2 ≤ 24mx^ε + 1` (`log_sharpT_le_lam`, `Adm.lam_bounds`); then
`ErrSizes.cut_le`. -/
theorem errors_cut_le (hA : Dg.Adm) (hs : Dg.ErrSizes) (u : S.A) (ED : ErrData S Dg.R) (hED : Dg.ErrOK u ED) :
    Dg.R.m * Dg.errT ED * Real.log (sharpT Dg u) ≤ S.cGform x ε / 40 := by
  have hx := hs.x_ge
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hA1 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have hb0 : 0 < scB x ε := Real.exp_pos _
  have hm1 := hs.m_ge
  have hm2 := hs.m_le
  have hxe := hs.xε_ge
  have hf : (S.f : ℝ) = 2 * Fintype.card S.A := by rw [Setting.f_eq]; push_cast; ring
  have hTT : (Dg.TT.card : ℝ) ≤ Fintype.card S.A := by exact_mod_cast card_le_univ Dg.TT
  have herr : Dg.errT ED ≤ 9 * Fintype.card S.A * scB x ε := by
    unfold errT
    have hW := hED.W_le
    have h1 : (S.f : ℝ) * Dg.R.N Dg.R.m ≤ 2 * Fintype.card S.A * x ^ 403 := by
      rw [hf]; exact mul_le_mul_of_nonneg_left hs.N_le (by positivity)
    have h2 : ((Dg.R.t : ℝ) + 1) * ((Dg.R.m : ℝ) + 1) ≤ (2 * x ^ 401) * (3 * x) := by
      have h3 : (1 : ℝ) ≤ x ^ 401 := one_le_pow₀ hx1
      gcongr
      · linarith [hs.t_le]
      · linarith
    have h4 : (Dg.TT.card : ℝ) * ((Dg.R.t : ℝ) + 1) * ((Dg.R.m : ℝ) + 1) / 4 ≤
        Fintype.card S.A * ((2 * x ^ 401) * (3 * x)) / 4 := by
      rw [mul_assoc]
      gcongr
    have e1 : (2 * x ^ 401) * (3 * x) = 6 * x ^ 402 := by ring
    have h5 : x ^ 402 ≤ x ^ 403 := pow_le_pow_right₀ hx1 (by norm_num)
    have h6 : 4 * x ^ 403 ≤ scB x ε := by
      have h7 : x ^ 403 ≤ x ^ 811 := pow_le_pow_right₀ hx1 (by norm_num)
      have h8 : (0 : ℝ) ≤ x ^ 403 := by positivity
      linarith [hs.b_ge]
    have h9 : Fintype.card S.A * (4 * x ^ 403) ≤ Fintype.card S.A * scB x ε :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    rw [e1] at h4
    have h10 : (Fintype.card S.A : ℝ) * x ^ 402 ≤ Fintype.card S.A * x ^ 403 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    nlinarith
  have hT0 : 0 ≤ Real.log (sharpT Dg u) :=
    Real.log_natCast_nonneg _
  have hT : Real.log (sharpT Dg u) ≤ 25 * Dg.R.m * x ^ ε := by
    have h1 := log_sharpT_le_lam hA u
    have h2 := (hA.lam_bounds u).2
    have hmm : (Dg.m : ℝ) = Dg.R.m := by exact_mod_cast Dg.hm
    rw [hmm] at h2
    have h3 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h4 : (1 : ℝ) ≤ Dg.R.m * x ^ ε := by nlinarith
    linarith
  have hc := hs.cut_le
  calc (Dg.R.m : ℝ) * Dg.errT ED * Real.log (sharpT Dg u) =
      Dg.R.m * (Dg.errT ED * Real.log (sharpT Dg u)) := by ring
    _ ≤ Dg.R.m * (9 * Fintype.card S.A * scB x ε * (25 * Dg.R.m * x ^ ε)) := by
        gcongr
    _ = (Fintype.card S.A * scB x ε) * (225 * (Dg.R.m : ℝ) ^ 2 * x ^ ε) := by ring
    _ ≤ (Fintype.card S.A * scB x ε) * (x ^ (1 + 2 * ε) / 40) := by gcongr; linarith
    _ = S.cGform x ε / 40 := by unfold Setting.cGform; ring

/-- **The errors** (M-G7d): `Σ_ϖ (Σ_j E_j(ϖ))·log N(ϖ) − m(Σ_t a_t)·log(g₀g₁) ≤ c_G/4`. By kinds
(`sum_Eexp_logN_eq`): the error data's two terms are at most `x^{1+3ε/2}|A|b ≤ c_G/40` each (`ErrOK.ν_le`,
`ErrOK.degD_le`), the inert and signal primes `3c_G/40` (`errors_inert_le`, with `TwoAdic` for the primes of odd
order), the stabiliser denominators, the constant at `g₀, g₁` and the cut `c_G/40` each (`errors_denom_le`,
`errors_g_le`, `errors_cut_le`): `8c_G/40 ≤ c_G/4`. Only the upper bound holds (and is used): the error data's bounds
are one-sided. -/
theorem errors_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) {e : ℕ} (h2 : S.TwoAdic κ e)
    (hB : GainBig ε x) (u : S.A) (ED : ErrData S Dg.R) (hED : Dg.ErrOK u ED) :
    ∑ ϖ ∈ Dg.primeSet ED, (∑ J, Dg.Eexp u ED J ϖ) * Dg.logN u ϖ -
      Dg.R.m * (∑ t ∈ Dg.TT, Dg.a t) * Real.log (Dg.g₀ * Dg.g₁) ≤ S.cGform x ε / 4 := by
  have hs := errSizes hA hB
  have h1 := errors_inert_le hA hF hs h2 u
  have h5 := errors_denom_le hs u ED hED
  have h6 := errors_g_le hA hs
  have h7 := errors_cut_le hA hs u ED hED
  have hν := hED.ν_le
  have hd := hED.degD_le
  have hU : x ^ (1 + 3 * ε / 2) * Fintype.card S.A * scB x ε ≤ S.cGform x ε / 40 := by
    have h := hs.half_le
    have hAb : 0 ≤ (Fintype.card S.A : ℝ) * scB x ε := by
      have := Real.exp_pos (scL x ε); positivity
    unfold Setting.cGform
    nlinarith
  have hcG : 0 ≤ S.cGform x ε := by
    unfold Setting.cGform
    have := Real.rpow_nonneg (by linarith [hs.x_ge] : (0 : ℝ) ≤ x) (1 + 2 * ε)
    have := Real.exp_pos (scL x ε)
    unfold scB
    positivity
  rw [sum_Eexp_logN_eq]
  linarith

/-- **The rounding** (M-G7d): `Σ_ϖ log N(ϖ) ≤ c_G/12`. By kinds (`sum_primeSet`): `Σ_{p ≤ X″} 2 log p ≤ 2X″ log X″
≤ 4x^{1+ε}|A|X′`, `Σ_{p ∣ D_Γ} 2 log p ≤ 2 log D_Γ ≤ 2(4|A|N_m)²` (`ErrOK.DΓ_le`), `3 log(g₀g₁) ≤ 51x^ε`,
`log T ≤ x` (`log_sharpT_le_lam`, `Adm.lam_add_log_two_le`) and `log d ≤ log N ≤ x^ε`; each group is at most
`c_G/48` as `b ≥ 10⁶x^{811}X′` (`ErrSizes.poly_le`). -/
theorem rounding_le (hA : Dg.Adm) (hB : GainBig ε x) (u : S.A) (ED : ErrData S Dg.R) (hED : Dg.ErrOK u ED) :
    ∑ ϖ ∈ Dg.primeSet ED, Dg.logN u ϖ ≤ S.cGform x ε / 12 := by
  classical
  have hs := errSizes hA hB
  have hx := hs.x_ge
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hX1 := GainErr.one_le_cutX (S := S) ε hx1
  obtain ⟨hmAN, e⟩ := hs.mAN_le
  have hA1 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have hb0 : 0 < scB x ε := Real.exp_pos _
  have hX0 : 0 < scX' x ε := Real.exp_pos _
  have hxe := hs.xε_ge
  have hm1 := hs.m_ge
  rw [Dg.sum_primeSet]
  simp only [logN, gs, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- the rational primes
  have hU : ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∪ ED.DΓ.primeFactors, 2 * Real.log p ≤
      ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), 2 * Real.log p +
        ∑ p ∈ ED.DΓ.primeFactors, 2 * Real.log p := by
    rw [← sum_union_inter]
    have : 0 ≤ ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∩ ED.DΓ.primeFactors, 2 * Real.log p :=
      sum_nonneg fun p _ => by have := Real.log_natCast_nonneg p; linarith
    linarith
  have hI : ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), Real.log p ≤
      S.cutX x ε * Real.log (S.cutX x ε) := sum_log_le_of_mem hX1 fun n hn =>
    ⟨(GainErr.mem_inertPrimes (by linarith) hn).1.one_lt.le, (GainErr.mem_inertPrimes (by linarith) hn).2.1⟩
  have hD : ∑ p ∈ ED.DΓ.primeFactors, Real.log p ≤ ((Dg.R.N Dg.R.m : ℝ) * (4 * Fintype.card S.A)) ^ 2 := by
    have hE : (Module.finrank ℚ S.E : ℝ) = 4 * Fintype.card S.A := by
      rw [← IsGalois.card_aut_eq_finrank, S.card_gal]; push_cast; ring
    have := hED.DΓ_le
    rw [hE] at this
    exact (GainErr.sum_log_primeFactors_le hED.DΓ_pos).trans this
  -- the specials
  have hg : Real.log (Dg.g₀ : ℝ) + Real.log Dg.g₁ ≤ 17 * x ^ ε := by
    rw [← Real.log_mul (Nat.cast_ne_zero.2 Dg.g₀_prime.ne_zero) (Nat.cast_ne_zero.2 Dg.g₁_prime.ne_zero)]
    exact hA.log_g_mem.2
  have hT : Real.log (sharpT Dg u) ≤ x := (log_sharpT_le_lam hA u).trans (hA.lam_add_log_two_le u)
  have hd : Real.log S.d ≤ x ^ ε := by
    have h1 : (S.d : ℝ) ≤ S.N := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) S.d_dvd_N
    have h2 : (0 : ℝ) < S.d := by exact_mod_cast (Fact.out : S.d.Prime).pos
    have := hA.log_N_le'
    linarith [Real.log_le_log h2 h1]
  -- the budget
  have hL := hs.logX_le
  have hbX := hs.poly_le
  have hb := hs.b_ge
  have hy1 : scB x ε ≤ x ^ ε * scB x ε := le_mul_of_one_le_left hb0.le (by linarith)
  have hcG : S.cGform x ε = x * x ^ ε * x ^ ε * Fintype.card S.A * scB x ε := by unfold Setting.cGform; rw [e]
  have b1 : 2 * (S.cutX x ε * Real.log (S.cutX x ε)) ≤ S.cGform x ε / 48 := by
    rw [hcG]
    have h1 : 192 * scX' x ε ≤ x ^ ε * scB x ε := by
      have : (192 : ℝ) ≤ 10 ^ 6 * x ^ 811 := by
        have : (1 : ℝ) ≤ x ^ 811 := one_le_pow₀ hx1
        linarith
      nlinarith
    calc 2 * (S.cutX x ε * Real.log (S.cutX x ε)) ≤ 2 * (S.cutX x ε * (2 * x ^ ε)) := by
          gcongr
      _ = (x * x ^ ε * Fintype.card S.A) * (4 * scX' x ε) := by unfold Setting.cutX scX'; ring
      _ ≤ (x * x ^ ε * Fintype.card S.A) * (x ^ ε * scB x ε / 48) := by gcongr; linarith
      _ = _ := by ring
  have b2 : 2 * ((Dg.R.N Dg.R.m : ℝ) * (4 * Fintype.card S.A)) ^ 2 ≤ S.cGform x ε / 48 := by
    rw [hcG]
    have hAN : (Fintype.card S.A : ℝ) * (Dg.R.N Dg.R.m : ℝ) ^ 2 ≤ 2 * x ^ 810 := by
      have : (Fintype.card S.A : ℝ) * (Dg.R.N Dg.R.m : ℝ) ^ 2 ≤
          (Dg.R.m : ℝ) * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 := by
        have h0 : (0 : ℝ) ≤ (Fintype.card S.A : ℝ) * (Dg.R.N Dg.R.m : ℝ) ^ 2 := by positivity
        nlinarith
      linarith
    have h1 : 3072 * x ^ 810 ≤ x * x ^ ε * x ^ ε * scB x ε := by
      have h2 : x ^ 810 ≤ x ^ 811 := pow_le_pow_right₀ hx1 (by norm_num)
      have h3 : scB x ε ≤ x * x ^ ε * x ^ ε * scB x ε := by
        have : (1 : ℝ) ≤ x * x ^ ε * x ^ ε := by
          have h4 : (1 : ℝ) ≤ x * x ^ ε := one_le_mul_of_one_le_of_one_le hx1 (by linarith)
          exact one_le_mul_of_one_le_of_one_le h4 (by linarith)
        exact le_mul_of_one_le_left hb0.le this
      have h5 : (0 : ℝ) ≤ x ^ 810 := by positivity
      linarith
    calc 2 * ((Dg.R.N Dg.R.m : ℝ) * (4 * Fintype.card S.A)) ^ 2 =
        Fintype.card S.A * (32 * ((Fintype.card S.A : ℝ) * (Dg.R.N Dg.R.m : ℝ) ^ 2)) := by ring
      _ ≤ Fintype.card S.A * (32 * (2 * x ^ 810)) := by gcongr
      _ ≤ Fintype.card S.A * (x * x ^ ε * x ^ ε * scB x ε / 48) := by gcongr; linarith
      _ = _ := by ring
  have b3 : 3 * (17 * x ^ ε) + x + x ^ ε ≤ S.cGform x ε / 48 := by
    rw [hcG]
    have h1 : 52 * x ^ ε + x ≤ 53 * (x * x ^ ε) := by nlinarith
    have h2 : 2544 ≤ scB x ε := by
      have : (1 : ℝ) ≤ x ^ 811 := one_le_pow₀ hx1
      linarith
    have h3 : 0 < x * x ^ ε := by positivity
    have h4 : x * x ^ ε * 2544 ≤ x * x ^ ε * (x ^ ε * Fintype.card S.A * scB x ε) := by
      refine mul_le_mul_of_nonneg_left ?_ h3.le
      have h5 : scB x ε ≤ x ^ ε * Fintype.card S.A * scB x ε := by
        have : (1 : ℝ) ≤ x ^ ε * Fintype.card S.A := one_le_mul_of_one_le_of_one_le (by linarith) hA1
        exact le_mul_of_one_le_left hb0.le this
      linarith
    nlinarith
  have hcG0 : 0 ≤ S.cGform x ε := by rw [hcG]; positivity
  have hlg0 : 0 ≤ Real.log (Dg.g₀ : ℝ) + Real.log Dg.g₁ := by
    have := Real.log_natCast_nonneg Dg.g₀
    have := Real.log_natCast_nonneg Dg.g₁
    linarith
  have hDs : ∑ p ∈ ED.DΓ.primeFactors, 2 * Real.log p ≤
      2 * ((Dg.R.N Dg.R.m : ℝ) * (4 * Fintype.card S.A)) ^ 2 := by rw [← mul_sum]; linarith
  have hIs : ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), 2 * Real.log p ≤
      2 * (S.cutX x ε * Real.log (S.cutX x ε)) := by rw [← mul_sum]; linarith
  linarith

/-- **The constant** (M-G7d): `0 ≤ c_G ≤ x^{4ε}·Σ_t a_t/8` at every admissible design: `Σ_t a_t ≥ |TT|·x·e^{x^ε}`
(`Adm.sum_a_ge`) and `|TT| ≥ δ₁|A|/2` (`Adm.TT_ge`), so `x^{4ε}Σ_t a_t/8 ≥ x^{1+31ε/8}|A|e^{x^ε}/16 ≥ c_G`, as
`x^{15ε/8} ≥ 16`. -/
theorem cG_le (hA : Dg.Adm) : 0 ≤ S.cGform x ε ∧ S.cGform x ε ≤ x ^ (4 * ε) * (∑ t ∈ Dg.TT, Dg.a t) / 8 := by
  have hx0 := hA.big.pos
  have hε := hA.big.ε_pos
  have hA0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
  have hb0 : 0 < scB x ε := Real.exp_pos _
  have h0 : 0 ≤ S.cGform x ε := by
    unfold Setting.cGform
    have := Real.rpow_nonneg hx0.le (1 + 2 * ε)
    positivity
  refine ⟨h0, ?_⟩
  have h1 := hA.sum_a_ge
  have h2 := hA.TT_ge
  have h16 : 16 ≤ x ^ (15 * ε / 8) := le_trans (by norm_num) (hA.big.le_rpow (by linarith))
  have e : x ^ (4 * ε) * scδ₁ x ε * x = x ^ (1 + 2 * ε) * x ^ (15 * ε / 8) := by
    unfold scδ₁
    rw [← Real.rpow_add hx0, mul_comm _ x, ← Real.rpow_one_add' hx0.le (by linarith), ← Real.rpow_add hx0]
    ring_nf
  have hbe : scB x ε = Real.exp (x ^ ε) := rfl
  have h4e : 0 ≤ x ^ (4 * ε) := Real.rpow_nonneg hx0.le _
  have h12 : 0 ≤ x ^ (1 + 2 * ε) := Real.rpow_nonneg hx0.le _
  calc S.cGform x ε = x ^ (1 + 2 * ε) * Fintype.card S.A * scB x ε := rfl
    _ ≤ x ^ (1 + 2 * ε) * (x ^ (15 * ε / 8) / 16) * Fintype.card S.A * scB x ε := by
        have h3 : 1 ≤ x ^ (15 * ε / 8) / 16 := by rw [le_div_iff₀ (by norm_num)]; linarith
        have h4 : 0 ≤ (Fintype.card S.A : ℝ) * scB x ε := by positivity
        calc x ^ (1 + 2 * ε) * Fintype.card S.A * scB x ε = x ^ (1 + 2 * ε) * 1 * (Fintype.card S.A * scB x ε) :=
              by ring
          _ ≤ x ^ (1 + 2 * ε) * (x ^ (15 * ε / 8) / 16) * (Fintype.card S.A * scB x ε) := by gcongr
          _ = _ := by ring
    _ = x ^ (4 * ε) * (scδ₁ x ε * Fintype.card S.A / 2) * (x * Real.exp (x ^ ε)) / 8 := by
        rw [← hbe, show x ^ (1 + 2 * ε) * (x ^ (15 * ε / 8) / 16) = x ^ (4 * ε) * scδ₁ x ε * x / 16 by
          rw [e]; ring]
        ring
    _ ≤ x ^ (4 * ε) * Dg.TT.card * (x * Real.exp (x ^ ε)) / 8 := by gcongr
    _ ≤ x ^ (4 * ε) * (∑ t ∈ Dg.TT, Dg.a t) / 8 := by
        rw [mul_assoc]
        gcongr

end SharpDesign

end

end ZetaBalance
