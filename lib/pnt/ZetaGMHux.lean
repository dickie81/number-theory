/-
# Huxley's count for `ζ` on `4/5 ≤ σ ≤ 11/12`, at the exponent `30/13`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `0 < ε ≤ 1/200` there is `C ≥ 0` with
`N(σ, T) ≤ C T^{(30/13 + 156ε)(1−σ)}(log T)^{12}` for `4/5 ≤ σ ≤ 11/12` and `T ≥ 2` (`nx_gmh`). It is
`ZetaHuxley`'s argument with the exponent `30/13` in place of `12/5`: the subintervals have height
`T₀ = U^{1−(30/13)(1−σ)−8ε}Λ^{2−2σ}` (`T0g`), the powers of the blocks lie in `[U^{10/13}, U^{15/13}]`, and the
detector has `X = ⌊U^{1/100}⌋`, `Y = U^{11/20}`, so that the blocks start at `U^{1/100}` (powers `m ≤ 77`,
`ZetaGMWin.choose_m100`) and `(2XN)² ≤ U^{15/13}`.

* `feas_gmh`: the `U`-exponent of `G_mΛ^{1/12}T₀^{5/12+ε}` at `Λ ≥ U^{10/13}` is at most
  `(145 − 190σ)/156 − (23/15)ε`, negative on `σ ≥ 4/5`.
* `count_bound_gmh`: `(4U/T₀)Λ^{2−2σ} = 4U^{(30/13)(1−σ)+8ε}` and `Λ^{2−2σ} ≤ U^{(30/13)(1−σ)}` for `Λ ≤ U^{15/13}`.
* `class_poly_gmh`, `window_classes_gmh`: as `ZetaHuxley.class_poly_huxley` and `window_classes_huxley`.
* `class3_bound_gmh`: the integral class at `Y = U^{11/20}`, `X ≤ U^{1/100}` carries `U^{107/50−(11/5)σ+ε}`, at most
  `U^{(30/13)(1−σ)+13ε}` for `σ ≤ 1`.
* `window_count_gmh`, `nx_gmh`: as `ZetaHuxley.window_count_huxley` and `nx_huxley`.

The file imports `ZetaHuxley.lean` and `ZetaGMWin.lean`.
-/
import ZetaHuxley
import ZetaGMWin

open Complex Real Filter Topology MeasureTheory

noncomputable section

namespace ZetaGMHux

open ShortWeil PsiOmega WeilForm WeilTest DirMean Finset InghamDensity ZetaIngham ZetaFourth ZetaKernel LinnikPower
  LinnikHuxley ZetaHuxley

/-! ### The exponents of one block -/

/-- `(4C(ε/308)⁴)^{77}`, the constant of the divisor bound for powers up to `77`. -/
def A77 (ε : ℝ) : ℝ := (4 * Cdiv (ε / 308) ^ 4) ^ 77

lemma one_le_A77 {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ A77 ε := by
  have hCd := one_le_Cdiv (ε := ε / 308) (by positivity) (by linarith)
  unfold A77
  exact one_le_pow₀ (by nlinarith [one_le_pow₀ (n := 4) hCd])

/-- The height of the subintervals for a power of length `Λ`: `T₀ = U^{(30σ−17)/13−8ε}Λ^{2−2σ}`, that is
`U^{1−(30/13)(1−σ)−8ε}Λ^{2−2σ}`. -/
def T0g (ε σ U Λ : ℝ) : ℝ := U ^ ((30 * σ - 17) / 13 - 8 * ε) * Λ ^ (2 - 2 * σ)

/-- `G_m(σ_b) ≤ (4C⁴)^{77}Λ^{1−2σ+ε}` for `m ≤ 77` (`LinnikHuxley.Gm_le` at `ε_d = ε/308`). -/
lemma Gm_le_A77 {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 77) {σ σb : ℝ}
    (hσ1 : σ ≤ 1) (hσb : σ ≤ σb) :
    Gm (ε / 308) P m σb ≤ A77 ε * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 - 2 * σ + ε) := by
  have hεd : 0 < ε / 308 := by positivity
  have hεd1 : ε / 308 ≤ 1 := by linarith
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ ((2 * P : ℕ) : ℝ) ^ m := one_le_pow₀ h2P
  have hCd := one_le_Cdiv hεd hεd1
  have hA1 : 1 ≤ 4 * Cdiv (ε / 308) ^ 4 := by nlinarith [one_le_pow₀ (n := 4) hCd]
  have hm' : (m : ℝ) ≤ 77 := by exact_mod_cast hm
  refine (Gm_le hεd hεd1 hP m hσ1 hσb).trans ?_
  unfold A77
  exact mul_le_mul (pow_le_pow_right₀ hA1 hm)
    (Real.rpow_le_rpow_of_exponent_le hΛ1 (by nlinarith)) (by positivity) (by positivity)

/-- **Feasibility of the power count** at height `T₀`: for `4/5 ≤ σ ≤ σ_b`, `Λ = (2P)^m ≥ U^{10/13}`, `m ≤ 77`,
`4K ≤ U^{ε/154}` and `12e(4C⁴)^{77}(KE + C_K) ≤ U^{ε/2}`, `2e·G_m(σ_b)(KE + C_KΛ^{1/12}(T₀ + 2)^{5/12+ε}) ≤ (4K)^{−2m}`
(`ZetaHuxley.feas_zeta` at these parameters; the `U`-exponent of `G_mΛ^{1/12}T₀^{5/12+ε}` is at most
`(145 − 190σ)/156 − (23/15)ε`).
Both terms are at most a constant times `U^{−(23/15)ε}`. -/
lemma feas_gmh {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {CK : ℝ} (hCK : 0 ≤ CK) {σ σb U : ℝ}
    (hσ : 4 / 5 ≤ σ) (hσb : σ ≤ σb) (hσ1 : σ ≤ 1) (hU : 1 ≤ U) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 77)
    (hΛ : U ^ (10 / 13 : ℝ) ≤ ((2 * P : ℕ) : ℝ) ^ m) {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ U ^ (ε / 154))
    (hfe : 12 * Real.exp 1 * A77 ε * (KE + CK) ≤ U ^ (ε / 2)) :
    2 * Real.exp 1 * Gm (ε / 308) P m σb * (KE + CK * (((2 * P : ℕ) : ℝ) ^ m) ^ (1 / 12 : ℝ) *
      (T0g ε σ U (((2 * P : ℕ) : ℝ) ^ m) + 2) ^ (5 / 12 + ε)) ≤ (1 / (4 * K)) ^ (2 * m) := by
  have hU0 : 0 < U := by linarith
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hKE := KE_pos
  have hA1 := one_le_A77 hε (by linarith)
  have hGm : Gm (ε / 308) P m σb ≤ A77 ε * Λ ^ (1 - 2 * σ + ε) := Gm_le_A77 hε (by linarith) hP hm hσ1 hσb
  set e : ℝ := 5 / 12 + ε with he
  have he0 : 0 ≤ e := by positivity
  set a : ℝ := (30 * σ - 17) / 13 - 8 * ε with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hT0def : T0g ε σ U Λ = U ^ a * Λ ^ (2 - 2 * σ) := rfl
  have hT01 : 1 ≤ T0g ε σ U Λ := by
    rw [hT0def]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hU ha0) (Real.one_le_rpow hΛ1 (by linarith))
  -- `(T₀ + 2)^e ≤ 3T₀^e`
  have hT02 : (T0g ε σ U Λ + 2) ^ e ≤ 3 * (T0g ε σ U Λ) ^ e := by
    have h3 : T0g ε σ U Λ + 2 ≤ 3 * T0g ε σ U Λ := by linarith
    calc (T0g ε σ U Λ + 2) ^ e ≤ (3 * T0g ε σ U Λ) ^ e := Real.rpow_le_rpow (by linarith) h3 he0
      _ = (3 : ℝ) ^ e * (T0g ε σ U Λ) ^ e := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 3 * (T0g ε σ U Λ) ^ e := by
          gcongr
          calc (3 : ℝ) ^ e ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 3 := Real.rpow_one 3
  have hT0e : (T0g ε σ U Λ) ^ e = U ^ (a * e) * Λ ^ ((2 - 2 * σ) * e) := by
    rw [hT0def, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hU0.le, ← Real.rpow_mul hΛ0.le]
  -- the `Λ`-exponent of the second term is negative
  set lam : ℝ := 1 - 2 * σ + ε + 1 / 12 + (2 - 2 * σ) * e with hlam
  have hle : (2 - 2 * σ) * e ≤ 1 / 2 * e := mul_le_mul_of_nonneg_right (by linarith) he0
  have hlam0 : lam ≤ 0 := by rw [hlam]; rw [he] at hle ⊢; linarith
  have hΛlam : Λ ^ lam ≤ U ^ (10 / 13 * lam) := by
    rw [Real.rpow_mul hU0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hΛ hlam0
  have hcomb : Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * Λ ^ ((2 - 2 * σ) * e) = Λ ^ lam := by
    rw [← Real.rpow_add hΛ0, ← Real.rpow_add hΛ0, hlam]
  have hUexp : a * e + 10 / 13 * lam ≤ -(23 / 15) * ε := by
    have key : a * e + 10 / 13 * lam = (145 - 190 * σ) / 156 + ε * ((10 * σ + 13) / 13 - 10 / 3) - 8 * ε ^ 2 := by
      rw [ha, he, hlam]; ring
    have h1 : ε * ((10 * σ + 13) / 13 - 10 / 3) ≤ ε * (-(23 / 15)) := mul_le_mul_of_nonneg_left (by linarith) hε.le
    have h2 : 0 ≤ ε ^ 2 := sq_nonneg ε
    rw [key]; linarith
  -- the first term
  have hT1 : Λ ^ (1 - 2 * σ + ε) ≤ U ^ (-(23 / 15) * ε) := by
    calc Λ ^ (1 - 2 * σ + ε) ≤ (U ^ (10 / 13 : ℝ)) ^ (1 - 2 * σ + ε) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hΛ (by linarith)
      _ = U ^ (10 / 13 * (1 - 2 * σ + ε)) := by rw [← Real.rpow_mul hU0.le]
      _ ≤ U ^ (-(23 / 15) * ε) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  -- the second term
  have hT2 : Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * (T0g ε σ U Λ) ^ e ≤ U ^ (-(23 / 15) * ε) := by
    rw [hT0e]
    calc Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * (U ^ (a * e) * Λ ^ ((2 - 2 * σ) * e))
        = U ^ (a * e) * (Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * Λ ^ ((2 - 2 * σ) * e)) := by ring
      _ = U ^ (a * e) * Λ ^ lam := by rw [hcomb]
      _ ≤ U ^ (a * e) * U ^ (10 / 13 * lam) := by gcongr
      _ = U ^ (a * e + 10 / 13 * lam) := by rw [← Real.rpow_add hU0]
      _ ≤ U ^ (-(23 / 15) * ε) := Real.rpow_le_rpow_of_exponent_le hU hUexp
  -- `(1/(4K))^{2m} ≥ U^{−ε}`
  have hR : U ^ (-ε) ≤ (1 / (4 * K)) ^ (2 * m) := by
    have hK0 : 0 < 4 * K := by linarith
    have h1 : U ^ (-(ε / 154)) ≤ 1 / (4 * K) := by
      rw [Real.rpow_neg hU0.le, one_div]
      exact inv_anti₀ hK0 hK
    have hm' : (m : ℝ) ≤ 77 := by exact_mod_cast hm
    calc U ^ (-ε) ≤ U ^ (-(ε / 154) * (2 * m : ℕ)) := by
          refine Real.rpow_le_rpow_of_exponent_le hU ?_
          push_cast; nlinarith
      _ = (U ^ (-(ε / 154))) ^ (2 * m) := by rw [Real.rpow_mul hU0.le, Real.rpow_natCast]
      _ ≤ (1 / (4 * K)) ^ (2 * m) := pow_le_pow_left₀ (by positivity) h1 _
  have hUe : U ^ (ε / 2) * U ^ (-(23 / 15) * ε) ≤ U ^ (-ε) := by
    rw [← Real.rpow_add hU0]
    exact Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hG0 : 0 ≤ Gm (ε / 308) P m σb := by
    have := one_le_Cdiv (ε := ε / 308) (by positivity) (by linarith); unfold Gm; positivity
  have hu0 : 0 ≤ U ^ (-(23 / 15) * ε) := by positivity
  have hfe' : 6 * Real.exp 1 * A77 ε * (KE + CK) * U ^ (-(23 / 15) * ε) ≤
      U ^ (ε / 2) * U ^ (-(23 / 15) * ε) / 2 := by
    have := mul_le_mul_of_nonneg_right hfe hu0
    linarith
  calc 2 * Real.exp 1 * Gm (ε / 308) P m σb * (KE + CK * Λ ^ (1 / 12 : ℝ) * (T0g ε σ U Λ + 2) ^ e)
      ≤ 2 * Real.exp 1 * (A77 ε * Λ ^ (1 - 2 * σ + ε)) *
          (KE + CK * Λ ^ (1 / 12 : ℝ) * (3 * (T0g ε σ U Λ) ^ e)) := by gcongr
    _ = 2 * Real.exp 1 * A77 ε * (KE * Λ ^ (1 - 2 * σ + ε) +
          3 * CK * (Λ ^ (1 - 2 * σ + ε) * Λ ^ (1 / 12 : ℝ) * (T0g ε σ U Λ) ^ e)) := by ring
    _ ≤ 2 * Real.exp 1 * A77 ε * (KE * U ^ (-(23 / 15) * ε) + 3 * CK * U ^ (-(23 / 15) * ε)) := by gcongr
    _ ≤ 6 * Real.exp 1 * A77 ε * (KE + CK) * U ^ (-(23 / 15) * ε) := by
        have : 0 ≤ Real.exp 1 * A77 ε * KE * U ^ (-(23 / 15) * ε) := by positivity
        linarith
    _ ≤ U ^ (ε / 2) * U ^ (-(23 / 15) * ε) / 2 := hfe'
    _ ≤ U ^ (-ε) := by
        have : 0 ≤ U ^ (ε / 2) * U ^ (-(23 / 15) * ε) := by positivity
        linarith
    _ ≤ (1 / (4 * K)) ^ (2 * m) := hR

/-- **The count of one block and one bin**: with `Λ = (2P)^m ≤ U^{15/13}`, `m ≤ 77`, `4K ≤ U^{ε/154}` and
`1 + KE(4 log U + 1) ≤ U^ε`, the `⌊4U/T₀⌋ + 1` subintervals of height `T₀` carry at most
`10e(4C⁴)^{77}U^{(30/13)(1−σ)+12ε}` in all: `(4U/T₀)Λ^{2−2σ} = 4U^{(30/13)(1−σ)+8ε}` and
`Λ^{2−2σ} ≤ U^{(30/13)(1−σ)}` (`ZetaHuxley.count_bound_zeta` at these parameters). -/
lemma count_bound_gmh {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {σ σb U : ℝ}
    (hσb : σ ≤ σb) (hσ1 : σ ≤ 1) (hU : 1 ≤ U) {P m : ℕ} (hP : 1 ≤ P) (hm : m ≤ 77)
    (hΛ : ((2 * P : ℕ) : ℝ) ^ m ≤ U ^ (15 / 13 : ℝ)) {K : ℝ} (hK1 : 1 ≤ K) (hK : 4 * K ≤ U ^ (ε / 154))
    (hlog : 1 + KE * (4 * Real.log U + 1) ≤ U ^ ε) :
    ((⌊4 * U / T0g ε σ U (((2 * P : ℕ) : ℝ) ^ m)⌋₊ + 1 : ℕ) : ℝ) *
      (2 * Real.exp 1 * Gm (ε / 308) P m σb * ((2 * P : ℕ) : ℝ) ^ m *
        (1 + KE * (2 * Real.log (((2 * P : ℕ) : ℝ) ^ m) + 1)) / (1 / (4 * K)) ^ (2 * m))
      ≤ 10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε) := by
  have hU0 : 0 < U := by linarith
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hKE := KE_pos
  have hA1 := one_le_A77 hε (by linarith)
  have hGm : Gm (ε / 308) P m σb ≤ A77 ε * Λ ^ (1 - 2 * σ + ε) := Gm_le_A77 hε (by linarith) hP hm hσ1 hσb
  have hG0 : 0 ≤ Gm (ε / 308) P m σb := by
    have := one_le_Cdiv (ε := ε / 308) (by positivity) (by linarith); unfold Gm; positivity
  set a : ℝ := (30 * σ - 17) / 13 - 8 * ε with ha
  set T₀ := T0g ε σ U Λ with hT₀
  have hT0def : T₀ = U ^ a * Λ ^ (2 - 2 * σ) := rfl
  have hT₀pos : 0 < T₀ := by rw [hT0def]; positivity
  have hLc : ((⌊4 * U / T₀⌋₊ + 1 : ℕ) : ℝ) ≤ 4 * U / T₀ + 1 := by
    push_cast; linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 4 * U / T₀)]
  -- the logarithm and the power of `4K`
  have hlogΛ : Real.log Λ ≤ 2 * Real.log U := by
    have h1 : Real.log Λ ≤ Real.log (U ^ (15 / 13 : ℝ)) := Real.log_le_log hΛ0 hΛ
    rw [Real.log_rpow hU0] at h1
    have hl : 0 ≤ Real.log U := Real.log_nonneg hU
    nlinarith
  have hL : 1 + KE * (2 * Real.log Λ + 1) ≤ U ^ ε := by
    have h1 : KE * (2 * Real.log Λ + 1) ≤ KE * (4 * Real.log U + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hKE.le
    linarith
  have hL0 : 0 ≤ 1 + KE * (2 * Real.log Λ + 1) := by have := Real.log_nonneg hΛ1; positivity
  have hK0 : 0 < 4 * K := by linarith
  have h4K : (4 * K) ^ (2 * m) ≤ U ^ ε := by
    have hm' : (m : ℝ) ≤ 77 := by exact_mod_cast hm
    calc (4 * K) ^ (2 * m) ≤ (U ^ (ε / 154)) ^ (2 * m) := pow_le_pow_left₀ hK0.le hK _
      _ = U ^ (ε / 154 * (2 * m : ℕ)) := by rw [Real.rpow_mul hU0.le, Real.rpow_natCast]
      _ ≤ U ^ ε := Real.rpow_le_rpow_of_exponent_le hU (by push_cast; nlinarith)
  -- the powers of `Λ`
  have hsplitΛ : Λ ^ (1 - 2 * σ + ε) * Λ = Λ ^ (2 - 2 * σ) * Λ ^ ε := by
    rw [← Real.rpow_add_one hΛ0.ne', ← Real.rpow_add hΛ0]; congr 1; ring
  have hΛε : Λ ^ ε ≤ U ^ (2 * ε) := by
    calc Λ ^ ε ≤ (U ^ (15 / 13 : ℝ)) ^ ε := Real.rpow_le_rpow hΛ0.le hΛ hε.le
      _ = U ^ (15 / 13 * ε) := by rw [← Real.rpow_mul hU0.le]
      _ ≤ U ^ (2 * ε) := Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hΛ2 : Λ ^ (2 - 2 * σ) ≤ U ^ (30 / 13 * (1 - σ) + 8 * ε) := by
    calc Λ ^ (2 - 2 * σ) ≤ (U ^ (15 / 13 : ℝ)) ^ (2 - 2 * σ) := Real.rpow_le_rpow hΛ0.le hΛ (by linarith)
      _ = U ^ (15 / 13 * (2 - 2 * σ)) := by rw [← Real.rpow_mul hU0.le]
      _ ≤ U ^ (30 / 13 * (1 - σ) + 8 * ε) := Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hUT : 4 * U / T₀ * Λ ^ (2 - 2 * σ) = 4 * U ^ (30 / 13 * (1 - σ) + 8 * ε) := by
    have e1 : 30 / 13 * (1 - σ) + 8 * ε = 1 - a := by rw [ha]; ring
    have hΛp : Λ ^ (2 - 2 * σ) ≠ 0 := by positivity
    have hUa : U ^ a ≠ 0 := by positivity
    rw [e1, Real.rpow_sub hU0, Real.rpow_one, hT0def]
    field_simp
  have hpow : ∀ x : ℝ, U ^ ε * U ^ ε * (U ^ x * U ^ (2 * ε)) = U ^ (x + 4 * ε) := by
    intro x
    rw [← Real.rpow_add hU0, ← Real.rpow_add hU0, ← Real.rpow_add hU0]; congr 1; ring
  have e2 : 30 / 13 * (1 - σ) + 8 * ε + 4 * ε = 30 / 13 * (1 - σ) + 12 * ε := by ring
  have hUε : 0 ≤ U ^ ε := by positivity
  calc ((⌊4 * U / T₀⌋₊ + 1 : ℕ) : ℝ) *
        (2 * Real.exp 1 * Gm (ε / 308) P m σb * Λ * (1 + KE * (2 * Real.log Λ + 1)) / (1 / (4 * K)) ^ (2 * m))
      = ((⌊4 * U / T₀⌋₊ + 1 : ℕ) : ℝ) *
          (2 * Real.exp 1 * Gm (ε / 308) P m σb * Λ * (1 + KE * (2 * Real.log Λ + 1)) * (4 * K) ^ (2 * m)) := by
        rw [one_div, inv_pow, div_inv_eq_mul]
    _ ≤ (4 * U / T₀ + 1) * (2 * Real.exp 1 * (A77 ε * Λ ^ (1 - 2 * σ + ε)) * Λ * U ^ ε * U ^ ε) := by
        gcongr
    _ = 2 * Real.exp 1 * A77 ε * (U ^ ε * U ^ ε * (4 * U / T₀ * (Λ ^ (2 - 2 * σ) * Λ ^ ε)) +
          U ^ ε * U ^ ε * (Λ ^ (2 - 2 * σ) * Λ ^ ε)) := by
        rw [← hsplitΛ]; ring
    _ = 2 * Real.exp 1 * A77 ε * (U ^ ε * U ^ ε * ((4 * U / T₀ * Λ ^ (2 - 2 * σ)) * Λ ^ ε) +
          U ^ ε * U ^ ε * (Λ ^ (2 - 2 * σ) * Λ ^ ε)) := by ring
    _ ≤ 2 * Real.exp 1 * A77 ε * (U ^ ε * U ^ ε * ((4 * U ^ (30 / 13 * (1 - σ) + 8 * ε)) * U ^ (2 * ε)) +
          U ^ ε * U ^ ε * (U ^ (30 / 13 * (1 - σ) + 8 * ε) * U ^ (2 * ε))) := by
        rw [hUT]; gcongr
    _ = 2 * Real.exp 1 * A77 ε * (4 * (U ^ ε * U ^ ε * (U ^ (30 / 13 * (1 - σ) + 8 * ε) * U ^ (2 * ε))) +
          U ^ ε * U ^ ε * (U ^ (30 / 13 * (1 - σ) + 8 * ε) * U ^ (2 * ε))) := by ring
    _ = 10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε) := by
        rw [hpow, e2]; ring

/-! ### The polynomial classes on `3/4 ≤ σ ≤ 1` -/

/-- **The polynomial class with powers at well-spaced heights.** Points `β_r + iγ_r`, `σ ≤ β_r < 1`, with
1-separated heights `|γ_r| ≤ 2U`, at which `|P_b(β_r, γ_r)| ≥ ¼` (`|b_j| ≤ d(j)`), number at most
`12K·10e(4C⁴)^{77}U^{(30/13)(1−σ)+12ε}`, `K = ⌊log₂ N⌋ + 1`, for `4/5 ≤ σ ≤ 1`, `U^{1/100} ≤ 2X` and
`(2XN)² ≤ U^{15/13}` (`ZetaHuxley.class_poly_huxley` at these parameters): some dyadic block is at least `1/(4K)`;
bins of width `1/48` in `β`; in each block a power `m` with `(2P)^m ≥ U^{10/13}` (`ZetaGMWin.choose_m100`), at most
`U^{15/13}` long; subintervals of height `T₀`; and `ZetaKernel.power_count_pts` with `feas_gmh` and
`count_bound_gmh`. -/
theorem class_poly_gmh {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ Λ : ℝ, 1 ≤ Λ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 24 →
      ‖∑' n, kTerm χ₁ Λ z n‖ ≤ KE * Λ * Real.exp (-|z.im|) + CK * Λ ^ (1 / 12 : ℝ) * (|z.im| + 2) ^ (5 / 12 + ε))
    (b : ℕ → ℂ) (hb : ∀ j, ‖b j‖ ≤ (j.divisors.card : ℝ)) {σ U : ℝ} (hσ : 4 / 5 ≤ σ) (hσ1 : σ ≤ 1)
    (hU : 1 < U) {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hXU : U ^ (1 / 100 : ℝ) ≤ 2 * X)
    (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ U ^ (ε / 154))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ U ^ (15 / 13 : ℝ))
    (hfe : 12 * Real.exp 1 * A77 ε * (KE + CK) ≤ U ^ (ε / 2))
    (hlog : 1 + KE * (4 * Real.log U + 1) ≤ U ^ ε)
    {ι : Type*} (Rs : Finset ι) (β γ : ι → ℝ) (hβ : ∀ r ∈ Rs, σ ≤ β r ∧ β r < 1)
    (hγ : ∀ r ∈ Rs, |γ r| ≤ 2 * U) (hsep : ∀ r ∈ Rs, ∀ r' ∈ Rs, r ≠ r' → 1 ≤ |γ r - γ r'|)
    (hbig : ∀ r ∈ Rs, 1 / 4 ≤ ‖Pv b X N (β r) (γ r)‖) :
    (Rs.card : ℝ) ≤ 12 * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
      (10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε)) := by
  classical
  set K := Nat.log 2 N + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set V : ℝ := 1 / (4 * (K : ℝ)) with hV
  have hV0 : 0 < V := by positivity
  set B := 10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε) with hB
  have hU0 : 0 < U := by linarith
  -- some dyadic block of each point is at least `V`
  have hlarge : ∀ r ∈ Rs, ∃ k ∈ range K, V ≤ ‖Fkb b X N k (β r) (γ r)‖ := by
    intro r hr
    by_contra hcon
    push Not at hcon
    have h1 := hbig r hr
    rw [Pv_eq_blocks b X N hX] at h1
    have h2 : ∑ k ∈ range K, ‖Fkb b X N k (β r) (γ r)‖ < ∑ _k ∈ range K, V :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩ fun k hk => hcon k hk
    rw [sum_const, card_range, nsmul_eq_mul] at h2
    have h3 : (K : ℝ) * V = 1 / 4 := by rw [hV]; field_simp
    linarith [(norm_sum_le (range K) fun k => Fkb b X N k (β r) (γ r)).trans_lt (h3 ▸ h2)]
  set Ck : ℕ → ℕ → Finset ι := fun k j =>
    Rs.filter fun r => V ≤ ‖Fkb b X N k (β r) (γ r)‖ ∧ ⌊48 * (β r - σ)⌋₊ = j with hCkdef
  have hsub : Rs ⊆ (range K).biUnion fun k => (range 12).biUnion fun j => Ck k j := by
    intro r hr
    obtain ⟨k, hk, hbigk⟩ := hlarge r hr
    have h1 := hβ r hr
    have hj : ⌊48 * (β r - σ)⌋₊ < 12 := by
      rw [Nat.floor_lt (by linarith)]
      push_cast
      linarith
    exact mem_biUnion.2 ⟨k, hk, mem_biUnion.2 ⟨_, mem_range.2 hj, mem_filter.2 ⟨hr, hbigk, rfl⟩⟩⟩
  have hCk : ∀ k ∈ range K, ∀ j ∈ range 12, ((Ck k j).card : ℝ) ≤ B := by
    intro k hk j _
    set P := 2 ^ k * X with hPdef
    have hP : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hPN : P ≤ X * N := by
      rw [hPdef, mul_comm X N]; exact Nat.mul_le_mul_right X (pow_blk_le (mem_range.1 hk) hN)
    have hXP : X ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left X (by positivity)
    have hSsub : (Ioc X (X * N)).filter (fun j => blk X j = k) ⊆ Ioc P (2 * P) := block_sub hX
    have h2Px : U ^ (1 / 100 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by
      have : (2 * (X : ℝ)) ≤ ((2 * P : ℕ) : ℝ) := by
        have h' : ((2 * X : ℕ) : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * X ≤ 2 * P)
        push_cast at h' ⊢; linarith
      linarith
    obtain ⟨m, hm1, hm77, hΛlo, hΛhi⟩ := ZetaGMWin.choose_m100 hU (by norm_num : (0 : ℝ) < 10 / 13) (by norm_num) h2Px
    set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛdef
    have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * P))
    have hΛ : Λ ≤ U ^ (15 / 13 : ℝ) := by
      refine hΛhi.trans (max_le ?_ ?_)
      · have h2 : ((2 * P : ℕ) : ℝ) ≤ 2 * ((X * N : ℕ) : ℝ) := by
          have h' : ((2 * P : ℕ) : ℝ) ≤ ((2 * (X * N) : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 2 * P ≤ 2 * (X * N))
          push_cast at h' ⊢; linarith
        calc ((2 * P : ℕ) : ℝ) ^ 2 ≤ (2 * ((X * N : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          _ ≤ U ^ (15 / 13 : ℝ) := hXN
      · rw [show 3 * (10 / 13 : ℝ) / 2 = 15 / 13 by norm_num]
    set σb : ℝ := σ + j / 48 with hσb
    have hσσb : σ ≤ σb := by
      have : (0 : ℝ) ≤ (j : ℝ) / 48 := by positivity
      rw [hσb]; linarith
    have hbin : ∀ r ∈ Ck k j, σb ≤ β r ∧ β r < σb + 1 / 48 := by
      intro r hr
      obtain ⟨hrR, -, hbj⟩ := mem_filter.1 hr
      have h0 : 0 ≤ 48 * (β r - σ) := by have := (hβ r hrR).1; linarith
      have h1 : ((⌊48 * (β r - σ)⌋₊ : ℕ) : ℝ) ≤ 48 * (β r - σ) := Nat.floor_le h0
      have h2 : 48 * (β r - σ) < ((⌊48 * (β r - σ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hbj] at h1 h2
      rw [hσb]
      constructor <;> linarith
    -- the subintervals of height `T₀`
    set T₀ := T0g ε σ U Λ with hT₀
    have hT₀pos : 0 < T₀ := by rw [hT₀, T0g]; positivity
    set D : ℕ → Finset ι := fun l => (Ck k j).filter fun r => ⌊(γ r + 2 * U) / T₀⌋₊ = l with hD
    have hsubD : Ck k j ⊆ (range (⌊4 * U / T₀⌋₊ + 1)).biUnion D := by
      intro r hr
      have hγr := hγ r (mem_filter.1 hr).1
      refine mem_biUnion.2 ⟨⌊(γ r + 2 * U) / T₀⌋₊, mem_range.2 ?_, mem_filter.2 ⟨hr, rfl⟩⟩
      rw [Nat.lt_succ_iff]
      exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith [(abs_le.1 hγr).2]) hT₀pos.le)
    have hDl : ∀ l ∈ range (⌊4 * U / T₀⌋₊ + 1), ((D l).card : ℝ) ≤ 2 * Real.exp 1 * Gm (ε / 308) P m σb * Λ *
        (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m) := by
      intro l _
      have hDsub : ∀ r ∈ D l, r ∈ Ck k j := fun r hr => (mem_filter.1 hr).1
      have hT : ∀ r ∈ D l, ∀ r' ∈ D l, |γ r - γ r'| ≤ T₀ := by
        intro r hr r' hr'
        have hl1 := (mem_filter.1 hr).2
        have hl2 := (mem_filter.1 hr').2
        have g1 := hγ r (mem_filter.1 (hDsub r hr)).1
        have g2 := hγ r' (mem_filter.1 (hDsub r' hr')).1
        have a1 : 0 ≤ (γ r + 2 * U) / T₀ := div_nonneg (by linarith [(abs_le.1 g1).1]) hT₀pos.le
        have a2 : 0 ≤ (γ r' + 2 * U) / T₀ := div_nonneg (by linarith [(abs_le.1 g2).1]) hT₀pos.le
        have f1 := Nat.floor_le a1
        have f2 := Nat.lt_floor_add_one ((γ r + 2 * U) / T₀)
        have f3 := Nat.floor_le a2
        have f4 := Nat.lt_floor_add_one ((γ r' + 2 * U) / T₀)
        rw [hl1] at f1 f2
        rw [hl2] at f3 f4
        rw [le_div_iff₀ hT₀pos] at f1 f3
        rw [div_lt_iff₀ hT₀pos] at f2 f4
        rw [abs_le]; constructor <;> nlinarith
      refine power_count_pts hP hSsub (c := b) (fun i _ => hb i) hm1 (σb := σb) (by linarith) β γ
        (fun r hr => hbin r (hDsub r hr))
        (fun r hr r' hr' hne => hsep r (mem_filter.1 (hDsub r hr)).1 r' (mem_filter.1 (hDsub r' hr')).1 hne)
        hT hV0 (fun r hr => by rw [← Fkb_eq_pv]; exact (mem_filter.1 (hDsub r hr)).2.1)
        (εd := ε / 308) (by positivity) (by linarith) (B := CK * Λ ^ (1 / 12 : ℝ) * (T₀ + 2) ^ (5 / 12 + ε))
        (by positivity) (fun z hz0 hz1 hzT => ?_) ?_
      · refine (hCK Λ hΛ1 z hz0 hz1).trans ?_
        gcongr
      · exact feas_gmh hε hε1 hCK0 hσ hσσb hσ1 hU.le hP hm77 hΛlo hK1 hK hfe
    calc ((Ck k j).card : ℝ) ≤ ((range (⌊4 * U / T₀⌋₊ + 1)).biUnion D).card := by
          exact_mod_cast card_le_card hsubD
      _ ≤ ∑ l ∈ range (⌊4 * U / T₀⌋₊ + 1), ((D l).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _l ∈ range (⌊4 * U / T₀⌋₊ + 1),
            (2 * Real.exp 1 * Gm (ε / 308) P m σb * Λ * (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m)) :=
          sum_le_sum hDl
      _ = ((⌊4 * U / T₀⌋₊ + 1 : ℕ) : ℝ) *
            (2 * Real.exp 1 * Gm (ε / 308) P m σb * Λ * (1 + KE * (2 * Real.log Λ + 1)) / V ^ (2 * m)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ B := count_bound_gmh hε hε1 hσσb hσ1 hU.le hP hm77 hΛ hK1 hK hlog
  calc (Rs.card : ℝ) ≤ ((range K).biUnion fun k => (range 12).biUnion fun j => Ck k j).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ k ∈ range K, (((range 12).biUnion fun j => Ck k j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range 12, ((Ck k j).card : ℝ) := by
        gcongr with k hk; exact_mod_cast card_biUnion_le
    _ ≤ ∑ k ∈ range K, ∑ j ∈ range 12, B := by
        gcongr with k hk j hj; exact hCk k hk j hj
    _ = 12 * (K : ℝ) * B := by simp only [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-! ### One window -/

/-- **The three classes in one window at the exponent `30/13`**: `ZetaHuxley.trichotomy7`, then
`class_poly_gmh` for the two polynomial classes and `class3_count_small` (at `δ = 1/4`) for the integral class, over
the parity classes of the unit windows (`InghamDensity.card_le_of_classes`). -/
theorem window_classes_gmh {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ Λ : ℝ, 1 ≤ Λ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 24 →
      ‖∑' n, kTerm χ₁ Λ z n‖ ≤ KE * Λ * Real.exp (-|z.im|) + CK * Λ ^ (1 / 12 : ℝ) * (|z.im| + 2) ^ (5 / 12 + ε))
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + ε))
    {σ U Y : ℝ} (hσ : 4 / 5 ≤ σ) (hσ1 : σ ≤ 1) (hU : 2 ≤ U) (hY : 8 ≤ Y) (hUY : 36864 * U ≤ Y ^ 7)
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) (hM : 22 * Y * Real.log Y ≤ ((X * N : ℕ) : ℝ))
    (hXU : U ^ (1 / 100 : ℝ) ≤ 2 * X) (hK : 4 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ U ^ (ε / 154))
    (hXN : (2 * ((X * N : ℕ) : ℝ)) ^ 2 ≤ U ^ (15 / 13 : ℝ))
    (hfe : 12 * Real.exp 1 * A77 ε * (KE + CK) ≤ U ^ (ε / 2))
    (hlog : 1 + KE * (4 * Real.log U + 1) ≤ U ^ ε)
    (Z : Finset (ZeroIdx (sqF Xi))) (hZ : ∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) :
    (Z.card : ℝ) ≤ 2 * Kloc (2 * U + 1) * (2 * (12 * ((Nat.log 2 N + 1 : ℕ) : ℝ) *
        (10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε))) +
      27 * (3 * KG * Y ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + ε))) := by
  classical
  have hU0 : 0 ≤ U := by linarith
  have hY0 : 0 < Y := by linarith
  set B1 := 12 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * (10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε))
    with hB1
  set B3 := 27 * (3 * KG * Y ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + ε)) with hB3
  have hB10 : 0 ≤ B1 := by have := one_le_A77 hε (by linarith); positivity
  have hB30 : 0 ≤ B3 := by have := KG_pos; positivity
  have htri : ∀ i ∈ Z, 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖ ∨ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
      ∨ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖ := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hZ i hi
    exact trichotomy7 hX hN hY hU hUY hM (by linarith) (βs_lt_one i) (by rw [abs_γs]; exact h1)
      (by rw [abs_γs]; exact h2) (DetectCore.zeta_βsγs i)
  set Z1 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖
  set Z2 := Z.filter fun i => 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖
  set Z3 := Z.filter fun i => U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖
  have hcover : Z ⊆ Z1 ∪ Z2 ∪ Z3 := by
    intro i hi
    rcases htri i hi with h | h | h
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hi, h⟩))
    · exact mem_union_right _ (mem_filter.2 ⟨hi, h⟩)
  have hpoly : ∀ b : ℕ → ℂ, (∀ j, ‖b j‖ ≤ (j.divisors.card : ℝ)) → ∀ (C : Finset ℕ) (rep : ℕ → ZeroIdx (sqF Xi)),
      (∀ n ∈ C, ∀ m ∈ C, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n) →
      (∀ n ∈ C, (n : ℝ) ≤ |(tau (rep n)).re| ∧ |(tau (rep n)).re| < n + 1) →
      (∀ n ∈ C, |(tau (rep n)).re| ≤ 2 * U ∧ (σ ≤ βs (rep n) ∧ 1 / 4 ≤ ‖Pv b X N (βs (rep n)) (γs (rep n))‖)) →
      (C.card : ℝ) ≤ B1 := by
    intro b hb C rep hC hwin hdet
    exact class_poly_gmh hε hε1 hCK0 hCK b hb hσ hσ1 (by linarith) hX hN hXU hK hXN hfe hlog C
      (fun n => βs (rep n)) (fun n => γs (rep n)) (fun n hn => ⟨(hdet n hn).2.1, βs_lt_one _⟩)
      (fun n hn => by rw [abs_γs]; exact (hdet n hn).1) (sep_of_windows C rep hC hwin)
      (fun n hn => (hdet n hn).2.2)
  have hZ1 : (Z1.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b1 X Y) X N (βs i) (γs i)‖) Z1
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet => hpoly (b1 X Y) (norm_b1_le X hY0) C rep hC hwin hdet
  have hZ2 : (Z2.card : ℝ) ≤ 2 * B1 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ 1 / 4 ≤ ‖Pv (b2 X Y) X N (βs i) (γs i)‖) Z2
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB10 fun C rep hC hwin hdet => hpoly (b2 X Y) (norm_b2_le X hY0) C rep hC hwin hdet
  have hZ3 : (Z3.card : ℝ) ≤ 2 * B3 * Kloc (2 * U + 1) :=
    card_le_of_classes hU0 (fun i => σ ≤ βs i ∧ U / 4 ≤ ‖Iv X Y ((βs i : ℂ) + γs i * I)‖) Z3
      (fun i hi => ⟨(hZ i (mem_filter.1 hi).1).2.1, (hZ i (mem_filter.1 hi).1).2.2, (mem_filter.1 hi).2⟩)
      hB30 fun C rep hC hwin hdet =>
        class3_count_small hε.le (by linarith) hC₄ h4 hX (δ := 1 / 4) (by norm_num) (by linarith) hU
          (by linarith) C rep hC hwin hdet
  calc (Z.card : ℝ) ≤ ((Z1 ∪ Z2 ∪ Z3).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ Z1.card + Z2.card + Z3.card := by
        have h1 := card_union_le (Z1 ∪ Z2) Z3
        have h2 := card_union_le Z1 Z2
        exact_mod_cast h1.trans (by omega)
    _ ≤ 2 * B1 * Kloc (2 * U + 1) + 2 * B1 * Kloc (2 * U + 1) + 2 * B3 * Kloc (2 * U + 1) := by
        linarith
    _ = 2 * Kloc (2 * U + 1) * (2 * B1 + B3) := by ring


/-- **The integral class at `Y = U^{11/20}`, `X ≤ U^{1/100}`**: `27(12KG)⁴Y^{2−4σ}X⁴C₄(2U + 2)^{1+ε} ≤
243(12KG)⁴C₄U^{(30/13)(1−σ)+13ε}` for `σ ≤ 1`: the exponent is `(11/5)(½ − σ) + 1/25 + 1 + ε`, and
`(30/13)(1 − σ) − (107/50 − (11/5)σ) = 109/650 − (7/65)σ > 0`. -/
lemma class3_bound_gmh {ε C₄ σ U : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) (hC₄ : 0 ≤ C₄) (hσ1 : σ ≤ 1)
    (hU : 8 ≤ U) {X : ℕ} (hXU : (X : ℝ) ≤ U ^ (1 / 100 : ℝ)) :
    27 * (3 * KG * (U ^ (11 / 20 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + ε))
      ≤ 243 * (12 * KG) ^ 4 * C₄ * U ^ (30 / 13 * (1 - σ) + 13 * ε) := by
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hKG := KG_pos
  have hY : ((U ^ (11 / 20 : ℝ)) ^ (1 / 2 - σ)) ^ 4 = U ^ (11 / 5 * (1 / 2 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le, ← Real.rpow_mul hU0.le]; congr 1; push_cast; ring
  have hX4 : (X : ℝ) ^ 4 ≤ U ^ (1 / 25 : ℝ) := by
    calc (X : ℝ) ^ 4 ≤ (U ^ (1 / 100 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg X) hXU 4
      _ = U ^ (1 / 25 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
  have hM : (2 * U + 2) ^ (1 + ε) ≤ 9 * U ^ (1 + ε) := by
    calc (2 * U + 2) ^ (1 + ε) ≤ (3 * U) ^ (1 + ε) := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (3 : ℝ) ^ (1 + ε) * U ^ (1 + ε) := Real.mul_rpow (by norm_num) hU0.le
      _ ≤ 9 * U ^ (1 + ε) := by
          gcongr
          calc (3 : ℝ) ^ (1 + ε) ≤ 3 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 9 := by norm_num
  have hexp : 11 / 5 * (1 / 2 - σ) + 1 / 25 + (1 + ε) ≤ 30 / 13 * (1 - σ) + 13 * ε := by linarith
  calc 27 * (3 * KG * (U ^ (11 / 20 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * (X : ℝ) ^ 4 * (C₄ * (2 * U + 2) ^ (1 + ε))
      = 27 * (12 * KG) ^ 4 * C₄ * (((U ^ (11 / 20 : ℝ)) ^ (1 / 2 - σ)) ^ 4 * (X : ℝ) ^ 4 *
          (2 * U + 2) ^ (1 + ε)) := by
        ring
    _ ≤ 27 * (12 * KG) ^ 4 * C₄ * (U ^ (11 / 5 * (1 / 2 - σ)) * U ^ (1 / 25 : ℝ) * (9 * U ^ (1 + ε))) := by
        rw [hY]; gcongr
    _ = 243 * (12 * KG) ^ 4 * C₄ * (U ^ (11 / 5 * (1 / 2 - σ)) * U ^ (1 / 25 : ℝ) * U ^ (1 + ε)) := by ring
    _ = 243 * (12 * KG) ^ 4 * C₄ * U ^ (11 / 5 * (1 / 2 - σ) + 1 / 25 + (1 + ε)) := by
        rw [← Real.rpow_add hU0, ← Real.rpow_add hU0]
    _ ≤ 243 * (12 * KG) ^ 4 * C₄ * U ^ (30 / 13 * (1 - σ) + 13 * ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1 hexp) (by positivity)

/-! ### Large `U` -/

/-- The conditions on `U` used on `4/5 ≤ σ ≤ 1` hold for all large `U` (`ZetaGMWin.ev_log_pow`, and `c ≤ U^θ`
eventually). -/
lemma eventually_gmh {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ U : ℝ in atTop, (8 : ℝ) ^ 100 ≤ U ∧ 4 * (1 + 2 * Real.log U) ≤ U ^ (ε / 154) ∧
      (2 * (23 * U ^ (11 / 20 : ℝ) * Real.log (U ^ (11 / 20 : ℝ)))) ^ 2 ≤ U ^ (15 / 13 : ℝ) ∧
      23 * U ^ (11 / 20 : ℝ) * Real.log (U ^ (11 / 20 : ℝ)) ≤ U ∧ A ≤ U ^ (ε / 2) ∧
      1 + KE * (4 * Real.log U + 1) ≤ U ^ ε := by
  have hev : ∀ c θ : ℝ, 0 < θ → ∀ᶠ U : ℝ in atTop, c ≤ U ^ θ := fun c θ hθ =>
    (tendsto_rpow_atTop hθ).eventually_ge_atTop c
  have hKE := KE_pos
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ 100),
    ZetaGMWin.ev_log_pow (a := 4) (b := 8) (by norm_num) (by norm_num) (by positivity : (0 : ℝ) < ε / 154) 1,
    ZetaGMWin.ev_log_pow (a := 0) (b := 253 / 10) le_rfl (by norm_num) (by norm_num : (0 : ℝ) < 7 / 130) 2,
    ZetaGMWin.ev_log_pow (a := 0) (b := 253 / 20) le_rfl (by norm_num) (by norm_num : (0 : ℝ) < 9 / 20) 1,
    hev A (ε / 2) (by positivity),
    ZetaGMWin.ev_log_pow (a := 1 + KE) (b := 4 * KE) (by positivity) (by positivity) hε 1]
    with U h1 h2 h3 h4 h5 h6
  have hU1 : 1 ≤ U := le_trans (by norm_num) h1
  have hU0 : 0 < U := by linarith
  have hlog : Real.log (U ^ (11 / 20 : ℝ)) = 11 / 20 * Real.log U := Real.log_rpow hU0 _
  refine ⟨h1, ?_, ?_, ?_, h5, ?_⟩
  · rw [pow_one] at h2
    calc 4 * (1 + 2 * Real.log U) = 4 + 8 * Real.log U := by ring
      _ ≤ U ^ (ε / 154) := h2
  · have e1 : (U ^ (11 / 20 : ℝ)) ^ 2 = U ^ (11 / 10 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; norm_num
    calc (2 * (23 * U ^ (11 / 20 : ℝ) * Real.log (U ^ (11 / 20 : ℝ)))) ^ 2
        = (U ^ (11 / 20 : ℝ)) ^ 2 * (0 + 253 / 10 * Real.log U) ^ 2 := by rw [hlog]; ring
      _ ≤ U ^ (11 / 10 : ℝ) * U ^ (7 / 130 : ℝ) := by rw [e1]; gcongr
      _ = U ^ (15 / 13 : ℝ) := by rw [← Real.rpow_add hU0]; norm_num
  · rw [zero_add, pow_one] at h4
    calc 23 * U ^ (11 / 20 : ℝ) * Real.log (U ^ (11 / 20 : ℝ)) = U ^ (11 / 20 : ℝ) * (253 / 20 * Real.log U) := by
          rw [hlog]; ring
      _ ≤ U ^ (11 / 20 : ℝ) * U ^ (9 / 20 : ℝ) := by gcongr
      _ = U := by rw [← Real.rpow_add hU0]; norm_num
  · rw [pow_one] at h6
    calc 1 + KE * (4 * Real.log U + 1) = 1 + KE + 4 * KE * Real.log U := by ring
      _ ≤ U ^ ε := h6

/-- **One window on `4/5 ≤ σ ≤ 1` at the exponent `30/13`**: for every `0 < ε ≤ 1/200` there is `Cw` such that for
`4/5 ≤ σ ≤ 1` and `U ≥ 8` at most `Cw(log U)^{11}U^{(30/13)(1−σ)+13ε}` zeros have `U ≤ |γ| ≤ 2U` and `β ≥ σ`. For
`U ≥ U₁` (`eventually_gmh`), `window_classes_gmh` at `X = ⌊U^{1/100}⌋`, `Y = U^{11/20}`, `N = ⌊22Y log Y/X⌋ + 1`
(`Xw`, `Yw`, `Nw` at `U^{1/100}`, `c = 27`); below `U₁` the zeros with `|γ| ≤ 2U₁`. -/
theorem window_count_gmh {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ σ : ℝ, 4 / 5 ≤ σ → σ ≤ 1 → ∀ U : ℝ, 8 ≤ U → ∀ Z : Finset (ZeroIdx (sqF Xi)),
      (∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) →
        (Z.card : ℝ) ≤ Cw * Real.log U ^ 11 * U ^ (30 / 13 * (1 - σ) + 13 * ε) := by
  obtain ⟨CK, hCK0, hCK⟩ := norm_kz_le (ε := ε) hε (by linarith)
  obtain ⟨C₄', hC₄'⟩ := zeta_fourth_moment (ε := ε) hε (by linarith)
  set C₄ := max C₄' 0 with hC₄def
  have hC₄0 : 0 ≤ C₄ := le_max_right _ _
  have h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + ε) := by
    intro C' t hsep T hT ht
    refine (hC₄' C' t hsep T hT ht).trans ?_
    gcongr
    exact le_max_left _ _
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.1 (eventually_gmh hε (12 * Real.exp 1 * A77 ε * (KE + CK)))
  set U₁ := max U₀ ((8 : ℝ) ^ 100) with hU₁
  set Cfin : ℝ := ((finite_re_le (2 * U₁)).toFinset.card : ℝ) with hCfin
  have hKG := KG_pos
  have hKc := Kc_nonneg
  have hA1 := one_le_A77 hε (by linarith)
  set Cmain : ℝ := 2 * Kc * (240 * Real.exp 1 * A77 ε + 243 * (12 * KG) ^ 4 * C₄) with hCmain
  have hCmain0 : 0 ≤ Cmain := by positivity
  have hCf : 0 ≤ Cfin := Nat.cast_nonneg _
  refine ⟨Cfin + Cmain, by positivity, fun σ hσ hσ1 U hU Z hZ => ?_⟩
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  set E := 30 / 13 * (1 - σ) + 13 * ε with hE
  have hE0 : 0 ≤ E := by rw [hE]; nlinarith
  have hUE : 1 ≤ U ^ E := Real.one_le_rpow hU1 hE0
  have hL := log_ge_two hU
  have hL11 : 1 ≤ Real.log U ^ 11 := one_le_pow₀ (by linarith)
  rcases lt_or_ge U U₁ with hsmall | hlarge
  · -- below `U₁`: every zero counted has `|γ| ≤ 2U₁`
    have hsub : Z ⊆ (finite_re_le (2 * U₁)).toFinset := fun i hi => by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      linarith [(hZ i hi).2.1]
    have hc : (Z.card : ℝ) ≤ Cfin := by rw [hCfin]; exact_mod_cast card_le_card hsub
    have h1 : 1 ≤ Real.log U ^ 11 * U ^ E := one_le_mul_of_one_le_of_one_le hL11 hUE
    have h2 : 0 ≤ Cmain * (Real.log U ^ 11 * U ^ E) := by positivity
    calc (Z.card : ℝ) ≤ Cfin := hc
      _ ≤ Cfin * (Real.log U ^ 11 * U ^ E) := le_mul_of_one_le_right hCf h1
      _ ≤ (Cfin + Cmain) * Real.log U ^ 11 * U ^ E := by nlinarith
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := hU₀ U (le_trans (le_max_left _ _) hlarge)
  -- the parameters
  set U' : ℝ := U ^ (1 / 100 : ℝ) with hU'
  have hU'8 : 8 ≤ U' := by
    rw [hU']
    calc (8 : ℝ) = ((8 : ℝ) ^ 100) ^ (1 / 100 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ U ^ (1 / 100 : ℝ) := Real.rpow_le_rpow (by positivity) ha (by norm_num)
  have hYU : Yw 27 U' = U ^ (11 / 20 : ℝ) := by rw [hU']; unfold Yw; rw [← Real.rpow_mul hU0.le]; norm_num
  have hX : 1 ≤ Xw U' := Xw_one hU'8
  have hN : 1 ≤ Nw 27 U' := Nw_one
  have hY8 : 8 ≤ Yw 27 U' := le_trans hU'8 (Yw_ge (by norm_num) hU'8)
  have hM : 22 * Yw 27 U' * Real.log (Yw 27 U') ≤ ((Xw U' * Nw 27 U' : ℕ) : ℝ) := XN_ge hU'8
  have hXNle : ((Xw U' * Nw 27 U' : ℕ) : ℝ) ≤ 23 * Yw 27 U' * Real.log (Yw 27 U') := XN_le (by norm_num) hU'8
  have hXU' : (Xw U' : ℝ) ≤ U ^ (1 / 100 : ℝ) := Xw_le hU'8
  have hXU2 : U ^ (1 / 100 : ℝ) ≤ 2 * (Xw U' : ℝ) := by have := Xw_half hU'8; rw [← hU']; linarith
  have hXr : (1 : ℝ) ≤ Xw U' := by exact_mod_cast hX
  have hUY : 36864 * U ≤ (Yw 27 U') ^ 7 := by
    rw [hYU, ← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    have e : U ^ ((11 / 20 : ℝ) * ((7 : ℕ) : ℝ)) = U ^ (57 / 20 : ℝ) * U := by
      rw [← Real.rpow_add_one hU0.ne']; norm_num
    rw [e]
    have h36 : (36864 : ℝ) ≤ U ^ (57 / 20 : ℝ) := by
      have h1 : U ≤ U ^ (57 / 20 : ℝ) := by
        calc U = U ^ (1 : ℝ) := (Real.rpow_one U).symm
          _ ≤ U ^ (57 / 20 : ℝ) := Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
      have h2 : (36864 : ℝ) ≤ 8 ^ 100 := by norm_num
      linarith
    exact mul_le_mul_of_nonneg_right h36 hU0.le
  have hNU : (Nw 27 U' : ℝ) ≤ U := by
    have h1 : (Nw 27 U' : ℝ) ≤ ((Xw U' * Nw 27 U' : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hXr
    rw [hYU] at hXNle
    linarith
  have hK : 4 * ((Nat.log 2 (Nw 27 U') + 1 : ℕ) : ℝ) ≤ U ^ (ε / 154) :=
    (mul_le_mul_of_nonneg_left (log_blocks_le hN hNU) (by norm_num)).trans hb
  have hXN : (2 * ((Xw U' * Nw 27 U' : ℕ) : ℝ)) ^ 2 ≤ U ^ (15 / 13 : ℝ) := by
    refine le_trans ?_ hc
    rw [← hYU]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hwc := window_classes_gmh hε hε1 hCK0 hCK hC₄0 h4 hσ hσ1 (by linarith) hY8 hUY hX hN hM hXU2 hK hXN
    he hf Z hZ
  rw [hYU] at hwc
  refine hwc.trans ?_
  -- the two classes as powers of `U`
  have hKle : ((Nat.log 2 (Nw 27 U') + 1 : ℕ) : ℝ) ≤ U ^ ε := by
    have h1 : U ^ (ε / 154) ≤ U ^ ε := Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
    linarith
  have hpow : U ^ ε * U ^ (30 / 13 * (1 - σ) + 12 * ε) = U ^ E := by
    rw [← Real.rpow_add hU0, hE]; congr 1; ring
  have hpart1 : 2 * (12 * ((Nat.log 2 (Nw 27 U') + 1 : ℕ) : ℝ) *
      (10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε))) ≤ 240 * Real.exp 1 * A77 ε * U ^ E := by
    calc 2 * (12 * ((Nat.log 2 (Nw 27 U') + 1 : ℕ) : ℝ) *
          (10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε)))
        ≤ 2 * (12 * U ^ ε * (10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε))) := by gcongr
      _ = 240 * Real.exp 1 * A77 ε * (U ^ ε * U ^ (30 / 13 * (1 - σ) + 12 * ε)) := by ring
      _ = 240 * Real.exp 1 * A77 ε * U ^ E := by rw [hpow]
  have hpart3 := class3_bound_gmh (σ := σ) hε hε1 hC₄0 hσ1 (by linarith : 8 ≤ U) hXU'
  rw [← hE] at hpart3
  have hKl := Kloc_le (U := U) (by linarith)
  have hKl0 : 0 ≤ Kloc (2 * U + 1) := Kloc_nonneg (by linarith)
  have hlogU : Real.log U ≤ Real.log U ^ 11 := by
    calc Real.log U = Real.log U ^ 1 := (pow_one _).symm
      _ ≤ Real.log U ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hUE0 : 0 ≤ U ^ E := by positivity
  calc 2 * Kloc (2 * U + 1) * (2 * (12 * ((Nat.log 2 (Nw 27 U') + 1 : ℕ) : ℝ) *
        (10 * Real.exp 1 * A77 ε * U ^ (30 / 13 * (1 - σ) + 12 * ε))) +
      27 * (3 * KG * (U ^ (11 / 20 : ℝ)) ^ (1 / 2 - σ) / (1 / 4)) ^ 4 * ((Xw U' : ℕ) : ℝ) ^ 4 *
        (C₄ * (2 * U + 2) ^ (1 + ε)))
      ≤ 2 * (Kc * Real.log U) * (240 * Real.exp 1 * A77 ε * U ^ E + 243 * (12 * KG) ^ 4 * C₄ * U ^ E) := by
        gcongr
    _ = Cmain * Real.log U * U ^ E := by rw [hCmain]; ring
    _ ≤ Cmain * Real.log U ^ 11 * U ^ E := by gcongr
    _ ≤ (Cfin + Cmain) * Real.log U ^ 11 * U ^ E := by gcongr; linarith


/-! ### The count on `4/5 ≤ σ ≤ 11/12` -/

/-- **The density estimate at the exponent `30/13` on `4/5 ≤ σ ≤ 11/12`**: for every `0 < ε ≤ 1/200` there is
`C ≥ 0` with `N(σ, T) ≤ C T^{(30/13 + 156ε)(1−σ)}(log T)^{12}` for `T ≥ 2` (`ZetaIngham.nx_le_of_windows` with
`window_count_gmh`; `13ε ≤ 156ε(1 − σ)` for `σ ≤ 11/12`). -/
theorem nx_gmh {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 200) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 4 / 5 ≤ σ → σ ≤ 11 / 12 →
      (NX (σ - 1 / 2) T : ℝ) ≤ C * T ^ ((30 / 13 + 156 * ε) * (1 - σ)) * Real.log T ^ 12 := by
  obtain ⟨Cw, hCw0, hCw⟩ := window_count_gmh hε hε1
  refine ⟨((finite_re_le 8).toFinset.card : ℝ) * 2 ^ 12 + 4 * Cw, by positivity, fun T hT σ hσ hσ1 => ?_⟩
  have he0 : 0 ≤ 30 / 13 * (1 - σ) + 13 * ε := by nlinarith
  have hN := nx_le_of_windows he0 hCw0 (fun U hU Z hZ => hCw σ hσ (by linarith) U hU Z hZ) hT
  refine hN.trans ?_
  have hT1 : 1 ≤ T := by linarith
  have hexp : 30 / 13 * (1 - σ) + 13 * ε ≤ (30 / 13 + 156 * ε) * (1 - σ) := by nlinarith
  have hlog : 0 ≤ Real.log T ^ 12 := by have := Real.log_nonneg hT1; positivity
  have hc : 0 ≤ ((finite_re_le 8).toFinset.card : ℝ) * 2 ^ 12 + 4 * Cw := by positivity
  gcongr

end ZetaGMHux

#print axioms ZetaGMHux.feas_gmh
#print axioms ZetaGMHux.count_bound_gmh
#print axioms ZetaGMHux.class_poly_gmh
#print axioms ZetaGMHux.window_count_gmh
#print axioms ZetaGMHux.nx_gmh
