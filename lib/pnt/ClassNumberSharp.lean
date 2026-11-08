/-
# Class numbers of quadratic fields with explicit constants, and class number one below `2.5·10⁷`

Plain statement. Let `K` be a quadratic field with discriminant `D_K`, class number `h_K`, `w_K` roots of unity and
regulator `R_K`, and let `ℓ_K = 52 + log log(|D_K| + 2)` and `c = e^{−γ−3/100}`, `γ` Euler's constant.

* `classNumber_ge_sharp`, `classNumber_le_sharp`: for `K` imaginary,
  `cw_K√|D_K|/(26πℓ_K) ≤ h_K ≤ 13w_K√|D_K|ℓ_K/(2πc)`.
* `regulator_mul_classNumber_ge_sharp`, `regulator_mul_classNumber_le_sharp`: for `K` real, the same with `4R_Kh_K`
  in place of `2πh_K`.
* `classNumber_ge_85`, `regulator_mul_classNumber_ge_55`: `h_K ≥ √|D_K|/(85ℓ_K)` for `K` imaginary, and
  `R_Kh_K ≥ √D_K/(55ℓ_K)` for `K` real, by `w_K ≥ 2`, `γ < 2/3` and `π < 3.1416`.
* `abs_discr_lt_of_classNumber_eq_one`: an imaginary quadratic field of class number one has `|D_K| < 2.5·10⁷`.

These follow from `QuadKronecker.classNumber_formula` and `LittlewoodSharp.norm_LFunction_one_bounds_sharp`, that is
from the zero-free half-plane `Re s > 11/12`, with no other hypothesis. They replace the constants `e^{±2·10²¹}` of
`QuadClassNumber`, and the bound `(320πe^{2·10²¹})⁴` of `ClassNumberBound` at `h_K = 1`. So Gauss's class number one
problem, given the half-plane, comes down to the discriminants below `2.5·10⁷`, a finite computation.
-/
import QuadClassNumber
import LittlewoodSharp

open NumberField

namespace ClassNumberSharp

variable {K : Type*} [Field K] [NumberField K]

/-- `w_K ≥ 2`: `−1` is a root of unity, so the number of roots of unity is even and positive. -/
lemma two_le_torsionOrder : (2 : ℝ) ≤ (Units.torsionOrder K : ℝ) := by
  have hpos := Units.torsionOrder_pos K
  obtain ⟨r, hr⟩ := Units.even_torsionOrder K
  have : 2 ≤ Units.torsionOrder K := by omega
  exact_mod_cast this

/-- `ℓ_K = 52 + log log(|D_K| + 2) > 0`. -/
lemma ell_pos (hK : Module.finrank ℚ K = 2) :
    0 < 52 + Real.log (Real.log (|(discr K : ℝ)| + 2)) := by
  have h3 := QuadClassNumber.three_le_abs_discr hK
  have hl : 1 < Real.log (|(discr K : ℝ)| + 2) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have := Real.log_pos hl
  linarith

/-- **The class number of an imaginary quadratic field, from below, with explicit constants**:
`h_K ≥ w_K√|D_K|e^{−γ−3/100}/(26π(52 + log log(|D_K| + 2)))`. -/
theorem classNumber_ge_sharp (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| *
        Real.exp (-(Real.eulerMascheroniConstant + 3 / 100)) /
      (26 * Real.pi * (52 + Real.log (Real.log (|(discr K : ℝ)| + 2)))) ≤ classNumber K := by
  obtain ⟨N, hN, χ, hND, -, hχ, hL⟩ := QuadClassNumber.exists_norm_imag hK hc
  have hlow := (LittlewoodSharp.norm_LFunction_one_bounds_sharp N χ hχ).1
  rw [hL, QuadClassNumber.natCast_eq_abs hND] at hlow
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hr := QuadClassNumber.sqrt_abs_discr_pos (K := K)
  have hℓ := ell_pos hK
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hlow
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- **The class number of an imaginary quadratic field, from above, with explicit constants**:
`h_K ≤ 13w_K√|D_K|e^{γ+3/100}(52 + log log(|D_K| + 2))/(2π)`. -/
theorem classNumber_le_sharp (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    (classNumber K : ℝ) ≤ 13 * (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| *
      Real.exp (Real.eulerMascheroniConstant + 3 / 100) *
        (52 + Real.log (Real.log (|(discr K : ℝ)| + 2))) / (2 * Real.pi) := by
  obtain ⟨N, hN, χ, hND, -, hχ, hL⟩ := QuadClassNumber.exists_norm_imag hK hc
  have hup := (LittlewoodSharp.norm_LFunction_one_bounds_sharp N χ hχ).2
  rw [hL, QuadClassNumber.natCast_eq_abs hND] at hup
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hr := QuadClassNumber.sqrt_abs_discr_pos (K := K)
  rw [div_le_iff₀ (by positivity)] at hup
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- **The class number and regulator of a real quadratic field, from below, with explicit constants**:
`R_K h_K ≥ w_K√D_K e^{−γ−3/100}/(52(52 + log log(D_K + 2)))`. -/
theorem regulator_mul_classNumber_ge_sharp (hK : Module.finrank ℚ K = 2)
    (hc : InfinitePlace.nrComplexPlaces K = 0) :
    (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| *
        Real.exp (-(Real.eulerMascheroniConstant + 3 / 100)) /
      (52 * (52 + Real.log (Real.log (|(discr K : ℝ)| + 2)))) ≤ Units.regulator K * classNumber K := by
  obtain ⟨N, hN, χ, hND, -, hχ, hL⟩ := QuadClassNumber.exists_norm_real hK hc
  have hlow := (LittlewoodSharp.norm_LFunction_one_bounds_sharp N χ hχ).1
  rw [hL, QuadClassNumber.natCast_eq_abs hND] at hlow
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hr := QuadClassNumber.sqrt_abs_discr_pos (K := K)
  have hℓ := ell_pos hK
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hlow
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **The class number and regulator of a real quadratic field, from above, with explicit constants**:
`R_K h_K ≤ 13w_K√D_K e^{γ+3/100}(52 + log log(D_K + 2))/4`. -/
theorem regulator_mul_classNumber_le_sharp (hK : Module.finrank ℚ K = 2)
    (hc : InfinitePlace.nrComplexPlaces K = 0) :
    Units.regulator K * classNumber K ≤ 13 * (Units.torsionOrder K : ℝ) * Real.sqrt |(discr K : ℝ)| *
      Real.exp (Real.eulerMascheroniConstant + 3 / 100) *
        (52 + Real.log (Real.log (|(discr K : ℝ)| + 2))) / 4 := by
  obtain ⟨N, hN, χ, hND, -, hχ, hL⟩ := QuadClassNumber.exists_norm_real hK hc
  have hup := (LittlewoodSharp.norm_LFunction_one_bounds_sharp N χ hχ).2
  rw [hL, QuadClassNumber.natCast_eq_abs hND] at hup
  have hw : 0 < (Units.torsionOrder K : ℝ) := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hr := QuadClassNumber.sqrt_abs_discr_pos (K := K)
  rw [div_le_iff₀ (by positivity)] at hup
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-! ### The numbers -/

/-- `e^{γ+3/100} ≤ 2.08`, from `γ < 2/3` and `e^x < 1/(1 − x)` at `x = 209/2400`. -/
lemma exp_c_le : Real.exp (Real.eulerMascheroniConstant + 3 / 100) ≤ 2.08 := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have h1 : Real.exp (Real.eulerMascheroniConstant + 3 / 100) ≤ Real.exp (209 / 300) :=
    Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (209 / 2400) ^ 8 = Real.exp (209 / 300) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h3 : Real.exp (209 / 2400) < 1 / (1 - 209 / 2400) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have h4 : Real.exp (209 / 2400) ^ 8 ≤ (1 / (1 - 209 / 2400 : ℝ)) ^ 8 :=
    pow_le_pow_left₀ (Real.exp_pos _).le h3.le 8
  have h5 : (1 / (1 - 209 / 2400 : ℝ)) ^ 8 ≤ 2.08 := by norm_num
  linarith

lemma exp_neg_c_ge : 1 / 2.08 ≤ Real.exp (-(Real.eulerMascheroniConstant + 3 / 100)) := by
  rw [Real.exp_neg]
  exact one_div_le_one_div_of_le (Real.exp_pos _) exp_c_le |>.trans_eq (one_div _)

/-- **`h_K ≥ √|D_K|/(85(52 + log log(|D_K| + 2)))`** for every imaginary quadratic field. -/
theorem classNumber_ge_85 (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    Real.sqrt |(discr K : ℝ)| / (85 * (52 + Real.log (Real.log (|(discr K : ℝ)| + 2)))) ≤
      classNumber K := by
  refine le_trans ?_ (classNumber_ge_sharp hK hc)
  have hℓ := ell_pos hK
  have hr := QuadClassNumber.sqrt_abs_discr_pos (K := K)
  have hw := two_le_torsionOrder (K := K)
  have he := exp_neg_c_ge
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  set ℓ := 52 + Real.log (Real.log (|(discr K : ℝ)| + 2))
  set s := Real.sqrt |(discr K : ℝ)|
  set c := Real.exp (-(Real.eulerMascheroniConstant + 3 / 100))
  -- `s · 26πℓ ≤ w s c · 85ℓ`, from `26π ≤ 85 · 2 · (1/2.08)`
  have h1 : 26 * Real.pi ≤ 85 * (2 * (1 / 2.08)) := by nlinarith
  have h2 : 85 * (2 * (1 / 2.08)) ≤ 85 * ((Units.torsionOrder K : ℝ) * c) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hw he (by norm_num) (by positivity)) (by norm_num)
  nlinarith [mul_pos hr hℓ]

/-- **`R_K h_K ≥ √D_K/(55(52 + log log(D_K + 2)))`** for every real quadratic field. -/
theorem regulator_mul_classNumber_ge_55 (hK : Module.finrank ℚ K = 2)
    (hc : InfinitePlace.nrComplexPlaces K = 0) :
    Real.sqrt |(discr K : ℝ)| / (55 * (52 + Real.log (Real.log (|(discr K : ℝ)| + 2)))) ≤
      Units.regulator K * classNumber K := by
  refine le_trans ?_ (regulator_mul_classNumber_ge_sharp hK hc)
  have hℓ := ell_pos hK
  have hr := QuadClassNumber.sqrt_abs_discr_pos (K := K)
  have hw := two_le_torsionOrder (K := K)
  have he := exp_neg_c_ge
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  set ℓ := 52 + Real.log (Real.log (|(discr K : ℝ)| + 2))
  set s := Real.sqrt |(discr K : ℝ)|
  set c := Real.exp (-(Real.eulerMascheroniConstant + 3 / 100))
  have h2 : 55 * (2 * (1 / 2.08)) ≤ 55 * ((Units.torsionOrder K : ℝ) * c) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hw he (by norm_num) (by positivity)) (by norm_num)
  have h1 : (52 : ℝ) ≤ 55 * (2 * (1 / 2.08)) := by norm_num
  nlinarith [mul_pos hr hℓ]

/-! ### Class number one -/

/-- `e^{17} < 2.5·10⁷`. -/
lemma exp_17_lt : Real.exp 17 < 25000000 := by
  have h : Real.exp 1 ^ 17 = Real.exp 17 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [← h]
  calc Real.exp 1 ^ 17 < 2.7182818286 ^ 17 := by
        gcongr
        exact Real.exp_one_lt_d9
    _ < 25000000 := by norm_num

/-- `e^{17/2} ≥ 4840`. -/
lemma exp_17_half_ge : 4840 ≤ Real.exp (17 / 2) := by
  have h8 : Real.exp 1 ^ 8 = Real.exp 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he8 : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 8 := by
    rw [← h8]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 8
  have hh : (1.625 : ℝ) ≤ Real.exp (1 / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    norm_num at this ⊢
    linarith
  have e : Real.exp (17 / 2) = Real.exp 8 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith

/-- `log 17 ≤ 2.9`, from `e^{2.9} ≥ e²(1 + 0.9 + 0.405) > 17`. -/
lemma log_17_le : Real.log 17 ≤ 2.9 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h2 : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he2 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 2 := by
    rw [← h2]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 2
  have h09 : (2.305 : ℝ) ≤ Real.exp 0.9 := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.9 by norm_num)
    norm_num at this ⊢
    linarith
  have e : Real.exp 2.9 = Real.exp 2 * Real.exp 0.9 := by
    rw [← Real.exp_add]
    norm_num
  rw [e]
  nlinarith

/-- `√X > 85(52 + log log(X + 2))` for `X ≥ 2.5·10⁷`. -/
lemma sqrt_gt_of_ge {X : ℝ} (hX : 25000000 ≤ X) :
    85 * (52 + Real.log (Real.log (X + 2))) < Real.sqrt X := by
  set t := Real.log (X + 2) with ht
  have hX0 : 0 < X + 2 := by linarith
  have ht17 : 17 ≤ t := by
    rw [ht, Real.le_log_iff_exp_le hX0]
    linarith [exp_17_lt]
  have ht0 : 0 < t := by linarith
  -- `log t ≤ log 17 + (t − 17)/17 ≤ 2.9 + (t − 17)/17`
  have hlt : Real.log t ≤ 2.9 + (t - 17) / 17 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < t / 17 by positivity)
    rw [Real.log_div ht0.ne' (by norm_num)] at h
    have := log_17_le
    linarith
  -- `√(X + 2) = e^{t/2} ≥ e^{17/2}(1 + (t − 17)/2)`
  have hsq : Real.sqrt (X + 2) = Real.exp (t / 2) := by
    rw [Real.exp_half, ht, Real.exp_log hX0]
  have hexp : Real.exp (17 / 2) * (1 + (t - 17) / 2) ≤ Real.exp (t / 2) := by
    have e : Real.exp (t / 2) = Real.exp (17 / 2) * Real.exp ((t - 17) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    have := Real.add_one_le_exp ((t - 17) / 2)
    have : 0 < Real.exp (17 / 2) := Real.exp_pos _
    nlinarith
  -- `√X ≥ √(X + 2) − 1`
  have hsX : Real.sqrt (X + 2) - 1 ≤ Real.sqrt X := by
    have hs0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    have h1 : 1 ≤ 2 * Real.sqrt X := by
      have : (1 : ℝ) ≤ Real.sqrt X := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by linarith)
      linarith
    have h2 : Real.sqrt (X + 2) ≤ Real.sqrt X + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ X by linarith)]
    linarith
  have h17 := exp_17_half_ge
  nlinarith

/-- **Class number one below `2.5·10⁷`**: an imaginary quadratic field with class number one has
`|D_K| < 2.5·10⁷`. -/
theorem abs_discr_lt_of_classNumber_eq_one (hK : Module.finrank ℚ K = 2)
    (hc : InfinitePlace.nrRealPlaces K = 0) (h1 : classNumber K = 1) :
    |(discr K : ℝ)| < 25000000 := by
  by_contra hX
  rw [not_lt] at hX
  have hge := classNumber_ge_85 hK hc
  rw [h1, Nat.cast_one] at hge
  have hℓ := ell_pos hK
  rw [div_le_one (by positivity)] at hge
  linarith [sqrt_gt_of_ge hX]

end ClassNumberSharp
