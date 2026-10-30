/-
# Gauss's class number problem, with an explicit bound

Plain statement. Let `K` be an imaginary quadratic field with discriminant `D_K` and class number `h_K`. Then
`|D_K| ≤ (320π e^{2·10²¹} h_K)⁴` (`abs_discr_le`). So for each `h` the imaginary quadratic fields of class number `h`
are finitely many, and their discriminants are bounded by an explicit polynomial in `h`.

Gauss's conjecture that `h_K → ∞` was proved by H. Heilbronn (1934), and C. L. Siegel's `h_K ≫_ε |D_K|^{1/2−ε}` (1935)
is ineffective. The effective lower bound of D. Goldfeld, B. Gross and D. Zagier (1976, 1986) is about `log |D_K|`, which
bounds `|D_K|` exponentially in `h`. A bound polynomial in `h` is what GRH gives. Here it follows from
`QuadClassNumber.classNumber_ge_loglog`, that is from the zero-free half-plane, with no hypothesis. The constant is far
too large for any computation.
-/
import QuadClassNumber

open NumberField

namespace ClassNumberBound

variable {K : Type*} [Field K] [NumberField K]

/-- **Gauss's class number problem, with an explicit bound**: `|D_K| ≤ (320π e^{2·10²¹} h_K)⁴` for every imaginary
quadratic field `K`. -/
theorem abs_discr_le (hK : Module.finrank ℚ K = 2) (hc : InfinitePlace.nrRealPlaces K = 0) :
    |(discr K : ℝ)| ≤ (320 * Real.pi * Real.exp (2 * 10 ^ 21) * classNumber K) ^ 4 := by
  have hmain := QuadClassNumber.classNumber_ge_loglog hK hc
  set x := |(discr K : ℝ)| with hx
  set h : ℝ := (classNumber K : ℝ) with hh
  set c := Real.exp (-(2 * 10 ^ 21)) with hc'
  have hx3 : 3 ≤ x := QuadClassNumber.three_le_abs_discr hK
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 < Real.log x := by
    have h3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
    linarith [QuadClassNumber.log_three_gt]
  have hL0 : 0 < Real.log (Real.log x) := Real.log_pos hlog1
  have hh0 : 0 ≤ h := Nat.cast_nonneg _
  have h1 : c * Real.sqrt x ≤ 80 * Real.pi * Real.log (Real.log x) * h := by
    rw [div_le_iff₀ (by positivity)] at hmain
    linarith
  set t := x ^ ((1 : ℝ) / 4) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx0 _
  have hlogx : Real.log x ≤ 4 * t := by
    have h4 : Real.log x = 4 * Real.log t := by
      rw [ht, Real.log_rpow hx0]
      ring
    rw [h4]
    linarith [Real.log_le_sub_one_of_pos ht0]
  have hLL : Real.log (Real.log x) ≤ Real.log x := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Real.log x)]
  have hsq : Real.sqrt x = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]
    norm_num
  have hx4 : x = t ^ 4 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have h2 : c * t * t ≤ 320 * Real.pi * h * t := by
    calc c * t * t = c * Real.sqrt x := by rw [hsq]; ring
      _ ≤ 80 * Real.pi * Real.log (Real.log x) * h := h1
      _ ≤ 80 * Real.pi * (4 * t) * h := by gcongr; linarith
      _ = 320 * Real.pi * h * t := by ring
  have hct : c * t ≤ 320 * Real.pi * h := le_of_mul_le_mul_right h2 ht0
  have hinv : Real.exp (2 * 10 ^ 21) * c = 1 := by
    rw [hc', ← Real.exp_add]
    norm_num
  have h3 : t ≤ 320 * Real.pi * Real.exp (2 * 10 ^ 21) * h := by
    calc t = Real.exp (2 * 10 ^ 21) * (c * t) := by rw [← mul_assoc, hinv, one_mul]
      _ ≤ Real.exp (2 * 10 ^ 21) * (320 * Real.pi * h) := by gcongr
      _ = 320 * Real.pi * Real.exp (2 * 10 ^ 21) * h := by ring
  rw [hx4]
  exact pow_le_pow_left₀ ht0.le h3 4

end ClassNumberBound
