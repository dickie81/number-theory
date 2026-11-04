import Mathlib
import CmBessel

/-! # Polynomial enclosure of `jₙ(15 λ s)` on `s ∈ [0,1]`, `λ = log 3`

`CmBessel.jP_s` encloses `jP n (15 s)` by `sⁿ q̂ₙ(s²)`. Here the argument `15` becomes a rational parameter `X`
(`jP_sX`, the same proof), and a Lipschitz bound in the argument (`jP_lip`) moves from the rational `X̂ = 15·l3lo`
to the irrational `15 λ`, at a cost of `Lip·15·(l3hi − l3lo)`, about `10⁻¹⁶`.
-/

namespace V3Bessel

open Real Finset WeilTailB WeilConst CmBessel

/-! ## The `s`-polynomial of `jP n (X s)` for rational `X` -/

/-- Exact coefficients: `jP n (X s) ≈ sⁿ Σ_k qxX_k s^{2k}`. -/
def qxX (X : ℚ) (K W n : ℕ) : List ℚ := (List.range K).map fun k =>
  X ^ (n + 2 * k) * (-1) ^ k * (rowG W n).getD k 0 / (2 ^ (n + 1) * (n.factorial : ℚ) * ((2 * k).factorial : ℚ))

def qhX (P : ℕ) (X : ℚ) (K W n : ℕ) : List ℚ := (qxX X K W n).map (rnd P)

def eTX (P : ℕ) (X : ℚ) (K W n : ℕ) : ℚ :=
  X ^ n / (2 ^ (n + 1) * (n.factorial : ℚ)) * (2 * X ^ (2 * K) / ((2 * K).factorial : ℚ) * (rowG W n).getD 0 0)
    + K / 2 ^ P

noncomputable def jAX (P : ℕ) (X : ℚ) (K W n : ℕ) (s : ℝ) : ℝ :=
  s ^ n * ∑ k ∈ range K, (((qhX P X K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k)

theorem jP_sX (P : ℕ) (X : ℚ) (K W n : ℕ) (hW : K + n < W) (hX0 : (0:ℝ) ≤ X)
    (hK : (X:ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) / 2) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |jP n ((X:ℝ) * s) - jAX P X K W n s| ≤ (eTX P X K W n : ℝ) := by
  have hx : 0 ≤ (X:ℝ) * s := mul_nonneg hX0 h0
  have hxX : (X:ℝ) * s ≤ X := by nlinarith
  have h := jP_enc K n hx hxX (by push_cast at hK; linarith)
  set C := ((X:ℝ) * s) ^ n / (2 ^ (n + 1) * (n.factorial : ℝ))
  -- exact polynomial
  have hex : C * ∑ k ∈ range K, (-1) ^ k * ((X:ℝ) * s) ^ (2 * k) / ((2 * k).factorial : ℝ) * J k n
      = s ^ n * ∑ k ∈ range K, (((qxX X K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k) := by
    unfold C; rw [mul_sum, mul_sum]; apply sum_congr rfl; intro k hk
    have hk' := mem_range.1 hk
    unfold qxX; rw [List.getD_eq_getElem?_getD]; simp only [List.getElem?_map, List.getElem?_range hk']
    simp only [Option.map_some, Option.getD_some]
    push_cast; rw [rowG_getD W n k (by omega)]
    rw [mul_pow, mul_pow, pow_add]; field_simp; ring
  rw [hex] at h
  -- rounding
  have hr : |s ^ n * ∑ k ∈ range K, (((qxX X K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k) - jAX P X K W n s|
      ≤ K / 2 ^ P := by
    unfold jAX; rw [← mul_sub, ← sum_sub_distrib, abs_mul]
    have hsn : |s ^ n| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ h0 h1
    have : |∑ k ∈ range K, ((((qxX X K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k)
        - (((qhX P X K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k))| ≤ ∑ k ∈ range K, (1 / 2 ^ P : ℝ) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
      have hk' := mem_range.1 hk
      rw [← sub_mul, abs_mul]
      have e : (qhX P X K W n).getD k 0 = rnd P ((qxX X K W n).getD k 0) := by
        have hl : k < (qxX X K W n).length := by simp [qxX, hk']
        unfold qhX; rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl, List.getElem_map]
      rw [e]
      have hs2 : |s ^ (2 * k)| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ h0 h1
      calc _ ≤ 1 / 2 ^ P * 1 := mul_le_mul (rnd_err P _) hs2 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    rw [sum_const, card_range, nsmul_eq_mul] at this
    calc |s ^ n| * _ ≤ 1 * ((K:ℝ) * (1 / 2 ^ P)) := mul_le_mul hsn this (abs_nonneg _) zero_le_one
      _ = _ := by ring
  have hJ : 0 ≤ J 0 n := by
    unfold J; apply intervalIntegral.integral_nonneg (by norm_num); intro t ht
    simp only [mul_zero, pow_zero, one_mul]; apply pow_nonneg; nlinarith [ht.1, ht.2]
  have hE : C * (2 * (X:ℝ) ^ (2 * K) / ((2 * K).factorial : ℝ) * J 0 n)
      ≤ (X:ℝ) ^ n / (2 ^ (n + 1) * n.factorial) * (2 * (X:ℝ) ^ (2 * K) / ((2 * K).factorial : ℝ) * J 0 n) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold C; gcongr
  have hc : (eTX P X K W n : ℝ) = (X:ℝ) ^ n / (2 ^ (n + 1) * n.factorial) *
      (2 * (X:ℝ) ^ (2 * K) / ((2 * K).factorial : ℝ) * J 0 n) + K / 2 ^ P := by
    unfold eTX; push_cast; rw [rowG_getD W n 0 (by omega)]
  rw [hc]
  calc |jP n ((X:ℝ) * s) - jAX P X K W n s|
      ≤ |jP n ((X:ℝ) * s) - s ^ n * ∑ k ∈ range K, (((qxX X K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k)|
        + |s ^ n * ∑ k ∈ range K, (((qxX X K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k) - jAX P X K W n s| :=
        abs_sub_le _ _ _
    _ ≤ _ := add_le_add (h.trans hE) hr

/-! ## Lipschitz bound in the argument -/

/-- `|jP n x − jP n y| ≤ (2n X₀^{n−1} + 2X₀ⁿ)/(2^{n+1} n!) · |x − y|` for `x, y ∈ [0, X₀]`. -/
theorem jP_lip (n : ℕ) {x y X0 : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxX : x ≤ X0) (hyX : y ≤ X0) :
    |jP n x - jP n y| ≤ (2 * n * X0 ^ (n - 1) + 2 * X0 ^ n) / (2 ^ (n + 1) * n.factorial) * |x - y| := by
  set F : ℝ → ℝ := fun z => ∫ t in (-1:ℝ)..1, Real.cos (z * t) * (1 - t ^ 2) ^ n with hF
  have hX0 : 0 ≤ X0 := hx.trans hxX
  have hc : (0:ℝ) < 2 ^ (n + 1) * n.factorial := by positivity
  have hj : ∀ z, jP n z = z ^ n / (2 ^ (n + 1) * n.factorial) * F z := fun z => rfl
  have hFb : |F x| ≤ 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1:ℝ)) (b := 1) (C := 1)
      (f := fun t => Real.cos (x * t) * (1 - t ^ 2) ^ n) (fun t ht => by
        obtain ⟨a, b⟩ := wt_bound ht n
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg a]
        calc |Real.cos (x * t)| * (1 - t ^ 2) ^ n ≤ 1 * 1 := mul_le_mul (abs_cos_le_one _) b a zero_le_one
          _ = 1 := by ring)
    rw [Real.norm_eq_abs] at this; norm_num at this; exact this
  have hFd : |F x - F y| ≤ 2 * |x - y| := by
    have ci : ∀ z : ℝ, IntervalIntegrable (fun t : ℝ => Real.cos (z * t) * (1 - t ^ 2) ^ n)
        MeasureTheory.volume (-1) 1 := fun z => (by fun_prop : Continuous fun t : ℝ =>
          Real.cos (z * t) * (1 - t ^ 2) ^ n).intervalIntegrable _ _
    rw [hF]; simp only
    rw [← intervalIntegral.integral_sub (ci x) (ci y)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1:ℝ)) (b := 1) (C := |x - y|)
      (f := fun t => Real.cos (x * t) * (1 - t ^ 2) ^ n - Real.cos (y * t) * (1 - t ^ 2) ^ n) (fun t ht => by
        obtain ⟨a, b⟩ := wt_bound ht n
        have ht' : |t| ≤ 1 := by
          rw [Set.uIoc_of_le (by norm_num)] at ht; exact abs_le.2 ⟨ht.1.le, ht.2⟩
        rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg a]
        have hcos : |Real.cos (x * t) - Real.cos (y * t)| ≤ |x - y| := by
          refine (Real.abs_cos_sub_cos_le _ _).trans ?_
          rw [← sub_mul, abs_mul]
          calc |x - y| * |t| ≤ |x - y| * 1 := mul_le_mul_of_nonneg_left ht' (abs_nonneg _)
            _ = _ := by ring
        calc |Real.cos (x * t) - Real.cos (y * t)| * (1 - t ^ 2) ^ n ≤ |x - y| * 1 :=
              mul_le_mul hcos b a (abs_nonneg _)
          _ = |x - y| := by ring)
    rw [Real.norm_eq_abs] at this; norm_num at this
    linarith
  have hpow : |x ^ n - y ^ n| ≤ |x - y| * n * X0 ^ (n - 1) := by
    refine (abs_pow_sub_pow_le (a := x) (b := y) (n := n)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _))
    rw [abs_of_nonneg hx, abs_of_nonneg hy]; exact max_le hxX hyX
  have hyn : |y ^ n| ≤ X0 ^ n := by
    rw [abs_of_nonneg (pow_nonneg hy n)]; exact pow_le_pow_left₀ hy hyX n
  rw [hj, hj]
  have e : x ^ n / (2 ^ (n + 1) * n.factorial) * F x - y ^ n / (2 ^ (n + 1) * n.factorial) * F y
      = ((x ^ n - y ^ n) * F x + y ^ n * (F x - F y)) / (2 ^ (n + 1) * n.factorial) := by ring
  rw [e, abs_div, abs_of_pos hc, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have a1 : |x ^ n - y ^ n| * |F x| ≤ |x - y| * n * X0 ^ (n - 1) * 2 :=
    mul_le_mul hpow hFb (abs_nonneg _) (by positivity)
  have a2 : |y ^ n| * |F x - F y| ≤ X0 ^ n * (2 * |x - y|) :=
    mul_le_mul hyn hFd (abs_nonneg _) (by positivity)
  nlinarith

end V3Bessel
