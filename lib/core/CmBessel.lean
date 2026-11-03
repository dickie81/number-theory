import Mathlib
import WeilConst

/-! # Polynomial enclosure of `jₙ(15 s)` on `s ∈ [0,1]` (input to the `C^ψ` quadrature)

`jP n x = xⁿ/(2ⁿ⁺¹n!) ∫₋₁¹ cos(xt)(1−t²)ⁿ dt`. Replacing `cos` by its Taylor polynomial of degree `2K−2`
(remainder from Mathlib's `Complex.exp_bound'`) and integrating the exact moments `J k n` gives
`|jP n (15 s) − sⁿ q̂ₙ(s²)| ≤ eT n` with an explicit dyadic coefficient list `q̂ₙ`.
-/

namespace CmBessel

open Real Finset WeilTailB WeilConst

/-! ## cos Taylor bound for large arguments -/

noncomputable def Tc (K : ℕ) (y : ℝ) : ℝ := ∑ k ∈ range K, (-1) ^ k * y ^ (2 * k) / ((2 * k).factorial : ℝ)

lemma re_sum (K : ℕ) (y : ℝ) :
    (∑ m ∈ range (2 * K), (Complex.I * y) ^ m / (m.factorial : ℂ)).re = Tc K y := by
  induction K with
  | zero => simp [Tc]
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, Complex.add_re,
      Complex.add_re, ih, Tc, Tc, sum_range_succ]
    have e1 : (Complex.I * y) ^ (2 * K) / ((2 * K).factorial : ℂ)
        = ((((-1) ^ K * y ^ (2 * K) / ((2 * K).factorial : ℝ)) : ℝ) : ℂ) := by
      rw [mul_pow, pow_mul, Complex.I_sq]; push_cast; ring
    have e2 : (Complex.I * y) ^ (2 * K + 1) / ((2 * K + 1).factorial : ℂ)
        = Complex.I * ((((-1) ^ K * y ^ (2 * K + 1) / ((2 * K + 1).factorial : ℝ)) : ℝ) : ℂ) := by
      rw [pow_succ, mul_pow, pow_mul, Complex.I_sq]; push_cast; ring
    rw [e1, e2, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im]; ring

theorem cos_tay (K : ℕ) {y : ℝ} (hy : |y| ≤ (2 * K + 1) / 2) :
    |Real.cos y - Tc K y| ≤ 2 * |y| ^ (2 * K) / ((2 * K).factorial : ℝ) := by
  have hn : ‖Complex.I * y‖ = |y| := by simp
  have hb := Complex.exp_bound' (x := Complex.I * y) (n := 2 * K) (by
    rw [hn, div_le_iff₀ (by positivity)]; push_cast; linarith)
  rw [hn] at hb
  have hc : Real.cos y = (Complex.exp (Complex.I * y)).re := by
    rw [mul_comm]; exact (Complex.exp_ofReal_mul_I_re y).symm
  rw [hc, ← re_sum, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans (hb.trans_eq ?_)
  ring

/-! ## Moments for general width -/

def rowG (W : ℕ) : ℕ → List ℚ
  | 0 => (List.range W).map fun k : ℕ => (2:ℚ) / (2 * (k:ℚ) + 1)
  | n + 1 => List.zipWith (· - ·) (rowG W n) (rowG W n).tail

lemma rowG_spec (W n : ℕ) : ∀ k, k + n < W → ∃ q, (rowG W n)[k]? = some q ∧ (q : ℝ) = J k n := by
  induction n with
  | zero =>
    intro k hk
    refine ⟨2 / (2 * k + 1), ?_, ?_⟩
    · have hk' : k < W := by omega
      simp [rowG, hk']
    · rw [J_zero]; push_cast; ring
  | succ n ih =>
    intro k hk
    obtain ⟨a, ha, ea⟩ := ih k (by omega)
    obtain ⟨b, hb, eb⟩ := ih (k + 1) (by omega)
    refine ⟨a - b, ?_, ?_⟩
    · simp only [rowG, List.getElem?_zipWith, List.getElem?_tail, ha, hb]
    · rw [J_succ, ← ea, ← eb]; exact Rat.cast_sub a b

lemma rowG_getD (W n k : ℕ) (h : k + n < W) : (((rowG W n).getD k 0 : ℚ) : ℝ) = J k n := by
  obtain ⟨q, hq, e⟩ := rowG_spec W n k h
  rw [List.getD_eq_getElem?_getD, hq]; exact e

/-! ## The jP enclosure -/

lemma int_Tc (K n : ℕ) (x : ℝ) : ∫ t in (-1:ℝ)..1, Tc K (x * t) * (1 - t ^ 2) ^ n
    = ∑ k ∈ range K, (-1) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ) * J k n := by
  unfold Tc
  simp only [sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by apply Continuous.intervalIntegrable; fun_prop)]
  apply sum_congr rfl; intro k _
  unfold J
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro t _
  simp only; rw [mul_pow]; ring

theorem jP_enc (K n : ℕ) {x X : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) (hX : X ≤ (2 * K + 1) / 2) :
    |jP n x - x ^ n / (2 ^ (n + 1) * n.factorial) *
        ∑ k ∈ range K, (-1) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ) * J k n|
      ≤ x ^ n / (2 ^ (n + 1) * n.factorial) * (2 * X ^ (2 * K) / ((2 * K).factorial : ℝ) * J 0 n) := by
  set E := 2 * X ^ (2 * K) / ((2 * K).factorial : ℝ)
  have hJ0 : J 0 n = ∫ t in (-1:ℝ)..1, (1 - t ^ 2) ^ n := by unfold J; simp
  have hCp : (0:ℝ) ≤ x ^ n / (2 ^ (n + 1) * n.factorial) := by positivity
  have ci : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume (-1) 1 :=
    fun g hg => hg.intervalIntegrable _ _
  have cT : Continuous fun t : ℝ => Tc K (x * t) * (1 - t ^ 2) ^ n := by unfold Tc; fun_prop
  have cc : Continuous fun t : ℝ => Real.cos (x * t) * (1 - t ^ 2) ^ n := by fun_prop
  have pt : ∀ t ∈ Set.Icc (-1:ℝ) 1, |Real.cos (x * t) - Tc K (x * t)| ≤ E := by
    intro t ht
    have ht1 : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
    have hxt : |x * t| ≤ X := by
      rw [abs_mul, abs_of_nonneg hx]; nlinarith [abs_nonneg t]
    refine (cos_tay K (hxt.trans hX)).trans ?_
    unfold E; gcongr
  have wn : ∀ t ∈ Set.Icc (-1:ℝ) 1, 0 ≤ (1 - t ^ 2) ^ n := by
    intro t ht; apply pow_nonneg; nlinarith [ht.1, ht.2]
  have lo : ∫ t in (-1:ℝ)..1, (Tc K (x * t) * (1 - t ^ 2) ^ n - E * (1 - t ^ 2) ^ n)
      ≤ ∫ t in (-1:ℝ)..1, Real.cos (x * t) * (1 - t ^ 2) ^ n := by
    apply intervalIntegral.integral_mono_on (by norm_num) (ci _ (by fun_prop)) (ci _ cc)
    intro t ht; nlinarith [mul_le_mul_of_nonneg_right (abs_le.1 (pt t ht)).1 (wn t ht)]
  have hi : ∫ t in (-1:ℝ)..1, Real.cos (x * t) * (1 - t ^ 2) ^ n
      ≤ ∫ t in (-1:ℝ)..1, (Tc K (x * t) * (1 - t ^ 2) ^ n + E * (1 - t ^ 2) ^ n) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (ci _ cc) (ci _ (by fun_prop))
    intro t ht; nlinarith [mul_le_mul_of_nonneg_right (abs_le.1 (pt t ht)).2 (wn t ht)]
  rw [intervalIntegral.integral_sub (ci _ cT) (ci _ (by fun_prop)), intervalIntegral.integral_const_mul,
    int_Tc, ← hJ0] at lo
  rw [intervalIntegral.integral_add (ci _ cT) (ci _ (by fun_prop)), intervalIntegral.integral_const_mul,
    int_Tc, ← hJ0] at hi
  unfold jP
  rw [← mul_sub, abs_mul, abs_of_nonneg hCp]
  apply mul_le_mul_of_nonneg_left _ hCp
  rw [abs_le]; constructor <;> linarith

/-! ## Dyadic rounding -/

def rnd (P : ℕ) (q : ℚ) : ℚ := (⌊q * 2 ^ P⌋ : ℚ) / 2 ^ P

lemma rnd_err (P : ℕ) (q : ℚ) : |(q : ℝ) - (rnd P q : ℝ)| ≤ 1 / 2 ^ P := by
  have h1 := Int.floor_le (q * 2 ^ P)
  have h2 := Int.lt_floor_add_one (q * 2 ^ P)
  have hp : (0:ℚ) < 2 ^ P := by positivity
  have e : q - rnd P q = (q * 2 ^ P - ⌊q * 2 ^ P⌋) / 2 ^ P := by unfold rnd; field_simp
  have : |q - rnd P q| ≤ 1 / 2 ^ P := by
    rw [e, abs_div, abs_of_pos hp, div_le_div_iff_of_pos_right hp, abs_le]
    constructor <;> linarith
  have := (Rat.cast_le (K := ℝ)).2 this
  push_cast at this; exact this

/-! ## The `s`-polynomial of `jP n (15 s)` -/

/-- Exact coefficients: `jP n (15 s) ≈ sⁿ Σ_k qx_k s^{2k}`. -/
def qx (K W n : ℕ) : List ℚ := (List.range K).map fun k =>
  (15:ℚ) ^ (n + 2 * k) * (-1) ^ k * (rowG W n).getD k 0 / (2 ^ (n + 1) * (n.factorial : ℚ) * ((2 * k).factorial : ℚ))

def qh (P K W n : ℕ) : List ℚ := (qx K W n).map (rnd P)

def eT (P K W n : ℕ) : ℚ :=
  (15:ℚ) ^ n / (2 ^ (n + 1) * (n.factorial : ℚ)) * (2 * 15 ^ (2 * K) / ((2 * K).factorial : ℚ) * (rowG W n).getD 0 0)
    + K / 2 ^ P

noncomputable def jA (P K W n : ℕ) (s : ℝ) : ℝ :=
  s ^ n * ∑ k ∈ range K, (((qh P K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k)

lemma getD_map_range {K k : ℕ} (hk : k < K) (f : ℕ → ℚ) (g : ℚ → ℚ) :
    (((List.range K).map f).map g).getD k 0 = g (f k) := by
  simp [hk]

theorem jP_s (P K W n : ℕ) (hW : K + n < W) (hK : 15 ≤ ((2 * K + 1 : ℕ) : ℝ) / 2) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    |jP n (15 * s) - jA P K W n s| ≤ (eT P K W n : ℝ) := by
  have hx : 0 ≤ 15 * s := by positivity
  have hxX : 15 * s ≤ 15 := by linarith
  have h := jP_enc K n hx hxX (by push_cast at hK; linarith)
  set C := (15 * s) ^ n / (2 ^ (n + 1) * (n.factorial : ℝ))
  -- exact polynomial
  have hex : C * ∑ k ∈ range K, (-1) ^ k * (15 * s) ^ (2 * k) / ((2 * k).factorial : ℝ) * J k n
      = s ^ n * ∑ k ∈ range K, (((qx K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k) := by
    unfold C; rw [mul_sum, mul_sum]; apply sum_congr rfl; intro k hk
    have hk' := mem_range.1 hk
    unfold qx; rw [List.getD_eq_getElem?_getD]; simp only [List.getElem?_map, List.getElem?_range hk']
    simp only [Option.map_some, Option.getD_some]
    rw [show ((rowG W n).getD k 0) = ((rowG W n).getD k 0) from rfl]
    push_cast; rw [rowG_getD W n k (by omega)]
    rw [mul_pow, mul_pow, pow_add]; field_simp; ring
  rw [hex] at h
  -- rounding
  have hr : |s ^ n * ∑ k ∈ range K, (((qx K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k) - jA P K W n s|
      ≤ K / 2 ^ P := by
    unfold jA; rw [← mul_sub, ← sum_sub_distrib, abs_mul]
    have hsn : |s ^ n| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ h0 h1
    have : |∑ k ∈ range K, ((((qx K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k)
        - (((qh P K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k))| ≤ ∑ k ∈ range K, (1 / 2 ^ P : ℝ) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
      have hk' := mem_range.1 hk
      rw [← sub_mul, abs_mul]
      have e : (qh P K W n).getD k 0 = rnd P ((qx K W n).getD k 0) := by
        have hl : k < (qx K W n).length := by simp [qx, hk']
        unfold qh; rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl, List.getElem_map]
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
  have hE : C * (2 * 15 ^ (2 * K) / ((2 * K).factorial : ℝ) * J 0 n)
      ≤ (15:ℝ) ^ n / (2 ^ (n + 1) * n.factorial) * (2 * 15 ^ (2 * K) / ((2 * K).factorial : ℝ) * J 0 n) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold C; gcongr
  have hc : (eT P K W n : ℝ) = (15:ℝ) ^ n / (2 ^ (n + 1) * n.factorial) *
      (2 * 15 ^ (2 * K) / ((2 * K).factorial : ℝ) * J 0 n) + K / 2 ^ P := by
    unfold eT; push_cast; rw [rowG_getD W n 0 (by omega)]
  rw [hc]
  calc |jP n (15 * s) - jA P K W n s|
      ≤ |jP n (15 * s) - s ^ n * ∑ k ∈ range K, (((qx K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k)|
        + |s ^ n * ∑ k ∈ range K, (((qx K W n).getD k 0 : ℚ) : ℝ) * s ^ (2 * k) - jA P K W n s| :=
        abs_sub_le _ _ _
    _ ≤ _ := add_le_add (h.trans hE) hr

end CmBessel
