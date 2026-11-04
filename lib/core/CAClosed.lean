import Mathlib
import WeilChiB
import DigammaGauss

/-!
# The closed forms `c₀ = −¼ log(27/4)` and `c₁ = ¾ log(3/4)`

`PsiOmega.cA a = Re ψ((1 + a)/2)/4 + A_a(log 2)/√2` is the constant of Theorem B (`PsiOmega.theoremB`), with the
archimedean integral `A_a(u) = (1/2π)∫H_u(r)Re ψ(q + ir/2)dr`, `q = (½ + a)/2` (`PsiOmega.archA`).
* The digamma series `Re ψ(q + ir/2) = −γ + Σ_k (1/(k + 1) − 2s_k/(s_k² + r²))`, `s_k = 2k + 2q`
  (`GammaIntegrals.hasSum_digamma_sub`), is integrated term by term against `H_u` (`CAClosed.hasSum_archA`).
* Each term is `(1/2π)∫H_u(r)·2s/(s² + r²)dr = ∫e^{−s|x|}ĝ_{H_u}(x)dx` (`CAClosed.J_eq`, Fubini with
  `∫e^{−s|x|}cos(rx)dx = 2s/(s² + r²)`, `CAClosed.integral_exp_abs_cos`), and `ĝ_{H_u}` vanishes beyond `u`, so the
  integral is elementary (`CAClosed.J_closed`).
* The resulting series sum to logarithms (`Real.hasSum_log_sub_log_of_abs_lt_one`, `Real.hasSum_pow_div_log_of_abs_lt_one`,
  and `ψ(1) − ψ(½) = 2 log 2`).
Result: `CAClosed.cA_zero : cA 0 = −¼ log(27/4)` and `CAClosed.cA_one : cA 1 = ¾ log(3/4)`. Unconditional.
See `formalisations/d2-density.md`.
-/

open Real Complex Filter Topology Set MeasureTheory WeilForm WeilTest WeilStrip

noncomputable section

namespace CAClosed

open PsiOmega BallPsi

/-! ## Part 1: `∫e^{−s|x|}cos(rx)dx = 2s/(s² + r²)` -/

theorem integral_exp_abs_cos {s : ℝ} (hs : 0 < s) (r : ℝ) :
    ∫ x : ℝ, Real.exp (-(s * |x|)) * Real.cos (r * x) = 2 * s / (s ^ 2 + r ^ 2) := by
  set a : ℂ := s + r * I with hadef
  set b : ℂ := -s + r * I with hbdef
  set G : ℝ → ℂ := fun x => ((Real.exp (-(s * |x|)) : ℝ) : ℂ) * cexp (((r * x : ℝ) : ℂ) * I) with hG
  have ha : 0 < a.re := by simp [a, hs]
  have hb : b.re < 0 := by simp [b, hs]
  have hL : EqOn G (fun x : ℝ => cexp (a * x)) (Iic 0) := by
    intro x hx
    simp only [G]
    rw [abs_of_nonpos (mem_Iic.1 hx), Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hR : EqOn G (fun x : ℝ => cexp (b * x)) (Ioi 0) := by
    intro x hx
    simp only [G]
    rw [abs_of_pos (mem_Ioi.1 hx), Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hiL : IntegrableOn G (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic ha 0).congr_fun hL.symm measurableSet_Iic
  have hiR : IntegrableOn G (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hb 0).congr_fun hR.symm measurableSet_Ioi
  have hGi : Integrable G := by
    have := hiL.union hiR
    rwa [Iic_union_Ioi, integrableOn_univ] at this
  have hval : ∫ x, G x = ((2 * s / (s ^ 2 + r ^ 2) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hiL hiR, setIntegral_congr_fun measurableSet_Iic hL,
      setIntegral_congr_fun measurableSet_Ioi hR, integral_exp_mul_complex_Iic ha,
      integral_exp_mul_complex_Ioi hb]
    have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
    have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
    have hq : ((s ^ 2 + r ^ 2 : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
    have hab : a * b = -((s ^ 2 + r ^ 2 : ℝ) : ℂ) := by
      rw [hadef, hbdef]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show (1 : ℂ) / a + -1 / b = (b - a) / (a * b) by field_simp; ring, hab,
      show b - a = -(2 * s) by rw [hadef, hbdef]; ring]
    push_cast
    field_simp
  have hre := congrArg Complex.re hval
  have hre2 : (∫ x, G x).re = ∫ x, (G x).re := (integral_re hGi).symm
  rw [hre2, Complex.ofReal_re] at hre
  rw [← hre]
  congr 1; funext x
  simp only [G]
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-! ## Part 2: `(1/2π)∫H_u(r)·2s/(s² + r²)dr = ∫e^{−s|x|}ĝ_{H_u}(x)dx` -/

theorem continuous_HuR (u : ℝ) : Continuous (HuR u) := by
  unfold HuR
  exact (by fun_prop : Continuous fun r : ℝ => Real.cos (r * u) - Real.cosh (u / 2)).div (by fun_prop)
    fun r => by positivity

theorem abs_HuR_le (u r : ℝ) : |HuR u r| ≤ (1 + Real.cosh (u / 2)) * (1 / (r ^ 2 + 1 / 4)) := by
  unfold HuR
  have h0 : (0 : ℝ) < r ^ 2 + 1 / 4 := by positivity
  rw [abs_div, abs_of_pos h0, mul_one_div]
  refine div_le_div_of_nonneg_right ?_ h0.le
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos (Real.cosh_pos _)]
  linarith [Real.abs_cos_le_one (r * u)]

theorem integrable_HuR (u : ℝ) : Integrable (HuR u) :=
  (integrable_cauchy.const_mul (1 + Real.cosh (u / 2))).mono' (continuous_HuR u).aestronglyMeasurable
    (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact abs_HuR_le u r)

theorem J_eq (u : ℝ) {s : ℝ} (hs : 0 < s) :
    1 / (2 * π) * ∫ r, HuR u r * (2 * s / (s ^ 2 + r ^ 2)) =
      ∫ x, Real.exp (-(s * |x|)) * gh (HuR u) x := by
  unfold gh
  have hI : Integrable (Function.uncurry fun (x r : ℝ) => Real.exp (-(s * |x|)) * (HuR u r * Real.cos (r * x)))
      (volume.prod volume) := by
    have hp := (WeilStrip.integrable_exp_neg_abs hs).mul_prod (integrable_HuR u)
    refine hp.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (Continuous.aestronglyMeasurable (by
        have := continuous_HuR u
        fun_prop))
    · obtain ⟨x, r⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs]
      rw [abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      calc |HuR u r| * |Real.cos (r * x)| ≤ |HuR u r| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |HuR u r| := mul_one _
  have e1 : (fun x : ℝ => Real.exp (-(s * |x|)) * (1 / (2 * π) * ∫ r, HuR u r * Real.cos (r * x))) =
      fun x => 1 / (2 * π) * ∫ r, Real.exp (-(s * |x|)) * (HuR u r * Real.cos (r * x)) := by
    funext x; rw [integral_const_mul]; ring
  rw [e1, integral_const_mul, integral_integral_swap hI]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  have e2 : (fun x : ℝ => Real.exp (-(s * |x|)) * (HuR u r * Real.cos (r * x))) =
      fun x => HuR u r * (Real.exp (-(s * |x|)) * Real.cos (r * x)) := by funext x; ring
  rw [e2, integral_const_mul, integral_exp_abs_cos hs]

/-! ## Part 3: the elementary integral at `u = log 2` -/

/-- `∫_0^{log 2} e^{−mx}dx`. -/
def Ie (m : ℕ) : ℝ := ∫ x in (0 : ℝ)..Real.log 2, Real.exp (-(m * x))

theorem exp_neg_nat_log_two (m : ℕ) : Real.exp (-(m * Real.log 2)) = (1 / 2) ^ m := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), one_div_pow, one_div]

theorem Ie_zero : Ie 0 = Real.log 2 := by simp [Ie]

theorem Ie_pos {m : ℕ} (hm : m ≠ 0) : Ie m = (1 - (1 / 2) ^ m) / m := by
  have hc : (-(m : ℝ)) ≠ 0 := by simp [hm]
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := Real.log 2) Real.exp hc
  simp only [neg_mul, mul_zero] at h
  rw [Ie, h, integral_exp, Real.exp_zero, exp_neg_nat_log_two, smul_eq_mul]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  ring

theorem gh_even (u x : ℝ) : gh (HuR u) |x| = gh (HuR u) x := by
  rw [gh_Hu, gh_Hu, abs_abs]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, show u + -x = u - x by ring, show u - -x = u + x by ring]; ring

theorem J_closed (m : ℕ) :
    ∫ x, Real.exp (-((m + 1 / 2) * |x|)) * gh (HuR (Real.log 2)) x = (Ie m - 2 * Ie (m + 1)) / √2 := by
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  set f : ℝ → ℝ := fun y => Real.exp (-((m + 1 / 2) * y)) * gh (HuR L) y with hf
  have e0 : (fun x : ℝ => Real.exp (-((m + 1 / 2) * |x|)) * gh (HuR L) x) = fun x => f |x| := by
    funext x; simp only [f]; rw [gh_even]
  rw [e0, integral_comp_abs]
  have hsub : ∫ x in Ioi (0 : ℝ), f x = ∫ x in Ioc 0 L, f x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun x hx => by
        have hx1 : 0 < x := hx.1
        have hx2 : L < x := by
          by_contra h; exact hx.2 ⟨hx1, not_lt.1 h⟩
        simp only [f]; rw [gh_Hu_eq_zero hL0.le hx2.le, mul_zero]
  rw [hsub, ← intervalIntegral.integral_of_le hL0.le]
  obtain ⟨hc0, -⟩ := cosh_sinh_log_two
  have hc : Real.cosh (L / 2) = 3 / (2 * √2) := by rw [hL]; exact hc0
  have hE : Real.exp (-(L / 2)) = 1 / √2 := by
    rw [Real.exp_neg, exp_log_half (by norm_num), one_div]
  have e1 : EqOn f (fun x => (1 / √2) / 2 * (Real.exp (-(m * x)) + Real.exp (-((m + 1 : ℕ) * x)))
      - 3 / (2 * √2) * Real.exp (-((m + 1 : ℕ) * x))) (uIcc 0 L) := by
    intro x hx
    rw [uIcc_of_le hL0.le] at hx
    simp only [f]
    rw [gh_Hu, abs_of_nonneg (by linarith [hx.1] : 0 ≤ L + x), abs_of_nonneg (by linarith [hx.2] : 0 ≤ L - x),
      abs_of_nonneg hx.1, hc, ← hE]
    push_cast
    rw [show -(L + x) / 2 = -(L / 2) + -(x / 2) by ring, show -(L - x) / 2 = -(L / 2) + x / 2 by ring,
      show -x / 2 = -(x / 2) by ring, Real.exp_add, Real.exp_add]
    have h1 : Real.exp (-((m + 1 / 2) * x)) * Real.exp (-(x / 2)) = Real.exp (-((m + 1) * x)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-((m + 1 / 2) * x)) * Real.exp (x / 2) = Real.exp (-(m * x)) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (Real.exp (-(L / 2)) / 2) * h1 + (Real.exp (-(L / 2)) / 2) * h2
      - 3 / (2 * √2) * h1
  rw [intervalIntegral.integral_congr e1]
  have ci : ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => Real.exp (-(c * x))) volume 0 L := fun c =>
    (by fun_prop : Continuous fun x : ℝ => Real.exp (-(c * x))).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub ((ci _).add (ci _) |>.const_mul _) ((ci _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (ci _) (ci _)]
  simp only [Ie, ← hL]
  have hs0 : √2 ≠ 0 := by positivity
  field_simp
  ring

/-! ## Part 4: the digamma series, integrated term by term -/

/-- `s_k = 2k + ½ + a`. -/
def sk (a k : ℕ) : ℝ := 2 * k + 1 / 2 + a

theorem sk_pos (a k : ℕ) : 0 < sk a k := by unfold sk; positivity

/-- The `k`-th term `1/(k + 1) − 2s_k/(s_k² + r²)` of `Re ψ(q + ir/2) + γ`. -/
def tk (a k : ℕ) (r : ℝ) : ℝ := 1 / (k + 1) - 2 * sk a k / (sk a k ^ 2 + r ^ 2)

/-- The series of `Re ψ(q + ir/2)`, with the constant `−γ` in front. -/
def gk (a : ℕ) : ℕ → ℝ → ℝ
  | 0, _ => -eulerMascheroniConstant
  | k + 1, r => tk a k r

theorem psi_series (a : ℕ) (r : ℝ) :
    HasSum (fun k => gk a k r) (Complex.digamma ((1 / 2 + I * r + a) / 2)).re := by
  set z : ℂ := (1 / 2 + I * r + a) / 2 with hz
  have hzr : 0 < z.re := by simp [z]; positivity
  have h := Complex.hasSum_re (GammaIntegrals.hasSum_digamma_sub hzr (w := 1) (by simp))
  rw [Complex.digamma_one] at h
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.range_one, Finset.sum_singleton]
  have e : (Complex.digamma z - -(eulerMascheroniConstant : ℂ)).re = (Complex.digamma z).re - gk a 0 r := by
    simp [gk]
  rw [e] at h
  refine h.congr_fun fun k => ?_
  simp only [gk, tk, sk]
  have h1 : (1 / ((k : ℂ) + 1)).re = 1 / ((k : ℝ) + 1) := by
    rw [show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_one,
      ← Complex.ofReal_div, Complex.ofReal_re]
  rw [Complex.sub_re, h1, one_div, one_div ((k : ℂ) + z), Complex.inv_re, Complex.normSq_apply]
  simp only [z, Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, Complex.div_re,
    Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  norm_num
  have hpos : (0 : ℝ) < (2 * k + 1 / 2 + a) ^ 2 + r ^ 2 := by positivity
  have hpos' : (0 : ℝ) < ((k : ℝ) + (1 / 2 + a) / 2) ^ 2 + (r / 2) ^ 2 := by positivity
  field_simp
  ring

theorem integral_inv_sq_add {s : ℝ} (hs : 0 < s) : ∫ r : ℝ, 1 / (s ^ 2 + r ^ 2) = π / s := by
  have e : (fun r : ℝ => 1 / (s ^ 2 + r ^ 2)) = fun r => s⁻¹ ^ 2 * (1 + (r / s) ^ 2)⁻¹ := by
    funext r; field_simp
  rw [e, integral_const_mul, Measure.integral_comp_div (fun r => (1 + r ^ 2)⁻¹) s,
    integral_univ_inv_one_add_sq, abs_of_pos hs, smul_eq_mul]
  field_simp

theorem integrable_inv_sq_add {s : ℝ} (hs : 0 < s) : Integrable fun r : ℝ => 1 / (s ^ 2 + r ^ 2) := by
  have e : (fun r : ℝ => 1 / (s ^ 2 + r ^ 2)) = fun r => s⁻¹ ^ 2 * (1 + (r / s) ^ 2)⁻¹ := by
    funext r; field_simp
  rw [e]
  exact ((integrable_inv_one_add_sq.comp_div hs.ne')).const_mul _

/-- `B = 1 + cosh(u/2)` bounds `(r² + ¼)|H_u(r)|`. -/
def Bc (u : ℝ) : ℝ := 1 + Real.cosh (u / 2)

theorem Bc_pos (u : ℝ) : 0 < Bc u := by unfold Bc; linarith [Real.cosh_pos (u / 2)]

/-- The dominating function of the `k`-th term. -/
def bd (u : ℝ) (a : ℕ) : ℕ → ℝ → ℝ
  | 0, r => |eulerMascheroniConstant| * |HuR u r|
  | k + 1, r => Bc u / (k + 1) * (1 / (sk a k ^ 2 + r ^ 2) + 2 / sk a k * (1 / (r ^ 2 + 1 / 4)))

theorem abs_tk_le {a : ℕ} (ha : a ≤ 1) (k : ℕ) (r : ℝ) :
    |tk a k r| ≤ (r ^ 2 + 2 * sk a k) / ((k + 1) * (sk a k ^ 2 + r ^ 2)) := by
  have hs := sk_pos a k
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hd : (0 : ℝ) < sk a k ^ 2 + r ^ 2 := by positivity
  have e : tk a k r = (r ^ 2 + sk a k * ((a : ℝ) - 3 / 2)) / ((k + 1) * (sk a k ^ 2 + r ^ 2)) := by
    unfold tk; field_simp; unfold sk; ring
  have ha' : (a : ℝ) ≤ 1 := by exact_mod_cast ha
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k + 1) * (sk a k ^ 2 + r ^ 2))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg r, Nat.cast_nonneg (α := ℝ) a]

theorem norm_le_bd {a : ℕ} (ha : a ≤ 1) (u : ℝ) (k : ℕ) (r : ℝ) :
    ‖HuR u r * gk a k r‖ ≤ bd u a k r := by
  rw [Real.norm_eq_abs, abs_mul]
  cases k with
  | zero => simp only [gk, bd, abs_neg]; ring_nf; rfl
  | succ k =>
    simp only [gk, bd]
    have hs := sk_pos a k
    have hH := abs_HuR_le u r
    have ht := abs_tk_le ha k r
    have hk : (0 : ℝ) < k + 1 := by positivity
    have h4 : (0 : ℝ) < r ^ 2 + 1 / 4 := by positivity
    have hd : (0 : ℝ) < sk a k ^ 2 + r ^ 2 := by positivity
    calc |HuR u r| * |tk a k r| ≤ (Bc u * (1 / (r ^ 2 + 1 / 4))) *
          ((r ^ 2 + 2 * sk a k) / ((k + 1) * (sk a k ^ 2 + r ^ 2))) :=
          mul_le_mul hH ht (abs_nonneg _) (by unfold Bc; positivity)
      _ ≤ _ := by
          rw [show Bc u * (1 / (r ^ 2 + 1 / 4)) * ((r ^ 2 + 2 * sk a k) / ((k + 1) * (sk a k ^ 2 + r ^ 2))) =
            Bc u / (k + 1) * ((r ^ 2 + 2 * sk a k) / ((r ^ 2 + 1 / 4) * (sk a k ^ 2 + r ^ 2))) by
              field_simp]
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Bc_pos u).le hk.le)
          set S := sk a k
          calc (r ^ 2 + 2 * S) / ((r ^ 2 + 1 / 4) * (S ^ 2 + r ^ 2))
              = (r ^ 2 * S + 2 * S ^ 2) / (S * (r ^ 2 + 1 / 4) * (S ^ 2 + r ^ 2)) := by
                field_simp
            _ ≤ (S * (r ^ 2 + 1 / 4) + 2 * (S ^ 2 + r ^ 2)) / (S * (r ^ 2 + 1 / 4) * (S ^ 2 + r ^ 2)) :=
                div_le_div_of_nonneg_right (by nlinarith [sq_nonneg r]) (by positivity)
            _ = 1 / (S ^ 2 + r ^ 2) + 2 / S * (1 / (r ^ 2 + 1 / 4)) := by
                field_simp

theorem integrable_bd (u : ℝ) (a k : ℕ) : Integrable (bd u a k) := by
  cases k with
  | zero => exact (integrable_HuR u).abs.const_mul _
  | succ k =>
    exact (((integrable_inv_sq_add (sk_pos a k)).add (integrable_cauchy.const_mul _)).const_mul _)

/-- `∫ bd`. -/
def cbd (u : ℝ) (a : ℕ) (k : ℕ) : ℝ := ∫ r, bd u a k r

theorem cbd_succ (u : ℝ) (a k : ℕ) : cbd u a (k + 1) = Bc u / (k + 1) * (5 * π / sk a k) := by
  have hs := sk_pos a k
  have hc : ∫ r : ℝ, 1 / (r ^ 2 + 1 / 4) = 2 * π := by
    have := integral_inv_sq_add (by norm_num : (0 : ℝ) < 1 / 2)
    rw [show π / (1 / 2) = 2 * π by ring] at this
    rw [← this]; congr 1; funext r; ring_nf
  simp only [cbd, bd]
  rw [integral_const_mul, integral_add (integrable_inv_sq_add hs) (integrable_cauchy.const_mul _),
    integral_const_mul, integral_inv_sq_add hs, hc]
  field_simp
  ring

theorem summable_cbd (u : ℝ) (a : ℕ) : Summable (cbd u a) := by
  refine (summable_nat_add_iff 1).1 ?_
  have hb := Bc_pos u
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((GammaIntegrals.summable_inv_sq).mul_left (10 * π * Bc u))
  · rw [cbd_succ]; have := sk_pos a k; positivity
  · rw [cbd_succ]
    have hs := sk_pos a k
    have hk : (0 : ℝ) < k + 1 := by positivity
    have hsk : ((k : ℝ) + 1) / 2 ≤ sk a k := by unfold sk; have := Nat.cast_nonneg (α := ℝ) a; linarith
    rw [show Bc u / (k + 1) * (5 * π / sk a k) = 5 * π * Bc u / ((k + 1) * sk a k) by field_simp,
      show 10 * π * Bc u * (1 / ((k : ℝ) + 1) ^ 2) = 5 * π * Bc u / ((k + 1) * ((k + 1) / 2)) by field_simp; ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hsk hk.le)

theorem integrable_Hg {a : ℕ} (ha : a ≤ 1) (u : ℝ) (k : ℕ) : Integrable fun r => HuR u r * gk a k r := by
  refine (integrable_bd u a k).mono' ?_ (Eventually.of_forall fun r => norm_le_bd ha u k r)
  cases k with
  | zero => exact ((continuous_HuR u).mul continuous_const).aestronglyMeasurable
  | succ k =>
    have hs := sk_pos a k
    refine ((continuous_HuR u).mul ?_).aestronglyMeasurable
    unfold gk tk
    exact continuous_const.sub (continuous_const.div (by fun_prop) fun r => by positivity)

/-- **The archimedean integral as a series**: `A_a(u) = Σ_k (1/2π)∫H_u(r)g_k(r)dr`. -/
theorem hasSum_archA {a : ℕ} (ha : a ≤ 1) (u : ℝ) :
    HasSum (fun k => 1 / (2 * π) * ∫ r, HuR u r * gk a k r) (archA a u) := by
  have hpt : ∀ r, HuR u r * (Complex.digamma ((1 / 2 + I * r + a) / 2)).re = ∑' k, HuR u r * gk a k r :=
    fun r => ((psi_series a r).mul_left (HuR u r)).tsum_eq.symm
  have hlin : ∑' k, ∫⁻ r, ‖HuR u r * gk a k r‖ₑ ≠ ⊤ := by
    have hle : ∀ k, ∫⁻ r, ‖HuR u r * gk a k r‖ₑ ≤ ENNReal.ofReal (cbd u a k) := fun k => by
      rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_Hg ha u k)]
      exact ENNReal.ofReal_le_ofReal (integral_mono (integrable_Hg ha u k).norm (integrable_bd u a k)
        fun r => norm_le_bd ha u k r)
    have hnn : ∀ k, 0 ≤ cbd u a k := fun k =>
      integral_nonneg fun r => (norm_nonneg _).trans (norm_le_bd ha u k r)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn (summable_cbd u a)]
    exact ENNReal.ofReal_ne_top
  have hint := integral_tsum (fun k => (integrable_Hg ha u k).aestronglyMeasurable) hlin
  have hsum : Summable fun k => ∫ r, HuR u r * gk a k r :=
    Summable.of_norm_bounded (summable_cbd u a) fun k =>
      (norm_integral_le_integral_norm _).trans (integral_mono (integrable_Hg ha u k).norm
        (integrable_bd u a k) fun r => norm_le_bd ha u k r)
  have e : archA a u = 1 / (2 * π) * ∑' k, ∫ r, HuR u r * gk a k r := by
    rw [archA, ← hint]; congr 1; exact integral_congr_ae (Eventually.of_forall hpt)
  rw [e]
  exact hsum.hasSum.mul_left _

/-! ## Part 5: the terms, and their sums -/

theorem gh0 : gh (HuR (Real.log 2)) 0 = -(1 / (2 * √2)) := by
  rw [gh_Hu_zero (Real.log_nonneg (by norm_num)), cosh_sinh_log_two.2]

theorem integral_HuR : 1 / (2 * π) * ∫ r, HuR (Real.log 2) r = -(1 / (2 * √2)) := by
  rw [← gh0, gh]; congr 1; congr 1; funext r; simp

theorem term_zero (a : ℕ) :
    1 / (2 * π) * ∫ r, HuR (Real.log 2) r * gk a 0 r = eulerMascheroniConstant / (2 * √2) := by
  simp only [gk]
  rw [integral_mul_const, ← mul_assoc, integral_HuR]; ring

theorem term_succ (a k : ℕ) :
    1 / (2 * π) * ∫ r, HuR (Real.log 2) r * gk a (k + 1) r =
      -(1 / (2 * √2)) / (k + 1) - (Ie (2 * k + a) - 2 * Ie (2 * k + a + 1)) / √2 := by
  have hs := sk_pos a k
  have hsk : sk a k = ((2 * k + a : ℕ) : ℝ) + 1 / 2 := by unfold sk; push_cast; ring
  simp only [gk, tk]
  have hi1 : Integrable fun r => HuR (Real.log 2) r * (1 / ((k : ℝ) + 1)) := (integrable_HuR _).mul_const _
  have hi2 : Integrable fun r => HuR (Real.log 2) r * (2 * sk a k / (sk a k ^ 2 + r ^ 2)) := by
    refine ((integrable_HuR (Real.log 2)).norm.const_mul (2 / sk a k)).mono'
      ((continuous_HuR _).mul (continuous_const.div (by fun_prop) fun r => by positivity)).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    have hd : (0 : ℝ) < sk a k ^ 2 + r ^ 2 := by positivity
    have hb : 2 * sk a k / (sk a k ^ 2 + r ^ 2) ≤ 2 / sk a k := by
      rw [div_le_div_iff₀ hd hs]; nlinarith [sq_nonneg r]
    rw [norm_mul, Real.norm_eq_abs (2 * sk a k / _), abs_of_pos (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have e : (fun r => HuR (Real.log 2) r * (1 / ((k : ℝ) + 1) - 2 * sk a k / (sk a k ^ 2 + r ^ 2))) =
      fun r => HuR (Real.log 2) r * (1 / ((k : ℝ) + 1)) - HuR (Real.log 2) r * (2 * sk a k / (sk a k ^ 2 + r ^ 2)) := by
    funext r; ring
  rw [e, integral_sub hi1 hi2, mul_sub, integral_mul_const, ← mul_assoc, integral_HuR, J_eq _ hs, hsk,
    J_closed]
  ring

theorem hasSum_altH : HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) - 1 / (2 * k + 2)) (Real.log 2) := by
  have h := Complex.hasSum_re (GammaIntegrals.hasSum_digamma_sub (z := 1) (w := 1 / 2) (by simp) (by norm_num))
  rw [Complex.digamma_one, Complex.digamma_one_half] at h
  have hv : (-(eulerMascheroniConstant : ℂ) - (-2 * Complex.log 2 - eulerMascheroniConstant)).re = 2 * Real.log 2 := by
    rw [show (-(eulerMascheroniConstant : ℂ) - (-2 * Complex.log 2 - eulerMascheroniConstant)) =
      2 * Complex.log 2 by ring]
    simp [Complex.log_re]
  rw [hv] at h
  have h2 := h.mul_left (1 / 2)
  rw [show 1 / 2 * (2 * Real.log 2) = Real.log 2 by ring] at h2
  refine h2.congr_fun fun k => ?_
  have e1 : (1 / ((k : ℂ) + 1 / 2)).re = 2 / (2 * k + 1) := by
    rw [show (k : ℂ) + 1 / 2 = (((k : ℝ) + 1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_one,
      ← Complex.ofReal_div, Complex.ofReal_re]; field_simp
  have e2 : (1 / ((k : ℂ) + 1)).re = 1 / (k + 1) := by
    rw [show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_one,
      ← Complex.ofReal_div, Complex.ofReal_re]
  rw [Complex.sub_re, e1, e2]
  field_simp

theorem hasSum_tele : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / (k + 2)) 1 := by
  have h := Complex.hasSum_re (GammaIntegrals.hasSum_digamma_sub (z := 2) (w := 1) (by norm_num) (by norm_num))
  have h2 : Complex.digamma 2 = Complex.digamma 1 + 1 := by
    have := Complex.digamma_apply_add_one 1 (by intro m hm; have := congrArg Complex.re hm; simp at this; linarith)
    rw [show (1 : ℂ) + 1 = 2 by norm_num] at this; rw [this]; simp
  rw [h2, show Complex.digamma 1 + 1 - Complex.digamma 1 = 1 by ring, Complex.one_re] at h
  refine h.congr_fun fun k => ?_
  have e : ∀ c : ℝ, (1 / ((k : ℂ) + c)).re = 1 / (k + c) := fun c => by
    rw [show (k : ℂ) + c = (((k : ℝ) + c : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_one,
      ← Complex.ofReal_div, Complex.ofReal_re]
  have e1 := e 1; have e2 := e 2
  push_cast at e1 e2
  rw [Complex.sub_re, e1, e2]

theorem hasSum_log3 : HasSum (fun k : ℕ => (1 / 4 : ℝ) ^ k / (2 * k + 1)) (Real.log 3) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := 1 / 2) (by norm_num [abs_of_pos])
  rw [show Real.log (1 + 1 / 2) - Real.log (1 - 1 / 2) = Real.log 3 by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num] at h
  refine h.congr_fun fun k => ?_
  rw [pow_succ, pow_mul]; norm_num; field_simp

theorem hasSum_log43 : HasSum (fun k : ℕ => (1 / 4 : ℝ) ^ (k + 1) / (k + 1)) (Real.log (4 / 3)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / 4) (by norm_num [abs_of_pos])
  rwa [show -Real.log (1 - 1 / 4) = Real.log (4 / 3) by
    rw [← Real.log_inv]; norm_num] at h

theorem Ie_odd (k : ℕ) : Ie (2 * k + 1) = 2 * (1 - (1 / 2) * (1 / 4 : ℝ) ^ k) / (2 * (2 * k + 1)) := by
  rw [Ie_pos (by omega), pow_succ, pow_mul]; push_cast; norm_num; field_simp

theorem Ie_even (k : ℕ) : Ie (2 * k + 2) = (1 - (1 / 4 : ℝ) ^ (k + 1)) / (2 * k + 2) := by
  rw [Ie_pos (by omega), show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]; push_cast; norm_num; ring

/-- The series for `a = 1`. -/
theorem hasSum_one : HasSum (fun k : ℕ => -(1 / (2 * √2)) / (k + 1) - (Ie (2 * k + 1) - 2 * Ie (2 * k + 1 + 1)) / √2)
    ((-Real.log 2 + Real.log 3 / 2 - Real.log (4 / 3)) / √2) := by
  have h := ((hasSum_altH.neg.add (hasSum_log3.mul_left (1 / 2))).sub hasSum_log43).div_const √2
  refine (h.congr_fun fun k => ?_).trans_eq ?_
  · rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, Ie_odd, Ie_even]
    have hs0 : √2 ≠ 0 := by positivity
    have hk : (0 : ℝ) < k + 1 := by positivity
    have hk2 : (0 : ℝ) < 2 * k + 1 := by positivity
    field_simp
    ring
  · ring

/-- The series for `a = 0`. -/
theorem hasSum_zero : HasSum (fun k : ℕ => -(1 / (2 * √2)) / (k + 1) - (Ie (2 * k + 0) - 2 * Ie (2 * k + 0 + 1)) / √2)
    ((Real.log 2 + Real.log (4 / 3) / 2 - Real.log 3) / √2) := by
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, add_zero, zero_add, Ie_zero]
  rw [show Ie 1 = 1 / 2 by rw [Ie_pos one_ne_zero]; norm_num]
  have hB1 : HasSum (fun j : ℕ => 1 / (2 * (j : ℝ) + 3) - 1 / (2 * j + 4)) (Real.log 2 - 1 / 2) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_altH
    simp only [Finset.range_one, Finset.sum_singleton] at this
    refine (this.congr_fun fun j => ?_).trans_eq (by norm_num)
    push_cast; ring_nf
  have hB2 : HasSum (fun j : ℕ => 1 / (2 * (j : ℝ) + 4) - 1 / (2 * j + 2)) (-(1 / 2)) := by
    refine ((hasSum_tele.mul_left (-(1 / 2))).congr_fun fun j => ?_).trans_eq (by ring)
    have : (0 : ℝ) < j + 1 := by positivity
    field_simp; ring
  have hB4 : HasSum (fun j : ℕ => (1 / 4 : ℝ) ^ (j + 1) / (2 * j + 3)) (Real.log 3 - 1) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_log3
    simp only [Finset.range_one, Finset.sum_singleton] at this
    refine (this.congr_fun fun j => ?_).trans_eq (by norm_num)
    push_cast; ring_nf
  have h := ((((hB1.mul_left 2).add hB2).add (hasSum_log43.div_const 2)).sub hB4).div_const √2
  refine (h.congr_fun fun j => ?_).trans_eq ?_
  · rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 1 = 2 * j + 3 by ring, Ie_even,
      Ie_pos (by omega : 2 * j + 3 ≠ 0)]
    have hs0 : √2 ≠ 0 := by positivity
    have hj : (0 : ℝ) < j + 1 := by positivity
    push_cast
    rw [show (1 / 2 : ℝ) ^ (2 * j + 3) = (1 / 2) * (1 / 4) ^ (j + 1) by
      rw [show 2 * j + 3 = 2 * (j + 1) + 1 by ring, pow_succ, pow_mul]; norm_num; ring]
    field_simp
    ring
  · have hs0 : √2 ≠ 0 := by positivity
    field_simp
    ring

/-- `A_a(log 2) = γ/(2√2) + V_a`. -/
theorem archA_eq {a : ℕ} (ha : a ≤ 1) {V : ℝ}
    (hV : HasSum (fun k : ℕ => -(1 / (2 * √2)) / (k + 1) - (Ie (2 * k + a) - 2 * Ie (2 * k + a + 1)) / √2) V) :
    archA a (Real.log 2) = eulerMascheroniConstant / (2 * √2) + V := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_archA ha (Real.log 2))
  simp only [Finset.range_one, Finset.sum_singleton, term_zero, term_succ] at h
  have := h.unique hV
  linarith

theorem log_four_div_three : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- **`c₀ = −¼ log(27/4)`.** -/
theorem cA_zero : cA 0 = -(1 / 4) * Real.log (27 / 4) := by
  have hA := archA_eq (le_refl 0 |>.trans zero_le_one) hasSum_zero
  have hψ : (Complex.digamma ((1 + ((0 : ℕ) : ℂ)) / 2)).re = -2 * Real.log 2 - eulerMascheroniConstant := by
    rw [show (1 + ((0 : ℕ) : ℂ)) / 2 = 1 / 2 by push_cast; ring, Complex.digamma_one_half]
    simp [Complex.log_re]
  rw [cA, hψ, hA, log_four_div_three, Real.log_div (by norm_num) (by norm_num),
    show (27 : ℝ) = 3 ^ 3 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : √2 ≠ 0 := by positivity
  push_cast
  field_simp
  rw [hs2]
  ring

/-- **`c₁ = ¾ log(3/4)`.** -/
theorem cA_one : cA 1 = 3 / 4 * Real.log (3 / 4) := by
  have hA := archA_eq le_rfl hasSum_one
  have hψ : (Complex.digamma ((1 + ((1 : ℕ) : ℂ)) / 2)).re = -eulerMascheroniConstant := by
    rw [show (1 + ((1 : ℕ) : ℂ)) / 2 = 1 by push_cast; ring, Complex.digamma_one]; simp
  rw [cA, hψ, hA, log_four_div_three, Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : √2 ≠ 0 := by positivity
  push_cast
  field_simp
  rw [hs2]
  ring

end CAClosed
