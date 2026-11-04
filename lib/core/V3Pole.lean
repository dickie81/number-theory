import Mathlib
import V3Zhu
import V3CertD
import WeilConst

/-! # Connes–Consani's subspace `V'` in mode coefficients, and the pole vector at `λ = log 3`

For `f = sc (hx N x y)`, supported in `[−L*, L*]`, `L* = λ/2`:

* `∫ f e^{−u/2} = √λ (Σ xᵢ p̃₂ᵢ + Σ yᵢ p̃₂ᵢ₊₁)` and `∫ f e^{u/2} = √λ (Σ xᵢ p̃₂ᵢ − Σ yᵢ p̃₂ᵢ₊₁)` (`poleR_sc_hx`,
  `poleL_sc_hx`), with `p̃ₙ = √(2n+1)·iₙ(λ/4) = V3Zhu.pole3 n`: Rodrigues' identity `pole_mode_gen` for the weight
  `e^{−au}` at `a = λ/2`;
* `∫ f = √λ·x₀` (`int_sc_hx`): the same identity at `a = 0`.

So `f ∈ V'` exactly when `x₀ = 0`, `Σ xᵢ p̃₂ᵢ = 0` and `Σ yᵢ p̃₂ᵢ₊₁ = 0`. The even pole vector is enclosed to `10⁻¹²`
(`pole3_enc`): `iₙ` is increasing on `[0, ∞)`, so `iₙ(λ/4)` lies between its values at `l3lo/4` and `l3hi/4`, which
a degree-10 Taylor polynomial of `cosh` with exact moments encloses (kernel check `pole3_chk`). -/

namespace V3Pole

open Real Finset MeasureTheory WeilTailB WeilPlanch WeilModes V3Scale
open scoped Nat

/-! ## Rodrigues' identity for the weight `e^{−au}` -/

theorem pole_mode_gen (a : ℝ) (n : ℕ) :
    ∫ u in (-(1/2):ℝ)..(1/2), (Real.sqrt (2 * n + 1) * (sL n).eval (u + 1 / 2)) * Real.exp (-(a * u))
      = Real.sqrt (2 * n + 1) * iP n (a / 2) := by
  set J := ∫ y in (0:ℝ)..1, Real.exp (-a * y) * (wP n).eval y
  set I := ∫ y in (0:ℝ)..1, Real.exp (-a * y) * (sL n).eval y
  have hIJ : (n ! : ℝ) * I = a ^ n * J := by
    have := rod_ibp_real (-a) n; rw [neg_neg] at this; exact this
  have hL : ∫ u in (-(1/2):ℝ)..(1/2), (Real.sqrt (2 * n + 1) * (sL n).eval (u + 1 / 2)) * Real.exp (-(a * u))
      = Real.sqrt (2 * n + 1) * Real.exp (a / 2) * I := by
    have e : ∀ u : ℝ, (Real.sqrt (2 * n + 1) * (sL n).eval (u + 1 / 2)) * Real.exp (-(a * u))
        = (fun y => Real.sqrt (2 * n + 1) * Real.exp (a / 2) * (Real.exp (-a * y) * (sL n).eval y)) (u + 1 / 2) := by
      intro u; simp only
      rw [mul_assoc (Real.sqrt _), mul_assoc (Real.sqrt _), ← mul_assoc (Real.exp (a / 2)), ← Real.exp_add]
      rw [show a / 2 + -a * (u + 1 / 2) = -(a * u) by ring]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_comp_add_right
      (fun y => Real.sqrt (2 * n + 1) * Real.exp (a / 2) * (Real.exp (-a * y) * (sL n).eval y)) (1/2)]
    norm_num [intervalIntegral.integral_const_mul, I]
  have hcosh : ∫ y in (0:ℝ)..1, Real.cosh (a / 2 * (2 * y - 1)) * (wP n).eval y = Real.exp (a / 2) * J := by
    have hsym : ∫ y in (0:ℝ)..1, Real.exp (a / 2 * (2 * y - 1)) * (wP n).eval y
        = ∫ y in (0:ℝ)..1, Real.exp (-(a / 2 * (2 * y - 1))) * (wP n).eval y := by
      have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
        (fun y : ℝ => Real.exp (a / 2 * (2 * y - 1)) * (wP n).eval y) 1
      simp only [sub_zero, sub_self] at this
      rw [← this]; congr 1; funext y; simp only [wP_eval]
      rw [show a / 2 * (2 * (1 - y) - 1) = -(a / 2 * (2 * y - 1)) by ring]; ring
    have e : ∀ y : ℝ, Real.cosh (a / 2 * (2 * y - 1)) * (wP n).eval y
        = (Real.exp (a / 2 * (2 * y - 1)) * (wP n).eval y
            + Real.exp (-(a / 2 * (2 * y - 1))) * (wP n).eval y) / 2 := by
      intro y; rw [Real.cosh_eq]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop), hsym]
    have : ∫ y in (0:ℝ)..1, Real.exp (-(a / 2 * (2 * y - 1))) * (wP n).eval y = Real.exp (a / 2) * J := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext y
      rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [this]; ring
  have hR : Real.sqrt (2 * n + 1) * iP n (a / 2)
      = Real.sqrt (2 * n + 1) * ((a / 2) ^ n / (2 ^ (n + 1) * n !) * (2 * (4 ^ n * (Real.exp (a / 2) * J)))) := by
    unfold iP
    rw [sub_m11]
    have e : ∀ y : ℝ, Real.cosh (a / 2 * (2 * y - 1)) * (1 - (2 * y - 1) ^ 2) ^ n
        = 4 ^ n * (Real.cosh (a / 2 * (2 * y - 1)) * (wP n).eval y) := by
      intro y; rw [one_sub_sq]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, hcosh]
  rw [hL, hR]
  have hf : (n ! : ℝ) ≠ 0 := by positivity
  have hI : I = a ^ n * J / n ! := by field_simp; linarith [hIJ]
  rw [hI, div_pow, show (4:ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
  field_simp
  ring

lemma pole_sum_gen (a : ℝ) (N : ℕ) (x y : ℕ → ℝ) (s : ℝ) :
    ∫ u in (-(1/2):ℝ)..(1/2), (fx N x u + s * WeilOdd.gx N y u) * Real.exp (-(a * u))
      = ∑ i ∈ range N, x i * (Real.sqrt (2 * ((2 * i : ℕ) : ℝ) + 1) * iP (2 * i) (a / 2))
        + s * ∑ i ∈ range N, y i * (Real.sqrt (2 * ((2 * i + 1 : ℕ) : ℝ) + 1) * iP (2 * i + 1) (a / 2)) := by
  have e : ∫ u in (-(1/2):ℝ)..(1/2), (fx N x u + s * WeilOdd.gx N y u) * Real.exp (-(a * u))
      = ∫ u in (-(1/2):ℝ)..(1/2), ((∑ i ∈ range N, x i *
          ((Real.sqrt (2 * ((2 * i : ℕ) : ℝ) + 1) * (sL (2 * i)).eval (u + 1 / 2)) * Real.exp (-(a * u))))
        + s * ∑ i ∈ range N, y i *
          ((Real.sqrt (2 * ((2 * i + 1 : ℕ) : ℝ) + 1) * (sL (2 * i + 1)).eval (u + 1 / 2)) * Real.exp (-(a * u)))) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hu' : |u| ≤ 1 / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
    simp only [fx, WeilOdd.gx, legT, ite_eq_left hu', aeval_eq, Finset.sum_mul, Finset.mul_sum, add_mul]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_); push_cast; ring
    · refine Finset.sum_congr rfl (fun i _ => ?_); push_cast; ring
  have c0 : ∀ i, Continuous fun u : ℝ => x i *
      ((Real.sqrt (2 * ((2 * i : ℕ) : ℝ) + 1) * (sL (2 * i)).eval (u + 1 / 2)) * Real.exp (-(a * u))) := by
    intro i; have := (sL (2 * i)).continuous; fun_prop
  have c1 : ∀ i, Continuous fun u : ℝ => y i *
      ((Real.sqrt (2 * ((2 * i + 1 : ℕ) : ℝ) + 1) * (sL (2 * i + 1)).eval (u + 1 / 2)) * Real.exp (-(a * u))) := by
    intro i; have := (sL (2 * i + 1)).continuous; fun_prop
  have i0 : IntervalIntegrable (fun u : ℝ => ∑ i ∈ range N, x i *
      ((Real.sqrt (2 * ((2 * i : ℕ) : ℝ) + 1) * (sL (2 * i)).eval (u + 1 / 2)) * Real.exp (-(a * u))))
      volume (-(1/2)) (1/2) := (continuous_finsetSum _ fun i _ => c0 i).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun u : ℝ => s * ∑ i ∈ range N, y i *
      ((Real.sqrt (2 * ((2 * i + 1 : ℕ) : ℝ) + 1) * (sL (2 * i + 1)).eval (u + 1 / 2)) * Real.exp (-(a * u))))
      volume (-(1/2)) (1/2) := (continuous_const.mul (continuous_finsetSum _ fun i _ => c1 i)).intervalIntegrable _ _
  rw [e, intervalIntegral.integral_add i0 i1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun i _ => (c0 i).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun i _ => (c1 i).intervalIntegrable _ _)]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_const_mul, pole_mode_gen]
  · congr 1; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_const_mul, pole_mode_gen]

lemma pole3_eq (n : ℕ) : V3Zhu.pole3 n = Real.sqrt (2 * (n : ℝ) + 1) * iP n (lam / 4) := by
  unfold V3Zhu.pole3
  congr 1
  rw [show (2 * n + 1 : ℝ) = 2 ^ 2 * ((1 / 2) * (n + 1 / 2)) by ring,
    Real.sqrt_mul (show (0:ℝ) ≤ 2 ^ 2 by norm_num) ((1/2) * (n + 1/2)), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-! ## The three functionals of `V'` on rescaled mode sums -/

theorem poleR_sc_hx (N : ℕ) (x y : ℕ → ℝ) : WeilForm.poleR (sc (WeilOdd.hx N x y)) (lam / 2)
    = Real.sqrt lam * (∑ i ∈ range N, x i * V3Zhu.pole3 (2 * i)
        + ∑ i ∈ range N, y i * V3Zhu.pole3 (2 * i + 1)) := by
  rw [poleR_sc]
  congr 1
  have h := pole_sum_gen (lam / 2) N x y 1
  simp only [one_mul] at h
  have e : ∀ u, WeilOdd.hx N x y u * Real.exp (-(lam * u / 2))
      = (fx N x u + WeilOdd.gx N y u) * Real.exp (-(lam / 2 * u)) := fun u => by
    unfold WeilOdd.hx; congr 2; ring
  simp_rw [e, h, pole3_eq, show lam / 2 / 2 = lam / 4 by ring]

theorem poleL_sc_hx (N : ℕ) (x y : ℕ → ℝ) : WeilForm.poleL (sc (WeilOdd.hx N x y)) (lam / 2)
    = Real.sqrt lam * (∑ i ∈ range N, x i * V3Zhu.pole3 (2 * i)
        - ∑ i ∈ range N, y i * V3Zhu.pole3 (2 * i + 1)) := by
  rw [poleL_sc]
  congr 1
  have h := pole_sum_gen (lam / 2) N x y (-1)
  have hc := intervalIntegral.integral_comp_neg (a := -(1/2:ℝ)) (b := 1/2)
    (fun u => WeilOdd.hx N x y u * Real.exp (lam * u / 2))
  simp only [neg_neg] at hc
  rw [← hc]
  have e : ∀ u, WeilOdd.hx N x y (-u) * Real.exp (lam * -u / 2)
      = (fx N x u + -1 * WeilOdd.gx N y u) * Real.exp (-(lam / 2 * u)) := fun u => by
    rw [WeilOdd.hx_neg]; congr 1
    · ring
    · congr 1; ring
  simp_rw [e, h, pole3_eq, show lam / 2 / 2 = lam / 4 by ring]
  ring

lemma iP_zero (n : ℕ) : iP n 0 = if n = 0 then 1 else 0 := by
  unfold iP
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, zero_add, pow_one, Nat.factorial_zero, Nat.cast_one, mul_one, zero_mul, Real.cosh_zero,
      intervalIntegral.integral_const, smul_eq_mul, ite_true]
    norm_num
  · rw [ite_eq_right hn.ne', zero_pow hn.ne']; simp

theorem int_sc_hx (N : ℕ) (hN : 1 ≤ N) (x y : ℕ → ℝ) :
    ∫ u in (-(lam / 2))..(lam / 2), sc (WeilOdd.hx N x y) u = Real.sqrt lam * x 0 := by
  have hl : lam ≠ 0 := lam_pos.ne'
  have key := intervalIntegral.integral_comp_div (a := -(lam / 2)) (b := lam / 2)
    (fun v => WeilOdd.hx N x y v / Real.sqrt lam) hl
  have e1 : -(lam / 2) / lam = -(1 / 2) := by field_simp
  have e2 : lam / 2 / lam = 1 / 2 := by field_simp
  rw [e1, e2, smul_eq_mul] at key
  unfold sc
  rw [key, intervalIntegral.integral_div]
  have hs : lam / Real.sqrt lam = Real.sqrt lam := by
    rw [div_eq_iff sqrt_lam_pos.ne', ← sq, sqrt_lam_sq]
  have h := pole_sum_gen 0 N x y 1
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, one_mul, zero_div] at h
  have e : ∀ u, WeilOdd.hx N x y u = fx N x u + WeilOdd.gx N y u := fun u => rfl
  simp_rw [e, h, iP_zero]
  rw [Finset.sum_eq_single 0 (fun i _ hi => by rw [ite_eq_right (by omega)]; ring) (fun h0 => absurd
    (Finset.mem_range.2 (by omega)) h0)]
  rw [Finset.sum_eq_zero (fun i _ => by rw [ite_eq_right (by omega)]; ring)]
  simp only [mul_zero, Nat.cast_zero, add_zero, zero_add, Real.sqrt_one, ite_true, mul_one]
  calc lam * (x 0 / Real.sqrt lam) = (lam / Real.sqrt lam) * x 0 := by ring
    _ = _ := by rw [hs]

/-! ## The even pole vector: monotonicity and a Taylor enclosure -/

lemma iP_mono (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : iP n a ≤ iP n b := by
  unfold iP
  have wt : ∀ t ∈ Set.Icc (-1:ℝ) 1, (0:ℝ) ≤ (1 - t ^ 2) ^ n := fun t ht => pow_nonneg (by nlinarith [ht.1, ht.2]) n
  have I1 : ∫ t in (-1:ℝ)..1, Real.cosh (a * t) * (1 - t ^ 2) ^ n
      ≤ ∫ t in (-1:ℝ)..1, Real.cosh (b * t) * (1 - t ^ 2) ^ n := by
    apply intervalIntegral.integral_mono_on (by norm_num) (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro t ht
    apply mul_le_mul_of_nonneg_right _ (wt t ht)
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]
    exact mul_le_mul_of_nonneg_right hab (abs_nonneg t)
  have I0 : 0 ≤ ∫ t in (-1:ℝ)..1, Real.cosh (a * t) * (1 - t ^ 2) ^ n :=
    intervalIntegral.integral_nonneg (by norm_num) fun t ht => mul_nonneg (Real.cosh_pos _).le (wt t ht)
  have P : a ^ n / (2 ^ (n + 1) * n !) ≤ b ^ n / (2 ^ (n + 1) * n !) := by gcongr
  exact mul_le_mul P I1 I0 (div_nonneg (pow_nonneg (ha.trans hab) n) (by positivity))

def EqX (x : ℚ) : ℚ := x ^ 12 * (13 / ((Nat.factorial 12 : ℚ) * 12))
def cqX (x : ℚ) (k : ℕ) : ℚ := x ^ (2 * k) / ((2 * k).factorial : ℚ)
def AqX (x : ℚ) (n : ℕ) : ℚ := WeilConst.lsum 6 fun k => cqX x k * (WeilConst.row n).getD k 0
def CqX (x : ℚ) (n : ℕ) : ℚ := x ^ n / (2 ^ (n + 1) * (n.factorial : ℚ))
def XloX (x : ℚ) (n : ℕ) : ℚ := CqX x n * (AqX x n - EqX x * (WeilConst.row n).getD 0 0)
def XhiX (x : ℚ) (n : ℕ) : ℚ := CqX x n * (AqX x n + EqX x * (WeilConst.row n).getD 0 0)

lemma cosh_tayX (x : ℚ) (hx : (x:ℝ) ≤ 1) (y : ℝ) (hy : |y| ≤ x) : |Real.cosh y - WeilConst.Tc y| ≤ (EqX x : ℝ) := by
  have h1 := Real.exp_bound (x := y) (by linarith) (n := 12) (by norm_num)
  have h2 := Real.exp_bound (x := -y) (by rw [abs_neg]; linarith) (n := 12) (by norm_num)
  have ee : WeilConst.Tc y = ((∑ m ∈ range 12, y ^ m / (m.factorial : ℝ)) +
      ∑ m ∈ range 12, (-y) ^ m / (m.factorial : ℝ)) / 2 := by
    unfold WeilConst.Tc; simp only [sum_range_succ, sum_range_zero]; ring
  rw [Real.cosh_eq, ee]
  rw [abs_neg] at h2
  have hp : |y| ^ 12 ≤ (x : ℝ) ^ 12 := pow_le_pow_left₀ (abs_nonneg y) hy 12
  have hE : |y| ^ 12 * ((Nat.succ 12 : ℝ) / ((Nat.factorial 12 : ℝ) * 12)) ≤ (EqX x : ℝ) := by
    unfold EqX; push_cast; exact mul_le_mul_of_nonneg_right hp (by norm_num)
  have a1 := abs_le.1 h1; have a2 := abs_le.1 h2
  rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

lemma int_TX (x : ℝ) (n : ℕ) : ∫ t in (-1:ℝ)..1, WeilConst.Tc (x * t) * (1 - t ^ 2) ^ n
    = ∑ k ∈ range 6, x ^ (2 * k) / ((2 * k).factorial : ℝ) * WeilConst.J k n := by
  unfold WeilConst.Tc
  simp only [sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by apply Continuous.intervalIntegrable; fun_prop)]
  apply sum_congr rfl; intro k _
  unfold WeilConst.J
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro t _
  simp only; rw [mul_pow]; ring

lemma iP_encX (x : ℚ) (hx0 : (0:ℝ) ≤ x) (hx1 : (x:ℝ) ≤ 1) (n : ℕ) (hn : 5 + n < WeilConst.W) :
    (XloX x n : ℝ) ≤ iP n x ∧ iP n x ≤ (XhiX x n : ℝ) := by
  have hA : ((AqX x n : ℚ) : ℝ) = ∑ k ∈ range 6, (x : ℝ) ^ (2 * k) / ((2 * k).factorial : ℝ) * WeilConst.J k n := by
    unfold AqX; rw [WeilConst.lsum_cast]; apply sum_congr rfl; intro k hk
    have := mem_range.1 hk; unfold cqX; push_cast; rw [WeilConst.row_getD n k (by omega)]
  have h0 : (((WeilConst.row n).getD 0 0 : ℚ) : ℝ) = WeilConst.J 0 n := WeilConst.row_getD n 0 (by omega)
  have hJ0 : WeilConst.J 0 n = ∫ t in (-1:ℝ)..1, (1 - t ^ 2) ^ n := by unfold WeilConst.J; simp
  have hC : ((CqX x n : ℚ) : ℝ) = (x : ℝ) ^ n / (2 ^ (n + 1) * n.factorial) := by unfold CqX; push_cast; ring
  have hCp : (0:ℝ) ≤ (x : ℝ) ^ n / (2 ^ (n + 1) * n.factorial) := by positivity
  have ci : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume (-1) 1 :=
    fun g hg => hg.intervalIntegrable _ _
  have cT : Continuous fun t : ℝ => WeilConst.Tc ((x : ℝ) * t) * (1 - t ^ 2) ^ n := by
    unfold WeilConst.Tc; fun_prop
  have cc : Continuous fun t : ℝ => Real.cosh ((x : ℝ) * t) * (1 - t ^ 2) ^ n := by fun_prop
  have pt : ∀ t ∈ Set.Icc (-1:ℝ) 1, |Real.cosh ((x : ℝ) * t) - WeilConst.Tc ((x : ℝ) * t)| ≤ (EqX x : ℝ) := by
    intro t ht; apply cosh_tayX x hx1; rw [abs_mul, abs_of_nonneg hx0]
    have : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
    nlinarith
  have wn : ∀ t ∈ Set.Icc (-1:ℝ) 1, 0 ≤ (1 - t ^ 2) ^ n := by
    intro t ht; apply pow_nonneg; nlinarith [ht.1, ht.2]
  have lo : ∫ t in (-1:ℝ)..1, (WeilConst.Tc ((x : ℝ) * t) * (1 - t ^ 2) ^ n - (EqX x : ℝ) * (1 - t ^ 2) ^ n)
      ≤ ∫ t in (-1:ℝ)..1, Real.cosh ((x : ℝ) * t) * (1 - t ^ 2) ^ n := by
    apply intervalIntegral.integral_mono_on (by norm_num) (ci _ (by fun_prop)) (ci _ cc)
    intro t ht; nlinarith [mul_le_mul_of_nonneg_right (abs_le.1 (pt t ht)).1 (wn t ht)]
  have hi : ∫ t in (-1:ℝ)..1, Real.cosh ((x : ℝ) * t) * (1 - t ^ 2) ^ n
      ≤ ∫ t in (-1:ℝ)..1, (WeilConst.Tc ((x : ℝ) * t) * (1 - t ^ 2) ^ n + (EqX x : ℝ) * (1 - t ^ 2) ^ n) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (ci _ cc) (ci _ (by fun_prop))
    intro t ht; nlinarith [mul_le_mul_of_nonneg_right (abs_le.1 (pt t ht)).2 (wn t ht)]
  rw [intervalIntegral.integral_sub (ci _ cT) (ci _ (by fun_prop)), intervalIntegral.integral_const_mul,
    int_TX, ← hJ0] at lo
  rw [intervalIntegral.integral_add (ci _ cT) (ci _ (by fun_prop)), intervalIntegral.integral_const_mul,
    int_TX, ← hJ0] at hi
  unfold iP XloX XhiX
  push_cast
  rw [hC, hA, h0]
  constructor
  · exact mul_le_mul_of_nonneg_left lo hCp
  · exact mul_le_mul_of_nonneg_left hi hCp

/-- Bool test that `√(4i+1)·[iₙ(l3lo/4), iₙ(l3hi/4)]` lies within `ε` of the centre `pq[i]`, `n = 2i`, `i < 28`. -/
def pchk3 (pq : List ℚ) (ε : ℚ) : Bool :=
  (List.range 28).all fun i => WeilConst.pt1 (2 * (2 * i : ℕ) + 1) (XloX (V3Log.l3lo / 4) (2 * i))
    (XhiX (V3Log.l3hi / 4) (2 * i)) (pq.getD i 0) ε

theorem pole3_chk : pchk3 V3Cert.pqE (1 / 10 ^ 12) = true := by decide +kernel

theorem pole3_enc : ∀ i < 28, |V3Zhu.pole3 (2 * i) - ((V3Cert.pqE.getD i 0 : ℚ) : ℝ)| ≤ 1 / 10 ^ 12 := by
  intro i hi
  have h1 := List.all_eq_true.1 pole3_chk i (List.mem_range.2 hi)
  obtain ⟨hl1, hl2⟩ := lam_bounds
  have hlo0 : (0:ℝ) ≤ ((V3Log.l3lo / 4 : ℚ) : ℝ) := by unfold V3Log.l3lo; norm_num
  have hlo1 : ((V3Log.l3lo / 4 : ℚ) : ℝ) ≤ 1 := by unfold V3Log.l3lo; norm_num
  have hhi0 : (0:ℝ) ≤ ((V3Log.l3hi / 4 : ℚ) : ℝ) := by unfold V3Log.l3hi; norm_num
  have hhi1 : ((V3Log.l3hi / 4 : ℚ) : ℝ) ≤ 1 := by unfold V3Log.l3hi; norm_num
  have hW : 5 + 2 * i < WeilConst.W := by unfold WeilConst.W; omega
  obtain ⟨l, -⟩ := iP_encX _ hlo0 hlo1 (2 * i) hW
  obtain ⟨-, u⟩ := iP_encX _ hhi0 hhi1 (2 * i) hW
  have m1 : iP (2 * i) ((V3Log.l3lo / 4 : ℚ) : ℝ) ≤ iP (2 * i) (lam / 4) :=
    iP_mono _ hlo0 (by push_cast; linarith)
  have m2 : iP (2 * i) (lam / 4) ≤ iP (2 * i) ((V3Log.l3hi / 4 : ℚ) : ℝ) :=
    iP_mono _ (by have := lam_pos; positivity) (by push_cast; linarith)
  have := WeilConst.pt1_spec _ _ _ _ _ (by positivity) h1 (iP (2 * i) (lam / 4)) (l.trans m1) (m2.trans u)
  rw [pole3_eq]
  push_cast at this ⊢
  exact this

end V3Pole
