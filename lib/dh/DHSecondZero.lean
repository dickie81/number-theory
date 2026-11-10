import DHSecond
import DHBall
import DHSecondCert0

/-!
# A zero of the second Davenport–Heilbronn function in the half-plane of absolute convergence

`dh2` has a zero within `1/10000` of `c = 23747444/10000000 + (16498708285/10000000) i`, so with real part above `2`
(`dh2_zero_re_gt_two`): a function with the functional equation of a Dirichlet `L`-function, and a zero where its
Dirichlet series converges absolutely. The zero is the one of largest real part below height `10000` in E. Bombieri
and A. Ghosh's computations (Russian Math. Surveys 66:2 (2011), §9), `2.37474435 + 1649.8708285i`; here it is proved.

The certificate is the minimum-modulus instrument of `DHLocateSkeleton` (`exists_zero_of_bounds`). At this real part
no Euler–Maclaurin tail is needed: the approximant is the Dirichlet polynomial over `n ≤ 5000`
(`Locate.secD 0 1000`), and the rest of the series is below `‖a(1)‖κ·5000^{−1.37}` (`Locate.norm_dh2_sub_le`). The
polynomial's value and derivative at `c`, and the termwise bound for its second derivative, are computed by the
kernel: `DHBall.run` at the centre `DHBall.Sec.ctr`, in `DHSecondCert0`.

* `inv1000`: the kernel's final state encloses the six sums.
* `norm_secD_zero_cS`, `norm_secD_one_cS`, `secD2sum_le_num`: the three numbers.
* `dh2_zero_near`: the zero; `dh2_zero_located`: its box; `dh2_zero_re_gt_two`, `dh2_zero_re_gt_one`: `Re ρ > 2 > 1`.
-/

open Complex Metric

noncomputable section

namespace PsiOmega.Locate.Sec

open DHBall (SA SB SA1 SB1 D2A D2B T)
open DHBall.Sec (ctr st1)

/-- The centre `c = 23747444/10000000 + (16498708285/10000000) i`. -/
def cS : ℂ := DHBall.c ctr

theorem cS_re : cS.re = 23747444 / 10000000 := by
  show ((ctr.reN : ℕ) : ℝ) / (ctr.reD : ℕ) = _
  norm_num [ctr]

theorem cS_im : cS.im = 16498708285 / 10000000 := by
  show ((ctr.imN : ℕ) : ℝ) / (ctr.imD : ℕ) = _
  norm_num [ctr]

/-! ## 1. The kernel's sums -/

/-- The kernel's final state encloses the sums over `n ≤ 5000`. -/
theorem inv1000 : DHBall.Inv ctr 1000 st1 := by
  have hr : 0 < ctr.reD := by decide
  have hi : 0 < ctr.imD := by decide
  have h := DHBall.inv_run hr hi 1000 0 DHBall.init (DHBall.inv_init ctr)
  rw [DHBall.Sec.run_0] at h
  exact h

/-- The Dirichlet polynomial at `c`, in terms of the sums. -/
theorem secD_zero_eq (M : ℕ) : secD 0 M cS = (kappa : ℂ) * SA ctr M - SB ctr M := by
  unfold secD SA SB
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [npsD, pow_zero, one_mul, T, cS]
  ring

/-- Its derivative at `c`, in terms of the sums. -/
theorem secD_one_eq (M : ℕ) : secD 1 M cS = (kappa : ℂ) * SA1 ctr M - SB1 ctr M := by
  unfold secD SA1 SB1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [npsD_one, nps, T, cS]
  ring

theorem pow_10000_ge : (5000 : ℝ) ≤ (1001 / 1000 : ℝ) ^ 10000 := by
  have h1 : (101 / 100 : ℝ) ≤ (1001 / 1000 : ℝ) ^ 10 := by norm_num
  have h2 : (11 / 10 : ℝ) ≤ (101 / 100 : ℝ) ^ 10 := by norm_num
  have h3 : (5 / 2 : ℝ) ≤ (11 / 10 : ℝ) ^ 10 := by norm_num
  have h4 : (5000 : ℝ) ≤ (5 / 2 : ℝ) ^ 10 := by norm_num
  calc (5000 : ℝ) ≤ (5 / 2 : ℝ) ^ 10 := h4
    _ ≤ ((11 / 10 : ℝ) ^ 10) ^ 10 := pow_le_pow_left₀ (by norm_num) h3 10
    _ ≤ (((101 / 100 : ℝ) ^ 10) ^ 10) ^ 10 :=
        pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h2 10) 10
    _ ≤ ((((1001 / 1000 : ℝ) ^ 10) ^ 10) ^ 10) ^ 10 :=
        pow_le_pow_left₀ (by positivity)
          (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h1 10) 10) 10
    _ = (1001 / 1000 : ℝ) ^ 10000 := by rw [← pow_mul, ← pow_mul, ← pow_mul]

/-- `n^{-σ}` at `σ = Re c − 1/10000`, against `|n^{-c}|`, for `n ≤ 5000`. -/
theorem ex_le_norm_T {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 5000) :
    ex (23746444 / 10000000) n ≤ 1001 / 1000 * ‖T ctr n‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hT : ‖T ctr n‖ = (n : ℝ) ^ (-(23747444 / 10000000 : ℝ)) := by
    rw [T, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re,
      show (DHBall.c ctr).re = 23747444 / 10000000 from cS_re]
  have e : (-(23746444 / 10000000 : ℝ)) = -(23747444 / 10000000 : ℝ) + ((10000 : ℕ) : ℝ)⁻¹ := by
    norm_num
  rw [ex_eq_rpow _ hn, hT, e, Real.rpow_add hn0, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
  calc (n : ℝ) ^ (((10000 : ℕ) : ℝ)⁻¹) ≤ (5000 : ℝ) ^ (((10000 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow hn0.le (by exact_mod_cast hn') (by norm_num)
    _ ≤ ((1001 / 1000 : ℝ) ^ 10000) ^ (((10000 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by norm_num) pow_10000_ge (by norm_num)
    _ = 1001 / 1000 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

/-- The termwise bound for the second derivative, in terms of the sums. -/
theorem secD2sum_le :
    secD2sum (23746444 / 10000000) 1000 ≤ 1001 / 1000 * (kappa * D2A ctr 1000 + D2B ctr 1000) := by
  have hk := kappa_pos
  have key : ∀ m ∈ Finset.range 1000,
      kappa * (Real.log ((5 * m + 1 : ℕ) : ℝ) ^ 2 * ex (23746444 / 10000000) (5 * m + 1))
        + Real.log ((5 * m + 2 : ℕ) : ℝ) ^ 2 * ex (23746444 / 10000000) (5 * m + 2)
        + Real.log ((5 * m + 3 : ℕ) : ℝ) ^ 2 * ex (23746444 / 10000000) (5 * m + 3)
        + kappa * (Real.log ((5 * m + 4 : ℕ) : ℝ) ^ 2 * ex (23746444 / 10000000) (5 * m + 4)) ≤
      1001 / 1000 * (kappa * (Real.log ((5 * m + 1 : ℕ) : ℝ) ^ 2 * ‖T ctr (5 * m + 1)‖ +
          Real.log ((5 * m + 4 : ℕ) : ℝ) ^ 2 * ‖T ctr (5 * m + 4)‖) +
        (Real.log ((5 * m + 2 : ℕ) : ℝ) ^ 2 * ‖T ctr (5 * m + 2)‖ +
          Real.log ((5 * m + 3 : ℕ) : ℝ) ^ 2 * ‖T ctr (5 * m + 3)‖)) := by
    intro m hm
    have hm' : m < 1000 := Finset.mem_range.1 hm
    have h1 := mul_le_mul_of_nonneg_left (ex_le_norm_T (n := 5 * m + 1) (by omega) (by omega))
      (sq_nonneg (Real.log ((5 * m + 1 : ℕ) : ℝ)))
    have h2 := mul_le_mul_of_nonneg_left (ex_le_norm_T (n := 5 * m + 2) (by omega) (by omega))
      (sq_nonneg (Real.log ((5 * m + 2 : ℕ) : ℝ)))
    have h3 := mul_le_mul_of_nonneg_left (ex_le_norm_T (n := 5 * m + 3) (by omega) (by omega))
      (sq_nonneg (Real.log ((5 * m + 3 : ℕ) : ℝ)))
    have h4 := mul_le_mul_of_nonneg_left (ex_le_norm_T (n := 5 * m + 4) (by omega) (by omega))
      (sq_nonneg (Real.log ((5 * m + 4 : ℕ) : ℝ)))
    have h1' := mul_le_mul_of_nonneg_left h1 hk.le
    have h4' := mul_le_mul_of_nonneg_left h4 hk.le
    linarith
  calc secD2sum (23746444 / 10000000) 1000 ≤ ∑ m ∈ Finset.range 1000,
        1001 / 1000 * (kappa * (Real.log ((5 * m + 1 : ℕ) : ℝ) ^ 2 * ‖T ctr (5 * m + 1)‖ +
            Real.log ((5 * m + 4 : ℕ) : ℝ) ^ 2 * ‖T ctr (5 * m + 4)‖) +
          (Real.log ((5 * m + 2 : ℕ) : ℝ) ^ 2 * ‖T ctr (5 * m + 2)‖ +
            Real.log ((5 * m + 3 : ℕ) : ℝ) ^ 2 * ‖T ctr (5 * m + 3)‖)) :=
        Finset.sum_le_sum key
    _ = 1001 / 1000 * (kappa * D2A ctr 1000 + D2B ctr 1000) := by
        unfold D2A D2B
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## 2. The three numbers -/

/-- `‖secD 0 1000 c‖ ≤ 10⁻⁷`: the Dirichlet polynomial at the centre, by the kernel's sums. -/
theorem norm_secD_zero_cS : ‖secD 0 1000 cS‖ ≤ 1 / 10000000 := by
  have hA := inv1000.A
  have hB := inv1000.B
  obtain ⟨a1, a2⟩ := DHBall.bounds_of_has hA.1
  obtain ⟨a3, a4⟩ := DHBall.bounds_of_has hA.2
  obtain ⟨b1, b2⟩ := DHBall.bounds_of_has hB.1
  obtain ⟨b3, b4⟩ := DHBall.bounds_of_has hB.2
  simp only [DHBall.Sec.st1, DHBall.S] at a1 a2 a3 a4 b1 b2 b3 b4
  norm_num at a1 a2 a3 a4 b1 b2 b3 b4
  obtain ⟨k1, k2⟩ := kappaBG
  have hk0 := kappa_pos.le
  have hre : (secD 0 1000 cS).re = kappa * (SA ctr 1000).re - (SB ctr 1000).re := by
    rw [secD_zero_eq, Complex.sub_re, Complex.re_ofReal_mul]
  have him : (secD 0 1000 cS).im = kappa * (SA ctr 1000).im - (SB ctr 1000).im := by
    rw [secD_zero_eq, Complex.sub_im, Complex.im_ofReal_mul]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [hre, him]
  have u1 := mul_le_mul_of_nonneg_left a1 hk0
  have u2 := mul_le_mul_of_nonneg_left a2 hk0
  have u3 := mul_le_mul_of_nonneg_left a3 hk0
  have u4 := mul_le_mul_of_nonneg_left a4 hk0
  have hr : |kappa * (SA ctr 1000).re - (SB ctr 1000).re| ≤ 2 / 100000000 := by
    rw [abs_le]; constructor <;> linarith
  have hi : |kappa * (SA ctr 1000).im - (SB ctr 1000).im| ≤ 1 / 100000000 := by
    rw [abs_le]; constructor <;> linarith
  linarith

/-- `24/100 ≤ ‖secD 1 1000 c‖`: the real part of the derivative is above `0.2426` there. -/
theorem norm_secD_one_cS : (24 / 100 : ℝ) ≤ ‖secD 1 1000 cS‖ := by
  have hA := inv1000.A1
  have hB := inv1000.B1
  obtain ⟨a1, -⟩ := DHBall.bounds_of_has hA.1
  obtain ⟨-, b2⟩ := DHBall.bounds_of_has hB.1
  simp only [DHBall.Sec.st1, DHBall.S] at a1 b2
  norm_num at a1 b2
  obtain ⟨k1, k2⟩ := kappaBG
  have hk0 := kappa_pos.le
  have hre : (secD 1 1000 cS).re = kappa * (SA1 ctr 1000).re - (SB1 ctr 1000).re := by
    rw [secD_one_eq, Complex.sub_re, Complex.re_ofReal_mul]
  have u1 := mul_le_mul_of_nonneg_left a1 hk0
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  rw [hre]
  refine le_trans ?_ (le_abs_self _)
  linarith

/-- The termwise sum for the second derivative is at most `1` (it is below `0.51`). -/
theorem secD2sum_le_num : secD2sum (23746444 / 10000000) 1000 ≤ 1 := by
  have hA := inv1000.d2a
  have hB := inv1000.d2b
  simp only [DHBall.Sec.st1, DHBall.S] at hA hB
  norm_num at hA hB
  obtain ⟨k1, k2⟩ := kappaBG
  have hk0 := kappa_pos.le
  have hA0 : 0 ≤ D2A ctr 1000 := by
    unfold D2A
    exact Finset.sum_nonneg fun m _ => by positivity
  have h := secD2sum_le
  nlinarith

/-- The tail of the series on `Re s ≥ 237/100`: `5000^{−37/100}/5000 ≤ 43/5000000`. -/
theorem tail_le :
    ((5 * 1000 : ℕ) : ℝ) ^ (-((237 / 100 : ℝ) - 2)) * ((5 * 1000 : ℕ) : ℝ)⁻¹ ≤ 43 / 5000000 := by
  have h : ((5 * 1000 : ℕ) : ℝ) ^ (-((237 / 100 : ℝ) - 2)) ≤ 43 / 1000 := by
    have e : (-((237 / 100 : ℝ) - 2)) = -(((37 : ℕ) : ℝ) / ((100 : ℕ) : ℝ)) := by norm_num
    rw [e]
    exact rpow_neg_div_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  calc ((5 * 1000 : ℕ) : ℝ) ^ (-((237 / 100 : ℝ) - 2)) * ((5 * 1000 : ℕ) : ℝ)⁻¹
      ≤ 43 / 1000 * ((5 * 1000 : ℕ) : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h (by positivity)
    _ = 43 / 5000000 := by norm_num

/-! ## 3. The zero -/

/-- **A zero of the second Davenport–Heilbronn function within `1/10000` of
`c = 23747444/10000000 + (16498708285/10000000) i`.** The margin `2(p₀ + e₀) < a₀r − m₂r²` is
`1.74·10⁻⁵ < 2.399·10⁻⁵`, in units of `‖a(1)‖κ`. -/
theorem dh2_zero_near : ∃ ρ, dh2 ρ = 0 ∧ ‖ρ - cS‖ < 1 / 10000 := by
  have hA0 : 0 < ‖aDH chi5 1‖ * kappa := mul_pos norm_aDH_one_pos kappa_pos
  have hnorm : ∀ z : ℂ, ‖aDH chi5 1 * (kappa : ℂ) * z‖ = ‖aDH chi5 1‖ * kappa * ‖z‖ := by
    intro z
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos kappa_pos]
  have hPd : ∀ s : ℂ, HasDerivAt (fun s => aDH chi5 1 * (kappa : ℂ) * secD 0 1000 s)
      (aDH chi5 1 * (kappa : ℂ) * secD 1 1000 s) s :=
    fun s => (hasDerivAt_secD 0 1000 s).const_mul _
  have hderiv : deriv (fun s => aDH chi5 1 * (kappa : ℂ) * secD 0 1000 s) =
      fun s => aDH chi5 1 * (kappa : ℂ) * secD 1 1000 s := funext fun s => (hPd s).deriv
  have hPd2 : ∀ s : ℂ, HasDerivAt (fun s => aDH chi5 1 * (kappa : ℂ) * secD 1 1000 s)
      (aDH chi5 1 * (kappa : ℂ) * secD 2 1000 s) s :=
    fun s => (hasDerivAt_secD 1 1000 s).const_mul _
  have key : ∃ z ∈ ball cS (1 / 10000), dh2 z = 0 := by
    refine exists_zero_of_bounds (f := dh2)
      (P := fun s => aDH chi5 1 * (kappa : ℂ) * secD 0 1000 s) (c := cS) (r := 1 / 10000)
      (p₀ := ‖aDH chi5 1‖ * kappa * (1 / 10000000)) (a₀ := ‖aDH chi5 1‖ * kappa * (24 / 100))
      (m₂ := ‖aDH chi5 1‖ * kappa * 1) (e₀ := ‖aDH chi5 1‖ * kappa * (43 / 5000000))
      (by norm_num) differentiable_dh2.differentiableOn
      (fun w _ => (hPd w).differentiableAt)
      (fun w _ => by rw [hderiv]; exact (hPd2 w).differentiableAt)
      ?_ ?_ ?_ ?_ ?_
    · show ‖aDH chi5 1 * (kappa : ℂ) * secD 0 1000 cS‖ ≤ _
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left norm_secD_zero_cS hA0.le
    · rw [(hPd cS).deriv, hnorm]
      exact mul_le_mul_of_nonneg_left norm_secD_one_cS hA0.le
    · intro w hw
      rw [hderiv, (hPd2 w).deriv, hnorm]
      apply mul_le_mul_of_nonneg_left _ hA0.le
      have hre : (23746444 / 10000000 : ℝ) ≤ w.re := by
        have := (box_of_memG hw).1
        rw [cS_re] at this
        linarith
      exact (norm_secD_two_le 1000 hre).trans secD2sum_le_num
    · intro w hw
      have hre : (237 / 100 : ℝ) ≤ w.re := by
        have := (box_of_memG hw).1
        rw [cS_re] at this
        linarith
      have h := norm_dh2_sub_le (M := 1000) (by norm_num) (σ₀ := 237 / 100) (by norm_num) hre
      exact h.trans (mul_le_mul_of_nonneg_left tail_le hA0.le)
    · linarith
  obtain ⟨z, hz, h0⟩ := key
  exact ⟨z, h0, mem_ball_iff_norm.1 hz⟩

/-- The zero in a box. -/
theorem dh2_zero_located :
    ∃ ρ : ℂ, dh2 ρ = 0 ∧ 23746444 / 10000000 < ρ.re ∧ ρ.re < 23748444 / 10000000 ∧
      16498707285 / 10000000 < ρ.im ∧ ρ.im < 16498709285 / 10000000 := by
  obtain ⟨ρ, h0, hρ⟩ := dh2_zero_near
  have hre := (Complex.abs_re_le_norm (ρ - cS)).trans_lt hρ
  have him := (Complex.abs_im_le_norm (ρ - cS)).trans_lt hρ
  rw [Complex.sub_re, cS_re, abs_lt] at hre
  rw [Complex.sub_im, cS_im, abs_lt] at him
  exact ⟨ρ, h0, by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

/-- **The second Davenport–Heilbronn function has a zero with real part above `2`.** -/
theorem dh2_zero_re_gt_two : ∃ ρ : ℂ, dh2 ρ = 0 ∧ 2 < ρ.re := by
  obtain ⟨ρ, h0, h1, -⟩ := dh2_zero_located
  exact ⟨ρ, h0, by linarith⟩

/-- **It has a zero in the half-plane of absolute convergence of its Dirichlet series**, `Re s > 1`, and that zero
is a zero of its completion. -/
theorem dh2_zero_re_gt_one : ∃ ρ : ℂ, dh2 ρ = 0 ∧ dh2Lam chi5 ρ = 0 ∧ 1 < ρ.re := by
  obtain ⟨ρ, h0, h2⟩ := dh2_zero_re_gt_two
  exact ⟨ρ, h0, (dh2_eq_zero_iff (by linarith)).1 h0, by linarith⟩

end PsiOmega.Locate.Sec

#print axioms PsiOmega.Locate.Sec.dh2_zero_near
#print axioms PsiOmega.Locate.Sec.dh2_zero_located
#print axioms PsiOmega.Locate.Sec.dh2_zero_re_gt_two
#print axioms PsiOmega.Locate.Sec.dh2_zero_re_gt_one
