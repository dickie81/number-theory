import DHLocateGen
import DHBall
import DHLocate5Cert0
import DHLocate5Cert1
import DHLocate5Cert2
import DHLocate5Cert3
import DHLocate5Cert4
import DHLocate5Cert5

/-!
# A zero of the Davenport–Heilbronn function with real part above `11/12`

`dh` has a zero within `18/10000` of `c = 918601/1000000 + (2441547865/100000) i`, so with real part above `11/12`
(`dh_zero_re_gt`): the zero-free half-plane `Re s > 11/12` of the Dirichlet `L`-functions fails for a function with
their functional equation and no Euler product.

The certificate is that of `DHLocateGen` (`dh_zero_near_of_fEMG`), with the Euler–Maclaurin approximant
`dhEM 6000 12`: a Dirichlet polynomial over `n < 30000` and a tail. At this height the polynomial has `24000` terms,
so its value and its derivative at `c` are not bounded term by term in the source, as for the four zeros below height
`177`, but computed by the kernel: `DHBall.run` is integer arithmetic on balls, `DHBall.inv_run` proves that it
encloses the sums, and `DHLocate5Cert0`, …, `DHLocate5Cert5` have the kernel run it.

* `inv6000`: the kernel's final state encloses the six sums.
* `DEM_eq`, `DEMk_one_eq`, `D2sum_le`: the approximant's Dirichlet polynomial, its derivative and the termwise bound
  for its second derivative, in terms of the sums.
* `Gsup_tight_le`, `Gsup_wide_le`: the tail `GEM` at `c` and on the box of `closedBall c (3018/10000)`.
* `dh_zero_near`: the zero; `dh_zero_located_five`: its box; `dh_zero_re_gt`: `Re ρ > 11/12`.
-/

open Complex Metric
open scoped Nat

noncomputable section

namespace PsiOmega.Locate.Z5

open DHBall (SA SB SA1 SB1 D2A D2B T)

/-- The centre `c = 918601/1000000 + (2441547865/100000) i`. -/
def cZ : ℂ := DHBall.c

theorem cZ_re : cZ.re = 918601 / 1000000 := by
  show ((DHBall.reN : ℕ) : ℝ) / (DHBall.reD : ℕ) = _
  norm_num [DHBall.reN, DHBall.reD]

theorem cZ_im : cZ.im = 2441547865 / 100000 := by
  show ((DHBall.imN : ℕ) : ℝ) / (DHBall.imD : ℕ) = _
  norm_num [DHBall.imN, DHBall.imD]

/-! ## 1. The kernel's sums -/

/-- The kernel's final state encloses the sums over `n < 30000`. -/
theorem inv6000 : DHBall.Inv 6000 DHBall.st6 := by
  have h1 : DHBall.Inv 1000 DHBall.st1 := by
    have h := DHBall.inv_run 1000 0 DHBall.init DHBall.inv_init
    rw [DHBall.run_0] at h
    exact h
  have h2 : DHBall.Inv 2000 DHBall.st2 := by
    have h := DHBall.inv_run 1000 1000 DHBall.st1 h1
    rw [DHBall.run_1] at h
    exact h
  have h3 : DHBall.Inv 3000 DHBall.st3 := by
    have h := DHBall.inv_run 1000 2000 DHBall.st2 h2
    rw [DHBall.run_2] at h
    exact h
  have h4 : DHBall.Inv 4000 DHBall.st4 := by
    have h := DHBall.inv_run 1000 3000 DHBall.st3 h3
    rw [DHBall.run_3] at h
    exact h
  have h5 : DHBall.Inv 5000 DHBall.st5 := by
    have h := DHBall.inv_run 1000 4000 DHBall.st4 h4
    rw [DHBall.run_4] at h
    exact h
  have h := DHBall.inv_run 1000 5000 DHBall.st5 h5
  rw [DHBall.run_5] at h
  exact h

/-- `DEM M c` in terms of the sums. -/
theorem DEM_eq (M : ℕ) : DEM M cZ = SA M + (kappa : ℂ) * SB M := by
  unfold DEM SA SB
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [nps, T, cZ]
  ring

/-- `DEM′ M c` in terms of the sums. -/
theorem DEMk_one_eq (M : ℕ) : DEMk 1 M cZ = SA1 M + (kappa : ℂ) * SB1 M := by
  unfold DEMk SA1 SB1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [npsD_one, nps, T, cZ]
  ring

theorem pow_500_ge : (30000 : ℝ) ≤ (1021 / 1000 : ℝ) ^ 500 := by
  have h1 : (1230 / 1000 : ℝ) ≤ (1021 / 1000 : ℝ) ^ 10 := by norm_num
  have h2 : (2815 / 1000 : ℝ) ≤ (1230 / 1000 : ℝ) ^ 5 := by norm_num
  have h3 : (30000 : ℝ) ≤ (2815 / 1000 : ℝ) ^ 10 := by norm_num
  calc (30000 : ℝ) ≤ (2815 / 1000 : ℝ) ^ 10 := h3
    _ ≤ ((1230 / 1000 : ℝ) ^ 5) ^ 10 := pow_le_pow_left₀ (by norm_num) h2 10
    _ ≤ (((1021 / 1000 : ℝ) ^ 10) ^ 5) ^ 10 :=
        pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h1 5) 10
    _ = (1021 / 1000 : ℝ) ^ 500 := by rw [← pow_mul, ← pow_mul]

/-- `n^{-σ}` at `σ = 9168/10000`, against `|n^{-c}| = n^{-918601/1000000}`, for `n ≤ 30000`. -/
theorem ex_le_norm_T {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 30000) :
    ex (9168 / 10000) n ≤ 1021 / 1000 * ‖T n‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT : ‖T n‖ = (n : ℝ) ^ (-(918601 / 1000000 : ℝ)) := by
    rw [T, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    congr 2
  have e : (-(9168 / 10000 : ℝ)) = -(918601 / 1000000 : ℝ) + 1801 / 1000000 := by norm_num
  rw [ex_eq_rpow _ hn, hT, e, Real.rpow_add hn0, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
  calc (n : ℝ) ^ (1801 / 1000000 : ℝ) ≤ (n : ℝ) ^ (((500 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    _ ≤ (30000 : ℝ) ^ (((500 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow hn0.le (by exact_mod_cast hn') (by norm_num)
    _ ≤ ((1021 / 1000 : ℝ) ^ 500) ^ (((500 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by norm_num) pow_500_ge (by norm_num)
    _ = 1021 / 1000 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

/-- The termwise bound for `DEM″`, in terms of the sums. -/
theorem D2sum_le : D2sum (9168 / 10000) 6000 ≤ 1021 / 1000 * (D2A 6000 + kappa * D2B 6000) := by
  have hk := kappa_pos
  have key : ∀ m ∈ Finset.range 6000,
      Real.log ((5 * m + 1 : ℕ) : ℝ) ^ 2 * ex (9168 / 10000) (5 * m + 1)
        + kappa * (Real.log ((5 * m + 2 : ℕ) : ℝ) ^ 2 * ex (9168 / 10000) (5 * m + 2))
        + kappa * (Real.log ((5 * m + 3 : ℕ) : ℝ) ^ 2 * ex (9168 / 10000) (5 * m + 3))
        + Real.log ((5 * m + 4 : ℕ) : ℝ) ^ 2 * ex (9168 / 10000) (5 * m + 4) ≤
      1021 / 1000 * ((Real.log ((5 * m + 1 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 1)‖ +
          Real.log ((5 * m + 4 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 4)‖) +
        kappa * (Real.log ((5 * m + 2 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 2)‖ +
          Real.log ((5 * m + 3 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 3)‖)) := by
    intro m hm
    have hm' : m < 6000 := Finset.mem_range.1 hm
    have h1 := mul_le_mul_of_nonneg_left (ex_le_norm_T (n := 5 * m + 1) (by omega) (by omega))
      (sq_nonneg (Real.log ((5 * m + 1 : ℕ) : ℝ)))
    have h2 := mul_le_mul_of_nonneg_left (ex_le_norm_T (n := 5 * m + 2) (by omega) (by omega))
      (sq_nonneg (Real.log ((5 * m + 2 : ℕ) : ℝ)))
    have h3 := mul_le_mul_of_nonneg_left (ex_le_norm_T (n := 5 * m + 3) (by omega) (by omega))
      (sq_nonneg (Real.log ((5 * m + 3 : ℕ) : ℝ)))
    have h4 := mul_le_mul_of_nonneg_left (ex_le_norm_T (n := 5 * m + 4) (by omega) (by omega))
      (sq_nonneg (Real.log ((5 * m + 4 : ℕ) : ℝ)))
    have h2' := mul_le_mul_of_nonneg_left h2 hk.le
    have h3' := mul_le_mul_of_nonneg_left h3 hk.le
    linarith
  calc D2sum (9168 / 10000) 6000 ≤ ∑ m ∈ Finset.range 6000,
        1021 / 1000 * ((Real.log ((5 * m + 1 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 1)‖ +
            Real.log ((5 * m + 4 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 4)‖) +
          kappa * (Real.log ((5 * m + 2 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 2)‖ +
            Real.log ((5 * m + 3 : ℕ) : ℝ) ^ 2 * ‖T (5 * m + 3)‖)) :=
        Finset.sum_le_sum key
    _ = 1021 / 1000 * (D2A 6000 + kappa * D2B 6000) := by
        unfold D2A D2B
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## 2. The tail `GEM`: at `c`, and on the box of `closedBall c (3018/10000)` -/

/-- The four `Q`-factors on the box `0 ≤ Re w ≤ 13/10`, `24415 ≤ Im w ≤ 24416`, in one rational bound. -/
theorem QsupR_le :
    QsupR 12 (6000 + 1 / 5) (13 / 10) 24416 24415 ≤ 1243 / 1000 ∧
    QsupR 12 (6000 + 2 / 5) (13 / 10) 24416 24415 ≤ 1243 / 1000 ∧
    QsupR 12 (6000 + 3 / 5) (13 / 10) 24416 24415 ≤ 1243 / 1000 ∧
    QsupR 12 (6000 + 4 / 5) (13 / 10) 24416 24415 ≤ 1243 / 1000 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [QsupR, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
      Finset.prod_range_zero, Nat.reduceMul, Nat.reduceAdd, bernoulli_2_eq, bernoulli_4_eq,
      bernoulli_6_eq, bernoulli_8_eq, bernoulli_10_eq, bernoulli_12_eq, bernoulli_14_eq,
      bernoulli_16_eq, bernoulli_18_eq, bernoulli_20_eq, bernoulli_22_eq, bernoulli_24_eq]
    norm_num [Nat.factorial]

/-- `Gsup` on the box, from one bound `y` for the four `n^{-σ₀}`, `n = 30001, …, 30004`. -/
theorem Gsup_le_of {σ₀ y : ℝ} (h1 : ex σ₀ 30001 ≤ y) (h2 : ex σ₀ 30002 ≤ y) (h3 : ex σ₀ 30003 ≤ y)
    (h4 : ex σ₀ 30004 ≤ y) :
    Gsup 6000 12 σ₀ (13 / 10) 24416 24415 ≤
      y * (1243 / 1000) + 28408 / 100000 * (y * (1243 / 1000)) + 28408 / 100000 * (y * (1243 / 1000)) +
        y * (1243 / 1000) := by
  obtain ⟨q1, q2, q3, q4⟩ := QsupR_le
  have r1 := QsupB_le_QsupR 12 (x := 6000 + 1 / 5) (σ₁ := 13 / 10) (τ := 24416) (τ₀ := 24415)
    (by norm_num) (by norm_num)
  have r2 := QsupB_le_QsupR 12 (x := 6000 + 2 / 5) (σ₁ := 13 / 10) (τ := 24416) (τ₀ := 24415)
    (by norm_num) (by norm_num)
  have r3 := QsupB_le_QsupR 12 (x := 6000 + 3 / 5) (σ₁ := 13 / 10) (τ := 24416) (τ₀ := 24415)
    (by norm_num) (by norm_num)
  have r4 := QsupB_le_QsupR 12 (x := 6000 + 4 / 5) (σ₁ := 13 / 10) (τ := 24416) (τ₀ := 24415)
    (by norm_num) (by norm_num)
  have hk := kappa_le
  have hk0 := kappa_pos.le
  have hq0 : ∀ j : ℕ, 0 ≤ QsupB 12 (6000 + j / 5) (13 / 10) 24416 24415 := by
    intro j
    unfold QsupB
    positivity
  have p1 := hq0 1
  have p2 := hq0 2
  have p3 := hq0 3
  have p4 := hq0 4
  have x1 : 0 ≤ ex σ₀ 30001 := (Real.exp_pos _).le
  have x2 : 0 ≤ ex σ₀ 30002 := (Real.exp_pos _).le
  have x3 : 0 ≤ ex σ₀ 30003 := (Real.exp_pos _).le
  have x4 : 0 ≤ ex σ₀ 30004 := (Real.exp_pos _).le
  push_cast at p1 p2 p3 p4
  have t1 := mul_le_mul h1 (r1.trans q1) p1 (x1.trans h1)
  have t2 := mul_le_mul hk (mul_le_mul h2 (r2.trans q2) p2 (x2.trans h2)) (mul_nonneg x2 p2)
    (by norm_num)
  have t3 := mul_le_mul hk (mul_le_mul h3 (r3.trans q3) p3 (x3.trans h3)) (mul_nonneg x3 p3)
    (by norm_num)
  have t4 := mul_le_mul h4 (r4.trans q4) p4 (x4.trans h4)
  have e : Gsup 6000 12 σ₀ (13 / 10) 24416 24415 =
      ex σ₀ 30001 * QsupB 12 (6000 + 1 / 5) (13 / 10) 24416 24415 +
        kappa * (ex σ₀ 30002 * QsupB 12 (6000 + 2 / 5) (13 / 10) 24416 24415) +
        kappa * (ex σ₀ 30003 * QsupB 12 (6000 + 3 / 5) (13 / 10) 24416 24415) +
        ex σ₀ 30004 * QsupB 12 (6000 + 4 / 5) (13 / 10) 24416 24415 := by
    unfold Gsup
    norm_num
  rw [e]
  linarith

/-- **The tail at the centre**: `‖GEM 6000 12 w‖ ≤ 31/100000` for `9/10 ≤ Re w ≤ 13/10`, `24415 ≤ Im w ≤ 24416`. -/
theorem Gsup_tight_le : Gsup 6000 12 (9 / 10) (13 / 10) 24416 24415 ≤ 31 / 100000 := by
  have e1 : ex (9 / 10) 30001 ≤ 94 / 1000000 :=
    ex_le_of (p := 9) (q := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : ex (9 / 10) 30002 ≤ 94 / 1000000 :=
    ex_le_of (p := 9) (q := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : ex (9 / 10) 30003 ≤ 94 / 1000000 :=
    ex_le_of (p := 9) (q := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : ex (9 / 10) 30004 ≤ 94 / 1000000 :=
    ex_le_of (p := 9) (q := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (Gsup_le_of e1 e2 e3 e4).trans (by norm_num)

/-- **The tail on the box of `closedBall c (3018/10000)`**: `‖GEM 6000 12 w‖ ≤ 7/1000` for `6/10 ≤ Re w ≤ 13/10`,
`24415 ≤ Im w ≤ 24416`. -/
theorem Gsup_wide_le : Gsup 6000 12 (6 / 10) (13 / 10) 24416 24415 ≤ 7 / 1000 := by
  have e1 : ex (6 / 10) 30001 ≤ 207 / 100000 :=
    ex_le_of (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : ex (6 / 10) 30002 ≤ 207 / 100000 :=
    ex_le_of (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : ex (6 / 10) 30003 ≤ 207 / 100000 :=
    ex_le_of (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : ex (6 / 10) 30004 ≤ 207 / 100000 :=
    ex_le_of (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (Gsup_le_of e1 e2 e3 e4).trans (by norm_num)

/-- `‖GEM 6000 12 w‖ ≤ 7/1000` on `closedBall c (3018/10000)`. -/
theorem norm_GEM_le_wide {w : ℂ} (hw : w ∈ closedBall cZ (3018 / 10000)) : ‖GEM 6000 12 w‖ ≤ 7 / 1000 := by
  obtain ⟨b1, b2, b3, b4⟩ := box_of_memG hw
  rw [cZ_re] at b1 b2
  rw [cZ_im] at b3 b4
  have hT : |w.im| ≤ 24416 := by rw [abs_le]; constructor <;> linarith
  have hT0 : (24415 : ℝ) ≤ |w.im| := by rw [abs_of_pos (by linarith)]; linarith
  exact (norm_GEM_le 6000 12 (σ₀ := 6 / 10) (σ₁ := 13 / 10) (by norm_num) (by norm_num)
    (by linarith) (by linarith) hT hT0).trans Gsup_wide_le

theorem cZ_ne_one : cZ ≠ 1 :=
  ne_one_of_memG (c := cZ) (ρ := 1) (by rw [cZ_im]; norm_num) (mem_closedBall_self (by norm_num))

/-- **The tail at the centre**: `‖GEM 6000 12 c‖ ≤ 31/100000`. -/
theorem norm_GEM_cZ : ‖GEM 6000 12 cZ‖ ≤ 31 / 100000 := by
  have hT : |cZ.im| ≤ 24416 := by rw [cZ_im, abs_le]; constructor <;> norm_num
  have hT0 : (24415 : ℝ) ≤ |cZ.im| := by rw [cZ_im, abs_of_pos (by norm_num)]; norm_num
  exact (norm_GEM_le 6000 12 (σ₀ := 9 / 10) (σ₁ := 13 / 10) (by norm_num) (by norm_num)
    (by rw [cZ_re]; norm_num) (by rw [cZ_re]; norm_num) hT hT0).trans Gsup_tight_le

/-- **Cauchy for `GEM′` at the centre**, on the circle of radius `3/10`: `‖GEM′(c)‖ ≤ 7/300`. -/
theorem norm_GEMd_cZ : ‖GEMd 6000 12 cZ‖ ≤ 7 / 300 := by
  rw [← (hasDerivAt_GEM 6000 12 cZ_ne_one).deriv]
  have hsub : closedBall cZ (3 / 10) ⊆ closedBall cZ (3018 / 10000) :=
    closedBall_subset_closedBall (by norm_num)
  have hd : DiffContOnCl ℂ (GEM 6000 12) (ball cZ (3 / 10)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball cZ (by norm_num)]
    exact (differentiableOn_GEM 6000 12).mono fun w hw =>
      ne_one_of_memG (c := cZ) (by rw [cZ_im]; norm_num) hw
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (R := 3 / 10) (C := 7 / 1000)
    (by norm_num) hd fun w hw => norm_GEM_le_wide (hsub (sphere_subset_closedBall hw))
  exact h.trans (le_of_eq (by norm_num))

/-! ## 3. The three numbers at the centre -/

/-- `‖fEM 6000 12 c‖ ≤ 42/100000`: the Dirichlet polynomial is below `11/100000` there, by the kernel's sums. -/
theorem norm_fEM_cZ : ‖fEM 6000 12 cZ‖ ≤ 42 / 100000 := by
  have hA := inv6000.A
  have hB := inv6000.B
  obtain ⟨a1, a2⟩ := DHBall.bounds_of_has hA.1
  obtain ⟨a3, a4⟩ := DHBall.bounds_of_has hA.2
  obtain ⟨b1, b2⟩ := DHBall.bounds_of_has hB.1
  obtain ⟨b3, b4⟩ := DHBall.bounds_of_has hB.2
  simp only [DHBall.st6, DHBall.S] at a1 a2 a3 a4 b1 b2 b3 b4
  norm_num at a1 a2 a3 a4 b1 b2 b3 b4
  obtain ⟨k1, k2⟩ := kappaBG
  have hk0 := kappa_pos.le
  have hre : (DEM 6000 cZ).re = (SA 6000).re + kappa * (SB 6000).re := by
    rw [DEM_eq, Complex.add_re, Complex.re_ofReal_mul]
  have him : (DEM 6000 cZ).im = (SA 6000).im + kappa * (SB 6000).im := by
    rw [DEM_eq, Complex.add_im, Complex.im_ofReal_mul]
  have hD : ‖DEM 6000 cZ‖ ≤ 11 / 100000 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hre, him]
    have u1 := mul_le_mul_of_nonneg_left b1 hk0
    have u2 := mul_le_mul_of_nonneg_left b2 hk0
    have u3 := mul_le_mul_of_nonneg_left b3 hk0
    have u4 := mul_le_mul_of_nonneg_left b4 hk0
    have hr : |(SA 6000).re + kappa * (SB 6000).re| ≤ 92 / 1000000 := by
      rw [abs_le]; constructor <;> linarith
    have hi : |(SA 6000).im + kappa * (SB 6000).im| ≤ 13 / 1000000 := by
      rw [abs_le]; constructor <;> linarith
    linarith
  rw [fEM]
  exact (norm_add_le _ _).trans (by linarith [norm_GEM_cZ])

/-- `196/100 ≤ ‖fEM′(c)‖`: the real part of the Dirichlet polynomial's derivative is above `1.9899` there. -/
theorem norm_fEMd_cZ : (196 / 100 : ℝ) ≤ ‖DEMk 1 6000 cZ + GEMd 6000 12 cZ‖ := by
  have hA := inv6000.A1
  have hB := inv6000.B1
  obtain ⟨a1, -⟩ := DHBall.bounds_of_has hA.1
  obtain ⟨b1, -⟩ := DHBall.bounds_of_has hB.1
  simp only [DHBall.st6, DHBall.S] at a1 b1
  norm_num at a1 b1
  obtain ⟨k1, k2⟩ := kappaBG
  have hk0 := kappa_pos.le
  have hre : (DEMk 1 6000 cZ).re = (SA1 6000).re + kappa * (SB1 6000).re := by
    rw [DEMk_one_eq, Complex.add_re, Complex.re_ofReal_mul]
  have u1 := mul_le_mul_of_nonneg_left b1 hk0
  have hD : (1989 / 1000 : ℝ) ≤ ‖DEMk 1 6000 cZ‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [hre]
    refine le_trans ?_ (le_abs_self _)
    linarith
  have hG := norm_GEMd_cZ
  have h := norm_sub_norm_le (DEMk 1 6000 cZ) (-GEMd 6000 12 cZ)
  rw [norm_neg, sub_neg_eq_add] at h
  linarith

/-- The termwise sum: `D2sum(9168/10000, 6000) ≤ 464`. -/
theorem D2sum_le_num : D2sum (9168 / 10000) 6000 ≤ 464 := by
  have hA := inv6000.d2a
  have hB := inv6000.d2b
  simp only [DHBall.st6, DHBall.S] at hA hB
  norm_num at hA hB
  obtain ⟨k1, k2⟩ := kappaBG
  have hk0 := kappa_pos.le
  have hB0 : 0 ≤ D2B 6000 := by
    unfold D2B
    exact Finset.sum_nonneg fun m _ => by positivity
  have h := D2sum_le
  nlinarith

/-! ## 4. The ball-uniform bounds -/

theorem five_rpow_le : (5 : ℝ) ^ (-(9168 / 10000 : ℝ)) ≤ (235 / 1000 : ℝ) := by
  calc (5 : ℝ) ^ (-(9168 / 10000 : ℝ)) ≤ (5 : ℝ) ^ (-((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = (5 : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) := by rw [neg_div]
    _ ≤ (235 / 1000 : ℝ) := rpow_neg_div_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `(6000 + j/5)^{1 − σ₀ − 24} ≤ (4/10000)/6000²³`, for `σ₀ = 9168/10000`. -/
theorem hy {x : ℝ} (hx : 6000 ≤ x) :
    x ^ (1 - (9168 / 10000 : ℝ) - 2 * 12) ≤ 4 / 10000 / (6000 : ℝ) ^ 23 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have e : (1 - (9168 / 10000 : ℝ) - 2 * 12) = -(239168 / 10000 : ℝ) := by norm_num
  rw [e]
  calc x ^ (-(239168 / 10000 : ℝ))
      ≤ x ^ (-(((23 : ℕ) : ℝ) + ((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ ≤ (x ^ 23)⁻¹ * (4 / 10000 : ℝ) := by
        refine rpow_neg_add_div_le hx0 (by norm_num) 23 (by norm_num) ?_
        have h9 : (6000 : ℝ) ^ 9 ≤ x ^ 9 := pow_le_pow_left₀ (by norm_num) hx 9
        have : (1 : ℝ) ≤ (6000 : ℝ) ^ 9 * (4 / 10000 : ℝ) ^ 10 := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right h9 (by positivity : (0 : ℝ) ≤ (4 / 10000 : ℝ) ^ 10)]
    _ ≤ ((6000 : ℝ) ^ 23)⁻¹ * (4 / 10000 : ℝ) := by
        have h23 : (6000 : ℝ) ^ 23 ≤ x ^ 23 := pow_le_pow_left₀ (by norm_num) hx 23
        gcongr
    _ = 4 / 10000 / (6000 : ℝ) ^ 23 := by ring

theorem prod_box_le : ∏ i ∈ Finset.range (2 * 12), (((9205 / 10000 : ℝ) + i) ^ 2 + (24416 : ℝ) ^ 2)
    ≤ ((2014610000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) ^ 2 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]; norm_num

/-- **The Euler–Maclaurin error on the ball**, normalised: `‖dh z − dhEM 6000 12 z‖ ≤ ‖a(1)‖/100000`. -/
theorem norm_dh_sub_dhEM_le_ball {z : ℂ} (hz : z ∈ closedBall cZ (18 / 10000 : ℝ)) :
    ‖dh z - dhEM 6000 12 z‖ ≤ ‖aDH chi5 1‖ * (1 / 100000 : ℝ) :=
  norm_dh_sub_dhEM_le_ballG (c := cZ) (r := (18 / 10000 : ℝ)) (σ₀ := (9168 / 10000 : ℝ))
    (σ₁ := (9205 / 10000 : ℝ)) (τ := (24416 : ℝ)) (B := (2014610000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)) (M := 6000)
    (by norm_num) (by norm_num) (by norm_num) (by rw [cZ_re]; norm_num) (by rw [cZ_re]; norm_num)
    (by rw [cZ_im]; norm_num) (by rw [cZ_im]; norm_num) prod_box_le five_rpow_le
    (hy (by norm_num)) (hy (by norm_num)) (hy (by norm_num)) (hy (by norm_num)) (by norm_num) hz

/-- **The second derivative on the ball**: `‖DEM″ + GEM″‖ ≤ 4642/10` on `closedBall c (18/10000)`. -/
theorem norm_deriv2_fEM_ball {z : ℂ} (hz : z ∈ closedBall cZ (18 / 10000 : ℝ)) :
    ‖DEMk 2 6000 z + deriv (deriv (GEM 6000 12)) z‖ ≤ 4642 / 10 := by
  have h := norm_deriv2_fEM_ballG 6000 12 (c := cZ) (r := (18 / 10000 : ℝ)) (R := (3 / 10 : ℝ))
    (σd := (9168 / 10000 : ℝ)) (σ₀ := (6 / 10 : ℝ)) (σ₁ := (13 / 10 : ℝ)) (τ := (24416 : ℝ))
    (τ₀ := (24415 : ℝ)) (C := (7 / 1000 : ℝ)) (d₂ := (464 : ℝ)) (by rw [cZ_re]; norm_num) D2sum_le_num
    (by norm_num) (by norm_num) (by norm_num) (by rw [cZ_re]; norm_num) (by rw [cZ_re]; norm_num)
    (by rw [cZ_im]; norm_num) (by rw [cZ_im]; norm_num) Gsup_wide_le hz
  exact h.trans (by norm_num)

/-! ## 5. The zero -/

/-- **A zero of `dh` within `18/10000` of `c = 918601/1000000 + (2441547865/100000) i`.** -/
theorem dh_zero_near : ∃ ρ, dh ρ = 0 ∧ ‖ρ - cZ‖ < 18 / 10000 :=
  dh_zero_near_of_fEMG (c := cZ) (r := (18 / 10000 : ℝ)) (p₀ := (42 / 100000 : ℝ)) (a₀ := (196 / 100 : ℝ))
    (m₂ := (4642 / 10 : ℝ)) (e₀ := (1 / 100000 : ℝ)) (M := 6000) (K := 12) (by norm_num)
    (by rw [cZ_im]; norm_num) norm_fEM_cZ norm_fEMd_cZ (fun _ hz => norm_deriv2_fEM_ball hz)
    (fun _ hz => norm_dh_sub_dhEM_le_ball hz) (by norm_num)

/-- **The fifth located zero**: `dh` has a zero `ρ` with `0.916801 < Re ρ < 0.920401` and
`24415.47685 < Im ρ < 24415.48045`. -/
theorem dh_zero_located_five :
    ∃ ρ : ℂ, dh ρ = 0 ∧ 916801 / 1000000 < ρ.re ∧ ρ.re < 920401 / 1000000 ∧
      2441547685 / 100000 < ρ.im ∧ ρ.im < 2441548045 / 100000 := by
  obtain ⟨ρ, h0, hρ⟩ := dh_zero_near
  have h1 := (Complex.abs_re_le_norm (ρ - cZ)).trans_lt hρ
  have h2 := (Complex.abs_im_le_norm (ρ - cZ)).trans_lt hρ
  rw [Complex.sub_re, cZ_re, abs_lt] at h1
  rw [Complex.sub_im, cZ_im, abs_lt] at h2
  refine ⟨ρ, h0, ?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **`dh` has a zero with real part above `11/12`**: the zero-free half-plane of the Dirichlet `L`-functions fails
for `dh`, which has their functional equation and no Euler product. -/
theorem dh_zero_re_gt : ∃ ρ : ℂ, dh ρ = 0 ∧ 11 / 12 < ρ.re := by
  obtain ⟨ρ, h0, h1, -⟩ := dh_zero_located_five
  exact ⟨ρ, h0, by linarith⟩

end PsiOmega.Locate.Z5
