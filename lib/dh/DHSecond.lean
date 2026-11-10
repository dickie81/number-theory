import DHLocateGen

/-!
# The second Davenport–Heilbronn function

For a primitive character `χ ≠ 1` the combination `(1 + ε')L(s, χ) + (1 + ε)L(s, χ⁻¹)` of `DavenportHeilbronn` has
the functional equation of an `L`-function with root number `1`. The combination with the other sign,
`(1 − ε')L(s, χ) + (1 − ε)L(s, χ⁻¹)` (`dh2L`), has the same functional equation with the sign `−`
(`dh2Lam_one_sub`). For the character mod `5` with `χ(2) = i` it is `dh2`, the second Davenport–Heilbronn function
of E. Bombieri and A. Ghosh (Russian Math. Surveys 66:2 (2011), §5): their `f(s, τ₋)`, up to a constant.

* `dh2L`, `dh2Lam`, `dh2Lam_one_sub`, `dh2Lam_eq`: the combination, its completion and the functional equation.
* `bDH`, `dh2L_eq_LSeries`: its Dirichlet coefficients, and the series on `Re s > 1`.
* `dh2`, `bDH_chi5_eq_mul`: for `χ₅` the coefficients are `a(1)·κ·v(n mod 5)` with `v = 0, κ, −1, 1, −κ`, where `a(1)`
  and `κ` are those of `dh` (whose coefficients are `a(1)·(0, 1, κ, −κ, −1)`). In Bombieri and Ghosh's normalisation
  the coefficients are `1, τ₋, −τ₋, −1` with `τ₋ = −1/κ`.
* `Locate.secD k M`: the `k`-th derivative of the Dirichlet polynomial `Σ_{n ≤ 5M} v(n) n^{-s}`;
  `Locate.norm_dh2_sub_le`: on `Re s ≥ σ₀ ≥ 2` it is within `‖a(1)‖κ·(5M)^{1−σ₀}` of `dh2/(a(1)κ)`;
  `Locate.norm_secD_two_le`: the termwise bound for its second derivative.

The zero of `dh2` at height `1650`, with real part above `2`, is in `DHSecondZero`.
-/

open Real Complex DirichletCharacter Filter Topology

noncomputable section

namespace PsiOmega

open WeilForm WeilTest

/-! ## The combination with the sign `−` -/

section general

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- The second combination `(1 − ε')L(s, χ) + (1 − ε)L(s, χ⁻¹)`, `ε, ε'` the root numbers of `χ, χ⁻¹`. -/
def dh2L (s : ℂ) : ℂ :=
  (1 - rootNumber χ⁻¹) * LFunction χ s + (1 - rootNumber χ) * LFunction χ⁻¹ s

/-- Its completion `(1 − ε')Λ*(s, χ) + (1 − ε)Λ*(s, χ⁻¹)`, `Λ* = N^{s/2}Λ`. -/
def dh2Lam (s : ℂ) : ℂ :=
  (1 - rootNumber χ⁻¹) * LamG χ s + (1 - rootNumber χ) * LamG χ⁻¹ s

/-- **The functional equation `Λ₂(1 − s) = −Λ₂(s)`**, from Mathlib's functional equation for `χ` and `χ⁻¹` and
`εε' = 1`. -/
theorem dh2Lam_one_sub (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (s : ℂ) :
    dh2Lam χ (1 - s) = -dh2Lam χ s := by
  have hprim' := isPrimitive_inv χ hprim
  have heps := rootNumber_mul_rootNumber_inv χ hχ hprim
  have h1 := hprim.completedLFunction_one_sub s
  have h2 := hprim'.completedLFunction_one_sub s
  rw [inv_inv] at h2
  have e : (N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2) = (N : ℂ) ^ (s / 2) := by
    rw [← cpow_add _ _ natCast_ne_zero']; congr 1; ring
  unfold dh2Lam LamG
  rw [h1, h2]
  linear_combination ((rootNumber χ - rootNumber χ * rootNumber χ⁻¹) * completedLFunction χ⁻¹ s
      + (rootNumber χ⁻¹ - rootNumber χ * rootNumber χ⁻¹) * completedLFunction χ s) * e
    - ((N : ℂ) ^ (s / 2) * (completedLFunction χ s + completedLFunction χ⁻¹ s)) * heps

theorem differentiable_dh2L (hχ : χ ≠ 1) : Differentiable ℂ (dh2L χ) :=
  ((differentiable_LFunction hχ).const_mul _).add
    ((differentiable_LFunction (inv_ne_one.2 hχ)).const_mul _)

/-- **`Λ₂ = N^{s/2} Γ_ℝ(s + 1) · dh2L`** on `Re s > 0` for odd `χ`. -/
theorem dh2Lam_eq (hodd : χ.Odd) {s : ℂ} (hs : 0 < s.re) :
    dh2Lam χ s = (N : ℂ) ^ (s / 2) * Gammaℝ (s + 1) * dh2L χ s := by
  have hodd' := odd_inv χ hodd
  unfold dh2Lam LamG dh2L
  rw [completed_eq_mul hs, completed_eq_mul hs, hodd.gammaFactor_def, hodd'.gammaFactor_def]
  ring

/-- `b(n) = (1 − ε_{χ⁻¹}) χ(n) + (1 − ε_χ) χ⁻¹(n)`, the Dirichlet coefficients of `dh2L χ`. -/
def bDH (n : ℕ) : ℂ :=
  (1 - rootNumber χ⁻¹) * χ n + (1 - rootNumber χ) * χ⁻¹ n

theorem norm_bDH_le (n : ℕ) : ‖bDH χ n‖ ≤ ‖1 - rootNumber χ⁻¹‖ + ‖1 - rootNumber χ‖ := by
  unfold bDH
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  gcongr
  · exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one χ _)
  · exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one χ⁻¹ _)

/-- **`dh2L χ s = Σ b(n) n^{−s}` on `Re s > 1`.** -/
theorem dh2L_eq_LSeries {s : ℂ} (hs : 1 < s.re) : dh2L χ s = LSeries (bDH χ) s := by
  have h1 : LSeriesSummable (fun n : ℕ => χ n) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_le_one χ _) hs
  have h2 : LSeriesSummable (fun n : ℕ => χ⁻¹ n) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_le_one χ⁻¹ _) hs
  have e : bDH χ = (1 - rootNumber χ⁻¹) • (fun n : ℕ => χ n)
      + (1 - rootNumber χ) • (fun n : ℕ => χ⁻¹ n) := by
    funext n; simp [bDH]
  unfold dh2L
  rw [LFunction_eq_LSeries χ hs, LFunction_eq_LSeries χ⁻¹ hs, e,
    LSeries_add (h1.smul _) (h2.smul _), LSeries_smul, LSeries_smul]

/-- The series of `dh2L χ` on `Re s > 1`, as a sum. -/
theorem hasSum_dh2L {s : ℂ} (hs : 1 < s.re) : HasSum (LSeries.term (bDH χ) s) (dh2L χ s) := by
  have h : LSeriesSummable (bDH χ) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_bDH_le χ n) hs
  rw [dh2L_eq_LSeries χ hs]
  exact h.LSeriesHasSum

end general

/-! ## The function for `χ₅` -/

/-- **The second Davenport–Heilbronn function** `(1 − ε')L(s, χ₅) + (1 − ε)L(s, χ₅⁻¹)`. -/
def dh2 : ℂ → ℂ := dh2L chi5

theorem differentiable_dh2 : Differentiable ℂ dh2 := differentiable_dh2L chi5 chi5_ne_one

/-- **Its functional equation**, with the sign `−`. -/
theorem dh2_functional_equation (s : ℂ) : dh2Lam chi5 (1 - s) = -dh2Lam chi5 s :=
  dh2Lam_one_sub chi5 chi5_ne_one chi5_isPrimitive s

/-- On `Re s > 0` the zeros of `dh2` are those of its completion. -/
theorem dh2_eq_zero_iff {s : ℂ} (hs : 0 < s.re) : dh2 s = 0 ↔ dh2Lam chi5 s = 0 := by
  rw [dh2Lam_eq chi5 chi5_odd hs]
  have h1 : ((5 : ℕ) : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => natCast_ne_zero' h.1
  have h2 : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  constructor
  · intro h; rw [show dh2L chi5 s = dh2 s from rfl, h, mul_zero]
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' (mul_ne_zero h1 h2)
    · exact h'

/-- `b(n) = 2((1 − Re ε) Re χ₅(n) − Im ε · Im χ₅(n))`, real. -/
theorem bDH_chi5_eq (n : ℕ) : bDH chi5 n =
    ((2 * ((1 - 2 * Real.sin (2 * π / 5) / Real.sqrt 5) * (chi5 n).re
      - 2 * Real.sin (π / 5) / Real.sqrt 5 * (chi5 n).im) : ℝ) : ℂ) := by
  simp only [bDH, chi5_inv_apply, rootNumber_chi5_inv_eq_conj, rootNumber_chi5_eq]
  apply Complex.ext <;>
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I] <;> ring

/-- `κ · Im ε = 1 − Re ε`: with `κ(1 + Re ε) = Im ε`, this is `|ε| = 1`. -/
theorem kappa_mul_im_eps :
    kappa * (2 * Real.sin (π / 5) / Real.sqrt 5) = 1 - 2 * Real.sin (2 * π / 5) / Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h1 := kappa_mul_one_add
  have hpos : 0 < 1 + 2 * Real.sin (2 * π / 5) / Real.sqrt 5 :=
    add_pos one_pos (div_pos (by linarith [sin_two_pi_div_five_pos]) (Real.sqrt_pos.2 (by norm_num)))
  have h2 : (2 * Real.sin (2 * π / 5) / Real.sqrt 5) ^ 2 + (2 * Real.sin (π / 5) / Real.sqrt 5) ^ 2 = 1 := by
    have hsum := sin_sq_pi_div_five_add
    rw [div_pow, div_pow, s5]
    nlinarith
  have key : (kappa * (2 * Real.sin (π / 5) / Real.sqrt 5) -
      (1 - 2 * Real.sin (2 * π / 5) / Real.sqrt 5)) * (1 + 2 * Real.sin (2 * π / 5) / Real.sqrt 5) = 0 := by
    linear_combination (2 * Real.sin (π / 5) / Real.sqrt 5) * h1 + h2
  rcases mul_eq_zero.1 key with h | h
  · linarith
  · linarith

/-- The normalised coefficients of `dh2` by residue class mod 5: `0, κ, −1, 1, −κ`. -/
def vval (r : ℕ) : ℝ :=
  if r = 1 then kappa else if r = 2 then -1 else if r = 3 then 1 else if r = 4 then -kappa else 0

theorem kappa_mul_re_sub_im (n : ℕ) :
    kappa * (chi5 n).re - (chi5 n).im = vval (n % 5) := by
  rw [← ZMod.natCast_mod n 5]
  have h : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize n % 5 = r at h ⊢
  interval_cases r <;> simp [vval]

/-- **`b(n) = a(1)·κ·v(n mod 5)`** for every `n`, with `a(1)` the first coefficient of `dh`. -/
theorem bDH_chi5_eq_mul (n : ℕ) :
    bDH chi5 n = aDH chi5 1 * (kappa : ℂ) * ((vval (n % 5) : ℝ) : ℂ) := by
  rw [bDH_chi5_eq n, aDH_chi5_eq 1, ← kappa_mul_re_sub_im n, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  simp only [Nat.cast_one, chi5_apply_one, Complex.one_re, Complex.one_im]
  linear_combination (-2 * (kappa * (chi5 n).re - (chi5 n).im)) * kappa_mul_one_add
    + (-2 * (chi5 n).re) * kappa_mul_im_eps

theorem abs_vval_le_one (r : ℕ) : |vval r| ≤ 1 := by
  have h1 := kappa_pos
  have h2 := kappa_lt
  unfold vval
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

namespace Locate

/-! ## The Dirichlet polynomial and the tail -/

/-- The `k`-th derivative of the Dirichlet polynomial of `dh2/(a(1)κ)` over `n ≤ 5M`:
`Σ_{m<M} (κ(5m+1)^{-s} − (5m+2)^{-s} + (5m+3)^{-s} − κ(5m+4)^{-s})` for `k = 0`. -/
def secD (k M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, ((kappa : ℂ) * npsD k (5 * m + 1) s - npsD k (5 * m + 2) s
    + npsD k (5 * m + 3) s - (kappa : ℂ) * npsD k (5 * m + 4) s)

theorem hasDerivAt_secD (k M : ℕ) (s : ℂ) : HasDerivAt (secD k M) (secD (k + 1) M s) s := by
  have hf : secD k M = fun s => ∑ m ∈ Finset.range M, ((kappa : ℂ) * npsD k (5 * m + 1) s -
      npsD k (5 * m + 2) s + npsD k (5 * m + 3) s - (kappa : ℂ) * npsD k (5 * m + 4) s) := rfl
  rw [hf, secD]
  apply HasDerivAt.fun_sum
  intro m _
  exact ((((hasDerivAt_npsD k (by omega) s).const_mul _).sub (hasDerivAt_npsD k (by omega) s)).add
    (hasDerivAt_npsD k (by omega) s)).sub ((hasDerivAt_npsD k (by omega) s).const_mul _)

/-- A term of the series of `dh2`. -/
theorem term_bDH_chi5 {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    LSeries.term (bDH chi5) s n =
      aDH chi5 1 * (kappa : ℂ) * (((vval (n % 5) : ℝ) : ℂ) * npsD 0 n s) := by
  rw [LSeries.term_of_ne_zero (by omega), bDH_chi5_eq_mul, npsD, pow_zero, one_mul, Complex.cpow_neg]
  ring

/-- **The partial sums of the series of `dh2`** over `n ≤ 5M`. -/
theorem sum_range_term_bDH (M : ℕ) (s : ℂ) :
    ∑ n ∈ Finset.range (5 * M + 1), LSeries.term (bDH chi5) s n =
      aDH chi5 1 * (kappa : ℂ) * secD 0 M s := by
  induction M with
  | zero => simp [secD]
  | succ M ih =>
    have e : 5 * (M + 1) + 1 = 5 * M + 1 + 1 + 1 + 1 + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, term_bDH_chi5 (by omega), term_bDH_chi5 (by omega),
      term_bDH_chi5 (by omega), term_bDH_chi5 (by omega), term_bDH_chi5 (by omega)]
    have m1 : (5 * M + 1) % 5 = 1 := by omega
    have m2 : (5 * M + 1 + 1) % 5 = 2 := by omega
    have m3 : (5 * M + 1 + 1 + 1) % 5 = 3 := by omega
    have m4 : (5 * M + 1 + 1 + 1 + 1) % 5 = 4 := by omega
    have m5 : (5 * M + 1 + 1 + 1 + 1 + 1) % 5 = 0 := by omega
    have v1 : vval 1 = kappa := by simp [vval]
    have v2 : vval 2 = -1 := by simp [vval]
    have v3 : vval 3 = 1 := by simp [vval]
    have v4 : vval 4 = -kappa := by simp [vval]
    have v0 : vval 0 = 0 := by simp [vval]
    rw [m1, m2, m3, m4, m5, v1, v2, v3, v4, v0]
    have hS : secD 0 (M + 1) s = secD 0 M s + ((kappa : ℂ) * npsD 0 (5 * M + 1) s -
        npsD 0 (5 * M + 1 + 1) s + npsD 0 (5 * M + 1 + 1 + 1) s -
        (kappa : ℂ) * npsD 0 (5 * M + 1 + 1 + 1 + 1) s) := by
      rw [secD, Finset.sum_range_succ, ← secD]
    rw [hS]
    push_cast
    ring

/-- `1/n^σ ≤ N^{-(σ₀ − 2)}/n²` for `n ≥ N ≥ 1` and `σ ≥ σ₀ ≥ 2`. -/
theorem inv_rpow_le_of_two_le {n N : ℕ} (hN : 1 ≤ N) (hn : N ≤ n) {σ₀ σ : ℝ} (hσ₀ : 2 ≤ σ₀)
    (hσ : σ₀ ≤ σ) : 1 / (n : ℝ) ^ σ ≤ (N : ℝ) ^ (-(σ₀ - 2)) * ((n : ℝ) ^ 2)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hN0 (by exact_mod_cast hn)
  have hn1 : (1 : ℝ) ≤ n := le_trans (by exact_mod_cast hN) (by exact_mod_cast hn : (N : ℝ) ≤ n)
  have h1 : (n : ℝ) ^ σ₀ ≤ (n : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le hn1 hσ
  have h2 : (n : ℝ) ^ σ₀ = (n : ℝ) ^ 2 * (n : ℝ) ^ (σ₀ - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    congr 1
    push_cast
    ring
  have h3 : (N : ℝ) ^ (σ₀ - 2) ≤ (n : ℝ) ^ (σ₀ - 2) :=
    Real.rpow_le_rpow hN0.le (by exact_mod_cast hn) (by linarith)
  have hN2 : 0 < (N : ℝ) ^ (σ₀ - 2) := Real.rpow_pos_of_pos hN0 _
  have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
  have h4 : (n : ℝ) ^ 2 * (N : ℝ) ^ (σ₀ - 2) ≤ (n : ℝ) ^ σ := by
    rw [h2] at h1
    exact (mul_le_mul_of_nonneg_left h3 hn2.le).trans h1
  rw [Real.rpow_neg hN0.le, ← mul_inv, ← one_div, mul_comm]
  exact one_div_le_one_div_of_le (by positivity) h4

/-- **The tail of the series of `dh2`**: on `Re s ≥ σ₀ ≥ 2` the Dirichlet polynomial over `n ≤ 5M` is within
`‖a(1)‖κ·(5M)^{−(σ₀−2)}/(5M)` of `dh2`. -/
theorem norm_dh2_sub_le {M : ℕ} (hM : 1 ≤ M) {σ₀ : ℝ} (hσ₀ : 2 ≤ σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) :
    ‖dh2 s - aDH chi5 1 * (kappa : ℂ) * secD 0 M s‖ ≤
      ‖aDH chi5 1‖ * kappa * (((5 * M : ℕ) : ℝ) ^ (-(σ₀ - 2)) * ((5 * M : ℕ) : ℝ)⁻¹) := by
  have hs1 : 1 < s.re := by linarith
  have hk0 := kappa_pos
  have h5M : 1 ≤ 5 * M := by omega
  have htend := (hasSum_dh2L chi5 hs1).tendsto_sum_nat
  have hA0 : 0 ≤ ‖aDH chi5 1‖ * kappa := mul_nonneg (norm_nonneg _) hk0.le
  have hR0 : 0 ≤ ((5 * M : ℕ) : ℝ) ^ (-(σ₀ - 2)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hev : ∀ᶠ n in atTop, ‖∑ i ∈ Finset.range n, LSeries.term (bDH chi5) s i -
      aDH chi5 1 * (kappa : ℂ) * secD 0 M s‖ ≤
      ‖aDH chi5 1‖ * kappa * (((5 * M : ℕ) : ℝ) ^ (-(σ₀ - 2)) * ((5 * M : ℕ) : ℝ)⁻¹) := by
    filter_upwards [Filter.eventually_ge_atTop (5 * M + 1)] with n hn
    rw [← sum_range_term_bDH M s, ← Finset.sum_range_add_sum_Ico _ hn, add_sub_cancel_left]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.Ico (5 * M + 1) n, ‖LSeries.term (bDH chi5) s i‖ ≤
        ‖aDH chi5 1‖ * kappa * ((5 * M : ℕ) : ℝ) ^ (-(σ₀ - 2)) * ((i : ℝ) ^ 2)⁻¹ := by
      intro i hi
      have hi1 : 5 * M ≤ i := by have := (Finset.mem_Ico.1 hi).1; omega
      have hi0 : i ≠ 0 := by omega
      rw [LSeries.term_of_ne_zero hi0, norm_div, Complex.norm_natCast_cpow_of_pos (by omega),
        bDH_chi5_eq_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hk0, div_eq_mul_one_div]
      have hv := abs_vval_le_one (i % 5)
      have hr := inv_rpow_le_of_two_le h5M hi1 hσ₀ hs
      have hr0 : 0 ≤ 1 / (i : ℝ) ^ s.re := by positivity
      calc ‖aDH chi5 1‖ * kappa * |vval (i % 5)| * (1 / (i : ℝ) ^ s.re)
          ≤ ‖aDH chi5 1‖ * kappa * 1 * (((5 * M : ℕ) : ℝ) ^ (-(σ₀ - 2)) * ((i : ℝ) ^ 2)⁻¹) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hv hA0) hr hr0 (by linarith [hA0])
        _ = ‖aDH chi5 1‖ * kappa * ((5 * M : ℕ) : ℝ) ^ (-(σ₀ - 2)) * ((i : ℝ) ^ 2)⁻¹ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hsub : Finset.Ico (5 * M + 1) n ⊆ Finset.Ioc (5 * M) n := by
      intro i hi
      have := Finset.mem_Ico.1 hi
      exact Finset.mem_Ioc.2 ⟨by omega, by omega⟩
    have hI : ∑ i ∈ Finset.Ico (5 * M + 1) n, ((i : ℝ) ^ 2)⁻¹ ≤ ((5 * M : ℕ) : ℝ)⁻¹ := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity).trans ?_
      have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 5 * M) (n := n) (by omega) (by omega)
      have hn0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      linarith
    calc ‖aDH chi5 1‖ * kappa * ((5 * M : ℕ) : ℝ) ^ (-(σ₀ - 2)) * ∑ i ∈ Finset.Ico (5 * M + 1) n, ((i : ℝ) ^ 2)⁻¹
        ≤ ‖aDH chi5 1‖ * kappa * ((5 * M : ℕ) : ℝ) ^ (-(σ₀ - 2)) * ((5 * M : ℕ) : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hI (mul_nonneg hA0 hR0)
      _ = ‖aDH chi5 1‖ * kappa * (((5 * M : ℕ) : ℝ) ^ (-(σ₀ - 2)) * ((5 * M : ℕ) : ℝ)⁻¹) := by ring
  exact le_of_tendsto ((htend.sub_const _).norm) hev

/-! ## The second derivative, termwise -/

/-- The termwise bound for the second derivative of the Dirichlet polynomial:
`Σ_{m<M} Σ_j |v(j)| log²(5m+j) (5m+j)^{-σ}`. -/
def secD2sum (σ : ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M, (kappa * (Real.log (5 * m + 1 : ℕ) ^ 2 * ex σ (5 * m + 1))
    + Real.log (5 * m + 2 : ℕ) ^ 2 * ex σ (5 * m + 2)
    + Real.log (5 * m + 3 : ℕ) ^ 2 * ex σ (5 * m + 3)
    + kappa * (Real.log (5 * m + 4 : ℕ) ^ 2 * ex σ (5 * m + 4)))

theorem norm_secD_two_le (M : ℕ) {σ : ℝ} {w : ℂ} (hw : σ ≤ w.re) :
    ‖secD 2 M w‖ ≤ secD2sum σ M := by
  rw [secD, secD2sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  have hk : ‖(kappa : ℂ)‖ = kappa := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos kappa_pos]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add_left (norm_add_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (norm_sub_le _ _) _) _).trans ?_
  rw [norm_mul, norm_mul, hk]
  have h1 := norm_npsD_le 2 (n := 5 * m + 1) (by omega) hw
  have h2 := norm_npsD_le 2 (n := 5 * m + 2) (by omega) hw
  have h3 := norm_npsD_le 2 (n := 5 * m + 3) (by omega) hw
  have h4 := norm_npsD_le 2 (n := 5 * m + 4) (by omega) hw
  have hk0 := kappa_pos
  nlinarith [mul_le_mul_of_nonneg_left h1 hk0.le, mul_le_mul_of_nonneg_left h4 hk0.le]

end Locate

end PsiOmega

#print axioms PsiOmega.dh2Lam_one_sub
#print axioms PsiOmega.bDH_chi5_eq_mul
#print axioms PsiOmega.Locate.norm_dh2_sub_le
#print axioms PsiOmega.Locate.norm_secD_two_le
