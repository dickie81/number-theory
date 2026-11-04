import D2Hcount
import ModelMoments

/-!
# Quantitative moments, uniform in `P ⊆ [1, y]` (unconditional)

`QuantMoments.moment_quant_pos`, `QuantMoments.moment_quant_neg`: for `P ⊆ [1, y]`, real weights `a` and every `k`, `x`,
the `k`-th moment of `Σ_{n ∈ P} a_n χ_D(n)` over fundamental `D ∈ (0, x]` of each sign is
`(3/π²) x E[(Σ a_n X(n))^k]` up to `(Σ |a_n|)^k · 2048 y^{3k} (√x + 2)`. From `GSMoment.moment_generic` with the
explicit Hcount (`GSHcount.hcount_pos`) for the square terms and `QuantMoments.GSB_le` (`GSB n x ≤ 2048 n³(√x+1)`)
for the others.
-/

namespace QuantMoments
open Finset Filter Topology
open GSFund GSEven GSKron GSMoment GSDens GSLink GSUncond GSDelta GSNu GSAssemble

theorem shape_le (c : ℕ) (hc : 1 ≤ c) :
    (c.divisors.card : ℝ) * (Real.sqrt c * (1 + Real.log c)) ≤ (c : ℝ) ^ 3 := by
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have h1 : (c.divisors.card : ℝ) ≤ c := by exact_mod_cast Nat.card_divisors_le_self c
  have h2 : Real.sqrt c ≤ c := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h3 : 1 + Real.log c ≤ c := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < c); linarith
  have h0 : 0 ≤ 1 + Real.log c := by have := Real.log_nonneg hc'; linarith
  calc (c.divisors.card : ℝ) * (Real.sqrt c * (1 + Real.log c)) ≤ c * (c * c) := by
        gcongr
    _ = (c : ℝ) ^ 3 := by ring

theorem T_shape_le {B : ℝ} (hB : 0 ≤ B) (x : ℕ) :
    2 * Real.sqrt (x * B) + B ≤ 2 * (B + 1) * (Real.sqrt x + 1) := by
  have hsB : Real.sqrt B ≤ B + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  rw [Real.sqrt_mul (Nat.cast_nonneg x)]
  have := Real.sqrt_nonneg (x : ℝ)
  nlinarith [Real.sqrt_nonneg B]

theorem Bn_nonneg (n : ℕ) : 0 ≤ Bn n := by
  unfold Bn
  have : 0 ≤ 1 + Real.log ((4 * n : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Real.log_nonneg (show (1:ℝ) ≤ ((4 * n : ℕ) : ℝ) by exact_mod_cast (by omega : 1 ≤ 4 * n)); linarith
  positivity

theorem B8_nonneg (m : ℕ) : 0 ≤ B8 m := by
  unfold B8
  have : 0 ≤ 1 + Real.log ((8 * m : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have := Real.log_nonneg (show (1:ℝ) ≤ ((8 * m : ℕ) : ℝ) by exact_mod_cast (by omega : 1 ≤ 8 * m)); linarith
  positivity

/-- **A polynomial bound for the GS error.** `GSB n x ≤ 2048 n³ (√x + 1)` for `n ≥ 1`. -/
theorem GSB_le {n : ℕ} (hn : 1 ≤ n) (x : ℕ) : GSB n x ≤ 2048 * (n : ℝ) ^ 3 * (Real.sqrt x + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ Real.sqrt x + 1 := by positivity
  unfold GSB
  split_ifs with ho
  · unfold T
    have hB := shape_le (4 * n) (by omega)
    have hBn : Bn n ≤ 64 * (n : ℝ) ^ 3 := by
      unfold Bn; push_cast at hB ⊢; nlinarith
    have := T_shape_le (Bn_nonneg n) x
    have h1 : 2 * (Bn n + 1) ≤ 2 * (64 * (n : ℝ) ^ 3 + 1) := by linarith
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn'
    nlinarith
  · unfold T8
    set m := n / 2 ^ n.factorization 2
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (Nat.div_ne_zero_iff_of_dvd (Nat.ordProj_dvd n 2) |>.2
      ⟨by omega, by positivity⟩)
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self _ _
    have hB := shape_le (8 * m) (by omega)
    have hB8 : B8 m ≤ 512 * (n : ℝ) ^ 3 := by
      have hm3 : (m : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmn 3
      unfold B8; push_cast at hB ⊢; nlinarith
    have := T_shape_le (B8_nonneg m) x
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn'
    nlinarith


theorem gfac_le_one (r : ℕ) : gfac r ≤ 1 :=
  prod_le_one₀ (fun p _ => by positivity) fun p _ => by
    rw [div_le_one (by positivity)]; linarith

theorem kappa_le_one (r : ℕ) : 3 / Real.pi ^ 2 * gfac r ≤ 1 := by
  have h0 : 0 ≤ gfac r := prod_nonneg fun p _ => by positivity
  have hpi : 3 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have : 3 / Real.pi ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  calc 3 / Real.pi ^ 2 * gfac r ≤ 1 * 1 := mul_le_mul this (gfac_le_one r) h0 zero_le_one
    _ = 1 := one_mul 1

open Classical in
/-- **Quantitative moments, uniform in `P ⊆ [1, y]`.** -/
theorem moment_quant (F : ℕ → Prop) [DecidablePred F] (Cp : ℕ → Prop) (hC0 : ¬ Cp 0)
    (hF : ∀ d, F d ↔ Cp (d % 16) ∧ Odf d) (χ : ℕ → ℕ → ℂ)
    (hχ : ∀ d r, 0 < r → χ d (r * r) = if Nat.Coprime d r then 1 else 0)
    (hprod : ∀ d (k : ℕ) (f : Fin k → ℕ), (∀ i, f i ≠ 0) → χ d (∏ i, f i) = ∏ i, χ d (f i))
    (HGS : ∀ x n, 1 < n → ¬ IsSquare n → ‖∑ d ∈ Ioc 0 x, (if F d then χ d n else 0)‖ ≤ GSKron.GSB n x)
    (hcount : ∀ r, 0 < r → ∀ x : ℕ,
      |(Nat.count (Q Cp r) x : ℝ) - 3 / Real.pi ^ 2 * gfac r * x| ≤ (16 * r + 3) * (Real.sqrt x + 1))
    (hd : ∀ {r : ℕ}, 0 < r → GSUncond.dens Cp hC0 r = 3 / Real.pi ^ 2 * gfac r)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) {y : ℕ} (hPy : ∀ p ∈ P, p ≤ y) (a : ℕ → ℝ) (k x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if F d then (∑ p ∈ P, (a p : ℂ) * χ d p) ^ k else 0) -
        (x : ℂ) * ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ P, a n * ModelMoments.Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ)‖ ≤
      (∑ p ∈ P, |a p|) ^ k * (2048 * (y : ℝ) ^ (3 * k) * (Real.sqrt x + 2)) := by
  set BB := 2048 * (y : ℝ) ^ (3 * k) * (Real.sqrt x + 2)
  set R : ℕ → ℝ := fun n => (16 * (Nat.sqrt n : ℝ) + 3) * (Real.sqrt (x + 1 : ℕ) + 1) + 1
  have hRc : ∀ n, 0 < n → IsSquare n → ‖∑ d ∈ Ioc 0 x, (if F d then χ d n else 0) -
      (GSUncond.dens Cp hC0 (Nat.sqrt n) : ℂ) * x‖ ≤ R n := by
    intro n hn hsq
    obtain ⟨r, rfl⟩ := hsq
    have hr : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    rw [sum_eq_count F Cp hC0 hF χ hr (hχ · r hr), Nat.sqrt_eq, hd hr]
    set κ := 3 / Real.pi ^ 2 * gfac r
    have hκ0 : 0 ≤ κ := mul_nonneg (by positivity) (prod_nonneg fun p _ => by positivity)
    have e : ((Nat.count (Q Cp r) (x + 1) : ℕ) : ℂ) - (κ : ℂ) * x =
        (((Nat.count (Q Cp r) (x + 1) : ℝ) - κ * (x + 1 : ℕ) + κ : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hcount r hr (x + 1)
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hκ0]
    simp only [R, Nat.sqrt_eq]
    have := kappa_le_one r
    have h2 : |(Nat.count (Q Cp r) (x + 1) : ℝ) - κ * (x + 1 : ℕ)| ≤ (16 * r + 3) * (Real.sqrt (x + 1 : ℕ) + 1) := by
      simpa [κ, mul_comm, mul_assoc, mul_left_comm] using h1
    linarith
  have hmg := moment_generic F χ hprod P hP (fun p => (a p : ℂ)) k x
    (fun n => (GSUncond.dens Cp hC0 (Nat.sqrt n) : ℂ)) R (fun n => GSKron.GSB n x) hRc (HGS x)
  rw [← ModelMoments.main_eq Cp hC0 hd P hP a k]
  refine hmg.trans ?_
  have hsum : (∑ p ∈ P, |a p|) ^ k * BB =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P), (∏ i, |a (f i)|) * BB := by
    rw [← Fin.prod_const, prod_univ_sum, sum_mul]
  rw [hsum]
  refine sum_le_sum fun f hf => ?_
  have hfP : ∀ i, f i ∈ P := Fintype.mem_piFinset.1 hf
  rw [norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun _ _ => abs_nonneg _)
  set n := ∏ i, f i
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun i _ => (hP _ (hfP i)).ne')
  have hny : n ≤ y ^ k := by
    calc n ≤ ∏ _i : Fin k, y := prod_le_prod' fun i _ => hPy _ (hfP i)
      _ = y ^ k := by simp
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn3 : (n : ℝ) ^ 3 ≤ (y : ℝ) ^ (3 * k) := by
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hny) 3
  have hs0 := Real.sqrt_nonneg (x : ℝ)
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hn1' (by norm_num)
  split_ifs with hsq
  · simp only [R]
    have hsq1 : (Nat.sqrt n : ℝ) ≤ n := by exact_mod_cast Nat.sqrt_le_self n
    have hsx : Real.sqrt (x + 1 : ℕ) ≤ Real.sqrt x + 1 := by
      rw [Real.sqrt_le_left (by positivity)]; push_cast; nlinarith [Real.sq_sqrt (Nat.cast_nonneg x : (0:ℝ) ≤ x)]
    have hsq0 : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
    have : (16 * (Nat.sqrt n : ℝ) + 3) * (Real.sqrt (x + 1 : ℕ) + 1) ≤ (16 * n + 3) * (Real.sqrt x + 2) := by
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    nlinarith
  · have hn2 : 1 < n := by
      rcases Nat.lt_or_ge 1 n with h | h
      · exact h
      · exact absurd ⟨1, by omega⟩ hsq
    refine (GSB_le hn2.le x).trans ?_
    nlinarith


/-- **Quantitative moments, positive fundamental discriminants**, uniform in `P ⊆ [1, y]`. Unconditional. -/
theorem moment_quant_pos (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) {y : ℕ} (hPy : ∀ p ∈ P, p ≤ y) (a : ℕ → ℝ)
    (k x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundPos d then (∑ p ∈ P, (a p : ℂ) * kron d p) ^ k else 0) -
        (x : ℂ) * ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ P, a n * ModelMoments.Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ)‖ ≤
      (∑ p ∈ P, |a p|) ^ k * (2048 * (y : ℝ) ^ (3 * k) * (Real.sqrt x + 2)) := by
  classical
  convert moment_quant fundPos GSLink.CpPos CpPos0 fundPos_iff (fun d n => kron d n)
    (fun d r hr => kron_sq_nat d hr) (fun d k f hf => kron_prod d f hf)
    (fun x n h1 hs => gs_kron_pos h1 hs x) GSHcount.hcount_pos ModelMoments.dens_pos_eq P hP hPy a k x

/-- **Quantitative moments, negative fundamental discriminants** (`D = -d`). Unconditional. -/
theorem moment_quant_neg (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) {y : ℕ} (hPy : ∀ p ∈ P, p ≤ y) (a : ℕ → ℝ)
    (k x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundNeg d then (∑ p ∈ P, (a p : ℂ) * kron (-(d : ℤ)) p) ^ k else 0) -
        (x : ℂ) * ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ P, a n * ModelMoments.Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ)‖ ≤
      (∑ p ∈ P, |a p|) ^ k * (2048 * (y : ℝ) ^ (3 * k) * (Real.sqrt x + 2)) := by
  classical
  convert moment_quant fundNeg GSLink.CpNeg CpNeg0 fundNeg_iff (fun d n => kron (-(d : ℤ)) n)
    (fun d r hr => by rw [kron_neg_sq_nat d hr]; exact kron_sq_nat d hr) (fun d k f hf => kron_prod _ f hf)
    (fun x n h1 hs => gs_kron_neg h1 hs x) GSHcount.hcount_neg ModelMoments.dens_neg_eq P hP hPy a k x

end QuantMoments
