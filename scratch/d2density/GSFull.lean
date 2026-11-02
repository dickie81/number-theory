import Mathlib

open Real Finset

namespace PolyaVinogradov

/-- `‖e(k/q) − 1‖ ≥ 4 min(k, q−k)/q` for `0 < k < q`. -/
theorem norm_sub_one_ge (q k : ℕ) [NeZero q] (hk0 : 0 < k) (hkq : k < q) :
    4 * ((min k (q - k) : ℕ) : ℝ) / q ≤ ‖ZMod.stdAddChar (k : ZMod q) - 1‖ := by
  have hq : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have he : ZMod.stdAddChar (k : ZMod q) = Complex.exp (Complex.I * ((2 * π * k / q : ℝ) : ℂ)) := by
    have := ZMod.stdAddChar_coe (N := q) (k : ℤ)
    simp only [Int.cast_natCast] at this
    rw [this]; congr 1; push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have hx : 2 * π * k / q / 2 = π * k / q := by ring
  rw [hx]
  -- reduce to the reflected argument when k > q/2
  have key : ∀ m : ℕ, 0 < m → 2 * m ≤ q → 4 * (m:ℝ) / q ≤ 2 * Real.sin (π * m / q) := by
    intro m hm h2
    have h0 : 0 ≤ π * m / q := by positivity
    have h1 : π * m / q ≤ π / 2 := by
      rw [div_le_div_iff₀ hq (by norm_num)]
      have : (2 * m : ℝ) ≤ q := by exact_mod_cast h2
      nlinarith [Real.pi_pos]
    have := Real.mul_le_sin h0 h1
    have e2 : 2 / π * (π * m / q) = 2 * m / q := by field_simp
    rw [e2] at this
    have : 4 * (m:ℝ) / q = 2 * (2 * m / q) := by ring
    linarith
  rcases le_total (2 * k) q with h | h
  · have hm : min k (q - k) = k := min_eq_left (by omega)
    rw [hm]
    have := key k hk0 h
    have hs : 0 ≤ Real.sin (π * k / q) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      rw [div_le_iff₀ hq]; have : (k:ℝ) ≤ q := by exact_mod_cast hkq.le
      nlinarith [Real.pi_pos]
    rw [abs_of_nonneg (by positivity)]; linarith
  · have hm : min k (q - k) = q - k := min_eq_right (by omega)
    rw [hm]
    have := key (q - k) (by omega) (by omega)
    have hr : Real.sin (π * k / q) = Real.sin (π * ((q - k : ℕ) : ℝ) / q) := by
      rw [Nat.cast_sub hkq.le, ← Real.sin_pi_sub]; congr 1; field_simp
    have hs : 0 ≤ Real.sin (π * k / q) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      rw [div_le_iff₀ hq]; have : (k:ℝ) ≤ q := by exact_mod_cast hkq.le
      nlinarith [Real.pi_pos]
    rw [abs_of_nonneg (by positivity), hr]; linarith

/-- `Σ_{0<k<q} 2/‖e(k/q) − 1‖ ≤ q (1 + log q)`. -/
theorem sum_inv_norm_le (q : ℕ) [NeZero q] :
    ∑ k ∈ Ioo 0 q, 2 / ‖ZMod.stdAddChar (k : ZMod q) - 1‖ ≤ q * (1 + Real.log q) := by
  have hq : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have step : ∀ k ∈ Ioo 0 q, 2 / ‖ZMod.stdAddChar (k : ZMod q) - 1‖ ≤
      (q:ℝ) / 2 * ((k:ℝ)⁻¹ + ((q - k : ℕ):ℝ)⁻¹) := by
    intro k hk
    rw [mem_Ioo] at hk
    have hb := norm_sub_one_ge q k hk.1 hk.2
    have hmpos : (0:ℝ) < min k (q - k) := by
      have : 0 < min k (q - k) := lt_min hk.1 (by omega)
      exact_mod_cast this
    have hpos : 0 < 4 * ((min k (q - k) : ℕ) : ℝ) / q := by positivity
    calc 2 / ‖ZMod.stdAddChar (k : ZMod q) - 1‖ ≤ 2 / (4 * ((min k (q - k) : ℕ) : ℝ) / q) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hb
      _ = (q:ℝ) / 2 * ((min k (q - k) : ℕ) : ℝ)⁻¹ := by field_simp; ring
      _ ≤ (q:ℝ) / 2 * ((k:ℝ)⁻¹ + ((q - k : ℕ):ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hk' : (0:ℝ) < k := by exact_mod_cast hk.1
          have hqk : (0:ℝ) < ((q - k : ℕ):ℝ) := by exact_mod_cast (show 0 < q - k by omega)
          rcases min_choice k (q - k) with h | h <;> rw [h] <;>
            [linarith [inv_pos.2 hqk]; linarith [inv_pos.2 hk']]
  have refl : ∑ k ∈ Ioo 0 q, ((q - k : ℕ):ℝ)⁻¹ = ∑ k ∈ Ioo 0 q, (k:ℝ)⁻¹ := by
    apply Finset.sum_nbij' (fun k => q - k) (fun k => q - k) <;> intro k hk <;>
      simp only [coe_Ioo, Set.mem_Ioo, mem_Ioo] at hk ⊢ <;> first | omega | (congr 2; omega)
  have hH : ∑ k ∈ Ioo 0 q, (k:ℝ)⁻¹ ≤ 1 + Real.log q := by
    have e : Ioo 0 q ⊆ Icc 1 q := fun k hk => by simp only [mem_Ioo, mem_Icc] at hk ⊢; omega
    calc ∑ k ∈ Ioo 0 q, (k:ℝ)⁻¹ ≤ ∑ k ∈ Icc 1 q, (k:ℝ)⁻¹ :=
          sum_le_sum_of_subset_of_nonneg e (fun _ _ _ => by positivity)
      _ = (harmonic q : ℝ) := by simp [harmonic_eq_sum_Icc]
      _ ≤ 1 + Real.log q := harmonic_le_one_add_log q
  calc _ ≤ ∑ k ∈ Ioo 0 q, (q:ℝ) / 2 * ((k:ℝ)⁻¹ + ((q - k : ℕ):ℝ)⁻¹) := sum_le_sum step
    _ = (q:ℝ) / 2 * (2 * ∑ k ∈ Ioo 0 q, (k:ℝ)⁻¹) := by
        rw [← mul_sum, sum_add_distrib, refl]; ring
    _ ≤ q * (1 + Real.log q) := by nlinarith



open DirichletCharacter ZMod

section Gauss
variable {q : ℕ} [NeZero q] {R : Type*} [CommRing R] [IsDomain R]
/-- (copied from `lib/core/RealCharHalfPlane.lean`) -/
theorem gaussSum_mul_gaussSum_inv {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e = χ (-1) * q := by
  classical
  have h1 : ∑ y : ZMod q, gaussSum χ (e.mulShift y) * e y = gaussSum χ e * gaussSum χ⁻¹ e := by
    have hg : gaussSum χ⁻¹ e = ∑ y, χ⁻¹ y * e y := rfl
    rw [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [gaussSum_mulShift_of_isPrimitive e hχ]
    ring
  have hin : ∀ x : ZMod q, ∑ y : ZMod q, χ x * e.mulShift y x * e y =
      χ x * (if x + 1 = 0 then (q : R) else 0) := by
    intro x
    have hs := AddChar.sum_mulShift (x + 1) he
    rw [ZMod.card] at hs
    push_cast at hs
    rw [← hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [AddChar.mulShift_apply, mul_add, mul_one, AddChar.map_add_eq_mul, mul_assoc, mul_comm y x]
  have h2 : ∑ y : ZMod q, gaussSum χ (e.mulShift y) * e y = χ (-1) * q := by
    simp only [gaussSum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [hin]
    have hite : ∀ x : ZMod q, χ x * (if x + 1 = 0 then (q : R) else 0) =
        if x = -1 then χ (-1) * q else 0 := by
      intro x
      by_cases hx : x = -1
      · simp [hx]
      · have h0 : x + 1 ≠ 0 := fun h => hx (eq_neg_of_add_eq_zero_left h)
        simp [hx, h0]
    simp_rw [hite]
    rw [Finset.sum_ite_eq' Finset.univ (-1 : ZMod q)]
    simp
  rw [← h1, h2]

end Gauss

variable {q : ℕ} [NeZero q]

theorem isPrimitive_inv {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [isPrimitive_def, conductor_inv]; exact hχ

/-- `‖τ(χ)‖² = q` for primitive `χ`. -/
theorem norm_gaussSum_sq {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ ^ 2 = q := by
  have he := isPrimitive_stdAddChar q
  have h1 := gaussSum_mul_gaussSum_inv hχ he
  have hst : star (gaussSum χ stdAddChar) = χ (-1) * gaussSum χ⁻¹ stdAddChar := by
    rw [star_gaussSum_eq, AddChar.inv_mulShift, gaussSum_mulShift_of_isPrimitive _ (isPrimitive_inv hχ),
      inv_inv]
  have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  have : gaussSum χ stdAddChar * star (gaussSum χ stdAddChar) = q := by
    rw [hst, mul_left_comm, h1, ← mul_assoc, hsq, one_mul]
  have h2 : ((‖gaussSum χ stdAddChar‖ ^ 2 : ℝ) : ℂ) = q := by
    rw [← this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h2

/-- Geometric sum: for `z ≠ 1` on the unit circle, `‖Σ_{M ≤ n < M+N} zⁿ‖ ≤ 2/‖z − 1‖`. -/
theorem norm_geom_le {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Ico M (M + N), z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  have hs : ∑ n ∈ Ico M (M + N), z ^ n = z ^ M * ∑ k ∈ range N, z ^ k := by
    rw [Finset.sum_Ico_eq_sum_range, mul_sum]; simp [pow_add]
  have hne : z - 1 ≠ 0 := sub_ne_zero.2 h1
  rw [hs, geom_sum_eq h1, norm_mul, norm_pow, hz, one_pow, one_mul, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz]; norm_num

/-- **Pólya–Vinogradov.** For a primitive Dirichlet character `χ` mod `q > 1`, and all `M N`,
`‖Σ_{M ≤ n < M+N} χ(n)‖ ≤ √q (1 + log q)`. -/
theorem polya_vinogradov {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) (hq : 1 < q) (M N : ℕ) :
    ‖∑ n ∈ Ico M (M + N), ψ n‖ ≤ Real.sqrt q * (1 + Real.log q) := by
  set χ := ψ⁻¹ with hχdef
  have hχ : χ.IsPrimitive := isPrimitive_inv hψ
  have hψχ : ψ = χ⁻¹ := by rw [hχdef, inv_inv]
  set τ := gaussSum χ stdAddChar
  have hqR : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτn : ‖τ‖ = Real.sqrt q := by
    rw [← norm_gaussSum_sq hχ, Real.sqrt_sq (norm_nonneg _)]
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, norm_zero] at hτn; exact (Real.sqrt_pos.2 hqR).ne' hτn.symm
  -- expansion `ψ(n) τ = Σ_a χ(a) e(a n)`
  have hexp : ∀ n : ℕ, ψ n * τ = ∑ a : ZMod q, χ a * stdAddChar a ^ n := by
    intro n
    rw [hψχ, ← gaussSum_mulShift_of_isPrimitive _ hχ]
    simp only [gaussSum, AddChar.mulShift_apply]
    refine sum_congr rfl fun a _ => ?_
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hsum : (∑ n ∈ Ico M (M + N), ψ n) * τ =
      ∑ a : ZMod q, χ a * ∑ n ∈ Ico M (M + N), stdAddChar a ^ n := by
    rw [sum_mul]; simp_rw [hexp]; rw [sum_comm]; simp_rw [mul_sum]
  -- bound each `a`
  have hterm : ∀ a : ZMod q, ‖χ a * ∑ n ∈ Ico M (M + N), stdAddChar a ^ n‖ ≤
      if a = 0 then 0 else 2 / ‖stdAddChar a - 1‖ := by
    intro a
    split_ifs with ha
    · have : χ a = 0 := by
        rw [ha]; apply MulChar.map_nonunit
        haveI : Fact (1 < q) := ⟨hq⟩
        exact not_isUnit_zero
      simp [this]
    · rw [norm_mul]
      have hχa : ‖χ a‖ ≤ 1 := DirichletCharacter.norm_le_one χ a
      have hz : ‖(stdAddChar a : ℂ)‖ = 1 := by rw [stdAddChar_apply]; exact Circle.norm_coe _
      have hz1 : stdAddChar a ≠ 1 := by
        intro h; apply ha; apply injective_stdAddChar (N := q); rw [h, AddChar.map_zero_eq_one]
      have := norm_geom_le hz hz1 M N
      calc ‖χ a‖ * _ ≤ 1 * (2 / ‖stdAddChar a - 1‖) :=
            mul_le_mul hχa this (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  have hreindex : ∑ a : ZMod q, (if a = 0 then (0:ℝ) else 2 / ‖stdAddChar a - 1‖) =
      ∑ k ∈ Ioo 0 q, 2 / ‖stdAddChar (k : ZMod q) - 1‖ := by
    have e1 : ∑ a : ZMod q, (if a = 0 then (0:ℝ) else 2 / ‖stdAddChar a - 1‖) =
        ∑ k ∈ range q, (if (k : ZMod q) = 0 then (0:ℝ) else 2 / ‖stdAddChar (k : ZMod q) - 1‖) := by
      apply Finset.sum_nbij' (fun a : ZMod q => a.val) (fun k : ℕ => (k : ZMod q))
      · intro a _; simp [ZMod.val_lt]
      · intro k _; simp
      · intro a _; simp
      · intro k hk; simp only [mem_coe, mem_range] at hk; exact ZMod.val_cast_of_lt hk
      · intro a _; simp
    rw [e1, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [Nat.cast_zero, ite_true, zero_add]
    have e2 : Ico (0 + 1) q = Ioo 0 q := by ext k; simp only [mem_Ico, mem_Ioo]; omega
    rw [e2]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Ioo] at hk
    have : (k : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun h => by have := Nat.le_of_dvd hk.1 h; omega
    simp [this]
  have hmain : ‖∑ n ∈ Ico M (M + N), ψ n‖ * Real.sqrt q ≤ q * (1 + Real.log q) := by
    rw [← hτn, ← norm_mul, hsum]
    calc _ ≤ ∑ a : ZMod q, ‖χ a * ∑ n ∈ Ico M (M + N), stdAddChar a ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ a : ZMod q, (if a = 0 then (0:ℝ) else 2 / ‖stdAddChar a - 1‖) := sum_le_sum fun a _ => hterm a
      _ = _ := hreindex
      _ ≤ _ := sum_inv_norm_le q
  have hsqpos : 0 < Real.sqrt q := Real.sqrt_pos.2 hqR
  have h3 := (le_div_iff₀ hsqpos).2 hmain
  rwa [mul_div_right_comm, Real.div_sqrt] at h3

end PolyaVinogradov


namespace PolyaVinogradov
open DirichletCharacter ZMod Finset

theorem Ico_one_eq (Y : ℕ) : Ico 1 (1 + Y) = Ioc 0 Y := by ext k; simp only [mem_Ico, mem_Ioc]; omega

/-- PV for initial segments: `‖Σ_{0<k≤Y} ψ(k)‖ ≤ √q (1 + log q)`. -/
theorem pv_Ioc {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive) (hq : 1 < q) (Y : ℕ) :
    ‖∑ k ∈ Ioc 0 Y, ψ k‖ ≤ Real.sqrt q * (1 + Real.log q) := by
  rw [← Ico_one_eq]; exact polya_vinogradov hψ hq 1 Y

/-- **Pólya–Vinogradov for non-principal characters (imprimitive allowed).** For `χ ≠ 1` mod `n`,
`‖Σ_{0<m≤y} χ(m)‖ ≤ d(n) · √n (1 + log n)`, where `d(n)` is the number of divisors. -/
theorem pv_nonprincipal {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (hχ : χ ≠ 1) (y : ℕ) :
    ‖∑ m ∈ Ioc 0 y, χ m‖ ≤ (n.divisors.card : ℝ) * (Real.sqrt n * (1 + Real.log n)) := by
  classical
  set f := χ.conductor
  haveI : NeZero f := ⟨conductor_ne_zero χ⟩
  set ψ := χ.primitiveCharacter
  have hψ : ψ.IsPrimitive := primitiveCharacter_isPrimitive χ
  have hf1 : 1 < f := by
    have h0 : f ≠ 0 := conductor_ne_zero χ
    have h1 : f ≠ 1 := fun h => hχ (eq_one_iff_conductor_eq_one.2 h)
    omega
  have hfn : f ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) (conductor_dvd_level χ)
  have hn0 : n ≠ 0 := NeZero.ne n
  -- A: χ(m) = [gcd(m,n)=1] ψ(m)
  have hA : ∀ m : ℕ, χ m = (if Nat.Coprime m n then 1 else 0) * ψ m := by
    intro m
    split_ifs with hc
    · rw [one_mul]
      have hc' : IsCoprime (m : ℤ) n := Nat.isCoprime_iff_coprime.2 hc
      have := primitiveCharacter_apply_of_isCoprime χ hc'
      simpa using this.symm
    · rw [zero_mul]; apply MulChar.map_nonunit
      rwa [ZMod.isUnit_iff_coprime]
  -- B: [gcd(m,n)=1] = Σ_{d ∣ n, d ∣ m} μ(d)
  have hB : ∀ m : ℕ, (if Nat.Coprime m n then (1:ℂ) else 0) =
      ∑ d ∈ n.divisors.filter (· ∣ m), (ArithmeticFunction.moebius d : ℂ) := by
    intro m
    have hg : Nat.gcd m n ≠ 0 := Nat.gcd_ne_zero_right hn0
    have hset : n.divisors.filter (· ∣ m) = (Nat.gcd m n).divisors := by
      ext d; simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]; tauto
    rw [hset]
    have h := congrArg (fun g : ArithmeticFunction ℤ ↦ g (Nat.gcd m n)) ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    rw [← Int.cast_sum, h]
    simp [Nat.Coprime]
  -- C: reorganise
  have hC : ∑ m ∈ Ioc 0 y, χ m =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) * (ψ d * ∑ k ∈ Ioc 0 (y / d), ψ k) := by
    simp_rw [hA, hB, sum_filter, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    simp_rw [ite_mul, zero_mul]
    rw [← sum_filter, mul_sum, mul_sum]
    symm
    apply sum_nbij' (fun k => d * k) (fun m => m / d)
    · intro k hk; simp only [mem_coe, mem_filter, mem_Ioc] at hk ⊢
      refine ⟨⟨Nat.mul_pos hd0 hk.1, ?_⟩, dvd_mul_right _ _⟩
      have := (Nat.le_div_iff_mul_le hd0).1 hk.2; linarith [mul_comm k d]
    · intro m hm; simp only [mem_coe, mem_filter, mem_Ioc] at hm ⊢
      obtain ⟨⟨h0, h1⟩, ⟨k, rfl⟩⟩ := hm
      rw [Nat.mul_div_cancel_left _ hd0]
      refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h0), ?_⟩
      rw [Nat.le_div_iff_mul_le hd0, mul_comm]; exact h1
    · intro k _; simp [Nat.mul_div_cancel_left _ hd0]
    · intro m hm; simp only [mem_coe, mem_filter] at hm; exact Nat.mul_div_cancel' hm.2
    · intro k _; push_cast; rw [map_mul]
  rw [hC]
  have hbound : ∀ d ∈ n.divisors, ‖(ArithmeticFunction.moebius d : ℂ) * (ψ d * ∑ k ∈ Ioc 0 (y / d), ψ k)‖ ≤
      Real.sqrt n * (1 + Real.log n) := by
    intro d _
    have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hψd : ‖ψ d‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
    have hpv := pv_Ioc hψ hf1 (y / d)
    have hmono : Real.sqrt f * (1 + Real.log f) ≤ Real.sqrt n * (1 + Real.log n) := by
      have hfR : (1:ℝ) < f := by exact_mod_cast hf1
      have hfnR : (f:ℝ) ≤ n := by exact_mod_cast hfn
      apply mul_le_mul (Real.sqrt_le_sqrt hfnR)
        (by linarith [Real.log_le_log (by linarith) hfnR]) (by linarith [Real.log_nonneg hfR.le])
        (Real.sqrt_nonneg _)
    rw [norm_mul, norm_mul]
    calc _ ≤ 1 * (1 * (Real.sqrt f * (1 + Real.log f))) := by
          gcongr
      _ ≤ _ := by linarith
  calc _ ≤ ∑ d ∈ n.divisors, ‖(ArithmeticFunction.moebius d : ℂ) * (ψ d * ∑ k ∈ Ioc 0 (y / d), ψ k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ n.divisors, Real.sqrt n * (1 + Real.log n) := sum_le_sum hbound
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end PolyaVinogradov


/-! # Non-principality of `D ↦ J(D | n)` for odd non-square `n` -/

namespace Kron

/-- For odd `n` that is not a perfect square, some integer `D` has `J(D | n) = -1`. -/
theorem exists_jacobiSym_eq_neg_one {n : ℕ} (hn : Odd n) (hsq : ¬ IsSquare n) :
    ∃ D : ℤ, jacobiSym D n = -1 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hsq ⟨0, rfl⟩
  obtain ⟨p, hp, hodd⟩ : ∃ p, p.Prime ∧ ¬ Even (n.factorization p) := by
    by_contra h; push_neg at h; exact hsq (Nat.isSquare_iff_even_factorization.2 h)
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ n := by
    by_contra h; rw [Nat.factorization_eq_zero_of_not_dvd h] at hodd; exact hodd ⟨0, rfl⟩
  have hp2 : p ≠ 2 := by
    rintro rfl; exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 hpdvd)
  -- a nonresidue mod p
  obtain ⟨r, hr⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  set v := n.factorization p
  set m := n / p ^ v
  have hnm : p ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hn0
  have hm0 : m ≠ 0 := by rintro h; rw [h, mul_zero] at hnm; exact hn0 hnm.symm
  -- CRT: k ≡ r (mod p), k ≡ 1 (mod m)
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, k ≡ r.val [MOD p] ∧ k ≡ 1 [MOD m] :=
    ⟨Nat.chineseRemainder hcop r.val 1, (Nat.chineseRemainder hcop r.val 1).2.1,
      (Nat.chineseRemainder hcop r.val 1).2.2⟩
  refine ⟨k, ?_⟩
  haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero m := ⟨hm0⟩
  rw [← hnm, jacobiSym.mul_right, jacobiSym.pow_right]
  have h1 : jacobiSym k p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    have : ((k : ℤ) : ZMod p) = r := by
      have := (ZMod.natCast_eq_natCast_iff k r.val p).2 hk1
      push_cast; rw [this, ZMod.natCast_zmod_val]
    rwa [this]
  have h2 : jacobiSym k m = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1), jacobiSym.one_left]
    have : k % m = 1 % m := hk2
    exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) this
  rw [h1, h2, mul_one]
  exact (Nat.not_even_iff_odd.1 hodd).neg_one_pow

end Kron


open Finset

namespace GSLemma

/-! Copied from `lib/pnt/SquarefreeCount.lean` (to avoid building PNT+): `μ² = Σ_{d²∣n} μ(d)`. -/
theorem dvd_of_sq_dvd_sq_mul {a b d : ℕ} (ha : Squarefree a) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : d ^ 2 ∣ b ^ 2 * a) : d ∣ b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  rw [← Nat.factorization_le_iff_dvd hd hb, Finsupp.le_def]
  have h2 := Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd)
    (mul_ne_zero (pow_ne_zero 2 hb) ha0)).2 h)
  intro p
  have hp := h2 p
  rw [Nat.factorization_pow, Nat.factorization_mul (pow_ne_zero 2 hb) ha0, Nat.factorization_pow]
    at hp
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at hp
  have h1 := ha.natFactorization_le_one p
  omega

/-- `Σ_{d² ∣ n} μ(d)` is `1` if `n ≥ 1` is squarefree and `0` otherwise. -/
theorem sum_sq_dvd_moebius {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ (Finset.Ioc 0 n).filter (fun d ↦ d ^ 2 ∣ n), (ArithmeticFunction.moebius d : ℝ) =
      if Squarefree n then 1 else 0 := by
  obtain ⟨a, b, ha0, hb0, rfl, ha⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hset : (Finset.Ioc 0 (b ^ 2 * a)).filter (fun d ↦ d ^ 2 ∣ b ^ 2 * a) = b.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd0, -⟩, hd⟩
      exact ⟨dvd_of_sq_dvd_sq_mul ha hb0.ne' hd0.ne' hd, hb0.ne'⟩
    · rintro ⟨hdb, -⟩
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdb hb0
      have hsq : d ^ 2 ∣ b ^ 2 * a := (pow_dvd_pow_of_dvd hdb 2).mul_right a
      refine ⟨⟨hd0, ?_⟩, hsq⟩
      calc d ≤ d ^ 2 := by nlinarith
        _ ≤ b ^ 2 * a := Nat.le_of_dvd (by positivity) hsq
  rw [hset]
  have hμ : ∑ d ∈ b.divisors, (ArithmeticFunction.moebius d : ℝ) = if b = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ ↦ f b) ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    rw [← Int.cast_sum, h]
    split_ifs <;> simp
  rw [hμ]
  have hiff : b = 1 ↔ Squarefree (b ^ 2 * a) := by
    constructor
    · rintro rfl
      simpa using ha
    · intro hsq
      exact Nat.isUnit_iff.1 (hsq b ⟨a, by ring⟩)
  by_cases hb1 : b = 1
  · rw [ite_eq_left hb1, ite_eq_left (hiff.1 hb1)]
  · rw [ite_eq_right hb1, ite_eq_right (fun h ↦ hb1 (hiff.2 h))]

/-- `Σ_{L < l ≤ L+K} 1/l² ≤ 1/L − 1/(L+K)` for `L ≥ 1`. -/
theorem tail_inv_sq (L : ℕ) (hL : 1 ≤ L) (K : ℕ) :
    ∑ l ∈ Ioc L (L + K), ((l:ℝ) ^ 2)⁻¹ ≤ (L:ℝ)⁻¹ - ((L + K : ℕ):ℝ)⁻¹ := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show L + (K + 1) = (L + K) + 1 by ring, Finset.sum_Ioc_succ_top (by omega)]
    have hpos : (0:ℝ) < (L + K : ℕ) := by exact_mod_cast (show 0 < L + K by omega)
    have h1 : (((L + K + 1 : ℕ):ℝ) ^ 2)⁻¹ ≤ ((L + K : ℕ):ℝ)⁻¹ - ((L + K + 1 : ℕ):ℝ)⁻¹ := by
      push_cast
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      push_cast at hpos
      rw [inv_sub_inv hpos.ne' (by positivity)]
      field_simp
      nlinarith
    linarith

/-- **The squarefree sieve (core of Granville–Soundararajan, Lemma 4.1).**
Let `ψ : ℕ → ℂ` be completely multiplicative with `‖ψ‖ ≤ 1` and every initial sum `‖Σ_{m ≤ y} ψ(m)‖ ≤ B`.
Then for every `L ≥ 1`, `‖Σ_{d ≤ N, d squarefree} ψ(d)‖ ≤ L·B + N/L`. -/
theorem sqf_sum_le (ψ : ℕ → ℂ) (hmul : ∀ a b, ψ (a * b) = ψ a * ψ b) (hle : ∀ m, ‖ψ m‖ ≤ 1)
    (B : ℝ) (hB : ∀ y, ‖∑ m ∈ Ioc 0 y, ψ m‖ ≤ B) (N L : ℕ) (hL : 1 ≤ L) :
    ‖∑ d ∈ (Ioc 0 N).filter Squarefree, ψ d‖ ≤ L * B + N / L := by
  classical
  -- `Σ_{d≤N} sqf(d) ψ(d) = Σ_{l≤N} μ(l) ψ(l)² Σ_{m ≤ N/l²} ψ(m)`
  have hid : ∑ d ∈ (Ioc 0 N).filter Squarefree, ψ d =
      ∑ l ∈ Ioc 0 N, (ArithmeticFunction.moebius l : ℂ) * ψ l ^ 2 * ∑ m ∈ Ioc 0 (N / l ^ 2), ψ m := by
    have h1 : ∀ d ∈ Ioc 0 N, (if Squarefree d then ψ d else 0) =
        ∑ l ∈ Ioc 0 N, if l ^ 2 ∣ d then (ArithmeticFunction.moebius l : ℂ) * ψ d else 0 := by
      intro d hd
      rw [mem_Ioc] at hd
      have hs := sum_sq_dvd_moebius hd.1
      have hs' : ∑ l ∈ (Ioc 0 d).filter (fun l ↦ l ^ 2 ∣ d), (ArithmeticFunction.moebius l : ℂ) =
          if Squarefree d then 1 else 0 := by exact_mod_cast hs
      have hsub : (Ioc 0 d).filter (fun l ↦ l ^ 2 ∣ d) = (Ioc 0 N).filter (fun l ↦ l ^ 2 ∣ d) := by
        ext l; simp only [mem_filter, mem_Ioc]; constructor
        · rintro ⟨⟨h0, h1⟩, h2⟩; exact ⟨⟨h0, h1.trans hd.2⟩, h2⟩
        · rintro ⟨⟨h0, -⟩, h2⟩
          exact ⟨⟨h0, (show l ≤ l ^ 2 by nlinarith).trans (Nat.le_of_dvd hd.1 h2)⟩, h2⟩
      rw [← sum_filter, ← sum_mul, ← hsub, hs']
      split_ifs <;> simp
    rw [sum_filter, sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun l hl => ?_
    rw [mem_Ioc] at hl
    rw [← sum_filter, mul_sum]
    -- reindex `d = l² m`
    have hl2 : 0 < l ^ 2 := pow_pos hl.1 2
    symm
    apply sum_nbij' (fun m => l ^ 2 * m) (fun d => d / l ^ 2)
    · intro m hm; simp only [mem_coe, mem_filter, mem_Ioc] at hm ⊢
      refine ⟨⟨Nat.mul_pos hl2 hm.1, ?_⟩, dvd_mul_right _ _⟩
      have := (Nat.le_div_iff_mul_le hl2).1 hm.2; linarith [mul_comm m (l^2)]
    · intro d hd; simp only [mem_coe, mem_filter, mem_Ioc] at hd ⊢
      obtain ⟨⟨h0, h1⟩, ⟨k, rfl⟩⟩ := hd
      rw [Nat.mul_div_cancel_left _ hl2]
      refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h0), ?_⟩
      rw [Nat.le_div_iff_mul_le hl2, mul_comm]; exact h1
    · intro m _; simp [Nat.mul_div_cancel_left _ hl2]
    · intro d hd; simp only [mem_coe, mem_filter] at hd
      exact Nat.mul_div_cancel' hd.2
    · intro m _; rw [hmul, show l ^ 2 = l * l by ring, hmul]; ring
  rw [hid]
  -- split at `L`
  have hterm : ∀ l ∈ Ioc 0 N, ‖(ArithmeticFunction.moebius l : ℂ) * ψ l ^ 2 *
      ∑ m ∈ Ioc 0 (N / l ^ 2), ψ m‖ ≤ if l ≤ L then B else (N:ℝ) / l ^ 2 := by
    intro l hl
    have hμ : ‖(ArithmeticFunction.moebius l : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hψ2 : ‖ψ l ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hle l)
    have hc : ‖(ArithmeticFunction.moebius l : ℂ) * ψ l ^ 2‖ ≤ 1 := by
      rw [norm_mul]; exact mul_le_one₀ hμ (norm_nonneg _) hψ2
    rw [norm_mul]
    have hinner_triv : ‖∑ m ∈ Ioc 0 (N / l ^ 2), ψ m‖ ≤ (N:ℝ) / l ^ 2 := by
      calc _ ≤ ∑ m ∈ Ioc 0 (N / l ^ 2), ‖ψ m‖ := norm_sum_le _ _
        _ ≤ ∑ m ∈ Ioc 0 (N / l ^ 2), (1:ℝ) := sum_le_sum fun m _ => hle m
        _ = ((N / l ^ 2 : ℕ) : ℝ) := by simp
        _ ≤ (N:ℝ) / l ^ 2 := by exact_mod_cast Nat.cast_div_le
    split_ifs
    · calc _ ≤ 1 * B := mul_le_mul hc (hB _) (norm_nonneg _) zero_le_one
        _ = B := one_mul _
    · calc _ ≤ 1 * ((N:ℝ) / l ^ 2) := mul_le_mul hc hinner_triv (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  calc _ ≤ ∑ l ∈ Ioc 0 N, ‖(ArithmeticFunction.moebius l : ℂ) * ψ l ^ 2 *
        ∑ m ∈ Ioc 0 (N / l ^ 2), ψ m‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ Ioc 0 N, (if l ≤ L then B else (N:ℝ) / l ^ 2) := sum_le_sum hterm
    _ ≤ ∑ l ∈ Ioc 0 L, B + ∑ l ∈ Ioc L (L + N), (N:ℝ) / l ^ 2 := by
        rw [← sum_filter_add_sum_filter_not (Ioc 0 N) (fun l => l ≤ L)]
        apply add_le_add
        · rw [sum_ite_of_true (fun l hl => (mem_filter.1 hl).2)]
          apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => hB0)
          intro l hl; simp only [mem_filter, mem_Ioc] at hl ⊢; omega
        · rw [sum_ite_of_false (fun l hl => (mem_filter.1 hl).2)]
          apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
          intro l hl; simp only [mem_filter, mem_Ioc] at hl ⊢; omega
    _ ≤ L * B + N / L := by
        rw [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
        have ht := tail_inv_sq L hL N
        have : ∑ l ∈ Ioc L (L + N), (N:ℝ) / l ^ 2 = N * ∑ l ∈ Ioc L (L + N), ((l:ℝ) ^ 2)⁻¹ := by
          rw [mul_sum]; rfl
        rw [this]
        have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
        have : (N:ℝ) * ∑ l ∈ Ioc L (L + N), ((l:ℝ) ^ 2)⁻¹ ≤ N * (L:ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ hN
          have : (0:ℝ) ≤ ((L + N : ℕ):ℝ)⁻¹ := by positivity
          linarith
        rw [div_eq_mul_inv]; linarith


/-- Optimised: `‖Σ_{d ≤ N squarefree} ψ(d)‖ ≤ 2√(N B) + B` for `B > 0`. With `B = √n (1 + log n)` (Pólya–Vinogradov,
`PV.lean`) this is Granville–Soundararajan's `≪ x^{1/2} n^{1/4} (log n)^{1/2}`. -/
theorem sqf_sum_le_sqrt (ψ : ℕ → ℂ) (hmul : ∀ a b, ψ (a * b) = ψ a * ψ b) (hle : ∀ m, ‖ψ m‖ ≤ 1)
    (B : ℝ) (hBpos : 0 < B) (hB : ∀ y, ‖∑ m ∈ Ioc 0 y, ψ m‖ ≤ B) (N : ℕ) :
    ‖∑ d ∈ (Ioc 0 N).filter Squarefree, ψ d‖ ≤ 2 * Real.sqrt (N * B) + B := by
  set r := Real.sqrt (N / B)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set L := ⌊r⌋₊ + 1
  have hL : 1 ≤ L := by omega
  have h := sqf_sum_le ψ hmul hle B hB N L hL
  have hLr : (L:ℝ) ≤ r + 1 := by
    simp only [L]; push_cast; linarith [Nat.floor_le hr0]
  have hrL : r < L := by simp only [L]; push_cast; exact Nat.lt_floor_add_one r
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hrB : r * B = Real.sqrt (N * B) := by
    rw [show (N:ℝ) * B = (N / B) * (B * B) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_mul_self hBpos.le]
  have h1 : (L:ℝ) * B ≤ Real.sqrt (N * B) + B := by nlinarith
  have h2 : (N:ℝ) / L ≤ Real.sqrt (N * B) := by
    rcases eq_or_lt_of_le hN with h0 | h0
    · rw [← h0]; simp
    have hrpos : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hLpos : (0:ℝ) < L := by linarith
    rw [div_le_iff₀ hLpos]
    have hsq : r * r = N / B := Real.mul_self_sqrt (by positivity)
    have : (N:ℝ) = r * r * B := by rw [hsq]; field_simp
    calc (N:ℝ) = r * B * r := by rw [this]; ring
      _ ≤ r * B * L := by apply mul_le_mul_of_nonneg_left hrL.le; positivity
      _ = _ := by rw [hrB]
  linarith

end GSLemma


namespace JChar
open DirichletCharacter ZMod Finset

/-- `a ↦ J(a.val | n)` as a Dirichlet character mod `n` (`1 < n`). -/
noncomputable def jchar (n : ℕ) [Fact (1 < n)] : DirichletCharacter ℂ n where
  toFun a := (jacobiSym (a.val : ℤ) n : ℂ)
  map_one' := by simp [ZMod.val_one, jacobiSym.one_left]
  map_mul' a b := by
    show (jacobiSym ((a*b).val : ℤ) n : ℂ) = (jacobiSym (a.val : ℤ) n : ℂ) * (jacobiSym (b.val : ℤ) n : ℂ)
    rw [ZMod.val_mul, ← Int.cast_mul, ← jacobiSym.mul_left]
    congr 1
    apply jacobiSym.mod_left'
    push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)
  map_nonunit' a ha := by
    show (jacobiSym (a.val : ℤ) n : ℂ) = 0
    have hn : NeZero n := ⟨by have := (Fact.out : 1 < n); omega⟩
    have : ¬ Nat.Coprime a.val n := by
      intro h; apply ha; rw [← ZMod.natCast_zmod_val a]; exact (ZMod.isUnit_iff_coprime _ _).2 h
    have h0 : jacobiSym (a.val : ℤ) n = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]; exact this
    rw [h0, Int.cast_zero]

theorem jchar_int (n : ℕ) [Fact (1 < n)] (D : ℤ) : jchar n (D : ZMod n) = (jacobiSym D n : ℂ) := by
  show (jacobiSym (((D : ZMod n)).val : ℤ) n : ℂ) = _
  congr 1
  apply jacobiSym.mod_left'
  rw [ZMod.val_intCast]; exact Int.emod_emod_of_dvd _ (dvd_refl _)

theorem jchar_nat (n : ℕ) [Fact (1 < n)] (m : ℕ) : jchar n (m : ZMod n) = (jacobiSym m n : ℂ) := by
  have := jchar_int n m; simpa using this

/-- The ℂ-valued `χ₄`. -/
noncomputable def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem chi4_nat (m : ℕ) : chi4 (m : ZMod 4) = ((ZMod.χ₄ (m : ZMod 4) : ℤ) : ℂ) := rfl

/-- The character `D ↦ J(D|n) · c(D)` mod `4n`, with `c ∈ {1, χ₄}` mod 4. -/
noncomputable def psiChar (n : ℕ) [Fact (1 < n)] (c : DirichletCharacter ℂ 4) : DirichletCharacter ℂ (4 * n) :=
  changeLevel (dvd_mul_left n 4) (jchar n) * changeLevel (dvd_mul_right 4 n) c

theorem psiChar_nat (n : ℕ) [Fact (1 < n)] (c : DirichletCharacter ℂ 4) (m : ℕ) :
    psiChar n c (m : ZMod (4 * n)) = jchar n (m : ZMod n) * c (m : ZMod 4) := by
  have hn : NeZero n := ⟨by have := (Fact.out : 1 < n); omega⟩
  by_cases hc : Nat.Coprime m (4 * n)
  · have hc' : IsCoprime (m : ℤ) (4 * n : ℕ) := Nat.isCoprime_iff_coprime.2 hc
    simp only [psiChar, MulChar.mul_apply]
    have e1 := changeLevel_eq_cast_of_dvd' (jchar n) (dvd_mul_left n 4) hc'
    have e2 := changeLevel_eq_cast_of_dvd' c (dvd_mul_right 4 n) hc'
    push_cast at e1 e2; rw [e1, e2]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    rcases Nat.Coprime.coprime_mul_left_right |> fun _ => (Nat.coprime_mul_iff_right.not.1 hc) with h
    by_cases h4 : Nat.Coprime m 4
    · have hn' : ¬ Nat.Coprime m n := fun h' => hc (Nat.Coprime.mul_right h4 h')
      rw [MulChar.map_nonunit (jchar n) (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    · rw [MulChar.map_nonunit c (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]

/-- For odd non-square `n > 1`, and `c` with `c(1) = 1`, the character `psiChar n c` is non-principal. -/
theorem psiChar_ne_one {n : ℕ} [Fact (1 < n)] (hn : Odd n) (hsq : ¬ IsSquare n) (c : DirichletCharacter ℂ 4) :
    psiChar n c ≠ 1 := by
  intro h1
  obtain ⟨D, hD⟩ := Kron.exists_jacobiSym_eq_neg_one hn hsq
  -- choose m ≡ D (mod n), m ≡ 1 (mod 4)
  have hcop : Nat.Coprime n 4 := by
    rw [Nat.coprime_comm, show (4:ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.coprime_two_left).2 hn)
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℕ, m ≡ (D % n).toNat [MOD n] ∧ m ≡ 1 [MOD 4] :=
    ⟨_, (Nat.chineseRemainder hcop (D % n).toNat 1).2.1, (Nat.chineseRemainder hcop (D % n).toNat 1).2.2⟩
  have hnpos : (0:ℤ) < n := by have := (Fact.out : 1 < n); omega
  have hJ : jacobiSym m n = -1 := by
    rw [← hD]; apply jacobiSym.mod_left'
    have h1 : (m : ℤ) % n = ((D % n).toNat : ℤ) % n := by exact_mod_cast hm1
    rw [h1, Int.toNat_of_nonneg (Int.emod_nonneg _ hnpos.ne'), Int.emod_emod_of_dvd _ (dvd_refl _)]
  have hm4 : (m : ZMod 4) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff m 1 4).2 hm2; simpa using this
  have hv := psiChar_nat n c m
  rw [h1, jchar_nat, hJ, hm4, MulChar.map_one] at hv
  -- (1 : char) m is 0 or 1
  by_cases hu : IsUnit (m : ZMod (4 * n))
  · rw [MulChar.one_apply hu] at hv; norm_num at hv
  · rw [MulChar.map_nonunit _ hu] at hv; norm_num at hv

end JChar

namespace GSAssemble
open DirichletCharacter ZMod Finset JChar

variable {n : ℕ} [Fact (1 < n)]

/-- `B = d(4n) √(4n) (1 + log 4n)`. -/
noncomputable def Bn (n : ℕ) : ℝ := ((4 * n).divisors.card : ℝ) * (Real.sqrt (4 * n : ℕ) * (1 + Real.log (4 * n : ℕ)))

theorem Bn_pos : 0 < Bn n := by
  have h1 : 1 < n := Fact.out
  have hc : 0 < (4 * n).divisors.card := Finset.card_pos.2 ⟨1, by simp; omega⟩
  have : (1:ℝ) ≤ ((4 * n : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 4 * n by omega)
  unfold Bn
  have := Real.log_nonneg this
  have : 0 < Real.sqrt ((4 * n : ℕ) : ℝ) := Real.sqrt_pos.2 (by linarith)
  positivity

/-- GS sieve for `ψ = psiChar n c` (odd non-square `n`). -/
theorem sqf_psi_le (hn : Odd n) (hsq : ¬ IsSquare n) (c : DirichletCharacter ℂ 4) (x : ℕ) :
    ‖∑ d ∈ (Ioc 0 x).filter Squarefree, psiChar n c (d : ZMod (4 * n))‖ ≤
      2 * Real.sqrt (x * Bn n) + Bn n := by
  haveI : NeZero (4 * n) := ⟨by have := (Fact.out : 1 < n); omega⟩
  apply GSLemma.sqf_sum_le_sqrt (fun m => psiChar n c (m : ZMod (4 * n)))
  · intro a b; push_cast; exact map_mul _ _ _
  · intro m; exact DirichletCharacter.norm_le_one _ _
  · exact Bn_pos
  · intro y; exact PolyaVinogradov.pv_nonprincipal (psiChar_ne_one hn hsq c) y

theorem unit4_iff (m : ℕ) : IsUnit (m : ZMod 4) ↔ m % 2 = 1 := by
  rw [ZMod.isUnit_iff_coprime, show (4:ℕ) = 2 ^ 2 by norm_num, Nat.coprime_pow_right_iff (by norm_num),
    Nat.coprime_two_right, Nat.odd_iff]

theorem one4_nat (m : ℕ) : (1 : DirichletCharacter ℂ 4) (m : ZMod 4) = if m % 2 = 1 then 1 else 0 := by
  by_cases h : m % 2 = 1
  · rw [if_pos h, MulChar.one_apply ((unit4_iff m).2 h)]
  · rw [if_neg h, MulChar.map_nonunit _ (fun hu => h ((unit4_iff m).1 hu))]

theorem chi4_val (m : ℕ) : chi4 (m : ZMod 4) =
    if m % 2 = 0 then 0 else if m % 4 = 1 then 1 else -1 := by
  rw [chi4_nat, ZMod.χ₄_nat_eq_if_mod_four]; split_ifs <;> simp

/-- **Class sums.** For odd non-square `n > 1` and `r ∈ {1, 3}`:
`‖Σ_{d ≤ x squarefree, d ≡ r (4)} J(d|n)‖ ≤ 2√(x B) + B`, with `B = d(4n)√(4n)(1 + log 4n)`. -/
theorem class_sum_le (hn : Odd n) (hsq : ¬ IsSquare n) (r : ℕ) (hr : r = 1 ∨ r = 3) (x : ℕ) :
    ‖∑ d ∈ (Ioc 0 x).filter Squarefree, (if d % 4 = r then (jacobiSym d n : ℂ) else 0)‖ ≤
      2 * Real.sqrt (x * Bn n) + Bn n := by
  set s : ℂ := if r = 1 then 1 else -1
  have hs : ‖s‖ = 1 := by simp only [s]; split_ifs <;> simp
  have hid : ∀ d : ℕ, (if d % 4 = r then (jacobiSym d n : ℂ) else 0) =
      (psiChar n 1 (d : ZMod (4 * n)) + s * psiChar n chi4 (d : ZMod (4 * n))) / 2 := by
    intro d
    rw [psiChar_nat, psiChar_nat, jchar_nat, one4_nat, chi4_val]
    have h2 : d % 2 = d % 4 % 2 := (Nat.mod_mod_of_dvd d (by norm_num)).symm
    have h4 : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
    simp only [s]
    rcases hr with rfl | rfl <;> interval_cases h : d % 4 <;> simp_all <;> ring
  simp_rw [hid]
  rw [← sum_div, sum_add_distrib, ← mul_sum, norm_div]
  have h1 := sqf_psi_le hn hsq 1 x
  have h2 := sqf_psi_le hn hsq chi4 x
  calc _ ≤ (‖∑ d ∈ (Ioc 0 x).filter Squarefree, psiChar n 1 (d : ZMod (4 * n))‖ +
        ‖s‖ * ‖∑ d ∈ (Ioc 0 x).filter Squarefree, psiChar n chi4 (d : ZMod (4 * n))‖) / ‖(2:ℂ)‖ := by
        gcongr; rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ _ := by rw [hs, one_mul, Complex.norm_two]; linarith

/-- **All odd squarefree `d`**: `‖Σ_{d ≤ x sqf, d odd} J(d|n)‖ ≤ 2√(xB) + B`. -/
theorem odd_sum_le (hn : Odd n) (hsq : ¬ IsSquare n) (x : ℕ) :
    ‖∑ d ∈ (Ioc 0 x).filter Squarefree, (if d % 2 = 1 then (jacobiSym d n : ℂ) else 0)‖ ≤
      2 * Real.sqrt (x * Bn n) + Bn n := by
  have hid : ∀ d : ℕ, (if d % 2 = 1 then (jacobiSym d n : ℂ) else 0) = psiChar n 1 (d : ZMod (4 * n)) := by
    intro d; rw [psiChar_nat, jchar_nat, one4_nat]; split_ifs <;> simp
  simp_rw [hid]; exact sqf_psi_le hn hsq 1 x

end GSAssemble

#print axioms GSAssemble.class_sum_le
#print axioms GSAssemble.odd_sum_le
