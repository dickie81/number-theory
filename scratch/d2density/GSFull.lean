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

namespace GSFund
open Finset GSAssemble JChar

/-- Positive fundamental discriminants: `d ≡ 1 (4)` squarefree, or `d = 4m` with `m ≡ 2, 3 (4)` squarefree. -/
def fundPos (d : ℕ) : Prop :=
  (Squarefree d ∧ d % 4 = 1) ∨ (4 ∣ d ∧ Squarefree (d / 4) ∧ ((d / 4) % 4 = 2 ∨ (d / 4) % 4 = 3))

/-- `|D|` for negative fundamental discriminants `D = -d`: `d ≡ 3 (4)` squarefree, or `d = 4m`, `m ≡ 1, 2 (4)` squarefree. -/
def fundNeg (d : ℕ) : Prop :=
  (Squarefree d ∧ d % 4 = 3) ∨ (4 ∣ d ∧ Squarefree (d / 4) ∧ ((d / 4) % 4 = 1 ∨ (d / 4) % 4 = 2))

instance : DecidablePred fundPos := fun d => by unfold fundPos; infer_instance
instance : DecidablePred fundNeg := fun d => by unfold fundNeg; infer_instance

/-- Reindexing `d = k m`. -/
theorem sum_dvd_reindex (k : ℕ) (hk : 0 < k) (x : ℕ) (g : ℕ → ℂ) :
    ∑ d ∈ Ioc 0 x, (if k ∣ d then g (d / k) else 0) = ∑ m ∈ Ioc 0 (x / k), g m := by
  rw [← sum_filter]
  apply sum_nbij' (fun d => d / k) (fun m => k * m)
  · intro d hd; simp only [mem_coe, mem_filter, mem_Ioc] at hd ⊢
    obtain ⟨⟨h0, h1⟩, ⟨j, rfl⟩⟩ := hd
    rw [Nat.mul_div_cancel_left _ hk]
    refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h0), ?_⟩
    rw [Nat.le_div_iff_mul_le hk, mul_comm]; exact h1
  · intro m hm; simp only [mem_coe, mem_Ioc, mem_filter] at hm ⊢
    refine ⟨⟨Nat.mul_pos hk hm.1, ?_⟩, dvd_mul_right _ _⟩
    have := (Nat.le_div_iff_mul_le hk).1 hm.2; linarith [mul_comm m k]
  · intro d hd; simp only [mem_coe, mem_filter] at hd; exact Nat.mul_div_cancel' hd.2
  · intro m _; simp [Nat.mul_div_cancel_left _ hk]
  · intro d _; rfl

variable {n : ℕ} [Fact (1 < n)]

/-- `T(x) = 2√(xB) + B`. -/
noncomputable def T (n x : ℕ) : ℝ := 2 * Real.sqrt (x * Bn n) + Bn n

theorem T_mono {x y : ℕ} (h : y ≤ x) : T n y ≤ T n x := by
  unfold T
  have : (y:ℝ) * Bn n ≤ x * Bn n := mul_le_mul_of_nonneg_right (by exact_mod_cast h) (Bn_pos).le
  linarith [Real.sqrt_le_sqrt this]

theorem class_ite_le (hn : Odd n) (hsq : ¬ IsSquare n) (r : ℕ) (hr : r = 1 ∨ r = 3) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if Squarefree d ∧ d % 4 = r then (jacobiSym d n : ℂ) else 0)‖ ≤ T n x := by
  have := class_sum_le hn hsq r hr x
  rw [sum_filter] at this; simp_rw [ite_and]; exact this

theorem odd_ite_le (hn : Odd n) (hsq : ¬ IsSquare n) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if Squarefree d ∧ d % 2 = 1 then (jacobiSym d n : ℂ) else 0)‖ ≤ T n x := by
  have := odd_sum_le hn hsq x
  rw [sum_filter] at this; simp_rw [ite_and]; exact this

theorem norm_jac_le (a : ℤ) : ‖(jacobiSym a n : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy a n with h | h | h <;> simp [h]

/-- The `m ≡ 2 (4)` class: `‖Σ_{m ≤ y sqf, m ≡ 2 (4)} J(m|n)‖ ≤ T(y)`. -/
theorem two_class_le (hn : Odd n) (hsq : ¬ IsSquare n) (y : ℕ) :
    ‖∑ m ∈ Ioc 0 y, (if Squarefree m ∧ m % 4 = 2 then (jacobiSym m n : ℂ) else 0)‖ ≤ T n y := by
  have hpt : ∀ m : ℕ, (if Squarefree m ∧ m % 4 = 2 then (jacobiSym m n : ℂ) else 0) =
      if 2 ∣ m then (jacobiSym 2 n : ℂ) * (if Squarefree (m / 2) ∧ (m / 2) % 2 = 1 then (jacobiSym (m / 2 : ℕ) n : ℂ) else 0)
      else 0 := by
    intro m
    by_cases h2 : 2 ∣ m
    · obtain ⟨k, rfl⟩ := h2
      rw [if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ (by norm_num)]
      have hiff : (Squarefree (2 * k) ∧ (2 * k) % 4 = 2) ↔ (Squarefree k ∧ k % 2 = 1) := by
        rw [Nat.squarefree_mul_iff]
        constructor
        · rintro ⟨⟨hc, -, hk⟩, -⟩; refine ⟨hk, ?_⟩
          have := (Nat.coprime_two_left).1 hc; exact Nat.odd_iff.1 this
        · rintro ⟨hk, ho⟩
          exact ⟨⟨(Nat.coprime_two_left).2 (Nat.odd_iff.2 ho), Nat.squarefree_two, hk⟩, by omega⟩
      by_cases hc : Squarefree k ∧ k % 2 = 1
      · rw [if_pos (hiff.2 hc), if_pos hc]; push_cast; rw [jacobiSym.mul_left]; push_cast; ring
      · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, mul_zero]
    · rw [if_neg h2, if_neg]; rintro ⟨-, h⟩; exact h2 (by omega)
  simp_rw [hpt]
  rw [sum_dvd_reindex 2 (by norm_num) y (fun k => (jacobiSym 2 n : ℂ) * (if Squarefree k ∧ k % 2 = 1 then (jacobiSym (k : ℕ) n : ℂ) else 0)), ← mul_sum, norm_mul]
  calc _ ≤ 1 * T n (y / 2) := mul_le_mul (norm_jac_le 2) (odd_ite_le hn hsq _) (norm_nonneg _) zero_le_one
    _ ≤ T n y := by rw [one_mul]; exact T_mono (Nat.div_le_self _ _)

/-- The `4m` part, for classes `r` (where `r = 2` is handled by `two_class_le`). -/
theorem four_part_le (hn : Odd n) (hsq : ¬ IsSquare n) (r s : ℕ) (hr : r = 1 ∨ r = 3) (hs : s = 2) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if 4 ∣ d ∧ Squarefree (d / 4) ∧ ((d / 4) % 4 = r ∨ (d / 4) % 4 = s)
        then (jacobiSym d n : ℂ) else 0)‖ ≤ 2 * T n x := by
  have h4 : ∀ m : ℕ, jacobiSym ((4 * m : ℕ) : ℤ) n = jacobiSym m n := by
    intro m; push_cast; rw [jacobiSym.mul_left, jacobiSym.at_four hn, one_mul]
  have hpt : ∀ d : ℕ, (if 4 ∣ d ∧ Squarefree (d / 4) ∧ ((d / 4) % 4 = r ∨ (d / 4) % 4 = s)
      then (jacobiSym d n : ℂ) else 0) =
      if 4 ∣ d then ((if Squarefree (d / 4) ∧ (d / 4) % 4 = r then (jacobiSym (d / 4 : ℕ) n : ℂ) else 0) +
        (if Squarefree (d / 4) ∧ (d / 4) % 4 = s then (jacobiSym (d / 4 : ℕ) n : ℂ) else 0)) else 0 := by
    intro d
    by_cases h : 4 ∣ d
    · obtain ⟨m, rfl⟩ := h
      rw [if_pos (dvd_mul_right 4 m), Nat.mul_div_cancel_left _ (by norm_num), h4]
      have hrs : r ≠ s := by rcases hr with rfl | rfl <;> omega
      by_cases h1 : Squarefree m <;> by_cases h2 : m % 4 = r <;> by_cases h3 : m % 4 = s <;>
        simp_all
    · simp [h]
  simp_rw [hpt]
  rw [sum_dvd_reindex 4 (by norm_num) x (fun m => (if Squarefree m ∧ m % 4 = r then (jacobiSym (m : ℕ) n : ℂ) else 0) + (if Squarefree m ∧ m % 4 = s then (jacobiSym (m : ℕ) n : ℂ) else 0)), sum_add_distrib]
  have e1 := class_ite_le hn hsq r hr (x / 4)
  have e2 := two_class_le hn hsq (x / 4)
  rw [← hs] at e2
  have m1 := T_mono (n := n) (Nat.div_le_self x 4)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ T n (x / 4) + T n (x / 4) := add_le_add e1 e2
    _ ≤ 2 * T n x := by linarith

/-- **Granville–Soundararajan Lemma 4.1, positive discriminants, odd `n`.** For odd non-square `n > 1`,
`‖Σ_{0 < D ≤ x, D fundamental} χ_D(n)‖ ≤ 3 (2√(xB) + B)`, `B = d(4n)√(4n)(1 + log 4n)`; here `χ_D(n) = J(D|n)`. -/
theorem gs_pos (hn : Odd n) (hsq : ¬ IsSquare n) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundPos d then (jacobiSym d n : ℂ) else 0)‖ ≤ 3 * T n x := by
  have hpt : ∀ d : ℕ, (if fundPos d then (jacobiSym d n : ℂ) else 0) =
      (if Squarefree d ∧ d % 4 = 1 then (jacobiSym d n : ℂ) else 0) +
      (if 4 ∣ d ∧ Squarefree (d / 4) ∧ ((d / 4) % 4 = 3 ∨ (d / 4) % 4 = 2) then (jacobiSym d n : ℂ) else 0) := by
    intro d; unfold fundPos
    by_cases h1 : Squarefree d ∧ d % 4 = 1
    · have : ¬ (4 ∣ d) := by omega
      simp [h1, this]
    · by_cases h2 : 4 ∣ d ∧ Squarefree (d / 4) ∧ ((d / 4) % 4 = 3 ∨ (d / 4) % 4 = 2)
      · rw [if_pos (Or.inr ⟨h2.1, h2.2.1, h2.2.2.symm⟩), if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, if_neg, add_zero]
        rintro (h | ⟨a, b, c⟩); exact h1 h; exact h2 ⟨a, b, c.symm⟩
  simp_rw [hpt]; rw [sum_add_distrib]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ T n x + 2 * T n x := add_le_add (class_ite_le hn hsq 1 (Or.inl rfl) x)
        (four_part_le hn hsq 3 2 (Or.inr rfl) rfl x)
    _ = 3 * T n x := by ring

/-- **Granville–Soundararajan Lemma 4.1, negative discriminants, odd `n`.** Same bound for `D = -d`,
`χ_D(n) = J(-d|n)`. -/
theorem gs_neg (hn : Odd n) (hsq : ¬ IsSquare n) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundNeg d then (jacobiSym (-(d:ℤ)) n : ℂ) else 0)‖ ≤ 3 * T n x := by
  have hm : ∀ d : ℕ, (jacobiSym (-(d:ℤ)) n : ℂ) = (jacobiSym (-1) n : ℂ) * (jacobiSym d n : ℂ) := by
    intro d; rw [show (-(d:ℤ)) = -1 * d by ring, jacobiSym.mul_left]; push_cast; ring
  have hpt : ∀ d : ℕ, (if fundNeg d then (jacobiSym (-(d:ℤ)) n : ℂ) else 0) =
      (jacobiSym (-1) n : ℂ) * ((if Squarefree d ∧ d % 4 = 3 then (jacobiSym d n : ℂ) else 0) +
      (if 4 ∣ d ∧ Squarefree (d / 4) ∧ ((d / 4) % 4 = 1 ∨ (d / 4) % 4 = 2) then (jacobiSym d n : ℂ) else 0)) := by
    intro d; unfold fundNeg; rw [hm]
    by_cases h1 : Squarefree d ∧ d % 4 = 3
    · have : ¬ (4 ∣ d) := by omega
      simp [h1, this]
    · by_cases h2 : 4 ∣ d ∧ Squarefree (d / 4) ∧ ((d / 4) % 4 = 1 ∨ (d / 4) % 4 = 2)
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, if_neg, add_zero, mul_zero]
        rintro (h | h); exact h1 h; exact h2 h
  simp_rw [hpt]; rw [← mul_sum, sum_add_distrib, norm_mul]
  calc _ ≤ 1 * (T n x + 2 * T n x) := mul_le_mul (norm_jac_le (-1))
        ((norm_add_le _ _).trans (add_le_add (class_ite_le hn hsq 3 (Or.inr rfl) x)
          (four_part_le hn hsq 1 2 (Or.inl rfl) rfl x))) (norm_nonneg _) zero_le_one
    _ = 3 * T n x := by ring

end GSFund

namespace GSEven
open DirichletCharacter ZMod Finset JChar GSFund

/-- The Kronecker symbol `(D | n)` for `n > 0`: `χ₈(D)^{v₂(n)} · J(D | n / 2^{v₂(n)})`
(Kronecker's `(D|2) = χ₈(D)`, extended multiplicatively in `n`). -/
noncomputable def kron (D : ℤ) (n : ℕ) : ℂ :=
  ((χ₈ (D : ZMod 8) : ℤ) : ℂ) ^ (n.factorization 2) * (jacobiSym D (n / 2 ^ n.factorization 2) : ℂ)

theorem kron_odd {n : ℕ} (hn : Odd n) (D : ℤ) : kron D n = (jacobiSym D n : ℂ) := by
  have : n.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => by rw [Nat.odd_iff] at hn; omega)
  simp [kron, this]

theorem fact2 {a m : ℕ} (hm : Odd m) : (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (fun h => by rw [Nat.odd_iff] at hm; omega)]
  simp

theorem kron_even {a m : ℕ} (hm : Odd m) (D : ℤ) :
    kron D (2 ^ a * m) = ((χ₈ (D : ZMod 8) : ℤ) : ℂ) ^ a * (jacobiSym D m : ℂ) := by
  rw [kron, fact2 hm, Nat.mul_div_cancel_left _ (by positivity)]

/-- `a ↦ J(a.val | m)` as a character mod `m`, any `m ≠ 0`. -/
noncomputable def jcharN (m : ℕ) [NeZero m] : DirichletCharacter ℂ m where
  toFun a := (jacobiSym (a.val : ℤ) m : ℂ)
  map_one' := by
    rcases Nat.lt_or_ge 1 m with h | h
    · haveI : Fact (1 < m) := ⟨h⟩; simp [ZMod.val_one, jacobiSym.one_left]
    · have : m = 1 := by have := NeZero.ne m; omega
      subst this; simp [jacobiSym.one_right]
  map_mul' a b := by
    show (jacobiSym ((a*b).val : ℤ) m : ℂ) = (jacobiSym (a.val : ℤ) m : ℂ) * (jacobiSym (b.val : ℤ) m : ℂ)
    rw [ZMod.val_mul, ← Int.cast_mul, ← jacobiSym.mul_left]
    congr 1
    apply jacobiSym.mod_left'
    push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)
  map_nonunit' a ha := by
    show (jacobiSym (a.val : ℤ) m : ℂ) = 0
    have : ¬ Nat.Coprime a.val m := by
      intro h; apply ha; rw [← ZMod.natCast_zmod_val a]; exact (ZMod.isUnit_iff_coprime _ _).2 h
    have h0 : jacobiSym (a.val : ℤ) m = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]; exact this
    rw [h0, Int.cast_zero]

theorem jcharN_nat (m : ℕ) [NeZero m] (k : ℕ) : jcharN m (k : ZMod m) = (jacobiSym k m : ℂ) := by
  show (jacobiSym (((k : ZMod m)).val : ℤ) m : ℂ) = _
  congr 1
  apply jacobiSym.mod_left'
  rw [ZMod.val_natCast]; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)

noncomputable def chi8C : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
noncomputable def chi8'C : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

/-- `k ↦ J(k|m) e(k)` mod `8m`. -/
noncomputable def psi8 (m : ℕ) [NeZero m] (e : DirichletCharacter ℂ 8) : DirichletCharacter ℂ (8 * m) :=
  changeLevel (dvd_mul_left m 8) (jcharN m) * changeLevel (dvd_mul_right 8 m) e

theorem psi8_nat (m : ℕ) [NeZero m] (e : DirichletCharacter ℂ 8) (k : ℕ) :
    psi8 m e (k : ZMod (8 * m)) = (jacobiSym k m : ℂ) * e (k : ZMod 8) := by
  rw [← jcharN_nat]
  by_cases hc : Nat.Coprime k (8 * m)
  · have hc' : IsCoprime (k : ℤ) (8 * m : ℕ) := Nat.isCoprime_iff_coprime.2 hc
    simp only [psi8, MulChar.mul_apply]
    have e1 := changeLevel_eq_cast_of_dvd' (jcharN m) (dvd_mul_left m 8) hc'
    have e2 := changeLevel_eq_cast_of_dvd' e (dvd_mul_right 8 m) hc'
    push_cast at e1 e2; rw [e1, e2]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    by_cases h8 : Nat.Coprime k 8
    · have hn' : ¬ Nat.Coprime k m := fun h' => hc (Nat.Coprime.mul_right h8 h')
      rw [MulChar.map_nonunit (jcharN m) (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    · rw [MulChar.map_nonunit e (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]

theorem ne_one_of_neg {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℕ) (h : χ (k : ZMod N) = -1) : χ ≠ 1 := by
  intro h1; rw [h1] at h
  by_cases hu : IsUnit (k : ZMod N)
  · rw [MulChar.one_apply hu] at h; norm_num at h
  · rw [MulChar.map_nonunit _ hu] at h; norm_num at h

theorem chi8_val (k : ℕ) : chi8C (k : ZMod 8) = ((χ₈ (k : ZMod 8) : ℤ) : ℂ) := rfl
theorem chi8'_val (k : ℕ) : chi8'C (k : ZMod 8) = ((χ₈' (k : ZMod 8) : ℤ) : ℂ) := rfl

/-- The two characters used for the class split, `e₁ = χ₈^a`, `e₂ = χ₈^{a+1} χ₈'`. -/
noncomputable def e1 (a : ℕ) : DirichletCharacter ℂ 8 := chi8C ^ a
noncomputable def e2 (a : ℕ) : DirichletCharacter ℂ 8 := chi8C ^ (a + 1) * chi8'C

theorem e1_nat {a : ℕ} (ha : a ≠ 0) (k : ℕ) : e1 a (k : ZMod 8) = ((χ₈ (k : ZMod 8) : ℤ) : ℂ) ^ a := by
  rw [e1, MulChar.pow_apply' _ ha, chi8_val]
theorem e2_nat (a : ℕ) (k : ℕ) : e2 a (k : ZMod 8) =
    ((χ₈ (k : ZMod 8) : ℤ) : ℂ) ^ (a + 1) * ((χ₈' (k : ZMod 8) : ℤ) : ℂ) := by
  rw [e2, MulChar.mul_apply, MulChar.pow_apply' _ (Nat.succ_ne_zero a), chi8_val, chi8'_val]

theorem crt8 {m : ℕ} (hm : Odd m) (u v : ℕ) : ∃ k : ℕ, k ≡ u [MOD m] ∧ k ≡ v [MOD 8] := by
  have hcop : Nat.Coprime m 8 := by
    rw [Nat.coprime_comm, show (8:ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.coprime_two_left).2 hm)
  exact ⟨_, (Nat.chineseRemainder hcop u v).2.1, (Nat.chineseRemainder hcop u v).2.2⟩

theorem mod8_cast {k v : ℕ} (h : k ≡ v [MOD 8]) : (k : ZMod 8) = v := (ZMod.natCast_eq_natCast_iff k v 8).2 h

/-- Non-principality: for odd `m`, `a ≥ 1`, and `m` non-square or `a` odd. -/
theorem psi8_ne_one {m a : ℕ} [NeZero m] (hm : Odd m) (ha : a ≠ 0) (hns : ¬ IsSquare m ∨ Odd a)
    (e : DirichletCharacter ℂ 8) (he : e = e1 a ∨ e = e2 a) : psi8 m e ≠ 1 := by
  by_cases hsq : IsSquare m
  · have hao : Odd a := hns.resolve_left (not_not.2 hsq)
    obtain ⟨k, hk1, hk2⟩ := crt8 hm 1 5
    apply ne_one_of_neg _ k
    rw [psi8_nat]
    have hJ : jacobiSym k m = 1 := by
      rw [jacobiSym.mod_left' (show (k:ℤ) % m = (1:ℕ) % m by exact_mod_cast hk1)]
      simp [jacobiSym.one_left]
    rw [hJ]
    have h5 : (k : ZMod 8) = 5 := by rw [mod8_cast hk2]; rfl
    obtain ⟨j, rfl⟩ := hao
    rcases he with rfl | rfl
    · rw [e1_nat ha, h5]; simp [pow_succ, pow_mul]
    · rw [e2_nat, h5]; simp [pow_succ, pow_mul]
  · obtain ⟨D, hD⟩ := Kron.exists_jacobiSym_eq_neg_one hm hsq
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge 1 m with h | h
      · exact h
      · exfalso; apply hsq; have := NeZero.ne m; exact ⟨1, by omega⟩
    obtain ⟨k, hk1, hk2⟩ := crt8 hm (D % m).toNat 1
    have hnpos : (0:ℤ) < m := by omega
    have hJ : jacobiSym k m = -1 := by
      rw [← hD]; apply jacobiSym.mod_left'
      have h1 : (k : ℤ) % m = ((D % m).toNat : ℤ) % m := by exact_mod_cast hk1
      rw [h1, Int.toNat_of_nonneg (Int.emod_nonneg _ hnpos.ne'), Int.emod_emod_of_dvd _ (dvd_refl _)]
    apply ne_one_of_neg _ k
    rw [psi8_nat, hJ, mod8_cast hk2]
    rcases he with rfl | rfl
    · rw [show ((1:ℕ) : ZMod 8) = 1 by simp, MulChar.map_one]; simp
    · rw [show ((1:ℕ) : ZMod 8) = 1 by simp, MulChar.map_one]; simp

/-- `B₈ = d(8m) √(8m) (1 + log 8m)`. -/
noncomputable def B8 (m : ℕ) : ℝ := ((8 * m).divisors.card : ℝ) * (Real.sqrt (8 * m : ℕ) * (1 + Real.log (8 * m : ℕ)))

theorem B8_pos {m : ℕ} [NeZero m] : 0 < B8 m := by
  have h1 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hc : 0 < (8 * m).divisors.card := Finset.card_pos.2 ⟨1, by simp; omega⟩
  have : (1:ℝ) ≤ ((8 * m : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 8 * m by omega)
  unfold B8
  have := Real.log_nonneg this
  have : 0 < Real.sqrt ((8 * m : ℕ) : ℝ) := Real.sqrt_pos.2 (by linarith)
  positivity

noncomputable def T8 (m x : ℕ) : ℝ := 2 * Real.sqrt (x * B8 m) + B8 m

theorem sqf_psi8_le {m a : ℕ} [NeZero m] (hm : Odd m) (ha : a ≠ 0) (hns : ¬ IsSquare m ∨ Odd a)
    (e : DirichletCharacter ℂ 8) (he : e = e1 a ∨ e = e2 a) (x : ℕ) :
    ‖∑ d ∈ (Ioc 0 x).filter Squarefree, psi8 m e (d : ZMod (8 * m))‖ ≤ T8 m x := by
  haveI : NeZero (8 * m) := ⟨by have := NeZero.ne m; omega⟩
  apply GSLemma.sqf_sum_le_sqrt (fun k => psi8 m e (k : ZMod (8 * m)))
  · intro a b; push_cast; exact map_mul _ _ _
  · intro k; exact DirichletCharacter.norm_le_one _ _
  · exact B8_pos
  · intro y; exact PolyaVinogradov.pv_nonprincipal (psi8_ne_one hm ha hns e he) y

/-- Class sums with the `χ₈^a` twist (`n = 2^a m`). -/
theorem class8_le {m a : ℕ} [NeZero m] (hm : Odd m) (ha : a ≠ 0) (hns : ¬ IsSquare m ∨ Odd a)
    (r : ℕ) (hr : r = 1 ∨ r = 3) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if Squarefree d ∧ d % 4 = r then
        ((χ₈ (d : ZMod 8) : ℤ) : ℂ) ^ a * (jacobiSym d m : ℂ) else 0)‖ ≤ T8 m x := by
  set s : ℂ := if r = 1 then 1 else -1
  have hs : ‖s‖ = 1 := by simp only [s]; split_ifs <;> simp
  have hid : ∀ d : ℕ, (if Squarefree d ∧ d % 4 = r then
      ((χ₈ (d : ZMod 8) : ℤ) : ℂ) ^ a * (jacobiSym d m : ℂ) else 0) =
      if Squarefree d then (psi8 m (e1 a) (d : ZMod (8 * m)) + s * psi8 m (e2 a) (d : ZMod (8 * m))) / 2
      else 0 := by
    intro d
    by_cases hq : Squarefree d
    · rw [if_pos hq, psi8_nat, psi8_nat, e1_nat ha, e2_nat, χ₈_nat_eq_if_mod_eight, χ₈'_nat_eq_if_mod_eight]
      have h4 : d % 4 = d % 8 % 4 := (Nat.mod_mod_of_dvd d (by norm_num)).symm
      have h2 : d % 2 = d % 8 % 2 := (Nat.mod_mod_of_dvd d (by norm_num)).symm
      rw [h4, h2]
      have h8 : d % 8 < 8 := Nat.mod_lt _ (by norm_num)
      simp only [s, hq, true_and]
      rcases hr with rfl | rfl <;> interval_cases h : d % 8 <;> simp [zero_pow ha] <;> ring
    · rw [if_neg (fun h => hq h.1), if_neg hq]
  simp_rw [hid]
  rw [← sum_filter, ← sum_div, sum_add_distrib, ← mul_sum, norm_div]
  have h1 := sqf_psi8_le hm ha hns (e1 a) (Or.inl rfl) x
  have h2 := sqf_psi8_le hm ha hns (e2 a) (Or.inr rfl) x
  calc _ ≤ (‖∑ d ∈ (Ioc 0 x).filter Squarefree, psi8 m (e1 a) (d : ZMod (8 * m))‖ +
        ‖s‖ * ‖∑ d ∈ (Ioc 0 x).filter Squarefree, psi8 m (e2 a) (d : ZMod (8 * m))‖) / ‖(2:ℂ)‖ := by
        gcongr; rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ _ := by rw [hs, one_mul, Complex.norm_two]; linarith

theorem chi8_four_dvd {d : ℕ} (h : 4 ∣ d) : χ₈ (d : ZMod 8) = 0 := by
  rw [χ₈_nat_eq_if_mod_eight, if_pos (by omega)]

/-- **GS Lemma 4.1, positive discriminants, even `n = 2^a m`** (`m` odd, `a ≥ 1`, `n` non-square):
`‖Σ_{0<D≤x, D fund.} (D|n)‖ ≤ 2√(x B₈) + B₈`, `B₈ = d(8m)√(8m)(1 + log 8m)`. -/
theorem gs_even_pos {m a : ℕ} [NeZero m] (hm : Odd m) (ha : a ≠ 0) (hns : ¬ IsSquare m ∨ Odd a) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundPos d then kron d (2 ^ a * m) else 0)‖ ≤ T8 m x := by
  have hpt : ∀ d : ℕ, (if fundPos d then kron d (2 ^ a * m) else 0) =
      (if Squarefree d ∧ d % 4 = 1 then ((χ₈ (d : ZMod 8) : ℤ) : ℂ) ^ a * (jacobiSym d m : ℂ) else 0) := by
    intro d; rw [kron_even hm]; push_cast; unfold fundPos
    by_cases h1 : Squarefree d ∧ d % 4 = 1
    · rw [if_pos (Or.inl h1), if_pos h1]
    · rw [if_neg h1]; split_ifs with h
      · rcases h with h | ⟨h4, -⟩
        · exact absurd h h1
        · rw [chi8_four_dvd h4]; simp [zero_pow ha]
      · rfl
  simp_rw [hpt]; exact class8_le hm ha hns 1 (Or.inl rfl) x

/-- **GS Lemma 4.1, negative discriminants, even `n = 2^a m`**: same bound for `D = -d`. -/
theorem gs_even_neg {m a : ℕ} [NeZero m] (hm : Odd m) (ha : a ≠ 0) (hns : ¬ IsSquare m ∨ Odd a) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundNeg d then kron (-(d:ℤ)) (2 ^ a * m) else 0)‖ ≤ T8 m x := by
  have hneg : ∀ d : ℕ, ((-(d:ℤ) : ℤ) : ZMod 8) = (-1 : ZMod 8) * (d : ZMod 8) := by intro d; push_cast; ring
  have hm1 : χ₈ (-1 : ZMod 8) = 1 := by decide
  have hpt : ∀ d : ℕ, (if fundNeg d then kron (-(d:ℤ)) (2 ^ a * m) else 0) =
      (jacobiSym (-1) m : ℂ) *
      (if Squarefree d ∧ d % 4 = 3 then ((χ₈ (d : ZMod 8) : ℤ) : ℂ) ^ a * (jacobiSym d m : ℂ) else 0) := by
    intro d
    rw [kron_even hm, hneg, map_mul, hm1, one_mul,
      show (-(d:ℤ)) = -1 * d by ring, jacobiSym.mul_left]
    push_cast; unfold fundNeg
    by_cases h1 : Squarefree d ∧ d % 4 = 3
    · rw [if_pos (Or.inl h1), if_pos h1]; ring
    · rw [if_neg h1, mul_zero]; split_ifs with h
      · rcases h with h | ⟨h4, -⟩
        · exact absurd h h1
        · rw [chi8_four_dvd h4]; simp [zero_pow ha]
      · rfl
  simp_rw [hpt]; rw [← mul_sum, norm_mul]
  calc _ ≤ 1 * T8 m x := mul_le_mul (by rcases jacobiSym.trichotomy (-1) m with h | h | h <;> simp [h]) (class8_le hm ha hns 3 (Or.inr rfl) x)
        (norm_nonneg _) zero_le_one
    _ = T8 m x := one_mul _

end GSEven

namespace GSKron
open Finset GSFund GSEven

/-- The bound in GS Lemma 4.1: `3(2√(xB)+B)` with `B = d(4n)√(4n)(1+log 4n)` for odd `n`, and
`2√(xB₈)+B₈` with `B₈ = d(8m)√(8m)(1+log 8m)`, `m = n / 2^{v₂(n)}`, for even `n`. -/
noncomputable def GSB (n x : ℕ) : ℝ :=
  if n % 2 = 1 then 3 * T n x else T8 (n / 2 ^ n.factorization 2) x

theorem even_split {n : ℕ} (hn : 1 < n) (hsq : ¬ IsSquare n) (hev : ¬ n % 2 = 1) :
    let a := n.factorization 2; let m := n / 2 ^ a;
    n = 2 ^ a * m ∧ Odd m ∧ a ≠ 0 ∧ (¬ IsSquare m ∨ Odd a) := by
  intro a m
  have hn0 : n ≠ 0 := by omega
  have e : n = 2 ^ a * m := (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hm : Odd m := (Nat.coprime_two_left).1 (Nat.coprime_ordCompl Nat.prime_two hn0)
  have ha : a ≠ 0 := (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 (by omega)).ne'
  refine ⟨e, hm, ha, ?_⟩
  by_contra h
  push_neg at h
  obtain ⟨⟨r, hr⟩, hae⟩ := h
  obtain ⟨b, hb⟩ := Nat.not_odd_iff_even.1 hae
  apply hsq; refine ⟨2 ^ b * r, ?_⟩
  rw [e, hr, hb, pow_add]; ring

/-- **Granville–Soundararajan Lemma 4.1, positive fundamental discriminants, all non-square `n > 1`**,
with `(D|n)` the Kronecker symbol. -/
theorem gs_kron_pos {n : ℕ} (hn : 1 < n) (hsq : ¬ IsSquare n) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundPos d then kron d n else 0)‖ ≤ GSB n x := by
  unfold GSB
  by_cases ho : n % 2 = 1
  · haveI : Fact (1 < n) := ⟨hn⟩
    have hodd : Odd n := Nat.odd_iff.2 ho
    rw [if_pos ho]; simp_rw [kron_odd hodd]; exact gs_pos hodd hsq x
  · rw [if_neg ho]
    obtain ⟨e, hm, ha, hns⟩ := even_split hn hsq ho
    haveI : NeZero (n / 2 ^ n.factorization 2) := ⟨by rintro h; rw [h] at hm; simp at hm⟩
    have := gs_even_pos hm ha hns x
    rwa [← e] at this

/-- **Granville–Soundararajan Lemma 4.1, negative fundamental discriminants, all non-square `n > 1`.** -/
theorem gs_kron_neg {n : ℕ} (hn : 1 < n) (hsq : ¬ IsSquare n) (x : ℕ) :
    ‖∑ d ∈ Ioc 0 x, (if fundNeg d then kron (-(d:ℤ)) n else 0)‖ ≤ GSB n x := by
  unfold GSB
  by_cases ho : n % 2 = 1
  · haveI : Fact (1 < n) := ⟨hn⟩
    have hodd : Odd n := Nat.odd_iff.2 ho
    rw [if_pos ho]; simp_rw [kron_odd hodd]; exact gs_neg hodd hsq x
  · rw [if_neg ho]
    obtain ⟨e, hm, ha, hns⟩ := even_split hn hsq ho
    haveI : NeZero (n / 2 ^ n.factorization 2) := ⟨by rintro h; rw [h] at hm; simp at hm⟩
    have := gs_even_neg hm ha hns x
    rwa [← e] at this

end GSKron

namespace GSMoment
open Finset GSFund GSEven GSKron

theorem kron_one (D : ℤ) : kron D 1 = 1 := by simp [kron]

theorem kron_mul (D : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : kron D (m * n) = kron D m * kron D n := by
  unfold kron
  have h1 : (m * n).factorization 2 = m.factorization 2 + n.factorization 2 := by
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply]
  have h2 : (m * n) / 2 ^ (m * n).factorization 2 = (m / 2 ^ m.factorization 2) * (n / 2 ^ n.factorization 2) :=
    Nat.ordCompl_mul m n 2
  have hm' : m / 2 ^ m.factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 hm).ne'
  have hn' : n / 2 ^ n.factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 hn).ne'
  rw [h2, h1, jacobiSym.mul_right' D hm' hn', pow_add]; push_cast; ring

theorem kron_prod (D : ℤ) {k : ℕ} (f : Fin k → ℕ) (hf : ∀ i, f i ≠ 0) :
    kron D (∏ i, f i) = ∏ i, kron D (f i) := by
  induction k with
  | zero => simp [kron_one]
  | succ k ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, kron_mul D (hf 0) (Finset.prod_ne_zero_iff.2 (fun i _ => hf _)),
      ih (fun i => f i.succ) (fun i => hf _)]

/-- Generic moment expansion. `χ d n` multiplicative in `n`; `F` the family of `d`. -/
theorem moment_generic (F : ℕ → Prop) [DecidablePred F] (χ : ℕ → ℕ → ℂ)
    (hprod : ∀ d (k : ℕ) (f : Fin k → ℕ), (∀ i, f i ≠ 0) → χ d (∏ i, f i) = ∏ i, χ d (f i))
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) (k x : ℕ)
    (c : ℕ → ℂ) (R G : ℕ → ℝ)
    (Hcount : ∀ n, 0 < n → IsSquare n → ‖∑ d ∈ Ioc 0 x, (if F d then χ d n else 0) - c n * x‖ ≤ R n)
    (HGS : ∀ n, 1 < n → ¬ IsSquare n → ‖∑ d ∈ Ioc 0 x, (if F d then χ d n else 0)‖ ≤ G n) :
    ‖∑ d ∈ Ioc 0 x, (if F d then (∑ p ∈ P, a p * χ d p) ^ k else 0) -
        (x : ℂ) * ∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
          (∏ i, a (f i)) * c (∏ i, f i)‖ ≤
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P),
        ‖∏ i, a (f i)‖ * (if IsSquare (∏ i, f i) then R (∏ i, f i) else G (∏ i, f i)) := by
  have hexp : ∀ d, (∑ p ∈ P, a p * χ d p) ^ k =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P), (∏ i, a (f i)) * χ d (∏ i, f i) := by
    intro d
    rw [← Fin.prod_const, prod_univ_sum (fun _ => P) (fun _ p => a p * χ d p)]
    apply sum_congr rfl; intro f hf
    rw [Fintype.mem_piFinset] at hf
    rw [hprod d k f (fun i => (hP _ (hf i)).ne'), prod_mul_distrib]
  simp_rw [hexp]
  have hsplit : ∀ d, (if F d then ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P),
        (∏ i, a (f i)) * χ d (∏ i, f i) else 0) =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P), (if F d then (∏ i, a (f i)) * χ d (∏ i, f i) else 0) := by
    intro d; split_ifs <;> simp
  rw [sum_congr rfl (fun d _ => hsplit d), sum_comm, mul_sum, sum_filter, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro f hf
  rw [Fintype.mem_piFinset] at hf
  have hpos : 0 < ∏ i, f i := Finset.prod_pos (fun i _ => hP _ (hf i))
  have hS : ∑ d ∈ Ioc 0 x, (if F d then (∏ i, a (f i)) * χ d (∏ i, f i) else 0) =
      (∏ i, a (f i)) * ∑ d ∈ Ioc 0 x, (if F d then χ d (∏ i, f i) else 0) := by
    rw [mul_sum]; apply sum_congr rfl; intro d _; split_ifs <;> simp
  rw [hS]
  by_cases hsq : IsSquare (∏ i, f i)
  · rw [if_pos hsq, if_pos hsq,
      show (∏ i, a (f i)) * ∑ d ∈ Ioc 0 x, (if F d then χ d (∏ i, f i) else 0) - (x:ℂ) * ((∏ i, a (f i)) * c (∏ i, f i)) =
        (∏ i, a (f i)) * (∑ d ∈ Ioc 0 x, (if F d then χ d (∏ i, f i) else 0) - c (∏ i, f i) * x) by ring,
      norm_mul]
    exact mul_le_mul_of_nonneg_left (Hcount _ hpos hsq) (norm_nonneg _)
  · rw [if_neg hsq, if_neg hsq, sub_zero, norm_mul]
    have h1 : 1 < ∏ i, f i := by
      rcases Nat.lt_or_ge 1 (∏ i, f i) with h | h
      · exact h
      · exfalso; apply hsq; exact ⟨1, by omega⟩
    exact mul_le_mul_of_nonneg_left (HGS _ h1 hsq) (norm_nonneg _)

/-- **Moments of the short Euler-sum model, positive discriminants.** For a finite set `P` of positive
integers (e.g. primes `≤ y`), weights `a`, and `S_D = Σ_{p∈P} a_p (D|p)`:
`‖Σ_{0<D≤x fund.} S_D^k − x · Σ_{f ∈ P^k, ∏f = □} (∏ a_{f i}) c(∏ f)‖ ≤ Σ_{f ∈ P^k} ‖∏ a‖ · (R or GSB)`,
**assuming** the square-`n` count hypothesis `Hcount` (main term `c(n) x`, error `R n`). -/
theorem moment_pos (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) (k x : ℕ) (c : ℕ → ℂ) (R : ℕ → ℝ)
    (Hcount : ∀ n, 0 < n → IsSquare n →
      ‖∑ d ∈ Ioc 0 x, (if fundPos d then kron d n else 0) - c n * x‖ ≤ R n) :
    ‖∑ d ∈ Ioc 0 x, (if fundPos d then (∑ p ∈ P, a p * kron d p) ^ k else 0) -
        (x : ℂ) * ∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
          (∏ i, a (f i)) * c (∏ i, f i)‖ ≤
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P),
        ‖∏ i, a (f i)‖ * (if IsSquare (∏ i, f i) then R (∏ i, f i) else GSB (∏ i, f i) x) :=
  moment_generic fundPos (fun d n => kron d n) (fun d k f hf => kron_prod d f hf) P hP a k x c R
    (fun n => GSB n x) Hcount (fun n h1 hs => gs_kron_pos h1 hs x)

/-- **Moments, negative discriminants** (`D = -d`). -/
theorem moment_neg (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) (k x : ℕ) (c : ℕ → ℂ) (R : ℕ → ℝ)
    (Hcount : ∀ n, 0 < n → IsSquare n →
      ‖∑ d ∈ Ioc 0 x, (if fundNeg d then kron (-(d:ℤ)) n else 0) - c n * x‖ ≤ R n) :
    ‖∑ d ∈ Ioc 0 x, (if fundNeg d then (∑ p ∈ P, a p * kron (-(d:ℤ)) p) ^ k else 0) -
        (x : ℂ) * ∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
          (∏ i, a (f i)) * c (∏ i, f i)‖ ≤
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P),
        ‖∏ i, a (f i)‖ * (if IsSquare (∏ i, f i) then R (∏ i, f i) else GSB (∏ i, f i) x) :=
  moment_generic fundNeg (fun d n => kron (-(d:ℤ)) n) (fun d k f hf => kron_prod _ f hf) P hP a k x c R
    (fun n => GSB n x) Hcount (fun n h1 hs => gs_kron_neg h1 hs x)

open Filter Topology in
theorem sqrt_bound_div (B : ℝ) (hB : 0 ≤ B) :
    Tendsto (fun x : ℕ => (2 * Real.sqrt (x * B) + B) / x) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℕ => ((x:ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun x : ℕ => Real.sqrt ((x:ℝ))⁻¹) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hinv; simpa [Function.comp_def] using this
  have hsum : Tendsto (fun x : ℕ => 2 * Real.sqrt B * Real.sqrt ((x:ℝ))⁻¹ + B * ((x:ℝ))⁻¹) atTop (𝓝 0) := by
    have := (hs.const_mul (2 * Real.sqrt B)).add (hinv.const_mul B); simpa using this
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx' : (0:ℝ) < x := by exact_mod_cast hx
  rw [Real.sqrt_mul hx'.le, Real.sqrt_inv, add_div]
  have h0 : Real.sqrt (x:ℝ) ≠ 0 := (Real.sqrt_pos.2 hx').ne'
  have h2 := Real.mul_self_sqrt hx'.le
  field_simp
  first | linear_combination (-2 * Real.sqrt B) * h2 | linear_combination (2 * Real.sqrt B) * h2

theorem Bn_nonneg (n : ℕ) : 0 ≤ GSAssemble.Bn n := by
  unfold GSAssemble.Bn; have := Real.log_natCast_nonneg (4 * n); positivity

theorem B8_nonneg (n : ℕ) : 0 ≤ B8 n := by
  unfold B8; have := Real.log_natCast_nonneg (8 * n); positivity

open Filter Topology in
theorem GSB_div (n : ℕ) : Tendsto (fun x : ℕ => GSB n x / x) atTop (𝓝 0) := by
  unfold GSB T T8
  split_ifs
  · have := (sqrt_bound_div _ (Bn_nonneg n)).const_mul 3
    simp only [mul_zero] at this; refine this.congr (fun x => ?_); ring
  · exact sqrt_bound_div _ (B8_nonneg _)

open Filter Topology in
/-- Generic normalised limit: from a bound `‖Σ − x M‖ ≤ b x` with `b x / x → 0`. -/
theorem lim_of_bound (Sx : ℕ → ℂ) (M : ℂ) (b : ℕ → ℝ) (hb : ∀ x, ‖Sx x - (x:ℂ) * M‖ ≤ b x)
    (hlim : Tendsto (fun x : ℕ => b x / x) atTop (𝓝 0)) :
    Tendsto (fun x : ℕ => ((x:ℂ))⁻¹ * Sx x) atTop (𝓝 M) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [show ((x:ℂ))⁻¹ * Sx x - M = ((x:ℂ))⁻¹ * (Sx x - x * M) by field_simp, norm_mul, norm_inv,
    Complex.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hb x) (by positivity)

open Filter Topology in
/-- **Moments, positive discriminants, limit form.** Under `Hcount` for every `x` with `R n x = o(x)`,
`(1/x) Σ_{0<D≤x fund.} S_D^k → Σ_{f ∈ P^k, ∏ f = □} (∏ a_{f i}) c(∏ f)`. -/
theorem moment_pos_tendsto (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) (k : ℕ) (c : ℕ → ℂ)
    (R : ℕ → ℕ → ℝ)
    (Hcount : ∀ x n, 0 < n → IsSquare n →
      ‖∑ d ∈ Ioc 0 x, (if fundPos d then kron d n else 0) - c n * x‖ ≤ R n x)
    (hR : ∀ n, Tendsto (fun x : ℕ => R n x / x) atTop (𝓝 0)) :
    Tendsto (fun x : ℕ => ((x:ℂ))⁻¹ *
        ∑ d ∈ Ioc 0 x, (if fundPos d then (∑ p ∈ P, a p * kron d p) ^ k else 0)) atTop
      (𝓝 (∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
          (∏ i, a (f i)) * c (∏ i, f i))) := by
  apply lim_of_bound _ _ _ (fun x => moment_pos P hP a k x c (fun n => R n x) (Hcount x))
  simp_rw [sum_div]
  rw [show (0:ℝ) = ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P), 0 by simp]
  apply tendsto_finsetSum; intro f _
  simp_rw [mul_div_assoc]
  rw [show (0:ℝ) = ‖∏ i, a (f i)‖ * 0 by simp]
  apply Tendsto.const_mul
  split_ifs
  · exact hR _
  · exact GSB_div _

open Filter Topology in
/-- **Moments, negative discriminants, limit form.** -/
theorem moment_neg_tendsto (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) (k : ℕ) (c : ℕ → ℂ)
    (R : ℕ → ℕ → ℝ)
    (Hcount : ∀ x n, 0 < n → IsSquare n →
      ‖∑ d ∈ Ioc 0 x, (if fundNeg d then kron (-(d:ℤ)) n else 0) - c n * x‖ ≤ R n x)
    (hR : ∀ n, Tendsto (fun x : ℕ => R n x / x) atTop (𝓝 0)) :
    Tendsto (fun x : ℕ => ((x:ℂ))⁻¹ *
        ∑ d ∈ Ioc 0 x, (if fundNeg d then (∑ p ∈ P, a p * kron (-(d:ℤ)) p) ^ k else 0)) atTop
      (𝓝 (∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
          (∏ i, a (f i)) * c (∏ i, f i))) := by
  apply lim_of_bound _ _ _ (fun x => moment_neg P hP a k x c (fun n => R n x) (Hcount x))
  simp_rw [sum_div]
  rw [show (0:ℝ) = ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P), 0 by simp]
  apply tendsto_finsetSum; intro f _
  simp_rw [mul_div_assoc]
  rw [show (0:ℝ) = ‖∏ i, a (f i)‖ * 0 by simp]
  apply Tendsto.const_mul
  split_ifs
  · exact hR _
  · exact GSB_div _

end GSMoment

namespace GSDens
open Finset Filter Topology

theorem count_periodic (p : ℕ → Prop) [DecidablePred p] (L : ℕ) (hp : Function.Periodic p L) (q s : ℕ) :
    Nat.count p (q * L + s) = q * Nat.count p L + Nat.count p s := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * L + s = L + (q * L + s) by ring, Nat.count_add]
    have : Nat.count (fun k => p (L + k)) (q * L + s) = Nat.count p (q * L + s) := by
      simp only [Nat.count_eq_card_filter_range]
      congr 1; apply filter_congr; intro k _; rw [add_comm, hp k]
    rw [this, ih]; ring

/-- Periodic counting: `|count p x − x · count p L / L| ≤ L`. -/
theorem periodic_dens (p : ℕ → Prop) [DecidablePred p] (L : ℕ) (hL : 0 < L) (hp : Function.Periodic p L) (x : ℕ) :
    |(Nat.count p x : ℝ) - x * ((Nat.count p L : ℝ) / L)| ≤ L := by
  have hx : x = x / L * L + x % L := (Nat.div_add_mod' x L).symm
  have hc := count_periodic p L hp (x / L) (x % L)
  rw [← hx] at hc
  have hs : x % L < L := Nat.mod_lt _ hL
  have h1 : Nat.count p (x % L) ≤ x % L := Nat.count_le p
  have h2 : Nat.count p L ≤ L := Nat.count_le p
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  have hxr : (x:ℝ) = (x / L : ℕ) * L + (x % L : ℕ) := by exact_mod_cast hx
  rw [hc, hxr]; push_cast
  have e : ((x / L : ℕ) * (L:ℝ) + (x % L : ℕ)) * ((Nat.count p L : ℝ) / L) =
      (x / L : ℕ) * (Nat.count p L : ℝ) + (x % L : ℕ) * (Nat.count p L : ℝ) / L := by
    field_simp
  rw [e]
  have h3 : (0:ℝ) ≤ (x % L : ℕ) * (Nat.count p L : ℝ) / L := by positivity
  have h4 : (x % L : ℕ) * (Nat.count p L : ℝ) / L ≤ (x % L : ℕ) := by
    rw [div_le_iff₀ hLr]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast h2) (by positivity)
  have h5 : ((x % L : ℕ) : ℝ) < L := by exact_mod_cast hs
  have h6 : ((Nat.count p (x % L) : ℕ) : ℝ) ≤ (x % L : ℕ) := by exact_mod_cast h1
  rw [abs_le]; constructor <;> push_cast at * <;> nlinarith

open Classical in
/-- Multiples of `e²` below `x`, beyond `E`: `#{0 < d < x : ∃ e > E, e² ∣ d} ≤ x / E`. -/
theorem tail_count (E : ℕ) (hE : 1 ≤ E) (x : ℕ) :
    (Nat.count (fun d => d ≠ 0 ∧ ∃ e, E < e ∧ e ^ 2 ∣ d) x : ℝ) ≤ x / E := by
  classical
  rw [Nat.count_eq_card_filter_range]
  have hsub : (range x).filter (fun d => d ≠ 0 ∧ ∃ e, E < e ∧ e ^ 2 ∣ d) ⊆
      (Ioc E x).biUnion (fun e => (Ioc 0 x).filter (fun d => e ^ 2 ∣ d)) := by
    intro d hd
    simp only [mem_filter, mem_range] at hd
    obtain ⟨hdx, hd0, e, he, hed⟩ := hd
    simp only [mem_biUnion, mem_Ioc, mem_filter]
    have : e ≤ d := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hed
      nlinarith
    exact ⟨e, ⟨he, by omega⟩, ⟨Nat.pos_of_ne_zero hd0, by omega⟩, hed⟩
  have hc := (card_le_card hsub).trans card_biUnion_le
  have hc' : ((card ((range x).filter (fun d => d ≠ 0 ∧ ∃ e, E < e ∧ e ^ 2 ∣ d)) : ℕ) : ℝ) ≤
      ∑ e ∈ Ioc E x, (x:ℝ) * ((e:ℝ) ^ 2)⁻¹ := by
    refine (Nat.cast_le.2 hc).trans ?_
    push_cast
    apply sum_le_sum; intro e he
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    have hpos : (0:ℝ) < (e:ℝ) ^ 2 := by
      have : 0 < e := by simp at he; omega
      positivity
    refine (Nat.cast_div_le).trans ?_
    push_cast; rw [div_eq_mul_inv]
  refine hc'.trans ?_
  rw [← mul_sum]
  by_cases hxE : E ≤ x
  · have ht := GSLemma.tail_inv_sq E hE (x - E)
    rw [show E + (x - E) = x by omega] at ht
    have hx0 : (0:ℝ) ≤ ((x:ℕ):ℝ)⁻¹ := by positivity
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · rw [Ioc_eq_empty (by omega)]; simp; positivity

/-- No odd square `e² > 1` divides `d`. -/
def Odf (d : ℕ) : Prop := ∀ e, 1 < e → Odd e → ¬ e ^ 2 ∣ d

/-- `Q d`: residue condition mod 16, coprime to `r`, no odd square factor. -/
def Q (Cp : ℕ → Prop) (r d : ℕ) : Prop := Cp (d % 16) ∧ Nat.Coprime d r ∧ Odf d

/-- Truncation of `Q` to odd squares `e² ≤ E²`; periodic. -/
def PE (Cp : ℕ → Prop) (r E d : ℕ) : Prop :=
  Cp (d % 16) ∧ Nat.Coprime d r ∧ ∀ e, 1 < e → e ≤ E → Odd e → ¬ e ^ 2 ∣ d

open Classical in
theorem PE_periodic (Cp : ℕ → Prop) (r E : ℕ) :
    Function.Periodic (PE Cp r E) (16 * r * (E.factorial) ^ 2) := by
  intro d
  unfold PE
  have h16 : (d + 16 * r * E.factorial ^ 2) % 16 = d % 16 := by
    rw [show 16 * r * E.factorial ^ 2 = 16 * (r * E.factorial ^ 2) by ring, Nat.add_mul_mod_self_left]
  have hr : Nat.Coprime (d + 16 * r * E.factorial ^ 2) r ↔ Nat.Coprime d r := by
    rw [show 16 * r * E.factorial ^ 2 = (16 * E.factorial ^ 2) * r by ring]
    exact Nat.coprime_add_mul_right_left _ _ _
  have he : ∀ e, 1 < e → e ≤ E → (e ^ 2 ∣ d + 16 * r * E.factorial ^ 2 ↔ e ^ 2 ∣ d) := by
    intro e he1 heE
    have h1 : e ∣ E.factorial := Nat.dvd_factorial (by omega) heE
    have h2 : e ^ 2 ∣ 16 * r * E.factorial ^ 2 := Dvd.dvd.mul_left (pow_dvd_pow_of_dvd h1 2) _
    exact ⟨fun h => by simpa using Nat.dvd_sub h h2, fun h => dvd_add h h2⟩
  rw [h16]
  apply propext
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, hr.1 b, fun e h1 h2 h3 h => c e h1 h2 h3 ((he e h1 h2).2 h)⟩
  · rintro ⟨a, b, c⟩; refine ⟨a, hr.2 b, fun e h1 h2 h3 h => c e h1 h2 h3 ((he e h1 h2).1 h)⟩

open Classical in
theorem Q_le_PE (Cp : ℕ → Prop) (r E x : ℕ) : Nat.count (Q Cp r) x ≤ Nat.count (PE Cp r E) x :=
  Nat.count_mono_left (fun d _ ⟨a, b, c⟩ => ⟨a, b, fun e h1 _ h3 => c e h1 h3⟩)

open Classical in
theorem PE_le_Q (Cp : ℕ → Prop) (hC0 : ¬ Cp 0) (r E x : ℕ) :
    Nat.count (PE Cp r E) x ≤ Nat.count (Q Cp r) x + Nat.count (fun d => d ≠ 0 ∧ ∃ e, E < e ∧ e ^ 2 ∣ d) x := by
  simp only [Nat.count_eq_card_filter_range]
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro d hd
  simp only [mem_filter, mem_range, mem_union] at hd ⊢
  obtain ⟨hdx, a, b, c⟩ := hd
  by_cases hq : Odf d
  · left; exact ⟨hdx, a, b, hq⟩
  · right
    refine ⟨hdx, ?_, ?_⟩
    · rintro rfl; exact hC0 (by simpa using a)
    · unfold Odf at hq; push Not at hq
      obtain ⟨e, h1, h2, h3⟩ := hq
      refine ⟨e, ?_, h3⟩
      by_contra h; exact c e h1 (by omega) h2 h3

open Classical in
theorem Q_approx (Cp : ℕ → Prop) (hC0 : ¬ Cp 0) (r : ℕ) (hr : 0 < r) (E : ℕ) (hE : 1 ≤ E) (x : ℕ) :
    |(Nat.count (Q Cp r) x : ℝ) - x * ((Nat.count (PE Cp r E) (16 * r * E.factorial ^ 2) : ℝ) /
        (16 * r * E.factorial ^ 2 : ℕ))| ≤ (16 * r * E.factorial ^ 2 : ℕ) + x / E := by
  set L := 16 * r * E.factorial ^ 2
  have hL : 0 < L := by have := E.factorial_pos; positivity
  have hp := periodic_dens (PE Cp r E) L hL (PE_periodic Cp r E) x
  have h1 : (Nat.count (Q Cp r) x : ℝ) ≤ Nat.count (PE Cp r E) x := by exact_mod_cast Q_le_PE Cp r E x
  have h2 : (Nat.count (PE Cp r E) x : ℝ) ≤ Nat.count (Q Cp r) x +
      Nat.count (fun d => d ≠ 0 ∧ ∃ e, E < e ∧ e ^ 2 ∣ d) x := by exact_mod_cast PE_le_Q Cp hC0 r E x
  have h3 := tail_count E hE x
  rw [abs_le] at hp ⊢; constructor <;> linarith [hp.1, hp.2]

open Classical in
/-- **Density.** `count (Q Cp r) x / x` converges. -/
theorem Q_density (Cp : ℕ → Prop) (hC0 : ¬ Cp 0) (r : ℕ) (hr : 0 < r) :
    ∃ c : ℝ, Tendsto (fun x : ℕ => (Nat.count (Q Cp r) x : ℝ) / x) atTop (𝓝 c) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨E, hE⟩ := exists_nat_gt (4 / ε)
  have hE1 : 1 ≤ E := by
    have : (0:ℝ) < 4 / ε := by positivity
    have : (0:ℝ) < E := by linarith
    exact_mod_cast this
  set L := 16 * r * E.factorial ^ 2
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * L / ε)
  have hEp : (0:ℝ) < E := by exact_mod_cast hE1
  have hLp : (0:ℝ) ≤ L := by positivity
  have hNp : (0:ℝ) < N := by
    have : (0:ℝ) ≤ 4 * L / ε := by positivity
    linarith
  set δ := (Nat.count (PE Cp r E) L : ℝ) / (L : ℕ)
  have key : ∀ x : ℕ, N ≤ x → |(Nat.count (Q Cp r) x : ℝ) / x - δ| < ε / 2 := by
    intro x hx
    have hxp : (0:ℝ) < x := lt_of_lt_of_le hNp (by exact_mod_cast hx)
    have ha := Q_approx Cp hC0 r hr E hE1 x
    have : (Nat.count (Q Cp r) x : ℝ) / x - δ = ((Nat.count (Q Cp r) x : ℝ) - x * δ) / x := by
      field_simp
    rw [this, abs_div, abs_of_pos hxp, div_lt_iff₀ hxp]
    have hLx : (L:ℝ) < ε / 4 * x := by
      have : 4 * L / ε < x := lt_of_lt_of_le hN (by exact_mod_cast hx)
      rw [div_lt_iff₀ hε] at this; linarith
    have hEx : (x:ℝ) / E < ε / 4 * x := by
      rw [div_lt_iff₀ hEp]
      have : 4 / ε < E := hE
      rw [div_lt_iff₀ hε] at this; nlinarith
    linarith
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have := key n hn; have := key N le_rfl
  calc _ ≤ |(Nat.count (Q Cp r) n : ℝ) / n - δ| + |(Nat.count (Q Cp r) N : ℝ) / N - δ| := by
        rw [← abs_neg ((Nat.count (Q Cp r) N : ℝ) / N - δ)]
        exact (le_of_eq (by ring_nf)).trans (abs_add_le _ _)
    _ < ε := by linarith

end GSDens

namespace GSLink
open Finset Filter Topology GSFund GSEven GSMoment GSDens ZMod

theorem chi8_sq_nat (d : ℕ) : ((χ₈ (d : ZMod 8) : ℤ) : ℂ) * ((χ₈ (d : ZMod 8) : ℤ) : ℂ) =
    if d % 2 = 1 then 1 else 0 := by
  rw [χ₈_nat_eq_if_mod_eight]
  by_cases h : d % 2 = 0
  · simp [h]
  · have h' : d % 2 = 1 := by omega
    rw [if_neg h, if_pos h']; split_ifs <;> simp

/-- `(d | r²) = 1` if `gcd(d, r) = 1`, else `0`. -/
theorem kron_sq_nat (d : ℕ) {r : ℕ} (hr : 0 < r) :
    kron d (r * r) = if Nat.Coprime d r then 1 else 0 := by
  rw [kron_mul _ hr.ne' hr.ne']
  unfold kron
  set v := r.factorization 2
  set r' := r / 2 ^ v
  have hr' : r' ≠ 0 := (Nat.ordCompl_pos 2 hr.ne').ne'
  haveI : NeZero r' := ⟨hr'⟩
  have e : r = 2 ^ v * r' := (Nat.ordProj_mul_ordCompl_eq_self r 2).symm
  have hsq : ∀ (A B : ℂ), A ^ v * B * (A ^ v * B) = (A * A) ^ v * (B * B) := by intro A B; ring
  push_cast
  rw [hsq, chi8_sq_nat]
  have hJ : ((jacobiSym d r' : ℤ) : ℂ) * ((jacobiSym d r' : ℤ) : ℂ) = if Nat.Coprime d r' then 1 else 0 := by
    by_cases hc : Nat.Coprime d r'
    · have : jacobiSym d r' ^ 2 = 1 := jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hc)
      rw [if_pos hc, ← Int.cast_mul, ← sq, this]; simp
    · have : jacobiSym d r' = 0 := jacobiSym.eq_zero_iff_not_coprime.2 (by rw [Int.gcd_natCast_natCast]; exact hc)
      rw [if_neg hc, this]; simp
  rw [hJ]
  have hiff : Nat.Coprime d r ↔ (v = 0 ∨ d % 2 = 1) ∧ Nat.Coprime d r' := by
    rw [e, Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩
      by_cases hv : v = 0
      · left; exact hv
      · right; have := (Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hv) d 2).1 h1
        exact Nat.odd_iff.1 ((Nat.coprime_two_right).1 this)
    · rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩
      rcases h1 with h | h
      · rw [h]; simp
      · exact Nat.Coprime.pow_right _ ((Nat.coprime_two_right).2 (Nat.odd_iff.2 h))
  by_cases hc : Nat.Coprime d r
  · rw [if_pos hc]
    obtain ⟨h1, h2⟩ := hiff.1 hc
    rw [if_pos h2, mul_one]
    rcases h1 with h | h
    · rw [h, pow_zero]
    · rw [if_pos h, one_pow]
  · rw [if_neg hc]
    by_cases h2 : Nat.Coprime d r'
    · rw [if_pos h2, mul_one]
      have hv : v ≠ 0 ∧ d % 2 ≠ 1 := by
        by_contra h; apply hc; apply hiff.2; refine ⟨?_, h2⟩; by_cases hv : v = 0
        · exact Or.inl hv
        · right; by_contra h'; exact h ⟨hv, h'⟩
      rw [if_neg hv.2, zero_pow hv.1]
    · rw [if_neg h2, mul_zero]

theorem kron_neg_sq_nat (d : ℕ) {r : ℕ} (hr : 0 < r) :
    kron (-(d:ℤ)) (r * r) = kron d (r * r) := by
  unfold kron
  have hm : ((-(d:ℤ) : ℤ) : ZMod 8) = (-1 : ZMod 8) * (d : ZMod 8) := by push_cast; ring
  have h1 : χ₈ (-1 : ZMod 8) = 1 := by decide
  rw [hm, map_mul, h1, one_mul, show (-(d:ℤ)) = -1 * d by ring, jacobiSym.mul_left]
  set m := r * r / 2 ^ (r * r).factorization 2
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos 2 (Nat.mul_pos hr hr).ne').ne'
  -- `m` is a square, so `J(-1 | m) = 1`
  have hmsq : m = (r / 2 ^ r.factorization 2) * (r / 2 ^ r.factorization 2) := Nat.ordCompl_mul r r 2
  have hJ : jacobiSym (-1) m = 1 := by
    rw [hmsq, jacobiSym.mul_right' _ (Nat.ordCompl_pos 2 hr.ne').ne' (Nat.ordCompl_pos 2 hr.ne').ne', ← sq,
      jacobiSym.sq_one (by simp)]
  rw [hJ]; push_cast; ring

/-- No odd square factor and not divisible by 4 ⇔ squarefree. -/
theorem sqf_iff (m : ℕ) : Squarefree m ↔ ¬ 4 ∣ m ∧ Odf m := by
  constructor
  · intro h
    refine ⟨fun h4 => ?_, fun e he1 _ he => ?_⟩
    · have := h 2 (by simpa using h4); simp at this
    · have := h e (by simpa [sq] using he); rw [Nat.isUnit_iff] at this; omega
  · rintro ⟨h4, ho⟩
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpp
    by_cases h2 : p = 2
    · subst h2; exact h4 (by simpa using hpp)
    · exact ho p hp.one_lt (hp.odd_of_ne_two h2) (by simpa [sq] using hpp)

theorem Odf_four (m : ℕ) : Odf (4 * m) ↔ Odf m := by
  constructor
  · intro h e h1 h2 he; exact h e h1 h2 (Dvd.dvd.mul_left he 4)
  · intro h e h1 h2 he
    apply h e h1 h2
    have hc : Nat.Coprime (e ^ 2) 4 := by
      rw [show (4:ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow 2 2 ((Nat.coprime_two_right).2 h2)
    exact hc.dvd_of_dvd_mul_left he

def CpPos (t : ℕ) : Prop := t = 1 ∨ t = 5 ∨ t = 9 ∨ t = 13 ∨ t = 8 ∨ t = 12
def CpNeg (t : ℕ) : Prop := t = 3 ∨ t = 7 ∨ t = 11 ∨ t = 15 ∨ t = 4 ∨ t = 8

theorem fundPos_iff (d : ℕ) : fundPos d ↔ CpPos (d % 16) ∧ Odf d := by
  unfold fundPos CpPos
  constructor
  · rintro (⟨hs, h4⟩ | ⟨⟨m, rfl⟩, hs, hm⟩)
    · exact ⟨by omega, ((sqf_iff d).1 hs).2⟩
    · rw [Nat.mul_div_cancel_left _ (by norm_num)] at hs hm
      exact ⟨by omega, (Odf_four m).2 ((sqf_iff m).1 hs).2⟩
  · rintro ⟨hc, ho⟩
    by_cases h1 : d % 4 = 1
    · left; exact ⟨(sqf_iff d).2 ⟨by omega, ho⟩, h1⟩
    · right
      obtain ⟨m, rfl⟩ : 4 ∣ d := by omega
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
      exact ⟨dvd_mul_right _ _, (sqf_iff m).2 ⟨by omega, (Odf_four m).1 ho⟩, by omega⟩

theorem fundNeg_iff (d : ℕ) : fundNeg d ↔ CpNeg (d % 16) ∧ Odf d := by
  unfold fundNeg CpNeg
  constructor
  · rintro (⟨hs, h4⟩ | ⟨⟨m, rfl⟩, hs, hm⟩)
    · exact ⟨by omega, ((sqf_iff d).1 hs).2⟩
    · rw [Nat.mul_div_cancel_left _ (by norm_num)] at hs hm
      exact ⟨by omega, (Odf_four m).2 ((sqf_iff m).1 hs).2⟩
  · rintro ⟨hc, ho⟩
    by_cases h1 : d % 4 = 3
    · left; exact ⟨(sqf_iff d).2 ⟨by omega, ho⟩, h1⟩
    · right
      obtain ⟨m, rfl⟩ : 4 ∣ d := by omega
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
      exact ⟨dvd_mul_right _ _, (sqf_iff m).2 ⟨by omega, (Odf_four m).1 ho⟩, by omega⟩

end GSLink

namespace GSUncond
open Finset Filter Topology GSFund GSEven GSMoment GSDens GSLink

theorem CpPos0 : ¬ CpPos 0 := by simp [CpPos]
theorem CpNeg0 : ¬ CpNeg 0 := by simp [CpNeg]

open Classical in
theorem sum_eq_count (F : ℕ → Prop) [DecidablePred F] (Cp : ℕ → Prop) (hC0 : ¬ Cp 0)
    (hF : ∀ d, F d ↔ Cp (d % 16) ∧ Odf d) (χ : ℕ → ℕ → ℂ) {r : ℕ} (hr : 0 < r)
    (hχ : ∀ d, χ d (r * r) = if Nat.Coprime d r then 1 else 0) (x : ℕ) :
    ∑ d ∈ Ioc 0 x, (if F d then χ d (r * r) else 0) = ((Nat.count (Q Cp r) (x + 1) : ℕ) : ℂ) := by
  have hpt : ∀ d, (if F d then χ d (r * r) else 0) = if Q Cp r d then (1:ℂ) else 0 := by
    intro d
    have hq : Q Cp r d ↔ F d ∧ Nat.Coprime d r := by rw [hF]; unfold Q; tauto
    rw [hχ]
    by_cases h1 : F d <;> by_cases h2 : Nat.Coprime d r <;> simp [h1, h2, hq]
  rw [sum_congr rfl (fun d _ => hpt d), sum_boole, Nat.count_eq_card_filter_range]
  congr 2
  ext d
  simp only [mem_filter, mem_Ioc, mem_range]
  constructor
  · rintro ⟨⟨_, h⟩, hq⟩; exact ⟨by omega, hq⟩
  · rintro ⟨h, hq⟩
    refine ⟨⟨Nat.pos_of_ne_zero ?_, by omega⟩, hq⟩
    rintro rfl; exact hC0 (by simpa using hq.1)

theorem shift_lim (f : ℕ → ℕ) (hf : ∀ x, f (x + 1) ≤ f x + 1) (hf' : ∀ x, f x ≤ f (x + 1)) (δ : ℝ)
    (h : Tendsto (fun x : ℕ => (f x : ℝ) / x) atTop (𝓝 δ)) :
    Tendsto (fun x : ℕ => ‖((f (x + 1) : ℕ) : ℂ) - (δ : ℂ) * x‖ / x) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℕ => ((x:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun x : ℕ => |(f x : ℝ) / x - δ| + ((x:ℝ))⁻¹) atTop (𝓝 0) := by
    have := ((h.sub_const δ).abs).add hinv; simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hg
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hxp : (0:ℝ) < x := by exact_mod_cast hx
  have e1 : ((f (x + 1) : ℕ) : ℂ) - (δ : ℂ) * x = (((f (x + 1) : ℝ) - δ * x : ℝ) : ℂ) := by push_cast; ring
  rw [e1, Complex.norm_real, Real.norm_eq_abs]
  have e2 : (f x : ℝ) / x - δ = ((f x : ℝ) - δ * x) / x := by field_simp
  rw [e2, abs_div, abs_of_pos hxp]
  have a1 : (f (x + 1) : ℝ) ≤ f x + 1 := by exact_mod_cast hf x
  have a2 : (f x : ℝ) ≤ f (x + 1) := by exact_mod_cast hf' x
  have key : |(f (x + 1) : ℝ) - δ * x| ≤ |(f x : ℝ) - δ * x| + 1 := by
    rw [abs_le]; constructor <;> cases abs_cases ((f x : ℝ) - δ * x) <;> linarith
  calc _ ≤ (|(f x : ℝ) - δ * x| + 1) / x := div_le_div_of_nonneg_right key hxp.le
    _ = _ := by rw [add_div, one_div]

open Classical in
theorem count_succ_le (p : ℕ → Prop) (x : ℕ) : Nat.count p (x + 1) ≤ Nat.count p x + 1 := by
  rw [Nat.count_succ]; split_ifs <;> omega

open Classical in
theorem count_le_succ (p : ℕ → Prop) (x : ℕ) : Nat.count p x ≤ Nat.count p (x + 1) := by
  rw [Nat.count_succ]; omega

/-- Density of `{d : Cp(d mod 16), gcd(d, r) = 1, no odd square factor}`. -/
noncomputable def dens (Cp : ℕ → Prop) (hC0 : ¬ Cp 0) (r : ℕ) : ℝ :=
  if h : 0 < r then Classical.choose (Q_density Cp hC0 r h) else 0

open Classical in
/-- Generic unconditional moment limit. -/
theorem moment_uncond (F : ℕ → Prop) [DecidablePred F] (Cp : ℕ → Prop) (hC0 : ¬ Cp 0)
    (hF : ∀ d, F d ↔ Cp (d % 16) ∧ Odf d) (χ : ℕ → ℕ → ℂ)
    (hχ : ∀ d r, 0 < r → χ d (r * r) = if Nat.Coprime d r then 1 else 0)
    (hprod : ∀ d (k : ℕ) (f : Fin k → ℕ), (∀ i, f i ≠ 0) → χ d (∏ i, f i) = ∏ i, χ d (f i))
    (HGS : ∀ x n, 1 < n → ¬ IsSquare n → ‖∑ d ∈ Ioc 0 x, (if F d then χ d n else 0)‖ ≤ GSKron.GSB n x)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) (k : ℕ) :
    Tendsto (fun x : ℕ => ((x:ℂ))⁻¹ *
        ∑ d ∈ Ioc 0 x, (if F d then (∑ p ∈ P, a p * χ d p) ^ k else 0)) atTop
      (𝓝 (∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
          (∏ i, a (f i)) * (dens Cp hC0 (Nat.sqrt (∏ i, f i)) : ℂ))) := by
  set c : ℕ → ℂ := fun n => (dens Cp hC0 (Nat.sqrt n) : ℂ)
  set R : ℕ → ℕ → ℝ := fun n x => if IsSquare n ∧ 0 < n then
    ‖∑ d ∈ Ioc 0 x, (if F d then χ d n else 0) - c n * x‖ else 0
  apply lim_of_bound _ _ _ (fun x => moment_generic F χ hprod P hP a k x c (fun n => R n x) (fun n => GSKron.GSB n x)
    (fun n hn hs => by simp only [R, if_pos (And.intro hs hn)]; exact le_rfl) (HGS x))
  simp_rw [sum_div]
  rw [show (0:ℝ) = ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P), 0 by simp]
  apply tendsto_finsetSum; intro f _
  simp_rw [mul_div_assoc]
  rw [show (0:ℝ) = ‖∏ i, a (f i)‖ * 0 by simp]
  apply Tendsto.const_mul
  split_ifs with hsq
  · set n := ∏ i, f i
    by_cases hn : 0 < n
    · simp only [R, if_pos (And.intro hsq hn)]
      obtain ⟨r, hr⟩ := hsq
      have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hr; omega)
      rw [hr]
      simp only [c, Nat.sqrt_eq]
      simp_rw [sum_eq_count F Cp hC0 hF χ hr0 (hχ · r hr0)]
      have hd : dens Cp hC0 r = Classical.choose (Q_density Cp hC0 r hr0) := by simp [dens, hr0]
      rw [hd]
      exact shift_lim (Nat.count (Q Cp r)) (count_succ_le _) (count_le_succ _) _
        (Classical.choose_spec (Q_density Cp hC0 r hr0))
    · have h0 : ∀ x, R n x = 0 := fun x => by simp only [R]; rw [if_neg (fun h => hn h.2)]
      simp_rw [h0, zero_div]; exact tendsto_const_nhds
  · exact GSB_div _

/-- **Unconditional moments, positive fundamental discriminants.** For finite `P ⊂ ℕ>0`, weights `a`,
`S_D = Σ_{p∈P} a_p (D|p)`: `(1/x) Σ_{0<D≤x fund.} S_D^k → Σ_{f∈P^k, ∏f=□} (∏ a_{f i}) δ₊(√∏f)`,
`δ₊(r)` the natural density of positive fundamental discriminants coprime to `r`. -/
theorem moment_pos_unconditional (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) (k : ℕ) :
    Tendsto (fun x : ℕ => ((x:ℂ))⁻¹ *
        ∑ d ∈ Ioc 0 x, (if fundPos d then (∑ p ∈ P, a p * kron d p) ^ k else 0)) atTop
      (𝓝 (∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
          (∏ i, a (f i)) * (dens CpPos CpPos0 (Nat.sqrt (∏ i, f i)) : ℂ))) :=
  moment_uncond fundPos CpPos CpPos0 fundPos_iff (fun d n => kron d n)
    (fun d r hr => kron_sq_nat d hr) (fun d k f hf => kron_prod d f hf)
    (fun x n h1 hs => GSKron.gs_kron_pos h1 hs x) P hP a k

/-- **Unconditional moments, negative fundamental discriminants** (`D = -d`). -/
theorem moment_neg_unconditional (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) (k : ℕ) :
    Tendsto (fun x : ℕ => ((x:ℂ))⁻¹ *
        ∑ d ∈ Ioc 0 x, (if fundNeg d then (∑ p ∈ P, a p * kron (-(d:ℤ)) p) ^ k else 0)) atTop
      (𝓝 (∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
          (∏ i, a (f i)) * (dens CpNeg CpNeg0 (Nat.sqrt (∏ i, f i)) : ℂ))) :=
  moment_uncond fundNeg CpNeg CpNeg0 fundNeg_iff (fun d n => kron (-(d:ℤ)) n)
    (fun d r hr => by rw [kron_neg_sq_nat d hr]; exact kron_sq_nat d hr)
    (fun d k f hf => kron_prod _ f hf)
    (fun x n h1 hs => GSKron.gs_kron_neg h1 hs x) P hP a k

end GSUncond

#print axioms GSUncond.moment_pos_unconditional
#print axioms GSUncond.moment_neg_unconditional
