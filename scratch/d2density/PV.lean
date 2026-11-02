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

#print axioms PolyaVinogradov.polya_vinogradov
