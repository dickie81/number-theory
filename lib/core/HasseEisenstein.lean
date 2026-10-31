/-
# Hasse's bound for the curves `y² = x³ + D`: the Frobenius is an Eisenstein integer of norm `q`

Plain statement. Let `𝔽_q` be a finite field of characteristic neither `2` nor `3`, `D ∈ 𝔽_q` nonzero, and `E` the
elliptic curve `y² = x³ + D` over `𝔽_q`, as Mathlib's `WeierstrassCurve` with its points `E.toAffine.Point`, the point
at infinity included. Write `#E(𝔽_q) = q + 1 − a`.
* If `q ≡ 2 (mod 3)`, then `a = 0` (`card_points_of_mod_three_eq_two`).
* If `q ≡ 1 (mod 3)`, then `a = 2u − v` for integers `u` and `v` with `u² − uv + v² = q` (`exists_eisenstein_trace`).
  So `a` is the trace of the Eisenstein integer `π = u + vω`, `ω = e^{2πi/3}`, of norm `q`: the Frobenius is a point
  of the lattice `ℤ[ω]` on the circle of radius `√q`.
* In both cases `|a| ≤ 2√q` (`abs_trace_le`): Hasse's bound, the Riemann hypothesis for these curves.
No hypothesis beyond the characteristic.

Mathlib defines this `a` in the local factor `1 − aT + qT²` of the L-function of a Weierstrass curve
(`WeierstrassCurve.localPolynomial`) but does not prove Hasse's bound, whose general proof needs isogenies. For these
curves the Frobenius is a Jacobi sum, as in Gauss's and Jacobi's counts:
* `#E(𝔽_q) = 1 + Σ_x (χ₂(x³ + D) + 1)`, with the quadratic character `χ₂` counting square roots
  (`quadraticChar_card_sqrts`).
* If `q ≡ 2 (mod 3)`, cubing permutes `𝔽_q` (`cube_bijective`), so the sum of `χ₂(x³ + D)` is the sum of `χ₂`, `0`.
* If `q ≡ 1 (mod 3)`, a character `χ₃` of order 3 counts cube roots: `#{x : x³ = u} = 1 + χ₃(u) + χ₃(u)²`
  (`card_cube_roots`). Then `Σ_x χ₂(x³ + D) = εJ + conj(εJ)`, where `J = J(χ₃, χ₂)` and `ε = χ₃(−D)χ₂(D)`
  (`sum_eq_add_star`), and `|J|² = q` (Mathlib's `jacobiSum_mul_jacobiSum_inv`). The values of the two characters lie
  in `ℤ[ω]`, so `−εJ = u + vω` (`isEis_jacobiSum`).

This is the rank-two case of the research direction in `docs/ball-conjecture.md`.
-/
import Mathlib

open Finset Complex

namespace HasseEisenstein

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The curve and its points -/

/-- The curve `y² = x³ + D`. -/
def curve (D : F) : WeierstrassCurve F := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := D }

omit [Fintype F] [DecidableEq F] in
lemma equation_iff (D x y : F) : (curve D).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + D := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curve]

omit [Fintype F] [DecidableEq F] in
lemma Δ_curve (D : F) : (curve D).Δ = -432 * D ^ 2 := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

variable (hF2 : ringChar F ≠ 2) (hF3 : ringChar F ≠ 3)

omit [DecidableEq F] in
include hF2 hF3 in
lemma Δ_ne_zero {D : F} (hD : D ≠ 0) : (curve D).Δ ≠ 0 := by
  obtain ⟨n, hpF, -⟩ := FiniteField.card F (ringChar F)
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have h3 : (3 : F) ≠ 0 := fun h => hF3 <| (Nat.prime_dvd_prime_iff_eq hpF Nat.prime_three).1 <|
    (CharP.cast_eq_zero_iff F (ringChar F) 3).1 (by exact_mod_cast h)
  rw [Δ_curve, show (432 : F) = 2 ^ 4 * 3 ^ 3 by norm_num]
  exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3))) (pow_ne_zero 2 hD)

omit [DecidableEq F] in
include hF2 hF3 in
lemma nonsingular_iff {D : F} (hD : D ≠ 0) (x y : F) :
    (curve D).toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + D :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (W := (curve D).toAffine)
    (Δ_ne_zero hF2 hF3 hD)).symm.trans (equation_iff D x y)

omit [DecidableEq F] in
/-- The points of `y² = x³ + D`: the point at infinity, and the solutions. -/
def pointEquiv {D : F} (hD : D ≠ 0) :
    (curve D).toAffine.Point ≃ Option {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + D} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), (nonsingular_iff hF2 hF3 hD x y).1 h⟩
  invFun
    | none => .zero
    | some xy => .some xy.1.1 xy.1.2 ((nonsingular_iff hF2 hF3 hD _ _).2 xy.2)
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | ⟨⟨x, y⟩, h⟩) <;> rfl

include hF2 hF3 in
lemma card_points {D : F} (hD : D ≠ 0) :
    Nat.card (curve D).toAffine.Point = (univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 + D)).card + 1 := by
  rw [Nat.card_congr (pointEquiv hF2 hF3 hD), Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_subtype]

include hF2 in
/-- The affine points counted with the quadratic character. -/
lemma card_solutions (D : F) :
    ((univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 + D)).card : ℤ) =
      ∑ x : F, (quadraticChar F (x ^ 3 + D) + 1) := by
  rw [card_filter, ← univ_product_univ, sum_product]
  push_cast
  refine sum_congr rfl fun x _ => ?_
  rw [← quadraticChar_card_sqrts hF2, Set.toFinset_ofPred, card_filter]
  push_cast
  rfl

/-! ## `q ≡ 2 (mod 3)`: cubing permutes `𝔽_q` -/

omit [DecidableEq F] in
lemma cube_bijective (h3 : Fintype.card F % 3 = 2) : Function.Bijective (fun x : F => x ^ 3) := by
  have hq1 := Fintype.one_lt_card (α := F)
  have key : ∀ x : F, x ^ (3 * ((2 * Fintype.card F - 1) / 3)) = x := by
    intro x
    have e : 3 * ((2 * Fintype.card F - 1) / 3) = Fintype.card F + (Fintype.card F - 1) := by omega
    rw [e, pow_add, FiniteField.pow_card, ← pow_succ', Nat.sub_add_cancel hq1.le, FiniteField.pow_card]
  refine Function.bijective_iff_has_inverse.2
    ⟨fun x => x ^ ((2 * Fintype.card F - 1) / 3), fun x => ?_, fun x => ?_⟩
  · dsimp only
    rw [← pow_mul, key]
  · dsimp only
    rw [← pow_mul, mul_comm, key]

include hF2 in
lemma sum_quadraticChar_cube_add (h3 : Fintype.card F % 3 = 2) (D : F) :
    ∑ x : F, quadraticChar F (x ^ 3 + D) = 0 := by
  rw [Fintype.sum_bijective _ (cube_bijective h3) (fun x => quadraticChar F (x ^ 3 + D))
    (fun u => quadraticChar F (u + D)) (fun _ => rfl), ← quadraticChar_sum_zero hF2]
  exact Fintype.sum_equiv (Equiv.addRight D) _ _ (fun _ => rfl)

include hF2 hF3 in
/-- **`y² = x³ + D` has `q + 1` points when `q ≡ 2 (mod 3)`.** -/
theorem card_points_of_mod_three_eq_two (h3 : Fintype.card F % 3 = 2) {D : F} (hD : D ≠ 0) :
    Nat.card (curve D).toAffine.Point = Fintype.card F + 1 := by
  have h := card_solutions hF2 D
  rw [sum_add_distrib, sum_quadraticChar_cube_add hF2 h3 D, sum_const, card_univ] at h
  rw [card_points hF2 hF3 hD]
  have h' : (univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 + D)).card = Fintype.card F := by
    simpa using h
  rw [h']

/-! ## `q ≡ 1 (mod 3)`: the Frobenius as a Jacobi sum -/

/-- The quadratic character of `𝔽_q` with complex values. -/
noncomputable abbrev chi2 : MulChar F ℂ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

lemma chi2_apply (a : F) : (chi2 a : ℂ) = (quadraticChar F a : ℂ) := rfl

lemma chi2_isQuadratic : (chi2 (F := F)).IsQuadratic := (quadraticChar_isQuadratic F).comp _

include hF2 in
lemma chi2_ne_one : chi2 (F := F) ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).2 (quadraticChar_ne_one hF2)

omit [DecidableEq F] in
lemma exists_cubic (h3 : Fintype.card F % 3 = 1) : ∃ χ : MulChar F ℂ, orderOf χ = 3 :=
  MulChar.exists_mulChar_orderOf F (by omega) (Complex.isPrimitiveRoot_exp 3 (by norm_num))

section Cubic

variable {χ : MulChar F ℂ} (hχ : orderOf χ = 3)
include hχ

omit [Fintype F] [DecidableEq F] in
lemma pow_three_eq_one : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ

omit [Fintype F] [DecidableEq F] in
lemma ne_one : χ ≠ 1 := fun h => by rw [h, orderOf_one] at hχ; norm_num at hχ

omit [Fintype F] [DecidableEq F] in
lemma apply_pow_three {a : F} (ha : a ≠ 0) : χ a ^ 3 = 1 := by
  rw [← MulChar.pow_apply' χ (by norm_num), pow_three_eq_one hχ, MulChar.one_apply (isUnit_iff_ne_zero.2 ha)]

omit [Fintype F] [DecidableEq F] in
lemma inv_eq_sq : χ⁻¹ = χ ^ 2 := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ', pow_three_eq_one hχ]

omit [DecidableEq F] in
/-- A character of order three takes the value `1` only at cubes. -/
lemma exists_cube_of_apply_eq_one {c : F} (hc : c ≠ 0) (h1 : χ c = 1) : ∃ α : F, α ^ 3 = c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  have hpow : ∀ n : ℕ, χ ((g ^ n : Fˣ) : F) = χ (g : F) ^ n := fun n => by
    rw [Units.val_pow_eq_pow_val, map_pow]
  have hw1 : χ (g : F) ≠ 1 := by
    intro hw
    refine ne_one hχ (MulChar.eq_one_iff.2 fun a => ?_)
    obtain ⟨m, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg a)
    rw [hpow, hw, one_pow]
  have hord : orderOf (χ (g : F)) = 3 := orderOf_eq_prime (apply_pow_three hχ g.ne_zero) hw1
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 c hc))
  have hcn : χ c = χ (g : F) ^ n := by
    rw [← hpow, hn, Units.val_mk0]
  rw [hcn, ← orderOf_dvd_iff_pow_eq_one, hord] at h1
  obtain ⟨k, rfl⟩ := h1
  refine ⟨(g : F) ^ k, ?_⟩
  rw [← pow_mul, mul_comm, ← Units.val_pow_eq_pow_val, hn, Units.val_mk0]

/-- **Cube roots counted by a character of order three.** -/
lemma card_cube_roots (h3 : Fintype.card F % 3 = 1) (c : F) :
    ((univ.filter (fun x : F => x ^ 3 = c)).card : ℂ) = 1 + χ c + χ c ^ 2 := by
  by_cases hc : c = 0
  · subst hc
    have h0 : univ.filter (fun x : F => x ^ 3 = 0) = {0} := by
      ext x; simp
    rw [h0, card_singleton, MulChar.map_zero]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 (G := Fˣ) (by rw [Fintype.card_units]; omega)
  have hζ : IsPrimitiveRoot (u : F) 3 := IsPrimitiveRoot.coe_units_iff.2 (hu ▸ IsPrimitiveRoot.orderOf u)
  have hcard : (univ.filter (fun x : F => x ^ 3 = c)).card = Multiset.card (Polynomial.nthRoots 3 c) := by
    rw [← Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup hc)]
    congr 1
    ext x
    simp [Polynomial.mem_nthRoots (by norm_num : 0 < 3)]
  rw [hcard, hζ.card_nthRoots c]
  split_ifs with hcube
  · obtain ⟨α, rfl⟩ := hcube
    have hα : α ≠ 0 := fun h => hc (by simp [h])
    rw [map_pow, apply_pow_three hχ hα]
    norm_num
  · have hz3 := apply_pow_three hχ hc
    have hz1 : χ c ≠ 1 := fun h => hcube (exists_cube_of_apply_eq_one hχ hc h)
    have : (χ c - 1) * (1 + χ c + χ c ^ 2) = 0 := by linear_combination hz3
    rw [Nat.cast_zero, eq_comm]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hz1)

end Cubic

/-- A sum over `𝔽_q` of a function of `x³`, by the number of cube roots. -/
lemma sum_cube (f : F → ℂ) :
    ∑ x : F, f (x ^ 3) = ∑ u : F, ((univ.filter (fun x : F => x ^ 3 = u)).card : ℂ) * f u := by
  rw [← sum_fiberwise univ (fun x : F => x ^ 3) (fun x => f (x ^ 3))]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2]), sum_const, nsmul_eq_mul]

omit [DecidableEq F] in
/-- The twisted sum `Σ_u ψ(u)φ(u + D)` is a Jacobi sum. -/
lemma sum_mul_apply_add (ψ φ : MulChar F ℂ) {D : F} (hD : D ≠ 0) :
    ∑ u : F, ψ u * φ (u + D) = ψ (-D) * φ D * jacobiSum ψ φ := by
  rw [jacobiSum, mul_sum]
  symm
  refine Fintype.sum_bijective (fun t => -D * t) (mulLeft_bijective₀ _ (neg_ne_zero.2 hD)) _ _ fun t => ?_
  rw [map_mul ψ, show -D * t + D = D * (1 - t) by ring, map_mul φ]
  ring

omit [DecidableEq F] in
lemma star_jacobiSum (ψ φ : MulChar F ℂ) : star (jacobiSum ψ φ) = jacobiSum ψ⁻¹ φ⁻¹ := by
  simp only [jacobiSum, star_sum, star_mul', MulChar.star_apply']

/-- `|ε| = 1`. -/
lemma unit_mul_star (χ : MulChar F ℂ) {D : F} (hD : D ≠ 0) :
    χ (-D) * chi2 D * star (χ (-D) * chi2 D) = 1 := by
  have hu : ∀ (ψ : MulChar F ℂ) {a : F}, a ≠ 0 → ψ a * star (ψ a) = 1 := fun ψ a ha => by
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (isUnit_iff_ne_zero.2 ha)]
  rw [star_mul']
  calc χ (-D) * chi2 D * (star (χ (-D)) * star (chi2 D))
      = (χ (-D) * star (χ (-D))) * (chi2 D * star (chi2 D)) := by ring
    _ = 1 := by rw [hu χ (neg_ne_zero.2 hD), hu chi2 hD, one_mul]

include hF2 in
/-- `|J|² = q`. -/
lemma jacobiSum_mul_star {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    jacobiSum χ chi2 * star (jacobiSum χ chi2) = Fintype.card F := by
  have hprod : χ * chi2 ≠ 1 := by
    intro h
    have hsq : χ ^ 2 = 1 := by
      rw [eq_inv_of_mul_eq_one_left h, chi2_isQuadratic.inv, chi2_isQuadratic.sq_eq_one]
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [hχ] at this
    norm_num at this
  have hchar : ringChar ℂ ≠ ringChar F := by
    obtain ⟨n, hpF, -⟩ := FiniteField.card F (ringChar F)
    rw [ringChar.eq_zero]; exact hpF.ne_zero.symm
  rw [star_jacobiSum, jacobiSum_mul_jacobiSum_inv hchar (ne_one hχ) (chi2_ne_one hF2) hprod]

include hF2 in
/-- **The character sum of `y² = x³ + D` is `εJ + conj(εJ)`**, `J = J(χ₃, χ₂)`, `ε = χ₃(−D)χ₂(D)`. -/
lemma sum_eq_add_star (h3 : Fintype.card F % 3 = 1) {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {D : F}
    (hD : D ≠ 0) :
    ∑ x : F, chi2 (x ^ 3 + D) =
      χ (-D) * chi2 D * jacobiSum χ chi2 + star (χ (-D) * chi2 D * jacobiSum χ chi2) := by
  rw [sum_cube (fun u => chi2 (u + D))]
  simp only [card_cube_roots hχ h3, add_mul, one_mul, sum_add_distrib]
  have h0 : ∑ u : F, chi2 (u + D) = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one (χ := (chi2 : MulChar F ℂ)) (chi2_ne_one hF2)]
    exact Fintype.sum_equiv (Equiv.addRight D) _ _ (fun _ => rfl)
  have h2 : ∑ u : F, χ u ^ 2 * chi2 (u + D) = (χ ^ 2) (-D) * chi2 D * jacobiSum (χ ^ 2) chi2 := by
    rw [← sum_mul_apply_add _ _ hD]
    exact sum_congr rfl fun u _ => by rw [MulChar.pow_apply' χ (by norm_num)]
  rw [h0, zero_add, sum_mul_apply_add _ _ hD, h2, star_mul', star_mul', star_jacobiSum, MulChar.star_apply',
    MulChar.star_apply', inv_eq_sq hχ, chi2_isQuadratic.inv]

/-! ## The Eisenstein integers `ℤ[ω]` in `ℂ` -/

/-- `ω = e^{2πi/3}`. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))

lemma ω_prim : IsPrimitiveRoot ω 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)

lemma ω_sq : ω ^ 2 = -1 - ω := by
  have h := ω_prim.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
  linear_combination h

lemma ω_mul_star : ω * star ω = 1 := by
  have h := Complex.norm_eq_one_of_pow_eq_one ω_prim.pow_eq_one (by norm_num)
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  norm_num

lemma star_ω : star ω = -1 - ω := by
  have hne : ω ≠ 0 := ω_prim.ne_zero (by norm_num)
  refine mul_left_cancel₀ hne ?_
  rw [ω_mul_star]
  linear_combination ω_sq

/-- `z ∈ ℤ[ω]`. -/
def IsEis (z : ℂ) : Prop := ∃ u v : ℤ, z = u + v * ω

lemma IsEis.intCast (n : ℤ) : IsEis n := ⟨n, 0, by simp⟩

lemma IsEis.zero : IsEis 0 := ⟨0, 0, by simp⟩

lemma IsEis.add {z w : ℂ} (hz : IsEis z) (hw : IsEis w) : IsEis (z + w) := by
  obtain ⟨a, b, rfl⟩ := hz; obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a + c, b + d, by push_cast; ring⟩

lemma IsEis.mul {z w : ℂ} (hz : IsEis z) (hw : IsEis w) : IsEis (z * w) := by
  obtain ⟨a, b, rfl⟩ := hz; obtain ⟨c, d, rfl⟩ := hw
  refine ⟨a * c - b * d, a * d + b * c - b * d, ?_⟩
  push_cast
  linear_combination (b * d : ℂ) * ω_sq

lemma IsEis.neg {z : ℂ} (hz : IsEis z) : IsEis (-z) := by
  simpa using (IsEis.intCast (-1)).mul hz

/-- A cube root of unity lies in `ℤ[ω]`. -/
lemma isEis_of_pow_three {z : ℂ} (hz : z ^ 3 = 1) : IsEis z := by
  obtain ⟨i, hi, rfl⟩ := ω_prim.eq_pow_of_pow_eq_one hz
  interval_cases i
  · exact ⟨1, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩
  · exact ⟨-1, -1, by rw [ω_sq]; push_cast; ring⟩

omit [Fintype F] [DecidableEq F] in
lemma isEis_apply {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (a : F) : IsEis (χ a) := by
  by_cases ha : a = 0
  · rw [ha, MulChar.map_zero]; exact IsEis.zero
  · exact isEis_of_pow_three (apply_pow_three hχ ha)

lemma isEis_chi2 (a : F) : IsEis (chi2 a) := by
  rw [chi2_apply]; exact IsEis.intCast _

lemma isEis_jacobiSum {χ : MulChar F ℂ} (hχ : orderOf χ = 3) : IsEis (jacobiSum χ chi2) := by
  rw [jacobiSum]
  exact Finset.sum_induction _ IsEis (fun _ _ => IsEis.add) IsEis.zero
    fun t _ => (isEis_apply hχ t).mul (isEis_chi2 _)

/-- The norm and the trace of `u + vω`. -/
lemma norm_trace (u v : ℤ) :
    ((u : ℂ) + v * ω) * star ((u : ℂ) + v * ω) = ((u ^ 2 - u * v + v ^ 2 : ℤ) : ℂ) ∧
      (u : ℂ) + v * ω + star ((u : ℂ) + v * ω) = ((2 * u - v : ℤ) : ℂ) := by
  have hs : star ((u : ℂ) + v * ω) = u + v * (-1 - ω) := by
    rw [star_add, star_mul', star_ω]
    simp
  rw [hs]
  constructor
  · push_cast; linear_combination (-(v : ℂ) ^ 2) * ω_sq
  · push_cast; ring

include hF2 hF3 in
/-- **The Frobenius of `y² = x³ + D` is an Eisenstein integer of norm `q`** when `q ≡ 1 (mod 3)`: there are integers
`u`, `v` with `u² − uv + v² = q` and `q + 1 − #E(𝔽_q) = 2u − v`, the trace of `u + vω`. -/
theorem exists_eisenstein_trace (h3 : Fintype.card F % 3 = 1) {D : F} (hD : D ≠ 0) :
    ∃ u v : ℤ, u ^ 2 - u * v + v ^ 2 = Fintype.card F ∧
      (Fintype.card F : ℤ) + 1 - Nat.card (curve D).toAffine.Point = 2 * u - v := by
  obtain ⟨χ, hχ⟩ := exists_cubic h3
  set π : ℂ := -(χ (-D) * chi2 D * jacobiSum χ chi2) with hπ
  have hEis : IsEis π :=
    ((((isEis_apply hχ (-D)).mul (isEis_chi2 D)).mul (isEis_jacobiSum hχ))).neg
  obtain ⟨u, v, huv⟩ := hEis
  obtain ⟨hnorm, htrace⟩ := norm_trace u v
  rw [← huv] at hnorm htrace
  refine ⟨u, v, ?_, ?_⟩
  · have hN : π * star π = Fintype.card F := by
      rw [hπ, star_neg, neg_mul_neg, star_mul', mul_mul_mul_comm, unit_mul_star χ hD, one_mul,
        jacobiSum_mul_star hF2 hχ]
    exact_mod_cast hnorm.symm.trans hN
  · have hsum := sum_eq_add_star hF2 h3 hχ hD
    have hcount := card_solutions hF2 D
    rw [card_points hF2 hF3 hD]
    have hC : ((univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 + D)).card : ℂ) =
        Fintype.card F + ∑ x : F, chi2 (x ^ 3 + D) := by
      have := congrArg (fun n : ℤ => (n : ℂ)) hcount
      simp only [Int.cast_natCast] at this
      rw [this]
      push_cast
      rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, add_comm]
      simp
    have key : (Fintype.card F : ℂ) + 1 -
        (((univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 + D)).card : ℂ) + 1) = 2 * (u : ℂ) - v := by
      rw [hC, hsum]
      push_cast at htrace
      rw [← htrace, hπ, star_neg]
      ring
    exact_mod_cast key

include hF2 hF3 in
/-- **Hasse's bound for `y² = x³ + D`**: `|q + 1 − #E(𝔽_q)| ≤ 2√q`, the Riemann hypothesis for these curves. -/
theorem abs_trace_le {D : F} (hD : D ≠ 0) :
    |(Fintype.card F : ℝ) + 1 - Nat.card (curve D).toAffine.Point| ≤ 2 * Real.sqrt (Fintype.card F) := by
  have hq3 : Fintype.card F % 3 = 1 ∨ Fintype.card F % 3 = 2 := by
    obtain ⟨n, hpF, hcard⟩ := FiniteField.card F (ringChar F)
    have h0 : Fintype.card F % 3 ≠ 0 := fun h => by
      have h3 : 3 ∣ ringChar F ^ (n : ℕ) := hcard ▸ Nat.dvd_of_mod_eq_zero h
      exact hF3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpF).1 (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    omega
  have h4q : 2 * Real.sqrt (Fintype.card F) = Real.sqrt (4 * Fintype.card F) := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [h4q]
  rcases hq3 with h1 | h2
  · obtain ⟨u, v, hn, ht⟩ := exists_eisenstein_trace hF2 hF3 h1 hD
    refine Real.abs_le_sqrt ?_
    have ht' : (Fintype.card F : ℝ) + 1 - Nat.card (curve D).toAffine.Point = 2 * u - v := by exact_mod_cast ht
    have hn' : (u : ℝ) ^ 2 - u * v + v ^ 2 = Fintype.card F := by exact_mod_cast hn
    rw [ht']
    nlinarith [sq_nonneg (v : ℝ)]
  · rw [card_points_of_mod_three_eq_two hF2 hF3 h2 hD]
    push_cast
    simp only [sub_self, abs_zero]
    exact Real.sqrt_nonneg _

end HasseEisenstein

#print axioms HasseEisenstein.card_points_of_mod_three_eq_two
#print axioms HasseEisenstein.exists_eisenstein_trace
#print axioms HasseEisenstein.abs_trace_le
