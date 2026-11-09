/-
# Gauss's count of `x³ + y³ = 1` modulo `p`

Plain statement. For a prime `p ≡ 1 (mod 3)` and any `4p = L² + 27M²` with `L ≡ 1 (mod 3)`, the congruence
`x³ + y³ ≡ 1 (mod p)` has exactly `p − 2 + L` solutions `(x, y)` (`card_eq`). For `p = 7`, `28 = 1 + 27` and the six
solutions are `(0, 1), (0, 2), (0, 4), (1, 0), (2, 0), (4, 0)`; for `p = 13`, `52 = 25 + 27` with `L = −5`, and there
are again six. For a prime `p ≢ 1 (mod 3)` there are `p` solutions (`card_eq_of_mod_three_ne_one`).
* **Cube roots counted by a character** (`card_cube_roots`): over a field with `q ≡ 1 (mod 3)` elements, a
  character `χ ≠ 1` with `χ³ = 1` has `#{x : x³ = c} = 1 + χ(c) + χ(c)²` for every `c`, `c = 0` included.
* **The Jacobi-sum count** (`card_eq_jacobiSum`): grouping the solutions by `x³` (`card_eq_sum`) and expanding,
  the count is `q − 2 + J(χ, χ) + J(χ̄, χ̄)`. The cross terms are `J(χ, χ̄) = −χ(−1) = −1` (Mathlib's
  `jacobiSum_nontrivial_inv`).
* **At a primary element** (`card_eq_trace`): for `π = a + bω ≡ 1 (mod 3)` of prime norm `p ≠ 3`, the cubic
  residue character modulo `(π)` has `J = −π` (`Eis.jacobiSum_eq_neg`), so the count is `p − 2 − (2a − b)`, with
  `2a − b = π + π̄` the trace of `π`. The element `π = −(L + 3M)/2 − 3Mω` of `CubicBinomial.choose_modEq` has
  trace `−L`.
* **With the binomial coefficient** (`card_modEq`): Jacobi's `C(2k, k) ≡ −L (mod p)`, `k = (p − 1)/3`
  (`CubicBinomial.choose_modEq`), makes the count `≡ −2 − C(2k, k) (mod p)`, a congruence with no `L` in it.
* **The projective curve** (`card_proj_eq`, `card_proj_eq_of_mod_three_ne_one`): the points of `X³ + Y³ = Z³` at
  infinity are the `(t : 1 : 0)` with `t³ = −1`, three of them when `p ≡ 1 (mod 3)` (`card_infinity_eq`) and one
  otherwise (`card_infinity_eq_of_mod_three_ne_one`). So the curve has `p + 1 + L`, resp. `p + 1`, points.
* **The Hasse–Weil bound** (`abs_sub_le`): the number `N` of projective points has `|p + 1 − N| ≤ 2√p` at every
  prime, since `L² ≤ 4p`. This is the Riemann hypothesis for the curve over `𝔽_p`, as `HasseEisenstein.abs_trace_le`
  is for `y² = x³ + D`.
C. F. Gauss, *Disquisitiones Arithmeticae* (1801), §358; K. Ireland and M. Rosen, *A Classical Introduction to
Modern Number Theory*, Chapter 8, §3. A. Weil, "Numbers of solutions of equations in finite fields", *Bull. Amer.
Math. Soc.* 55 (1949), the paper in which the Weil conjectures began, starts from this count of Gauss's.
-/
import Mathlib
import CubicBinomial

open NumberField Ideal

namespace FermatCubicCount

open Eis

/-! ### Cube roots counted by a cubic character -/

/-- A character with `χ³ = 1` has cube roots of unity as its values at units. -/
theorem apply_pow_three {F R : Type*} [Field F] [CommRing R] {χ : MulChar F R} (hχ3 : χ ^ 3 = 1)
    {a : F} (ha : a ≠ 0) : χ a ^ 3 = 1 := by
  rw [← MulChar.pow_apply' χ (by norm_num), hχ3, MulChar.one_apply (isUnit_iff_ne_zero.2 ha)]

/-- A character `χ ≠ 1` with `χ³ = 1` takes the value `1` only at cubes. -/
theorem exists_cube_of_apply_eq_one {F R : Type*} [Field F] [Fintype F] [CommRing R] {χ : MulChar F R}
    (hχ3 : χ ^ 3 = 1) (hχ1 : χ ≠ 1) {c : F} (hc : c ≠ 0) (h1 : χ c = 1) : ∃ α : F, α ^ 3 = c := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  have hpow : ∀ n : ℕ, χ ((g ^ n : Fˣ) : F) = χ (g : F) ^ n := fun n => by
    rw [Units.val_pow_eq_pow_val, map_pow]
  have hw1 : χ (g : F) ≠ 1 := by
    intro hw
    refine hχ1 (MulChar.eq_one_iff.2 fun a => ?_)
    obtain ⟨m, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg a)
    rw [hpow, hw, one_pow]
  have hord : orderOf (χ (g : F)) = 3 := orderOf_eq_prime (apply_pow_three hχ3 g.ne_zero) hw1
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 c hc))
  have hcn : χ c = χ (g : F) ^ n := by
    rw [← hpow, hn, Units.val_mk0]
  rw [hcn, ← orderOf_dvd_iff_pow_eq_one, hord] at h1
  obtain ⟨k, rfl⟩ := h1
  refine ⟨(g : F) ^ k, ?_⟩
  rw [← pow_mul, mul_comm, ← Units.val_pow_eq_pow_val, hn, Units.val_mk0]

/-- Over a field with `q ≡ 1 (mod 3)` elements, a nonzero cube has three cube roots. -/
theorem card_cube_roots_eq_three {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h3 : Fintype.card F % 3 = 1) {c : F} (hc : c ≠ 0) (hcube : ∃ α : F, α ^ 3 = c) :
    (Finset.univ.filter fun x : F => x ^ 3 = c).card = 3 := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 (G := Fˣ) (by rw [Fintype.card_units]; omega)
  have hζ : IsPrimitiveRoot (u : F) 3 := IsPrimitiveRoot.coe_units_iff.2 (hu ▸ IsPrimitiveRoot.orderOf u)
  have hcard : (Finset.univ.filter fun x : F => x ^ 3 = c).card = Multiset.card (Polynomial.nthRoots 3 c) := by
    rw [← Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup hc)]
    congr 1
    ext x
    simp [Polynomial.mem_nthRoots (by norm_num : 0 < 3)]
  rw [hcard, hζ.card_nthRoots c, ite_eq_left hcube]

/-- **Cube roots counted by a cubic character**: `#{x : x³ = c} = 1 + χ(c) + χ(c)²`, `c = 0` included. -/
theorem card_cube_roots {F R : Type*} [Field F] [Fintype F] [DecidableEq F] [CommRing R] [IsDomain R]
    {χ : MulChar F R} (hχ3 : χ ^ 3 = 1) (hχ1 : χ ≠ 1) (h3 : Fintype.card F % 3 = 1) (c : F) :
    ((Finset.univ.filter fun x : F => x ^ 3 = c).card : R) = 1 + χ c + χ c ^ 2 := by
  by_cases hc : c = 0
  · subst hc
    have h0 : Finset.univ.filter (fun x : F => x ^ 3 = 0) = {0} := by
      ext x; simp
    rw [h0, Finset.card_singleton, MulChar.map_zero]
    norm_num
  by_cases hcube : ∃ α : F, α ^ 3 = c
  · rw [card_cube_roots_eq_three h3 hc hcube]
    obtain ⟨α, rfl⟩ := hcube
    have hα : α ≠ 0 := fun h => hc (by rw [h, zero_pow three_ne_zero])
    rw [map_pow, apply_pow_three hχ3 hα]
    norm_num
  · have h0 : Finset.univ.filter (fun x : F => x ^ 3 = c) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun x _ h => hcube ⟨x, h⟩
    have hz1 : χ c ≠ 1 := fun h => hcube (exists_cube_of_apply_eq_one hχ3 hχ1 hc h)
    have : (χ c - 1) * (1 + χ c + χ c ^ 2) = 0 := by linear_combination apply_pow_three hχ3 hc
    rw [h0, Finset.card_empty, Nat.cast_zero, eq_comm]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hz1)

/-! ### The count as a sum of Jacobi sums -/

/-- Grouping the solutions of `x³ + y³ = 1` by `a = x³`. -/
theorem card_eq_sum {F : Type*} [CommRing F] [Fintype F] [DecidableEq F] :
    (Finset.univ.filter fun q : F × F => q.1 ^ 3 + q.2 ^ 3 = 1).card =
      ∑ a : F, (Finset.univ.filter fun x : F => x ^ 3 = a).card *
        (Finset.univ.filter fun y : F => y ^ 3 = 1 - a).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q : F × F => q.1 ^ 3) (t := Finset.univ)
    (fun _ _ => by simp)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.card_product]
  congr 1
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by linear_combination h1 - h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h1 + h2, h1⟩

/-- **The Jacobi-sum count**: for a character `χ ≠ 1` with `χ³ = 1` on a field with `q ≡ 1 (mod 3)`
elements, `x³ + y³ = 1` has `q − 2 + J(χ, χ) + J(χ̄, χ̄)` solutions. -/
theorem card_eq_jacobiSum {F R : Type*} [Field F] [Fintype F] [DecidableEq F] [CommRing R] [IsDomain R]
    {χ : MulChar F R} (hχ3 : χ ^ 3 = 1) (hχ1 : χ ≠ 1) (h3 : Fintype.card F % 3 = 1) :
    ((Finset.univ.filter fun q : F × F => q.1 ^ 3 + q.2 ^ 3 = 1).card : R) =
      Fintype.card F - 2 + jacobiSum χ χ + jacobiSum χ⁻¹ χ⁻¹ := by
  have hinv : χ⁻¹ = χ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hχ3])
  have hsq : ∀ a : F, χ a ^ 2 = χ⁻¹ a := fun a => by rw [hinv, MulChar.pow_apply' χ two_ne_zero]
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ1
  have hJ : jacobiSum χ χ⁻¹ = -1 := by
    rw [jacobiSum_nontrivial_inv hχ1, MulChar.val_neg_one_eq_one_of_odd_order (by decide) hχ3]
  have hJ' : jacobiSum χ⁻¹ χ = -1 := by rw [jacobiSum_comm, hJ]
  have hshift : ∀ ψ : MulChar F R, ψ ≠ 1 → ∑ a : F, ψ (1 - a) = 0 := fun ψ hψ => by
    rw [Fintype.sum_equiv (Equiv.subLeft 1) (fun a => ψ (1 - a)) ψ (fun a => rfl)]
    exact MulChar.sum_eq_zero_of_ne_one hψ
  have hexp : ∀ a : F, (1 + χ a + χ⁻¹ a) * (1 + χ (1 - a) + χ⁻¹ (1 - a)) =
      1 + (χ a + χ⁻¹ a) + (χ (1 - a) + χ⁻¹ (1 - a)) + (χ a * χ (1 - a) + χ⁻¹ a * χ⁻¹ (1 - a)) +
        (χ a * χ⁻¹ (1 - a) + χ⁻¹ a * χ (1 - a)) := fun a => by ring
  rw [card_eq_sum, Nat.cast_sum]
  simp only [Nat.cast_mul, card_cube_roots hχ3 hχ1 h3, hsq, hexp]
  unfold jacobiSum at hJ hJ' ⊢
  simp only [Finset.sum_add_distrib, MulChar.sum_eq_zero_of_ne_one hχ1, MulChar.sum_eq_zero_of_ne_one hinv1,
    hshift χ hχ1, hshift χ⁻¹ hinv1, hJ, hJ', Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-- The count is the same in isomorphic rings. -/
theorem card_ringEquiv {E F : Type*} [CommRing E] [CommRing F] [Fintype E] [Fintype F] [DecidableEq E]
    [DecidableEq F] (e : E ≃+* F) :
    (Finset.univ.filter fun q : E × E => q.1 ^ 3 + q.2 ^ 3 = 1).card =
      (Finset.univ.filter fun q : F × F => q.1 ^ 3 + q.2 ^ 3 = 1).card := by
  refine Finset.card_equiv ((e : E ≃ F).prodCongr (e : E ≃ F)) fun q => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodCongr_apply, Prod.map_fst,
    Prod.map_snd, RingEquiv.coe_toEquiv, ← map_pow, ← map_add]
  exact e.map_eq_one_iff.symm

/-! ### Gauss's count -/

/-- **Gauss's count at a primary element**: if `π = a + bω ≡ 1 (mod 3)` has prime norm `a² − ab + b² = p ≠ 3`,
then `x³ + y³ = 1` has `p − 2 − (2a − b)` solutions modulo `p`, `2a − b = π + π̄` the trace of `π`. -/
theorem card_eq_trace {a b : ℤ} (hπ : Primary ((a : 𝓞 K) + b * ω)) (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3)
    (hn : a ^ 2 - a * b + b ^ 2 = p) :
    ((Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card : ℤ) = p - 2 - (2 * a - b) := by
  classical
  have hp : p.Prime := Fact.out
  set π : 𝓞 K := (a : 𝓞 K) + b * ω with hπdef
  set P : Ideal (𝓞 K) := span {π} with hPdef
  have hNP : absNorm P = p := by rw [hPdef, CubicBinomial.absNorm_span_coords, hn, Int.natAbs_natCast]
  have hPm : P.IsMaximal := by
    have hprime : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hNP]; exact hp)
    have hne : P ≠ ⊥ := fun h => by rw [h, absNorm_bot] at hNP; exact hp.ne_zero hNP.symm
    exact hprime.isMaximal hne
  have hP3 : (3 : 𝓞 K) ∉ P := by
    intro h3
    have hd := Ideal.absNorm_dvd_absNorm_of_le
      ((Ideal.span_singleton_le_iff_mem _).2 (by exact_mod_cast h3 : ((3 : ℕ) : 𝓞 K) ∈ P))
    rw [absNorm_natCast_span_sq, hNP] at hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hd))
  have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
    rw [← hNP, absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have h3 : Fintype.card (𝓞 K ⧸ P) % 3 = 1 := by rw [CubicBinomial.card_eq P hP3]; omega
  have h := card_eq_jacobiSum (cubChar_pow_three P hP3) (cubChar_ne_one P hP3) h3
  rw [jacobiSum_inv_eq_cj P hP3, jacobiSum_eq_neg P hP3 hπ rfl, map_neg, hcard,
    ← card_ringEquiv (ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hp hcard)] at h
  have htr : π + cj π = ((2 * a - b : ℤ) : 𝓞 K) := by rw [hπdef, cj_coords]; push_cast; ring
  have hcast : (((Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card : ℤ) : 𝓞 K) =
      ((p - 2 - (2 * a - b) : ℤ) : 𝓞 K) := by
    rw [Int.cast_natCast, h, Int.cast_sub, ← htr]
    push_cast
    ring
  exact Int.cast_injective hcast

/-- **Gauss's count of `x³ + y³ = 1` (mod p)**: for a prime `p ≡ 1 (mod 3)` and every representation
`4p = L² + 27M²` with `L ≡ 1 (mod 3)`, the number of solutions is `p − 2 + L`. -/
theorem card_eq (p : ℕ) [Fact p.Prime] (hp1 : p % 3 = 1) {L M : ℤ}
    (hLM : 4 * (p : ℤ) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1) :
    ((Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card : ℤ) = p - 2 + L := by
  -- the primary element `π = −s − 3Mω`, `2s = L + 3M`, of `CubicBinomial.choose_modEq`
  obtain ⟨s, hs⟩ : ∃ s, L + 3 * M = 2 * s := by
    obtain ⟨l, hl | hl⟩ := Int.even_or_odd' L <;> obtain ⟨n, hn | hn⟩ := Int.even_or_odd' M
    · exact ⟨l + 3 * n, by rw [hl, hn]; ring⟩
    · exfalso
      subst hl hn
      have h4 : (4 : ℤ) ∣ 27 := ⟨p - l ^ 2 - 27 * n ^ 2 - 27 * n, by linear_combination (-1 : ℤ) * hLM⟩
      norm_num at h4
    · exfalso
      subst hl hn
      have h4 : (4 : ℤ) ∣ 1 := ⟨p - l ^ 2 - l - 27 * n ^ 2, by linear_combination (-1 : ℤ) * hLM⟩
      norm_num at h4
    · exact ⟨l + 3 * n + 2, by rw [hl, hn]; ring⟩
  obtain ⟨t, ht⟩ : ∃ t, -s - 1 = 3 * t := ⟨(-s - 1) / 3, by omega⟩
  have hπ : Primary (((-s : ℤ) : 𝓞 K) + ((-3 * M : ℤ) : 𝓞 K) * ω) :=
    ⟨(t : 𝓞 K) + (-M : 𝓞 K) * ω, by
      have e : (((-s - 1 : ℤ)) : 𝓞 K) = ((3 * t : ℤ) : 𝓞 K) := by rw [ht]
      push_cast at e ⊢
      linear_combination e⟩
  have hn : (-s) ^ 2 - (-s) * (-3 * M) + (-3 * M) ^ 2 = (p : ℤ) := by
    have h4 : 4 * ((-s) ^ 2 - (-s) * (-3 * M) + (-3 * M) ^ 2) = 4 * (p : ℤ) := by
      rw [hLM, show L = 2 * s - 3 * M by linarith]; ring
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4
  rw [card_eq_trace hπ p (by omega) hn]
  ring_nf
  linarith

/-- **The count modulo `p`, by Jacobi's binomial coefficient**: for a prime `p ≡ 1 (mod 3)`, `k = (p − 1)/3`,
the number of solutions of `x³ + y³ = 1` is `≡ −2 − C(2k, k) (mod p)`. -/
theorem card_modEq (p : ℕ) [Fact p.Prime] (hp1 : p % 3 = 1) :
    ((Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card : ℤ) ≡
      -2 - (((2 * ((p - 1) / 3)).choose ((p - 1) / 3) : ℕ) : ℤ) [ZMOD p] := by
  obtain ⟨L, M, hLM, hL⟩ := CubicBinomial.exists_rep Fact.out hp1
  have hc := Int.modEq_iff_dvd.1 (CubicBinomial.choose_modEq Fact.out hp1 hLM hL)
  rw [card_eq p hp1 hLM hL, Int.modEq_iff_dvd]
  convert hc.sub (dvd_refl (p : ℤ)) using 1
  ring

/-! ### `p ≢ 1 (mod 3)` -/

/-- For a prime `p ≢ 1 (mod 3)`, cubing permutes `ZMod p`. -/
theorem cube_bijective (p : ℕ) [Fact p.Prime] (hp1 : p % 3 ≠ 1) :
    Function.Bijective (fun x : ZMod p => x ^ 3) := by
  have hp : p.Prime := Fact.out
  have key : ∀ x : ZMod p, x ^ (3 * ((2 * p - 1) / 3)) = x := by
    intro x
    by_cases h3 : p = 3
    · subst h3
      exact ZMod.pow_card x
    · have h0 : p % 3 ≠ 0 := fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.dvd_of_mod_eq_zero h)).symm
      have e : 3 * ((2 * p - 1) / 3) = p + (p - 1) := by omega
      rw [e, pow_add, ZMod.pow_card, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, ZMod.pow_card]
  refine Function.bijective_iff_has_inverse.2 ⟨fun x => x ^ ((2 * p - 1) / 3), fun x => ?_, fun x => ?_⟩
  · dsimp only
    rw [← pow_mul, key]
  · dsimp only
    rw [← pow_mul, mul_comm, key]

/-- When cubing is a bijection, every element has exactly one cube root. -/
theorem card_cube_roots_eq_one {F : Type*} [Monoid F] [Fintype F] [DecidableEq F]
    (hbij : Function.Bijective (fun x : F => x ^ 3)) (c : F) :
    (Finset.univ.filter fun x : F => x ^ 3 = c).card = 1 := by
  obtain ⟨y, hy, huniq⟩ := hbij.existsUnique c
  rw [Finset.card_eq_one]
  refine ⟨y, Finset.ext fun x => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => huniq x h, fun h => by rw [h]; exact hy⟩

/-- **`p` solutions when `p ≢ 1 (mod 3)`**: cubing permutes `ZMod p`, so the count is that of `u + v = 1`. -/
theorem card_eq_of_mod_three_ne_one (p : ℕ) [Fact p.Prime] (hp1 : p % 3 ≠ 1) :
    (Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card = p := by
  rw [card_eq_sum]
  simp only [card_cube_roots_eq_one (cube_bijective p hp1), mul_one, Finset.sum_const, Finset.card_univ,
    ZMod.card, smul_eq_mul]

/-! ### The projective curve and the Hasse–Weil bound -/

/-- **Three points at infinity** `(t : 1 : 0)`, `t³ = −1`, when `p ≡ 1 (mod 3)`. -/
theorem card_infinity_eq (p : ℕ) [Fact p.Prime] (hp1 : p % 3 = 1) :
    (Finset.univ.filter fun t : ZMod p => t ^ 3 = -1).card = 3 :=
  card_cube_roots_eq_three (by rw [ZMod.card]; exact hp1) (neg_ne_zero.2 (one_ne_zero (α := ZMod p)))
    ⟨-1, Odd.neg_one_pow (by decide)⟩

/-- **One point at infinity** when `p ≢ 1 (mod 3)`. -/
theorem card_infinity_eq_of_mod_three_ne_one (p : ℕ) [Fact p.Prime] (hp1 : p % 3 ≠ 1) :
    (Finset.univ.filter fun t : ZMod p => t ^ 3 = -1).card = 1 :=
  card_cube_roots_eq_one (cube_bijective p hp1) (-1)

/-- **The projective Fermat cubic** `X³ + Y³ = Z³` has `p + 1 + L` points over `𝔽_p`, `p ≡ 1 (mod 3)`. -/
theorem card_proj_eq (p : ℕ) [Fact p.Prime] (hp1 : p % 3 = 1) {L M : ℤ}
    (hLM : 4 * (p : ℤ) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1) :
    ((Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card +
      (Finset.univ.filter fun t : ZMod p => t ^ 3 = -1).card : ℤ) = p + 1 + L := by
  rw [card_eq p hp1 hLM hL, card_infinity_eq p hp1]
  push_cast
  ring

/-- **The projective Fermat cubic** has `p + 1` points over `𝔽_p` when `p ≢ 1 (mod 3)`. -/
theorem card_proj_eq_of_mod_three_ne_one (p : ℕ) [Fact p.Prime] (hp1 : p % 3 ≠ 1) :
    (Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card +
      (Finset.univ.filter fun t : ZMod p => t ^ 3 = -1).card = p + 1 := by
  rw [card_eq_of_mod_three_ne_one p hp1, card_infinity_eq_of_mod_three_ne_one p hp1]

/-- **The Hasse–Weil bound for the Fermat cubic**: its number `N` of projective points over `𝔽_p` has
`|p + 1 − N| ≤ 2√p`, at every prime `p`. -/
theorem abs_sub_le (p : ℕ) [Fact p.Prime] :
    |(p : ℝ) + 1 - ((Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card +
      (Finset.univ.filter fun t : ZMod p => t ^ 3 = -1).card)| ≤ 2 * Real.sqrt p := by
  by_cases hp1 : p % 3 = 1
  · obtain ⟨L, M, hLM, hL⟩ := CubicBinomial.exists_rep Fact.out hp1
    have h := card_proj_eq p hp1 hLM hL
    have hR : ((Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card +
        (Finset.univ.filter fun t : ZMod p => t ^ 3 = -1).card : ℝ) = p + 1 + L := by exact_mod_cast h
    rw [hR, show (p : ℝ) + 1 - (p + 1 + L) = -L by ring, abs_neg]
    have hL2 : (L : ℝ) ^ 2 ≤ 4 * p := by exact_mod_cast (by nlinarith [sq_nonneg M] : L ^ 2 ≤ 4 * (p : ℤ))
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    linarith
  · have h := card_proj_eq_of_mod_three_ne_one p hp1
    have hR : ((Finset.univ.filter fun x : ZMod p × ZMod p => x.1 ^ 3 + x.2 ^ 3 = 1).card +
        (Finset.univ.filter fun t : ZMod p => t ^ 3 = -1).card : ℝ) = p + 1 := by exact_mod_cast h
    rw [hR, sub_self, abs_zero]
    positivity

end FermatCubicCount

#print axioms FermatCubicCount.card_cube_roots
#print axioms FermatCubicCount.card_eq_jacobiSum
#print axioms FermatCubicCount.card_eq_trace
#print axioms FermatCubicCount.card_eq
#print axioms FermatCubicCount.card_modEq
#print axioms FermatCubicCount.card_eq_of_mod_three_ne_one
#print axioms FermatCubicCount.card_infinity_eq
#print axioms FermatCubicCount.card_infinity_eq_of_mod_three_ne_one
#print axioms FermatCubicCount.card_proj_eq
#print axioms FermatCubicCount.card_proj_eq_of_mod_three_ne_one
#print axioms FermatCubicCount.abs_sub_le
