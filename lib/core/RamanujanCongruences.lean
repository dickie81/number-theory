/-
# Ramanujan's partition congruences, from Jacobi's cube and Euler's pentagonal theorem

Plain statement. Let `p(n)` be the number of partitions of `n` (Mathlib's `Nat.Partition n`), and for `k ≥ 1` let
`p₋ₖ(n)` be the number of `k`-coloured partitions of `n` (`k`-tuples of partitions of total size `n`), the coefficient
of `Xⁿ` in `P^k` with `P = Σ p(n)Xⁿ` (`colouredPartitions`).
* **Ramanujan's congruences** (`ramanujan_five`, `ramanujan_seven`): `p(5n + 4) ≡ 0 (mod 5)` and
  `p(7n + 5) ≡ 0 (mod 7)` for every `n` (S. Ramanujan, "Some properties of p(n), the number of partitions of n",
  Proc. Cambridge Philos. Soc. 19 (1919)).
* **Coloured partitions**, by the same argument (`coloured_two_five`, `coloured_four_five`, `coloured_four_seven`,
  `coloured_six_seven`): `p₋₂(5n + 2)`, `p₋₂(5n + 3)` and `p₋₂(5n + 4)` are divisible by `5`; `p₋₄(5n + 3)` and
  `p₋₄(5n + 4)` by `5`; `p₋₄(7n + 2)`, `p₋₄(7n + 4)`, `p₋₄(7n + 5)` and `p₋₄(7n + 6)` by `7`; and `p₋₆(7n + 3)`,
  `p₋₆(7n + 4)` and `p₋₆(7n + 6)` by `7`.
* **Three-coloured partitions modulo `9`** (`coloured_three_nine`): `p₋₃(3n + 2) ≡ 0 (mod 9)`.
The method (`coeff_P_pow_eq_zero`). With Euler's `E = ∏_{i ≥ 1}(1 − X^i)`, `P·E = 1` (`P_mul_E`, from Mathlib's
`Nat.Partition.hasProd_powerSeriesMk_card_restricted`), so `P^k·E^ℓ = E^{ℓ−k}` for `k ≤ ℓ`. Modulo a prime `ℓ`,
`E^ℓ ≡ ∏(1 − X^{ℓi})` by Frobenius, on the finite truncations of the product (`map_trunc_pow`): a series with constant
term `1` supported on the multiples of `ℓ`. So if every coefficient of `E^{ℓ−k}` at the exponents `≡ r (mod ℓ)` is
divisible by `ℓ`, so is every coefficient of `P^k` there (`coeff_eq_zero_of_mul_supp`). The coefficients of `E` are
Euler's, from Mathlib's pentagonal number theorem (`PowerSeries.WithPiTopology.hasProd_one_sub_X_pow`): `±1` at the
pentagonal numbers `j(3j − 1)/2` and `0` elsewhere. Those of `E³` are Jacobi's, from the library's
`JacobiFourSquares.jacobi_cube`: `2·[Xᵐ]E³ = Σ_{T(j) = m}(2j + 1)(−1)^j` with `T(j) = j(j + 1)/2`
(`two_mul_coeff_cube`). The rest is a residue check modulo `ℓ`:
* `ℓ = 5`, `E⁴ = E·E³`: `j(3j − 1) + i(i + 1) ≡ 8 (mod 5)` forces `5 ∣ 2i + 1`, since `2` is not a square mod `5`;
* `ℓ = 7`, `E⁶ = (E³)²`: `i(i + 1) + l(l + 1) ≡ 10 (mod 7)` forces `7 ∣ 2i + 1`, since `−1` is not a square mod `7`;
* the triangular numbers are `0, 1, 3 (mod 5)` and `0, 1, 3, 6 (mod 7)`, `≡ 3 (mod 5)` and `≡ 6 (mod 7)` only when
  `ℓ ∣ 2i + 1`; the pentagonal numbers are `0, 1, 2 (mod 5)` and `0, 1, 2, 5 (mod 7)`.
* modulo `9`: `(1 − a)⁹ = (1 − a³)³` there (`one_sub_pow_nine`), so `E⁹ ≡ (∏(1 − X^{3i}))³`
  (`map_trunc_pow_nine`); and `T(j) + T(l) ≡ 2 (mod 3)` forces `T(j) ≡ T(l) ≡ 1`, that is `3 ∣ 2j + 1` and
  `3 ∣ 2l + 1`, so the coefficients of `E⁶ = (E³)²` at the exponents `≡ 2 (mod 3)` are divisible by `9`
  (`cast_coeff_E_six`).
From Mathlib: the partitions, their generating function and the pentagonal number theorem. From the library: Jacobi's
cube (`JacobiFourSquares.jacobi_cube`) and its power-series tools.
Not reached: `p(11n + 6) ≡ 0 (mod 11)`, which needs Winquist's identity or modular forms.
-/
import Mathlib
import JacobiFourSquares

open PowerSeries PowerSeries.WithPiTopology Filter Topology JacobiFourSquares

noncomputable section

namespace RamanujanCongruences

/-! ## Euler's function and the partition generating function -/

/-- Euler's function `E = ∏_{i ≥ 1}(1 − X^i)`, which is Mathlib's pentagonal series. -/
abbrev E : ℤ⟦X⟧ := pentagonalSeries ℤ

/-- The generating function `P = Σ p(n)Xⁿ` of the partitions. -/
def P : ℤ⟦X⟧ := PowerSeries.mk fun n => (Fintype.card (Nat.Partition n) : ℤ)

/-- The number of `k`-coloured partitions of `n`, `k`-tuples of partitions of total size `n`: the coefficient of
`Xⁿ` in `P^k`. -/
def colouredPartitions (k n : ℕ) : ℤ := coeff n (P ^ k)

theorem hasProd_E : HasProd (fun i : ℕ => (1 - X ^ (i + 1) : ℤ⟦X⟧)) E := hasProd_one_sub_X_pow ℤ

/-- **Euler**: `P·E = 1`. -/
theorem P_mul_E : P * E = 1 := by
  have hP := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ => True)
  have hP' : HasProd (fun i : ℕ => ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) P := by
    convert hP using 1
    · funext i
      simp
    · unfold P
      congr 1
      funext n
      simp [Nat.Partition.restricted]
  have h := hP'.mul hasProd_E
  have h1 : (fun i : ℕ => (∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) * (1 - X ^ (i + 1))) = fun _ => 1 := by
    funext i
    simp_rw [pow_mul]
    exact tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  rw [h1] at h
  exact h.unique hasProd_one

/-! ## Jacobi's cube -/

theorem summable_cubeTerm : Summable cubeTerm :=
  summable_of_dvd T (fun _ => X_pow_dvd_monomial le_rfl _) finite_T

/-- **Jacobi's cube**: `E³ = Σ_j j(−1)^j X^{T(j)}`. -/
theorem E_cube : E ^ 3 = ∑' j, cubeTerm j := jacobi_cube hasProd_E summable_cubeTerm.hasSum

theorem hasSum_negOnePow : HasSum (fun j : ℤ => (monomial (T j) (j.negOnePow : ℤ) : ℤ⟦X⟧)) 0 := by
  obtain ⟨Z, hZ⟩ : Summable fun j : ℤ => (monomial (T j) (j.negOnePow : ℤ) : ℤ⟦X⟧) :=
    summable_of_dvd T (fun _ => X_pow_dvd_monomial le_rfl _) finite_T
  have h1 : HasSum (fun j : ℤ => (monomial (T j) (j.negOnePow : ℤ) : ℤ⟦X⟧)) (-Z) := by
    convert ((Equiv.subLeft (-1 : ℤ)).hasSum_iff.mpr hZ).neg using 1
    funext j
    simp only [Function.comp_apply, Equiv.subLeft_apply, T_neg]
    rw [Int.negOnePow_sub, Int.negOnePow_neg, Int.negOnePow_one]
    simp only [neg_mul, one_mul, Units.val_neg, map_neg, neg_neg]
  have h2 := hZ.unique h1
  have h3 : (2 : ℤ⟦X⟧) * Z = 0 := by linear_combination h2
  rwa [(mul_eq_zero.mp h3).resolve_left (by rw [← map_ofNat C 2]; exact C_ne_zero two_ne_zero)] at hZ

theorem hasSum_two_cube :
    HasSum (fun j : ℤ => (monomial (T j) ((2 * j + 1) * (j.negOnePow : ℤ)) : ℤ⟦X⟧)) (2 * E ^ 3) := by
  rw [E_cube]
  convert (summable_cubeTerm.hasSum.mul_left 2).add hasSum_negOnePow using 1
  · funext j
    rw [cubeTerm, monomial_eq, monomial_eq, monomial_eq]
    simp only [map_mul, map_add, map_ofNat, map_one]
    ring
  · ring

/-- `2·[Xᵐ]E³ = Σ_{T(j) = m}(2j + 1)(−1)^j`. -/
theorem two_mul_coeff_cube (m : ℕ) :
    2 * coeff m (E ^ 3) = ∑ j ∈ (finite_T m).toFinset,
      if m = T j then (2 * j + 1) * (j.negOnePow : ℤ) else 0 := by
  have h := coeff_of_hasSum hasSum_two_cube m (finite_T m).toFinset fun j hj => by
    rw [coeff_monomial, ite_eq_right]
    intro hm
    exact hj (by simp [hm])
  rw [← map_ofNat C 2, coeff_C_mul] at h
  rw [h]
  exact Finset.sum_congr rfl fun j _ => by rw [coeff_monomial]

/-- If `ℓ ∣ 2j + 1` whenever `T(j) = m`, and `2` is a unit modulo `ℓ`, then `ℓ ∣ [Xᵐ]E³`. -/
theorem cast_coeff_cube_eq_zero {ℓ : ℕ} (h2 : IsUnit (2 : ZMod ℓ)) {m : ℕ}
    (h : ∀ j : ℤ, T j = m → ((2 * j + 1 : ℤ) : ZMod ℓ) = 0) : ((coeff m (E ^ 3) : ℤ) : ZMod ℓ) = 0 := by
  have h1 := congrArg (Int.cast : ℤ → ZMod ℓ) (two_mul_coeff_cube m)
  rw [Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Finset.sum_eq_zero] at h1
  · exact h2.mul_right_eq_zero.mp h1
  · intro j _
    split_ifs with hj
    · rw [Int.cast_mul, h j hj.symm, zero_mul]
    · exact Int.cast_zero

/-- `[Xᵐ]E³ = 0` when `m` is not triangular. -/
theorem coeff_cube_eq_zero {m : ℕ} (h : ∀ j : ℤ, T j ≠ m) : coeff m (E ^ 3) = 0 := by
  have h1 := two_mul_coeff_cube m
  rw [Finset.sum_eq_zero fun j _ => ite_eq_right fun hj => h j hj.symm] at h1
  exact (mul_eq_zero.mp h1).resolve_left two_ne_zero

/-- `[Xᵐ]E = 0` when `m` is not pentagonal. -/
theorem coeff_E_eq_zero {m : ℕ} (h : ∀ j : ℤ, pentagonal j ≠ m) : coeff m E = 0 :=
  coeff_pentagonalSeries_eq_zero ℤ fun ⟨j, hj⟩ => h j hj

theorem cast_two_mul_pentagonal (ℓ : ℕ) (j : ℤ) :
    2 * ((pentagonal j : ℕ) : ZMod ℓ) = (j : ZMod ℓ) * (3 * j - 1) := by
  have := congrArg (Int.cast : ℤ → ZMod ℓ) (two_mul_natCast_pentagonal j)
  push_cast at this
  exact this

theorem cast_two_mul_T (ℓ : ℕ) (j : ℤ) : 2 * ((T j : ℕ) : ZMod ℓ) = (j : ZMod ℓ) * (j + 1) := by
  have := congrArg (Int.cast : ℤ → ZMod ℓ) (two_mul_T j)
  push_cast at this
  exact this

/-- The coefficients of `E³` at the exponents `≡ r (mod ℓ)` vanish modulo `ℓ`, from a residue check on `T`. -/
theorem cube_residue {ℓ r : ℕ} (h2 : IsUnit (2 : ZMod ℓ))
    (hkey : ∀ y : ZMod ℓ, y * (y + 1) = 2 * (r : ZMod ℓ) → 2 * y + 1 = 0) (m : ℕ) (hm : m % ℓ = r) :
    ((coeff m (E ^ 3) : ℤ) : ZMod ℓ) = 0 :=
  cast_coeff_cube_eq_zero h2 fun j hj => by
    have h1 := cast_two_mul_T ℓ j
    rw [hj, ← ZMod.natCast_mod, hm] at h1
    push_cast
    exact hkey _ h1.symm

/-- The coefficients of `E` at the exponents `≡ r (mod ℓ)` vanish, from a residue check on the pentagonal
numbers. -/
theorem pent_residue {ℓ r : ℕ} (hkey : ∀ x : ZMod ℓ, x * (3 * x - 1) ≠ 2 * (r : ZMod ℓ)) (m : ℕ)
    (hm : m % ℓ = r) : ((coeff m E : ℤ) : ZMod ℓ) = 0 := by
  rw [coeff_E_eq_zero fun j hj => hkey j ?_, Int.cast_zero]
  have h1 := cast_two_mul_pentagonal ℓ j
  rw [hj, ← ZMod.natCast_mod, hm] at h1
  exact h1.symm

/-! ## Series supported on the multiples of `ℓ` -/

/-- The power series `f` is supported on the multiples of `ℓ`. -/
def Supp {R : Type*} [CommRing R] (ℓ : ℕ) (f : R⟦X⟧) : Prop := ∀ j, ¬ ℓ ∣ j → coeff j f = 0

theorem supp_one {R : Type*} [CommRing R] (ℓ : ℕ) : Supp ℓ (1 : R⟦X⟧) := fun j hj => by
  rw [coeff_one, ite_eq_right]
  rintro rfl
  exact hj (dvd_zero ℓ)

theorem supp_mul {R : Type*} [CommRing R] {ℓ : ℕ} {f g : R⟦X⟧} (hf : Supp ℓ f) (hg : Supp ℓ g) :
    Supp ℓ (f * g) := by
  intro j hj
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases ha : ℓ ∣ p.1
  · rw [hg p.2 fun hb => hj (hp ▸ dvd_add ha hb), mul_zero]
  · rw [hf p.1 ha, zero_mul]

theorem supp_one_sub_X_pow {R : Type*} [CommRing R] (ℓ i : ℕ) : Supp ℓ (1 - X ^ (i * ℓ) : R⟦X⟧) := by
  intro j hj
  have h0 : j ≠ 0 := by
    rintro rfl
    exact hj (dvd_zero ℓ)
  have h1 : j ≠ i * ℓ := by
    rintro rfl
    exact hj (dvd_mul_left ℓ i)
  rw [map_sub, coeff_one, coeff_X_pow, ite_eq_right h0, ite_eq_right h1, sub_zero]

theorem supp_pow {R : Type*} [CommRing R] {ℓ : ℕ} {f : R⟦X⟧} (hf : Supp ℓ f) (k : ℕ) : Supp ℓ (f ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact supp_one ℓ
  | succ k ih =>
    rw [pow_succ]
    exact supp_mul ih hf

theorem supp_prod {R : Type*} [CommRing R] {ℓ : ℕ} (s : Finset ℕ) (f : ℕ → R⟦X⟧)
    (h : ∀ i ∈ s, Supp ℓ (f i)) : Supp ℓ (∏ i ∈ s, f i) :=
  Finset.prod_induction f (Supp ℓ) (fun _ _ => supp_mul) (supp_one ℓ) h

/-- **Division by a series supported on `ℓℕ`**: if `g` has constant term `1` and is supported on the multiples of
`ℓ`, and the coefficients of `f·g` vanish at the exponents `m ≤ n` with `m ≡ r (mod ℓ)`, then so does the
coefficient of `f` at `n ≡ r`. -/
theorem coeff_eq_zero_of_mul_supp {R : Type*} [CommRing R] {ℓ r : ℕ} {f g : R⟦X⟧} (hg0 : coeff 0 g = 1)
    (hg : Supp ℓ g) (n : ℕ) (h : ∀ m ≤ n, m % ℓ = r → coeff m (f * g) = 0) (hn : n % ℓ = r) :
    coeff n f = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have key := h n le_rfl hn
    rw [coeff_mul, Finset.sum_eq_single (n, 0)] at key
    · rwa [hg0, mul_one] at key
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases hb : ℓ ∣ p.2
      · obtain ⟨c, hc⟩ := hb
        have hb0 : p.2 ≠ 0 := fun h0 => hne (Prod.ext (by omega) h0)
        have ha : p.1 < n := by omega
        have har : p.1 % ℓ = r := by rw [← hn, ← hp, hc, Nat.add_mul_mod_self_left]
        rw [ih p.1 ha (fun m hm => h m (by omega)) har, zero_mul]
      · rw [hg p.2 hb, mul_zero]
    · intro hmem
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hmem

/-! ## Frobenius on the truncations of `E` -/

theorem exists_trunc (n : ℕ) : ∃ s : Finset ℕ, X ^ (n + 1) ∣ E - ∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧) := by
  have h : ∀ m ∈ Finset.range (n + 1), ∀ᶠ s in atTop,
      coeff m (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧)) = coeff m E :=
    fun m _ => coeff_prod_one_sub_X_pow_eventually_eq ℤ m
  obtain ⟨s, hs⟩ := ((eventually_all_finset _).mpr h).exists
  refine ⟨s, X_pow_dvd_iff.mpr fun m hm => ?_⟩
  rw [map_sub, hs m (Finset.mem_range.mpr hm), sub_self]

instance charP_powerSeries (ℓ : ℕ) : CharP (ZMod ℓ)⟦X⟧ ℓ := charP_of_injective_ringHom C_injective ℓ

/-- **Frobenius** on one factor: `(1 − X^{i+1})^ℓ = 1 − X^{(i+1)ℓ}` modulo a prime `ℓ`. -/
theorem one_sub_X_pow_pow (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    ((1 : (ZMod ℓ)⟦X⟧) - X ^ (i + 1)) ^ ℓ = 1 - X ^ ((i + 1) * ℓ) := by
  rw [sub_pow_char (p := ℓ), one_pow, ← pow_mul]

theorem coeff_zero_prod_one_sub {R : Type*} [CommRing R] {c : ℕ} (hc : c ≠ 0) (s : Finset ℕ) :
    coeff 0 (∏ i ∈ s, (1 - X ^ ((i + 1) * c) : R⟦X⟧)) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, map_prod]
  exact Finset.prod_eq_one fun i _ => by simp [hc]

/-- **Frobenius**: modulo a prime `ℓ`, `(∏_{i ∈ s}(1 − X^{i+1}))^ℓ = ∏_{i ∈ s}(1 − X^{(i+1)ℓ})`. -/
theorem map_trunc_pow (ℓ : ℕ) [Fact ℓ.Prime] (s : Finset ℕ) :
    (map (Int.castRingHom (ZMod ℓ)) (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧))) ^ ℓ =
      ∏ i ∈ s, (1 - X ^ ((i + 1) * ℓ) : (ZMod ℓ)⟦X⟧) := by
  rw [map_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_pow, map_X]
  exact one_sub_X_pow_pow ℓ i

/-! ## The method -/

/-- **The reduction.** Let `ℓ` be prime and `k ≤ ℓ`. If the coefficients of `E^{ℓ−k}` at the exponents `≡ r (mod ℓ)`
are divisible by `ℓ`, so are those of `P^k`. -/
theorem coeff_P_pow_eq_zero {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {k r : ℕ} (hk : k ≤ ℓ)
    (hE : ∀ m, m % ℓ = r → ((coeff m (E ^ (ℓ - k)) : ℤ) : ZMod ℓ) = 0) (n : ℕ) (hn : n % ℓ = r) :
    ((coeff n (P ^ k) : ℤ) : ZMod ℓ) = 0 := by
  obtain ⟨s, hs⟩ := exists_trunc n
  set Es : ℤ⟦X⟧ := ∏ i ∈ s, (1 - X ^ (i + 1)) with hEs
  have hPE : P ^ k * E ^ ℓ = E ^ (ℓ - k) := by
    have : E ^ ℓ = E ^ k * E ^ (ℓ - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
    rw [this, ← mul_assoc, ← mul_pow, P_mul_E, one_pow, one_mul]
  have hdvd : X ^ (n + 1) ∣ P ^ k * Es ^ ℓ - E ^ (ℓ - k) := by
    rw [← hPE, ← mul_sub]
    refine dvd_mul_of_dvd_right ?_ _
    rw [← neg_sub]
    exact dvd_neg.mpr (hs.trans (sub_dvd_pow_sub_pow E Es ℓ))
  have hg : map (Int.castRingHom (ZMod ℓ)) (Es ^ ℓ) = ∏ i ∈ s, (1 - X ^ ((i + 1) * ℓ) : (ZMod ℓ)⟦X⟧) := by
    rw [map_pow]
    exact map_trunc_pow ℓ s
  have hℓ0 : ℓ ≠ 0 := hℓ.out.ne_zero
  have key := coeff_eq_zero_of_mul_supp (r := r) (f := map (Int.castRingHom (ZMod ℓ)) (P ^ k))
    (g := map (Int.castRingHom (ZMod ℓ)) (Es ^ ℓ)) ?_ ?_ n ?_ hn
  · rwa [coeff_map, eq_intCast] at key
  · rw [hg]
    exact coeff_zero_prod_one_sub hℓ0 s
  · rw [hg]
    exact supp_prod s _ fun i _ => supp_one_sub_X_pow ℓ (i + 1)
  · intro m hm hmr
    rw [← map_mul, coeff_map, eq_intCast, coeff_eq_of_dvd hdvd (by omega)]
    exact hE m hmr

/-! ## The congruences -/

theorem fact_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem fact_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `j(3j − 1) + i(i + 1) ≡ 8 (mod 5)` forces `5 ∣ 2i + 1`: `2` is not a square modulo `5`. -/
theorem key_five : ∀ x y : ZMod 5, x * (3 * x - 1) + y * (y + 1) = 8 → 2 * y + 1 = 0 := by decide

/-- `i(i + 1) + l(l + 1) ≡ 10 (mod 7)` forces `7 ∣ 2i + 1`: `−1` is not a square modulo `7`. -/
theorem key_seven : ∀ x y : ZMod 7, x * (x + 1) + y * (y + 1) = 10 → 2 * x + 1 = 0 := by decide

theorem isUnit_two_five : IsUnit (2 : ZMod 5) := IsUnit.of_mul_eq_one 3 (by decide)

theorem isUnit_two_seven : IsUnit (2 : ZMod 7) := IsUnit.of_mul_eq_one 4 (by decide)

theorem card_partition_modEq {ℓ k : ℕ} [NeZero ℓ] (h : ((coeff k (P ^ 1) : ℤ) : ZMod ℓ) = 0) :
    Fintype.card (Nat.Partition k) ≡ 0 [MOD ℓ] := by
  rw [pow_one, P, coeff_mk, Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h
  exact Nat.modEq_zero_iff_dvd.mpr h

theorem coloured_modEq {ℓ k n : ℕ} [NeZero ℓ] (h : ((coeff n (P ^ k) : ℤ) : ZMod ℓ) = 0) :
    colouredPartitions k n ≡ 0 [ZMOD ℓ] := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact Int.modEq_zero_iff_dvd.mpr h

/-- **Ramanujan's congruence modulo `5`**: `p(5n + 4) ≡ 0 (mod 5)`. -/
theorem ramanujan_five (n : ℕ) : Fintype.card (Nat.Partition (5 * n + 4)) ≡ 0 [MOD 5] := by
  refine card_partition_modEq
    (coeff_P_pow_eq_zero (hℓ := fact_five) (ℓ := 5) (k := 1) (r := 4) (by norm_num) ?_ _ (by omega))
  intro m hm
  rw [show (5 - 1 : ℕ) = 1 + 3 from rfl, pow_add, pow_one, coeff_mul, Int.cast_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [Int.cast_mul]
  by_cases ha : ∃ i : ℤ, pentagonal i = p.1
  · obtain ⟨i, hi⟩ := ha
    rw [cast_coeff_cube_eq_zero isUnit_two_five fun j hj => ?_, mul_zero]
    have h1 := cast_two_mul_pentagonal 5 i
    have h2 := cast_two_mul_T 5 j
    have hm' : ((pentagonal i : ℕ) : ZMod 5) + ((T j : ℕ) : ZMod 5) = 4 := by
      rw [hi, hj, ← Nat.cast_add, hp, ← ZMod.natCast_mod, hm]
      rfl
    push_cast
    exact key_five (i : ZMod 5) (j : ZMod 5) (by rw [← h1, ← h2, ← mul_add, hm']; rfl)
  · rw [coeff_E_eq_zero fun i hi => ha ⟨i, hi⟩, Int.cast_zero, zero_mul]

/-- **Ramanujan's congruence modulo `7`**: `p(7n + 5) ≡ 0 (mod 7)`. -/
theorem ramanujan_seven (n : ℕ) : Fintype.card (Nat.Partition (7 * n + 5)) ≡ 0 [MOD 7] := by
  refine card_partition_modEq
    (coeff_P_pow_eq_zero (hℓ := fact_seven) (ℓ := 7) (k := 1) (r := 5) (by norm_num) ?_ _ (by omega))
  intro m hm
  rw [show (7 - 1 : ℕ) = 3 + 3 from rfl, pow_add, coeff_mul, Int.cast_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [Int.cast_mul]
  by_cases hb : ∃ l : ℤ, T l = p.2
  · obtain ⟨l, hl⟩ := hb
    rw [cast_coeff_cube_eq_zero isUnit_two_seven fun j hj => ?_, zero_mul]
    have h1 := cast_two_mul_T 7 j
    have h2 := cast_two_mul_T 7 l
    have hm' : ((T j : ℕ) : ZMod 7) + ((T l : ℕ) : ZMod 7) = 5 := by
      rw [hj, hl, ← Nat.cast_add, hp, ← ZMod.natCast_mod, hm]
      rfl
    push_cast
    exact key_seven (j : ZMod 7) (l : ZMod 7) (by rw [← h1, ← h2, ← mul_add, hm']; rfl)
  · rw [coeff_cube_eq_zero fun l hl => hb ⟨l, hl⟩, Int.cast_zero, mul_zero]

/-- **Two-coloured partitions modulo `5`**: `p₋₂(5n + 2)`, `p₋₂(5n + 3)` and `p₋₂(5n + 4)` are divisible by `5`. -/
theorem coloured_two_five (n : ℕ) :
    colouredPartitions 2 (5 * n + 2) ≡ 0 [ZMOD 5] ∧ colouredPartitions 2 (5 * n + 3) ≡ 0 [ZMOD 5] ∧
      colouredPartitions 2 (5 * n + 4) ≡ 0 [ZMOD 5] := by
  refine ⟨coloured_modEq ?_, coloured_modEq ?_, coloured_modEq ?_⟩
  · exact coeff_P_pow_eq_zero (hℓ := fact_five) (ℓ := 5) (k := 2) (r := 2) (by norm_num)
      (cube_residue isUnit_two_five (by decide)) _ (by omega)
  · exact coeff_P_pow_eq_zero (hℓ := fact_five) (ℓ := 5) (k := 2) (r := 3) (by norm_num)
      (cube_residue isUnit_two_five (by decide)) _ (by omega)
  · exact coeff_P_pow_eq_zero (hℓ := fact_five) (ℓ := 5) (k := 2) (r := 4) (by norm_num)
      (cube_residue isUnit_two_five (by decide)) _ (by omega)

/-- **Four-coloured partitions modulo `5`**: `p₋₄(5n + 3)` and `p₋₄(5n + 4)` are divisible by `5`. -/
theorem coloured_four_five (n : ℕ) :
    colouredPartitions 4 (5 * n + 3) ≡ 0 [ZMOD 5] ∧ colouredPartitions 4 (5 * n + 4) ≡ 0 [ZMOD 5] := by
  refine ⟨coloured_modEq ?_, coloured_modEq ?_⟩
  · exact coeff_P_pow_eq_zero (hℓ := fact_five) (ℓ := 5) (k := 4) (r := 3) (by norm_num)
      (fun m hm => by rw [show (5 - 4 : ℕ) = 1 from rfl, pow_one]; exact pent_residue (by decide) m hm) _
      (by omega)
  · exact coeff_P_pow_eq_zero (hℓ := fact_five) (ℓ := 5) (k := 4) (r := 4) (by norm_num)
      (fun m hm => by rw [show (5 - 4 : ℕ) = 1 from rfl, pow_one]; exact pent_residue (by decide) m hm) _
      (by omega)

/-- **Four-coloured partitions modulo `7`**: `p₋₄(7n + 2)`, `p₋₄(7n + 4)`, `p₋₄(7n + 5)` and `p₋₄(7n + 6)` are
divisible by `7`. -/
theorem coloured_four_seven (n : ℕ) :
    colouredPartitions 4 (7 * n + 2) ≡ 0 [ZMOD 7] ∧ colouredPartitions 4 (7 * n + 4) ≡ 0 [ZMOD 7] ∧
      colouredPartitions 4 (7 * n + 5) ≡ 0 [ZMOD 7] ∧ colouredPartitions 4 (7 * n + 6) ≡ 0 [ZMOD 7] := by
  refine ⟨coloured_modEq ?_, coloured_modEq ?_, coloured_modEq ?_, coloured_modEq ?_⟩
  · exact coeff_P_pow_eq_zero (hℓ := fact_seven) (ℓ := 7) (k := 4) (r := 2) (by norm_num)
      (cube_residue isUnit_two_seven (by decide)) _ (by omega)
  · exact coeff_P_pow_eq_zero (hℓ := fact_seven) (ℓ := 7) (k := 4) (r := 4) (by norm_num)
      (cube_residue isUnit_two_seven (by decide)) _ (by omega)
  · exact coeff_P_pow_eq_zero (hℓ := fact_seven) (ℓ := 7) (k := 4) (r := 5) (by norm_num)
      (cube_residue isUnit_two_seven (by decide)) _ (by omega)
  · exact coeff_P_pow_eq_zero (hℓ := fact_seven) (ℓ := 7) (k := 4) (r := 6) (by norm_num)
      (cube_residue isUnit_two_seven (by decide)) _ (by omega)

/-- **Six-coloured partitions modulo `7`**: `p₋₆(7n + 3)`, `p₋₆(7n + 4)` and `p₋₆(7n + 6)` are divisible by `7`. -/
theorem coloured_six_seven (n : ℕ) :
    colouredPartitions 6 (7 * n + 3) ≡ 0 [ZMOD 7] ∧ colouredPartitions 6 (7 * n + 4) ≡ 0 [ZMOD 7] ∧
      colouredPartitions 6 (7 * n + 6) ≡ 0 [ZMOD 7] := by
  refine ⟨coloured_modEq ?_, coloured_modEq ?_, coloured_modEq ?_⟩
  · exact coeff_P_pow_eq_zero (hℓ := fact_seven) (ℓ := 7) (k := 6) (r := 3) (by norm_num)
      (fun m hm => by rw [show (7 - 6 : ℕ) = 1 from rfl, pow_one]; exact pent_residue (by decide) m hm) _
      (by omega)
  · exact coeff_P_pow_eq_zero (hℓ := fact_seven) (ℓ := 7) (k := 6) (r := 4) (by norm_num)
      (fun m hm => by rw [show (7 - 6 : ℕ) = 1 from rfl, pow_one]; exact pent_residue (by decide) m hm) _
      (by omega)
  · exact coeff_P_pow_eq_zero (hℓ := fact_seven) (ℓ := 7) (k := 6) (r := 6) (by norm_num)
      (fun m hm => by rw [show (7 - 6 : ℕ) = 1 from rfl, pow_one]; exact pent_residue (by decide) m hm) _
      (by omega)

/-! ## Three-coloured partitions modulo `9` -/

/-- Modulo `9`, `(1 − a)⁹ = (1 − a³)³`: the difference is `9` times a polynomial in `a`. -/
theorem one_sub_pow_nine {R : Type*} [CommRing R] (h9 : (9 : R) = 0) (a : R) : (1 - a) ^ 9 = (1 - a ^ 3) ^ 3 := by
  have h : (1 - a) ^ 9 - (1 - a ^ 3) ^ 3 =
      9 * (-a + 4 * a ^ 2 - 9 * a ^ 3 + 14 * a ^ 4 - 14 * a ^ 5 + 9 * a ^ 6 - 4 * a ^ 7 + a ^ 8) := by ring
  rw [h9, zero_mul, sub_eq_zero] at h
  exact h

/-- Modulo `9`, `(∏_{i ∈ s}(1 − X^{i+1}))⁹ = (∏_{i ∈ s}(1 − X^{3(i+1)}))³`. -/
theorem map_trunc_pow_nine (s : Finset ℕ) :
    (PowerSeries.map (Int.castRingHom (ZMod 9)) (∏ i ∈ s, (1 - X ^ (i + 1) : ℤ⟦X⟧))) ^ 9 =
      (∏ i ∈ s, (1 - X ^ ((i + 1) * 3) : (ZMod 9)⟦X⟧)) ^ 3 := by
  have h9 : (9 : (ZMod 9)⟦X⟧) = 0 := by exact_mod_cast CharP.cast_eq_zero (ZMod 9)⟦X⟧ 9
  rw [map_prod, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_pow, map_X, one_sub_pow_nine h9, ← pow_mul]

theorem isUnit_two_three : IsUnit (2 : ZMod 3) := IsUnit.of_mul_eq_one 2 (by decide)

/-- `i(i + 1) + l(l + 1) ≡ 4 (mod 3)` forces `3 ∣ 2i + 1`. -/
theorem key_three : ∀ x y : ZMod 3, x * (x + 1) + y * (y + 1) = 4 → 2 * x + 1 = 0 := by decide

/-- If `T(j) + T(l) ≡ 2 (mod 3)`, then `3` divides `[X^{T(j)}]E³`. -/
theorem three_dvd_coeff_cube {a b m : ℕ} (hab : a + b = m) (hm : m % 3 = 2) {l : ℤ} (hl : T l = b) :
    (3 : ℤ) ∣ coeff a (E ^ 3) := by
  have key : ((coeff a (E ^ 3) : ℤ) : ZMod 3) = 0 := by
    refine cast_coeff_cube_eq_zero isUnit_two_three fun j hj => ?_
    have h1 := cast_two_mul_T 3 j
    have h2 := cast_two_mul_T 3 l
    have hm' : ((T j : ℕ) : ZMod 3) + ((T l : ℕ) : ZMod 3) = 2 := by
      rw [hj, hl, ← Nat.cast_add, hab, ← ZMod.natCast_mod, hm]
      rfl
    push_cast
    exact key_three (j : ZMod 3) (l : ZMod 3) (by rw [← h1, ← h2, ← mul_add, hm']; rfl)
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp key

/-- The coefficients of `E⁶ = (E³)²` at the exponents `≡ 2 (mod 3)` are divisible by `9`. -/
theorem cast_coeff_E_six {m : ℕ} (hm : m % 3 = 2) : ((coeff m (E ^ 6) : ℤ) : ZMod 9) = 0 := by
  rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, coeff_mul, Int.cast_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases ha : ∃ j : ℤ, T j = p.1
  · by_cases hb : ∃ l : ℤ, T l = p.2
    · obtain ⟨j, hj⟩ := ha
      obtain ⟨l, hl⟩ := hb
      obtain ⟨u, hu⟩ := three_dvd_coeff_cube hp hm hl
      obtain ⟨v, hv⟩ := three_dvd_coeff_cube ((add_comm p.2 p.1).trans hp) hm hj
      rw [hu, hv, show (3 * u * (3 * v) : ℤ) = 9 * (u * v) by ring, Int.cast_mul,
        show ((9 : ℤ) : ZMod 9) = 0 by decide, zero_mul]
    · rw [coeff_cube_eq_zero fun l hl => hb ⟨l, hl⟩, mul_zero, Int.cast_zero]
  · rw [coeff_cube_eq_zero fun j hj => ha ⟨j, hj⟩, zero_mul, Int.cast_zero]

/-- **Three-coloured partitions modulo `9`**: `p₋₃(3n + 2) ≡ 0 (mod 9)`. -/
theorem coloured_three_nine (n : ℕ) : colouredPartitions 3 (3 * n + 2) ≡ 0 [ZMOD 9] := by
  refine coloured_modEq ?_
  obtain ⟨s, hs⟩ := exists_trunc (3 * n + 2)
  set Es : ℤ⟦X⟧ := ∏ i ∈ s, (1 - X ^ (i + 1)) with hEs
  have hPE : P ^ 3 * E ^ 9 = E ^ 6 := by
    have : E ^ 9 = E ^ 3 * E ^ 6 := by rw [← pow_add]
    rw [this, ← mul_assoc, ← mul_pow, P_mul_E, one_pow, one_mul]
  have hdvd : X ^ (3 * n + 2 + 1) ∣ P ^ 3 * Es ^ 9 - E ^ 6 := by
    rw [← hPE, ← mul_sub]
    refine dvd_mul_of_dvd_right ?_ _
    rw [← neg_sub]
    exact dvd_neg.mpr (hs.trans (sub_dvd_pow_sub_pow E Es 9))
  have hg : PowerSeries.map (Int.castRingHom (ZMod 9)) (Es ^ 9) =
      (∏ i ∈ s, (1 - X ^ ((i + 1) * 3) : (ZMod 9)⟦X⟧)) ^ 3 := by
    rw [map_pow]
    exact map_trunc_pow_nine s
  have key := coeff_eq_zero_of_mul_supp (ℓ := 3) (r := 2) (f := PowerSeries.map (Int.castRingHom (ZMod 9)) (P ^ 3))
    (g := PowerSeries.map (Int.castRingHom (ZMod 9)) (Es ^ 9)) ?_ ?_ (3 * n + 2) ?_ (by omega)
  · rwa [coeff_map, eq_intCast] at key
  · rw [hg, coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply,
      coeff_zero_prod_one_sub (by norm_num) s, one_pow]
  · rw [hg]
    exact supp_pow (supp_prod s _ fun i _ => supp_one_sub_X_pow 3 (i + 1)) 3
  · intro m hm hmr
    rw [← map_mul, coeff_map, eq_intCast, coeff_eq_of_dvd hdvd (by omega)]
    exact cast_coeff_E_six hmr

end RamanujanCongruences

#print axioms RamanujanCongruences.P_mul_E
#print axioms RamanujanCongruences.coeff_P_pow_eq_zero
#print axioms RamanujanCongruences.ramanujan_five
#print axioms RamanujanCongruences.ramanujan_seven
#print axioms RamanujanCongruences.coloured_two_five
#print axioms RamanujanCongruences.coloured_four_five
#print axioms RamanujanCongruences.coloured_four_seven
#print axioms RamanujanCongruences.coloured_six_seven
#print axioms RamanujanCongruences.coloured_three_nine
