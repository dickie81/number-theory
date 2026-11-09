/-
# Ramanujan's congruences in four infinite families

Plain statement. With `p₋ₖ(n)` the number of `k`-coloured partitions of `n` (`RamanujanCongruences.colouredPartitions`)
and `ℓ` a prime, four families of congruences `p₋ₖ(n) ≡ 0 (mod ℓ)`, uniform in `ℓ`:
* **From `E`** (`family_one`): `k = ℓ − 1`, when `24n + 1` is not a square modulo `ℓ`.
* **From `E³`** (`family_three`): `k = ℓ − 3`, when `ℓ ∣ 8n + 1` or `8n + 1` is not a square modulo `ℓ`, for `ℓ ≥ 5`.
* **From `E⁴`** (`family_four`): `k = ℓ − 4`, when `ℓ ∣ 6n + 1`, for `ℓ ≡ 2 (mod 3)`, `ℓ ≥ 5`.
* **From `E⁶`** (`family_six`): `k = ℓ − 6`, when `ℓ ∣ 4n + 1`, for `ℓ ≡ 3 (mod 4)`, `ℓ ≥ 7`.
* **Ramanujan's congruences** are the first members of the last two, with `k = 1` (`ramanujan_five_of_family`,
  `ramanujan_seven_of_family`): `p(5n + 4) ≡ 0 (mod 5)` from `E⁴` at `ℓ = 5`, `p(7n + 5) ≡ 0 (mod 7)` from `E⁶` at
  `ℓ = 7`. The coloured congruences of `RamanujanCongruences` modulo `5` and `7` are the members `ℓ = 5, 7` of the
  first two: `coloured_four_five` and `coloured_six_seven` from `E`, `coloured_two_five` and `coloured_four_seven`
  from `E³`.
* **Modulo `11`** (`coloured_seven_eleven`, `coloured_eight_eleven`, `coloured_five_eleven`): `p₋₇(11n + 9)`,
  `p₋₈(11n + 4)` and `p₋₅(11n + 8)` are divisible by `11`, from `E⁴`, `E³` and `E⁶`.
The method is `RamanujanCongruences.coeff_P_pow_eq_zero`: `P^k·E^ℓ = E^{ℓ−k}` and `E^ℓ ≡ ∏(1 − X^{ℓi}) (mod ℓ)`, so it
is enough that the coefficients of `E^{ℓ−k}` at the exponents `≡ n (mod ℓ)` vanish modulo `ℓ`. Those of `E` sit at
the pentagonal numbers `m = i(3i − 1)/2` (Euler), where `24m + 1 = (6i − 1)²` (`sq_of_pent`); those of `E³` at the
triangular numbers `m = T(j) = j(j + 1)/2`, as `±(2j + 1)` (Jacobi), where `8m + 1 = (2j + 1)²` (`sq_of_tri`). So:
* for `E`, the exponents `m` have `24m + 1` a square;
* for `E³`, they have `8m + 1` a square, and `ℓ ∣ 8m + 1` forces `ℓ ∣ 2j + 1`;
* for `E⁴ = E·E³`, `24(m + T(j)) + 4 = (6i − 1)² + 3(2j + 1)²` (`pent_tri`), and `−3` is not a square modulo `ℓ ≡ 2
  (mod 3)` (`not_isSquare_neg_three`: a square root of `−3` gives a cube root of unity `≠ 1`, of order `3 ∣ ℓ − 1`), so
  `ℓ ∣ 6(m + T(j)) + 1` forces `ℓ ∣ 2j + 1`;
* for `E⁶ = (E³)²`, `8(T(j) + T(l)) + 2 = (2j + 1)² + (2l + 1)²` (`tri_tri`), and `−1` is not a square modulo
  `ℓ ≡ 3 (mod 4)`, so `ℓ ∣ 4(T(j) + T(l)) + 1` forces `ℓ ∣ 2j + 1`.
These are the families of I. Kiming and J. B. Olsson, "Congruences like Ramanujan's for powers of the partition
function", Arch. Math. 59 (1992), that come from `η`, `η³`, `η⁴` and `η⁶`; the remaining ones, from `η⁸`, `η¹⁰`, `η¹⁴`
and `η²⁶`, need more than the triple product.
-/
import Mathlib
import RamanujanCongruences

open PowerSeries JacobiFourSquares RamanujanCongruences

namespace RamanujanFamilies

/-! ## The identities, in any commutative ring -/

/-- A pentagonal exponent: `x(3x − 1) = 2r` gives `24r + 1 = (6x − 1)²`. -/
theorem sq_of_pent {R : Type*} [CommRing R] {x r : R} (h : x * (3 * x - 1) = 2 * r) :
    24 * r + 1 = (6 * x - 1) * (6 * x - 1) := by
  linear_combination (-12) * h

/-- A triangular exponent: `y(y + 1) = 2r` gives `(2y + 1)² = 8r + 1`. -/
theorem sq_of_tri {R : Type*} [CommRing R] {y r : R} (h : y * (y + 1) = 2 * r) : (2 * y + 1) ^ 2 = 8 * r + 1 := by
  linear_combination 4 * h

/-- A pentagonal and a triangular exponent: `(6x − 1)² + 3(2y + 1)² = 24(a + b) + 4`. -/
theorem pent_tri {R : Type*} [CommRing R] {a b n x y : R} (ha : 2 * a = x * (3 * x - 1)) (hb : 2 * b = y * (y + 1))
    (hab : a + b = n) : (6 * x - 1) ^ 2 + 3 * (2 * y + 1) ^ 2 = 4 * (6 * n + 1) := by
  linear_combination (-12) * ha + (-12) * hb + 24 * hab

/-- Two triangular exponents: `(2x + 1)² + (2y + 1)² = 8(a + b) + 2`. -/
theorem tri_tri {R : Type*} [CommRing R] {a b n x y : R} (ha : 2 * a = x * (x + 1)) (hb : 2 * b = y * (y + 1))
    (hab : a + b = n) : (2 * x + 1) ^ 2 + (2 * y + 1) ^ 2 = 2 * (4 * n + 1) := by
  linear_combination (-4) * ha + (-4) * hb + 8 * hab

/-- **A cube root of unity from `√−3`**: where `2, 3 ≠ 0`, a square root `x` of `−3` gives `w = (x − 1)/2` with
`w³ = 1` and `w ≠ 1`. -/
theorem exists_cube_root {K : Type*} [Field K] {x : K} (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hx : -3 = x * x) :
    ∃ w : K, w ^ 3 = 1 ∧ w ≠ 1 := by
  obtain ⟨w, hw⟩ : ∃ w : K, w * 2 = x - 1 := ⟨(x - 1) / 2, div_mul_cancel₀ (x - 1) h2⟩
  have h4 : 2 * (2 * (w ^ 2 + w + 1)) = 0 := by linear_combination (2 * w + x + 1) * hw - hx
  have h0 : w ^ 2 + w + 1 = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h2)).resolve_left h2
  refine ⟨w, by linear_combination (w - 1) * h0, fun h1 => h3 ?_⟩
  rw [h1] at h0
  linear_combination h0

/-- `a² + 3b² = 0` with `b ≠ 0` makes `−3` a square. -/
theorem neg_three_eq_sq_div {K : Type*} [Field K] {a b : K} (h : a ^ 2 + 3 * b ^ 2 = 0) (hb : b ≠ 0) :
    -3 = a / b * (a / b) := by
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb hb)]
  linear_combination -h

/-- `a² + b² = 0` with `a ≠ 0` makes `−1` a square. -/
theorem neg_one_eq_sq_div {K : Type*} [Field K] {a b : K} (h : a ^ 2 + b ^ 2 = 0) (ha : a ≠ 0) :
    -1 = b / a * (b / a) := by
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero ha ha)]
  linear_combination -h

/-! ## Squares modulo `ℓ` -/

theorem two_isUnit {ℓ : ℕ} [Fact ℓ.Prime] (h3 : 3 ≤ ℓ) : IsUnit (2 : ZMod ℓ) := by
  refine isUnit_iff_ne_zero.mpr fun h => ?_
  have h' : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

/-- **`−3` is not a square modulo a prime `ℓ ≡ 2 (mod 3)`, `ℓ ≥ 5`**: a square root of `−3` would give a cube root of
unity other than `1` (`exists_cube_root`), of order `3 ∣ ℓ − 1`. -/
theorem not_isSquare_neg_three {ℓ : ℕ} [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) (h3 : ℓ % 3 = 2) :
    ¬ IsSquare (-3 : ZMod ℓ) := by
  rintro ⟨x, hx⟩
  have h30 : (3 : ZMod ℓ) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨w, hw3, hw1⟩ := exists_cube_root (two_isUnit (by omega)).ne_zero h30 hx
  have hu : IsUnit w := IsUnit.of_pow_eq_one hw3 (by norm_num)
  have hu3 : hu.unit ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hw3, Units.val_one])
  have hord : orderOf hu.unit = 3 :=
    orderOf_eq_prime hu3 fun h => hw1 (by rw [← IsUnit.unit_spec hu, h, Units.val_one])
  have hdvd := orderOf_dvd_card (x := hu.unit)
  rw [hord, ZMod.card_units] at hdvd
  omega

/-- If `a² + 3b² ≡ 0` modulo a prime `ℓ ≡ 2 (mod 3)`, `ℓ ≥ 5`, then `b ≡ 0`. -/
theorem eq_zero_of_sq_add_three_sq {ℓ : ℕ} [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) (h3 : ℓ % 3 = 2) {a b : ZMod ℓ}
    (h : a ^ 2 + 3 * b ^ 2 = 0) : b = 0 := by
  by_contra hb
  exact not_isSquare_neg_three h5 h3 ⟨a / b, neg_three_eq_sq_div h hb⟩

/-- If `a² + b² ≡ 0` modulo a prime `ℓ ≡ 3 (mod 4)`, then `a ≡ 0`. -/
theorem eq_zero_of_sq_add_sq {ℓ : ℕ} [Fact ℓ.Prime] (h4 : ℓ % 4 = 3) {a b : ZMod ℓ} (h : a ^ 2 + b ^ 2 = 0) :
    a = 0 := by
  by_contra ha
  exact ZMod.exists_sq_eq_neg_one_iff.mp ⟨b / a, neg_one_eq_sq_div h ha⟩ h4

/-! ## The four reductions, in `ZMod ℓ` -/

/-- From `E`: the coefficient of `P^{ℓ−1}` at `n` vanishes modulo `ℓ` when `24n + 1` is not a square. -/
theorem zmod_one {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {n : ℕ} (hn : ¬ IsSquare ((24 * n + 1 : ℕ) : ZMod ℓ)) :
    ((coeff n (P ^ (ℓ - 1)) : ℤ) : ZMod ℓ) = 0 := by
  refine coeff_P_pow_eq_zero (k := ℓ - 1) (r := n % ℓ) (Nat.sub_le ℓ 1) (fun m hm => ?_) n rfl
  rw [Nat.sub_sub_self hℓ.out.one_lt.le, pow_one]
  refine pent_residue (r := n % ℓ) (fun x hx => hn ⟨6 * x - 1, ?_⟩) m hm
  rw [ZMod.natCast_mod] at hx
  push_cast
  exact sq_of_pent hx

/-- From `E³`: the coefficient of `P^{ℓ−3}` at `n` vanishes modulo `ℓ` when `ℓ ∣ 8n + 1` or `8n + 1` is not a
square. -/
theorem zmod_three {ℓ : ℕ} [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) {n : ℕ}
    (hn : ℓ ∣ 8 * n + 1 ∨ ¬ IsSquare ((8 * n + 1 : ℕ) : ZMod ℓ)) : ((coeff n (P ^ (ℓ - 3)) : ℤ) : ZMod ℓ) = 0 := by
  refine coeff_P_pow_eq_zero (k := ℓ - 3) (r := n % ℓ) (Nat.sub_le ℓ 3) (fun m hm => ?_) n rfl
  rw [Nat.sub_sub_self (by omega : 3 ≤ ℓ)]
  refine cube_residue (two_isUnit (by omega)) (fun y hy => ?_) m hm
  rw [ZMod.natCast_mod] at hy
  have hsq := sq_of_tri hy
  rcases hn with hn | hn
  · have hn' : ((8 * n + 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hn
    push_cast at hn'
    exact pow_eq_zero_iff two_ne_zero |>.mp (hsq.trans hn')
  · exact (hn ⟨2 * y + 1, by push_cast; exact hsq.symm.trans (sq _)⟩).elim

/-- From `E⁴ = E·E³`: the coefficient of `P^{ℓ−4}` at `n` vanishes modulo `ℓ ≡ 2 (mod 3)` when `ℓ ∣ 6n + 1`. -/
theorem zmod_four {ℓ : ℕ} [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) (h3 : ℓ % 3 = 2) {n : ℕ} (hn : ℓ ∣ 6 * n + 1) :
    ((coeff n (P ^ (ℓ - 4)) : ℤ) : ZMod ℓ) = 0 := by
  have hn' : ((6 * n + 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hn
  push_cast at hn'
  refine coeff_P_pow_eq_zero (k := ℓ - 4) (r := n % ℓ) (Nat.sub_le ℓ 4) (fun m hm => ?_) n rfl
  rw [Nat.sub_sub_self (by omega : 4 ≤ ℓ), show (4 : ℕ) = 1 + 3 from rfl, pow_add, pow_one, coeff_mul,
    Int.cast_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [Int.cast_mul]
  by_cases ha : ∃ i : ℤ, pentagonal i = p.1
  · obtain ⟨i, hi⟩ := ha
    rw [cast_coeff_cube_eq_zero (two_isUnit (by omega)) fun j hj => ?_, mul_zero]
    have hm' : ((pentagonal i : ℕ) : ZMod ℓ) + ((T j : ℕ) : ZMod ℓ) = (n : ZMod ℓ) := by
      rw [hi, hj, ← Nat.cast_add, hp, ← ZMod.natCast_mod, hm, ZMod.natCast_mod]
    have hsq := pent_tri (cast_two_mul_pentagonal ℓ i) (cast_two_mul_T ℓ j) hm'
    rw [hn', mul_zero] at hsq
    push_cast
    exact eq_zero_of_sq_add_three_sq h5 h3 hsq
  · rw [coeff_E_eq_zero fun i hi => ha ⟨i, hi⟩, Int.cast_zero, zero_mul]

/-- From `E⁶ = (E³)²`: the coefficient of `P^{ℓ−6}` at `n` vanishes modulo `ℓ ≡ 3 (mod 4)` when `ℓ ∣ 4n + 1`. -/
theorem zmod_six {ℓ : ℕ} [Fact ℓ.Prime] (h7 : 7 ≤ ℓ) (h4 : ℓ % 4 = 3) {n : ℕ} (hn : ℓ ∣ 4 * n + 1) :
    ((coeff n (P ^ (ℓ - 6)) : ℤ) : ZMod ℓ) = 0 := by
  have hn' : ((4 * n + 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hn
  push_cast at hn'
  refine coeff_P_pow_eq_zero (k := ℓ - 6) (r := n % ℓ) (Nat.sub_le ℓ 6) (fun m hm => ?_) n rfl
  rw [Nat.sub_sub_self (by omega : 6 ≤ ℓ), show (6 : ℕ) = 3 + 3 from rfl, pow_add, coeff_mul, Int.cast_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [Int.cast_mul]
  by_cases hb : ∃ l : ℤ, T l = p.2
  · obtain ⟨l, hl⟩ := hb
    rw [cast_coeff_cube_eq_zero (two_isUnit (by omega)) fun j hj => ?_, zero_mul]
    have hm' : ((T j : ℕ) : ZMod ℓ) + ((T l : ℕ) : ZMod ℓ) = (n : ZMod ℓ) := by
      rw [hj, hl, ← Nat.cast_add, hp, ← ZMod.natCast_mod, hm, ZMod.natCast_mod]
    have hsq := tri_tri (cast_two_mul_T ℓ j) (cast_two_mul_T ℓ l) hm'
    rw [hn', mul_zero] at hsq
    push_cast
    exact eq_zero_of_sq_add_sq h4 hsq
  · rw [coeff_cube_eq_zero fun l hl => hb ⟨l, hl⟩, Int.cast_zero, mul_zero]

/-! ## The four families -/

/-- **From `E`**: for a prime `ℓ`, `p₋ₖ(n) ≡ 0 (mod ℓ)` with `k = ℓ − 1` whenever `24n + 1` is not a square modulo
`ℓ` (never for `ℓ = 2, 3`). -/
theorem family_one {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {n : ℕ} (hn : ¬ IsSquare ((24 * n + 1 : ℕ) : ZMod ℓ)) :
    colouredPartitions (ℓ - 1) n ≡ 0 [ZMOD ℓ] :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  coloured_modEq (zmod_one hn)

/-- **From `E³`**: for a prime `ℓ ≥ 5`, `p₋ₖ(n) ≡ 0 (mod ℓ)` with `k = ℓ − 3` whenever `ℓ ∣ 8n + 1` or `8n + 1` is
not a square modulo `ℓ`. -/
theorem family_three {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (h5 : 5 ≤ ℓ) {n : ℕ}
    (hn : ℓ ∣ 8 * n + 1 ∨ ¬ IsSquare ((8 * n + 1 : ℕ) : ZMod ℓ)) : colouredPartitions (ℓ - 3) n ≡ 0 [ZMOD ℓ] :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  coloured_modEq (zmod_three h5 hn)

/-- **From `E⁴ = E·E³`**: for a prime `ℓ ≡ 2 (mod 3)`, `ℓ ≥ 5`, `p₋ₖ(n) ≡ 0 (mod ℓ)` with `k = ℓ − 4` whenever
`ℓ ∣ 6n + 1`. -/
theorem family_four {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (h5 : 5 ≤ ℓ) (h3 : ℓ % 3 = 2) {n : ℕ} (hn : ℓ ∣ 6 * n + 1) :
    colouredPartitions (ℓ - 4) n ≡ 0 [ZMOD ℓ] :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  coloured_modEq (zmod_four h5 h3 hn)

/-- **From `E⁶ = (E³)²`**: for a prime `ℓ ≡ 3 (mod 4)`, `ℓ ≥ 7`, `p₋ₖ(n) ≡ 0 (mod ℓ)` with `k = ℓ − 6` whenever
`ℓ ∣ 4n + 1`. -/
theorem family_six {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (h7 : 7 ≤ ℓ) (h4 : ℓ % 4 = 3) {n : ℕ} (hn : ℓ ∣ 4 * n + 1) :
    colouredPartitions (ℓ - 6) n ≡ 0 [ZMOD ℓ] :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  coloured_modEq (zmod_six h7 h4 hn)

/-! ## Members -/

/-- **Ramanujan's congruence modulo `5`** is the member `ℓ = 5` of the family from `E⁴`
(`RamanujanCongruences.ramanujan_five`). -/
theorem ramanujan_five_of_family (n : ℕ) : Fintype.card (Nat.Partition (5 * n + 4)) ≡ 0 [MOD 5] :=
  haveI := fact_five
  card_partition_modEq (zmod_four (ℓ := 5) le_rfl rfl ⟨6 * n + 5, by ring⟩)

/-- **Ramanujan's congruence modulo `7`** is the member `ℓ = 7` of the family from `E⁶`
(`RamanujanCongruences.ramanujan_seven`). -/
theorem ramanujan_seven_of_family (n : ℕ) : Fintype.card (Nat.Partition (7 * n + 5)) ≡ 0 [MOD 7] :=
  haveI := fact_seven
  card_partition_modEq (zmod_six (ℓ := 7) le_rfl rfl ⟨4 * n + 3, by ring⟩)

theorem fact_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- **Seven-coloured partitions modulo `11`**: `p₋₇(11n + 9) ≡ 0 (mod 11)`, from `E⁴`. -/
theorem coloured_seven_eleven (n : ℕ) : colouredPartitions 7 (11 * n + 9) ≡ 0 [ZMOD 11] :=
  family_four (ℓ := 11) (hℓ := fact_eleven) (by norm_num) rfl ⟨6 * n + 5, by ring⟩

/-- **Eight-coloured partitions modulo `11`**: `p₋₈(11n + 4) ≡ 0 (mod 11)`, from `E³`. -/
theorem coloured_eight_eleven (n : ℕ) : colouredPartitions 8 (11 * n + 4) ≡ 0 [ZMOD 11] :=
  family_three (ℓ := 11) (hℓ := fact_eleven) (by norm_num) (.inl ⟨8 * n + 3, by ring⟩)

/-- **Five-coloured partitions modulo `11`**: `p₋₅(11n + 8) ≡ 0 (mod 11)`, from `E⁶`. -/
theorem coloured_five_eleven (n : ℕ) : colouredPartitions 5 (11 * n + 8) ≡ 0 [ZMOD 11] :=
  family_six (ℓ := 11) (hℓ := fact_eleven) (by norm_num) rfl ⟨4 * n + 3, by ring⟩

end RamanujanFamilies

#print axioms RamanujanFamilies.not_isSquare_neg_three
#print axioms RamanujanFamilies.family_one
#print axioms RamanujanFamilies.family_three
#print axioms RamanujanFamilies.family_four
#print axioms RamanujanFamilies.family_six
#print axioms RamanujanFamilies.ramanujan_five_of_family
#print axioms RamanujanFamilies.ramanujan_seven_of_family
#print axioms RamanujanFamilies.coloured_seven_eleven
#print axioms RamanujanFamilies.coloured_eight_eleven
#print axioms RamanujanFamilies.coloured_five_eleven
