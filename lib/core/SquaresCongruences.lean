/-
# Congruences for sums of squares and the binary forms of class number one

Plain statement. Classical consequences of formulas the library already proves: the divisor sums that count the points
of `ℤ²`, `ℤ⁴` and `ℤ⁸` on each sphere and of the hexagonal lattice and `x² + xy + 2y²` on each ellipse
(`GlobalTeeth.two_sq_count`, `JacobiFourSquares.r4_eq`, `JacobiEightSquares.r8_eq`, `EpsteinHexagonal.rQ_eq`,
`EpsteinSeven.rQ_eq`), with Euler's criterion and the pairing `d ↔ n/d` of the divisors. Throughout `n ≥ 1`.
* **Theta series ≡ Eisenstein series (mod ℓ).** For the forms of discriminant `−3` and `−7`, the character in the
  divisor sum is `d ↦ d^{(ℓ−1)/2}` modulo `ℓ = 3` and `7` (Euler's criterion), so the theta series of the form agrees
  modulo `ℓ` with an Eisenstein series of weight `(ℓ + 1)/2`. For `x² + y²`, `χ₋₄(d) ≡ d (mod 4)` for odd `d`, and the
  theta series agrees modulo `4` with one of weight `2`:
  - `hex_modEq`: for `x² + xy + y²`, `r(n) ≡ 6Σ_{d ∣ n, 3 ∤ d} d (mod 18)`;
  - `seven_modEq`: for `x² + xy + 2y²`, `r(n) ≡ 2Σ_{d ∣ n, 7 ∤ d} d³ (mod 14)`;
  - `two_modEq`: for `x² + y²`, `r₂(n) ≡ 4Σ_{d ∣ n, d odd} d (mod 16)`.
* **2-adic.**
  - `r8_modEq`: `r₈(n) ≡ 2r₄(n) (mod 64)`, since `θ⁸ = (θ⁴)²` and `θ⁴ = 1 + 8Σ σ*(n)qⁿ`
    (`JacobiFourSquares.theta_pow_four`).
  - `r4_mod_sixteen`: for odd `m`, `r₄(2^a m) ≡ 8 (mod 16)` if `m` is a square and `≡ 0 (mod 16)` otherwise. Here
    `σ*(2^a m)` is `σ(m)` or `3σ(m)` (`sigma4_two_pow_mul`), and `σ(m)` is odd exactly when the odd number `m` is a
    square (`odd_sigma_iff`).
* **Divisor pairing** (`sum_divisors_pair`): when `f(d) + f(n/d) = 0` for every divisor, the sum over the divisors is
  the sum over those with `d² = n`, and in the classes below `n` is not a square.
  - `three_dvd_sigma`: `σ(n) ≡ 0 (mod 3)` for `n ≡ 2 (mod 3)`, as `d + n/d ≡ 0 (mod 3)`;
  - `nine_dvd_sigma_three`: `σ₃(n) ≡ 0 (mod 9)` for `n ≡ 2 (mod 3)`, as `d³ + (n/d)³ ≡ 0 (mod 9)`;
  - `seven_dvd_sigma_three`: `σ₃(n) ≡ 0 (mod 7)` for `n ≡ 3, 5, 6 (mod 7)`, the non-residues;
  - `r4_three_mul_add_two`: `r₄(3k + 2) ≡ 0 (mod 24)`;
  - `r8_mod_seven`: `r₈(n) ≡ 0 (mod 112)` for `n ≡ 3, 5, 6 (mod 7)`, through the odd part of `n`
    (`isMultiplicative_w8`), which is again a non-residue because `2` is a square modulo `7`.
-/
import Mathlib
import GlobalTeeth
import EpsteinHexagonal
import EpsteinSeven
import JacobiEightSquares

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

noncomputable section

namespace SquaresCongruences

/-! ## Divisor pairing -/

/-- **Divisor pairing**: if `f(d) + f(n/d) = 0` for every divisor `d` of `n`, the sum of `f` over the divisors is its
sum over the divisors with `d² = n`. -/
theorem sum_divisors_pair {R : Type*} [AddCommGroup R] {n : ℕ} (f : ℕ → R)
    (h : ∀ d ∈ n.divisors, f d + f (n / d) = 0) :
    ∑ d ∈ n.divisors, f d = ∑ d ∈ n.divisors with d * d = n, f d := by
  have h0 : ∑ d ∈ n.divisors with ¬ d * d = n, f d = 0 := by
    refine Finset.sum_involution (fun d _ => n / d) (fun d hd => h d (Finset.mem_filter.1 hd).1) ?_ ?_ ?_
    · intro d hd _ heq
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      apply hd.2
      conv_rhs => rw [← Nat.div_mul_cancel hd.1.1]
      rw [heq]
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      refine ⟨⟨Nat.div_dvd_of_dvd hd.1.1, hd.1.2⟩, fun h2 => hd.2 ?_⟩
      have hde : d * (n / d) = n := Nat.mul_div_cancel' hd.1.1
      have he : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.1.2) hd.1.1)
        (Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hd.1.2))
      have hd' : d = n / d := Nat.eq_of_mul_eq_mul_right he (hde.trans h2.symm)
      rw [← hde, ← hd']
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 hd.1.2
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => d * d = n), h0, add_zero]

/-- The pairing of a divisor with its cofactor, in `ZMod q`. -/
lemma cast_mul_div {q n d : ℕ} (hd : d ∣ n) : (d : ZMod q) * ((n / d : ℕ) : ZMod q) = (n : ZMod q) := by
  rw [← Nat.cast_mul, Nat.mul_div_cancel' hd]

/-- **`σ(m)` is odd exactly when the odd number `m` is a square.** The divisors pair off as `d ↔ m/d`, all of them
odd, except `√m`. -/
theorem odd_sigma_iff {m : ℕ} (hm : Odd m) : Odd (σ 1 m) ↔ IsSquare m := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hcast : ((σ 1 m : ℕ) : ZMod 2) = ∑ d ∈ m.divisors with d * d = m, (1 : ZMod 2) := by
    rw [sigma_apply, Nat.cast_sum]
    have h1 : ∀ d ∈ m.divisors, ((d ^ 1 : ℕ) : ZMod 2) = 1 := fun d hd => by
      rw [pow_one, ZMod.natCast_eq_one_iff_odd]
      exact hm.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
    rw [Finset.sum_congr rfl h1]
    exact sum_divisors_pair (fun _ => (1 : ZMod 2)) fun _ _ => by decide
  rw [← ZMod.natCast_eq_one_iff_odd, hcast, Finset.sum_const, nsmul_eq_mul, mul_one]
  constructor
  · intro h
    by_contra hns
    have he : (m.divisors.filter fun d => d * d = m) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun d _ hd => hns ⟨d, hd.symm⟩
    rw [he, Finset.card_empty, Nat.cast_zero] at h
    exact zero_ne_one h
  · rintro ⟨k, rfl⟩
    have hs : ((k * k).divisors.filter fun d => d * d = k * k) = {k} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hd⟩
        exact Nat.mul_self_inj.1 hd
      · rintro rfl
        exact ⟨⟨dvd_mul_right d d, hm0⟩, rfl⟩
    rw [hs, Finset.card_singleton, Nat.cast_one]

/-- **`σ(n) ≡ 0 (mod 3)` for `n ≡ 2 (mod 3)`**: `d + n/d ≡ d + 2d ≡ 0 (mod 3)`. -/
theorem three_dvd_sigma {n : ℕ} (h : n % 3 = 2) : 3 ∣ σ 1 n := by
  have hn : (n : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h]; rfl
  have hpair : ∀ d ∈ n.divisors, (d : ZMod 3) + ((n / d : ℕ) : ZMod 3) = 0 := fun d hd => by
    have hp := cast_mul_div (q := 3) (Nat.dvd_of_mem_divisors hd)
    rw [hn] at hp
    revert hp
    generalize (d : ZMod 3) = x
    generalize ((n / d : ℕ) : ZMod 3) = y
    revert x y
    decide
  rw [← ZMod.natCast_eq_zero_iff, sigma_apply, Nat.cast_sum]
  simp only [pow_one]
  refine (sum_divisors_pair (fun d => (d : ZMod 3)) hpair).trans (Finset.sum_eq_zero fun d hd => ?_)
  rw [Finset.mem_filter] at hd
  have hsq : (d : ZMod 3) * d = 2 := by rw [← Nat.cast_mul, hd.2, hn]
  revert hsq
  generalize (d : ZMod 3) = x
  revert x
  decide

/-- **`σ₃(n) ≡ 0 (mod 9)` for `n ≡ 2 (mod 3)`**: the cube of a unit is `±1 (mod 9)` and `n³ ≡ −1 (mod 9)`, so
`d³ + (n/d)³ ≡ 0 (mod 9)`. -/
theorem nine_dvd_sigma_three {n : ℕ} (h : n % 3 = 2) : 9 ∣ σ 3 n := by
  have hn : (n : ZMod 9) = 2 ∨ (n : ZMod 9) = 5 ∨ (n : ZMod 9) = 8 := by
    rw [← ZMod.natCast_mod]
    have h9 : n % 9 = 2 ∨ n % 9 = 5 ∨ n % 9 = 8 := by omega
    rcases h9 with h9 | h9 | h9 <;> rw [h9] <;> decide
  have hpair : ∀ d ∈ n.divisors, (d : ZMod 9) ^ 3 + ((n / d : ℕ) : ZMod 9) ^ 3 = 0 := fun d hd => by
    have hp := cast_mul_div (q := 9) (Nat.dvd_of_mem_divisors hd)
    have hn' := hn
    rw [← hp] at hn'
    revert hn'
    generalize (d : ZMod 9) = x
    generalize ((n / d : ℕ) : ZMod 9) = y
    revert x y
    decide
  rw [← ZMod.natCast_eq_zero_iff, sigma_apply, Nat.cast_sum]
  simp only [Nat.cast_pow]
  refine (sum_divisors_pair (fun d => (d : ZMod 9) ^ 3) hpair).trans (Finset.sum_eq_zero fun d hd => ?_)
  rw [Finset.mem_filter] at hd
  have hsq : (d : ZMod 9) * d = n := by rw [← Nat.cast_mul, hd.2]
  rw [← hsq] at hn
  revert hn
  generalize (d : ZMod 9) = x
  revert x
  decide

/-- The class of `n` modulo `7` among the non-residues `3, 5, 6`, in `ZMod 7`. -/
lemma cast_nonres {n : ℕ} (h : n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) :
    (n : ZMod 7) = 3 ∨ (n : ZMod 7) = 5 ∨ (n : ZMod 7) = 6 := by
  rw [← ZMod.natCast_mod]
  rcases h with h | h | h <;> rw [h] <;> decide

/-- **`σ₃(n) ≡ 0 (mod 7)` for `n ≡ 3, 5, 6 (mod 7)`**: the cube of a unit is `±1 (mod 7)`, and `n³ ≡ −1 (mod 7)`
for a non-residue, so `d³ + (n/d)³ ≡ 0 (mod 7)`. -/
theorem seven_dvd_sigma_three {n : ℕ} (h : n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) : 7 ∣ σ 3 n := by
  have hn := cast_nonres h
  have hpair : ∀ d ∈ n.divisors, (d : ZMod 7) ^ 3 + ((n / d : ℕ) : ZMod 7) ^ 3 = 0 := fun d hd => by
    have hp := cast_mul_div (q := 7) (Nat.dvd_of_mem_divisors hd)
    have hn' := hn
    rw [← hp] at hn'
    revert hn'
    generalize (d : ZMod 7) = x
    generalize ((n / d : ℕ) : ZMod 7) = y
    revert x y
    decide
  rw [← ZMod.natCast_eq_zero_iff, sigma_apply, Nat.cast_sum]
  simp only [Nat.cast_pow]
  refine (sum_divisors_pair (fun d => (d : ZMod 7) ^ 3) hpair).trans (Finset.sum_eq_zero fun d hd => ?_)
  rw [Finset.mem_filter] at hd
  have hsq : (d : ZMod 7) * d = n := by rw [← Nat.cast_mul, hd.2]
  rw [← hsq] at hn
  revert hn
  generalize (d : ZMod 7) = x
  revert x
  decide

/-! ## `σ*` and the sign-twisted cube sum through the odd part -/

/-- `d ↦ d` away from the multiples of `4`, so that `σ*(n) = Σ_{d ∣ n} g₄(d)`. -/
def g4 : ArithmeticFunction ℕ := ⟨fun d => if 4 ∣ d then 0 else d, by simp⟩

lemma g4_apply (d : ℕ) : g4 d = if 4 ∣ d then 0 else d := rfl

lemma not_four_dvd_of_odd {m : ℕ} (hm : Odd m) : ¬ 4 ∣ m := fun h4 => by
  have := Nat.odd_iff.1 hm
  omega

lemma coprime_four_of_odd {m : ℕ} (hm : Odd m) : Nat.Coprime 4 m := by
  have h := (Nat.coprime_two_left.2 hm).pow_left 2
  norm_num at h
  exact h

lemma isMultiplicative_g4 : g4.IsMultiplicative := by
  refine ⟨by simp [g4_apply], fun {m n} hmn => ?_⟩
  simp only [g4_apply]
  rcases Nat.even_or_odd n with hn | hn
  · have hm : Odd m := by
      rcases Nat.even_or_odd m with hm | hm
      · exact absurd (Nat.Coprime.gcd_eq_one hmn ▸ Nat.dvd_gcd hm.two_dvd hn.two_dvd) (by norm_num)
      · exact hm
    have h4 : 4 ∣ m * n ↔ 4 ∣ n := by
      rw [mul_comm m n]
      exact Nat.Coprime.dvd_mul_right (coprime_four_of_odd hm)
    simp only [h4, not_four_dvd_of_odd hm, ↓reduceIte]
    split_ifs <;> ring
  · have h4 : 4 ∣ m * n ↔ 4 ∣ m := Nat.Coprime.dvd_mul_right (coprime_four_of_odd hn)
    simp only [h4, not_four_dvd_of_odd hn, ↓reduceIte]
    split_ifs <;> ring

lemma sigma4_eq (n : ℕ) : JacobiFourSquares.sigma4 n = (g4 * ζ) n := by
  rw [mul_zeta_apply, JacobiFourSquares.sigma4, Finset.sum_filter]
  exact Finset.sum_congr rfl fun d _ => by rw [g4_apply, ite_not]

lemma sum_g4_two_pow (a : ℕ) : ∑ e ∈ range (a + 1), g4 (2 ^ e) = if a = 0 then 1 else 3 := by
  induction a with
  | zero => simp [g4_apply]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases k with _ | k
    · simp [g4_apply]
    · have h4 : 4 ∣ 2 ^ (k + 1 + 1) := ⟨2 ^ k, by ring⟩
      simp [g4_apply, h4]

/-- **`σ*(2^a m) = σ(m)` or `3σ(m)`** for odd `m`: `σ*` is multiplicative, `σ*(2^a)` is `1` or `3`, and no divisor
of `m` is a multiple of `4`. -/
theorem sigma4_two_pow_mul (a : ℕ) {m : ℕ} (hm : Odd m) :
    JacobiFourSquares.sigma4 (2 ^ a * m) = (if a = 0 then 1 else 3) * σ 1 m := by
  have hmul : (g4 * ζ).IsMultiplicative := isMultiplicative_g4.mul isMultiplicative_zeta
  rw [sigma4_eq, hmul.map_mul_of_coprime ((Nat.coprime_two_left.2 hm).pow_left a)]
  congr 1
  · rw [mul_zeta_apply, Nat.sum_divisors_prime_pow Nat.prime_two, sum_g4_two_pow]
  · rw [mul_zeta_apply, sigma_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd4 := not_four_dvd_of_odd (hm.of_dvd_nat (Nat.dvd_of_mem_divisors hd))
    simp [g4_apply, hd4]

/-- `d ↦ (−1)^{d+1}d³`, a multiplicative function: `Σ_{d ∣ n} (−1)^{n+d} d³ = (−1)^{n+1} Σ_{d ∣ n} w(d)`. -/
def w8 : ArithmeticFunction ℤ := ⟨fun d => if d = 0 then 0 else (-1) ^ (d + 1) * (d : ℤ) ^ 3, by simp⟩

lemma w8_apply {d : ℕ} (hd : d ≠ 0) : w8 d = (-1) ^ (d + 1) * (d : ℤ) ^ 3 := by
  simp [w8, hd]

/-- `w(d) = (−1)^{d+1}d³` is multiplicative: two coprime numbers are not both even. -/
theorem isMultiplicative_w8 : w8.IsMultiplicative := by
  refine ⟨by simp [w8], fun {m n} hmn => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [w8]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [w8]
  rw [w8_apply (Nat.mul_ne_zero hm.ne' hn.ne'), w8_apply hm.ne', w8_apply hn.ne']
  have hpar : (-1 : ℤ) ^ (m * n + 1) = (-1) ^ (m + 1) * (-1) ^ (n + 1) := by
    rcases Nat.even_or_odd m with hme | hmo <;> rcases Nat.even_or_odd n with hne | hno
    · exact absurd (Nat.Coprime.gcd_eq_one hmn ▸ Nat.dvd_gcd hme.two_dvd hne.two_dvd) (by norm_num)
    · rw [Odd.neg_one_pow (hme.mul_right n).add_one, Odd.neg_one_pow hme.add_one, Even.neg_one_pow hno.add_one]
      norm_num
    · rw [Odd.neg_one_pow (hne.mul_left m).add_one, Even.neg_one_pow hmo.add_one, Odd.neg_one_pow hne.add_one]
      norm_num
    · rw [Even.neg_one_pow (hmo.mul hno).add_one, Even.neg_one_pow hmo.add_one, Even.neg_one_pow hno.add_one]
      norm_num
  rw [hpar]
  push_cast
  ring

lemma sum_sign_eq (n : ℕ) :
    ∑ d ∈ n.divisors, (-1) ^ (n + d) * (d : ℤ) ^ 3 = (-1) ^ (n + 1) * (w8 * ζ) n := by
  rw [coe_mul_zeta_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [w8_apply (Nat.pos_of_mem_divisors hd).ne']
  ring

lemma w8_zeta_odd {m : ℕ} (hm : Odd m) : (w8 * ζ) m = (σ 3 m : ℤ) := by
  rw [coe_mul_zeta_apply, sigma_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : Odd d := hm.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
  rw [w8_apply hd'.pos.ne', Even.neg_one_pow hd'.add_one, one_mul]
  push_cast
  ring

/-- The powers of `2` modulo `7` are `1, 2, 4`, the squares. -/
lemma two_pow_mod_seven (a : ℕ) : 2 ^ a % 7 = 1 ∨ 2 ^ a % 7 = 2 ∨ 2 ^ a % 7 = 4 := by
  induction a with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h | h <;> rw [h] <;> norm_num

/-- If `2^a m ≡ 3, 5, 6 (mod 7)`, so is `m`: the powers of `2` are squares modulo `7`. -/
lemma nonres_of_two_pow_mul {a m : ℕ} (h : 2 ^ a * m % 7 = 3 ∨ 2 ^ a * m % 7 = 5 ∨ 2 ^ a * m % 7 = 6) :
    m % 7 = 3 ∨ m % 7 = 5 ∨ m % 7 = 6 := by
  have h2 := two_pow_mod_seven a
  rw [Nat.mul_mod] at h
  rcases h2 with h2 | h2 | h2 <;> rw [h2] at h <;> omega

/-! ## Theta series ≡ Eisenstein series (mod ℓ) -/

/-- **The hexagonal lattice modulo `3`**: `r(n) ≡ 6Σ_{d ∣ n, 3 ∤ d} d (mod 18)` for `x² + xy + y²`, since
`χ₋₃(d) ≡ d (mod 3)`: its theta series is an Eisenstein series of weight `2` modulo `3`. -/
theorem hex_modEq {n : ℕ} (hn : n ≠ 0) :
    (EpsteinHexagonal.rQ n : ℤ) ≡ 6 * ∑ d ∈ n.divisors with ¬ 3 ∣ d, (d : ℤ) [ZMOD 18] := by
  rw [EpsteinHexagonal.rQ_eq hn]
  have h3 : ∑ d ∈ n.divisors, Eis.chiInt d ≡ ∑ d ∈ n.divisors with ¬ 3 ∣ d, (d : ℤ) [ZMOD 3] := by
    rw [Finset.sum_filter]
    refine Int.ModEq.sum fun d _ => ?_
    unfold Eis.chiInt Int.ModEq
    split_ifs <;> omega
  have h18 := h3.mul_left' (c := 6)
  rwa [show (6 : ℤ) * 3 = 18 by norm_num] at h18

/-- `χ₋₇(d) = (d/7) ≡ d³ (mod 7)` off the multiples of `7`: Euler's criterion. -/
lemma chi7_modEq (d : ℕ) : (WeilTwinGeneral.χ₇ d : ℤ) ≡ if ¬ 7 ∣ d then (d : ℤ) ^ 3 else 0 [ZMOD 7] := by
  have hd : (d : ℤ) ≡ ((d % 7 : ℕ) : ℤ) [ZMOD 7] := by
    unfold Int.ModEq
    push_cast
    omega
  have h3 := hd.pow 3
  rw [WeilTwinGeneral.χ₇_nat]
  simp only [Nat.dvd_iff_mod_eq_zero]
  have hr : d % 7 < 7 := Nat.mod_lt _ (by norm_num)
  generalize (d : ℤ) ^ 3 = D at h3 ⊢
  generalize d % 7 = r at hr h3 ⊢
  unfold Int.ModEq at h3 ⊢
  interval_cases r <;> norm_num at h3 ⊢ <;> omega

/-- **`x² + xy + 2y²` modulo `7`**: `r(n) ≡ 2Σ_{d ∣ n, 7 ∤ d} d³ (mod 14)`, since `(d/7) ≡ d³ (mod 7)`: its theta
series is an Eisenstein series of weight `4` modulo `7`. -/
theorem seven_modEq {n : ℕ} (hn : n ≠ 0) :
    (EpsteinSeven.rQ n : ℤ) ≡ 2 * ∑ d ∈ n.divisors with ¬ 7 ∣ d, (d : ℤ) ^ 3 [ZMOD 14] := by
  rw [EpsteinSeven.rQ_eq hn]
  have h7 : ∑ d ∈ n.divisors, (WeilTwinGeneral.χ₇ d : ℤ) ≡
      ∑ d ∈ n.divisors with ¬ 7 ∣ d, (d : ℤ) ^ 3 [ZMOD 7] := by
    rw [Finset.sum_filter]
    exact Int.ModEq.sum fun d _ => chi7_modEq d
  have h14 := h7.mul_left' (c := 2)
  rwa [show (2 : ℤ) * 7 = 14 by norm_num] at h14

/-- **`x² + y²` modulo `4`**: `r₂(n) ≡ 4Σ_{d ∣ n, d odd} d (mod 16)`, since `χ₋₄(d) ≡ d (mod 4)` for odd `d`: its
theta series agrees modulo `4` with the Eisenstein series `Σ_n Σ_{d ∣ n, d odd} d qⁿ` of weight `2`. -/
theorem two_modEq {n : ℕ} (hn : n ≠ 0) :
    (GlobalTeeth.R n : ℤ) ≡ 4 * ∑ d ∈ n.divisors with ¬ 2 ∣ d, (d : ℤ) [ZMOD 16] := by
  rw [GlobalTeeth.two_sq_count n (Nat.pos_of_ne_zero hn), GlobalTeeth.f]
  have h4 : ∑ d ∈ n.divisors, (ZMod.χ₄ d : ℤ) ≡ ∑ d ∈ n.divisors with ¬ 2 ∣ d, (d : ℤ) [ZMOD 4] := by
    rw [Finset.sum_filter]
    refine Int.ModEq.sum fun d _ => ?_
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [Nat.dvd_iff_mod_eq_zero]
    unfold Int.ModEq
    split_ifs <;> omega
  have h16 := h4.mul_left' (c := 4)
  rwa [show (4 : ℤ) * 4 = 16 by norm_num] at h16

/-! ## 2-adic congruences -/

/-- **`r₈(n) ≡ 2r₄(n) (mod 64)`** for `n ≥ 1`: `θ⁸ = (θ⁴)² = (1 + 8S)² = 1 + 16S + 64S²` with
`S = Σ σ*(n)qⁿ`, and `r₄(n) = 8σ*(n)`. -/
theorem r8_modEq {n : ℕ} (hn : n ≠ 0) :
    (JacobiEightSquares.r8 n : ℤ) ≡ 2 * (JacobiFourSquares.r4 n : ℤ) [ZMOD 64] := by
  have h8 := JacobiEightSquares.coeff_theta_pow_eight_int n
  rw [show JacobiFourSquares.theta ^ 8 = (JacobiFourSquares.theta ^ 4) ^ 2 by ring,
    JacobiFourSquares.theta_pow_four] at h8
  set S : PowerSeries ℤ := PowerSeries.mk fun n => (JacobiFourSquares.sigma4 n : ℤ) with hS
  rw [show ((1 : PowerSeries ℤ) + 8 * S) ^ 2 = 1 + PowerSeries.C 16 * S + PowerSeries.C 64 * S ^ 2 by
      simp only [map_ofNat]; ring, map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, hS, PowerSeries.coeff_mk] at h8
  simp only [hn, ↓reduceIte, zero_add] at h8
  rw [JacobiFourSquares.r4_eq hn, Int.modEq_iff_dvd]
  refine ⟨-PowerSeries.coeff n (S ^ 2), ?_⟩
  rw [← h8]
  push_cast
  ring

/-- **`r₄(2^a m) ≡ 8 (mod 16)` exactly when the odd number `m` is a square**, and `≡ 0 (mod 16)` otherwise. -/
theorem r4_mod_sixteen (a : ℕ) {m : ℕ} (hm : Odd m) :
    JacobiFourSquares.r4 (2 ^ a * m) % 16 = if IsSquare m then 8 else 0 := by
  have h0 : 2 ^ a * m ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) hm.pos.ne'
  rw [JacobiFourSquares.r4_eq h0, sigma4_two_pow_mul a hm]
  by_cases hsq : IsSquare m
  · obtain ⟨t, ht⟩ := (odd_sigma_iff hm).2 hsq
    simp only [hsq, ↓reduceIte, ht]
    split_ifs <;> omega
  · obtain ⟨t, ht⟩ := Nat.not_odd_iff_even.1 (mt (odd_sigma_iff hm).1 hsq)
    simp only [hsq, ↓reduceIte, ht]
    split_ifs <;> omega

/-! ## Divisor-pairing congruences for `r₄` and `r₈` -/

/-- **`r₄(3k + 2) ≡ 0 (mod 24)`**: `σ*(3k + 2)` is `3σ(m)`, or `σ(3k + 2) ≡ 0 (mod 3)` when `3k + 2` is odd. -/
theorem r4_three_mul_add_two (k : ℕ) : 24 ∣ JacobiFourSquares.r4 (3 * k + 2) := by
  have hn : 3 * k + 2 ≠ 0 := by omega
  rw [JacobiFourSquares.r4_eq hn]
  obtain ⟨a, m, hm, ha⟩ := Nat.exists_eq_two_pow_mul_odd hn
  rw [ha, sigma4_two_pow_mul a hm]
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · have hm3 : m % 3 = 2 := by
      rw [pow_zero, one_mul] at ha
      omega
    obtain ⟨c, hc⟩ := three_dvd_sigma hm3
    rw [hc]
    exact ⟨c, by simp; ring⟩
  · simp only [ha0.ne', ↓reduceIte]
    exact ⟨σ 1 m, by ring⟩

/-- **`r₈(n) ≡ 0 (mod 112)` for `n ≡ 3, 5, 6 (mod 7)`**: with `n = 2^a m`, `m` odd,
`r₈(n) = ±16 W(2^a) σ₃(m)` for the multiplicative `W = w ∗ 1`, and `m` is again a non-residue. -/
theorem r8_mod_seven {n : ℕ} (h : n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) : 112 ∣ JacobiEightSquares.r8 n := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  obtain ⟨c, hc⟩ := seven_dvd_sigma_three (nonres_of_two_pow_mul h)
  have hW : (w8 * ζ) (2 ^ a * m) = (w8 * ζ) (2 ^ a) * (σ 3 m : ℤ) := by
    rw [(isMultiplicative_w8.mul isMultiplicative_zeta.natCast).map_mul_of_coprime
      ((Nat.coprime_two_left.2 hm).pow_left a), w8_zeta_odd hm]
  have hr := JacobiEightSquares.r8_eq hn
  rw [sum_sign_eq, hW, hc] at hr
  have h112 : (112 : ℤ) ∣ (JacobiEightSquares.r8 (2 ^ a * m) : ℤ) := by
    rw [hr]
    exact ⟨(-1) ^ (2 ^ a * m + 1) * ((w8 * ζ) (2 ^ a) * c), by push_cast; ring⟩
  exact_mod_cast h112

end SquaresCongruences

#print axioms SquaresCongruences.hex_modEq
#print axioms SquaresCongruences.seven_modEq
#print axioms SquaresCongruences.two_modEq
#print axioms SquaresCongruences.r8_modEq
#print axioms SquaresCongruences.r4_mod_sixteen
#print axioms SquaresCongruences.odd_sigma_iff
#print axioms SquaresCongruences.sigma4_two_pow_mul
#print axioms SquaresCongruences.three_dvd_sigma
#print axioms SquaresCongruences.nine_dvd_sigma_three
#print axioms SquaresCongruences.seven_dvd_sigma_three
#print axioms SquaresCongruences.r4_three_mul_add_two
#print axioms SquaresCongruences.r8_mod_seven
