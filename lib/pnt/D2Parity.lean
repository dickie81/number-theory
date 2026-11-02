import Mathlib
import D2Prim

/-!
# The parity of `χ_D`

For a fundamental discriminant `D`, `χ_D(−1) = sign D`: `(D | |D| − 1) = 1` for `D > 1` and `= −1` for `D < 0`
(`D2Parity.kron_pos`, `D2Parity.kron_neg`), by quadratic reciprocity. So a character with `χ(n) = (D|n)` mod `|D|`
has `χ(−1) = sign D` (`D2Parity.chi_neg_one`). Unconditional. See `formalisations/d2-density.md`.
-/

namespace D2Parity
open GSFund GSEven GSPrim ZMod

theorem modEq_neg_one {a n : ℕ} (hd : a ∣ n + 1) : ((n : ℕ) : ℤ) % (a : ℕ) = (-1 : ℤ) % (a : ℕ) := by
  refine Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd ?_)
  rw [sub_neg_eq_add]; exact_mod_cast hd

/-- `J(a | n) = 1` for odd `a` and `n ≡ 3 (4)` with `a ∣ n + 1`. -/
theorem jac_one {a n : ℕ} (ha : Odd a) (hn : n % 4 = 3) (hd : a ∣ n + 1) : jacobiSym a n = 1 := by
  have hno : Odd n := Nat.odd_iff.2 (by omega)
  have hJ : jacobiSym n a = χ₄ a := by
    rw [jacobiSym.mod_left' (modEq_neg_one hd), jacobiSym.at_neg_one ha]
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by rcases ha with ⟨t, rfl⟩; omega
  rcases ha4 with h | h
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four h hno, hJ, χ₄_nat_one_mod_four h]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four h hn, hJ, χ₄_nat_three_mod_four h]; rfl

/-- `J(m | 4m − 1) = 1` for `m ≥ 1` odd or twice an odd number. -/
theorem jac_m {m : ℕ} (hm : Odd m ∨ ∃ a, Odd a ∧ m = 2 * a) (h0 : 0 < m) :
    jacobiSym m (4 * m - 1) = 1 := by
  rcases hm with hm | ⟨a, ha, rfl⟩
  · exact jac_one hm (by omega) ⟨4, by omega⟩
  · have hn : Odd (4 * (2 * a) - 1) := Nat.odd_iff.2 (by omega)
    rw [Nat.cast_mul, jacobiSym.mul_left, jac_one ha (by omega) ⟨8, by omega⟩, mul_one,
      show ((2 : ℕ) : ℤ) = 2 by norm_num, jacobiSym.at_two hn, χ₈_nat_mod_eight,
      show (4 * (2 * a) - 1) % 8 = 7 by omega]
    rfl

theorem kron_four {m : ℤ} {n : ℕ} (hn : Odd n) : kron (4 * m) n = (jacobiSym m n : ℂ) := by
  rw [kron_odd hn, show (4:ℤ) * m = 2 ^ 2 * m by norm_num, jacobiSym.mul_left,
    jacobiSym.sq_one' (by
      rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, Int.gcd_natCast_natCast]
      exact (Nat.coprime_two_left).2 hn), one_mul]

theorem shape {m : ℕ} (hs : Squarefree m) (h : m % 4 = 2 ∨ m % 4 = 3 ∨ m % 4 = 1) :
    Odd m ∨ ∃ a, Odd a ∧ m = 2 * a := by
  rcases h with h | h | h
  · right
    obtain ⟨a, rfl⟩ : 2 ∣ m := by omega
    refine ⟨a, Nat.odd_iff.2 ?_, rfl⟩
    by_contra hc
    obtain ⟨b, rfl⟩ : 2 ∣ a := by omega
    have := hs 2 ⟨b, by ring⟩
    simp at this
  all_goals exact Or.inl (Nat.odd_iff.2 (by omega))

/-- **`(d | d − 1) = 1`** for a positive fundamental discriminant `d > 1`. -/
theorem kron_pos {d : ℕ} (hd : fundPos d) (h1 : 1 < d) : kron d (d - 1) = 1 := by
  rcases hd with ⟨hs, h4⟩ | ⟨h4, hs, hm⟩
  · rw [kron_eq_jacobi_one (by omega) (by omega), Int.natAbs_natCast, Nat.cast_sub h1.le, Nat.cast_one,
      jacobiSym.mod_left' (b := d) (a₂ := -1) (by
        refine Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd ⟨1, by ring⟩)),
      jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)), χ₄_nat_one_mod_four h4]
    norm_num
  · obtain ⟨m, rfl⟩ := h4
    rw [Nat.mul_div_cancel_left _ (by norm_num)] at hs hm
    have h0 : 0 < m := by omega
    have := jac_m (shape hs (by omega)) h0
    push_cast
    rw [kron_four (Nat.odd_iff.2 (by omega)), this]; norm_num

/-- **`(−d | d − 1) = −1`** for a negative fundamental discriminant `−d`. -/
theorem kron_neg {d : ℕ} (hd : fundNeg d) : kron (-(d : ℤ)) (d - 1) = -1 := by
  rcases hd with ⟨hs, h4⟩ | ⟨h4, hs, hm⟩
  · have hd1 : 1 < d := by
      by_contra h; interval_cases d <;> simp_all
    rw [kron_eq_jacobi_one (by omega) (by omega), Int.natAbs_neg, Int.natAbs_natCast, Nat.cast_sub hd1.le,
      Nat.cast_one, jacobiSym.mod_left' (b := d) (a₂ := -1) (by
        refine Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd ⟨1, by ring⟩)),
      jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)), χ₄_nat_three_mod_four h4]
    simp
  · obtain ⟨m, rfl⟩ := h4
    rw [Nat.mul_div_cancel_left _ (by norm_num)] at hs hm
    have h0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hs
      · exact h
    have hn : Odd (4 * m - 1) := Nat.odd_iff.2 (by omega)
    have := jac_m (shape hs (by omega)) h0
    rw [show -((4 * m : ℕ) : ℤ) = 4 * (-(m : ℤ)) by push_cast; ring, kron_four hn,
      show -(m : ℤ) = -1 * m by ring, jacobiSym.mul_left, this, jacobiSym.at_neg_one hn,
      χ₄_nat_three_mod_four (by omega)]
    simp

/-- `χ(−1) = (D | N − 1)` for a character mod `N > 1` with `χ(n) = (D|n)`. -/
theorem chi_neg_one {N : ℕ} {D : ℤ} (χ : DirichletCharacter ℂ N) (hN : 1 < N)
    (hv : ∀ n : ℕ, n ≠ 0 → χ n = kron D n) : χ (-1) = kron D (N - 1) := by
  have : ((N - 1 : ℕ) : ZMod N) = -1 := by
    rw [Nat.cast_sub hN.le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [← this, hv _ (by omega)]

end D2Parity
