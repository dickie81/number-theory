import Mathlib

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

#print axioms Kron.exists_jacobiSym_eq_neg_one
