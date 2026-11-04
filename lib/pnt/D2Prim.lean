import Mathlib
import D2GS
import QuadKronecker

/-!
# The Kronecker character of a fundamental discriminant is primitive

Unconditional. `GSPrim.primitive_pos` and `GSPrim.primitive_neg`: for a fundamental discriminant `D` (`d > 1`, or
`-d`), there is a primitive Dirichlet character mod `|D|` whose value at every `n ≥ 1` is the Kronecker symbol
`GSEven.kron D n`. The character is the library's `QuadKronecker.jacBot |D|` when `D ≡ 1 (4)`
(`GSPrim.kron_eq_jacobi_one`), and `QuadKronecker.jacTop (D/4)` when `4 ∣ D` (`GSPrim.kron_eq_jacTop`).
See `formalisations/d2-density.md`.
-/

namespace GSPrim
open GSEven ZMod

/-- A Dirichlet character is primitive if for each prime `p ∣ N` some `a` coprime to `N` with `a ≡ 1 (N/p)`
has `χ a ≠ 1`. -/
theorem isPrimitive_of_witness {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : ∀ p, p.Prime → p ∣ N → ∃ a : ℕ, a.Coprime N ∧ (a : ZMod (N / p)) = 1 ∧ χ a ≠ 1) :
    χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hft0 := χ.factorsThrough_conductor
  have hcd := χ.conductor_dvd_level
  generalize χ.conductor = c at hft0 hcd ⊢
  obtain ⟨k, hk⟩ := hcd
  by_contra hne
  have hk1 : k ≠ 1 := by rintro rfl; exact hne (by rw [hk, mul_one])
  have hk0 : k ≠ 0 := by rintro rfl; exact NeZero.ne N (by rw [hk, mul_zero])
  have hp : k.minFac.Prime := Nat.minFac_prime hk1
  obtain ⟨j, hj⟩ := k.minFac_dvd
  have hpN : k.minFac ∣ N := ⟨c * j, by rw [hk]; nth_rewrite 1 [hj]; ring⟩
  have hNp : N / k.minFac = c * j := by
    rw [hk]; nth_rewrite 1 [hj]
    rw [show c * (k.minFac * j) = k.minFac * (c * j) by ring,
      Nat.mul_div_cancel_left _ hp.pos]
  have hft : χ.FactorsThrough (N / k.minFac) :=
    hft0.mono χ ⟨j, hNp⟩ (Nat.div_dvd_of_dvd hpN)
  obtain ⟨a, hcop, ha1, hχa⟩ := h _ hp hpN
  apply hχa
  obtain ⟨hd, χ₀, hχ₀⟩ := hft
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ₀ hd (ZMod.unitOfCoprime a hcop)
  rw [← hχ₀] at this
  simp only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd, ha1, map_one] at this
  exact this

theorem chi8_neg (x : ZMod 8) : χ₈ (-x) = χ₈ x := by
  rw [show -x = (-1) * x by ring, map_mul, show χ₈ (-1) = 1 by decide, one_mul]

theorem cop_of_modEq {a k : ℕ} (h : a ≡ 1 [MOD k]) : a.Coprime k := by
  unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq h]; simp

/-- **Bridge, `D ≡ 1 (4)`**: `(D|n) = J(n | |D|)`, the repo's `jacBot |D|`. -/
theorem kron_eq_jacobi_one {D : ℤ} (hD : D % 4 = 1) {n : ℕ} (hn : n ≠ 0) :
    kron D n = (jacobiSym n D.natAbs : ℂ) := by
  obtain ⟨v, n', hn', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm : Odd D.natAbs := by
    rw [Nat.odd_iff]; have := Int.natAbs_emod_two D; omega
  rw [kron_even hn', Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym.pow_left]
  have h2 : jacobiSym ((2:ℕ):ℤ) D.natAbs = χ₈ (D : ZMod 8) := by
    rw [Nat.cast_ofNat, jacobiSym.at_two hm]
    rcases Int.natAbs_eq D with h | h
    · conv_rhs => rw [h]
      simp
    · conv_rhs => rw [h]
      rw [Int.cast_neg, chi8_neg]; simp
  rw [h2]; push_cast; congr 1
  obtain ⟨m, hmD⟩ : ∃ m, m = D.natAbs := ⟨_, rfl⟩
  rw [← hmD] at hm ⊢
  -- `J(D|n') = J(n'| |D|)`
  have hn'4 : n' % 4 = 1 ∨ n' % 4 = 3 := by rcases hn' with ⟨t, rfl⟩; omega
  rcases Int.natAbs_eq D with h | h
  · have hm4 : m % 4 = 1 := by rw [hmD]; omega
    rw [← hmD] at h
    rw [h, jacobiSym.quadratic_reciprocity_one_mod_four hm4 hn']
  · have hm4 : m % 4 = 3 := by rw [hmD]; omega
    rw [← hmD] at h
    rw [h, show -(m:ℤ) = -1 * m by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hn']
    rcases hn'4 with h4 | h4
    · rw [ZMod.χ₄_nat_one_mod_four h4, one_mul,
        jacobiSym.quadratic_reciprocity_one_mod_four' hm h4]
    · rw [ZMod.χ₄_nat_three_mod_four h4, jacobiSym.quadratic_reciprocity_three_mod_four hm4 h4]
      ring

/-- **Bridge, `D = 4m`**: `(D|n)` is the repo's `jacTop m`. -/
theorem kron_eq_jacTop {m : ℤ} (hm : m ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    kron (4 * m) n = QuadKronecker.toC (QuadKronecker.jacTop m hm) n := by
  rw [QuadKronecker.toC_apply, QuadKronecker.jacTop_natCast]
  split_ifs with ho
  · have hodd : Odd n := Nat.odd_iff.2 ho
    rw [kron_odd hodd, show (4:ℤ) * m = 2 ^ 2 * m by norm_num, jacobiSym.mul_left,
      jacobiSym.sq_one' (by
        rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, Int.gcd_natCast_natCast]
        exact (Nat.coprime_two_left).2 hodd), one_mul]
  · obtain ⟨v, n', hn', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
    have hv : v ≠ 0 := by
      rintro rfl; apply ho; simpa [Nat.odd_iff] using hn'
    rw [kron_even hn']
    have : χ₈ ((4 * m : ℤ) : ZMod 8) = 0 := by
      push_cast
      rw [map_mul, show χ₈ (4 : ZMod 8) = 0 by decide, zero_mul]
    rw [this]; simp [hv]

theorem finish {D : ℤ} {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hv : ∀ n : ℕ, n ≠ 0 → χ n = kron D n)
    (hw : ∀ p, p.Prime → p ∣ N → ∃ a : ℕ, a.Coprime N ∧ (a : ZMod (N / p)) = 1 ∧ a ≠ 0 ∧ kron D a = -1) :
    χ.IsPrimitive := by
  apply isPrimitive_of_witness
  intro p hp hpN
  obtain ⟨a, h1, h2, h3, h4⟩ := hw p hp hpN
  refine ⟨a, h1, h2, ?_⟩
  rw [hv a h3, h4]; norm_num

/-- Witness at an odd prime `p ∥ D`. -/
theorem wit_odd {D : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpD : (p:ℤ) ∣ D) (hsq : ¬ (p:ℤ) ^ 2 ∣ D) :
    ∃ a : ℕ, a.Coprime D.natAbs ∧ (a : ZMod (D.natAbs / p)) = 1 ∧ a ≠ 0 ∧ kron D a = -1 := by
  obtain ⟨D', rfl⟩ := hpD
  have hpD' : ¬ (p:ℤ) ∣ D' := fun h => hsq (by obtain ⟨e, rfl⟩ := h; exact ⟨e, by ring⟩)
  have hD'0 : D' ≠ 0 := by rintro rfl; exact hsq (by simp)
  have hpD'n : ¬ p ∣ D'.natAbs := fun h => hpD' (Int.natCast_dvd.2 h)
  have hcop : (4 * D'.natAbs).Coprime p := by
    apply Nat.coprime_mul_iff_left.2 ⟨?_, ?_⟩
    · rw [show (4:ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hpD'n).symm
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hr : legendreSym p (g.val : ℕ) = -1 :=
    (legendreSym.eq_neg_one_iff' p).2 (by rw [ZMod.natCast_zmod_val]; exact hg)
  obtain ⟨a, ha1, har⟩ := Nat.chineseRemainder hcop 1 g.val
  have hD1 : 0 < D'.natAbs := Int.natAbs_pos.2 hD'0
  have hamod : a % (4 * D'.natAbs) = 1 := by
    rw [ha1]; exact Nat.mod_eq_of_lt (by omega)
  have ha4 : a % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd a (dvd_mul_right 4 D'.natAbs), hamod]
  have hodd : Odd a := Nat.odd_iff.2 (by omega)
  have hag : (a : ZMod p) = g := by
    rw [(ZMod.natCast_eq_natCast_iff' a g.val p).2 har, ZMod.natCast_zmod_val]
  have hJ : jacobiSym a p = -1 := by
    rw [← hr, jacobiSym.legendreSym.to_jacobiSym]
    apply jacobiSym.mod_left'
    rw [← Int.natCast_mod, ← Int.natCast_mod, har]
  have hpa : a.Coprime p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    apply hg
    rw [← hag, (ZMod.natCast_eq_zero_iff a p).2 h]
    exact ⟨0, by simp⟩
  have hD'm : a ≡ 1 [MOD D'.natAbs] := Nat.ModEq.of_dvd (dvd_mul_left _ _) ha1
  refine ⟨a, ?_, ?_, by omega, ?_⟩
  · rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.Coprime.mul_right hpa (cop_of_modEq hD'm)
  · rw [Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hp.pos, ← Nat.cast_one,
      ZMod.natCast_eq_natCast_iff]
    exact hD'm
  · rw [kron_odd hodd, jacobiSym.mul_left, jacobiSym.mod_right D' hodd, hamod, jacobiSym.one_right,
      mul_one, jacobiSym.quadratic_reciprocity_one_mod_four' (hp.odd_of_ne_two hp2) ha4, hJ]
    norm_num

/-- Witness at `2` for `D = 4m`, `m ≡ 2, 3 (4)`. -/
theorem wit_two {m : ℤ} (hm : m % 4 = 2 ∨ m % 4 = 3) :
    ∃ a : ℕ, a.Coprime (4 * m).natAbs ∧ (a : ZMod ((4 * m).natAbs / 2)) = 1 ∧ a ≠ 0 ∧
      kron (4 * m) a = -1 := by
  have e : (4 * m).natAbs = 4 * m.natAbs := by rw [Int.natAbs_mul]; rfl
  obtain ⟨k, hk⟩ : ∃ k, k = m.natAbs := ⟨_, rfl⟩
  rw [e, ← hk]
  have hodd : Odd (1 + 2 * k) := ⟨k, by ring⟩
  have hak : 1 + 2 * k ≡ 1 [MOD k] := by
    unfold Nat.ModEq; rw [show 1 + 2 * k = 1 + k * 2 by ring, Nat.add_mul_mod_self_left]
  have hak' : ((1 + 2 * k : ℕ) : ℤ) % (k : ℤ) = 1 % (k : ℤ) := by
    rw [show ((1 + 2 * k : ℕ) : ℤ) = 1 + (k:ℤ) * 2 by push_cast; ring, Int.add_mul_emod_self_left]
  refine ⟨1 + 2 * k, ?_, ?_, by omega, ?_⟩
  · apply Nat.Coprime.mul_right
    · rw [show (4:ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2 (cop_of_modEq (by unfold Nat.ModEq; omega))
    · exact cop_of_modEq hak
  · rw [show 4 * k / 2 = 2 * k by omega, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, add_zero]
  · rw [kron_odd hodd, show (4:ℤ) * m = 2 ^ 2 * m by norm_num, jacobiSym.mul_left,
      jacobiSym.sq_one' (by
        rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, Int.gcd_natCast_natCast]
        exact (Nat.coprime_two_left).2 hodd), one_mul]
    have hmk : m = k ∨ m = -k := by rw [hk]; exact Int.natAbs_eq m
    rcases hm with h2 | h3
    · -- `k = 2j`, `j` odd
      have hk2 : k % 4 = 2 := by omega
      obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
      have hj : Odd j := Nat.odd_iff.2 (by omega)
      have ha4 : (1 + 2 * (2 * j)) % 4 = 1 := by omega
      have hJ : jacobiSym (((2 * j : ℕ)) : ℤ) (1 + 2 * (2 * j)) = -1 := by
        rw [Nat.cast_mul, jacobiSym.mul_left, Nat.cast_ofNat, jacobiSym.at_two hodd,
          jacobiSym.quadratic_reciprocity_one_mod_four' hj ha4,
          jacobiSym.mod_left' (b := j) (a₂ := 1) (by
            rw [show ((1 + 2 * (2 * j) : ℕ) : ℤ) = 1 + (j:ℤ) * 4 by push_cast; ring,
              Int.add_mul_emod_self_left]),
          jacobiSym.one_left, mul_one, ZMod.χ₈_nat_eq_if_mod_eight]
        have : (1 + 2 * (2 * j)) % 8 = 5 := by omega
        simp [this]
      rcases hmk with h | h
      · rw [h, hJ]; norm_num
      · rw [h, show -(((2 * j : ℕ)) : ℤ) = -1 * ((2 * j : ℕ) : ℤ) by ring, jacobiSym.mul_left,
          jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_one_mod_four ha4, hJ]; norm_num
    · rcases hmk with h | h
      · have hk4 : k % 4 = 3 := by omega
        have ha4 : (1 + 2 * k) % 4 = 3 := by omega
        rw [h, jacobiSym.quadratic_reciprocity_three_mod_four hk4 ha4, jacobiSym.mod_left' hak',
          jacobiSym.one_left]; norm_num
      · have hk4 : k % 4 = 1 := by omega
        have ha4 : (1 + 2 * k) % 4 = 3 := by omega
        rw [h, show -(k : ℤ) = -1 * (k : ℤ) by ring, jacobiSym.mul_left, jacobiSym.at_neg_one hodd,
          ZMod.χ₄_nat_three_mod_four ha4, jacobiSym.quadratic_reciprocity_one_mod_four hk4 hodd,
          jacobiSym.mod_left' hak', jacobiSym.one_left]; norm_num

/-- **`χ_D` is a primitive character mod `|D|`** for a fundamental discriminant `D ≠ 1`, with `χ_D(n) = (D|n)`. -/
theorem exists_primitive_kron (D : ℤ)
    (hD : (D % 4 = 1 ∧ Squarefree D.natAbs ∧ 1 < D.natAbs) ∨
      (∃ m : ℤ, D = 4 * m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ Squarefree m.natAbs)) :
    ∃ χ : DirichletCharacter ℂ D.natAbs, χ.IsPrimitive ∧ ∀ n : ℕ, n ≠ 0 → χ n = kron D n := by
  rcases hD with ⟨h1, hsq, hgt⟩ | ⟨m, rfl, hm, hsq⟩
  · have : NeZero D.natAbs := ⟨by omega⟩
    have hv : ∀ n : ℕ, n ≠ 0 → QuadKronecker.toC (QuadKronecker.jacBot D.natAbs hgt) n = kron D n := by
      intro n hn
      rw [QuadKronecker.toC_apply, QuadKronecker.jacBot_natCast, kron_eq_jacobi_one h1 hn]
    refine ⟨_, finish _ hv ?_, hv⟩
    intro p hp hpN
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : D.natAbs % 2 = 1 := by have := Int.natAbs_emod_two D; omega
      omega
    apply wit_odd hp hp2 (Int.natCast_dvd.2 hpN)
    intro h
    have h' : p * p ∣ D.natAbs := by rw [← sq]; exact Int.natCast_dvd.1 (by exact_mod_cast h)
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p h'))
  · have hm0 : m ≠ 0 := by rintro rfl; omega
    have e : (4 * m).natAbs = 4 * m.natAbs := by rw [Int.natAbs_mul]; rfl
    have : NeZero (4 * m).natAbs := ⟨by rw [e]; have := Int.natAbs_pos.2 hm0; omega⟩
    have hw : ∀ p, p.Prime → p ∣ (4 * m).natAbs →
        ∃ a : ℕ, a.Coprime (4 * m).natAbs ∧ (a : ZMod ((4 * m).natAbs / p)) = 1 ∧ a ≠ 0 ∧
          kron (4 * m) a = -1 := by
      intro p hp hpN
      by_cases hp2 : p = 2
      · subst hp2; exact wit_two hm
      have hc4 : Nat.Coprime (p ^ 2) 4 := by
        rw [show (4:ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow 2 2 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      apply wit_odd hp hp2 (Int.natCast_dvd.2 hpN)
      intro h
      have h1 : p ^ 2 ∣ 4 * m.natAbs := by rw [← e]; exact Int.natCast_dvd.1 (by exact_mod_cast h)
      have h2 : p * p ∣ m.natAbs := by rw [← sq]; exact hc4.dvd_of_dvd_mul_left h1
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p h2))
    revert hw
    generalize hN : (4 * m).natAbs = N
    rw [e] at hN; subst hN
    intro hw
    have : NeZero (4 * m.natAbs) := ⟨by have := Int.natAbs_pos.2 hm0; omega⟩
    have hv : ∀ n : ℕ, n ≠ 0 → QuadKronecker.toC (QuadKronecker.jacTop m hm0) n = kron (4 * m) n :=
      fun n hn => (kron_eq_jacTop hm0 hn).symm
    exact ⟨_, finish _ hv hw, hv⟩

open GSFund in
/-- **Positive fundamental discriminants**: `χ_d` is primitive mod `d`, with `χ_d(n) = (d|n)`. -/
theorem primitive_pos {d : ℕ} (hd : fundPos d) (h1 : 1 < d) :
    ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ ∀ n : ℕ, n ≠ 0 → χ n = kron d n := by
  have := exists_primitive_kron (d : ℤ) (by
    rcases hd with ⟨hs, h4⟩ | ⟨h4, hs, hm⟩
    · left; refine ⟨by omega, by rwa [Int.natAbs_natCast], by rwa [Int.natAbs_natCast]⟩
    · right; obtain ⟨j, rfl⟩ := h4
      rw [Nat.mul_div_cancel_left _ (by norm_num)] at hs hm
      exact ⟨j, by push_cast; ring, by omega, by rwa [Int.natAbs_natCast]⟩)
  rwa [Int.natAbs_natCast] at this

open GSFund in
/-- **Negative fundamental discriminants**: `χ_{-d}` is primitive mod `d`, with `χ_{-d}(n) = (-d|n)`. -/
theorem primitive_neg {d : ℕ} (hd : fundNeg d) :
    ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ ∀ n : ℕ, n ≠ 0 → χ n = kron (-d) n := by
  have := exists_primitive_kron (-(d : ℤ)) (by
    rcases hd with ⟨hs, h4⟩ | ⟨h4, hs, hm⟩
    · left; refine ⟨by omega, by rwa [Int.natAbs_neg, Int.natAbs_natCast], by
        rw [Int.natAbs_neg, Int.natAbs_natCast]; omega⟩
    · right; obtain ⟨j, rfl⟩ := h4
      rw [Nat.mul_div_cancel_left _ (by norm_num)] at hs hm
      exact ⟨-(j:ℤ), by push_cast; ring, by omega, by rwa [Int.natAbs_neg, Int.natAbs_natCast]⟩)
  rwa [Int.natAbs_neg, Int.natAbs_natCast] at this

end GSPrim

