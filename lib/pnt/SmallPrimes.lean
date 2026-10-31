/-
# The small primes generate the units mod `q`

Plain statement. For every `A > 12` there is `C` such that, for every `q ≥ 1`:
* every proper subgroup of `(ℤ/qℤ)ˣ` misses the class of a prime `p ≤ C(log(q + 2))^A` prime to `q`
  (`exists_prime_not_mem`);
* so the classes of the primes `p ≤ C(log(q + 2))^A` generate `(ℤ/qℤ)ˣ` (`closure_primes_eq_top`);
* and for a prime `p` and every `k ≥ 2` dividing `p − 1`, some prime `ℓ ≤ C(log(p + 2))^A` is not a `k`-th power mod
  `p` (`exists_prime_not_pow`): the least `k`-th power non-residue is at most a power of `log p`.

Under GRH these are the bounds of N. C. Ankeny (1952) and E. Bach (1990), with `(log q)²` in place of `(log q)^A`.
Bach's form is what makes G. L. Miller's primality test deterministic: for a composite `n`, the bases that the test
passes lie in a proper subgroup of `(ℤ/nℤ)ˣ`, so a base below the bound exposes `n`. Here the bounds follow from the
zero-free half-plane, through `LeastNonresidue.exists_prime_ne_one`, with no hypothesis: a proper subgroup lies in the
kernel of a nontrivial character (Mathlib's `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, on the quotient),
and the least prime at which that character is not `1` lies outside it. Miller's test itself is
`MillerTest.prime_iff_forall_strongProbablePrime`.
-/
import LeastNonresidue

namespace SmallPrimes

/-- A proper subgroup of `(ℤ/qℤ)ˣ` lies in the kernel of a nontrivial Dirichlet character. -/
lemma exists_char_of_ne_top {q : ℕ} [NeZero q] {H : Subgroup (ZMod q)ˣ} (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 ∧ ∀ u ∈ H, χ (u : ZMod q) = 1 := by
  obtain ⟨a, haH⟩ : ∃ a : (ZMod q)ˣ, a ∉ H := by
    by_contra h
    exact hH (eq_top_iff.2 fun a _ ↦ not_not.1 (not_exists.1 h a))
  have hexp : Monoid.exponent ((ZMod q)ˣ ⧸ H) ≠ 0 := Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ ⧸ H)
  have : NeZero ((Monoid.exponent ((ZMod q)ˣ ⧸ H) : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.2 hexp⟩
  have ha : (QuotientGroup.mk a : (ZMod q)ˣ ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ ha
  refine ⟨MulChar.ofUnitHom (φ.comp (QuotientGroup.mk' H)), fun h1 ↦ hφ ?_, fun u hu ↦ ?_⟩
  · have h := congrArg (fun χ : DirichletCharacter ℂ q ↦ χ (a : ZMod q)) h1
    simp only [MulChar.ofUnitHom_coe, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MulChar.one_apply_coe] at h
    exact Units.ext h
  · rw [MulChar.ofUnitHom_coe, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff u).2 hu, map_one, Units.val_one]

/-- **The least prime outside a proper subgroup.** For every `A > 12` there is `C` such that every proper subgroup of
`(ℤ/qℤ)ˣ` misses the class of a prime `p ≤ C(log(q + 2))^A` prime to `q`. -/
theorem exists_prime_not_mem {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
      ∃ (p : ℕ) (hp : p.Coprime q), p.Prime ∧ (p : ℝ) ≤ C * Real.log (q + 2) ^ A ∧
        ZMod.unitOfCoprime p hp ∉ H := by
  obtain ⟨C, hC, hprime⟩ := LeastNonresidue.exists_prime_ne_one hA
  refine ⟨C, hC, fun q _ H hH ↦ ?_⟩
  obtain ⟨χ, hχ1, hχH⟩ := exists_char_of_ne_top hH
  obtain ⟨p, hp, hpq, hχp, hple⟩ := hprime q χ hχ1
  have hcop : p.Coprime q := (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
  refine ⟨p, hcop, hp, hple, fun hmem ↦ hχp ?_⟩
  have h := hχH _ hmem
  rwa [ZMod.coe_unitOfCoprime] at h

/-- **The small primes generate `(ℤ/qℤ)ˣ`.** For every `A > 12` there is `C` such that, for every `q ≥ 1`, the classes
of the primes `p ≤ C(log(q + 2))^A` generate `(ℤ/qℤ)ˣ`. -/
theorem closure_primes_eq_top {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q],
      Subgroup.closure {u : (ZMod q)ˣ | ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * Real.log (q + 2) ^ A ∧
        (u : ZMod q) = p} = ⊤ := by
  obtain ⟨C, hC, h⟩ := exists_prime_not_mem hA
  refine ⟨C, hC, fun q _ ↦ ?_⟩
  by_contra hne
  obtain ⟨p, hcop, hp, hple, hnot⟩ := h q _ hne
  exact hnot (Subgroup.subset_closure ⟨p, hp, hple, ZMod.coe_unitOfCoprime p hcop⟩)

/-- For a prime `p` and `k ≥ 2` dividing `p − 1`, not every unit mod `p` is a `k`-th power. -/
lemma range_pow_ne_top {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) (hkp : k ∣ p - 1) :
    (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range ≠ ⊤ := by
  intro htop
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  have hkle : k ≤ p - 1 := Nat.le_of_dvd hp1 hkp
  have hall : ∀ u : (ZMod p)ˣ, u ^ ((p - 1) / k) = 1 := by
    intro u
    obtain ⟨y, rfl⟩ := (MonoidHom.range_eq_top.1 htop) u
    rw [powMonoidHom_apply, ← pow_mul, Nat.mul_div_cancel' hkp, ZMod.units_pow_card_sub_one_eq_one]
  have hdvd : Monoid.exponent (ZMod p)ˣ ∣ (p - 1) / k := Monoid.exponent_dvd_of_forall_pow_eq_one hall
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units p] at hdvd
  have hpos : 0 < (p - 1) / k := Nat.div_pos hkle (by omega)
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.2 (Nat.div_lt_self hp1 (by omega)))

/-- **The least `k`-th power non-residue.** For every `A > 12` there is `C` such that, for every prime `p` and every
`k ≥ 2` dividing `p − 1`, some prime `ℓ ≤ C(log(p + 2))^A` is not a `k`-th power mod `p`. -/
theorem exists_prime_not_pow {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2 ≤ k → k ∣ p - 1 →
      ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : ℝ) ≤ C * Real.log (p + 2) ^ A ∧ ∀ x : ZMod p, x ^ k ≠ ℓ := by
  obtain ⟨C, hC, h⟩ := exists_prime_not_mem hA
  refine ⟨C, hC, fun p _ k hk hkp ↦ ?_⟩
  obtain ⟨ℓ, hcop, hℓ, hle, hnot⟩ := h p _ (range_pow_ne_top hk hkp)
  refine ⟨ℓ, hℓ, hle, fun x hx ↦ hnot ?_⟩
  have hu : ((ZMod.unitOfCoprime ℓ hcop : (ZMod p)ˣ) : ZMod p) = ℓ := ZMod.coe_unitOfCoprime ℓ hcop
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), ← hu] at hx
    exact (ZMod.unitOfCoprime ℓ hcop).ne_zero hx.symm
  refine ⟨Units.mk0 x hx0, Units.ext ?_⟩
  rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hx, hu]

end SmallPrimes
