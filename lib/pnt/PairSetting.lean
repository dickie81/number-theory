import CMHost
import ZetaTwist

/-!
# The setting of a pair

A step of the proof of the sharp frontier (`SharpInputs`, the field `SharpPieces.params`): for a primitive character
`χ` mod `f` and a pair `(q, d)` of `ZetaTwist.WinPair`, a `ZetaBalance.Setting` with that pair and a character `κ` of
its group `A` lifting `χ` (`Setting.Lifts`), at every level `e`, with the sizes that the design reads off it.

**The arithmetic of the pair** (`PairArith f q d`): primes `q ≡ 3 (mod 8)` and `d ≡ 7 (mod 8)` with `q ∣ d + 1`, every
prime of `f` dividing `d + 1`, and `f < q`. A pair of `WinPair ε Y` has it once `f ≤ Y^{ε/5}/2`
(`ZetaTwist.WinPair.pairArith`): the primes of `f` are then at most `Y^{ε/5}`, and `f < log q < q`. The one Legendre
computation (`legendreSym_eq_one_of_dvd`): `(p/d) = 1` for every prime `p ∣ d + 1`. At `p = 2` this is `d ≡ 7 (mod 8)`.
At odd `p`, `d ≡ −1 (mod p)` gives `(d/p) = (−1/p) = χ₄(p)`, and reciprocity with `d ≡ 3 (mod 4)` gives
`(p/d) = χ₄(p)(d/p) = 1`. It gives `(2/d) = 1`, `(q/d) = 1` and `Setting.split`, as `2`, `q` and the primes of `f` all
divide `d + 1`.

**The setting** (`pairSetting χ h e`): `QS = lcm(2^{e+2}, f)` (`pairQS`) and `K = {u ≡ ±1 (mod 2^{e+2}) : χ(u) = 1}`,
taken as the kernel of `pairMap : (ℤ/QS)ˣ → H_e × ℂˣ`, `u ↦ ([u mod 2^{e+2}], χ(u mod f))`, where
`H_e = (ℤ/2^{e+2})ˣ/{±1}` (`He`). So `A = (ℤ/QS)ˣ/K` embeds in `H_e × ℂˣ` (`pairLift`, `pairLift_injective`), and
`κ = pairChar χ h e` is the second coordinate: `κ([u]) = χ(u mod f)`. It lifts `χ` (`pairChar_lifts`): `κ̃` and
`χ` changed to the level `QS` are both `MulChar.ofUnitHom` of `u ↦ χ(u mod f)`. `q ∤ QS` as `q` is odd and `q > f`.

**The sizes.**
* `H_e` has order `2^e` (`card_He`) and is cyclic (`isCyclic_He`): the class of `5` has order `2^e`, by Mathlib's
  `ZMod.orderOf_five` and `5^j ≢ −1 (mod 4)`.
* `2^e ≤ |A|` (`two_pow_le_card_A`): `A` maps onto `H_e`, as `(ℤ/QS)ˣ → (ℤ/2^{e+2})ˣ` is onto.
* `A₀ = ker κ` embeds in `H_e` (`injective_ker`): a class of `A₀` with trivial image in `H_e` has trivial image in
  `H_e × ℂˣ`. So `A₀` is cyclic (`isCyclic_ker`) of order at most `2^e` (`card_A₀_le`).
* `|A| = o·|A₀|` for any character `κ` of order `o` of a finite abelian group (`card_A_eq`): `|A| = |κ(A)|·|ker κ|`,
  and `κ(A)` is a finite subgroup of `ℂˣ`, cyclic, so of order its exponent, which is `o` (`orderOf_eq_card_range`).
  With the above, `2^e ≤ |A| ≤ o·2^e`.
* `QS ≤ 4·2^e·f` (`QS_le`), so `log N ≤ log(4·2^e·f) + log q + log d` (`log_N_le`).
* For every setting, `log(2 v_E) ≤ log N` (`log_vE_le`), from `|d_E| ≤ N^{[E:ℚ]}` (`natAbs_discr_le`). `E` is a
  subfield of `ℚ(ζ_N)`, so `|d_E|^{[ℚ(ζ_N):E]}` divides `|d_{ℚ(ζ_N)}|` (Mathlib's
  `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`), which is at most `N^{φ(N)}` (Mathlib's
  `IsCyclotomicExtension.Rat.natAbs_discr`), and `φ(N) = [ℚ(ζ_N):E]·[E:ℚ]`.

**Choices.**
* `PairArith` asks `d ≡ 7 (mod 8)` and "every prime of `f` divides `d + 1`", which is all the setting uses. Since
  `2 ∣ d + 1`, the prime `2` needs no case of its own.
* The level `e` is free. No `e ≥ max(1, v₂(f))` is needed: `2^e ≤ |A|` comes from the surjection onto `H_e`, not from
  a unit `≡ 5 (mod 2^{e+2})` and `≡ 1` on the odd part of `f`, and the bounds on `A₀` and `QS` hold for every `e`.
* `K` is defined as a kernel, so that `A ↪ H_e × ℂˣ` is `QuotientGroup.lift` of `pairMap` and its injectivity is the
  first isomorphism theorem; `κ` and the map to `H_e` are its two coordinates.
-/

open DirichletCharacter NumberField

namespace ZetaBalance

/-! ## The arithmetic of a pair -/

/-- **What the setting of a pair needs**: primes `q ≡ 3 (mod 8)` and `d ≡ 7 (mod 8)` with `q ∣ d + 1`, every prime of
`f` dividing `d + 1`, and `f < q`. -/
structure PairArith (f q d : ℕ) : Prop where
  /-- `q` is prime. -/
  q_prime : q.Prime
  /-- `d` is prime. -/
  d_prime : d.Prime
  /-- `q ≡ 3 (mod 8)`. -/
  q_mod : q % 8 = 3
  /-- `d ≡ 7 (mod 8)`. -/
  d_mod : d % 8 = 7
  /-- `q ∣ d + 1`. -/
  q_dvd : q ∣ d + 1
  /-- Every prime of `f` divides `d + 1`. -/
  f_dvd : ∀ p : ℕ, p.Prime → p ∣ f → p ∣ d + 1
  /-- `f < q`. -/
  f_lt_q : f < q

/-- **A pair of `WinPair ε Y` has the arithmetic of a setting** once `f ≤ Y^{ε/5}/2`: the primes of `f` are at most
`Y^{ε/5}`, and `f < log q < q`. -/
theorem _root_.ZetaTwist.WinPair.pairArith {ε Y : ℝ} {q d f : ℕ} [NeZero f] (h : ZetaTwist.WinPair ε Y q d)
    (hf : (f : ℝ) ≤ Y ^ (ε / 5) / 2) : PairArith f q d where
  q_prime := h.q_prime
  d_prime := h.d_prime
  q_mod := h.q_mod
  d_mod := by have := h.d_mod; omega
  q_dvd := h.q_dvd
  f_dvd p hp hpf := by
    rcases eq_or_ne p 2 with rfl | hp2
    · have := h.d_mod; omega
    · have h1 : (p : ℝ) ≤ f := by exact_mod_cast Nat.le_of_dvd (NeZero.pos f) hpf
      have h2 : (1 : ℝ) ≤ f := by exact_mod_cast NeZero.one_le
      exact h.small_dvd p hp hp2 (by linarith)
  f_lt_q := by
    have h1 := Real.log_le_sub_one_of_pos (Nat.cast_pos.2 h.q_prime.pos)
    have : (f : ℝ) < q := by linarith [h.q_size.1]
    exact_mod_cast this

/-- **`(p/d) = 1` for every prime `p ∣ d + 1`**, when `d ≡ 7 (mod 8)`: at `p = 2` by `d ≡ 7 (mod 8)`; at odd `p`,
`(d/p) = (−1/p) = χ₄(p)` and reciprocity with `d ≡ 3 (mod 4)` gives `(p/d) = χ₄(p)(d/p)`. -/
theorem legendreSym_eq_one_of_dvd {d p : ℕ} [Fact d.Prime] (hd : d % 8 = 7) (hp : p.Prime) (hpd : p ∣ d + 1) :
    legendreSym d p = 1 := by
  have hd2 : d ≠ 2 := by omega
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [Nat.cast_ofNat, legendreSym.at_two hd2, ZMod.χ₈_nat_eq_if_mod_eight]
    simp [hd, show d % 2 = 1 by omega]
  have := Fact.mk hp
  have hdp : legendreSym p d = legendreSym p (-1) := by
    have h0 : (((d + 1 : ℕ) : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff]; exact hpd
    have : ((d : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) := by
      push_cast at h0 ⊢; linear_combination h0
    rw [legendreSym, legendreSym, this]
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by have := hp.mod_two_eq_one_iff_ne_two.2 hp2; omega
  rcases h4 with h4 | h4
  · rw [legendreSym.quadratic_reciprocity_one_mod_four h4 hd2, hdp, legendreSym.at_neg_one hp2,
      ZMod.χ₄_nat_one_mod_four h4]
  · rw [legendreSym.quadratic_reciprocity_three_mod_four h4 (by omega), hdp, legendreSym.at_neg_one hp2,
      ZMod.χ₄_nat_three_mod_four h4, neg_neg]

/-! ## The group `H_e` -/

/-- `H_e = (ℤ/2^{e+2})ˣ/{±1}`. -/
abbrev He (e : ℕ) : Type := (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)

/-- **`|H_e| = 2^e`**: `(ℤ/2^{e+2})ˣ` has `φ(2^{e+2}) = 2^{e+1}` elements and `−1` has order `2`. -/
theorem card_He (e : ℕ) : Nat.card (He e) = 2 ^ e := by
  have : Fact (1 < 2 ^ (e + 2)) := ⟨Nat.one_lt_two_pow (by omega)⟩
  have h1 := Subgroup.card_mul_index (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  have h2 : orderOf (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 2 := by
    rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one, ZMod.ringChar_zmod_n, ite_eq_right]
    have : 2 ^ (e + 2) = 4 * 2 ^ e := by ring
    have := Nat.one_le_two_pow (n := e)
    omega
  rw [Nat.card_zpowers, h2, Subgroup.index, Nat.card_eq_fintype_card (α := (ZMod _)ˣ), ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega), show e + 2 - 1 = e + 1 by omega,
    show 2 ^ (e + 1) = 2 * 2 ^ e by ring] at h1
  have : 2 * Nat.card (He e) = 2 * 2 ^ e := h1.trans (by ring)
  omega

/-- The unit `5` of `ℤ/2^{e+2}`. -/
noncomputable def fiveUnit (e : ℕ) : (ZMod (2 ^ (e + 2)))ˣ :=
  ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right _ (by norm_num))

/-- **The class of `5` has order `2^e` in `H_e`**: `5` has order `2^e` mod `2^{e+2}` (`ZMod.orderOf_five`), and no
power of `5` is `−1`, as `5 ≡ 1 (mod 4)`. -/
theorem orderOf_fiveUnit (e : ℕ) : orderOf (fiveUnit e : He e) = 2 ^ e := by
  have h5 : orderOf (fiveUnit e) = 2 ^ e := by
    rw [← orderOf_units, fiveUnit, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, ZMod.orderOf_five]
  cases e with
  | zero =>
    have h1 := orderOf_dvd_natCard (fiveUnit 0 : He 0)
    rw [card_He, pow_zero, Nat.dvd_one] at h1
    rw [h1, pow_zero]
  | succ n =>
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
      rintro ⟨k, hk⟩
      rcases Int.even_or_odd k with hk2 | hk2
      · rw [hk2.neg_one_zpow] at hk
        have := orderOf_dvd_of_pow_eq_one hk.symm
        rw [h5] at this
        exact absurd (Nat.le_of_dvd (by positivity) this) (by rw [pow_succ]; omega)
      · rw [hk2.neg_one_zpow] at hk
        have h4 := congrArg (fun u : (ZMod (2 ^ (n + 1 + 2)))ˣ =>
          ZMod.castHom (show 4 ∣ 2 ^ (n + 1 + 2) from ⟨2 ^ (n + 1), by ring⟩) (ZMod 4) (u : ZMod _)) hk
        simp only [Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val, fiveUnit, ZMod.coe_unitOfCoprime,
          map_neg, map_one, map_pow, map_natCast] at h4
        revert h4
        rw [show ((5 : ℕ) : ZMod 4) = 1 from rfl, one_pow]
        decide
    · rw [← QuotientGroup.mk_pow, ← h5, pow_orderOf_eq_one, QuotientGroup.mk_one]

/-- **`H_e` is cyclic**, generated by the class of `5`. -/
instance isCyclic_He (e : ℕ) : IsCyclic (He e) :=
  isCyclic_of_orderOf_eq_card _ ((orderOf_fiveUnit e).trans (card_He e).symm)

/-! ## Characters of a finite abelian group -/

section Characters

variable {A : Type*} [CommGroup A] [Fintype A]

/-- `|A₀| = |ker κ|`. -/
theorem card_A₀ (κ : A →* ℂˣ) : (A₀ κ).card = Nat.card κ.ker := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by rw [mem_A₀, MonoidHom.mem_ker])

/-- `orderOf κ = |κ(A)|`: the image is a finite subgroup of `ℂˣ`, so cyclic, of order its exponent, which is the
order of `κ`. -/
theorem orderOf_eq_card_range (κ : A →* ℂˣ) : orderOf κ = Nat.card κ.range := by
  have : Finite κ.range := Finite.of_surjective _ κ.rangeRestrict_surjective
  rw [← IsCyclic.exponent_eq_card]
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (MonoidHom.ext fun a => ?_))
    (Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_)
  · simpa using congrArg Subtype.val (Monoid.pow_exponent_eq_one (⟨κ a, a, rfl⟩ : κ.range))
  · obtain ⟨_, a, rfl⟩ := y
    refine Subtype.ext ?_
    simp [← MonoidHom.pow_apply, pow_orderOf_eq_one]

/-- **`|A| = o·|A₀|`** for a character `κ` of order `o`: `|A| = |κ(A)|·|ker κ|` and `|κ(A)| = o`. -/
theorem card_A_eq (κ : A →* ℂˣ) : Fintype.card A = orderOf κ * (A₀ κ).card := by
  rw [card_A₀, orderOf_eq_card_range, ← Subgroup.index_ker, mul_comm, Subgroup.card_mul_index,
    Nat.card_eq_fintype_card]

end Characters

/-! ## The setting of a pair -/

/-- `QS(e) = lcm(2^{e+2}, f)`, the modulus of the setting of a pair at level `e`. -/
def pairQS (f e : ℕ) : ℕ := Nat.lcm (2 ^ (e + 2)) f

/-- `QS(e) ≠ 0`. -/
instance pairQS_neZero (f e : ℕ) [NeZero f] : NeZero (pairQS f e) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne f)⟩

/-- The map `(ℤ/QS)ˣ → H_e × ℂˣ`, `u ↦ ([u mod 2^{e+2}], χ(u mod f))`. Its kernel is the `K` of the setting,
`{u ≡ ±1 (mod 2^{e+2}) : χ(u) = 1}`. -/
noncomputable def pairMap {f : ℕ} (χ : DirichletCharacter ℂ f) (e : ℕ) : (ZMod (pairQS f e))ˣ →* He e × ℂˣ :=
  ((QuotientGroup.mk' _).comp (ZMod.unitsMap (Nat.dvd_lcm_left _ _))).prod
    (χ.toUnitHom.comp (ZMod.unitsMap (Nat.dvd_lcm_right _ _)))

/-- **The setting of a pair** `(q, d)` at level `e`: `QS = lcm(2^{e+2}, f)` and `K = {u ≡ ±1 (mod 2^{e+2}) : χ(u) = 1}`.
`(2/d) = (q/d) = 1` and `Setting.split` hold as `2`, `q` and the primes of `f` divide `d + 1`; `q ∤ QS` as `q` is odd
and `q > f`. -/
noncomputable def pairSetting {f q d : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) (h : PairArith f q d) (e : ℕ) :
    Setting where
  q := q
  d := d
  QS := pairQS f e
  K := (pairMap χ e).ker
  q_prime := ⟨h.q_prime⟩
  d_prime := ⟨h.d_prime⟩
  q_mod_four := by have := h.q_mod; omega
  two_mod_d := by
    have := Fact.mk h.d_prime
    exact_mod_cast legendreSym_eq_one_of_dvd h.d_mod Nat.prime_two (by have := h.d_mod; omega)
  q_mod_d := by
    have := Fact.mk h.d_prime
    exact legendreSym_eq_one_of_dvd h.d_mod h.q_prime h.q_dvd
  q_coprime := by
    refine Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_right ?_ ?_)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes h.q_prime Nat.prime_two).2 (by have := h.q_mod; omega))
    · exact (Nat.Prime.coprime_iff_not_dvd h.q_prime).2 fun hq =>
        absurd (Nat.le_of_dvd (NeZero.pos f) hq) (not_le.2 h.f_lt_q)
  split p hp hpQ := by
    have := Fact.mk h.d_prime
    refine legendreSym_eq_one_of_dvd h.d_mod hp ?_
    rcases (Nat.Prime.dvd_mul hp).1 (hpQ.trans (Nat.lcm_dvd_mul _ _)) with h2 | hf
    · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)]
      have := h.d_mod
      omega
    · exact h.f_dvd p hp hf

variable {f q d : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) (h : PairArith f q d) (e : ℕ)

/-- **`QS ≤ 4·2^e·f`**, as `lcm(2^{e+2}, f) ∣ 2^{e+2} f`. -/
theorem QS_le : (pairSetting χ h e).QS ≤ 4 * 2 ^ e * f :=
  (Nat.le_of_dvd (Nat.mul_pos (by positivity) (NeZero.pos f)) (Nat.lcm_dvd_mul _ _)).trans_eq (by ring)

/-- **The level**: `log N ≤ log(4·2^e·f) + log q + log d`, as `N = QS·q·d`. -/
theorem log_N_le : Real.log (pairSetting χ h e).N ≤ Real.log (4 * 2 ^ e * f) + Real.log q + Real.log d := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.2 h.q_prime.pos
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 h.d_prime.pos
  have hQ : (0 : ℝ) < (pairSetting χ h e).QS := Nat.cast_pos.2 (NeZero.pos _)
  have hN : (pairSetting χ h e).N = (pairSetting χ h e).QS * q * d := rfl
  rw [hN, Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) hd.ne', Real.log_mul hQ.ne' hq.ne']
  gcongr
  exact_mod_cast QS_le χ h e

/-- The embedding `A → H_e × ℂˣ`, `[u] ↦ ([u mod 2^{e+2}], χ(u mod f))`, induced by `pairMap`. -/
noncomputable def pairLift : (pairSetting χ h e).A →* He e × ℂˣ :=
  QuotientGroup.lift (M := He e × ℂˣ) (pairSetting χ h e).K (pairMap χ e) le_rfl

/-- `A → H_e × ℂˣ` is injective, as `K` is the kernel of `pairMap`. -/
theorem pairLift_injective : Function.Injective (pairLift χ h e) := by
  intro a b hab
  obtain ⟨u, rfl⟩ := (pairSetting χ h e).mkA_surjective a
  obtain ⟨v, rfl⟩ := (pairSetting χ h e).mkA_surjective b
  change pairMap χ e u = pairMap χ e v at hab
  have key (u v : (ZMod (pairQS f e))ˣ) (huv : pairMap χ e u = pairMap χ e v) : pairMap χ e (u⁻¹ * v) = 1 := by
    rw [map_mul, map_inv, huv]
    exact inv_mul_cancel (pairMap χ e v)
  exact (QuotientGroup.mk'_eq_mk' _).2 ⟨u⁻¹ * v, key u v hab, mul_inv_cancel_left u v⟩

/-- **The character `κ`** of `A = (ℤ/QS)ˣ/K` induced by `χ`: `κ([u]) = χ(u mod f)`. -/
noncomputable def pairChar : (pairSetting χ h e).A →* ℂˣ := (MonoidHom.snd _ _).comp (pairLift χ h e)

/-- **`κ` lifts `χ`**: `κ̃` and `χ` at the level `QS` are both `MulChar.ofUnitHom` of `u ↦ χ(u mod f)`. -/
theorem pairChar_lifts : (pairSetting χ h e).Lifts (pairChar χ h e) χ :=
  ⟨Nat.dvd_lcm_right _ _, (congrArg MulChar.ofUnitHom (MonoidHom.ext fun _ => rfl)).trans (changeLevel_def χ _).symm⟩

/-- **`2^e ≤ |A|`**: `A` maps onto `H_e`, as `(ℤ/QS)ˣ → (ℤ/2^{e+2})ˣ` is onto. -/
theorem two_pow_le_card_A : 2 ^ e ≤ Fintype.card (pairSetting χ h e).A := by
  rw [← card_He e, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_surjective ((MonoidHom.fst _ _).comp (pairLift χ h e)) fun y => ?_
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective (show 2 ^ (e + 2) ∣ pairQS f e from Nat.dvd_lcm_left _ _) v
  exact ⟨(pairSetting χ h e).mkA u, rfl⟩

/-- `A₀ = ker κ` embeds in `H_e`: a class of `A₀` with trivial image in `H_e` has trivial image in `H_e × ℂˣ`. -/
theorem injective_ker : Function.Injective
    (((MonoidHom.fst _ _).comp (pairLift χ h e)).comp (pairChar χ h e).ker.subtype) := fun a b hab =>
  Subtype.ext (pairLift_injective χ h e (Prod.ext hab ((MonoidHom.mem_ker.1 a.2).trans (MonoidHom.mem_ker.1 b.2).symm)))

/-- **`A₀ = ker κ` is cyclic**, as a subgroup of the cyclic group `H_e`. -/
instance isCyclic_ker : IsCyclic (pairChar χ h e).ker := isCyclic_of_injective _ (injective_ker χ h e)

/-- **`|A₀| ≤ 2^e`**, as `A₀` embeds in `H_e`. -/
theorem card_A₀_le : (A₀ (pairChar χ h e)).card ≤ 2 ^ e := by
  rw [card_A₀, ← card_He e]
  exact Nat.card_le_card_of_injective _ (injective_ker χ h e)

/-! ## The discriminant of `E` -/

/-- **`|d_E| ≤ N^{[E:ℚ]}`**: `|d_E|^{[ℚ(ζ_N):E]}` divides `|d_{ℚ(ζ_N)}| ≤ N^{φ(N)}`, and
`φ(N) = [ℚ(ζ_N):E]·[E:ℚ]`. -/
theorem natAbs_discr_le (S : Setting) : (discr S.E).natAbs ≤ S.N ^ Module.finrank ℚ S.E := by
  have h1 := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow S.E (𝓞 S.E) S.M (𝓞 S.M)
  have h2 := IsCyclotomicExtension.Rat.natAbs_discr S.N S.M
  have h3 := Module.finrank_mul_finrank ℚ S.E S.M
  rw [IsCyclotomicExtension.Rat.finrank S.N S.M] at h3
  refine (Nat.pow_le_pow_iff_left (Module.finrank_pos (R := S.E) (M := S.M)).ne').1 ?_
  calc (discr S.E).natAbs ^ Module.finrank S.E S.M ≤ (discr S.M).natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.2 (discr_ne_zero S.M)) (Dvd.intro_left _ h1.symm)
    _ ≤ S.N ^ S.N.totient := h2 ▸ Nat.div_le_self _ _
    _ = (S.N ^ Module.finrank ℚ S.E) ^ Module.finrank S.E S.M := by rw [← pow_mul, h3]

/-- **`log(2 v_E) ≤ log N`** for every setting: `2 v_E = |d_E|^{1/[E:ℚ]} ≤ N` (`natAbs_discr_le`). -/
theorem log_vE_le (S : Setting) : Real.log (2 * S.vE) ≤ Real.log S.N := by
  have hn : Module.finrank ℚ S.E ≠ 0 := Module.finrank_pos.ne'
  have hd : (0 : ℝ) < |(discr S.E : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero S.E))
  have h2 : 2 * S.vE = |(discr S.E : ℝ)| ^ ((Module.finrank ℚ S.E : ℝ)⁻¹) := by rw [Setting.vE]; ring
  rw [h2]
  refine Real.log_le_log (Real.rpow_pos_of_pos hd _) ?_
  calc |(discr S.E : ℝ)| ^ ((Module.finrank ℚ S.E : ℝ)⁻¹)
      ≤ ((S.N : ℝ) ^ Module.finrank ℚ S.E) ^ ((Module.finrank ℚ S.E : ℝ)⁻¹) := by
        gcongr
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        exact_mod_cast natAbs_discr_le S
    _ = S.N := Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hn

end ZetaBalance

#print axioms ZetaTwist.WinPair.pairArith
#print axioms ZetaBalance.pairChar_lifts
#print axioms ZetaBalance.two_pow_le_card_A
#print axioms ZetaBalance.card_A_eq
#print axioms ZetaBalance.isCyclic_ker
#print axioms ZetaBalance.card_A₀_le
#print axioms ZetaBalance.QS_le
#print axioms ZetaBalance.log_N_le
#print axioms ZetaBalance.log_vE_le
