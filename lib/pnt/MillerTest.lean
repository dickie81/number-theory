/-
# Miller's primality test with small bases

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. Write `n − 1 = 2^s d` with `d` odd. An odd `n` is a strong probable prime to the base `a` if
`a^d ≡ 1` or `a^{2^r d} ≡ −1 (mod n)` for some `r < s` (`StrongProbablePrime`). Every odd prime is one to every base
prime to it (`strongProbablePrime_of_prime`). For every `A > 12` there is `C` such that every odd composite `n` fails
the test at some prime base `a ≤ C(log(n + 2))^A` prime to `n` (`exists_witness_le`). So an odd `n ≥ 3` is prime if
and only if it passes the test at every base `a ≤ C(log(n + 2))^A` prime to `n`
(`prime_iff_forall_strongProbablePrime`): Miller's test, deterministic, with `C(log n)^A` bases. No hypothesis.

G. L. Miller (1976) proved this under the extended Riemann hypothesis, and E. Bach (1990) showed that the bases
`a < 2(log n)²` suffice. M. O. Rabin (1980) made the test probabilistic and unconditional, and M. Agrawal, N. Kayal and
N. Saxena (2004) gave an unconditional deterministic polynomial-time test of another kind. Here the half-plane stands
in for the hypothesis, through `SmallPrimes.exists_prime_not_mem`: every proper subgroup of `(ℤ/nℤ)ˣ` misses a prime
`a ≤ C(log(n + 2))^A`.

* `strongProbablePrime_of_prime`: in the field `ℤ/pℤ`, `a^{2^s d} = 1`, and the first `1` in the sequence
  `a^d, a^{2d}, …` is `1` or follows `−1`, since `x² = 1` forces `x = ±1`.
* `exists_subgroup_prime_pow`: for `n = pᵏ`, `k ≥ 2`, the strong liars satisfy `a^{n−1} = 1`, and `1 + p` does not: its
  order `p^{k−1}` (Mathlib's `ZMod.orderOf_one_add_prime`) does not divide `n − 1 ≡ −1 (mod p)`.
* `exists_subgroup_mul`: for `n = n₁n₂` with coprime odd factors `n₁, n₂ ≥ 3`, let `2^t` be the largest power with
  `b^{2^t d} = −1` for some unit `b` (`b = −1` gives `t ≥ 0`). The strong liars lie in `J = {u : u^{2^t d} = ±1}`.
  The unit `c ≡ b (mod n₁)`, `c ≡ 1 (mod n₂)` (Mathlib's `ZMod.chineseRemainder`) is not in `J`, since its power
  `c^{2^t d}` is `−1 mod n₁` and `1 mod n₂`.
* `exists_subgroup_of_not_prime`: an odd composite `n` is a prime power `pᵏ`, `k ≥ 2`, or the product of its `p`-part
  and the rest, for `p` its least prime factor.
-/
import SmallPrimes

namespace MillerTest

/-- `n` is a **strong probable prime** to the base `a`: with `n − 1 = 2^s d` and `d` odd, `a^d = 1` or
`a^{2^r d} = −1` for some `r < s`. -/
def StrongProbablePrime (n : ℕ) (a : ZMod n) : Prop :=
  ∀ s d : ℕ, n - 1 = 2 ^ s * d → Odd d → a ^ d = 1 ∨ ∃ r < s, a ^ (2 ^ r * d) = -1

/-- **Every odd prime passes.** A prime `p` is a strong probable prime to every base `a ≢ 0 (mod p)`. -/
theorem strongProbablePrime_of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    StrongProbablePrime p a := by
  classical
  intro s d hsd _
  have hfermat : a ^ (2 ^ s * d) = 1 := by rw [← hsd]; exact ZMod.pow_card_sub_one_eq_one ha
  by_cases h0 : a ^ d = 1
  · exact Or.inl h0
  right
  have hex : ∃ r, a ^ (2 ^ r * d) = 1 := ⟨s, hfermat⟩
  have hle : Nat.find hex ≤ s := Nat.find_min' hex hfermat
  have hne0 : Nat.find hex ≠ 0 := by
    intro h
    have hspec := Nat.find_spec hex
    rw [h, pow_zero, one_mul] at hspec
    exact h0 hspec
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨k, by omega, ?_⟩
  have hsq : a ^ (2 ^ k * d) * a ^ (2 ^ k * d) = 1 := by
    rw [← pow_add, show 2 ^ k * d + 2 ^ k * d = 2 ^ (k + 1) * d by ring, ← hk]
    exact Nat.find_spec hex
  have hne : a ^ (2 ^ k * d) ≠ 1 := Nat.find_min hex (by omega)
  rcases mul_self_eq_one_iff.1 hsq with h | h
  · exact absurd h hne
  · exact h

/-- A strong liar is a Fermat liar: `a^{n−1} = 1`. -/
lemma pow_sub_one_eq_one {n : ℕ} {a : ZMod n} (ha : StrongProbablePrime n a) {s d : ℕ} (hsd : n - 1 = 2 ^ s * d)
    (hd : Odd d) : a ^ (n - 1) = 1 := by
  rcases ha s d hsd hd with h | ⟨r, hr, h⟩
  · rw [hsd, pow_mul', h, one_pow]
  · obtain ⟨j, rfl⟩ : ∃ j, s = r + 1 + j := ⟨s - (r + 1), by omega⟩
    rw [hsd, show 2 ^ (r + 1 + j) * d = 2 ^ r * d * (2 * 2 ^ j) by ring, pow_mul, h, pow_mul, neg_one_sq, one_pow]

/-- **Prime powers.** For `n = pᵏ`, `p` an odd prime and `k ≥ 2`, the strong liars lie in the proper subgroup
`{u : u^{n−1} = 1}`, which misses `1 + p`. -/
lemma exists_subgroup_prime_pow {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) :
    ∃ H : Subgroup (ZMod (p ^ k))ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod (p ^ k))ˣ, StrongProbablePrime (p ^ k) u → u ∈ H := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
  obtain ⟨s, d, hd, hsd⟩ := Nat.exists_eq_two_pow_mul_odd (show p ^ k - 1 ≠ 0 by omega)
  refine ⟨(powMonoidHom (p ^ k - 1)).ker, fun htop ↦ ?_, fun u hu ↦ ?_⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hord := ZMod.orderOf_one_add_prime hp hp2 k'
    have hw : IsUnit (1 + (p : ZMod (p ^ (k' + 1)))) :=
      (orderOf_pos_iff.1 (by rw [hord]; exact pow_pos hp.pos k')).isUnit
    have hmem : hw.unit ∈ (powMonoidHom (p ^ (k' + 1) - 1)).ker := by rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hmem
    have h1 : (1 + (p : ZMod (p ^ (k' + 1)))) ^ (p ^ (k' + 1) - 1) = 1 := by
      have := congrArg Units.val hmem
      rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at this
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    have h3 : p ∣ p ^ (k' + 1) - 1 := (dvd_pow_self p (by omega)).trans h2
    have h4 : p ∣ p ^ (k' + 1) := dvd_pow_self p (by omega)
    have h5 : p ∣ 1 := by
      have := Nat.dvd_sub h4 h3
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h5)
  · rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact pow_sub_one_eq_one hu hsd hd)

open scoped Classical in
/-- **Two coprime factors.** For `n = n₁n₂` with `n₁, n₂ ≥ 3` coprime and `n` odd, the strong liars lie in a proper
subgroup `J = {u : u^{2^t d} = ±1}` of `(ℤ/nℤ)ˣ`, where `2^t` is the largest power with `b^{2^t d} = −1` for a unit `b`;
the unit `c ≡ b (mod n₁)`, `c ≡ 1 (mod n₂)` is not in `J`. -/
lemma exists_subgroup_mul {n₁ n₂ : ℕ} (h₁ : 3 ≤ n₁) (h₂ : 3 ≤ n₂) (hodd : Odd (n₁ * n₂))
    (hcop : n₁.Coprime n₂) :
    ∃ H : Subgroup (ZMod (n₁ * n₂))ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod (n₁ * n₂))ˣ, StrongProbablePrime (n₁ * n₂) u → u ∈ H := by
  have hn9 : 9 ≤ n₁ * n₂ := Nat.mul_le_mul h₁ h₂
  obtain ⟨s, d, hd, hsd⟩ := Nat.exists_eq_two_pow_mul_odd (show n₁ * n₂ - 1 ≠ 0 by omega)
  have hs : 1 ≤ s := by
    by_contra h
    have h0 : s = 0 := by omega
    rw [h0, pow_zero, one_mul] at hsd
    obtain ⟨j, hj⟩ := hodd
    obtain ⟨i, hi⟩ := hd
    omega
  -- the largest `t ≤ s − 1` with a unit `b`, `b^{2^t d} = −1`
  set P : ℕ → Prop := fun r ↦ ∃ b : (ZMod (n₁ * n₂))ˣ, b ^ (2 ^ r * d) = -1 with hPdef
  have hP0 : P 0 := ⟨-1, by rw [pow_zero, one_mul, hd.neg_one_pow]⟩
  set t := Nat.findGreatest P (s - 1) with htdef
  have hPt : P t := Nat.findGreatest_spec (Nat.zero_le _) hP0
  set m := 2 ^ t * d with hmdef
  let J : Subgroup (ZMod (n₁ * n₂))ˣ :=
    { carrier := {u | u ^ m = 1 ∨ u ^ m = -1}
      one_mem' := Or.inl (one_pow m)
      mul_mem' := fun {a b} ha hb ↦ by
        change a ^ m = 1 ∨ a ^ m = -1 at ha
        change b ^ m = 1 ∨ b ^ m = -1 at hb
        change (a * b) ^ m = 1 ∨ (a * b) ^ m = -1
        rw [mul_pow]
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
      inv_mem' := fun {a} ha ↦ by
        change a ^ m = 1 ∨ a ^ m = -1 at ha
        change a⁻¹ ^ m = 1 ∨ a⁻¹ ^ m = -1
        rw [inv_pow]
        rcases ha with ha | ha
        · exact Or.inl (by rw [ha, inv_one])
        · exact Or.inr (by rw [ha, inv_neg_one]) }
  refine ⟨J, fun htop ↦ ?_, fun u hu ↦ ?_⟩
  · -- the unit `c ≡ b (mod n₁)`, `c ≡ 1 (mod n₂)` is not in `J`
    obtain ⟨b, hb⟩ := hPt
    have : Fact (2 < n₁) := ⟨by omega⟩
    have : Fact (2 < n₂) := ⟨by omega⟩
    set e := ZMod.chineseRemainder hcop
    set c₀ : ZMod (n₁ * n₂) := e.symm ((e b).1, 1) with hc₀
    have hb' : b ^ m = -1 := hb
    have hbm : (e (b : ZMod (n₁ * n₂))).1 ^ m = -1 := by
      have h1 : (b : ZMod (n₁ * n₂)) ^ m = -1 := by
        rw [← Units.val_pow_eq_pow_val, hb', Units.val_neg, Units.val_one]
      rw [← Prod.pow_fst, ← map_pow, h1, map_neg, map_one, Prod.fst_neg, Prod.fst_one]
    have hc₀m : e (c₀ ^ m) = (-1, 1) := by
      rw [map_pow, hc₀, RingEquiv.apply_symm_apply, Prod.pow_mk, hbm, one_pow]
    have hc₀u : IsUnit c₀ := by
      have h2 : c₀ ^ (m * 2) = 1 := by
        apply e.injective
        rw [pow_mul, map_pow, hc₀m, Prod.pow_mk, neg_one_sq, one_pow, map_one, Prod.mk_one_one]
      have hm0 : m ≠ 0 := by rw [hmdef]; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hd.pos.ne'
      exact IsUnit.of_pow_eq_one h2 (mul_ne_zero hm0 two_ne_zero)
    have hmem : hc₀u.unit ∈ J := by rw [htop]; exact Subgroup.mem_top _
    rcases hmem with h | h
    · have h' : c₀ ^ m = 1 := by
        have := congrArg Units.val h
        rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at this
      have := hc₀m
      rw [h', map_one, ← Prod.mk_one_one, Prod.mk.injEq] at this
      exact ZMod.neg_one_ne_one this.1.symm
    · have h' : c₀ ^ m = -1 := by
        have := congrArg Units.val h
        rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_neg, Units.val_one] at this
      have := hc₀m
      rw [h', map_neg, map_one, ← Prod.mk_one_one, Prod.neg_mk, Prod.mk.injEq] at this
      exact ZMod.neg_one_ne_one this.2
  · -- strong liars lie in `J`
    rcases hu s d hsd hd with h | ⟨r, hr, h⟩
    · left
      have hd1 : u ^ d = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)
      show u ^ m = 1
      rw [hmdef, pow_mul', hd1, one_pow]
    · have hur : u ^ (2 ^ r * d) = -1 :=
        Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]; exact h)
      have hrt : r ≤ t := Nat.le_findGreatest (by omega) ⟨u, hur⟩
      rcases eq_or_lt_of_le hrt with hrt | hrt
      · right
        show u ^ m = -1
        rw [hmdef, ← hrt, hur]
      · left
        show u ^ m = 1
        obtain ⟨j, hj⟩ : ∃ j, t = r + 1 + j := ⟨t - (r + 1), by omega⟩
        rw [hmdef, hj, show 2 ^ (r + 1 + j) * d = 2 ^ r * d * (2 * 2 ^ j) by ring, pow_mul, hur, pow_mul,
          neg_one_sq, one_pow]

/-- **The strong liars lie in a proper subgroup.** For every odd composite `n ≥ 3`, a proper subgroup of `(ℤ/nℤ)ˣ`
contains every unit to whose base `n` is a strong probable prime. -/
lemma exists_subgroup_of_not_prime {n : ℕ} (hodd : Odd n) (h3 : 3 ≤ n) (hn : ¬ n.Prime) :
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧ ∀ u : (ZMod n)ˣ, StrongProbablePrime n u → u ∈ H := by
  by_cases hpow : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpow
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k = 1 := by omega
      rw [hk1, pow_one] at hn
      exact hn hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
    exact exists_subgroup_prime_pow hp hp2 hk2
  · -- the `p`-part and the rest, for `p` the least prime factor
    obtain ⟨n₁, n₂, h₁, h₂, hcop, rfl⟩ :
        ∃ n₁ n₂ : ℕ, 3 ≤ n₁ ∧ 3 ≤ n₂ ∧ n₁.Coprime n₂ ∧ n₁ * n₂ = n := by
      have hn0 : n ≠ 0 := by omega
      have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hpn : n.minFac ∣ n := Nat.minFac_dvd n
      have hpodd : n.minFac ≠ 2 := by
        intro h2
        rw [h2] at hpn
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpn)
      have hp3 : 3 ≤ n.minFac := by have := hp.two_le; omega
      have he : 1 ≤ n.factorization n.minFac := hp.factorization_pos_of_dvd hn0 hpn
      have hmul := Nat.ordProj_mul_ordCompl_eq_self n n.minFac
      have hcop := (Nat.coprime_ordCompl hp hn0).pow_left (n.factorization n.minFac)
      refine ⟨n.minFac ^ n.factorization n.minFac, n / n.minFac ^ n.factorization n.minFac, ?_, ?_, hcop, hmul⟩
      · exact hp3.trans (Nat.le_self_pow (by omega) _)
      · have h2pos : 0 < n / n.minFac ^ n.factorization n.minFac := Nat.ordCompl_pos _ hn0
        have h2ne : n / n.minFac ^ n.factorization n.minFac ≠ 1 := by
          intro h1
          rw [h1, mul_one] at hmul
          exact hpow (hmul ▸ (hp.isPrimePow.pow (by omega)))
        have h2odd : Odd (n / n.minFac ^ n.factorization n.minFac) :=
          Nat.Odd.of_mul_right (hmul.symm ▸ hodd)
        obtain ⟨j, hj⟩ := h2odd
        omega
    exact exists_subgroup_mul h₁ h₂ hodd hcop

/-- **Miller's test with small bases.** For every `A > 12` there is `C > 0` such that every odd composite `n ≥ 3` has
a prime base `a ≤ C(log(n + 2))^A`, prime to `n`, to which `n` is not a strong probable prime. -/
theorem exists_witness_le {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, Odd n → 3 ≤ n → ¬ n.Prime →
      ∃ a : ℕ, a.Prime ∧ a.Coprime n ∧ (a : ℝ) ≤ C * Real.log (n + 2) ^ A ∧ ¬ StrongProbablePrime n a := by
  obtain ⟨C, hC, h⟩ := SmallPrimes.exists_prime_not_mem hA
  refine ⟨C, hC, fun n hodd h3 hn ↦ ?_⟩
  have : NeZero n := ⟨by omega⟩
  obtain ⟨H, hH, hsub⟩ := exists_subgroup_of_not_prime hodd h3 hn
  obtain ⟨a, hcop, ha, hle, hnot⟩ := h n H hH
  refine ⟨a, ha, hcop, hle, fun hspp ↦ hnot (hsub _ ?_)⟩
  rwa [ZMod.coe_unitOfCoprime]

/-- **Miller's test, deterministic.** For every `A > 12` there is `C > 0` such that an odd `n ≥ 3` is prime if and
only if `n` is a strong probable prime to every base `a ≤ C(log(n + 2))^A` prime to `n`. -/
theorem prime_iff_forall_strongProbablePrime {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, Odd n → 3 ≤ n →
      (n.Prime ↔ ∀ a : ℕ, a.Coprime n → (a : ℝ) ≤ C * Real.log (n + 2) ^ A → StrongProbablePrime n a) := by
  obtain ⟨C, hC, h⟩ := exists_witness_le hA
  refine ⟨C, hC, fun n hodd h3 ↦ ⟨fun hp a hcop _ ↦ ?_, fun hall ↦ ?_⟩⟩
  · have : Fact n.Prime := ⟨hp⟩
    refine strongProbablePrime_of_prime fun h0 ↦ ?_
    have hdvd : n ∣ a := (ZMod.natCast_eq_zero_iff a n).1 h0
    have := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd
    omega
  · by_contra hn
    obtain ⟨a, -, hcop, hle, hnot⟩ := h n hodd h3 hn
    exact hnot (hall a hcop hle)

end MillerTest

#print axioms MillerTest.strongProbablePrime_of_prime
#print axioms MillerTest.exists_witness_le
#print axioms MillerTest.prime_iff_forall_strongProbablePrime
