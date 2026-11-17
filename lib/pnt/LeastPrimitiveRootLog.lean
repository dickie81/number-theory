/-
# The least prime primitive root is at most a power of `log q`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. There is `K > 0` such that every modulus `q ≥ 1` whose units `(ℤ/qℤ)ˣ` are cyclic
(`q = 1, 2, 4, pᵏ, 2pᵏ` with `p` an odd prime: Mathlib's `ZMod.isCyclic_units_iff`) has a primitive root that is a
prime `ℓ ∤ q` with `ℓ ≤ K(log(q + 2))^{1820}` (`exists_prime_primRoot_le_log`). In particular every prime `p` has a
prime primitive root `ℓ ≤ K(log(p + 2))^{1820}` (`exists_prime_primRoot_le_log_prime`), and so does every power of
an odd prime (`exists_prime_primRoot_le_log_pow`). No hypothesis.

`LeastPrimitiveRoot.lean` has `ℓ ≤ C(d(φ(q))² log(q + 2))^A`, a power of `log q` only when `φ(q)` has boundedly many
divisors: Vinogradov's indicator of the primitive roots is a sum over the squarefree divisors of `φ(q)`, and each
divisor costs an error term. Here the primes `ℓ' ∣ φ(q)` are sifted, as V. Shoup does under GRH (1992). A unit `n`
is a primitive root exactly when it is an `ℓ'`-th power for no prime `ℓ' ∣ φ(q)`; the units that are `ℓ'`-th
powers for every `ℓ'` of a set `s` are those with `n^{φ(q)/∏ s} = 1`, in proportion `∏_{ℓ'∈s} 1/ℓ'`; and Brun's
sieve asks for these sums only for the sets `s` of its truncations, `w³²` of them for the primes below `w`. Under
GRH Shoup has the exponent `6` for a prime modulus. The exponent `1820 = 13·35·4` is what Brun's sieve gives with
the constants of this file (`Σ 1/ℓ' ≤ 3` on a range, the levels `14 + 2j`, `w ≤ 2^{140}(log q)⁴`); it is not
optimised, and a linear sieve in its place would give an exponent near `36`.

* `pow_div_prod_eq_one_iff`, `prod_yv`: for a unit `n` and primes `ℓ' ∈ s` dividing `m = φ(q)`,
  `∏_{s} [n^{m/ℓ'} = 1] = [n^{m/∏ s} = 1]`, from `gcd(m/ℓ₀, m/d) = m/(ℓ₀d)` for a prime `ℓ₀ ∤ d`.
* `card_pow_eq_one`, `card_char_pow_eq_one`: for `k ∣ m` and `(ℤ/qℤ)ˣ` cyclic, `a^k = 1` has `k` solutions, and `k`
  characters have `χ^k = 1` (`Σ_a Σ_χ χ^k(a)`, summed either way).
* `abs_sum_pow_eq_one_sub_le`, `abs_sum_yv_sub_le`: `|Σ_{n ≤ x} Λ(n)[n^k = 1] − (k/m) Re ψ(x, χ₀)| ≤
  C log(q + 2)x^{11/12+η}`, from `m[a^k = 1] = Σ_χ χ^k(a)` and `ChiUniform.psiChi_le_uniform`; so the sum over the
  `n` prime to `q` of `Λ(n) ∏_{s} yv(n, ℓ')` is `Re ψ(x, χ₀) ∏_{s} 1/ℓ'` within the same error.
* `fam`, `sum_fam_le`, `prod_fam_ge`, `card_fam_le`: the family `T_j` of the primes `ℓ' ∣ m` in
  `[w^{2^{−j−1}}, w^{2^{−j}})` has `Σ 1/ℓ' ≤ 3` (`SieveRanges.rng_sum_le_three`), `∏ (1 − 1/ℓ') ≥ e^{−6}` and fewer
  than `w^{2^{−j}}` primes.
* `gap_fam_le`, `terms_le`: at the levels `k_j = 14 + 2j` the gap of the sieve is at most half its main term
  (`SieveBrun.gap_le`, `SieveBrun.sum_levels_le`), and its truncations have at most `w³²` terms.
* `primRoot_ge`, `sum_primRoot_ge`: `Σ_{n ≤ x} Λ(n)[ord n = m] ≥ XV/2 − (J + 1)Ew³² − 2L(X/w + E)`, with
  `X = Re ψ(x, χ₀)`, `V = ∏_j ∏_{T_j} (1 − 1/ℓ')`, `E = C log(q + 2)x^{11/12+η}` and `L = log(q + 2)`: the primes
  below `w` by `SieveBrun.fundamentalW`, the at most `2L` primes from `w` on one at a time.
* `exists_level_spec`, `lower_pos`: the level `w = 2^{2^J}` with `8L ≤ √w` and `w ≤ 2^{140}L⁴`, at which
  `V ≥ 1/√w`, and the sizes at `x = (64(C + 1)w^{35})^{13}`.
-/
import LeastPrimitiveRoot
import SieveRangeSum
import SieveBrunW

open Real ChiPNT

noncomputable section

namespace LeastPrimitiveRoot

variable {q : ℕ} [NeZero q]

/-! ### Powers, and products of primes -/

/-- In a monoid, if `u^m = 1` and `s` is a set of primes whose product divides `m`, then `u^{m/ℓ} = 1` for every
`ℓ ∈ s` exactly when `u^{m/∏ s} = 1`: `gcd(m/ℓ₀, m/d) = m/(ℓ₀d)` for a prime `ℓ₀ ∤ d`. -/
lemma pow_div_prod_eq_one_iff {G : Type*} [Monoid G] {u : G} {m : ℕ} (hu : u ^ m = 1) (s : Finset ℕ)
    (hs : ∀ ℓ ∈ s, ℓ.Prime) (hd : ∏ ℓ ∈ s, ℓ ∣ m) :
    (∀ ℓ ∈ s, u ^ (m / ℓ) = 1) ↔ u ^ (m / ∏ ℓ ∈ s, ℓ) = 1 := by
  classical
  constructor
  · induction s using Finset.induction_on with
    | empty => intro _; simpa using hu
    | insert ℓ₀ s hℓ₀ ih =>
      intro h
      rw [Finset.prod_insert hℓ₀] at hd ⊢
      have hds : ∏ ℓ ∈ s, ℓ ∣ m := (Dvd.intro_left _ rfl).trans hd
      have hs' : ∀ ℓ ∈ s, ℓ.Prime := fun ℓ hℓ => hs ℓ (Finset.mem_insert_of_mem hℓ)
      have h2 := ih hs' hds (fun ℓ hℓ => h ℓ (Finset.mem_insert_of_mem hℓ))
      have h1 := h ℓ₀ (Finset.mem_insert_self _ _)
      have hp := hs ℓ₀ (Finset.mem_insert_self _ _)
      have hdpos : 0 < ∏ ℓ ∈ s, ℓ := Finset.prod_pos fun ℓ hℓ => (hs' ℓ hℓ).pos
      have hcop : Nat.Coprime (∏ ℓ ∈ s, ℓ) ℓ₀ := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
        intro hdvd
        obtain ⟨ℓ, hℓ, hℓdvd⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
        exact hℓ₀ ((Nat.prime_dvd_prime_iff_eq hp (hs' ℓ hℓ)).1 hℓdvd ▸ hℓ)
      obtain ⟨t, ht⟩ := hd
      have e1 : m / ℓ₀ = (∏ ℓ ∈ s, ℓ) * t := by
        rw [ht, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
      have e2 : m / ∏ ℓ ∈ s, ℓ = ℓ₀ * t := by
        rw [ht, mul_comm ℓ₀ (∏ ℓ ∈ s, ℓ), mul_assoc, Nat.mul_div_cancel_left _ hdpos]
      have e3 : m / (ℓ₀ * ∏ ℓ ∈ s, ℓ) = t := by
        rw [ht, Nat.mul_div_cancel_left _ (Nat.mul_pos hp.pos hdpos)]
      have hg : Nat.gcd ((∏ ℓ ∈ s, ℓ) * t) (ℓ₀ * t) = t := by
        rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
      rw [e3, ← hg]
      exact pow_gcd_eq_one.2 ⟨e1 ▸ h1, e2 ▸ h2⟩
  · intro h ℓ hℓ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun ℓ => ℓ) hℓ
    obtain ⟨t, ht⟩ := hd
    have hprodpos : 0 < ∏ ℓ ∈ s, ℓ := Finset.prod_pos fun ℓ hℓ => (hs ℓ hℓ).pos
    have e1 : m / ∏ ℓ ∈ s, ℓ = t := by rw [ht, Nat.mul_div_cancel_left _ hprodpos]
    have e2 : m / ℓ = t * c := by
      rw [ht, hc, mul_assoc, Nat.mul_div_cancel_left _ (hs ℓ hℓ).pos, mul_comm]
    rw [e2, pow_mul, ← e1, h, one_pow]

/-! ### The solutions of `a^k = 1`, and the characters with `χ^k = 1` -/

/-- In `ℤ/qℤ` with `(ℤ/qℤ)ˣ` cyclic, `a^k = 1` has exactly `k` solutions for `k ∣ φ(q)` (Mathlib's
`IsCyclic.card_orderOf_eq_totient` and `Nat.sum_totient`). -/
lemma card_pow_eq_one [IsCyclic (ZMod q)ˣ] {k : ℕ} (hk : k ∣ q.totient) :
    (Finset.univ.filter fun a : ZMod q => a ^ k = 1).card = k := by
  classical
  have hk0 : k ≠ 0 := fun h => totient_ne_zero (q := q) (Nat.eq_zero_of_zero_dvd (h ▸ hk))
  have hunits : (Finset.univ.filter fun u : (ZMod q)ˣ => u ^ k = 1).card = k := by
    rw [← sum_card_orderOf_eq_card_pow_eq_one hk0]
    have h : ∀ d ∈ k.divisors, (Finset.univ.filter fun u : (ZMod q)ˣ => orderOf u = d).card = d.totient :=
      fun d hd => IsCyclic.card_orderOf_eq_totient (by
        rw [ZMod.card_units_eq_totient]; exact (Nat.dvd_of_mem_divisors hd).trans hk)
    rw [Finset.sum_congr rfl h, Nat.sum_totient]
  have hset : (Finset.univ.filter fun a : ZMod q => a ^ k = 1) =
      (Finset.univ.filter fun u : (ZMod q)ˣ => u ^ k = 1).map ⟨Units.val, Units.val_injective⟩ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      have hu : IsUnit a := IsUnit.of_pow_eq_one h hk0
      refine ⟨hu.unit, ?_, hu.unit_spec⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hu.unit_spec, h, Units.val_one]
    · rintro ⟨u, hu, rfl⟩
      rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  rw [hset, Finset.card_map, hunits]

/-- The characters mod `q` with `χ^k = 1` number `k`, for `k ∣ φ(q)` and `(ℤ/qℤ)ˣ` cyclic: `Σ_a Σ_χ χ^k(a)`,
summed either way. -/
lemma card_char_pow_eq_one [IsCyclic (ZMod q)ˣ] {k : ℕ} (hk : k ∣ q.totient) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ^ k = 1).card = k := by
  classical
  have hk0 : k ≠ 0 := fun h => totient_ne_zero (q := q) (Nat.eq_zero_of_zero_dvd (h ▸ hk))
  have hm0 : (q.totient : ℂ) ≠ 0 := by exact_mod_cast totient_ne_zero (q := q)
  have h1 : ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, (χ ^ k) a = (q.totient : ℂ) * k := by
    have h : ∀ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, (χ ^ k) a =
        if a ^ k = 1 then (q.totient : ℂ) else 0 := by
      intro a
      rw [← DirichletCharacter.sum_characters_eq ℂ (a ^ k)]
      exact Finset.sum_congr rfl fun χ _ => by rw [MulChar.pow_apply' χ hk0, map_pow]
    rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.sum_filter, Finset.sum_const, card_pow_eq_one hk,
      nsmul_eq_mul, mul_comm]
  have h2 : ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, (χ ^ k) a =
      (q.totient : ℂ) * (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ^ k = 1).card := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun χ _ => sum_char_eq (χ ^ k), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact_mod_cast (mul_left_cancel₀ hm0 (h1.symm.trans h2)).symm

/-- **The prime powers `n ≤ x` with `n^k = 1` in `ℤ/qℤ`.** For every `η > 0` there is `C ≥ 0` such that for every
modulus `q ≥ 1` with `(ℤ/qℤ)ˣ` cyclic, `m = φ(q)`, every `k ∣ m` and every `x > 1`,
`|m Σ_{n ≤ x} Λ(n)[n^k = 1] − k·Re ψ(x, χ₀)| ≤ m·C log(q + 2)x^{11/12+η}`: the `k` characters with `χ^k = 1` give
`ψ(x, χ₀)` each, and each of the others at most `C log(q + 2)x^{11/12+η}` (`ChiUniform.psiChi_le_uniform`). -/
theorem abs_sum_pow_eq_one_sub_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], IsCyclic (ZMod q)ˣ → ∀ k : ℕ, k ∣ q.totient → ∀ x : ℝ, 1 < x →
      |(q.totient : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n *
          (if (n : ZMod q) ^ k = 1 then 1 else 0) - k * (psiChi (1 : DirichletCharacter ℂ q) x).re| ≤
        q.totient * (C * Real.log (q + 2) * x ^ (11 / 12 + η)) := by
  classical
  obtain ⟨C, hC, hψ⟩ := ChiUniform.psiChi_le_uniform hη
  refine ⟨C, hC, fun q _ hcyc k hk x hx => ?_⟩
  set B : ℝ := C * Real.log (q + 2) * x ^ (11 / 12 + η) with hBdef
  have hx0 : 0 < x := by linarith
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith)
    positivity
  have hk0 : k ≠ 0 := fun h => totient_ne_zero (q := q) (Nat.eq_zero_of_zero_dvd (h ▸ hk))
  -- the weighted sum by characters
  have hid : (((q.totient : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n *
      (if (n : ZMod q) ^ k = 1 then 1 else 0) : ℝ) : ℂ) = ∑ χ : DirichletCharacter ℂ q, psiChi (χ ^ k) x := by
    simp only [psiChi]
    rw [Finset.sum_comm]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_mul]
    have h : ∑ χ : DirichletCharacter ℂ q, (χ ^ k) (n : ZMod q) =
        if (n : ZMod q) ^ k = 1 then (q.totient : ℂ) else 0 := by
      rw [← DirichletCharacter.sum_characters_eq ℂ ((n : ZMod q) ^ k)]
      exact Finset.sum_congr rfl fun χ _ => by rw [MulChar.pow_apply' χ hk0, map_pow]
    rw [h]
    split_ifs <;> simp
  -- the characters with `χ^k = 1`, and the others
  have hsplit : ∑ χ : DirichletCharacter ℂ q, psiChi (χ ^ k) x =
      (k : ℂ) * psiChi (1 : DirichletCharacter ℂ q) x +
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ¬ χ ^ k = 1), psiChi (χ ^ k) x := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun χ : DirichletCharacter ℂ q => χ ^ k = 1)]
    congr 1
    rw [Finset.sum_congr rfl fun χ hχ => by rw [(Finset.mem_filter.1 hχ).2], Finset.sum_const,
      card_char_pow_eq_one hk, nsmul_eq_mul]
  have hrest : ‖∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ¬ χ ^ k = 1), psiChi (χ ^ k) x‖ ≤
      q.totient * B := by
    have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
    calc ‖∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ¬ χ ^ k = 1), psiChi (χ ^ k) x‖
        ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ¬ χ ^ k = 1), B :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ hχ => hψ q (χ ^ k) (Finset.mem_filter.1 hχ).2 x hx)
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, B :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => hB0
      _ = q.totient * B := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hre := congrArg Complex.re (hid.trans hsplit)
  have hkre : ((k : ℂ) * psiChi (1 : DirichletCharacter ℂ q) x).re =
      k * (psiChi (1 : DirichletCharacter ℂ q) x).re := by
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  rw [Complex.ofReal_re, Complex.add_re, hkre] at hre
  rw [hre, add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans hrest

/-! ### The residues of prime order -/

/-- `yv q n ℓ` is `1` when `n^{φ(q)/ℓ} = 1` in `ℤ/qℤ` and `0` otherwise: for a prime `ℓ ∣ φ(q)` and `n` prime to `q`,
whether `n` is an `ℓ`-th power in the cyclic group `(ℤ/qℤ)ˣ`. -/
def yv (q n ℓ : ℕ) : ℝ := if (n : ZMod q) ^ (q.totient / ℓ) = 1 then 1 else 0

lemma yv_nonneg (q n ℓ : ℕ) : 0 ≤ yv q n ℓ := by unfold yv; split_ifs <;> norm_num

lemma yv_le_one (q n ℓ : ℕ) : yv q n ℓ ≤ 1 := by unfold yv; split_ifs <;> norm_num

omit [NeZero q] in
/-- For `n` prime to `q` and primes `ℓ ∈ s` dividing `φ(q)`, `∏_{ℓ∈s} yv(n, ℓ) = [n^{φ(q)/∏ s} = 1]`. -/
lemma prod_yv {n : ℕ} (hn : IsUnit (n : ZMod q)) (s : Finset ℕ) (hs : ∀ ℓ ∈ s, ℓ.Prime ∧ ℓ ∣ q.totient) :
    ∏ ℓ ∈ s, yv q n ℓ = if (n : ZMod q) ^ (q.totient / ∏ ℓ ∈ s, ℓ) = 1 then 1 else 0 := by
  classical
  have hd : ∏ ℓ ∈ s, ℓ ∣ q.totient :=
    Finset.prod_primes_dvd _ (fun ℓ hℓ => (hs ℓ hℓ).1.prime) (fun ℓ hℓ => (hs ℓ hℓ).2)
  have hiff := pow_div_prod_eq_one_iff (pow_totient_eq_one hn) s (fun ℓ hℓ => (hs ℓ hℓ).1) hd
  unfold yv
  rw [Finset.prod_ite_zero, Finset.prod_const_one]
  exact if_congr hiff rfl rfl

open scoped Classical in
/-- The integers `1 ≤ n ≤ x` prime to `q`. -/
def unitsLe (q : ℕ) (x : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊x⌋₊).filter fun n => IsUnit (n : ZMod q)

lemma mem_unitsLe {q : ℕ} {x : ℝ} {n : ℕ} :
    n ∈ unitsLe q x ↔ n ∈ Finset.Icc 1 ⌊x⌋₊ ∧ IsUnit (n : ZMod q) := by
  classical
  rw [unitsLe, Finset.mem_filter]

/-- **The prime powers that are `ℓ`-th powers for every `ℓ ∈ s`.** For every `η > 0` there is `C ≥ 0` such that for
every modulus `q ≥ 1` with `(ℤ/qℤ)ˣ` cyclic, every finite set `s` of primes dividing `φ(q)` and every `x > 1`,
`|Σ_{n ≤ x, (n, q) = 1} Λ(n) ∏_{ℓ∈s} yv(n, ℓ) − Re ψ(x, χ₀) ∏_{ℓ∈s} 1/ℓ| ≤ C log(q + 2)x^{11/12+η}`. -/
theorem abs_sum_yv_sub_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], IsCyclic (ZMod q)ˣ → ∀ s : Finset ℕ,
      (∀ ℓ ∈ s, ℓ.Prime ∧ ℓ ∣ q.totient) → ∀ x : ℝ, 1 < x →
      |∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n * ∏ ℓ ∈ s, yv q n ℓ -
          (psiChi (1 : DirichletCharacter ℂ q) x).re * ∏ ℓ ∈ s, (1 / (ℓ : ℝ))| ≤
        C * Real.log (q + 2) * x ^ (11 / 12 + η) := by
  classical
  obtain ⟨C, hC, h⟩ := abs_sum_pow_eq_one_sub_le hη
  refine ⟨C, hC, fun q _ hcyc s hs x hx => ?_⟩
  have hm0 : q.totient ≠ 0 := totient_ne_zero
  have hmpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hd : ∏ ℓ ∈ s, ℓ ∣ q.totient :=
    Finset.prod_primes_dvd _ (fun ℓ hℓ => (hs ℓ hℓ).1.prime) (fun ℓ hℓ => (hs ℓ hℓ).2)
  have hd0 : ∏ ℓ ∈ s, ℓ ≠ 0 := fun h0 => hm0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hd))
  set k := q.totient / ∏ ℓ ∈ s, ℓ with hk
  have hkd : k ∣ q.totient := Nat.div_dvd_of_dvd hd
  have hk0 : k ≠ 0 := fun h0 => hm0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hkd))
  -- the sum over the units is the sum over all `n ≤ x`
  have hsum : ∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n * ∏ ℓ ∈ s, yv q n ℓ =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (if (n : ZMod q) ^ k = 1 then 1 else 0) := by
    rw [unitsLe, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hu hp hp
    · rw [prod_yv hu s hs, ← hk, ite_eq_left hp]
    · rw [prod_yv hu s hs, ← hk, ite_eq_right hp]
    · exact absurd (IsUnit.of_pow_eq_one hp hk0) hu
    · rw [mul_zero]
  have hprod : ∏ ℓ ∈ s, (1 / (ℓ : ℝ)) = (k : ℝ) / q.totient := by
    have hcast : ((∏ ℓ ∈ s, ℓ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hd0
    rw [hk, Nat.cast_div hd hcast, Finset.prod_div_distrib, Finset.prod_const_one, Nat.cast_prod]
    field_simp
  have h1 := h q hcyc k hkd x hx
  rw [hsum, hprod]
  have e : (q.totient : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n *
      (if (n : ZMod q) ^ k = 1 then 1 else 0) - k * (psiChi (1 : DirichletCharacter ℂ q) x).re =
      q.totient * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n *
        (if (n : ZMod q) ^ k = 1 then 1 else 0) - (psiChi (1 : DirichletCharacter ℂ q) x).re *
          ((k : ℝ) / q.totient)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hmpos] at h1
  exact le_of_mul_le_mul_left h1 hmpos

/-! ### The families of the sieve -/

/-- The primes `ℓ ∣ φ(q)` of the range `[w^{2^{−j−1}}, w^{2^{−j}})`. -/
def fam (q : ℕ) (w : ℝ) (j : ℕ) : Finset ℕ :=
  (SieveRanges.rng (w ^ ((1 / 2 : ℝ) ^ (j + 1)))).filter (· ∣ q.totient)

lemma mem_fam {q : ℕ} {w : ℝ} {j ℓ : ℕ} (h : ℓ ∈ fam q w j) : ℓ.Prime ∧ ℓ ∣ q.totient :=
  ⟨(SieveRanges.mem_rng.1 (Finset.mem_filter.1 h).1).1, (Finset.mem_filter.1 h).2⟩

lemma one_le_rpow_half {w : ℝ} (hw : 1 ≤ w) (j : ℕ) : 1 ≤ w ^ ((1 / 2 : ℝ) ^ j) :=
  Real.one_le_rpow hw (by positivity)

lemma fam_disjoint {q : ℕ} {w : ℝ} (hw : 1 ≤ w) {i j : ℕ} (hij : i ≠ j) : Disjoint (fam q w i) (fam q w j) :=
  Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
    (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (SieveRanges.rng_disjoint hw hij))

lemma sum_fam_le {q : ℕ} {w : ℝ} (hw : 1 ≤ w) (j : ℕ) : ∑ ℓ ∈ fam q w j, 1 / (ℓ : ℝ) ≤ 3 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun ℓ _ _ => by positivity).trans
    (SieveRanges.rng_sum_le_three (one_le_rpow_half hw (j + 1)))

/-- `e^{−2t} ≤ 1 − t` for `0 ≤ t ≤ 1/2`. -/
lemma exp_neg_two_mul_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : Real.exp (-(2 * t)) ≤ 1 - t := by
  have h := Real.add_one_le_exp (2 * t)
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by linarith)]
  refine le_trans ?_ h
  rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- `∏_{ℓ ∈ T_j} (1 − 1/ℓ) ≥ e^{−6}`. -/
lemma prod_fam_ge {q : ℕ} {w : ℝ} (hw : 1 ≤ w) (j : ℕ) :
    Real.exp (-6) ≤ ∏ ℓ ∈ fam q w j, (1 - 1 / (ℓ : ℝ)) := by
  have h1 : ∀ ℓ ∈ fam q w j, Real.exp (-(2 * (1 / (ℓ : ℝ)))) ≤ 1 - 1 / (ℓ : ℝ) := by
    intro ℓ hℓ
    have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast (mem_fam hℓ).1.two_le
    refine exp_neg_two_mul_le (by positivity) ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  calc Real.exp (-6) ≤ Real.exp (∑ ℓ ∈ fam q w j, -(2 * (1 / (ℓ : ℝ)))) := by
        apply Real.exp_le_exp.2
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
        linarith [sum_fam_le (q := q) hw j]
    _ = ∏ ℓ ∈ fam q w j, Real.exp (-(2 * (1 / (ℓ : ℝ)))) := Real.exp_sum _ _
    _ ≤ ∏ ℓ ∈ fam q w j, (1 - 1 / (ℓ : ℝ)) :=
        Finset.prod_le_prod₀ (fun ℓ _ => (Real.exp_pos _).le) h1

/-- A family has fewer than `w^{2^{−j}}` primes. -/
lemma card_fam_le {q : ℕ} {w : ℝ} (hw : 1 ≤ w) (j : ℕ) :
    ((fam q w j).card : ℝ) + 1 ≤ w ^ ((1 / 2 : ℝ) ^ j) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = w ^ ((1 / 2 : ℝ) ^ (j + 1)) := ⟨_, rfl⟩
  have hA2 : A ^ 2 = w ^ ((1 / 2 : ℝ) ^ j) := by rw [hA]; exact SieveRanges.sq_rpow_half (by linarith) j
  have h1 : 1 ≤ A ^ 2 := by rw [hA2]; exact one_le_rpow_half hw j
  have hsub : fam q w j ⊆ Finset.Ico 2 ⌈A ^ 2⌉₊ := by
    intro ℓ hℓ
    have hmem := SieveRanges.mem_rng.1 (Finset.mem_filter.1 hℓ).1
    rw [← hA] at hmem
    exact Finset.mem_Ico.2 ⟨hmem.1.two_le, Nat.lt_ceil.2 hmem.2.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  have hceil : (⌈A ^ 2⌉₊ : ℝ) < A ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  rw [← hA2]
  by_cases h2 : 2 ≤ ⌈A ^ 2⌉₊
  · have : ((fam q w j).card : ℝ) ≤ (⌈A ^ 2⌉₊ : ℝ) - 2 := by
      have h := (Nat.cast_le (α := ℝ)).2 hcard
      rwa [Nat.cast_sub h2] at h
    linarith
  · have h0 : (fam q w j).card = 0 := by omega
    rw [h0]; simpa using h1

/-- `e⁶ ≤ 404`. -/
lemma exp_six_le : Real.exp 6 ≤ 404 := by
  have h1 := Real.exp_one_lt_d9
  have h : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 6
    _ ≤ 404 := by norm_num

/-- **The gap of the sieve** at the levels `k_j = 14 + 2j`: at most half the main term. -/
lemma gap_fam_le {q : ℕ} {w : ℝ} (hw : 1 ≤ w) (J : ℕ) :
    ∑ j : Fin J, SieveBrun.esym (fam q w j) (fun ℓ => 1 / (ℓ : ℝ)) (14 + 2 * (j : ℕ)) *
        ∏ i ∈ Finset.univ.erase j, SieveBrun.trunc (fam q w i) (fun ℓ => 1 / (ℓ : ℝ)) (14 + 2 * (i : ℕ)) ≤
      (∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - 1 / (ℓ : ℝ))) * (1 / 2) := by
  have hg0 : ∀ j : Fin J, ∀ ℓ ∈ fam q w j, (0 : ℝ) ≤ 1 / (ℓ : ℝ) := fun j ℓ _ => by positivity
  have hg1 : ∀ j : Fin J, ∀ ℓ ∈ fam q w j, 1 / (ℓ : ℝ) ≤ 1 := fun j ℓ hℓ => by
    have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast (mem_fam hℓ).1.two_le
    rw [div_le_one (by linarith)]; linarith
  have h := SieveBrun.gap_le (fun j : Fin J => fam q w j) (fun j : Fin J => 14 + 2 * (j : ℕ))
    (fun j => ⟨7 + (j : ℕ), by ring⟩) hg0 hg1 (C₀ := 3) (c₀ := Real.exp (-6)) (by norm_num) (Real.exp_pos _)
    (fun j => sum_fam_le hw j) (fun j => prod_fam_ge hw j)
  have hV0 : 0 ≤ ∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - 1 / (ℓ : ℝ)) :=
    Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun ℓ hℓ => by linarith [hg1 j ℓ hℓ]
  have he6 := exp_six_le
  have hinv : (Real.exp (-6))⁻¹ = Real.exp 6 := by rw [Real.exp_neg, inv_inv]
  -- the sum of the levels
  have hS1 : ∑ j : Fin J, (3 : ℝ) ^ (14 + 2 * (j : ℕ)) / ((14 + 2 * (j : ℕ)).factorial : ℝ) ≤
      2 * ((3 : ℝ) ^ 14 / (Nat.factorial 14 : ℝ)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (3 : ℝ) ^ (14 + 2 * j) / ((14 + 2 * j).factorial : ℝ)) J]
    exact SieveBrun.sum_levels_le (by norm_num) (by norm_num) J
  -- the product
  have hS2 : ∏ i : Fin J, (1 + (3 : ℝ) ^ (14 + 2 * (i : ℕ) + 1) /
      (((14 + 2 * (i : ℕ) + 1).factorial : ℝ) * Real.exp (-6))) ≤ 3 := by
    refine (SieveBrun.prod_one_add_le_exp _ _ fun i _ => by positivity).trans ?_
    have hsum : ∑ i : Fin J, (3 : ℝ) ^ (14 + 2 * (i : ℕ) + 1) /
        (((14 + 2 * (i : ℕ) + 1).factorial : ℝ) * Real.exp (-6)) ≤ 1 := by
      have e : ∀ i : Fin J, (3 : ℝ) ^ (14 + 2 * (i : ℕ) + 1) /
          (((14 + 2 * (i : ℕ) + 1).factorial : ℝ) * Real.exp (-6)) =
          Real.exp 6 * ((3 : ℝ) ^ (15 + 2 * (i : ℕ)) / ((15 + 2 * (i : ℕ)).factorial : ℝ)) := by
        intro i
        rw [show 14 + 2 * (i : ℕ) + 1 = 15 + 2 * (i : ℕ) by ring, ← hinv]
        field_simp
      rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum,
        Fin.sum_univ_eq_sum_range (fun j => (3 : ℝ) ^ (15 + 2 * j) / ((15 + 2 * j).factorial : ℝ)) J]
      have h15 := SieveBrun.sum_levels_le (C := 3) (by norm_num) (k := 15) (by norm_num) J
      have hnum : (404 : ℝ) * (2 * ((3 : ℝ) ^ 15 / (Nat.factorial 15 : ℝ))) ≤ 1 := by
        norm_num [Nat.factorial]
      have hnn : (0 : ℝ) ≤ 2 * ((3 : ℝ) ^ 15 / (Nat.factorial 15 : ℝ)) := by positivity
      calc Real.exp 6 * ∑ j ∈ Finset.range J, (3 : ℝ) ^ (15 + 2 * j) / ((15 + 2 * j).factorial : ℝ)
          ≤ 404 * (2 * ((3 : ℝ) ^ 15 / (Nat.factorial 15 : ℝ))) :=
            mul_le_mul he6 h15 (Finset.sum_nonneg fun j _ => by positivity) (by norm_num)
        _ ≤ 1 := hnum
    calc Real.exp (∑ i : Fin J, (3 : ℝ) ^ (14 + 2 * (i : ℕ) + 1) /
          (((14 + 2 * (i : ℕ) + 1).factorial : ℝ) * Real.exp (-6))) ≤ Real.exp 1 := Real.exp_le_exp.2 hsum
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hS20 : 0 ≤ ∏ i : Fin J, (1 + (3 : ℝ) ^ (14 + 2 * (i : ℕ) + 1) /
      (((14 + 2 * (i : ℕ) + 1).factorial : ℝ) * Real.exp (-6))) :=
    Finset.prod_nonneg fun i _ => by positivity
  have hnum : (404 : ℝ) * (2 * ((3 : ℝ) ^ 14 / (Nat.factorial 14 : ℝ))) * 3 ≤ 1 / 2 := by
    norm_num [Nat.factorial]
  have hmid : (Real.exp (-6))⁻¹ * ∑ j : Fin J, (3 : ℝ) ^ (14 + 2 * (j : ℕ)) / ((14 + 2 * (j : ℕ)).factorial : ℝ) ≤
      404 * (2 * ((3 : ℝ) ^ 14 / (Nat.factorial 14 : ℝ))) := by
    rw [hinv]
    exact mul_le_mul he6 hS1 (Finset.sum_nonneg fun j _ => by positivity) (by norm_num)
  have hmid0 : 0 ≤ (Real.exp (-6))⁻¹ *
      ∑ j : Fin J, (3 : ℝ) ^ (14 + 2 * (j : ℕ)) / ((14 + 2 * (j : ℕ)).factorial : ℝ) :=
    mul_nonneg (inv_nonneg.2 (Real.exp_pos _).le) (Finset.sum_nonneg fun j _ => by positivity)
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hV0
  calc (Real.exp (-6))⁻¹ * (∑ j : Fin J, (3 : ℝ) ^ (14 + 2 * (j : ℕ)) / ((14 + 2 * (j : ℕ)).factorial : ℝ)) *
        ∏ i : Fin J, (1 + (3 : ℝ) ^ (14 + 2 * (i : ℕ) + 1) /
          (((14 + 2 * (i : ℕ) + 1).factorial : ℝ) * Real.exp (-6)))
      ≤ 404 * (2 * ((3 : ℝ) ^ 14 / (Nat.factorial 14 : ℝ))) * 3 := mul_le_mul hmid hS2 hS20 (by positivity)
    _ ≤ 1 / 2 := hnum

/-- `Σ_{i ≤ k} C(n, i) ≤ (n + 1)^k`. -/
lemma sum_choose_le (n k : ℕ) : ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) ≤ ((n : ℝ) + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 : (n.choose (k + 1) : ℝ) ≤ (n : ℝ) ^ (k + 1) := by exact_mod_cast Nat.choose_le_pow n (k + 1)
    have h2 : (n : ℝ) ^ (k + 1) ≤ ((n : ℝ) + 1) ^ k * n := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) k) (Nat.cast_nonneg n)
    nlinarith

/-- `Σ_{j < J} 2^{−j}(14 + 2j) = 32 − (4J + 32)2^{−J}`. -/
lemma sum_half_eq (J : ℕ) :
    ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j * (14 + 2 * (j : ℝ)) = 32 - (4 * J + 32) * (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ, ih, pow_succ]; push_cast; ring

/-- **The number of terms of the sieve** at the levels `14 + 2j`: at most `w³²`. -/
lemma terms_le {q : ℕ} {w : ℝ} (hw : 1 ≤ w) (J : ℕ) :
    ∏ j : Fin J, ∑ i ∈ Finset.range (14 + 2 * (j : ℕ) + 1), (((fam q w j).card).choose i : ℝ) ≤ w ^ (32 : ℝ) := by
  have hw0 : 0 < w := by linarith
  have h1 : ∀ j : Fin J, ∑ i ∈ Finset.range (14 + 2 * (j : ℕ) + 1), (((fam q w j).card).choose i : ℝ) ≤
      w ^ ((1 / 2 : ℝ) ^ (j : ℕ) * (14 + 2 * ((j : ℕ) : ℝ))) := by
    intro j
    refine (sum_choose_le _ _).trans ?_
    have e : w ^ ((1 / 2 : ℝ) ^ (j : ℕ) * (14 + 2 * ((j : ℕ) : ℝ))) =
        (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ (14 + 2 * (j : ℕ)) := by
      have hc : (14 + 2 * ((j : ℕ) : ℝ)) = ((14 + 2 * (j : ℕ) : ℕ) : ℝ) := by push_cast; ring
      rw [Real.rpow_mul hw0.le, hc, Real.rpow_natCast]
    rw [e]
    exact pow_le_pow_left₀ (by positivity) (card_fam_le hw j) _
  calc ∏ j : Fin J, ∑ i ∈ Finset.range (14 + 2 * (j : ℕ) + 1), (((fam q w j).card).choose i : ℝ)
      ≤ ∏ j : Fin J, w ^ ((1 / 2 : ℝ) ^ (j : ℕ) * (14 + 2 * ((j : ℕ) : ℝ))) :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun i _ => Nat.cast_nonneg _) fun j _ => h1 j
    _ = w ^ (∑ j : Fin J, (1 / 2 : ℝ) ^ (j : ℕ) * (14 + 2 * ((j : ℕ) : ℝ))) :=
        (Real.rpow_sum_of_pos hw0 _ _).symm
    _ ≤ w ^ (32 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hw ?_
        rw [Fin.sum_univ_eq_sum_range (fun j => (1 / 2 : ℝ) ^ j * (14 + 2 * (j : ℝ))) J, sum_half_eq]
        have : 0 ≤ (4 * (J : ℝ) + 32) * (1 / 2 : ℝ) ^ J := by positivity
        linarith

/-- `ω(m) ≤ 2 log m`. -/
lemma card_primeFactors_le_log {m : ℕ} (hm : m ≠ 0) : (m.primeFactors.card : ℝ) ≤ 2 * Real.log m := by
  have h2 : 2 ^ m.primeFactors.card ≤ m :=
    calc 2 ^ m.primeFactors.card = ∏ _p ∈ m.primeFactors, 2 := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ m.primeFactors, p := Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)
  have h3 : ((2 : ℝ) ^ m.primeFactors.card) ≤ m := by exact_mod_cast h2
  have h4 : (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log m := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h3
  have hl2 := Real.log_two_gt_d9
  have hc0 : (0 : ℝ) ≤ m.primeFactors.card := Nat.cast_nonneg _
  nlinarith

/-! ### The primitive roots by the sieve -/

open scoped Classical in
/-- The primes `ℓ ∣ φ(q)` with `ℓ ≥ w`. -/
def large (q : ℕ) (w : ℝ) : Finset ℕ := q.totient.primeFactors.filter fun ℓ : ℕ => w ≤ ℓ

/-- **The indicator of the primitive roots, from below**: for `n` prime to `q`, and `w^{2^{−J}} ≤ 2`,
`∏_j ∏_{ℓ∈T_j} (1 − yv(n, ℓ)) − Σ_{ℓ ≥ w} yv(n, ℓ) ≤ [ord n = φ(q)]`. If `n` is an `ℓ`-th power for no prime
`ℓ ∣ φ(q)` its order is `φ(q)`; otherwise the left side is at most `0`, the prime being in a family or above `w`. -/
lemma primRoot_ge {w : ℝ} {J : ℕ} (hJ : w ^ ((1 / 2 : ℝ) ^ J) ≤ 2) {n : ℕ} (hn : IsUnit (n : ZMod q)) :
    ∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - yv q n ℓ) - ∑ ℓ ∈ large q w, yv q n ℓ ≤
      if orderOf (n : ZMod q) = q.totient then 1 else 0 := by
  classical
  have hin : ∀ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - yv q n ℓ) ≤ 1 := fun j => by
    have h := Finset.prod_le_prod₀ (s := fam q w j) (f := fun ℓ => 1 - yv q n ℓ) (g := fun _ => (1 : ℝ))
      (fun ℓ _ => by linarith [yv_le_one q n ℓ]) (fun ℓ _ => by linarith [yv_nonneg q n ℓ])
    rwa [Finset.prod_const_one] at h
  have hprod1 : ∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - yv q n ℓ) ≤ 1 := by
    have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin J)))
      (f := fun j : Fin J => ∏ ℓ ∈ fam q w (j : ℕ), (1 - yv q n ℓ)) (g := fun _ : Fin J => (1 : ℝ))
      (fun j _ => Finset.prod_nonneg fun ℓ _ => by linarith [yv_le_one q n ℓ]) (fun j _ => hin j)
    rwa [Finset.prod_const_one] at h
  have hsum0 : 0 ≤ ∑ ℓ ∈ large q w, yv q n ℓ := Finset.sum_nonneg fun ℓ _ => yv_nonneg q n ℓ
  by_cases hall : ∀ ℓ ∈ q.totient.primeFactors, yv q n ℓ = 0
  · have hord : orderOf (n : ZMod q) = q.totient := by
      refine orderOf_eq_of_pow_and_pow_div_prime (Nat.pos_of_ne_zero totient_ne_zero)
        (pow_totient_eq_one hn) fun p hp hpd h => ?_
      have h0 := hall p (Nat.mem_primeFactors.2 ⟨hp, hpd, totient_ne_zero⟩)
      rw [yv, ite_eq_left h] at h0
      exact one_ne_zero h0
    rw [ite_eq_left hord]; linarith
  · push Not at hall
    obtain ⟨ℓ₀, hℓ₀, hy⟩ := hall
    have hy1 : yv q n ℓ₀ = 1 := by
      unfold yv at hy ⊢
      split_ifs at hy ⊢ with h
      · rfl
      · exact absurd rfl hy
    have hRHS : (0 : ℝ) ≤ if orderOf (n : ZMod q) = q.totient then 1 else 0 := by split_ifs <;> norm_num
    refine le_trans ?_ hRHS
    by_cases hbig : w ≤ ℓ₀
    · have h1 : yv q n ℓ₀ ≤ ∑ ℓ ∈ large q w, yv q n ℓ :=
        Finset.single_le_sum (f := fun ℓ => yv q n ℓ) (fun ℓ _ => yv_nonneg q n ℓ)
          (Finset.mem_filter.2 ⟨hℓ₀, hbig⟩)
      linarith
    · obtain ⟨j, hj, hmem⟩ := SieveRanges.cover hJ (Nat.prime_of_mem_primeFactors hℓ₀) (not_le.1 hbig)
      have hfam : ℓ₀ ∈ fam q w j := Finset.mem_filter.2 ⟨hmem, Nat.dvd_of_mem_primeFactors hℓ₀⟩
      have hz : ∏ ℓ ∈ fam q w j, (1 - yv q n ℓ) = 0 := Finset.prod_eq_zero hfam (by rw [hy1]; ring)
      have hz2 : ∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - yv q n ℓ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ (⟨j, hj⟩ : Fin J)) hz
      rw [hz2]; linarith

/-- **The prime powers that are primitive roots, from below.** For every `η > 0` there is `C ≥ 0` such that for
every modulus `q ≥ 1` with `(ℤ/qℤ)ˣ` cyclic, `J`, `w ≥ 1` with `w^{2^{−J}} ≤ 2`, and `x > 1` with
`X = Re ψ(x, χ₀) ≥ 0`: with `V = ∏_{j<J} ∏_{ℓ∈T_j} (1 − 1/ℓ)`, `E = C log(q + 2)x^{11/12+η}` and `L = log(q + 2)`,
`Σ_{n ≤ x} Λ(n)[ord n = φ(q)] ≥ XV/2 − (J + 1)E w³² − 2L(X/w + E)`. The primes `ℓ ∣ φ(q)` below `w` are sifted
by Brun's sieve in the families `T_j` at the levels `14 + 2j` (`SieveBrun.fundamentalW`, `gap_fam_le`,
`terms_le`), with the sums of `abs_sum_yv_sub_le`; the primes from `w` on, at most `2L` of them, are removed one
at a time. -/
theorem sum_primRoot_ge {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], IsCyclic (ZMod q)ˣ → ∀ (J : ℕ) (w : ℝ), 1 ≤ w →
      w ^ ((1 / 2 : ℝ) ^ J) ≤ 2 → ∀ x : ℝ, 1 < x → 0 ≤ (psiChi (1 : DirichletCharacter ℂ q) x).re →
      (psiChi (1 : DirichletCharacter ℂ q) x).re *
            ((∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - 1 / (ℓ : ℝ))) * (1 / 2)) -
          ((J : ℝ) + 1) * (C * Real.log (q + 2) * x ^ (11 / 12 + η)) * w ^ (32 : ℝ) -
          2 * Real.log (q + 2) * ((psiChi (1 : DirichletCharacter ℂ q) x).re / w +
            C * Real.log (q + 2) * x ^ (11 / 12 + η)) ≤
        ∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n *
          (if orderOf (n : ZMod q) = q.totient then 1 else 0) := by
  classical
  obtain ⟨C, hC, hA⟩ := abs_sum_yv_sub_le hη
  refine ⟨C, hC, fun q _ hcyc J w hw hJ x hx hX => ?_⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (psiChi (1 : DirichletCharacter ℂ q) x).re := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = C * Real.log (q + 2) * x ^ (11 / 12 + η) := ⟨_, rfl⟩
  rw [← hXdef] at hX ⊢
  rw [← hEdef]
  have hL0 : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith)
  have hx0 : 0 < x := by linarith
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hw0 : 0 < w := by linarith
  -- the sums of the fundamental lemma
  have hR : ∀ s : Fin J → Finset ℕ, (∀ j, s j ⊆ fam q w j) →
      |∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n * ∏ j, ∏ ℓ ∈ s j, yv q n ℓ -
        X * ∏ j, ∏ ℓ ∈ s j, (1 / (ℓ : ℝ))| ≤ E := by
    intro s hs
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin J))) s := by
      intro i _ j _ hij
      exact Finset.disjoint_of_subset_left (hs i) (Finset.disjoint_of_subset_right (hs j)
        (fam_disjoint hw fun h => hij (Fin.ext h)))
    have hU : ∀ ℓ ∈ Finset.univ.biUnion s, ℓ.Prime ∧ ℓ ∣ q.totient := by
      intro ℓ hℓ
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hℓ
      exact mem_fam (hs j hj)
    have h := hA q hcyc (Finset.univ.biUnion s) hU x hx
    simp_rw [Finset.prod_biUnion hdisj] at h
    rw [hXdef, hEdef]; exact h
  have hfund := SieveBrun.fundamentalW (unitsLe q x) (w := fun n => ArithmeticFunction.vonMangoldt n)
    (fun n _ => ArithmeticFunction.vonMangoldt_nonneg) (y := yv q) (fun j : Fin J => fam q w j)
    (fun n _ j ℓ _ => yv_nonneg q n ℓ) (fun n _ j ℓ _ => yv_le_one q n ℓ) (fun j : Fin J => 14 + 2 * (j : ℕ))
    (fun j => ⟨7 + (j : ℕ), by ring⟩) (fun j => by omega) hX (g := fun ℓ => 1 / (ℓ : ℝ))
    (fun j ℓ _ => by positivity) (fun j ℓ hℓ => by
      have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast (mem_fam hℓ).1.two_le
      rw [div_le_one (by linarith)]; linarith) hR
  rw [Fintype.card_fin] at hfund
  have hgap := mul_le_mul_of_nonneg_left (gap_fam_le (q := q) hw J) hX
  have hterms := mul_le_mul_of_nonneg_left (terms_le (q := q) hw J)
    (mul_nonneg (by positivity : (0 : ℝ) ≤ (J : ℝ) + 1) hE0)
  have hSlow := (abs_le.1 hfund).1
  -- the large primes
  have hlarge : ∀ ℓ ∈ large q w,
      ∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n * yv q n ℓ ≤ X / w + E := by
    intro ℓ hℓ
    obtain ⟨hpf, hwℓ⟩ := Finset.mem_filter.1 hℓ
    have hp := Nat.prime_of_mem_primeFactors hpf
    have h := hA q hcyc {ℓ} (fun ℓ' hℓ' => by
      rw [Finset.mem_singleton.1 hℓ']; exact ⟨hp, Nat.dvd_of_mem_primeFactors hpf⟩) x hx
    simp only [Finset.prod_singleton] at h
    rw [← hXdef, ← hEdef] at h
    have h1 := (abs_le.1 h).2
    have h2 : X * (1 / (ℓ : ℝ)) ≤ X / w := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_left hX hw0 hwℓ
    linarith
  have hcardL : ((large q w).card : ℝ) ≤ 2 * Real.log (q + 2) := by
    have h1 : ((large q w).card : ℝ) ≤ q.totient.primeFactors.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h2 := card_primeFactors_le_log (totient_ne_zero (q := q))
    have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have h3 : Real.log q.totient ≤ Real.log (q + 2) :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (totient_ne_zero (q := q))) (by linarith)
    linarith
  have hXE0 : 0 ≤ X / w + E := add_nonneg (div_nonneg hX hw0.le) hE0
  have hLsum : ∑ ℓ ∈ large q w, ∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n * yv q n ℓ ≤
      2 * Real.log (q + 2) * (X / w + E) := by
    calc ∑ ℓ ∈ large q w, ∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n * yv q n ℓ
        ≤ ∑ _ℓ ∈ large q w, (X / w + E) := Finset.sum_le_sum hlarge
      _ = (large q w).card * (X / w + E) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * Real.log (q + 2) * (X / w + E) := mul_le_mul_of_nonneg_right hcardL hXE0
  -- the sum over `n`
  have hpt : ∀ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n *
      (∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - yv q n ℓ) - ∑ ℓ ∈ large q w, yv q n ℓ) ≤
      ArithmeticFunction.vonMangoldt n * (if orderOf (n : ZMod q) = q.totient then 1 else 0) :=
    fun n hn => mul_le_mul_of_nonneg_left (primRoot_ge hJ (mem_unitsLe.1 hn).2)
      ArithmeticFunction.vonMangoldt_nonneg
  have hsum := Finset.sum_le_sum hpt
  have hexp : ∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n *
      (∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - yv q n ℓ) - ∑ ℓ ∈ large q w, yv q n ℓ) =
      ∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n * ∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - yv q n ℓ) -
        ∑ ℓ ∈ large q w, ∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n * yv q n ℓ := by
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_sub, Finset.mul_sum]
  rw [hexp] at hsum
  linarith

/-! ### The parameters -/

/-- `9J ≤ 2^{J−1}` for `J ≥ 7`. -/
lemma nine_mul_le {J : ℕ} (hJ : 7 ≤ J) : 9 * J ≤ 2 ^ (J - 1) := by
  induction J, hJ using Nat.le_induction with
  | base => norm_num
  | succ J hJ ih =>
    have h1 : 2 ^ (J + 1 - 1) = 2 * 2 ^ (J - 1) := by
      obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
      simp [pow_succ, mul_comm]
    rw [h1]
    have h2 : 9 ≤ 2 ^ (J - 1) := le_trans (by omega) ih
    omega

/-- For every `L` there is `J ≥ 7` with `8L ≤ 2^{2^{J−1}}`. -/
lemma exists_level (L : ℝ) : ∃ J : ℕ, 7 ≤ J ∧ 8 * L ≤ (2 : ℝ) ^ (2 ^ (J - 1)) := by
  refine ⟨⌈8 * L⌉₊ + 8, by omega, ?_⟩
  have h1 : ⌈8 * L⌉₊ + 8 - 1 = ⌈8 * L⌉₊ + 7 := by omega
  rw [h1]
  have h2 : ⌈8 * L⌉₊ + 7 < 2 ^ (⌈8 * L⌉₊ + 7) := Nat.lt_two_pow_self
  have h3 : 2 ^ (⌈8 * L⌉₊ + 7) < 2 ^ (2 ^ (⌈8 * L⌉₊ + 7)) := Nat.lt_two_pow_self
  have h4 : (⌈8 * L⌉₊ : ℝ) ≤ ((2 ^ (2 ^ (⌈8 * L⌉₊ + 7)) : ℕ) : ℝ) := by exact_mod_cast (by omega : ⌈8 * L⌉₊ ≤ _)
  calc 8 * L ≤ (⌈8 * L⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ ((2 ^ (2 ^ (⌈8 * L⌉₊ + 7)) : ℕ) : ℝ) := h4
    _ = (2 : ℝ) ^ (2 ^ (⌈8 * L⌉₊ + 7)) := by push_cast; rfl

/-- `(2^{2^J})^{2^{−J}} = 2`. -/
lemma rpow_half_two_pow (J : ℕ) : ((2 : ℝ) ^ (2 ^ J)) ^ ((1 / 2 : ℝ) ^ J) = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h : ((2 ^ J : ℕ) : ℝ) * (1 / 2 : ℝ) ^ J = 1 := by
    push_cast
    rw [← mul_pow]; norm_num
  rw [h, Real.rpow_one]

/-- `4√x log x ≤ x/16` for `x ≥ 2³²`. -/
lemma sqrt_mul_log_le {x : ℝ} (hx : 2 ^ 32 ≤ x) : 4 * √x * Real.log x ≤ x / 16 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    have e : x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) := by ring
    linarith
  have h256 : (256 : ℝ) ≤ x ^ (1 / 4 : ℝ) := by
    have h1 : ((2 : ℝ) ^ 32) ^ (1 / 4 : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hx (by norm_num)
    have h2 : ((2 : ℝ) ^ 32) ^ (1 / 4 : ℝ) = 256 := by
      rw [show ((2 : ℝ) ^ 32) = (256 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hs : √x = x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; norm_num
  have hx4 : x = x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = x ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  rw [← hu] at hlog h256 hs hx4
  have hu0 : 0 < u := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (le_trans (by norm_num) hx)
  rw [hs]
  have h1 : 4 * (u * u) * Real.log x ≤ 4 * (u * u) * (4 * u) := mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : 16 * (u * u * u) * 256 ≤ 16 * (u * u * u) * u := mul_le_mul_of_nonneg_left h256 (by positivity)
  nlinarith

/-- **The level of the sieve.** For `L ≥ 1` there are `J ≥ 7`, `H = 2^{2^{J−1}}` and `w = H² = 2^{2^J}` with
`8L ≤ H`, `w ≤ c₂L⁴` for every `c₂ ≥ 2^{128}`, `w^{2^{−J}} ≤ 2`, `J + 1 ≤ w` and `512^J ≤ H`: `J` is the least
with `8L ≤ 2^{2^{J−1}}`, so either `J = 7` or `2^{2^{J−2}} < 8L`. -/
lemma exists_level_spec {L c₂ : ℝ} (hL : 1 ≤ L) (hc₂ : 2 ^ 128 ≤ c₂) :
    ∃ (J : ℕ) (H w : ℝ), w = H ^ 2 ∧ 8 * L ≤ H ∧ w ≤ c₂ * L ^ 4 ∧ w ^ ((1 / 2 : ℝ) ^ J) ≤ 2 ∧
      (J : ℝ) + 1 ≤ w ∧ (512 : ℝ) ^ J ≤ H := by
  classical
  have hex := exists_level L
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = Nat.find hex := ⟨_, rfl⟩
  obtain ⟨hJ7, hJL⟩ : 7 ≤ J ∧ 8 * L ≤ (2 : ℝ) ^ (2 ^ (J - 1)) := by rw [hJdef]; exact Nat.find_spec hex
  refine ⟨J, (2 : ℝ) ^ (2 ^ (J - 1)), (2 : ℝ) ^ (2 ^ J), ?_, hJL, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul]
    obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
    simp [pow_succ]
  · have hL4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL
    have hc0 : (0 : ℝ) ≤ c₂ := le_trans (by norm_num) hc₂
    rcases Nat.lt_or_ge 7 J with h8 | h7
    · have hmin := Nat.find_min hex (show J - 1 < Nat.find hex by rw [← hJdef]; omega)
      have hlt : (2 : ℝ) ^ (2 ^ (J - 1 - 1)) < 8 * L := by
        by_contra hge
        exact hmin ⟨by omega, not_lt.1 hge⟩
      have e : (2 : ℝ) ^ (2 ^ J) = ((2 : ℝ) ^ (2 ^ (J - 1 - 1))) ^ 4 := by
        rw [← pow_mul]
        obtain ⟨J', rfl⟩ : ∃ J', J = J' + 2 := ⟨J - 2, by omega⟩
        congr 1
        simp [pow_succ]; ring
      rw [e]
      calc ((2 : ℝ) ^ (2 ^ (J - 1 - 1))) ^ 4 ≤ (8 * L) ^ 4 := pow_le_pow_left₀ (by positivity) hlt.le 4
        _ = 4096 * L ^ 4 := by ring
        _ ≤ c₂ * L ^ 4 := mul_le_mul_of_nonneg_right (le_trans (by norm_num) hc₂) (by positivity)
    · have hJ7' : J = 7 := le_antisymm h7 hJ7
      rw [hJ7']
      calc (2 : ℝ) ^ (2 ^ 7) = 2 ^ 128 := by norm_num
        _ ≤ c₂ * 1 := by linarith
        _ ≤ c₂ * L ^ 4 := mul_le_mul_of_nonneg_left hL4 hc0
  · rw [rpow_half_two_pow]
  · have h1 : J + 1 ≤ 2 ^ J := Nat.lt_two_pow_self
    have h2 : 2 ^ J ≤ 2 ^ (2 ^ J) := (Nat.lt_two_pow_self).le
    have h3 : ((J + 1 : ℕ) : ℝ) ≤ ((2 ^ (2 ^ J) : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
    push_cast at h3; exact h3
  · rw [show (512 : ℝ) = 2 ^ 9 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (nine_mul_le hJ7)

/-- **The sizes.** With `8L ≤ H`, `w = H²`, `J' + 1 ≤ w`, `V ≥ 1/H`, `X ≥ x/8` and `x = y·64(C + 1)w^{35}`, the
lower bound of `sum_primRoot_ge` is positive: it is at least `X/(4H) − 2Cyw^{34}`, and
`x/(32H) ≥ 2(C + 1)yw^{34}`. -/
lemma lower_pos {C L H w X V x y J' : ℝ} (hC : 0 ≤ C) (hL : 1 ≤ L) (hH8 : 8 * L ≤ H) (hwH : w = H ^ 2)
    (hJ0 : 0 ≤ J') (hJw : J' + 1 ≤ w) (hV : 1 / H ≤ V) (hX8 : x / 8 ≤ X) (hy0 : 0 < y)
    (hxy : x = y * (64 * (C + 1) * w ^ 35)) :
    0 < X * (V * (1 / 2)) - (J' + 1) * (C * L * y) * w ^ 32 - 2 * L * (X / w + C * L * y) := by
  have hH0 : 0 < H := by linarith
  have hw1 : 1 ≤ w := by rw [hwH]; nlinarith
  have hw0 : 0 < w := by linarith
  have hHw : H ≤ w := by rw [hwH]; nlinarith
  have hLw : L ≤ w := by linarith
  have hw34 : w ≤ w ^ 34 := le_self_pow₀ hw1 (by norm_num)
  have hx0 : 0 < x := by rw [hxy]; positivity
  have hX0 : 0 ≤ X := by linarith
  have hCy : 0 ≤ C * y := by positivity
  have hT1 : X / (2 * H) ≤ X * (V * (1 / 2)) := by
    have h := mul_le_mul_of_nonneg_left hV (by linarith : (0 : ℝ) ≤ X * (1 / 2))
    have e : X * (1 / 2) * (1 / H) = X / (2 * H) := by field_simp
    linarith
  have hT2 : (J' + 1) * (C * L * y) * w ^ 32 ≤ C * y * w ^ 34 := by
    have h1 : (J' + 1) * L ≤ w * w := mul_le_mul hJw hLw (by linarith) hw0.le
    have h2 : (J' + 1) * L * (C * y * w ^ 32) ≤ w * w * (C * y * w ^ 32) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    calc (J' + 1) * (C * L * y) * w ^ 32 = (J' + 1) * L * (C * y * w ^ 32) := by ring
      _ ≤ w * w * (C * y * w ^ 32) := h2
      _ = C * y * w ^ 34 := by ring
  have hT3 : 2 * L * (X / w) ≤ X / (4 * H) := by
    rw [hwH, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_right hH8 (by positivity : (0 : ℝ) ≤ X * H)
    have e1 : 2 * L * X * (4 * H) = 8 * L * (X * H) := by ring
    have e2 : X * H ^ 2 = H * (X * H) := by ring
    linarith
  have hT4 : 2 * L * (C * L * y) ≤ C * y * w ^ 34 := by
    have h1 : 2 * L * L ≤ w := by rw [hwH]; nlinarith
    have h2 : 2 * L * L * (C * y) ≤ w ^ 34 * (C * y) := mul_le_mul_of_nonneg_right (h1.trans hw34) hCy
    linarith
  have hX4 : x / (32 * H) ≤ X / (4 * H) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_right hX8 (by positivity : (0 : ℝ) ≤ 32 * H)
    linarith
  have hfin : 2 * C * y * w ^ 34 < x / (32 * H) := by
    rw [lt_div_iff₀ (by positivity), hxy]
    have h34 : 0 < w ^ 34 := by positivity
    have h1 : w ^ 34 * H ≤ w ^ 35 := by
      calc w ^ 34 * H ≤ w ^ 34 * w := mul_le_mul_of_nonneg_left hHw h34.le
        _ = w ^ 35 := by ring
    have h2 : 0 < y * w ^ 34 * H := by positivity
    have h3 : y * (C + 1) * (w ^ 34 * H) ≤ y * (C + 1) * w ^ 35 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have e : 2 * L * (X / w + C * L * y) = 2 * L * (X / w) + 2 * L * (C * L * y) := by ring
  have e2 : X / (2 * H) - X / (4 * H) = X / (4 * H) := by field_simp; ring
  rw [e]
  linarith

/-- **The least prime primitive root is at most a power of `log q`.** There is `K > 0` such that every modulus
`q ≥ 1` with `(ℤ/qℤ)ˣ` cyclic (`q = 1, 2, 4, pᵏ, 2pᵏ` with `p` an odd prime) has a primitive root that is a prime
`ℓ ∤ q` with `ℓ ≤ K(log(q + 2))^{1820}`. With `L = log(q + 2)`: the primes `ℓ' ∣ φ(q)` below `w = 2^{2^J}`, where
`J ≥ 7` is the least with `8L ≤ 2^{2^{J−1}}`, so that `w ≤ 2^{140}L⁴`, are sifted by `sum_primRoot_ge` at
`η = 1/156`, and at `x = (64(C + 1)w^{35})^{13}` the main term, at least `x/(32√w)`, exceeds the errors, at most
`2Cw^{34}x^{12/13}` (`lower_pos`). The exponent `1820 = 13·35·4` is what these choices give and no more. -/
theorem exists_prime_primRoot_le_log :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q], IsCyclic (ZMod q)ˣ →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ q ∧ orderOf (ℓ : ZMod q) = q.totient ∧
        (ℓ : ℝ) ≤ K * Real.log (q + 2) ^ 1820 := by
  classical
  obtain ⟨C, hC, hS⟩ := sum_primRoot_ge (η := 1 / 156) (by norm_num)
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = 2 ^ 140 := ⟨_, rfl⟩
  have hc₂128 : (2 : ℝ) ^ 128 ≤ c₂ := by rw [hc₂]; norm_num
  have hc₂0 : 0 < c₂ := lt_of_lt_of_le (by norm_num) hc₂128
  refine ⟨(64 * (C + 1)) ^ 13 * c₂ ^ 455, by positivity, fun q _ hcyc => ?_⟩
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (q + 2) := ⟨_, rfl⟩
  rw [← hLdef]
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨J, H, w, hwH, hH8, hwL, hwJ, hJw, h512⟩ := exists_level_spec hL hc₂128
  have hH0 : 0 < H := by linarith
  have hw1 : 1 ≤ w := by rw [hwH]; nlinarith
  have hw0 : 0 < w := by linarith
  have hHw : H ≤ w := by rw [hwH]; nlinarith
  -- the main term of the sieve
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = ∏ j : Fin J, ∏ ℓ ∈ fam q w j, (1 - 1 / (ℓ : ℝ)) := ⟨_, rfl⟩
  have hV : 1 / H ≤ V := by
    have h1 : (Real.exp (-6)) ^ J ≤ V := by
      have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin J))) (f := fun _ : Fin J => Real.exp (-6))
        (g := fun j : Fin J => ∏ ℓ ∈ fam q w (j : ℕ), (1 - 1 / (ℓ : ℝ))) (fun _ _ => (Real.exp_pos _).le)
        (fun j _ => prod_fam_ge hw1 j)
      rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hVdef] at h
    have h2 : (1 : ℝ) / 512 ≤ Real.exp (-6) := by
      rw [Real.exp_neg, one_div, inv_le_inv₀ (by norm_num) (Real.exp_pos _)]
      linarith [exp_six_le]
    have h3 : ((1 : ℝ) / 512) ^ J ≤ (Real.exp (-6)) ^ J := pow_le_pow_left₀ (by norm_num) h2 J
    have h4 : (1 : ℝ) / H ≤ ((1 : ℝ) / 512) ^ J := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) h512
    linarith
  -- the point `x`
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = 64 * (C + 1) * w ^ 35 := ⟨_, rfl⟩
  have hw35 : w ≤ w ^ 35 := le_self_pow₀ hw1 (by norm_num)
  have hr64 : 64 * w ≤ r := by
    have h35 : 0 ≤ w ^ 35 := by positivity
    have : 64 * w ^ 35 ≤ 64 * (C + 1) * w ^ 35 := by nlinarith
    rw [hrdef]; linarith
  have hr1 : 64 ≤ r := by linarith
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = r ^ 13 := ⟨_, rfl⟩
  have hxr : r ≤ x := by rw [hxdef]; exact le_self_pow₀ (by linarith) (by norm_num)
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hx32 : (2 : ℝ) ^ 32 ≤ x := by
    rw [hxdef]
    calc (2 : ℝ) ^ 32 ≤ 64 ^ 13 := by norm_num
      _ ≤ r ^ 13 := pow_le_pow_left₀ (by norm_num) hr1 13
  have hxrpow : x ^ (1 / 13 : ℝ) = r := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = x ^ (11 / 12 + 1 / 156 : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hydef]; exact Real.rpow_pos_of_pos hx0 _
  have hxy : x = y * (64 * (C + 1) * w ^ 35) := by
    rw [← hrdef, hydef, ← hxrpow, ← Real.rpow_add hx0, show (11 / 12 + 1 / 156 + 1 / 13 : ℝ) = 1 by norm_num,
      Real.rpow_one]
  -- the trivial character
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (psiChi (1 : DirichletCharacter ℂ q) x).re := ⟨_, rfl⟩
  have hX8 : x / 8 ≤ X := by
    have hlow := LeastNonresidue.re_psiChi_ge (1 : DirichletCharacter ℂ q) (ε := 1) (Or.inl rfl)
      (by linarith : (1 : ℝ) ≤ x) fun p hp _ hpq ↦ by
        have hu : IsUnit (p : ZMod q) :=
          (ZMod.isUnit_iff_coprime p q).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
        rw [MulChar.one_apply hu, Complex.ofReal_one]
    rw [one_mul, ← hXdef] at hlow
    have hψ := LeastNonresidue.psi_ge_quarter (le_trans (by norm_num) hx32 : (100 : ℝ) ≤ x)
    have h1 := sqrt_mul_log_le hx32
    have h2 : Real.log q ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by linarith) (by linarith)
    linarith
  have hX0 : 0 ≤ X := by linarith
  have hmain := hS q hcyc J w hw1 hwJ x hx1 (by rw [← hXdef]; exact hX0)
  rw [← hXdef, ← hLdef, ← hydef, ← hVdef,
    show (32 : ℝ) = ((32 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hmain
  have hpos := lower_pos hC hL hH8 hwH (Nat.cast_nonneg J) hJw hV hX8 hy0 hxy
  -- no prime below `x` is a primitive root: a contradiction
  by_contra hcon
  push Not at hcon
  have hxK : x ≤ (64 * (C + 1)) ^ 13 * c₂ ^ 455 * L ^ 1820 := by
    have h1 : w ^ (35 * 13) ≤ (c₂ * L ^ 4) ^ (35 * 13) := pow_le_pow_left₀ hw0.le hwL _
    have h2 : x = (64 * (C + 1)) ^ 13 * w ^ (35 * 13) := by rw [hxdef, hrdef, mul_pow, ← pow_mul]
    have h3 : (c₂ * L ^ 4) ^ (35 * 13) = c₂ ^ 455 * L ^ 1820 := by rw [mul_pow, ← pow_mul]
    rw [h2, mul_assoc, ← h3]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hzero : ∑ n ∈ unitsLe q x, ArithmeticFunction.vonMangoldt n *
      (if orderOf (n : ZMod q) = q.totient then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · rw [hΛ, zero_mul]
    rw [ite_eq_right, mul_zero]
    intro hord
    obtain ⟨ℓ, k, hℓ, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
    obtain ⟨hord', hℓq⟩ := orderOf_prime_eq hℓ hk hord
    have hℓX : (ℓ : ℝ) ≤ x := by
      have h1 : ℓ ≤ ⌊x⌋₊ := (Nat.le_self_pow hk.ne' ℓ).trans (Finset.mem_Icc.1 (mem_unitsLe.1 hn).1).2
      exact (Nat.cast_le.2 h1).trans (Nat.floor_le hx0.le)
    exact (hcon ℓ hℓ hℓq hord').not_ge (hℓX.trans hxK)
  rw [hzero] at hmain
  linarith

/-- **The least prime primitive root mod a prime is at most a power of `log p`.** There is `K > 0` such that every
prime `p` has a primitive root that is a prime `ℓ ≠ p` with `ℓ ≤ K(log(p + 2))^{1820}`. -/
theorem exists_prime_primRoot_le_log_prime :
    ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ, p.Prime →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ orderOf (ℓ : ZMod p) = p - 1 ∧ (ℓ : ℝ) ≤ K * Real.log (p + 2) ^ 1820 := by
  obtain ⟨K, hK, h⟩ := exists_prime_primRoot_le_log
  refine ⟨K, hK, fun p hp ↦ ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ℓ, hℓ, hℓp, hord, hle⟩ := h p (ZMod.isCyclic_units_prime hp)
  refine ⟨ℓ, hℓ, fun h ↦ hℓp (by subst h; exact dvd_rfl), ?_, hle⟩
  rwa [Nat.totient_prime hp] at hord

/-- **The least prime primitive root mod a prime power.** There is `K > 0` such that for every odd prime `p` and
every `k ≥ 1`, some prime `ℓ ≠ p` with `ℓ ≤ K(log(pᵏ + 2))^{1820}` generates `(ℤ/pᵏℤ)ˣ`. -/
theorem exists_prime_primRoot_le_log_pow :
    ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ k : ℕ, 0 < k →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ orderOf (ℓ : ZMod (p ^ k)) = (p ^ k).totient ∧
        (ℓ : ℝ) ≤ K * Real.log ((p ^ k : ℕ) + 2) ^ 1820 := by
  obtain ⟨K, hK, h⟩ := exists_prime_primRoot_le_log
  refine ⟨K, hK, fun p hp hp2 k hk ↦ ?_⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  obtain ⟨ℓ, hℓ, hℓp, hord, hle⟩ := h (p ^ k) (ZMod.isCyclic_units_of_prime_pow p hp hp2 k)
  exact ⟨ℓ, hℓ, fun h ↦ hℓp (by subst h; exact dvd_pow_self _ hk.ne'), hord, hle⟩

end LeastPrimitiveRoot
