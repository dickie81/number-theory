/-
# Jacobi's cubic binomial congruence `C(2k, k) ≡ −L (mod p)`

Plain statement. Let `p ≡ 1 (mod 3)` be prime and `k = (p − 1)/3`. Then `4p = L² + 27M²` with `L ≡ 1 (mod 3)`
(`exists_rep`), and for every such representation `C(2k, k) ≡ −L (mod p)` (`choose_modEq`). For `p = 7`,
`28 = 1 + 27` and `C(4, 2) = 6 ≡ −1`; for `p = 13`, `52 = 25 + 27` with `L = −5`, and `C(8, 4) = 70 ≡ 5`.
* **The binomial sum** (`sum_pow_mul_one_sub_pow`): over a field with `q = 3m + 1` elements, `m` even,
  `Σ_x x^{2m}(1 − x)^{2m} = −C(2m, m)`. Of the power sums `Σ_x x^e` with `2m ≤ e ≤ 4m`, only `e = q − 1`
  survives (`FiniteField.sum_pow_units`).
* **At the prime** (`mk_choose_eq`): for `P = (π)` with `π ≡ 1 (mod 3)` and `m = (N(P) − 1)/3` even,
  `C(2m, m) ≡ π + π̄ (mod P)`. The cubic character has `χ_P(x) ≡ x^m (mod P)` (`Eis.mk_cubChar`) and
  conjugation squares its values (`cj_cubChar`), so modulo `P` the conjugate Jacobi sum
  `J̄ = Σ_x χ̄_P(x)χ̄_P(1 − x)` is `Σ_x x^{2m}(1 − x)^{2m} = −C(2m, m)` (`mk_cj_jacobiSum`). With `J = −π`
  (`Eis.jacobiSum_eq_neg`) and `π ∈ P`, `C(2m, m) ≡ π̄ ≡ π + π̄`.
* **In the integers** (`choose_modEq_trace`): for `π = a + bω ≡ 1 (mod 3)` of prime norm `a² − ab + b² = p ≠ 3`,
  `C(2k, k) ≡ 2a − b (mod p)`, the trace of `π`. A rational integer in `P` is divisible by `p`, by norms
  (`dvd_of_intCast_mem`, `absNorm_span_coords`).
* **Jacobi's form** (`choose_modEq`): a representation `4p = L² + 27M²` with `L ≡ 1 (mod 3)` gives the element
  `π = −(L + 3M)/2 − 3Mω ≡ 1 (mod 3)` of norm `p` and trace `−L`, so no uniqueness of the representation is used.
* **Existence** (`exists_rep`): `p` splits in `ℤ[ω]` (`Eis.split_of_mod_one`), the prime above it is principal
  with a primary generator `a + bω` (`Eis.exists_primary`), and comparing norms gives `3 ∣ b` and `3 ∣ a − 1`, so
  `4p = (2a − b)² + 27(b/3)²` with `b − 2a ≡ 1 (mod 3)`.
C. G. J. Jacobi (1837); B. C. Berndt, R. J. Evans and K. S. Williams, *Gauss and Jacobi Sums* (1998), Chapter 9.
The quartic analogue, Gauss's `C((p − 1)/2, (p − 1)/4) ≡ 2a (mod p)` for `p = a² + b²` with `a ≡ 1 (mod 4)`
(1828), needs the quartic residue character on `ℤ[i]` and its Jacobi sum, which the library does not have.
-/
import Mathlib
import EisensteinCubicChar

open NumberField Ideal

namespace CubicBinomial

open Eis

/-! ### Power sums over a finite field -/

/-- Over a finite field, `Σ_x x^e` is the sum over the units when `e ≠ 0`. -/
theorem sum_pow_eq_sum_units {F : Type*} [Field F] [Fintype F] [DecidableEq F] {e : ℕ} (he : e ≠ 0) :
    ∑ x : F, x ^ e = ∑ x : Fˣ, (x : F) ^ e := by
  have hmap : (Finset.univ : Finset Fˣ).map ⟨Units.val, Units.val_injective⟩ =
      Finset.univ \ {0} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, Finset.mem_sdiff,
      Finset.mem_singleton] using
      (⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩ : (∃ u : Fˣ, (u : F) = x) ↔ x ≠ 0)
  rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset F)), Finset.sum_singleton, zero_pow he,
    add_zero, ← hmap, Finset.sum_map]
  rfl

/-- **The binomial sum**: over a field with `q = 3m + 1` elements, `m` even,
`Σ_x x^{2m}(1 − x)^{2m} = −C(2m, m)`. -/
theorem sum_pow_mul_one_sub_pow {F : Type*} [Field F] [Fintype F] {m : ℕ}
    (hq : Fintype.card F = 3 * m + 1) (hm : 0 < m) (hm2 : Even m) :
    ∑ x : F, x ^ (2 * m) * (1 - x) ^ (2 * m) = -((2 * m).choose m : F) := by
  classical
  have hterm : ∀ x : F, x ^ (2 * m) * (1 - x) ^ (2 * m) =
      ∑ k ∈ Finset.range (2 * m + 1), ((-1) ^ (k + 2 * m) * ((2 * m).choose k : F)) * x ^ (4 * m - k) := by
    intro x
    rw [sub_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ 2 * m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [one_pow, show 4 * m - k = 2 * m + (2 * m - k) by omega, pow_add]
    ring
  have hinner : ∀ k ∈ Finset.range (2 * m + 1),
      ∑ x : F, x ^ (4 * m - k) = if k = m then -1 else 0 := by
    intro k hk
    have hk' : k ≤ 2 * m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [sum_pow_eq_sum_units (by omega), FiniteField.sum_pow_units, hq,
      show 3 * m + 1 - 1 = 3 * m by omega]
    by_cases h : k = m
    · subst h
      have hd : 3 * k ∣ 4 * k - k := by rw [show 4 * k - k = 3 * k by omega]
      simp [hd]
    · have hnd : ¬ 3 * m ∣ 4 * m - k := by
        rintro ⟨c, hc⟩
        rcases c with _ | _ | c
        · simp only [mul_zero] at hc
          omega
        · simp only [zero_add, mul_one] at hc
          omega
        · have hle : 4 * m - k ≤ 4 * m := Nat.sub_le _ _
          generalize 4 * m - k = t at hc hle
          nlinarith [Nat.zero_le (m * c)]
      simp [h, hnd]
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k hk => by rw [hinner k hk]]
  have hmem : m ∈ Finset.range (2 * m + 1) := Finset.mem_range.2 (by omega)
  simp only [mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq', hmem, ↓reduceIte]
  obtain ⟨r, hr⟩ := hm2
  rw [show m + 2 * m = 2 * (3 * r) by omega, pow_mul]
  simp

/-! ### The Jacobi sum modulo its own prime, conjugated -/

section Prime

variable (P : Ideal (𝓞 K)) [hPm : P.IsMaximal] (hP3 : (3 : 𝓞 K) ∉ P)

include hP3 in
/-- Conjugation squares the values of the cubic character. -/
theorem cj_cubChar (x : 𝓞 K ⧸ P) : cj (cubChar P hP3 x) = cubChar P hP3 x ^ 2 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    exact cj_of_cube (cubChar_spec P hP3 u).2
  · rw [MulChar.map_nonunit _ hx, map_zero, zero_pow two_ne_zero]

include hP3 in
/-- `J̄ ≡ Σ_x x^{2m}(1 − x)^{2m} (mod P)`, `m = (N(P) − 1)/3`. -/
theorem mk_cj_jacobiSum : Ideal.Quotient.mk P (cj (jacobiSum (cubChar P hP3) (cubChar P hP3))) =
    ∑ x : 𝓞 K ⧸ P, x ^ (2 * m3 P) * (1 - x) ^ (2 * m3 P) := by
  simp only [jacobiSum, map_sum, map_mul, cj_cubChar, map_pow, mk_cubChar]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← pow_mul, ← pow_mul, mul_comm (m3 P) 2]

include hP3 in
/-- `N(P) = 3m + 1` with `m = (N(P) − 1)/3`. -/
theorem card_eq : Fintype.card (𝓞 K ⧸ P) = 3 * m3 P + 1 := by
  have h := three_dvd_card_sub_one P hP3
  have h1 : 1 ≤ Fintype.card (𝓞 K ⧸ P) := Fintype.card_pos
  unfold m3
  omega

include hP3 in
/-- **The congruence at a primary prime**: `C(2m, m) ≡ π + π̄ (mod P)` for `P = (π)`, `π ≡ 1 (mod 3)`,
`m = (N(P) − 1)/3` even. -/
theorem mk_choose_eq {π : 𝓞 K} (hπ : Primary π) (hP : P = span {π}) (hm2 : Even (m3 P)) :
    Ideal.Quotient.mk P (((2 * m3 P).choose (m3 P) : ℕ) : 𝓞 K) = Ideal.Quotient.mk P (π + cj π) := by
  have h1 := mk_cj_jacobiSum P hP3
  rw [jacobiSum_eq_neg P hP3 hπ hP, map_neg, map_neg,
    sum_pow_mul_one_sub_pow (card_eq P hP3) (m3_pos P hP3) hm2] at h1
  have hπP : Ideal.Quotient.mk P π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (hP ▸ Ideal.mem_span_singleton_self π)
  rw [map_add, hπP, zero_add, map_natCast]
  exact (neg_injective h1).symm

end Prime

/-! ### From the prime to the rational integers -/

/-- The norm of the principal ideal of `a + bω` is `a² − ab + b²`. -/
theorem absNorm_span_coords (a b : ℤ) :
    absNorm (span {(a : 𝓞 K) + b * ω}) = (a ^ 2 - a * b + b ^ 2).natAbs := by
  have hnn : 0 ≤ a ^ 2 - a * b + b ^ 2 := by nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]
  have e1 : span {(a : 𝓞 K) + b * ω} * span {cj ((a : 𝓞 K) + b * ω)} =
      span {(((a ^ 2 - a * b + b ^ 2).natAbs : ℕ) : 𝓞 K)} := by
    rw [Ideal.span_singleton_mul_span_singleton, mul_cj_coords, ← Int.cast_natCast,
      Int.natAbs_of_nonneg hnn]
  have hsq := congrArg absNorm e1
  rw [map_mul, absNorm_span_cj, absNorm_natCast_span_sq, ← sq] at hsq
  exact Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hsq

/-- A rational integer in an ideal of prime norm `p` is divisible by `p`. -/
theorem dvd_of_intCast_mem {P : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hNP : absNorm P = p) {z : ℤ}
    (h : (z : 𝓞 K) ∈ P) : (p : ℤ) ∣ z := by
  have hmem : ((z.natAbs : ℕ) : 𝓞 K) ∈ P := by
    rw [← Int.cast_natCast]
    rcases Int.natAbs_eq z with hz | hz
    · rw [← hz]; exact h
    · rw [show (z.natAbs : ℤ) = -z by omega, Int.cast_neg]; exact P.neg_mem h
  have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [absNorm_natCast_span_sq, hNP] at hd
  exact Int.natCast_dvd.2 (hp.dvd_of_dvd_pow hd)

/-- **The congruence for a primary element of prime norm**: if `π = a + bω ≡ 1 (mod 3)` has norm
`a² − ab + b² = p`, a prime other than `3`, then `C(2k, k) ≡ 2a − b = π + π̄ (mod p)`, `k = (p − 1)/3`. -/
theorem choose_modEq_trace {a b : ℤ} (hπ : Primary ((a : 𝓞 K) + b * ω)) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hn : a ^ 2 - a * b + b ^ 2 = p) :
    (((2 * ((p - 1) / 3)).choose ((p - 1) / 3) : ℕ) : ℤ) ≡ 2 * a - b [ZMOD p] := by
  set π : 𝓞 K := (a : 𝓞 K) + b * ω with hπdef
  set P : Ideal (𝓞 K) := span {π} with hPdef
  have hNP : absNorm P = p := by rw [hPdef, absNorm_span_coords, hn, Int.natAbs_natCast]
  have hPm : P.IsMaximal := by
    have hprime : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hNP]; exact hp)
    have hne : P ≠ ⊥ := fun h => by rw [h, absNorm_bot] at hNP; exact hp.ne_zero hNP.symm
    exact hprime.isMaximal hne
  have hP3 : (3 : 𝓞 K) ∉ P := by
    intro h3
    have hd := Ideal.absNorm_dvd_absNorm_of_le
      ((Ideal.span_singleton_le_iff_mem _).2 (by exact_mod_cast h3 : ((3 : ℕ) : 𝓞 K) ∈ P))
    rw [absNorm_natCast_span_sq, hNP] at hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hd))
  have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
    rw [← hNP, absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hm : m3 P = (p - 1) / 3 := by unfold m3; rw [hcard]
  have hm2 : Even (m3 P) := by
    have h3 := three_dvd_card_sub_one P hP3
    rw [hcard] at h3
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | h2
      · subst h2; norm_num at h3
      · exact h2
    rw [hm, Nat.even_iff]
    omega
  have hkey := mk_choose_eq P hP3 hπ rfl hm2
  have htr : π + cj π = ((2 * a - b : ℤ) : 𝓞 K) := by
    rw [hπdef, cj_coords]; push_cast; ring
  rw [htr, hm] at hkey
  have hmem : ((((2 * ((p - 1) / 3)).choose ((p - 1) / 3) : ℕ) - (2 * a - b) : ℤ) : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Int.cast_sub, map_sub, Int.cast_natCast, hkey, sub_self]
  exact (Int.modEq_iff_dvd.2 (dvd_of_intCast_mem hp hNP hmem)).symm

/-- **Jacobi's cubic binomial congruence**: for a prime `p ≡ 1 (mod 3)` and every representation
`4p = L² + 27M²` with `L ≡ 1 (mod 3)`, `C(2k, k) ≡ −L (mod p)`, `k = (p − 1)/3`. -/
theorem choose_modEq {p : ℕ} (hp : p.Prime) (hp1 : p % 3 = 1) {L M : ℤ}
    (hLM : 4 * (p : ℤ) = L ^ 2 + 27 * M ^ 2) (hL : L % 3 = 1) :
    (((2 * ((p - 1) / 3)).choose ((p - 1) / 3) : ℕ) : ℤ) ≡ -L [ZMOD p] := by
  obtain ⟨s, hs⟩ : ∃ s, L + 3 * M = 2 * s := by
    obtain ⟨l, hl | hl⟩ := Int.even_or_odd' L <;> obtain ⟨n, hn | hn⟩ := Int.even_or_odd' M
    · exact ⟨l + 3 * n, by rw [hl, hn]; ring⟩
    · exfalso
      subst hl hn
      have h4 : (4 : ℤ) ∣ 27 := ⟨p - l ^ 2 - 27 * n ^ 2 - 27 * n, by linear_combination (-1 : ℤ) * hLM⟩
      norm_num at h4
    · exfalso
      subst hl hn
      have h4 : (4 : ℤ) ∣ 1 := ⟨p - l ^ 2 - l - 27 * n ^ 2, by linear_combination (-1 : ℤ) * hLM⟩
      norm_num at h4
    · exact ⟨l + 3 * n + 2, by rw [hl, hn]; ring⟩
  have hs3 : (s + 1) % 3 = 0 := by omega
  obtain ⟨t, ht⟩ : ∃ t, -s - 1 = 3 * t := ⟨(-s - 1) / 3, by omega⟩
  have hπ : Primary (((-s : ℤ) : 𝓞 K) + ((-3 * M : ℤ) : 𝓞 K) * ω) :=
    ⟨(t : 𝓞 K) + (-M : 𝓞 K) * ω, by
      have e : (((-s - 1 : ℤ)) : 𝓞 K) = ((3 * t : ℤ) : 𝓞 K) := by rw [ht]
      push_cast at e ⊢
      linear_combination e⟩
  have hn : (-s) ^ 2 - (-s) * (-3 * M) + (-3 * M) ^ 2 = (p : ℤ) := by
    have h4 : 4 * ((-s) ^ 2 - (-s) * (-3 * M) + (-3 * M) ^ 2) = 4 * (p : ℤ) := by
      rw [hLM, show L = 2 * s - 3 * M by linarith]; ring
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4
  have h := choose_modEq_trace hπ hp (by omega) hn
  rwa [show 2 * -s - -3 * M = -L by linarith] at h

/-- **The representation exists**: every prime `p ≡ 1 (mod 3)` is `4p = L² + 27M²` with `L ≡ 1 (mod 3)`,
from a primary prime of `ℤ[ω]` above `p`. -/
theorem exists_rep {p : ℕ} (hp : p.Prime) (hp1 : p % 3 = 1) :
    ∃ L M : ℤ, 4 * (p : ℤ) = L ^ 2 + 27 * M ^ 2 ∧ L % 3 = 1 := by
  obtain ⟨P, -, -, -, hNP, -⟩ := split_of_mod_one hp hp1
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : 𝓞 K, P = span {π₀} :=
    ⟨Submodule.IsPrincipal.generator P, (Submodule.IsPrincipal.span_singleton_generator P).symm⟩
  have hlam : ¬ (ω - 1) ∣ π₀ := by
    intro h
    have hle : span {π₀} ≤ span {(-1 : ℤ) + (1 : ℤ) * ω} := by
      rw [Ideal.span_singleton_le_span_singleton]
      convert h using 1; push_cast; ring
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [absNorm_span_coords, ← hπ₀, hNP] at hd
    norm_num at hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hd
    omega
  obtain ⟨u, hu⟩ := exists_primary hlam
  obtain ⟨a, b, hab⟩ := exists_coords ((u : 𝓞 K) * π₀)
  have hspan : span {(u : 𝓞 K) * π₀} = P := by
    rw [hπ₀, Ideal.span_singleton_mul_left_unit u.isUnit]
  have hn : a ^ 2 - a * b + b ^ 2 = (p : ℤ) := by
    have h := absNorm_span_coords a b
    rw [← hab, hspan, hNP] at h
    have hnn : 0 ≤ a ^ 2 - a * b + b ^ 2 := by nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]
    omega
  rw [hab] at hu
  -- `3 ∣ π − π̄ = b(1 + 2ω)`, so `9 ∣ 3b²` and `3 ∣ b`
  have hb : (3 : ℤ) ∣ b := by
    have h1 := dvd_sub hu hu.cj
    have e : (a : 𝓞 K) + b * ω - 1 - (cj ((a : 𝓞 K) + b * ω) - 1) = (b : 𝓞 K) + ((2 * b : ℤ) : 𝓞 K) * ω := by
      rw [cj_coords]; push_cast; ring
    rw [e] at h1
    have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_span_singleton).2
      (by exact_mod_cast h1 : ((3 : ℕ) : 𝓞 K) ∣ (b : 𝓞 K) + ((2 * b : ℤ) : 𝓞 K) * ω))
    rw [absNorm_natCast_span_sq, absNorm_span_coords] at hd
    have h9 : (9 : ℤ) ∣ 3 * b ^ 2 := by
      have : ((3 * b ^ 2).natAbs : ℤ) = 3 * b ^ 2 := Int.natAbs_of_nonneg (by positivity)
      rw [← this]
      exact Int.natCast_dvd_natCast.2 (by convert hd using 2; ring_nf)
    have h3 : (3 : ℤ) ∣ b ^ 2 := by omega
    exact Int.Prime.dvd_pow' (by norm_num) h3
  obtain ⟨b', rfl⟩ := hb
  -- then `3 ∣ a − 1`
  have ha : (3 : ℤ) ∣ a - 1 := by
    have h1 : (3 : 𝓞 K) ∣ ((a - 1 : ℤ) : 𝓞 K) := by
      have e : ((a - 1 : ℤ) : 𝓞 K) = (a : 𝓞 K) + ((3 * b' : ℤ) : 𝓞 K) * ω - 1 - 3 * ((b' : 𝓞 K) * ω) := by
        push_cast; ring
      rw [e]
      exact dvd_sub hu (dvd_mul_right _ _)
    have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_span_singleton).2
      (by rw [Int.cast_zero, zero_mul, add_zero]; exact_mod_cast h1 :
        ((3 : ℕ) : 𝓞 K) ∣ ((a - 1 : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * ω))
    rw [absNorm_natCast_span_sq, absNorm_span_coords] at hd
    have h9 : (9 : ℤ) ∣ (a - 1) ^ 2 := by
      have : (((a - 1) ^ 2 - (a - 1) * 0 + 0 ^ 2).natAbs : ℤ) = (a - 1) ^ 2 := by
        rw [Int.natAbs_of_nonneg (by nlinarith [sq_nonneg (a - 1)])]; ring
      rw [← this]
      exact Int.natCast_dvd_natCast.2 (by convert hd using 2)
    have h3 : (3 : ℤ) ∣ (a - 1) ^ 2 := dvd_trans ⟨3, by norm_num⟩ h9
    exact Int.Prime.dvd_pow' (by norm_num) h3
  refine ⟨3 * b' - 2 * a, b', ?_, ?_⟩
  · linear_combination (-4 : ℤ) * hn
  · omega

end CubicBinomial

#print axioms CubicBinomial.sum_pow_mul_one_sub_pow
#print axioms CubicBinomial.mk_choose_eq
#print axioms CubicBinomial.choose_modEq_trace
#print axioms CubicBinomial.choose_modEq
#print axioms CubicBinomial.exists_rep
