/-
# The least primitive root

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `A > 12` there is `C` such that every modulus `q ≥ 1` whose units `(ℤ/qℤ)ˣ` are cyclic
(`q = 1, 2, 4, pᵏ, 2pᵏ` with `p` an odd prime: Mathlib's `ZMod.isCyclic_units_iff`) has a primitive root that is a
prime `ℓ ∤ q` with `ℓ ≤ C(d(φ(q))² log(q + 2))^A`, where `d` counts divisors (`exists_prime_primRoot_le`). So for
every `ε > 0` there is `C` such that every such `q` has a prime primitive root `ℓ ≤ Cq^ε`
(`exists_prime_primRoot_le_rpow`). In particular every prime `p` has a prime primitive root `ℓ ≤ Cp^ε`
(`exists_prime_primRoot_le_rpow_prime`), and so does every power of an odd prime (`exists_prime_primRoot_le_rpow_pow`).
When `d(p − 1)` is bounded the bound is a power of `log p`: for a safe prime `p = 2r + 1`, `r` an odd prime,
`ℓ ≤ C(log(p + 2))^A` (`exists_prime_primRoot_le_safe`). Behind these, the prime powers that are primitive roots
have, up to `x`, the weight `(φ(m)/m)ψ(x, χ₀)` that their density predicts, within `d(m)C log(q + 2)x^{11/12+η}`,
`m = φ(q)` (`norm_sum_primRoot_sub_le`). No hypothesis.

D. A. Burgess (1962) bounds the least primitive root mod `p` by `p^{1/4+ε}`; under GRH, V. Shoup (1992) bounds it by
`(log p)^6`. Here `p^ε`, and a prime primitive root, follow from the half-plane, through the bound
`ψ(x, χ) ≪ log q · x^{11/12+η}`, uniform in `q` (`ChiUniform.psiChi_le_uniform`).

* `sum_moebius_pow_eq`: Vinogradov's indicator. For `a` in `ℤ/qℤ` and `m = φ(q)`,
  `Σ_{d ∣ m} μ(d)[a^{m/d} = 1] = [ord a = m]`: a unit of order `o ∣ m` has `a^{m/d} = 1` exactly when `d ∣ m/o`, and
  `Σ_{d ∣ k} μ(d) = [k = 1]`.
* `mul_indicator_eq`: with the orthogonality of the characters at `a^{m/d}` (Mathlib's
  `DirichletCharacter.sum_characters_eq`), `m[ord a = m] = Σ_χ Σ_{d ∣ m} μ(d)χ(a)^{m/d}`.
* `sum_coeff_eq_totient`: summed over `a`, the pairs `(χ, d)` with `χ^{m/d} = 1` weigh `φ(m)` in all, the number of
  generators of the cyclic group `(ℤ/qℤ)ˣ` (Mathlib's `IsCyclic.card_orderOf_eq_totient`).
* `norm_sum_primRoot_sub_le`: weighted by `Λ(n)` and summed over `n ≤ x`, the pairs with `χ^{m/d} = 1` give
  `φ(m)ψ(x, χ₀)`, and each of the at most `m d(m)` others at most `C log(q + 2)x^{11/12+η}`.
* `rpow_le_of_le`: Ankeny's algebra, as in `LeastNonresidue.rpow_le_of_forall_eq_of`.
* `exists_prime_primRoot_le`: if no prime `ℓ ≤ x` is a primitive root then no prime power is (`ℓᵏ` of order `m`
  forces `ℓ` of order `m`), the weighted sum vanishes, and with `m ≤ φ(m)d(m)`
  (`LinnikCGLConst.le_totient_mul_card_divisors`) and `LeastNonresidue.re_psiChi_ge` at `χ₀`,
  `x^{1/A} ≤ K d(m)² log(q + 2)`.
* `exists_prime_primRoot_le_rpow`: the divisor bound `d(m) ≤ C_δ m^δ` (`LinnikPower.card_divisors_le`) and
  `log(q + 2) ≤ (3q)^δ/δ`, at `A = 13`.
-/
import LinnikCGLConst

open Real ChiPNT

open scoped Chebyshev

noncomputable section

namespace LeastPrimitiveRoot

/-- `Σ_{d ∣ n} μ(d) = [n = 1]` (Mathlib's `ArithmeticFunction.moebius_mul_coe_zeta`). -/
lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ ↦ f n) ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using h

variable {q : ℕ} [NeZero q]

lemma totient_ne_zero : q.totient ≠ 0 :=
  (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'

omit [NeZero q] in
lemma div_ne_zero_of_mem {d : ℕ} (hd : d ∈ q.totient.divisors) : q.totient / d ≠ 0 :=
  (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'

omit [NeZero q] in
/-- Fermat–Euler for a unit of `ℤ/qℤ`: `a^{φ(q)} = 1`. -/
lemma pow_totient_eq_one {a : ZMod q} (ha : IsUnit a) : a ^ q.totient = 1 := by
  have h := congrArg Units.val (ZMod.pow_totient ha.unit)
  rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h

/-- An element of order `φ(q) ≥ 1` is a unit. -/
lemma isUnit_of_orderOf_eq {a : ZMod q} (h : orderOf a = q.totient) : IsUnit a := by
  have h1 : a ^ q.totient = 1 := by rw [← h]; exact pow_orderOf_eq_one a
  exact IsUnit.of_pow_eq_one h1 totient_ne_zero

/-- **Vinogradov's indicator of the primitive roots.** For `a` in `ℤ/qℤ` and `m = φ(q)`,
`Σ_{d ∣ m} μ(d)[a^{m/d} = 1] = [ord a = m]`. -/
lemma sum_moebius_pow_eq (a : ZMod q) :
    ∑ d ∈ q.totient.divisors, (ArithmeticFunction.moebius d : ℤ) * (if a ^ (q.totient / d) = 1 then 1 else 0) =
      if orderOf a = q.totient then 1 else 0 := by
  have hm0 : q.totient ≠ 0 := totient_ne_zero
  by_cases ha : IsUnit a
  · have hu := pow_totient_eq_one ha
    have ho0 : 0 < orderOf a := orderOf_pos_iff.2
      (isOfFinOrder_iff_pow_eq_one.2 ⟨q.totient, Nat.pos_of_ne_zero hm0, hu⟩)
    obtain ⟨k, hk⟩ := orderOf_dvd_of_pow_eq_one hu
    have hk0 : k ≠ 0 := by rintro rfl; exact hm0 (by rw [hk, mul_zero])
    have hiff : ∀ d ∈ q.totient.divisors, (a ^ (q.totient / d) = 1 ↔ d ∣ k) := by
      intro d hd
      rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_divisors hd), hk,
        mul_comm d, Nat.mul_dvd_mul_iff_left ho0]
    have hfilter : q.totient.divisors.filter (· ∣ k) = k.divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨fun h ↦ ⟨h.2, hk0⟩, fun h ↦ ⟨⟨h.1.trans ⟨orderOf a, by rw [hk, mul_comm]⟩, hm0⟩, h.1⟩⟩
    rw [Finset.sum_congr rfl fun d hd ↦ by rw [if_congr (hiff d hd) rfl rfl], ← Finset.sum_filter_add_sum_filter_not
      q.totient.divisors (· ∣ k)]
    have h2 : ∑ d ∈ q.totient.divisors.filter (fun d ↦ ¬ d ∣ k),
        (ArithmeticFunction.moebius d : ℤ) * (if d ∣ k then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun d hd ↦ by rw [ite_eq_right (Finset.mem_filter.1 hd).2, mul_zero]
    rw [h2, add_zero, Finset.sum_congr rfl fun d hd ↦ by rw [ite_eq_left (Finset.mem_filter.1 hd).2, mul_one],
      hfilter, sum_moebius_divisors]
    refine if_congr ⟨fun h ↦ by rw [hk, h, mul_one], fun h ↦ ?_⟩ rfl rfl
    have h' : orderOf a * k = orderOf a * 1 := by rw [← hk, h, mul_one]
    exact Nat.eq_of_mul_eq_mul_left ho0 h'
  · have hord : orderOf a ≠ q.totient := fun h ↦ ha (isUnit_of_orderOf_eq h)
    rw [ite_eq_right hord]
    exact Finset.sum_eq_zero fun d hd ↦ by
      rw [ite_eq_right fun h ↦ ha (IsUnit.of_pow_eq_one h (div_ne_zero_of_mem hd)), mul_zero]

/-- **The indicator by characters.** For `a` in `ℤ/qℤ` and `m = φ(q)`, `m[ord a = m] = Σ_χ Σ_{d ∣ m} μ(d)χ(a)^{m/d}`
(Mathlib's `DirichletCharacter.sum_characters_eq` at `a^{m/d}`). -/
lemma mul_indicator_eq (a : ZMod q) :
    (q.totient : ℂ) * (if orderOf a = q.totient then 1 else 0) =
      ∑ χ : DirichletCharacter ℂ q, ∑ d ∈ q.totient.divisors,
        (ArithmeticFunction.moebius d : ℂ) * χ a ^ (q.totient / d) := by
  rw [Finset.sum_comm]
  have h : ∀ d ∈ q.totient.divisors, ∑ χ : DirichletCharacter ℂ q,
      (ArithmeticFunction.moebius d : ℂ) * χ a ^ (q.totient / d) = (q.totient : ℂ) *
        (((ArithmeticFunction.moebius d : ℤ) * (if a ^ (q.totient / d) = 1 then 1 else 0) : ℤ) : ℂ) := by
    intro d _
    rw [← Finset.mul_sum]
    simp only [← map_pow]
    rw [DirichletCharacter.sum_characters_eq ℂ (a ^ (q.totient / d))]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← Int.cast_sum, sum_moebius_pow_eq]
  split_ifs <;> simp

open scoped Classical in
/-- The sum of a character over `ℤ/qℤ`: `φ(q)` for `χ = 1`, and `0` otherwise. -/
lemma sum_char_eq (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, χ a = if χ = 1 then (q.totient : ℂ) else 0 := by
  split_ifs with h
  · subst h
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one h

/-- The generators of `(ℤ/qℤ)ˣ`, counted in `ℤ/qℤ`: `#{a : ord a = φ(q)} = φ(φ(q))` when `(ℤ/qℤ)ˣ` is cyclic. -/
lemma card_primRoots [IsCyclic (ZMod q)ˣ] :
    (Finset.univ.filter fun a : ZMod q ↦ orderOf a = q.totient).card = q.totient.totient := by
  have hm0 : q.totient ≠ 0 := totient_ne_zero
  have hset : (Finset.univ.filter fun a : ZMod q ↦ orderOf a = q.totient) =
      (Finset.univ.filter fun u : (ZMod q)ˣ ↦ orderOf u = q.totient).map
        ⟨Units.val, Units.val_injective⟩ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      have hu : IsUnit a := isUnit_of_orderOf_eq h
      exact ⟨hu.unit, by rw [← orderOf_units, IsUnit.unit_spec, h], hu.unit_spec⟩
    · rintro ⟨u, hu, rfl⟩
      rw [orderOf_units, hu]
  rw [hset, Finset.card_map]
  exact IsCyclic.card_orderOf_eq_totient (by rw [ZMod.card_units_eq_totient] )

open scoped Classical in
/-- **The weight of the trivial terms.** When `(ℤ/qℤ)ˣ` is cyclic, the pairs `(χ, d)` with `d ∣ m = φ(q)` and
`χ^{m/d} = 1`, weighted by `μ(d)`, sum to `φ(m)`: `mul_indicator_eq` summed over `ℤ/qℤ` counts the generators. -/
lemma sum_coeff_eq_totient [IsCyclic (ZMod q)ˣ] :
    ∑ χ : DirichletCharacter ℂ q, ∑ d ∈ q.totient.divisors,
      (ArithmeticFunction.moebius d : ℂ) * (if χ ^ (q.totient / d) = 1 then 1 else 0) =
        (q.totient.totient : ℂ) := by
  have hm0 : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.2 totient_ne_zero
  have hsum : (q.totient : ℂ) * q.totient.totient = (q.totient : ℂ) *
      ∑ χ : DirichletCharacter ℂ q, ∑ d ∈ q.totient.divisors,
        (ArithmeticFunction.moebius d : ℂ) * (if χ ^ (q.totient / d) = 1 then 1 else 0) := by
    calc (q.totient : ℂ) * q.totient.totient
        = ∑ a : ZMod q, (q.totient : ℂ) * (if orderOf a = q.totient then 1 else 0) := by
          rw [← Finset.mul_sum, Finset.sum_boole, card_primRoots]
      _ = ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, ∑ d ∈ q.totient.divisors,
            (ArithmeticFunction.moebius d : ℂ) * (χ ^ (q.totient / d)) a := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [mul_indicator_eq]
          refine Finset.sum_congr rfl fun χ _ ↦ Finset.sum_congr rfl fun d hd ↦ ?_
          rw [MulChar.pow_apply' χ (div_ne_zero_of_mem hd)]
      _ = ∑ χ : DirichletCharacter ℂ q, ∑ d ∈ q.totient.divisors,
            (ArithmeticFunction.moebius d : ℂ) * ∑ a : ZMod q, (χ ^ (q.totient / d)) a := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ _ ↦ ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun d _ ↦ (Finset.mul_sum _ _ _).symm
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun χ _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ ↦ ?_
          rw [sum_char_eq]
          split_ifs <;> ring
  exact (mul_left_cancel₀ hm0 hsum).symm

open scoped Classical in
/-- **The prime powers that are primitive roots.** For every `η > 0` there is `C ≥ 0` such that for every modulus
`q ≥ 1` with `(ℤ/qℤ)ˣ` cyclic, `m = φ(q)` and every `x > 1`,
`|m Σ_{n ≤ x} Λ(n)[ord n = m] − φ(m)ψ(x, χ₀)| ≤ m d(m) C log(q + 2)x^{11/12+η}`, where `χ₀` is the trivial character
mod `q`. -/
theorem norm_sum_primRoot_sub_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], IsCyclic (ZMod q)ˣ → ∀ x : ℝ, 1 < x →
      ‖(q.totient : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (if orderOf (n : ZMod q) = q.totient then 1 else 0) -
            q.totient.totient * psiChi (1 : DirichletCharacter ℂ q) x‖ ≤
        q.totient * q.totient.divisors.card * (C * Real.log (q + 2) * x ^ (11 / 12 + η)) := by
  obtain ⟨C, hC, hψ⟩ := ChiUniform.psiChi_le_uniform hη
  refine ⟨C, hC, fun q _ hcyc x hx ↦ ?_⟩
  set B : ℝ := C * Real.log (q + 2) * x ^ (11 / 12 + η) with hBdef
  have hx0 : 0 < x := by linarith
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith)
    positivity
  -- the weighted sum by characters
  have hid : (q.totient : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (if orderOf (n : ZMod q) = q.totient then 1 else 0) = ∑ χ : DirichletCharacter ℂ q,
        ∑ d ∈ q.totient.divisors, (ArithmeticFunction.moebius d : ℂ) * psiChi (χ ^ (q.totient / d)) x := by
    rw [Finset.mul_sum]
    have h1 : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, (q.totient : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) *
        (if orderOf (n : ZMod q) = q.totient then 1 else 0)) = ∑ χ : DirichletCharacter ℂ q,
          ∑ d ∈ q.totient.divisors, (ArithmeticFunction.moebius d : ℂ) *
            ((χ ^ (q.totient / d)) n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      intro n _
      rw [mul_left_comm, mul_indicator_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [MulChar.pow_apply' χ (div_ne_zero_of_mem hd)]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [psiChi, Finset.mul_sum]
  -- the pairs with `χ^{m/d} = 1`, and the others
  have hsplit : ∀ χ : DirichletCharacter ℂ q, ∀ d ∈ q.totient.divisors,
      (ArithmeticFunction.moebius d : ℂ) * psiChi (χ ^ (q.totient / d)) x =
        (ArithmeticFunction.moebius d : ℂ) * (if χ ^ (q.totient / d) = 1 then 1 else 0) *
            psiChi (1 : DirichletCharacter ℂ q) x +
          (ArithmeticFunction.moebius d : ℂ) *
            (if χ ^ (q.totient / d) = 1 then 0 else psiChi (χ ^ (q.totient / d)) x) := by
    intro χ d _
    split_ifs with h
    · rw [h]; ring
    · ring
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  set E : ℂ := ∑ χ : DirichletCharacter ℂ q, ∑ d ∈ q.totient.divisors, (ArithmeticFunction.moebius d : ℂ) *
      (if χ ^ (q.totient / d) = 1 then 0 else psiChi (χ ^ (q.totient / d)) x) with hEdef
  have hmain : ∑ χ : DirichletCharacter ℂ q, ∑ d ∈ q.totient.divisors,
      (ArithmeticFunction.moebius d : ℂ) * psiChi (χ ^ (q.totient / d)) x =
        q.totient.totient * psiChi (1 : DirichletCharacter ℂ q) x + E := by
    rw [Finset.sum_congr rfl fun χ _ ↦ Finset.sum_congr rfl (hsplit χ)]
    simp only [Finset.sum_add_distrib]
    rw [← sum_coeff_eq_totient, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun χ _ ↦ (Finset.sum_mul _ _ _).symm
  have hE : ‖E‖ ≤ q.totient * q.totient.divisors.card * B := by
    calc ‖E‖ ≤ ∑ χ : DirichletCharacter ℂ q, ∑ d ∈ q.totient.divisors, ‖(ArithmeticFunction.moebius d : ℂ) *
          (if χ ^ (q.totient / d) = 1 then 0 else psiChi (χ ^ (q.totient / d)) x)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ ↦ norm_sum_le _ _)
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, ∑ _d ∈ q.totient.divisors, B := by
        refine Finset.sum_le_sum fun χ _ ↦ Finset.sum_le_sum fun d _ ↦ ?_
        have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        rw [norm_mul]
        split_ifs with h
        · rw [norm_zero, mul_zero]; exact hB0
        · calc ‖(ArithmeticFunction.moebius d : ℂ)‖ * ‖psiChi (χ ^ (q.totient / d)) x‖ ≤ 1 * B :=
                mul_le_mul hμ (hψ q _ h x hx) (norm_nonneg _) zero_le_one
            _ = B := one_mul B
      _ = q.totient * q.totient.divisors.card * B := by
        rw [Finset.sum_const, Finset.sum_const, hcard, nsmul_eq_mul, nsmul_eq_mul]; ring
  rw [hid, hmain, add_sub_cancel_left]
  exact hE

/-- Ankeny's algebra, as in `LeastNonresidue.rpow_le_of_forall_eq_of`: if `x ≥ 100`, `A > 12` and
`ψ(x) − 4√x log x − log q ≤ U ≤ C₁ log(q + 2)x^{1−1/A}`, then `x^{1/A} ≤ 4(C₁ + 11) log(q + 2)`. -/
lemma rpow_le_of_le {A C₁ U x : ℝ} (hA : 12 < A) {q : ℕ} (hq : q ≠ 0) (hx : 100 ≤ x)
    (hlow : ψ x - 4 * √x * Real.log x - Real.log q ≤ U)
    (hup : U ≤ C₁ * Real.log (q + 2) * x ^ (1 - 1 / A)) :
    x ^ (1 / A) ≤ 4 * (C₁ + 11) * Real.log (q + 2) := by
  have hA0 : 0 < A := by linarith
  have hiA : 1 / A < 1 / 12 := by
    rw [div_lt_div_iff₀ hA0 (by norm_num)]; linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set L : ℝ := Real.log (q + 2) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq
    linarith
  set e : ℝ := 1 - 1 / A with hedef
  have hxe : 1 ≤ x ^ e := Real.one_le_rpow hx1 (by rw [hedef]; linarith)
  have hψx := LeastNonresidue.psi_ge_quarter hx
  -- `√x log x ≤ (12/5)x^e`
  have hsqrt : √x * Real.log x ≤ 12 / 5 * x ^ e := by
    have h1 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 5 / 12)
    have h2 : √x * (x ^ (5 / 12 : ℝ) / (5 / 12)) = 12 / 5 * x ^ (11 / 12 : ℝ) := by
      rw [Real.sqrt_eq_rpow, mul_div_assoc', mul_comm, ← Real.rpow_add hx0]
      ring_nf
    have h3 : x ^ (11 / 12 : ℝ) ≤ x ^ e :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hedef]; linarith)
    calc √x * Real.log x ≤ √x * (x ^ (5 / 12 : ℝ) / (5 / 12)) :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = 12 / 5 * x ^ (11 / 12 : ℝ) := h2
      _ ≤ 12 / 5 * x ^ e := by gcongr
  have hlogq : Real.log q ≤ L * x ^ e := by
    have h1 : Real.log q ≤ L :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hq) (by linarith)
    exact h1.trans (le_mul_of_one_le_right (by linarith) hxe)
  -- `x/4 ≤ (C₁ + 11)·L·x^e`
  have hmain : x / 4 ≤ (C₁ + 11) * L * x ^ e := by
    have h1 : 12 / 5 * x ^ e ≤ 12 / 5 * (L * x ^ e) := by
      have := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ x ^ e) hL
      linarith
    have h2 : (C₁ + 11) * L * x ^ e = C₁ * L * x ^ e + 11 * (L * x ^ e) := by ring
    have h3 : 0 ≤ L * x ^ e := by positivity
    nlinarith
  have hsplit : x = x ^ (1 / A) * x ^ e := by
    rw [← Real.rpow_add hx0, hedef, show 1 / A + (1 - 1 / A) = (1 : ℝ) by ring, Real.rpow_one]
  have hxe0 : 0 < x ^ e := by positivity
  have h5 : x ^ (1 / A) * x ^ e ≤ (4 * (C₁ + 11) * L) * x ^ e := by
    rw [← hsplit]; linarith
  exact le_of_mul_le_mul_right h5 hxe0

/-- A prime power `ℓᵏ` (`k ≥ 1`) of order `φ(q)` mod `q` has `ℓ` of order `φ(q)` too, and `ℓ ∤ q`. -/
lemma orderOf_prime_eq {ℓ k : ℕ} (hℓ : ℓ.Prime) (hk : 0 < k)
    (h : orderOf ((ℓ ^ k : ℕ) : ZMod q) = q.totient) : orderOf (ℓ : ZMod q) = q.totient ∧ ¬ ℓ ∣ q := by
  have hm0 : q.totient ≠ 0 := totient_ne_zero
  rw [Nat.cast_pow] at h
  have hu : IsUnit ((ℓ : ZMod q) ^ k) := by
    have h1 : ((ℓ : ZMod q) ^ k) ^ q.totient = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    exact IsUnit.of_pow_eq_one h1 hm0
  have hℓu : IsUnit (ℓ : ZMod q) := (isUnit_pow_iff hk.ne').1 hu
  refine ⟨Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (pow_totient_eq_one hℓu)) ?_, ?_⟩
  · rw [← h]; exact orderOf_pow_dvd k
  · exact (Nat.Prime.coprime_iff_not_dvd hℓ).1 ((ZMod.isUnit_iff_coprime ℓ q).1 hℓu)

/-- **The least prime primitive root.** For every `A > 12` there is `C > 0` such that every modulus `q ≥ 1` with
`(ℤ/qℤ)ˣ` cyclic has a primitive root that is a prime `ℓ ∤ q` with `ℓ ≤ C(d(φ(q))² log(q + 2))^A`, where `d` counts
divisors. -/
theorem exists_prime_primRoot_le {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], IsCyclic (ZMod q)ˣ →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ q ∧ orderOf (ℓ : ZMod q) = q.totient ∧
        (ℓ : ℝ) ≤ C * ((q.totient.divisors.card : ℝ) ^ 2 * Real.log (q + 2)) ^ A := by
  have hA0 : 0 < A := by linarith
  have hiA : 1 / A < 1 / 12 := by
    rw [div_lt_div_iff₀ hA0 (by norm_num)]; linarith
  obtain ⟨C₀, hC₀, hE⟩ := norm_sum_primRoot_sub_le (η := 1 / 12 - 1 / A) (by linarith)
  set K : ℝ := 4 * (C₀ + 11) with hKdef
  have hK : 0 < K := by positivity
  refine ⟨101 + K ^ A, by positivity, fun q _ hcyc ↦ ?_⟩
  have hq0 : q ≠ 0 := NeZero.ne q
  have hm0 : q.totient ≠ 0 := totient_ne_zero
  set D : ℝ := (q.totient.divisors.card : ℝ) with hDdef
  have hD : 1 ≤ D := by
    rw [hDdef]; exact_mod_cast Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hm0⟩
  set L : ℝ := Real.log (q + 2) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0
    linarith
  set Y : ℝ := D ^ 2 * L with hYdef
  have hD2 : 1 ≤ D ^ 2 := one_le_pow₀ hD
  have hY : 1 ≤ Y := by rw [hYdef]; nlinarith
  have hYA : 1 ≤ Y ^ A := Real.one_le_rpow hY hA0.le
  set X : ℝ := max 100 ((K * Y) ^ A) + 1 with hXdef
  have hX100 : 100 ≤ X := by
    have := le_max_left (100 : ℝ) ((K * Y) ^ A); linarith
  have hXC : X ≤ (101 + K ^ A) * Y ^ A := by
    have h1 : max 100 ((K * Y) ^ A) ≤ 100 + K ^ A * Y ^ A := by
      rw [Real.mul_rpow hK.le (by linarith)]
      have : 0 ≤ K ^ A * Y ^ A := by positivity
      exact max_le (by linarith) (by linarith)
    have h2 : 101 + K ^ A * Y ^ A ≤ (101 + K ^ A) * Y ^ A := by nlinarith
    linarith
  by_contra hcon
  push Not at hcon
  -- no prime power `n ≤ X` is a primitive root
  have hzero : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
      (if orderOf (n : ZMod q) = q.totient then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp [hΛ]
    rw [ite_eq_right, mul_zero]
    intro hord
    obtain ⟨ℓ, k, hℓ, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hΛ)
    obtain ⟨hord', hℓq⟩ := orderOf_prime_eq hℓ hk hord
    have hℓX : (ℓ : ℝ) ≤ X := by
      have h1 : ℓ ≤ ⌊X⌋₊ := (Nat.le_self_pow hk.ne' ℓ).trans (Finset.mem_Icc.1 hn).2
      exact (Nat.cast_le.2 h1).trans (Nat.floor_le (by linarith))
    exact (hcon ℓ hℓ hℓq hord').not_ge (hℓX.trans hXC)
  have hb := hE q hcyc X (by linarith)
  rw [hzero, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_natCast] at hb
  -- the upper bound for `Re ψ(X, χ₀)`
  have hφ : (0 : ℝ) < q.totient.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0)
  have hmφ : (q.totient : ℝ) ≤ q.totient.totient * D := by
    rw [hDdef]; exact_mod_cast LinnikCGLConst.le_totient_mul_card_divisors q.totient
  set B : ℝ := C₀ * L * X ^ (11 / 12 + (1 / 12 - 1 / A)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hup : (psiChi (1 : DirichletCharacter ℂ q) X).re ≤ D ^ 2 * C₀ * L * X ^ (1 - 1 / A) := by
    have h1 : (q.totient.totient : ℝ) * (psiChi (1 : DirichletCharacter ℂ q) X).re ≤
        q.totient.totient * (D * (D * B)) := by
      calc (q.totient.totient : ℝ) * (psiChi (1 : DirichletCharacter ℂ q) X).re
          ≤ q.totient.totient * ‖psiChi (1 : DirichletCharacter ℂ q) X‖ :=
            mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hφ.le
        _ ≤ q.totient * D * B := hb
        _ ≤ (q.totient.totient * D) * D * B := by gcongr
        _ = q.totient.totient * (D * (D * B)) := by ring
    have h2 := le_of_mul_le_mul_left h1 hφ
    have hexp : X ^ (11 / 12 + (1 / 12 - 1 / A)) = X ^ (1 - 1 / A) := by
      rw [show (11 : ℝ) / 12 + (1 / 12 - 1 / A) = 1 - 1 / A by ring]
    calc (psiChi (1 : DirichletCharacter ℂ q) X).re ≤ D * (D * B) := h2
      _ = D ^ 2 * C₀ * L * X ^ (1 - 1 / A) := by rw [hBdef, hexp]; ring
  -- the lower bound, at the trivial character
  have hlow := LeastNonresidue.re_psiChi_ge (1 : DirichletCharacter ℂ q) (ε := 1) (Or.inl rfl)
    (by linarith : (1 : ℝ) ≤ X) fun p hp _ hpq ↦ by
      have hu : IsUnit (p : ZMod q) :=
        (ZMod.isUnit_iff_coprime p q).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
      rw [MulChar.one_apply hu, Complex.ofReal_one]
  rw [one_mul] at hlow
  have hX := rpow_le_of_le hA hq0 hX100 hlow hup
  rw [← hLdef] at hX
  -- but `X^{1/A} > K Y`
  have hgt : K * Y < X ^ (1 / A) := by
    have h1 : (K * Y) ^ A < X := by
      have := le_max_right (100 : ℝ) ((K * Y) ^ A); linarith
    have h2 : ((K * Y) ^ A) ^ (1 / A) = K * Y := by
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hA0.ne', Real.rpow_one]
    rw [← h2]
    exact Real.rpow_lt_rpow (by positivity) h1 (by positivity)
  have hKY : 4 * (D ^ 2 * C₀ + 11) * L ≤ K * Y := by
    rw [hKdef, hYdef]
    have : D ^ 2 * C₀ + 11 ≤ (C₀ + 11) * D ^ 2 := by nlinarith
    have hL0 : 0 ≤ L := by linarith
    nlinarith
  linarith

/-- **The least prime primitive root is at most `q^ε`.** For every `ε > 0` there is `C > 0` such that every modulus
`q ≥ 1` with `(ℤ/qℤ)ˣ` cyclic has a primitive root that is a prime `ℓ ∤ q` with `ℓ ≤ Cq^ε`. -/
theorem exists_prime_primRoot_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], IsCyclic (ZMod q)ˣ →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ q ∧ orderOf (ℓ : ZMod q) = q.totient ∧ (ℓ : ℝ) ≤ C * (q : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := exists_prime_primRoot_le (A := 13) (by norm_num)
  set δ : ℝ := min (ε / 39) 1 with hδdef
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : 39 * δ ≤ ε := by have := min_le_left (ε / 39) 1; linarith
  have hCd : 1 ≤ LinnikPower.Cdiv δ := LinnikPower.one_le_Cdiv hδ hδ1
  set W : ℝ := LinnikPower.Cdiv δ ^ 2 * (3 ^ δ / δ) with hWdef
  have hW : 0 < W := by positivity
  refine ⟨C * W ^ (13 : ℝ), by positivity, fun q _ hcyc ↦ ?_⟩
  obtain ⟨ℓ, hℓ, hℓq, hord, hle⟩ := h q hcyc
  refine ⟨ℓ, hℓ, hℓq, hord, hle.trans ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := by linarith
  -- `d(φ(q)) ≤ C_δ q^δ`
  have hd : (q.totient.divisors.card : ℝ) ≤ LinnikPower.Cdiv δ * (q : ℝ) ^ δ := by
    refine (LinnikPower.card_divisors_le hδ hδ1 q.totient).trans ?_
    gcongr
    exact_mod_cast Nat.totient_le q
  -- `log(q + 2) ≤ 3^δ q^δ/δ`
  have hlog : Real.log (q + 2) ≤ 3 ^ δ / δ * (q : ℝ) ^ δ := by
    refine (Real.log_le_rpow_div (by positivity) hδ).trans ?_
    have h3 : ((q : ℝ) + 2) ^ δ ≤ (3 * q) ^ δ := Real.rpow_le_rpow (by positivity) (by linarith) hδ.le
    rw [Real.mul_rpow (by norm_num) hq0] at h3
    calc ((q : ℝ) + 2) ^ δ / δ ≤ 3 ^ δ * (q : ℝ) ^ δ / δ := by gcongr
      _ = 3 ^ δ / δ * (q : ℝ) ^ δ := by ring
  have hY : (q.totient.divisors.card : ℝ) ^ 2 * Real.log (q + 2) ≤ W * (q : ℝ) ^ (3 * δ) := by
    have hd0 : (0 : ℝ) ≤ q.totient.divisors.card := Nat.cast_nonneg _
    have hlog0 : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith)
    calc (q.totient.divisors.card : ℝ) ^ 2 * Real.log (q + 2)
        ≤ (LinnikPower.Cdiv δ * (q : ℝ) ^ δ) ^ 2 * (3 ^ δ / δ * (q : ℝ) ^ δ) := by gcongr
      _ = W * ((q : ℝ) ^ δ * (q : ℝ) ^ δ * (q : ℝ) ^ δ) := by rw [hWdef]; ring
      _ = W * (q : ℝ) ^ (3 * δ) := by
          rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]; ring_nf
  have hY0 : 0 ≤ (q.totient.divisors.card : ℝ) ^ 2 * Real.log (q + 2) := by
    have : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith)
    positivity
  calc C * ((q.totient.divisors.card : ℝ) ^ 2 * Real.log (q + 2)) ^ (13 : ℝ)
      ≤ C * (W * (q : ℝ) ^ (3 * δ)) ^ (13 : ℝ) := by gcongr
    _ = C * W ^ (13 : ℝ) * (q : ℝ) ^ (39 * δ) := by
        rw [Real.mul_rpow hW.le (by positivity), ← Real.rpow_mul hq0]; ring_nf
    _ ≤ C * W ^ (13 : ℝ) * (q : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 hδε) (by positivity)

/-- **The least prime primitive root mod a prime.** For every `ε > 0` there is `C > 0` such that every prime `p` has
a primitive root that is a prime `ℓ ≠ p` with `ℓ ≤ Cp^ε`. -/
theorem exists_prime_primRoot_le_rpow_prime {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ orderOf (ℓ : ZMod p) = p - 1 ∧ (ℓ : ℝ) ≤ C * (p : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := exists_prime_primRoot_le_rpow hε
  refine ⟨C, hC, fun p hp ↦ ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ℓ, hℓ, hℓp, hord, hle⟩ := h p (ZMod.isCyclic_units_prime hp)
  refine ⟨ℓ, hℓ, fun h ↦ hℓp (by subst h; exact dvd_rfl), ?_, hle⟩
  rwa [Nat.totient_prime hp] at hord

/-- **The least prime primitive root mod a prime power.** For every `ε > 0` there is `C > 0` such that for every odd
prime `p` and every `k ≥ 1`, some prime `ℓ ≠ p` with `ℓ ≤ C(pᵏ)^ε` generates `(ℤ/pᵏℤ)ˣ`. -/
theorem exists_prime_primRoot_le_rpow_pow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ k : ℕ, 0 < k →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ orderOf (ℓ : ZMod (p ^ k)) = (p ^ k).totient ∧
        (ℓ : ℝ) ≤ C * ((p ^ k : ℕ) : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := exists_prime_primRoot_le_rpow hε
  refine ⟨C, hC, fun p hp hp2 k hk ↦ ?_⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  obtain ⟨ℓ, hℓ, hℓp, hord, hle⟩ := h (p ^ k) (ZMod.isCyclic_units_of_prime_pow p hp hp2 k)
  exact ⟨ℓ, hℓ, fun h ↦ hℓp (by subst h; exact dvd_pow_self _ hk.ne'), hord, hle⟩

/-- **Safe primes.** For every `A > 12` there is `C > 0` such that for every odd prime `r` with `p = 2r + 1` prime,
some prime `ℓ ≤ C(log(p + 2))^A` generates `(ℤ/pℤ)ˣ`: here `d(p − 1) = d(2r) = 4`. -/
theorem exists_prime_primRoot_le_safe {A : ℝ} (hA : 12 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ p r : ℕ, r.Prime → r ≠ 2 → p = 2 * r + 1 → p.Prime →
      ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧ (ℓ : ℝ) ≤ C * Real.log (p + 2) ^ A := by
  have hA0 : 0 < A := by linarith
  obtain ⟨C, hC, h⟩ := exists_prime_primRoot_le hA
  refine ⟨C * 16 ^ A, by positivity, fun p r hr hr2 hpr hp ↦ ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ℓ, hℓ, -, hord, hle⟩ := h p (ZMod.isCyclic_units_prime hp)
  have htot : p.totient = 2 * r := by rw [Nat.totient_prime hp, hpr]; omega
  have hcard : (p.totient.divisors.card : ℝ) = 4 := by
    have hcop : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2)
    rw [htot, Nat.Coprime.card_divisors_mul hcop, Nat.prime_two.divisors, hr.divisors,
      Finset.card_pair (show (1 : ℕ) ≠ 2 by norm_num), Finset.card_pair hr.one_lt.ne]
    norm_num
  refine ⟨ℓ, hℓ, by rwa [Nat.totient_prime hp] at hord, hle.trans ?_⟩
  rw [hcard]
  have hlog0 : 0 ≤ Real.log (p + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) p; linarith)
  rw [show (4 : ℝ) ^ 2 * Real.log (p + 2) = 16 * Real.log (p + 2) by norm_num,
    Real.mul_rpow (by norm_num) hlog0]
  exact le_of_eq (by ring)

end LeastPrimitiveRoot

#print axioms LeastPrimitiveRoot.norm_sum_primRoot_sub_le
#print axioms LeastPrimitiveRoot.exists_prime_primRoot_le
#print axioms LeastPrimitiveRoot.exists_prime_primRoot_le_rpow
#print axioms LeastPrimitiveRoot.exists_prime_primRoot_le_rpow_prime
#print axioms LeastPrimitiveRoot.exists_prime_primRoot_le_rpow_pow
#print axioms LeastPrimitiveRoot.exists_prime_primRoot_le_safe
