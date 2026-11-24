/-
# Primes in almost all reduced classes: below `q^{1+η}` under GRH, and `q^{1.1667+η}` from the curve `g7d`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. Let `A ≥ 2`, `B ≥ 0` and `C ≥ 0` with the density estimate `Linnik.CharDensity A B C`. For every
`η > 0` there are `K` and `c > 0` such that for every modulus `q ≥ 1`, all the `φ(q)` reduced classes mod `q` but at
most `Kφ(q)q^{−c}` hold a prime `p ≤ Kq^{A/2+η}` (`almostAll_of_charDensity`). This is a theorem about almost all
classes, not every class: for every class the same estimate gives the exponent `A + η`
(`Linnik.linnik_of_charDensity`), and no exponent below `2` is known for every class, even under GRH.

* `almostAll_one_of_GRH`, `almostAll_one`: GRH gives `A = 2` (`LinnikGRH.charDensity_two_of_GRH`), so all classes but
  `Kφ(q)q^{−c}` hold a prime `p ≤ Kq^{1+η}`. `almostAll_one` takes GRH in the words of L. Alpöge's Lean archive
  (`LinnikGRH.DirichletRH`), which proves it on its own pins (`tools/rh/README.md`); here it stays a hypothesis.
* `almostAll_g7d`: the library's curve `g7d` gives `A = 11667/5000` (`LinnikG7.charDensity_g7d`), so all classes but
  `Kφ(q)q^{−c}` hold a prime `p ≤ Kq^{11667/10000+η}`, with no hypothesis. CONDITIONAL, below.
* `almostAll_turan`: under GRH, a bound of Turán's type for the exceptions, from GRH's `√x` directly: for `0 < δ ≤ 1`,
  all classes but `Kq^{1−δ+η}` hold a prime `p ≤ Kq^{1+δ}`; at `δ = 1 − κ`, all but `Kq^{κ+η}` hold one below
  `Kq^{2−κ}`.

The method is classical: the deduction of `LinnikDeduction` in mean square over the classes. With
`S(x; q, a) = Σ_{n ≡ a} Λ(n)e^{−n/x}` and `S_χ(x) = Σ_n χ(n)Λ(n)e^{−n/x}`, orthogonality gives
`φ(q)S(x; q, a) = S_1(x) + E(a)`, `E(a) = Σ_{χ ≠ 1} χ(a⁻¹)S_χ(x)`, and Parseval over the classes gives
`Σ_a |E(a)|² = φ(q)Σ_{χ ≠ 1}|S_χ(x)|²`. In a class with no prime up to `Y = 10x log x`, `S(x; q, a)` is made of prime
powers and of the terms beyond `Y`; over all such classes together these are at most `2√Y log Y + 96x³e^{−Y/(2x)}`,
where one class at a time would need `x ≥ q²`. Against the main term `Re S_1(x) ≥ x/24`, Markov's inequality counts
those classes by `φ(q)(x^{−1/2+ε} + Σ_{χ ≠ 1}|S_χ(x)|²/x²)`, and the density estimate bounds the sum level by level, as
`Linnik.error_le` does in mean, by `(qT)^{A(1−σ)}x^{2σ}` at the worst `σ`: that is `x^{2−c}` once `q^{A/2+η} ≤ x`.

* `sum_norm_sq_eq`: Parseval, `Σ_{a mod q}|Σ_{χ ∈ s} χ(a)c_χ|² = φ(q)Σ_{χ ∈ s}|c_χ|²`, from Mathlib's
  `MulChar.sum_eq_zero_of_ne_one` (`sum_mul_conj`).
* `card_bad_le`: the count, `#B·x² ≤ φ(q)(48x(2√Y log Y + 96x³e^{−Y/(2x)}) + 2304Σ_{χ ≠ 1}|S_χ(x)|²)`, with
  `Σ_{a ∈ B} S(x; q, a)` bounded for the classes of `B` together (`Linnik.sum_SAP_le_of_noPrime`).
* `error_sq_le`: under `CharDensity`, `Σ_{χ ≠ 1}|S_χ(x)|²` is at most `4M*(δ) log(q + 2)` times the bound of
  `Linnik.error_le` at `x²`, by the same count by levels (`Linnik.sum_level_le`); `Linnik.total_le` bounds it
  (`total_parts`).
* `exists_X₀`, `card_bad_density`, `almostAll_of_charDensity`: the count at `x = X₀q^{(A+η₀)/2}`, `η₀ = min(η, 1)/2`.
* `error_sq_le_of_RH`, `Z_le_sqrt`, `almostAll_turan`: under GRH every character has `|S_χ(x)| ≪ log(q + 2)x^{1/2+ε}`,
  with no levels, and the prime powers are `≪ x^{1/2+ε}`; the count at `x = X₀q^{1+δ−8ε}`.

**CONDITIONAL.** Every result here goes through `Linnik.norm_Sx_le`, whose contour shift uses the zero-free
half-plane `Re s > 11/12` for every Dirichlet `L`-function (`Eis.LFunction_ne_zero_of_re_gt`, OpenAI's, proved in the
library; `formalisations/openai-half-plane.md`), an input that no referee has read; the levels of `Linnik.error_le` use
it too. GRH implies the half-plane, so `almostAll_one_of_GRH`, `almostAll_one` and `almostAll_turan` rest mathematically
on GRH alone, though their Lean proofs use the library's proof of the half-plane. `almostAll_g7d` has no hypothesis,
and rests on the half-plane and, through the curve `g7d`, on Chen, Gupta and Li's Proposition 3.1
(`LinnikCGLHB101.prop31`), the library's other unreviewed input: Lean checks it with the standard axioms only, and it
must be cited as conditional on them.
-/
import LinnikGRH
import LinnikG7

open Real ArithmeticFunction

noncomputable section

namespace LinnikAlmostAll

open Linnik DirichletCharacter

/-! ### Parseval over the classes -/

/-- **Orthogonality over the classes**: `Σ_{a mod q} χ(a)·conj ξ(a)` is `φ(q)` if `χ = ξ` and `0` otherwise
(Mathlib's `MulChar.sum_eq_zero_of_ne_one` at `χξ⁻¹`). -/
lemma sum_mul_conj {q : ℕ} [NeZero q] (χ ξ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, χ a * starRingEnd ℂ (ξ a) = if χ = ξ then (q.totient : ℂ) else 0 := by
  have e : ∀ a : ZMod q, χ a * starRingEnd ℂ (ξ a) = (χ * ξ⁻¹) a := fun a => by
    rw [MulChar.mul_apply, starRingEnd_apply, MulChar.star_apply']
  rw [Finset.sum_congr rfl fun a _ => e a]
  split_ifs with h
  · rw [h, mul_inv_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one (mul_inv_eq_one.not.2 h)

/-- **Parseval over the classes**: `Σ_{a mod q} |Σ_{χ ∈ s} χ(a)c_χ|² = φ(q)Σ_{χ ∈ s}|c_χ|²` for every set `s` of
characters mod `q` (`sum_mul_conj`). -/
theorem sum_norm_sq_eq {q : ℕ} [NeZero q] (s : Finset (DirichletCharacter ℂ q)) (c : DirichletCharacter ℂ q → ℂ) :
    ∑ a : ZMod q, ‖∑ χ ∈ s, χ a * c χ‖ ^ 2 = q.totient * ∑ χ ∈ s, ‖c χ‖ ^ 2 := by
  classical
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have key : ∑ a : ZMod q, (∑ χ ∈ s, χ a * c χ) * starRingEnd ℂ (∑ χ ∈ s, χ a * c χ) =
      (q.totient : ℂ) * ∑ χ ∈ s, c χ * starRingEnd ℂ (c χ) := by
    simp_rw [map_sum, map_mul, Finset.sum_mul_sum]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [Finset.sum_comm]
    have e : ∀ ξ ∈ s, ∑ a : ZMod q, χ a * c χ * (starRingEnd ℂ (ξ a) * starRingEnd ℂ (c ξ)) =
        if χ = ξ then c χ * starRingEnd ℂ (c ξ) * (q.totient : ℂ) else 0 := fun ξ _ => by
      rw [← mul_ite_zero, ← sum_mul_conj, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq s χ, ite_eq_left hχ]
    ring
  calc ∑ a : ZMod q, ‖∑ χ ∈ s, χ a * c χ‖ ^ 2
      = (∑ a : ZMod q, (∑ χ ∈ s, χ a * c χ) * starRingEnd ℂ (∑ χ ∈ s, χ a * c χ)).re := by
        rw [Complex.re_sum]; exact Finset.sum_congr rfl fun a _ => hsq _
    _ = q.totient * ∑ χ ∈ s, ‖c χ‖ ^ 2 := by
        have e : (q.totient : ℂ) * ∑ χ ∈ s, c χ * starRingEnd ℂ (c χ) =
            ((q.totient * ∑ χ ∈ s, ‖c χ‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          congr 1
          exact Finset.sum_congr rfl fun χ _ => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
        rw [key, e, Complex.ofReal_re]

/-! ### The classes with no small prime -/

section

open scoped Chebyshev

open scoped Classical in
/-- **Counting the classes with no small prime, by Parseval.** Let `q ≥ 1`, `x ≥ 100` with `q log x ≤ x/8`, and
`Y ≥ 1`, and let `B` be the set of units `a` mod `q` whose class holds no prime `p ≤ Y`. Then
`#B·x² ≤ φ(q)(48x(2√Y log Y + 96x³e^{−Y/(2x)}) + 2304Σ_{χ ≠ 1}|S_χ(x)|²)`. For `a ∈ B`, orthogonality
(`Linnik.totient_mul_SAP`) gives `φ(q)S(x; q, a) = S_1(x) + E(a)`, `E(a) = Σ_{χ ≠ 1} χ(a⁻¹)S_χ(x)`, and
`Re S_1(x) ≥ e^{−1}(x/4 − q log x) ≥ x/24` (`Linnik.re_Sx_one_ge`); so `x/24 ≤ φ(q)S(x; q, a) + |E(a)|`, and
`x² ≤ 48xφ(q)S(x; q, a) + 2304|E(a)|²`. Summed over `B`, the first terms are bounded by
`Linnik.sum_SAP_le_of_noPrime` and the second by Parseval (`sum_norm_sq_eq`). -/
theorem card_bad_le (q : ℕ) [NeZero q] {x Y : ℝ} (hx : 100 ≤ x) (hqx : q * Real.log x ≤ x / 8) (hY : 1 ≤ Y) :
    ((Finset.univ.filter fun a : (ZMod q)ˣ => ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y → (p : ZMod q) ≠ a).card : ℝ) *
        x ^ 2 ≤
      q.totient * (48 * x * (2 * √Y * Real.log Y + 96 * x ^ 3 * Real.exp (-(Y / (2 * x)))) +
        2304 * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2) := by
  classical
  set B := Finset.univ.filter fun a : (ZMod q)ˣ => ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y → (p : ZMod q) ≠ a
  set S := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) with hS
  have hx0 : 0 < x := by linarith
  have hφ0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  -- the trivial character
  have he : 1 / 3 ≤ Real.exp (-1) := by
    have h1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    have h2 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (-1)]
  have hone : x / 24 ≤ (Sx (1 : DirichletCharacter ℂ q) x).re := by
    have h1 := re_Sx_one_ge q (by linarith : (1 : ℝ) ≤ x)
    have h2 := LeastNonresidue.psi_ge_quarter hx
    have h3 : (q.primeFactors.card : ℝ) * Real.log x ≤ q * Real.log x :=
      mul_le_mul_of_nonneg_right (card_primeFactors_le q) hlogx
    have h4 : x / 8 ≤ ψ x - q.primeFactors.card * Real.log x := by linarith
    nlinarith
  -- one class
  have hpt : ∀ a ∈ B, x ^ 2 ≤ 48 * x * (q.totient * SAP q a x) +
      2304 * ‖∑ χ ∈ S, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * Sx χ x‖ ^ 2 := by
    intro a _
    have horth := totient_mul_SAP q a.isUnit hx0
    rw [ZMod.inv_coe_unit] at horth
    have hsplit : ∑ χ : DirichletCharacter ℂ q, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * Sx χ x =
        Sx (1 : DirichletCharacter ℂ q) x + ∑ χ ∈ S, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * Sx χ x := by
      rw [hS, Finset.filter_ne', ← Finset.add_sum_erase _ _ (Finset.mem_univ 1), MulChar.one_apply (a⁻¹).isUnit,
        one_mul]
    have hre : (q.totient : ℝ) * SAP q a x =
        (∑ χ : DirichletCharacter ℂ q, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * Sx χ x).re := by
      rw [← horth]; simp
    rw [hsplit, Complex.add_re] at hre
    set E := ∑ χ ∈ S, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * Sx χ x
    have hE : -‖E‖ ≤ E.re := by have := Complex.abs_re_le_norm E; linarith [neg_abs_le E.re]
    have hSAP : 0 ≤ SAP q a x := tsum_nonneg fun n => by
      split_ifs
      · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
      · exact le_rfl
    have hu : 0 ≤ (q.totient : ℝ) * SAP q a x := mul_nonneg hφ0 hSAP
    have hlin : x ≤ 24 * ((q.totient : ℝ) * SAP q a x) + 24 * ‖E‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlin hx0.le, sq_nonneg (x / 2 - 24 * ‖E‖), mul_nonneg hx0.le hu]
  -- the prime powers of the classes of `B`, together
  have hZ : ∑ a ∈ B, SAP q a x ≤ 2 * √Y * Real.log Y + 96 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by
    have e : ∑ a ∈ B, SAP q a x = ∑ b ∈ B.map ⟨Units.val, fun _ _ h => Units.ext h⟩, SAP q b x := by
      rw [Finset.sum_map]; rfl
    rw [e]
    refine sum_SAP_le_of_noPrime q _ hx0 hY fun b hb => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hb
    exact (Finset.mem_filter.1 ha).2
  -- the other characters, by Parseval
  have hE2 : ∑ a ∈ B, ‖∑ χ ∈ S, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * Sx χ x‖ ^ 2 ≤
      q.totient * ∑ χ ∈ S, ‖Sx χ x‖ ^ 2 := by
    have e : ∑ a ∈ B, ‖∑ χ ∈ S, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * Sx χ x‖ ^ 2 =
        ∑ b ∈ B.map ⟨fun a => ((a⁻¹ : (ZMod q)ˣ) : ZMod q), fun _ _ h => inv_injective (Units.ext h)⟩,
          ‖∑ χ ∈ S, χ b * Sx χ x‖ ^ 2 := by
      rw [Finset.sum_map]; rfl
    rw [e, ← sum_norm_sq_eq S fun χ => Sx χ x]
    exact Finset.sum_le_univ_sum_of_nonneg fun b => by positivity
  calc (B.card : ℝ) * x ^ 2 = ∑ a ∈ B, x ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ B, (48 * x * (q.totient * SAP q a x) +
          2304 * ‖∑ χ ∈ S, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * Sx χ x‖ ^ 2) := Finset.sum_le_sum hpt
    _ = 48 * x * q.totient * ∑ a ∈ B, SAP q a x +
          2304 * ∑ a ∈ B, ‖∑ χ ∈ S, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * Sx χ x‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun a _ => by ring
    _ ≤ 48 * x * q.totient * (2 * √Y * Real.log Y + 96 * x ^ 3 * Real.exp (-(Y / (2 * x)))) +
          2304 * (q.totient * ∑ χ ∈ S, ‖Sx χ x‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hZ (by positivity)) (mul_le_mul_of_nonneg_left hE2 (by norm_num))
    _ = _ := by ring

end

/-! ### The characters other than the trivial one, in mean square -/

/-- `s ≤ a(u + 2wE)` with `s ≥ 0` and `0 ≤ E ≤ 1` gives `s² ≤ 4a²(u² + 2w²E)`. -/
lemma sq_le_of_le {s a u w E : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ a * (u + 2 * w * E)) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    s ^ 2 ≤ 4 * a ^ 2 * (u ^ 2 + 2 * w ^ 2 * E) := by
  have h1 : s ^ 2 ≤ (a * (u + 2 * w * E)) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have h2 : (u + 2 * w * E) ^ 2 ≤ 4 * (u ^ 2 + 2 * w ^ 2 * E) := by
    nlinarith [sq_nonneg (u - 2 * w * E), mul_nonneg (sq_nonneg w) (mul_nonneg hE0 (sub_nonneg.2 hE1))]
  calc s ^ 2 ≤ (a * (u + 2 * w * E)) ^ 2 := h1
    _ = a ^ 2 * (u + 2 * w * E) ^ 2 := by ring
    _ ≤ a ^ 2 * (4 * (u ^ 2 + 2 * w ^ 2 * E)) := by gcongr
    _ = 4 * a ^ 2 * (u ^ 2 + 2 * w ^ 2 * E) := by ring

/-- **The characters other than the trivial one, in mean square.** Under `CharDensity A B C`, for `0 < δ ≤ 1/24`,
`T ≥ 1` and `x ≥ 1`, with `M = M*(δ)` and `ℓ = log(q + 2)`, `Σ_{χ ≠ 1}|S_χ(x)|²` is at most `4Mℓ` times the bound of
`Linnik.error_le` at `x²`: a character of level `j` has `|S_χ(x)| ≤ Mℓ(x^{θ_j+δ} + 2x^{11/12+δ}e^{−T/2})`
(`Linnik.norm_Sx_le`), so `|S_χ(x)|² ≤ 4M²ℓ²((x²)^{θ_j+δ} + 2(x²)^{11/12+δ}e^{−T/2})`; then `Linnik.sum_level_le`. -/
theorem error_sq_le {A B C : ℝ} (hD : CharDensity A B C) (q : ℕ) [NeZero q] {δ T x : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 24) (hT : 1 ≤ T) (hx : 1 ≤ x) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2 ≤
      4 * (Mstar δ * Real.log (q + 2)) * (Mstar δ * Real.log (q + 2) * ((q : ℝ) * (x ^ 2) ^ (1 / 2 + δ) +
        ∑ j ∈ Finset.range (nlev δ), C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) *
          Real.log ((q : ℝ) * (T + 1)) ^ B * (x ^ 2) ^ (lev δ (j + 1) + δ) +
        2 * q * (x ^ 2) ^ (11 / 12 + δ) * Real.exp (-T / 2))) := by
  set S := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)
  set M := Mstar δ
  set ℓ := Real.log (q + 2)
  set E := Real.exp (-T / 2)
  have hM0 : 0 < M := Mstar_pos hδ hδ1
  have hℓ0 : 0 ≤ ℓ := by have := one_le_log_add_two q; linarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hx0 : 0 < x := by linarith
  have hsq : ∀ r : ℝ, (x ^ r) ^ 2 = (x ^ 2) ^ r := fun r => by
    rw [← Real.rpow_natCast (x ^ r), ← Real.rpow_mul hx0.le, ← Real.rpow_natCast x 2, ← Real.rpow_mul hx0.le,
      mul_comm]
  -- each character, at its level
  have hchar : ∀ χ ∈ S, ‖Sx χ x‖ ^ 2 ≤
      4 * (M * ℓ) ^ 2 * ((x ^ 2) ^ (lev δ (level χ T hδ) + δ) + 2 * (x ^ 2) ^ (11 / 12 + δ) * E) := by
    intro χ hχS
    have hχ : χ ≠ 1 := (Finset.mem_filter.1 hχS).2
    have h1 := norm_Sx_le hχ (half_le_lev hδ.le _) (lev_le δ _) hδ hδ1 (by linarith) hx (level_spec hχ T hδ)
    have h2 := Mc_le_Mstar hδ hδ1 (level_le χ T hδ)
    have hb : 0 ≤ x ^ (lev δ (level χ T hδ) + δ) + 2 * x ^ (11 / 12 + δ) * E := by positivity
    have h3 : ‖Sx χ x‖ ≤ M * ℓ * (x ^ (lev δ (level χ T hδ) + δ) + 2 * x ^ (11 / 12 + δ) * E) :=
      h1.trans (by gcongr)
    have h4 := sq_le_of_le (norm_nonneg _) h3 hE0 hE1
    rwa [hsq, hsq] at h4
  -- the characters of each level
  calc ∑ χ ∈ S, ‖Sx χ x‖ ^ 2 ≤ 4 * (M * ℓ) ^ 2 *
        ∑ χ ∈ S, ((x ^ 2) ^ (lev δ (level χ T hδ) + δ) + 2 * (x ^ 2) ^ (11 / 12 + δ) * E) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hchar
    _ ≤ 4 * (M * ℓ) ^ 2 * (q * ((x ^ 2) ^ (lev δ 0 + δ) + 2 * (x ^ 2) ^ (11 / 12 + δ) * E) +
          ∑ j ∈ Finset.range (nlev δ), C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) *
            Real.log ((q : ℝ) * (T + 1)) ^ B * (x ^ 2) ^ (lev δ (j + 1) + δ)) :=
        mul_le_mul_of_nonneg_left (sum_level_le hD q hδ hT (b := fun j => (x ^ 2) ^ (lev δ j + δ))
          (fun j => by positivity) (by positivity)) (by positivity)
    _ = _ := by rw [lev_zero]; ring

/-! ### The sizes -/

/-- **The parts of `Linnik.total_le`.** For `x ≥ 3` and `q^{A+η₀} ≤ x`, with `T = 2 log x + 2` and `Y = 10x log x`,
the bound of `Linnik.error_le` and `q(2√Y log Y + 96x³e^{−Y/(2x)})` are each at most `Ktot x^{1−c₀}`: they are two of
the three terms of `total_le`, all `≥ 0`. -/
lemma total_parts {A B C η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    (q : ℕ) [NeZero q] {x : ℝ} (hx : 3 ≤ x) (hqx : (q : ℝ) ^ (A + η₀) ≤ x) :
    Mstar (dL A η₀) * Real.log (q + 2) * ((q : ℝ) * x ^ (1 / 2 + dL A η₀) +
        ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
          (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
            x ^ (lev (dL A η₀) (j + 1) + dL A η₀) +
        2 * q * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2)) ≤
      Ktot A B C η₀ * x ^ (1 - c0 A η₀) ∧
    q * (2 * √(10 * x * Real.log x) * Real.log (10 * x * Real.log x) +
        96 * x ^ 3 * Real.exp (-(10 * x * Real.log x / (2 * x)))) ≤ Ktot A B C η₀ * x ^ (1 - c0 A η₀) := by
  have h := total_le hA hB hC hη0 hη1 q hx hqx
  have hx0 : 0 < x := by linarith
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hL0 : 0 ≤ Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) := Real.log_nonneg (by nlinarith)
  have hsum : 0 ≤ ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
      (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
        x ^ (lev (dL A η₀) (j + 1) + dL A η₀) := Finset.sum_nonneg fun j _ => by
    have := Real.rpow_nonneg hL0 B
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ q * (2 * Real.log x + 2 + 1) by positivity) (A * (1 - lev (dL A η₀) j))
    positivity
  have hM := (Mstar_pos (dL_pos hA hη0) (dL_le hA hη1)).le
  have hl2 : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith)
  have hY : 0 ≤ Real.log (10 * x * Real.log x) := Real.log_nonneg (by nlinarith)
  have h1 : 0 ≤ Real.exp (-1) * (q * Real.log x) := by positivity
  have h2 : 0 ≤ Mstar (dL A η₀) * Real.log (q + 2) * ((q : ℝ) * x ^ (1 / 2 + dL A η₀) +
      ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^
        (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log x + 2 + 1)) ^ B *
          x ^ (lev (dL A η₀) (j + 1) + dL A η₀) +
      2 * q * x ^ (11 / 12 + dL A η₀) * Real.exp (-(2 * Real.log x + 2) / 2)) := by positivity
  have h3 : 0 ≤ (q : ℝ) * (2 * √(10 * x * Real.log x) * Real.log (10 * x * Real.log x) +
      96 * x ^ 3 * Real.exp (-(10 * x * Real.log x / (2 * x)))) := by positivity
  constructor <;> linarith

open scoped Classical in
/-- **The count at one `x`, from a density estimate.** Let `A ≥ 2`, `B ≥ 0`, `C ≥ 0` with `CharDensity A B C`, and
`0 < η₀ ≤ 1/2`. There is `K` such that for every `q ≥ 1` and every `x ≥ 100` with `q^{A+η₀} ≤ x²` and
`q log x ≤ x/8`, at most `Kφ(q)x^{−c₀}` units `a` mod `q`, `c₀ = η₀/(48(A + 1))`, hold no prime `p ≤ 10x log x`:
`card_bad_le`, with `Σ_{χ ≠ 1}|S_χ(x)|² ≤ 4M*ℓ·Ktot x^{2−2c₀}` (`error_sq_le`, and `total_parts` at `x²`),
`ℓ = log(q + 2) ≤ 6x^{c₀}/c₀`, and `2√Y log Y + 96x³e^{−Y/(2x)} ≤ Ktot x^{1−c₀}` (`total_parts` at `q = 1`). -/
theorem card_bad_density {A B C η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] {x : ℝ}, 100 ≤ x → (q : ℝ) ^ (A + η₀) ≤ x ^ 2 → q * Real.log x ≤ x / 8 →
      ((Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 10 * x * Real.log x → (p : ZMod q) ≠ a).card : ℝ) ≤
          K * q.totient * x ^ (-c0 A η₀) := by
  set c := c0 A η₀ with hc
  set M := Mstar (dL A η₀)
  set Kt := Ktot A B C η₀
  have hc0 : 0 < c := c0_pos hA hη0
  have hc1 : c ≤ 1 := by rw [hc]; unfold c0; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hM0 : 0 < M := Mstar_pos (dL_pos hA hη0) (dL_le hA hη1)
  have hKt0 : 0 ≤ Kt := Ktot_nonneg hA hB hC hη0 hη1
  refine ⟨Kt * (48 + 55296 * M / c), fun q _ x hx hqx hql => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hY1 : 1 ≤ 10 * x * Real.log x := by nlinarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqx' : (q : ℝ) ≤ x := by
    have h1 : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ (A + η₀) := by
      rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    nlinarith
  have hcount := card_bad_le q hx hql hY1
  set Z := 2 * √(10 * x * Real.log x) * Real.log (10 * x * Real.log x) +
    96 * x ^ 3 * Real.exp (-(10 * x * Real.log x / (2 * x)))
  set E₂ := ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2
  -- the prime powers: `total_parts` at `q = 1`
  have hZle : Z ≤ Kt * x ^ (1 - c) := by
    have h := (total_parts hA hB hC hη0 hη1 1 (x := x) (by linarith) (by simp; linarith)).2
    rwa [Nat.cast_one, one_mul] at h
  -- the other characters: `error_sq_le`, and `total_parts` at `x²`
  have hE₂le : E₂ ≤ 4 * (M * Real.log (q + 2)) * (Kt * (x ^ 2) ^ (1 - c)) := by
    have h1 := error_sq_le hD q (dL_pos hA hη0) (dL_le hA hη1) (T := 2 * Real.log (x ^ 2) + 2)
      (by nlinarith [Real.log_nonneg (one_le_pow₀ hx1 : (1 : ℝ) ≤ x ^ 2)]) hx1
    have h2 := (total_parts hA hB hC hη0 hη1 q (x := x ^ 2) (by nlinarith) hqx).1
    have hMl : 0 ≤ 4 * (M * Real.log (q + 2)) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ q + 2); positivity
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hMl)
  have hℓ : Real.log (q + 2) ≤ 6 * (x ^ c / c) :=
    (Real.log_le_log (by positivity) (by linarith)).trans (log_le_P hx1 hc0 hc1).2.1
  have h2c : x ^ (2 - c) = x ^ 2 * x ^ (-c) := by
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_two]
  have h1c : x * x ^ (1 - c) = x ^ (2 - c) := by
    rw [show (2 : ℝ) - c = 1 + (1 - c) by ring, Real.rpow_add hx0, Real.rpow_one]
  have h22 : x ^ c * (x ^ 2) ^ (1 - c) = x ^ (2 - c) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; ring_nf
  have hE₂' : E₂ ≤ 24 * M / c * Kt * x ^ (2 - c) := by
    calc E₂ ≤ 4 * (M * Real.log (q + 2)) * (Kt * (x ^ 2) ^ (1 - c)) := hE₂le
      _ ≤ 4 * (M * (6 * (x ^ c / c))) * (Kt * (x ^ 2) ^ (1 - c)) := by gcongr
      _ = 24 * M / c * Kt * (x ^ c * (x ^ 2) ^ (1 - c)) := by ring
      _ = _ := by rw [h22]
  have hfin : ((Finset.univ.filter fun a : (ZMod q)ˣ =>
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 10 * x * Real.log x → (p : ZMod q) ≠ a).card : ℝ) * x ^ 2 ≤
      Kt * (48 + 55296 * M / c) * q.totient * x ^ (-c) * x ^ 2 := by
    calc _ ≤ q.totient * (48 * x * Z + 2304 * E₂) := hcount
      _ ≤ q.totient * (48 * x * (Kt * x ^ (1 - c)) + 2304 * (24 * M / c * Kt * x ^ (2 - c))) := by gcongr
      _ = q.totient * (48 * Kt * (x * x ^ (1 - c)) + 55296 * M / c * Kt * x ^ (2 - c)) := by ring
      _ = _ := by rw [h1c, h2c]; ring
  exact le_of_mul_le_mul_right hfin (by positivity)

/-! ### Primes in almost all classes -/

/-- **The point `x = X₀q^L`.** For `L ≥ 1 + κ` with `κ > 0`, and `ε > 0`, there are `X₀` and `K ≥ 0` such that for every
`q ≥ 1`, `x = X₀q^L` has `x ≥ 100`, `q^L ≤ x`, `q log x ≤ x/8` and `10x log x ≤ Kq^{L+ε}`: `log x = log X₀ + L log q`,
with `log q ≤ q^κ/κ` and `log q ≤ q^ε/ε` (Mathlib's `Real.log_le_rpow_div`), and `X₀ = max(1024, 16L/κ)`. -/
lemma exists_X₀ {L κ ε : ℝ} (hκ : 0 < κ) (hL : 1 + κ ≤ L) (hε : 0 < ε) :
    ∃ X₀ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q], 100 ≤ X₀ * (q : ℝ) ^ L ∧ (q : ℝ) ^ L ≤ X₀ * (q : ℝ) ^ L ∧
      q * Real.log (X₀ * (q : ℝ) ^ L) ≤ X₀ * (q : ℝ) ^ L / 8 ∧
        10 * (X₀ * (q : ℝ) ^ L) * Real.log (X₀ * (q : ℝ) ^ L) ≤ K * (q : ℝ) ^ (L + ε) := by
  set X₀ : ℝ := max 1024 (16 * L / κ)
  have hX₀1 : 1024 ≤ X₀ := le_max_left _ _
  have hX₀2 : L / κ ≤ X₀ / 16 := by
    have : L / κ = 16 * L / κ / 16 := by ring
    rw [this]; linarith [le_max_right 1024 (16 * L / κ)]
  have hX₀0 : 0 < X₀ := by linarith
  have hlX : 0 ≤ Real.log X₀ := Real.log_nonneg (by linarith)
  have hlX16 : Real.log X₀ ≤ X₀ / 16 := by
    rw [Real.log_le_iff_le_exp hX₀0]
    have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ X₀ / 16)
    nlinarith [mul_nonneg hX₀0.le (by linarith : (0 : ℝ) ≤ X₀ - 1024)]
  have hL0 : 0 ≤ L := by linarith
  have hLε : 0 ≤ L / ε := div_nonneg hL0 hε.le
  refine ⟨X₀, 10 * X₀ * (Real.log X₀ + L / ε), by positivity, fun q _ => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hqL1 : 1 ≤ (q : ℝ) ^ L := Real.one_le_rpow hq1 hL0
  have hlx : Real.log (X₀ * (q : ℝ) ^ L) = Real.log X₀ + L * Real.log q := by
    rw [Real.log_mul hX₀0.ne' (by positivity), Real.log_rpow hq0]
  refine ⟨by nlinarith, le_mul_of_one_le_left (by positivity) (by linarith), ?_, ?_⟩
  · -- `q log x ≤ x/8`, from `q·q^κ ≤ q^L`
    have h2 : (q : ℝ) * (q : ℝ) ^ κ ≤ (q : ℝ) ^ L := by
      calc (q : ℝ) * (q : ℝ) ^ κ = (q : ℝ) ^ (1 + κ) := by rw [Real.rpow_add hq0, Real.rpow_one]
        _ ≤ (q : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le hq1 hL
    have hqL : (q : ℝ) ≤ (q : ℝ) ^ L := by nlinarith [Real.one_le_rpow hq1 hκ.le]
    have h3 : (q : ℝ) * Real.log q ≤ 1 / κ * (q : ℝ) ^ L := by
      calc (q : ℝ) * Real.log q ≤ (q : ℝ) * ((q : ℝ) ^ κ / κ) := by
            gcongr; exact Real.log_le_rpow_div hq0.le hκ
        _ = 1 / κ * ((q : ℝ) * (q : ℝ) ^ κ) := by ring
        _ ≤ 1 / κ * (q : ℝ) ^ L := by gcongr
    rw [hlx]
    calc (q : ℝ) * (Real.log X₀ + L * Real.log q) = Real.log X₀ * q + L * (q * Real.log q) := by ring
      _ ≤ Real.log X₀ * (q : ℝ) ^ L + L * (1 / κ * (q : ℝ) ^ L) := by gcongr
      _ = (Real.log X₀ + L / κ) * (q : ℝ) ^ L := by ring
      _ ≤ (X₀ / 16 + X₀ / 16) * (q : ℝ) ^ L := by gcongr
      _ = X₀ * (q : ℝ) ^ L / 8 := by ring
  · -- `10x log x ≤ Kq^{L+ε}`, from `log x ≤ (log X₀ + L/ε)q^ε`
    have hqe1 : 1 ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq1 hε.le
    have hlx2 : Real.log (X₀ * (q : ℝ) ^ L) ≤ (Real.log X₀ + L / ε) * (q : ℝ) ^ ε := by
      rw [hlx]
      have h1 : L * Real.log q ≤ L * ((q : ℝ) ^ ε / ε) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hq0.le hε) hL0
      have h2 : Real.log X₀ ≤ Real.log X₀ * (q : ℝ) ^ ε := le_mul_of_one_le_right hlX hqe1
      have h3 : (Real.log X₀ + L / ε) * (q : ℝ) ^ ε = Real.log X₀ * (q : ℝ) ^ ε + L * ((q : ℝ) ^ ε / ε) := by
        ring
      linarith
    calc 10 * (X₀ * (q : ℝ) ^ L) * Real.log (X₀ * (q : ℝ) ^ L)
        ≤ 10 * (X₀ * (q : ℝ) ^ L) * ((Real.log X₀ + L / ε) * (q : ℝ) ^ ε) := by gcongr
      _ = 10 * X₀ * (Real.log X₀ + L / ε) * ((q : ℝ) ^ L * (q : ℝ) ^ ε) := by ring
      _ = 10 * X₀ * (Real.log X₀ + L / ε) * (q : ℝ) ^ (L + ε) := by rw [Real.rpow_add hq0]

open scoped Classical in
/-- **Primes in almost all reduced classes, from a density estimate.** Let `A ≥ 2`, `B ≥ 0` and `C ≥ 0` with
`CharDensity A B C`. For every `η > 0` there are `K` and `c > 0` such that for every modulus `q ≥ 1`, at most
`Kφ(q)q^{−c}` of the units `a` mod `q` have no prime `p ≡ a (mod q)` with `p ≤ Kq^{A/2+η}`: `card_bad_density` at
`x = X₀q^{(A+η₀)/2}`, `η₀ = min(η, 1)/2` (`exists_X₀`). For every class the same estimate gives `A + η`
(`Linnik.linnik_of_charDensity`). The zero-free half-plane is used through `error_sq_le`, as in `Linnik.error_le`. -/
theorem almostAll_of_charDensity {A B C : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q],
      ((Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ K * (q : ℝ) ^ (A / 2 + η) → (p : ZMod q) ≠ a).card : ℝ) ≤
          K * q.totient * (q : ℝ) ^ (-c) := by
  set η₀ := min η 1 / 2 with hη₀
  have hmin : 0 < min η 1 := lt_min hη one_pos
  have hη0 : 0 < η₀ := by rw [hη₀]; positivity
  have hη1 : η₀ ≤ 1 / 2 := by have := min_le_right η 1; rw [hη₀]; linarith
  have hη2 : 3 / 2 * η₀ ≤ η := by have := min_le_left η 1; rw [hη₀]; linarith
  obtain ⟨K₁, hK₁⟩ := card_bad_density hA hB hC hD hη0 hη1
  obtain ⟨X₀, K₂, hK₂, hX⟩ :=
    exists_X₀ (L := (A + η₀) / 2) (κ := η₀ / 2) (ε := η₀) (by positivity) (by linarith) hη0
  refine ⟨max K₁ K₂, c0 A η₀, c0_pos hA hη0, fun q _ => ?_⟩
  obtain ⟨hx100, hqLx, hql, hY⟩ := hX q
  set x := X₀ * (q : ℝ) ^ ((A + η₀) / 2)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hx0 : 0 < x := by linarith
  have hqx' : (q : ℝ) ≤ x :=
    le_trans (by simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : (1 : ℝ) ≤ (A + η₀) / 2)) hqLx
  have hqx : (q : ℝ) ^ (A + η₀) ≤ x ^ 2 := by
    have e : (q : ℝ) ^ (A + η₀) = ((q : ℝ) ^ ((A + η₀) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; push_cast; ring_nf
    rw [e]; exact pow_le_pow_left₀ (by positivity) hqLx 2
  -- the classes with no prime up to `K q^{A/2+η}` have none up to `10x log x`
  have hsub : (Finset.univ.filter fun a : (ZMod q)ˣ =>
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ max K₁ K₂ * (q : ℝ) ^ (A / 2 + η) → (p : ZMod q) ≠ a) ⊆
      Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 10 * x * Real.log x → (p : ZMod q) ≠ a := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨ha.1, fun p hp hpY => ha.2 p hp (hpY.trans (hY.trans ?_))⟩
    exact mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) (by positivity)
      (hK₂.trans (le_max_right _ _))
  have hφ : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hxc : x ^ (-c0 A η₀) ≤ (q : ℝ) ^ (-c0 A η₀) :=
    Real.rpow_le_rpow_of_nonpos hq0 hqx' (by linarith [c0_pos hA hη0])
  calc _ ≤ ((Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 10 * x * Real.log x → (p : ZMod q) ≠ a).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ K₁ * q.totient * x ^ (-c0 A η₀) := hK₁ q hx100 hqx hql
    _ ≤ max K₁ K₂ * q.totient * x ^ (-c0 A η₀) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hφ) (Real.rpow_nonneg hx0.le _)
    _ ≤ max K₁ K₂ * q.totient * (q : ℝ) ^ (-c0 A η₀) :=
        mul_le_mul_of_nonneg_left hxc (mul_nonneg (hK₂.trans (le_max_right _ _)) hφ)

open scoped Classical in
/-- **Primes in almost all classes under GRH, below `q^{1+η}`.** If every Dirichlet `L`-function satisfies GRH
(`PsiOmega.GRH χ` for every `χ` mod every `q ≥ 1`), then for every `η > 0` there are `K` and `c > 0` such that for
every `q ≥ 1` all the reduced classes mod `q` but at most `Kφ(q)q^{−c}` hold a prime `p ≤ Kq^{1+η}`:
`almostAll_of_charDensity` at `LinnikGRH.charDensity_two_of_GRH`. For every class GRH gives `2 + η`
(`LinnikGRH.linnik_two_of_GRH`). -/
theorem almostAll_one_of_GRH (h : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), PsiOmega.GRH χ) {η : ℝ}
    (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q],
      ((Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ K * (q : ℝ) ^ (1 + η) → (p : ZMod q) ≠ a).card : ℝ) ≤
          K * q.totient * (q : ℝ) ^ (-c) := by
  have := almostAll_of_charDensity (le_refl _) (le_refl _) zero_le_one (LinnikGRH.charDensity_two_of_GRH h) hη
  rwa [show (2 : ℝ) / 2 = 1 by norm_num] at this

open scoped Classical in
/-- **Primes in almost all classes below `q^{1+η}`, from GRH as L. Alpöge's Lean archive proves it**: all the reduced
classes mod `q` but at most `Kφ(q)q^{−c}` hold a prime `p ≤ Kq^{1+η}`. `almostAll_one_of_GRH` with its hypothesis in
the archive's words (`LinnikGRH.DirichletRH`). -/
theorem almostAll_one (h : LinnikGRH.DirichletRH) {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q],
      ((Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ K * (q : ℝ) ^ (1 + η) → (p : ZMod q) ≠ a).card : ℝ) ≤
          K * q.totient * (q : ℝ) ^ (-c) :=
  almostAll_one_of_GRH (fun q _ χ s hz h0 h1 => h q χ s h0 h1 hz) hη

open scoped Classical in
/-- **CONDITIONAL. Primes in almost all classes below `q^{11667/10000+η}`, from the curve `g7d`** (conditional on the
half-plane `Re s > 11/12` and on Chen, Gupta and Li's Proposition 3.1, the library's two unreviewed inputs; no
hypothesis in Lean): for every `η > 0` there are `K` and `c > 0` such that for every `q ≥ 1` all the reduced classes
mod `q` but at most `Kφ(q)q^{−c}` hold a prime `p ≤ Kq^{11667/10000+η}`. `almostAll_of_charDensity` at
`LinnikG7.charDensity_g7d`, `A = 11667/5000`; for every class the same estimate gives `11667/5000 + η`
(`LinnikG7.linnik_g7d`). -/
theorem almostAll_g7d {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q],
      ((Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ K * (q : ℝ) ^ (11667 / 10000 + η) → (p : ZMod q) ≠ a).card : ℝ) ≤
          K * q.totient * (q : ℝ) ^ (-c) := by
  obtain ⟨C, hC0, hD⟩ := LinnikG7.charDensity_g7d
  have := almostAll_of_charDensity (by norm_num) (by norm_num) hC0 hD hη
  rwa [show (11667 / 5000 : ℝ) / 2 = 11667 / 10000 by norm_num] at this

/-! ### Under GRH: a bound of Turán's type for the exceptions -/

/-- **The characters other than the trivial one under GRH**, with no levels: under GRH (`LinnikGRH.DirichletRH`),
for `0 < δ ≤ 1/24` and `x ≥ 1`, `Σ_{χ ≠ 1}|S_χ(x)|² ≤ q(3Mℓx^{1/2+δ})²` with
`M = Mc(1/2, 1/2 + δ) + Mc(11/12, 11/12 + δ)` and `ℓ = log(q + 2)`. No `L(·, χ)`, `χ ≠ 1`, vanishes on `Re s > 1/2`,
so `Linnik.norm_Sx_le` at `θ = 1/2` and `T = 2 log x + 2` bounds every character alike, the line's tail
`x^{11/12+δ}e^{−T/2} ≤ x^{−1/12+δ}` included. -/
theorem error_sq_le_of_RH (h : LinnikGRH.DirichletRH) (q : ℕ) [NeZero q] {δ x : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 24) (hx : 1 ≤ x) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2 ≤
      q * (3 * ((Mc (1 / 2) (1 / 2 + δ) + Mc (11 / 12) (11 / 12 + δ)) * Real.log (q + 2)) * x ^ (1 / 2 + δ)) ^ 2 := by
  classical
  have hx0 : 0 < x := by linarith
  have hMℓ : 0 ≤ (Mc (1 / 2) (1 / 2 + δ) + Mc (11 / 12) (11 / 12 + δ)) * Real.log (q + 2) :=
    mul_nonneg (add_pos (Mc_pos (by linarith) (by linarith)) (Mc_pos (by linarith) (by linarith))).le
      (by have := one_le_log_add_two q; linarith)
  have htail : x ^ (11 / 12 + δ) * Real.exp (-(2 * Real.log x + 2) / 2) ≤ x ^ (1 / 2 + δ) := by
    calc x ^ (11 / 12 + δ) * Real.exp (-(2 * Real.log x + 2) / 2) ≤ x ^ (11 / 12 + δ) * x⁻¹ :=
          mul_le_mul_of_nonneg_left (exp_T_le hx0) (by positivity)
      _ = x ^ (11 / 12 + δ - 1) := by rw [Real.rpow_sub_one hx0.ne']; ring
      _ ≤ x ^ (1 / 2 + δ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hb : ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2 ≤
      (3 * ((Mc (1 / 2) (1 / 2 + δ) + Mc (11 / 12) (11 / 12 + δ)) * Real.log (q + 2)) * x ^ (1 / 2 + δ)) ^ 2 := by
    intro χ hχS
    have hχ : χ ≠ 1 := (Finset.mem_filter.1 hχS).2
    have hloc : ∀ s : ℂ, 1 / 2 < s.re → |s.im| < 2 * Real.log x + 2 + 1 → LFunction χ s ≠ 0 :=
      fun s hs _ hz => by
        rcases lt_or_ge s.re 1 with h1 | h1
        · linarith [h q χ s (by linarith) h1 hz]
        · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h1 hz
    have h1 := norm_Sx_le hχ le_rfl (by norm_num) hδ hδ1 (by linarith [Real.log_nonneg hx]) hx hloc
    refine pow_le_pow_left₀ (norm_nonneg _) (h1.trans ?_) 2
    nlinarith [mul_le_mul_of_nonneg_left htail hMℓ]
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (LinnikDensity.card_chars_le _) (sq_nonneg _)

/-- **The prime powers, to `√x`.** For `x ≥ 3`, `0 < ε ≤ 1` and `Y = 10x log x`,
`2√Y log Y + 96x³e^{−Y/(2x)} ≤ (72√10/ε² + 96)x^{1/2+2ε}`: `log Y ≤ 2 log x + 3` and `√Y = √(10x log x)`
(`Linnik.size_Y`), `e^{−Y/(2x)} = x^{−5}` (`Linnik.exp_Y_eq`), and `2 log x + 3 ≤ 6x^ε/ε` (`Linnik.log_le_P`). -/
lemma Z_le_sqrt {x ε : ℝ} (hx : 3 ≤ x) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 * √(10 * x * Real.log x) * Real.log (10 * x * Real.log x) +
        96 * x ^ 3 * Real.exp (-(10 * x * Real.log x / (2 * x))) ≤
      (72 * √10 / ε ^ 2 + 96) * x ^ (1 / 2 + 2 * ε) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  obtain ⟨hlY, hsqY⟩ := size_Y hx
  obtain ⟨hP1, -, hP3, -⟩ := log_le_P hx1 hε hε1
  have hsl : √(Real.log x) ≤ 6 * (x ^ ε / ε) := by
    have : √(Real.log x) ≤ Real.log x := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
    linarith
  have hlY0 : 0 ≤ Real.log (10 * x * Real.log x) := Real.log_nonneg (by nlinarith)
  have h1 : 2 * √(10 * x * Real.log x) * Real.log (10 * x * Real.log x) ≤
      2 * √10 * √x * (6 * (x ^ ε / ε)) ^ 2 := by
    rw [hsqY]
    calc 2 * (√10 * √x * √(Real.log x)) * Real.log (10 * x * Real.log x)
        ≤ 2 * (√10 * √x * (6 * (x ^ ε / ε))) * (6 * (x ^ ε / ε)) := by gcongr; linarith
      _ = 2 * √10 * √x * (6 * (x ^ ε / ε)) ^ 2 := by ring
  have h2 : 96 * x ^ 3 * Real.exp (-(10 * x * Real.log x / (2 * x))) ≤ 96 := by
    rw [exp_Y_eq hx0]
    have : x ^ 3 * (x ^ 5)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      exact pow_le_pow_right₀ hx1 (by norm_num)
    nlinarith
  have hP : √x * (6 * (x ^ ε / ε)) ^ 2 = 36 / ε ^ 2 * x ^ (1 / 2 + 2 * ε) := by
    rw [Real.sqrt_eq_rpow, show (1 / 2 + 2 * ε : ℝ) = 1 / 2 + ε + ε by ring, Real.rpow_add hx0,
      Real.rpow_add hx0]
    field_simp
    ring
  have hx12 : 1 ≤ x ^ (1 / 2 + 2 * ε) := Real.one_le_rpow hx1 (by positivity)
  calc _ ≤ 2 * √10 * √x * (6 * (x ^ ε / ε)) ^ 2 + 96 := add_le_add h1 h2
    _ = 72 * √10 / ε ^ 2 * x ^ (1 / 2 + 2 * ε) + 96 := by rw [mul_assoc (2 * √10), hP]; ring
    _ ≤ _ := by nlinarith

open scoped Classical in
/-- **All the classes but `Kq^{1−δ+η}` have a prime below `Kq^{1+δ}`, under GRH as L. Alpöge's Lean archive proves
it**, a bound of Turán's type. For `0 < δ ≤ 1` and `η > 0` there is `K` such that for every `q ≥ 1`, at most
`Kq^{1−δ+η}` of the reduced classes mod `q` hold no prime `p ≤ Kq^{1+δ}`; at `δ = 1 − κ`, all the classes but `Kq^{κ+η}`
hold a prime `p ≤ Kq^{2−κ}`. `card_bad_le` at
`x = X₀q^{1+δ−8ε}`, `ε = min(η, δ)/32` (`exists_X₀`), with `Σ_{χ ≠ 1}|S_χ(x)|² ≤ 9M²ℓ²qx^{1+2ε}`
(`error_sq_le_of_RH`) and the prime powers at most `x^{1/2+2ε}` (`Z_le_sqrt`), so that the classes with no prime
up to `10x log x` number `≪ q(x^{−1/2+2ε} + qℓ²x^{−1+2ε})`. -/
theorem almostAll_turan (h : LinnikGRH.DirichletRH) {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q],
      ((Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ K * (q : ℝ) ^ (1 + δ) → (p : ZMod q) ≠ a).card : ℝ) ≤
          K * (q : ℝ) ^ (1 - δ + η) := by
  set ε := min η δ / 32 with hεdef
  have hmin : 0 < min η δ := lt_min hη hδ
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hεη : 32 * ε ≤ η := by have := min_le_left η δ; rw [hεdef]; linarith
  have hεδ : 32 * ε ≤ δ := by have := min_le_right η δ; rw [hεdef]; linarith
  obtain ⟨X₀, K₁, hK₁, hX⟩ := exists_X₀ (L := 1 + δ - 8 * ε) (κ := δ / 2) (ε := 8 * ε) (by positivity)
    (by linarith) (by positivity)
  set Kz := 72 * √10 / ε ^ 2 + 96
  refine ⟨max K₁ (48 * Kz + 20736 * (Mc (1 / 2) (1 / 2 + ε) + Mc (11 / 12) (11 / 12 + ε)) ^ 2 * (6 / ε) ^ 2),
    fun q _ => ?_⟩
  obtain ⟨hx100, hqLx, hql, hY⟩ := hX q
  rw [show 1 + δ - 8 * ε + 8 * ε = 1 + δ by ring] at hY
  set x := X₀ * (q : ℝ) ^ (1 + δ - 8 * ε)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  -- the count at `x`
  have hcount := card_bad_le q hx100 hql (Y := 10 * x * Real.log x) (by nlinarith)
  have hZ := Z_le_sqrt (x := x) (by linarith) hε (by linarith)
  have hE := error_sq_le_of_RH h q (x := x) hε (by linarith) (by linarith)
  set M := Mc (1 / 2) (1 / 2 + ε) + Mc (11 / 12) (11 / 12 + ε)
  set ℓ := Real.log (q + 2)
  set K := max K₁ (48 * Kz + 20736 * M ^ 2 * (6 / ε) ^ 2)
  set Z := 2 * √(10 * x * Real.log x) * Real.log (10 * x * Real.log x) +
    96 * x ^ 3 * Real.exp (-(10 * x * Real.log x / (2 * x)))
  set E₂ := ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hℓ : ℓ ^ 2 ≤ (6 / ε) ^ 2 * (q : ℝ) ^ (2 * ε) := by
    calc ℓ ^ 2 ≤ (6 * ((q : ℝ) ^ ε / ε)) ^ 2 :=
          pow_le_pow_left₀ hℓ0 (log_le_P hq1 hε (by linarith)).2.1 2
      _ = (6 / ε) ^ 2 * (q : ℝ) ^ (2 * ε) := by
          rw [mul_comm 2 ε, Real.rpow_mul hq0.le, Real.rpow_two]; ring
  -- the exponents
  have hT1 : (q : ℝ) ^ (δ - η) ≤ x ^ (1 / 2 - 2 * ε) := by
    calc (q : ℝ) ^ (δ - η) ≤ (q : ℝ) ^ ((1 + δ - 8 * ε) * (1 / 2 - 2 * ε)) :=
          Real.rpow_le_rpow_of_exponent_le hq1
            (by nlinarith [mul_le_mul_of_nonneg_right hδ1 hε.le, sq_nonneg ε])
      _ = ((q : ℝ) ^ (1 + δ - 8 * ε)) ^ (1 / 2 - 2 * ε) := Real.rpow_mul hq0.le _ _
      _ ≤ x ^ (1 / 2 - 2 * ε) := Real.rpow_le_rpow (by positivity) hqLx (by linarith)
  have hT2 : (q : ℝ) ^ (1 + δ - η + 2 * ε) ≤ x ^ (1 - 2 * ε) := by
    calc (q : ℝ) ^ (1 + δ - η + 2 * ε) ≤ (q : ℝ) ^ ((1 + δ - 8 * ε) * (1 - 2 * ε)) :=
          Real.rpow_le_rpow_of_exponent_le hq1
            (by nlinarith [mul_le_mul_of_nonneg_right hδ1 hε.le, sq_nonneg ε])
      _ = ((q : ℝ) ^ (1 + δ - 8 * ε)) ^ (1 - 2 * ε) := Real.rpow_mul hq0.le _ _
      _ ≤ x ^ (1 - 2 * ε) := Real.rpow_le_rpow (by positivity) hqLx (by linarith)
  have t1 : (q : ℝ) * (x * x ^ (1 / 2 + 2 * ε)) ≤ (q : ℝ) ^ (1 - δ + η) * x ^ 2 := by
    have e1 : (q : ℝ) ^ (1 - δ + η) * (q : ℝ) ^ (δ - η) = q := by
      rw [← Real.rpow_add hq0, show 1 - δ + η + (δ - η) = (1 : ℝ) by ring, Real.rpow_one]
    have e2 : x * x ^ (1 / 2 + 2 * ε) = x ^ (3 / 2 + 2 * ε) := by
      rw [show (3 / 2 + 2 * ε : ℝ) = 1 + (1 / 2 + 2 * ε) by ring, Real.rpow_add hx0 1, Real.rpow_one]
    calc (q : ℝ) * (x * x ^ (1 / 2 + 2 * ε)) =
          (q : ℝ) ^ (1 - δ + η) * (q : ℝ) ^ (δ - η) * x ^ (3 / 2 + 2 * ε) := by rw [e1, e2]
      _ = (q : ℝ) ^ (1 - δ + η) * ((q : ℝ) ^ (δ - η) * x ^ (3 / 2 + 2 * ε)) := by ring
      _ ≤ (q : ℝ) ^ (1 - δ + η) * (x ^ (1 / 2 - 2 * ε) * x ^ (3 / 2 + 2 * ε)) := by gcongr
      _ = (q : ℝ) ^ (1 - δ + η) * x ^ 2 := by
          rw [← Real.rpow_add hx0, show 1 / 2 - 2 * ε + (3 / 2 + 2 * ε) = (2 : ℝ) by ring, Real.rpow_two]
  have t2 : (q : ℝ) ^ 2 * ℓ ^ 2 * (x ^ (1 / 2 + ε)) ^ 2 ≤ (6 / ε) ^ 2 * ((q : ℝ) ^ (1 - δ + η) * x ^ 2) := by
    have hx4 : (x ^ (1 / 2 + ε)) ^ 2 = x ^ (1 + 2 * ε) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hx0.le]; ring_nf
    have hq3 : (q : ℝ) ^ 2 * (q : ℝ) ^ (2 * ε) = (q : ℝ) ^ (1 - δ + η) * (q : ℝ) ^ (1 + δ - η + 2 * ε) := by
      rw [← Real.rpow_two, ← Real.rpow_add hq0, ← Real.rpow_add hq0]; ring_nf
    calc (q : ℝ) ^ 2 * ℓ ^ 2 * (x ^ (1 / 2 + ε)) ^ 2
        ≤ (q : ℝ) ^ 2 * ((6 / ε) ^ 2 * (q : ℝ) ^ (2 * ε)) * x ^ (1 + 2 * ε) := by rw [hx4]; gcongr
      _ = (6 / ε) ^ 2 * ((q : ℝ) ^ (1 - δ + η) * ((q : ℝ) ^ (1 + δ - η + 2 * ε) * x ^ (1 + 2 * ε))) := by
          rw [show (q : ℝ) ^ 2 * ((6 / ε) ^ 2 * (q : ℝ) ^ (2 * ε)) * x ^ (1 + 2 * ε) =
            (6 / ε) ^ 2 * ((q : ℝ) ^ 2 * (q : ℝ) ^ (2 * ε)) * x ^ (1 + 2 * ε) by ring, hq3]; ring
      _ ≤ (6 / ε) ^ 2 * ((q : ℝ) ^ (1 - δ + η) * (x ^ (1 - 2 * ε) * x ^ (1 + 2 * ε))) := by gcongr
      _ = (6 / ε) ^ 2 * ((q : ℝ) ^ (1 - δ + η) * x ^ 2) := by
          rw [← Real.rpow_add hx0, show 1 - 2 * ε + (1 + 2 * ε) = (2 : ℝ) by ring, Real.rpow_two]
  -- the classes with no prime up to `Kq^{1+δ}` have none up to `10x log x`
  have hsub : (Finset.univ.filter fun a : (ZMod q)ˣ =>
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ K * (q : ℝ) ^ (1 + δ) → (p : ZMod q) ≠ a) ⊆
      Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 10 * x * Real.log x → (p : ZMod q) ≠ a := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, fun p hp hpY => ha.2 p hp (hpY.trans (hY.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))))⟩
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hKz : 0 ≤ Kz := by positivity
  have hfin : ((Finset.univ.filter fun a : (ZMod q)ˣ =>
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 10 * x * Real.log x → (p : ZMod q) ≠ a).card : ℝ) * x ^ 2 ≤
      K * (q : ℝ) ^ (1 - δ + η) * x ^ 2 := by
    have hR : 0 ≤ 48 * x * (Kz * x ^ (1 / 2 + 2 * ε)) + 2304 * (q * (3 * (M * ℓ) * x ^ (1 / 2 + ε)) ^ 2) := by
      positivity
    calc _ ≤ q.totient * (48 * x * Z + 2304 * E₂) := hcount
      _ ≤ q * (48 * x * (Kz * x ^ (1 / 2 + 2 * ε)) + 2304 * (q * (3 * (M * ℓ) * x ^ (1 / 2 + ε)) ^ 2)) :=
          (mul_le_mul_of_nonneg_left (by gcongr) (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right hφ hR)
      _ = 48 * Kz * ((q : ℝ) * (x * x ^ (1 / 2 + 2 * ε))) +
            20736 * M ^ 2 * ((q : ℝ) ^ 2 * ℓ ^ 2 * (x ^ (1 / 2 + ε)) ^ 2) := by ring
      _ ≤ 48 * Kz * ((q : ℝ) ^ (1 - δ + η) * x ^ 2) +
            20736 * M ^ 2 * ((6 / ε) ^ 2 * ((q : ℝ) ^ (1 - δ + η) * x ^ 2)) := by gcongr
      _ = (48 * Kz + 20736 * M ^ 2 * (6 / ε) ^ 2) * (q : ℝ) ^ (1 - δ + η) * x ^ 2 := by ring
      _ ≤ K * (q : ℝ) ^ (1 - δ + η) * x ^ 2 := by gcongr; exact le_max_right _ _
  calc _ ≤ ((Finset.univ.filter fun a : (ZMod q)ˣ =>
        ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 10 * x * Real.log x → (p : ZMod q) ≠ a).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := le_of_mul_le_mul_right hfin (by positivity)

end LinnikAlmostAll

#print axioms LinnikAlmostAll.sum_norm_sq_eq
#print axioms LinnikAlmostAll.card_bad_le
#print axioms LinnikAlmostAll.error_sq_le
#print axioms LinnikAlmostAll.almostAll_of_charDensity
#print axioms LinnikAlmostAll.almostAll_one_of_GRH
#print axioms LinnikAlmostAll.almostAll_one
#print axioms LinnikAlmostAll.almostAll_g7d
#print axioms LinnikAlmostAll.almostAll_turan
