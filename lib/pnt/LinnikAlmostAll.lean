/-
# Primes in almost every residue class, and the entropy of the primes mod `q`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. Let `A ≥ 2`, `B ≥ 0` and `C ≥ 0`, and suppose that for every modulus `q ≥ 1`, `½ ≤ σ ≤ 1` and
`T ≥ 2` at most `C(qT)^{A(1−σ)}(log qT)^B` Dirichlet characters mod `q` have a zero of `L(·, χ)` in `Re s ≥ σ`,
`|Im s| ≤ T` (`Linnik.CharDensity A B C`). Then for every `η > 0` there are `K` and `c > 0` such that, for every
modulus `q ≥ 1`:

* all the reduced classes mod `q` but at most `Kφ(q)q^{−c}` hold a prime `p ≤ Kq^{A/2+η}`
  (`least_prime_of_charDensity`);
* for every `x ≥ Kq^{A/2+η}`, all the reduced classes but at most `Kφ(q)x^{−c}` hold at least `x/(240φ(q) log x)`
  primes `p ≤ 10x log x` (`few_of_charDensity`);
* for every `x ≥ Kq^{A/2+η}`, with `S(x; q, a) = Σ_{n ≡ a (q)} Λ(n)e^{−n/x}` (`Linnik.SAP`) and
  `S₀ = Σ_{(a, q) = 1} S(x; q, a)` (`S0`): `Σ_{(a, q) = 1} (φ(q)S(x; q, a) − S₀)² ≤ Kφ(q)x^{−c}S₀²`
  (`meanSq_of_charDensity`), and the entropy `H = −Σ_{(a, q) = 1} P(a) log P(a)` of `P(a) = S(x; q, a)/S₀`
  (`entropy`) is at least `log φ(q) − Kx^{−c}` (`entropy_of_charDensity`). Its greatest possible value is
  `log φ(q)`, that of the uniform distribution.

The exponent is half that of `Linnik.linnik_of_charDensity`, which puts a prime `p ≤ Kq^{A+η}` in every class. There
the deviation of each class from the mean is bounded by `Σ_{χ ≠ 1} |S_χ|`; here the mean square of the deviations
over the classes is `Σ_{χ ≠ 1} |S_χ|²/φ(q)` at most (`variance_le`), and under `CharDensity` the levels bound it by
the bound of the first sum at `x²` (`error_sq_le`, `sum_sq_le`). With the library's estimate
`LinnikG7.charDensity_g7d`, where `A = 11667/5000`, the statements hold with no hypothesis and the exponent
`11667/10000 + η` (`least_prime_g7d`, `few_g7d`, `meanSq_g7d`, `entropy_g7d`). The zero-free region the argument uses
is the half-plane `Eis.LFunction_ne_zero_of_re_gt`, through `Linnik.norm_Sx_le`.

In terms of information: the relative entropy of `P` to the uniform distribution `U` on the reduced classes,
`log φ(q) − H`, is at most the chi-square divergence `Σ_a (φ(q)P(a) − 1)²/φ(q)` (`entropy_ge`), which is the mean
square above. So the residue mod `q` of an integer drawn with probability proportional to `Λ(n)e^{−n/x}`, among
those prime to `q`, is within `Kx^{−c}` of uniform in relative entropy once `x ≥ Kq^{A/2+η}`. That every class has
positive probability is Linnik's theorem; it is a statement about the least value of `P`, which the mean square does
not bound, and the deduction from the same density estimate has it at twice the exponent.

* `error_sq_le`: `Σ_{χ ≠ 1} |S_χ(x)|²` by levels, as `Linnik.error_le` has `Σ_{χ ≠ 1} |S_χ(x)|`: each character is
  bounded by `norm_Sx_le` at its level and squared, with `(u + v)² ≤ 2u² + 2v²`.
* `sum_sq_le`: at `T = 2 log x² + 2` the bound is at most `2M log(q + 2)` times the bracket of `Linnik.total_le` at
  `x²`, so `Σ_{χ ≠ 1} |S_χ(x)|² ≤ 2M log(q + 2)·Ktot·(x²)^{1−c₀}` when `q^{A+η₀} ≤ x²`.
* `variance_le`: `Σ_{(a, q) = 1} (φ(q)S(x; q, a) − S₀)² ≤ φ(q) Σ_{χ ≠ 1} |S_χ|²`. By `Linnik.totient_mul_SAP` the
  deviation is `Σ_{χ ≠ 1} χ⁻¹(a)S_χ`, which vanishes off the units; its squares sum to `φ(q) Σ_{χ ≠ 1} S_χ S_{χ⁻¹}`
  by the orthogonality of the characters over the classes (`sum_char_apply`).
* `S0_eq`, `S0_ge`: `S₀ = S_1(x)`, the trivial character's sum, and `S₀ ≥ x/12` for `x ≥ 10⁷` and `q ≤ x`
  (`Linnik.re_Sx_one_ge`, `ψ(x) ≥ x/4` and `ω(q) ≤ 2 log q`).
* `SAP_le_cnt`, `sum_PP_le`: `S(x; q, a) ≤ π(Y; q, a) log Y + PP(Y; q, a) + 96x³e^{−Y/(2x)}`, where `PP` is the
  weight of the prime powers of the class up to `Y` that are not primes, and `Σ_a PP(Y; q, a) = ψ(Y) − θ(Y)`.
* `card_few_le`: a class with fewer than `x/(240φ(q) log x)` primes up to `Y = 10x log x` has
  `φ(q)S(x; q, a) ≤ S₀/2`, or prime powers of weight above `S₀/(8φ(q))`. The mean square counts the first kind,
  `sum_PP_le` the second.
* `entropy_ge`: `−p log p ≥ p log m − (mp² − p)` for `p ≥ 0`, from `log(mp) ≤ mp − 1`, summed over the classes with
  `m = φ(q)`.
-/
import LinnikG7

open Complex Set Real Filter Topology MeasureTheory ArithmeticFunction

noncomputable section

namespace LinnikAlmostAll

open Linnik DirichletCharacter InghamDensity

/-! ### The mean square over the characters, by levels -/

/-- **The mean square over the characters**: `Σ_{χ ≠ 1} |S_χ(x)|²` under `CharDensity`, by levels as in
`Linnik.error_le`. Each character is bounded by `norm_Sx_le` at its level, squared with `(u + v)² ≤ 2u² + 2v²`; the
bound is that of `error_le` at `x²`, with `2e^{−T}` for `e^{−T/2}`. -/
theorem error_sq_le {A B C : ℝ} (hD : CharDensity A B C)
    (q : ℕ) [NeZero q] {δ T x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 24) (hT : 1 ≤ T) (hx : 1 ≤ x) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2 ≤
      2 * (Mstar δ * Real.log (q + 2)) ^ 2 * ((q : ℝ) * (x ^ 2) ^ (1 / 2 + δ) +
        ∑ j ∈ Finset.range (nlev δ), C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) *
          Real.log ((q : ℝ) * (T + 1)) ^ B * (x ^ 2) ^ (lev δ (j + 1) + δ) +
        2 * q * (x ^ 2) ^ (11 / 12 + δ) * (2 * Real.exp (-T / 2) ^ 2)) := by
  classical
  set S := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) with hS
  set M := Mstar δ with hM
  set ℓ := Real.log (q + 2) with hℓ
  set E := Real.exp (-T / 2) with hE
  set y := x ^ 2 with hy
  have hM0 : 0 < M := Mstar_pos hδ hδ1
  have hℓ0 : 0 ≤ ℓ := by have := one_le_log_add_two q; linarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by positivity
  have hsq : ∀ θ : ℝ, (x ^ θ) ^ 2 = y ^ θ := by
    intro θ
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  -- each character at its level, squared
  have hchar : ∀ χ ∈ S, ‖Sx χ x‖ ^ 2 ≤
      2 * (M * ℓ) ^ 2 * (y ^ (lev δ (level χ T hδ) + δ) + 2 * y ^ (11 / 12 + δ) * (2 * E ^ 2)) := by
    intro χ hχS
    have hχ : χ ≠ 1 := (Finset.mem_filter.1 hχS).2
    have hle := level_le χ T hδ
    have h1 : ‖Sx χ x‖ ≤ M * ℓ * (x ^ (lev δ (level χ T hδ) + δ) + 2 * x ^ (11 / 12 + δ) * E) := by
      refine (norm_Sx_le hχ (half_le_lev hδ.le _) (lev_le δ _) hδ hδ1 (by linarith) hx
        (level_spec hχ T hδ)).trans ?_
      have hb : 0 ≤ x ^ (lev δ (level χ T hδ) + δ) + 2 * x ^ (11 / 12 + δ) * E := by positivity
      have := Mc_le_Mstar hδ hδ1 hle
      gcongr
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
    rw [← hsq, ← hsq]
    set u := x ^ (lev δ (level χ T hδ) + δ) with hu
    set v := x ^ (11 / 12 + δ) with hv
    have h2 : (u + 2 * v * E) ^ 2 ≤ 2 * (u ^ 2 + 2 * v ^ 2 * (2 * E ^ 2)) := by
      nlinarith [sq_nonneg (u - 2 * v * E)]
    calc (M * ℓ * (u + 2 * v * E)) ^ 2 = (M * ℓ) ^ 2 * (u + 2 * v * E) ^ 2 := by ring
      _ ≤ (M * ℓ) ^ 2 * (2 * (u ^ 2 + 2 * v ^ 2 * (2 * E ^ 2))) := by gcongr
      _ = 2 * (M * ℓ) ^ 2 * (u ^ 2 + 2 * v ^ 2 * (2 * E ^ 2)) := by ring
  -- the fibres
  set F : ℕ → Finset (DirichletCharacter ℂ q) := fun j => S.filter (fun χ => level χ T hδ = j) with hF
  have hmaps : ∀ χ ∈ S, level χ T hδ ∈ Finset.range (nlev δ + 1) :=
    fun χ _ => Finset.mem_range.2 (Nat.lt_succ_of_le (level_le χ T hδ))
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun χ => ‖Sx χ x‖ ^ 2)
  have hcardS : (S.card : ℝ) ≤ q := by
    have h1 : S.card ≤ Fintype.card (DirichletCharacter ℂ q) := Finset.card_le_univ S
    have h2 : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]; exact card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    exact_mod_cast h1.trans (h2 ▸ Nat.totient_le q)
  have hcardF : ∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) = S.card := by
    have := Finset.card_eq_sum_card_fiberwise hmaps
    exact_mod_cast this.symm
  -- the bound on each fibre
  have hfibre : ∀ j ∈ Finset.range (nlev δ + 1), ∑ χ ∈ F j, ‖Sx χ x‖ ^ 2 ≤
      ((F j).card : ℝ) * (2 * (M * ℓ) ^ 2 * (y ^ (lev δ j + δ) + 2 * y ^ (11 / 12 + δ) * (2 * E ^ 2))) := by
    intro j _
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun χ hχ => ?_
    have hχ' := Finset.mem_filter.1 hχ
    have := hchar χ hχ'.1
    rwa [hχ'.2] at this
  -- the count of each fibre of level `j + 1`
  have hcount : ∀ j ∈ Finset.range (nlev δ), ((F (j + 1)).card : ℝ) ≤
      C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) * Real.log ((q : ℝ) * (T + 1)) ^ B := by
    intro j _
    refine le_trans ?_ (hD q (lev δ j) (T + 1) (half_le_lev hδ.le j) (by linarith [lev_le δ j]) (by linarith))
    exact_mod_cast Finset.card_le_card fun χ hχ => by
      have hχ' := Finset.mem_filter.1 hχ
      have hnz := not_ZF_of_level T hδ hχ'.2
      simp only [ZF, not_forall, not_not, exists_prop] at hnz
      obtain ⟨s, hs1, hs2, hs3⟩ := hnz
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, s, hs1.le, hs2.le, hs3⟩
  have hF0 : ((F 0).card : ℝ) ≤ q := by
    refine le_trans ?_ hcardS
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  -- assemble
  have hsplit : ∑ j ∈ Finset.range (nlev δ + 1),
      ((F j).card : ℝ) * (2 * (M * ℓ) ^ 2 * (y ^ (lev δ j + δ) + 2 * y ^ (11 / 12 + δ) * (2 * E ^ 2))) =
      2 * (M * ℓ) ^ 2 * (∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) * y ^ (lev δ j + δ)) +
        2 * (M * ℓ) ^ 2 * (2 * y ^ (11 / 12 + δ) * (2 * E ^ 2)) *
          ∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hfirst : ∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) * y ^ (lev δ j + δ) ≤
      (q : ℝ) * y ^ (1 / 2 + δ) + ∑ j ∈ Finset.range (nlev δ), C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) *
          Real.log ((q : ℝ) * (T + 1)) ^ B * y ^ (lev δ (j + 1) + δ) := by
    rw [Finset.sum_range_succ', lev_zero, add_comm]
    gcongr with j hj
    exact hcount j hj
  calc ∑ χ ∈ S, ‖Sx χ x‖ ^ 2 = ∑ j ∈ Finset.range (nlev δ + 1), ∑ χ ∈ F j, ‖Sx χ x‖ ^ 2 := hfib.symm
    _ ≤ ∑ j ∈ Finset.range (nlev δ + 1),
          ((F j).card : ℝ) * (2 * (M * ℓ) ^ 2 * (y ^ (lev δ j + δ) + 2 * y ^ (11 / 12 + δ) * (2 * E ^ 2))) :=
        Finset.sum_le_sum hfibre
    _ = 2 * (M * ℓ) ^ 2 * (∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) * y ^ (lev δ j + δ)) +
        2 * (M * ℓ) ^ 2 * (2 * y ^ (11 / 12 + δ) * (2 * E ^ 2)) *
          ∑ j ∈ Finset.range (nlev δ + 1), ((F j).card : ℝ) := hsplit
    _ ≤ 2 * (M * ℓ) ^ 2 * ((q : ℝ) * y ^ (1 / 2 + δ) + ∑ j ∈ Finset.range (nlev δ),
          C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) * Real.log ((q : ℝ) * (T + 1)) ^ B *
            y ^ (lev δ (j + 1) + δ)) +
        2 * (M * ℓ) ^ 2 * (2 * y ^ (11 / 12 + δ) * (2 * E ^ 2)) * q := by
        rw [hcardF]
        have : 0 ≤ 2 * (M * ℓ) ^ 2 * (2 * y ^ (11 / 12 + δ) * (2 * E ^ 2)) := by positivity
        gcongr
    _ = 2 * (M * ℓ) ^ 2 * ((q : ℝ) * y ^ (1 / 2 + δ) + ∑ j ∈ Finset.range (nlev δ),
          C * ((q : ℝ) * (T + 1)) ^ (A * (1 - lev δ j)) * Real.log ((q : ℝ) * (T + 1)) ^ B *
            y ^ (lev δ (j + 1) + δ) + 2 * q * y ^ (11 / 12 + δ) * (2 * E ^ 2)) := by ring

/-! ### The sizes -/

/-- **The mean square, sized.** For `x ≥ 3` and `q^{A+η₀} ≤ x²`,
`Σ_{χ ≠ 1} |S_χ(x)|² ≤ 2M log(q + 2)·Ktot·(x²)^{1−c₀}`: `error_sq_le` at `T = 2 log x² + 2`, where `2e^{−T} ≤ e^{−T/2}`,
and `Linnik.total_le` at `x²`. -/
theorem sum_sq_le {A B C η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) (q : ℕ) [NeZero q] {x : ℝ} (hx : 3 ≤ x)
    (hqx : (q : ℝ) ^ (A + η₀) ≤ x ^ 2) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2 ≤
      2 * (Mstar (dL A η₀) * Real.log (q + 2)) * (Ktot A B C η₀ * (x ^ 2) ^ (1 - c0 A η₀)) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have herr := error_sq_le hD q (dL_pos hA hη0) (dL_le hA hη1) (T := 2 * Real.log (x ^ 2) + 2)
    (by have := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ x ^ 2); linarith) hx1
  obtain ⟨y, hy⟩ : ∃ y : ℝ, x ^ 2 = y := ⟨_, rfl⟩
  rw [hy] at herr hqx ⊢
  have hy3 : (3 : ℝ) ≤ y := by rw [← hy]; nlinarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hly : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]; have := Real.exp_one_lt_d9; linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hM0 : 0 < Mstar (dL A η₀) := Mstar_pos (dL_pos hA hη0) (dL_le hA hη1)
  have hℓ1 := one_le_log_add_two q
  have hMℓ : 0 ≤ Mstar (dL A η₀) * Real.log (q + 2) := mul_nonneg hM0.le (by linarith)
  have htot := total_le hA hB hC hη0 hη1 q hy3 hqx
  -- `2E² ≤ E`
  have hE0 : 0 < Real.exp (-(2 * Real.log y + 2) / 2) := Real.exp_pos _
  have hE2 : 2 * Real.exp (-(2 * Real.log y + 2) / 2) ^ 2 ≤ Real.exp (-(2 * Real.log y + 2) / 2) := by
    have h1 : Real.exp (-(2 * Real.log y + 2) / 2) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.exp_one_gt_d9; norm_num; linarith
    nlinarith
  obtain ⟨W, hW⟩ : ∃ W : ℝ, ∑ j ∈ Finset.range (nlev (dL A η₀)), C * ((q : ℝ) * (2 * Real.log y + 2 + 1)) ^
      (A * (1 - lev (dL A η₀) j)) * Real.log ((q : ℝ) * (2 * Real.log y + 2 + 1)) ^ B *
        y ^ (lev (dL A η₀) (j + 1) + dL A η₀) = W := ⟨_, rfl⟩
  rw [hW] at herr htot
  obtain ⟨E, hE⟩ : ∃ E : ℝ, Real.exp (-(2 * Real.log y + 2) / 2) = E := ⟨_, rfl⟩
  rw [hE] at herr htot hE0 hE2
  have hy11 : 0 ≤ 2 * (q : ℝ) * y ^ (11 / 12 + dL A η₀) := by positivity
  have h1 : 0 ≤ Real.exp (-1) * ((q : ℝ) * Real.log y) := by
    have : 0 ≤ (q : ℝ) * Real.log y := mul_nonneg (by linarith) (by linarith)
    positivity
  have h3 : 0 ≤ (q : ℝ) * (2 * √(10 * y * Real.log y) * Real.log (10 * y * Real.log y) +
      96 * y ^ 3 * Real.exp (-(10 * y * Real.log y / (2 * y)))) := by
    have hl : 0 ≤ Real.log (10 * y * Real.log y) := Real.log_nonneg (by nlinarith)
    have : 0 ≤ 2 * √(10 * y * Real.log y) * Real.log (10 * y * Real.log y) :=
      mul_nonneg (by positivity) hl
    have h96 : 0 ≤ 96 * y ^ 3 * Real.exp (-(10 * y * Real.log y / (2 * y))) := by positivity
    exact mul_nonneg (by linarith) (by linarith)
  -- the bracket of `error_sq_le` is at most that of `total_le`
  have hbr : (q : ℝ) * y ^ (1 / 2 + dL A η₀) + W + 2 * q * y ^ (11 / 12 + dL A η₀) * (2 * E ^ 2) ≤
      (q : ℝ) * y ^ (1 / 2 + dL A η₀) + W + 2 * q * y ^ (11 / 12 + dL A η₀) * E := by
    have := mul_le_mul_of_nonneg_left hE2 hy11
    linarith
  have hmid : Mstar (dL A η₀) * Real.log (q + 2) * ((q : ℝ) * y ^ (1 / 2 + dL A η₀) + W +
      2 * q * y ^ (11 / 12 + dL A η₀) * E) ≤ Ktot A B C η₀ * y ^ (1 - c0 A η₀) := by linarith
  calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2
      ≤ 2 * (Mstar (dL A η₀) * Real.log (q + 2)) ^ 2 * ((q : ℝ) * y ^ (1 / 2 + dL A η₀) + W +
          2 * q * y ^ (11 / 12 + dL A η₀) * (2 * E ^ 2)) := herr
    _ ≤ 2 * (Mstar (dL A η₀) * Real.log (q + 2)) ^ 2 * ((q : ℝ) * y ^ (1 / 2 + dL A η₀) + W +
          2 * q * y ^ (11 / 12 + dL A η₀) * E) := by gcongr
    _ = 2 * (Mstar (dL A η₀) * Real.log (q + 2)) * (Mstar (dL A η₀) * Real.log (q + 2) *
          ((q : ℝ) * y ^ (1 / 2 + dL A η₀) + W + 2 * q * y ^ (11 / 12 + dL A η₀) * E)) := by ring
    _ ≤ 2 * (Mstar (dL A η₀) * Real.log (q + 2)) * (Ktot A B C η₀ * y ^ (1 - c0 A η₀)) := by gcongr

/-! ### The mean square over the classes -/

open scoped Classical in
/-- The total over the reduced classes: `S₀(x; q) = Σ_{(a, q) = 1} S(x; q, a)`. -/
def S0 (q : ℕ) [NeZero q] (x : ℝ) : ℝ := ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a), SAP q a x

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- `χ(a⁻¹) = χ⁻¹(a)` for a unit `a`. -/
lemma inv_apply_of_isUnit (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) : χ a⁻¹ = χ⁻¹ a := by
  rw [MulChar.inv_apply_eq_inv']
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, ZMod.inv_mul_of_unit a ha, map_one]

/-- Orthogonality over the classes: `Σ_a ψ(a) = φ(q)[ψ = 1]` (Mathlib's `MulChar.sum_eq_zero_of_ne_one` and
`MulChar.sum_one_eq_card_units`). -/
lemma sum_char_apply (ψ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, ψ a = if ψ = 1 then (q.totient : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [h, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one h

open scoped Classical in
/-- `Σ_χ χ⁻¹(a)S_χ(x)` is `φ(q)S(x; q, a)` on the units (`Linnik.totient_mul_SAP`) and `0` elsewhere. -/
lemma sum_inv_apply_mul (a : ZMod q) {x : ℝ} (hx : 0 < x) :
    ∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * Sx χ x =
      if IsUnit a then (q.totient : ℂ) * (SAP q a x : ℂ) else 0 := by
  split_ifs with ha
  · rw [totient_mul_SAP q ha hx]
    exact Finset.sum_congr rfl fun χ _ => by rw [inv_apply_of_isUnit χ ha]
  · exact Finset.sum_eq_zero fun χ _ => by rw [MulChar.map_nonunit _ ha, zero_mul]

/-- `S₀(x; q) = S_1(x)`: the trivial character's sum is the total over the reduced classes. -/
lemma S0_eq (q : ℕ) [NeZero q] {x : ℝ} (hx : 0 < x) : (S0 q x : ℂ) = Sx (1 : DirichletCharacter ℂ q) x := by
  classical
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have h1 : ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * Sx χ x = (q.totient : ℂ) * (S0 q x : ℂ) := by
    rw [S0, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun a _ => sum_inv_apply_mul a hx
  have h2 : ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * Sx χ x =
      (q.totient : ℂ) * Sx (1 : DirichletCharacter ℂ q) x := by
    rw [Finset.sum_comm]
    have h : ∀ χ : DirichletCharacter ℂ q, ∑ a : ZMod q, χ⁻¹ a * Sx χ x =
        if χ = 1 then (q.totient : ℂ) * Sx χ x else 0 := by
      intro χ
      rw [← Finset.sum_mul, sum_char_apply]
      by_cases hχ : χ = 1
      · rw [ite_eq_left (by rw [hχ, inv_one]), ite_eq_left hχ]
      · rw [ite_eq_right (by rwa [inv_eq_one]), ite_eq_right hχ, zero_mul]
    rw [Finset.sum_congr rfl fun χ _ => h χ, Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ q)
      (fun χ => (q.totient : ℂ) * Sx χ x), ite_eq_left (Finset.mem_univ _)]
  exact mul_left_cancel₀ hφ (h1.symm.trans h2)

open scoped Classical in
/-- **The mean square over the reduced classes** (Parseval, as an inequality):
`Σ_{(a, q) = 1} (φ(q)S(x; q, a) − S₀(x; q))² ≤ φ(q) Σ_{χ ≠ 1} |S_χ(x)|²`. The left side is
`φ(q) Σ_{χ ≠ 1} S_χ S_{χ⁻¹}`, by the orthogonality of the characters over the classes. -/
theorem variance_le (q : ℕ) [NeZero q] {x : ℝ} (hx : 0 < x) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a), ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 ≤
      (q.totient : ℝ) * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖Sx χ x‖ ^ 2 := by
  set S := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) with hS
  set D : ZMod q → ℂ := fun a => ∑ χ ∈ S, χ⁻¹ a * Sx χ x with hD
  -- `D` on the units and elsewhere
  have hDu : ∀ a : ZMod q, D a = if IsUnit a then (((q.totient : ℝ) * SAP q a x - S0 q x : ℝ) : ℂ) else 0 := by
    intro a
    have hall := sum_inv_apply_mul a hx
    have hsplit : ∑ χ : DirichletCharacter ℂ q, χ⁻¹ a * Sx χ x =
        (1 : DirichletCharacter ℂ q)⁻¹ a * Sx (1 : DirichletCharacter ℂ q) x + D a := by
      rw [hD, hS, Finset.filter_ne', ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
    split_ifs with ha
    · rw [ite_eq_left ha] at hall
      have h1 : (1 : DirichletCharacter ℂ q)⁻¹ a = 1 := by rw [inv_one, MulChar.one_apply ha]
      rw [h1, one_mul, ← S0_eq q hx] at hsplit
      push_cast
      linear_combination hall - hsplit
    · exact Finset.sum_eq_zero fun χ _ => by rw [MulChar.map_nonunit _ ha, zero_mul]
  -- the sum of the squares of `D`
  have hpar : ∑ a : ZMod q, D a * D a = (q.totient : ℂ) * ∑ χ ∈ S, Sx χ x * Sx χ⁻¹ x := by
    have h1 : ∀ a : ZMod q, D a * D a = ∑ χ ∈ S, ∑ χ' ∈ S, (χ⁻¹ * χ'⁻¹) a * (Sx χ x * Sx χ' x) := by
      intro a
      rw [hD, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun χ' _ => ?_
      rw [MulChar.mul_apply]; ring
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [Finset.sum_comm]
    have h2 : ∀ χ' ∈ S, ∑ a : ZMod q, (χ⁻¹ * χ'⁻¹) a * (Sx χ x * Sx χ' x) =
        if χ' = χ⁻¹ then (q.totient : ℂ) * (Sx χ x * Sx χ' x) else 0 := by
      intro χ' _
      have hiff : χ⁻¹ * χ'⁻¹ = 1 ↔ χ' = χ⁻¹ := by
        rw [inv_mul_eq_one]
        exact ⟨fun h => by rw [h, inv_inv], fun h => by rw [h, inv_inv]⟩
      rw [← Finset.sum_mul, sum_char_apply, ite_mul, zero_mul]
      exact if_congr hiff rfl rfl
    have hmem : χ⁻¹ ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, inv_ne_one.2 (Finset.mem_filter.1 hχ).2⟩
    rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' S χ⁻¹ (fun χ' => (q.totient : ℂ) * (Sx χ x * Sx χ' x)),
      ite_eq_left hmem]
  -- back to the reals
  have hV : ((∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
      ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 : ℝ) : ℂ) = ∑ a : ZMod q, D a * D a := by
    rw [Complex.ofReal_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hDu a]
    split_ifs
    · push_cast; ring
    · simp
  have hV0 : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
      ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hinv : ∑ χ ∈ S, ‖Sx χ⁻¹ x‖ ^ 2 = ∑ χ ∈ S, ‖Sx χ x‖ ^ 2 := by
    refine Finset.sum_equiv (Equiv.inv (DirichletCharacter ℂ q)) (fun χ => ?_) (fun χ _ => rfl)
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.inv_apply, ne_eq, inv_eq_one]
  calc ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a), ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2
      = ‖((∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
          ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hV0]
    _ = (q.totient : ℝ) * ‖∑ χ ∈ S, Sx χ x * Sx χ⁻¹ x‖ := by
        rw [hV, hpar, norm_mul, Complex.norm_natCast]
    _ ≤ (q.totient : ℝ) * ∑ χ ∈ S, ‖Sx χ x‖ * ‖Sx χ⁻¹ x‖ := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => (norm_mul _ _).le)
    _ ≤ (q.totient : ℝ) * ∑ χ ∈ S, (‖Sx χ x‖ ^ 2 + ‖Sx χ⁻¹ x‖ ^ 2) / 2 := by
        gcongr with χ _
        nlinarith [sq_nonneg (‖Sx χ x‖ - ‖Sx χ⁻¹ x‖)]
    _ = (q.totient : ℝ) * ∑ χ ∈ S, ‖Sx χ x‖ ^ 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hinv]; ring

/-! ### The main term -/

/-- `2^{ω(q)} ≤ q`. -/
lemma two_pow_card_primeFactors_le {q : ℕ} (hq : q ≠ 0) : 2 ^ q.primeFactors.card ≤ q := by
  calc 2 ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ q.primeFactors, p :=
        Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)

/-- `log² x ≤ x/100` for `x ≥ 10⁷`. -/
lemma log_sq_le {x : ℝ} (hx : 10 ^ 7 ≤ x) : Real.log x ^ 2 ≤ x / 100 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (le_trans (by norm_num) hx)
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    have e : x ^ (1 / 4 : ℝ) / (1 / 4) = 4 * x ^ (1 / 4 : ℝ) := by ring
    linarith
  have hsq : (x ^ (1 / 4 : ℝ)) ^ 2 = √x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]; norm_num
  have hsqrt : √x ≤ x / 3162 := by
    have h1 : (3162 : ℝ) ≤ √x := by
      rw [show (3162 : ℝ) = √(3162 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (le_trans (by norm_num) hx)
    have h2 : √x * √x = x := Real.mul_self_sqrt hx0.le
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have h1 : Real.log x ^ 2 ≤ (4 * x ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hlx0 hlog 2
  have h2 : (4 * x ^ (1 / 4 : ℝ)) ^ 2 = 16 * √x := by rw [mul_pow, hsq]; norm_num
  linarith

/-- **The main term**: `S₀(x; q) ≥ x/12` for `x ≥ 10⁷` and `q ≤ x`, from `Linnik.re_Sx_one_ge`, Chebyshev's
`ψ(x) ≥ x/4` and `ω(q) ≤ 2 log q`. -/
theorem S0_ge (q : ℕ) [NeZero q] {x : ℝ} (hx : 10 ^ 7 ≤ x) (hqx : (q : ℝ) ≤ x) : x / 12 ≤ S0 q x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hS : S0 q x = (Sx (1 : DirichletCharacter ℂ q) x).re := by rw [← S0_eq q hx0, Complex.ofReal_re]
  have hone := re_Sx_one_ge q hx1
  have hψ := LeastNonresidue.psi_ge_quarter (le_trans (by norm_num) hx : (100 : ℝ) ≤ x)
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlq : Real.log q ≤ Real.log x := Real.log_le_log (by linarith) hqx
  have hω : (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
    have h3 : ((2 : ℝ) ^ q.primeFactors.card) ≤ q := by exact_mod_cast two_pow_card_primeFactors_le (NeZero.ne q)
    have h4 : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h3
    have hl2 := Real.log_two_gt_d9
    have hc0 : (0 : ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
    nlinarith
  have hωl : (q.primeFactors.card : ℝ) * Real.log x ≤ 2 * Real.log x ^ 2 := by
    calc (q.primeFactors.card : ℝ) * Real.log x ≤ 2 * Real.log q * Real.log x := by gcongr
      _ ≤ 2 * Real.log x * Real.log x := by gcongr
      _ = 2 * Real.log x ^ 2 := by ring
  have hl2 := log_sq_le hx
  have he : (367 / 1000 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    have := Real.exp_one_lt_d9; norm_num; linarith
  rw [hS]
  refine le_trans ?_ hone
  have h5 : x / 4 - x / 50 ≤ Chebyshev.psi x - q.primeFactors.card * Real.log x := by linarith
  have h6 : 0 ≤ x / 4 - x / 50 := by linarith
  calc x / 12 ≤ 367 / 1000 * (x / 4 - x / 50) := by linarith
    _ ≤ Real.exp (-1) * (x / 4 - x / 50) := by gcongr
    _ ≤ Real.exp (-1) * (Chebyshev.psi x - q.primeFactors.card * Real.log x) := by gcongr

/-! ### The primes of a class -/

open scoped Classical in
/-- The number of primes `p ≤ Y` in the class `a` mod `q`. -/
def cnt (q : ℕ) (a : ZMod q) (Y : ℝ) : ℕ :=
  ((Finset.Ioc 0 ⌊Y⌋₊).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = a).card

open scoped Classical in
/-- The prime powers up to `Y` in the class `a` that are not primes, with von Mangoldt's weights. -/
def PP (q : ℕ) (a : ZMod q) (Y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊Y⌋₊).filter (fun n : ℕ => ¬ n.Prime), if (n : ZMod q) = a then Λ n else 0

lemma PP_nonneg (q : ℕ) (a : ZMod q) (Y : ℝ) : 0 ≤ PP q a Y := by
  classical
  refine Finset.sum_nonneg fun n _ => ?_
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

/-- Over all the classes the prime powers weigh `ψ(Y) − θ(Y) ≤ 2√Y log Y` (Mathlib's
`Chebyshev.psi_sub_theta_le`). -/
theorem sum_PP_le (q : ℕ) [NeZero q] {Y : ℝ} (hY : 1 ≤ Y) : ∑ a : ZMod q, PP q a Y ≤ 2 * √Y * Real.log Y := by
  classical
  have h : ∑ a : ZMod q, PP q a Y = Chebyshev.psi Y - Chebyshev.theta Y := by
    unfold PP
    rw [Finset.sum_comm, Chebyshev.psi_sub_theta_eq_sum_not_prime]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (n : ZMod q) (fun _ => Λ n), ite_eq_left (Finset.mem_univ _)]
  rw [h]; exact Chebyshev.psi_sub_theta_le hY

/-- **A class by its primes**: `S(x; q, a) ≤ π(Y; q, a) log Y + PP(Y; q, a) + 96x³e^{−Y/(2x)}`: a prime `p ≤ Y`
weighs at most `log Y`, and the terms beyond `Y` are those of `Linnik.SAP_le_of_noPrime`. -/
theorem SAP_le_cnt (q : ℕ) (a : ZMod q) {x Y : ℝ} (hx : 0 < x) (hY : 1 ≤ Y) :
    SAP q a x ≤ cnt q a Y * Real.log Y + PP q a Y + 96 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by
  classical
  set P₀ := (Finset.Ioc 0 ⌊Y⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a) with hP₀
  set N₀ := (Finset.Ioc 0 ⌊Y⌋₊).filter (fun n : ℕ => ¬ n.Prime) with hN₀
  set g₀ : ℕ → ℝ := fun n => if n ∈ P₀ then Real.log Y else 0 with hg₀
  set f₁ : ℕ → ℝ := fun n => if n ∈ N₀ then (if (n : ZMod q) = a then Λ n else 0) else 0 with hf₁
  set f₂ : ℕ → ℝ := fun n => if Y < n then Λ n * Real.exp (-((n : ℝ) / x)) else 0 with hf₂
  set K : ℝ := 48 * x ^ 3 * Real.exp (-(Y / (2 * x))) with hK
  have hK0 : 0 ≤ K := by positivity
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hg₀s : Summable g₀ := summable_of_ne_finset_zero (s := P₀)
    fun n hn => by simp only [hg₀]; rw [ite_eq_right hn]
  have hf₁s : Summable f₁ := summable_of_ne_finset_zero (s := N₀)
    fun n hn => by simp only [hf₁]; rw [ite_eq_right hn]
  have hf₂le : ∀ n, f₂ n ≤ K * (1 / (n : ℝ) ^ 2) := by
    intro n
    simp only [hf₂]
    split_ifs with h
    · exact tail_term_le hx (by linarith) h
    · positivity
  have hf₂0 : ∀ n, 0 ≤ f₂ n := fun n => by
    simp only [hf₂]; split_ifs
    · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
    · exact le_rfl
  have hg₀0 : ∀ n, 0 ≤ g₀ n := fun n => by
    simp only [hg₀]; split_ifs
    · exact hlY
    · exact le_rfl
  have hf₁0 : ∀ n, 0 ≤ f₁ n := fun n => by
    simp only [hf₁]; split_ifs
    · exact vonMangoldt_nonneg
    · exact le_rfl
    · exact le_rfl
  have hzeta : HasSum (fun n : ℕ => K * (1 / (n : ℝ) ^ 2)) (K * (π ^ 2 / 6)) := hasSum_zeta_two.mul_left K
  have hf₂s : Summable f₂ := Summable.of_nonneg_of_le hf₂0 hf₂le hzeta.summable
  have hpt : ∀ n : ℕ, (if (n : ZMod q) = a then Λ n * Real.exp (-((n : ℝ) / x)) else 0) ≤
      g₀ n + f₁ n + f₂ n := by
    intro n
    by_cases hnY : Y < n
    · have : f₂ n = Λ n * Real.exp (-((n : ℝ) / x)) := by simp only [hf₂]; rw [ite_eq_left hnY]
      split_ifs
      · linarith [hg₀0 n, hf₁0 n]
      · linarith [hg₀0 n, hf₁0 n, hf₂0 n]
    · split_ifs with ha
      · by_cases hΛ : Λ n = 0
        · rw [hΛ, zero_mul]; linarith [hg₀0 n, hf₁0 n, hf₂0 n]
        · have hn0 : n ≠ 0 := fun h => hΛ (by rw [h]; exact ArithmeticFunction.map_zero)
          have hIoc : n ∈ Finset.Ioc 0 ⌊Y⌋₊ :=
            Finset.mem_Ioc.2 ⟨Nat.pos_of_ne_zero hn0, Nat.le_floor (not_lt.1 hnY)⟩
          have he : Real.exp (-((n : ℝ) / x)) ≤ 1 := Real.exp_le_one_iff.2 (by
            have : 0 ≤ (n : ℝ) / x := by positivity
            linarith)
          have hterm := mul_le_mul_of_nonneg_left he (vonMangoldt_nonneg (n := n))
          by_cases hnp : n.Prime
          · have hmem : n ∈ P₀ := Finset.mem_filter.2 ⟨hIoc, hnp, ha⟩
            have hg : g₀ n = Real.log Y := by simp only [hg₀]; rw [ite_eq_left hmem]
            have hΛn : Λ n ≤ Real.log Y := by
              rw [vonMangoldt_apply_prime hnp]
              exact Real.log_le_log (by exact_mod_cast hnp.pos) (not_lt.1 hnY)
            linarith [hf₁0 n, hf₂0 n]
          · have hmem : n ∈ N₀ := Finset.mem_filter.2 ⟨hIoc, hnp⟩
            have hf : f₁ n = Λ n := by simp only [hf₁]; rw [ite_eq_left hmem, ite_eq_left ha]
            linarith [hg₀0 n, hf₂0 n]
      · linarith [hg₀0 n, hf₁0 n, hf₂0 n]
  have hsum0 : ∑' n, g₀ n = cnt q a Y * Real.log Y := by
    rw [tsum_eq_sum (s := P₀) fun n hn => by simp only [hg₀]; rw [ite_eq_right hn]]
    rw [Finset.sum_congr rfl fun n hn => by simp only [hg₀]; rw [ite_eq_left hn], Finset.sum_const,
      nsmul_eq_mul, cnt]
  have hsum1 : ∑' n, f₁ n = PP q a Y := by
    rw [tsum_eq_sum (s := N₀) fun n hn => by simp only [hf₁]; rw [ite_eq_right hn], PP]
    exact Finset.sum_congr rfl fun n hn => by simp only [hf₁]; rw [ite_eq_left hn]
  have hsum2 : ∑' n, f₂ n ≤ 96 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by
    refine (Summable.tsum_le_tsum hf₂le hf₂s hzeta.summable).trans ?_
    rw [hzeta.tsum_eq]
    have hpi : π ^ 2 / 6 ≤ 2 := by have := Real.pi_lt_d2; nlinarith [Real.pi_pos]
    calc K * (π ^ 2 / 6) ≤ K * 2 := by gcongr
      _ = 96 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by rw [hK]; ring
  calc SAP q a x ≤ ∑' n, (g₀ n + f₁ n + f₂ n) :=
        Summable.tsum_le_tsum hpt (summable_SAP_term q a hx) ((hg₀s.add hf₁s).add hf₂s)
    _ = ∑' n, g₀ n + ∑' n, f₁ n + ∑' n, f₂ n := by
        rw [(hg₀s.add hf₁s).tsum_add hf₂s, hg₀s.tsum_add hf₁s]
    _ ≤ cnt q a Y * Real.log Y + PP q a Y + 96 * x ^ 3 * Real.exp (-(Y / (2 * x))) := by
        rw [hsum0, hsum1]; linarith

/-! ### Almost every class -/

/-- `log(q + 2)(x²)^{1−c} ≤ (2/c)x²x^{−c}` for `1 ≤ q ≤ x`, `x ≥ 2` and `c > 0`. -/
lemma log_mul_rpow_le {q x c : ℝ} (hq1 : 1 ≤ q) (hqx : q ≤ x) (hx : 2 ≤ x) (hc : 0 < c) :
    Real.log (q + 2) * (x ^ 2) ^ (1 - c) ≤ 2 / c * (x ^ 2 * x ^ (-c)) := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.log (q + 2) ≤ 2 * Real.log x := by
    have : Real.log (q + 2) ≤ Real.log (x * x) := Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_mul hx0.ne' hx0.ne'] at this; linarith
  have h2 : Real.log x ≤ x ^ c / c := Real.log_le_rpow_div hx0.le hc
  have h3 : (x ^ 2) ^ (1 - c) = x ^ 2 * x ^ (-c) * x ^ (-c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1; push_cast; ring
  have h4 : x ^ c * x ^ (-c) = 1 := by rw [← Real.rpow_add hx0]; simp
  have hpos : 0 ≤ x ^ 2 * x ^ (-c) * x ^ (-c) := by positivity
  have hxc : 0 ≤ x ^ c / c := by positivity
  calc Real.log (q + 2) * (x ^ 2) ^ (1 - c) ≤ 2 * (x ^ c / c) * (x ^ 2 * x ^ (-c) * x ^ (-c)) := by
        rw [h3]; exact mul_le_mul_of_nonneg_right (by linarith) hpos
    _ = 2 / c * (x ^ 2 * x ^ (-c)) * (x ^ c * x ^ (-c)) := by ring
    _ = 2 / c * (x ^ 2 * x ^ (-c)) := by rw [h4, mul_one]

/-- The prime powers, sized: `192√Y log Y ≤ 200000·x·x^{−c}` at `Y = 10x log x`, for `x ≥ 3` and `0 < c ≤ 1/4`. -/
lemma pp_size {x c : ℝ} (hx : 3 ≤ x) (hc : 0 < c) (hc4 : c ≤ 1 / 4) :
    192 * (√(10 * x * Real.log x) * Real.log (10 * x * Real.log x)) ≤ 200000 * (x * x ^ (-c)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  obtain ⟨hY1, hY2⟩ := size_Y hx
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hsl : √(Real.log x) ≤ Real.log x := by
    have h1 : 1 ≤ √(Real.log x) := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hl1
    have h2 : √(Real.log x) * √(Real.log x) = Real.log x := Real.mul_self_sqrt (by linarith)
    nlinarith
  have h10 : √(10 : ℝ) ≤ 317 / 100 := by
    rw [show (317 / 100 : ℝ) = √((317 / 100) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hlog : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 8)
    have e : x ^ (1 / 8 : ℝ) / (1 / 8) = 8 * x ^ (1 / 8 : ℝ) := by ring
    linarith
  have hl2 : Real.log x ^ 2 ≤ 64 * x ^ (1 / 4 : ℝ) := by
    have h1 : Real.log x ^ 2 ≤ (8 * x ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith) hlog 2
    have h2 : (8 * x ^ (1 / 8 : ℝ)) ^ 2 = 64 * x ^ (1 / 4 : ℝ) := by
      have e : (x ^ (1 / 8 : ℝ)) ^ 2 = x ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
      rw [mul_pow, e]; norm_num
    linarith
  have hsx : √x * x ^ (1 / 4 : ℝ) ≤ x * x ^ (-c) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    nth_rewrite 2 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg _
  have hs10 : 0 ≤ √(10 : ℝ) := Real.sqrt_nonneg _
  have hsl0 : 0 ≤ √(Real.log x) := Real.sqrt_nonneg _
  have hx4 : 0 ≤ x ^ (1 / 4 : ℝ) := by positivity
  -- `√Y log Y ≤ 5√10 √x log² x`
  have hA : √(10 * x * Real.log x) * Real.log (10 * x * Real.log x) ≤
      317 / 100 * √x * Real.log x * (5 * Real.log x) := by
    rw [hY2]
    have h5 : Real.log (10 * x * Real.log x) ≤ 5 * Real.log x := by linarith
    have h6 : √10 * √x * √(Real.log x) ≤ 317 / 100 * √x * Real.log x := by
      have := mul_le_mul h10 hsl hsl0 (by norm_num : (0 : ℝ) ≤ 317 / 100)
      nlinarith
    exact mul_le_mul h6 h5 (Real.log_nonneg (by nlinarith)) (by positivity)
  have hB : 317 / 100 * √x * Real.log x * (5 * Real.log x) ≤ 317 / 100 * 5 * 64 * (√x * x ^ (1 / 4 : ℝ)) := by
    have : √x * Real.log x ^ 2 ≤ √x * (64 * x ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hl2 hs0
    nlinarith
  nlinarith [mul_nonneg hs0 hx4]

open scoped Classical in
/-- The reduced classes mod `q` number `φ(q)`. -/
lemma card_isUnit (q : ℕ) [NeZero q] : (Finset.univ.filter fun a : ZMod q => IsUnit a).card = q.totient := by
  have h := sum_char_apply (1 : DirichletCharacter ℂ q)
  rw [ite_eq_left rfl] at h
  have h2 : ∑ a : ZMod q, (1 : DirichletCharacter ℂ q) a =
      ((Finset.univ.filter fun a : ZMod q => IsUnit a).card : ℂ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with ha
    · exact MulChar.one_apply ha
    · exact MulChar.map_nonunit _ ha
  exact_mod_cast h2.symm.trans h

open scoped Classical in
/-- The reduced classes `a` mod `q` with fewer than `m` primes `p ≤ Y`. -/
def few (q : ℕ) [NeZero q] (Y m : ℝ) : Finset (ZMod q) :=
  Finset.univ.filter fun a : ZMod q => IsUnit a ∧ (cnt q a Y : ℝ) < m

/-- The constant of `card_few_le`. -/
def Kaa (A B C η₀ : ℝ) : ℝ := 2304 * Mstar (dL A η₀) * Ktot A B C η₀ / c0 A η₀ + 200000

/-- **Almost every class, at `x`.** Let `A ≥ 2`, `B ≥ 0`, `C ≥ 0` with `CharDensity A B C`, `0 < η₀ ≤ 1/2`,
`x ≥ 10⁷`, `q ≤ x` and `q^{A+η₀} ≤ x²`. The reduced classes mod `q` with fewer than `x/(240φ(q) log x)` primes
`p ≤ 10x log x` number at most `Kaa·φ(q)·x^{−c₀}`. Such a class has `φ(q)S(x; q, a) ≤ S₀/2` unless its prime powers
weigh more than `S₀/(8φ(q))` (`SAP_le_cnt`); the first kind is counted by the mean square (`variance_le`,
`sum_sq_le`), the second by `sum_PP_le`. -/
theorem card_few_le {A B C η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) (q : ℕ) [NeZero q] {x : ℝ} (hx : 10 ^ 7 ≤ x) (hqx1 : (q : ℝ) ≤ x)
    (hqx : (q : ℝ) ^ (A + η₀) ≤ x ^ 2) :
    ((few q (10 * x * Real.log x) (x / (240 * q.totient * Real.log x))).card : ℝ) ≤
      (q.totient : ℝ) * (Kaa A B C η₀ * x ^ (-c0 A η₀)) := by
  classical
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hφ0 : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hS0 := S0_ge q hx hqx1
  have hc0 : 0 < c0 A η₀ := c0_pos hA hη0
  have hc4 : c0 A η₀ ≤ 1 / 4 := by unfold c0; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hM0 : 0 < Mstar (dL A η₀) := Mstar_pos (dL_pos hA hη0) (dL_le hA hη1)
  have hKt0 : 0 ≤ Ktot A B C η₀ := Ktot_nonneg hA hB hC hη0 hη1
  have hpp := pp_size hx3 hc0 hc4
  obtain ⟨hlY, -⟩ := size_Y hx3
  -- the tail
  have htail : (q.totient : ℝ) * (96 * x ^ 3 * Real.exp (-(10 * x * Real.log x / (2 * x)))) ≤ S0 q x / 8 := by
    rw [exp_Y_eq hx0]
    have h1 : 96 * x ^ 3 * (x ^ 5)⁻¹ = 96 / x ^ 2 := by field_simp
    have h2 : (q.totient : ℝ) * (96 / x ^ 2) ≤ x * (96 / x ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : x * (96 / x ^ 2) = 96 / x := by field_simp
    have h4 : 96 / x ≤ x / 96 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; nlinarith
    rw [h1]; linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = 10 * x * Real.log x := ⟨_, rfl⟩
  rw [← hY] at hpp hlY htail ⊢
  have hY1 : 1 ≤ Y := by rw [hY]; nlinarith
  have hlY0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
  set U := Finset.univ.filter (fun a : ZMod q => IsUnit a) with hU
  set B₁ := U.filter (fun a => x ^ 2 / 576 ≤ ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2) with hB₁
  set B₂ := U.filter (fun a => S0 q x / 8 < (q.totient : ℝ) * PP q a Y) with hB₂
  have hsub : few q Y (x / (240 * q.totient * Real.log x)) ⊆ B₁ ∪ B₂ := by
    intro a ha
    rw [few, Finset.mem_filter] at ha
    obtain ⟨-, hu, hcnt⟩ := ha
    have haU : a ∈ U := Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩
    by_cases hppa : S0 q x / 8 < (q.totient : ℝ) * PP q a Y
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨haU, hppa⟩)
    · refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨haU, ?_⟩)
      have hSAP := SAP_le_cnt q a hx0 hY1
      have h1 : (q.totient : ℝ) * ((cnt q a Y : ℝ) * Real.log Y) ≤ x / 48 := by
        have h2 : (cnt q a Y : ℝ) * Real.log Y ≤ x / (240 * q.totient * Real.log x) * (5 * Real.log x) :=
          mul_le_mul hcnt.le (by linarith) hlY0 (by positivity)
        have h3 : (q.totient : ℝ) * (x / (240 * q.totient * Real.log x) * (5 * Real.log x)) = x / 48 := by
          field_simp; ring
        calc (q.totient : ℝ) * ((cnt q a Y : ℝ) * Real.log Y)
            ≤ (q.totient : ℝ) * (x / (240 * q.totient * Real.log x) * (5 * Real.log x)) :=
              mul_le_mul_of_nonneg_left h2 hφ0.le
          _ = x / 48 := h3
      have h4 : (q.totient : ℝ) * SAP q a x ≤ S0 q x / 2 := by
        have h := mul_le_mul_of_nonneg_left hSAP hφ0.le
        have e : (q.totient : ℝ) * (cnt q a Y * Real.log Y + PP q a Y + 96 * x ^ 3 * Real.exp (-(Y / (2 * x)))) =
            (q.totient : ℝ) * ((cnt q a Y : ℝ) * Real.log Y) + (q.totient : ℝ) * PP q a Y +
              (q.totient : ℝ) * (96 * x ^ 3 * Real.exp (-(Y / (2 * x)))) := by ring
        have hppa' := not_lt.1 hppa
        linarith
      have h5 : x / 24 ≤ S0 q x - (q.totient : ℝ) * SAP q a x := by linarith
      have h6 : (x / 24) ^ 2 ≤ (S0 q x - (q.totient : ℝ) * SAP q a x) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h5 2
      have h7 : ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 = (S0 q x - (q.totient : ℝ) * SAP q a x) ^ 2 := by
        ring
      rw [h7]
      calc x ^ 2 / 576 = (x / 24) ^ 2 := by ring
        _ ≤ (S0 q x - (q.totient : ℝ) * SAP q a x) ^ 2 := h6
  -- the first set, by the mean square
  have hV := variance_le q hx0
  have hsq := sum_sq_le hA hB hC hD hη0 hη1 q hx3 hqx
  have hcard1 : (B₁.card : ℝ) * (x ^ 2 / 576) ≤ (q.totient : ℝ) *
      (2 * (Mstar (dL A η₀) * Real.log (q + 2)) * (Ktot A B C η₀ * (x ^ 2) ^ (1 - c0 A η₀))) := by
    have h1 : (B₁.card : ℝ) * (x ^ 2 / 576) ≤ ∑ a ∈ B₁, ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 := by
      rw [← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum _ _ _ fun a ha => (Finset.mem_filter.1 ha).2
    have h2 : ∑ a ∈ B₁, ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 ≤
        ∑ a ∈ U, ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a _ _ => sq_nonneg _
    have h3 := mul_le_mul_of_nonneg_left hsq hφ0.le
    linarith
  -- the second set, by the prime powers
  have hcard2 : (B₂.card : ℝ) * (S0 q x / 8) ≤ (q.totient : ℝ) * (2 * √Y * Real.log Y) := by
    have h1 : (B₂.card : ℝ) * (S0 q x / 8) ≤ ∑ a ∈ B₂, (q.totient : ℝ) * PP q a Y := by
      rw [← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum _ _ _ fun a ha => (Finset.mem_filter.1 ha).2.le
    have h2 : ∑ a ∈ B₂, (q.totient : ℝ) * PP q a Y ≤ (q.totient : ℝ) * ∑ a : ZMod q, PP q a Y := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun a _ _ => mul_nonneg hφ0.le (PP_nonneg q a Y)
    have h3 := mul_le_mul_of_nonneg_left (sum_PP_le q hY1) hφ0.le
    linarith
  have hb1 : (B₁.card : ℝ) ≤
      (q.totient : ℝ) * (2304 * Mstar (dL A η₀) * Ktot A B C η₀ / c0 A η₀ * x ^ (-c0 A η₀)) := by
    have hlm := log_mul_rpow_le hq1 hqx1 (by linarith : (2 : ℝ) ≤ x) hc0
    have hMK : 0 ≤ (q.totient : ℝ) * (2 * Mstar (dL A η₀) * Ktot A B C η₀) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hlm hMK
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < x ^ 2 / 576)
    calc (B₁.card : ℝ) * (x ^ 2 / 576) ≤ (q.totient : ℝ) *
          (2 * (Mstar (dL A η₀) * Real.log (q + 2)) * (Ktot A B C η₀ * (x ^ 2) ^ (1 - c0 A η₀))) := hcard1
      _ = (q.totient : ℝ) * (2 * Mstar (dL A η₀) * Ktot A B C η₀) *
          (Real.log (q + 2) * (x ^ 2) ^ (1 - c0 A η₀)) := by ring
      _ ≤ (q.totient : ℝ) * (2 * Mstar (dL A η₀) * Ktot A B C η₀) *
          (2 / c0 A η₀ * (x ^ 2 * x ^ (-c0 A η₀))) := h1
      _ = (q.totient : ℝ) * (2304 * Mstar (dL A η₀) * Ktot A B C η₀ / c0 A η₀ * x ^ (-c0 A η₀)) *
          (x ^ 2 / 576) := by field_simp; ring
  have hb2 : (B₂.card : ℝ) ≤ (q.totient : ℝ) * (200000 * x ^ (-c0 A η₀)) := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < x / 96)
    have h1 : (B₂.card : ℝ) * (x / 96) ≤ (B₂.card : ℝ) * (S0 q x / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have h2 := mul_le_mul_of_nonneg_left hpp hφ0.le
    calc (B₂.card : ℝ) * (x / 96) ≤ (q.totient : ℝ) * (2 * √Y * Real.log Y) := h1.trans hcard2
      _ = (q.totient : ℝ) * (192 * (√Y * Real.log Y)) / 96 := by ring
      _ ≤ (q.totient : ℝ) * (200000 * (x * x ^ (-c0 A η₀))) / 96 := by gcongr
      _ = (q.totient : ℝ) * (200000 * x ^ (-c0 A η₀)) * (x / 96) := by ring
  calc ((few q Y (x / (240 * q.totient * Real.log x))).card : ℝ) ≤ ((B₁ ∪ B₂).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (B₁.card : ℝ) + B₂.card := by exact_mod_cast Finset.card_union_le _ _
    _ ≤ (q.totient : ℝ) * (Kaa A B C η₀ * x ^ (-c0 A η₀)) := by
        have e : (q.totient : ℝ) * (Kaa A B C η₀ * x ^ (-c0 A η₀)) =
            (q.totient : ℝ) * (2304 * Mstar (dL A η₀) * Ktot A B C η₀ / c0 A η₀ * x ^ (-c0 A η₀)) +
              (q.totient : ℝ) * (200000 * x ^ (-c0 A η₀)) := by rw [Kaa]; ring
        rw [e]; linarith

/-! ### The entropy of the primes mod `q` -/

open scoped Classical in
/-- **The entropy of the primes mod `q`** with the weights `Λ(n)e^{−n/x}`:
`H(x; q) = −Σ_{(a, q) = 1} P(a) log P(a)`, `P(a) = S(x; q, a)/S₀(x; q)`. -/
def entropy (q : ℕ) [NeZero q] (x : ℝ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a), Real.negMulLog (SAP q a x / S0 q x)

lemma SAP_nonneg (q : ℕ) (a : ZMod q) (x : ℝ) : 0 ≤ SAP q a x := tsum_nonneg fun n => by
  split_ifs
  · exact mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le
  · exact le_rfl

/-- `−p log p ≥ p log m − (mp² − p)` for `p ≥ 0` and `m > 0`: `log(mp) ≤ mp − 1`. -/
lemma negMulLog_ge {p m : ℝ} (hp : 0 ≤ p) (hm : 0 < m) :
    p * Real.log m - (m * p ^ 2 - p) ≤ Real.negMulLog p := by
  rcases hp.eq_or_lt with rfl | hp0
  · simp [Real.negMulLog]
  · have h := Real.log_le_sub_one_of_pos (mul_pos hm hp0)
    rw [Real.log_mul hm.ne' hp0.ne'] at h
    rw [Real.negMulLog]
    nlinarith

open scoped Classical in
/-- **Entropy and mean square**: when `S₀ > 0`,
`log φ(q) − Σ_{(a, q) = 1} (φ(q)S(x; q, a) − S₀)²/(φ(q)S₀²) ≤ H(x; q)`: the relative entropy of `P` to the uniform
distribution on the reduced classes is at most its chi-square divergence. -/
theorem entropy_ge (q : ℕ) [NeZero q] {x : ℝ} (hS : 0 < S0 q x) :
    Real.log q.totient - (∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
      ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2) / (q.totient * S0 q x ^ 2) ≤ entropy q x := by
  set U := Finset.univ.filter (fun a : ZMod q => IsUnit a) with hU
  have hφ0 : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hcard : (U.card : ℝ) = q.totient := by exact_mod_cast card_isUnit q
  have hsumP : ∑ a ∈ U, SAP q a x / S0 q x = 1 := by
    rw [← Finset.sum_div]
    exact div_self hS.ne'
  have hkey : ∀ a ∈ U, ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 / (q.totient * S0 q x ^ 2) =
      q.totient * (SAP q a x / S0 q x) ^ 2 - 2 * (SAP q a x / S0 q x) + 1 / q.totient := by
    intro a _
    field_simp
    ring
  have hV : (∑ a ∈ U, ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2) / (q.totient * S0 q x ^ 2) =
      q.totient * ∑ a ∈ U, (SAP q a x / S0 q x) ^ 2 - 1 := by
    rw [Finset.sum_div, Finset.sum_congr rfl hkey, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hsumP, Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
    ring
  have hpt : ∀ a ∈ U, SAP q a x / S0 q x * Real.log q.totient -
      (q.totient * (SAP q a x / S0 q x) ^ 2 - SAP q a x / S0 q x) ≤ Real.negMulLog (SAP q a x / S0 q x) :=
    fun a _ => negMulLog_ge (div_nonneg (SAP_nonneg q a x) hS.le) hφ0
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsumP] at hsum
  rw [hV, entropy]
  linarith

/-! ### The statements -/

/-- From `x ≥ Kq^{A/2+η}` with `K ≥ 10⁷` and `η₀/2 ≤ η`: `x ≥ 10⁷`, `q ≤ x` and `q^{A+η₀} ≤ x²`. -/
lemma hyps_of_le {A η η₀ K : ℝ} (hA : 2 ≤ A) (hη : 0 < η) (hη₀ : η₀ / 2 ≤ η) (hK : 10 ^ 7 ≤ K) (q : ℕ) [NeZero q]
    {x : ℝ} (hx : K * (q : ℝ) ^ (A / 2 + η) ≤ x) :
    (10 : ℝ) ^ 7 ≤ x ∧ (q : ℝ) ≤ x ∧ (q : ℝ) ^ (A + η₀) ≤ x ^ 2 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK
  have hK1 : (1 : ℝ) ≤ K := le_trans (by norm_num) hK
  have hqe1 : 1 ≤ (q : ℝ) ^ (A / 2 + η) := Real.one_le_rpow hq1 (by linarith)
  have hqe : (q : ℝ) ^ (A / 2 + η) ≤ x := le_trans (le_mul_of_one_le_left (by positivity) hK1) hx
  have hx7 : (10 : ℝ) ^ 7 ≤ x := le_trans (hK.trans (le_mul_of_one_le_right hK0.le hqe1)) hx
  refine ⟨hx7, ?_, ?_⟩
  · calc (q : ℝ) = (q : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (q : ℝ) ^ (A / 2 + η) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ ≤ x := hqe
  · have h1 : (q : ℝ) ^ ((A + η₀) / 2) ≤ x :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) hqe
    have h2 : ((q : ℝ) ^ ((A + η₀) / 2)) ^ 2 = (q : ℝ) ^ (A + η₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
    rw [← h2]; exact pow_le_pow_left₀ (by positivity) h1 2

/-- **Primes in almost every class.** Let `A ≥ 2`, `B ≥ 0` and `C ≥ 0` with `CharDensity A B C`. For every `η > 0`
there are `K` and `c > 0` such that for every modulus `q ≥ 1` and every `x ≥ Kq^{A/2+η}`, all the reduced classes
mod `q` but at most `Kφ(q)x^{−c}` hold at least `x/(240φ(q) log x)` primes `p ≤ 10x log x`: `card_few_le` at
`η₀ = min(2η, 1/2)`. -/
theorem few_of_charDensity {A B C : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (x : ℝ), K * (q : ℝ) ^ (A / 2 + η) ≤ x →
      ((few q (10 * x * Real.log x) (x / (240 * q.totient * Real.log x))).card : ℝ) ≤
        K * q.totient * x ^ (-c) := by
  set η₀ := min (2 * η) (1 / 2) with hη₀
  have hη0 : 0 < η₀ := lt_min (by linarith) (by norm_num)
  have hη1 : η₀ ≤ 1 / 2 := min_le_right _ _
  have hη2 : η₀ / 2 ≤ η := by have := min_le_left (2 * η) (1 / 2); linarith
  refine ⟨max (10 ^ 7) (Kaa A B C η₀), c0 A η₀, c0_pos hA hη0, fun q _ x hx => ?_⟩
  obtain ⟨hx7, hqx1, hqx⟩ := hyps_of_le hA hη hη2 (le_max_left _ _) q hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx7
  have hxc : 0 ≤ x ^ (-c0 A η₀) := (Real.rpow_pos_of_pos hx0 _).le
  have hφ0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  refine (card_few_le hA hB hC hD hη0 hη1 q hx7 hqx1 hqx).trans ?_
  calc (q.totient : ℝ) * (Kaa A B C η₀ * x ^ (-c0 A η₀))
      ≤ (q.totient : ℝ) * (max (10 ^ 7) (Kaa A B C η₀) * x ^ (-c0 A η₀)) := by
        gcongr; exact le_max_right _ _
    _ = max (10 ^ 7) (Kaa A B C η₀) * q.totient * x ^ (-c0 A η₀) := by ring

open scoped Classical in
/-- **The least prime of almost every class.** Let `A ≥ 2`, `B ≥ 0` and `C ≥ 0` with `CharDensity A B C`. For every
`η > 0` there are `K` and `c > 0` such that for every modulus `q ≥ 1`, all the reduced classes mod `q` but at most
`Kφ(q)q^{−c}` hold a prime `p ≤ Kq^{A/2+η}`: `few_of_charDensity` at `x = K₂q^{A/2+η/2}`, where
`10x log x ≤ Kq^{A/2+η}` (`log q ≤ q^{η/2}/(η/2)`). -/
theorem least_prime_of_charDensity {A B C : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q],
      ((Finset.univ.filter fun a : ZMod q => IsUnit a ∧
        ∀ p : ℕ, p.Prime → (p : ZMod q) = a → K * (q : ℝ) ^ (A / 2 + η) < p).card : ℝ) ≤
        K * q.totient * (q : ℝ) ^ (-c) := by
  obtain ⟨K₁, c, hc, h⟩ := few_of_charDensity hA hB hC hD (half_pos hη)
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = max K₁ (10 ^ 7) := ⟨_, rfl⟩
  have hK₂7 : (10 : ℝ) ^ 7 ≤ K₂ := by rw [hK₂]; exact le_max_right _ _
  have hK₁₂ : K₁ ≤ K₂ := by rw [hK₂]; exact le_max_left _ _
  have hK₂0 : 0 < K₂ := lt_of_lt_of_le (by norm_num) hK₂7
  have hK₂1 : (1 : ℝ) ≤ K₂ := le_trans (by norm_num) hK₂7
  have hlK : 0 ≤ Real.log K₂ := Real.log_nonneg hK₂1
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = A / 2 + η / 2 := ⟨_, rfl⟩
  have he1 : 1 ≤ e := by rw [he]; linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.log K₂ + e / (η / 2) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    have : 0 ≤ e / (η / 2) := div_nonneg (by linarith) (by linarith)
    rw [hR]; linarith
  have hKR0 : 0 ≤ 10 * K₂ * R := by positivity
  refine ⟨max K₁ (10 * K₂ * R), c, hc, fun q _ => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hφ0 : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = K₂ * (q : ℝ) ^ e := ⟨_, rfl⟩
  have hqe1 : 1 ≤ (q : ℝ) ^ e := Real.one_le_rpow hq1 (by linarith)
  have hqe0 : 0 < (q : ℝ) ^ e := by linarith
  have hxK : K₁ * (q : ℝ) ^ (A / 2 + η / 2) ≤ x := by
    rw [hx, ← he]; exact mul_le_mul_of_nonneg_right hK₁₂ hqe0.le
  have hx7 : (10 : ℝ) ^ 7 ≤ x := by rw [hx]; exact le_trans hK₂7 (le_mul_of_one_le_right hK₂0.le hqe1)
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx7
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx7
  have hlx0 : 0 < Real.log x := Real.log_pos hx1
  have hqx : (q : ℝ) ≤ x := by
    calc (q : ℝ) = (q : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (q : ℝ) ^ e := Real.rpow_le_rpow_of_exponent_le hq1 he1
      _ ≤ x := by rw [hx]; exact le_mul_of_one_le_left hqe0.le hK₂1
  -- `10x log x ≤ 10K₂R q^{A/2+η}`
  have hY : 10 * x * Real.log x ≤ 10 * K₂ * R * (q : ℝ) ^ (A / 2 + η) := by
    have hlogq : Real.log q ≤ (q : ℝ) ^ (η / 2) / (η / 2) := Real.log_le_rpow_div hq0.le (half_pos hη)
    have hqη1 : 1 ≤ (q : ℝ) ^ (η / 2) := Real.one_le_rpow hq1 (half_pos hη).le
    have hlx : Real.log x = Real.log K₂ + e * Real.log q := by
      rw [hx, Real.log_mul hK₂0.ne' hqe0.ne', Real.log_rpow hq0]
    have hlx2 : Real.log x ≤ R * (q : ℝ) ^ (η / 2) := by
      have h1 : e * Real.log q ≤ e * ((q : ℝ) ^ (η / 2) / (η / 2)) :=
        mul_le_mul_of_nonneg_left hlogq (by linarith)
      have h2 : Real.log K₂ ≤ Real.log K₂ * (q : ℝ) ^ (η / 2) := le_mul_of_one_le_right hlK hqη1
      have h3 : (Real.log K₂ + e / (η / 2)) * (q : ℝ) ^ (η / 2) =
          Real.log K₂ * (q : ℝ) ^ (η / 2) + e * ((q : ℝ) ^ (η / 2) / (η / 2)) := by ring
      rw [hlx, hR]; linarith
    have hqpow : (q : ℝ) ^ e * (q : ℝ) ^ (η / 2) = (q : ℝ) ^ (A / 2 + η) := by
      rw [← Real.rpow_add hq0]; congr 1; rw [he]; ring
    calc 10 * x * Real.log x ≤ 10 * x * (R * (q : ℝ) ^ (η / 2)) :=
          mul_le_mul_of_nonneg_left hlx2 (by positivity)
      _ = 10 * K₂ * R * ((q : ℝ) ^ e * (q : ℝ) ^ (η / 2)) := by rw [hx]; ring
      _ = 10 * K₂ * R * (q : ℝ) ^ (A / 2 + η) := by rw [hqpow]
  -- a class with no small prime has few primes
  have hm : 0 < x / (240 * q.totient * Real.log x) :=
    div_pos hx0 (mul_pos (mul_pos (by norm_num) hφ0) hlx0)
  have hqA0 : 0 ≤ (q : ℝ) ^ (A / 2 + η) := Real.rpow_nonneg hq0.le _
  have hsub : (Finset.univ.filter fun a : ZMod q => IsUnit a ∧ ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
      max K₁ (10 * K₂ * R) * (q : ℝ) ^ (A / 2 + η) < p) ⊆
      few q (10 * x * Real.log x) (x / (240 * q.totient * Real.log x)) := by
    intro a ha
    obtain ⟨-, hu, hno⟩ := Finset.mem_filter.1 ha
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, ?_⟩
    have hcnt : cnt q a (10 * x * Real.log x) = 0 := by
      rw [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro p hp ⟨hpp, hpa⟩
      have h1 := hno p hpp hpa
      have h2 : (p : ℝ) ≤ 10 * x * Real.log x :=
        (Nat.le_floor_iff (by positivity)).1 (Finset.mem_Ioc.1 hp).2
      have h3 : 10 * K₂ * R * (q : ℝ) ^ (A / 2 + η) ≤ max K₁ (10 * K₂ * R) * (q : ℝ) ^ (A / 2 + η) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hqA0
      linarith
    rw [hcnt, Nat.cast_zero]; exact hm
  have hxc : x ^ (-c) ≤ (q : ℝ) ^ (-c) := Real.rpow_le_rpow_of_nonpos hq0 hqx (by linarith)
  have hxc0 : 0 ≤ x ^ (-c) := (Real.rpow_pos_of_pos hx0 _).le
  calc ((Finset.univ.filter fun a : ZMod q => IsUnit a ∧ ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
        max K₁ (10 * K₂ * R) * (q : ℝ) ^ (A / 2 + η) < p).card : ℝ)
      ≤ ((few q (10 * x * Real.log x) (x / (240 * q.totient * Real.log x))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ K₁ * q.totient * x ^ (-c) := h q x hxK
    _ ≤ max K₁ (10 * K₂ * R) * q.totient * x ^ (-c) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hφ0.le) hxc0
    _ ≤ max K₁ (10 * K₂ * R) * q.totient * (q : ℝ) ^ (-c) :=
        mul_le_mul_of_nonneg_left hxc (mul_nonneg (le_trans hKR0 (le_max_right _ _)) hφ0.le)

/-- The constant of `meanSq_le`. -/
def Kms (A B C η₀ : ℝ) : ℝ := 576 * Mstar (dL A η₀) * Ktot A B C η₀ / c0 A η₀

open scoped Classical in
/-- **The mean square of the primes mod `q`, at `x`.** Under the hypotheses of `card_few_le`,
`Σ_{(a, q) = 1} (φ(q)S(x; q, a) − S₀)² ≤ Kms·φ(q)·x^{−c₀}·S₀²` (`variance_le`, `sum_sq_le`, `S0_ge`). -/
theorem meanSq_le {A B C η₀ : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2) (q : ℕ) [NeZero q] {x : ℝ} (hx : 10 ^ 7 ≤ x) (hqx1 : (q : ℝ) ≤ x)
    (hqx : (q : ℝ) ^ (A + η₀) ≤ x ^ 2) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a), ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 ≤
      (q.totient : ℝ) * (Kms A B C η₀ * x ^ (-c0 A η₀)) * S0 q x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hφ0 : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hS0 := S0_ge q hx hqx1
  have hc0 : 0 < c0 A η₀ := c0_pos hA hη0
  have hM0 : 0 < Mstar (dL A η₀) := Mstar_pos (dL_pos hA hη0) (dL_le hA hη1)
  have hKt0 : 0 ≤ Ktot A B C η₀ := Ktot_nonneg hA hB hC hη0 hη1
  have hV := variance_le q hx0
  have hsq := mul_le_mul_of_nonneg_left (sum_sq_le hA hB hC hD hη0 hη1 q hx3 hqx) hφ0.le
  have hlm := log_mul_rpow_le hq1 hqx1 (by linarith : (2 : ℝ) ≤ x) hc0
  have hMK : 0 ≤ (q.totient : ℝ) * (2 * Mstar (dL A η₀) * Ktot A B C η₀) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hlm hMK
  have hx2 : x ^ 2 ≤ 144 * S0 q x ^ 2 := by
    have h : x ^ 2 ≤ (12 * S0 q x) ^ 2 := pow_le_pow_left₀ hx0.le (by linarith) 2
    linarith [mul_pow 12 (S0 q x) 2]
  have hK0 : 0 ≤ (q.totient : ℝ) * (4 * Mstar (dL A η₀) * Ktot A B C η₀ / c0 A η₀ * x ^ (-c0 A η₀)) := by
    have : 0 < x ^ (-c0 A η₀) := Real.rpow_pos_of_pos hx0 _
    positivity
  calc ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a), ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2
      ≤ (q.totient : ℝ) * (2 * (Mstar (dL A η₀) * Real.log (q + 2)) *
          (Ktot A B C η₀ * (x ^ 2) ^ (1 - c0 A η₀))) := hV.trans hsq
    _ = (q.totient : ℝ) * (2 * Mstar (dL A η₀) * Ktot A B C η₀) *
          (Real.log (q + 2) * (x ^ 2) ^ (1 - c0 A η₀)) := by ring
    _ ≤ (q.totient : ℝ) * (2 * Mstar (dL A η₀) * Ktot A B C η₀) *
          (2 / c0 A η₀ * (x ^ 2 * x ^ (-c0 A η₀))) := h1
    _ = (q.totient : ℝ) * (4 * Mstar (dL A η₀) * Ktot A B C η₀ / c0 A η₀ * x ^ (-c0 A η₀)) * x ^ 2 := by
        field_simp; ring
    _ ≤ (q.totient : ℝ) * (4 * Mstar (dL A η₀) * Ktot A B C η₀ / c0 A η₀ * x ^ (-c0 A η₀)) *
          (144 * S0 q x ^ 2) := mul_le_mul_of_nonneg_left hx2 hK0
    _ = (q.totient : ℝ) * (Kms A B C η₀ * x ^ (-c0 A η₀)) * S0 q x ^ 2 := by rw [Kms]; field_simp; ring

open scoped Classical in
/-- **The mean square of the primes mod `q`.** Let `A ≥ 2`, `B ≥ 0` and `C ≥ 0` with `CharDensity A B C`. For every
`η > 0` there are `K` and `c > 0` such that for every modulus `q ≥ 1` and every `x ≥ Kq^{A/2+η}`, `S₀(x; q) > 0` and
`Σ_{(a, q) = 1} (φ(q)S(x; q, a) − S₀)² ≤ Kφ(q)x^{−c}S₀²`: the mean over the reduced classes of the squared relative
deviation of `S(x; q, a)` from its mean `S₀/φ(q)` is at most `Kx^{−c}`. -/
theorem meanSq_of_charDensity {A B C : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (x : ℝ), K * (q : ℝ) ^ (A / 2 + η) ≤ x →
      0 < S0 q x ∧
      ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a), ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 ≤
        K * q.totient * x ^ (-c) * S0 q x ^ 2 := by
  set η₀ := min (2 * η) (1 / 2) with hη₀
  have hη0 : 0 < η₀ := lt_min (by linarith) (by norm_num)
  have hη1 : η₀ ≤ 1 / 2 := min_le_right _ _
  have hη2 : η₀ / 2 ≤ η := by have := min_le_left (2 * η) (1 / 2); linarith
  refine ⟨max (10 ^ 7) (Kms A B C η₀), c0 A η₀, c0_pos hA hη0, fun q _ x hx => ?_⟩
  obtain ⟨hx7, hqx1, hqx⟩ := hyps_of_le hA hη hη2 (le_max_left _ _) q hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx7
  have hS0 := S0_ge q hx7 hqx1
  have hS : 0 < S0 q x := lt_of_lt_of_le (by positivity) hS0
  have hxc : 0 ≤ x ^ (-c0 A η₀) := (Real.rpow_pos_of_pos hx0 _).le
  have hφ0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  refine ⟨hS, (meanSq_le hA hB hC hD hη0 hη1 q hx7 hqx1 hqx).trans ?_⟩
  have h1 : (q.totient : ℝ) * (Kms A B C η₀ * x ^ (-c0 A η₀)) ≤
      max (10 ^ 7) (Kms A B C η₀) * q.totient * x ^ (-c0 A η₀) := by
    have := mul_le_mul_of_nonneg_right (le_max_right ((10 : ℝ) ^ 7) (Kms A B C η₀)) (mul_nonneg hφ0 hxc)
    linarith
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

/-- **The entropy of the primes mod `q`.** Let `A ≥ 2`, `B ≥ 0` and `C ≥ 0` with `CharDensity A B C`. For every
`η > 0` there are `K` and `c > 0` such that for every modulus `q ≥ 1` and every `x ≥ Kq^{A/2+η}`,
`H(x; q) ≥ log φ(q) − Kx^{−c}`: the residue mod `q` of an integer `n` drawn with probability proportional to
`Λ(n)e^{−n/x}` (among those prime to `q`) is within `Kx^{−c}`, in relative entropy, of the uniform distribution on
the reduced classes (`entropy_ge`, `meanSq_of_charDensity`). -/
theorem entropy_of_charDensity {A B C : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : CharDensity A B C)
    {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (x : ℝ), K * (q : ℝ) ^ (A / 2 + η) ≤ x →
      Real.log q.totient - K * x ^ (-c) ≤ entropy q x := by
  classical
  obtain ⟨K, c, hc, h⟩ := meanSq_of_charDensity hA hB hC hD hη
  refine ⟨K, c, hc, fun q _ x hx => ?_⟩
  obtain ⟨hS, hV⟩ := h q x hx
  have hφ0 : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have hdiv : (∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
      ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2) / (q.totient * S0 q x ^ 2) ≤ K * x ^ (-c) := by
    rw [div_le_iff₀ (by positivity)]
    calc ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a), ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2
        ≤ K * q.totient * x ^ (-c) * S0 q x ^ 2 := hV
      _ = K * x ^ (-c) * (q.totient * S0 q x ^ 2) := by ring
  have := entropy_ge q hS
  linarith

/-! ### The curve `g7d`: the exponent `1.1667` -/

/-- **Primes in almost every class, with no hypothesis.** For every `η > 0` there are `K` and `c > 0` such that for
every modulus `q ≥ 1` and every `x ≥ Kq^{11667/10000+η}`, all the reduced classes mod `q` but at most
`Kφ(q)x^{−c}` hold at least `x/(240φ(q) log x)` primes `p ≤ 10x log x`: `few_of_charDensity` at
`LinnikG7.charDensity_g7d`. -/
theorem few_g7d {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (x : ℝ), K * (q : ℝ) ^ (11667 / 10000 + η) ≤ x →
      ((few q (10 * x * Real.log x) (x / (240 * q.totient * Real.log x))).card : ℝ) ≤
        K * q.totient * x ^ (-c) := by
  obtain ⟨C, hC0, hD⟩ := LinnikG7.charDensity_g7d
  obtain ⟨K, c, hc, h⟩ := few_of_charDensity (by norm_num) (by norm_num) hC0 hD hη
  refine ⟨K, c, hc, fun q _ x hx => h q x ?_⟩
  rwa [show (11667 / 5000 : ℝ) / 2 + η = 11667 / 10000 + η by ring]

open scoped Classical in
/-- **The least prime of almost every class, with no hypothesis.** For every `η > 0` there are `K` and `c > 0` such
that for every modulus `q ≥ 1`, all the reduced classes mod `q` but at most `Kφ(q)q^{−c}` hold a prime
`p ≤ Kq^{11667/10000+η}`: Linnik's exponent for almost every class is at most `1.1667`. -/
theorem least_prime_g7d {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q],
      ((Finset.univ.filter fun a : ZMod q => IsUnit a ∧
        ∀ p : ℕ, p.Prime → (p : ZMod q) = a → K * (q : ℝ) ^ (11667 / 10000 + η) < p).card : ℝ) ≤
        K * q.totient * (q : ℝ) ^ (-c) := by
  obtain ⟨C, hC0, hD⟩ := LinnikG7.charDensity_g7d
  obtain ⟨K, c, hc, h⟩ := least_prime_of_charDensity (by norm_num) (by norm_num) hC0 hD hη
  refine ⟨K, c, hc, fun q _ => ?_⟩
  have := h q
  rwa [show (11667 / 5000 : ℝ) / 2 + η = 11667 / 10000 + η by ring] at this

open scoped Classical in
/-- **The mean square of the primes mod `q`, with no hypothesis.** For every `η > 0` there are `K` and `c > 0` such
that for every modulus `q ≥ 1` and every `x ≥ Kq^{11667/10000+η}`, `S₀(x; q) > 0` and
`Σ_{(a, q) = 1} (φ(q)S(x; q, a) − S₀)² ≤ Kφ(q)x^{−c}S₀²`. -/
theorem meanSq_g7d {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (x : ℝ), K * (q : ℝ) ^ (11667 / 10000 + η) ≤ x →
      0 < S0 q x ∧
      ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a), ((q.totient : ℝ) * SAP q a x - S0 q x) ^ 2 ≤
        K * q.totient * x ^ (-c) * S0 q x ^ 2 := by
  obtain ⟨C, hC0, hD⟩ := LinnikG7.charDensity_g7d
  obtain ⟨K, c, hc, h⟩ := meanSq_of_charDensity (by norm_num) (by norm_num) hC0 hD hη
  refine ⟨K, c, hc, fun q _ x hx => h q x ?_⟩
  rwa [show (11667 / 5000 : ℝ) / 2 + η = 11667 / 10000 + η by ring]

/-- **The entropy of the primes mod `q`, with no hypothesis.** For every `η > 0` there are `K` and `c > 0` such that
for every modulus `q ≥ 1` and every `x ≥ Kq^{11667/10000+η}`, `H(x; q) ≥ log φ(q) − Kx^{−c}`. -/
theorem entropy_g7d {η : ℝ} (hη : 0 < η) :
    ∃ K c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (x : ℝ), K * (q : ℝ) ^ (11667 / 10000 + η) ≤ x →
      Real.log q.totient - K * x ^ (-c) ≤ entropy q x := by
  obtain ⟨C, hC0, hD⟩ := LinnikG7.charDensity_g7d
  obtain ⟨K, c, hc, h⟩ := entropy_of_charDensity (by norm_num) (by norm_num) hC0 hD hη
  refine ⟨K, c, hc, fun q _ x hx => h q x ?_⟩
  rwa [show (11667 / 5000 : ℝ) / 2 + η = 11667 / 10000 + η by ring]

end LinnikAlmostAll
