/-
# Mertens' function twisted by a character, uniformly in the modulus

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `η > 0` there is `C` such that `|Σ_{n≤X} χ(n)μ(n)| ≤ C(q + 2)^η X^{11/12+η}` for every
modulus `q ≥ 1`, every Dirichlet character `χ ≠ 1` mod `q` and every `X ≥ 1` (`norm_sum_le`). So for one `χ ≠ 1`,
`Σ_{n≤X} χ(n)μ(n) = O(X^{11/12+η})` for every `η > 0` (`isBigO`), with no hypothesis. This is the Möbius bound for
one character, resting on the Lindelöf bound.

* `LSeries_fχμ`: `Σ χ(n)μ(n)n^{−s} = 1/L(s, χ)` on `Re s > 1` (Mathlib's `DirichletCharacter.LSeries.mul_mu_eq_one`).
* `norm_sum_le_of`: the argument (`MertensExponent.mertens_isBigO_of_zeroFree`) for any `F` with a Lindelöf bound.
  Let `θ > 0`, `η > 0`, `θ + η ≤ 1` and `θ' = θ + η/4`. If `|f(n)| ≤ 1`, `L(f, s) = F(s)` on `Re s > 1`, and `F` is
  holomorphic on `Re s ≥ θ'` with `|F(σ + it)| ≤ A(|t| + 4)^{η/8}` there, then `|Σ_{n≤X} f(n)| ≤ (CA + 4)X^{θ+η}`,
  with `C` depending on `θ` and `η` only. `SmoothPerron.smoothedSum_eq_verticalIntegral_left` moves the smoothed
  Perron integral to `Re s = θ'`, where `SmoothPerron.mellin_le_geom` (with `κ = η/4`) and the bound give
  `O(Aε^{−κ}X^{θ'})`. The same bound, with `η/8 ≤ 1` and `|t| + 4 ≤ 5|t|`, is the linear growth on `θ' ≤ σ ≤ 2`,
  `|t| ≥ 1`, that the contour shift needs. `SmoothPerron.norm_smoothedSum_sub_le` costs `3 log 2 · εX + 1`, and
  `ε = X^{θ'−1}`.
* `norm_sum_le`: `norm_sum_le_of` at `θ = 11/12` and `η₀ = min(η, 1/24)` with `F = 1/L(·, χ)`, which is holomorphic
  on `Re s > 11/12` by `LinnikLindelof.LFunction_ne_zero`, and the inverse half of `LinnikLindelof.lindelof`
  (`1/|L(σ + it, χ)| ≤ C₀((q + 2)(|t| + 4))^{η₀/8}`), so that `A = C₀(q + 2)^{η₀/8}`.
-/
import LinnikLindelof

open Complex Set Real Filter Topology MeasureTheory Asymptotics

local notation (name := mellintransformMC) "𝓜" => mellin

noncomputable section

namespace MertensChi

open SmoothPerron DirichletCharacter

/-- The coefficients `χ(n)μ(n)`. -/
abbrev fχμ {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  fun n ↦ χ n * (ArithmeticFunction.moebius n : ℂ)

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
lemma fχμ_zero (χ : DirichletCharacter ℂ q) : fχμ χ 0 = 0 := by simp [fχμ]

omit [NeZero q] in
lemma norm_fχμ_le (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖fχμ χ n‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_intCast]
  have h1 := DirichletCharacter.norm_le_one χ n
  have h2 : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc ‖χ n‖ * |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- `L(χμ, s) = 1/L(s, χ)` on `Re s > 1` (Mathlib's `LSeries.mul_mu_eq_one`). -/
lemma LSeries_fχμ (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fχμ χ) s = (LFunction χ s)⁻¹ := by
  have hm := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [← LFunction_eq_LSeries χ hs] at hm
  exact (inv_eq_of_mul_eq_one_right hm).symm

omit [NeZero q] in
lemma LSeriesSummable_fχμ (χ : DirichletCharacter ℂ q) : LSeriesSummable (fχμ χ) ((2 : ℝ) : ℂ) :=
  DirichletCharacter.LSeriesSummable_mul χ
    (ArithmeticFunction.LSeriesSummable_moebius_iff.2 (by norm_num))

/-- **Perron's formula with a Lindelöf bound.** Let `θ > 0`, `η > 0` and `θ + η ≤ 1`. There is `C ≥ 0` such that for
every `f : ℕ → ℂ` with `f(0) = 0` and `|f(n)| ≤ 1` whose Dirichlet series is `F(s)` on `Re s > 1`, where `F` is
holomorphic on `Re s ≥ θ + η/4` with `|F(σ + it)| ≤ A(|t| + 4)^{η/8}` there, `|Σ_{n≤X} f(n)| ≤ (CA + 4)X^{θ+η}` for
every `X ≥ 1`. -/
theorem norm_sum_le_of {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hθη : θ + η ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℕ → ℂ) (F : ℂ → ℂ) (A : ℝ), 0 ≤ A → f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) →
      LSeriesSummable f ((2 : ℝ) : ℂ) → (∀ s : ℂ, 1 < s.re → LSeries f s = F s) →
      (∀ s : ℂ, θ + η / 4 ≤ s.re → DifferentiableAt ℂ F s) →
      (∀ σ t : ℝ, θ + η / 4 ≤ σ → ‖F (σ + t * I)‖ ≤ A * (|t| + 4) ^ (η / 8)) →
      ∀ X : ℝ, 1 ≤ X → ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ ≤ (C * A + 4) * X ^ (θ + η) := by
  set θ' : ℝ := θ + η / 4 with hθ'def
  set κ : ℝ := η / 4 with hκdef
  set ε₁ : ℝ := η / 8 with hε₁def
  have hθ'1 : θ' < 1 := by linarith
  have hθ'0 : 0 < θ' := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hκ1 : κ ≤ 1 := by linarith
  have hε₁ : 0 < ε₁ := by linarith
  have hε₁1 : ε₁ ≤ 1 := by linarith
  obtain ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have diffν : ContDiff ℝ 1 ν := ContDiffν.of_le (by simp)
  have νnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have mass_one : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨KM, hKM0, hKM⟩ := mellin_le_geom diffν ν_supp hκ0 hκ1 hθ'0 hθ'1.le
  set r : ℝ := 1 + κ - ε₁ with hrdef
  have hr : 1 < r := by linarith
  have hIr : Integrable fun t : ℝ ↦ (1 + |t|) ^ (-r) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simp; linarith)
    simpa only [Real.norm_eq_abs] using this
  set Ir : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hIrdef
  have hIr0 : 0 ≤ Ir := integral_nonneg fun t ↦ by positivity
  refine ⟨4 ^ ε₁ * KM * Ir, by positivity, fun f F A hA hf0 hf1 hfs hLF hFd hFb X hX ↦ ?_⟩
  have hC0' : 0 ≤ 4 ^ ε₁ * KM * Ir * A + 4 := by positivity
  -- `X = 1`
  rcases eq_or_lt_of_le hX with hX1 | hX1
  · subst hX1
    have hs : ∑ n ∈ Finset.Icc 1 ⌊(1 : ℝ)⌋₊, f n = f 1 := by simp
    rw [hs, Real.one_rpow, mul_one]
    linarith [hf1 1, show 0 ≤ 4 ^ ε₁ * KM * Ir * A by positivity]
  have Xpos : 0 < X := by linarith
  set K₁ : ℝ := A * 4 ^ ε₁ with hK₁def
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hline : ∀ t : ℝ, ‖F (θ' + t * I)‖ ≤ K₁ * (1 + |t|) ^ ε₁ := by
    intro t
    refine (hFb θ' t le_rfl).trans ?_
    have h1 : |t| + 4 ≤ 4 * (1 + |t|) := by linarith [abs_nonneg t]
    calc A * (|t| + 4) ^ ε₁ ≤ A * (4 * (1 + |t|)) ^ ε₁ := by gcongr
      _ = K₁ * (1 + |t|) ^ ε₁ := by
          rw [hK₁def, Real.mul_rpow (by norm_num) (by positivity)]; ring
  have hgrowth : ∀ σ t : ℝ, θ' ≤ σ → σ ≤ 2 → 1 ≤ |t| → ‖F (σ + t * I)‖ ≤ (5 * A) * |t| := by
    intro σ t hσ _ ht
    refine (hFb σ t hσ).trans ?_
    have hP1 : 1 ≤ |t| + 4 := by linarith [abs_nonneg t]
    calc A * (|t| + 4) ^ ε₁ ≤ A * (|t| + 4) := by
          gcongr
          exact (Real.rpow_le_rpow_of_exponent_le hP1 hε₁1).trans_eq (Real.rpow_one _)
      _ ≤ A * (5 * |t|) := by gcongr; linarith
      _ = (5 * A) * |t| := by ring
  have hcont : Continuous fun t : ℝ ↦ F (θ' + t * I) :=
    continuous_iff_continuousAt.2 fun t ↦ (hFd _ (by simp)).continuousAt.comp' (by fun_prop)
  set ε : ℝ := X ^ (θ' - 1) with hεdef
  have εpos : 0 < ε := Real.rpow_pos_of_pos Xpos _
  have ε_lt_one : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg hX1 (by linarith)
  -- the integrand on `Re s = θ'`
  have hpt : ∀ t : ℝ, ‖integrand ν ε X F (θ' + t * I)‖ ≤
      K₁ * KM * ε ^ (-κ) * X ^ θ' * (1 + |t|) ^ (-r) := by
    intro t
    rw [norm_integrand Xpos]
    have hre : ((θ' : ℂ) + t * I).re = θ' := by simp
    rw [hre]
    have h1 := hline t
    have h2 := hKM ε εpos ε_lt_one t
    have hpow : (1 + |t|) ^ ε₁ * (1 + |t|) ^ (-(1 + κ)) = (1 + |t|) ^ (-r) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      rw [hrdef]
      ring
    calc ‖F (θ' + t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (θ' + t * I)‖ * X ^ θ'
        ≤ (K₁ * (1 + |t|) ^ ε₁) * (KM * ε ^ (-κ) * (1 + |t|) ^ (-(1 + κ))) * X ^ θ' := by
          gcongr
      _ = K₁ * KM * ε ^ (-κ) * X ^ θ' * ((1 + |t|) ^ ε₁ * (1 + |t|) ^ (-(1 + κ))) := by ring
      _ = K₁ * KM * ε ^ (-κ) * X ^ θ' * (1 + |t|) ^ (-r) := by rw [hpow]
  have hint' : Integrable fun t : ℝ ↦ integrand ν ε X F (θ' + t * I) :=
    Integrable.mono' (hIr.const_mul (K₁ * KM * ε ^ (-κ) * X ^ θ'))
      (continuous_integrand_line hθ'0 hcont diffν νnonneg ν_supp mass_one εpos ε_lt_one
        Xpos).aestronglyMeasurable (Eventually.of_forall hpt)
  have hid := smoothedSum_eq_verticalIntegral_left hf0 hfs hLF hθ'0 (by linarith) hFd hgrowth diffν νnonneg
    ν_supp mass_one εpos ε_lt_one hX hint'
  have hsm : ‖smoothedSum ν ε X f‖ ≤ K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') := by
    rw [hid]
    calc _ ≤ ∫ t, K₁ * KM * ε ^ (-κ) * X ^ θ' * (1 + |t|) ^ (-r) :=
          norm_verticalIntegral'_le (hIr.const_mul _) hpt
      _ = K₁ * KM * ε ^ (-κ) * X ^ θ' * Ir := integral_const_mul _ _
      _ = K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') := by ring
  have hun := norm_smoothedSum_sub_le hf0 Xpos (B := 1) (fun n _ ↦ hf1 n) νnonneg ν_supp mass_one εpos
    ε_lt_one
  -- exponents
  have hεκ : ε ^ (-κ) * X ^ θ' ≤ X ^ (θ' + κ) := by
    rw [hεdef, ← Real.rpow_mul Xpos.le, ← Real.rpow_add Xpos]
    exact Real.rpow_le_rpow_of_exponent_le hX (by nlinarith)
  have hεX : ε * X = X ^ θ' := by
    rw [hεdef, ← Real.rpow_add_one Xpos.ne', sub_add_cancel]
  have hθκ : X ^ θ' ≤ X ^ (θ' + κ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have h1κ : 1 ≤ X ^ (θ' + κ) := Real.one_le_rpow hX (by linarith)
  have hfin : X ^ (θ' + κ) ≤ X ^ (θ + η) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n =
      smoothedSum ν ε X f - (smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n) := by ring
  rw [hsplit]
  calc ‖smoothedSum ν ε X f - (smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n)‖
      ≤ ‖smoothedSum ν ε X f‖ + ‖smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ := norm_sub_le _ _
    _ ≤ K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') + 1 * (3 * Real.log 2 * ε * X + 1) := add_le_add hsm hun
    _ = K₁ * KM * Ir * (ε ^ (-κ) * X ^ θ') + (3 * Real.log 2 * X ^ θ' + 1) := by
        rw [← hεX]
        ring
    _ ≤ K₁ * KM * Ir * X ^ (θ' + κ) + (3 * X ^ (θ' + κ) + X ^ (θ' + κ)) := by
        gcongr
        linarith
    _ = (4 ^ ε₁ * KM * Ir * A + 4) * X ^ (θ' + κ) := by rw [hK₁def]; ring
    _ ≤ (4 ^ ε₁ * KM * Ir * A + 4) * X ^ (θ + η) := mul_le_mul_of_nonneg_left hfin hC0'

/-- **Mertens' function twisted by a character, uniformly in the modulus.** For every `η > 0` there is `C`
such that for every modulus `q ≥ 1`, every Dirichlet character `χ ≠ 1` mod `q` and every `X ≥ 1`,
`|Σ_{n≤X} χ(n)μ(n)| ≤ C(q + 2)^η X^{11/12+η}`: `norm_sum_le_of` for `1/L(s, χ)`, whose Dirichlet series has
coefficients `χ(n)μ(n)`, with the Lindelöf bound `LinnikLindelof.lindelof` for `1/|L(s, χ)|`. -/
theorem norm_sum_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X : ℝ, 1 ≤ X →
      ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤
        C * ((q : ℝ) + 2) ^ η * X ^ (11 / 12 + η) := by
  set η₀ : ℝ := min η (1 / 24) with hη₀def
  have hη₀ : 0 < η₀ := lt_min hη (by norm_num)
  have hη₀η : η₀ ≤ η := min_le_left _ _
  have hη₀1 : η₀ ≤ 1 / 24 := min_le_right _ _
  obtain ⟨C, hC0, hC⟩ := norm_sum_le_of (θ := 11 / 12) (by norm_num) hη₀ (by linarith)
  obtain ⟨C₀, hC₀, hL⟩ := LinnikLindelof.lindelof (σ₀ := 11 / 12 + η₀ / 4) (by linarith)
    (by positivity : 0 < η₀ / 8)
  refine ⟨C * C₀ + 4, fun q _ χ hχ X hX ↦ ?_⟩
  have hq2 : (1 : ℝ) ≤ (q : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  have hne : ∀ s : ℂ, 11 / 12 < s.re → LFunction χ s ≠ 0 := fun s hs ↦
    LinnikLindelof.LFunction_ne_zero hχ hs
  have h := hC (fχμ χ) (fun s ↦ (LFunction χ s)⁻¹) (C₀ * ((q : ℝ) + 2) ^ (η₀ / 8)) (by positivity)
    (fχμ_zero χ) (norm_fχμ_le χ) (LSeriesSummable_fχμ χ) (fun s hs ↦ LSeries_fχμ χ hs)
    (fun s hs ↦ ((differentiable_LFunction hχ) s).inv (hne s (by linarith)))
    (fun σ t hσ ↦ by
      rw [norm_inv]
      refine (hL q χ hχ σ t hσ).2.trans_eq ?_
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring) X hX
  refine h.trans ?_
  have hqη : ((q : ℝ) + 2) ^ (η₀ / 8) ≤ ((q : ℝ) + 2) ^ η :=
    Real.rpow_le_rpow_of_exponent_le hq2 (by linarith)
  have hqη1 : 1 ≤ ((q : ℝ) + 2) ^ η := Real.one_le_rpow hq2 hη.le
  have hX' : X ^ (11 / 12 + η₀) ≤ X ^ (11 / 12 + η) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  calc (C * (C₀ * ((q : ℝ) + 2) ^ (η₀ / 8)) + 4) * X ^ (11 / 12 + η₀)
      ≤ (C * (C₀ * ((q : ℝ) + 2) ^ η) + 4 * ((q : ℝ) + 2) ^ η) * X ^ (11 / 12 + η) := by
        gcongr
        linarith
    _ = (C * C₀ + 4) * ((q : ℝ) + 2) ^ η * X ^ (11 / 12 + η) := by ring

/-- For one character `χ ≠ 1`: `Σ_{n≤X} χ(n)μ(n) = O(X^{11/12+η})` for every `η > 0` -/
theorem isBigO {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {η : ℝ} (hη : 0 < η) :
    (fun X : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, χ n * (ArithmeticFunction.moebius n : ℂ)) =O[atTop]
      fun X ↦ X ^ (11 / 12 + η) := by
  obtain ⟨C, hC⟩ := norm_sum_le hη
  refine IsBigO.of_bound (C * ((q : ℝ) + 2) ^ η) ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact hC q χ hχ X hX

end MertensChi

#print axioms MertensChi.LSeries_fχμ
#print axioms MertensChi.norm_sum_le_of
#print axioms MertensChi.norm_sum_le
#print axioms MertensChi.isBigO
