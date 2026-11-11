/-
# Type II families with an abstract polynomial part

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveFamily` bounds the sum over `𝒜 − ℬ/φ(q)` of a family: `m` in a set `S ⊆ (P, 2P]` with coefficients `a_m`, primes
with smooth weights, and sharp comparisons with pivots, given the route's Type II estimate for one polynomial. Its
argument uses `m` only through its value, its coefficient, its parts `φ_j(m)` of the forms, the sum of `|a_m|`, and one
bound: the Type II estimate at each frequency of the separated sum. This file is that argument with those five as
data: `m` runs over a finite set `Xs` of any type, with a value `nv m`, a coefficient `c_m` and parts `φ_j(m)`, and
the estimate is a hypothesis (`hbox`): for the coefficients `c_m` and `|c_m|`, every `ξ ∈ ℝ^J`, `κ ∈ ℝ` and heights
`|h_i| ≤ q^{1/100000}`,

`Σ_{χ≠1} |Σ_m c′_m e(κ + Σ_j ξ_jφ_j(m))χ(nv m)|·|∏_i Sp(χ, Q_i, h_i)| ≤ B₁`.

* `family_bound_gen` (Lemma 4′): the smooth family, as `SieveFamily.family_bound`.
* `Dsum_sharp_le_gen`, `sharp_explicit_gen` (Lemma 4″): sharp comparisons with pivots, as
  `SieveFamily.typeII_sharp_explicit`.
* `sharp_gen`: the asymptotic form, as `SieveFamily.typeII_sharp`: with `Σ|c_m| ≤ PA₀`, `∏ Q_i ≤ 2^{K₀}q^L/P` and
  `B₁ = A₀q^{L − 1/50000}`, there are `δ > 0` and `q₀` with `|A − B/φ(q)| ≤ A₀q^{L−δ}/φ(q)` for `q ≥ q₀`.

`SieveFamilyTwo` applies it to pairs `(m₁, m₂)`, where the estimate is Proposition 3′ in two variables. The proofs
are those of `SieveFamily`, whose lemmas on the cut-off, the pivots and the elementary bounds are used as they are.

The file imports `SieveFamily.lean`.
-/
import SieveFamily

open MeasureTheory Real Complex FourierTransform Finset SieveFamily

namespace SieveFamilyGen

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- The separated sum factors: `Σ_{m,p} w(m, p)e^{2πiΣ_jξ_jℓ_j(m,p)}` is the twisted `m`-sum times the twisted prime
sums. -/
theorem inner_factor_gen {ι : Type*} (χ : DirichletCharacter ℂ q) (f0 : ℝ → ℝ) (Xs : Finset ι) (nv : ι → ℕ)
    (cf : ι → ℂ) {K J : ℕ} (Q : ℕ → ℝ) (φ : Fin J → ι → ℝ) (e : Fin J → Fin K → ℝ) (ξ : Fin J → ℝ) :
    ∑ x ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
        (cf x.1 * χ (nv x.1) * ∏ i : Fin K, (χ (x.2 i) * (f0 (x.2 i / Q i) : ℂ))) *
          Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * ((φ j x.1 + ∑ i : Fin K, e j i * Real.log (x.2 i) : ℝ) : ℂ)) =
      (∑ m ∈ Xs, cf m * χ (nv m) * Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * φ j m)) *
        ∏ i : Fin K, ∑ p ∈ primesTo (Q i),
          χ p * (f0 (p / Q i) : ℂ) * Complex.exp (2 * π * I * (∑ j, ξ j * e j i) * Real.log p) := by
  rw [Finset.prod_univ_sum, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun p _ => ?_
  have key : (∑ j, ξ j * (φ j m + ∑ i : Fin K, e j i * Real.log (p i)) : ℝ) =
      ∑ j, ξ j * φ j m + ∑ i : Fin K, (∑ j, ξ j * e j i) * Real.log (p i) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j (i : Fin K) => ξ j * (e j i * Real.log (p i)))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hexp : Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * ((φ j m + ∑ i : Fin K, e j i * Real.log (p i) : ℝ) : ℂ)) =
      Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * φ j m) *
        ∏ i : Fin K, Complex.exp (2 * π * I * (∑ j, ξ j * e j i : ℝ) * Real.log (p i)) := by
    have h1 : (∑ j, (ξ j : ℂ) * ((φ j m + ∑ i : Fin K, e j i * Real.log (p i) : ℝ) : ℂ)) =
        (((∑ j, ξ j * (φ j m + ∑ i : Fin K, e j i * Real.log (p i)) : ℝ)) : ℂ) := by push_cast; rfl
    rw [h1, key, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    push_cast
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp]
  simp only [Finset.prod_mul_distrib]
  ring

/-- **The bound for a smooth family with an abstract polynomial part.** Let `m` run over a finite set `Xs` of any
type, with values `nv m`, coefficients `c_m` and forms `φ_j(m)`, and `K` primes over `Sp`'s ranges at the scales
`Q_i > 0` with the weights `f0(p_i/Q_i)`; and let `J` continuous integrable `g_j` with integrable `𝓕g_j` be applied
to the forms `ℓ_j(m, p) = φ_j(m) + Σ_i e_{ji} log p_i`, with `2π(Σ_j |e_{ji}|)T₀ ≤ q^η` for each `i`. Suppose that for
every `ξ ∈ ℝ^J` and all heights `|h_i| ≤ q^η` the sum over `χ ≠ 1` of
`|Σ_m c_m e(Σ_j ξ_jφ_j(m))χ(nv m)|·|∏_i Sp(χ, Q_i, h_i)|` is at most `B₁` (`hbox`). Then the sum over `χ ≠ 1` of the
family's twisted sums is at most `B₁∏_j ‖𝓕g_j‖₁`, plus the number of characters `χ ≠ 1` times
`Σ_m |c_m| ∏_i Σ_p |f0(p/Q_i)|` times `Σ_j (∫_{|t|>T₀} |𝓕g_j(t)| dt) ∏_{i≠j} ‖𝓕g_i‖₁`. -/
theorem family_bound_gen {ι : Type*} (Xs : Finset ι) (nv : ι → ℕ) (cf : ι → ℂ) {f0 : ℝ → ℝ} {K : ℕ} (Q : ℕ → ℝ)
    (hQpos : ∀ i : Fin K, 0 < Q i) {J : ℕ} (g : Fin J → ℝ → ℂ) (hgc : ∀ j, Continuous (g j))
    (hgi : ∀ j, Integrable (g j)) (hgf : ∀ j, Integrable (𝓕 (g j))) (φ : Fin J → ι → ℝ) (e : Fin J → Fin K → ℝ)
    (T₀ : ℝ) {η B₁ : ℝ} (hB₁0 : 0 ≤ B₁) (hT : ∀ i : Fin K, 2 * π * (∑ j, |e j i|) * T₀ ≤ (q : ℝ) ^ η)
    (hbox : ∀ (ξ : Fin J → ℝ) (hh : ℕ → ℝ), (∀ j < K, |hh j| ≤ (q : ℝ) ^ η) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∑ m ∈ Xs, cf m * Complex.exp (2 * π * I * ((∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ (nv m)‖ *
          ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (hh j)‖ ≤ B₁) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∑ m ∈ Xs, ∑ p ∈ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
          cf m * χ (nv m) * (∏ i : Fin K, χ (p i) * (f0 (p i / Q i) : ℂ)) *
            ∏ j, g j (φ j m + ∑ i : Fin K, e j i * Real.log (p i))‖ ≤
      B₁ * (∏ j, ∫ t, ‖𝓕 (g j) t‖) +
        (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card *
          ((∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin K, ∑ p ∈ primesTo (Q i), |f0 (p / Q i)|) *
          ∑ j, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (g j) t‖) t) *
            ∏ i ∈ Finset.univ.erase j, ∫ t, ‖𝓕 (g i) t‖ := by
  -- the separated sum
  set W : DirichletCharacter ℂ q → (Fin J → ℝ) → ℂ := fun χ ξ =>
    ∑ m ∈ Xs, cf m * χ (nv m) * Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * φ j m) with hWdef
  set B : DirichletCharacter ℂ q → (Fin J → ℝ) → Fin K → ℂ := fun χ ξ i =>
    ∑ p ∈ primesTo (Q i), χ p * (f0 (p / Q i) : ℂ) * Complex.exp (2 * π * I * (∑ j, ξ j * e j i) * Real.log p)
    with hBdef
  set F : DirichletCharacter ℂ q → (Fin J → ℝ) → ℂ := fun χ ξ => W χ ξ * ∏ i, B χ ξ i with hFdef
  have hsep : ∀ χ : DirichletCharacter ℂ q,
      ∑ m ∈ Xs, ∑ p ∈ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
        cf m * χ (nv m) * (∏ i : Fin K, χ (p i) * (f0 (p i / Q i) : ℂ)) *
          ∏ j, g j (φ j m + ∑ i : Fin K, e j i * Real.log (p i)) =
      ∫ ξ : Fin J → ℝ, (∏ j, 𝓕 (g j) (ξ j)) * F χ ξ := by
    intro χ
    rw [← Finset.sum_product']
    rw [SieveSep.sum_sep (Xs ×ˢ Fintype.piFinset (fun i : Fin K => primesTo (Q i)))
      (fun x => cf x.1 * χ (nv x.1) * ∏ i : Fin K, (χ (x.2 i) * (f0 (x.2 i / Q i) : ℂ)))
      (fun j x => φ j x.1 + ∑ i : Fin K, e j i * Real.log (x.2 i)) hgc hgi hgf]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [inner_factor_gen χ f0 Xs nv cf Q φ e ξ]
  -- continuity in `ξ`
  have hcont : ∀ χ : DirichletCharacter ℂ q, Continuous (F χ) := by
    intro χ
    have hW : Continuous (W χ) := continuous_finsetSum _ fun m _ => continuous_const.mul
      (Continuous.cexp (continuous_const.mul (continuous_finsetSum _ fun j _ =>
        (Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const)))
    have hB : ∀ i, Continuous fun ξ => B χ ξ i := fun i => continuous_finsetSum _ fun p _ =>
      continuous_const.mul (Continuous.cexp ((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const))).mul continuous_const))
    exact hW.mul (continuous_finsetProd _ fun i _ => hB i)
  -- the norms of the factors
  have hWnorm : ∀ χ : DirichletCharacter ℂ q, ∀ ξ, ‖W χ ξ‖ ≤ ∑ m ∈ Xs, ‖cf m‖ := by
    intro χ ξ
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul, norm_mul]
    have h1 := DirichletCharacter.norm_le_one χ ((nv m : ℕ) : ZMod q)
    have h2 : ‖Complex.exp (2 * π * I * ∑ j, (ξ j : ℂ) * φ j m)‖ = 1 := by
      have : 2 * π * I * ∑ j, (ξ j : ℂ) * φ j m = ((2 * π * ∑ j, ξ j * φ j m : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [h2, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) h1
  have hBnorm : ∀ χ : DirichletCharacter ℂ q, ∀ ξ i, ‖B χ ξ i‖ ≤ ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| := by
    intro χ ξ i
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, norm_mul]
    have h1 := DirichletCharacter.norm_le_one χ (p : ZMod q)
    have h2 : ‖Complex.exp (2 * π * I * (∑ j, ξ j * e j i) * Real.log p)‖ = 1 := by
      have : 2 * π * I * (∑ j, ξ j * e j i : ℝ) * Real.log p =
          ((2 * π * (∑ j, ξ j * e j i) * Real.log p : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [h2, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  -- the trivial bound
  set B₂ : ℝ := (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card *
    ((∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin K, ∑ p ∈ primesTo (Q i), |f0 (p / Q i)|) with hB₂def
  have hB₂0 : 0 ≤ B₂ := by positivity
  have hB₂ : ∀ ξ, ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖F χ ξ‖ ≤ B₂ := by
    intro ξ
    rw [hB₂def, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun χ _ => ?_
    rw [hFdef]
    simp only
    rw [norm_mul, norm_prod]
    exact mul_le_mul (hWnorm χ ξ) (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hBnorm χ ξ i)
      (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.sum_nonneg fun m _ => norm_nonneg _)
  -- the box
  have hB₁ : ∀ ξ : Fin J → ℝ, (∀ j, |ξ j| ≤ T₀) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖F χ ξ‖ ≤ B₁ := by
    intro ξ hξ
    set hh : ℕ → ℝ := fun j => if hj : j < K then -(2 * π * ∑ j', ξ j' * e j' ⟨j, hj⟩) else 0 with hhh
    have hheq : ∀ i : Fin K, hh i = -(2 * π * ∑ j', ξ j' * e j' i) := fun i => by
      simp [hhh, i.isLt]
    have hexp1 : ∀ r : ℝ, ‖Complex.exp (2 * π * I * (r : ℂ))‖ = 1 := fun r => by
      have : 2 * π * I * (r : ℂ) = ((2 * π * r : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hFeq : ∀ χ : DirichletCharacter ℂ q, ‖F χ ξ‖ =
        ‖∑ m ∈ Xs, cf m * Complex.exp (2 * π * I * ((∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ (nv m)‖ *
          ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (hh j)‖ := by
      intro χ
      rw [hFdef]
      simp only
      rw [norm_mul]
      congr 1
      · congr 1
        rw [hWdef]
        refine Finset.sum_congr rfl fun m _ => ?_
        push_cast
        ring
      · rw [norm_prod, norm_prod,
          ← Fin.prod_univ_eq_prod_range (fun j => ‖SieveWeight.Sp χ f0 (Q j) (hh j)‖)]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hBdef]
        simp only
        have h1 := sum_twist_eq χ f0 (hQpos i) (∑ j, ξ j * e j i)
        rw [h1, norm_mul, hheq i]
        have h2 : ‖Complex.exp (2 * π * I * ((∑ j, ξ j * e j i : ℝ) : ℂ) * (Real.log (Q i) : ℂ))‖ = 1 := by
          have : 2 * π * I * ((∑ j, ξ j * e j i : ℝ) : ℂ) * (Real.log (Q i) : ℂ) =
              2 * π * I * (((∑ j, ξ j * e j i) * Real.log (Q i) : ℝ) : ℂ) := by push_cast; ring
          rw [this, hexp1]
        rw [h2, one_mul]
    have hheight : ∀ j < K, |hh j| ≤ (q : ℝ) ^ η := by
      intro j hj
      have h2π : (0 : ℝ) < 2 * π := by positivity
      have hsum : |∑ j', ξ j' * e j' ⟨j, hj⟩| ≤ (∑ j', |e j' ⟨j, hj⟩|) * T₀ := by
        rw [Finset.sum_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j' _ => ?_)
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (hξ j') (abs_nonneg _)
      calc |hh j| = 2 * π * |∑ j', ξ j' * e j' ⟨j, hj⟩| := by
            rw [show hh j = -(2 * π * ∑ j', ξ j' * e j' ⟨j, hj⟩) by simp [hhh, hj], abs_neg, abs_mul,
              abs_of_pos h2π]
        _ ≤ 2 * π * ((∑ j', |e j' ⟨j, hj⟩|) * T₀) := mul_le_mul_of_nonneg_left hsum h2π.le
        _ = 2 * π * (∑ j', |e j' ⟨j, hj⟩|) * T₀ := by ring
        _ ≤ (q : ℝ) ^ η := hT ⟨j, hj⟩
    calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖F χ ξ‖
        = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖∑ m ∈ Xs, cf m * Complex.exp (2 * π * I * ((∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ (nv m)‖ *
              ‖∏ j ∈ Finset.range K, SieveWeight.Sp χ f0 (Q j) (hh j)‖ :=
          Finset.sum_congr rfl fun χ _ => hFeq χ
      _ ≤ B₁ := hbox ξ hh hheight
  have hfin := SieveSep.sep_bound (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)) F hcont hgf
    hB₁0 hB₂0 hB₁ hB₂
  calc _ = ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∫ ξ : Fin J → ℝ, (∏ j, 𝓕 (g j) (ξ j)) * F χ ξ‖ :=
        Finset.sum_congr rfl fun χ _ => by rw [hsep χ]
    _ ≤ _ := hfin


section SharpFamily

open SieveSmooth Classical

/-- **A sharp family, explicitly.** Let `a` be a unit, `Q_i > 0`, `0 ≤ f0 ≤ F₀` and `0 < θ ≤ 2Λ`. The tuples
`(m, x)` with `m ∈ Xs`, of value `nv m`, and `n + 1` primes `x_i` of `Sp`'s ranges, with weight `w = c_m ∏_i f0(x_i/Q_i)`, are cut by `J`
sharp comparisons `P_j`, where `P_j` holds when `ℓ_j(m, x) = φ_j(m) + Σ_i e_{ji} log x_i > 0` and implies `ℓ_j ≥ 0`. If
each `ℓ_j ≤ Λ` on the tuples and each comparison has a pivot prime with coefficient `±1`, then `|A − B/φ(q)|` of the
family is at most `φ(q)⁻¹` times the twisted sums of the smoothed family and of the `J` near-boundary families, plus
twice `φ(q)⁻¹` times the pivots' counts. -/
theorem Dsum_sharp_le_gen {ι : Type*} {a : ZMod q} (ha : IsUnit a) (Xs : Finset ι) (nv : ι → ℕ) (cf : ι → ℂ)
    {n : ℕ} (Q : ℕ → ℝ)
    (hQ : ∀ i : Fin (n + 1), 0 < Q i) {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀) {J : ℕ}
    (φ : Fin J → ι → ℝ) (e : Fin J → Fin (n + 1) → ℝ) (Pr : Fin J → ι → (Fin (n + 1) → ℕ) → Prop)
    {θ Λ : ℝ} (hθ : 0 < θ) (hθΛ : θ ≤ 2 * Λ)
    (hP : ∀ j m x, (0 < φ j m + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
      (Pr j m x → 0 ≤ φ j m + ∑ i, e j i * Real.log (x i)))
    (hΛ : ∀ j, ∀ m ∈ Xs, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
      φ j m + ∑ i, e j i * Real.log (x i) ≤ Λ)
    (piv : Fin J → Fin (n + 1)) (hpiv : ∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1) :
    ‖Dsum q a (Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
        (fun mx => nv mx.1 * ∏ i, mx.2 i)
        (fun mx => (cf mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) * ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ mx ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
            ((cf mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
              ∏ j, ((G θ Λ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i)) : ℝ) : ℂ)) * χ ((nv mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q)‖ +
        ∑ j, (2 * (q.totient : ℝ)⁻¹ * (F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
            ((∑ m ∈ Xs, ‖cf m‖) *
              ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i)))) +
          (q.totient : ℝ)⁻¹ * ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖∑ mx ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
              (((‖cf mx.1‖ * ∏ i, f0 (mx.2 i / Q i)) *
                G θ θ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i) + θ) : ℝ) : ℂ) * χ ((nv mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q)‖) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hsharp := norm_Dsum_sharp_le (q := q) (a := a) (Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
    (fun mx => nv mx.1 * ∏ i, mx.2 i) (fun mx => cf mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ))
    (fun j mx => if Pr j mx.1 mx.2 then 1 else 0)
    (fun j mx => G θ Λ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i)))
    (fun j mx => if mx ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)) then
      G θ θ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i) + θ) else 1)
    (fun j mx => by split_ifs <;> norm_num)
    (fun j mx => ⟨G_nonneg hθ hθΛ _, G_le_one _⟩)
    (fun j mx => by
      split_ifs with hp hmx hmx
      · rw [Finset.mem_product] at hmx
        have := abs_ind_sub_G_le hθ hΛ0 (hΛ j mx.1 hmx.1 mx.2 hmx.2) (Pr j mx.1 mx.2) (hP j mx.1 mx.2)
        rwa [ite_eq_left hp] at this
      · rw [abs_le]
        have h1 := G_nonneg hθ hθΛ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i))
        have h2 := G_le_one (θ := θ) (Λ := Λ) (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i))
        constructor <;> linarith
      · rw [Finset.mem_product] at hmx
        have := abs_ind_sub_G_le hθ hΛ0 (hΛ j mx.1 hmx.1 mx.2 hmx.2) (Pr j mx.1 mx.2) (hP j mx.1 mx.2)
        rwa [ite_eq_right hp] at this
      · rw [abs_le]
        have h1 := G_nonneg hθ hθΛ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i))
        have h2 := G_le_one (θ := θ) (Λ := Λ) (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i))
        constructor <;> linarith)
  have hw : ∀ (m : ι) (x : Fin (n + 1) → ℕ),
      ‖cf m * ∏ i : Fin (n + 1), (f0 (x i / Q i) : ℂ)‖ = ‖cf m‖ * ∏ i : Fin (n + 1), f0 (x i / Q i) := by
    intro m x
    rw [norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
  refine hsharp.trans (add_le_add (norm_Dsum_le ha _ _ _) (Finset.sum_le_sum fun j _ => add_le_add ?_ ?_))
  · -- the pivot count
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.sum_product]
    calc ∑ m ∈ Xs, ∑ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          ‖cf (m, x).1 * ∏ i, (f0 ((m, x).2 i / Q i) : ℂ)‖ *
            (if (m, x) ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)) then
              G θ θ (φ j (m, x).1 + ∑ i, e j i * Real.log ((m, x).2 i) + θ) else 1)
        = ∑ m ∈ Xs, ‖cf m‖ * ∑ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
            (∏ i, f0 (x i / Q i)) * G θ θ (φ j m + ∑ i, e j i * Real.log (x i) + θ) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [ite_eq_left (Finset.mem_product.2 ⟨hm, hx⟩), hw]
          ring
      _ ≤ ∑ m ∈ Xs, ‖cf m‖ * (F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
            ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i))) := by
          refine Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine pivot_sum_le (fun i => primesTo (Q i)) (piv j) (fun i y => f0 (y / Q i)) (fun i y => hf0 _)
            (fun x => G θ θ (φ j m + ∑ i, e j i * Real.log (x i) + θ)) fun z => ?_
          have hsplit : ∀ y : ℕ, φ j m + ∑ i, e j i * Real.log (((piv j).insertNth y z : Fin (n + 1) → ℕ) i) + θ =
              (φ j m + ∑ i : Fin n, e j ((piv j).succAbove i) * Real.log (z i)) +
                e j (piv j) * Real.log y + θ := by
            intro y
            rw [Fin.sum_univ_succAbove _ (piv j)]
            simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
            ring
          simp only [hsplit]
          exact pivot_term_le hf0 hF₀ hθ (hQ (piv j)) (hpiv j)
      _ = F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
            ((∑ m ∈ Xs, ‖cf m‖) *
              ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i))) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
  · -- the near-boundary families
    refine (norm_Dsum_le ha _ _ _).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun mx hmx => ?_
    rw [ite_eq_left hmx, hw]

end SharpFamily

omit [NeZero q] in
/-- The tuple form of a twisted family sum is the form of `family_bound`. -/
theorem tuple_sum_eq_gen {ι : Type*} (χ : DirichletCharacter ℂ q) (Xs : Finset ι) (nv : ι → ℕ) (cf : ι → ℂ)
    {K J : ℕ} (Q : ℕ → ℝ)
    (f0 : ℝ → ℝ) (g : Fin J → ℝ → ℂ) (ℓ : Fin J → ι → (Fin K → ℕ) → ℝ) :
    ∑ mx ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
        ((cf mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) * ∏ j, g j (ℓ j mx.1 mx.2)) *
          χ ((nv mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q) =
      ∑ m ∈ Xs, ∑ x ∈ Fintype.piFinset (fun i : Fin K => primesTo (Q i)),
        cf m * χ (nv m) * (∏ i : Fin K, χ (x i) * (f0 (x i / Q i) : ℂ)) * ∏ j, g j (ℓ j m x) := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.cast_mul, Nat.cast_prod, map_mul, map_prod, Finset.prod_mul_distrib]
  ring


section Explicit

open SieveSmooth Classical
open scoped ContDiff

/-- **A sharp family with an abstract polynomial part, explicitly.** Let `0 ≤ f0 ≤ F₀`, `a` a unit, `m` over a finite
set `Xs` with values `nv m`, coefficients `c_m` and forms `φ_j(m)`, `n + 1` primes at the scales `Q_i > 0`, and `J`
sharp comparisons as in `Dsum_sharp_le_gen`, with `0 < θ ≤ 1 ≤ Λ`, `ℓ_j ≤ Λ` on the family, pivots with coefficients
`±1`, `T₀ ≥ 1`, `k ≥ 2` and `2π(Σ_j |e_{ji}|)T₀ ≤ q^{1/100000}` for each `i`. Suppose that for the coefficients `c_m`
and `|c_m|`, every `ξ ∈ ℝ^J`, `κ ∈ ℝ` and all heights `|h_i| ≤ q^{1/100000}`, the sum over `χ ≠ 1` of
`|Σ_m c′_m e(κ + Σ_j ξ_jφ_j(m))χ(nv m)|·|∏_i Sp(χ, Q_i, h_i)|` is at most `B₁` (`hbox`). Then the `|A − B/φ(q)|` of the
sharp family is at most `φ(q)⁻¹(B₁(M^J + J·M̃) + φ(q)·Box·Jτ(M^J + 1))` plus twice `φ(q)⁻¹` times the pivots' counts,
with `M = massB θ Λ`, `M̃ = massB θ θ`, `τ = tailB θ T₀ k` and `Box = Σ|c_m| ∏_i Σ_p |f0(p/Q_i)|`. -/
theorem sharp_explicit_gen {ι : Type*} {f0 : ℝ → ℝ} (hf0nn : ∀ u, 0 ≤ f0 u) {F₀ : ℝ} (hF₀ : ∀ u, f0 u ≤ F₀)
    {a : ZMod q} (ha : IsUnit a) (Xs : Finset ι) (nv : ι → ℕ) (cf : ι → ℂ) (n : ℕ) (Q : ℕ → ℝ)
    (hQpos : ∀ i : Fin (n + 1), 0 < Q i) {J : ℕ} (φ : Fin J → ι → ℝ) (e : Fin J → Fin (n + 1) → ℝ)
    (Pr : Fin J → ι → (Fin (n + 1) → ℕ) → Prop)
    (hP : ∀ j m x, (0 < φ j m + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
      (Pr j m x → 0 ≤ φ j m + ∑ i, e j i * Real.log (x i)))
    {θ Λ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ j, ∀ m ∈ Xs, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
      φ j m + ∑ i, e j i * Real.log (x i) ≤ Λ)
    (piv : Fin J → Fin (n + 1)) (hpiv : ∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1)
    {T₀ : ℝ} {k : ℕ} (hT₀ : 1 ≤ T₀) (hk : 2 ≤ k) {B₁ : ℝ} (hB₁0 : 0 ≤ B₁)
    (hT : ∀ i : Fin (n + 1), 2 * π * (∑ j, |e j i|) * T₀ ≤ (q : ℝ) ^ (1 / 100000 : ℝ))
    (hbox : ∀ c' : ι → ℂ, (c' = cf ∨ c' = fun m => ((‖cf m‖ : ℝ) : ℂ)) → ∀ (ξ : Fin J → ℝ) (κ : ℝ) (hh : ℕ → ℝ),
      (∀ j < n + 1, |hh j| ≤ (q : ℝ) ^ (1 / 100000 : ℝ)) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∑ m ∈ Xs, c' m * Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ (nv m)‖ *
          ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ f0 (Q j) (hh j)‖ ≤ B₁) :
    ‖Dsum q a (Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
        (fun mx => nv mx.1 * ∏ i, mx.2 i)
        (fun mx => (cf mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
          ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
      (q.totient : ℝ)⁻¹ *
        (B₁ * (massB θ Λ ^ J + J * massB θ θ) +
          q.totient * ((∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)|) *
            (J * tailB θ T₀ k * massB θ Λ ^ J + J * tailB θ T₀ k)) +
        ∑ j, 2 * (q.totient : ℝ)⁻¹ * (F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
          ((∑ m ∈ Xs, ‖cf m‖) *
            ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i)))) := by
  have hθΛ : θ ≤ 2 * Λ := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hstep := Dsum_sharp_le_gen ha Xs nv cf Q hQpos hf0nn hF₀ φ e Pr hθ hθΛ hP hΛ piv hpiv
  refine hstep.trans ?_
  -- the bounds of the masses and tails
  set M := massB θ Λ with hMdef
  set Mt := massB θ θ with hMtdef
  set τ := tailB θ T₀ k with hτdef
  have hc₂ : 0 ≤ ∫ v, ‖iteratedDeriv 2 gc v‖ := integral_nonneg fun _ => norm_nonneg _
  have hM1 : 1 ≤ M := by
    rw [hMdef, massB]
    have : 0 ≤ (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π * θ) := by positivity
    nlinarith [Real.pi_gt_three]
  have hmass : ∫ t, ‖𝓕 (GC θ Λ) t‖ ≤ M := mass_GC_le hθ hθΛ
  have hmasst : ∫ t, ‖𝓕 (GC θ θ) t‖ ≤ Mt := mass_GC_le hθ (by linarith)
  have htail : ∀ Λ' : ℝ, 0 ≤ Λ' →
      ∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ') t‖) t ≤ τ := fun Λ' hΛ' =>
    tail_GC_le hθ hΛ' hk hT₀
  have hm0 : ∀ Λ' : ℝ, 0 ≤ ∫ t, ‖𝓕 (GC θ Λ') t‖ := fun Λ' => integral_nonneg fun _ => norm_nonneg _
  have ht0 : ∀ Λ' : ℝ, 0 ≤ ∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ') t‖) t :=
    fun Λ' => integral_nonneg fun _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  set Box := (∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| with hBox
  have hBox0 : 0 ≤ Box := by positivity
  have hcard := card_chars_le (q := q)
  have hτ0 : 0 ≤ τ := le_trans (ht0 Λ) (htail Λ hΛ0)
  -- the hypothesis on the box, for the smoothed family and for the near-boundary families
  have hbox₁ : ∀ (ξ : Fin J → ℝ) (hh : ℕ → ℝ), (∀ j < n + 1, |hh j| ≤ (q : ℝ) ^ (1 / 100000 : ℝ)) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∑ m ∈ Xs, cf m * Complex.exp (2 * π * I * ((∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ (nv m)‖ *
          ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ f0 (Q j) (hh j)‖ ≤ B₁ := by
    intro ξ hh hhh
    have h := hbox cf (Or.inl rfl) ξ 0 hh hhh
    simpa only [zero_add] using h
  have hbox₂ : ∀ (j : Fin J) (ξ : Fin 1 → ℝ) (hh : ℕ → ℝ),
      (∀ j < n + 1, |hh j| ≤ (q : ℝ) ^ (1 / 100000 : ℝ)) →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖∑ m ∈ Xs, ((‖cf m‖ : ℝ) : ℂ) *
            Complex.exp (2 * π * I * ((∑ j' : Fin 1, ξ j' * (φ j m + θ) : ℝ) : ℂ)) * χ (nv m)‖ *
          ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ f0 (Q j) (hh j)‖ ≤ B₁ := by
    intro j ξ hh hhh
    have h := hbox (fun m => ((‖cf m‖ : ℝ) : ℂ)) (Or.inr rfl) (Pi.single j (ξ 0)) (ξ 0 * θ) hh hhh
    have hsum : ∀ m, ξ 0 * θ + ∑ j', (Pi.single j (ξ 0) : Fin J → ℝ) j' * φ j' m =
        ∑ j' : Fin 1, ξ j' * (φ j m + θ) := by
      intro m
      rw [Fin.sum_univ_one, Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]
      ring
    simpa only [hsum] using h
  -- the smoothed family
  have hX : ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ‖∑ mx ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        ((cf mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
          ∏ j, ((G θ Λ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i)) : ℝ) : ℂ)) *
            χ ((nv mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q)‖ ≤
      B₁ * M ^ J +
        q.totient * Box * (J * τ * M ^ J) := by
    have hconv : ∀ χ : DirichletCharacter ℂ q,
        ∑ mx ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          ((cf mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
            ∏ j, ((G θ Λ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i)) : ℝ) : ℂ)) *
              χ ((nv mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q) =
        ∑ m ∈ Xs, ∑ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          cf m * χ (nv m) * (∏ i : Fin (n + 1), χ (x i) * (f0 (x i / Q i) : ℂ)) *
            ∏ j, GC θ Λ (φ j m + ∑ i : Fin (n + 1), e j i * Real.log (x i)) := by
      intro χ
      simp_rw [GC_eq_G]
      exact tuple_sum_eq_gen χ Xs nv cf Q f0 (fun _ u => (G θ Λ u : ℂ))
        (fun j m x => φ j m + ∑ i, e j i * Real.log (x i))
    simp_rw [hconv]
    refine (family_bound_gen Xs nv cf Q hQpos (fun _ => GC θ Λ)
      (fun _ => (contDiff_GC (n := 0)).continuous) (fun _ => integrable_GC hθ hΛ0)
      (fun _ => integrable_fourier_GC hθ hΛ0) φ e T₀ hB₁0 hT hbox₁).trans ?_
    refine add_le_add (mul_le_mul_of_nonneg_left (prod_masses_le _ (fun j => hm0 Λ) (fun j => hmass)) hB₁0) ?_
    have hS' := sum_tails_le (fun _ : Fin J => ∫ t, ‖𝓕 (GC θ Λ) t‖)
      (fun _ : Fin J => ∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) t)
      hM1 (fun j => hm0 Λ) (fun j => hmass) (fun j => ht0 Λ) (fun j => htail Λ hΛ0)
    have hS0 : 0 ≤ ∑ j : Fin J, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) t) *
        ∏ i ∈ Finset.univ.erase j, ∫ t, ‖𝓕 (GC θ Λ) t‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (ht0 Λ) (Finset.prod_nonneg fun i _ => hm0 Λ)
    calc ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) * Box *
          ∑ j : Fin J, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) t) *
            ∏ i ∈ Finset.univ.erase j, ∫ t, ‖𝓕 (GC θ Λ) t‖
        ≤ q.totient * Box * ∑ j : Fin J, (∫ t, Set.indicator {t : ℝ | T₀ < |t|} (fun t => ‖𝓕 (GC θ Λ) t‖) t) *
            ∏ i ∈ Finset.univ.erase j, ∫ t, ‖𝓕 (GC θ Λ) t‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hBox0) hS0
      _ ≤ q.totient * Box * (J * τ * M ^ J) := mul_le_mul_of_nonneg_left hS' (by positivity)
  -- the near-boundary families
  have hY : ∀ j, ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ‖∑ mx ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        (((‖cf mx.1‖ * ∏ i, f0 (mx.2 i / Q i)) *
          G θ θ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i) + θ) : ℝ) : ℂ) *
            χ ((nv mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q)‖ ≤
      B₁ * Mt +
        q.totient * Box * τ := by
    intro j
    have hconv : ∀ χ : DirichletCharacter ℂ q,
        ∑ mx ∈ Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          (((‖cf mx.1‖ * ∏ i, f0 (mx.2 i / Q i)) *
            G θ θ (φ j mx.1 + ∑ i, e j i * Real.log (mx.2 i) + θ) : ℝ) : ℂ) *
              χ ((nv mx.1 * ∏ i, mx.2 i : ℕ) : ZMod q) =
        ∑ m ∈ Xs, ∑ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
          (‖cf m‖ : ℂ) * χ (nv m) * (∏ i : Fin (n + 1), χ (x i) * (f0 (x i / Q i) : ℂ)) *
            ∏ _j' : Fin 1, GC θ θ ((φ j m + θ) + ∑ i : Fin (n + 1), e j i * Real.log (x i)) := by
      intro χ
      rw [← tuple_sum_eq_gen χ Xs nv (fun m => (‖cf m‖ : ℂ)) Q f0 (fun _ : Fin 1 => GC θ θ)
        (fun _ m x => (φ j m + θ) + ∑ i : Fin (n + 1), e j i * Real.log (x i))]
      refine Finset.sum_congr rfl fun mx _ => ?_
      rw [Fin.prod_univ_one, GC_eq_G]
      push_cast
      ring_nf
    simp_rw [hconv]
    have hT1 : ∀ i : Fin (n + 1), 2 * π * (∑ _j' : Fin 1, |e j i|) * T₀ ≤ (q : ℝ) ^ (1 / 100000 : ℝ) := by
      intro i
      refine le_trans ?_ (hT i)
      rw [Fin.sum_univ_one]
      have hle : |e j i| ≤ ∑ j', |e j' i| :=
        Finset.single_le_sum (f := fun j' => |e j' i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have hT0' : 0 ≤ T₀ := by linarith
      have h2π : 0 ≤ 2 * π := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle h2π) hT0'
    refine (family_bound_gen Xs nv (fun m => (‖cf m‖ : ℂ)) Q hQpos (fun _ : Fin 1 => GC θ θ)
      (fun _ => (contDiff_GC (n := 0)).continuous) (fun _ => integrable_GC hθ hθ.le)
      (fun _ => integrable_fourier_GC hθ hθ.le) (fun _ m => φ j m + θ) (fun _ i => e j i) T₀ hB₁0 hT1
      (hbox₂ j)).trans ?_
    have hn1 : ∀ m, ‖((‖cf m‖ : ℝ) : ℂ)‖ = ‖cf m‖ := fun m => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    simp only [hn1, Fin.prod_univ_one, Fin.sum_univ_one]
    have herase : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
    rw [herase, Finset.prod_empty, mul_one]
    refine add_le_add (mul_le_mul_of_nonneg_left hmasst hB₁0) ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right hcard hBox0) (htail θ hθ.le) (ht0 θ) (by positivity)
  -- assemble
  have hφ0 : 0 ≤ (q.totient : ℝ)⁻¹ := by positivity
  calc _ ≤ (q.totient : ℝ)⁻¹ *
        (B₁ * M ^ J +
          q.totient * Box * (J * τ * M ^ J)) +
      ∑ j, (2 * (q.totient : ℝ)⁻¹ * (F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q (piv j)) + 1) *
            ((∑ m ∈ Xs, ‖cf m‖) *
              ∏ i : Fin n, ∑ y ∈ primesTo (Q ((piv j).succAbove i)), f0 (y / Q ((piv j).succAbove i)))) +
        (q.totient : ℝ)⁻¹ * (B₁ * Mt + q.totient * Box * τ)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hX hφ0)
          (Finset.sum_le_sum fun j _ => add_le_add le_rfl (mul_le_mul_of_nonneg_left (hY j) hφ0))
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Explicit

/-- The box: `Σ|c_m| ∏_i Σ_p |f0(p/Q_i)| ≤ A₀(3F₀ + 1)^{K₀}X`, for `0 ≤ f0 ≤ F₀`, `P > 0`, `A₀ ≥ 0`,
`Σ|c_m| ≤ PA₀`, `n + 1 ≤ K₀`, `Q_i ≥ 1` and `∏ Q_i ≤ X/P`. -/
theorem box_le_gen {ι : Type*} {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀)
    {Xs : Finset ι} {cf : ι → ℂ} {P A₀ : ℝ} (hP' : 0 < P) (hA0 : 0 ≤ A₀) (hsum : ∑ m ∈ Xs, ‖cf m‖ ≤ P * A₀)
    {n K₀ : ℕ} (hK : n + 1 ≤ K₀) {Q : ℕ → ℝ} (hQ : ∀ i : Fin (n + 1), 1 ≤ Q i) {X : ℝ}
    (hQP : ∏ j ∈ Finset.range (n + 1), Q j ≤ X / P) :
    (∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| ≤
      A₀ * (3 * F₀ + 1) ^ K₀ * X := by
  have hF0 : 0 ≤ F₀ := le_trans (hf0 0) (hF₀ 0)
  have hQ0 : ∀ i : Fin (n + 1), 0 ≤ Q i := fun i => by linarith [hQ i]
  have hprodQ : ∏ i : Fin (n + 1), Q i ≤ X / P := by
    rw [Fin.prod_univ_eq_prod_range (fun j => Q j) (n + 1)]; exact hQP
  have hprod0 : 0 ≤ ∏ i : Fin (n + 1), Q i := Finset.prod_nonneg fun i _ => hQ0 i
  have hX0 : 0 ≤ X := by
    have h := mul_nonneg (hprod0.trans hprodQ) hP'.le
    rwa [div_mul_cancel₀ _ hP'.ne'] at h
  have h1 : ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| ≤ ∏ i : Fin (n + 1), (3 * F₀ * Q i) :=
    Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun p _ => abs_nonneg _)
      (fun i _ => sum_f0_le hf0 hF₀ (hQ i))
  have h2 : ∏ i : Fin (n + 1), (3 * F₀ * Q i) = (3 * F₀) ^ (n + 1) * ∏ i : Fin (n + 1), Q i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h3 : (3 * F₀) ^ (n + 1) ≤ (3 * F₀ + 1) ^ K₀ :=
    (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hK)
  calc (∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)|
      ≤ (P * A₀) * ((3 * F₀) ^ (n + 1) * (X / P)) := by
        refine mul_le_mul (hsum) ?_ (Finset.prod_nonneg fun i _ =>
          Finset.sum_nonneg fun p _ => abs_nonneg _) (by positivity)
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left hprodQ (by positivity))
    _ = A₀ * (3 * F₀) ^ (n + 1) * X := by field_simp
    _ ≤ A₀ * (3 * F₀ + 1) ^ K₀ * X := by gcongr

/-- A pivot's count: `F₀((e^{3θ} − 1)2Q_p + 1)·Σ|c_m|·∏_{i ≠ p} Σ_y f0(y/Q_i) ≤ F₀A₀(3F₀ + 1)^{K₀}(12θ + 1/Q_min)X`,
for `0 ≤ f0 ≤ F₀`, `P > 0`, `A₀ ≥ 0`, `Σ|c_m| ≤ PA₀`, `n + 1 ≤ K₀`, `Q_i ≥ Q_min ≥ 1`,
`∏ Q_i ≤ X/P` and `0 ≤ θ ≤ 1/3`. -/
theorem pivot_le_gen {ι : Type*} {f0 : ℝ → ℝ} {F₀ : ℝ} (hf0 : ∀ u, 0 ≤ f0 u) (hF₀ : ∀ u, f0 u ≤ F₀)
    {Xs : Finset ι} {cf : ι → ℂ} {P A₀ : ℝ} (hP' : 0 < P) (hA0 : 0 ≤ A₀) (hsum : ∑ m ∈ Xs, ‖cf m‖ ≤ P * A₀)
    {n K₀ : ℕ} (hK : n + 1 ≤ K₀) {Q : ℕ → ℝ} {Qmin : ℝ} (hQmin : 1 ≤ Qmin) (hQ : ∀ i : Fin (n + 1), Qmin ≤ Q i)
    {X : ℝ} (hQP : ∏ j ∈ Finset.range (n + 1), Q j ≤ X / P) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 3)
    (p : Fin (n + 1)) :
    F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q p) + 1) *
        ((∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i))) ≤
      F₀ * A₀ * (3 * F₀ + 1) ^ K₀ * (12 * θ + Qmin⁻¹) * X := by
  have hF0 : 0 ≤ F₀ := le_trans (hf0 0) (hF₀ 0)
  have hQ1 : ∀ i : Fin (n + 1), 1 ≤ Q i := fun i => hQmin.trans (hQ i)
  have hQ0 : ∀ i : Fin (n + 1), 0 ≤ Q i := fun i => by linarith [hQ1 i]
  have hQp : 0 < Q p := by linarith [hQ1 p]
  have hprodQ : ∏ i : Fin (n + 1), Q i ≤ X / P := by
    rw [Fin.prod_univ_eq_prod_range (fun j => Q j) (n + 1)]; exact hQP
  have hsplit : ∏ i : Fin (n + 1), Q i = Q p * ∏ i : Fin n, Q (p.succAbove i) := Fin.prod_univ_succAbove _ p
  set R := ∏ i : Fin n, Q (p.succAbove i) with hR
  have hR0 : 0 ≤ R := Finset.prod_nonneg fun i _ => hQ0 _
  have hX0 : 0 ≤ X / P := le_trans (by rw [hsplit]; exact mul_nonneg hQp.le hR0) hprodQ
  -- the counts of the other primes
  have h1 : ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i)) ≤ (3 * F₀) ^ n * R := by
    have : ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i)) ≤
        ∏ i : Fin n, (3 * F₀ * Q (p.succAbove i)) :=
      Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => hf0 _) (fun i _ => by
        have := sum_f0_le hf0 hF₀ (hQ1 (p.succAbove i))
        simp only [abs_of_nonneg (hf0 _)] at this
        exact this)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have h1' : 0 ≤ ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i)) :=
    Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun y _ => hf0 _
  -- the pivot's factor
  have he : (Real.exp (3 * θ) - 1) * (2 * Q p) + 1 ≤ 12 * θ * Q p + 1 := by
    have := exp_three_sub_one_le hθ0 hθ
    nlinarith
  have he0 : 0 ≤ (Real.exp (3 * θ) - 1) * (2 * Q p) + 1 := by
    have : 0 ≤ Real.exp (3 * θ) - 1 := by
      have := Real.add_one_le_exp (3 * θ); linarith
    positivity
  have hkey : (12 * θ * Q p + 1) * R ≤ (12 * θ + Qmin⁻¹) * (X / P) := by
    have hRQ : R ≤ Qmin⁻¹ * (Q p * R) := by
      rw [← mul_assoc]
      have : 1 ≤ Qmin⁻¹ * Q p := by
        rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]; linarith [hQ p]
      nlinarith
    calc (12 * θ * Q p + 1) * R = 12 * θ * (Q p * R) + R := by ring
      _ ≤ 12 * θ * (Q p * R) + Qmin⁻¹ * (Q p * R) := by linarith
      _ = (12 * θ + Qmin⁻¹) * (Q p * R) := by ring
      _ ≤ (12 * θ + Qmin⁻¹) * (X / P) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← hsplit]; exact hprodQ
  have h3 : (3 * F₀) ^ n ≤ (3 * F₀ + 1) ^ K₀ :=
    (pow_le_pow_left₀ (by positivity) (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  calc F₀ * ((Real.exp (3 * θ) - 1) * (2 * Q p) + 1) *
        ((∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin n, ∑ y ∈ primesTo (Q (p.succAbove i)), f0 (y / Q (p.succAbove i)))
      ≤ F₀ * (12 * θ * Q p + 1) * ((P * A₀) * ((3 * F₀) ^ n * R)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left he hF0) (mul_le_mul (hsum) h1 h1'
          (by positivity)) (mul_nonneg (Finset.sum_nonneg fun m _ => norm_nonneg _) h1') (by positivity)
    _ = F₀ * A₀ * (3 * F₀) ^ n * P * ((12 * θ * Q p + 1) * R) := by ring
    _ ≤ F₀ * A₀ * (3 * F₀) ^ n * P * ((12 * θ + Qmin⁻¹) * (X / P)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = F₀ * A₀ * (3 * F₀) ^ n * (12 * θ + Qmin⁻¹) * X := by field_simp
    _ ≤ F₀ * A₀ * (3 * F₀ + 1) ^ K₀ * (12 * θ + Qmin⁻¹) * X := by
        have : 0 ≤ (12 * θ + Qmin⁻¹) * X := by
          have hXX : 0 ≤ X := by
            have h := mul_nonneg hX0 hP'.le
            rwa [div_mul_cancel₀ _ hP'.ne'] at h
          positivity
        have := mul_le_mul_of_nonneg_right h3 this
        nlinarith [mul_nonneg hF0 hA0]

section Asym

open SieveSmooth Classical Filter Asymptotics
open scoped ContDiff

/-- **A sharp family with an abstract polynomial part, asymptotic form.** Let `0 ≤ f0 ≤ F₀`, and fix `L` and the
family's shape: `K₀`, `J₀`, `e₁ > 0`, `E₀ ≥ 0` and `Λ₀ ≥ 0`. There are `δ > 0` and `q₀` with the following property.
Let `q ≥ q₀`, let `a` be a unit mod `q`, let `m` run over a finite set `Xs` with values `nv m` and coefficients `c_m`
with `Σ_m |c_m| ≤ PA₀` for some `P > 0` and `A₀ ≥ 0`, and let `n + 1 ≤ K₀` primes `x_i` run over `Sp`'s ranges at the
scales `Q_i ≥ q^{e₁}`, `∏_i Q_i ≤ 2^{K₀}q^L/P`, with the weights `f0(x_i/Q_i)`. Let `J ≤ J₀` sharp comparisons `P_j`
hold when `ℓ_j = φ_j(m) + Σ_i e_{ji} log x_i > 0` and imply `ℓ_j ≥ 0`, with `|e_{ji}| ≤ E₀`, `ℓ_j ≤ Λ₀ log q` on the
family, and for each `j` a pivot `i` with `e_{ji} = ±1`. Suppose that for the coefficients `c_m` and `|c_m|`, every
`ξ ∈ ℝ^J`, `κ ∈ ℝ` and all heights `|h_i| ≤ q^{1/100000}`, the sum over `χ ≠ 1` of
`|Σ_m c′_m e(κ + Σ_j ξ_jφ_j(m))χ(nv m)|·|∏_i Sp(χ, Q_i, h_i)|` is at most `A₀q^{L − 1/50000}` (`hbox`). Then the family's
`|A − B/φ(q)|` is at most `A₀q^{L−δ}/φ(q)`. -/
theorem sharp_gen {ι : Type*} {f0 : ℝ → ℝ} (hf0nn : ∀ u, 0 ≤ f0 u) {F₀ : ℝ} (hF₀ : ∀ u, f0 u ≤ F₀) (K₀ J₀ : ℕ)
    (L : ℝ) {e₁ E₀ Λ₀ : ℝ} (he₁ : 0 < e₁) (hE₀ : 0 ≤ E₀) (hΛ₀ : 0 ≤ Λ₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (Xs : Finset ι) (nv : ι → ℕ) (cf : ι → ℂ) (P A₀ : ℝ), 0 < P → 0 ≤ A₀ → ∑ m ∈ Xs, ‖cf m‖ ≤ P * A₀ →
      ∀ (n : ℕ), n + 1 ≤ K₀ → ∀ Q : ℕ → ℝ, (∀ j < n + 1, (q : ℝ) ^ e₁ ≤ Q j) →
      ∏ j ∈ Finset.range (n + 1), Q j ≤ 2 ^ K₀ * (q : ℝ) ^ L / P →
      ∀ {J : ℕ}, J ≤ J₀ → ∀ (φ : Fin J → ι → ℝ) (e : Fin J → Fin (n + 1) → ℝ)
        (Pr : Fin J → ι → (Fin (n + 1) → ℕ) → Prop), (∀ j i, |e j i| ≤ E₀) →
      (∀ j m x, (0 < φ j m + ∑ i, e j i * Real.log (x i) → Pr j m x) ∧
        (Pr j m x → 0 ≤ φ j m + ∑ i, e j i * Real.log (x i))) →
      (∀ j, ∀ m ∈ Xs, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
        φ j m + ∑ i, e j i * Real.log (x i) ≤ Λ₀ * Real.log q) →
      ∀ piv : Fin J → Fin (n + 1), (∀ j, e j (piv j) = 1 ∨ e j (piv j) = -1) →
      (∀ c' : ι → ℂ, (c' = cf ∨ c' = fun m => ((‖cf m‖ : ℝ) : ℂ)) → ∀ (ξ : Fin J → ℝ) (κ : ℝ) (hh : ℕ → ℝ),
        (∀ j < n + 1, |hh j| ≤ (q : ℝ) ^ (1 / 100000 : ℝ)) →
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖∑ m ∈ Xs, c' m * Complex.exp (2 * π * I * ((κ + ∑ j, ξ j * φ j m : ℝ) : ℂ)) * χ (nv m)‖ *
            ‖∏ j ∈ Finset.range (n + 1), SieveWeight.Sp χ f0 (Q j) (hh j)‖ ≤ A₀ * (q : ℝ) ^ (L - 1 / 50000)) →
      ‖Dsum q a (Xs ×ˢ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)))
          (fun mx => nv mx.1 * ∏ i, mx.2 i)
          (fun mx => (cf mx.1 * ∏ i, (f0 (mx.2 i / Q i) : ℂ)) *
            ∏ j, ((if Pr j mx.1 mx.2 then 1 else 0 : ℝ) : ℂ))‖ ≤
        (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ)) := by
  have hF0 : 0 ≤ F₀ := le_trans (hf0nn 0) (hF₀ 0)
  have hpi := Real.pi_pos
  have hJ0 : (0 : ℝ) ≤ J₀ := Nat.cast_nonneg _
  -- the exponents
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℝ, ε₂ = 1 / (400000 * ((J₀ : ℝ) + 1)) := ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; positivity
  have hε₂1 : ε₂ ≤ 1 / 400000 := by
    rw [hε₂]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hε₂J : ε₂ * ((J₀ : ℝ) + 1) = 1 / 400000 := by rw [hε₂]; field_simp
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min ε₂ e₁ / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hε₂0 he₁)
  have hδε : 2 * δ ≤ ε₂ := by rw [hδ]; linarith [min_le_left ε₂ e₁]
  have hδe : 2 * δ ≤ e₁ := by rw [hδ]; linarith [min_le_right ε₂ e₁]
  -- the constants
  have hc₂ : 0 ≤ ∫ v, ‖iteratedDeriv 2 gc v‖ := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 + (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by
    rw [hC]; have : 0 ≤ (∫ v, ‖iteratedDeriv 2 gc v‖) / (2 * π) := by positivity
    linarith
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ,
      c' = 2 * π * ((2 * ∫ v, ‖iteratedDeriv 1200003 gc v‖) / (2 * π) ^ 1200003) := ⟨_, rfl⟩
  have hc'0 : 0 ≤ c' := by rw [hc']; positivity
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℝ, a₁ = (1 + J₀) * C ^ (J₀ + 1) := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : ℝ, a₂ = 2 * (3 * F₀ + 1) ^ K₀ * 2 ^ K₀ * J₀ * c' * C ^ (J₀ + 1) := ⟨_, rfl⟩
  obtain ⟨a₃, ha₃⟩ : ∃ a₃ : ℝ, a₃ = 2 * F₀ * J₀ * (3 * F₀ + 1) ^ K₀ * 2 ^ K₀ := ⟨_, rfl⟩
  have hF1 : 0 ≤ (3 * F₀ + 1) ^ K₀ := pow_nonneg (by linarith) _
  have hC0 : 0 ≤ C ^ (J₀ + 1) := pow_nonneg (by linarith) _
  have ha₁0 : 0 ≤ a₁ := by rw [ha₁]; exact mul_nonneg (by linarith) hC0
  have ha₂0 : 0 ≤ a₂ := by
    rw [ha₂]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF1) (by positivity)) hJ0)
      hc'0) hC0
  have ha₃0 : 0 ≤ a₃ := by
    rw [ha₃]; exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hJ0) hF1) (by positivity)
  -- large `q`
  have hev : ∀ᶠ x : ℝ in atTop, 3 ≤ x ^ ε₂ ∧ π * (2 * Λ₀ * Real.log x + 3) ≤ x ^ ε₂ ∧
      2 * π * J₀ * E₀ ≤ x ^ (1 / 200000 : ℝ) ∧ a₁ + a₂ + 13 * a₃ ≤ x ^ δ ∧ 1 ≤ x :=
    ((tendsto_rpow_atTop hε₂0).eventually_ge_atTop 3).and ((ev_pi_log_le hε₂0 hΛ₀).and
      (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200000)).eventually_ge_atTop _).and
        (((tendsto_rpow_atTop hδ0).eventually_ge_atTop _).and (eventually_ge_atTop 1))))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨δ, hδ0, N, fun q _ hq a ha Xs nv cf P A₀ hP0 hA0 hsumc n hK Q hQ hQP J hJ φ e Pr he hP hΛ piv hpiv
    hbox => ?_⟩
  obtain ⟨h3, hlog, hE, hcon, hq1⟩ := hN q hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hQpos : ∀ i : Fin (n + 1), 0 < Q i := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hq0 _) (hQ i i.isLt)
  have hB₁0 : 0 ≤ A₀ * (q : ℝ) ^ (L - 1 / 50000) := mul_nonneg hA0 (Real.rpow_nonneg hq0.le _)
  have hl : 0 ≤ Real.log q := Real.log_nonneg hq1
  -- `θ = q^{−ε₂}`, `Λ = Λ₀ log q + 1`, `T₀ = q^{1/200000}` and `k = 1200003`
  have hθ0 : 0 < (q : ℝ) ^ (-ε₂) := Real.rpow_pos_of_pos hq0 _
  have hθ3 : (q : ℝ) ^ (-ε₂) ≤ 1 / 3 := by
    rw [Real.rpow_neg hq0.le, one_div]; exact inv_anti₀ (by norm_num) h3
  have hθ1 : (q : ℝ) ^ (-ε₂) ≤ 1 := by linarith
  have hΛ1 : (1 : ℝ) ≤ Λ₀ * Real.log q + 1 := by nlinarith [mul_nonneg hΛ₀ hl]
  have hΛ' : ∀ j, ∀ m ∈ Xs, ∀ x ∈ Fintype.piFinset (fun i : Fin (n + 1) => primesTo (Q i)),
      φ j m + ∑ i, e j i * Real.log (x i) ≤ Λ₀ * Real.log q + 1 := fun j m hm x hx => by
    linarith [hΛ j m hm x hx]
  have hT₀ : (1 : ℝ) ≤ (q : ℝ) ^ (1 / 200000 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
  have hT : ∀ i : Fin (n + 1), 2 * π * (∑ j, |e j i|) * (q : ℝ) ^ (1 / 200000 : ℝ) ≤
      (q : ℝ) ^ (1 / 100000 : ℝ) := by
    intro i
    have hs : ∑ j, |e j i| ≤ J₀ * E₀ := by
      calc ∑ j, |e j i| ≤ ∑ _j : Fin J, E₀ := Finset.sum_le_sum fun j _ => he j i
        _ = J * E₀ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ J₀ * E₀ := mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) hE₀
    have hsplit : (q : ℝ) ^ (1 / 100000 : ℝ) = (q : ℝ) ^ (1 / 200000 : ℝ) * (q : ℝ) ^ (1 / 200000 : ℝ) := by
      rw [← Real.rpow_add hq0]; norm_num
    rw [hsplit]
    have hTnn : 0 ≤ (q : ℝ) ^ (1 / 200000 : ℝ) := by positivity
    have h2 : 2 * π * (∑ j, |e j i|) ≤ 2 * π * J₀ * E₀ := by
      rw [mul_assoc (2 * π) (J₀ : ℝ)]; exact mul_le_mul_of_nonneg_left hs (by positivity)
    exact mul_le_mul_of_nonneg_right (h2.trans hE) hTnn
  have hmain := sharp_explicit_gen hf0nn hF₀ ha Xs nv cf n Q hQpos φ e Pr hP hθ0 hθ1 hΛ1 hΛ' piv hpiv hT₀
    (k := 1200003) (by norm_num) hB₁0 hT hbox
  refine hmain.trans ?_
  -- the masses and the tail
  obtain ⟨hM, hMt⟩ := massB_le (ε := ε₂) hq1 hΛ₀ hlog
  have hτ := tailB_le (ε := ε₂) (k := 1200003) hq1 (by norm_num) (by push_cast; linarith)
  rw [← hC] at hM hMt
  rw [← hc'] at hτ
  have hM0 : 0 ≤ massB ((q : ℝ) ^ (-ε₂)) (Λ₀ * Real.log q + 1) := by
    rw [massB]; exact add_nonneg (mul_nonneg hpi.le (by linarith)) (by positivity)
  have hMt0 : 0 ≤ massB ((q : ℝ) ^ (-ε₂)) ((q : ℝ) ^ (-ε₂)) := by
    rw [massB]; exact add_nonneg (mul_nonneg hpi.le (by linarith)) (by positivity)
  have hτ0 : 0 ≤ tailB ((q : ℝ) ^ (-ε₂)) ((q : ℝ) ^ (1 / 200000 : ℝ)) 1200003 := by
    rw [tailB]; positivity
  generalize massB ((q : ℝ) ^ (-ε₂)) (Λ₀ * Real.log q + 1) = M at hM hM0 ⊢
  generalize massB ((q : ℝ) ^ (-ε₂)) ((q : ℝ) ^ (-ε₂)) = Mt at hMt hMt0 ⊢
  generalize tailB ((q : ℝ) ^ (-ε₂)) ((q : ℝ) ^ (1 / 200000 : ℝ)) 1200003 = τ at hτ hτ0 ⊢
  -- elementary facts
  have hφpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφinv0 : 0 ≤ (q.totient : ℝ)⁻¹ := by positivity
  have hQ1 : ∀ i : Fin (n + 1), (q : ℝ) ^ e₁ ≤ Q i := fun i => hQ i i.isLt
  have hqe1 : (1 : ℝ) ≤ (q : ℝ) ^ e₁ := Real.one_le_rpow hq1 he₁.le
  have hqL : 0 ≤ (q : ℝ) ^ L := by positivity
  have hq4 : 1 ≤ (q : ℝ) ^ (1 / 400000 : ℝ) := Real.one_le_rpow hq1 (by norm_num)
  have hqε : 1 ≤ (q : ℝ) ^ ε₂ := Real.one_le_rpow hq1 hε₂0.le
  have hCq : 1 ≤ C * (q : ℝ) ^ ε₂ := one_le_mul_of_one_le_of_one_le hC1 hqε
  have hpowJ : (C * (q : ℝ) ^ ε₂) ^ (J₀ + 1) = C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ ε₂), ← Real.rpow_mul hq0.le]
    congr 2; push_cast; exact hε₂J
  have hMJ : M ^ J ≤ C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ) := by
    rw [← hpowJ]
    exact (pow_le_pow_left₀ hM0 hM J).trans (pow_le_pow_right₀ hCq (by omega))
  have hMt' : (J : ℝ) * Mt ≤ J₀ * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by
    rw [← hpowJ]
    have h1 : Mt ≤ (C * (q : ℝ) ^ ε₂) ^ (J₀ + 1) :=
      hMt.trans (by simpa using pow_le_pow_right₀ hCq (show 1 ≤ J₀ + 1 by omega))
    exact mul_le_mul (by exact_mod_cast hJ) h1 hMt0 hJ0
  have hCq4 : 1 ≤ C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1) hq4
  -- the smoothed family and its tails
  have hT1 : A₀ * (q : ℝ) ^ (L - 1 / 50000) * (M ^ J + J * Mt) ≤
      A₀ * (q : ℝ) ^ L * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ)) := by
    have hsum : M ^ J + J * Mt ≤ (1 + J₀) * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by linarith
    have hexp : (q : ℝ) ^ (L - 1 / 50000) * (q : ℝ) ^ (1 / 400000 : ℝ) =
        (q : ℝ) ^ L * (q : ℝ) ^ (-(7 / 400000) : ℝ) := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]; congr 1; ring
    calc A₀ * (q : ℝ) ^ (L - 1 / 50000) * (M ^ J + J * Mt)
        ≤ A₀ * (q : ℝ) ^ (L - 1 / 50000) * ((1 + J₀) * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum hB₁0
      _ = A₀ * ((1 + J₀) * C ^ (J₀ + 1)) *
            ((q : ℝ) ^ (L - 1 / 50000) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by ring
      _ = A₀ * (q : ℝ) ^ L * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ)) := by
          rw [hexp, ha₁]; ring
  have hBox := box_le_gen hf0nn hF₀ hP0 hA0 hsumc hK (fun i => hqe1.trans (hQ1 i)) hQP
  have hBox0 : 0 ≤ (∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| := by
    positivity
  generalize (∑ m ∈ Xs, ‖cf m‖) * ∏ i : Fin (n + 1), ∑ p ∈ primesTo (Q i), |f0 (p / Q i)| = Box at hBox hBox0 ⊢
  have hT2 : (q.totient : ℝ) * Box * (J * τ * M ^ J + J * τ) ≤
      A₀ * (q : ℝ) ^ L * (a₂ * (q : ℝ) ^ (-1 : ℝ)) := by
    have hm1 : M ^ J + 1 ≤ 2 * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by linarith
    have hJτ : (J : ℝ) * τ * M ^ J + J * τ ≤
        J₀ * (c' * (q : ℝ) ^ (-3 : ℝ)) * (2 * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ))) := by
      calc (J : ℝ) * τ * M ^ J + J * τ = J * τ * (M ^ J + 1) := by ring
        _ ≤ J₀ * (c' * (q : ℝ) ^ (-3 : ℝ)) * (2 * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ))) :=
          mul_le_mul (mul_le_mul (by exact_mod_cast hJ) hτ hτ0 hJ0) hm1
            (by linarith [pow_nonneg hM0 J]) (mul_nonneg hJ0 (mul_nonneg hc'0 (by positivity)))
    have hexp : (q : ℝ) * (q : ℝ) ^ (-3 : ℝ) * (q : ℝ) ^ (1 / 400000 : ℝ) ≤ (q : ℝ) ^ (-1 : ℝ) := by
      have : (q : ℝ) * (q : ℝ) ^ (-3 : ℝ) * (q : ℝ) ^ (1 / 400000 : ℝ) = (q : ℝ) ^ ((1 : ℝ) + -3 + 1 / 400000) := by
        rw [Real.rpow_add hq0, Real.rpow_add hq0, Real.rpow_one]
      rw [this]; exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    have hK0 : 0 ≤ A₀ * (q : ℝ) ^ L * a₂ := mul_nonneg (mul_nonneg hA0 hqL) ha₂0
    calc (q.totient : ℝ) * Box * (J * τ * M ^ J + J * τ)
        ≤ (q : ℝ) * (A₀ * (3 * F₀ + 1) ^ K₀ * (2 ^ K₀ * (q : ℝ) ^ L)) *
            (J₀ * (c' * (q : ℝ) ^ (-3 : ℝ)) * (2 * (C ^ (J₀ + 1) * (q : ℝ) ^ (1 / 400000 : ℝ)))) :=
          mul_le_mul (mul_le_mul hφq hBox hBox0 (by positivity)) hJτ
            (by linarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg J) hτ0) (pow_nonneg hM0 J),
              mul_nonneg (Nat.cast_nonneg J) hτ0])
            (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hA0 hF1) (by positivity)))
      _ = A₀ * (q : ℝ) ^ L * (2 * (3 * F₀ + 1) ^ K₀ * 2 ^ K₀ * J₀ * c' * C ^ (J₀ + 1)) *
            ((q : ℝ) * (q : ℝ) ^ (-3 : ℝ) * (q : ℝ) ^ (1 / 400000 : ℝ)) := by ring
      _ ≤ A₀ * (q : ℝ) ^ L * (2 * (3 * F₀ + 1) ^ K₀ * 2 ^ K₀ * J₀ * c' * C ^ (J₀ + 1)) *
            (q : ℝ) ^ (-1 : ℝ) := by
          rw [← ha₂]; exact mul_le_mul_of_nonneg_left hexp hK0
      _ = A₀ * (q : ℝ) ^ L * (a₂ * (q : ℝ) ^ (-1 : ℝ)) := by rw [← ha₂]; ring
  -- the pivots' counts
  have hT3 := Finset.sum_le_sum fun (j : Fin J) (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pivot_le_gen hf0nn hF₀ hP0 hA0 hsumc hK hqe1 hQ1 hQP hθ0.le hθ3 (piv j))
      (show (0 : ℝ) ≤ 2 * (q.totient : ℝ)⁻¹ by positivity)
  have hinv : ((q : ℝ) ^ e₁)⁻¹ = (q : ℝ) ^ (-e₁) := (Real.rpow_neg hq0.le e₁).symm
  have hX0 : 0 ≤ F₀ * A₀ * (3 * F₀ + 1) ^ K₀ * (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)) *
      (2 ^ K₀ * (q : ℝ) ^ L) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hF0 hA0) hF1) (by positivity)) (by positivity)
  calc _ ≤ (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ L * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ)) +
            A₀ * (q : ℝ) ^ L * (a₂ * (q : ℝ) ^ (-1 : ℝ))) +
          ∑ _j : Fin J, 2 * (q.totient : ℝ)⁻¹ * (F₀ * A₀ * (3 * F₀ + 1) ^ K₀ *
            (12 * (q : ℝ) ^ (-ε₂) + ((q : ℝ) ^ e₁)⁻¹) * (2 ^ K₀ * (q : ℝ) ^ L)) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) hφinv0) hT3
    _ ≤ (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ L * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ)) +
            A₀ * (q : ℝ) ^ L * (a₂ * (q : ℝ) ^ (-1 : ℝ))) +
          (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ L *
            (a₃ * (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)))) := by
        refine add_le_add le_rfl ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hinv, ha₃]
        calc (J : ℝ) * (2 * (q.totient : ℝ)⁻¹ * (F₀ * A₀ * (3 * F₀ + 1) ^ K₀ *
              (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)) * (2 ^ K₀ * (q : ℝ) ^ L)))
            ≤ J₀ * (2 * (q.totient : ℝ)⁻¹ * (F₀ * A₀ * (3 * F₀ + 1) ^ K₀ *
              (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)) * (2 ^ K₀ * (q : ℝ) ^ L))) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) (mul_nonneg (by positivity) hX0)
          _ = _ := by ring
    _ = (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ L * (a₁ * (q : ℝ) ^ (-(7 / 400000) : ℝ) +
            a₂ * (q : ℝ) ^ (-1 : ℝ) + a₃ * (12 * (q : ℝ) ^ (-ε₂) + (q : ℝ) ^ (-e₁)))) := by ring
    _ ≤ (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ L * (q : ℝ) ^ (-δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (bracket_le hq1 ha₁0 ha₂0 ha₃0 hδ0 hδε hε₂1 hδe hcon) (mul_nonneg hA0 hqL)) hφinv0
    _ = (q.totient : ℝ)⁻¹ * (A₀ * (q : ℝ) ^ (L - δ)) := by
        rw [mul_assoc A₀, ← Real.rpow_add hq0, sub_eq_add_neg]

end Asym

end SieveFamilyGen

#print axioms SieveFamilyGen.family_bound_gen
#print axioms SieveFamilyGen.sharp_gen
