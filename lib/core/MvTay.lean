import ThetaChain
import CMFormalBiadd

/-!
# Multivariable Taylor series at `0`

D1b-0 of the D1b plan: the Taylor series `mtay G = Σ_m ∂^mG(0)/m!·X^m` of a function `G : ℂ^ι → ℂ` analytic at
`0`, as an `MvPowerSeries ι ℂ` (`∂^mG(0)` is the chain's `ThetaChain.pd`), and its calculus. `mtay` is additive,
`ℂ`-linear and multiplicative (`mtay_add`, `mtay_smul`, `mtay_mul`, `mtay_sum`, `mtay_prod`), commutes with linear
substitutions (`mtay_comp_linear`, `mtay_comp_reindex`), and takes a one-variable function of a linear form, or a
product of one-variable functions of the coordinates, to the substituted one-variable series `CMFormalBiadd.tay`
(`mtay_comp_form`, `mtay_comp_coord`, `mtay_prod_coord`); in one variable it is `tay` (`mtay_unit`). Shared
infrastructure for `ThetaGauss` (D1b-6) and for the chain's jets (C2e).

**Lines.** Everything is reduced to one variable. The restriction `lineR y F = F(t·y)` to the line through `y` is a
substitution, so an algebra map `ℂ⟦X_ι⟧ → ℂ⟦t⟧` (`lineR`); its `n`-th coefficient is the value at `y` of the
degree-`n` part of `F` (`coeff_lineR`), so a series is determined by its restrictions to all lines (`eq_of_lineR`,
from `MvPolynomial.funext`). And `lineR y (mtay G) = tay(t ↦ G(t·y))` (`lineR_mtay`): `∂ⁿ_t G(t·y)` at `0` is
`DⁿG(0)(y, …, y)` (`iteratedDeriv_comp_smul`), which multilinearity expands over the words `σ : Fin n → ι`; the
iterated derivative of an analytic function is symmetric (`ContDiffAt.iteratedFDeriv_comp_perm`), so the term of a
word depends only on its multi-index `wordIdx σ` (`pd_wordIdx`), and a multi-index `d` of degree `n` is that of
`n!/d!` words (`card_wordIdx_eq`: the coefficient of `X^d` in `(Σ_i X_i)ⁿ`) (`iteratedFDeriv_diag`). The laws of
`mtay` then follow from those of `tay` (`tay_mul`, and the dilations `tay_comp_mul_of_analyticAt`) and from the
composition of substitutions (`MvPowerSeries.subst_comp_subst_apply`).

**Main results:** `lineR_mtay`, `eq_of_lineR`, `mtay_add`, `mtay_smul`, `mtay_mul`, `mtay_sum`, `mtay_prod`,
`mtay_const`, `mtay_congr`, `constantCoeff_mtay`, `mtay_comp_linear`, `mtay_comp_reindex`, `mtay_comp_form`,
`mtay_comp_coord`, `mtay_prod_coord`, `mtay_unit`; the definitions `mtay`, `lineR`, `wordIdx`.
-/

namespace MvTay

open PowerSeries ThetaChain CMFormalBiadd Finset
open scoped ContDiff

noncomputable section

/-! ## Words and their multi-indices -/

section Words

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The multi-index of a word** `σ : Fin n → ι`: `wordIdx σ i = #{j | σ j = i}`. -/
def wordIdx {n : ℕ} (σ : Fin n → ι) : ι →₀ ℕ := ∑ j, Finsupp.single (σ j) 1

omit [Fintype ι] in
/-- **The entries of `wordIdx`.** -/
theorem wordIdx_apply {n : ℕ} (σ : Fin n → ι) (i : ι) : wordIdx σ i = #{j | σ j = i} := by
  simp only [wordIdx, Finsupp.finsetSum_apply, Finsupp.single_apply, card_filter]

/-- **The multi-index of a word of length `n` has degree `n`.** -/
theorem wordIdx_mem {n : ℕ} (σ : Fin n → ι) : wordIdx σ ∈ finsuppAntidiag univ n := by
  rw [mem_finsuppAntidiag]
  refine ⟨?_, subset_univ _⟩
  simp only [wordIdx_apply]
  rw [← card_eq_sum_card_fiberwise (fun j _ => mem_univ (σ j))]
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- **The monomial of a word**: `∏_j X_{σ j} = X^{wordIdx σ}`. -/
theorem prod_X_eq_monomial {R : Type} [CommSemiring R] {n : ℕ} (σ : Fin n → ι) :
    ∏ j, (MvPolynomial.X (σ j) : MvPolynomial ι R) = MvPolynomial.monomial (wordIdx σ) 1 := by
  rw [wordIdx, MvPolynomial.monomial_sum_one]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- **The value of the monomial of a word**: `∏_j y_{σ j} = y^{wordIdx σ}`. -/
theorem prod_eq_wordIdx_prod {n : ℕ} (σ : Fin n → ι) (y : ι → ℂ) :
    ∏ j, y (σ j) = (wordIdx σ).prod fun i k => y i ^ k := by
  have h := congrArg (MvPolynomial.eval y) (prod_X_eq_monomial (R := ℂ) σ)
  simpa [MvPolynomial.eval_monomial] using h

/-- **A multi-index `d` of degree `n` is that of `n!/d!` words**: the coefficient of `X^d` in
`(Σ_i X_i)ⁿ = Σ_σ ∏_j X_{σ j}` (`MvPolynomial.coeff_sum_X_pow_of_fintype`). -/
theorem card_wordIdx_eq {n : ℕ} {d : ι →₀ ℕ} (hd : d ∈ finsuppAntidiag univ n) :
    #{σ : Fin n → ι | wordIdx σ = d} = d.multinomial := by
  have h := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℕ) d n
  rw [Fintype.sum_pow, MvPolynomial.coeff_sum] at h
  simp only [prod_X_eq_monomial, MvPolynomial.coeff_monomial] at h
  rw [mem_finsuppAntidiag'] at hd
  rw [ite_eq_left hd.1] at h
  simpa [sum_boole] using h

omit [Fintype ι] in
/-- **Words with the same multi-index differ by a permutation** (matched fibre by fibre). -/
theorem exists_perm_of_wordIdx_eq {n : ℕ} {σ τ : Fin n → ι} (h : wordIdx σ = wordIdx τ) :
    ∃ π : Equiv.Perm (Fin n), τ ∘ π = σ := by
  have hc : ∀ i, Fintype.card {j // σ j = i} = Fintype.card {j // τ j = i} := fun i => by
    rw [Fintype.card_subtype, Fintype.card_subtype, ← wordIdx_apply, ← wordIdx_apply, h]
  exact ⟨Equiv.ofFiberEquiv fun i => Fintype.equivOfCardEq (hc i), funext (Equiv.ofFiberEquiv_map _)⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **The multiset of a word's letters** is that of its multi-index. -/
theorem toMultiset_wordIdx {n : ℕ} (σ : Fin n → ι) :
    Finsupp.toMultiset (wordIdx σ) = Multiset.map σ univ.val := by
  rw [wordIdx, Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  rw [← Multiset.sum_map_singleton (Multiset.map σ univ.val), Multiset.map_map]
  rfl

/-- **Symmetry**: for `G` analytic at `0`, `DᵏG(0)(e_{τ 1}, …, e_{τ k})` depends only on the multi-index of the
word `τ` (`ContDiffAt.iteratedFDeriv_comp_perm`). -/
theorem iteratedFDeriv_word {G : (ι → ℂ) → ℂ} (hG : AnalyticAt ℂ G 0) {k n : ℕ} {τ : Fin k → ι}
    {σ : Fin n → ι} (h : wordIdx τ = wordIdx σ) :
    iteratedFDeriv ℂ k G 0 (fun j => Pi.single (τ j) 1) =
      iteratedFDeriv ℂ n G 0 (fun j => Pi.single (σ j) 1) := by
  have hkn : k = n := by
    have h1 := (mem_finsuppAntidiag.1 (wordIdx_mem τ)).1
    have h2 := (mem_finsuppAntidiag.1 (wordIdx_mem σ)).1
    rw [h] at h1
    omega
  subst hkn
  obtain ⟨π, rfl⟩ := exists_perm_of_wordIdx_eq h
  exact (hG.contDiffAt (n := ω)).iteratedFDeriv_comp_perm (fun j => Pi.single (σ j) 1) π

/-- **`pd` along any word**: `∂^{wordIdx σ}G(0) = DⁿG(0)(e_{σ 1}, …, e_{σ n})` for `G` analytic at `0`. -/
theorem pd_wordIdx {G : (ι → ℂ) → ℂ} (hG : AnalyticAt ℂ G 0) {n : ℕ} (σ : Fin n → ι) :
    pd G (wordIdx σ) = iteratedFDeriv ℂ n G 0 (fun j => Pi.single (σ j) 1) := by
  rw [pd]
  apply iteratedFDeriv_word hG
  have hl : ∀ (l : List ι) (k : ℕ) (h : k = l.length), List.ofFn (fun j : Fin k => l.get (Fin.cast h j)) = l := by
    rintro l k rfl
    simp
  have key : Finsupp.toMultiset (wordIdx fun j => (Finsupp.toMultiset (wordIdx σ)).toList.get
      (Fin.cast (Multiset.length_toList _).symm j)) = Finsupp.toMultiset (wordIdx σ) := by
    rw [toMultiset_wordIdx, Fin.univ_val_map, hl, Multiset.coe_toList]
  rw [← Finsupp.toMultiset_toFinsupp (wordIdx _), key, Finsupp.toMultiset_toFinsupp]

end Words

/-! ## Restriction to lines -/

section Line

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The line through `y` can be substituted**: `X_i ↦ y_i·t` has no constant term. -/
theorem hasSubst_line (y : ι → ℂ) : MvPowerSeries.HasSubst fun i => y i • (X : ℂ⟦X⟧) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    have : MvPowerSeries.constantCoeff (X : ℂ⟦X⟧) = 0 := MvPowerSeries.constantCoeff_X ()
    simp [this]

omit [DecidableEq ι] in
/-- **The restriction to the line** through `y`: `lineR y F = F(t·y)`, the substitution `X_i ↦ y_i·t`, as an
algebra map to series in `t`. -/
def lineR (y : ι → ℂ) : MvPowerSeries ι ℂ →ₐ[ℂ] ℂ⟦X⟧ := MvPowerSeries.substAlgHom (hasSubst_line y)

omit [DecidableEq ι] in
/-- **`lineR` is a substitution.** -/
theorem lineR_apply (y : ι → ℂ) (F : MvPowerSeries ι ℂ) :
    lineR y F = MvPowerSeries.subst (fun i => y i • (X : ℂ⟦X⟧)) F :=
  congrFun (MvPowerSeries.coe_substAlgHom _) F

/-- **The coefficients of `lineR`**: the `n`-th is the value at `y` of the degree-`n` part. -/
theorem coeff_lineR (y : ι → ℂ) (F : MvPowerSeries ι ℂ) (n : ℕ) :
    coeff n (lineR y F) = ∑ d ∈ finsuppAntidiag univ n, MvPowerSeries.coeff d F * d.prod fun i k => y i ^ k := by
  have hprod : ∀ d : ι →₀ ℕ, (d.prod fun s e => (y s • (X : ℂ⟦X⟧)) ^ e) =
      C (d.prod fun s e => y s ^ e) * X ^ (d.sum fun _ e => e) := fun d => by
    simp only [Finsupp.prod, Finsupp.sum, smul_eq_C_mul, mul_pow, prod_mul_distrib, ← map_pow, ← map_prod,
      prod_pow_eq_pow_sum]
  rw [lineR_apply, show coeff n = MvPowerSeries.coeff (Finsupp.single () n) from rfl,
    MvPowerSeries.coeff_subst (hasSubst_line y)]
  simp only [hprod, show MvPowerSeries.coeff (Finsupp.single () n) = coeff (R := ℂ) n from rfl,
    coeff_C_mul_X_pow, smul_eq_mul]
  rw [finsum_eq_sum_of_support_subset (s := finsuppAntidiag univ n)]
  · refine sum_congr rfl fun d hd => ?_
    rw [mem_finsuppAntidiag'] at hd
    rw [ite_eq_left hd.1.symm]
  · intro d hd
    rw [Function.mem_support] at hd
    rw [mem_coe, mem_finsuppAntidiag']
    refine ⟨?_, subset_univ _⟩
    by_contra h'
    exact hd (by rw [ite_eq_right fun h => h' h.symm, mul_zero])

/-- **A series is determined by its restrictions to lines** (the degree-`n` parts are polynomials that agree on
`ℂ^ι`, `MvPolynomial.funext`). -/
theorem eq_of_lineR {F F' : MvPowerSeries ι ℂ} (h : ∀ y, lineR y F = lineR y F') : F = F' := by
  ext d
  set n := d.sum fun _ k => k
  have hd : d ∈ finsuppAntidiag univ n := mem_finsuppAntidiag'.2 ⟨rfl, subset_univ _⟩
  let P : MvPolynomial ι ℂ :=
    ∑ e ∈ finsuppAntidiag univ n, MvPolynomial.monomial e (MvPowerSeries.coeff e F - MvPowerSeries.coeff e F')
  have hP : P = 0 := MvPolynomial.funext fun y => by
    have := congrArg (coeff n) (h y)
    rw [coeff_lineR, coeff_lineR] at this
    simp only [P, map_sum, MvPolynomial.eval_monomial, sub_mul, sum_sub_distrib, map_zero]
    rw [this, sub_self]
  have := congrArg (fun p : MvPolynomial ι ℂ => p.coeff d) hP
  simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, sum_ite_eq', ite_eq_left hd] at this
  exact sub_eq_zero.1 (this.trans (by simp))

omit [DecidableEq ι] in
/-- **`lineR` of a variable.** -/
theorem lineR_X (y : ι → ℂ) (i : ι) : lineR y (MvPowerSeries.X i) = y i • X := by
  rw [lineR_apply, MvPowerSeries.subst_X (hasSubst_line y)]

omit [DecidableEq ι] in
/-- **`lineR` of a constant.** -/
theorem lineR_C (y : ι → ℂ) (c : ℂ) : lineR y (MvPowerSeries.C c) = C c := by
  rw [lineR_apply, MvPowerSeries.subst_C]
  rfl

omit [DecidableEq ι] in
/-- **`lineR` of a linear form**: `Σ_i c_i X_i ↦ (Σ_i c_i y_i)·t`. -/
theorem lineR_linear (y : ι → ℂ) (c : ι → ℂ) :
    lineR y (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) = (∑ i, c i * y i) • X := by
  simp only [map_sum, map_mul, lineR_C, lineR_X, sum_smul]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, smul_eq_C_mul, ← mul_assoc, ← map_mul]

end Line

/-! ## The iterated derivative along a line -/

section Diag

/-- **The `n`-th derivative along a line**: `∂ⁿ_t G(t·y)` at `0` is `DⁿG(0)(y, …, y)`, for `G` analytic at `0`. -/
theorem iteratedDeriv_comp_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : E → ℂ}
    (hG : AnalyticAt ℂ G 0) (y : E) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => G (t • y)) 0 = iteratedFDeriv ℂ n G 0 (fun _ => y) := by
  obtain ⟨r, hr, hGr⟩ := hG.exists_ball_analyticOnNhd
  let g : ℂ →L[ℂ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) y
  have hs : IsOpen (g ⁻¹' Metric.ball 0 r) := Metric.isOpen_ball.preimage g.continuous
  have h0 : g 0 ∈ Metric.ball 0 r := by simp [hr]
  have h := g.iteratedFDerivWithin_comp_right (hGr.contDiffOn (n := n) Metric.isOpen_ball.uniqueDiffOn)
    Metric.isOpen_ball.uniqueDiffOn hs.uniqueDiffOn h0 le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hs (show (0 : ℂ) ∈ g ⁻¹' Metric.ball 0 r from h0),
    iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball h0] at h
  rw [iteratedDeriv_eq_iteratedFDeriv, show (fun t : ℂ => G (t • y)) = G ∘ g from rfl, h]
  simp [g]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The multinomial expansion of `DⁿG(0)(y, …, y)`**: `Σ_{|d| = n} (n!/d!)·∂^dG(0)·y^d`, for `G` analytic at `0`
(multilinearity over the words, `pd_wordIdx`, `card_wordIdx_eq`). -/
theorem iteratedFDeriv_diag {G : (ι → ℂ) → ℂ} (hG : AnalyticAt ℂ G 0) (y : ι → ℂ) (n : ℕ) :
    iteratedFDeriv ℂ n G 0 (fun _ => y) =
      ∑ d ∈ finsuppAntidiag univ n, (d.multinomial : ℂ) * (pd G d * d.prod fun i k => y i ^ k) := by
  have hy : (fun _ : Fin n => y) = fun _ => ∑ i, y i • (Pi.single i 1 : ι → ℂ) := by
    funext _ j
    simp [Pi.single_apply]
  rw [hy, ContinuousMultilinearMap.map_sum]
  simp only [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  rw [← sum_fiberwise_of_maps_to (g := wordIdx) (t := finsuppAntidiag univ n) fun σ _ => wordIdx_mem σ]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_congr rfl (g := fun _ => pd G d * d.prod fun i k => y i ^ k), sum_const, card_wordIdx_eq hd,
    nsmul_eq_mul]
  intro σ hσ
  rw [(mem_filter.1 hσ).2.symm, pd_wordIdx hG, prod_eq_wordIdx_prod, mul_comm]

end Diag

/-! ## The multivariable Taylor series -/

section Tay

open Filter Topology

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `mtay G = Σ_m (∂^m G(0)/m!)·X^m` (the chain's `pd`, divided by `m!`). -/
def mtay (G : (ι → ℂ) → ℂ) : MvPowerSeries ι ℂ :=
  fun m => pd G m / (m.prod fun _ k => (k.factorial : ℂ))

/-- **The coefficients of `mtay`**, by definition. -/
theorem coeff_mtay (G : (ι → ℂ) → ℂ) (m : ι →₀ ℕ) :
    MvPowerSeries.coeff m (mtay G) = pd G m / (m.prod fun _ k => (k.factorial : ℂ)) := rfl

/-- **A function analytic at `0` is analytic at `0` on every line through `0`.** -/
theorem analyticAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : E → ℂ} (hG : AnalyticAt ℂ G 0)
    (y : E) : AnalyticAt ℂ (fun t : ℂ => G (t • y)) 0 :=
  hG.comp_of_eq ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) y).analyticAt 0) (by simp)

/-- **`mtay` on a line is `tay`**: `mtay G(t·y) = tay(t ↦ G(t·y))` for `G` analytic at `0`. -/
theorem lineR_mtay {G : (ι → ℂ) → ℂ} (hG : AnalyticAt ℂ G 0) (y : ι → ℂ) :
    lineR y (mtay G) = tay fun t => G (t • y) := by
  ext n
  rw [coeff_lineR, coeff_tay, iteratedDeriv_comp_smul hG, iteratedFDeriv_diag hG, sum_div]
  refine sum_congr rfl fun d hd => ?_
  rw [coeff_mtay]
  have hm : (d.prod fun _ k => (k.factorial : ℂ)) * d.multinomial = n.factorial := by
    have h1 := Nat.multinomial_spec d.support d
    rw [← Finsupp.multinomial_eq] at h1
    rw [mem_finsuppAntidiag'] at hd
    rw [← hd.1]
    simp only [Finsupp.prod, Finsupp.sum]
    exact_mod_cast h1
  have hf : (d.prod fun _ k => (k.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (d i).factorial_ne_zero
  have hmu : (d.multinomial : ℂ) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hm
    exact n.factorial_ne_zero (by exact_mod_cast hm.symm)
  rw [← hm]
  field_simp

/-- **`mtay G` is the series whose restriction to every line is `tay` of `G` there.** -/
theorem eq_of_lineR_mtay {G : (ι → ℂ) → ℂ} (hG : AnalyticAt ℂ G 0) {F : MvPowerSeries ι ℂ}
    (h : ∀ y, tay (fun t => G (t • y)) = lineR y F) : mtay G = F :=
  eq_of_lineR fun y => (lineR_mtay hG y).trans (h y)

/-- **`mtay` is additive** on functions analytic at `0`. -/
theorem mtay_add {G₁ G₂ : (ι → ℂ) → ℂ} (h₁ : AnalyticAt ℂ G₁ 0) (h₂ : AnalyticAt ℂ G₂ 0) :
    mtay (G₁ + G₂) = mtay G₁ + mtay G₂ := by
  ext m
  rw [map_add, coeff_mtay, coeff_mtay, coeff_mtay, pd, pd, pd,
    iteratedFDeriv_add_apply h₁.contDiffAt h₂.contDiffAt, add_apply, add_div]

/-- **`mtay` is `ℂ`-linear** on functions analytic at `0`. -/
theorem mtay_smul (c : ℂ) {G : (ι → ℂ) → ℂ} (h : AnalyticAt ℂ G 0) :
    mtay (c • G) = MvPowerSeries.C c * mtay G := by
  ext m
  rw [MvPowerSeries.coeff_C_mul, coeff_mtay, coeff_mtay, pd, pd, iteratedFDeriv_const_smul_apply h.contDiffAt,
    smul_apply, smul_eq_mul, mul_div_assoc]

/-- **`mtay` is multiplicative** on functions analytic at `0` (`tay_mul` on every line). -/
theorem mtay_mul {G₁ G₂ : (ι → ℂ) → ℂ} (h₁ : AnalyticAt ℂ G₁ 0) (h₂ : AnalyticAt ℂ G₂ 0) :
    mtay (G₁ * G₂) = mtay G₁ * mtay G₂ :=
  eq_of_lineR_mtay (h₁.mul h₂) fun y => by
    rw [map_mul, lineR_mtay h₁, lineR_mtay h₂]
    exact tay_mul (analyticAt_line h₁ y) (analyticAt_line h₂ y)

/-- **`∂⁰G(0) = G(0)`.** -/
theorem pd_zero (G : (ι → ℂ) → ℂ) : pd G 0 = G 0 := by
  have h : ∀ (k : ℕ) (v : Fin k → ι → ℂ), k = 0 → iteratedFDeriv ℂ k G 0 v = G 0 := by
    rintro k v rfl
    simp
  exact h _ _ (by simp)

/-- **`mtay` of a constant.** -/
theorem mtay_const (c : ℂ) : mtay (fun _ : ι → ℂ => c) = MvPowerSeries.C c := by
  ext m
  rw [coeff_mtay, MvPowerSeries.coeff_C]
  by_cases hm : m = 0
  · subst hm
    simp [pd_zero]
  · have : Multiset.card (Finsupp.toMultiset m) ≠ 0 := by
      rw [Ne, Multiset.card_eq_zero]
      intro h0
      apply hm
      rw [← Finsupp.toMultiset_toFinsupp m, h0, map_zero]
    rw [pd, iteratedFDeriv_const_of_ne this, ite_eq_right hm]
    simp

/-- **The constant term of `mtay G` is `G(0)`.** -/
theorem constantCoeff_mtay (G : (ι → ℂ) → ℂ) : MvPowerSeries.constantCoeff (mtay G) = G 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mtay, pd_zero]
  simp

/-- **`mtay` only sees a neighbourhood of `0`.** -/
theorem mtay_congr {G₁ G₂ : (ι → ℂ) → ℂ} (h : G₁ =ᶠ[𝓝 0] G₂) : mtay G₁ = mtay G₂ := by
  ext m
  rw [coeff_mtay, coeff_mtay, pd, pd, (h.iteratedFDeriv ℂ _).eq_of_nhds]

/-- **`mtay` of a finite sum.** -/
theorem mtay_sum {α : Type} (s : Finset α) {G : α → (ι → ℂ) → ℂ} (hG : ∀ a ∈ s, AnalyticAt ℂ (G a) 0) :
    mtay (fun z => ∑ a ∈ s, G a z) = ∑ a ∈ s, mtay (G a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mtay_const (ι := ι) 0
  | insert b s hb ih =>
    simp only [sum_insert hb]
    rw [← ih fun a ha => hG a (mem_insert_of_mem ha)]
    exact mtay_add (hG b (mem_insert_self b s)) (analyticAt_fun_sum _ fun a ha => hG a (mem_insert_of_mem ha))

/-- **`mtay` of a finite product.** -/
theorem mtay_prod {α : Type} (s : Finset α) {G : α → (ι → ℂ) → ℂ} (hG : ∀ a ∈ s, AnalyticAt ℂ (G a) 0) :
    mtay (fun z => ∏ a ∈ s, G a z) = ∏ a ∈ s, mtay (G a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mtay_const (ι := ι) 1
  | insert b s hb ih =>
    simp only [prod_insert hb]
    rw [← ih fun a ha => hG a (mem_insert_of_mem ha)]
    exact mtay_mul (hG b (mem_insert_self b s)) (analyticAt_fun_prod _ fun a ha => hG a (mem_insert_of_mem ha))

/-- **Linear substitution**: `mtay (G ∘ L) = (mtay G)(L·X)`. -/
theorem mtay_comp_linear (L : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)) {G : (ι → ℂ) → ℂ} (h : AnalyticAt ℂ G 0) :
    mtay (G ∘ L) = MvPowerSeries.subst
      (fun i => ∑ k, MvPowerSeries.C (L (Pi.single k 1) i) * (MvPowerSeries.X k : MvPowerSeries κ ℂ)) (mtay G) := by
  set a : ι → MvPowerSeries κ ℂ := fun i => ∑ k, MvPowerSeries.C (L (Pi.single k 1) i) * MvPowerSeries.X k
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp [a]
  have hGL : AnalyticAt ℂ (G ∘ L) 0 := by
    have := h.comp_of_eq ((LinearMap.toContinuousLinearMap L).analyticAt 0) (map_zero _)
    simpa using this
  refine eq_of_lineR_mtay hGL fun y => ?_
  have hLy : (fun i => MvPowerSeries.subst (fun k => y k • (X : ℂ⟦X⟧)) (a i)) = fun i => L y i • X := by
    funext i
    have hy : L y = ∑ k, y k • L (Pi.single k 1) := by
      conv_lhs => rw [show y = ∑ k, y k • (Pi.single k 1 : κ → ℂ) by ext j; simp [Pi.single_apply]]
      simp only [map_sum, map_smul]
    rw [← lineR_apply, lineR_linear, hy]
    simp [mul_comm]
  rw [lineR_apply, MvPowerSeries.subst_comp_subst_apply ha (hasSubst_line y), hLy, ← lineR_apply, lineR_mtay h]
  simp

/-- **Reindexing**: `mtay (G(z ∘ e)) = (mtay G)(X ∘ e)`. -/
theorem mtay_comp_reindex (e : ι → κ) {G : (ι → ℂ) → ℂ} (h : AnalyticAt ℂ G 0) :
    mtay (fun z : κ → ℂ => G fun i => z (e i)) =
      MvPowerSeries.subst (fun i => (MvPowerSeries.X (e i) : MvPowerSeries κ ℂ)) (mtay G) := by
  have e2 : (fun i => ∑ k, MvPowerSeries.C (LinearMap.funLeft ℂ ℂ e (Pi.single k 1) i) *
      (MvPowerSeries.X k : MvPowerSeries κ ℂ)) = fun i => MvPowerSeries.X (e i) := by
    funext i
    rw [sum_eq_single (e i) (fun j _ hj => by simp [LinearMap.funLeft_apply, Ne.symm hj]) (by simp)]
    simp [LinearMap.funLeft_apply]
  rw [← e2, ← mtay_comp_linear _ h]
  rfl

/-- **`tay` of a dilation**, `tay(f(c·)) = tay(f)(cz)`, for `f` analytic at `0` (cf. `tay_comp_mul`). -/
theorem tay_comp_mul_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (c : ℂ) :
    tay (fun z => f (c * z)) = rescale c (tay f) := by
  ext n
  rw [coeff_tay, coeff_rescale, coeff_tay, show (fun z => f (c * z)) = fun z : ℂ => f (z • c) by
    funext z; rw [smul_eq_mul, mul_comm], iteratedDeriv_comp_smul hf, iteratedDeriv_eq_iteratedFDeriv,
    show (fun _ : Fin n => c) = fun _ => c • (1 : ℂ) by simp, ContinuousMultilinearMap.map_smul_univ]
  simp [prod_const, mul_div_assoc]

/-- **A one-variable function of a linear form**: `mtay (f(λ·z)) = (tay f)(Σ λ_i X_i)`. -/
theorem mtay_comp_form (f : ℂ → ℂ) (lam : ι → ℂ) (hf : AnalyticAt ℂ f 0) :
    mtay (fun z => f (∑ i, lam i * z i)) =
      PowerSeries.subst (∑ i, MvPowerSeries.C (lam i) * (MvPowerSeries.X i : MvPowerSeries ι ℂ)) (tay f) := by
  set a : MvPowerSeries ι ℂ := ∑ i, MvPowerSeries.C (lam i) * MvPowerSeries.X i
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero (by simp [a])
  have hF : AnalyticAt ℂ (fun z : ι → ℂ => f (∑ i, lam i * z i)) 0 := by
    let lf : (ι → ℂ) →L[ℂ] ℂ := ∑ i, lam i • ContinuousLinearMap.proj i
    have e : (fun z : ι → ℂ => f (∑ i, lam i * z i)) = f ∘ lf := by
      funext z
      simp [lf]
    rw [e]
    exact hf.comp_of_eq (lf.analyticAt 0) (map_zero _)
  refine eq_of_lineR_mtay hF fun y => ?_
  rw [lineR_apply, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const ha) (hasSubst_line y), ← PowerSeries.subst_def,
    ← lineR_apply, lineR_linear, ← PowerSeries.rescale_eq_subst, ← tay_comp_mul_of_analyticAt hf]
  congr 1
  funext t
  simp only [Pi.smul_apply, smul_eq_mul, sum_mul]
  congr 1
  exact sum_congr rfl fun i _ => by ring

/-- **A one-variable function of a coordinate**: `mtay (f(z_i)) = (tay f)(X_i)`. -/
theorem mtay_comp_coord (f : ℂ → ℂ) (i : ι) (hf : AnalyticAt ℂ f 0) :
    mtay (fun z => f (z i)) = PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι ℂ) (tay f) := by
  have h' := mtay_comp_form f (Pi.single i 1) hf
  rw [sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at h'
  simpa [Pi.single_apply] using h'

/-- **In one variable `mtay` is `tay`.** -/
theorem mtay_unit (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) : mtay (fun z : Unit → ℂ => f (z ())) = tay f :=
  (mtay_comp_coord f () hf).trans (PowerSeries.X_subst _)

/-- **A product of one-variable functions of the coordinates**: `mtay (∏_i f_i(z_i)) = ∏_i (tay f_i)(X_i)`. -/
theorem mtay_prod_coord (f : ι → ℂ → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    mtay (fun z => ∏ i, f i (z i)) =
      ∏ i, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι ℂ) (tay (f i)) := by
  rw [mtay_prod (G := fun i z => f i (z i)) univ fun i _ =>
    (hf i).comp_of_eq ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt 0) rfl]
  exact prod_congr rfl fun i _ => mtay_comp_coord (f i) i (hf i)

end Tay

end

end MvTay
