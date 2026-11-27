import CapacityTop

/-!
# Capacity-constrained spans of the path basis (T3)

For letters `0, …, N − 1` (the conventions of `PathBasis`), checkpoints `chk` (prefix lengths `i ≤ N`, prefix
`Set.Iio i`) and integers `θ_i`, `M_i`: the polynomials of multidegree `B` with `θ_i ≤ val_{<i} G` and
`top_{<i} G ≤ M_i` at the checkpoints (`capSet`) are exactly the span of the path polynomials `Ψ(P, I)` whose path has
`θ_i ≤ μ_i(n − 1)` and `μ_i(0) ≤ M_i` (`CapOK`), over every domain (`ℤ`, `O`, `Kf`, residue fields of any
characteristic).

**Main results.**
* *(E3)* `gcomp_top_linearIndependent`: for a dominant `μ₀`, the weight-`μ₀` components of the generic translates
  through the first `i` letters of the `Ψ(x)` with `μ_i = μ₀` are linearly independent (`CapacityTop`).
* *(T3)* `repr_eq_zero_of_mem_capSet` (the path-basis coordinates of a member of the capacity set vanish off the
  admissible paths) and `capSet_eq_span`, by the dominance-maximal argument of `CapacityWeights`
  (`repr_eq_zero_of_indep`, `capSet_eq_span_of_indep`) with (E3).
* *Reduction* `capSet_image_map`: a surjection of domains `O → k` maps the `O`-capacity set onto the `k`-capacity set
  (both are spans of the admissible path polynomials, which are defined over `ℤ`, `map_pathFam`).
* Proved in `CapacityWeights` and stated there: the easy inclusion over any ring (`span_subset_capSet`), the dimension
  (`finrank_capSpan`, `card_capOK`: the chain sum) and saturation (`mem_capSet_map_iff`).
-/

namespace CapacitySpan

open MvPolynomial Finset PathBasis PathSpan TwistWeights

noncomputable section

variable (R : Type*) [CommRing R] (m N : ℕ) (vec : ℕ → Bool) (B : ℕ → ℕ)

/-- **(E3) Top components are independent** (domains): for a dominant `μ₀`, the weight-`μ₀` components of the
generic translates through the first `i` letters of the `Ψ(x)` with `μ_i = μ₀` are `R`-linearly independent. -/
theorem gcomp_top_linearIndependent [IsDomain R] {i : ℕ} (hi : i ≤ N) (μ₀ : Fin (m + 1) → ℤ) :
    LinearIndependent R (fun x : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} =>
      gcomp vec (Set.Iio i) μ₀ (pathFam R x.1)) :=
  top_linearIndependent R N vec B hi μ₀

/-- **(T3, coefficient form)** over a domain, the path-basis coordinates of a member of the capacity set vanish off
the capacity-admissible paths. -/
theorem repr_eq_zero_of_mem_capSet [IsDomain R] {chk : Finset ℕ} (hchk : ∀ i ∈ chk, i ≤ N) {θ M : ℕ → ℤ}
    {G : MvPolynomial (ℕ × Fin (m + 1)) R} (hG : G ∈ capSet R m N vec B chk θ M) (x : PathIdx (m + 1) N vec B)
    (hx : ¬ CapOK chk θ M x.1) : (pathFam_basis R m N vec B).repr ⟨G, hG.1⟩ x = 0 :=
  repr_eq_zero_of_indep hchk hG (fun _ hi μ₀ => gcomp_top_linearIndependent R m N vec B hi μ₀) x hx

/-- **(T3) The capacity set is the span of the admissible path polynomials** over every domain (`ℤ`, `O`, `Kf`, the
residue field). The inclusion `⊇` holds over every commutative ring (`span_subset_capSet`). -/
theorem capSet_eq_span [IsDomain R] {chk : Finset ℕ} (hchk : ∀ i ∈ chk, i ≤ N) (θ M : ℕ → ℤ) :
    capSet R m N vec B chk θ M =
      (Submodule.span R (pathFam R '' {x : PathIdx (m + 1) N vec B | CapOK chk θ M x.1}) : Set _) :=
  capSet_eq_span_of_indep R m N vec B hchk θ M fun _ hi μ₀ => gcomp_top_linearIndependent R m N vec B hi μ₀

variable {R m N vec B}

/-- **The path family is defined over the base**: coefficient maps carry it along. -/
theorem map_pathFam {O k : Type*} [CommRing O] [CommRing k] (φ : O →+* k) {n : ℕ} (x : PathIdx n N vec B) :
    MvPolynomial.map φ (pathFam O x) = pathFam k x := by
  unfold pathFam pathPoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [TwistedDegree.colK, TwistedDegree.map_colSt]
  simp only [map_X]
  rfl

/-- **Coefficient maps and scalars.** -/
theorem map_smul' {O k σ : Type*} [CommRing O] [CommRing k] (φ : O →+* k) (c : O) (F : MvPolynomial σ O) :
    MvPolynomial.map φ (c • F) = φ c • MvPolynomial.map φ F := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

variable (m N vec B) in
/-- **Reduction** (e.g. `O → k`): the image of the capacity set under a surjection of domains is the capacity set. -/
theorem capSet_image_map {O k : Type*} [CommRing O] [IsDomain O] [CommRing k] [IsDomain k] (φ : O →+* k)
    (hφ : Function.Surjective φ) {chk : Finset ℕ} (hchk : ∀ i ∈ chk, i ≤ N) (θ M : ℕ → ℤ) :
    MvPolynomial.map φ '' capSet O m N vec B chk θ M = capSet k m N vec B chk θ M := by
  classical
  let _ : Fintype (PathIdx (m + 1) N vec B) := Fintype.ofFinite _
  ext H
  constructor
  · rintro ⟨G, hG, rfl⟩
    refine span_subset_capSet k m N vec B hchk θ M ?_
    rw [eq_sum_repr (vec := vec) hG.1, map_sum]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [map_smul', map_pathFam]
    by_cases hx : CapOK chk θ M x.1
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    · rw [repr_eq_zero_of_mem_capSet O m N vec B hchk hG x hx, map_zero, zero_smul]
      exact zero_mem _
  · intro hH
    choose c hc using fun x : PathIdx (m + 1) N vec B => hφ ((pathFam_basis k m N vec B).repr ⟨H, hH.1⟩ x)
    refine ⟨∑ x ∈ univ.filter fun x : PathIdx (m + 1) N vec B => CapOK chk θ M x.1, c x • pathFam O x,
      span_subset_capSet O m N vec B hchk θ M (Submodule.sum_mem _ fun x hx =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, (mem_filter.1 hx).2, rfl⟩)), ?_⟩
    rw [map_sum]
    conv_rhs => rw [eq_sum_repr (vec := vec) hH.1]
    rw [← Finset.sum_subset (Finset.filter_subset _ univ) fun x _ hx => by
      rw [repr_eq_zero_of_mem_capSet k m N vec B hchk hH x (by simpa using hx), zero_smul]]
    exact Finset.sum_congr rfl fun x _ => by rw [map_smul', map_pathFam, hc]

end

end CapacitySpan
