import TraceSlope

/-!
# An upper bound for the maximal slope from integral coordinates

A tool for the range (R′) of the sharp frontier (`ZetaBalance.SharpMuMax`): the maximal slope of a hermitian
`O_K`-lattice (`KLattice`, `K` totally complex) is bounded above by the weight of a family of integral coordinates
that the metric dominates. In the archive's units (`deg ↦ 2·deg + c_K·rk`, `c_K = −log 2 + log|d_K|/[K:ℚ]`, written
out as in `TraceSlope`):

**The bound** (`slopeLe_of_coord`). Let `T : K^ι → K^J` be `K`-linear and injective, with `T(M) ⊆ O_K^J`, and
`w·|σ_v(T)y|² ≤ yᴴ G_v y` at every place `v` and every `y ∈ ℂ^ι`. Then every `O_K`-stable saturated sublattice has
slope at most `−log w`: `μ_max ≤ −log w`. Denominators are absorbed by scaling: `T(M) ⊆ D⁻¹O_K^J` gives the
coordinates `D·T` of weight `w/D²`, so the bound `2·log D − log w`.

**The route.** A sublattice `a` of `ψ(M)` comes from the `O_K`-module `A = M ∩ ψ⁻¹(a)`; let `W` be its `K`-span, of
dimension `s`, with a basis `P : K^s → W`.
* *Coordinates* (`exists_coord_inj`): `T(W)` projects injectively onto `s` of the coordinates of `K^J`, as the
  coordinate forms span the dual of `T(W)` (`Submodule.span_eq_top_of_ne_zero`) and contain a basis of it. Let
  `R : K^J → K^I` be that projection and `B = R ∘ T`: `B∘P : K^s → K^I` is injective, between spaces of equal
  dimension.
* *The span of `a`* is the image of `Ψ = (A_v σ_v(P))_v : ⊕_v ℂ^s → ⊕_v ℂ^ι` (`Ψ(ψ₀ c) = ψ(Pc)`): it contains `ψ(W)`
  (`a` is stable under `O_K`, so its span under `K ⊗ ℝ`, `HermitianLattice.act_mem`), hence the image of `Ψ`
  (`sum_act_ψ₀`); and `a ⊆ ψ(W)`.
* *The map* `Φ = hom B` into `O_K^I` with the metric `1` sends `Ψ` to `(A'_v σ_v(BP))_v`, injective at every place
  (`HermForms.mulVec_map_injective`), so bijective; hence `rk a = [K:ℚ]·s` and `Φ(span a)` is everything. It has
  norm at most `w^{−1/2}` (`norm_hom_sq_le`: `w·|σ_v(B)y|² ≤ w·|σ_v(T)y|² ≤ yᴴG_v y`).
* *Volumes.* For a `ℤ`-basis `b` of `a`, `Φ ∘ b` lies in `ψ(O_K^I)` and spans, so
  `covol ψ(O_K^I) ≤ vol(Φ ∘ b) ≤ w^{−rk a/2}·covol a` (`EuclidLattice.covol_le`, `GramVolume.vol_comp_le`), and
  `covol ψ(O_K^I)` is K3 with the metric `1` (`degK_const`): its archive slope is `0`. So
  `2·deg a + c_K·rk a ≤ −log w·rk a`.
-/

namespace KLattice

open Module Submodule NumberField HermitianLattice Matrix

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical ComplexOrder InnerProductSpace nonZeroDivisors

/-- **Coordinates on a subspace**: a subspace `U ⊆ F^J` has `dim U` coordinates on which it projects injectively.
The coordinate forms restricted to `U` separate its points, so they span its dual (`span_eq_top_of_ne_zero`), and a
linearly independent subfamily (`exists_linearIndependent'`) is a basis of the dual, of `dim U` members. -/
theorem exists_coord_inj {F : Type} [Field F] {J : Type} [Fintype J] (U : Submodule F (J → F)) :
    ∃ (I : Type) (_ : Fintype I) (e : I → J), Function.Injective e ∧ Fintype.card I = finrank F U ∧
      ∀ u ∈ U, (∀ i, u (e i) = 0) → u = 0 := by
  let f : J → Module.Dual F U := fun j => (LinearMap.proj j).comp U.subtype
  have hsep : ∀ z : U, z ≠ 0 → ∃ φ ∈ Set.range f, φ z ≠ 0 := fun z hz => by
    by_contra h
    push Not at h
    exact hz (Subtype.ext (funext fun j => h _ ⟨j, rfl⟩))
  have hspan : span F (Set.range f) = ⊤ := Submodule.span_eq_top_of_ne_zero hsep
  obtain ⟨I, a, ha, hsp, hli⟩ := exists_linearIndependent' F f
  have : Finite I := Finite.of_injective a ha
  let : Fintype I := Fintype.ofFinite I
  have hsp' : span F (Set.range (f ∘ a)) = ⊤ := hsp.trans hspan
  refine ⟨I, inferInstance, a, ha, ?_, fun u hu h0 => ?_⟩
  · rw [← Subspace.dual_finrank_eq, finrank_eq_card_basis (Basis.mk hli hsp'.ge)]
  · have h1 : ∀ φ : Module.Dual F U, φ ⟨u, hu⟩ = 0 := fun φ => by
      have hφ : φ ∈ span F (Set.range (f ∘ a)) := hsp' ▸ mem_top
      induction hφ using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨i, rfl⟩ := hφ
        exact h0 i
      | zero => rfl
      | add φ ψ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
      | smul c φ _ h => rw [LinearMap.smul_apply, h, smul_zero]
    exact congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff F (⟨u, hu⟩ : U)).1 h1)

variable {K : Type} [Field K] [NumberField K] {ι J : Type} [Fintype ι] [Fintype J]

/-- **The norm of the map of `B`**, in coordinates: if `w·|σ_v(B)y|² ≤ yᴴ G_v y` at every place `v` and every
`y ∈ ℂ^ι`, then `w·‖hom B y‖² ≤ ‖y‖²` for a target with the metric `1`. With `y = A z` (`A_v` the factors of `X`),
`hom B y = A'σ(B)z` with `A'` unitary, so `‖hom B y‖² = Σ_v |σ_v(B)z_v|²`, and `‖y‖² = Σ_v z_vᴴ G_v z_v`. -/
theorem norm_hom_sq_le {I : Type} [Fintype I] (X : KLattice K ι) (Z : KLattice K I) (hZ : ∀ v, Z.G v = 1)
    (B : (ι → K) →ₗ[K] (I → K)) {w : ℝ}
    (hG : ∀ (v : Pl K) (y : ι → ℂ), w * ∑ k, ‖∑ i, v.1.embedding (B (Pi.single i 1) k) * y i‖ ^ 2 ≤
      (∑ i, ∑ i', starRingEnd ℂ (y i) * X.G v i i' * y i').re) (y : Space K ι) :
    w * ‖X.hom Z B y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  set σB : Pl K → Matrix I ι ℂ := fun v => (LinearMap.toMatrix' B).map v.1.embedding
  have hmul (v : Pl K) : X.factor v * (X.factor v)⁻¹ = 1 := mul_eq_one_comm.1 (X.inv_mul_factor v)
  obtain ⟨z, hy, hB⟩ : ∃ z, y = op X.factor z ∧ X.hom Z B y = op Z.factor (op σB z) := by
    refine ⟨op (fun v => (X.factor v)⁻¹) y, ?_,
      (op_mul (fun v => (X.factor v)⁻¹) (fun v => Z.factor v * σB v) y).trans (op_mul σB Z.factor _)⟩
    rw [← op_mul (fun v => (X.factor v)⁻¹) X.factor y]
    simp_rw [hmul]
    rw [op_one]
  have hZn (u : Space K I) : ‖op Z.factor u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, inner_op, ← op_mul]
    simp_rw [Z.factor_spec, hZ]
    rw [op_one]
  have hcoord (u : Space K I) : ‖u‖ ^ 2 = ∑ v : Pl K, ∑ k, ‖coord (k, v) u‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, inner_apply, RCLike.re_to_complex, Complex.re_sum, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hX : ‖y‖ ^ 2 = ∑ v : Pl K,
      (∑ i, ∑ i', starRingEnd ℂ (coord (i, v) z) * X.G v i i' * coord (i', v) z).re := by
    rw [hy, @norm_sq_eq_re_inner ℂ, inner_op, ← op_mul]
    simp_rw [X.factor_spec]
    rw [inner_apply, RCLike.re_to_complex, Complex.re_sum, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coord_op, Finset.mul_sum]
    exact congrArg Complex.re (Finset.sum_congr rfl fun i' _ => by ring)
  rw [hB, hZn, hcoord, hX, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have h := hG v fun i => coord (i, v) z
  convert h using 4 with k
  rw [coord_op]
  simp only [σB, Matrix.map_apply, LinearMap.toMatrix'_apply]

variable [IsTotallyComplex K]

/-- **The standard lattice** `O_K^I` with the metric `1` at every place. -/
noncomputable def stdK (I : Type) [Fintype I] : KLattice K I :=
  have : (pi Set.univ fun _ : I => (1 : Submodule (𝓞 K) K)).IsLattice K := by
    have := HermForms.isLattice_pi (ι := I) (𝔠 := fun _ => (1 : FractionalIdeal (𝓞 K)⁰ K)) fun _ => one_ne_zero
    rwa [FractionalIdeal.coe_one] at this
  ⟨pi Set.univ fun _ => (1 : Submodule (𝓞 K) K), fun _ => 1, fun _ => PosDef.one⟩

/-- **The covolume of the standard lattice** (K3 with the metric `1`, `degK_const`):
`−log covol ψ(O_K^I) = −|I|·([K:ℚ]/2)·(log|d_K|/[K:ℚ] − log 2)`. -/
theorem neg_log_covol_stdK (I : Type) [Fintype I] :
    -Real.log (EuclidLattice.covol (stdK (K := K) I).lattice) =
      -(Fintype.card I * (finrank ℚ K / 2 : ℝ) * (Real.log |(discr K : ℝ)| / finrank ℚ K - Real.log 2)) := by
  have h := degK_const (stdK (K := K) I) 1 rfl fun _ => (Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one).symm
  simp only [det_one, Real.log_one, mul_zero, zero_sub] at h
  exact h


omit [IsTotallyComplex K] in
/-- **A block-diagonal map is injective** when each of its blocks is. -/
theorem op_injective {κ : Type} [Fintype κ] {S : Pl K → Matrix κ ι ℂ}
    (hS : ∀ v, Function.Injective (S v).mulVec) : Function.Injective (op S) := fun y y' h => ext_coord fun p => by
  have hv : (S p.2).mulVec (fun i => coord (i, p.2) y) = (S p.2).mulVec (fun i => coord (i, p.2) y') := by
    funext k
    have := congrArg (coord (k, p.2)) h
    simpa only [coord_op, mulVec, dotProduct] using this
  exact congrFun (hS p.2 hv) p.1

/-- **The maximal slope from integral coordinates** (main): if `T : K^ι → K^J` is injective, `T(M) ⊆ O_K^J` and
`w·|σ_v(T)y|² ≤ yᴴ G_v y` at every place, then `μ_max ≤ −log w` in the archive's units. See the module docstring for
the route. -/
theorem slopeLe_of_coord (X : KLattice K ι) (T : (ι → K) →ₗ[K] (J → K)) (hT : Function.Injective T)
    (hM : ∀ x ∈ X.M, ∀ j, T x j ∈ (1 : Submodule (𝓞 K) K)) {w : ℝ} (hw : 0 < w)
    (hG : ∀ (v : Pl K) (y : ι → ℂ), w * ∑ j, ‖∑ i, v.1.embedding (T (Pi.single i 1) j) * y i‖ ^ 2 ≤
      (∑ i, ∑ i', starRingEnd ℂ (y i) * X.G v i i' * y i').re) :
    (X.toPlaceLattice.slopeLattice.rescale (-Real.log 2 + Real.log |(discr K : ℝ)| / finrank ℚ K)).SlopeLe
      (-Real.log w) := by
  rintro ⟨⟨A, haΛ, hsat⟩, hstab⟩
  have hst : Stable part A := hstab
  have : DiscreteTopology A := EuclidLattice.discrete_of_le haΛ
  set c := -Real.log 2 + Real.log |(discr K : ℝ)| / finrank ℚ K
  show 2 * -Real.log (EuclidLattice.covol A) + c * (finrank ℝ (span ℝ (A : Set (Space K ι))) : ℝ) ≤
    -Real.log w * (finrank ℝ (span ℝ (A : Set (Space K ι))) : ℝ)
  -- the `K`-span `W` of the `O_K`-module of `a`, with a basis `P`
  set W : Submodule K (ι → K) := span K {x | x ∈ X.M ∧ X.ψ x ∈ A} with hW
  set s := finrank K W
  set β := Module.finBasis K W
  set Pm : Matrix ι (Fin s) K := fun i j => (β j : ι → K) i
  have hPm (c' : Fin s → K) : Pm *ᵥ c' = ((∑ j, c' j • β j : W) : ι → K) := by
    funext i
    simp only [mulVec, dotProduct, Pm, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm]
  have hPmW (c' : Fin s → K) : Pm *ᵥ c' ∈ W := by
    rw [hPm]
    exact Submodule.coe_mem _
  have hWPm : ∀ x ∈ W, ∃ c' : Fin s → K, Pm *ᵥ c' = x := fun x hx =>
    ⟨β.repr ⟨x, hx⟩, by rw [hPm, β.sum_repr]⟩
  -- the span of `a` is stable under `K ⊗ ℝ` and contains `ψ(W)`
  have hU : ∀ k : 𝓞 K, ∀ y ∈ span ℝ (A : Set (Space K ι)), act part (emb (k : K)) y ∈ span ℝ (A : Set _) :=
    fun k _ hy => span_stable hst k hy
  have hψW : ∀ x ∈ W, X.ψ x ∈ span ℝ (A : Set (Space K ι)) := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx => exact subset_span hx.2
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul k x _ hx => rw [X.ψ_smul]; exact act_mem hU _ hx
  -- `Ψ = (A_v σ_v(P))_v`, whose image is the span of `a`
  set Ψ : Space K (Fin s) →L[ℂ] Space K ι := op fun v => X.factor v * Pm.map v.1.embedding with hΨdef
  have hΨψ₀ (c' : Fin s → K) : Ψ (ψ₀ c') = X.ψ (Pm *ᵥ c') := by
    rw [hΨdef, op_mul, op_ψ₀, ψ_apply]
  have hΨact (z : Pl K → ℂ) (y : Space K (Fin s)) : Ψ (act part z y) = act part z (Ψ y) := op_act _ _ _
  have hΨ_mem (y : Space K (Fin s)) : Ψ y ∈ span ℝ (A : Set (Space K ι)) := by
    rw [← sum_act_ψ₀ y, map_sum]
    refine Submodule.sum_mem _ fun p _ => ?_
    rw [hΨact, hΨψ₀]
    exact act_mem hU _ (hψW _ (hPmW _))
  set Ψr : Space K (Fin s) →ₗ[ℝ] Space K ι := (Ψ : Space K (Fin s) →ₗ[ℂ] Space K ι).restrictScalars ℝ
  have hspan_eq : span ℝ (A : Set (Space K ι)) = LinearMap.range Ψr := by
    refine le_antisymm (span_le.2 fun y hy => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := haΛ hy
      obtain ⟨c', rfl⟩ := hWPm x (subset_span ⟨hx, hy⟩)
      exact ⟨ψ₀ c', hΨψ₀ c'⟩
    · rintro _ ⟨y, rfl⟩
      exact hΨ_mem y
  -- coordinates on `T(W)`, and `B = R ∘ T`
  obtain ⟨I, _, e, he, hcard, hinj⟩ := exists_coord_inj (W.map T)
  have hsI : Fintype.card I = s := by
    rw [hcard]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective T hT W)).symm
  set B : (ι → K) →ₗ[K] (I → K) := LinearMap.funLeft K K e ∘ₗ T with hBdef
  have hBapp (x : ι → K) (i : I) : B x i = T x (e i) := rfl
  -- `B ∘ P` is injective
  set Q : Matrix I (Fin s) K := LinearMap.toMatrix' B * Pm with hQdef
  have hQ : Function.Injective Q.mulVec := by
    intro c₁ c₂ h
    have h0 : Q *ᵥ (c₁ - c₂) = 0 := by rw [mulVec_sub, h, sub_self]
    have hT0 : T (Pm *ᵥ (c₁ - c₂)) = 0 := hinj _ ⟨_, hPmW _, rfl⟩ fun i => by
      have := congrFun h0 i
      rwa [hQdef, ← mulVec_mulVec, LinearMap.toMatrix'_mulVec, hBapp] at this
    have hP0 : Pm *ᵥ (c₁ - c₂) = 0 := hT (by rw [hT0, map_zero])
    rw [hPm] at hP0
    have h3 := Fintype.linearIndependent_iff.1 β.linearIndependent _ (Subtype.ext hP0)
    funext j
    exact sub_eq_zero.1 (h3 j)
  -- the target `O_K^I` with the metric `1`, and the map `Φ` of `B`
  set Z : KLattice K I := stdK I with hZdef
  have hZG : ∀ v, Z.G v = 1 := fun _ => rfl
  set Φ : Space K ι →L[ℝ] Space K I := (X.hom Z B).restrictScalars ℝ with hΦdef
  have hΦΨ (y : Space K (Fin s)) : Φ (Ψ y) = op (fun v => Z.factor v * Q.map v.1.embedding) y := by
    have e : (fun v => (Z.factor v * (LinearMap.toMatrix' B).map v.1.embedding * (X.factor v)⁻¹) *
        (X.factor v * Pm.map v.1.embedding)) = fun v => Z.factor v * Q.map v.1.embedding := by
      funext v
      simp only [hQdef, Matrix.map_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (X.factor v)⁻¹, X.inv_mul_factor, Matrix.one_mul]
    show op _ (op _ y) = _
    rw [← op_mul, e]
  set L : Space K (Fin s) →ₗ[ℝ] Space K I := (Φ : Space K ι →ₗ[ℝ] Space K I) ∘ₗ Ψr
  have hLapp (y : Space K (Fin s)) : L y = Φ (Ψ y) := rfl
  have hLinj : Function.Injective L := by
    intro y y' h
    rw [hLapp, hLapp, hΦΨ, hΦΨ] at h
    refine op_injective (fun v => ?_) h
    intro u u' hu
    have := congrArg (fun t => (Z.factor v)⁻¹ *ᵥ t) hu
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, Z.inv_mul_factor, Matrix.one_mul] at this
    exact HermForms.mulVec_map_injective v.1.embedding hQ this
  have hfr (κ : Type) [Fintype κ] : finrank ℝ (Space K κ) = Fintype.card κ * finrank ℚ K := by
    rw [finrank_space, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hLsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hfr, hfr, hsI, Fintype.card_fin])).1 hLinj
  have hΨinj : Function.Injective Ψr := fun y y' h => hLinj (by rw [hLapp, hLapp]; exact congrArg Φ h)
  have hr : finrank ℝ (span ℝ (A : Set (Space K ι))) = s * finrank ℚ K := by
    rw [hspan_eq, LinearMap.finrank_range_of_inj hΨinj, hfr, Fintype.card_fin]
  -- the volumes, through a `ℤ`-basis `b` of `a`
  have hBM : ∀ x ∈ X.M, B x ∈ Z.M := fun x hx i _ => hM x hx (e i)
  have hGB : ∀ (v : Pl K) (y : ι → ℂ), w * ∑ k, ‖∑ i, v.1.embedding (B (Pi.single i 1) k) * y i‖ ^ 2 ≤
      (∑ i, ∑ i', starRingEnd ℂ (y i) * X.G v i i' * y i').re := fun v y => by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hw.le) (hG v y)
    calc ∑ k, ‖∑ i, v.1.embedding (B (Pi.single i 1) k) * y i‖ ^ 2
        = ∑ j ∈ Finset.univ.image e, ‖∑ i, v.1.embedding (T (Pi.single i 1) j) * y i‖ ^ 2 :=
          by rw [Finset.sum_image fun x _ y _ h => he h]; rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hnormΦ : ‖Φ‖ ≤ (Real.sqrt w)⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hsw.le) fun y => ?_
    have h := norm_hom_sq_le X Z hZG B hGB y
    have h2 : (Real.sqrt w * ‖Φ y‖) ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hw.le]
      exact h
    have h3 := (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 h2
    rw [inv_mul_eq_div, le_div_iff₀ hsw]
    linarith
  set n := finrank ℤ A
  have hn : finrank ℝ (span ℝ (A : Set (Space K ι))) = n := EuclidLattice.finrank_span A
  set b := Module.finBasis ℤ A
  have hv : ∀ i, Φ (b i) ∈ Z.lattice := fun i => X.hom_mem Z hBM _ (haΛ (b i).2)
  have hspan : span ℝ (Z.lattice : Set (Space K I)) ≤ span ℝ (Set.range fun i => Φ (b i)) := by
    rw [Z.span_lattice]
    intro y' _
    obtain ⟨y, rfl⟩ := hLsurj y'
    have hmem : Ψ y ∈ span ℝ (Set.range fun i => (b i : Space K ι)) := by
      rw [EuclidLattice.span_basis b]
      exact hΨ_mem y
    have := Submodule.apply_mem_span_image_of_mem_span (Φ : Space K ι →ₗ[ℝ] Space K I) hmem
    rw [← Set.range_comp] at this
    exact this
  have hcard : Fintype.card (Fin n) ≤ finrank ℤ Z.lattice := by
    rw [Fintype.card_fin, ← EuclidLattice.finrank_span, Z.span_lattice, finrank_top, hfr, hsI, ← hn, hr]
  have h1 : EuclidLattice.covol Z.lattice ≤ GramVolume.vol fun i => Φ (b i) := EuclidLattice.covol_le hv hspan hcard
  have h2 : (GramVolume.vol fun i => Φ (b i)) ≤ ‖Φ‖ ^ n * EuclidLattice.covol A := by
    have := GramVolume.vol_comp_le Φ fun i => (b i : Space K ι)
    rw [Fintype.card_fin, ← EuclidLattice.covol_eq_vol b] at this
    exact this
  have h3 : ‖Φ‖ ^ n ≤ (Real.sqrt w)⁻¹ ^ n := pow_le_pow_left₀ (norm_nonneg _) hnormΦ n
  have hcA := EuclidLattice.covol_pos A
  have hcZ := EuclidLattice.covol_pos Z.lattice
  have h4 : EuclidLattice.covol Z.lattice ≤ (Real.sqrt w)⁻¹ ^ n * EuclidLattice.covol A :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_right h3 hcA.le))
  have h5 := Real.log_le_log hcZ h4
  rw [Real.log_mul (by positivity) hcA.ne', Real.log_pow, Real.log_inv, Real.log_sqrt hw.le] at h5
  have h6 := neg_log_covol_stdK (K := K) I
  have hnI : (n : ℝ) = Fintype.card I * finrank ℚ K := by
    rw [← hn, hr, hsI]
    push_cast
    ring
  rw [hn]
  have h7 : (Fintype.card I : ℝ) * (finrank ℚ K / 2 : ℝ) = n / 2 := by
    rw [hnI]
    ring
  rw [h7] at h6
  have h8 : c = Real.log |(discr K : ℝ)| / finrank ℚ K - Real.log 2 := by ring
  rw [h8]
  nlinarith

end KLattice
