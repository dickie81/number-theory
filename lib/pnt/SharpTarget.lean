import SharpInputs

/-!
# The target metric: the Petersson metric pushed through the period map

The target metric of the construction (`SharpObj.g`, read by the frame through `SharpObj.RealWith` and by (G↑)).
Whatever the metric `g` on `W_u`, a realising frame bounds the period map by heights with
`‖σ_v(B_ω)y‖_g ≤ e^{ht_v}‖y‖_{Pet}`, so `‖f‖_g ≤ e^{ht_v}‖f‖_quot` on `W_u` and `μ_g(C_u) + h̄_g ≥ μ_quot(C_u)`: the
quotient metric, for which `B_ω` is a co-isometry, makes (G↑) as weak as it can be, with heights `0`. So the
construction takes it.

**The quotient metric of a linear map** `P : V → Y` (`quotMetric`), with a form `pet` on `V` at each complex place
`v` (the Petersson form of the source). In Mathlib's basis of a finite-dimensional `V`, with `P_v` the Gram matrix of
`pet` (`petGram`) and `β` the matrix of `P` into coordinates of `range P` (`quotMat`; the coordinates `quotCoord`
are a left inverse of the inclusion of `range P`, then Mathlib's basis of `range P`), the metric on `range P` has
Gram matrix `G_v = (σ_v(β)·P_v⁻¹·σ_v(β)ᴴ)⁻¹` (`quotGram`): `‖y‖²` is the least `pet(φ, φ)` over the preimages `φ`
of `y`. It is defined with no hypothesis (`0` when `V` is infinite-dimensional).

**Its basic facts.**
* *Positive definite* (`quotGram_spec`), when `P_v` is: `β` has a right inverse (`P` maps onto `range P`), so
  `σ_v(β)ᴴ` is injective and `σ_v(β)·P_v⁻¹·σ_v(β)ᴴ` positive definite.
* *A co-isometry* (`KLattice.norm_hom_le_of_coisometry`): `σ_v(β)·P_v⁻¹·σ_v(β)ᴴ = G_v⁻¹` (`quotGram_spec`) says
  that in the coordinates of the metrics, `T_v = A'_v σ_v(β) A_v⁻¹` (`A_vᴴA_v = P_v`, `A'ᴴ_vA'_v = G_v`) has
  `T_vT_vᴴ = 1`. Then `T_vᴴ` is an isometry and `T_v` a contraction (`KLattice.norm_op_le_of_mul_conjTranspose`), so
  the map of a frame is bounded by `e^0`: the heights are `0`.

**For the construction's object** (`SharpObj.gQuot`): the quotient metric of the Petersson form of a word's source
(`SharpObj.petForm`, `HermForms.petAt` at `σ_v` through the isomorphism `e`) through its period map `B_ω = P_{μ0}(ω)`.
For one word, `W_u = range B_ω` and `B_ω` is onto it.
-/

namespace KLattice

open Matrix HermitianLattice

open scoped InnerProductSpace Classical

variable {K : Type} [Field K] [NumberField K] {ι κ : Type} [Fintype ι] [Fintype κ]

/-- **A block-diagonal co-isometry is a contraction**: if `T_vT_vᴴ = 1` at every place, then `T_vᴴ` is an isometry,
and `‖Ty‖² = Re⟪y, TᴴTy⟫ ≤ ‖y‖·‖TᴴTy‖ = ‖y‖·‖Ty‖`. -/
theorem norm_op_le_of_mul_conjTranspose {T : Pl K → Matrix κ ι ℂ} (hT : ∀ v, T v * (T v)ᴴ = 1)
    (y : Space K ι) : ‖op T y‖ ≤ ‖y‖ := by
  have hadj : ∀ z : Space K κ, ‖op (fun v => (T v)ᴴ) z‖ = ‖z‖ := fun z => by
    have h : ⟪op (fun v => (T v)ᴴ) z, op (fun v => (T v)ᴴ) z⟫_ℂ = ⟪z, z⟫_ℂ := by
      rw [inner_op, ← op_mul]
      simp_rw [conjTranspose_conjTranspose, hT, op_one]
    have h2 := congrArg RCLike.re h
    rw [← norm_sq_eq_re_inner (𝕜 := ℂ), ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h2
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  have h1 : ‖op T y‖ ^ 2 ≤ ‖y‖ * ‖op T y‖ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_op, ← hadj (op T y)]
    exact re_inner_le_norm (𝕜 := ℂ) _ _
  nlinarith [norm_nonneg (op T y), norm_nonneg y]

/-- **The map of a co-isometry is a contraction**: if `σ_v(B)·G_X,v⁻¹·σ_v(B)ᴴ = G_Y,v⁻¹` at every place, the map of
`B` (`KLattice.hom`, blockwise `T_v = A'_v σ_v(B) A_v⁻¹`) has `T_vT_vᴴ = A'_v G_Y,v⁻¹ A'ᴴ_v = 1`. The inverses are
taken for any decidable equality on the coordinates (all agree; `KLattice.hom` uses the classical one). -/
theorem norm_hom_le_of_coisometry [DecidableEq ι] [DecidableEq κ] (X : KLattice K ι) (Y : KLattice K κ)
    (B : (ι → K) →ₗ[K] (κ → K)) (h : ∀ v : Pl K, (LinearMap.toMatrix' B).map v.1.embedding * (X.G v)⁻¹ *
      ((LinearMap.toMatrix' B).map v.1.embedding)ᴴ = (Y.G v)⁻¹) (y : Space K ι) : ‖X.hom Y B y‖ ≤ ‖y‖ := by
  obtain rfl : ‹DecidableEq ι› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  obtain rfl : ‹DecidableEq κ› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  refine norm_op_le_of_mul_conjTranspose (fun v => ?_) y
  set M := (LinearMap.toMatrix' B).map v.1.embedding
  set A := X.factor v
  set A' := Y.factor v
  have hA : A⁻¹ * A⁻¹ᴴ = (X.G v)⁻¹ := by
    rw [← X.factor_spec v, Matrix.mul_inv_rev, conjTranspose_nonsing_inv]
  have hA' : A' * A'⁻¹ = 1 := mul_eq_one_comm.1 (Y.inv_mul_factor v)
  have hA'' : A'ᴴ⁻¹ * A'ᴴ = 1 := by
    rw [← conjTranspose_nonsing_inv, ← conjTranspose_mul, hA', conjTranspose_one]
  calc A' * M * A⁻¹ * (A' * M * A⁻¹)ᴴ = A' * (M * (A⁻¹ * A⁻¹ᴴ) * Mᴴ) * A'ᴴ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = A' * A'⁻¹ * (A'ᴴ⁻¹ * A'ᴴ) := by
        rw [hA, h v, ← Y.factor_spec v, Matrix.mul_inv_rev]
        simp only [Matrix.mul_assoc]
        rfl
    _ = 1 := by rw [hA', hA'', Matrix.one_mul]

end KLattice

namespace ZetaBalance

open NumberField HermitianLattice Module

open scoped Matrix ComplexOrder

noncomputable section

/-! ## The quotient metric of a linear map -/

section Quot

variable {K : Type} [Field K] {V Y : Type*} [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module K Y]
  (pet : Pl K → V → V → ℂ) (P : V →ₗ[K] Y)

/-- **The coordinates of the target** `range P`: a left inverse of its inclusion (`LinearMap.leftInverse`), then
Mathlib's basis of `range P`, when `V` is finite-dimensional (`0` otherwise). -/
def quotCoord : Y →ₗ[K] (Fin (finrank K (LinearMap.range P)) → K) := by
  classical
  exact if _ : FiniteDimensional K V then
    (finBasis K (LinearMap.range P)).equivFun.toLinearMap ∘ₗ (LinearMap.range P).subtype.leftInverse
  else 0

/-- **The coordinates of a period** `P φ` are those of `P φ ∈ range P` in Mathlib's basis. -/
theorem quotCoord_apply [FiniteDimensional K V] (φ : V) :
    quotCoord P (P φ) = (finBasis K (LinearMap.range P)).equivFun (P.rangeRestrict φ) := by
  rw [quotCoord, dite_eq_left ‹_›]
  exact congrArg (finBasis K (LinearMap.range P)).equivFun
    ((LinearMap.range P).subtype.leftInverse_apply_of_inj (Submodule.ker_subtype _) (P.rangeRestrict φ))

/-- **The coordinates are injective on `range P`** (`quotCoord_apply`). -/
theorem quotCoord_injOn [FiniteDimensional K V] : Set.InjOn (quotCoord P) (LinearMap.range P) := by
  rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩ h
  rw [quotCoord_apply, quotCoord_apply] at h
  exact congrArg Subtype.val ((finBasis K (LinearMap.range P)).equivFun.injective h)

/-- **The coordinates are onto from the periods**: every coordinate vector is that of some `P φ`. -/
theorem surjective_quotCoord [FiniteDimensional K V] : Function.Surjective (quotCoord P ∘ₗ P) := fun y => by
  obtain ⟨w, rfl⟩ := (finBasis K (LinearMap.range P)).equivFun.surjective y
  obtain ⟨φ, rfl⟩ := P.surjective_rangeRestrict w
  exact ⟨φ, quotCoord_apply P φ⟩

/-- **The matrix of `P`**, from Mathlib's basis of `V` to the coordinates of `range P`. -/
def quotMat [FiniteDimensional K V] : Matrix (Fin (finrank K (LinearMap.range P))) (Fin (finrank K V)) K :=
  LinearMap.toMatrix' (quotCoord P ∘ₗ P ∘ₗ (finBasis K V).equivFun.symm.toLinearMap)

/-- **The Gram matrix of `pet`** at a complex place, in Mathlib's basis of `V`. -/
def petGram [FiniteDimensional K V] (v : Pl K) : Matrix (Fin (finrank K V)) (Fin (finrank K V)) ℂ :=
  fun i j => pet v (finBasis K V i) (finBasis K V j)

/-- **The quotient Gram matrix** `G_v = (σ_v(β)·P_v⁻¹·σ_v(β)ᴴ)⁻¹` at a complex place `v`, with `β = quotMat P` and
`P_v = petGram pet v`. -/
def quotGram [FiniteDimensional K V] (v : Pl K) :
    Matrix (Fin (finrank K (LinearMap.range P))) (Fin (finrank K (LinearMap.range P))) ℂ :=
  ((quotMat P).map v.1.embedding * (petGram pet v)⁻¹ * ((quotMat P).map v.1.embedding)ᴴ)⁻¹

/-- **The quotient metric** of `pet` through `P` at a complex place `v`: the quotient Gram matrix in the coordinates
`quotCoord` (`0` when `V` is infinite-dimensional). -/
def quotMetric (v : Pl K) (y z : Y) : ℂ := by
  classical
  exact if _ : FiniteDimensional K V then
    ∑ i, ∑ k, starRingEnd ℂ (v.1.embedding (quotCoord P y i)) * quotGram pet P v i k *
      v.1.embedding (quotCoord P z k)
  else 0

/-- **The quotient metric in coordinates**, for finite-dimensional `V`. -/
theorem quotMetric_eq [FiniteDimensional K V] (v : Pl K) (y z : Y) :
    quotMetric pet P v y z = ∑ i, ∑ k, starRingEnd ℂ (v.1.embedding (quotCoord P y i)) * quotGram pet P v i k *
      v.1.embedding (quotCoord P z k) := by
  rw [quotMetric, dite_eq_left ‹_›]

open Matrix in
/-- **The quotient metric is positive definite, and `P` a co-isometry for it**, where the form is: `β` has a right
inverse (`surjective_quotCoord`), so `σ_v(β)ᴴ` is injective, `σ_v(β)·P_v⁻¹·σ_v(β)ᴴ` is positive definite, and so is
its inverse `G_v`, whose inverse it is. -/
theorem quotGram_spec [FiniteDimensional K V] (v : Pl K) (h : (petGram pet v).PosDef) :
    (quotGram pet P v).PosDef ∧ (quotGram pet P v)⁻¹ =
      (quotMat P).map v.1.embedding * (petGram pet v)⁻¹ * ((quotMat P).map v.1.embedding)ᴴ := by
  obtain ⟨g, hg⟩ := (quotCoord P ∘ₗ P ∘ₗ (finBasis K V).equivFun.symm.toLinearMap).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 fun y => by
      obtain ⟨φ, hφ⟩ := surjective_quotCoord P y
      exact ⟨(finBasis K V).equivFun φ, by simpa using hφ⟩)
  have hγ : (quotMat P).map v.1.embedding * (LinearMap.toMatrix' g).map v.1.embedding = 1 := by
    rw [← Matrix.map_mul, quotMat, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hpos := h.inv.mul_mul_conjTranspose_same (B := (quotMat P).map v.1.embedding) fun x y hxy => by
    simpa [Matrix.vecMul_vecMul, hγ] using congrArg (· ᵥ* (LinearMap.toMatrix' g).map v.1.embedding) hxy
  exact ⟨hpos.inv, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hpos.isUnit)⟩

end Quot

/-! ## The quotient metric of a word -/

namespace SharpObj

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}
  (b : SharpObj Dg C)

/-- **The Petersson form of a word** at a complex place `v`, on its source: `HermForms.petAt` at `σ_v` through the
isomorphism `e` with `X_c ⊓ V_ω`, as in `SharpObj.RealWith`. -/
def petForm (ω : b.Ω) (v : Pl C.K) (φ ψ : b.Vs ω) : ℂ :=
  HermForms.petAt (b.ST ω) (b.lam0 ω) v.1.embedding (b.e ω φ).1 (b.e ω ψ).1

/-- **The quotient metric of a word** `ω`: the Petersson metric of its source pushed through its period map
`B_ω = P_{μ0}(ω)` (`quotMetric`). For an object of one word, `W_u = range B_ω`, `B_ω` is a co-isometry onto it, and
the heights are `0`. -/
def gQuot (ω : b.Ω) : Pl C.K → (b.P.V0 b.μ0 → C.K) → (b.P.V0 b.μ0 → C.K) → ℂ :=
  quotMetric (b.petForm ω) (b.P.P b.μ0 ω)

end SharpObj

end

end ZetaBalance
