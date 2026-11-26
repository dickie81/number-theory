import Mathlib
import KLattice

/-!
# Volumes of hermitian `O_K`-lattices

The volume lemmas of the exact slope bound for the source of the sharp frontier: how the degree
`deg X = −log covol ψ(M)` of a hermitian `O_K`-lattice (`KLattice`, `K` totally complex) moves under a change of
lattice, what it is for a constant rational metric, and how it compares with blocks mapped in by scaled isometries.
With `rk X = [K:ℚ]·|ι|` (`rk_top`), the slope is `μ = deg/rk` (`degK`, `rkK`, `muK`).

**Covolumes of images** (`EuclidLattice.covol_map`). A real linear map `T` sending a full-rank discrete subgroup `M`
onto a full-rank one multiplies the covolume by `|det T|`: a `ℤ`-basis of `M` is a real basis, its image a `ℤ`-basis of
`T(M)`, and the image is the basis times the matrix of `T` (`GramVolume.vol_comb`).

**K1, an automorphism of `K^ι`** (`degK_map`): `deg g(M) = deg M − log |N_{K/ℚ}(det g)|`, with the metrics kept. The
map `hom` of `g` extends it (`hom_ψ`) and is blockwise `A_v σ_v(g) A_v⁻¹`, so its real determinant is
`∏_v |det σ_v(g)|² = ∏_v |σ_v(det g)|²` (`LinearMap.det_restrictScalars`, `Matrix.det_blockDiagonal`), which is
`|N_{K/ℚ}(det g)|` as every place is complex, of multiplicity `2` (`InfinitePlace.prod_eq_abs_norm`).

**K2, diagonal fractional ideals** (`degK_pi`): for `D(𝔠) = ∏_i 𝔠_i ⊆ K^ι`,
`deg D(𝔠) = deg O_K^ι − Σ_i log N(𝔠_i)`. The denominators `d_i` of Mathlib's `FractionalIdeal.den` scale `D(𝔠)`
onto `D(num)`, the product of the integral ideals `num_i = d_i 𝔠_i` (`FractionalIdeal.den_mul_self_eq_num`), which
costs `Σ_i log |N(d_i)|` by K1. `D(num)` has index `∏_i N(num_i)` in `O_K^ι`, a product of quotients
(`AddSubgroup.index_pi`; `Ideal.absNorm` is the index), which costs `Σ_i log N(num_i)` (`deg_withLattice`). And
`N(𝔠_i) = N(num_i)/|N(d_i)|` is Mathlib's definition (`FractionalIdeal.absNorm_eq`). The `𝔠_i` are nonzero as
`D(𝔠)` spans `K^ι`.

**K3, a constant rational metric** (`degK_const`, `muK_const`): if `G_v = Γ` for a real matrix `Γ` at every place,
`deg O_K^ι = −([K:ℚ]/2)·log det Γ − |ι|·([K:ℚ]/2)·(log|d_K|/[K:ℚ] − log 2)`. The vectors `ω_φ e_i`, for an integral
basis `ω` indexed by the embeddings `φ : K → ℂ` (`NumberField.equivReindex`), are a `ℤ`-basis, with Gram matrix
`Γ ⊗ G_O`, `(G_O)_{φφ'} = Re Σ_v conj(σ_v ω_φ)·σ_v ω_{φ'}` (`inner_ψ_single`). Pairing `σ_v` with `conj ∘ σ_v` at
each place (`sum_embeddings`) gives `2·G_O = conj(B)·Bᵀ` for Mathlib's `basisMatrix` `B`, and `det B² = d_K`
(`discr_eq_basisMatrix_det_sq`), so `det G_O = |d_K|/2^{[K:ℚ]}`; then `Matrix.det_kronecker`. In slopes,
`μ = −log det Γ/(2|ι|) − archShift(K)/2` with `archShift(K) = log|d_K|/[K:ℚ] − log 2` (written out, as it lives in
`lib/pnt`), so in the archive's units `μ_arch = 2μ + archShift(K) = −log det Γ/|ι|`: the field constant cancels.

**K4, Fischer over blocks** (`degK_ge_sum`). Let `K`-linear maps `Θ_i : K^{κ_i} → K^ι` send `M_i` into `M` (h1), with
`(y_i)_i ↦ Σ_i Θ_i y_i` bijective (h2) and `(σ_vΘ_i)ᴴ G_v (σ_vΘ_i) = s_i·G_{i,v}` at every place (h3). Then
`deg X ≥ Σ_i (deg X_i − (rk X_i/2)·log s_i)`. Take `ℤ`-bases of the `ψ_i(M_i)`, pull them back to `M_i` and push
them by `ψ ∘ Θ_i`: the Gram matrices scale by `s_i` (`inner_ψ_map`), so the volumes by `s_i^{rk_i/2}`. The joint
family lies in `ψ(M)`, spans it (as `Θ` is onto, through `hom_ψ` and `span_lattice`) and has `[K:ℚ]·Σ_i|κ_i| = rk`
members, so it bounds `covol ψ(M)` (`EuclidLattice.covol_le`); Fischer's inequality, one block at a time, bounds its
volume by the product of the blocks' (`GramVolume.vol_le_prod_fiber`).
-/

namespace EuclidLattice

open Module Submodule GramVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The covolume of an image**: a real linear map `T` sending a full-rank discrete subgroup `M` onto a full-rank
discrete subgroup `M'` multiplies the covolume by `|det T|`. A `ℤ`-basis `b` of `M` is a real basis of `E`; `T` is onto,
as `M'` spans, hence injective, so `T ∘ b` is a `ℤ`-basis of `M'`; and `T ∘ b = b·P` for the matrix `P` of `T`. -/
theorem covol_map {M M' : Submodule ℤ E} [DiscreteTopology M] [DiscreteTopology M'] (T : E →ₗ[ℝ] E)
    (hM : span ℝ (M : Set E) = ⊤) (hM' : span ℝ (M' : Set E) = ⊤) (hTM : (M' : Set E) = T '' M) :
    covol M' = |LinearMap.det T| * covol M := by
  classical
  set b := finBasis ℤ M
  have hsp : ⊤ ≤ span ℝ (Set.range fun i => (b i : E)) := by rw [span_basis, hM]
  let bR := Basis.mk (linearIndependent_basis b) hsp
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hM', span_le, hTM]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hinj : Function.Injective T := LinearMap.injective_iff_surjective.2 hsurj
  have hmem (x : M) : T x ∈ M' := by
    have : T x ∈ (M' : Set E) := hTM ▸ ⟨x, x.2, rfl⟩
    exact this
  let f : M →ₗ[ℤ] M' := ((T.restrictScalars ℤ).comp M.subtype).codRestrict M' hmem
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (hinj (congrArg Subtype.val h)), fun y => ?_⟩
    have : (y : E) ∈ T '' M := hTM ▸ y.2
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e := LinearEquiv.ofBijective f hf
  rw [covol_eq_vol (b.map e)]
  have h1 : (fun i => ((b.map e) i : E)) = fun j => ∑ i, LinearMap.toMatrix bR bR T i j • bR i := by
    funext j
    rw [Basis.map_apply]
    simp only [LinearMap.toMatrix_apply, Basis.sum_repr]
    simp [e, bR]
    rfl
  rw [h1, vol_comb, LinearMap.det_toMatrix]
  congr 1
  rw [covol]
  simp [bR, b]

end EuclidLattice

namespace GramVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Fischer's inequality over blocks**: the volume of a family is at most the product of the volumes of its fibres
over any map `p : J → I`. By induction on the set of fibres, one block at a time (`vol_sumElim_le`). -/
theorem vol_le_prod_fiber {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (v : J → E)
    (p : J → I) : vol v ≤ ∏ i, vol fun j : {j // p j = i} => v j := by
  suffices h : ∀ s : Finset I, vol (fun j : {j // p j ∈ s} => v j) ≤ ∏ i ∈ s, vol fun j : {j // p j = i} => v j by
    have h' := h Finset.univ
    rwa [← vol_comp_equiv (fun j : {j // p j ∈ Finset.univ} => v j)
      (Equiv.subtypeUnivEquiv fun j => Finset.mem_univ (p j)).symm] at h'
  intro s
  induction s using Finset.induction_on with
  | empty =>
    have : IsEmpty {j // p j ∈ (∅ : Finset I)} := ⟨fun j => by simpa using j.2⟩
    rw [vol_of_isEmpty, Finset.prod_empty]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    let f : {j // p j = a} ⊕ {j // p j ∈ s} → {j // p j ∈ insert a s} :=
      Sum.elim (fun j => ⟨j.1, Finset.mem_insert.2 (Or.inl j.2)⟩) fun j => ⟨j.1, Finset.mem_insert_of_mem j.2⟩
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · rintro (⟨x, hx⟩ | ⟨x, hx⟩) (⟨y, hy⟩ | ⟨y, hy⟩) h <;> have h' := congrArg Subtype.val h <;>
          simp only [f, Sum.elim_inl, Sum.elim_inr] at h' <;> subst h'
        · rfl
        · exact absurd (hx ▸ hy) ha
        · exact absurd (hy ▸ hx) ha
        · rfl
      · rintro ⟨j, hj⟩
        rcases Finset.mem_insert.1 hj with h | h
        · exact ⟨Sum.inl ⟨j, h⟩, rfl⟩
        · exact ⟨Sum.inr ⟨j, h⟩, rfl⟩
    rw [← vol_comp_equiv _ (Equiv.ofBijective f hf)]
    have hc : (fun j : {j // p j ∈ insert a s} => v j) ∘ Equiv.ofBijective f hf =
        Sum.elim (fun j : {j // p j = a} => v j) fun j : {j // p j ∈ s} => v j := by
      funext x
      cases x <;> rfl
    rw [hc]
    exact (vol_sumElim_le _ _).trans (mul_le_mul_of_nonneg_left ih (vol_nonneg _))

end GramVolume

namespace KLattice

open Module Submodule NumberField HermitianLattice Matrix WithLp

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical ComplexOrder InnerProductSpace nonZeroDivisors Pointwise

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {ι : Type} [Fintype ι]

/-- **The degree** `deg X = −log covol ψ(M)`. -/
noncomputable abbrev degK (X : KLattice K ι) : ℝ := X.toPlaceLattice.slopeLattice.deg ⊤

/-- **The rank** `rk X = [K:ℚ]·|ι|` (`rk_top`), the `ℤ`-rank of `ψ(M)`. -/
noncomputable abbrev rkK (X : KLattice K ι) : ℕ := X.toPlaceLattice.slopeLattice.rk ⊤

/-- **The slope** `μ X = deg X/rk X`. -/
noncomputable abbrev muK (X : KLattice K ι) : ℝ := degK X / rkK X

/-- The degree depends on the lattice and the metrics alone, not on the chosen factors of the metrics. -/
theorem degK_congr {X Y : KLattice K ι} (hM : X.M = Y.M) (hG : X.G = Y.G) : degK X = degK Y := by
  obtain ⟨M, G, _⟩ := X
  obtain ⟨M', G', _⟩ := Y
  subst hM hG
  rfl

omit [IsTotallyComplex K] in
/-- The complex determinant of a block-diagonal map is the product of the determinants of the blocks. -/
theorem det_op (S : Pl K → Matrix ι ι ℂ) :
    LinearMap.det ((op S : Space K ι →L[ℂ] Space K ι) : Space K ι →ₗ[ℂ] Space K ι) = ∏ v, (S v).det := by
  have h := LinearMap.det_toLin (EuclideanSpace.basisFun (ι × Pl K) ℂ).toBasis (blockDiagonal S)
  rw [det_blockDiagonal] at h
  exact h

omit [IsTotallyComplex K] in
/-- The real determinant of a block-diagonal map is `∏_v |det S_v|²`, the norm from `ℂ` to `ℝ` of the complex one. -/
theorem det_op_real (S : Pl K → Matrix ι ι ℂ) :
    LinearMap.det (((op S : Space K ι →L[ℂ] Space K ι) : Space K ι →ₗ[ℂ] Space K ι).restrictScalars ℝ) =
      ∏ v, Complex.normSq (S v).det := by
  rw [LinearMap.det_restrictScalars, det_op, map_prod]
  simp_rw [Algebra.norm_complex_apply]

/-- `∏_v |σ_v(x)|² = |N_{K/ℚ}(x)|`: every place is complex, of multiplicity `2` (`InfinitePlace.prod_eq_abs_norm`). -/
theorem prod_normSq_embedding (x : K) :
    ∏ v : Pl K, Complex.normSq (v.1.embedding x) = |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w) _ _ fun v => ?_
  rw [Equiv.subtypeUnivEquiv_apply, InfinitePlace.mult_isComplex v, Complex.normSq_eq_norm_sq,
    InfinitePlace.norm_embedding_eq]

/-- **K1, an automorphism of `K^ι`**: with the metrics kept, `deg g(M) = deg M − log |N_{K/ℚ}(det g)|`. The map
`hom` of `g` extends it, and its real determinant is `∏_v |σ_v(det g)|² = |N_{K/ℚ}(det g)|` (`det_op_real`,
`prod_normSq_embedding`), so `covol ψ(g(M)) = |N_{K/ℚ}(det g)|·covol ψ(M)` (`EuclidLattice.covol_map`). -/
theorem degK_map (X Y : KLattice K ι) (g : (ι → K) ≃ₗ[K] (ι → K))
    (hM : Y.M = X.M.map (g.toLinearMap.restrictScalars (𝓞 K))) (hG : Y.G = X.G) :
    degK Y = degK X - Real.log |(Algebra.norm ℚ (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) : ℝ)| := by
  have : (X.M.map (g.toLinearMap.restrictScalars (𝓞 K))).IsLattice K := hM ▸ Y.isLattice
  rw [degK_congr (Y := X.withLattice (X.M.map (g.toLinearMap.restrictScalars (𝓞 K)))) hM hG]
  set Z := X.withLattice (X.M.map (g.toLinearMap.restrictScalars (𝓞 K)))
  set T := (X.hom Z (g : (ι → K) →ₗ[K] (ι → K)) : Space K ι →ₗ[ℂ] Space K ι).restrictScalars ℝ with hT
  have hdet : LinearMap.det T = |(Algebra.norm ℚ (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) : ℝ)| := by
    rw [← prod_normSq_embedding, hT, hom, det_op_real]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hA : IsUnit (X.factor v) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse (X.inv_mul_factor v))
    rw [show Z.factor v = X.factor v from rfl, Matrix.det_conj hA, ← LinearMap.det_toMatrix', RingHom.map_det,
      RingHom.mapMatrix_apply]
  have hZ : (Z.lattice : Set (Space K ι)) = T '' X.lattice := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨X.ψ x, ⟨x, hx, rfl⟩, X.hom_ψ Z _ x⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨g x, ⟨x, hx, rfl⟩, (X.hom_ψ Z _ x).symm⟩
  have h := EuclidLattice.covol_map T X.span_lattice Z.span_lattice hZ
  rw [hdet, abs_abs] at h
  have hpos : 0 < |(Algebra.norm ℚ (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) : ℝ)| :=
    pos_of_mul_pos_left (h ▸ EuclidLattice.covol_pos _) (EuclidLattice.covol_pos _).le
  show -Real.log (EuclidLattice.covol Z.lattice) = -Real.log (EuclidLattice.covol X.lattice) - _
  rw [h, Real.log_mul hpos.ne' (EuclidLattice.covol_pos _).ne']
  ring

omit [NumberField K] [IsTotallyComplex K] [Fintype ι] in
/-- The image of an `O_K`-lattice under a `K`-linear automorphism of `K^ι` is an `O_K`-lattice. -/
theorem isLattice_map (N : Submodule (𝓞 K) (ι → K)) [N.IsLattice K] (g : (ι → K) ≃ₗ[K] (ι → K)) :
    (N.map (g.toLinearMap.restrictScalars (𝓞 K))).IsLattice K where
  fg := IsLattice.fg.map _
  span_eq_top := by
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, IsLattice.span_eq_top,
      Submodule.map_top, LinearEquiv.range]

/-- **K2, diagonal fractional ideals**: if `X` has the lattice `D(𝔠) = ∏_i 𝔠_i` and `Y`, with the same metrics, the
lattice `O_K^ι`, then `deg X = deg Y − Σ_i log N(𝔠_i)`. The denominators `d_i` scale `D(𝔠)` onto `D(num)` (K1, at
the cost `Σ_i log |N(d_i)|`), which has index `∏_i N(num_i)` in `O_K^ι` (`deg_withLattice`), and
`N(𝔠_i) = N(num_i)/|N(d_i)|`. -/
theorem degK_pi (X Y : KLattice K ι) (𝔠 : ι → FractionalIdeal (𝓞 K)⁰ K)
    (hX : X.M = Submodule.pi Set.univ fun i => (𝔠 i : Submodule (𝓞 K) K))
    (hY : Y.M = Submodule.pi Set.univ fun _ => 1) (hG : X.G = Y.G) :
    degK X = degK Y - ∑ i, Real.log (FractionalIdeal.absNorm (𝔠 i) : ℝ) := by
  -- the ideals are nonzero, as `D(𝔠)` spans
  have h𝔠 (i : ι) : 𝔠 i ≠ 0 := by
    intro h0
    have hle : span K (X.M : Set (ι → K)) ≤ LinearMap.ker (LinearMap.proj i : (ι → K) →ₗ[K] K) :=
      span_le.2 fun x hx => by
        rw [hX] at hx
        have : x i ∈ ((𝔠 i : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := hx i (Set.mem_univ i)
        rw [h0, FractionalIdeal.coe_zero, Submodule.mem_bot] at this
        exact this
    rw [IsLattice.span_eq_top] at hle
    have := hle (mem_top : Pi.single i (1 : K) ∈ ⊤)
    simp at this
  -- the denominators, and the diagonal map `g` they define
  set d : ι → K := fun i => (((𝔠 i).den : 𝓞 K) : K)
  have hd (i : ι) : d i ≠ 0 := by
    simp [d]
  have hdet : LinearMap.det (Matrix.toLin' (Matrix.diagonal d)) = ∏ i, d i := by
    rw [LinearMap.det_toLin', det_diagonal]
  let g := LinearMap.equivOfDetNeZero (Matrix.toLin' (Matrix.diagonal d))
    (hdet ▸ Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have hg (x : ι → K) (i : ι) : g x i = d i * x i := by
    simp [g, Matrix.mulVec_diagonal]
  -- `g(D(𝔠)) = D(num)`
  set Nn : ι → Submodule (𝓞 K) K := fun i => Submodule.map (Algebra.linearMap (𝓞 K) K) (𝔠 i).num
  have hNn (i : ι) (x : K) : x ∈ Nn i ↔ ∃ y ∈ (𝔠 i : Submodule (𝓞 K) K), d i * y = x := by
    show x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) (𝔠 i).num ↔ _
    rw [← FractionalIdeal.den_mul_self_eq_num, Submonoid.smul_def, Submodule.mem_smul_pointwise_iff_exists]
    simp [Algebra.smul_def, d]
  have hmap : X.M.map (g.toLinearMap.restrictScalars (𝓞 K)) = Submodule.pi Set.univ Nn := by
    rw [hX]
    ext x
    simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, hNn]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      exact ⟨y i, hy i, (hg y i).symm⟩
    · intro hx
      choose y hy hyx using hx
      exact ⟨y, hy, funext fun i => (hg y i).trans (hyx i)⟩
  -- `D(num) ≤ O_K^ι`, of index `∏_i N(num_i)`
  have hle : Submodule.pi Set.univ Nn ≤ Y.M := by
    rw [hY]
    intro x hx i _
    obtain ⟨a, -, ha⟩ := hx i (Set.mem_univ i)
    exact Submodule.mem_one.2 ⟨a, ha⟩
  have hidx : (Submodule.pi Set.univ Nn).toAddSubgroup.relIndex Y.M.toAddSubgroup =
      ∏ i, Ideal.absNorm (𝔠 i).num := by
    let φ : (ι → 𝓞 K) →+ (ι → K) := (algebraMap (𝓞 K) K).toAddMonoidHom.compLeft ι
    have hφ : Function.Injective φ := fun x y h =>
      funext fun i => FaithfulSMul.algebraMap_injective (𝓞 K) K (congrFun h i)
    have h1 : (Submodule.pi Set.univ Nn).toAddSubgroup =
        (AddSubgroup.pi Set.univ fun i => (𝔠 i).num.toAddSubgroup).map φ := by
      ext x
      simp only [Submodule.mem_toAddSubgroup, Submodule.mem_pi, Set.mem_univ, true_implies, AddSubgroup.mem_map,
        AddSubgroup.mem_pi, Submodule.mem_toAddSubgroup]
      constructor
      · intro hx
        choose a ha hax using fun i => hx i
        exact ⟨a, ha, funext hax⟩
      · rintro ⟨a, ha, rfl⟩ i
        exact ⟨a i, ha i, rfl⟩
    have h2 : Y.M.toAddSubgroup = (⊤ : AddSubgroup (ι → 𝓞 K)).map φ := by
      rw [hY]
      ext x
      simp only [Submodule.mem_toAddSubgroup, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
        AddSubgroup.mem_map, AddSubgroup.mem_top, true_and]
      constructor
      · intro hx
        choose a ha using hx
        exact ⟨a, funext ha⟩
      · rintro ⟨a, rfl⟩ i
        exact ⟨a i, rfl⟩
    rw [h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hφ, AddSubgroup.relIndex_top_right,
      AddSubgroup.index_pi]
    rfl
  -- K1 for `g`, and the index
  have : (X.M.map (g.toLinearMap.restrictScalars (𝓞 K))).IsLattice K := isLattice_map X.M g
  have h1 := degK_map X (X.withLattice (X.M.map (g.toLinearMap.restrictScalars (𝓞 K)))) g rfl rfl
  have : (Submodule.pi Set.univ Nn).IsLattice K := hmap ▸ this
  have h2 : degK (Y.withLattice (Submodule.pi Set.univ Nn)) = degK Y - _ := Y.deg_withLattice hle
  rw [degK_congr (X := X.withLattice (X.M.map (g.toLinearMap.restrictScalars (𝓞 K))))
    (Y := Y.withLattice (Submodule.pi Set.univ Nn)) hmap hG, h2, hidx] at h1
  -- the norms
  have hnum (i : ι) : (Ideal.absNorm (𝔠 i).num : ℝ) ≠ 0 := by
    have h := (FractionalIdeal.absNorm_eq_zero_iff (K := K)).not.2 (h𝔠 i)
    rw [FractionalIdeal.absNorm_eq] at h
    intro h0
    exact h (by rw [show (Ideal.absNorm (𝔠 i).num : ℚ) = 0 by exact_mod_cast h0, zero_div])
  have hden (i : ι) : |(Algebra.norm ℚ (d i) : ℝ)| ≠ 0 := by
    simpa using hd i
  have hN (i : ι) : (FractionalIdeal.absNorm (𝔠 i) : ℝ) =
      (Ideal.absNorm (𝔠 i).num : ℝ) / |(Algebra.norm ℚ (d i) : ℝ)| := by
    rw [FractionalIdeal.absNorm_eq, Int.cast_abs, Algebra.coe_norm_int]
    push_cast
    rfl
  have hg' : (g : (ι → K) →ₗ[K] (ι → K)) = Matrix.toLin' (Matrix.diagonal d) := LinearEquiv.coe_ofIsUnitDet _
  rw [hg', hdet, map_prod, Rat.cast_prod, Finset.abs_prod, Real.log_prod fun i _ => hden i, Nat.cast_prod,
    Real.log_prod fun i _ => hnum i] at h1
  simp_rw [hN, Real.log_div (hnum _) (hden _), Finset.sum_sub_distrib]
  linarith

/-- **Pairing the embeddings**: if `f(conj ∘ φ) = conj (f φ)`, then `Σ_φ f(φ) = Σ_v 2·Re f(σ_v)`, as the embeddings
at the complex place `v` are `σ_v` and `conj ∘ σ_v`. -/
theorem sum_embeddings (f : (K →+* ℂ) → ℂ)
    (hf : ∀ φ, f (ComplexEmbedding.conjugate φ) = starRingEnd ℂ (f φ)) :
    ∑ φ, f φ = ∑ v : Pl K, ((2 * (f v.1.embedding).re : ℝ) : ℂ) := by
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk f]
  have hfib (w : InfinitePlace K) :
      ∑ φ ∈ Finset.univ with InfinitePlace.mk φ = w, f φ = ((2 * (f w.embedding).re : ℝ) : ℂ) := by
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
      (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))
        (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
    have hs : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff, ComplexEmbedding.conjugate,
        star_involutive.eq_iff]
    rw [hs, Finset.sum_pair hne, hf, Complex.add_conj]
  simp_rw [hfib]
  exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w).symm _ _ fun w => rfl

omit [IsTotallyComplex K] in
/-- The metric on two coordinate vectors: `⟪ψ(a e_i), ψ(b e_j)⟫ = Σ_v conj(σ_v a)·(G_v)_{ij}·σ_v b`. -/
theorem inner_ψ_single (X : KLattice K ι) (i j : ι) (a b : K) :
    ⟪X.ψ (Pi.single i a), X.ψ (Pi.single j b)⟫_ℂ =
      ∑ v : Pl K, starRingEnd ℂ (v.1.embedding a) * X.G v i j * v.1.embedding b := by
  rw [inner_ψ, inner_apply, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [coord_ψ₀, coord_op, Pi.single_apply, mul_assoc, apply_ite (⇑v.1.embedding)]
  · intro k _ hk
    simp [coord_ψ₀, hk]
  · simp

/-- **K3, a constant rational metric**: if `X` has the lattice `O_K^ι` and the metric `Γ` (real) at every place, then
`deg X = −([K:ℚ]/2)·log det Γ − |ι|·([K:ℚ]/2)·(log|d_K|/[K:ℚ] − log 2)`. The vectors `ω_φ e_i` are a `ℤ`-basis with
Gram matrix `Γ ⊗ G_O`, and `det G_O = |d_K|/2^{[K:ℚ]}`, as `2·G_O = conj(B)·Bᵀ` with `det B² = d_K`. -/
theorem degK_const (X : KLattice K ι) (Γ : Matrix ι ι ℝ) (hM : X.M = Submodule.pi Set.univ fun _ => 1)
    (hG : ∀ v, X.G v = Γ.map Complex.ofReal) :
    degK X = -(finrank ℚ K / 2 : ℝ) * Real.log Γ.det -
      Fintype.card ι * (finrank ℚ K / 2 : ℝ) * (Real.log |(discr K : ℝ)| / finrank ℚ K - Real.log 2) := by
  -- the `ℤ`-basis `ω_φ e_i` of `ψ(O_K^ι)`
  set ω : Basis (K →+* ℂ) ℤ (𝓞 K) := (RingOfIntegers.basis K).reindex (equivReindex K).symm with hω
  let f₀ : (ι → 𝓞 K) →ₗ[ℤ] Space K ι :=
    X.ψ.toIntLinearMap ∘ₗ ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ).compLeft ι
  have hf₀ (x : ι → 𝓞 K) : f₀ x = X.ψ fun i => (x i : K) := rfl
  have hmem (x : ι → 𝓞 K) : f₀ x ∈ X.lattice :=
    ⟨fun i => (x i : K), by rw [hM]; exact fun i _ => Submodule.mem_one.2 ⟨x i, rfl⟩, rfl⟩
  have hbij : Function.Bijective (f₀.codRestrict X.lattice hmem) := by
    refine ⟨fun x y h => funext fun i => ?_, ?_⟩
    · have h' := X.ψ_injective (congrArg Subtype.val h)
      exact RingOfIntegers.coe_injective (congrFun h' i)
    · rintro ⟨_, x, hx, rfl⟩
      rw [hM] at hx
      choose a ha using fun i => Submodule.mem_one.1 (hx i (Set.mem_univ i))
      exact ⟨a, Subtype.ext (by rw [LinearMap.codRestrict_apply, hf₀]; exact congrArg X.ψ (funext ha))⟩
  let bZ := ((Pi.basis fun _ : ι => ω).reindex (Equiv.sigmaEquivProd ι (K →+* ℂ))).map
    (LinearEquiv.ofBijective _ hbij)
  have hbZ (p : ι × (K →+* ℂ)) : (bZ p : Space K ι) = X.ψ (Pi.single p.1 (ω p.2 : K)) := by
    simp only [bZ, Basis.map_apply, Basis.reindex_apply, LinearEquiv.ofBijective_apply, LinearMap.codRestrict_apply,
      hf₀, Pi.basis_apply]
    congr 1
    funext i
    by_cases h : i = p.1
    · subst h
      simp
    · simp [h]
  -- the Gram matrix is `Γ ⊗ G_O`
  set GO : Matrix (K →+* ℂ) (K →+* ℂ) ℝ := Matrix.of fun φ φ' =>
    (∑ v : Pl K, starRingEnd ℂ (v.1.embedding (ω φ)) * v.1.embedding (ω φ')).re with hGO
  have hgram : Matrix.gram ℝ (fun p => (bZ p : Space K ι)) = Matrix.kroneckerMap (· * ·) Γ GO := by
    ext ⟨i, φ⟩ ⟨j, φ'⟩
    rw [Matrix.gram_apply, hbZ, hbZ, real_inner_eq_re_inner ℂ, inner_ψ_single]
    show _ = Γ i j * GO φ φ'
    simp only [hG, Matrix.map_apply, hGO, Matrix.of_apply, RCLike.re_to_complex]
    rw [← Complex.re_ofReal_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun v _ => by ring
  -- `2·G_O = conj(B)·Bᵀ`, with `B` Mathlib's `basisMatrix`, and `det B² = d_K`
  have hBe (φ ψ : K →+* ℂ) : basisMatrix K φ ψ = ψ (ω φ) := by
    simp [basisMatrix, hω, integralBasis_apply]
  have hB : ((2 : ℝ) • GO).map Complex.ofReal = (basisMatrix K).map (starRingEnd ℂ) * (basisMatrix K)ᵀ := by
    ext φ φ'
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.transpose_apply, hBe]
    rw [sum_embeddings (fun ψ : K →+* ℂ => starRingEnd ℂ (ψ (ω φ : K)) * ψ (ω φ' : K)) fun ψ => by
      simp [ComplexEmbedding.conjugate_coe_eq]]
    simp [hGO, Complex.re_sum, Finset.mul_sum]
  have hdetGO : GO.det = |(discr K : ℝ)| / 2 ^ finrank ℚ K := by
    have h := congrArg Matrix.det hB
    have h1 : (((2 : ℝ) • GO).map Complex.ofReal).det = (((2 : ℝ) • GO).det : ℂ) :=
      (RingHom.map_det Complex.ofRealHom _).symm
    rw [h1, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ← norm_pow, ← discr_eq_basisMatrix_det_sq,
      Complex.norm_intCast, Matrix.det_smul, Embeddings.card] at h
    have h' := Complex.ofReal_injective h
    rw [eq_div_iff (by positivity)]
    linarith
  -- `covol² = det Γ^{[K:ℚ]}·(|d_K|/2^{[K:ℚ]})^{|ι|}`
  have hcov : EuclidLattice.covol X.lattice ^ 2 =
      Γ.det ^ finrank ℚ K * (|(discr K : ℝ)| / 2 ^ finrank ℚ K) ^ Fintype.card ι := by
    rw [EuclidLattice.covol_eq_vol bZ, GramVolume.vol_sq, hgram, Matrix.det_kronecker, hdetGO, Embeddings.card]
  have hpos := EuclidLattice.covol_pos X.lattice
  have hd : |(discr K : ℝ)| / 2 ^ finrank ℚ K ≠ 0 := by
    have := discr_ne_zero K
    positivity
  have hΓ : Γ.det ^ finrank ℚ K ≠ 0 := fun h => by
    rw [h, zero_mul] at hcov
    exact (pow_pos hpos 2).ne' hcov
  have hlog := congrArg Real.log hcov
  rw [Real.log_pow, Real.log_mul hΓ (pow_ne_zero _ hd), Real.log_pow, Real.log_pow,
    Real.log_div (by have := discr_ne_zero K; positivity) (by positivity), Real.log_pow] at hlog
  have hn : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have e : (Fintype.card ι : ℝ) * (finrank ℚ K / 2) * (Real.log |(discr K : ℝ)| / finrank ℚ K - Real.log 2) =
      (Fintype.card ι * Real.log |(discr K : ℝ)| - Fintype.card ι * finrank ℚ K * Real.log 2) / 2 := by
    field_simp
  show -Real.log (EuclidLattice.covol X.lattice) = _
  rw [e]
  push_cast at hlog
  linarith

/-- **K3 in slopes**: `μ = −log det Γ/(2|ι|) − archShift(K)/2`, with `archShift(K) = log|d_K|/[K:ℚ] − log 2`; so in
the archive's units, `μ_arch = 2μ + archShift(K) = −log det Γ/|ι|`. -/
theorem muK_const [Nonempty ι] (X : KLattice K ι) (Γ : Matrix ι ι ℝ)
    (hM : X.M = Submodule.pi Set.univ fun _ => 1) (hG : ∀ v, X.G v = Γ.map Complex.ofReal) :
    muK X = -Real.log Γ.det / (2 * Fintype.card ι) - (Real.log |(discr K : ℝ)| / finrank ℚ K - Real.log 2) / 2 := by
  rw [muK, degK_const X Γ hM hG, rkK, rk_top]
  have hn : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  push_cast
  field_simp

omit [IsTotallyComplex K] in
/-- **A scaled isometry**: if `(σ_vΘ)ᴴ G_v (σ_vΘ) = s·G'_v` at every place, then `ψ ∘ Θ` multiplies real inner
products by `s`. -/
theorem inner_ψ_map {κ : Type} [Fintype κ] (X : KLattice K ι) (Y : KLattice K κ) (Θ : (κ → K) →ₗ[K] (ι → K))
    (s : ℝ) (h : ∀ v, ((LinearMap.toMatrix' Θ).map v.1.embedding)ᴴ * X.G v *
      (LinearMap.toMatrix' Θ).map v.1.embedding = s • Y.G v) (x y : κ → K) :
    ⟪X.ψ (Θ x), X.ψ (Θ y)⟫_ℝ = s * ⟪Y.ψ x, Y.ψ y⟫_ℝ := by
  rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, inner_ψ, inner_ψ, ← LinearMap.toMatrix'_mulVec Θ x,
    ← LinearMap.toMatrix'_mulVec Θ y, ← op_ψ₀, ← op_ψ₀, inner_op, ← op_mul, ← op_mul]
  simp_rw [h, ← Complex.coe_smul]
  rw [op_smul, inner_smul_right]
  exact Complex.re_ofReal_mul s _

/-- **K4, Fischer over blocks**: let `Θ_i : K^{κ_i} → K^ι` send `M_i` into `M` (`h1`), with
`(y_i)_i ↦ Σ_i Θ_i y_i` bijective (`h2`), and `(σ_vΘ_i)ᴴ G_v (σ_vΘ_i) = s_i·G_{i,v}`, `s_i > 0`, at every place
(`h3`). Then `deg X ≥ Σ_i (deg X_i − (rk X_i/2)·log s_i)`. The images under `ψ ∘ Θ_i` of `ℤ`-bases of the blocks
have volumes `s_i^{rk_i/2}·covol_i` (`inner_ψ_map`); together they lie in `ψ(M)`, span it and have `rk` members, so
`covol ψ(M)` is at most their volume (`EuclidLattice.covol_le`), and Fischer's inequality bounds that by the product
of the blocks' (`GramVolume.vol_le_prod_fiber`). -/
theorem degK_ge_sum {I : Type} [Fintype I] {κ : I → Type} [∀ i, Fintype (κ i)] (X : KLattice K ι)
    (Y : ∀ i, KLattice K (κ i)) (Θ : ∀ i, (κ i → K) →ₗ[K] (ι → K)) (s : I → ℝ) (hs : ∀ i, 0 < s i)
    (h1 : ∀ i, ∀ x ∈ (Y i).M, Θ i x ∈ X.M)
    (h2 : Function.Bijective fun y : (∀ i, κ i → K) => ∑ i, Θ i (y i))
    (h3 : ∀ i v, ((LinearMap.toMatrix' (Θ i)).map v.1.embedding)ᴴ * X.G v *
      (LinearMap.toMatrix' (Θ i)).map v.1.embedding = s i • (Y i).G v) :
    ∑ i, (degK (Y i) - rkK (Y i) / 2 * Real.log (s i)) ≤ degK X := by
  -- `ℤ`-bases of the blocks, their preimages `y i` in `M_i`, and the family `w = ψ ∘ Θ ∘ y`
  set r : I → ℕ := fun i => finrank ℤ (Y i).lattice
  have hy (i : I) (j : Fin (r i)) : ∃ y ∈ (Y i).M, (Y i).ψ y = (finBasis ℤ (Y i).lattice j : Space K (κ i)) :=
    (finBasis ℤ (Y i).lattice j).2
  choose y hyM hyψ using hy
  let w : (Σ i, Fin (r i)) → Space K ι := fun p => X.ψ (Θ p.1 (y p.1 p.2))
  -- ranks: `Σ_i r_i = [K:ℚ]·Σ_i |κ_i| = [K:ℚ]·|ι| = rk ψ(M)`
  have hrk (i : I) : rkK (Y i) = r i := EuclidLattice.finrank_span (Y i).lattice
  have hrX : finrank ℤ X.lattice = finrank ℚ K * Fintype.card ι := by
    rw [← EuclidLattice.finrank_span]
    exact X.rk_top
  have hcard : ∑ i, Fintype.card (κ i) = Fintype.card ι := by
    let L : (∀ i, κ i → K) →ₗ[K] (ι → K) := ∑ i, (Θ i).comp (LinearMap.proj i)
    have hL : Function.Bijective L := by
      convert h2 using 1
      funext z
      simp [L]
    have := (LinearEquiv.ofBijective L hL).finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype] at this
    simpa only [Module.finrank_fintype_fun_eq_card] using this
  -- (a) the family lies in `ψ(M)`, spans it (`Θ` is onto), and has `rk ψ(M)` members: `covol ψ(M) ≤ vol w`
  have hcov : EuclidLattice.covol X.lattice ≤ GramVolume.vol w := by
    refine EuclidLattice.covol_le (fun p => ⟨_, h1 _ _ (hyM p.1 p.2), rfl⟩) ?_ ?_
    · rw [span_le]
      rintro _ ⟨x, -, rfl⟩
      obtain ⟨z, rfl⟩ := h2.2 x
      show X.ψ (∑ i, Θ i (z i)) ∈ _
      rw [map_sum]
      refine sum_mem fun i _ => ?_
      rw [← (Y i).hom_ψ X (Θ i) (z i)]
      have hz : (Y i).ψ (z i) ∈ span ℝ (Set.range fun j => (finBasis ℤ (Y i).lattice j : Space K (κ i))) := by
        rw [EuclidLattice.span_basis, (Y i).span_lattice]
        exact mem_top
      have := mem_map_of_mem (f := (((Y i).hom X (Θ i) : Space K (κ i) →ₗ[ℂ] Space K ι).restrictScalars ℝ)) hz
      rw [map_span, ← Set.range_comp] at this
      refine span_mono ?_ this
      rintro _ ⟨j, rfl⟩
      exact ⟨⟨i, j⟩, by simp [w, ← hyψ, hom_ψ]⟩
    · rw [hrX, Fintype.card_sigma]
      simp_rw [Fintype.card_fin, ← hrk, rkK, rk_top, ← Finset.mul_sum, hcard]
      exact le_rfl
  -- (b) Fischer over the blocks
  have hfis : GramVolume.vol w ≤ ∏ i, GramVolume.vol fun j : Fin (r i) => w ⟨i, j⟩ := by
    refine (GramVolume.vol_le_prod_fiber w Sigma.fst).trans (le_of_eq (Finset.prod_congr rfl fun i _ => ?_))
    have hb : Function.Bijective fun j : Fin (r i) => (⟨⟨i, j⟩, rfl⟩ : {p : Σ i, Fin (r i) // p.1 = i}) :=
      ⟨fun j j' h => sigma_mk_injective (β := fun i => Fin (r i)) (congrArg Subtype.val h),
        by rintro ⟨⟨_, j⟩, rfl⟩; exact ⟨j, rfl⟩⟩
    exact (GramVolume.vol_comp_equiv _ (Equiv.ofBijective _ hb)).symm
  -- (c) each block is a `ℤ`-basis of `ψ_i(M_i)` with inner products scaled by `s i`
  have hblock (i : I) : GramVolume.vol (fun j : Fin (r i) => w ⟨i, j⟩) ^ 2 =
      s i ^ r i * EuclidLattice.covol (Y i).lattice ^ 2 := by
    have hg : Matrix.gram ℝ (fun j : Fin (r i) => w ⟨i, j⟩) =
        s i • Matrix.gram ℝ fun j => (finBasis ℤ (Y i).lattice j : Space K (κ i)) := by
      ext j k
      rw [Matrix.gram_apply, Matrix.smul_apply, Matrix.gram_apply, ← hyψ, ← hyψ, smul_eq_mul]
      exact inner_ψ_map X (Y i) (Θ i) (s i) (h3 i) _ _
    rw [GramVolume.vol_sq, EuclidLattice.covol, GramVolume.vol_sq, hg, Matrix.det_smul, Fintype.card_fin]
  have hvpos (i : I) : 0 < GramVolume.vol fun j : Fin (r i) => w ⟨i, j⟩ := by
    refine lt_of_le_of_ne (GramVolume.vol_nonneg _) fun h0 => ?_
    have := hblock i
    rw [← h0] at this
    exact (mul_pos (pow_pos (hs i) _) (pow_pos (EuclidLattice.covol_pos _) 2)).ne' (by simpa using this.symm)
  have hlogi (i : I) : Real.log (GramVolume.vol fun j : Fin (r i) => w ⟨i, j⟩) =
      r i / 2 * Real.log (s i) + Real.log (EuclidLattice.covol (Y i).lattice) := by
    have := congrArg Real.log (hblock i)
    rw [Real.log_pow, Real.log_mul (pow_pos (hs i) _).ne' (pow_pos (EuclidLattice.covol_pos _) 2).ne',
      Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  -- (d) take logarithms
  have hle := Real.log_le_log (EuclidLattice.covol_pos _) (hcov.trans hfis)
  rw [Real.log_prod fun i _ => (hvpos i).ne'] at hle
  simp_rw [hlogi] at hle
  show _ ≤ -Real.log (EuclidLattice.covol X.lattice)
  have hdeg (i : I) : degK (Y i) - rkK (Y i) / 2 * Real.log (s i) =
      -(r i / 2 * Real.log (s i) + Real.log (EuclidLattice.covol (Y i).lattice)) := by
    rw [hrk]
    show -Real.log (EuclidLattice.covol (Y i).lattice) - _ = _
    ring
  simp_rw [hdeg, Finset.sum_neg_distrib]
  linarith

end KLattice
