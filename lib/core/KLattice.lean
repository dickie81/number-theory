import Mathlib
import FrameAtPlace

/-!
# Hermitian `O_K`-lattices in `K^ι`

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, "Next"), the first layer of a sharp
frontier: lattices over the ring of integers `O_K` of a totally complex field `K`, with hermitian metrics at the complex
places, become the hermitian lattices of `HermitianLattice`, and `K`-linear maps the maps of their frames.

**The data** (`KLattice K ι`): an `O_K`-lattice `M` in `K^ι` (Mathlib's `Submodule.IsLattice`), and positive definite
hermitian matrices `G v`, the metrics on `ℂ^ι = K^ι ⊗_{K,σ_v} ℂ` at the complex places `v`, defined or only known to
exist. The `K`-rational case `G v = σ_v(H)` is `ofForm` (on a CM field, see `isHermitian_map`).

**The hermitian lattice** (`toPlaceLattice`) lives in `⊕_v ℂ^ι` (`Space`, which keeps only the complex structure of
`EuclideanSpace`: the real inner product of `PiLp` would clash with the `Re⟪·,·⟫` of `HermitianLattice`), with the
blocks as the parts at the places (`part`). With factors `A_vᴴA_v = G_v` (`factor`), `ψ(x) = (A_v σ_v(x))_v` has
`⟪ψ x, ψ y⟫ = Σ_v σ_v(x)ᴴ G_v σ_v(y)` (`inner_ψ`), so the factor does not matter: covolumes depend on inner products
alone (`EuclidLattice.covol_sq_eq` with `c = 1`). The lattice `ψ(M)` is stable under `O_K` (`stable`), of full rank
(`span_lattice`: its real span is stable under `K ⊗ ℝ`, and `M` spans `K^ι`) and discrete (`discrete`: a `ℤ`-basis of
`M` is `ℚ`-free, so has at most `[K:ℚ]·|ι| = dim_ℝ` members, and spans).

**Maps** (`hom`). A `K`-linear `B : K^ι → K^κ` acts on the block at `v` by `A'_v σ_v(B) A_v⁻¹`, which is `σ_v(B)` in the
coordinates of the metrics. It extends `B` (`hom_ψ`) and commutes with `O_K`, as `HermitianLattice.frame` asks
(`frame`). In any hermitian frame, a map that commutes with `O_K` commutes with `K ⊗ ℝ = ∏_v ℂ`
(`HermitianLattice.comm_act`), so it is complex-linear from `V v` to `W v` (`HermitianLattice.component`): the
components that `HermitianLattice.spread_of_frameCond` took as data. So the frame condition over `ℂ` at one place gives
rank spreading, with no padding at full rank (`spread_of_frameCond`).

**Index and scaling**, with `deg = −log covol` and `rk = rk_ℤ` (`EuclidLattice.slopeLattice`):
* for `O_K`-lattices `N ≤ M`, `deg N = deg M − log [M : N]` and `μ(N) = μ(M) − log [M : N]/rk`, with `[M : N]` the
  index of groups (`deg_withLattice`, `slope_withLattice`; `EuclidLattice.covol_eq_relIndex_mul`);
* the metrics `c·G v`, `c > 0`, shift `deg` by `−(rk/2)·log c` (`deg_scale`), and `μ = deg/rk` by `−(log c)/2`.

**The factor 2.** `rk = [K:ℚ]·|ι| = 2·n_∞·|ι|` (`rk_top`): twice the complex dimension of `⊕_v ℂ^ι`, and `[K:ℚ]` times
the `O_K`-rank `|ι|`, the complex dimension of each part. The archive's units (`PlaceLattice`) are complex:
`μ = 2·deg/rk_ℤ − log 2 + log|d_K|/[K:ℚ]` is degree per complex dimension, and its heights `log‖φ_v‖²` are twice the
library's. Its `−log 2` is the trace form, which counts each complex place twice, so is `2·Re⟪·,·⟫` (`deg_scale` with
`c = 2`). Nothing else carries the factor: the frame inequality is homogeneous in slopes, heights, `U` and `H`; rank
spreading compares ranks with ranks; and the frame condition has the same `e`, `η` over `ℝ` and over `ℂ`
(`FrameAtPlace.FrameCond.restrictScalars`). A frontier in the archive's units converts by
`μ = (μ_arch + log 2 − log|d_K|/[K:ℚ])/2` and `h̄ = h_arch/2`, with the ranks of `rk_top`.
-/

namespace HermitianLattice

open Module Submodule NumberField

attribute [local instance] InnerProductSpace.complexToReal

open scoped Classical

variable {K : Type} [Field K] [NumberField K]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {V : Pl K → Submodule ℂ E}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {W : Pl K → Submodule ℂ F}

/-- `Pi.single v c` acts by `c` on the part at `v`, and kills the others. -/
theorem act_single (v : Pl K) (c : ℂ) (x : E) : act V (Pi.single v c) x = c • (V v).starProjection x := by
  rw [act_apply, Finset.sum_eq_single v (fun w _ hw => by simp [hw]) (by simp), Pi.single_eq_same]

variable {φ : E →L[ℝ] F} (hφK : ∀ (k : 𝓞 K) x, φ (act V (emb (k : K)) x) = act W (emb (k : K)) (φ x))
include hφK

/-- **A map that commutes with `O_K` commutes with `K ⊗ ℝ = ∏_v ℂ`**, which `O_K` spans (`span_emb`). -/
theorem comm_act (z : Pl K → ℂ) (x : E) : φ (act V z x) = act W z (φ x) := by
  have hz : z ∈ span ℝ (Set.range fun k : 𝓞 K => emb (k : K)) := span_emb (K := K) ▸ mem_top
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    exact hφK k x
  | zero => simp [act_apply]
  | add z z' _ _ h h' => rw [act_add_left, act_add_left, map_add, h, h']
  | smul r z _ h => rw [act_smul_left, act_smul_left, map_smul, h]

/-- A map that commutes with `O_K` sends the part at `v` into the part at `v`, as `Pi.single v 1` projects onto both. -/
theorem map_mem {v : Pl K} {x : E} (hx : x ∈ V v) : φ x ∈ W v := by
  have h := comm_act hφK (Pi.single v 1) x
  rw [act_single, act_single, one_smul, one_smul, starProjection_eq_self_iff.2 hx] at h
  exact starProjection_eq_self_iff.1 h.symm

/-- **The component at `v`** of a map that commutes with `O_K`: it is complex-linear from `V v` to `W v`, as
`Pi.single v c` acts by `c` on both. -/
noncomputable def component (v : Pl K) : V v →ₗ[ℂ] W v where
  toFun x := ⟨φ x.1, map_mem hφK x.2⟩
  map_add' x y := Subtype.ext (map_add φ x.1 y.1)
  map_smul' c x := Subtype.ext <| by
    have h := comm_act hφK (Pi.single v c) x.1
    rwa [act_single, act_single, starProjection_eq_self_iff.2 x.2,
      starProjection_eq_self_iff.2 (map_mem hφK x.2)] at h

end HermitianLattice

namespace EuclidLattice

open Module Submodule GramVolume

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-- **Index**: if `N ≤ M` are discrete of equal rank, then `covol N = [M : N]·covol M`, as a basis of `N` is a basis of
`M` times an integer matrix of determinant `±[M : N]` (`AddSubgroup.relIndex_eq_natAbs_det`). -/
theorem covol_eq_relIndex_mul {M N : Submodule ℤ E} [DiscreteTopology M] [DiscreteTopology N] (hNM : N ≤ M)
    (h : finrank ℤ N = finrank ℤ M) : covol N = N.toAddSubgroup.relIndex M.toAddSubgroup * covol M := by
  classical
  let bN := (finBasis ℤ N).reindex (finCongr h)
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ hNM bN (finBasis ℤ M), covol_eq_vol bN, covol_eq_vol (finBasis ℤ M)]
  refine (vol_eq_abs_det_mul (finBasis ℤ M) fun i => ⟨bN i, hNM (bN i).2⟩).trans ?_
  rw [Nat.cast_natAbs, Int.cast_abs]
  rfl

/-- **Similar lattices**: if `e : M ≃ M'` multiplies inner products by `c`, then `covol M'² = c^{rk M}·covol M²`. With
`c = 1`: covolumes depend on inner products alone. -/
theorem covol_sq_eq {M : Submodule ℤ E} {M' : Submodule ℤ E'} [DiscreteTopology M] [DiscreteTopology M']
    (e : M ≃ₗ[ℤ] M') (c : ℝ) (he : ∀ x y, inner ℝ (e x : E') (e y : E') = c * inner ℝ (x : E) (y : E)) :
    covol M' ^ 2 = c ^ finrank ℤ M * covol M ^ 2 := by
  classical
  rw [covol_eq_vol ((finBasis ℤ M).map e), covol, vol_sq, vol_sq]
  have : Matrix.gram ℝ (fun i => ((finBasis ℤ M).map e i : E')) = c • Matrix.gram ℝ fun i => (finBasis ℤ M i : E) := by
    ext i j
    simp [Matrix.gram_apply, he]
  rw [this, Matrix.det_smul, Fintype.card_fin]

end EuclidLattice

open NumberField HermitianLattice in
open scoped ComplexOrder in
/-- **A hermitian `O_K`-lattice in `K^ι`**: an `O_K`-lattice `M` (finitely generated, spanning `K^ι` over `K`), and at
each complex place `v` a positive definite hermitian matrix `G v`, the metric on `ℂ^ι = K^ι ⊗_{K,σ_v} ℂ`. -/
structure KLattice (K : Type) [Field K] (ι : Type) where
  /-- The lattice: an `O_K`-submodule of `K^ι`. -/
  M : Submodule (𝓞 K) (ι → K)
  [isLattice : M.IsLattice K]
  /-- The metric at each complex place. -/
  G : Pl K → Matrix ι ι ℂ
  /-- The metrics are positive definite. -/
  posDef : ∀ v, (G v).PosDef

namespace KLattice

open Module Submodule NumberField HermitianLattice Matrix WithLp

attribute [local instance] InnerProductSpace.complexToReal

attribute [instance] isLattice

open scoped Classical MatrixOrder ComplexOrder InnerProductSpace

variable {K : Type} [Field K] {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] (X : KLattice K ι)

/-- A factor `A_v` of the metric, `A_vᴴ A_v = G_v`. -/
noncomputable def factor (v : Pl K) : Matrix ι ι ℂ :=
  (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (X.posDef v).posSemidef.nonneg).choose

/-- `A_vᴴ A_v = G_v`. -/
theorem factor_spec (v : Pl K) : (X.factor v)ᴴ * X.factor v = X.G v :=
  (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (X.posDef v).posSemidef.nonneg).choose_spec.symm

/-- The factor is invertible, as `G_v` is. -/
theorem inv_mul_factor (v : Pl K) : (X.factor v)⁻¹ * X.factor v = 1 := by
  have h := (X.posDef v).isUnit
  rw [← X.factor_spec v, isUnit_iff_isUnit_det, det_mul] at h
  exact nonsing_inv_mul _ (isUnit_of_mul_isUnit_right h)

/-- **The space** `⊕_v ℂ^ι`, with coordinates `(i, v)`: a copy of `EuclideanSpace ℂ (ι × Pl K)` that keeps only its
complex structure, so that its real inner product is `Re⟪·,·⟫` (`InnerProductSpace.complexToReal`). -/
def Space (K : Type) [Field K] (ι : Type) : Type := EuclideanSpace ℂ (ι × Pl K)

variable [NumberField K]

noncomputable instance : NormedAddCommGroup (Space K ι) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (ι × Pl K)))

noncomputable instance : InnerProductSpace ℂ (Space K ι) :=
  inferInstanceAs (InnerProductSpace ℂ (EuclideanSpace ℂ (ι × Pl K)))

instance : FiniteDimensional ℂ (Space K ι) :=
  inferInstanceAs (FiniteDimensional ℂ (EuclideanSpace ℂ (ι × Pl K)))

/-- The coordinate at `p = (i, v)`. -/
noncomputable def coord (p : ι × Pl K) : Space K ι →ₗ[ℂ] ℂ where
  toFun y := ofLp y p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `coord p y` is the `p`-th coordinate. -/
theorem coord_apply (p : ι × Pl K) (y : Space K ι) : coord p y = ofLp y p := rfl

/-- Vectors with the same coordinates are equal. -/
theorem ext_coord {x y : Space K ι} (h : ∀ p, coord p x = coord p y) : x = y :=
  WithLp.ofLp_injective 2 (funext fun p => h p)

/-- The inner product in coordinates. -/
theorem inner_apply (x y : Space K ι) : ⟪x, y⟫_ℂ = ∑ p, (starRingEnd ℂ) (coord p x) * coord p y :=
  (PiLp.inner_apply (𝕜 := ℂ) (x : EuclideanSpace ℂ (ι × Pl K)) y).trans
    (Finset.sum_congr rfl fun p _ => by simp [coord_apply, mul_comm])

/-- The block-diagonal map `(y_v)_v ↦ (T_v y_v)_v`. -/
noncomputable def op (T : Pl K → Matrix κ ι ℂ) : Space K ι →L[ℂ] Space K κ :=
  LinearMap.toContinuousLinearMap (toEuclideanLin (blockDiagonal T))

/-- `op T` in coordinates. -/
theorem coord_op (T : Pl K → Matrix κ ι ℂ) (y : Space K ι) (p : κ × Pl K) :
    coord p (op T y) = ∑ i, T p.2 p.1 i * coord (i, p.2) y := by
  show (blockDiagonal T *ᵥ ofLp y) p = _
  simp [mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, coord_apply]

/-- `op` is multiplicative. -/
theorem op_mul (T : Pl K → Matrix κ ι ℂ) (S : Pl K → Matrix μ κ ℂ) (y : Space K ι) :
    op (fun v => S v * T v) y = op S (op T y) := by
  show toLp 2 (blockDiagonal _ *ᵥ ofLp y) = toLp 2 (blockDiagonal S *ᵥ (blockDiagonal T *ᵥ ofLp y))
  rw [blockDiagonal_mul, mulVec_mulVec]

/-- `op 1` is the identity. -/
theorem op_one (y : Space K ι) : op (fun _ => (1 : Matrix ι ι ℂ)) y = y := by
  show toLp 2 (blockDiagonal (1 : Pl K → Matrix ι ι ℂ) *ᵥ ofLp y) = y
  rw [blockDiagonal_one, one_mulVec]
  rfl

/-- The adjoint of `op T` is `op Tᴴ`. -/
theorem inner_op (T : Pl K → Matrix κ ι ℂ) (x : Space K ι) (y : Space K κ) :
    ⟪op T x, y⟫_ℂ = ⟪x, op (fun v => (T v)ᴴ) y⟫_ℂ := by
  have h := LinearMap.adjoint_inner_right (toEuclideanLin (blockDiagonal T)) (x : EuclideanSpace ℂ (ι × Pl K))
    (y : EuclideanSpace ℂ (κ × Pl K))
  rw [← toEuclideanLin_conjTranspose_eq_adjoint, blockDiagonal_conjTranspose] at h
  exact h.symm

/-- `op` is linear in its matrices. -/
theorem op_smul (c : ℂ) (T : Pl K → Matrix κ ι ℂ) (y : Space K ι) : op (fun v => c • T v) y = c • op T y := by
  show toLp 2 (blockDiagonal (c • T) *ᵥ ofLp y) = c • toLp 2 (blockDiagonal T *ᵥ ofLp y)
  rw [blockDiagonal_smul, smul_mulVec, WithLp.toLp_smul]

/-- The part at `v`: `ℂ^ι` in the `v`-th block, the range of the projection `op (Pi.single v 1)`. -/
noncomputable def part (v : Pl K) : Submodule ℂ (Space K ι) :=
  LinearMap.range (op (Pi.single v (1 : Matrix ι ι ℂ)) : Space K ι →ₗ[ℂ] Space K ι)

/-- The projection onto the part at `v`, in coordinates. -/
theorem coord_op_single (v : Pl K) (y : Space K ι) (p : ι × Pl K) :
    coord p (op (Pi.single v (1 : Matrix ι ι ℂ)) y) = if p.2 = v then coord p y else 0 := by
  rw [coord_op]
  by_cases h : p.2 = v
  · subst h
    simp [one_apply]
  · simp [h]

/-- The orthogonal projection onto the part at `v` is `op (Pi.single v 1)`. -/
theorem starProjection_part (v : Pl K) (y : Space K ι) :
    (part v : Submodule ℂ (Space K ι)).starProjection y = op (Pi.single v 1) y := by
  refine eq_starProjection_of_mem_of_inner_eq_zero ⟨y, rfl⟩ ?_
  rintro _ ⟨u, rfl⟩
  rw [inner_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  simp only [map_sub, ContinuousLinearMap.coe_coe, coord_op_single]
  split_ifs <;> simp

/-- The parts at the places are pairwise orthogonal. -/
theorem part_orth : Pairwise fun v w => (part v : Submodule ℂ (Space K ι)) ⟂ part w := by
  intro v w hvw
  refine isOrtho_iff_inner_eq.2 ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [inner_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  simp only [ContinuousLinearMap.coe_coe, coord_op_single]
  split_ifs with h1 h2 <;> simp_all

/-- The parts at the places span `⊕_v ℂ^ι`. -/
theorem part_iSup : ⨆ v, (part v : Submodule ℂ (Space K ι)) = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  have hy : ∑ v, op (Pi.single v (1 : Matrix ι ι ℂ)) y = y := ext_coord fun p => by
    simp [map_sum, coord_op_single]
  exact hy ▸ sum_mem fun v _ => mem_iSup_of_mem v ⟨y, rfl⟩

/-- `z : Pl K → ℂ` acts on the coordinates at `v` by `z v`. -/
theorem coord_act (z : Pl K → ℂ) (y : Space K ι) (p : ι × Pl K) : coord p (act part z y) = z p.2 * coord p y := by
  simp [act_apply, starProjection_part, map_sum, coord_op_single]

/-- Block-diagonal maps commute with `K ⊗ ℝ = ∏_v ℂ`. -/
theorem op_act (T : Pl K → Matrix κ ι ℂ) (z : Pl K → ℂ) (y : Space K ι) :
    op T (act part z y) = act part z (op T y) :=
  ext_coord fun p => by simp [coord_op, coord_act, Finset.mul_sum, mul_left_comm]

/-- `K^ι` in `⊕_v ℂ^ι`, by the embeddings: `x ↦ (σ_v(x_i))_{i,v}`. -/
noncomputable def ψ₀ : (ι → K) →+ Space K ι where
  toFun x := (toLp 2 fun p : ι × Pl K => p.2.1.embedding (x p.1) : EuclideanSpace ℂ (ι × Pl K))
  map_zero' := by simp; rfl
  map_add' x y := by simp; rfl

/-- `ψ₀ x` in coordinates. -/
theorem coord_ψ₀ (x : ι → K) (p : ι × Pl K) : coord p (ψ₀ x : Space K ι) = p.2.1.embedding (x p.1) := rfl

/-- `k ∈ K` acts on `ψ₀ x` by `emb k`. -/
theorem ψ₀_smul (k : K) (x : ι → K) : ψ₀ (k • x) = act part (emb k) (ψ₀ x : Space K ι) :=
  ext_coord fun p => by simp [coord_ψ₀, coord_act, emb]

/-- A matrix over `K` acts on `ψ₀ x` blockwise by its embeddings. -/
theorem op_ψ₀ (B : Matrix κ ι K) (x : ι → K) : op (fun v => B.map v.1.embedding) (ψ₀ x) = ψ₀ (B *ᵥ x) :=
  ext_coord fun p => by simp [coord_op, coord_ψ₀, mulVec, dotProduct]

/-- Every vector is a sum of the `act (Pi.single v c) (ψ₀ (Pi.single i 1))`. -/
theorem sum_act_ψ₀ (y : Space K ι) :
    ∑ p : ι × Pl K, act part (Pi.single p.2 (coord p y)) (ψ₀ (Pi.single p.1 1)) = y :=
  ext_coord fun q => by simp [map_sum, coord_act, coord_ψ₀, Pi.single_apply, Fintype.sum_prod_type]

/-- `dim_ℝ ⊕_v ℂ^ι = 2·n_∞·|ι| = [K:ℚ]·|ι| = dim_ℚ K^ι`. -/
theorem finrank_space [IsTotallyComplex K] : finrank ℝ (Space K ι) = finrank ℚ (ι → K) := by
  rw [finrank_real_of_complex, show finrank ℂ (Space K ι) = Fintype.card (ι × Pl K) from finrank_euclideanSpace,
    Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, IsTotallyComplex.finrank,
    Fintype.card_prod]
  ring

/-- **The embedding** `x ↦ (A_v σ_v(x))_v` of `K^ι` in `⊕_v ℂ^ι`. -/
noncomputable def ψ : (ι → K) →+ Space K ι :=
  (op X.factor : Space K ι →+ Space K ι).comp ψ₀

/-- `ψ = op A ∘ ψ₀`. -/
theorem ψ_apply (x : ι → K) : X.ψ x = op X.factor (ψ₀ x) := rfl

/-- **The metric**: `⟪ψ x, ψ y⟫ = ⟪ψ₀ x, G (ψ₀ y)⟫ = Σ_v σ_v(x)ᴴ G_v σ_v(y)`, which depends on `G` alone. -/
theorem inner_ψ (x y : ι → K) : ⟪X.ψ x, X.ψ y⟫_ℂ = ⟪ψ₀ x, op X.G (ψ₀ y)⟫_ℂ := by
  rw [ψ_apply, ψ_apply, inner_op, ← op_mul]
  simp_rw [X.factor_spec]

/-- `ψ(k x) = act (emb k) (ψ x)`. -/
theorem ψ_smul (k : K) (x : ι → K) : X.ψ (k • x) = act part (emb k) (X.ψ x) := by
  rw [ψ_apply, ψ_apply, ψ₀_smul, op_act]

/-- **The lattice** `ψ(M)`. -/
noncomputable def lattice : Submodule ℤ (Space K ι) :=
  (X.M.restrictScalars ℤ).map X.ψ.toIntLinearMap

/-- `ψ(M)` is stable under `O_K`. -/
theorem stable : Stable part X.lattice := by
  rintro k _ ⟨x, hx, rfl⟩
  exact ⟨(k : K) • x, X.M.smul_mem k hx, X.ψ_smul k x⟩

/-- **Full rank**: the real span of `ψ(M)` is stable under `K ⊗ ℝ` (`act_mem`), and `M` spans `K^ι`, so it contains
`ψ(K^ι)`, and then every vector (`sum_act_ψ₀`). -/
theorem span_lattice : span ℝ (X.lattice : Set (Space K ι)) = ⊤ := by
  set U := span ℝ (X.lattice : Set (Space K ι))
  have hU : ∀ k : 𝓞 K, ∀ y ∈ U, act part (emb (k : K)) y ∈ U := fun k _ hy => span_stable X.stable k hy
  have hψ (x : ι → K) : X.ψ x ∈ U := by
    have hx : x ∈ span K (X.M : Set (ι → K)) := by simp [IsLattice.span_eq_top]
    induction hx using span_induction with
    | mem x hx => exact subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul k x _ hx => rw [X.ψ_smul]; exact act_mem hU _ hx
  refine eq_top_iff.2 fun y _ => ?_
  rw [← op_one y, ← funext fun v => mul_eq_one_comm.1 (X.inv_mul_factor v), op_mul, ← sum_act_ψ₀ (op _ y), map_sum]
  exact sum_mem fun p _ => by rw [op_act]; exact act_mem hU _ (hψ _)

variable [IsTotallyComplex K]

/-- **Discrete**: a `ℤ`-basis of `M` is free over `ℚ`, so it has at most `dim_ℚ K^ι = dim_ℝ` members; and it spans,
so its image is a basis over `ℝ`, whose `ℤ`-span contains `ψ(M)`. -/
instance discrete : DiscreteTopology X.lattice := by
  have : Module.Finite ℤ (X.M.restrictScalars ℤ) := Module.Finite.iff_fg.2 IsLattice.fg.restrictScalars
  let b := Module.Free.chooseBasis ℤ (X.M.restrictScalars ℤ)
  have hb : X.lattice ≤ span ℤ (Set.range fun j => X.ψ (b j)) := by
    rintro _ ⟨x, hx, rfl⟩
    have := mem_map_of_mem (f := X.ψ.toIntLinearMap ∘ₗ (X.M.restrictScalars ℤ).subtype) (b.mem_span ⟨x, hx⟩)
    rwa [map_span, ← Set.range_comp] at this
  have hspan : ⊤ ≤ span ℝ (Set.range fun j => X.ψ (b j)) :=
    X.span_lattice ▸ span_le.2 fun y hy => span_le_restrictScalars ℤ ℝ _ (hb hy)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (X.M.restrictScalars ℤ)) ≤ finrank ℝ (Space K ι) := by
    rw [finrank_space]
    exact ((LinearIndependent.iff_fractionRing ℤ ℚ).1
      (b.linearIndependent.map' _ (ker_subtype _))).fintype_card_le_finrank
  have hli := linearIndependent_of_top_le_span_of_card_le_finrank hspan hcard
  exact EuclidLattice.discrete_of_le (N := span ℤ (Set.range (Basis.mk hli hspan))) (by rwa [Basis.coe_mk])

/-- **The hermitian lattice** of `X`: `ψ(M)`, with the parts `ℂ^ι` at the complex places (`placeLattice`). -/
noncomputable def toPlaceLattice : PlaceLattice (Space K ι) :=
  placeLattice part part_orth part_iSup X.lattice X.stable

/-- `ψ` is injective, as the factors are invertible and the embeddings injective. -/
theorem ψ_injective : Function.Injective X.ψ := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => funext fun i => ?_
  have h0 : (ψ₀ x : Space K ι) = 0 := by
    rw [← op_one (ψ₀ x), ← funext X.inv_mul_factor, op_mul, ← ψ_apply, hx, map_zero]
  obtain ⟨v⟩ : Nonempty (Pl K) := ⟨⟨Classical.arbitrary _, IsTotallyComplex.isComplex _⟩⟩
  have := congrArg (coord (i, v)) h0
  rwa [coord_ψ₀, map_zero, map_eq_zero_iff _ (RingHom.injective _)] at this

/-- **Ranks**: `rk ψ(M) = [K:ℚ]·|ι| = 2·n_∞·|ι|`, twice the complex dimension of `⊕_v ℂ^ι`. -/
theorem rk_top : X.toPlaceLattice.slopeLattice.rk ⊤ = finrank ℚ K * Fintype.card ι := by
  show finrank ℝ (span ℝ (X.lattice : Set (Space K ι))) = _
  rw [span_lattice, finrank_top, finrank_space, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm]

/-! ### Index and scaling -/

/-- `X` with the lattice `N` in place of `M`. -/
abbrev withLattice (N : Submodule (𝓞 K) (ι → K)) [N.IsLattice K] : KLattice K ι := ⟨N, X.G, X.posDef⟩

/-- **Index**: for `O_K`-lattices `N ≤ M`, `deg N = deg M − log [M : N]`, with `[M : N]` the index of groups. -/
theorem deg_withLattice {N : Submodule (𝓞 K) (ι → K)} [N.IsLattice K] (hN : N ≤ X.M) :
    (X.withLattice N).toPlaceLattice.slopeLattice.deg ⊤ =
      X.toPlaceLattice.slopeLattice.deg ⊤ - Real.log (N.toAddSubgroup.relIndex X.M.toAddSubgroup) := by
  have hrk : finrank ℤ (X.withLattice N).lattice = finrank ℤ X.lattice := by
    rw [← EuclidLattice.finrank_span, ← EuclidLattice.finrank_span, span_lattice, span_lattice]
  have hle : (X.withLattice N).lattice ≤ X.lattice := fun y ⟨x, hx, hxy⟩ => ⟨x, hN hx, hxy⟩
  have h := EuclidLattice.covol_eq_relIndex_mul hle hrk
  have hi : (X.withLattice N).lattice.toAddSubgroup.relIndex X.lattice.toAddSubgroup =
      N.toAddSubgroup.relIndex X.M.toAddSubgroup := by
    rw [lattice, lattice, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ X.ψ_injective
  rw [hi] at h
  have hpos : 0 < (N.toAddSubgroup.relIndex X.M.toAddSubgroup : ℝ) :=
    pos_of_mul_pos_left (h ▸ EuclidLattice.covol_pos _) (EuclidLattice.covol_pos _).le
  show -Real.log (EuclidLattice.covol (X.withLattice N).lattice) = -Real.log (EuclidLattice.covol X.lattice) - _
  rw [h, Real.log_mul hpos.ne' (EuclidLattice.covol_pos _).ne']
  ring

/-- **The slope after an index**: `μ(N) = μ(M) − log [M : N]/rk`. -/
theorem slope_withLattice {N : Submodule (𝓞 K) (ι → K)} [N.IsLattice K] (hN : N ≤ X.M) :
    (X.withLattice N).toPlaceLattice.slopeLattice.deg ⊤ / (X.withLattice N).toPlaceLattice.slopeLattice.rk ⊤ =
      X.toPlaceLattice.slopeLattice.deg ⊤ / X.toPlaceLattice.slopeLattice.rk ⊤ -
        Real.log (N.toAddSubgroup.relIndex X.M.toAddSubgroup) / X.toPlaceLattice.slopeLattice.rk ⊤ := by
  rw [deg_withLattice X hN, rk_top, rk_top, sub_div]

/-- `X` with its metrics multiplied by `c > 0`. -/
noncomputable abbrev scale (c : ℝ) (hc : 0 < c) : KLattice K ι :=
  ⟨X.M, fun v => c • X.G v, fun v => (X.posDef v).smul hc⟩

/-- **Scaling the metrics** by `c > 0` multiplies inner products by `c` (`inner_ψ`), so it shifts the degree by
`−(rk/2)·log c` (`EuclidLattice.covol_sq_eq`). -/
theorem deg_scale {c : ℝ} (hc : 0 < c) :
    (X.scale c hc).toPlaceLattice.slopeLattice.deg ⊤ =
      X.toPlaceLattice.slopeLattice.deg ⊤ - X.toPlaceLattice.slopeLattice.rk ⊤ / 2 * Real.log c := by
  let e₁ : X.M.restrictScalars ℤ ≃ₗ[ℤ] X.lattice :=
    Submodule.equivMapOfInjective X.ψ.toIntLinearMap X.ψ_injective _
  let e₂ : X.M.restrictScalars ℤ ≃ₗ[ℤ] (X.scale c hc).lattice :=
    Submodule.equivMapOfInjective (X.scale c hc).ψ.toIntLinearMap (X.scale c hc).ψ_injective _
  have h := EuclidLattice.covol_sq_eq (e₁.symm.trans e₂) c fun x y => by
    obtain ⟨x, rfl⟩ := e₁.surjective x
    obtain ⟨y, rfl⟩ := e₁.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    show ⟪(X.scale c hc).ψ x, (X.scale c hc).ψ y⟫_ℝ = c * ⟪X.ψ x, X.ψ y⟫_ℝ
    rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, inner_ψ, inner_ψ]
    simp_rw [← Complex.coe_smul c]
    rw [op_smul, inner_smul_right]
    exact Complex.re_ofReal_mul c _
  have hl := congrArg Real.log h
  rw [Real.log_pow, Real.log_mul (pow_ne_zero _ hc.ne') (pow_ne_zero _ (EuclidLattice.covol_pos _).ne'),
    Real.log_pow, Real.log_pow] at hl
  show -Real.log (EuclidLattice.covol (X.scale c hc).lattice) = -Real.log (EuclidLattice.covol X.lattice) -
    (finrank ℝ (span ℝ (X.lattice : Set (Space K ι))) : ℝ) / 2 * Real.log c
  rw [EuclidLattice.finrank_span]
  push_cast at hl
  linarith

/-! ### The `K`-rational case -/

/-- **The `K`-rational case**: a matrix `H` over `K` positive definite at every complex place gives the metrics
`G v = σ_v(H)`. -/
noncomputable abbrev ofForm (M : Submodule (𝓞 K) (ι → K)) [M.IsLattice K] (H : Matrix ι ι K)
    (hH : ∀ v : Pl K, (H.map v.1.embedding).PosDef) : KLattice K ι :=
  ⟨M, fun v => H.map v.1.embedding, hH⟩

omit [Fintype ι] [IsTotallyComplex K] in
/-- On a CM field, a matrix hermitian for complex conjugation is hermitian at every complex place, so only positivity
is asked of `σ_v(H)` there. -/
theorem isHermitian_map [IsCMField K] {H : Matrix ι ι K} (hH : H.IsHermitian) (v : Pl K) :
    (H.map v.1.embedding).IsHermitian :=
  hH.map _ fun x => IsCMField.complexEmbedding_complexConj K _ x

/-! ### Maps and frames -/

variable (Y : KLattice K κ)

/-- **The map of a `K`-linear map** `B : K^ι → K^κ`: blockwise `A'_v σ_v(B) A_v⁻¹`, which is `σ_v(B)` in the
coordinates of the metrics. It extends `B` (`hom_ψ`). -/
noncomputable def hom (B : (ι → K) →ₗ[K] (κ → K)) : Space K ι →L[ℂ] Space K κ :=
  op fun v => Y.factor v * (LinearMap.toMatrix' B).map v.1.embedding * (X.factor v)⁻¹

omit [IsTotallyComplex K] in
/-- The map of `B` extends `B`: `φ(ψ x) = ψ'(B x)`. -/
theorem hom_ψ (B : (ι → K) →ₗ[K] (κ → K)) (x : ι → K) : X.hom Y B (X.ψ x) = Y.ψ (B x) := by
  rw [ψ_apply, hom, ← op_mul, ψ_apply, ← LinearMap.toMatrix'_mulVec B x, ← op_ψ₀, ← op_mul]
  simp_rw [Matrix.mul_assoc, inv_mul_factor, Matrix.mul_one]

omit [IsTotallyComplex K] in
/-- The map commutes with `O_K`. -/
theorem hom_act (B : (ι → K) →ₗ[K] (κ → K)) (k : 𝓞 K) (y : Space K ι) :
    (X.hom Y B).restrictScalars ℝ (act part (emb (k : K)) y) =
      act part (emb (k : K)) ((X.hom Y B).restrictScalars ℝ y) :=
  op_act _ _ _

omit [IsTotallyComplex K] in
/-- The map sends `ψ(M)` into `ψ'(M')` when `B(M) ⊆ M'`. -/
theorem hom_mem {B : (ι → K) →ₗ[K] (κ → K)} (hB : ∀ x ∈ X.M, B x ∈ Y.M) :
    ∀ y ∈ X.lattice, (X.hom Y B).restrictScalars ℝ y ∈ Y.lattice := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨B x, hB x hx, (X.hom_ψ Y B x).symm⟩

variable {Ω : Type} [Fintype Ω] {n : Ω → Type} [∀ ω, Fintype (n ω)] [Nonempty κ] (X : ∀ ω, KLattice K (n ω))
  (B : ∀ ω, (n ω → K) →ₗ[K] (κ → K)) (hB : ∀ ω, ∀ x ∈ (X ω).M, B ω x ∈ Y.M) (h : Ω → Pl K → ℝ)
  (hφ : ∀ ω v, ∀ x ∈ (part v : Submodule ℂ (Space K (n ω))), ‖(X ω).hom Y (B ω) x‖ ≤ Real.exp (h ω v) * ‖x‖)

/-- **Frames of hermitian `O_K`-lattices**: lattices `X ω` mapped into one lattice `Y` by `K`-linear maps `B ω` with
`B ω (M_ω) ⊆ M_Y`, with `e^{h ω v}` bounding the maps on the parts at each complex place `v`
(`HermitianLattice.frame`). -/
noncomputable def frame : SlopeFrame.Frame :=
  HermitianLattice.frame (fun _ => part) (fun _ => part_orth) (fun _ => part_iSup) (fun ω => (X ω).lattice)
    (fun ω => (X ω).stable) part part_orth part_iSup Y.lattice Y.stable
    (fun ω => ((X ω).hom Y (B ω)).restrictScalars ℝ) (fun ω => (X ω).hom_mem Y (hB ω))
    (fun ω => (X ω).hom_act Y (B ω)) h hφ (by rw [Y.span_lattice, finrank_top, finrank_space]; exact Module.finrank_pos)

/-- **Rank spreading from the frame condition at one complex place** (`HermitianLattice.spread_of_frameCond`): if
multiples `c ω` of the components of the maps at `v` (`HermitianLattice.component`) meet the frame condition over `ℂ`
with constants `e` and `η`, then the frame spreads ranks with `α = η + 2√e/(1 − √e)` and `β = 2/(1 − √e)`. -/
theorem spread_of_frameCond (v : Pl K) (c : Ω → ℝ) {e η : ℝ}
    (hc : FrameAtPlace.FrameCond (fun ω => c ω • component ((X ω).hom_act Y (B ω)) v) e η) :
    (frame Y X B hB h hφ).RankSpread (η + 2 * √e / (1 - √e)) (2 / (1 - √e)) := by
  have := HermitianLattice.spread_of_frameCond (fun _ => part) (fun _ => part_orth) (fun _ => part_iSup)
    (fun ω => (X ω).lattice) (fun ω => (X ω).stable) part part_orth part_iSup Y.lattice Y.stable
    (fun ω => ((X ω).hom Y (B ω)).restrictScalars ℝ) (fun ω => (X ω).hom_mem Y (hB ω))
    (fun ω => (X ω).hom_act Y (B ω)) h hφ (frame Y X B hB h hφ).rk_pos (fun ω => (X ω).span_lattice) v
    (fun ω => component ((X ω).hom_act Y (B ω)) v) (fun _ _ => rfl) c hc zero_lt_one
    (by rw [Y.span_lattice, top_inf_eq, sub_zero, one_mul])
  rwa [sub_zero, inv_one, one_mul, one_mul] at this

end KLattice
