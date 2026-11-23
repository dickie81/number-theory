import Mathlib
import GramVolume
import SlopeFrame

/-!
# Euclidean lattices and their slopes

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, step 4): concrete lattices for the
frame inequality of `SlopeFrame`, with Bost's slope inequality on images.

`Λ` is a discrete subgroup of a finite-dimensional real inner product space `E`, not necessarily of full rank.

* `Sat Λ`: its saturated sublattices, the `M ≤ Λ` containing every point of `Λ` in their real span. They form a bounded
  lattice with `⊥ = 0`, `⊤ = Λ`, `M ⊓ N = M ∩ N`, and `M ⊔ N` the saturation of `M + N`.
* The rank of `M` is `dim span M`, its `ℤ`-rank (`finrank_span`); `covol M` is the volume of any `ℤ`-basis
  (`covol_eq_vol`), and the degree is `−log covol M`. They make `Sat Λ` a `SlopeLattice` (`slopeLattice`).
* Rank is modular (`rk_sup_add_rk_inf`) and degree supermodular (`deg_add_deg_le`), so sums of sublattices of minimal
  slope at least `θ` have minimal slope at least `θ` (`supClosed`).
* **Bost's inequality** (`bost`): if `φ : E → F` sends `Λ` into `Λ'` and `‖φ‖ ≤ eʰ`, then `img φ a`, the saturation of
  `φ(a)`, has `μ_min(img φ a) ≥ μ_min(a) − h`. At `b ≤ img φ a` it uses the slope bound for `a` only at
  `a ⊓ preimg φ b` (`bost_le`), so it also serves sublattices of `Sat Λ` closed under `⊓` that contain these.

The facts used:

1. **Rationality.** For discrete subgroups, `dim span` is the `ℤ`-rank (`Real.finrank_eq_int_finrank_of_discrete`).
   With rank–nullity over `ℤ` and `ℝ`, rational subspaces are spanned by lattice points: `span (M ∩ N) =
   span M ∩ span N` (`span_inf`), and `span (A ∩ g⁻¹ B) = span A ∩ g⁻¹(span B)` when `g(A)` and `B` lie in a
   discrete subgroup (`span_inf_comap`).
2. **Additivity** (`exists_adapted`). For saturated `K ≤ X`, a basis of `K` extends to a basis `(k, x)` of `X`, since
   `X/K` is torsion-free, hence free (`exists_basis_extend`). Then `covol X = covol K·vol (π ∘ x)`, with `π` the
   projection onto `(span K)ᗮ`.
3. **Index** (`covol_le`). `rk M` vectors of `M` spanning `span M` have volume at least `covol M`.
4. **Hadamard**: `vol (f ∘ v) ≤ ‖f‖ⁿ·vol v` (`GramVolume.vol_comp_le`).

The two inequalities:

* **Supermodularity.** Take a basis `z` of `a ⊓ b`, and adapted bases `(z, x)` of `a` and `(z, y)` of `b`. Then
  `covol (a ⊔ b) ≤ vol (z, x, y) = vol z·vol (πx, πy) ≤ vol z·vol πx·vol πy = covol a·covol b/covol (a ⊓ b)`.
* **Bost.** For `b ≤ img φ a`, the sublattice `K = a ⊓ preimg φ b = a ∩ φ⁻¹ b` is saturated. Take a basis `(k, x)` of
  `a` adapted to `K`, and a basis `β` of `b`. As `span K = span a ∩ φ⁻¹(span b)`, the family `(β, φx)` is
  independent, and it spans `img φ a`. So `covol (img φ a) ≤ vol (β, φx) = covol b·vol (π_b φ π_K x) ≤
  covol b·‖φ‖ʳ·covol a/covol K`, with `r = rk a − rk K = rk (img φ a) − rk b`, and the slope bound for `a` at `K`
  finishes.
-/

namespace EuclidLattice

open Module Submodule GramVolume

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-! ### Discrete subgroups and their real spans -/

/-- A subgroup of a discrete subgroup is discrete. -/
theorem discrete_of_le {M N : Submodule ℤ E} [DiscreteTopology N] (h : M ≤ N) : DiscreteTopology M :=
  DiscreteTopology.of_subset (s := (N : Set E)) ‹_› h

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- The real span of a sum of subgroups is the sum of their real spans. -/
theorem span_sup (M N : Submodule ℤ E) :
    span ℝ ((M ⊔ N : Submodule ℤ E) : Set E) = span ℝ (M : Set E) ⊔ span ℝ (N : Set E) := by
  rw [← span_union, ← span_span_of_tower (R := ℤ) (S := ℝ) ((M : Set E) ∪ N), span_union, span_eq, span_eq]

/-- A `ℤ`-basis of `M` spans `span M` over `ℝ`. -/
theorem span_basis {M : Submodule ℤ E} {ι : Type*} (b : Basis ι ℤ M) :
    span ℝ (Set.range fun i => (b i : E)) = span ℝ (M : Set E) := by
  have h := congrArg (map M.subtype) b.span_eq
  rw [map_span, Submodule.map_top, range_subtype, ← Set.range_comp] at h
  conv_rhs => rw [← h]
  exact (span_span_of_tower (R := ℤ) (S := ℝ) _).symm

/-- **Change of basis**: `vol (b·P) = |det P|·vol b` for a `ℤ`-basis `b` and an integer matrix `P`. -/
theorem vol_eq_abs_det_mul {M : Submodule ℤ E} {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ M)
    (v : ι → M) : vol (fun j => (v j : E)) = |(b.det v : ℝ)| * vol fun i => (b i : E) := by
  rw [b.det_apply, Int.cast_det, ← vol_comb]
  congr 1
  funext j
  simp only [Matrix.map_apply, Int.cast_smul_eq_zsmul]
  exact_mod_cast (congrArg Subtype.val (b.sum_toMatrix_smul_self v j)).symm

/-! ### Saturated sublattices -/

/-- The saturation in `Λ` of a set: the points of `Λ` in its real span. -/
def sat (Λ : Submodule ℤ E) (s : Set E) : Submodule ℤ E :=
  Λ ⊓ (span ℝ s).restrictScalars ℤ

/-- The saturated sublattices of `Λ`: the `M ≤ Λ` that contain every point of `Λ` in their real span. -/
abbrev Sat (Λ : Submodule ℤ E) : Type _ :=
  {M : Submodule ℤ E // M ≤ Λ ∧ ∀ x ∈ Λ, x ∈ span ℝ (M : Set E) → x ∈ M}

variable {Λ : Submodule ℤ E}

/-- A saturation spans no more than the set. -/
theorem span_sat_le (s : Set E) : span ℝ (sat Λ s : Set E) ≤ span ℝ s :=
  span_le.2 fun _ hy => hy.2

/-- A saturation is saturated. -/
theorem sat_isSat (s : Set E) : sat Λ s ≤ Λ ∧ ∀ x ∈ Λ, x ∈ span ℝ (sat Λ s : Set E) → x ∈ sat Λ s :=
  ⟨inf_le_left, fun _ hx hxs => ⟨hx, span_sat_le s hxs⟩⟩

/-- The saturation of a subset of `Λ` has the same real span. -/
theorem span_sat {s : Set E} (hs : s ⊆ Λ) : span ℝ (sat Λ s : Set E) = span ℝ s :=
  le_antisymm (span_sat_le s) (span_mono fun _ hx => ⟨hs hx, subset_span hx⟩)

namespace Sat

/-- `a ⊓ b = a ∩ b`, and `a ⊔ b` is the saturation of `a + b`. -/
instance : Lattice (Sat Λ) where
  sup a b := ⟨sat Λ ((a.1 ⊔ b.1 : Submodule ℤ E) : Set E), sat_isSat _⟩
  le_sup_left a _ _ hx := ⟨a.2.1 hx, subset_span (mem_sup_left hx)⟩
  le_sup_right _ b _ hx := ⟨b.2.1 hx, subset_span (mem_sup_right hx)⟩
  sup_le _ _ c hac hbc x hx := c.2.2 x hx.1 (span_mono (SetLike.coe_subset_coe.2 (sup_le hac hbc)) hx.2)
  inf a b := ⟨a.1 ⊓ b.1, inf_le_left.trans a.2.1, fun x hx hxs =>
    ⟨a.2.2 x hx (span_mono inf_le_left hxs), b.2.2 x hx (span_mono inf_le_right hxs)⟩⟩
  inf_le_left a b := show a.1 ⊓ b.1 ≤ a.1 from inf_le_left
  inf_le_right a b := show a.1 ⊓ b.1 ≤ b.1 from inf_le_right
  le_inf a b c hab hac := show a.1 ≤ b.1 ⊓ c.1 from le_inf hab hac

/-- `⊥ = 0` and `⊤ = Λ`. -/
instance : BoundedOrder (Sat Λ) where
  top := ⟨Λ, le_rfl, fun _ hx _ => hx⟩
  le_top a := a.2.1
  bot := ⟨⊥, bot_le, fun _ _ hx => by simpa using hx⟩
  bot_le a := show ⊥ ≤ a.1 from bot_le

/-- `⊥ = 0`. -/
theorem coe_bot : (⊥ : Sat Λ).1 = ⊥ := rfl

/-- `a ⊔ b` is the saturation of `a + b`. -/
theorem coe_sup (a b : Sat Λ) : (a ⊔ b).1 = sat Λ ((a.1 ⊔ b.1 : Submodule ℤ E) : Set E) := rfl

/-- The real span of `a ⊔ b` is `span a + span b`. -/
theorem span_coe_sup (a b : Sat Λ) :
    span ℝ ((a ⊔ b).1 : Set E) = span ℝ (a.1 : Set E) ⊔ span ℝ (b.1 : Set E) := by
  rw [coe_sup, span_sat (SetLike.coe_subset_coe.2 (sup_le a.2.1 b.2.1)), span_sup]

end Sat

/-! ### Ranks and rationality -/

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The real span of a discrete subgroup has dimension its `ℤ`-rank. -/
theorem finrank_span (M : Submodule ℤ E) [DiscreteTopology M] :
    finrank ℝ (span ℝ (M : Set E)) = finrank ℤ M := by
  have h : finrank ℝ (span ℝ (M : Set E)) = finrank ℤ (span ℤ (M : Set E)) :=
    Real.finrank_eq_int_finrank_of_discrete (by rwa [span_eq])
  rwa [span_eq] at h

/-- **Rank–nullity** on a submodule: `rk h(P) + rk (P ∩ ker h) = rk P`. -/
theorem finrank_map_add_finrank_inf_ker {R M N : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (P : Submodule R M) [Module.Finite R P] (h : M →ₗ[R] N) :
    finrank R (P.map h) + finrank R ↥(P ⊓ LinearMap.ker h) = finrank R P := by
  have := (LinearMap.ker (h ∘ₗ P.subtype)).finrank_quotient_add_finrank
  rwa [(h ∘ₗ P.subtype).quotKerEquivRange.finrank_eq, LinearMap.range_comp, range_subtype, LinearMap.ker_comp,
    ← finrank_map_subtype_eq, map_comap_subtype] at this

/-- **Rationality of intersections**: for subgroups of a discrete subgroup, `span (M ∩ N) = span M ∩ span N`. Both
sides have dimension `rk M + rk N − rk (M + N)`, by modularity of `ℤ`-ranks and of dimensions. -/
theorem span_inf {M N : Submodule ℤ E} [DiscreteTopology Λ] (hM : M ≤ Λ) (hN : N ≤ Λ) :
    span ℝ ((M ⊓ N : Submodule ℤ E) : Set E) = span ℝ (M : Set E) ⊓ span ℝ (N : Set E) := by
  have := discrete_of_le hM
  have := discrete_of_le hN
  have := discrete_of_le (sup_le hM hN)
  have := discrete_of_le (inf_le_left.trans hM : M ⊓ N ≤ Λ)
  refine eq_of_le_of_finrank_eq (le_inf (span_mono inf_le_left) (span_mono inf_le_right)) ?_
  have h := rank_sup_add_rank_inf_eq M N
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank]
    at h
  norm_cast at h
  rw [← finrank_span, ← finrank_span, ← finrank_span, ← finrank_span, span_sup] at h
  have := finrank_sup_add_finrank_inf_eq (span ℝ (M : Set E)) (span ℝ (N : Set E))
  omega

/-- **Rationality of kernels**: if a linear map `g` sends a discrete subgroup `A` into a discrete subgroup, then
`span (A ∩ ker g) = span A ∩ ker g`. Both sides have dimension `rk A − rk g(A)`, by rank–nullity over `ℤ` and `ℝ`. -/
theorem span_inf_ker {A : Submodule ℤ E} [DiscreteTopology A] {Λ' : Submodule ℤ F} [DiscreteTopology Λ']
    (g : E →ₗ[ℝ] F) (hg : ∀ x ∈ A, g x ∈ Λ') :
    span ℝ ((A ⊓ LinearMap.ker (g.restrictScalars ℤ) : Submodule ℤ E) : Set E) =
      span ℝ (A : Set E) ⊓ LinearMap.ker g := by
  have hAg : A.map (g.restrictScalars ℤ) ≤ Λ' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have := discrete_of_le hAg
  have := discrete_of_le (inf_le_left : A ⊓ LinearMap.ker (g.restrictScalars ℤ) ≤ A)
  refine eq_of_le_of_finrank_eq (le_inf (span_mono inf_le_left) (span_le.2 fun x hx => hx.2)) ?_
  have h := finrank_map_add_finrank_inf_ker A (g.restrictScalars ℤ)
  rw [← finrank_span, ← finrank_span, ← finrank_span, map_coe, LinearMap.coe_restrictScalars, span_image] at h
  have := finrank_map_add_finrank_inf_ker (span ℝ (A : Set E)) g
  omega

/-- **Rationality of preimages**: if `g` sends a discrete subgroup `A` into a discrete subgroup `Λ'`, and `B ≤ Λ'`,
then the points of `A` that `g` sends into `B` span `span A ∩ g⁻¹(span B)`. Indeed `g(A) ∩ B` spans
`g(span A) ∩ span B` (`span_inf`), and `A ∩ ker g` spans `span A ∩ ker g` (`span_inf_ker`). -/
theorem span_inf_comap {A : Submodule ℤ E} [DiscreteTopology A] {Λ' B : Submodule ℤ F} [DiscreteTopology Λ']
    (hB : B ≤ Λ') (g : E →ₗ[ℝ] F) (hg : ∀ x ∈ A, g x ∈ Λ') :
    span ℝ ((A ⊓ B.comap (g.restrictScalars ℤ) : Submodule ℤ E) : Set E) =
      span ℝ (A : Set E) ⊓ (span ℝ (B : Set F)).comap g := by
  have hAg : A.map (g.restrictScalars ℤ) ≤ Λ' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  refine le_antisymm (le_inf (span_mono inf_le_left) (span_le.2 fun x hx => subset_span hx.2)) ?_
  rintro v ⟨hvA, hvB⟩
  have h1 : g v ∈ span ℝ (((A ⊓ B.comap (g.restrictScalars ℤ)).map (g.restrictScalars ℤ) : Submodule ℤ F) :
      Set F) := by
    refine span_mono ?_ ((span_inf hAg hB).ge ⟨?_, hvB⟩)
    · rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
    · rw [map_coe, LinearMap.coe_restrictScalars, span_image]
      exact mem_map_of_mem hvA
  rw [map_coe, LinearMap.coe_restrictScalars, span_image] at h1
  obtain ⟨w, hw, hgw⟩ := h1
  have h2 : v - w ∈ span ℝ ((A ⊓ LinearMap.ker (g.restrictScalars ℤ) : Submodule ℤ E) : Set E) := by
    rw [span_inf_ker g hg]
    exact ⟨sub_mem hvA (span_mono inf_le_left hw), by simp [hgw]⟩
  have hker : LinearMap.ker (g.restrictScalars ℤ) ≤ B.comap (g.restrictScalars ℤ) := fun x hx => by
    simp only [LinearMap.mem_ker] at hx
    simp [hx]
  simpa using add_mem (span_mono (inf_le_inf_left A hker) h2) hw

/-! ### Covolumes -/

/-- The covolume of a discrete subgroup: the volume of a `ℤ`-basis, which does not depend on the basis
(`covol_eq_vol`). -/
noncomputable def covol (M : Submodule ℤ E) [DiscreteTopology M] : ℝ :=
  vol fun i => (finBasis ℤ M i : E)

/-- The covolume is the volume of any `ℤ`-basis, as two bases differ by a unimodular integer matrix. -/
theorem covol_eq_vol {M : Submodule ℤ E} [DiscreteTopology M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ M) : covol M = vol fun i => (b i : E) := by
  let e := b.indexEquiv (finBasis ℤ M)
  have hu : |((((finBasis ℤ M).reindex e.symm).det b : ℤ) : ℝ)| = 1 := by
    rw [← Int.cast_abs, Int.isUnit_iff_abs_eq.1 (Basis.isUnit_det _ _), Int.cast_one]
  rw [vol_eq_abs_det_mul ((finBasis ℤ M).reindex e.symm) b, hu, one_mul]
  simp only [Basis.reindex_apply, Equiv.symm_symm]
  exact (vol_comp_equiv (fun i => (finBasis ℤ M i : E)) e).symm

/-- A `ℤ`-basis of a discrete subgroup is linearly independent over `ℝ`. -/
theorem linearIndependent_basis {M : Submodule ℤ E} [DiscreteTopology M] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ M) : LinearIndependent ℝ fun i => (b i : E) := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_basis, finrank_span, finrank_eq_card_basis b]

/-- Covolumes are positive. -/
theorem covol_pos (M : Submodule ℤ E) [DiscreteTopology M] : 0 < covol M :=
  vol_pos_iff.2 (linearIndependent_basis _)

/-- The zero subgroup has covolume `1`. -/
theorem covol_eq_one {M : Submodule ℤ E} [DiscreteTopology M] (h : M = ⊥) : covol M = 1 := by
  subst h
  have : IsEmpty (Fin (finrank ℤ (⊥ : Submodule ℤ E))) := by rw [finrank_bot]; infer_instance
  exact vol_of_isEmpty _

/-- A family whose real span contains `M` has at least `rk M` members. -/
theorem finrank_le_card {M : Submodule ℤ E} [DiscreteTopology M] {ι : Type*} [Fintype ι] {v : ι → E}
    (hspan : span ℝ (M : Set E) ≤ span ℝ (Set.range v)) : finrank ℤ M ≤ Fintype.card ι :=
  finrank_span M ▸ (finrank_mono hspan).trans (finrank_range_le_card v)

/-- **Index**: `rk M` vectors of `M` spanning `span M` have volume at least `covol M`, since they are `b·P` for a basis
`b` and an integer matrix `P` of nonzero determinant. -/
theorem covol_le {M : Submodule ℤ E} [DiscreteTopology M] {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → E}
    (hv : ∀ i, v i ∈ M) (hspan : span ℝ (M : Set E) ≤ span ℝ (Set.range v)) (hcard : Fintype.card ι ≤ finrank ℤ M) :
    covol M ≤ vol v := by
  have hc : Fintype.card ι = finrank ℤ M := le_antisymm hcard (finrank_le_card hspan)
  have hs : span ℝ (Set.range v) = span ℝ (M : Set E) :=
    le_antisymm (span_le.2 (Set.range_subset_iff.2 fun i => subset_span (hv i))) hspan
  have hli : LinearIndependent ℝ v := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hs, finrank_span, hc]
  let b := (finBasis ℤ M).reindex (Fintype.equivFinOfCardEq hc).symm
  have h : vol v = |(b.det fun j => ⟨v j, hv j⟩ : ℝ)| * vol fun i => (b i : E) :=
    vol_eq_abs_det_mul b fun j => ⟨v j, hv j⟩
  have hd : b.det (fun j => ⟨v j, hv j⟩) ≠ 0 := fun h0 => by
    rw [h0, Int.cast_zero, abs_zero, zero_mul] at h
    exact (vol_pos_iff.2 hli).ne' h
  rw [covol_eq_vol b, h]
  exact le_mul_of_one_le_left (vol_nonneg _) (by exact_mod_cast Int.one_le_abs hd)

/-! ### Adapted bases -/

/-- **Adapted bases**: if `K ≤ X` contains every point of `X` in its real span, a `ℤ`-basis of `K` extends to one of
`X`, since `X/K` is torsion-free, hence free. -/
theorem exists_basis_extend {K X : Submodule ℤ E} [DiscreteTopology X] (hKX : K ≤ X)
    (hK : ∀ x ∈ X, x ∈ span ℝ (K : Set E) → x ∈ K) {ι : Type*} (bK : Basis ι ℤ K) :
    ∃ (n : ℕ) (b : Basis (ι ⊕ Fin n) ℤ X), ∀ i, (b (.inl i) : E) = bK i := by
  let W := K.comap X.subtype
  have : IsTorsionFree ℤ (X ⧸ W) := .of_smul_eq_zero fun r m h => by
    obtain ⟨x, rfl⟩ := W.mkQ_surjective m
    rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    refine or_iff_not_imp_left.2 fun hr => (Submodule.Quotient.mk_eq_zero W).2 (hK x x.2 ?_)
    have hx : (x : E) = (r : ℝ)⁻¹ • ((r • x : X) : E) := by
      rw [coe_smul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hr), one_smul]
    rw [hx]
    exact smul_mem _ _ (subset_span h)
  exact ⟨_, (bK.map (comapSubtypeEquivOfLe hKX).symm).sumQuot (finBasis ℤ (X ⧸ W)), fun i => by simp⟩

variable [DiscreteTopology Λ]

/-- Saturated sublattices are discrete. -/
instance (a : Sat Λ) : DiscreteTopology a.1 :=
  discrete_of_le a.2.1

/-- **Additivity**: for saturated `K ≤ X`, the basis of `K` extends by vectors `x` of `X` to a basis of `X`, and
`covol X = covol K·vol (π ∘ x)`, with `π` the projection onto `(span K)ᗮ`. -/
theorem exists_adapted {K X : Sat Λ} (hKX : K ≤ X) :
    ∃ (n : ℕ) (x : Fin n → E), (∀ j, x j ∈ X.1) ∧ finrank ℤ K.1 + n = finrank ℤ X.1 ∧
      span ℝ (X.1 : Set E) = span ℝ (K.1 : Set E) ⊔ span ℝ (Set.range x) ∧
      LinearIndependent ℝ x ∧ Disjoint (span ℝ (K.1 : Set E)) (span ℝ (Set.range x)) ∧
      covol X.1 = covol K.1 * vol fun j => (span ℝ (K.1 : Set E))ᗮ.starProjection (x j) := by
  obtain ⟨n, b, hb⟩ := exists_basis_extend hKX (fun y hy => K.2.2 y (X.2.1 hy)) (finBasis ℤ K.1)
  have hb' : (fun s => (b s : E)) = Sum.elim (fun i => (finBasis ℤ K.1 i : E)) fun j => (b (.inr j) : E) := by
    funext s
    cases s with
    | inl i => exact hb i
    | inr j => rfl
  have hli := linearIndependent_basis b
  rw [hb', linearIndependent_sum] at hli
  refine ⟨n, fun j => b (.inr j), fun j => (b _).2, ?_, ?_, hli.2.1, ?_, ?_⟩
  · rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  · rw [← span_basis b, hb', Set.Sum.elim_range, span_union, span_basis (finBasis ℤ K.1)]
  · simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, span_basis] using hli.2.2
  · rw [covol_eq_vol b, hb', vol_sumElim, span_basis]
    rfl

/-! ### The slope lattice -/

/-- The slope lattice of `Λ`: its saturated sublattices, with rank `dim span M` and degree `−log covol M`. -/
noncomputable def slopeLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ] : SlopeFrame.SlopeLattice (Sat Λ) where
  rk a := finrank ℝ (span ℝ (a.1 : Set E))
  deg a := -Real.log (covol a.1)
  rk_bot := by simp [Sat.coe_bot]
  deg_bot := by rw [covol_eq_one Sat.coe_bot, Real.log_one, neg_zero]
  rk_strictMono a b hab := finrank_lt_finrank_of_lt <| (span_mono (show (a.1 : Set E) ⊆ b.1 from hab.le)).lt_of_ne
    fun h => hab.not_ge fun x hx => a.2.2 x (b.2.1 hx) (h ▸ subset_span hx)

/-- The rank of `a` is its `ℤ`-rank. -/
theorem rk_eq (a : Sat Λ) : (slopeLattice Λ).rk a = finrank ℤ a.1 :=
  finrank_span a.1

/-- **Modularity** of rank, as `span (a ⊓ b) = span a ∩ span b` and `span (a ⊔ b) = span a + span b`. -/
theorem rk_sup_add_rk_inf (a b : Sat Λ) :
    (slopeLattice Λ).rk (a ⊔ b) + (slopeLattice Λ).rk (a ⊓ b) = (slopeLattice Λ).rk a + (slopeLattice Λ).rk b := by
  show finrank ℝ (span ℝ ((a ⊔ b).1 : Set E)) + finrank ℝ (span ℝ ((a.1 ⊓ b.1 : Submodule ℤ E) : Set E)) = _
  rw [Sat.span_coe_sup, span_inf a.2.1 b.2.1]
  exact finrank_sup_add_finrank_inf_eq _ _

/-- `covol (a ⊔ b)·covol (a ⊓ b) ≤ covol a·covol b`. With `z` a basis of `a ⊓ b` and adapted bases `(z, x)` of `a`
and `(z, y)` of `b`, the family `(z, x, y)` spans `a ⊔ b` and has `rk (a ⊔ b)` members, so
`covol (a ⊔ b) ≤ vol (z, x, y) = vol z·vol (πx, πy) ≤ vol z·vol πx·vol πy`. -/
theorem covol_sup_mul_covol_inf_le (a b : Sat Λ) :
    covol (a ⊔ b).1 * covol (a ⊓ b).1 ≤ covol a.1 * covol b.1 := by
  obtain ⟨n, x, hxa, hn, hspa, -, -, hca⟩ :=
    exists_adapted (inf_le_left : a ⊓ b ≤ a)
  obtain ⟨m, y, hyb, hm, hspb, -, -, hcb⟩ :=
    exists_adapted (inf_le_right : a ⊓ b ≤ b)
  have hv : covol (a ⊔ b).1 ≤ vol (Sum.elim (fun i => (finBasis ℤ (a ⊓ b).1 i : E)) (Sum.elim x y)) := by
    refine covol_le ?_ ?_ ?_
    · rintro (i | j | j)
      · exact (inf_le_left.trans le_sup_left : a ⊓ b ≤ a ⊔ b) (finBasis ℤ (a ⊓ b).1 i).2
      · exact (le_sup_left : a ≤ a ⊔ b) (hxa j)
      · exact (le_sup_right : b ≤ a ⊔ b) (hyb j)
    · rw [Sat.span_coe_sup, hspa, hspb, ← span_basis (finBasis ℤ (a ⊓ b).1), Set.Sum.elim_range,
        Set.Sum.elim_range, span_union, span_union]
      exact sup_le (sup_le le_sup_left (le_sup_left.trans le_sup_right))
        (sup_le le_sup_left (le_sup_right.trans le_sup_right))
    · have h := rk_sup_add_rk_inf a b
      simp only [rk_eq] at h
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
  have hvol : vol (Sum.elim (fun i => (finBasis ℤ (a ⊓ b).1 i : E)) (Sum.elim x y)) ≤
      covol (a ⊓ b).1 * (vol (fun j => (span ℝ ((a ⊓ b).1 : Set E))ᗮ.starProjection (x j)) *
        vol fun j => (span ℝ ((a ⊓ b).1 : Set E))ᗮ.starProjection (y j)) := by
    rw [vol_sumElim, span_basis]
    refine mul_le_mul_of_nonneg_left (Eq.trans_le ?_ (vol_sumElim_le _ _)) (vol_nonneg _)
    congr 1
    funext s
    cases s <;> rfl
  rw [hca, hcb]
  nlinarith [mul_le_mul_of_nonneg_right (hv.trans hvol) (covol_pos (a ⊓ b).1).le]

/-- **Supermodularity** of degree. -/
theorem deg_add_deg_le (a b : Sat Λ) :
    (slopeLattice Λ).deg a + (slopeLattice Λ).deg b ≤ (slopeLattice Λ).deg (a ⊔ b) + (slopeLattice Λ).deg (a ⊓ b) := by
  show -Real.log (covol a.1) + -Real.log (covol b.1) ≤ -Real.log (covol (a ⊔ b).1) + -Real.log (covol (a ⊓ b).1)
  have h := Real.log_le_log (mul_pos (covol_pos _) (covol_pos _)) (covol_sup_mul_covol_inf_le a b)
  rw [Real.log_mul (covol_pos _).ne' (covol_pos _).ne', Real.log_mul (covol_pos _).ne' (covol_pos _).ne'] at h
  linarith

/-- Saturated sums of sublattices of minimal slope at least `θ` have minimal slope at least `θ`. -/
theorem supClosed : (slopeLattice Λ).SupClosed :=
  SlopeFrame.SlopeLattice.supClosed_of_modular rk_sup_add_rk_inf deg_add_deg_le

/-! ### Bost's inequality -/

omit [FiniteDimensional ℝ E] in
/-- **Hadamard** after a projection: `vol (π ∘ ψ ∘ y) ≤ ‖ψ‖ⁿ·vol y`, for `π` the projection onto `Vᗮ`. -/
theorem vol_starProjection_comp_le (V : Submodule ℝ F) (ψ : E →L[ℝ] F) {n : ℕ} (y : Fin n → E) :
    vol (fun j => Vᗮ.starProjection (ψ (y j))) ≤ ‖ψ‖ ^ n * vol y := by
  have h := vol_comp_le (Vᗮ.starProjection ∘L ψ) y
  rw [Fintype.card_fin] at h
  refine h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ n) (vol_nonneg y))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (starProjection_norm_le _))

/-- If `ψ` sends `W` into `V`, then `ψ` and `ψ` after the projection onto `Wᗮ` agree after the projection onto `Vᗮ`. -/
theorem starProjection_comp_eq {W : Submodule ℝ E} {V : Submodule ℝ F} {ψ : E →L[ℝ] F} (h : ∀ w ∈ W, ψ w ∈ V)
    (v : E) : Vᗮ.starProjection (ψ (Wᗮ.starProjection v)) = Vᗮ.starProjection (ψ v) := by
  have h1 : v - Wᗮ.starProjection v ∈ W := by
    rw [← eq_sub_of_add_eq (starProjection_add_starProjection_orthogonal (K := W) v)]
    exact starProjection_apply_mem W v
  have h2 := starProjection_orthogonal_apply_eq_zero (h _ h1)
  rw [map_sub, map_sub, sub_eq_zero] at h2
  exact h2.symm

variable {Λ' : Submodule ℤ F}

/-- The image of a saturated sublattice under `φ`: the saturation of `φ(a)` in `Λ'`. -/
def img (φ : E →L[ℝ] F) (a : Sat Λ) : Sat Λ' :=
  ⟨sat Λ' (φ '' (a.1 : Set E)), sat_isSat _⟩

/-- The preimage of a saturated sublattice under `φ`: the points of `Λ` that `φ` sends into `span b`. -/
def preimg (φ : E →L[ℝ] F) (b : Sat Λ') : Sat Λ :=
  ⟨sat Λ ((span ℝ (b.1 : Set F)).comap (φ : E →ₗ[ℝ] F)), sat_isSat _⟩

/-- **Bost's inequality** at one quotient: if `φ` sends `Λ` into `Λ'`, `‖φ‖ ≤ eʰ` and `b ≤ img φ a`, then the slope
bound for `a` at `a ⊓ preimg φ b` gives the bound for `img φ a` at `b`, less `h`. -/
theorem bost_le [DiscreteTopology Λ'] (φ : E →L[ℝ] F) (hφΛ : ∀ x ∈ Λ, φ x ∈ Λ') {h : ℝ} (hφ : ‖φ‖ ≤ Real.exp h)
    {a : Sat Λ} {b : Sat Λ'} (hb : b ≤ img φ a) {θ : ℝ}
    (ha : θ * (((slopeLattice Λ).rk a : ℝ) - (slopeLattice Λ).rk (a ⊓ preimg φ b)) ≤
      (slopeLattice Λ).deg a - (slopeLattice Λ).deg (a ⊓ preimg φ b)) :
    (θ - h) * (((slopeLattice Λ').rk (img φ a) : ℝ) - (slopeLattice Λ').rk b) ≤
      (slopeLattice Λ').deg (img φ a) - (slopeLattice Λ').deg b := by
  -- `K = a ⊓ preimg φ b` is `a ∩ φ⁻¹ b`, and `span K = span a ∩ φ⁻¹(span b)`.
  have hK1 : (a ⊓ preimg φ b).1 = a.1 ⊓ b.1.comap ((φ : E →ₗ[ℝ] F).restrictScalars ℤ) := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxa, -, hxb⟩
      have hxb : x ∈ span ℝ ((span ℝ (b.1 : Set F)).comap (φ : E →ₗ[ℝ] F) : Set E) := hxb
      rw [span_eq] at hxb
      exact ⟨hxa, b.2.2 _ (hφΛ x (a.2.1 hxa)) hxb⟩
    · rintro x ⟨hxa, hxb⟩
      refine ⟨hxa, a.2.1 hxa, ?_⟩
      show x ∈ span ℝ ((span ℝ (b.1 : Set F)).comap (φ : E →ₗ[ℝ] F) : Set E)
      rw [span_eq]
      exact subset_span (R := ℝ) (s := (b.1 : Set F)) hxb
  have hKa : a ⊓ preimg φ b ≤ a := inf_le_left
  generalize a ⊓ preimg φ b = K at hK1 hKa ha
  have hspanK := span_inf_comap (A := a.1) b.2.1 (φ : E →ₗ[ℝ] F) fun x hx => hφΛ x (a.2.1 hx)
  rw [← hK1] at hspanK
  obtain ⟨n, x, hxa, hn, hspa, hli, hdisj, hca⟩ := exists_adapted hKa
  -- `φ` sends `span K` into `span b`, the span of a basis `β` of `b`.
  have hβ := span_basis (finBasis ℤ b.1)
  have hφK (v : E) (hv : v ∈ span ℝ (K.1 : Set E)) :
      φ v ∈ span ℝ (Set.range fun i => (finBasis ℤ b.1 i : F)) := by
    rw [hβ]
    exact (hspanK.le hv).2
  -- The family `(β, φ ∘ x)`.
  have hwvol : vol (Sum.elim (fun i => (finBasis ℤ b.1 i : F)) fun j => φ (x j)) =
      covol b.1 * vol fun j => (span ℝ (Set.range fun i => (finBasis ℤ b.1 i : F)))ᗮ.starProjection (φ (x j)) :=
    vol_sumElim _ _
  -- `φ ∘ x` stays independent modulo `span b`.
  have hind : LinearIndependent ℝ fun j =>
      (span ℝ (Set.range fun i => (finBasis ℤ b.1 i : F)))ᗮ.starProjection (φ (x j)) := by
    refine hli.map (f := (((span ℝ (Set.range fun i => (finBasis ℤ b.1 i : F)))ᗮ.starProjection ∘L φ :
      E →L[ℝ] F) : E →ₗ[ℝ] F)) (disjoint_def.2 fun v hvx hv0 => disjoint_def.1 hdisj v ?_ hvx)
    rw [hspanK]
    refine ⟨(le_sup_right.trans hspa.ge) hvx, ?_⟩
    show φ v ∈ span ℝ (b.1 : Set F)
    rw [← hβ, ← orthogonal_orthogonal (K := span ℝ _), ← starProjection_apply_eq_zero_iff]
    exact hv0
  have hw : LinearIndependent ℝ (Sum.elim (fun i => (finBasis ℤ b.1 i : F)) fun j => φ (x j)) := by
    rw [← vol_pos_iff, hwvol]
    exact mul_pos (covol_pos b.1) (vol_pos_iff.2 hind)
  have hmem : ∀ s, Sum.elim (fun i => (finBasis ℤ b.1 i : F)) (fun j => φ (x j)) s ∈ (img φ a : Sat Λ').1 := by
    rintro (i | j)
    · exact hb (finBasis ℤ b.1 i).2
    · exact ⟨hφΛ _ (a.2.1 (hxa j)), subset_span ⟨x j, hxa j, rfl⟩⟩
  have hspan : span ℝ ((img φ a : Sat Λ').1 : Set F) ≤
      span ℝ (Set.range (Sum.elim (fun i => (finBasis ℤ b.1 i : F)) fun j => φ (x j))) := by
    refine (span_sat_le _).trans ?_
    rw [show span ℝ (φ '' (a.1 : Set E)) = (span ℝ (a.1 : Set E)).map (φ : E →ₗ[ℝ] F) from span_image _, hspa,
      Submodule.map_sup]
    refine sup_le ?_ ?_
    · rw [map_le_iff_le_comap, hspanK, ← hβ]
      exact inf_le_right.trans (comap_mono (span_mono (Set.range_subset_iff.2 fun i => ⟨.inl i, rfl⟩)))
    · rw [map_span]
      exact span_mono (Set.image_subset_iff.2 (Set.range_subset_iff.2 fun j => ⟨.inr j, rfl⟩))
  have hcard : Fintype.card (Fin (finrank ℤ b.1) ⊕ Fin n) = finrank ℤ (img φ a : Sat Λ').1 := by
    refine le_antisymm ?_ (finrank_le_card hspan)
    rw [← finrank_span_eq_card hw, ← finrank_span (img φ a : Sat Λ').1]
    exact finrank_mono (span_le.2 (Set.range_subset_iff.2 fun s => subset_span (hmem s)))
  -- Volumes: `covol (img φ a) ≤ covol b·eʰⁿ·vol (π_K ∘ x)`, and `covol a = covol K·vol (π_K ∘ x)`.
  have hV : 0 < vol fun j => (span ℝ (K.1 : Set E))ᗮ.starProjection (x j) := by
    have := covol_pos a.1
    rw [hca] at this
    exact pos_of_mul_pos_right this (covol_pos _).le
  have key : covol (img φ a : Sat Λ').1 ≤
      covol b.1 * (Real.exp (n * h) * vol fun j => (span ℝ (K.1 : Set E))ᗮ.starProjection (x j)) := by
    refine (covol_le hmem hspan hcard.le).trans ?_
    rw [hwvol]
    refine mul_le_mul_of_nonneg_left ?_ (covol_pos _).le
    rw [← funext fun j => starProjection_comp_eq hφK (x j)]
    refine (vol_starProjection_comp_le _ φ _).trans ?_
    rw [Real.exp_nat_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg φ) hφ n) (vol_nonneg _)
  have hlog := Real.log_le_log (covol_pos _) key
  rw [Real.log_mul (covol_pos _).ne' (mul_pos (Real.exp_pos _) hV).ne', Real.log_mul (Real.exp_pos _).ne' hV.ne',
    Real.log_exp] at hlog
  have hlogA := congrArg Real.log hca
  rw [Real.log_mul (covol_pos _).ne' hV.ne'] at hlogA
  -- Ranks: `rk (img φ a) − rk b = n = rk a − rk K`.
  have hr : ((slopeLattice Λ').rk (img φ a) : ℝ) - (slopeLattice Λ').rk b = n := by
    rw [rk_eq, rk_eq, ← hcard]
    simp
  have hr' : ((slopeLattice Λ).rk a : ℝ) - (slopeLattice Λ).rk K = n := by
    rw [rk_eq, rk_eq, ← hn]
    simp
  rw [hr'] at ha
  rw [hr]
  change θ * (n : ℝ) ≤ -Real.log (covol a.1) - -Real.log (covol K.1) at ha
  change (θ - h) * (n : ℝ) ≤ -Real.log (covol (img φ a : Sat Λ').1) - -Real.log (covol b.1)
  linarith

/-- **Bost's inequality** on images: if `φ` sends `Λ` into `Λ'` and `‖φ‖ ≤ eʰ`, then
`μ_min(img φ a) ≥ μ_min(a) − h`. -/
theorem bost [DiscreteTopology Λ'] (φ : E →L[ℝ] F) (hφΛ : ∀ x ∈ Λ, φ x ∈ Λ') {h : ℝ} (hφ : ‖φ‖ ≤ Real.exp h)
    {a : Sat Λ} {θ : ℝ} (ha : (slopeLattice Λ).SlopeGe a θ) : (slopeLattice Λ').SlopeGe (img φ a) (θ - h) :=
  fun _ hb => bost_le φ hφΛ hφ hb (ha _ inf_le_left)

end EuclidLattice

namespace EuclidLattice

/-- **Euclidean frames**: discrete subgroups `Λ ω` of Euclidean spaces, sent into one discrete subgroup `Λ'` by maps
`φ ω` of norm at most `e^{h ω}` that carry `Λ ω` into `Λ'`, form a frame (`SlopeFrame.Frame`). -/
noncomputable def frame {ι : Type} [Fintype ι] {E : ι → Type} [∀ ω, NormedAddCommGroup (E ω)]
    [∀ ω, InnerProductSpace ℝ (E ω)] [∀ ω, FiniteDimensional ℝ (E ω)] (Λ : ∀ ω, Submodule ℤ (E ω))
    [∀ ω, DiscreteTopology (Λ ω)] {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Λ' : Submodule ℤ F) [DiscreteTopology Λ'] (φ : ∀ ω, E ω →L[ℝ] F) (hφΛ : ∀ ω, ∀ x ∈ Λ ω, φ ω x ∈ Λ')
    (h : ι → ℝ) (hφ : ∀ ω, ‖φ ω‖ ≤ Real.exp (h ω)) (hrk : 0 < Module.finrank ℝ (Submodule.span ℝ (Λ' : Set F))) :
    SlopeFrame.Frame where
  ι := ι
  L ω := Sat (Λ ω)
  N ω := slopeLattice (Λ ω)
  M := Sat Λ'
  C := slopeLattice Λ'
  img ω := EuclidLattice.img (φ ω)
  h := h
  bost ω _ _ ha := EuclidLattice.bost (φ ω) (hφΛ ω) (hφ ω) ha
  supClosed := EuclidLattice.supClosed
  rk_pos := hrk

end EuclidLattice

#print axioms EuclidLattice.frame
#print axioms EuclidLattice.bost
#print axioms EuclidLattice.supClosed
#print axioms SlopeFrame.SlopeLattice.supClosed_of_modular
