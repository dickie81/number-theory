import Mathlib

/-!
# Volumes of parallelotopes

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, step 4): the linear algebra under the
covolumes of Euclidean lattices.

For a finite family `v` in a real inner product space, `vol v = √det (gram v)` is the volume of the parallelotope it
spans. It is `LinearMap.normDet` of `c ↦ Σ cᵢ vᵢ` (`LinearMap.normDet_sq_eq_det_gram`).

* `vol_comb`: `vol (v·P) = |det P|·vol v`, where `(v·P)ⱼ = Σᵢ Pᵢⱼ vᵢ`, since `gram (v·P) = Pᴴ·gram v·P`;
* `vol_sumElim`, the projection formula: `vol (u, w) = vol u·vol (π ∘ w)`, with `π` the orthogonal projection onto
  `(span u)ᗮ`. The family `(u, w)` is `(u, π ∘ w)` times a unipotent block matrix, and the Gram matrix of
  `(u, π ∘ w)` is block diagonal;
* `vol_comp_le`, Hadamard's inequality for maps: `vol (f ∘ v) ≤ ‖f‖ⁿ·vol v`, for `n` vectors. The matrix
  `‖f‖²·gram v − gram (f ∘ v)` is positive semidefinite (`Matrix.posSemidef_opNorm_smul_gram_sub_gram`), and `det`
  is monotone on positive semidefinite matrices (`det_le_det`);
* `vol_sumElim_le`, Fischer's inequality: `vol (u, w) ≤ vol u·vol w`, from the two above, as `‖π‖ ≤ 1`.

**Hadamard place by place** (`volLe_iSup`), for heights averaged over places (`PlaceLattice`). Say `f` multiplies
volumes in a subspace `W` by at most `k` (`VolLe f W k`) when `vol (f ∘ w) ≤ k·vol w` for every `dim W` vectors `w` of
`W`. If `‖f x‖ ≤ c_v‖x‖` on each of pairwise orthogonal subspaces `W_v`, then `f` multiplies volumes in their sum by at
most `∏ c_v^{dim W_v}`. Hadamard gives it on each `W_v` (`volLe_of_norm_le`). Fischer's inequality, on a basis adapted
to two orthogonal subspaces, whose volume is the product of theirs, joins them (`VolLe.sup`), and `vol_comb` passes to
any other family (`volLe_of_span`). Nothing is asked of `f` across places: Fischer absorbs the cross terms.
-/

namespace GramVolume

open Matrix Submodule Module

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The volume of the parallelotope spanned by `v`: `√det (gram v)`. -/
noncomputable def vol (v : ι → E) : ℝ :=
  √(gram ℝ v).det

/-- `vol v ≥ 0`. -/
theorem vol_nonneg (v : ι → E) : 0 ≤ vol v :=
  Real.sqrt_nonneg _

/-- `vol v² = det (gram v)`. -/
theorem vol_sq (v : ι → E) : vol v ^ 2 = (gram ℝ v).det :=
  Real.sq_sqrt (posSemidef_gram ℝ v).det_nonneg

/-- `vol v > 0` exactly when `v` is linearly independent. -/
theorem vol_pos_iff {v : ι → E} : 0 < vol v ↔ LinearIndependent ℝ v := by
  rw [vol, Real.sqrt_pos, (posSemidef_gram ℝ v).det_nonneg.lt_iff_ne',
    det_gram_ne_zero_iff_linearIndependent]

/-- The empty family has volume `1`. -/
theorem vol_of_isEmpty [IsEmpty ι] (v : ι → E) : vol v = 1 := by
  simp [vol]

/-- Reindexing keeps the volume. -/
theorem vol_comp_equiv (v : ι → E) (e : κ ≃ ι) : vol (v ∘ e) = vol v :=
  congrArg Real.sqrt (det_submatrix_equiv_self e (gram ℝ v))

/-- **Change of family**: `vol (v·P) = |det P|·vol v`. -/
theorem vol_comb (v : ι → E) (P : Matrix ι ι ℝ) : vol (fun j => ∑ i, P i j • v i) = |P.det| * vol v := by
  have h : gram ℝ (fun j => ∑ i, P i j • v i) = Pᴴ * gram ℝ v * P := by
    ext j k
    rw [mul_mul_apply]
    exact (star_dotProduct_gram_mulVec v (Pᵀ j) (Pᵀ k)).symm
  simp only [vol]
  rw [h, det_mul, det_mul, det_conjTranspose, star_trivial, mul_right_comm, ← sq,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- **The projection formula**: `vol (u, w) = vol u·vol (π ∘ w)`, with `π` the orthogonal projection onto
`(span u)ᗮ`. -/
theorem vol_sumElim [FiniteDimensional ℝ E] (u : ι → E) (w : κ → E) :
    vol (Sum.elim u w) = vol u * vol (fun k => (span ℝ (Set.range u))ᗮ.starProjection (w k)) := by
  set K := span ℝ (Set.range u)
  choose c hc using fun k => (mem_span_range_iff_exists_fun ℝ).mp (K.starProjection_apply_mem (w k))
  have h : Sum.elim u w = fun j => ∑ i, fromBlocks 1 (of fun i k => c k i) 0 1 i j •
      Sum.elim u (fun k => Kᗮ.starProjection (w k)) i := by
    ext (i | k) <;> simp [Fintype.sum_sum_type, one_apply, hc]
  have hg : gram ℝ (Sum.elim u fun k => Kᗮ.starProjection (w k)) =
      fromBlocks (gram ℝ u) 0 0 (gram ℝ fun k => Kᗮ.starProjection (w k)) := by
    ext (i | k) (j | l)
    · rfl
    · exact inner_right_of_mem_orthogonal (subset_span (Set.mem_range_self i)) (starProjection_apply_mem _ _)
    · exact inner_left_of_mem_orthogonal (subset_span (Set.mem_range_self j)) (starProjection_apply_mem _ _)
    · rfl
  rw [h, vol_comb, det_fromBlocks_zero₂₁, det_one, det_one, mul_one, abs_one, one_mul]
  simp only [vol]
  rw [hg, det_fromBlocks_zero₂₁, Real.sqrt_mul (posSemidef_gram ℝ u).det_nonneg]

/-- `det (1 + Y) ≥ 1` for a positive semidefinite real matrix `Y`: it is `∏ (1 + λᵢ)`, over the eigenvalues
`λᵢ ≥ 0` of `Y`. -/
theorem one_le_det_one_add {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef) : 1 ≤ (1 + Y).det := by
  rw [hY.1.spectral_theorem, ← map_one (Unitary.conjStarAlgAut ℝ _ hY.1.eigenvectorUnitary),
    ← map_add, det_map', ← diagonal_one, diagonal_add, det_diagonal]
  exact Finset.one_le_prod₀ fun i _ => le_add_of_nonneg_right (hY.eigenvalues_nonneg i)

open scoped MatrixOrder in
/-- **`det` is monotone** on positive semidefinite real matrices: if `A` and `B − A` are positive semidefinite, then
`det A ≤ det B`. For invertible `A`, write `B − A = Dᴴ·D`; then `det B = det A·det (1 + D·A⁻¹·Dᴴ)`. -/
theorem det_le_det {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) : A.det ≤ B.det := by
  obtain h | h := hA.det_nonneg.eq_or_lt
  · exact h ▸ (sub_add_cancel B A ▸ hAB.add hA).det_nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hAB.nonneg
  rw [← add_sub_cancel A B, hD, star_eq_conjTranspose, det_add_mul _ _ h.ne'.isUnit]
  exact le_mul_of_one_le_right h.le (one_le_det_one_add (hA.inv.mul_mul_conjTranspose_same D))

/-- **Hadamard's inequality for maps**: `vol (f ∘ v) ≤ ‖f‖ⁿ·vol v`. -/
theorem vol_comp_le (f : E →L[ℝ] F) (v : ι → E) : vol (f ∘ v) ≤ ‖f‖ ^ Fintype.card ι * vol v := by
  have h := det_le_det (posSemidef_gram ℝ (f ∘ v)) (posSemidef_opNorm_smul_gram_sub_gram v f)
  rw [det_smul, pow_right_comm, ← vol_sq, ← vol_sq, ← mul_pow] at h
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (by positivity) (vol_nonneg v)) h

/-- **Projections do not increase volume**: `vol (π ∘ w) ≤ vol w`, for `π` an orthogonal projection. -/
theorem vol_starProjection_le (K : Submodule ℝ E) [K.HasOrthogonalProjection] (w : ι → E) :
    vol (fun i => K.starProjection (w i)) ≤ vol w :=
  (vol_comp_le K.starProjection w).trans
    (mul_le_of_le_one_left (vol_nonneg w) (pow_le_one₀ (norm_nonneg _) (starProjection_norm_le _)))

/-- **Fischer's inequality**: `vol (u, w) ≤ vol u·vol w`. -/
theorem vol_sumElim_le [FiniteDimensional ℝ E] (u : ι → E) (w : κ → E) : vol (Sum.elim u w) ≤ vol u * vol w := by
  rw [vol_sumElim]
  exact mul_le_mul_of_nonneg_left (vol_starProjection_le _ w) (vol_nonneg u)

/-! ### Hadamard place by place -/

/-- `f` multiplies volumes in `W` by at most `k`: `vol (f ∘ w) ≤ k·vol w` for every `dim W` vectors `w` of `W`. -/
def VolLe (f : E →L[ℝ] F) (W : Submodule ℝ E) (k : ℝ) : Prop :=
  ∀ (n : ℕ) (w : Fin n → E), n = finrank ℝ W → (∀ i, w i ∈ W) → vol (f ∘ w) ≤ k * vol w

/-- `VolLe` holds once it holds for one family of `dim W` vectors whose span contains `W`, since every other family
is a combination of it (`vol_comb`). -/
theorem volLe_of_span {f : E →L[ℝ] F} {W : Submodule ℝ E} {k : ℝ} (z : ι → E)
    (hc : Fintype.card ι = finrank ℝ W) (hz : W ≤ span ℝ (Set.range z)) (h : vol (f ∘ z) ≤ k * vol z) :
    VolLe f W k := by
  intro n w hn hw
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq (hc.trans hn.symm)
  choose c hc' using fun j => (mem_span_range_iff_exists_fun ℝ).1 (hz (hw (e j)))
  have h1 : w ∘ e = fun j => ∑ i, Matrix.of (fun i j => c j i) i j • z i := funext fun j => (hc' j).symm
  have h2 : (f ∘ w) ∘ e = fun j => ∑ i, Matrix.of (fun i j => c j i) i j • (f ∘ z) i := funext fun j => by
    simp [← hc' j, map_sum, map_smul]
  rw [← vol_comp_equiv w e, ← vol_comp_equiv (f ∘ w) e, h1, h2, vol_comb, vol_comb, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- **Hadamard on a subspace**: if `‖f x‖ ≤ c‖x‖` on `W`, then `f` multiplies volumes in `W` by at most `c^dim W`. -/
theorem volLe_of_norm_le {f : E →L[ℝ] F} {W : Submodule ℝ E} [W.HasOrthogonalProjection] {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ x ∈ W, ‖f x‖ ≤ c * ‖x‖) : VolLe f W (c ^ finrank ℝ W) := by
  rintro n w rfl hw
  have h := vol_comp_le (f ∘L W.starProjection) w
  rw [Fintype.card_fin] at h
  have hw' : (f ∘L W.starProjection) ∘ w = f ∘ w := funext fun i => by
    simp [starProjection_eq_self_iff.2 (hw i)]
  rw [hw'] at h
  refine h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ _) (vol_nonneg w))
  exact ContinuousLinearMap.opNorm_le_bound _ hc fun x =>
    (hf _ (starProjection_apply_mem W x)).trans (mul_le_mul_of_nonneg_left (norm_starProjection_apply_le W x) hc)

/-- Orthogonal subspaces: `dim (W₁ ⊔ W₂) = dim W₁ + dim W₂`. -/
theorem finrank_sup_of_isOrtho [FiniteDimensional ℝ E] {W₁ W₂ : Submodule ℝ E} (h : W₁ ⟂ W₂) :
    finrank ℝ ↥(W₁ ⊔ W₂) = finrank ℝ W₁ + finrank ℝ W₂ := by
  have := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  rwa [h.disjoint.eq_bot, finrank_bot, add_zero] at this

/-- **Fischer's inequality** on orthogonal subspaces: if `f` multiplies volumes in `W₁` by at most `k₁` and in `W₂` by
at most `k₂`, and `W₁ ⟂ W₂`, then it multiplies volumes in `W₁ ⊔ W₂` by at most `k₁k₂`. Take bases `z₁` of `W₁` and
`z₂` of `W₂`: `vol (f z₁, f z₂) ≤ vol (f z₁)·vol (f z₂)`, while `vol (z₁, z₂) = vol z₁·vol z₂`. -/
theorem VolLe.sup [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {f : E →L[ℝ] F} {W₁ W₂ : Submodule ℝ E}
    {k₁ k₂ : ℝ} (h₁ : VolLe f W₁ k₁) (h₂ : VolLe f W₂ k₂) (hW : W₁ ⟂ W₂) : VolLe f (W₁ ⊔ W₂) (k₁ * k₂) := by
  have hspan (W : Submodule ℝ E) : span ℝ (Set.range fun i => (finBasis ℝ W i : E)) = W := by
    have h := congrArg (map W.subtype) (finBasis ℝ W).span_eq
    rwa [map_span, Submodule.map_top, range_subtype, ← Set.range_comp] at h
  let z₁ i := (finBasis ℝ W₁ i : E)
  let z₂ i := (finBasis ℝ W₂ i : E)
  have hz₁ i : z₁ i ∈ W₁ := (finBasis ℝ W₁ i).2
  have hz₂ i : z₂ i ∈ W₂ := (finBasis ℝ W₂ i).2
  refine volLe_of_span (Sum.elim z₁ z₂) (by simp [finrank_sup_of_isOrtho hW]) ?_ ?_
  · rw [Set.Sum.elim_range, span_union, hspan, hspan]
  · have h0 : vol (Sum.elim z₁ z₂) = vol z₁ * vol z₂ := by
      rw [vol_sumElim]
      congr 2
      exact funext fun i => starProjection_eq_self_iff.2
        (orthogonal_le (span_le.2 (Set.range_subset_iff.2 hz₁)) (hW.symm (hz₂ i)))
    rw [h0, Sum.comp_elim]
    have := h₁ _ z₁ rfl hz₁
    have := h₂ _ z₂ rfl hz₂
    have := vol_nonneg (f ∘ z₁)
    have := vol_nonneg (f ∘ z₂)
    nlinarith [vol_sumElim_le (f ∘ z₁) (f ∘ z₂)]

/-- **Hadamard place by place**: if `‖f x‖ ≤ c v·‖x‖` on each of pairwise orthogonal subspaces `W v`, then `f`
multiplies volumes in their sum by at most `∏ c v ^ dim W v`. -/
theorem volLe_iSup [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {P : Type*} [Fintype P] {f : E →L[ℝ] F}
    {W : P → Submodule ℝ E} (hW : Pairwise fun v w => W v ⟂ W w) {c : P → ℝ} (hc : ∀ v, 0 ≤ c v)
    (hf : ∀ v, ∀ x ∈ W v, ‖f x‖ ≤ c v * ‖x‖) : VolLe f (⨆ v, W v) (∏ v, c v ^ finrank ℝ (W v)) := by
  classical
  rw [← Finset.sup_univ_eq_iSup]
  generalize (Finset.univ : Finset P) = s
  induction s using Finset.induction_on with
  | empty =>
    rintro n w rfl _
    have : IsEmpty (Fin (finrank ℝ ↥((∅ : Finset P).sup W))) := by
      rw [Finset.sup_empty, finrank_bot]
      infer_instance
    simp [vol_of_isEmpty]
  | insert v s hv ih =>
    rw [Finset.sup_insert, Finset.prod_insert hv]
    refine (volLe_of_norm_le (hc v) (hf v)).sup ih ?_
    rw [Finset.sup_eq_iSup]
    exact isOrtho_iSup_right.2 fun w => isOrtho_iSup_right.2 fun hw => hW (ne_of_mem_of_not_mem hw hv).symm

/-- The dimension of a sum of pairwise orthogonal subspaces is the sum of their dimensions. -/
theorem finrank_iSup_of_isOrtho [FiniteDimensional ℝ E] {P : Type*} [Fintype P] {W : P → Submodule ℝ E}
    (hW : Pairwise fun v w => W v ⟂ W w) : finrank ℝ ↥(⨆ v, W v) = ∑ v, finrank ℝ (W v) := by
  classical
  rw [← Finset.sup_univ_eq_iSup]
  generalize (Finset.univ : Finset P) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert v s hv ih =>
    rw [Finset.sup_insert, Finset.sum_insert hv, finrank_sup_of_isOrtho, ih]
    rw [Finset.sup_eq_iSup]
    exact isOrtho_iSup_right.2 fun w => isOrtho_iSup_right.2 fun hw => hW (ne_of_mem_of_not_mem hw hv).symm

end GramVolume

#print axioms GramVolume.vol_comb
#print axioms GramVolume.vol_sumElim
#print axioms GramVolume.vol_comp_le
#print axioms GramVolume.vol_sumElim_le
#print axioms GramVolume.volLe_iSup
