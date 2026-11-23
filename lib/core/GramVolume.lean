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
-/

namespace GramVolume

open Matrix Submodule

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

/-- **Fischer's inequality**: `vol (u, w) ≤ vol u·vol w`. -/
theorem vol_sumElim_le [FiniteDimensional ℝ E] (u : ι → E) (w : κ → E) : vol (Sum.elim u w) ≤ vol u * vol w := by
  rw [vol_sumElim]
  refine mul_le_mul_of_nonneg_left ((vol_comp_le (span ℝ (Set.range u))ᗮ.starProjection w).trans ?_)
    (vol_nonneg u)
  exact mul_le_of_le_one_left (vol_nonneg w) (pow_le_one₀ (norm_nonneg _) (starProjection_norm_le _))

end GramVolume

#print axioms GramVolume.vol_comb
#print axioms GramVolume.vol_sumElim
#print axioms GramVolume.vol_comp_le
#print axioms GramVolume.vol_sumElim_le
