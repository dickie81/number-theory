import TraceSlope

/-!
# The maximal slope from an integral twisted pairing

For the range (R′) of the sharp frontier (`ZetaBalance.SharpMuMax`), route (P): an upper bound for the maximal slope
of a hermitian `O_K`-lattice (`KLattice`, `K` totally complex) whose metrics come from one weighted form, through one
automorphism of `K`. No reduction theory, no Galois descent and no root-discriminant bound enter.

**Theorem A** (`slopeLe_of_twPair`). Let the metrics be `G_v = σ_v(E)ᴴ W σ_v(E)` for a matrix `E ∈ K^{R×ι}` and
`W = diag(w)`, `w_r ∈ ℚ_{>0}`; let `c ∈ Aut(K)` be complex conjugation at one place `v₀`
(`σ_{v₀} ∘ c = conj ∘ σ_{v₀}`), and let

  `h_c(x, y) = Σ_r w_r·c((Ex)_r)·(Ey)_r ∈ K`  (`twPair`, `c`-semilinear in `x`, linear in `y`).

If `D ≥ 1` and `D·h_c(x, y) ∈ O_K` for `x, y ∈ M`, then every member `a` of the slope lattice has
`2·deg a + c_K·rk a ≤ log D·rk a`, `c_K = −log 2 + log|d_K|/[K:ℚ]` (the archive's units, as in `TraceSlope`). For a
normal `K` such a `c` exists (`exists_conj_ringEquiv`), and it is complex conjugation on every CM subfield
(`conj_comp_of_isConj`).

**The route.**
* *Transport* (`exists_subKLattice`). A member `a` of positive rank is a full hermitian lattice `Y` in a basis `Pm`
  of its `K`-span: `M_Y = Pm⁻¹{x ∈ M : ψ(x) ∈ a}`, with the metrics `σ_v(Pm)ᴴ G_v σ_v(Pm)`. The map of `Pm` (`hom`)
  is an isometry of `ψ_Y(M_Y)` onto `a` (`inner_ψ_map`), so `deg a = deg Y` (`EuclidLattice.covol_sq_eq`) and
  `rk a = [K:ℚ]·s`. In `Y`'s coordinates the data are `E·Pm` and `h_{c,E}(Pm·, Pm·)` (`twPair_mul`).
* *Pseudo-basis* (`exists_pseudo_pi_int`). `M_Y = P·∏_i I_i` with `P` invertible and `I_i` nonzero integral ideals,
  so `μ_arch(Y) = −(Σ_v log g_v + Σ_i log N(I_i))/(n_∞·s)`, `g_v = det(σ_v(F)ᴴ W σ_v(F))`, `F = E·Pm·P`
  (`slopeArch_pseudo`).
* *Claim 1* (`abs_norm_det_twGram_le`). For the twisted Gram determinant `δ = det(c(F)ᵀ W F)`:
  `σ_v(δ) = det(τ_v(F)ᴴ W σ_v(F))` with `τ_v = conj ∘ σ_v ∘ c` (`map_det_twGram`), an embedding of the place `π(v)`
  of `σ_v ∘ c`, and `π` permutes the complex places (`exists_plPerm`). Cauchy–Schwarz for Gram determinants
  (`normSq_det_weighted_le`, from the monotonicity of `det` on positive semidefinite matrices, `det_le_det_C`)
  gives `|σ_v(δ)|² ≤ g_{π(v)}·g_v`; as `|N(δ)| = ∏_v |σ_v(δ)|²` (`prod_normSq_embedding`), `|N(δ)| ≤ (∏_v g_v)²`.
  At `v₀`, `σ_{v₀}(δ) = g_{v₀} > 0`, so `δ ≠ 0`.
* *Claim 2* (`one_le_norm_det_mul_absNorm`). For `H = D·c(F)ᵀ W F` the entries `c(b)·b′·H_ij = D·h_c(P b e_i,
  P b′ e_j)`, `b ∈ I_i`, `b′ ∈ I_j`, are integral, so `det H·∏_i c(b_i)·∏_j b′_j = det(diag(c b)·H·diag(b′))` is
  integral (`det_mem_one`). These products span `c(∏_i I_i)·∏_j I_j` (`prod_ideals_induction`), so the fractional
  ideal `(det H)·c(∏_i I_i)·∏_j I_j` is integral and nonzero, of norm `|N(det H)|·∏_i N(I_i)² ≥ 1`
  (`N(c(I)) = N(I)`, `absNorm_map_ringEquiv`); and `N(det H) = D^{[K:ℚ]·s}·N(δ)`.
* Together, `1 ≤ D^{[K:ℚ]·s}·(∏_v g_v)²·∏_i N(I_i)²`; with `[K:ℚ] = 2n_∞` this is `μ_arch(Y) ≤ log D`
  (`slopeArch_le_of_twPair`). The discriminant of `K` cancels exactly.

*Why one automorphism suffices.* `h_c` is hermitian only at the places where `c` is complex conjugation, but at every
place the twisted Gram determinant is bounded by the geometric mean of the true Gram determinants at `v` and at
`π(v)`, and `π` is a permutation.
-/

namespace KLattice

open NumberField HermitianLattice Matrix Module

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexOrder MatrixOrder Classical nonZeroDivisors

/-! ### Determinants of positive semidefinite matrices -/

/-- `det(1 + Y) ≥ 1` for a positive semidefinite `Y` (in the order of `ℂ`): its eigenvalues are `1 + λ_i ≥ 1`. -/
theorem one_le_det_one_add_C {s : Type} [Fintype s] [DecidableEq s] {Y : Matrix s s ℂ} (hY : Y.PosSemidef) :
    1 ≤ (1 + Y).det := by
  rw [hY.1.spectral_theorem, ← map_one (Unitary.conjStarAlgAut ℂ _ hY.1.eigenvectorUnitary),
    ← map_add, det_map', ← diagonal_one, diagonal_add, det_diagonal]
  exact Finset.one_le_prod₀ fun i _ => le_add_of_nonneg_right (by
    simpa using (RCLike.ofReal_nonneg (K := ℂ)).2 (hY.eigenvalues_nonneg i))

/-- **`det` is monotone on positive semidefinite complex matrices**, in the order of `ℂ`: for `A ≥ 0` and
`B − A = Dᴴ D`, `det B = det A·det(1 + A⁻¹DᴴD)` when `A` is invertible (`det_add_mul`), and `det B ≥ 0` otherwise. -/
theorem det_le_det_C {s : Type} [Fintype s] [DecidableEq s] {A B : Matrix s s ℂ} (hA : A.PosSemidef)
    (hAB : (B - A).PosSemidef) : A.det ≤ B.det := by
  obtain h | h := hA.det_nonneg.eq_or_lt
  · exact h ▸ (sub_add_cancel B A ▸ hAB.add hA).det_nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hAB.nonneg
  rw [← add_sub_cancel A B, hD, star_eq_conjTranspose, det_add_mul _ _ h.ne'.isUnit]
  exact le_mul_of_one_le_right h.le (one_le_det_one_add_C (hA.inv.mul_mul_conjTranspose_same D))

/-- **Cauchy–Schwarz for Gram determinants**: `|det(UᴴV)|² ≤ det(UᴴU)·det(VᴴV)`, in the order of `ℂ`. If
`A = UᴴU` is singular, so is `UᴴV`; otherwise `VᴴV − (UᴴV)ᴴA⁻¹(UᴴV) = (V − UA⁻¹UᴴV)ᴴ(V − UA⁻¹UᴴV) ≥ 0`, and
`det_le_det_C`. -/
theorem normSq_det_le_C {R s : Type} [Fintype R] [Fintype s] [DecidableEq s] (U V : Matrix R s ℂ) :
    ((Complex.normSq (Uᴴ * V).det : ℝ) : ℂ) ≤ (Uᴴ * U).det * (Vᴴ * V).det := by
  set A := Uᴴ * U
  set B := Uᴴ * V
  have hA : A.PosSemidef := posSemidef_conjTranspose_mul_self U
  have hBB : (Bᴴ).det = starRingEnd ℂ B.det := by rw [det_conjTranspose]; rfl
  by_cases h0 : A.det = 0
  · obtain ⟨z, hz, hAz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hUz : U *ᵥ z = 0 := by
      have hmem : z ∈ LinearMap.ker (Uᴴ * U).mulVecLin := by simpa [A] using hAz
      rw [ker_mulVecLin_conjTranspose_mul_self] at hmem
      simpa using hmem
    have hB0 : (Bᴴ).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨z, hz, ?_⟩
      simp only [B, conjTranspose_mul, conjTranspose_conjTranspose, ← mulVec_mulVec, hUz, mulVec_zero]
    rw [hBB, map_eq_zero] at hB0
    rw [hB0, h0, zero_mul]
    simp
  · have hApd : A.PosDef := hA.posDef_iff_isUnit.2 (isUnit_iff_isUnit_det _ |>.2 (isUnit_iff_ne_zero.2 h0))
    have hP : (Bᴴ * A⁻¹ * B).PosSemidef := hApd.inv.posSemidef.conjTranspose_mul_mul_same B
    have hdiff : ((Vᴴ * V) - Bᴴ * A⁻¹ * B).PosSemidef := by
      have e : (Vᴴ * V) - Bᴴ * A⁻¹ * B = (V - U * (A⁻¹ * B))ᴴ * (V - U * (A⁻¹ * B)) := by
        have hAi : A⁻¹ * A = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h0)
        have hAH : A⁻¹ᴴ = A⁻¹ := (hApd.inv.isHermitian).eq
        have hX : (U * (A⁻¹ * B))ᴴ = Bᴴ * A⁻¹ * Uᴴ := by
          rw [conjTranspose_mul, conjTranspose_mul, hAH, Matrix.mul_assoc]
        have hBH : Bᴴ = Vᴴ * U := by simp [B]
        rw [conjTranspose_sub, hX, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
        have e1 : Bᴴ * A⁻¹ * Uᴴ * V = Bᴴ * A⁻¹ * B := by simp only [B, Matrix.mul_assoc]
        have e2 : Vᴴ * (U * (A⁻¹ * B)) = Bᴴ * A⁻¹ * B := by rw [hBH]; simp only [Matrix.mul_assoc]
        have e3 : Bᴴ * A⁻¹ * Uᴴ * (U * (A⁻¹ * B)) = Bᴴ * A⁻¹ * B := by
          calc Bᴴ * A⁻¹ * Uᴴ * (U * (A⁻¹ * B)) = Bᴴ * (A⁻¹ * (Uᴴ * U)) * (A⁻¹ * B) := by
                simp only [Matrix.mul_assoc]
            _ = Bᴴ * A⁻¹ * B := by
                rw [show Uᴴ * U = A from rfl, hAi, Matrix.mul_one, Matrix.mul_assoc]
        rw [e1, e2, e3]
        abel
      rw [e]
      exact posSemidef_conjTranspose_mul_self _
    have hle := det_le_det_C hP (by simpa using hdiff)
    rw [det_mul, det_mul, hBB, det_nonsing_inv, Ring.inverse_eq_inv'] at hle
    have hApos : 0 < A.det := hApd.det_pos
    have e2 : starRingEnd ℂ B.det * (A.det)⁻¹ * B.det = ((Complex.normSq B.det : ℝ) : ℂ) * (A.det)⁻¹ := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [e2] at hle
    have := mul_le_mul_of_nonneg_left hle hApos.le
    rwa [mul_comm (A.det) (((Complex.normSq B.det : ℝ) : ℂ) * (A.det)⁻¹), mul_assoc,
      inv_mul_cancel₀ hApos.ne', mul_one] at this

/-- (TS2) **Cauchy–Schwarz for Gram determinants, weighted**: `|det(Uᴴ W V)|² ≤ det(Uᴴ W U)·det(Vᴴ W V)` for a
nonnegative diagonal `W`: `normSq_det_le_C` for `W^{1/2}U` and `W^{1/2}V`. -/
theorem normSq_det_weighted_le {R s : Type} [Fintype R] [DecidableEq R] [Fintype s] [DecidableEq s] (w : R → ℝ)
    (hw : ∀ r, 0 ≤ w r) (U V : Matrix R s ℂ) :
    Complex.normSq (Uᴴ * diagonal (fun r => (w r : ℂ)) * V).det ≤
      (Uᴴ * diagonal (fun r => (w r : ℂ)) * U).det.re * (Vᴴ * diagonal (fun r => (w r : ℂ)) * V).det.re := by
  set S : Matrix R R ℂ := diagonal fun r => ((Real.sqrt (w r) : ℝ) : ℂ)
  have hS (X Y : Matrix R s ℂ) : (S * X)ᴴ * (S * Y) = Xᴴ * diagonal (fun r => (w r : ℂ)) * Y := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Sᴴ, diagonal_conjTranspose, diagonal_mul_diagonal,
      Matrix.mul_assoc]
    congr 3
    funext r
    rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hw r)]
  have h := normSq_det_le_C (S * U) (S * V)
  rw [hS, hS, hS] at h
  have hU := (posSemidef_conjTranspose_mul_self (S * U)).det_nonneg
  have hV := (posSemidef_conjTranspose_mul_self (S * V)).det_nonneg
  rw [hS] at hU hV
  have h1 := (Complex.le_def.1 h).1
  rw [Complex.ofReal_re, Complex.mul_re, ← (Complex.le_def.1 hU).2, Complex.zero_im, zero_mul, sub_zero] at h1
  exact h1

variable {K : Type} [Field K] [NumberField K]

/-! ### An automorphism, the places, and complex conjugation -/

/-- (TS3) **An automorphism permutes the complex places**: `π(v)` is the place of `σ_v ∘ c`, whose embedding is
`σ_v ∘ c` or its conjugate (`InfinitePlace.embedding_mk_eq`); `v ↦ π(v)` is injective (`InfinitePlace.mk_eq_iff`). -/
theorem exists_plPerm (c : K ≃+* K) : ∃ π : Pl K ≃ Pl K, ∀ v : Pl K,
    (π v).1.embedding = v.1.embedding.comp (c : K →+* K) ∨
      (π v).1.embedding = ComplexEmbedding.conjugate (v.1.embedding.comp (c : K →+* K)) := by
  have hc (v : Pl K) : (InfinitePlace.mk (v.1.embedding.comp (c : K →+* K))).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_comp_iff]
    exact InfinitePlace.isComplex_iff.1 v.2
  let f : Pl K → Pl K := fun v => ⟨_, hc v⟩
  have hf : Function.Injective f := by
    intro u v huv
    have h := congrArg Subtype.val huv
    simp only [f] at h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · have : u.1.embedding = v.1.embedding := by
        ext x
        simpa using congrArg (fun φ : K →+* ℂ => φ (c.symm x)) h
      exact Subtype.ext (by rw [← InfinitePlace.mk_embedding u.1, this, InfinitePlace.mk_embedding])
    · have : ComplexEmbedding.conjugate u.1.embedding = v.1.embedding := by
        ext x
        simpa using congrArg (fun φ : K →+* ℂ => φ (c.symm x)) h
      refine Subtype.ext ?_
      rw [← InfinitePlace.mk_embedding u.1, ← InfinitePlace.mk_embedding v.1, ← this, InfinitePlace.mk_conjugate_eq]
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun v => ?_⟩
  exact InfinitePlace.embedding_mk_eq _

/-- (TS4) **Complex conjugation at one place is an automorphism** of a normal `K`
(`ComplexEmbedding.exists_comp_symm_eq_of_comp_eq` over `ℚ`). -/
theorem exists_conj_ringEquiv [IsTotallyComplex K] [Normal ℚ K] :
    ∃ c : K ≃+* K, ∃ v₀ : Pl K, ∀ z, v₀.1.embedding (c z) = starRingEnd ℂ (v₀.1.embedding z) := by
  have : IsGalois ℚ K := IsGalois.mk
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  let v₀ : Pl K := ⟨w, IsTotallyComplex.isComplex w⟩
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) v₀.1.embedding
    (ComplexEmbedding.conjugate v₀.1.embedding) (RingHom.ext_rat _ _)
  refine ⟨σ.symm.toRingEquiv, v₀, fun z => ?_⟩
  have := congrArg (fun f : K →+* ℂ => f z) hσ
  simpa [ComplexEmbedding.conjugate_coe_eq] using this

omit [NumberField K] in
/-- (TS5) **It is complex conjugation on every CM subfield**: `c ∘ τ = τ ∘ conj_E` for every `τ : E → K`
(`IsCMField.isConj_complexConj` at `σ_{v₀} ∘ τ`, and `σ_{v₀}` is injective). -/
theorem conj_comp_of_isConj {E : Type} [Field E] [NumberField E] [IsCMField E] (c : K ≃+* K) (v₀ : Pl K)
    (hv : ∀ z, v₀.1.embedding (c z) = starRingEnd ℂ (v₀.1.embedding z)) (τ : E →+* K) (z : E) :
    c (τ z) = τ (IsCMField.complexConj E z) := by
  apply v₀.1.embedding.injective
  rw [hv]
  have h := (NumberField.IsCMField.isConj_complexConj (K := E) (v₀.1.embedding.comp τ)).eq z
  rw [RingHom.comp_apply, RingHom.comp_apply] at h
  exact h.symm

/-! ### The twisted pairing and Claim 1 -/

variable {ι R : Type} [Fintype ι] [Fintype R]

/-- **The `c`-twisted weighted pairing** `h_c(x, y) = Σ_r w_r·c((Ex)_r)·(Ey)_r`, a `K`-valued form, `c`-semilinear
in `x`. At every embedding `σ`, `σ(h_c(x, y)) = Σ_r w_r·conj(τ(Ex)_r)·σ(Ey)_r` with `τ = conj ∘ σ ∘ c`. -/
noncomputable def twPair (c : K →+* K) (w : R → ℚ) (E : Matrix R ι K) (x y : ι → K) : K :=
  ∑ r, (w r : K) * c ((E *ᵥ x) r) * (E *ᵥ y) r

/-- **A weighted Gram product in coordinates**: `(A·diag(d)·B)_{ij} = Σ_r A_{ir}·d_r·B_{rj}`. -/
theorem mul_diagonal_mul_apply [DecidableEq R] {α s t : Type} [CommSemiring α] (A : Matrix s R α) (d : R → α)
    (B : Matrix R t α) (i : s) (j : t) : (A * diagonal d * B) i j = ∑ r, A i r * d r * B r j := by
  rw [mul_apply]
  simp only [mul_diagonal]

omit [NumberField K] in
/-- **A change of coordinates** `x = P y`: `h_{c,E}(Px, Py) = h_{c,EP}(x, y)`. -/
theorem twPair_mul {κ : Type} [Fintype κ] (c : K →+* K) (w : R → ℚ) (E : Matrix R ι K) (P : Matrix ι κ K)
    (x y : κ → K) : twPair c w (E * P) x y = twPair c w E (P *ᵥ x) (P *ᵥ y) := by
  simp only [twPair, mulVec_mulVec]

omit [NumberField K] in
/-- **The twisted pairing on coordinate vectors**: `h_c(b e_i, b' e_j) = c(b)·b'·(c(E)ᵀ W E)_{ij}`. -/
theorem twPair_single [DecidableEq ι] [DecidableEq R] (c : K →+* K) (w : R → ℚ) (E : Matrix R ι K) (i j : ι)
    (b b' : K) : twPair c w E (Pi.single i b) (Pi.single j b') =
      c b * b' * ((E.map c)ᵀ * diagonal (fun r => (w r : K)) * E) i j := by
  simp only [twPair, mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    mul_diagonal_mul_apply, transpose_apply, map_apply, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

omit [NumberField K] in
/-- **The Gram determinant at the conjugate embedding** has the same real part: `σ̄(F)ᴴ W σ̄(F)` is the conjugate of
`σ(F)ᴴ W σ(F)`, for a real `W`. -/
theorem re_det_gram_conjugate [DecidableEq R] {s : Type} [Fintype s] [DecidableEq s] (w : R → ℚ) (F : Matrix R s K)
    (σ : K →+* ℂ) :
    ((F.map (ComplexEmbedding.conjugate σ))ᴴ * diagonal (fun r => (w r : ℂ)) *
      F.map (ComplexEmbedding.conjugate σ)).det.re =
      ((F.map σ)ᴴ * diagonal (fun r => (w r : ℂ)) * F.map σ).det.re := by
  have h : (F.map (ComplexEmbedding.conjugate σ))ᴴ * diagonal (fun r => (w r : ℂ)) *
      F.map (ComplexEmbedding.conjugate σ) =
      ((F.map σ)ᴴ * diagonal (fun r => (w r : ℂ)) * F.map σ).map (starRingEnd ℂ) := by
    ext i j
    simp only [map_apply, mul_diagonal_mul_apply, conjTranspose_apply, ComplexEmbedding.conjugate_coe_eq, map_sum,
      map_mul, map_ratCast, RCLike.star_def]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_re]

omit [NumberField K] in
/-- **A twisted Gram determinant at an embedding**: `σ(det(c(F)ᵀ W F)) = det(τ(F)ᴴ W σ(F))`, `τ = conj ∘ σ ∘ c`. -/
theorem map_det_twGram [DecidableEq R] {s : Type} [Fintype s] [DecidableEq s] (c : K →+* K) (w : R → ℚ)
    (F : Matrix R s K) (σ : K →+* ℂ) :
    σ ((F.map c)ᵀ * diagonal (fun r => (w r : K)) * F).det =
      ((F.map (ComplexEmbedding.conjugate (σ.comp c)))ᴴ * diagonal (fun r => (w r : ℂ)) * F.map σ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, map_apply, mul_diagonal_mul_apply, transpose_apply, conjTranspose_apply,
    ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, map_sum, map_mul, map_ratCast, RCLike.star_def,
    Complex.conj_conj]

variable [IsTotallyComplex K]

/-- (TS7) **Claim 1, the norm of the twisted Gram determinant**: `|N(det(c(F)ᵀ W F))| ≤ (∏_v det(σ_v(F)ᴴ W σ_v(F)))²`.
At `v`, `σ_v(det) = det(τ(F)ᴴ W σ_v(F))`, `τ = conj ∘ σ_v ∘ c` of place `π(v)` (`exists_plPerm`); (TS2) bounds its
square by the Gram determinants at `π(v)` and `v`; `π` is a permutation; `|N| = ∏_v |σ_v|²`
(`prod_normSq_embedding`). -/
theorem abs_norm_det_twGram_le [DecidableEq R] {s : Type} [Fintype s] [DecidableEq s] (c : K ≃+* K) (w : R → ℚ)
    (hw : ∀ r, 0 ≤ w r) (F : Matrix R s K) :
    |((Algebra.norm ℚ ((F.map c)ᵀ * diagonal (fun r => (w r : K)) * F).det : ℚ) : ℝ)| ≤
      (∏ v : Pl K, ((F.map v.1.embedding)ᴴ * diagonal (fun r => (w r : ℂ)) * F.map v.1.embedding).det.re) ^ 2 := by
  set g : (K →+* ℂ) → ℝ := fun σ => ((F.map σ)ᴴ * diagonal (fun r => (w r : ℂ)) * F.map σ).det.re with hg
  have hW : (fun r => (w r : ℂ)) = fun r => (((w r : ℚ) : ℝ) : ℂ) := funext fun r => (Complex.ofReal_ratCast _).symm
  have hw' : ∀ r, (0 : ℝ) ≤ (w r : ℝ) := fun r => Rat.cast_nonneg.2 (hw r)
  have hg0 (σ : K →+* ℂ) : 0 ≤ g σ := by
    have h : (diagonal fun r => (w r : ℂ)).PosSemidef :=
      PosSemidef.diagonal fun r => by
        rw [Pi.zero_apply, ← Complex.ofReal_ratCast]
        exact Complex.zero_le_real.2 (hw' r)
    exact (Complex.le_def.1 (h.conjTranspose_mul_mul_same (F.map σ)).det_nonneg).1
  obtain ⟨π, hπ⟩ := exists_plPerm c
  have hv (v : Pl K) : Complex.normSq (v.1.embedding ((F.map c)ᵀ * diagonal (fun r => (w r : K)) * F).det) ≤
      g (π v).1.embedding * g v.1.embedding := by
    have e := map_det_twGram (c : K →+* K) w F v.1.embedding
    rw [RingEquiv.coe_toRingHom] at e
    rw [e]
    have h := normSq_det_weighted_le (fun r => (w r : ℝ)) hw'
      (F.map (ComplexEmbedding.conjugate (v.1.embedding.comp (c : K →+* K)))) (F.map v.1.embedding)
    rw [← hW] at h
    refine h.trans (mul_le_mul_of_nonneg_right (le_of_eq ?_) (hg0 _))
    rcases hπ v with h' | h'
    · rw [h']
      exact re_det_gram_conjugate w F _
    · rw [h']
  rw [← prod_normSq_embedding, sq]
  calc ∏ v : Pl K, Complex.normSq (v.1.embedding ((F.map c)ᵀ * diagonal (fun r => (w r : K)) * F).det)
      ≤ ∏ v : Pl K, (g (π v).1.embedding * g v.1.embedding) :=
        Finset.prod_le_prod₀ (fun v _ => Complex.normSq_nonneg _) fun v _ => hv v
    _ = (∏ v : Pl K, g v.1.embedding) * ∏ v : Pl K, g v.1.embedding := by
        rw [Finset.prod_mul_distrib, Equiv.prod_comp π fun v => g v.1.embedding]

/-! ### Claim 2: the ideal norm -/

omit [NumberField K] [IsTotallyComplex K] in
/-- **An integral matrix has an integral determinant**: it is the image of a matrix over `O_K`. -/
theorem det_mem_one {κ : Type} [Fintype κ] [DecidableEq κ] {U : Matrix κ κ K}
    (hU : ∀ i j, U i j ∈ (1 : Submodule (𝓞 K) K)) : U.det ∈ (1 : Submodule (𝓞 K) K) := by
  choose N hN using fun i j => Submodule.mem_one.1 (hU i j)
  have hUN : U = (algebraMap (𝓞 K) K).mapMatrix (Matrix.of N) := by
    ext i j
    exact (hN i j).symm
  rw [hUN, ← RingHom.map_det]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

omit [IsTotallyComplex K] in
/-- **A ring automorphism preserves ideal norms**: `N(c(I)) = N(I)`, as `c` induces `O_K/I ≅ O_K/c(I)`
(`Ideal.quotientEquiv`). -/
theorem absNorm_map_ringEquiv (e : 𝓞 K ≃+* 𝓞 K) (I : Ideal (𝓞 K)) :
    Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv).symm

omit [NumberField K] [IsTotallyComplex K] in
/-- **Induction over a product of ideals**: a property of the elements of `∏_i I_i` that holds for `0`, is closed
under sums and multiples, and holds for the products `∏_i b_i` with `b_i ∈ I_i` (which span, `Ideal.prod_span`). -/
theorem prod_ideals_induction {κ : Type} [Fintype κ] (I : κ → Ideal (𝓞 K)) (p : 𝓞 K → Prop) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hmul : ∀ a x, p x → p (a * x))
    (hgen : ∀ b : κ → 𝓞 K, (∀ i, b i ∈ I i) → p (∏ i, b i)) : ∀ x ∈ ∏ i, I i, p x := by
  intro x hx
  rw [show ∏ i, I i = ∏ i, Ideal.span (I i : Set (𝓞 K)) by simp only [Ideal.span_eq], Ideal.prod_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := (Set.mem_finsetProd _ _ _).1 hx
    exact hgen b fun i => hb (Finset.mem_univ i)
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => exact hmul a x hx

omit [IsTotallyComplex K] in
/-- (TS8) **Claim 2, the ideal norm**: if `c(b)·b′·H_ij ∈ O_K` for all `b ∈ I_i`, `b′ ∈ I_j`, and `det H ≠ 0`, then
`|N(det H)|·∏_i N(I_i)² ≥ 1`: `(det H)·c(∏_i I_i)·∏_j I_j` is a nonzero integral ideal (its generators
`det H·∏c(b_i)∏b′_j = det(diag(c b)·H·diag(b′))` are integral), the absolute norm is multiplicative, and
`N(c(I)) = N(I)` (`absNorm_map_ringEquiv`). -/
theorem one_le_norm_det_mul_absNorm {κ : Type} [Fintype κ] [DecidableEq κ] (c : K ≃+* K) (I : κ → Ideal (𝓞 K))
    (hI : ∀ i, I i ≠ ⊥) (H : Matrix κ κ K)
    (hH : ∀ i j, ∀ b ∈ I i, ∀ b' ∈ I j, c (b : K) * (b' : K) * H i j ∈ (1 : Submodule (𝓞 K) K))
    (hdet : H.det ≠ 0) :
    1 ≤ |((Algebra.norm ℚ H.det : ℚ) : ℝ)| * ∏ i, (Ideal.absNorm (I i) : ℝ) ^ 2 := by
  set cO : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv c
  set A : Ideal (𝓞 K) := ∏ i, I i
  have hprod (b : κ → 𝓞 K) : ((∏ i, b i : 𝓞 K) : K) = ∏ i, (b i : K) := map_prod (algebraMap (𝓞 K) K) b _
  have hadd (x y : 𝓞 K) : ((x + y : 𝓞 K) : K) = x + y := map_add (algebraMap (𝓞 K) K) x y
  have hmul (x y : 𝓞 K) : ((x * y : 𝓞 K) : K) = x * y := map_mul (algebraMap (𝓞 K) K) x y
  -- the generators
  have hgen (b b' : κ → 𝓞 K) (hb : ∀ i, b i ∈ I i) (hb' : ∀ i, b' i ∈ I i) :
      H.det * c ((∏ i, b i : 𝓞 K) : K) * ((∏ i, b' i : 𝓞 K) : K) ∈ (1 : Submodule (𝓞 K) K) := by
    have e : H.det * c ((∏ i, b i : 𝓞 K) : K) * ((∏ i, b' i : 𝓞 K) : K) =
        (diagonal (fun i => c (b i : K)) * H * diagonal (fun i => (b' i : K))).det := by
      rw [det_mul, det_mul, det_diagonal, det_diagonal, hprod, hprod, map_prod]
      ring
    rw [e]
    refine det_mem_one fun i j => ?_
    rw [mul_diagonal, diagonal_mul]
    have := hH i j (b i) (hb i) (b' j) (hb' j)
    rwa [show c (b i : K) * H i j * (b' j : K) = c (b i : K) * (b' j : K) * H i j by ring]
  -- every `δ·c(x)·y`, `x, y ∈ ∏_i I_i`, is integral
  have hint : ∀ x ∈ A, ∀ y ∈ A, H.det * c (x : K) * (y : K) ∈ (1 : Submodule (𝓞 K) K) := by
    refine prod_ideals_induction I _ (fun y _ => by simp) (fun x x' hx hx' y hy => ?_) (fun a x hx y hy => ?_)
      fun b hb => prod_ideals_induction I _ (by simp) (fun y y' hy hy' => ?_) (fun a y hy => ?_)
        fun b' hb' => hgen b b' hb hb'
    · have := add_mem (hx y hy) (hx' y hy)
      rwa [← add_mul, ← mul_add, ← map_add, ← hadd] at this
    · have := Submodule.smul_mem _ (cO a) (hx y hy)
      rwa [Algebra.smul_def, show algebraMap (𝓞 K) K (cO a) = c (a : K) from rfl,
        show c (a : K) * (H.det * c (x : K) * (y : K)) = H.det * c ((a * x : 𝓞 K) : K) * (y : K) by
          rw [hmul, map_mul]; ring] at this
    · have := add_mem hy hy'
      rwa [← mul_add, ← hadd] at this
    · have := Submodule.smul_mem _ a hy
      rwa [Algebra.smul_def, show algebraMap (𝓞 K) K a = (a : K) from rfl,
        show (a : K) * (H.det * c ((∏ i, b i : 𝓞 K) : K) * (y : K)) =
          H.det * c ((∏ i, b i : 𝓞 K) : K) * ((a * y : 𝓞 K) : K) by rw [hmul]; ring] at this
  -- the fractional ideal `(δ)·c(A)·A` is integral and nonzero
  set F : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (𝓞 K)⁰ H.det * ((A.map cO : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      (A : FractionalIdeal (𝓞 K)⁰ K)
  have hF1 : F ≤ 1 := by
    refine FractionalIdeal.mul_le.2 fun u hu v hv => ?_
    obtain ⟨u', hu', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hu
    obtain ⟨x', hx', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hu'
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv cO x').1 hx'
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hv
    obtain ⟨z, hz⟩ := Submodule.mem_one.1 (hint x hx y hy)
    exact (FractionalIdeal.mem_one_iff _).2 ⟨z, by rw [hz]; rfl⟩
  have hA : A ≠ ⊥ := by
    rw [← Submodule.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [Submodule.zero_eq_bot]; exact hI i
  have hF0 : F ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hdet) ?_)
      (FractionalIdeal.coeIdeal_ne_zero.2 hA)
    refine FractionalIdeal.coeIdeal_ne_zero.2 fun h => hA ?_
    exact (Ideal.map_eq_bot_iff_of_injective cO.injective).1 h
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hF1
  have hJ0 : J ≠ ⊥ := fun h => hF0 (by rw [← hJ, h, FractionalIdeal.coeIdeal_bot])
  have hJ1 : (1 : ℚ) ≤ Ideal.absNorm J := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
  have hnorm : FractionalIdeal.absNorm F = |Algebra.norm ℚ H.det| * (∏ i, (Ideal.absNorm (I i) : ℚ)) ^ 2 := by
    rw [map_mul, map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm,
      FractionalIdeal.coeIdeal_absNorm, absNorm_map_ringEquiv, map_prod]
    push_cast
    ring
  rw [← hJ, FractionalIdeal.coeIdeal_absNorm] at hnorm
  rw [hnorm] at hJ1
  have := (Rat.cast_le (K := ℝ)).2 hJ1
  rw [Finset.prod_pow]
  simpa only [Rat.cast_one, Rat.cast_mul, Rat.cast_abs, Rat.cast_pow, Rat.cast_prod, Rat.cast_natCast] using this

/-! ### Integral pseudo-bases and sublattices -/

omit [IsTotallyComplex K] in
/-- (TS8a) **Integral pseudo-bases**: every `O_K`-lattice is `P·∏_i I_i` with `P` invertible and nonzero integral
ideals `I_i`: from `M = P·∏_i 𝔟_i` (`exists_pseudo_pi`), write `𝔟_i = a_i⁻¹·I_i` with `a_i ∈ O_K∖0`
(`FractionalIdeal.exists_eq_spanSingleton_mul`) and replace `P` by `P·diag(a_i⁻¹)`. -/
theorem exists_pseudo_pi_int {κ : Type} [Fintype κ] (M : Submodule (𝓞 K) (κ → K)) [M.IsLattice K] :
    ∃ (I : κ → Ideal (𝓞 K)) (P : Matrix κ κ K), (∀ i, I i ≠ ⊥) ∧ IsUnit P ∧
      M = (Submodule.pi Set.univ fun i => ((I i : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)).map
        ((Matrix.mulVecLin P).restrictScalars (𝓞 K)) := by
  obtain ⟨𝔟, P, h𝔟, hP, hM⟩ := exists_pseudo_pi M
  choose a J ha hJ using fun i => FractionalIdeal.exists_eq_spanSingleton_mul (𝔟 i)
  have ha' (i : κ) : algebraMap (𝓞 K) K (a i) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 (ha i)
  have hmem (i : κ) (x : K) : x ∈ (𝔟 i : Submodule (𝓞 K) K) ↔
      algebraMap (𝓞 K) K (a i) * x ∈ ((J i : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coe, hJ i, FractionalIdeal.mem_singleton_mul]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [← mul_assoc, mul_inv_cancel₀ (ha' i), one_mul]
    · exact fun h => ⟨_, h, by rw [← mul_assoc, inv_mul_cancel₀ (ha' i), one_mul]⟩
  set D : Matrix κ κ K := diagonal fun i => (algebraMap (𝓞 K) K (a i))⁻¹
  refine ⟨J, P * D, fun i h => h𝔟 i ?_, hP.mul ?_, ?_⟩
  · rw [hJ i, h, FractionalIdeal.coeIdeal_bot, mul_zero]
  · rw [isUnit_iff_isUnit_det, det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (ha' i)).isUnit
  · rw [hM]
    ext x
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, mulVecLin_apply, Submodule.mem_pi, Set.mem_univ,
      true_implies]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun i => algebraMap (𝓞 K) K (a i) * u i, fun i => (hmem i _).1 (hu i), ?_⟩
      rw [← mulVec_mulVec]
      congr 1
      funext i
      rw [mulVec_diagonal, ← mul_assoc, inv_mul_cancel₀ (ha' i), one_mul]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨D *ᵥ y, fun i => (hmem i _).2 ?_, by rw [mulVec_mulVec]⟩
      rw [mulVec_diagonal, ← mul_assoc, mul_inv_cancel₀ (ha' i), one_mul]
      exact hy i

/-- (TS6) **A sublattice as a hermitian lattice in its own coordinates**: a member `a` of the slope lattice of `X`
(an `O_K`-stable saturated `ℤ`-sublattice of `ψ(M)`) is `Y` in a basis `Pm` of its `K`-span: `Y.G = σ(Pm)ᴴ G σ(Pm)`,
`Pm·Y.M ⊆ M`, `deg a = deg Y`, `rk a = [K:ℚ]·s`. The `O_K`-module `A_K = {x ∈ M : ψ(x) ∈ a}` spans `W = Pm·K^s`, and
`M_Y = Pm⁻¹(A_K)`; the map of `Pm` (`hom`) is an isometry (`inner_ψ_map`) from `ψ_Y(M_Y)` onto `a`, so the covolumes
agree (`EuclidLattice.covol_sq_eq`). -/
theorem exists_subKLattice [DecidableEq ι] (X : KLattice K ι) (a : X.toPlaceLattice.S) :
    ∃ (s : ℕ) (Pm : Matrix ι (Fin s) K) (Y : KLattice K (Fin s)),
      (∀ v, Y.G v = (Pm.map v.1.embedding)ᴴ * X.G v * Pm.map v.1.embedding) ∧
      (∀ y ∈ Y.M, Pm *ᵥ y ∈ X.M) ∧
      X.toPlaceLattice.slopeLattice.deg a = degK Y ∧
      (X.toPlaceLattice.slopeLattice.rk a : ℝ) = finrank ℚ K * s := by
  obtain ⟨⟨A, haΛ, hsat⟩, hstab⟩ := a
  have hst : Stable part A := hstab
  have : DiscreteTopology A := EuclidLattice.discrete_of_le haΛ
  -- the `O_K`-module `A_K` of `a`, its `K`-span `W`, and a basis `Pm` of `W`
  let AK : Submodule (𝓞 K) (ι → K) :=
    { carrier := {x | x ∈ X.M ∧ X.ψ x ∈ A}
      add_mem' := fun hx hy => ⟨X.M.add_mem hx.1 hy.1, by rw [map_add]; exact A.add_mem hx.2 hy.2⟩
      zero_mem' := ⟨X.M.zero_mem, by rw [map_zero]; exact A.zero_mem⟩
      smul_mem' := fun k x hx => ⟨X.M.smul_mem k hx.1, by
        change X.ψ ((k : K) • x) ∈ A
        rw [X.ψ_smul]
        exact hst k _ hx.2⟩ }
  have hAK (x : ι → K) : x ∈ AK ↔ x ∈ X.M ∧ X.ψ x ∈ A := Iff.rfl
  set W : Submodule K (ι → K) := Submodule.span K (AK : Set (ι → K))
  set s := finrank K W
  set β := Module.finBasis K W
  set Pm : Matrix ι (Fin s) K := fun i j => (β j : ι → K) i
  have hPm (c' : Fin s → K) : Pm *ᵥ c' = ((∑ j, c' j • β j : W) : ι → K) := by
    funext i
    simp only [mulVec, dotProduct, Pm, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm]
  have hrange : LinearMap.range (mulVecLin Pm) = W := by
    ext x
    refine ⟨?_, fun hx => ⟨β.repr ⟨x, hx⟩, by rw [mulVecLin_apply, hPm, β.sum_repr]⟩⟩
    rintro ⟨c', rfl⟩
    rw [mulVecLin_apply, hPm]
    exact Submodule.coe_mem _
  have hinj : Function.Injective Pm.mulVec := by
    intro c₁ c₂ h
    rw [hPm, hPm] at h
    have h' := Fintype.linearIndependent_iff.1 β.linearIndependent (c₁ - c₂) (Subtype.ext (by
      simpa only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Submodule.coe_sub, Submodule.coe_zero,
        sub_eq_zero] using h))
    funext j
    exact sub_eq_zero.1 (h' j)
  have hAKW : ∀ x ∈ AK, ∃ y, Pm *ᵥ y = x := fun x hx => by
    obtain ⟨y, hy⟩ : x ∈ LinearMap.range (mulVecLin Pm) := hrange ▸ Submodule.subset_span hx
    exact ⟨y, hy⟩
  -- the lattice `M_Y = Pm⁻¹(A_K)`
  set f : (Fin s → K) →ₗ[𝓞 K] (ι → K) := (mulVecLin Pm).restrictScalars (𝓞 K)
  set MY : Submodule (𝓞 K) (Fin s → K) := AK.comap f
  have hmapMY : MY.map f = AK := by
    refine le_antisymm (Submodule.map_comap_le _ _) fun x hx => ?_
    obtain ⟨y, rfl⟩ := hAKW x hx
    exact ⟨y, hx, rfl⟩
  have hAKfg : AK.FG := Submodule.FG.of_le (Submodule.IsLattice.fg : X.M.FG) fun x hx => hx.1
  have : MY.IsLattice K :=
    { fg := Submodule.fg_of_fg_map_injective f hinj (hmapMY ▸ hAKfg)
      span_eq_top := by
        refine Submodule.map_injective_of_injective (f := mulVecLin Pm) hinj ?_
        rw [Submodule.map_top, hrange, ← Submodule.span_image]
        congr 1
        ext x
        exact ⟨fun ⟨y, hy, hxy⟩ => hxy ▸ hy, fun hx => (hmapMY ▸ hx : x ∈ MY.map f)⟩ }
  have hσinj (v : Pl K) : Function.Injective (Pm.map v.1.embedding).mulVec :=
    HermForms.mulVec_map_injective v.1.embedding hinj
  let Y : KLattice K (Fin s) := ⟨MY, fun v => (Pm.map v.1.embedding)ᴴ * X.G v * Pm.map v.1.embedding,
    fun v => (X.posDef v).conjTranspose_mul_mul_same (hσinj v)⟩
  -- the isometry from `ψ_Y(M_Y)` onto `a`
  set T : Space K (Fin s) →ₗ[ℤ] Space K ι :=
    ((Y.hom X (mulVecLin Pm) : Space K (Fin s) →ₗ[ℂ] Space K ι)).restrictScalars ℤ
  have hT (y : Fin s → K) : T (Y.ψ y) = X.ψ (Pm *ᵥ y) := Y.hom_ψ X (mulVecLin Pm) y
  have hTmaps : ∀ u ∈ Y.lattice, T u ∈ A := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hT y).symm ▸ hy.2
  let e : Y.lattice ≃ₗ[ℤ] A := LinearEquiv.ofBijective (T.restrict hTmaps) ⟨fun u u' h => by
      obtain ⟨y, -, hy⟩ := u.2
      obtain ⟨y', -, hy'⟩ := u'.2
      change Y.ψ y = u.1 at hy
      change Y.ψ y' = u'.1 at hy'
      have h' : T u.1 = T u'.1 := congrArg Subtype.val h
      rw [← hy, ← hy', hT, hT] at h'
      exact Subtype.ext (hy.symm.trans ((congrArg Y.ψ (hinj (X.ψ_injective h'))).trans hy')), fun z => by
      obtain ⟨x, hx, hxz⟩ := haΛ z.2
      have hxA : x ∈ AK := ⟨hx, hxz.symm ▸ z.2⟩
      obtain ⟨y, rfl⟩ := hAKW x hxA
      exact ⟨⟨Y.ψ y, y, hxA, rfl⟩, Subtype.ext ((hT y).trans hxz)⟩⟩
  have he (u u' : Y.lattice) : inner ℝ ((e u : A) : Space K ι) ((e u' : A) : Space K ι) =
      1 * inner ℝ (u : Space K (Fin s)) (u' : Space K (Fin s)) := by
    obtain ⟨_, ⟨y, -, rfl⟩⟩ := u
    obtain ⟨_, ⟨y', -, rfl⟩⟩ := u'
    change inner ℝ (T (Y.ψ y)) (T (Y.ψ y')) = _
    rw [hT, hT]
    have hP : @LinearMap.toMatrix' K _ ι (Fin s) (fun a b => Classical.propDecidable (a = b)) _ (mulVecLin Pm) =
        Pm := by
      rw [Subsingleton.elim (fun a b : Fin s => Classical.propDecidable (a = b)) (instDecidableEqFin s)]
      exact LinearMap.toMatrix'_toLin' Pm
    exact X.inner_ψ_map Y (mulVecLin Pm) 1 (fun v => by
      rw [one_smul]
      exact congrArg (fun Q : Matrix ι (Fin s) K => (Q.map v.1.embedding)ᴴ * X.G v * Q.map v.1.embedding) hP) y y'
  have hcov := EuclidLattice.covol_sq_eq e 1 he
  rw [one_pow, one_mul, sq_eq_sq₀ (EuclidLattice.covol_pos _).le (EuclidLattice.covol_pos _).le] at hcov
  refine ⟨s, Pm, Y, fun v => rfl, fun y hy => hy.1, ?_, ?_⟩
  · show -Real.log (EuclidLattice.covol A) = -Real.log (EuclidLattice.covol Y.lattice)
    rw [hcov]
  · have h1 : finrank ℝ (Submodule.span ℝ (A : Set (Space K ι))) = finrank ℤ Y.lattice := by
      rw [EuclidLattice.finrank_span A, e.finrank_eq]
    have h2 := Y.rk_top
    change finrank ℝ (Submodule.span ℝ (Y.lattice : Set (Space K (Fin s)))) = _ at h2
    change (finrank ℝ (Submodule.span ℝ (A : Set (Space K ι))) : ℝ) = _
    rw [h1, ← EuclidLattice.finrank_span, h2, Fintype.card_fin]
    push_cast
    ring

/-! ### Theorem A -/

/-- (TS9) **The slope of a lattice with an integral twisted pairing**: if `G_v = σ_v(F)ᴴ W σ_v(F)` at every place,
`c` is complex conjugation at one place, and `D·h_c` is integral on `M`, then `μ_arch ≤ log D`. With
`M = P·∏_i I_i` (`exists_pseudo_pi_int`) and `g_v = det(σ_v(FP)ᴴ W σ_v(FP))`, `slopeArch_pseudo` gives
`μ_arch = −(Σ_v log g_v + Σ_i log N(I_i))/(n_∞·|κ|)`. The twisted Gram determinant `δ = det(c(FP)ᵀ W FP)` has
`σ_{v₀}(δ) = g_{v₀} ≠ 0`, `|N(δ)| ≤ (∏_v g_v)²` (Claim 1, `abs_norm_det_twGram_le`) and
`D^{[K:ℚ]·|κ|}·|N(δ)|·∏_i N(I_i)² ≥ 1` (Claim 2, `one_le_norm_det_mul_absNorm`, for `H = D·c(FP)ᵀ W FP`, whose
entries `c(b)b′H_{ij} = D·h_c(P b e_i, P b′ e_j)` are integral); `[K:ℚ] = 2n_∞`. -/
theorem slopeArch_le_of_twPair {κ : Type} [Fintype κ] [Nonempty κ] [DecidableEq R]
    (Y : KLattice K κ) (w : R → ℚ) (hw : ∀ r, 0 < w r) (F : Matrix R κ K)
    (hG : ∀ v : Pl K, Y.G v = (F.map v.1.embedding)ᴴ * diagonal (fun r => (w r : ℂ)) * F.map v.1.embedding)
    (c : K ≃+* K) (hc : ∃ v₀ : Pl K, ∀ z, v₀.1.embedding (c z) = starRingEnd ℂ (v₀.1.embedding z))
    {D : ℕ} (hD : 0 < D)
    (hint : ∀ x ∈ Y.M, ∀ y ∈ Y.M, (D : K) * twPair (c : K →+* K) w F x y ∈ (1 : Submodule (𝓞 K) K)) :
    slopeArch Y ≤ Real.log D := by
  obtain ⟨v₀, hv₀⟩ := hc
  obtain ⟨I, P, hI, hP, hM⟩ := exists_pseudo_pi_int Y.M
  rw [slopeArch_pseudo Y (fun i => FractionalIdeal.coeIdeal_ne_zero.2 (hI i)) P hM]
  simp only [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  set F' := F * P
  set Hm : Matrix κ κ K := (F'.map c)ᵀ * diagonal (fun r => (w r : K)) * F'
  set g : Pl K → ℝ := fun v => ((P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding).det.re with hgdef
  have hg (v : Pl K) : (P.map v.1.embedding)ᴴ * Y.G v * P.map v.1.embedding =
      (F'.map v.1.embedding)ᴴ * diagonal (fun r => (w r : ℂ)) * F'.map v.1.embedding := by
    rw [hG, Matrix.map_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hgpos (v : Pl K) : 0 < g v :=
    (Complex.pos_iff.1 ((Y.posDef v).conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.2 (hP.map v.1.embedding.mapMatrix))).det_pos).1
  -- the twisted Gram determinant is nonzero
  have hmap (σ : K →+* ℂ) : σ Hm.det = ((F'.map (ComplexEmbedding.conjugate (σ.comp (c : K →+* K))))ᴴ *
      diagonal (fun r => (w r : ℂ)) * F'.map σ).det := by
    have e := map_det_twGram (c : K →+* K) w F' σ
    rwa [RingEquiv.coe_toRingHom] at e
  have hconj : ComplexEmbedding.conjugate (v₀.1.embedding.comp (c : K →+* K)) = v₀.1.embedding := by
    ext z
    simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, RingEquiv.coe_toRingHom, hv₀,
      Complex.conj_conj]
  have hδ : Hm.det ≠ 0 := fun h0 => by
    have e := hmap v₀.1.embedding
    rw [hconj, ← hg, h0, map_zero] at e
    have := hgpos v₀
    rw [hgdef] at this
    simp only [← e, Complex.zero_re, lt_self_iff_false] at this
  -- Claim 1
  have h1 := abs_norm_det_twGram_le c w (fun r => (hw r).le) F'
  simp only [← hg] at h1
  -- Claim 2, for `H = D·Hm`
  have hsingle (i : κ) (b : 𝓞 K) (hb : b ∈ I i) : P *ᵥ Pi.single i (b : K) ∈ Y.M := by
    rw [hM]
    refine ⟨Pi.single i (b : K), fun j _ => ?_, rfl⟩
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same]
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩
    · rw [Pi.single_eq_of_ne hj]
      exact Submodule.zero_mem _
  have hH : ∀ i j, ∀ b ∈ I i, ∀ b' ∈ I j, c (b : K) * (b' : K) * ((D : K) • Hm) i j ∈ (1 : Submodule (𝓞 K) K) := by
    intro i j b hb b' hb'
    have h := hint _ (hsingle i b hb) _ (hsingle j b' hb')
    rw [← twPair_mul, twPair_single, RingEquiv.coe_toRingHom] at h
    rwa [Matrix.smul_apply, smul_eq_mul, show c (b : K) * (b' : K) * ((D : K) * Hm i j) =
      (D : K) * (c (b : K) * (b' : K) * Hm i j) by ring]
  have hdet : ((D : K) • Hm).det ≠ 0 := by
    rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hD.ne')) hδ
  have h2 := one_le_norm_det_mul_absNorm c I hI _ hH hdet
  have hN : |((Algebra.norm ℚ ((D : K) • Hm).det : ℚ) : ℝ)| =
      (D : ℝ) ^ (finrank ℚ K * Fintype.card κ) * |((Algebra.norm ℚ Hm.det : ℚ) : ℝ)| := by
    rw [det_smul, map_mul, map_pow, ← map_natCast (algebraMap ℚ K), Algebra.norm_algebraMap, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_pow, Rat.cast_natCast, abs_mul, abs_pow, abs_pow, Nat.abs_cast, ← pow_mul]
  rw [hN] at h2
  -- the logarithms
  set n := Fintype.card (Pl K)
  set s := Fintype.card κ
  have hK : (finrank ℚ K : ℝ) = 2 * n := by
    rw [IsTotallyComplex.finrank]
    push_cast
    rfl
  have hn : (0 : ℝ) < n := by
    have : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    rw [hK] at this
    linarith
  have hs : (0 : ℝ) < s := Nat.cast_pos.2 Fintype.card_pos
  have hNI (i : κ) : (0 : ℝ) < Ideal.absNorm (I i) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => hI i (Ideal.absNorm_eq_zero_iff.1 h))
  have hprod : 1 ≤ (D : ℝ) ^ (finrank ℚ K * s) * (∏ v, g v) ^ 2 * ∏ i, (Ideal.absNorm (I i) : ℝ) ^ 2 := by
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => sq_nonneg _))
    exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (Nat.cast_nonneg _) _)
  have hD' : (0 : ℝ) < D := Nat.cast_pos.2 hD
  have hlog := Real.log_nonneg hprod
  have hgp : 0 < ∏ v, g v := Finset.prod_pos fun v _ => hgpos v
  rw [Real.log_mul (mul_pos (pow_pos hD' _) (pow_pos hgp 2)).ne' (Finset.prod_pos fun i _ => pow_pos (hNI i) 2).ne',
    Real.log_mul (pow_pos hD' _).ne' (pow_pos hgp 2).ne', Real.log_pow, Real.log_pow,
    Real.log_prod fun v _ => (hgpos v).ne', Real.log_prod fun i _ => (pow_pos (hNI i) 2).ne'] at hlog
  simp only [Real.log_pow] at hlog
  rw [← Finset.mul_sum] at hlog
  push_cast at hlog
  change -((n : ℝ)⁻¹ * ∑ v, Real.log (g v) / s) -
    2 * (∑ i, Real.log (Ideal.absNorm (I i) : ℝ)) / (finrank ℚ K * s) ≤ Real.log D
  rw [← Finset.sum_div, hK]
  rw [hK] at hlog
  have key : -((n : ℝ)⁻¹ * ((∑ v, Real.log (g v)) / s)) -
      2 * (∑ i, Real.log (Ideal.absNorm (I i) : ℝ)) / (2 * n * s) =
      -((∑ v, Real.log (g v)) + ∑ i, Real.log (Ideal.absNorm (I i) : ℝ)) / (n * s) := by
    field_simp
    ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith

/-- (TS10) **Theorem A, the maximal slope from an integral twisted pairing**: for metrics `G_v = σ_v(E)ᴴ W σ_v(E)`
(`W = diag(w)`, `w > 0` rational) and an automorphism `c` of `K` that is complex conjugation at one place, if
`D·h_c` is integral on `M` then every member of the slope lattice has archive slope at most `log D`. A member `a`
of positive rank is a lattice `Y` in a basis `Pm` of its `K`-span (`exists_subKLattice`), with
`G_{Y,v} = σ_v(E·Pm)ᴴ W σ_v(E·Pm)` and `h_{c,E·Pm} = h_{c,E}(Pm·, Pm·)` (`twPair_mul`) integral on `M_Y`; then
`slopeArch_le_of_twPair`. -/
theorem slopeLe_of_twPair [DecidableEq ι] [DecidableEq R] (X : KLattice K ι) (w : R → ℚ) (hw : ∀ r, 0 < w r)
    (E : Matrix R ι K)
    (hG : ∀ v : Pl K, X.G v = (E.map v.1.embedding)ᴴ * diagonal (fun r => (w r : ℂ)) * E.map v.1.embedding)
    (c : K ≃+* K) (hc : ∃ v₀ : Pl K, ∀ z, v₀.1.embedding (c z) = starRingEnd ℂ (v₀.1.embedding z))
    {D : ℕ} (hD : 0 < D)
    (hint : ∀ x ∈ X.M, ∀ y ∈ X.M, (D : K) * twPair (c : K →+* K) w E x y ∈ (1 : Submodule (𝓞 K) K)) :
    (X.toPlaceLattice.slopeLattice.rescale (-Real.log 2 + Real.log |(discr K : ℝ)| / finrank ℚ K)).SlopeLe
      (Real.log D) := by
  intro a
  obtain ⟨s, Pm, Y, hYG, hYM, hdeg, hrk⟩ := exists_subKLattice X a
  show 2 * X.toPlaceLattice.slopeLattice.deg a +
      (-Real.log 2 + Real.log |(discr K : ℝ)| / finrank ℚ K) * X.toPlaceLattice.slopeLattice.rk a ≤
    Real.log D * X.toPlaceLattice.slopeLattice.rk a
  rcases Nat.eq_zero_or_pos s with hs | hs
  · have hrk0 : X.toPlaceLattice.slopeLattice.rk a = 0 := by
      rw [hs, Nat.cast_zero, mul_zero] at hrk
      exact_mod_cast hrk
    have ha : a = ⊥ := by
      by_contra hne
      have := X.toPlaceLattice.slopeLattice.rk_strictMono (bot_lt_iff_ne_bot.2 hne)
      rw [X.toPlaceLattice.slopeLattice.rk_bot, hrk0] at this
      exact lt_irrefl _ this
    rw [ha, X.toPlaceLattice.slopeLattice.deg_bot, X.toPlaceLattice.slopeLattice.rk_bot]
    simp
  · have : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
    have hGY (v : Pl K) : Y.G v = ((E * Pm).map v.1.embedding)ᴴ * diagonal (fun r => (w r : ℂ)) *
        (E * Pm).map v.1.embedding := by
      rw [hYG, hG, Matrix.map_mul, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have h := slopeArch_le_of_twPair Y w hw (E * Pm) hGY c hc hD fun y hy y' hy' => by
      rw [twPair_mul]
      exact hint _ (hYM y hy) _ (hYM y' hy')
    unfold slopeArch at h
    have hr : (0 : ℝ) < finrank ℚ K * s := mul_pos (Nat.cast_pos.2 Module.finrank_pos) (Nat.cast_pos.2 hs)
    rw [Y.rk_top, Fintype.card_fin] at h
    push_cast at h
    have hdeg' : X.toPlaceLattice.slopeLattice.deg a = Y.toPlaceLattice.slopeLattice.deg ⊤ := hdeg
    rw [hrk, hdeg']
    have h' := mul_le_mul_of_nonneg_right h hr.le
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hr.ne'] at h'
    linarith

end KLattice
