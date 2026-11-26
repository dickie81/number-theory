import FormSlope

/-!
# The `ℤ`-form of `∇` and the coordinates of `Δ`

Part III of the exact slope bound (F) (W1–W8), for an antitone weight `λ` and its shape `ν = natW λ`. Write
`⟨P, Q⟩ = Σ_d P_d Q_d d!` for the bilinear Fock form and `κ = ⟨hw_ν, hw_ν⟩ ∈ ℚ_{>0}` (`HermForms.kappa`).

**Row weights** (W1). A bideterminant is homogeneous for the row weight (`rowW`: `x_{τ,a,b}` counts in row `(τ, a)`),
of weight `μ(rows)_{σ,a} = #{(s, c, i) : rows σ s c i = a}` (`bidet_isWH_rowW`): a minor of `x_τ` on the rows `I` has
row weight `Σ_i e_{I i}`. On a row-homogeneous polynomial of weight `μ`, the substitution by diagonal matrices is
multiplication by `∏ a^μ` (`lsub_diagonal_of_isWH`, `twist_diagonal_of_isWH`).

**The `ℤ`-form** (W2). `∇_ℤ ⊆ Pol_ℚ` is the `ℤ`-span of the bideterminants (`nablaZ`); its weight parts `∇_ℤ(μ)`
(`nablaZw`, spanned by the bideterminants of row weight `μ`) are finitely generated and torsion-free, hence free.
Concatenating bases gives `zb`, indexed by `ZIdx`, with `zb j` of row weight `zwt j` (`zb_isWH`): a `ℤ`-basis of `∇_ℤ`
(independent since the weight-`μ` component of a relation is a relation in `∇_ℤ(μ)`), with integer
coefficients (`coeff_zb_mem`). Over any field `K` of characteristic `0` its image spans `∇_K` (`span_zbK`, from
`span_bidet`) and is independent (`linearIndependent_zbK`), so `|ZIdx| = dim ∇_K`.

**The dual basis** (W3). `Gzb = (⟨zb_i, zb_j⟩/κ)` is invertible (the Fock form is definite over `ℚ`), `Γ = Gzb⁻¹`
(`Γ_mul_Gzb`), and `zdual_i = Σ_k Γ_{ik} zb_k` has `⟨zdual_i, zb_j⟩ = κ·δ_{ij}` (`fock_zdual_zb`) and
`⟨zdual_i, zdual_j⟩ = κ·Γ_{ij}` (`fock_zdual_zdual`). Distinct row weights have disjoint monomials
(`fock_eq_zero_of_isWH`), so `Gzb` is block-diagonal, hence so is `Γ` (it commutes with the projections onto the
weights), and `zdual_i` has row weight `zwt i` (`zdual_isWH`). `Γ` is positive definite over `ℝ` (`posDef_Γ`).

**Coordinates of `Δ`** (W4). Over `K`, the `zdual` are a basis of `∇_K` (`zdualBasis`, by the duality); `dcoord` is its
coordinate map, `dcoord F j = dc_j F = ⟨F, zb_j⟩/κ`. For every subring `A ⊆ K`, `F ∈ Δ_A(ν)` iff
`F ∈ ∇_K` and every `dc_j F ∈ A` (`mem_Delta_iff`): the bideterminants and the `zb_j` are `ℤ`-combinations of each
other.

**Integral substitutions** (W5–W7). `β(U·x) = Σ_{rows'} (∏ U_{rows, rows'})·β_{rows'}` by multilinearity of the
determinant in the rows (`lsub_bidet`), so with adjointness (`fock_lsub`) a substitution over `A` keeps `Δ_A`
(`lsub_mem_Delta`), and a twist by `U ∈ GL_n(A)` preserves and reflects it (`twist_mem_Delta_iff`).

**Multiplicities** (W8). `wtMult ρ a = Σ_j (zwt j)_{ρ,a}` does not depend on `a` (`wtMult_eq`): renaming the rows by a
permutation `π` maps `∇_ℤ(μ)` injectively into `∇_ℤ(μ ∘ π⁻¹)`, so the ranks are permutation invariant (`finrank_perm`),
and `wtMult ρ a = Σ_μ rk ∇_ℤ(μ)·μ_{ρ,a}`. Every `zb j` has degree `|ν_ρ|` in block `ρ` (its monomials have row weight
`zwt j` and column weight `ν`), so `Σ_a wtMult ρ a = r·|ν_ρ|` (`sum_wtMult`), and `cExp ρ = r·s_ρ + wtMult ρ 0` has
`n·cExp ρ = r·Λ_ρ` (`n_mul_cExp`) and `n·C_λ = r·ΣΛ` (`n_mul_cLam`), with `r = |ZIdx|`, `s_ρ = λ_{ρ,n−1}` and
`Λ_ρ = Σ_i λ_{ρ,i}`.
-/

namespace WeylFock

open MvPolynomial HermForms

open scoped Matrix

noncomputable section

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ}

/-! ## W1: row weights of bideterminants -/

section RowWeight

variable {L : Type*} [Field L]

variable (Φ n) in
/-- The row maps of the bideterminants of shape `ν`: `rows τ s c` are the rows of the `c`-th factor `D_{τ,s+1}`. -/
abbrev BRows (ν : Φ → Fin n → ℕ) : Type :=
  (τ : Φ) → (s : Fin n) → Fin (mult (ν τ) s) → Fin (s + 1) → Fin n

/-- The row weight of the bideterminant with rows `rows`: `μ_{σ,a} = #{(s, c, i) : rows σ s c i = a}`. -/
def rowWt {ν : Φ → Fin n → ℕ} (rows : BRows Φ n ν) : Φ → Fin n → ℕ :=
  fun σ a => ∑ s, ∑ c, ∑ i, if rows σ s c i = a then 1 else 0

omit [Fintype Φ] in
/-- A minor of `x_τ` on the rows `I` has row weight `Σ_i e_{I i}` in block `τ`. -/
theorem minor_isWH_rowW (τ : Φ) (s : Fin n) (I : Fin (s + 1) → Fin n) :
    IsWeightedHomogeneous (rowW Φ n) (minor τ s I : Pol Φ n L)
      (∑ i, (Pi.single τ (Pi.single (I i) 1) : Φ → Fin n → ℕ)) := by
  rw [minor, Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule]
  have h := IsWeightedHomogeneous.prod (R := L) (w := rowW Φ n) Finset.univ
    (fun i => (xMat τ).submatrix I (Fin.castLE s.isLt) (σ i) i) _
    fun i _ => isWeightedHomogeneous_X L _ _
  convert h using 1
  exact (Equiv.sum_comp σ (fun i => (Pi.single τ (Pi.single (I i) 1) : Φ → Fin n → ℕ))).symm

/-- **W1.** The bideterminant with rows `rows` is homogeneous for the row weight, of weight `rowWt rows`. -/
theorem bidet_isWH_rowW {ν : Φ → Fin n → ℕ} (rows : BRows Φ n ν) :
    IsWeightedHomogeneous (rowW Φ n) (bidet L ν rows) (rowWt rows) := by
  have key : IsWeightedHomogeneous (rowW Φ n) (bidet L ν rows)
      (∑ τ, ∑ s, ∑ c, ∑ i, (Pi.single τ (Pi.single (rows τ s c i) 1) : Φ → Fin n → ℕ)) :=
    IsWeightedHomogeneous.prod _ _ _ fun τ _ => IsWeightedHomogeneous.prod _ _ _ fun s _ =>
      IsWeightedHomogeneous.prod _ _ _ fun c _ => minor_isWH_rowW τ s (rows τ s c)
  convert key using 1
  funext σ a
  simp only [rowWt, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_eq_single σ (fun τ _ h => by simp [Ne.symm h]) (by simp)]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne (rows σ s c i) a with h | h
  · simp [h]
  · simp [h, Ne.symm h]

/-- **W1 (diagonal substitutions).** On a row-homogeneous `F` of weight `μ`, `F ↦ F(diag(a)·x)` is multiplication
by `∏_{σ,i} a_{σ,i}^{μ_{σ,i}}`. -/
theorem lsub_diagonal_of_isWH {F : Pol Φ n L} {μ : Φ → Fin n → ℕ} (hF : IsWeightedHomogeneous (rowW Φ n) F μ)
    (a : Φ → Fin n → L) : lsub (fun σ => Matrix.diagonal (a σ)) F = (∏ σ, ∏ i, a σ i ^ μ σ i) • F := by
  have hX : ∀ p : Φ × Fin n × Fin n,
      lsub (fun σ => Matrix.diagonal (a σ)) (X p) = C (a p.1 p.2.1) * X p := fun p => by
    rw [lsub_X, Finset.sum_eq_single p.2.1 (fun b _ hb => by
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), map_zero, zero_mul]) (by simp), Matrix.diagonal_apply_eq]
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  conv_rhs => rw [F.as_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : ∏ σ, ∏ i, a σ i ^ μ σ i = ∏ p ∈ d.support, a p.1 p.2.1 ^ d p := by
    rw [← hF (mem_support_iff.1 hd)]
    have := Finsupp.prod_fintype d (fun p k => a p.1 p.2.1 ^ k) (fun _ => pow_zero _)
    rw [Finsupp.prod] at this
    rw [this, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [weight_rowW_apply, ← Finset.prod_pow_eq_pow_sum]
  rw [monomial_eq, map_mul, lsub_C, Finsupp.prod, map_prod]
  simp only [map_pow, hX, mul_pow, Finset.prod_mul_distrib]
  rw [hw, smul_eq_C_mul, map_prod]
  simp only [map_pow]
  ring

/-- **W1 (diagonal twists).** On a row-homogeneous `F` of weight `μ`,
`twist_{diag(a)} F = ∏_σ ((∏_i a_{σ,i})^{s_σ}·∏_i a_{σ,i}^{μ_{σ,i}})·F`, `s_σ = λ_{σ,n−1}`. -/
theorem twist_diagonal_of_isWH (lam : Φ → Fin n → ℤ) {F : Pol Φ n L} {μ : Φ → Fin n → ℕ}
    (hF : IsWeightedHomogeneous (rowW Φ n) F μ) (a : Φ → Fin n → L) :
    twist lam (fun σ => Matrix.diagonal (a σ)) F =
      (∏ σ, ((∏ i, a σ i) ^ detShift (lam σ) * ∏ i, a σ i ^ μ σ i)) • F := by
  rw [twist, lsub_diagonal_of_isWH hF, Finset.prod_mul_distrib, mul_smul, ← smul_eq_C_mul]
  simp only [Matrix.det_diagonal]

end RowWeight

/-! ## W2: the `ℤ`-form of `∇` and a row-homogeneous `ℤ`-basis -/

section ZForm

variable (lam : Φ → Fin n → ℤ)

/-- `∇_ℤ`, the `ℤ`-span of the bideterminants of shape `ν = natW λ` in `Pol_ℚ`. -/
def nablaZ : Submodule ℤ (Pol Φ n ℚ) := Submodule.span ℤ (Set.range (bidet ℚ fun ρ => natW (lam ρ)))

/-- The row weights of the bideterminants of shape `natW λ`. -/
def wts : Finset (Φ → Fin n → ℕ) :=
  Finset.univ.image fun rows : BRows Φ n (fun ρ => natW (lam ρ)) => rowWt rows

/-- The weight-`μ` part of `∇_ℤ`: the `ℤ`-span of the bideterminants of row weight `μ`. -/
def nablaZw (μ : Φ → Fin n → ℕ) : Submodule ℤ (Pol Φ n ℚ) :=
  Submodule.span ℤ (bidet ℚ (fun ρ => natW (lam ρ)) '' {rows | rowWt rows = μ})

/-- The weight parts are finitely generated. -/
instance (μ : Φ → Fin n → ℕ) : Module.Finite ℤ (nablaZw lam μ) :=
  Module.Finite.span_of_finite ℤ ((Set.toFinite _).image _)

/-- The weight parts are free: finitely generated and torsion-free over `ℤ`. -/
instance (μ : Φ → Fin n → ℕ) : Module.Free ℤ (nablaZw lam μ) := Module.free_of_finite_type_torsion_free'

/-- The index set of the `ℤ`-basis `zb` of `∇_ℤ`: a weight `μ` and an index of a basis of the weight-`μ` part. -/
def ZIdx : Type := Σ μ : wts lam, Module.Free.ChooseBasisIndex ℤ (nablaZw lam μ)

/-- `ZIdx` is finite. -/
instance : Fintype (ZIdx lam) := by unfold ZIdx; infer_instance

/-- `ZIdx` has decidable equality (classically). -/
instance : DecidableEq (ZIdx lam) := Classical.decEq _

/-- A sum over `ZIdx` is a sum over the weights and the basis indices of each weight part. -/
theorem sum_ZIdx {M : Type*} [AddCommMonoid M] (f : ZIdx lam → M) :
    ∑ j, f j = ∑ μ : wts lam, ∑ i : Module.Free.ChooseBasisIndex ℤ (nablaZw lam μ), f ⟨μ, i⟩ :=
  Fintype.sum_sigma f

/-- The row weight `zwt j` of the basis vector `zb j`. -/
def zwt (j : ZIdx lam) : Φ → Fin n → ℕ := j.1

/-- The basis vectors of `∇_ℤ`: a `ℤ`-basis of each weight part, concatenated. -/
def zb (j : ZIdx lam) : Pol Φ n ℚ := (Module.Free.chooseBasis ℤ (nablaZw lam j.1) j.2 : Pol Φ n ℚ)

/-- `zb j` is row-homogeneous of weight `zwt j`: its weight part is spanned by bideterminants of that weight
(W1). -/
theorem zb_isWH (j : ZIdx lam) : IsWeightedHomogeneous (rowW Φ n) (zb lam j) (zwt lam j) := by
  have h : nablaZw lam j.1 ≤
      (weightedHomogeneousSubmodule ℚ (rowW Φ n) (j.1 : Φ → Fin n → ℕ)).restrictScalars ℤ := by
    rw [nablaZw, Submodule.span_le]
    rintro _ ⟨rows, hrows, rfl⟩
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem, mem_weightedHomogeneousSubmodule]
    exact hrows ▸ bidet_isWH_rowW rows
  have := h (Module.Free.chooseBasis ℤ (nablaZw lam j.1) j.2).2
  rwa [Submodule.restrictScalars_mem, mem_weightedHomogeneousSubmodule] at this

/-- The `zb` span `∇_ℤ` over `ℤ`: each weight part lies in `∇_ℤ`, and each bideterminant lies in its weight part. -/
theorem span_zb : Submodule.span ℤ (Set.range (zb lam)) = nablaZ lam := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.span_mono (Set.image_subset_range _ _) (Module.Free.chooseBasis ℤ (nablaZw lam j.1) j.2).2
  · rw [nablaZ, Submodule.span_le]
    rintro _ ⟨rows, rfl⟩
    set μ : wts lam := ⟨rowWt rows, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    have h1 : bidet ℚ (fun ρ => natW (lam ρ)) rows ∈ nablaZw lam μ :=
      Submodule.subset_span (Set.mem_image_of_mem _ (show rowWt rows = (μ : Φ → Fin n → ℕ) from rfl))
    have h3 := Submodule.mem_map_of_mem (f := (nablaZw lam μ).subtype)
      ((Module.Free.chooseBasis ℤ (nablaZw lam μ)).mem_span (⟨_, h1⟩ : nablaZw lam μ))
    rw [Submodule.map_span, ← Set.range_comp] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨i, rfl⟩
    exact ⟨Sigma.mk μ i, rfl⟩

/-- The `zb` are `ℤ`-independent: the weight-`μ` component of a relation is a relation in the weight-`μ` part. -/
theorem linearIndependent_zb : LinearIndependent ℤ (zb lam) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro c hc ⟨μ, i⟩
  have hcomp : ∀ k : ZIdx lam, weightedHomogeneousComponent (rowW Φ n) (μ : Φ → Fin n → ℕ) (zb lam k) =
      if k.1 = μ then zb lam k else 0 := fun k => by
    split_ifs with h
    · have := (zb_isWH lam k).weightedHomogeneousComponent_same
      rwa [zwt, h] at this
    · exact (zb_isWH lam k).weightedHomogeneousComponent_ne _ fun h' => h (Subtype.ext h'.symm)
  have h1 := congrArg (weightedHomogeneousComponent (rowW Φ n) (μ : Φ → Fin n → ℕ)) hc
  simp only [map_sum, map_zsmul, hcomp, map_zero, smul_ite, smul_zero] at h1
  rw [sum_ZIdx, Finset.sum_eq_single μ (fun μ' _ h => Finset.sum_eq_zero fun i' _ => ite_eq_right_iff.2
    fun h' => absurd h' h) (by simp)] at h1
  have h3 : ∑ i', c ⟨μ, i'⟩ • Module.Free.chooseBasis ℤ (nablaZw lam μ) i' = 0 :=
    Subtype.ext (by simpa [zb] using h1)
  exact Fintype.linearIndependent_iff.1 (Module.Free.chooseBasis ℤ _).linearIndependent _ h3 i

/-- **W2.** The `zb` have integer coefficients, as the bideterminants do (`coeff_bidet_mem`). -/
theorem coeff_zb_mem (j : ZIdx lam) (d : Φ × Fin n × Fin n →₀ ℕ) :
    (zb lam j).coeff d ∈ (Int.castRingHom ℚ).range := by
  have h : zb lam j ∈ nablaZ lam := span_zb lam ▸ Submodule.subset_span ⟨j, rfl⟩
  refine Submodule.span_induction (p := fun x _ => x.coeff d ∈ (Int.castRingHom ℚ).range) ?_ ?_ ?_ ?_ h
  · rintro _ ⟨rows, rfl⟩
    exact coeff_bidet_mem _ _ rows d
  · simp
  · intro x y _ _ hx hy
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact add_mem hx hy
  · intro a x _ hx
    rw [coeff_smul]
    exact zsmul_mem hx a

/-- The `zb` are `ℚ`-independent (clear denominators). -/
theorem linearIndependent_zb_rat : LinearIndependent ℚ (zb lam) :=
  (LinearIndependent.iff_fractionRing ℤ ℚ).1 (linearIndependent_zb lam)

end ZForm

/-! ## The bilinear Fock form: bilinearity and orthogonality of row weights -/

section FockForm

variable {K : Type*} [Field K]

omit [DecidableEq Φ] in
/-- The bilinear Fock form is linear in its second argument: scalars. -/
theorem fock_smul_right (a : K) (P Q : Pol Φ n K) :
    fockWith (RingHom.id K) P (a • Q) = a * fockWith (RingHom.id K) P Q := by
  rw [smul_eq_C_mul, fock_C_mul_right]

omit [DecidableEq Φ] in
/-- The bilinear Fock form of two combinations. -/
theorem fock_sum_smul_sum {ι : Type*} [Fintype ι] (x y : ι → K) (P Q : ι → Pol Φ n K) :
    fockWith (RingHom.id K) (∑ i, x i • P i) (∑ j, y j • Q j) =
      ∑ i, ∑ j, x i * y j * fockWith (RingHom.id K) (P i) (Q j) := by
  rw [fock_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fock_smul_left, fock_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fock_smul_right]
  ring

omit [Fintype Φ] in
/-- **Orthogonality of row weights**: polynomials of distinct row weights have disjoint monomials. -/
theorem fock_eq_zero_of_isWH {P Q : Pol Φ n K} {μ μ' : Φ → Fin n → ℕ}
    (hP : IsWeightedHomogeneous (rowW Φ n) P μ) (hQ : IsWeightedHomogeneous (rowW Φ n) Q μ') (h : μ ≠ μ') :
    fockWith (RingHom.id K) P Q = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  by_cases hPd : P.coeff d = 0
  · simp [hPd]
  · exact absurd ((hP hPd).symm.trans (hQ (mem_support_iff.1 hd))) h

omit [DecidableEq Φ] in
/-- The bilinear Fock form over `ℝ` is definite. -/
theorem fock_self_pos_real {P : Pol Φ n ℝ} (hP : P ≠ 0) : 0 < fockWith (RingHom.id ℝ) P P := by
  rw [fock_eq_sum_left (subset_refl _)]
  exact Finset.sum_pos (fun d hd => mul_pos (mul_self_pos.2 (mem_support_iff.1 hd))
    (Finset.prod_pos fun _ _ => Nat.cast_pos.2 (Nat.factorial_pos _))) (support_nonempty.2 hP)

end FockForm

/-! ## W3: the dual basis over `ℚ` -/

section Dual

variable (lam : Φ → Fin n → ℤ)

/-- `Gzb_{ij} = ⟨zb_i, zb_j⟩/κ`, the Gram matrix of `zb` for the normalised bilinear Fock form. -/
def Gzb : Matrix (ZIdx lam) (ZIdx lam) ℚ := fun i j => fockWith (RingHom.id ℚ) (zb lam i) (zb lam j) / kappa lam

/-- `Γ = Gzb⁻¹`, the Gram matrix of the dual basis `zdual` (`fock_zdual_zdual`). -/
def Γ : Matrix (ZIdx lam) (ZIdx lam) ℚ := (Gzb lam)⁻¹

/-- The dual basis `zdual_i = Σ_k Γ_{ik} zb_k`: `⟨zdual_i, zb_j⟩/κ = δ_{ij}` (`fock_zdual_zb`). -/
def zdual (i : ZIdx lam) : Pol Φ n ℚ := ∑ k, Γ lam i k • zb lam k

/-- `det Gzb ≠ 0`: a null vector `v` gives `⟨Σ v_i zb_i, Σ v_i zb_i⟩ = 0`, so `Σ v_i zb_i = 0` (the Fock form is
definite over `ℚ`), so `v = 0` (`linearIndependent_zb_rat`). -/
theorem det_Gzb_ne_zero : (Gzb lam).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  refine hv0 (funext fun i => Fintype.linearIndependent_iff.1 (linearIndependent_zb_rat lam) v ?_ i)
  by_contra hne
  have h1 := fock_self_pos_rat hne
  rw [fock_sum_smul_sum] at h1
  have h2 : ∑ i, ∑ j, v i * v j * fockWith (RingHom.id ℚ) (zb lam i) (zb lam j) =
      kappa lam * ∑ i, v i * (Gzb lam *ᵥ v) i := by
    simp only [Matrix.mulVec, dotProduct, Gzb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    field_simp [(kappa_pos lam).ne']
  rw [h2, hv] at h1
  simp at h1

/-- `Gzb·Γ = 1`. -/
theorem Gzb_mul_Γ : Gzb lam * Γ lam = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_Gzb_ne_zero lam))

/-- **W3.** `Γ·Gzb = 1`: `Γ = Gzb⁻¹`. -/
theorem Γ_mul_Gzb : Γ lam * Gzb lam = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_Gzb_ne_zero lam))

/-- `Gzb` is block-diagonal for the row weights (`fock_eq_zero_of_isWH`). -/
theorem Gzb_eq_zero {i k : ZIdx lam} (h : zwt lam i ≠ zwt lam k) : Gzb lam i k = 0 := by
  unfold Gzb
  rw [fock_eq_zero_of_isWH (zb_isWH lam i) (zb_isWH lam k) h, zero_div]

/-- `Γ` is block-diagonal for the row weights: `Gzb` commutes with the projection `D` onto a weight, hence so does
its inverse. -/
theorem Γ_eq_zero {i k : ZIdx lam} (h : zwt lam i ≠ zwt lam k) : Γ lam i k = 0 := by
  set D : Matrix (ZIdx lam) (ZIdx lam) ℚ := Matrix.diagonal fun l => if zwt lam l = zwt lam k then 1 else 0
  have hG : Gzb lam * D = D * Gzb lam := by
    ext a b
    simp only [D, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hab : zwt lam a = zwt lam b
    · rw [hab, mul_comm]
    · rw [Gzb_eq_zero lam hab, zero_mul, mul_zero]
  have hΓ : Γ lam * D = D * Γ lam :=
    calc Γ lam * D = Γ lam * D * (Gzb lam * Γ lam) := by rw [Gzb_mul_Γ, Matrix.mul_one]
      _ = Γ lam * (Gzb lam * D) * Γ lam := by rw [hG]; simp only [Matrix.mul_assoc]
      _ = D * Γ lam := by rw [← Matrix.mul_assoc, Γ_mul_Gzb, Matrix.one_mul]
  have := congrFun (congrFun hΓ i) k
  simpa [D, Matrix.mul_diagonal, Matrix.diagonal_mul, h] using this

/-- **W3.** The duality `⟨zdual_i, zb_j⟩ = κ·δ_{ij}`: `Γ·Gzb = 1`. -/
theorem fock_zdual_zb (i j : ZIdx lam) :
    fockWith (RingHom.id ℚ) (zdual lam i) (zb lam j) = if i = j then kappa lam else 0 := by
  have h := congrFun (congrFun (Γ_mul_Gzb lam) i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [zdual, fock_sum_left]
  simp only [fock_smul_left]
  calc ∑ k, Γ lam i k * fockWith (RingHom.id ℚ) (zb lam k) (zb lam j) = kappa lam * ∑ k, Γ lam i k * Gzb lam k j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Gzb]
        field_simp [(kappa_pos lam).ne']
    _ = _ := by rw [h]; split_ifs <;> simp

/-- **W3.** `zdual_i` is row-homogeneous of weight `zwt i`, as `Γ` is block-diagonal (`Γ_eq_zero`). -/
theorem zdual_isWH (i : ZIdx lam) : IsWeightedHomogeneous (rowW Φ n) (zdual lam i) (zwt lam i) := by
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases h : zwt lam i = zwt lam k
  · rw [h]
    exact Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (zb_isWH lam k))
  · rw [Γ_eq_zero lam h, zero_smul]
    exact zero_mem _

/-- `Γ` is symmetric, as `Gzb` is (`fock_comm`). -/
theorem Γ_transpose : (Γ lam)ᵀ = Γ lam := by
  have hG : (Gzb lam)ᵀ = Gzb lam := by
    ext i j
    simp only [Matrix.transpose_apply, Gzb, fock_comm]
  rw [Γ, Matrix.transpose_nonsing_inv, hG]

/-- **W3.** `⟨zdual_i, zdual_j⟩ = κ·Γ_{ij}`: `Γ` is the Gram matrix of the dual basis. -/
theorem fock_zdual_zdual (i j : ZIdx lam) :
    fockWith (RingHom.id ℚ) (zdual lam i) (zdual lam j) = kappa lam * Γ lam i j := by
  show fockWith (RingHom.id ℚ) (zdual lam i) (∑ k, Γ lam j k • zb lam k) = _
  rw [fock_sum_right]
  simp only [fock_smul_right, fock_zdual_zb, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← congrFun (congrFun (Γ_transpose lam) i) j, Matrix.transpose_apply, mul_comm]

end Dual

/-! ## W2–W4 over a field of characteristic `0`: bases of `∇_K` and the coordinates of `Δ` -/

section Field

variable (K : Type*) [Field K] [CharZero K] (lam : Φ → Fin n → ℤ)

/-- The basis vectors `zb` over `K`. -/
def zbK (j : ZIdx lam) : Pol Φ n K := map (algebraMap ℚ K) (zb lam j)

/-- The dual basis `zdual` over `K`. -/
def zdualK (i : ZIdx lam) : Pol Φ n K := map (algebraMap ℚ K) (zdual lam i)

omit [DecidableEq Φ] in
/-- The normaliser `κ_K = ⟨hw_ν, hw_ν⟩` over `K` is the rational `κ`. -/
theorem fock_hw_eq_kappa :
    fockWith (RingHom.id K) (hw K fun ρ => natW (lam ρ)) (hw K fun ρ => natW (lam ρ)) =
      algebraMap ℚ K (kappa lam) := by
  rw [kappa, map_fockWith_id, map_hw]

/-- The duality over `K`: `⟨zdual_i, zb_j⟩ = κ·δ_{ij}`. -/
theorem fock_zdualK_zbK (i j : ZIdx lam) :
    fockWith (RingHom.id K) (zdualK K lam i) (zbK K lam j) = if i = j then algebraMap ℚ K (kappa lam) else 0 := by
  rw [zdualK, zbK, ← map_fockWith_id, fock_zdual_zb]
  split_ifs <;> simp

/-- **W3.** `⟨zdual_i, zdual_j⟩ = κ·Γ_{ij}` over `K`. -/
theorem fock_zdualK_zdualK (i j : ZIdx lam) :
    fockWith (RingHom.id K) (zdualK K lam i) (zdualK K lam j) = algebraMap ℚ K (kappa lam * Γ lam i j) := by
  rw [zdualK, zdualK, ← map_fockWith_id, fock_zdual_zdual]

/-- **W3.** `zdual_i` is row-homogeneous of weight `zwt i` over `K`. -/
theorem zdualK_isWH (i : ZIdx lam) : IsWeightedHomogeneous (rowW Φ n) (zdualK K lam i) (zwt lam i) :=
  fun {d} hd => zdual_isWH lam i fun h => hd (by rw [zdualK, coeff_map, h, map_zero])

/-- `zb_j` is a `ℤ`-combination of bideterminants (over `K`). -/
theorem exists_zbK_eq (j : ZIdx lam) : ∃ z : BRows Φ n (fun ρ => natW (lam ρ)) → ℤ,
    zbK K lam j = ∑ rows, z rows • bidet K (fun ρ => natW (lam ρ)) rows := by
  have h : zb lam j ∈ nablaZ lam := span_zb lam ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h
  refine ⟨z, ?_⟩
  rw [zbK, ← hz, map_sum]
  simp only [map_zsmul, map_bidet']

/-- Every bideterminant is a `ℤ`-combination of the `zb_j` (over `K`). -/
theorem exists_bidet_eq (rows : BRows Φ n (fun ρ => natW (lam ρ))) :
    ∃ y : ZIdx lam → ℤ, bidet K (fun ρ => natW (lam ρ)) rows = ∑ j, y j • zbK K lam j := by
  have h : bidet ℚ (fun ρ => natW (lam ρ)) rows ∈ Submodule.span ℤ (Set.range (zb lam)) :=
    (span_zb lam).symm ▸ Submodule.subset_span ⟨rows, rfl⟩
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h
  refine ⟨y, ?_⟩
  rw [← map_bidet' (algebraMap ℚ K), ← hy, map_sum]
  simp only [map_zsmul, zbK]

/-- `zdual_i = Σ_k Γ_{ik} zb_k` over `K`. -/
theorem zdualK_eq (i : ZIdx lam) : zdualK K lam i = ∑ k, algebraMap ℚ K (Γ lam i k) • zbK K lam k := by
  simp only [zdualK, zdual, map_sum, zbK]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

/-- `zb_k = Σ_j Gzb_{kj} zdual_j` over `K`: `Gzb·Γ = 1`. -/
theorem zbK_eq (k : ZIdx lam) : zbK K lam k = ∑ j, algebraMap ℚ K (Gzb lam k j) • zdualK K lam j := by
  simp only [zdualK_eq, Finset.smul_sum, smul_smul, ← map_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← map_sum, ← Matrix.mul_apply, Gzb_mul_Γ, Matrix.one_apply, apply_ite,
    map_one, map_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The `zdual` are `K`-independent, by the duality. -/
theorem linearIndependent_zdualK : LinearIndependent K (zdualK K lam) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (fun P => fockWith (RingHom.id K) P (zbK K lam j)) hc
  simp only [fock_sum_left, fock_smul_left, fock_zdualK_zbK, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  have h0 : fockWith (RingHom.id K) (0 : Pol Φ n K) (zbK K lam j) = 0 := by simp [fockWith]
  rw [h0] at h
  exact (mul_eq_zero.1 h).resolve_right (by simpa using (kappa_pos lam).ne')

/-- **W2.** The images of the `zb` are `K`-independent, by the duality. -/
theorem linearIndependent_zbK : LinearIndependent K (zbK K lam) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (fun P => fockWith (RingHom.id K) (zdualK K lam i) P) hc
  simp only [fock_sum_right, fock_smul_right, fock_zdualK_zbK, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, fock_zero_right] at h
  exact (mul_eq_zero.1 h).resolve_right (by simpa using (kappa_pos lam).ne')

variable {lam}

/-- The `zb` lie in `∇_K`: they are combinations of bideterminants. -/
theorem zbK_mem (hlam : ∀ ρ, Antitone (lam ρ)) (j : ZIdx lam) :
    zbK K lam j ∈ nabla K (fun ρ => natW (lam ρ)) := by
  obtain ⟨z, hz⟩ := exists_zbK_eq K lam j
  rw [hz]
  exact Submodule.sum_mem _ fun rows _ => zsmul_mem (bidet_mem_nabla (fun ρ => natW_antitone (hlam ρ)) rows) _

/-- **W2.** The images of the `zb` span `∇_K` (`span_bidet`). -/
theorem span_zbK (hlam : ∀ ρ, Antitone (lam ρ)) :
    Submodule.span K (Set.range (zbK K lam)) = nabla K (fun ρ => natW (lam ρ)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact zbK_mem K hlam j
  · rw [← span_bidet (fun ρ => natW_antitone (hlam ρ)), Submodule.span_le]
    rintro _ ⟨rows, rfl⟩
    obtain ⟨y, hy⟩ := exists_bidet_eq K lam rows
    rw [SetLike.mem_coe, hy]
    exact Submodule.sum_mem _ fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self j)) _

/-- The `zdual` span `∇_K`: they span the same space as the `zb` (`zdualK_eq`, `zbK_eq`). -/
theorem span_zdualK (hlam : ∀ ρ, Antitone (lam ρ)) :
    Submodule.span K (Set.range (zdualK K lam)) = nabla K (fun ρ => natW (lam ρ)) := by
  rw [← span_zbK K hlam]
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨j, rfl⟩
  · rw [SetLike.mem_coe, zdualK_eq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [SetLike.mem_coe, zbK_eq]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- **W3.** The dual basis `zdual` of `∇_K` (`zdualBasis_apply`). -/
def zdualBasis (hlam : ∀ ρ, Antitone (lam ρ)) : Module.Basis (ZIdx lam) K (nabla K fun ρ => natW (lam ρ)) :=
  (Module.Basis.span (linearIndependent_zdualK K lam)).map (LinearEquiv.ofEq _ _ (span_zdualK K hlam))

/-- **W3.** The basis `zdualBasis` is the family `zdual`. -/
theorem zdualBasis_apply (hlam : ∀ ρ, Antitone (lam ρ)) (i : ZIdx lam) :
    (zdualBasis K hlam i : Pol Φ n K) = zdualK K lam i := by
  simp [zdualBasis, Module.Basis.span_apply]

variable (lam) in
/-- `dc_j(F) = ⟨F, zb_j⟩/κ`, the `j`-th coordinate of `F` in the dual basis. -/
def dc (j : ZIdx lam) (F : Pol Φ n K) : K := fockWith (RingHom.id K) F (zbK K lam j) / algebraMap ℚ K (kappa lam)

/-- **W4.** The coordinates in the dual basis: `F = Σ_j dc_j(F)·zdual_j` (`dcoord_symm_apply`). -/
def dcoord (hlam : ∀ ρ, Antitone (lam ρ)) : (nabla K fun ρ => natW (lam ρ)) ≃ₗ[K] (ZIdx lam → K) :=
  (zdualBasis K hlam).equivFun

/-- **W4.** The inverse of `dcoord`: `x ↦ Σ_j x_j·zdual_j`. -/
theorem dcoord_symm_apply (hlam : ∀ ρ, Antitone (lam ρ)) (x : ZIdx lam → K) :
    ((dcoord K hlam).symm x : Pol Φ n K) = ∑ j, x j • zdualK K lam j := by
  simp [dcoord, Module.Basis.equivFun_symm_apply, zdualBasis_apply]

variable (lam) in
/-- **W4 (coordinates of `Δ`).** For every subring `A ⊆ K`, `F ∈ Δ_A(ν)` iff `F ∈ ∇_K` and every coordinate
`dc_j F = ⟨F, zb_j⟩/κ` lies in `A`: the bideterminants and the `zb_j` are `ℤ`-combinations of each other. -/
theorem mem_Delta_iff (A : Subring K) (F : Pol Φ n K) :
    F ∈ Delta A (fun ρ => natW (lam ρ)) ↔ F ∈ nabla K (fun ρ => natW (lam ρ)) ∧ ∀ j, dc K lam j F ∈ A := by
  simp only [Delta, Set.mem_ofPred_eq, fock_hw_eq_kappa]
  refine and_congr_right fun _ => ⟨fun h j => ?_, fun h rows => ?_⟩
  · obtain ⟨z, hz⟩ := exists_zbK_eq K lam j
    rw [dc, hz, fock_sum_right, Finset.sum_div]
    refine A.sum_mem fun rows _ => ?_
    rw [← Int.cast_smul_eq_zsmul K, fock_smul_right, mul_div_assoc]
    exact A.mul_mem (intCast_mem _ _) (h rows)
  · obtain ⟨y, hy⟩ := exists_bidet_eq K lam rows
    rw [hy, fock_sum_right, Finset.sum_div]
    refine A.sum_mem fun j _ => ?_
    rw [← Int.cast_smul_eq_zsmul K, fock_smul_right, mul_div_assoc]
    exact A.mul_mem (intCast_mem _ _) (h j)

end Field

/-! ## W3: `Γ` is positive definite -/

section PosDef

variable (lam : Φ → Fin n → ℤ)

/-- **W3.** `Γ` is positive definite (over `ℝ`): `xᵀΓx = ⟨Σ x_i zdual_i, Σ x_i zdual_i⟩/κ`, and the `zdual` are
`ℝ`-independent (`linearIndependent_zdualK`), the Fock form definite. -/
theorem posDef_Γ : ((Γ lam).map (algebraMap ℚ ℝ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
    rw [← congrFun (congrFun (Γ_transpose lam) i) j, Matrix.transpose_apply]
  · set P := ∑ i, x i • zdualK ℝ lam i
    have hP : P ≠ 0 := fun h =>
      hx (funext fun i => Fintype.linearIndependent_iff.1 (linearIndependent_zdualK ℝ lam) x h i)
    have h1 := fock_self_pos_real hP
    rw [fock_sum_smul_sum] at h1
    have hκ : (0 : ℝ) < algebraMap ℚ ℝ (kappa lam) := by simpa using kappa_pos lam
    have h2 : ∑ i, ∑ j, x i * x j * fockWith (RingHom.id ℝ) (zdualK ℝ lam i) (zdualK ℝ lam j) =
        algebraMap ℚ ℝ (kappa lam) * (star x ⬝ᵥ ((Γ lam).map (algebraMap ℚ ℝ) *ᵥ x)) := by
      simp only [fock_zdualK_zdualK, map_mul, star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h2] at h1
    exact pos_of_mul_pos_right h1 hκ.le

end PosDef

/-! ## W5–W6: integral substitutions keep `Δ_A` -/

section Subst

variable {L : Type} [Field L]

omit [Fintype Φ] [DecidableEq Φ] in
/-- A minor of `U·x` is a combination of minors of `x`, by multilinearity of the determinant in the rows:
`minor_I(U·x) = Σ_f (∏_i U_{I i, f i})·minor_f(x)`. -/
theorem lsub_minor_eq (U : Φ → Matrix (Fin n) (Fin n) L) (τ : Φ) (s : Fin n) (I : Fin (s + 1) → Fin n) :
    lsub U (minor τ s I) = ∑ f : Fin (s + 1) → Fin n, C (∏ i, U τ (I i) (f i)) * minor τ s f := by
  have hrow : (lsub U).mapMatrix ((xMat τ).submatrix I (Fin.castLE s.isLt)) =
      fun i => ∑ c, (C (U τ (I i) c) : Pol Φ n L) • fun j => (X (τ, c, Fin.castLE s.isLt j) : Pol Φ n L) := by
    ext i j
    simp [xMat, lsub_X, Finset.sum_apply, smul_eq_mul]
  rw [minor, AlgHom.map_det, hrow]
  unfold Matrix.det
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ, AlternatingMap.coe_multilinearMap, smul_eq_mul, map_prod, minor]
  rfl

/-- **W5.** `F ↦ F(U·x)` maps a bideterminant to a combination of bideterminants, with coefficients products of
entries of `U`. -/
theorem lsub_bidet (U : Φ → Matrix (Fin n) (Fin n) L) {ν : Φ → Fin n → ℕ} (rows : BRows Φ n ν) :
    lsub U (bidet L ν rows) =
      ∑ rows' : BRows Φ n ν, C (∏ τ, ∏ s, ∏ c, ∏ i, U τ (rows τ s c i) (rows' τ s c i)) * bidet L ν rows' := by
  simp only [bidet, map_prod, lsub_minor_eq, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun rows' _ => ?_
  simp only [Finset.prod_mul_distrib]

/-- **W5.** A substitution `F ↦ F(U·x)` with the entries of `U` in a subring `A` keeps `Δ_A(ν)`: by adjointness
(`fock_lsub`), `⟨F(U·x), β⟩ = ⟨F, β(Uᵀ·x)⟩`, and `β(Uᵀ·x)` is an `A`-combination of bideterminants (`lsub_bidet`). -/
theorem lsub_mem_Delta {A : Subring L} {U : Φ → Matrix (Fin n) (Fin n) L} (hU : ∀ σ i j, U σ i j ∈ A)
    {ν : Φ → Fin n → ℕ} {G : Pol Φ n L} (hG : G ∈ Delta A ν) : lsub U G ∈ Delta A ν := by
  refine ⟨lsub_mem_nabla U hG.1, fun rows => ?_⟩
  have h := fock_lsub (fun σ => (U σ).transpose) G (bidet L ν rows)
  simp only [Matrix.transpose_transpose] at h
  rw [h, lsub_bidet, fock_sum_right, Finset.sum_div]
  refine A.sum_mem fun rows' _ => ?_
  rw [fock_C_mul_right, mul_div_assoc]
  exact A.mul_mem (A.prod_mem fun τ _ => A.prod_mem fun s _ => A.prod_mem fun c _ => A.prod_mem fun i _ =>
    hU _ _ _) (hG.2 rows')

/-- `det(U)^s ∈ A` for `U` invertible over `A`: `det(U)⁻¹ = det(V)`. -/
theorem det_zpow_mem_of_mul_eq_one {A : Subring L} {U V : Matrix (Fin n) (Fin n) L} (hU : ∀ i j, U i j ∈ A)
    (hV : ∀ i j, V i j ∈ A) (hUV : U * V = 1) (s : ℤ) : U.det ^ s ∈ A := by
  have hdet : U.det * V.det = 1 := by rw [← Matrix.det_mul, hUV, Matrix.det_one]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg s
  · rw [zpow_natCast]
    exact A.pow_mem (det_mem hU) _
  · rw [zpow_neg, zpow_natCast, ← inv_pow, inv_eq_of_mul_eq_one_right hdet]
    exact A.pow_mem (det_mem hV) _

/-- A twist by `U ∈ GL_n(A)` keeps `Δ_A(ν)`: `lsub_mem_Delta`, and `∏ det(U_σ)^{s_σ}` is a unit of `A`. -/
theorem twist_mem_Delta {A : Subring L} (lam : Φ → Fin n → ℤ) {U V : Φ → Matrix (Fin n) (Fin n) L}
    (hU : ∀ σ i j, U σ i j ∈ A) (hV : ∀ σ i j, V σ i j ∈ A) (hUV : ∀ σ, U σ * V σ = 1) {ν : Φ → Fin n → ℕ}
    {G : Pol Φ n L} (hG : G ∈ Delta A ν) : twist lam U G ∈ Delta A ν := by
  rw [twist, C_mul']
  exact smul_mem_Delta (lsub_mem_Delta hU hG)
    (A.prod_mem fun σ _ => det_zpow_mem_of_mul_eq_one (hU σ) (hV σ) (hUV σ) _)

/-- **W6 (`GL_n(A)`-stability).** For `U` with inverse `V`, both with entries in a subring `A` (for example
`A = O_{L,w}`), `twist_U G ∈ Δ_A(ν) ↔ G ∈ Δ_A(ν)`: `twist_mem_Delta` both ways, and `twist_V ∘ twist_U = id`
(`twist_twist`). -/
theorem twist_mem_Delta_iff {A : Subring L} (lam : Φ → Fin n → ℤ) {U V : Φ → Matrix (Fin n) (Fin n) L}
    (hU : ∀ σ i j, U σ i j ∈ A) (hV : ∀ σ i j, V σ i j ∈ A) (hUV : ∀ σ, U σ * V σ = 1) {ν : Φ → Fin n → ℕ}
    {G : Pol Φ n L} : twist lam U G ∈ Delta A ν ↔ G ∈ Delta A ν := by
  refine ⟨fun h => ?_, twist_mem_Delta lam hU hV hUV⟩
  have := twist_mem_Delta lam hV hU (fun σ => mul_eq_one_comm.1 (hUV σ)) h
  have e : (fun σ => U σ * V σ) = fun _ => (1 : Matrix (Fin n) (Fin n) L) := funext hUV
  rwa [twist_twist, e, twist_one] at this

end Subst

/-! ## W8: the weight multiplicities are symmetric -/

section Mult

variable (lam : Φ → Fin n → ℤ)

/-- The multiplicity `wtMult ρ a = Σ_j (zwt j)_{ρ,a}` of row `a` of block `ρ` in the weights of the `zb`. -/
def wtMult (ρ : Φ) (a : Fin n) : ℕ := ∑ j, zwt lam j ρ a

/-- The permuted weight `μ ∘ π⁻¹` (in every block). -/
def permW (π : Equiv.Perm (Fin n)) (μ : Φ → Fin n → ℕ) : Φ → Fin n → ℕ := fun σ a => μ σ (π.symm a)

/-- The permuted rows `π ∘ rows`. -/
def permRows (π : Equiv.Perm (Fin n)) {ν : Φ → Fin n → ℕ} (rows : BRows Φ n ν) : BRows Φ n ν :=
  fun τ s c i => π (rows τ s c i)

/-- The renaming `x_{τ,a,b} ↦ x_{τ,π a,b}` of the variables. -/
def permVar (π : Equiv.Perm (Fin n)) (p : Φ × Fin n × Fin n) : Φ × Fin n × Fin n := (p.1, π p.2.1, p.2.2)

omit [Fintype Φ] [DecidableEq Φ] in
/-- `permW π⁻¹ ∘ permW π = id`. -/
theorem permW_symm (π : Equiv.Perm (Fin n)) (μ : Φ → Fin n → ℕ) : permW π.symm (permW π μ) = μ := by
  funext σ a
  simp [permW]

omit [Fintype Φ] [DecidableEq Φ] in
/-- The rows `π ∘ rows` have the permuted row weight. -/
theorem rowWt_permRows (π : Equiv.Perm (Fin n)) {ν : Φ → Fin n → ℕ} (rows : BRows Φ n ν) :
    rowWt (permRows π rows) = permW π (rowWt rows) := by
  funext σ a
  simp only [rowWt, permRows, permW, ← Equiv.eq_symm_apply]

omit [DecidableEq Φ] in
/-- Renaming the rows by `π` maps a bideterminant to the bideterminant with the rows `π ∘ rows`. -/
theorem rename_bidet (π : Equiv.Perm (Fin n)) {ν : Φ → Fin n → ℕ} (rows : BRows Φ n ν) :
    rename (permVar π) (bidet ℚ ν rows) = bidet ℚ ν (permRows π rows) := by
  simp only [bidet, minor, map_prod, AlgHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 1
  ext i j
  simp [xMat, permVar, permRows]

omit [DecidableEq Φ] in
/-- The renaming by `π` maps the weight-`μ` part of `∇_ℤ` into the weight-`π μ` part (`rename_bidet`). -/
theorem rename_mem_nablaZw (π : Equiv.Perm (Fin n)) (μ : Φ → Fin n → ℕ) {P : Pol Φ n ℚ}
    (hP : P ∈ nablaZw lam μ) : rename (permVar π) P ∈ nablaZw lam (permW π μ) := by
  have : nablaZw lam μ ≤
      (nablaZw lam (permW π μ)).comap ((rename (permVar π)).toLinearMap.restrictScalars ℤ) := by
    rw [nablaZw, Submodule.span_le]
    rintro _ ⟨rows, hrows, rfl⟩
    show rename (permVar π) (bidet ℚ _ rows) ∈ nablaZw lam (permW π μ)
    rw [rename_bidet]
    exact Submodule.subset_span ⟨permRows π rows, by rw [Set.mem_ofPred_eq, rowWt_permRows, hrows.out], rfl⟩
  exact this hP

omit [DecidableEq Φ] in
/-- The ranks of the weight parts are invariant under permuting the rows: `rename` by `π` is injective, and
`π⁻¹` maps back (`permW_symm`). -/
theorem finrank_perm (π : Equiv.Perm (Fin n)) (μ : Φ → Fin n → ℕ) :
    Module.finrank ℤ (nablaZw lam (permW π μ)) = Module.finrank ℤ (nablaZw lam μ) := by
  have hinj : ∀ π : Equiv.Perm (Fin n), Function.Injective (permVar (Φ := Φ) π) := fun π p q h => by
    simp only [permVar, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  have hle : ∀ (π : Equiv.Perm (Fin n)) μ,
      Module.finrank ℤ (nablaZw lam μ) ≤ Module.finrank ℤ (nablaZw lam (permW π μ)) := fun π μ =>
    LinearMap.finrank_le_finrank_of_injective
      (f := ((rename (permVar π)).toLinearMap.restrictScalars ℤ).restrict
        fun _ hx => rename_mem_nablaZw lam π μ hx)
      fun x y hxy => Subtype.ext (rename_injective _ (hinj π) (congrArg Subtype.val hxy))
  refine le_antisymm ?_ (hle π μ)
  have := hle π.symm (permW π μ)
  rwa [permW_symm] at this

/-- The permuted weights of bideterminants are weights of bideterminants. -/
theorem permW_mem_wts (π : Equiv.Perm (Fin n)) {μ : Φ → Fin n → ℕ} (h : μ ∈ wts lam) : permW π μ ∈ wts lam := by
  obtain ⟨rows, -, rfl⟩ := Finset.mem_image.1 h
  exact Finset.mem_image.2 ⟨permRows π rows, Finset.mem_univ _, rowWt_permRows π rows⟩

/-- `wtMult ρ a = Σ_μ rk(∇_ℤ)_μ·μ_{ρ,a}`. -/
theorem wtMult_eq_sum (ρ : Φ) (a : Fin n) :
    wtMult lam ρ a = ∑ μ ∈ wts lam, Module.finrank ℤ (nablaZw lam μ) * μ ρ a := by
  rw [wtMult, sum_ZIdx]
  simp only [zwt, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Module.finrank_eq_card_chooseBasisIndex]
  exact Finset.sum_coe_sort (wts lam) fun μ => Module.finrank ℤ (nablaZw lam μ) * μ ρ a

/-- **W8.** The multiplicities are symmetric: `wtMult ρ a = wtMult ρ b`. Permuting the rows permutes the weights
(`permW_mem_wts`) and keeps the ranks of the weight parts (`finrank_perm`). -/
theorem wtMult_eq (ρ : Φ) (a b : Fin n) : wtMult lam ρ a = wtMult lam ρ b := by
  have key : ∀ π : Equiv.Perm (Fin n), wtMult lam ρ (π.symm a) = wtMult lam ρ a := fun π => by
    rw [wtMult_eq_sum, wtMult_eq_sum]
    refine Finset.sum_nbij' (permW π) (permW π.symm) (fun μ h => permW_mem_wts lam π h)
      (fun μ h => permW_mem_wts lam π.symm h) (fun μ _ => permW_symm π μ)
      (fun μ _ => by simpa using permW_symm π.symm μ) fun μ _ => ?_
    rw [finrank_perm]
    rfl
  have := key (Equiv.swap a b)
  rw [Equiv.symm_swap, Equiv.swap_apply_left] at this
  exact this.symm

variable {lam}

/-- The `zb` lie in `∇_ℚ`. -/
theorem zb_mem_nabla (hlam : ∀ ρ, Antitone (lam ρ)) (j : ZIdx lam) :
    zb lam j ∈ nabla ℚ (fun ρ => natW (lam ρ)) := by
  have h : nablaZ lam ≤ (nabla ℚ fun ρ => natW (lam ρ)).restrictScalars ℤ := by
    rw [nablaZ, Submodule.span_le]
    rintro _ ⟨rows, rfl⟩
    exact bidet_mem_nabla (fun ρ => natW_antitone (hlam ρ)) rows
  exact h (span_zb lam ▸ Submodule.subset_span ⟨j, rfl⟩)

/-- Every `zb j` has degree `|ν_ρ|` in block `ρ`: a monomial of row weight `zwt j` and column weight `ν`. -/
theorem sum_zwt (hlam : ∀ ρ, Antitone (lam ρ)) (j : ZIdx lam) (ρ : Φ) :
    ∑ a, zwt lam j ρ a = ∑ b, natW (lam ρ) b := by
  have hne : zb lam j ≠ 0 := fun h =>
    (Module.Free.chooseBasis ℤ (nablaZw lam j.1)).ne_zero j.2 (Subtype.ext h)
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.1 hne
  have hc : ∀ b, natW (lam ρ) b = Finsupp.weight (colW Φ n) d ρ b := fun b => by
    rw [(mem_nabla_iff.1 (zb_mem_nabla hlam j)).1 hd]
  rw [← zb_isWH lam j hd]
  simp only [hc, weight_rowW_apply, weight_colW_apply]
  exact Finset.sum_comm

/-- **W8.** `Σ_a wtMult ρ a = r·|ν_ρ|`, `r = |ZIdx|`. -/
theorem sum_wtMult (hlam : ∀ ρ, Antitone (lam ρ)) (ρ : Φ) :
    ∑ a, wtMult lam ρ a = Fintype.card (ZIdx lam) * ∑ b, natW (lam ρ) b := by
  simp only [wtMult]
  rw [Finset.sum_comm]
  simp only [sum_zwt hlam, Finset.sum_const, Finset.card_univ, smul_eq_mul]

variable (lam) in
/-- The exponent `cExp ρ = r·s_ρ + wtMult ρ 0` of the determinant of `ρ_λ` on `VV` (`n_mul_cExp`). -/
def cExp (ρ : Φ) : ℤ :=
  Fintype.card (ZIdx lam) * detShift (lam ρ) + if h : 0 < n then (wtMult lam ρ ⟨0, h⟩ : ℤ) else 0

/-- `natW λ_i + s = λ_i` for antitone `λ`. -/
theorem natW_add_detShift {w : Fin n → ℤ} (hw : Antitone w) (i : Fin n) : (natW w i : ℤ) + detShift w = w i := by
  have hn : 0 < n := i.pos
  have : detShift w ≤ w i := by
    simp only [detShift, hn, ↓reduceDIte]
    exact hw (Fin.le_def.2 (by simp; omega))
  rw [natW, Int.toNat_of_nonneg (sub_nonneg.2 this)]
  ring

/-- **W8.** `n·cExp ρ = r·Λ_ρ`, `Λ_ρ = Σ_i λ_{ρ,i}`: `n·wtMult ρ 0 = Σ_a wtMult ρ a = r·|ν_ρ|` (`wtMult_eq`,
`sum_wtMult`), and `Λ_ρ = |ν_ρ| + n·s_ρ`. -/
theorem n_mul_cExp (hlam : ∀ ρ, Antitone (lam ρ)) (ρ : Φ) :
    (n : ℤ) * cExp lam ρ = Fintype.card (ZIdx lam) * ∑ i, lam ρ i := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  simp only [cExp, hn, ↓reduceDIte]
  have h1 : (n : ℤ) * wtMult lam ρ ⟨0, hn⟩ = Fintype.card (ZIdx lam) * ∑ b, (natW (lam ρ) b : ℤ) := by
    have := sum_wtMult hlam ρ
    rw [Finset.sum_congr rfl fun a _ => wtMult_eq lam ρ a ⟨0, hn⟩, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at this
    exact_mod_cast this
  have h2 : ∑ i, lam ρ i = ∑ i, (natW (lam ρ) i : ℤ) + n * detShift (lam ρ) := by
    rw [← Finset.sum_congr rfl fun i _ => natW_add_detShift (hlam ρ) i, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h2, mul_add, h1]
  ring

variable (lam) in
/-- `C_λ = Σ_ρ cExp ρ` (`n_mul_cLam`). -/
def cLam : ℤ := ∑ ρ, cExp lam ρ

/-- **W8.** `n·C_λ = r·ΣΛ`. -/
theorem n_mul_cLam (hlam : ∀ ρ, Antitone (lam ρ)) :
    (n : ℤ) * cLam lam = Fintype.card (ZIdx lam) * ∑ ρ, ∑ i, lam ρ i := by
  rw [cLam, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => n_mul_cExp hlam ρ

end Mult

end

end WeylFock

/-! ## W7: `Δ_N` in some local basis is `Δ_N` in every local basis -/

namespace HermForms

open WeylFock NumberField IsDedekindDomain

variable {E : Type} [Field E] {n : ℕ} {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L]

/-- If the columns of `C'` lie in the `A`-span of those of `C`, then `C' = C·U` with `U` over `A`. -/
theorem exists_mul_eq_of_span_le {A : Subring L} {C C' : Matrix (Fin n) (Fin n) L}
    (h : Submodule.span A (Set.range fun j i => C' i j) ≤ Submodule.span A (Set.range fun j i => C i j)) :
    ∃ U : Matrix (Fin n) (Fin n) L, (∀ i j, U i j ∈ A) ∧ C' = C * U := by
  have hj : ∀ j, ∃ c : Fin n → A, ∑ k, c k • (fun i => C i k) = fun i => C' i j :=
    fun j => (Submodule.mem_span_range_iff_exists_fun A).1 (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hj
  refine ⟨Matrix.of fun k j => (c j k : L), fun k j => (c j k).2, ?_⟩
  ext i j
  have := congrFun (hc j) i
  simp only [Finset.sum_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable [NumberField L]

end HermForms
