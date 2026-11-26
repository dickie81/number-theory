import LatticePseudo
import WeylDet

/-!
# The exact degree of `Δ_N`

Part V of the exact slope bound (F) (V1–V7), for a number field `L`, embeddings `τ : Φ → (E →+* L)` of a number
field `E` (CM where degrees of `O_E`-lattices enter), and an antitone weight `λ`, with `s_ρ = λ_{ρ,n−1}`,
`r = |ZIdx| ≥ 1` (`nonempty_ZIdx`), the dual basis `zdual` of `∇` and `Γ = (⟨zdual_i, zdual_j⟩/κ)` (`WeylZForm`).
Main results: `degK_deltaK` (V5), `degK_deltaK_Lsh` and `muK_deltaK_Lsh` (V6), `muArch_deltaK_intVec` (V7).

**V1, the lattice** (`deltaLat`, `deltaK`). `Δ_N`, tested in every local basis (`DeltaA`), in the coordinates of the
dual basis: `x ∈ Δ_N` iff `Σ_j x_j·zdual_j ∈ Δ_N`. It is an `O_L`-module, and an `O_L`-lattice for every
`O_E`-lattice `N` (`isLattice_deltaLat`, from V3, V4 and P1). The hermitian lattice `deltaK N` has the constant
metric `Γ` at every place (positive definite over `ℂ` as over `ℝ`, `posDef_map_ofReal`): the `zdual` are rational, so
at every embedding `σ` the normalised Fock form is `Σ_{i,j} conj(σx_i)·σy_j·Γ_{ij}` (`fock_map_sum_zdualK`).

**V2, local membership** (`mem_prod_zpow_iff`). Localising at `w`, `J ↦ O_{L,w}·J`, is Mathlib's
`FractionalIdeal.extendedHom'` along `O_L → O_{L,w}` (`locw`), a ring hom, so it commutes with products and integer
powers; `O_{L,w}` is a principal ideal ring, so `O_{L,w}·J = O_{L,w}·a` (`exists_locw_eq`). And `x ∈ J` iff
`x ∈ O_{L,w}·J` at every `w` (`mem_of_forall_mem_locw`): otherwise `{r : r·x ∈ J}` lies in a maximal ideal `w`, but
`x = Σ_k o_k y_k` with `y_k ∈ J`, `o_k = n_k/d_k` and `d_k ∉ w`. So `x ∈ ∏_k J_k^{e_k}` iff
`x·∏_k a_{w,k}^{−e_k} ∈ O_{L,w}` at every `w`.

**V3, diagonal lattices** (`deltaLat_diagLat`): for nonzero fractional ideals `𝔞_i` of `O_E`,
`Δ_{D(𝔞)} = ∏_j 𝔅(zwt j)` with `𝔅(μ) = ∏_{ρ,i} (τ_ρ(𝔞_i)·O_L)^{−(μ_{ρ,i} + s_ρ)}` (`bIdeal`; `τ_ρ(𝔞)·O_L` is
`extT`, Mathlib's `FractionalIdeal.extended`). At each `w` the diagonal matrices of generators of `O_{L,w}·τ_ρ(𝔞_i)`
are local bases (`isLocalBasis_diagonal`); on `zdual_j`, of row weight `zwt j`, the twist is the scalar
`∏_{ρ,i} a_{ρ,i}^{(zwt j)_{ρ,i} + s_ρ}` (`twist_diagonal_sum`), and `Δ_{O_{L,w}}` is read on the coordinates
(`mem_Delta_iff`), so V2 applies. Other local bases give the same, with no hypothesis on `N` (`DeltaN_subset_DeltaA`).
For `𝔞 = 1`, `Δ_{O_E^n} = O_L^{ZIdx}` (`deltaLat_intVec`).

**V4, transport** (`deltaLat_map`): `Δ_{γN} = R_γ(Δ_N)`, with `R_γ = rhoMat γ` the matrix of `ρ_λ(γ)` in the dual
basis, by `rho_mem_DeltaA` for `γ` and `γ⁻¹`.

**V5, the exact degree** (`degK_deltaK`): for every `O_E`-lattice `N ⊆ E^n`,
`deg Δ_N = deg Δ_{O_E^n} + [L:E]·C_λ·(deg O_E^n − deg N)`, with `[L:E] = [L:ℚ]/[E:ℚ]` and `C_λ = Σ_ρ cExp ρ`. Write
`N = γD(𝔞)` (P1, `exists_pseudo`). K1 with V4 and `det R_γ = ∏_ρ τ_ρ(det γ)^{−cExp ρ}` (`det_rhoMat`) gives
`deg Δ_{γD(𝔞)} = deg Δ_{D(𝔞)} + [L:E]·C_λ·log |N_{E/ℚ}(det γ)|` (`degK_deltaK_map`), as
`log |N_{L/ℚ}(τ_ρ x)| = [L:E]·log |N_{E/ℚ}(x)|` (`log_abs_norm_map`: `N_{L/ℚ} = N_{E/ℚ} ∘ N_{L/E}`). K2 with V3 gives
`deg Δ_{D(𝔞)} = deg Δ_{O_E^n} + [L:E]·C_λ·Σ_i log N(𝔞_i)` (`degK_deltaK_diagLat`), as
`log N(τ_ρ(𝔞)·O_L) = [L:E]·log N(𝔞)` (`log_absNorm_extT`: `Ideal.absNorm_algebraMap`, on the numerator and the
denominator of `𝔞`) and `Σ_j ((zwt j)_{ρ,i} + s_ρ) = cExp ρ` for every row `i` (`cExp_eq_sum`, W8). P2
(`degE_pseudo`) assembles the two parts.

**V6** (`degK_deltaK_of_unimodular`, `degK_deltaK_Lsh`, `muK_deltaK_Lsh`): for unimodular `N`,
`deg Δ_N = deg Δ_{O_E^n}` (P5); for a good `d`, `deg Δ_{Lsh d} = deg Δ_{O_E^n} − [L:E]·C_λ·Σ_{P∈ST} log N(P)` (P7),
and with `rk = [L:ℚ]·r` and `n·C_λ = r·ΣΛ`, `μ(Δ_{Lsh d}) = μ(Δ_{O_E^n}) − (ΣΛ/(n·[E:ℚ]))·Σ_{P∈ST} log N(P)`,
`ΣΛ = Σ_{ρ,i} λ_{ρ,i}`: independent of `d`.

**V7** (`muK_deltaK_intVec`, `muArch_deltaK_intVec`): K3 with V3 for `O_E^n`,
`μ(Δ_{O_E^n}) = −log det Γ/(2r) − archShift(L)/2`, with `archShift(L) = log|d_L|/[L:ℚ] − log 2` written out; in
the archive's units, `μ_arch(Δ_{O_E^n}) = 2μ + archShift(L) = −log det Γ/r`.
-/

namespace HermForms

open NumberField IsDedekindDomain WeylFock MvPolynomial HermClasses Module

open scoped nonZeroDivisors ComplexOrder Matrix

noncomputable section

/-! ## Real positive definite matrices over `ℂ` -/

/-- A real positive definite matrix is positive definite over `ℂ`: for `x = u + iv`, `xᴴAx = uᵀAu + vᵀAv`, the
cross terms cancelling as `A` is symmetric. For the metric `Γ` of `deltaK`. -/
theorem posDef_map_ofReal {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (A.map Complex.ofReal).PosDef := by
  have hT : ∀ i j, A j i = A i j := fun i j => by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hA.isHermitian i) j
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, hT]
  · set u : ι → ℝ := fun i => (x i).re with hu
    set v : ι → ℝ := fun i => (x i).im with hv
    have key : star x ⬝ᵥ (A.map Complex.ofReal *ᵥ x) = ((u ⬝ᵥ (A *ᵥ u) + v ⬝ᵥ (A *ᵥ v) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum, Complex.re_sum,
          Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
          Complex.ofReal_im, ← Finset.sum_add_distrib, hu, hv]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      · simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum, Complex.im_sum,
          Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
          Complex.ofReal_im]
        have h1 : ∑ i, ∑ j, (x i).re * (A i j * (x j).im) = ∑ i, ∑ j, (x i).im * (A i j * (x j).re) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hT]; ring
        trans ∑ i, ∑ j, ((x i).re * (A i j * (x j).im) - (x i).im * (A i j * (x j).re))
        · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
        · simp only [Finset.sum_sub_distrib, h1, sub_self]
    have hpos : 0 < u ⬝ᵥ (A *ᵥ u) + v ⬝ᵥ (A *ᵥ v) := by
      have hu0 := hA.posSemidef.dotProduct_mulVec_nonneg u
      have hv0 := hA.posSemidef.dotProduct_mulVec_nonneg v
      simp only [star_trivial] at hu0 hv0
      by_cases h : u = 0
      · have hv' : v ≠ 0 := fun h' => hx (funext fun i => Complex.ext (congrFun h i) (congrFun h' i))
        have := hA.dotProduct_mulVec_pos hv'
        simp only [star_trivial] at this
        linarith
      · have := hA.dotProduct_mulVec_pos h
        simp only [star_trivial] at this
        linarith
    rw [key]
    exact_mod_cast hpos

/-! ## The dual basis is not empty -/

/-- `r = |ZIdx| ≥ 1`: the highest-weight vector is a nonzero element of `∇_ℚ` (`hw_mem_nabla`, `eval_one_hw`),
which has the basis `zdual`. -/
theorem nonempty_ZIdx {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {lam : Φ → Fin n → ℤ}
    (hlam : ∀ ρ, Antitone (lam ρ)) : Nonempty (ZIdx lam) := by
  have hmem := hw_mem_nabla (L := ℚ) fun ρ => natW_antitone (hlam ρ)
  have hne : hw ℚ (fun ρ => natW (lam ρ)) ≠ 0 := fun h => by
    simpa [h] using eval_one_hw (L := ℚ) (Φ := Φ) fun ρ => natW (lam ρ)
  have : Nontrivial (nabla ℚ fun ρ => natW (lam ρ)) :=
    ⟨⟨⟨_, hmem⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  exact (zdualBasis ℚ hlam).index_nonempty

/-! ## V2: local membership in fractional ideals -/

section Local

variable {L : Type} [Field L] [NumberField L]

/-- `L` is the fraction field of `O_{L,w}` (Mathlib's instance for valuation subrings). -/
instance isFractionRing_Ow (w : HeightOneSpectrum (𝓞 L)) : IsFractionRing (Ow w) L := by
  have h : IsFractionRing ((w.valuation L).valuationSubring) L := inferInstance
  exact h

/-- The inclusion `O_L → O_{L,w}`. -/
def toOw (w : HeightOneSpectrum (𝓞 L)) : 𝓞 L →+* Ow w :=
  (algebraMap (𝓞 L) L).codRestrict (Ow w) fun r => w.valuation_le_one r

/-- The inclusion `O_L → O_{L,w}` is injective. -/
theorem toOw_injective (w : HeightOneSpectrum (𝓞 L)) : Function.Injective (toOw w) :=
  fun _ _ h => IsFractionRing.injective (𝓞 L) L (congrArg (fun z : Ow w => (z : L)) h)

/-- The inclusion `O_L → O_{L,w}` keeps nonzero divisors. -/
theorem le_comap_toOw (w : HeightOneSpectrum (𝓞 L)) : (𝓞 L)⁰ ≤ (Ow w)⁰.comap (toOw w) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (toOw_injective w)

/-- **The localisation at `w`** of fractional ideals, `J ↦ O_{L,w}·J`: a ring hom (Mathlib's
`FractionalIdeal.extendedHom'`), so it commutes with products, inverses and integer powers. -/
def locw (w : HeightOneSpectrum (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L →+* FractionalIdeal (Ow w)⁰ L :=
  FractionalIdeal.extendedHom' L (le_comap_toOw w)

/-- The map of fraction fields induced by `O_L → O_{L,w}` is the identity of `L`. -/
theorem map_toOw (w : HeightOneSpectrum (𝓞 L)) :
    IsLocalization.map (S := L) L (toOw w) (le_comap_toOw w) = RingHom.id L :=
  IsLocalization.ringHom_ext (𝓞 L)⁰ (RingHom.ext fun r => by
    simp only [RingHom.comp_apply, IsLocalization.map_eq, RingHom.id_apply]
    rfl)

/-- `O_{L,w}·J` is the `O_{L,w}`-span of `J`. -/
theorem mem_locw {w : HeightOneSpectrum (𝓞 L)} {J : FractionalIdeal (𝓞 L)⁰ L} {x : L} :
    x ∈ locw w J ↔ x ∈ Submodule.span (Ow w) (J : Set L) := by
  rw [locw, FractionalIdeal.extendedHom'_apply, FractionalIdeal.mem_extended_iff, map_toOw]
  simp

/-- **(A) Local-global membership**: an element of `O_{L,w}·J` at every `w` lies in `J`. Otherwise the ideal
`{r : r·x ∈ J}` lies in a maximal ideal `w`; but `x = Σ_k o_k y_k` with `y_k ∈ J` and `o_k = n_k/d_k`, `d_k ∉ w`
(`exists_primeCompl_mul_eq_of_integer`), so `Π_k d_k` lies in it. -/
theorem mem_of_forall_mem_locw {J : FractionalIdeal (𝓞 L)⁰ L} {x : L} (h : ∀ w, x ∈ locw w J) : x ∈ J := by
  by_contra hx
  set Q : Ideal (𝓞 L) := (J : Submodule (𝓞 L) L).comap (LinearMap.toSpanSingleton (𝓞 L) L x)
  have hQ : Q ≠ ⊤ := fun hQ => hx (by
    have : (1 : 𝓞 L) ∈ Q := hQ ▸ Submodule.mem_top
    simpa [Q] using this)
  obtain ⟨m, hm, hQm⟩ := Ideal.exists_le_maximal Q hQ
  let w : HeightOneSpectrum (𝓞 L) :=
    ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField L)⟩
  have h1 : (1 : 𝓞 L) ∉ m := fun h1 => hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  have key : ∀ y ∈ Submodule.span (Ow w) (J : Set L), ∃ d : 𝓞 L, d ∉ m ∧ d • y ∈ (J : Submodule (𝓞 L) L) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact ⟨1, h1, by simpa using hy⟩
    | zero => exact ⟨1, h1, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨e, he, hez⟩ := hz
      refine ⟨d * e, fun h => (hm.isPrime.mem_or_mem h).elim hd he, ?_⟩
      have h1' : (d * e) • y = e • (d • y) := by rw [mul_comm, mul_smul]
      rw [smul_add, h1', mul_smul]
      exact add_mem (Submodule.smul_mem _ e hdy) (Submodule.smul_mem _ d hez)
    | smul o y _ hy =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨n', d', hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer w (o : L) o.2
      refine ⟨d' * d, fun h => (hm.isPrime.mem_or_mem h).elim d'.2 hd, ?_⟩
      have : ((d' : 𝓞 L) * d) • (o • y) = n' • (d • y) := by
        have ho : algebraMap (Ow w) L o = (o : L) := rfl
        simp only [Algebra.smul_def, map_mul, ho, ← hnd]
        ring
      rw [this]
      exact Submodule.smul_mem _ n' hdy
  obtain ⟨d, hd, hdx⟩ := key x (mem_locw.1 (h w))
  exact hd (hQm (by simpa [Q] using hdx))

/-- At every `w`, `O_{L,w}·J` is principal (`O_{L,w}` is a principal ideal ring, `FractionalIdeal.isPrincipal`),
on a nonzero generator for `J ≠ 0`. -/
theorem exists_locw_eq (w : HeightOneSpectrum (𝓞 L)) {J : FractionalIdeal (𝓞 L)⁰ L} (hJ : J ≠ 0) :
    ∃ a : L, a ≠ 0 ∧ locw w J = FractionalIdeal.spanSingleton (Ow w)⁰ a := by
  set g := Submodule.IsPrincipal.generator (locw w J : Submodule (Ow w) L)
  have hg : locw w J = FractionalIdeal.spanSingleton (Ow w)⁰ g := by
    apply FractionalIdeal.coeToSubmodule_injective
    show (locw w J : Submodule (Ow w) L) = (FractionalIdeal.spanSingleton (Ow w)⁰ g : Submodule (Ow w) L)
    rw [FractionalIdeal.coe_spanSingleton, Submodule.IsPrincipal.span_singleton_generator]
  refine ⟨g, fun h0 => ?_, hg⟩
  have hne : locw w J ≠ 0 :=
    FractionalIdeal.extended_ne_zero L (le_comap_toOw w) (toOw_injective w) hJ zero_notMem_nonZeroDivisors
  rw [hg, h0, FractionalIdeal.spanSingleton_zero] at hne
  exact hne rfl

/-- **V2, local membership in a product of powers of fractional ideals.** If `O_{L,w}·J_k = O_{L,w}·a_{w,k}` with
`a_{w,k} ≠ 0`, then `x ∈ ∏_k J_k^{e_k}` iff `x·∏_k a_{w,k}^{−e_k} ∈ O_{L,w}` at every `w`: localising is
multiplicative (B), so `O_{L,w}·∏_k J_k^{e_k} = O_{L,w}·∏_k a_{w,k}^{e_k}`, and (A). -/
theorem mem_prod_zpow_iff {ι : Type*} [Fintype ι] (J : ι → FractionalIdeal (𝓞 L)⁰ L) (e : ι → ℤ)
    (a : HeightOneSpectrum (𝓞 L) → ι → L) (ha0 : ∀ w k, a w k ≠ 0)
    (ha : ∀ w k, locw w (J k) = FractionalIdeal.spanSingleton (Ow w)⁰ (a w k)) (x : L) :
    x ∈ ∏ k, J k ^ e k ↔ ∀ w, x * ∏ k, a w k ^ (-e k) ∈ Ow w := by
  have hmem : ∀ w, x ∈ locw w (∏ k, J k ^ e k) ↔ x * ∏ k, a w k ^ (-e k) ∈ Ow w := by
    intro w
    let φ : L →*₀ FractionalIdeal (Ow w)⁰ L :=
      { toFun := FractionalIdeal.spanSingleton (Ow w)⁰
        map_zero' := FractionalIdeal.spanSingleton_zero
        map_one' := FractionalIdeal.spanSingleton_one
        map_mul' := fun x y => (FractionalIdeal.spanSingleton_mul_spanSingleton x y).symm }
    have hloc : locw w (∏ k, J k ^ e k) = φ (∏ k, a w k ^ e k) := by
      rw [map_prod, map_prod]
      simp only [map_zpow₀, ha]
      rfl
    have hc : ∏ k, a w k ^ e k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (ha0 w k)
    have hinv : ∏ k, a w k ^ (-e k) = (∏ k, a w k ^ e k)⁻¹ := by
      simp only [zpow_neg, Finset.prod_inv_distrib]
    rw [hloc, hinv]
    show x ∈ FractionalIdeal.spanSingleton (Ow w)⁰ _ ↔ _
    rw [FractionalIdeal.mem_spanSingleton]
    constructor
    · rintro ⟨z, rfl⟩
      rw [Algebra.smul_def, mul_assoc, mul_inv_cancel₀ hc, mul_one]
      exact z.2
    · intro h
      refine ⟨⟨_, h⟩, ?_⟩
      rw [Algebra.smul_def]
      show x * _ * _ = x
      rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  constructor
  · intro hx w
    exact (hmem w).1 (mem_locw.2 (Submodule.subset_span hx))
  · intro h
    exact mem_of_forall_mem_locw fun w => (hmem w).2 (h w)

end Local

/-! ## The extension `σ(𝔞)·O_L` -/

section Ext

variable {E : Type} [Field E] [NumberField E] {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
/-- `σ` restricted to the rings of integers is injective. -/
theorem mapRingHom_injective (σ : E →+* L) : Function.Injective (RingOfIntegers.mapRingHom σ) :=
  fun _ _ h => IsFractionRing.injective (𝓞 E) E (σ.injective (congrArg (fun z : 𝓞 L => (z : L)) h))

omit [NumberField L] in
/-- `σ` restricted to the rings of integers keeps nonzero divisors. -/
theorem le_comap_mapRingHom (σ : E →+* L) : (𝓞 E)⁰ ≤ (𝓞 L)⁰.comap (RingOfIntegers.mapRingHom σ) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (mapRingHom_injective σ)

/-- **The extension** `𝔞 ↦ σ(𝔞)·O_L` of fractional ideals along `σ : E → L` (Mathlib's
`FractionalIdeal.extendedHom'`, along `σ` on the rings of integers), a ring hom. -/
def extT (σ : E →+* L) : FractionalIdeal (𝓞 E)⁰ E →+* FractionalIdeal (𝓞 L)⁰ L :=
  FractionalIdeal.extendedHom' L (le_comap_mapRingHom σ)

/-- The map of fraction fields induced by `σ` on the rings of integers is `σ`. -/
theorem map_mapRingHom (σ : E →+* L) :
    IsLocalization.map (S := E) L (RingOfIntegers.mapRingHom σ) (le_comap_mapRingHom σ) = σ :=
  IsLocalization.ringHom_ext (𝓞 E)⁰ (RingHom.ext fun r => by
    simp only [RingHom.comp_apply, IsLocalization.map_eq]
    rfl)

/-- `σ(𝔞)·O_L` is the `O_L`-span of `σ(𝔞)`. -/
theorem mem_extT {σ : E →+* L} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {x : L} :
    x ∈ extT σ 𝔞 ↔ x ∈ Submodule.span (𝓞 L) (σ '' (𝔞 : Set E)) := by
  rw [extT, FractionalIdeal.extendedHom'_apply, FractionalIdeal.mem_extended_iff, map_mapRingHom]

/-- `σ(𝔞)·O_L ≠ 0` for `𝔞 ≠ 0`. -/
theorem extT_ne_zero (σ : E →+* L) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) : extT σ 𝔞 ≠ 0 :=
  FractionalIdeal.extended_ne_zero L (le_comap_mapRingHom σ) (mapRingHom_injective σ) h𝔞
    zero_notMem_nonZeroDivisors

/-- `O_{L,w}·(σ(𝔞)·O_L) = O_{L,w}·σ(𝔞)`, as `O_L ⊆ O_{L,w}`. -/
theorem span_Ow_extT (w : HeightOneSpectrum (𝓞 L)) (σ : E →+* L) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    Submodule.span (Ow w) (extT σ 𝔞 : Set L) = Submodule.span (Ow w) (σ '' (𝔞 : Set E)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    have hy' : y ∈ Submodule.span (𝓞 L) (σ '' (𝔞 : Set E)) := mem_extT.1 hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy =>
      have : r • y = toOw w r • y := by
        rw [Algebra.smul_def, Algebra.smul_def]
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ hy
  · refine Submodule.span_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mem_extT.2 (Submodule.subset_span ⟨y, hy, rfl⟩)

/-- **Local generators**: for `𝔞 ≠ 0`, at every `w` some `a ≠ 0` generates `O_{L,w}·σ(𝔞)`, both as the
localisation of `σ(𝔞)·O_L` (for V2) and as a span (for the local bases). -/
theorem exists_gen (w : HeightOneSpectrum (𝓞 L)) (σ : E →+* L) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) :
    ∃ a : L, a ≠ 0 ∧ locw w (extT σ 𝔞) = FractionalIdeal.spanSingleton (Ow w)⁰ a ∧
      Submodule.span (Ow w) (σ '' (𝔞 : Set E)) = Submodule.span (Ow w) {a} := by
  obtain ⟨a, ha0, ha⟩ := exists_locw_eq w (extT_ne_zero σ h𝔞)
  refine ⟨a, ha0, ha, ?_⟩
  rw [← span_Ow_extT]
  ext x
  rw [← mem_locw, ha, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_spanSingleton]

/-- `log |N_{L/ℚ}(σ x)| = [L:E]·log |N_{E/ℚ}(x)|`, `[L:E] = [L:ℚ]/[E:ℚ]`: with `L` an `E`-algebra through `σ`,
`N_{L/ℚ} = N_{E/ℚ} ∘ N_{L/E}` (`Algebra.norm_norm`) and `N_{L/E}(x) = x^{[L:E]}` (`Algebra.norm_algebraMap`). -/
theorem log_abs_norm_map (σ : E →+* L) (x : E) :
    Real.log |(Algebra.norm ℚ (σ x) : ℝ)| = (finrank ℚ L / finrank ℚ E : ℝ) * Real.log |(Algebra.norm ℚ x : ℝ)| := by
  let _ : Algebra E L := σ.toAlgebra
  have h1 : Algebra.norm ℚ (σ x) = Algebra.norm ℚ x ^ finrank E L := by
    have : σ x = algebraMap E L x := rfl
    rw [this, ← Algebra.norm_norm (S := E), Algebra.norm_algebraMap, map_pow]
  have h2 : (finrank ℚ L : ℝ) = finrank ℚ E * finrank E L := by
    rw [← Module.finrank_mul_finrank ℚ E L]
    push_cast
    ring
  have hE : (finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [h1, h2, mul_div_cancel_left₀ _ hE]
  push_cast
  rw [abs_pow, Real.log_pow]

/-- `log N(σ(𝔞)·O_L) = [L:E]·log N(𝔞)`. For an integral ideal `I`, `σ(I)·O_L` is the image of `I`
(`extended_coeIdeal_eq_map`), of norm `N(I)^{[O_L:O_E]}` (`Ideal.absNorm_algebraMap`), and `[O_L:O_E] = [L:E]`
(`IsFractionRing.finrank_eq`); in general `den(𝔞)·𝔞 = num(𝔞)`, and both norms are multiplicative. -/
theorem log_absNorm_extT (σ : E →+* L) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    Real.log (FractionalIdeal.absNorm (extT σ 𝔞) : ℝ) =
      (finrank ℚ L / finrank ℚ E : ℝ) * Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) := by
  let _ : Algebra E L := σ.toAlgebra
  have hint (I : Ideal (𝓞 E)) : FractionalIdeal.absNorm (extT σ (I : FractionalIdeal (𝓞 E)⁰ E)) =
      (Ideal.absNorm I : ℚ) ^ finrank E L := by
    rw [extT, FractionalIdeal.extendedHom'_apply, FractionalIdeal.extended_coeIdeal_eq_map,
      FractionalIdeal.coeIdeal_absNorm]
    have : I.map (RingOfIntegers.mapRingHom σ) = I.map (algebraMap (𝓞 E) (𝓞 L)) := rfl
    rw [this, Ideal.absNorm_algebraMap, IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L]
    push_cast
    rfl
  set J : Ideal (𝓞 E) := Ideal.span {(𝔞.den : 𝓞 E)}
  have hden : (J : FractionalIdeal (𝓞 E)⁰ E) * 𝔞 = 𝔞.num := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.den_mul_self_eq_num']
  have h1 := congrArg (fun I => FractionalIdeal.absNorm (extT σ I)) hden
  have h2 := congrArg FractionalIdeal.absNorm hden
  simp only [map_mul, hint, FractionalIdeal.coeIdeal_absNorm] at h1 h2
  have hJ : (Ideal.absNorm J : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.coe_ne_zero _
  have hX : FractionalIdeal.absNorm (extT σ 𝔞) = FractionalIdeal.absNorm 𝔞 ^ finrank E L := by
    rw [← h2, mul_pow] at h1
    exact mul_left_cancel₀ (pow_ne_zero _ hJ) h1
  have h3 : (finrank ℚ L : ℝ) = finrank ℚ E * finrank E L := by
    rw [← Module.finrank_mul_finrank ℚ E L]
    push_cast
    ring
  have hE : (finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [hX, h3, mul_div_cancel_left₀ _ hE]
  push_cast
  rw [Real.log_pow]

end Ext

/-! ## Lattices of fractional ideals -/

/-- `∏_i 𝔠_i ⊆ K^ι` is an `O_K`-lattice for nonzero fractional ideals `𝔠_i`: finitely generated, and containing a
nonzero multiple of every `e_i`. -/
theorem isLattice_pi {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    {𝔠 : ι → FractionalIdeal (𝓞 K)⁰ K} (h𝔠 : ∀ i, 𝔠 i ≠ 0) :
    (Submodule.pi Set.univ fun i => (𝔠 i : Submodule (𝓞 K) K)).IsLattice K where
  fg := by
    classical
    rw [← Submodule.iSup_map_single]
    exact Submodule.fg_iSup _ fun i => (FractionalIdeal.fg_of_isNoetherianRing le_rfl (𝔠 i)).map _
  span_eq_top := by
    classical
    refine eq_top_iff.2 fun x _ => ?_
    have ha (i : ι) : ∃ a ∈ (𝔠 i : Submodule (𝓞 K) K), a ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot (by rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]; exact h𝔠 i)
    choose a ha ha0 using ha
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : Pi.single i (x i) = (x i * (a i)⁻¹) • (Pi.single i (a i) : ι → K) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [ha0 j]
      · simp [hj]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.mem_pi.2 fun j _ => ?_))
    by_cases hj : j = i
    · subst hj
      simpa using ha j
    · rw [Pi.single_eq_of_ne hj]
      exact (𝔠 j : Submodule (𝓞 K) K).zero_mem

/-! ## V1: `Δ_N` in the coordinates of the dual basis -/

section Lat

variable {E : Type} [Field E] {n : ℕ} {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L]
  [NumberField L] (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ)

/-- **V1.** `Δ_N` in the coordinates of the dual basis `zdual`: `x ∈ deltaLat N` iff `Σ_j x_j·zdual_j ∈ Δ_N`
(tested in every local basis, `DeltaA`), an `O_L`-module as `Δ_N` is closed under sums and `O_L`
(`add_mem_DeltaA`, `smul_mem_DeltaA`). For antitone `λ` it is the image of `Δ_N` under `dcoord`
(`dcoord_symm_apply`). -/
def deltaLat (N : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 L) (ZIdx lam → L) where
  carrier := {x | Fintype.linearCombination L (zdualK L lam) x ∈ DeltaA τ lam N}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem_DeltaA hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact zero_mem_DeltaA
  smul_mem' r x hx := by
    simp only [Set.mem_ofPred_eq] at *
    rw [← algebraMap_smul L r x, map_smul]
    exact smul_mem_DeltaA hx fun w => w.valuation_le_one r

variable {τ lam} in
/-- Membership in `deltaLat N`. -/
theorem mem_deltaLat {N : Submodule (𝓞 E) (Fin n → E)} {x : ZIdx lam → L} :
    x ∈ deltaLat τ lam N ↔ ∑ j, x j • zdualK L lam j ∈ DeltaA τ lam N := by
  rw [← Fintype.linearCombination_apply]
  rfl

/-- The coordinates of a combination of the dual basis: `dc_j(Σ_k x_k·zdual_k) = x_j` (`fock_zdualK_zbK`). -/
theorem dc_sum (x : ZIdx lam → L) (j : ZIdx lam) : dc L lam j (∑ k, x k • zdualK L lam k) = x j := by
  rw [dc, fock_sum_left]
  simp only [fock_smul_left, fock_zdualK_zbK, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [mul_div_assoc, div_self (by simpa using (kappa_pos lam).ne'), mul_one]

variable {lam} in
/-- `zdual_k ∈ ∇_L` for antitone `λ`. -/
theorem zdualK_mem (hlam : ∀ ρ, Antitone (lam ρ)) (k : ZIdx lam) :
    zdualK L lam k ∈ nabla L fun ρ => natW (lam ρ) :=
  zdualBasis_apply L hlam k ▸ (zdualBasis L hlam k).2

/-- A diagonal twist on a combination of the dual basis: `zdual_k`, of row weight `zwt k`, is scaled by
`∏_{ρ,i} a_{ρ,i}^{(zwt k)_{ρ,i} + s_ρ}` (`twist_diagonal_of_isWH`). -/
theorem twist_diagonal_sum (a : Φ → Fin n → L) (ha : ∀ ρ i, a ρ i ≠ 0) (x : ZIdx lam → L) :
    twist lam (fun ρ => Matrix.diagonal (a ρ)) (∑ k, x k • zdualK L lam k) =
      ∑ k, (x k * ∏ ρ, ∏ i, a ρ i ^ ((zwt lam k ρ i : ℤ) + detShift (lam ρ))) • zdualK L lam k := by
  simp only [twist, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := twist_diagonal_of_isWH lam (zdualK_isWH L lam k) a
  rw [twist] at h
  rw [h, smul_smul]
  refine congrArg (· • zdualK L lam k) (congrArg (x k * ·) ?_)
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_add₀ (ha ρ i), zpow_natCast, mul_comm]

omit [Fintype Φ] [DecidableEq Φ] in
/-- **The diagonal local basis of `D(I)`**: if `O_{L,w}·σ(I_i) = O_{L,w}·a_i` with `a_i ≠ 0`, then `diag(a)` is a
local basis of `O_{L,w}·σ(∏_i I_i)`. -/
theorem isLocalBasis_diagonal {w : HeightOneSpectrum (𝓞 L)} {σ : E →+* L} {I : Fin n → Submodule (𝓞 E) E}
    {a : Fin n → L} (ha0 : ∀ i, a i ≠ 0)
    (ha : ∀ i, Submodule.span (Ow w) (σ '' (I i : Set E)) = Submodule.span (Ow w) {a i}) :
    IsLocalBasis w σ (Submodule.pi Set.univ I) (Matrix.diagonal a) := by
  classical
  refine ⟨by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => ha0 i, ?_⟩
  have hcol : (Set.range fun j i => Matrix.diagonal a i j) = Set.range fun j => (Pi.single j (a j) : Fin n → L) := by
    congr 1
    funext j i
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, Pi.single_eq_of_ne h]
  rw [hcol]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show (fun i => σ (v i)) ∈ Submodule.span (Ow w) _
    rw [← Finset.univ_sum_single (fun i => σ (v i))]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hvj : σ (v j) ∈ Submodule.span (Ow w) {a j} :=
      ha j ▸ Submodule.subset_span ⟨v j, hv j (Set.mem_univ j), rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hvj
    rw [← hc]
    have : (Pi.single j (c • a j) : Fin n → L) = c • (Pi.single j (a j) : Fin n → L) := by
      ext i
      by_cases h : i = j
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : a j ∈ Submodule.span (Ow w) (σ '' (I j : Set E)) := ha j ▸ Submodule.mem_span_singleton_self _
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.single (Ow w) (fun _ : Fin n => L) j) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨Pi.single j y, Submodule.mem_pi.2 fun i _ => ?_, ?_⟩
    · by_cases h : i = j
      · subst h
        simpa using hy
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    · funext i
      by_cases h : i = j
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]

/-- `Δ_N` in some local basis lies in `Δ_N` in every local basis, with no hypothesis on `N`: two local bases
differ by `GL_n(O_{L,w})` (`exists_mul_eq_of_span_le`), and W6 applies (the argument of `DeltaN_eq_DeltaA`,
which needs `Sand` only for the converse). -/
theorem DeltaN_subset_DeltaA {N : Submodule (𝓞 E) (Fin n → E)} :
    DeltaN τ lam N ⊆ DeltaA τ lam N := by
  intro F hF
  refine ⟨hF.1, fun w C' hC' => ?_⟩
  obtain ⟨C, hC, hCF⟩ := hF.2 w
  have key : ∀ σ, ∃ U V : Matrix (Fin n) (Fin n) L, (∀ i j, U i j ∈ Ow w) ∧ (∀ i j, V i j ∈ Ow w) ∧
      U * V = 1 ∧ C' σ = C σ * U := by
    intro σ
    obtain ⟨U, hU, hCU⟩ := exists_mul_eq_of_span_le (le_of_eq ((hC' σ).2.symm.trans (hC σ).2))
    obtain ⟨V, hV, hCV⟩ := exists_mul_eq_of_span_le (le_of_eq ((hC σ).2.symm.trans (hC' σ).2))
    refine ⟨U, V, hU, hV, ?_, hCU⟩
    have hinv : (C σ)⁻¹ * C σ = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hC σ).1)
    calc U * V = (C σ)⁻¹ * C σ * (U * V) := by rw [hinv, Matrix.one_mul]
      _ = (C σ)⁻¹ * C σ := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C σ), ← hCU, ← hCV]
      _ = 1 := hinv
  choose U V hU hV hUV hCU using key
  have e : twist lam C' F = twist lam U (twist lam C F) := by
    rw [twist_twist]
    exact congrArg (fun D => twist lam D F) (funext hCU)
  rw [e]
  exact (twist_mem_Delta_iff lam hU hV hUV).2 hCF

/-! ## V4: transport by `GL_n(E)` -/

variable {lam} in
/-- `R_γ` in the dual basis: `Σ_j (R_γ x)_j·zdual_j = ρ_λ(γ)(Σ_j x_j·zdual_j)`. -/
theorem sum_rhoMat (hlam : ∀ ρ, Antitone (lam ρ)) (γ : GL (Fin n) E) (x : ZIdx lam → L) :
    ∑ j, rhoMat τ hlam γ x j • zdualK L lam j = rho τ lam γ (∑ j, x j • zdualK L lam j) := by
  rw [← dcoord_symm_apply L hlam, ← dcoord_symm_apply L hlam]
  simp [rhoMat, rhoVV_apply]

variable {lam} in
/-- `R_γ⁻¹` in the dual basis: `Σ_j (R_γ⁻¹ x)_j·zdual_j = ρ_λ(γ⁻¹)(Σ_j x_j·zdual_j)`. -/
theorem sum_rhoMat_symm (hlam : ∀ ρ, Antitone (lam ρ)) (γ : GL (Fin n) E) (x : ZIdx lam → L) :
    ∑ j, (rhoMat τ hlam γ).symm x j • zdualK L lam j = rho τ lam γ⁻¹ (∑ j, x j • zdualK L lam j) := by
  rw [← dcoord_symm_apply L hlam, ← dcoord_symm_apply L hlam]
  simp [rhoMat, rhoVV_apply]

variable {lam} in
/-- **V4, transport by `GL_n(E)`**: `Δ_{γN} = R_γ(Δ_N)`, with `R_γ = rhoMat γ` the matrix of `ρ_λ(γ)` in the dual
basis: `ρ_λ(γ)` moves `Δ_N` into `Δ_{γN}`, and `ρ_λ(γ⁻¹)` back (`rho_mem_DeltaA`). The shape of K1
(`KLattice.degK_map`). -/
theorem deltaLat_map (hlam : ∀ ρ, Antitone (lam ρ)) (γ : GL (Fin n) E) (N : Submodule (𝓞 E) (Fin n → E)) :
    deltaLat τ lam (N.map (act γ)) =
      (deltaLat τ lam N).map ((rhoMat τ hlam γ).toLinearMap.restrictScalars (𝓞 L)) := by
  have hN : (N.map (act γ)).map (act γ⁻¹) = N := by
    rw [← Submodule.map_comp]
    convert Submodule.map_id N
    exact LinearMap.ext fun x => act_inv_act γ x
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · intro hx
    refine ⟨(rhoMat τ hlam γ).symm x, ?_, LinearEquiv.apply_symm_apply _ x⟩
    rw [mem_deltaLat, sum_rhoMat_symm]
    have h := rho_mem_DeltaA γ⁻¹ (mem_deltaLat.1 hx)
    rwa [hN] at h
  · rintro ⟨y, hy, rfl⟩
    rw [mem_deltaLat, sum_rhoMat]
    exact rho_mem_DeltaA γ (mem_deltaLat.1 hy)

/-! ## V3: diagonal lattices -/

variable [NumberField E]

/-- `𝔅(μ) = ∏_{ρ,i} (τ_ρ(𝔞_i)·O_L)^{−(μ_{ρ,i} + s_ρ)}`, `s_ρ = λ_{ρ,n−1}`: the ideal of the coordinates of row
weight `μ` of `Δ_{D(𝔞)}`. -/
def bIdeal (𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E) (μ : Φ → Fin n → ℕ) : FractionalIdeal (𝓞 L)⁰ L :=
  ∏ ρ, ∏ i, extT (τ ρ) (𝔞 i) ^ (-((μ ρ i : ℤ) + detShift (lam ρ)))

omit [DecidableEq Φ] in
/-- `𝔅(μ) ≠ 0` for nonzero `𝔞_i`. -/
theorem bIdeal_ne_zero {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : ∀ i, 𝔞 i ≠ 0) (μ : Φ → Fin n → ℕ) :
    bIdeal τ lam 𝔞 μ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (extT_ne_zero _ (h𝔞 i))

variable {lam} in
/-- **V3, membership.** `x ∈ Δ_{D(𝔞)}` iff `x_j ∈ 𝔅(zwt j)` for every `j`. At each `w`, `diag(a_{w,ρ,i})`, with
`a_{w,ρ,i}` a generator of `O_{L,w}·τ_ρ(𝔞_i)`, is a local basis (`isLocalBasis_diagonal`), which scales the
coordinate `x_j` by `∏_{ρ,i} a_{w,ρ,i}^{(zwt j)_{ρ,i} + s_ρ}` (`twist_diagonal_sum`); `Δ_{O_{L,w}}` is read on the
coordinates (`mem_Delta_iff`, `dc_sum`), other local bases give the same (`DeltaN_subset_DeltaA`), and V2 turns
the local conditions into `x_j ∈ 𝔅(zwt j)`. -/
theorem mem_deltaLat_diagLat (hlam : ∀ ρ, Antitone (lam ρ)) {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E}
    (h𝔞 : ∀ i, 𝔞 i ≠ 0) (x : ZIdx lam → L) :
    x ∈ deltaLat τ lam (diagLat 𝔞) ↔ ∀ j, x j ∈ bIdeal τ lam 𝔞 (zwt lam j) := by
  choose a ha0 hloc hspan using fun (w : HeightOneSpectrum (𝓞 L)) (ρ : Φ) (i : Fin n) =>
    exists_gen w (τ ρ) (h𝔞 i)
  have hbasis : ∀ w ρ, IsLocalBasis w (τ ρ) (diagLat 𝔞) (Matrix.diagonal (a w ρ)) := fun w ρ =>
    isLocalBasis_diagonal (ha0 w ρ) (hspan w ρ)
  have hB : ∀ j, x j ∈ bIdeal τ lam 𝔞 (zwt lam j) ↔
      ∀ w, x j * ∏ ρ, ∏ i, a w ρ i ^ ((zwt lam j ρ i : ℤ) + detShift (lam ρ)) ∈ Ow w := by
    intro j
    have h := mem_prod_zpow_iff (fun p : Φ × Fin n => extT (τ p.1) (𝔞 p.2))
      (fun p => -((zwt lam j p.1 p.2 : ℤ) + detShift (lam p.1))) (fun w p => a w p.1 p.2)
      (fun w p => ha0 w p.1 p.2) (fun w p => hloc w p.1 p.2) (x j)
    simp only [neg_neg, Fintype.prod_prod_type] at h
    exact h
  have hnab : ∑ k, x k • zdualK L lam k ∈ nabla L fun ρ => natW (lam ρ) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (zdualK_mem hlam k)
  constructor
  · intro hx j
    refine (hB j).2 fun w => ?_
    have h1 := (mem_deltaLat.1 hx).2 w _ (hbasis w)
    rw [twist_diagonal_sum lam (a w) (ha0 w) x, mem_Delta_iff] at h1
    simpa only [dc_sum] using h1.2 j
  · intro hx
    refine mem_deltaLat.2 (DeltaN_subset_DeltaA τ lam ⟨hnab, fun w => ⟨_, hbasis w, ?_⟩⟩)
    rw [twist_diagonal_sum lam (a w) (ha0 w) x, mem_Delta_iff]
    refine ⟨Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (zdualK_mem hlam k), fun j => ?_⟩
    rw [dc_sum]
    exact (hB j).1 (hx j) w

variable {lam} in
/-- **V3, diagonal lattices.** `Δ_{D(𝔞)} = ∏_j 𝔅(zwt j)` in the coordinates of the dual basis, the shape of K2
(`KLattice.degK_pi`). -/
theorem deltaLat_diagLat (hlam : ∀ ρ, Antitone (lam ρ)) {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E}
    (h𝔞 : ∀ i, 𝔞 i ≠ 0) :
    deltaLat τ lam (diagLat 𝔞) = Submodule.pi Set.univ fun j => (bIdeal τ lam 𝔞 (zwt lam j) : Submodule (𝓞 L) L) := by
  ext x
  simp only [mem_deltaLat_diagLat τ hlam h𝔞, Submodule.mem_pi, Set.mem_univ, true_implies, FractionalIdeal.mem_coe]

variable {lam} in
/-- **V3 for `O_E^n`**: `Δ_{O_E^n} = O_L^{ZIdx}`, as `𝔅(μ) = 1` for `𝔞 = 1`. -/
theorem deltaLat_intVec (hlam : ∀ ρ, Antitone (lam ρ)) :
    deltaLat τ lam (intVec E n) = Submodule.pi Set.univ fun _ => 1 := by
  have hD : intVec E n = diagLat fun _ => (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    simp only [intVec, diagLat, FractionalIdeal.coe_one]
  have hb : ∀ μ, bIdeal τ lam (fun _ => 1) μ = 1 := fun μ => by
    simp only [bIdeal, map_one, one_zpow, Finset.prod_const_one]
  rw [hD, deltaLat_diagLat τ hlam fun _ => one_ne_zero]
  simp only [hb, FractionalIdeal.coe_one]

variable {lam} in
/-- `Δ_{D(𝔞)}` is an `O_L`-lattice for nonzero `𝔞_i`. -/
theorem isLattice_deltaLat_diagLat (hlam : ∀ ρ, Antitone (lam ρ)) {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E}
    (h𝔞 : ∀ i, 𝔞 i ≠ 0) : (deltaLat τ lam (diagLat 𝔞)).IsLattice L := by
  rw [deltaLat_diagLat τ hlam h𝔞]
  exact isLattice_pi fun j => bIdeal_ne_zero τ lam h𝔞 _

variable {lam} in
/-- **`Δ_N` is an `O_L`-lattice** for every `O_E`-lattice `N`: `N = γD(𝔞)` (P1, `exists_pseudo`), so
`Δ_N = R_γ(∏_j 𝔅(zwt j))` (V4, V3). -/
theorem isLattice_deltaLat (hlam : ∀ ρ, Antitone (lam ρ)) (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] :
    (deltaLat τ lam N).IsLattice L := by
  obtain ⟨𝔞, γ, h𝔞, rfl⟩ := exists_pseudo N
  rw [deltaLat_map τ hlam]
  have := isLattice_deltaLat_diagLat τ hlam h𝔞
  exact KLattice.isLattice_map _ (rhoMat τ hlam γ)

variable {lam} in
/-- **V1.** The hermitian `O_L`-lattice `Δ_N`, in the coordinates of the dual basis, with the constant metric `Γ`
at every place: on the rational `zdual`, the Fock form at every embedding is `κ·Γ` (`fock_map_sum_zdualK`). -/
def deltaK (hlam : ∀ ρ, Antitone (lam ρ)) (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] :
    KLattice L (ZIdx lam) :=
  haveI := isLattice_deltaLat τ hlam N
  ⟨deltaLat τ lam N, fun _ => ((Γ lam).map (algebraMap ℚ ℝ)).map Complex.ofReal,
    fun _ => posDef_map_ofReal (posDef_Γ lam)⟩

variable {lam} in
/-- The lattice of `deltaK N` is `deltaLat N`. -/
@[simp] theorem deltaK_M (hlam : ∀ ρ, Antitone (lam ρ)) (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] :
    (deltaK τ hlam N).M = deltaLat τ lam N := rfl

variable {lam} in
/-- The metric of `deltaK N` is `Γ` at every place. -/
@[simp] theorem deltaK_G (hlam : ∀ ρ, Antitone (lam ρ)) (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E]
    (v : HermitianLattice.Pl L) :
    (deltaK τ hlam N).G v = ((Γ lam).map (algebraMap ℚ ℝ)).map Complex.ofReal := rfl

/-! ## V7: the standard lattice -/

/-- `det Γ` over `ℝ` is the rational `det Γ`. -/
theorem det_Γ_real : ((Γ lam).map (algebraMap ℚ ℝ)).det = ((Γ lam).det : ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_ratCast]

variable {lam} in
/-- **V7.** `μ(Δ_{O_E^n}) = −log det Γ/(2r) − archShift(L)/2`, `archShift(L) = log|d_L|/[L:ℚ] − log 2` written
out: K3 (`KLattice.muK_const`) with V3 for `O_E^n`. -/
theorem muK_deltaK_intVec [IsTotallyComplex L] (hlam : ∀ ρ, Antitone (lam ρ)) :
    KLattice.muK (deltaK τ hlam (intVec E n)) = -Real.log ((Γ lam).det : ℝ) / (2 * Fintype.card (ZIdx lam)) -
      (Real.log |(discr L : ℝ)| / finrank ℚ L - Real.log 2) / 2 := by
  have := nonempty_ZIdx hlam
  rw [KLattice.muK_const _ ((Γ lam).map (algebraMap ℚ ℝ)) (deltaLat_intVec τ hlam) fun _ => rfl, det_Γ_real]

variable {lam} in
/-- **V7 in the archive's units**: `μ_arch(Δ_{O_E^n}) = 2μ + archShift(L) = −log det Γ/r`; the field constant
cancels. -/
theorem muArch_deltaK_intVec [IsTotallyComplex L] (hlam : ∀ ρ, Antitone (lam ρ)) :
    2 * KLattice.muK (deltaK τ hlam (intVec E n)) - Real.log 2 + Real.log |(discr L : ℝ)| / finrank ℚ L =
      -Real.log ((Γ lam).det : ℝ) / Fintype.card (ZIdx lam) := by
  rw [muK_deltaK_intVec τ hlam]
  have := nonempty_ZIdx hlam
  have hc : (Fintype.card (ZIdx lam) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp
  ring

/-! ## The metric of `deltaK` -/

/-- **The metric of `deltaK`**: at every embedding `σ : L → ℂ`, the normalised Fock form of `Σ_i x_i·zdual_i` and
`Σ_j y_j·zdual_j` is `Σ_{i,j} conj(σx_i)·σy_j·Γ_{ij}`: the `zdual` are rational, so
`fock(zdual_i, zdual_j) = ⟨zdual_i, zdual_j⟩/κ = Γ_{ij}` (`fockWith_star`, `fock_zdual_zdual`), and the form is
sesquilinear (`fock_sum_smul`). For the blocks of the cut (C2). -/
theorem fock_map_sum_zdualK (σ : L →+* ℂ) (x y : ZIdx lam → L) :
    fock (fun ρ => natW (lam ρ)) (map σ (∑ i, x i • zdualK L lam i)) (map σ (∑ j, y j • zdualK L lam j)) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (x i)) * σ (y j) * ((Γ lam i j : ℚ) : ℂ) := by
  have hσ : σ.comp (algebraMap ℚ L) = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  have hmap (z : ZIdx lam → L) : map σ (∑ i, z i • zdualK L lam i) = ∑ i, C (σ (z i)) * zdualK ℂ lam i := by
    simp only [map_sum, smul_eq_C_mul, map_mul, map_C, zdualK, map_map, hσ]
  rw [hmap, hmap, fock_sum_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hc : (starRingEnd ℂ).comp (algebraMap ℚ ℂ) = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  rw [fock, fockWith_hw_C, zdualK, zdualK, fockWith_star, map_map, hc, ← map_fockWith_id, fock_zdual_zdual]
  have hκ : (kappa lam : ℂ) ≠ 0 := by exact_mod_cast (kappa_pos lam).ne'
  simp only [map_mul, eq_ratCast]
  field_simp

/-! ## V5: the exact degree of `Δ_N` -/

omit [NumberField E] in
/-- `log |N_{K/ℚ}(x^e)| = e·log |N_{K/ℚ}(x)|` for `e ∈ ℤ`. -/
theorem log_abs_norm_zpow {K : Type} [Field K] [NumberField K] (x : K) (e : ℤ) :
    Real.log |(Algebra.norm ℚ (x ^ e) : ℝ)| = e * Real.log |(Algebra.norm ℚ x : ℝ)| := by
  let N : K →*₀ ℚ := { Algebra.norm ℚ with map_zero' := Algebra.norm_zero }
  have : Algebra.norm ℚ (x ^ e) = Algebra.norm ℚ x ^ e := map_zpow₀ N x e
  rw [this]
  push_cast
  rw [abs_zpow, Real.log_zpow]

variable {lam} in
/-- **V5, the `GL_n(E)` part.** `deg Δ_{γM} = deg Δ_M + [L:E]·C_λ·log |N_{E/ℚ}(det γ)|`: K1 with V4,
`det R_γ = ∏_ρ τ_ρ(det γ)^{−cExp ρ}` (`det_rhoMat`) and `log |N_{L/ℚ}(τ_ρ x)| = [L:E]·log |N_{E/ℚ}(x)|`. -/
theorem degK_deltaK_map [IsTotallyComplex L] (hlam : ∀ ρ, Antitone (lam ρ)) (M : Submodule (𝓞 E) (Fin n → E))
    [M.IsLattice E] (γ : GL (Fin n) E) [(M.map (act γ)).IsLattice E] :
    KLattice.degK (deltaK τ hlam (M.map (act γ))) = KLattice.degK (deltaK τ hlam M) +
      (finrank ℚ L / finrank ℚ E : ℝ) * cLam lam *
        Real.log |(Algebra.norm ℚ (γ : Matrix (Fin n) (Fin n) E).det : ℝ)| := by
  rw [KLattice.degK_map (deltaK τ hlam M) (deltaK τ hlam (M.map (act γ))) (rhoMat τ hlam γ)
    (deltaLat_map τ hlam γ M) rfl, det_rhoMat, map_prod, Rat.cast_prod, Finset.abs_prod,
    Real.log_prod fun ρ _ => ?_]
  · have hterm (ρ : Φ) : Real.log |((Algebra.norm ℚ (τ ρ (γ : Matrix (Fin n) (Fin n) E).det ^ (-cExp lam ρ)) : ℚ) : ℝ)|
        = -((cExp lam ρ : ℝ) * ((finrank ℚ L / finrank ℚ E : ℝ) *
          Real.log |(Algebra.norm ℚ (γ : Matrix (Fin n) (Fin n) E).det : ℝ)|)) := by
      rw [log_abs_norm_zpow, log_abs_norm_map]
      push_cast
      ring
    simp only [hterm, Finset.sum_neg_distrib, cLam, Int.cast_sum, ← Finset.sum_mul]
    ring
  · rw [abs_ne_zero, Rat.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]
    exact zpow_ne_zero _ ((map_ne_zero _).2 (Matrix.isUnits_det_units γ).ne_zero)

/-- `cExp ρ = Σ_j ((zwt j)_{ρ,i} + s_ρ)` for every row `i`, as the multiplicities do not depend on `i`
(`wtMult_eq`). -/
theorem cExp_eq_sum (ρ : Φ) (i : Fin n) :
    cExp lam ρ = ∑ j, ((zwt lam j ρ i : ℤ) + detShift (lam ρ)) := by
  have hn : 0 < n := i.pos
  simp only [cExp, hn, ↓reduceDIte]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    wtMult_eq lam ρ ⟨0, hn⟩ i, wtMult]
  push_cast
  ring

/-- `Σ_j Σ_{ρ,i} ((zwt j)_{ρ,i} + s_ρ)·A_i = C_λ·Σ_i A_i` (`cExp_eq_sum`). -/
theorem sum_zwt_mul (A : Fin n → ℝ) :
    ∑ j, ∑ ρ, ∑ i, (((zwt lam j ρ i : ℤ) + detShift (lam ρ) : ℤ) : ℝ) * A i = cLam lam * ∑ i, A i := by
  rw [Finset.sum_comm]
  rw [cLam, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, cExp_eq_sum lam ρ i, Int.cast_sum]

omit [DecidableEq Φ] in
/-- `log N(𝔅(μ)) = −[L:E]·Σ_{ρ,i} (μ_{ρ,i} + s_ρ)·log N(𝔞_i)`: the norm is multiplicative, and
`log N(τ_ρ(𝔞)·O_L) = [L:E]·log N(𝔞)` (`log_absNorm_extT`). -/
theorem log_absNorm_bIdeal {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : ∀ i, 𝔞 i ≠ 0) (μ : Φ → Fin n → ℕ) :
    Real.log (FractionalIdeal.absNorm (bIdeal τ lam 𝔞 μ) : ℝ) = -((finrank ℚ L / finrank ℚ E : ℝ) *
      ∑ ρ, ∑ i, (((μ ρ i : ℤ) + detShift (lam ρ) : ℤ) : ℝ) * Real.log (FractionalIdeal.absNorm (𝔞 i) : ℝ)) := by
  have hne (ρ : Φ) (i : Fin n) (e : ℤ) : (FractionalIdeal.absNorm (extT (τ ρ) (𝔞 i) ^ e) : ℝ) ≠ 0 := by
    rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact zpow_ne_zero _ (extT_ne_zero _ (h𝔞 i))
  rw [bIdeal, map_prod, Rat.cast_prod, Real.log_prod fun ρ _ => ?_]
  · simp only [map_prod, Rat.cast_prod]
    rw [Finset.sum_congr rfl fun ρ _ => Real.log_prod fun i _ => hne ρ i _]
    simp only [map_zpow₀, Rat.cast_zpow, Real.log_zpow, log_absNorm_extT]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  · rw [map_prod, Rat.cast_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hne ρ i _

variable {lam} in
/-- **V5, the diagonal part.** `deg Δ_{D(𝔞)} = deg Δ_{O_E^n} + [L:E]·C_λ·Σ_i log N(𝔞_i)`: K2 with V3, and the
sum over `j` of the exponents of `𝔅(zwt j)` (`sum_zwt_mul`). -/
theorem degK_deltaK_diagLat [IsTotallyComplex L] (hlam : ∀ ρ, Antitone (lam ρ))
    {𝔞 : Fin n → FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : ∀ i, 𝔞 i ≠ 0) [(diagLat 𝔞).IsLattice E] :
    KLattice.degK (deltaK τ hlam (diagLat 𝔞)) = KLattice.degK (deltaK τ hlam (intVec E n)) +
      (finrank ℚ L / finrank ℚ E : ℝ) * cLam lam * ∑ i, Real.log (FractionalIdeal.absNorm (𝔞 i) : ℝ) := by
  rw [KLattice.degK_pi (deltaK τ hlam (diagLat 𝔞)) (deltaK τ hlam (intVec E n))
    (fun j => bIdeal τ lam 𝔞 (zwt lam j)) (deltaLat_diagLat τ hlam h𝔞) (deltaLat_intVec τ hlam) rfl]
  have h := sum_zwt_mul lam fun i => Real.log (FractionalIdeal.absNorm (𝔞 i) : ℝ)
  simp only [log_absNorm_bIdeal τ lam h𝔞, Finset.sum_neg_distrib, ← Finset.mul_sum, h]
  ring

variable {lam} in
/-- **V5, the exact degree of `Δ_N`.** For every `O_E`-lattice `N ⊆ E^n`,
`deg Δ_N = deg Δ_{O_E^n} + [L:E]·C_λ·(deg O_E^n − deg N)`, `[L:E] = [L:ℚ]/[E:ℚ]`: `N = γD(𝔞)` (P1), the two
parts (`degK_deltaK_map`, `degK_deltaK_diagLat`), and P2 (`degE_pseudo`). -/
theorem degK_deltaK [IsCMField E] [IsTotallyComplex L] (hlam : ∀ ρ, Antitone (lam ρ))
    (N : Submodule (𝓞 E) (Fin n → E)) [N.IsLattice E] :
    KLattice.degK (deltaK τ hlam N) = KLattice.degK (deltaK τ hlam (intVec E n)) +
      (finrank ℚ L / finrank ℚ E : ℝ) * cLam lam * (degE (intVec E n) - degE N) := by
  obtain ⟨𝔞, γ, h𝔞, rfl⟩ := exists_pseudo N
  have : (diagLat 𝔞).IsLattice E := isLattice_diagLat h𝔞
  rw [degK_deltaK_map τ hlam, degK_deltaK_diagLat τ hlam h𝔞, degE_pseudo _ rfl]
  ring

/-! ## V6: unimodular lattices and the attached lattices -/

variable {lam} in
/-- **V6, unimodular lattices**: `deg Δ_N = deg Δ_{O_E^n}` (V5 with P5, `degE_of_unimodular`). -/
theorem degK_deltaK_of_unimodular [IsCMField E] [IsTotallyComplex L] (hlam : ∀ ρ, Antitone (lam ρ))
    {N : Submodule (𝓞 E) (Fin n → E)} [N.IsLattice E] (hN : IsUnimodular N) :
    KLattice.degK (deltaK τ hlam N) = KLattice.degK (deltaK τ hlam (intVec E n)) := by
  rw [degK_deltaK τ hlam N, degE_of_unimodular hN, sub_self, mul_zero, add_zero]

variable {lam} in
/-- **V6, the attached lattices**: for a good `d`, `deg Δ_{Lsh d} = deg Δ_{O_E^n} − [L:E]·C_λ·Σ_{P∈ST} log N(P)`
(V5 with P7, `degE_Lsh`), independent of `d`. -/
theorem degK_deltaK_Lsh [IsCMField E] [IsTotallyComplex L] (hlam : ∀ ρ, Antitone (lam ρ))
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Good) [(Lsh d).IsLattice E] :
    KLattice.degK (deltaK τ hlam (Lsh d)) = KLattice.degK (deltaK τ hlam (intVec E n)) -
      (finrank ℚ L / finrank ℚ E : ℝ) * cLam lam * ∑ P ∈ ST, Real.log (Ideal.absNorm P.asIdeal : ℝ) := by
  rw [degK_deltaK τ hlam, degE_Lsh hd]
  ring

variable {lam} in
/-- **V6 in slopes**: `μ(Δ_{Lsh d}) = μ(Δ_{O_E^n}) − (ΣΛ/(n·[E:ℚ]))·Σ_{P∈ST} log N(P)`, `ΣΛ = Σ_{ρ,i} λ_{ρ,i}`:
`rk = [L:ℚ]·r` (`rk_top`) and `n·C_λ = r·ΣΛ` (`n_mul_cLam`). -/
theorem muK_deltaK_Lsh [IsCMField E] [IsTotallyComplex L] (hlam : ∀ ρ, Antitone (lam ρ))
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Good) [(Lsh d).IsLattice E] :
    KLattice.muK (deltaK τ hlam (Lsh d)) = KLattice.muK (deltaK τ hlam (intVec E n)) -
      (∑ ρ, ∑ i, (lam ρ i : ℝ)) / (n * finrank ℚ E) * ∑ P ∈ ST, Real.log (Ideal.absNorm P.asIdeal : ℝ) := by
  have := nonempty_ZIdx hlam
  simp only [KLattice.muK, KLattice.rkK, KLattice.rk_top]
  rw [degK_deltaK_Lsh τ hlam hd]
  have hC : (n : ℝ) * cLam lam = Fintype.card (ZIdx lam) * ∑ ρ, ∑ i, (lam ρ i : ℝ) := by
    exact_mod_cast n_mul_cLam hlam
  have hr : (Fintype.card (ZIdx lam) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hL : (finrank ℚ L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hE : (finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [cLam, cExp, detShift]
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    push_cast
    field_simp
    linear_combination (-(finrank ℚ L : ℝ) * ∑ P ∈ ST, Real.log (Ideal.absNorm P.asIdeal : ℝ)) * hC

end Lat

end

end HermForms
