import HermClasses
import WeylFock
import KLattice

/-!
# Forms on decorated lattices, the Petersson form, the ramified cut and the source lattices

Layer L4 of the sharp frontier (`docs/rh-rebuild.md`): the algebraic modular forms on the classes of decorated
lattices (`HermClasses`) with values in the coefficient systems of `WeylFock`, their integral forms, the Petersson
form, the ramified cut at `T`, and the source of a word as a hermitian `O_L`-lattice (`KLattice`), which L6.5 reads.
Generic in `E`, `L`, `Φ`, `τ`, the level group `Λ_SG`, its character `χ_SG` and the weight `λ`.

**Forms** (L4.1). The spec's `Forms_j(λ)` are the functions `φ : Cl → VV_L(λ)` with `chr(g)·ρ_λ(γ_g)φ(c) = φ(c)` for
`g ∈ Stab(c)`, or equivalently the `𝒢`-equivariant functions on the decorated lattices `D`. We take the second:
`F : D → VV_L(λ)` with `F(g·d) = chr(g)·ρ_λ(γ_g)F(d)` (`Forms`, an `L`-submodule of `Fn = (D → L[x])`). For
`g ∈ Stab(d)` this is the spec's condition, and the diamond operators are then plain precomposition. The integral
forms `M` (`Mint`) have `F(rep c) ∈ Δ_{Lsh(rep c)}(λ)` for every class `c` (`DeltaN` is a set, so `Mint` is one too).
The Petersson form is `H(F, G) = Σᶠ_c |Stab(c)|⁻¹·⟨F(rep c), G(rep c)⟩` (`pet`), with `⟨·,·⟩` the normalised Fock form.

**The Petersson form at a place.** At an embedding `σ : L →+* ℂ` the metric is the complex Petersson form
`H_σ(F, G) = Σᶠ_c |Stab(c)|⁻¹·⟨σF(rep c), σG(rep c)⟩` (`petAt`): `σ` applied coefficientwise, then the Fock form over
`ℂ`, conjugation in `ℂ` (the archive's metric at every place). It is hermitian at every `σ` (`conj_petAt`), and
`σ(H)` where the star of `L` is conjugation at `σ` (`petAt_eq_map`). Elsewhere `σ(H)` need not be hermitian, and on
`V ⊗_σ ℂ` it depends on the basis (a basis change `P` gives `σ(P)ᴴσ(H)σ(P)` only for `P` with entries where
`σ ∘ star = conj ∘ σ`), so the frontier pins `H_σ`, not `σ(H)`.

**The ramified cut** (L4.2, L4.3). The diamond operators `dia_a` keep `D` (`diaPt`), and act on functions by
`⟨a⟩F = F ∘ dia_a` (`dOp`). `Nm_P = Σ_{a ∈ (O_E/P)ˣ} ⟨a⟩_P` (`Nm`, a `finsum`: no finiteness of the residue field is
needed to state). The cut is `V_ω = Forms ∩ ⋂_{P ∈ ST} ker Nm_P` (`Vω`), `M_ω = M ∩ V_ω` (`Mω`), and
`H_{ω,σ} = H_σ|_{V_ω}` (`Hω`). At step 0 all stabilisers are trivial, so `H_ω` has weights 1; nothing here uses it.

**The source** (L6.5). In Mathlib's basis of a finite-dimensional `V_ω` (`Module.finBasis`), `M_ω` gives the
`O_L`-span of its coordinates (`Mlat`; it is `M_ω` itself once `M_ω` is an `O_L`-module), and `H_{ω,σ}` its Gram
matrix at each `σ` (`gram σ`, hermitian at every `σ` by `gram_isHermitian`). With the lattice property and the
positivity of `gram σ_v` at the complex places as hypotheses, `source` is the `KLattice` with metric `gram σ_v` at `v`.
The finite-dimensionality, the lattice property and the positivity are not proved here (given finitely many classes,
each with a finite stabiliser, the positivity is automatic: `H_σ(F, F)` is a positive combination of Fock norms of the
`σF(rep c)`, and a form vanishing at every representative is `0`).

**The coefficient field** `L` need carry no star for `petAt`, `H_ω`, `gram` and `source`. `pet` uses a star
(`StarRing L`), not a CM structure: the frontier asks only that the star be complex conjugation at one embedding (the
archive's coefficient field contains `j(cc)`, so lies in no CM field). The Fock form and `pet` are hermitian for it.

**Sanity theorems:** `conj_pet` (`H` is hermitian, via `conj_fockWith`), `petAt_eq_map` (`H_σ = σ ∘ H` where the
star is conjugation at `σ`), `dOp_mem` (the diamond operators act on forms), `gram_isHermitian` (at every `σ`, via
`conj_petAt`), `source_G` (the metric at `v` is the Gram matrix of `H_{ω,σ_v}`).
-/

namespace HermForms

open NumberField IsDedekindDomain HermClasses WeylFock

open scoped ComplexOrder

noncomputable section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}
  {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L] [NumberField L]

variable (ST Λ Φ L) in
/-- The functions `D → L[x_{τ,a,b}]` on the decorated lattices. -/
abbrev Fn := ↥(points (E := E) (n := n) (ST := ST) Λ) → Pol Φ n L

/-! ## Forms (L4.1) -/

section Forms

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- The forms of weight `λ`: the `𝒢`-equivariant functions `F : D → VV_L(λ)`,
`F(g·d) = chr(g)·ρ_λ(γ_g) F(d)`. -/
def Forms : Submodule L (Fn ST Λ Φ L) where
  carrier := {F | (∀ d, F d ∈ VV lam) ∧ ∀ (g : Grp E n SG Λ) d, F (g • d) = chr χ g • rho τ lam g.1.1 (F d)}
  add_mem' {F G} hF hG := ⟨fun d => add_mem (hF.1 d) (hG.1 d), fun g d => by
    simp only [Pi.add_apply, hF.2, hG.2, rho, map_add, mul_add, smul_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun g d => by simp [rho]⟩
  smul_mem' a F hF := ⟨fun d => Submodule.smul_mem _ a (hF.1 d), fun g d => by
    simp only [Pi.smul_apply, hF.2, rho, map_smul, mul_smul_comm, smul_comm a (chr χ g)]⟩

/-- The integral forms `M`: the forms with `F(c) ∈ Δ_{Lsh(rep c)}(λ)` at the representative of every class. -/
def Mint : Set (Fn ST Λ Φ L) :=
  {F | F ∈ Forms ST τ χ lam ∧ ∀ c : DCl E n ST Λ, F c.out ∈ DeltaN τ lam (Lsh c.rep)}

/-- **The Petersson form at an embedding** `σ : L →+* ℂ` (a complex place):
`H_σ(F, G) = Σᶠ_c |Stab(c)|⁻¹·⟨σF(c), σG(c)⟩`, `σ` applied coefficientwise and then the Fock form over `ℂ`, so
hermitian at every `σ` (`conj_petAt`) with no star on `L`. The frontier's source metrics (the archive's metric at
each place). It is `σ(H(F, G))` where the star of `L` is conjugation at `σ` (`petAt_eq_map`). -/
def petAt (σ : L →+* ℂ) (F G : Fn ST Λ Φ L) : ℂ :=
  classSum fun c : DCl E n ST Λ =>
    fock (fun ρ => natW (lam ρ)) (MvPolynomial.map σ (F c.out)) (MvPolynomial.map σ (G c.out))

variable [StarRing L]

/-- The Petersson form `H(F, G) = Σᶠ_c |Stab(c)|⁻¹·⟨F(c), G(c)⟩`, hermitian for the star of `L`. -/
def pet (F G : Fn ST Λ Φ L) : L :=
  classSum fun c : DCl E n ST Λ => fock (fun σ => natW (lam σ)) (F c.out) (G c.out)

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- The Fock form is star-symmetric: `star fock(F, G) = fock(G, F)`. -/
theorem conj_fockWith (F G : Pol Φ n L) :
    starRingEnd L (fockWith (starRingEnd L) F G) = fockWith (starRingEnd L) G F := by
  classical
  simp only [fockWith, map_sum, map_mul, Finsupp.prod, map_prod, map_natCast, starRingEnd_self_apply]
  rw [← Finset.sum_subset (Finset.inter_subset_left : G.support ∩ F.support ⊆ G.support) ?_,
    ← Finset.sum_subset (Finset.inter_subset_left : F.support ∩ G.support ⊆ F.support) ?_, Finset.inter_comm]
  · exact Finset.sum_congr rfl fun _ _ => by ring
  all_goals intro x hx hx'; simp_all [MvPolynomial.mem_support_iff]

omit [DecidableEq Φ] in
/-- **Sanity:** the Petersson form is hermitian for the star, `star H(F, G) = H(G, F)`. -/
theorem conj_pet (F G : Fn ST Λ Φ L) : starRingEnd L (pet ST lam F G) = pet ST lam G F := by
  refine ((starAddEquiv : L ≃+ L).map_finsum _).trans (finsum_congr fun c => ?_)
  change starRingEnd L (mass c • fock _ _ _) = _
  rw [map_rat_smul]
  unfold fock
  rw [map_div₀, conj_fockWith, conj_fockWith]

omit [DecidableEq Φ] [NumberField L] [StarRing L] in
/-- The Petersson form at `σ` is hermitian, `conj H_σ(F, G) = H_σ(G, F)`. Serves `gram_isHermitian`. -/
theorem conj_petAt (σ : L →+* ℂ) (F G : Fn ST Λ Φ L) :
    starRingEnd ℂ (petAt ST lam σ F G) = petAt ST lam σ G F := by
  refine ((starAddEquiv : ℂ ≃+ ℂ).map_finsum _).trans (finsum_congr fun c => ?_)
  change starRingEnd ℂ (mass c • fock _ _ _) = _
  rw [map_rat_smul]
  unfold fock
  rw [map_div₀, conj_fockWith, conj_fockWith]

omit [DecidableEq Φ] [NumberField L] [StarRing L] in
/-- `σ` maps the highest-weight vector over `L` to the one over `ℂ`. Serves `petAt_eq_map`. -/
theorem map_hw (σ : L →+* ℂ) (ν : Φ → Fin n → ℕ) : MvPolynomial.map σ (hw L ν) = hw ℂ ν := by
  simp only [hw, minor, map_prod, map_pow, RingHom.map_det, RingHom.mapMatrix_apply]
  congr! with τ _ s _
  ext a b
  simp [xMat]

omit [Fintype Φ] [DecidableEq Φ] [NumberField L] in
/-- Where the star of `L` is conjugation at `σ`, `σ` maps the Fock form over `L` to the one over `ℂ`. Serves
`petAt_eq_map`. -/
theorem map_fockWith (σ : L →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) (F G : Pol Φ n L) :
    σ (fockWith (starRingEnd L) F G) =
      fockWith (starRingEnd ℂ) (MvPolynomial.map σ F) (MvPolynomial.map σ G) := by
  simp only [fockWith, map_sum, map_mul, MvPolynomial.coeff_map, MvPolynomial.support_map_of_injective _ σ.injective,
    Finsupp.prod, map_prod, map_natCast, starRingEnd_apply, hσ]

omit [DecidableEq Φ] in
/-- **Sanity:** where the star of `L` is conjugation at `σ` (in the frontier, at `σ₀` only), the Petersson form at
`σ` is the image of the `L`-valued one, `H_σ = σ ∘ H`. -/
theorem petAt_eq_map (σ : L →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) (F G : Fn ST Λ Φ L) :
    petAt ST lam σ F G = σ (pet ST lam F G) := by
  refine (finsum_congr fun c => ?_).trans (σ.toAddMonoidHom.map_finsum_of_injective σ.injective _).symm
  change _ = σ (mass c • fock _ _ _)
  unfold fock
  rw [map_rat_smul, map_div₀, map_fockWith σ hσ, map_fockWith σ hσ, map_hw]

end Forms

/-! ## The ramified cut at `T` (L4.2, L4.3) -/

section Cut

/-- The diamond operators keep the conditions: `a_P·f_P ≠ 0` for a unit `a_P`. -/
def diaPt (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : points (E := E) (n := n) (ST := ST) Λ) :
    points (E := E) (n := n) (ST := ST) Λ :=
  ⟨dia a d, { d.2 with
    f_ne := fun P h => d.2.f_ne P <| by
      have h' : (a P : 𝓞 E ⧸ P.1.asIdeal) • (d : Deco E n ST SG).f P = 0 := h
      simpa [Units.smul_def, smul_smul] using congrArg (((a P)⁻¹ : (𝓞 E ⧸ P.1.asIdeal)ˣ) • ·) h' }⟩

/-- The diamond operator `⟨a⟩ F = F ∘ dia_a` on functions on `D`. -/
def dOp (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) : Module.End L (Fn ST Λ Φ L) :=
  LinearMap.funLeft L (Pol Φ n L) (diaPt a)

open Classical in
/-- The norm `Nm_P = Σ_{a ∈ (O_E/P)ˣ} ⟨a⟩_P`, with `⟨a⟩_P = dOp (Pi.mulSingle P a)`. -/
def Nm (P : ST) : Module.End L (Fn ST Λ Φ L) :=
  ∑ᶠ a : (𝓞 E ⧸ P.1.asIdeal)ˣ, dOp (Pi.mulSingle P a)

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

omit [NumberField L] in
/-- **Sanity:** the diamond operators commute with `𝒢` (`dia_smul`), so they act on forms. -/
theorem dOp_mem (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) :
    dOp a F ∈ Forms ST τ χ lam := by
  refine ⟨fun d => hF.1 _, fun g d => ?_⟩
  have : diaPt a (g • d) = g • diaPt a d := Subtype.ext (dia_smul Λ a g d)
  simp only [dOp, LinearMap.funLeft_apply, this, hF.2]

/-- The cut `V_ω = {F ∈ Forms : Nm_P F = 0 ∀ P ∈ ST}`. -/
def Vω : Submodule L (Fn ST Λ Φ L) := Forms ST τ χ lam ⊓ ⨅ P, LinearMap.ker (Nm P)

/-- The integral cut forms `M_ω = M ∩ V_ω`. -/
def Mω : Set (Fn ST Λ Φ L) := Mint ST τ χ lam ∩ (Vω ST τ χ lam : Set (Fn ST Λ Φ L))

/-- The Petersson form on the cut at an embedding `σ`, `H_{ω,σ} = H_σ|_{V_ω}`. -/
def Hω (σ : L →+* ℂ) (F G : Vω ST τ χ lam) : ℂ := petAt ST lam σ (F : Fn ST Λ Φ L) G

end Cut

/-! ## The source as a hermitian `O_L`-lattice (L4.3, L6.5) -/

section Source

variable (ST) (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ) [FiniteDimensional L (Vω ST τ χ lam)]

/-- The index set `Fin (dim V_ω)` of Mathlib's chosen basis of `V_ω`. -/
abbrev Idx := Fin (Module.finrank L (Vω ST τ χ lam))

/-- The coordinates of `V_ω` in Mathlib's chosen basis. -/
abbrev coords : Vω ST τ χ lam ≃ₗ[L] (Idx ST τ χ lam → L) := (Module.finBasis L _).equivFun

/-- The `O_L`-span of `M_ω` in coordinates. -/
def Mlat : Submodule (𝓞 L) (Idx ST τ χ lam → L) :=
  Submodule.span (𝓞 L) (coords ST τ χ lam '' {F | (F : Fn ST Λ Φ L) ∈ Mω ST τ χ lam})

/-- The Gram matrix of `H_ω` at an embedding `σ` in the basis. -/
def gram (σ : L →+* ℂ) : Matrix (Idx ST τ χ lam) (Idx ST τ χ lam) ℂ :=
  fun i j => Hω ST τ χ lam σ (Module.finBasis L _ i) (Module.finBasis L _ j)

omit [NumberField L] in
/-- **Sanity:** the Gram matrix is hermitian at every embedding `σ` (`conj_petAt`), whether or not a star of `L` is
complex conjugation there; `source` asks only the positivity. -/
theorem gram_isHermitian (σ : L →+* ℂ) : (gram ST τ χ lam σ).IsHermitian :=
  Matrix.ext fun _ _ => conj_petAt ST lam σ _ _

/-- The source `(M_ω, H_ω)` as a hermitian `O_L`-lattice: the metric at `v` is the Gram matrix of `H_ω` at `σ_v`. -/
def source [(Mlat ST τ χ lam).IsLattice L]
    (hpos : ∀ v : HermitianLattice.Pl L, (gram ST τ χ lam v.1.embedding).PosDef) :
    KLattice L (Idx ST τ χ lam) :=
  ⟨Mlat ST τ χ lam, fun v => gram ST τ χ lam v.1.embedding, hpos⟩

/-- **Sanity:** the metric of the source at a complex place `v` is the Gram matrix of `H_{ω,σ_v}`. -/
theorem source_G [(Mlat ST τ χ lam).IsLattice L]
    (hpos : ∀ v : HermitianLattice.Pl L, (gram ST τ χ lam v.1.embedding).PosDef) (v : HermitianLattice.Pl L) :
    (source ST τ χ lam hpos).G v = gram ST τ χ lam v.1.embedding :=
  rfl

end Source

end

end HermForms
