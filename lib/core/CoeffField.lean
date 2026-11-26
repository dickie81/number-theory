import Mathlib

/-!
# The coefficient field: normal number fields inside `ℂ`

The coefficient field `K` of the sharp construction (`ZetaBalance.SharpCoeff`) is a number field, totally complex and
normal over `ℚ`, with complex conjugation as its star, a CM type `τ_K` into it and an embedding `j : K → ℂ` with
`j ∘ τ_K = τ`. This module builds such fields generically, as subfields of `ℂ`; the design's generators come later.

**The closure** (`coeffClosure s`): the normal closure in `ℂ` of `ℚ(s)`, the compositum of the images of `ℚ(s)`
under all its `ℚ`-embeddings into `ℂ`. It contains `s` (`subset_coeffClosure`). For a finite set `s` of algebraic
numbers it is finite-dimensional (`finiteDimensional_coeffClosure`), so a number field (`numberField_coeffClosure`),
and it is normal over `ℚ` (`normal_coeffClosure`), as the minimal polynomials split in `ℂ`.

**Conjugation is automatic.** A subfield `F ⊆ ℂ` normal over `ℚ` is stable under complex conjugation
(`conj_mem_of_normal`): conjugation restricted to `F` is a `ℚ`-embedding `F → ℂ`, whose image is `F` by normality. So
the closure need not adjoin `conj s`, and `conj_mem_coeffClosure` follows. Such an `F` carries the star `conj|_F`
(`instStarRing`), with `F.val (star x) = conj (F.val x)` by definition (`val_star`).

**Totally complex** (`isTotallyComplex_of_ringHom`): a field receiving a ring map from a totally complex field is
totally complex, as each of its embeddings into `ℂ` restricts to a non-real one of the source (Mathlib's
`isTotallyComplex_of_algebra`). For `K = F` it is applied to the codomain restriction of an embedding of `E`.

**Embeddings into `F`.** An embedding `σ : E → ℂ` lands in `F` once the images of a `ℚ`-basis of `E` do
(`map_mem_of_basis`, as `σ` is `ℚ`-linear). Then `σ.codRestrict F` embeds `E` into `F`, with
`F.val ∘ σ.codRestrict F = σ` by definition (`val_comp_codRestrict`).
-/

namespace CoeffField

open IntermediateField ComplexConjugate NumberField

noncomputable section

/-! ### Normal subfields of `ℂ`: conjugation and the star -/

section Normal

variable (F : IntermediateField ℚ ℂ) [Normal ℚ F]

/-- **A normal subfield of `ℂ` is stable under complex conjugation**: conjugation restricted to `F` is a
`ℚ`-embedding `F → ℂ`, whose image is `F` (`AlgHom.fieldRange_of_normal`). -/
theorem conj_mem_of_normal {x : ℂ} (hx : x ∈ F) : conj x ∈ F := by
  rw [← AlgHom.fieldRange_of_normal ((starRingEnd ℂ).toRatAlgHom.comp F.val)]
  exact ⟨⟨x, hx⟩, rfl⟩

/-- **The star of a normal subfield of `ℂ`**: complex conjugation restricted to `F`. -/
instance instStarRing : StarRing F where
  star x := ⟨conj (x : ℂ), conj_mem_of_normal F x.2⟩
  star_involutive x := Subtype.ext (Complex.conj_conj (x : ℂ))
  star_mul _ _ := Subtype.ext ((map_mul (starRingEnd ℂ) _ _).trans (mul_comm _ _))
  star_add _ _ := Subtype.ext (map_add (starRingEnd ℂ) _ _)

/-- **The star is conjugation**: `F.val (star x) = conj (F.val x)`. -/
theorem val_star (x : F) : F.val (star x) = conj (F.val x) := rfl

end Normal

/-! ### Totally complex fields and embeddings into a subfield -/

/-- **Totally complex by a ring map**: a field `K` receiving a ring map from a totally complex `E` is totally complex,
as an embedding of `K` into `ℂ` restricts to one of `E`, which is not real (`isTotallyComplex_of_algebra`). -/
theorem isTotallyComplex_of_ringHom {E K : Type*} [Field E] [Field K] [IsTotallyComplex E] (f : E →+* K) :
    IsTotallyComplex K :=
  letI := f.toAlgebra
  isTotallyComplex_of_algebra E K

/-- **An embedding lands in `F` if a basis does**: `σ : E → ℂ` is `ℚ`-linear, so it maps the `ℚ`-span of a basis
`b` of `E`, all of `E`, into `F` once each `σ(b_i) ∈ F`. -/
theorem map_mem_of_basis {E ι : Type*} [Field E] [CharZero E] (b : Module.Basis ι ℚ E) (σ : E →+* ℂ)
    {F : IntermediateField ℚ ℂ} (h : ∀ i, σ (b i) ∈ F) (x : E) : σ x ∈ F :=
  (Submodule.span_le (p := (Subalgebra.toSubmodule F.toSubalgebra).comap σ.toRatAlgHom.toLinearMap).2
    (Set.range_subset_iff.2 h)) (b.mem_span x)

/-- **The codomain restriction recovers the embedding**: `F.val ∘ σ.codRestrict F h = σ`. -/
theorem val_comp_codRestrict {E : Type*} [Field E] (σ : E →+* ℂ) (F : IntermediateField ℚ ℂ) (h : ∀ x, σ x ∈ F) :
    (F.val : F →+* ℂ).comp (σ.codRestrict F h) = σ :=
  RingHom.ext fun _ => rfl

/-! ### The coefficient closure -/

/-- **The coefficient closure** of `s ⊆ ℂ`: the normal closure in `ℂ` of `ℚ(s)`. -/
def coeffClosure (s : Set ℂ) : IntermediateField ℚ ℂ :=
  normalClosure ℚ (adjoin ℚ s) ℂ

/-- **The closure contains its generators**: `s ⊆ ℚ(s) ⊆ coeffClosure s`. -/
theorem subset_coeffClosure (s : Set ℂ) : s ⊆ coeffClosure s :=
  (subset_adjoin ℚ s).trans (le_normalClosure (adjoin ℚ s))

variable {s : Set ℂ}

/-- **The closure of finitely many algebraic numbers is finite-dimensional**: `ℚ(s)` is, and so is its normal
closure (`normalClosure.is_finiteDimensional`). -/
theorem finiteDimensional_coeffClosure (hs : s.Finite) (hi : ∀ x ∈ s, IsIntegral ℚ x) :
    FiniteDimensional ℚ (coeffClosure s) :=
  haveI := hs.to_subtype
  haveI := finiteDimensional_adjoin hi
  normalClosure.is_finiteDimensional ℚ (adjoin ℚ s) ℂ

/-- **The closure of finitely many algebraic numbers is a number field.** -/
theorem numberField_coeffClosure (hs : s.Finite) (hi : ∀ x ∈ s, IsIntegral ℚ x) :
    NumberField (coeffClosure s) :=
  haveI := finiteDimensional_coeffClosure hs hi
  ⟨⟩

/-- **The closure of algebraic numbers is normal**: `ℚ(s)` is algebraic and its minimal polynomials split in `ℂ`, so
its normal closure in `ℂ` is a normal closure (`isNormalClosure_normalClosure`), hence normal. -/
theorem normal_coeffClosure (hi : ∀ x ∈ s, IsIntegral ℚ x) : Normal ℚ (coeffClosure s) :=
  haveI := isAlgebraic_adjoin hi
  IsNormalClosure.normal (h := Algebra.IsAlgebraic.isNormalClosure_normalClosure fun _ => IsAlgClosed.splits _)

/-- **The closure of algebraic numbers is stable under complex conjugation**, being normal. -/
theorem conj_mem_coeffClosure (hi : ∀ x ∈ s, IsIntegral ℚ x) {x : ℂ} (hx : x ∈ coeffClosure s) :
    conj x ∈ coeffClosure s :=
  haveI := normal_coeffClosure hi
  conj_mem_of_normal _ hx

end

end CoeffField
