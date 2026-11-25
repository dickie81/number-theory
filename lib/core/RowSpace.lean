import Mathlib
import PeriodTarget
import HermClasses

/-!
# The row space `V0 = e·Amb`

Part of layer L6.2 of the sharp frontier (`docs/rh-rebuild.md`). `PeriodTarget.PerData.V0` is a free submodule of the
rows `Cl G X →₀ Pol Φ n L`; this module defines the predicate `IsRowSpace` that pins it to the spec's `e·Amb`, so the
frontier can require `IsRowSpace ρ P ψ (D.V0 μ0)` and no tiny row space is a witness.

**The type group** `𝔊` (the spec's `∏_{k} ∏_{v ∈ PlG_k} GL_r(ℤ/g_k)`, the archive's `∏_{w ∈ SG} GL_r(O/w)`) is a
finite group parameter. **Its action on the rows** `ρ : Representation L 𝔊 M` is a parameter: `HermClasses` acts on
the decorations by `U_n(E) × Λ_SG`, and the action of `𝔊` on the classes through the `SG` component is not defined
there. In use `M = Cl G X →₀ Pol Φ n L`, the rows of `PeriodTarget`; the definitions are generic in `M`.

**The ambient** `Amb = range lvlIdem`, `lvlIdem = |P|⁻¹Σ_{h∈P} ψ(h⁻¹)·h`: the `ψ`-isotypic part for a subgroup `P`
(unipotent in the spec) with a character `ψ` (generic in the spec). `P` and `ψ` are parameters.

**The idempotent** `idemOf X = Σ_{χ∈X} (χ(1)/|𝔊|)·Σ_g χ(g⁻¹)·g` for a finite set `X` of class functions `𝔊 → L`.

**The row space.** `IsRowSpace V0`: there is a nonempty, `Gal(L/ℚ)`-stable `X` of characters of simple `FDRep L 𝔊`
(Mathlib's `FDRep.character`) with `V0 = idemOf X (Amb) = range (idemOf X ∘ lvlIdem)`. The set `X` is existential
(the archive's good series are abstract). The frontier must still add `W_u ≠ 0` to exclude a zero `e·Amb`.

**Sanity theorems:** `idemOf_empty`, `map_Amb_eq_range`.
-/

namespace RowSpace

open CategoryTheory

noncomputable section

universe u

variable {L 𝔊 : Type u} [Field L] [Group 𝔊] [Fintype 𝔊] {M : Type*} [AddCommGroup M] [Module L M]
  (ρ : Representation L 𝔊 M)

/-- The level idempotent `lvlIdem = |P|⁻¹Σ_{h∈P} ψ(h⁻¹)·h` of a subgroup `P` with a character `ψ`. -/
def lvlIdem (P : Subgroup 𝔊) [Fintype P] (ψ : P →* L) : Module.End L M :=
  (Fintype.card P : L)⁻¹ • ∑ h : P, ψ h⁻¹ • ρ h

/-- The ambient `Amb`: the `ψ`-isotypic rows, the range of `lvlIdem`. -/
def Amb (P : Subgroup 𝔊) [Fintype P] (ψ : P →* L) : Submodule L M := LinearMap.range (lvlIdem ρ P ψ)

/-- The character idempotent `idemOf X = Σ_{χ∈X} (χ(1)/|𝔊|)·Σ_g χ(g⁻¹)·g`. -/
def idemOf (X : Finset (𝔊 → L)) : Module.End L M :=
  ∑ χ ∈ X, (χ 1 / Fintype.card 𝔊) • ∑ g, χ g⁻¹ • ρ g

/-- `χ` is the character of an irreducible (simple) finite-dimensional representation of `𝔊` over `L`. -/
def IsIrrChar (χ : 𝔊 → L) : Prop := ∃ V : FDRep L 𝔊, Simple V ∧ V.character = χ

/-- `X` is stable under `Gal(L/ℚ)`, acting on the values. -/
def GalStable [CharZero L] (X : Finset (𝔊 → L)) : Prop := ∀ σ : L ≃ₐ[ℚ] L, ∀ χ ∈ X, (σ ∘ χ) ∈ X

/-- **The row space** `V0 = e·Amb`: for some nonempty `Gal(L/ℚ)`-stable set `X` of irreducible characters,
`V0 = idemOf X (Amb)`. Meant for L7, on `PerData.V0 μ0`. -/
def IsRowSpace [CharZero L] (P : Subgroup 𝔊) [Fintype P] (ψ : P →* L) (V0 : Submodule L M) : Prop :=
  ∃ X : Finset (𝔊 → L), X.Nonempty ∧ (∀ χ ∈ X, IsIrrChar χ) ∧ GalStable X ∧
    V0 = (Amb ρ P ψ).map (idemOf ρ X)

/-- **Sanity:** the empty set of characters gives the zero idempotent. -/
@[simp] theorem idemOf_empty : idemOf ρ (∅ : Finset (𝔊 → L)) = 0 := by simp [idemOf]

/-- **Sanity:** `e·Amb = range (idemOf X ∘ lvlIdem)`, the archive's `range goodAt`. -/
theorem map_Amb_eq_range (P : Subgroup 𝔊) [Fintype P] (ψ : P →* L) (X : Finset (𝔊 → L)) :
    (Amb ρ P ψ).map (idemOf ρ X) = LinearMap.range (idemOf ρ X ∘ₗ lvlIdem ρ P ψ) :=
  (LinearMap.range_comp _ _).symm

end

end RowSpace
