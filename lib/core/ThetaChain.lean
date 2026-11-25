import Mathlib
import HermClasses
import WeylFock

/-!
# Hecke characters, theta kernels and the theta chain

Layer L5 of the sharp frontier (`docs/rh-rebuild.md`): the characters, the theta functions per pair of lattices,
their jets, the step kernels `κ_j`, the lifts `K_j` and the chain `Θ_ω = K_{m−1} ∘ … ∘ K_0`. Generic in the CM field
`E`, the coefficient field `L`, the CM type `Φ` and its embeddings `τ : Φ → (E →+* L)`.

**Characters** (L5.1). A Hecke character is taken in its algebraic form: the finite part `χ : 𝔸_{E,f}^× → L^×` of a
unitary character of `𝔸_E^×/E^×` whose values lie in `L`, a homomorphism with open kernel (`Hecke`). Its infinity type
`a : Φ → ℤ` is read on the principal ideles: `χ(x) = ∏_{σ ∈ Φ} τ_σ(x/x̄)^{−a_σ}` (`Hecke.HasType`; the archimedean
component is `z ↦ ∏ (z_σ/z̄_σ)^{a_σ}`, and `χ` is trivial on `E^×`). `UnramAway S` and `Tame S` say that `χ` kills the
local units away from `S`, and the principal units at the places of `S`. The lift characters `μ_{0,j}` (type `−e_j`)
form one existential bundle (`LiftChars`). Not encoded:
triviality on `𝔸_F^×` (Mathlib has no base change of finite adeles at the pin) and the tie `μ_{0,j} = ω^{−2(j+1)}` on
the residue units at `g` (it lives with the level data, spec-2 2a).

**Splitting characters** (L5.2). For the determinant idele `d` of a class, `ρ_j = (μξ)(d)⁻¹` (`rhoIn`) and
`ρ′_j = (μξ)(d)` (`rhoOut`), as in the archive's step kernel: no `χ_ψ` (its powers would cancel only against a
`chiFac` on the theta, which `thMoved` does not carry). The determinant idele needs the frames at `SG ∪ Q`, which the
decorated lattices of `HermClasses` do not carry; it is a parameter of the chain data (`Data.dI`).

**Theta functions** (spec-2, 1a and 1e). On `V = (Φ × Fin b × Fin a → ℂ)` (`Amb`): the form
`H(z, w) = s·Σ z·w̄` (`Hf`), the semicharacter `α(x) = (−1)^{round(sd·Re H(x, x))}` (`al`, `sd = √d/2`), the Heisenberg
operators `U_x G(z) = G(z + x)·exp(−πH(z, x) − πH(x, x)/2)` (`opU`), the theta space
`Th(Λ) = {G holomorphic : α(x)·U_x G = G ∀ x ∈ Λ}` (`Th`), the lattice `La(N, N′) = ι(𝔄·Hom(N, N′))` with
`ι(x) = (δ·τ(x))_τ` (`La`, `iota`), and the averaging operator
`Iop(Λ₁, Λ₂)G = [Λ₂ : Λ₁ ∩ Λ₂]^{−1/2}·Σ_{q ∈ Λ₂/(Λ₁ ∩ Λ₂)} α(q)·U_q G` (`Iop`). The theta of a pair of lattices is the
archive's moved theta `θ_{N,N′} = Iop(La(N, std′), La(N, N′)) (Iop(La(std, std′), La(N, std′)) θ_std)` (`thMoved`):
**no `χ`, no `chiFac`** (they cancel in the jets, spec-2 1b). The constants `s, sd, δ, 𝔄, cD` and the embedding
`σ₀ : L → ℂ` are pinned by the setting and passed in `TP`. The base theta `θ_std` is **existential** (`ThetaStd`):
nonzero, in `Th(La(std, std′))`; the rationality of the jets of the coset thetas that `κ_j` sums is a condition on
the chain data (`Data.θ_rat`), on the archive's range only.

**Finite places** (spec-2, 1b, 1e). The coset theta `θ_{N,N′,x} = vol^{−1/2}·α(s)·U_{−s}(xiS(1_{BC}) θ_{N,N′})`,
`s = ι(liftW x)` with `liftW x` a lift of the coset into the half-lattice `HA` (`Data.HA`, the archive's `halfAO`, a
parameter), so `vol^{−1/2}` enters twice, as in the archive; with
the finite Heisenberg sum `xiS Φ e = Σ_{y ∈ SB} Φ̂(y)·α(y)·U_y e`, `Φ̂(y) = vol^{−1/2}(vol/|SA|)·Σ_{t ∈ SA} Φ(t)
e^{2πi Im H(t, y)}` (`xiS`, `thInd`). The finite data `SA, SB, BC, vol` are a parameter (`XiData`), pinned by
`Data.XDPinned` (spec-3 §3, spec-5 §3: `HA = halfAO(cA·cB)`, `BC = ι(halfBO(cB))` with `perO`, `twist₂`, `expS`;
`IsReps`; `volS`).
The cosets are `cA⁻¹H_S/cB·H_S` with `H_S = {x : x(N_P) ⊆ N′_P, P ∈ S}` (`homAt`, read globally: `x(N) ⊆ N′_P`,
`locMem`). The local factor `Ξ = Π_P XiAt_P` (spec-2 1d: `E1 ∘ om ∘ PhiG/PhiQ` over `volN`) is
**a parameter** (`Data.Xi`), too heavy to transcribe here; its stated property, invariance under `cB·H_S`, is
`XiInv`.

**Jets and `κ_j`** (spec-2 1e). `jetVal θ m = cD^m·∂^m θ(0)` (`pd`, holomorphic iterated derivatives), brought to `L`
by `desc = σ₀⁻¹` (`0` off `σ₀(L)`). The jet operator multiplies by `Π_τ det(x_τ)^{n_τ}`, substitutes
`x_{τ,r,c} ↦ Σ_β y_{τ,β,c}·∂_{τ,β,r}` (row `r`, column `c`; `jetSub`) and replaces each `∂^m` by its jet value
(`jetEval`); it is linear
(`jetOp`). Then `κ_j(c, c′) = Σ_{x} Ξ(x)·ρ_j(c)ρ′_j(c′)·Jet(θ_{N,N′,x})` (`kappa`). **Determinant powers.** In the
library's convention (`WeylFock`: `VV λ` stores `F` for the function `det^{λ_{n−1}}·F`), the spec's output factor
`Π det(y′)^{−s÷_j}` is the implicit factor of `VV(λ_{j+1})`, as `λ_{j+1, N_{j+1}−1} = −s÷_j` (L3.1), and the input
power is `n_τ = s♯_j(τ) + λ_{j, N_j−1}(τ)` (`nIn`), which is `≥ 0` by L0.6 ("the input is a genuine polynomial").

**The chain** (`Chain`). `K_jφ(c′) = Σᶠ_c mass(c)·κ_j(c, c′)(φ(c))` (`Chain.lift`) and `Θ = K_{m−1} ∘ … ∘ K_0`
(`Chain.comp`), with dependent ranks `n j`. `Data.chain` instantiates it with the classes `Σ_{b ∈ β j} DCl` of
`HermClasses`.

**Level data** (spec-2 Item 2). Step 0 is explicit: the upper unitriangular group (`uniUT`) and the generic character
`u ↦ ψ₀(Σ_{i<k−1} u_{i,i+1})` (`lamGen`), with `ψ₀` pinned by `xi0 = −1/(N(cc)√−d)` (`psi0`). Steps `j ≥ 1` go
through the existential `ChIdx`: index types, representatives, groups and characters, with the step-0 and last-step
conditions exact and the archive's remaining `Ok` ties (`grpG/chrG/grpQ/chrQ/inj/surj`, which need `prX`, `R1`, `J`)
as a parameter predicate. The coset `Y` of the last step is explicit (`Ycos`); `z = e_last` is `HermClasses.eLast`.

**Sanity theorems:** `opU_zero`, `Chain.comp_zero`, `Chain.lift_add`, `detShift_wt_succ`.
-/

namespace ThetaChain

open NumberField IsDedekindDomain MvPolynomial HermClasses WeylFock Matrix

/-! ## Hecke characters (L5.1) -/

section Hecke

variable (E L : Type*) [Field E] [NumberField E] [Field L]

/-- The finite ideles `𝔸_{E,f}^×`. -/
abbrev Ideles := (FiniteAdeleRing (𝓞 E) E)ˣ

/-- An algebraic Hecke character: the finite part `𝔸_{E,f}^× → L^×` of a character of the idele class group, with
open kernel. Meant for `LiftChars` and `Data`. -/
structure Hecke where
  /-- The character on the finite ideles. -/
  toHom : Ideles E →* Lˣ
  /-- Continuity: the kernel is open. -/
  isOpen_ker : IsOpen (toHom.ker : Set (Ideles E))

variable {E L}

/-- The unit ideles that are `1` at the places of `S`. -/
def unitsAway (S : Set (HeightOneSpectrum (𝓞 E))) : Set (Ideles E) :=
  {x | ∀ v, (x : FiniteAdeleRing (𝓞 E) E) v ∈ v.adicCompletionIntegers E ∧
    ((x⁻¹ : Ideles E) : FiniteAdeleRing (𝓞 E) E) v ∈ v.adicCompletionIntegers E ∧
    (v ∈ S → (x : FiniteAdeleRing (𝓞 E) E) v = 1)}

/-- The principal units at `v`: ideles `1` away from `v` and `≡ 1 (mod v)` at `v`. -/
def oneUnitsAt (v : HeightOneSpectrum (𝓞 E)) : Set (Ideles E) :=
  {x | (∀ w ≠ v, (x : FiniteAdeleRing (𝓞 E) E) w = 1) ∧
    Valued.v ((x : FiniteAdeleRing (𝓞 E) E) v - 1) < 1}

/-- `χ` is unramified away from `S`. -/
def Hecke.UnramAway (χ : Hecke E L) (S : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ x ∈ unitsAway S, χ.toHom x = 1

/-- `χ` is tame at the places of `S`. -/
def Hecke.Tame (χ : Hecke E L) (S : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ v ∈ S, ∀ x ∈ oneUnitsAt v, χ.toHom x = 1

variable [IsCMField E] {Φ : Type*} [Fintype Φ] (τ : Φ → (E →+* L))

/-- `χ` has infinity type `a` on `Φ`: `χ(x) = ∏_{σ ∈ Φ} τ_σ(x/x̄)^{−a_σ}` on the principal ideles. -/
def Hecke.HasType (χ : Hecke E L) (a : Φ → ℤ) : Prop :=
  ∀ x : Eˣ, (χ.toHom (FiniteAdeleRing.unitEmbedding (𝓞 E) E x) : L) =
    ∏ σ, τ σ ((x : E) / IsCMField.complexConj E (x : E)) ^ (-a σ)

/-- The lift characters `μ_{0,j}` (`j < m`; type `−e_j`, unramified away from `Sg`, tame there), L5.1. Existential:
L7 quantifies over it. -/
structure LiftChars (m : ℕ) (e : ℕ → Φ → ℤ) (Sg : Set (HeightOneSpectrum (𝓞 E))) where
  /-- The lift characters `μ_{0,j}`. -/
  mu : ℕ → Hecke E L
  mu_type : ∀ j < m, (mu j).HasType τ (-e j)
  mu_unram : ∀ j < m, (mu j).UnramAway Sg
  mu_tame : ∀ j < m, (mu j).Tame Sg

end Hecke

/-! ## Splitting characters and determinant powers (L5.2, L5.4) -/

section Split

variable {E L : Type*} [Field E] [NumberField E] [Field L]

/-- `ρ_j(c) = (μ_{0,j}ξ)(d)⁻¹` at the determinant idele `d` of `c`. -/
def rhoIn (μ : Hecke E L) (d : Ideles E) : L :=
  ((μ.toHom d)⁻¹ : Lˣ)

/-- `ρ′_j(c′) = (μ_{0,j}ξ)(d′)` at the determinant idele `d′` of `c′`. -/
def rhoOut (μ : Hecke E L) (d : Ideles E) : L :=
  (μ.toHom d : Lˣ)

/-- The determinant power `s♯_j(τ) = e_j(τ) − N_{j+1}/2` (`b = N_{j+1}`). -/
def sSharp {Φ : Type*} (e : Φ → ℤ) (b : ℕ) (σ : Φ) : ℤ := e σ - (b / 2 : ℕ)

/-- The determinant power `s÷_j(τ) = e_j(τ) − N_j/2` (`a = N_j`); in the library's convention it is
`−λ_{j+1, N_{j+1}−1}`, the implicit factor of `VV(λ_{j+1})` (module docstring). Meant for L6. -/
def sDiv {Φ : Type*} (e : Φ → ℤ) (a : ℕ) (σ : Φ) : ℤ := e σ - (a / 2 : ℕ)

/-- The input power `n_τ = s♯_j(τ) + λ_{j, N_j−1}(τ)` of the jet operator in the library's convention (`≥ 0` by L0.6,
so `toNat` is exact). -/
def nIn {Φ : Type*} {a : ℕ} (e : Φ → ℤ) (b : ℕ) (lam : Φ → Fin a → ℤ) (σ : Φ) : ℕ :=
  (sSharp e b σ + detShift (lam σ)).toNat

/-- **Sanity:** `λ_{j+1, N_{j+1}−1} = −s÷_j` (L3.1, `k` even, `t` odd): the output factor `Π det(y′)^{−s÷_j}` of L5.4
is the implicit factor of `VV(λ_{j+1})`, as the module docstring says. -/
theorem detShift_wt_succ {Φ : Type*} (k t j : ℕ) (hk : Even k) (ht : Odd t) (u : Φ → Fin k → ℤ)
    (e : Φ → ℕ → ℤ) (σ : Φ) :
    detShift (wt k t (j + 1) u e σ) = -sDiv (fun σ => e σ j) (k + j * (t + 1)) σ := by
  obtain ⟨k', rfl⟩ := hk
  obtain ⟨t', rfl⟩ := ht
  have hpos : 0 < k' + k' + (j + 1) * (2 * t' + 1 + 1) := by positivity
  have h1 : ¬ (k' + k' + (j + 1) * (2 * t' + 1 + 1) - 1 < k' + k') := by
    have : 1 ≤ (j + 1) * (2 * t' + 1 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have h2 : (k' + k' + (j + 1) * (2 * t' + 1 + 1) - 1 - (k' + k')) / (2 * t' + 1 + 1) = j := by
    apply Nat.div_eq_of_lt_le
    · have : (j + 1) * (2 * t' + 1 + 1) = j * (2 * t' + 1 + 1) + (2 * t' + 1 + 1) := by ring
      omega
    · have : (j + 1) * (2 * t' + 1 + 1) = j * (2 * t' + 1 + 1) + (2 * t' + 1 + 1) := by ring
      omega
  have h3 : (k' + k') / 2 = k' := by omega
  have h4 : (2 * t' + 1 + 1) / 2 = t' + 1 := by omega
  have h5 : (k' + k' + j * (2 * t' + 1 + 1)) / 2 = k' + j * (t' + 1) := by
    rw [show k' + k' + j * (2 * t' + 1 + 1) = 2 * (k' + j * (t' + 1)) by ring]; simp
  simp only [detShift, wt, dite_eq_left hpos, dite_eq_right h1, h2, h3, h4, h5, sDiv]
  have h6 : ((↑(k' + k' + (j + 1) * (2 * t' + 1 + 1) - 1) - ↑(k' + k')) / (↑(2 * t' + 1) + 1) : ℤ) = j := by
    rw [← Nat.cast_sub (by omega), show ((2 * t' + 1 : ℕ) : ℤ) + 1 = ((2 * t' + 1 + 1 : ℕ) : ℤ) by push_cast; ring,
      ← Int.natCast_div, h2]
  rw [h6]
  push_cast
  ring

end Split

/-! ## Theta functions (spec-2, 1a, 1e) -/

section Theta

variable {ι : Type*} [Fintype ι]

/-- `H(z, w) = s·Σ_p z_p·w̄_p`. -/
def Hf (s : ℝ) (z w : ι → ℂ) : ℂ := s * ∑ p, z p * starRingEnd ℂ (w p)

/-- The semicharacter `α(x) = (−1)^{round(sd·Re H(x, x))}`, `sd = √d/2`. -/
noncomputable def al (s sd : ℝ) (x : ι → ℂ) : ℂ := (-1 : ℂ) ^ round (sd * (Hf s x x).re)

/-- The Heisenberg operator `U_x G(z) = G(z + x)·exp(−πH(z, x) − πH(x, x)/2)`. -/
noncomputable def opU (s : ℝ) (x : ι → ℂ) (G : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-Real.pi * Hf s z x - Real.pi * Hf s x x / 2)

/-- The theta space `Th(Λ) = {G holomorphic : α(x)·U_x G = G for all x ∈ Λ}`. -/
def Th (s sd : ℝ) (Λ : AddSubgroup (ι → ℂ)) : Set ((ι → ℂ) → ℂ) :=
  {G | Differentiable ℂ G ∧ ∀ x ∈ Λ, al s sd x • opU s x G = G}

/-- The averaging operator `Iop(Λ₁, Λ₂)G = [Λ₂ : Λ₁ ∩ Λ₂]^{−1/2}·Σ_{q ∈ Λ₂/(Λ₁ ∩ Λ₂)} α(q)·U_q G`, with chosen
representatives (the sum does not depend on them, spec-2 1a). -/
noncomputable def Iop (s sd : ℝ) (Λ₁ Λ₂ : AddSubgroup (ι → ℂ)) (G : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ :=
  ((Real.sqrt ((Λ₁ ⊓ Λ₂).relIndex Λ₂ : ℝ))⁻¹ : ℂ) •
    ∑ᶠ q : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂, al s sd (q.out : ι → ℂ) • opU s (q.out : ι → ℂ) G

/-- `S` is a set of representatives of `Λ₂/(Λ₁ ∩ Λ₂)` (spec-3 §3): `S ⊆ Λ₂`, distinct elements of `S` are distinct
mod `Λ₁`, and every `y ∈ Λ₂` is `≡` some `x ∈ S` mod `Λ₁`. Pins `XiData.SA`, `SB` (`Data.XDPinned`). -/
def IsReps (Λ₁ Λ₂ : Set (ι → ℂ)) (S : Finset (ι → ℂ)) : Prop :=
  ↑S ⊆ Λ₂ ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ₁ → x = y) ∧ ∀ y ∈ Λ₂, ∃ x ∈ S, y - x ∈ Λ₁

/-- The finite data of a Heisenberg sum: coset representatives `SA`, `SB`, the lattice `BC` and the volume (the
archive's `halfAO/halfBO/repsOf`; free here, pinned by `Data.XDPinned`). -/
structure XiData (ι : Type*) where
  /-- Representatives `SA`. -/
  SA : Finset (ι → ℂ)
  /-- Representatives `SB`. -/
  SB : Finset (ι → ℂ)
  /-- The lattice `BC` whose indicator is transformed. -/
  BC : Set (ι → ℂ)
  /-- The volume. -/
  vol : ℝ

/-- The finite Fourier transform `Φ̂(y) = vol^{−1/2}(vol/|SA|)·Σ_{t ∈ SA} Φ(t)·e^{2πi Im H(t, y)}`. -/
noncomputable def hatS (s : ℝ) (D : XiData ι) (F : (ι → ℂ) → ℂ) (y : ι → ℂ) : ℂ :=
  ((Real.sqrt D.vol)⁻¹ * (D.vol / D.SA.card) : ℝ) *
    ∑ t ∈ D.SA, F t * Complex.exp (2 * Real.pi * Complex.I * (Hf s t y).im)

/-- The finite Heisenberg sum `xiS Φ e = Σ_{y ∈ SB} Φ̂(y)·α(y)·U_y e`. -/
noncomputable def xiS (s sd : ℝ) (D : XiData ι) (F : (ι → ℂ) → ℂ) (e : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ :=
  ∑ y ∈ D.SB, (hatS s D F y * al s sd y) • opU s y e

/-- The coset theta `vol^{−1/2}·α(x)·U_{−x}(xiS(1_{BC}) e)` at the point `x = ι(lift)` of a coset (spec-2 1b; the
outer `vol^{−1/2}` is the archive's, on top of the one in `hatS`). -/
noncomputable def thInd (s sd : ℝ) (D : XiData ι) (e : (ι → ℂ) → ℂ) (x : ι → ℂ) : (ι → ℂ) → ℂ :=
  (((Real.sqrt D.vol)⁻¹ : ℝ) : ℂ) • al s sd x • opU s (-x) (xiS s sd D (D.BC.indicator 1) e)

variable [DecidableEq ι]

/-- The holomorphic derivative `∂^m G(0)` for a multi-index `m`. -/
noncomputable def pd (G : (ι → ℂ) → ℂ) (m : ι →₀ ℕ) : ℂ :=
  iteratedFDeriv ℂ (Multiset.card (Finsupp.toMultiset m)) G 0 fun i =>
    Pi.single ((Finsupp.toMultiset m).toList.get (Fin.cast (Multiset.length_toList _).symm i)) 1

end Theta

/-! ## Lattices, the moved theta and the base theta -/

section Lattices

variable {E L : Type*} [Field E] [NumberField E] [Field L] {Φ : Type*} [Fintype Φ] [DecidableEq Φ]

/-- The ambient `V = ⊕_{τ ∈ Φ} M_{b×a}(ℂ)`, as functions of `(τ, row, column)`. -/
abbrev Amb (Φ : Type*) (a b : ℕ) := Φ × Fin b × Fin a → ℂ

variable (E L Φ) in
/-- The constants of the theta functions, pinned by the setting: `σ₀ : L → ℂ`, `δ` (`δ¹² = Δ(φ₀(cc))`),
`s = 1/area(Λ_c)`, `sd = √d/2`, the ideal `𝔄 = cc·AA0` and the coordinate generators `cD(τ)` of `𝔟⁻¹`. -/
structure TP where
  /-- The complex embedding of `L`. -/
  σ₀ : L →+* ℂ
  /-- The normalising constant `δ`. -/
  δ : ℂ
  /-- `s = 1/area(Λ_c)`. -/
  s : ℝ
  /-- `sd = √d/2`. -/
  sd : ℝ
  /-- The fractional ideal `𝔄 = cc·AA0`. -/
  A : Submodule (𝓞 E) E
  /-- The generators `cD(τ)`. -/
  cD : Φ → ℂ

variable (τ : Φ → (E →+* L)) (P : TP E L Φ)

/-- `ι(x) = (δ·τ(x))_τ` for `x ∈ M_{b×a}(E)`. -/
def iota {a b : ℕ} (x : Matrix (Fin b) (Fin a) E) : Amb Φ a b := fun p => P.δ * P.σ₀ (τ p.1 (x p.2.1 p.2.2))

/-- `Hom(N, N′) = {A ∈ M_{b×a}(E) : A·N ⊆ N′}`. -/
def homSet {a b : ℕ} (N : Submodule (𝓞 E) (Fin a → E)) (N' : Submodule (𝓞 E) (Fin b → E)) :
    Set (Matrix (Fin b) (Fin a) E) :=
  {A | ∀ v ∈ N, A *ᵥ v ∈ N'}

/-- The lattice `La(N, N′) = ι(𝔄·Hom(N, N′))`. -/
def La {a b : ℕ} (N : Submodule (𝓞 E) (Fin a → E)) (N' : Submodule (𝓞 E) (Fin b → E)) : AddSubgroup (Amb Φ a b) :=
  AddSubgroup.closure {z | ∃ w ∈ P.A, ∃ A ∈ homSet N N', z = iota τ P (w • A)}

/-- The moved theta `θ_{N,N′} = Iop(La(N, std′), La(N, N′)) (Iop(La(std, std′), La(N, std′)) θ_std)`. -/
noncomputable def thMoved {a b : ℕ} (θ : Amb Φ a b → ℂ) (N : Submodule (𝓞 E) (Fin a → E))
    (N' : Submodule (𝓞 E) (Fin b → E)) : Amb Φ a b → ℂ :=
  Iop P.s P.sd (La τ P N (stdLat (E := E) (n := b))) (La τ P N N')
    (Iop P.s P.sd (La τ P (stdLat (E := E) (n := a)) (stdLat (E := E) (n := b)))
      (La τ P N (stdLat (E := E) (n := b))) θ)

/-- The jet value `cD^m·∂^m θ(0)`. -/
noncomputable def jetVal {a b : ℕ} (θ : Amb Φ a b → ℂ) (m : Φ × Fin b × Fin a →₀ ℕ) : ℂ :=
  (m.prod fun p k => P.cD p.1 ^ k) * pd θ m

/-- `σ₀⁻¹` on `σ₀(L)`, and `0` off it (`σ₀` is injective, so this is pinned). -/
noncomputable def desc (z : ℂ) : L := by
  classical exact if h : ∃ l, P.σ₀ l = z then h.choose else 0

end Lattices

/-! ## Jets and the step kernel (spec-2, 1e) -/

section Jets

variable {E L : Type*} [Field E] [NumberField E] [Field L] {Φ : Type*} [Fintype Φ] [DecidableEq Φ]
  {a b : ℕ}

/-- The substitution `x_{τ,r,c} ↦ Σ_β y_{τ,β,c}·∂_{τ,β,r}` (`r` the row, `c` the column of `x`; as matrices
`x ↦ ∂ᵀ·y_{·,<a}`, so column weights pass to `y`): polynomials in the `∂_{τ,β,r}` with coefficients polynomials in
`y`. -/
noncomputable def jetSub (hab : a ≤ b) : Pol Φ a L →ₐ[L] MvPolynomial (Φ × Fin b × Fin a) (Pol Φ b L) :=
  aeval fun p => ∑ β : Fin b, C (X (p.1, β, Fin.castLE hab p.2.2)) * X (p.1, β, p.2.1)

/-- Replace each monomial `∂^m` by the scalar `J(m)`. -/
noncomputable def jetEval (J : (Φ × Fin b × Fin a →₀ ℕ) → L) :
    MvPolynomial (Φ × Fin b × Fin a) (Pol Φ b L) →ₗ[L] Pol Φ b L :=
  Finsupp.lsum L (fun m => J m • LinearMap.id) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv L).toLinearMap

/-- The jet operator of `θ`: multiply by `Π_τ det(x_τ)^{n_τ}`, substitute, and replace `∂^m` by
`σ₀⁻¹(cD^m·∂^m θ(0))`. -/
noncomputable def jetOp (P : TP E L Φ) (hab : a ≤ b) (n : Φ → ℕ) (θ : Amb Φ a b → ℂ) :
    Pol Φ a L →ₗ[L] Pol Φ b L :=
  jetEval (fun m => desc P (jetVal P θ m)) ∘ₗ (jetSub hab).toLinearMap ∘ₗ
    LinearMap.mulLeft L (∏ σ, (xMat σ).det ^ n σ)

/-- `z ∈ N_P`: some `s ∉ P` has `s·z ∈ N`. -/
def locMem {n : ℕ} (Pl : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E) : Prop :=
  ∃ s : 𝓞 E, s ∉ Pl.asIdeal ∧ (s : E) • z ∈ N

/-- `H_S = homAt_S(N, N′)`: the `x ∈ M_{b×a}(E)` with `x(N_P) ⊆ N′_P` for `P ∈ S`. -/
def homAt (S : Set (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Fin a → E))
    (N' : Submodule (𝓞 E) (Fin b → E)) : AddSubgroup (Matrix (Fin b) (Fin a) E) :=
  AddSubgroup.closure {x | ∀ Pl ∈ S, ∀ v ∈ N, locMem Pl N' (x *ᵥ v)}

/-- The scaled group `c·H`. -/
def scl {n : ℕ} (c : E) (H : AddSubgroup (Matrix (Fin b) (Fin n) E)) : AddSubgroup (Matrix (Fin b) (Fin n) E) :=
  H.map (smulAddHom E (Matrix (Fin b) (Fin n) E) c)

/-- The cosets `cA⁻¹H_S / cB·H_S` of the step kernel. -/
abbrev Cosets (S : Set (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (N : Submodule (𝓞 E) (Fin a → E))
    (N' : Submodule (𝓞 E) (Fin b → E)) :=
  scl (cA : E)⁻¹ (homAt S N N') ⧸ (scl (cB : E) (homAt S N N')).addSubgroupOf (scl (cA : E)⁻¹ (homAt S N N'))

/-- The property of the local factor `Ξ` (spec-2 1d): invariant under `cB·H_S`, so the coset sum is well defined. -/
def XiInv (S : Set (HeightOneSpectrum (𝓞 E))) (cB : ℕ) (N : Submodule (𝓞 E) (Fin a → E))
    (N' : Submodule (𝓞 E) (Fin b → E)) (Xi : Matrix (Fin b) (Fin a) E → L) : Prop :=
  ∀ x, ∀ y ∈ scl (cB : E) (homAt S N N'), Xi (x + y) = Xi x

/-- The representative lift of a coset `x` (the archive's `liftW`): a chosen `s ∈ HA` with `s − x ∈ cB·H_S` (Hilbert
choice, as the archive's `ε`; arbitrary if there is none). `HA` is the half-lattice (the archive's `halfAO`, not
transcribed: a parameter). -/
noncomputable def liftW (S : Set (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (N : Submodule (𝓞 E) (Fin a → E))
    (N' : Submodule (𝓞 E) (Fin b → E)) (HA : Set (Matrix (Fin b) (Fin a) E)) (x : Cosets S cA cB N N') :
    Matrix (Fin b) (Fin a) E :=
  Classical.epsilon fun s => s ∈ HA ∧ s - (x.out : Matrix (Fin b) (Fin a) E) ∈ scl (cB : E) (homAt S N N')

variable (τ : Φ → (E →+* L)) (P : TP E L Φ)

/-- The step kernel `κ(c, c′) = Σ_{x ∈ cA⁻¹H_S/cB·H_S} Ξ(x)·r·Jet(θ_{N,N′,x})`, with `r = ρ_j(c)ρ′_j(c′)`,
`θ_{N,N′,x} = thInd(θ_{N,N′})(ι(liftW x))` (the lift in the half-lattice `HA`) and `θ_{N,N′} = thMoved θ_std`
(spec-2 1e). -/
noncomputable def kappa (hab : a ≤ b) (n : Φ → ℕ) (θ : Amb Φ a b → ℂ) (S : Set (HeightOneSpectrum (𝓞 E)))
    (cA cB : ℕ) (D : XiData (Φ × Fin b × Fin a)) (HA : Set (Matrix (Fin b) (Fin a) E))
    (Xi : Matrix (Fin b) (Fin a) E → L) (r : L)
    (N : Submodule (𝓞 E) (Fin a → E)) (N' : Submodule (𝓞 E) (Fin b → E)) : Pol Φ a L →ₗ[L] Pol Φ b L :=
  ∑ᶠ x : Cosets S cA cB N N', (Xi (x.out : Matrix (Fin b) (Fin a) E) * r) •
    jetOp P hab n (thInd P.s P.sd D (thMoved τ P θ N N') (iota τ P (liftW S cA cB N N' HA x)))

variable [IsCMField E]

/-- The base theta `θ_std` for the sizes `(a, b)` (spec-2 1e, item 2): existential, a nonzero element of
`Th(La(std, std′))`. Its rationality (`JetsRat`) holds only on the archive's range (self-dual lattices, points of
`cA⁻¹H_S`, the pinned coset datum), so it is a condition on the chain data (`Data.θ_rat`), not stated here. -/
structure ThetaStd (a b : ℕ) where
  /-- The base theta. -/
  θ : Amb Φ a b → ℂ
  ne_zero : θ ≠ 0
  mem : θ ∈ Th P.s P.sd (La τ P (stdLat (E := E) (n := a)) (stdLat (E := E) (n := b)))

/-- The localisation `M_(P) = {z : s·z ∈ M for some s ∉ P}` (an additive group: the closure adds nothing). -/
def locSub (Pl : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Matrix (Fin b) (Fin a) E)) :
    AddSubgroup (Matrix (Fin b) (Fin a) E) :=
  AddSubgroup.closure {z | ∃ s : 𝓞 E, s ∉ Pl.asIdeal ∧ (s : E) • z ∈ M}

/-- `perO(𝔄, N, N′) = O_E·𝔄·Hom(N, N′)` (spec-3 §3); `ι(perO) = La(N, N′)`, as `𝔄·Hom` is `O_E`-stable. -/
def perO (A : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Fin a → E)) (N' : Submodule (𝓞 E) (Fin b → E)) :
    Submodule (𝓞 E) (Matrix (Fin b) (Fin a) E) :=
  Submodule.span (𝓞 E) {z | ∃ w ∈ A, ∃ x ∈ homSet N N', z = w • x}

open Classical in
/-- `expS(SS, Q) = 1` if `Q ∈ SS`, `−1` if `Q̄ ∈ SS`, `0` otherwise. -/
noncomputable def expS (SS : Set (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) : ℤ :=
  if Q ∈ SS then 1 else
    if ∃ Pl ∈ SS, Q.asIdeal = Pl.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) then -1
    else 0

/-- `twist₂(M, c, e) = ⋂_Q {w : c^{−e(Q)}·w ∈ M_(Q)}`: the lattice equal to `c^{e(Q)}·M` at every `Q`. -/
def twist₂ (M : Submodule (𝓞 E) (Matrix (Fin b) (Fin a) E)) (c : E) (ex : HeightOneSpectrum (𝓞 E) → ℤ) :
    Set (Matrix (Fin b) (Fin a) E) :=
  {w | ∀ Q, c ^ (-ex Q) • w ∈ locSub Q M}

/-- `halfAO(SS, M, c)`: `c⁻¹M` at `P ∈ SS`, `cM` at `P̄`, `M` elsewhere (the half-lattice of the lifts). -/
noncomputable def halfAO (SS : Set (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (Matrix (Fin b) (Fin a) E))
    (c : E) : Set (Matrix (Fin b) (Fin a) E) :=
  twist₂ M c fun Q => -expS SS Q

/-- `halfBO(SS, M, c)`: `cM` at `P ∈ SS`, `c⁻¹M` at `P̄`, `M` elsewhere (the lattice `BC`). -/
noncomputable def halfBO (SS : Set (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (Matrix (Fin b) (Fin a) E))
    (c : E) : Set (Matrix (Fin b) (Fin a) E) :=
  twist₂ M c (expS SS)

/-- `volS(SS, M₀, M) = Π_{P ∈ SS} [M_P : M₀_P ∩ M_P]/[M₀_P : M₀_P ∩ M_P]`, the covolume ratio. -/
noncomputable def volS (SS : Set (HeightOneSpectrum (𝓞 E))) (M₀ M : Submodule (𝓞 E) (Matrix (Fin b) (Fin a) E)) :
    ℝ :=
  ∏ᶠ Pl ∈ SS, ((locSub Pl M₀).relIndex (locSub Pl M) : ℝ) / ((locSub Pl M).relIndex (locSub Pl M₀) : ℝ)

/-- **The Heisenberg data pinned** (spec-3 §3, spec-5 §3), for a step with lattices `N`, `N′`, places `SS`, integers
`cA` and `c` (the modulus of the lift congruence, as in the archive's `liftS`): `HA = halfAO(SS, perO, cA·c)` (the
lift of the archive's proved normal form `thInd_index`), `BC = ι(halfBO(SS, perO, c))`, `SA` representatives of
`(LamC ∩ AC)/(LamC ∩ AC ∩ BC)` with `0 ∈ SA`, `SB` of `BC/(BC ∩ LamC)` (`LamC = La(N, N′) = ι(perO)`, `AC = ι(HA)`),
and `vol = volS(SS, perO(std, std′), perO(N, N′))` (it cancels). -/
def XDPin (SS : Set (HeightOneSpectrum (𝓞 E))) (cA c : ℕ) (N : Submodule (𝓞 E) (Fin a → E))
    (N' : Submodule (𝓞 E) (Fin b → E)) (XD : XiData (Φ × Fin b × Fin a)) (HA : Set (Matrix (Fin b) (Fin a) E)) :
    Prop :=
  HA = halfAO SS (perO P.A N N') ((cA * c : ℕ) : E) ∧ XD.BC = iota τ P '' halfBO SS (perO P.A N N') (c : E) ∧
    IsReps XD.BC ((La τ P N N' : Set (Amb Φ a b)) ∩ iota τ P '' HA) XD.SA ∧ (0 : Amb Φ a b) ∈ XD.SA ∧
    IsReps (La τ P N N') XD.BC XD.SB ∧
    XD.vol = volS SS (perO P.A (stdLat (E := E) (n := a)) (stdLat (E := E) (n := b))) (perO P.A N N')

end Jets

/-! ## Level data (spec-2, Item 2) -/

section Level

variable {E L : Type*} [Field E] [NumberField E] [Field L] {SG : Finset (HeightOneSpectrum (𝓞 E))} {n : ℕ}

variable (SG n) in
/-- The upper unitriangular group `U_n(O_E/w)` at every `w ∈ SG`, the level group of step 0 (spec-2 2a). The set of
upper unitriangular matrices is a group, so the closure adds nothing. -/
def uniUT : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) :=
  Subgroup.closure {g | ∀ w, ((g w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal))).BlockTriangular id ∧
    ∀ i, (g w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) i i = 1}

/-- The least `b ∈ ℕ` with `b ≡ xi0·c (mod w)`. -/
noncomputable def resRep (xi0 : E) (w : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E ⧸ w.asIdeal) : ℕ :=
  sInf {b : ℕ | ∃ c' : 𝓞 E, Ideal.Quotient.mk w.asIdeal c' = c ∧ w.valuation E ((b : E) - xi0 * c') < 1}

/-- The residue additive character `ψ₀(c) = exp(2πi·b/q)`, `b ≡ xi0·c (mod w)`, `q = N(w)`, pinned by
`Chars.WeilTied` with `xi0 = −1/(N(cc)·√−d)` (spec-2 2a). Complex-valued; its `L`-valued form is `desc ∘ ψ₀`. -/
noncomputable def psi0 (xi0 : E) (w : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E ⧸ w.asIdeal) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (resRep xi0 w c : ℂ) / (Ideal.absNorm w.asIdeal : ℂ))

/-- The generic character of step 0, `u ↦ Π_{w ∈ SG} ψ₀(Σ_{i < n−1} u_{w,i,i+1})` (spec-2 2a). -/
noncomputable def lamGen (xi0 : E) (g : ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : ℂ :=
  ∏ w : SG, psi0 xi0 w.1 (∑ i : Fin n,
    if h : (i : ℕ) + 1 < n then (g w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) i ⟨i + 1, h⟩ else 0)

variable (SG) in
/-- The chain index (spec-2 2b), existential: per step `j`, index types `β j`, representatives
`h_{j,b} ∈ Π_{P ∈ S} GL_{N_j + c_j}(E)` (`c_j = m − 1 − j`), level groups `Λ_{j,b}` and their characters. Step 0 is
explicit (`β 0` a singleton, `h = 1`, `uniUT` with `lamGen`), and so is the last step (`β(m−1)` a singleton, `h = 1`).
The archive's remaining ties (`grpG/chrG/grpQ/chrQ`: `Λ_{j,b}` and its character are the reductions of
`prX(R1 ∩ hJh⁻¹)` and `chiInv`; `inj/surj`: `β(j+1)` enumerates the admissible double cosets) need `prX`, `R1` and
`J`, which are not transcribed. Meant for L6/L7, which build `Data` from it. -/
structure ChIdx (Nj : ℕ → ℕ) (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (xi0 : E) (σ₀ : L →+* ℂ) where
  /-- The index types. -/
  β : ℕ → Type
  finite : ∀ j, Finite (β j)
  /-- The representatives. -/
  h : ∀ j, β j → S → GL (Fin (Nj j + (m - 1 - j))) E
  /-- The level groups. -/
  Λ : ∀ j, β j → Subgroup (∀ w : SG, GL (Fin (Nj j)) (𝓞 E ⧸ w.1.asIdeal))
  /-- Their characters. -/
  chr : ∀ j b, Λ j b →* Lˣ
  zero_unique : Unique (β 0)
  zero_h : ∀ b, h 0 b = 1
  zero_grp : ∀ b, Λ 0 b = uniUT SG (Nj 0)
  zero_chr : ∀ b g, σ₀ (chr 0 b g : L) = lamGen xi0 (g : ∀ w : SG, GL (Fin (Nj 0)) (𝓞 E ⧸ w.1.asIdeal))
  last_unique : Unique (β (m - 1))
  last_h : ∀ b, h (m - 1) b = 1

/-- `locLat_S(N; ex) = {z : q_P^{−ex_P}·z ∈ N_P for P ∈ S}`, `q_P = N(P)`. -/
def locLat (S : Set (HeightOneSpectrum (𝓞 E))) (ex : HeightOneSpectrum (𝓞 E) → ℤ) (N : Submodule (𝓞 E) (Fin n → E)) :
    AddSubgroup (Fin n → E) :=
  AddSubgroup.closure {z | ∀ Pl ∈ S, locMem Pl N (((Ideal.absNorm Pl.asIdeal : ℕ) : E) ^ (-ex Pl) • z)}

open Classical in
/-- The coset space `Y` of the last step (spec-2 2c): `locLat_S(N; −1 at SG, −M at Q)` modulo
`locLat_S(N; 0 at SG, M at Q)`, `S = SG ∪ Q`, i.e. `Π_{SG} q⁻¹N_P/N_P × Π_Q q^{−M}N_P/q^M N_P`. Meant for L6. -/
abbrev Ycos (SG Q : Set (HeightOneSpectrum (𝓞 E))) (M : ℕ) (N : Submodule (𝓞 E) (Fin n → E)) :=
  locLat (SG ∪ Q) (fun Pl => if Pl ∈ SG then -1 else -(M : ℤ)) N ⧸
    (locLat (SG ∪ Q) (fun Pl => if Pl ∈ SG then 0 else (M : ℤ)) N).addSubgroupOf
      (locLat (SG ∪ Q) (fun Pl => if Pl ∈ SG then -1 else -(M : ℤ)) N)

end Level

/-! ## The lift and the chain -/

section Chain

variable {Φ : Type*} {L : Type*} [Field L]

variable (Φ L) in
/-- A chain of steps: ranks `n j`, class types `C j` with mass weights, and step kernels
`κ_j(c, c′) : Pol(n j) → Pol(n (j+1))`. -/
structure Chain where
  /-- The rank at step `j`. -/
  n : ℕ → ℕ
  /-- The classes at step `j`. -/
  C : ℕ → Type*
  /-- The mass weights. -/
  mass : ∀ j, C j → ℚ
  /-- The step kernels. -/
  kappa : ∀ j, C j → C (j + 1) → Pol Φ (n j) L →ₗ[L] Pol Φ (n (j + 1)) L

/-- The lift `K_jφ(c′) = Σᶠ_c mass(c)·κ_j(c, c′)(φ(c))`. -/
noncomputable def Chain.lift (K : Chain Φ L) (j : ℕ) (φ : K.C j → Pol Φ (K.n j) L) :
    K.C (j + 1) → Pol Φ (K.n (j + 1)) L :=
  fun c' => ∑ᶠ c, ((K.mass j c : ℚ) : L) • K.kappa j c c' (φ c)

/-- The chain `Θ = K_{j−1} ∘ … ∘ K_0`; `Θ_ω` is `K.comp m`. -/
noncomputable def Chain.comp (K : Chain Φ L) : ∀ j, (K.C 0 → Pol Φ (K.n 0) L) → K.C j → Pol Φ (K.n j) L
  | 0 => id
  | j + 1 => fun φ => K.lift j (K.comp j φ)

/-- **Sanity:** the chain of length `0` is the identity. -/
theorem Chain.comp_zero (K : Chain Φ L) (φ : K.C 0 → Pol Φ (K.n 0) L) : K.comp 0 φ = φ := rfl

/-- **Sanity:** the lift is additive (finitely many classes). -/
theorem Chain.lift_add (K : Chain Φ L) (j : ℕ) [Finite (K.C j)] (φ ψ : K.C j → Pol Φ (K.n j) L) :
    K.lift j (φ + ψ) = K.lift j φ + K.lift j ψ := by
  funext c'
  simp only [Chain.lift, Pi.add_apply, map_add, smul_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

end Chain

/-! ## The theta chain of a setting -/

section Data

variable {E L : Type*} [Field E] [NumberField E] [IsCMField E] [Field L] {Φ : Type*} [Fintype Φ] [DecidableEq Φ]

/-- The classes at step `j`: `Σ_{b ∈ β j}` of the decorated classes for the level group `Λ_{j,b}`. -/
abbrev Cls (n : ℕ → ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (β : ℕ → Type)
    (Λ : ∀ j, β j → Subgroup (∀ w : SG, GL (Fin (n j)) (𝓞 E ⧸ w.1.asIdeal))) (j : ℕ) :=
  Σ b : β j, DCl E (n j) ST (Λ j b)

variable (τ : Φ → (E →+* L))

/-- The data of a theta chain: ranks `N_j`, the theta constants, the place sets, the level data, the weights `λ_j`
and `e_j`, the characters `μ_{0,j}ξ`, the determinant ideles, the base thetas, the coset parameters and
the local factors `Ξ`. L7 builds it from a setting and a `ChIdx`. -/
structure Data where
  /-- The ranks `N_j`. -/
  n : ℕ → ℕ
  mono : ∀ j, n j ≤ n (j + 1)
  /-- The theta constants. -/
  P : TP E L Φ
  /-- The level-`T` places. -/
  ST : Finset (HeightOneSpectrum (𝓞 E))
  /-- The level places `SG`. -/
  SG : Finset (HeightOneSpectrum (𝓞 E))
  /-- The row set `S = SG ∪ Q`. -/
  S : Set (HeightOneSpectrum (𝓞 E))
  /-- The index types of the components. -/
  β : ℕ → Type
  /-- The level groups. -/
  Λ : ∀ j, β j → Subgroup (∀ w : SG, GL (Fin (n j)) (𝓞 E ⧸ w.1.asIdeal))
  /-- The weights `e_j`. -/
  e : ℕ → Φ → ℤ
  /-- The weights `λ_j`. -/
  lam : ∀ j, Φ → Fin (n j) → ℤ
  /-- The characters `μ_{0,j}ξ_μ`. -/
  mu : ℕ → Hecke E L
  /-- The determinant ideles `d(N_c)` (L5.2). -/
  dI : ∀ j, Cls n ST SG β Λ j → Ideles E
  /-- The base thetas. -/
  θ : ∀ j, ThetaStd τ P (n j) (n (j + 1))
  /-- The integers `cA`, `cB` of the coset sums. -/
  cA : ℕ → ℕ
  /-- See `cA`. -/
  cB : ℕ → ℕ
  /-- The finite Heisenberg data. -/
  XD : ∀ j, Cls n ST SG β Λ j → Cls n ST SG β Λ (j + 1) → XiData (Φ × Fin (n (j + 1)) × Fin (n j))
  /-- The half-lattices in which the coset points are lifted (`liftW`; the archive's `halfAO`). -/
  HA : ∀ j, Cls n ST SG β Λ j → Cls n ST SG β Λ (j + 1) → Set (Matrix (Fin (n (j + 1))) (Fin (n j)) E)
  /-- The local factors `Ξ_j(c, c′)` (`PsiAt` at the last step). -/
  Xi : ∀ j, Cls n ST SG β Λ j → Cls n ST SG β Λ (j + 1) → Matrix (Fin (n (j + 1))) (Fin (n j)) E → L
  Xi_inv : ∀ j c c', XiInv S (cB j) (c.2.N) (c'.2.N) (Xi j c c')
  /-- `JetsRat` on the archive's range: the jets of every coset theta that `kappa` sums (the class lattices, the
  lifted coset points `liftW x` of `cA⁻¹H_S`, the data's own `XD`) lie in `σ₀(L)`. -/
  θ_rat : ∀ j (c : Cls n ST SG β Λ j) (c' : Cls n ST SG β Λ (j + 1)) (x : Cosets S (cA j) (cB j) c.2.N c'.2.N)
    (m : Φ × Fin (n (j + 1)) × Fin (n j) →₀ ℕ),
    jetVal P (thInd P.s P.sd (XD j c c') (thMoved τ P (θ j).θ c.2.N c'.2.N)
      (iota τ P (liftW S (cA j) (cB j) c.2.N c'.2.N (HA j c c') x))) m ∈ Set.range P.σ₀

/-- The theta chain of the data: `κ_j(c, c′)` with `r = ρ_j(c)ρ′_j(c′)` and the input power `nIn`. -/
noncomputable def Data.chain (D : Data τ) : Chain Φ L where
  n := D.n
  C := Cls D.n D.ST D.SG D.β D.Λ
  mass _ c := mass c.2
  kappa j c c' := kappa τ D.P (D.mono j) (nIn (D.e j) (D.n (j + 1)) (D.lam j)) (D.θ j).θ D.S (D.cA j) (D.cB j)
    (D.XD j c c') (D.HA j c c') (D.Xi j c c')
    (rhoIn (D.mu j) (D.dI j c) * rhoOut (D.mu j) (D.dI (j + 1) c'))
    c.2.N c'.2.N

/-- **The data's Heisenberg data and half-lattices are pinned** (`XDPin` at every step, places `S`, integers `cA j`
and `cB j`, the latter the modulus of `liftW`'s congruence; `HA` at `cA j·cB j`). Meant for L7 (`IsThetaCol`). -/
def Data.XDPinned (D : Data τ) : Prop :=
  ∀ j c c', XDPin τ D.P D.S (D.cA j) (D.cB j) c.2.N c'.2.N (D.XD j c c') (D.HA j c c')

end Data

/-- **Sanity:** `U_0` is the identity. -/
theorem opU_zero {ι : Type*} [Fintype ι] (s : ℝ) (G : (ι → ℂ) → ℂ) : opU s 0 G = G := by
  funext z
  simp [opU, Hf]

end ThetaChain
