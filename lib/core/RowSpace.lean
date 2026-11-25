import Mathlib
import PeriodTarget
import HermClasses
import ThetaChain

/-!
# The row space `V0 = e·Amb`

Part of layer L6.2 of the sharp frontier (`docs/rh-rebuild.md`, spec-9). `PeriodTarget.PerData.V0 μ` is a free
submodule of the rows `Cl G X →₀ Pol Φ n L`; this module defines what pins it, at every level, to the archive's
`V0X = range(idemOf X · lvlIdem)` on the forms `mtildeKGSD`, so no tiny or infinite-dimensional row space is a witness.

**Generic part.** For a finite group `𝔊` acting by `ρ : Representation L 𝔊 M`: the level idempotent
`lvlIdem = |P|⁻¹Σ_{h∈P} ψ(h⁻¹)·h` of a subgroup `P` with a character `ψ`, the ambient `Amb = range lvlIdem`, the
character idempotent `idemOf X = Σ_{χ∈X} (χ(1)/|𝔊|)·Σ_g χ(g⁻¹)·g`, and `IsIrrChar` (the character of a simple
`FDRep L 𝔊`). The set `X` is existential in the frontier (the archive's good series are abstract), nonempty and
irreducible, one for all levels; it is **not** required to be `Gal(L/ℚ)`-stable (the archive's need not be).

**The rows on points** (spec-9 items 1–5). The forms live on the points `(N, be)` of `HermClasses.points` (with
`ST = ∅`), where the type action is a substitution and no cocycle or stabiliser bookkeeping is needed:
* `rowLevel SG Q` (`n = r + m·t`): `HKJ` at `SG` (block upper triangular for `(r, t, …, t)`, the `r × r` block `I`)
  and `HQ` at `Q \ SG` (the parabolic `(r, n − r)`), by `Matrix.BlockTriangular`; `rowChar` its character, from
  residue characters taken as data (`Hecke.ResAt`): the lift characters on the `t`-block determinants at `SG`, the
  twist on the `(n − r)`-block determinant at `Q`;
* `AmbPt`: the `VV(σ)`-valued `φ` with `φ((γ, h)·x) = χ(h)·ρ_σ(γ)φ(x)`;
* the type group `𝔊 = ∏_{w ∈ SG} GL_r(O_E/w)` through the Levi block (`levi`, `diag(a, I)`), acting by
  `(a·φ)(x) = φ(levi(a)⁻¹·x)` (`tyRep`, through `tyPt`); its level `Psym = ∏ HPsymF_w` and the character `chiSym`
  (`ψ₀(Σ_{i ≠ k−1} u_{i,i+1})`, complex-valued like `ThetaChain.lamGen`);
* `V0pt = idemOf X (Amb ⊓ AmbPt)`: the frontier reads `V0_μ` off it at class representatives.

`rowLevel` and `Psym` are closures of sets that are groups (as `ThetaChain.uniUT`); `rowChar` is a plain function
(only its values enter).

**Sanity theorems:** `idemOf_empty`, `map_Amb_eq_range`, `tyPt_mul`, `tyRep_apply`.
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

/-- **Sanity:** the empty set of characters gives the zero idempotent. -/
@[simp] theorem idemOf_empty : idemOf ρ (∅ : Finset (𝔊 → L)) = 0 := by simp [idemOf]

/-- **Sanity:** `e·Amb = range (idemOf X ∘ lvlIdem)`, the archive's `range goodAt`. -/
theorem map_Amb_eq_range (P : Subgroup 𝔊) [Fintype P] (ψ : P →* L) (X : Finset (𝔊 → L)) :
    (Amb ρ P ψ).map (idemOf ρ X) = LinearMap.range (idemOf ρ X ∘ₗ lvlIdem ρ P ψ) :=
  (LinearMap.range_comp _ _).symm

end

/-! ## The row level and the rows on points (spec-9) -/

noncomputable section RowLevel

open NumberField IsDedekindDomain Matrix HermClasses WeylFock ThetaChain

universe v

variable {E L : Type v} [Field E] [NumberField E] [Field L] {n : ℕ}

/-- The block index of `HKJ` at `w ∈ SG`: `0` on `[0, r)`, then `s + 1` on `[r + s·t, r + (s + 1)·t)`. -/
def blkSG (r t : ℕ) (i : Fin n) : ℕ := if (i : ℕ) < r then 0 else ((i : ℕ) - r) / t + 1

/-- The block index of `HQ` at `P ∈ Q`: `0` on `[0, r)`, `1` on `[r, n)`. -/
def blkQ (r : ℕ) (i : Fin n) : ℕ := if (i : ℕ) < r then 0 else 1

open Classical in
variable (n) in
/-- **The row level** `Λ = ∏_{w ∈ SG} HKJ_w × ∏_{P ∈ Q \ SG} HQ_P` in `∏_{w ∈ SG ∪ Q} GL_n(O_E/w)`, for
`n = r + m·t` (spec-9 items 1, 3): at `w ∈ SG` the matrices block upper triangular for the blocks `(r, t, …, t)`
(`blkSG`) with the `r × r` block `I` (the `t × t` blocks free); at `P ∈ Q \ SG` the parabolic with blocks `(r, n − r)`
(`blkQ`). The set is a group, so the closure adds nothing (as `ThetaChain.uniUT`). -/
def rowLevel (r t : ℕ) (SG Q : Finset (HeightOneSpectrum (𝓞 E))) :
    Subgroup (∀ w : ↥(SG ∪ Q), GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) :=
  Subgroup.closure {h | ∀ w : ↥(SG ∪ Q),
    (w.1 ∈ SG → (h w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).BlockTriangular (blkSG r t) ∧
      ∀ i j : Fin n, (i : ℕ) < r → (j : ℕ) < r →
        (h w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) i j = (1 : Matrix (Fin n) (Fin n) _) i j) ∧
    (w.1 ∉ SG → (h w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).BlockTriangular (blkQ r))}

/-- `c` is **the residue character** of the Hecke character `χ` at `w`: `χ(x) = c(x_w mod w)` for every unit idele
`x` that is `1` off `w` (it exists for `χ` tame at `w`). The residue characters of `rowChar`. -/
def _root_.ThetaChain.Hecke.ResAt (χ : Hecke E L) (w : HeightOneSpectrum (𝓞 E))
    (c : MulChar (𝓞 E ⧸ w.asIdeal) L) : Prop :=
  ∀ x ∈ unitsAway {v | v ≠ w}, ∀ a : 𝓞 E,
    Valued.v ((x : FiniteAdeleRing (𝓞 E) E) w - algebraMap E (w.adicCompletion E) (a : E)) < 1 →
      (χ.toHom x : L) = c (Ideal.Quotient.mk w.asIdeal a)

open Classical in
/-- **The character of the row level** (spec-9 items 1, 3): at `w ∈ SG`, `∏_{s < m} c_{s,w}(det h_s)` over the
`t × t` diagonal blocks (`c_{s,w}` the residue at `w` of the lift character `μ_{0,s}`, the archive's `lamKJ⁻¹`); at
`P ∈ Q \ SG`, `c_P(det D)` for the `(n − r) × (n − r)` block `D` (`c_P` the residue at `P` of the twist). The residue
characters are data (`Hecke.ResAt` ties them). A character on `rowLevel`; only its values are needed. -/
def rowChar (r t m : ℕ) {SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    (cS : ℕ → ∀ w : HeightOneSpectrum (𝓞 E), MulChar (𝓞 E ⧸ w.asIdeal) L)
    (cQ : ∀ w : HeightOneSpectrum (𝓞 E), MulChar (𝓞 E ⧸ w.asIdeal) L)
    (h : ∀ w : ↥(SG ∪ Q), GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : L :=
  ∏ w : ↥(SG ∪ Q), if w.1 ∈ SG then
      ∏ s ∈ Finset.range m, cS s w.1 ((h w : Matrix (Fin n) (Fin n) _).toSquareBlock (blkSG r t) (s + 1)).det
    else cQ w.1 ((h w : Matrix (Fin n) (Fin n) _).toSquareBlock (blkQ r) 1).det

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] [NumberField L] [IsCMField E]

omit [NumberField E] [DecidableEq Φ] [NumberField L] [IsCMField E] in
/-- `ρ_λ(γ)` is additive. -/
theorem rho_add (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ) (γ : GL (Fin n) E) (F G : Pol Φ n L) :
    rho τ lam γ (F + G) = rho τ lam γ F + rho τ lam γ G := by
  simp [rho, mul_add]

omit [NumberField E] [DecidableEq Φ] [NumberField L] [IsCMField E] in
/-- `ρ_λ(γ)` is `L`-linear. -/
theorem rho_smul (τ : Φ → (E →+* L)) (lam : Φ → Fin n → ℤ) (γ : GL (Fin n) E) (c : L) (F : Pol Φ n L) :
    rho τ lam γ (c • F) = c • rho τ lam γ F := by
  simp [rho]

/-- **The ambient on points** `Amb_pt`: the functions `φ` on the points `(N, be)` with values in `VV(σ)` and
`φ((γ, h)·x) = χ(h)·ρ_σ(γ)φ(x)` (spec-9 item 4, the archive's `EqFun`). With `Λ = rowLevel` and `χ = rowChar`,
finite-dimensional (finitely many classes, `VV` finite-dimensional). -/
def AmbPt (τ : Φ → (E →+* L)) (sg : Φ → Fin n → ℤ) {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) (χ : Λ → L) :
    Submodule L (points (E := E) (ST := ST) Λ → Pol Φ n L) where
  carrier := {φ | ∀ x, φ x ∈ VV sg ∧ ∀ g : Grp E n SG Λ, φ (g • x) = χ g.2 • rho τ sg g.1.1 (φ x)}
  add_mem' {φ ψ} hφ hψ x := ⟨add_mem (hφ x).1 (hψ x).1, fun g => by
    simp only [Pi.add_apply, (hφ x).2 g, (hψ x).2 g, rho_add, smul_add]⟩
  zero_mem' x := ⟨zero_mem _, fun g => by simp [rho]⟩
  smul_mem' c φ hφ x := ⟨Submodule.smul_mem _ c (hφ x).1, fun g => by
    simp only [Pi.smul_apply, (hφ x).2 g, rho_smul, smul_comm c]⟩

/-- The type group on a point, through the `SG` component: `g·(N, f, be) = (N, f, g·be)`, the action of
`(1, g) ∈ U_n(E) × ∏_{w ∈ SG} GL_n(O_E/w)`. It keeps `Deco.Good`, so it maps `points Λ` to itself for every `Λ`. -/
def tyPt {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}
    (g : ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) (x : points (E := E) (ST := ST) Λ) :
    points (E := E) (ST := ST) Λ :=
  ⟨(show Grp E n SG ⊤ from (1, ⟨g, Subgroup.mem_top g⟩)) • x.1, (points (ST := ST) ⊤).smul_mem _ x.2⟩

/-- **Sanity:** `tyPt` is an action. -/
theorem tyPt_mul {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))} (g g' : ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))
    (x : points (E := E) (ST := ST) Λ) : tyPt (g * g') x = tyPt g (tyPt g' x) := by
  apply Subtype.ext
  change ((1, ⟨g * g', Subgroup.mem_top _⟩) : Grp E n SG ⊤) • x.1 =
    ((1, ⟨g, Subgroup.mem_top _⟩) : Grp E n SG ⊤) • (((1, ⟨g', Subgroup.mem_top _⟩) : Grp E n SG ⊤) • x.1)
  rw [← mul_smul]
  exact congrArg (· • x.1) (Prod.ext (mul_one (1 : U E n)).symm rfl)

/-- `tyPt 1` is the identity. -/
theorem tyPt_one {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))} (x : points (E := E) (ST := ST) Λ) :
    tyPt 1 x = x :=
  Subtype.ext (one_smul (Grp E n SG ⊤) x.1)

/-- **The type action** on the functions on points, through `lv : 𝔊 →* ∏_w GL_n(O_E/w)`: `(a·φ)(x) = φ(lv(a)⁻¹·x)`
(the archive's `trF`; `lv = levi`). -/
def tyRep {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}
    {𝔊 : Type*} [Group 𝔊] (lv : 𝔊 →* ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) (V : Type*) [AddCommGroup V]
    [Module L V] : Representation L 𝔊 (points (E := E) (ST := ST) Λ → V) where
  toFun a := LinearMap.funLeft L V (tyPt (lv a⁻¹))
  map_one' := LinearMap.ext fun φ => funext fun x => by simp [LinearMap.funLeft_apply, tyPt_one]
  map_mul' a b := LinearMap.ext fun φ => funext fun x => by
    simp [LinearMap.funLeft_apply, tyPt_mul]

omit [NumberField L] in
/-- **Sanity:** the defining law of the type action. -/
theorem tyRep_apply {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))} {𝔊 : Type*} [Group 𝔊]
    (lv : 𝔊 →* ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) (V : Type*) [AddCommGroup V] [Module L V] (a : 𝔊)
    (φ : points (E := E) (ST := ST) Λ → V) (x : points (E := E) (ST := ST) Λ) :
    tyRep (L := L) lv V a φ x = φ (tyPt (lv a⁻¹) x) :=
  rfl

/-- `diag(A, I)`: `A` on `[0, r)` and the identity on `[r, n)`, for `r ≤ n` (the archive's `diagMat`). -/
def diagI {R : Type*} [CommRing R] (r : ℕ) (hr : r ≤ n) : Matrix (Fin r) (Fin r) R →* Matrix (Fin n) (Fin n) R where
  toFun A := reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hr))) (fromBlocks A 0 0 1)
  map_one' := by rw [fromBlocks_one]; exact map_one _
  map_mul' A B := by rw [← map_mul, fromBlocks_multiply]; simp

open Classical in
/-- **The Levi embedding** of the type group `𝔊 = ∏_{w ∈ SG} GL_r(O_E/w)` (spec-9 item 2, the archive's
`unipotentGroupBlockEmbedding`): `a ↦ diag(a_w, I)` at `w ∈ SG` and `1` at `w ∈ Q \ SG`. -/
def levi (r : ℕ) (hr : r ≤ n) (SG Q : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ w : SG, GL (Fin r) (𝓞 E ⧸ w.1.asIdeal)) →* ∀ w : ↥(SG ∪ Q), GL (Fin n) (𝓞 E ⧸ w.1.asIdeal) where
  toFun a w := if h : w.1 ∈ SG then Units.map (diagI r hr) (a ⟨w.1, h⟩) else 1
  map_one' := funext fun w => by split_ifs <;> simp
  map_mul' a b := funext fun w => by by_cases h : w.1 ∈ SG <;> simp [h]

/-- The order `σ` of `{0, …, r − 1}` with `A < B < C`, for `B = [0, k)`, `A = [k, k + rS)`, `C = [k + rS, r)`:
`σ(i) = i + rS` on `B`, `i − k` on `A`, `i` on `C` (the archive's `symIdx`). -/
def symIdx (k rS i : ℕ) : ℕ := if i < k then i + rS else if i < k + rS then i - k else i

/-- **The level subgroup** `Psym = ∏_{w ∈ SG} HPsymF_w` of the type group (spec-9 item 2): `u_ii = 1`, `u_ij = 0`
when `σ(j) < σ(i)` (`symIdx`), and `u_{i, k+rS} = 0` for `i < k`. The set is a group, so the closure adds nothing. -/
def Psym (r k rS : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E))) :
    Subgroup (∀ w : SG, GL (Fin r) (𝓞 E ⧸ w.1.asIdeal)) :=
  Subgroup.closure {u | ∀ w, (∀ i, (u w : Matrix (Fin r) (Fin r) (𝓞 E ⧸ w.1.asIdeal)) i i = 1) ∧
    (u w : Matrix (Fin r) (Fin r) (𝓞 E ⧸ w.1.asIdeal)).BlockTriangular (fun i => symIdx k rS i) ∧
    ∀ i j : Fin r, (i : ℕ) < k → (j : ℕ) = k + rS → (u w : Matrix (Fin r) (Fin r) (𝓞 E ⧸ w.1.asIdeal)) i j = 0}

/-- **The character of `Psym`** (spec-9 item 2), complex-valued as `ThetaChain.lamGen`:
`u ↦ ∏_{w ∈ SG} ψ₀(Σ_{i + 1 < r, i + 1 ≠ k} u_{w,i,i+1})`, `ψ₀ = psi0 xi0 w`: the generic superdiagonal sum with the
link `(k − 1, k)` omitted. -/
def chiSym (xi0 : E) (r k : ℕ) {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (u : ∀ w : SG, GL (Fin r) (𝓞 E ⧸ w.1.asIdeal)) : ℂ :=
  ∏ w : SG, psi0 xi0 w.1 (∑ i : Fin r, if h : (i : ℕ) + 1 < r ∧ (i : ℕ) + 1 ≠ k then
    (u w : Matrix (Fin r) (Fin r) (𝓞 E ⧸ w.1.asIdeal)) i ⟨i + 1, h.1⟩ else 0)

/-- **The point-level row space** `V0 = idemOf X (Amb ⊓ Amb_pt)` (spec-9 items 4–5): the `X`-part, for the type action
`tyRep lv`, of the `(P, ψ)`-isotypic functions in `AmbPt`. When `lv` normalises `Λ` and fixes `χ` (the archive's
`HK_normBy`), `AmbPt` is stable and this is `idemOf X (lvlIdem (AmbPt))`, the archive's `V0X = range goodAt`. -/
def V0pt {𝔊 : Type v} [Group 𝔊] [Fintype 𝔊] (τ : Φ → (E →+* L)) (sg : Φ → Fin n → ℤ)
    (ST : Finset (HeightOneSpectrum (𝓞 E))) {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) (χ : Λ → L)
    (lv : 𝔊 →* ∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) (P : Subgroup 𝔊) [Fintype P] (ψ : P →* L)
    (X : Finset (𝔊 → L)) : Submodule L (points (E := E) (ST := ST) Λ → Pol Φ n L) :=
  (Amb (tyRep lv _) P ψ ⊓ AmbPt τ sg Λ χ).map (idemOf (tyRep lv _) X)

end RowLevel

end RowSpace
