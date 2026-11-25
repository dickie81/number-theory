import Mathlib

/-!
# Hermitian spaces, decorated unimodular lattices and their classes

Layer L2 of the sharp frontier for the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`): the
hermitian spaces of the theta chain, the decorated unimodular lattices in them, the group that moves them, and their
classes with mass weights. Generic in the CM field `E`; only L0 and L7 know the fields of a setting.

**The space** (L2.1). `X = E^n` with `h(y, x) = Σᵢ conj(yᵢ) xᵢ` (`herm`), `conj` the complex conjugation of `E`
(`NumberField.IsCMField.complexConj`). The dual of an `O_E`-lattice is `N^# = {x : h(y, x) ∈ O_E ∀ y ∈ N}` (`dual`;
`h(y, x) = conj h(x, y)` and `O_E` is stable under `conj`, so this is the spec's `h(x, y) ∈ O_E`), and `N` is
unimodular if `N^# = N` (L2.2). `U_n(E)` (`U`) is the subgroup of `GL_n(E)` that preserves `h`; it carries duals to
duals (`dual_map`).

**Decorated lattices** (L2.3), with `Q = ∅`. For finite sets `ST`, `SG` of finite places of `E`, a point is
`d = (N, (f_P)_{P ∈ ST}, (be_w)_{w ∈ SG})` (`Deco`), with `f_P : N → O_E/P` nonzero and `O_E`-linear, and
`be_w : N ↠ (O_E/w)^n` with kernel `w·N` (`Deco.Good`). Linear maps on `N` see only `N/PN = N_(P)/P·N_(P)`, so `f_P`
on `N` is the spec's `f_P` on `N_(P)`. The attached lattice is `Lsh(d) = (N ∩ ⋂_P ker f_P)^#` (`Lsh`).

**The group** `𝒢 = U_n(E) × Λ_SG` (`Grp`) acts by `(γ, h)·d = (γN, f ∘ γ⁻¹, h·be ∘ γ⁻¹)`, a group action on the data
(`instMulActionDeco`) that keeps the conditions (`points`, a `SubMulAction`). Its character is `chr(γ, h) = χ_SG(h)`.
`Λ_SG ≤ ∏_{w ∈ SG} GL_n(O_E/w)` and `χ_SG` are parameters: the spec fixes them only at step 0 (the unitriangular
group with a generic character), and the archive picks them by existence choices at the later steps. The diamond
operators `dia` (L4.2) rescale the `f_P` and commute with `𝒢` (`dia_smul`).

**The twist `Q`.** The twisted case adds the frames `fr_P` at `P ∈ Q` and the factor `Θ_Q`; nothing below depends on
`Q = ∅` except `Deco` and `Grp`. The class machinery (`Cl`, `stab`, `mass`, `classSum`) is generic in a group action,
so a twisted point set plugs into it unchanged.

**Classes** (L2.4). `Cl G X = G\X` (`MulAction.orbitRel.Quotient`), `stab c` the stabiliser of the chosen
representative, the mass weight `mass c = 1/|Stab(c)|` (`Nat.card`, so `0` for an infinite stabiliser), which does
not depend on the representative (`mass_mk`), and `classSum F = Σᶠ_c mass(c)·F(c)` (`finsum`: no finiteness needed to
state). For decorated lattices, `DCl` with the representative `DCl.rep` and its lattice `DCl.N`, which L5.2 reads.

**The branching geometry** (L2.5). `X′ = E^n ⊂ X = E^{n+1} = X′ ⊕ E·z` (`incl`), with `z = e_last` (`eLast`), the lift
`til(L′) = L′ ⊕ tz⁻¹·O_E·e_last` (`til`, with `tz = conj(π_T)` a parameter), and `ext : U(X′) → U(X)`,
`γ ↦ diag(γ, 1)` (`ext`), which fixes `e_last` (`act_ext_eLast`). **The decorated lift** `tilQ tz` (audit 9, T1) takes
a decorated lattice of rank `n` to one of rank `n + 1` on the same frame places: the lattice `til 1 N = N ⊕ O_E·e_last`,
the level-`T` decorations `(tz·a) mod P` on the `e_last`-coordinate `a`, and the frames `(be_w, (a/conj(tz)) mod w)`.
With `ST` the places over `conj(tz)`, `Lsh(tilQ d) = til tz N`; L7's top step maps to the lift of each row point.

**Frames and `phiT`** (the archive's `liftFr`, `inFr`, `phiT`). The frame lift `liftFr d w` is a matrix whose column
`i` lies in `N` over `e_i` under `be_w` (`fr(O_(w)^n) = N_(w)` for a good `d`); `frAt d P` is it at `P ∈ SG` and `1`
elsewhere, and `inFr(fr, fr′, x) = fr′⁻¹·x·fr` reads a map in the frames. `phiT(d, d′, x)` is the level-`T` indicator:
`x` carries `N` into `N′_(P)` with `f′_P ∘ x = f_P` at every `P ∈ ST`. L7's factors read both (`ThetaVol`).

**Choices.** Matrices for `GL_n` and `U_n`, so later layers (`WeylFock`) can read `ρ(γ)` off the entries. The
decorations are data on the lattice itself (`↥N →ₗ[O_E] …`), compared by `Deco.ext'`. Following the spec's
"minimal", the T-Hecke data, `rp`/`pref`, `DGam`, `autO` and `autOrd` are dropped.

**Sanity theorems:** the `MulAction` instance, `Lsh_of_isEmpty`, `dia_smul`, `mass_mk`, `act_ext_eLast`.
-/

namespace HermClasses

open NumberField IsDedekindDomain Matrix

noncomputable section

/-! ### The hermitian space -/

section Space

variable {E : Type*} [Field E] {n : ℕ}

/-- `γ ∈ GL_n(E)` as an `O_E`-linear map of `E^n`. -/
def act (γ : GL (Fin n) E) : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
  (mulVecLin (γ : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)

/-- `act γ x = γx`. -/
@[simp] theorem act_apply (γ : GL (Fin n) E) (x : Fin n → E) :
    act γ x = (γ : Matrix (Fin n) (Fin n) E) *ᵥ x := rfl

/-- `act` is multiplicative. -/
theorem act_mul (γ δ : GL (Fin n) E) (x : Fin n → E) : act (γ * δ) x = act γ (act δ x) := by
  simp [mulVec_mulVec]

/-- `act 1` is the identity. -/
@[simp] theorem act_one (x : Fin n → E) : act 1 x = x := by simp

/-- `γ⁻¹(γx) = x`. -/
@[simp] theorem act_inv_act (γ : GL (Fin n) E) (x : Fin n → E) : act γ⁻¹ (act γ x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- `γ(γ⁻¹x) = x`. -/
@[simp] theorem act_act_inv (γ : GL (Fin n) E) (x : Fin n → E) : act γ (act γ⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

variable [NumberField E] [IsCMField E]

/-- The hermitian form `h(y, x) = Σᵢ conj(yᵢ) xᵢ` on `E^n`, as a linear map in `x`, with `conj` the complex
conjugation of the CM field `E`. -/
def hermL (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := ∑ i, IsCMField.complexConj E (y i) * x i
  map_add' x x' := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

/-- The hermitian form `h(y, x) = Σᵢ conj(yᵢ) xᵢ`. -/
def herm (y x : Fin n → E) : E := hermL y x

/-- The formula for `h`. -/
theorem herm_def (y x : Fin n → E) : herm y x = ∑ i, IsCMField.complexConj E (y i) * x i := rfl

/-- The dual lattice `N^# = {x : h(y, x) ∈ O_E for all y ∈ N}`. -/
def dual (N : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  ⨅ y ∈ N, (1 : Submodule (𝓞 E) E).comap ((hermL y).restrictScalars (𝓞 E))

/-- Membership in the dual lattice. -/
theorem mem_dual {N : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} :
    x ∈ dual N ↔ ∀ y ∈ N, herm y x ∈ (1 : Submodule (𝓞 E) E) := by
  simp [dual, Submodule.mem_iInf, herm]

/-- A lattice is unimodular if it is its own dual. -/
def IsUnimodular (N : Submodule (𝓞 E) (Fin n → E)) : Prop := dual N = N

variable (E n) in
/-- The unitary group `U_n(E)`: the matrices that preserve `h`. -/
def U : Subgroup (GL (Fin n) E) where
  carrier := {γ | ∀ x y, herm (act γ x) (act γ y) = herm x y}
  one_mem' := by simp
  mul_mem' ha hb x y := by rw [act_mul, act_mul, ha _ _, hb _ _]
  inv_mem' {γ} ha x y := by rw [← ha (act γ⁻¹ x), act_act_inv, act_act_inv]

/-- A unitary `γ` preserves `h`. -/
theorem herm_act {γ : GL (Fin n) E} (hγ : γ ∈ U E n) (x y : Fin n → E) :
    herm (act γ x) (act γ y) = herm x y :=
  hγ x y

omit [NumberField E] [IsCMField E] in
/-- `x ∈ γN` if and only if `γ⁻¹x ∈ N`. -/
theorem mem_map_act {γ : GL (Fin n) E} {N : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} :
    x ∈ N.map (act γ) ↔ act γ⁻¹ x ∈ N :=
  ⟨fun hx => by obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx; simpa, fun hx => ⟨_, hx, by simp⟩⟩

/-- A unitary `γ` carries duals to duals: `(γN)^# = γ(N^#)`. -/
theorem dual_map {γ : GL (Fin n) E} (hγ : γ ∈ U E n) (N : Submodule (𝓞 E) (Fin n → E)) :
    dual (N.map (act γ)) = (dual N).map (act γ) := by
  ext x
  rw [mem_map_act, mem_dual, mem_dual]
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · rw [← herm_act hγ, act_act_inv]; exact h _ (Submodule.mem_map_of_mem hy)
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    rw [← act_act_inv γ x, herm_act hγ]; exact h z hz

end Space

/-! ### Decorated lattices -/

section Deco

variable (E : Type*) [Field E] [NumberField E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E)))

/-- A decorated lattice `d = (N, (f_P)_{P ∈ ST}, (be_w)_{w ∈ SG})`, as data: an `O_E`-lattice `N ⊂ E^n`, linear
maps `f_P : N → O_E/P` (the level-`T` decoration), and `be_w : N → (O_E/w)^n`. The conditions are `Deco.Good`. -/
structure Deco where
  /-- The lattice. -/
  N : Submodule (𝓞 E) (Fin n → E)
  /-- The level-`T` decoration at `P ∈ ST`. -/
  f : ∀ P : ST, N →ₗ[𝓞 E] 𝓞 E ⧸ P.1.asIdeal
  /-- The level structure at `w ∈ SG`. -/
  be : ∀ w : SG, N →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ w.1.asIdeal)

variable {E n ST SG}

omit [NumberField E] in
/-- Two decorated lattices are equal if their lattices and their decorations agree. -/
theorem Deco.ext' {d d' : Deco E n ST SG} (hN : d.N = d'.N)
    (hf : ∀ P x (hx : x ∈ d.N) (hx' : x ∈ d'.N), d.f P ⟨x, hx⟩ = d'.f P ⟨x, hx'⟩)
    (hb : ∀ w x (hx : x ∈ d.N) (hx' : x ∈ d'.N), d.be w ⟨x, hx⟩ = d'.be w ⟨x, hx'⟩) : d = d' := by
  obtain ⟨N, f, be⟩ := d
  obtain ⟨N', f', be'⟩ := d'
  obtain rfl : N = N' := hN
  congr 1
  · funext P; exact LinearMap.ext fun x => hf P x x.2 x.2
  · funext w; exact LinearMap.ext fun x => hb w x x.2 x.2

/-- The conditions on a decorated lattice: `N` is unimodular, each `f_P` is nonzero, and each `be_w` is
surjective with kernel `w·N`. -/
structure Deco.Good [IsCMField E] (d : Deco E n ST SG) : Prop where
  unimod : IsUnimodular d.N
  f_ne : ∀ P, d.f P ≠ 0
  be_surj : ∀ w, Function.Surjective (d.be w)
  be_ker : ∀ w (x : d.N), d.be w x = 0 ↔ (x : Fin n → E) ∈ w.1.asIdeal • d.N


/-- The inverse of `γ`, from `γN` back to `N`. -/
def back (γ : GL (Fin n) E) (N : Submodule (𝓞 E) (Fin n → E)) : N.map (act γ) →ₗ[𝓞 E] N :=
  (act γ⁻¹).restrict fun x hx => by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    rwa [act_inv_act]

omit [NumberField E] in
/-- `back γ N` is `γ⁻¹`. -/
@[simp] theorem back_apply (γ : GL (Fin n) E) (N : Submodule (𝓞 E) (Fin n → E)) (x : N.map (act γ)) :
    (back γ N x : Fin n → E) = act γ⁻¹ x := rfl

/-- `h ∈ GL_n(R)`, for an `O_E`-algebra `R`, as an `O_E`-linear map of `R^n`. -/
def mv {R : Type*} [CommRing R] [Algebra (𝓞 E) R] (h : GL (Fin n) R) : (Fin n → R) →ₗ[𝓞 E] (Fin n → R) :=
  (mulVecLin (h : Matrix (Fin n) (Fin n) R)).restrictScalars (𝓞 E)

omit [NumberField E] in
/-- `mv h v = hv`. -/
@[simp] theorem mv_apply {R : Type*} [CommRing R] [Algebra (𝓞 E) R] (h : GL (Fin n) R) (v : Fin n → R) :
    mv (E := E) h v = (h : Matrix (Fin n) (Fin n) R) *ᵥ v := rfl

variable [IsCMField E] (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))

variable (E n SG) in
/-- The group `𝒢 = U_n(E) × Λ_SG` (with `Q = ∅`, so `Θ_Q` is trivial). The subgroup
`Λ_SG ≤ ∏_{w ∈ SG} GL_n(O_E/w)` is a parameter: the spec does not pin it beyond step 0. -/
abbrev Grp := U E n × Λ

/-- The action `(γ, h)·d = (γN, f ∘ γ⁻¹, h·be ∘ γ⁻¹)`. -/
instance : SMul (Grp E n SG Λ) (Deco E n ST SG) where
  smul g d :=
    { N := d.N.map (act g.1.1)
      f := fun P => (d.f P).comp (back g.1.1 d.N)
      be := fun w => (mv (g.2.1 w)).comp ((d.be w).comp (back g.1.1 d.N)) }

/-- The lattice of `g·d` is `γN`. -/
theorem smul_N (g : Grp E n SG Λ) (d : Deco E n ST SG) : (g • d).N = d.N.map (act g.1.1) := rfl

/-- The level-`T` decoration of `g·d` is `f ∘ γ⁻¹`. -/
theorem smul_f (g : Grp E n SG Λ) (d : Deco E n ST SG) (P : ST) (x : (g • d).N) :
    (g • d).f P x = d.f P (back g.1.1 d.N x) := rfl

/-- The level structure of `g·d` is `h·be ∘ γ⁻¹`. -/
theorem smul_be (g : Grp E n SG Λ) (d : Deco E n ST SG) (w : SG) (x : (g • d).N) :
    (g • d).be w x = mv (E := E) (g.2.1 w) (d.be w (back g.1.1 d.N x)) := rfl

/-- **The action is a group action.** -/
instance instMulActionDeco : MulAction (Grp E n SG Λ) (Deco E n ST SG) where
  one_smul d := Deco.ext' (by ext; simp [smul_N])
    (fun P x _ _ => by rw [smul_f]; exact congrArg (d.f P) (Subtype.ext (by simp)))
    (fun w x _ _ => by rw [smul_be]; simpa using congrArg (d.be w) (Subtype.ext (by simp)))
  mul_smul g g' d := Deco.ext' (by ext; simp [smul_N])
    (fun P x _ _ => by
      rw [smul_f, smul_f, smul_f]; exact congrArg (d.f P) (Subtype.ext (by simp)))
    (fun w x hx hx' => by
      have : back (g * g').1.1 d.N ⟨x, hx⟩ = back g'.1.1 d.N (back g.1.1 (g' • d).N ⟨x, hx'⟩) :=
        Subtype.ext (by simp)
      rw [smul_be, smul_be, smul_be, this]
      simp [mulVec_mulVec])

omit [NumberField E] in
/-- `back γ N` is onto. -/
theorem back_surj (γ : GL (Fin n) E) (N : Submodule (𝓞 E) (Fin n → E)) : Function.Surjective (back γ N) :=
  fun y => ⟨⟨act γ y, Submodule.mem_map_of_mem y.2⟩, Subtype.ext (by simp)⟩

omit [NumberField E] [IsCMField E] in
/-- An invertible `h` kills only `0`. -/
theorem mv_eq_zero {R : Type*} [CommRing R] [Algebra (𝓞 E) R] (h : GL (Fin n) R) {v : Fin n → R} :
    mv (E := E) h v = 0 ↔ v = 0 :=
  ⟨fun hv => by simpa [mulVec_mulVec] using congrArg (mv (E := E) h⁻¹) hv, fun hv => by simp [hv]⟩

omit [NumberField E] [IsCMField E] in
/-- An invertible `h` is onto. -/
theorem mv_surj {R : Type*} [CommRing R] [Algebra (𝓞 E) R] (h : GL (Fin n) R) :
    Function.Surjective (mv (E := E) h) :=
  fun v => ⟨mv (E := E) h⁻¹ v, by simp [mulVec_mulVec]⟩

/-- The decorated lattices `D`: the data satisfying `Deco.Good`, a set stable under `𝒢`. -/
def points : SubMulAction (Grp E n SG Λ) (Deco E n ST SG) where
  carrier := {d | d.Good}
  smul_mem' g d hd :=
    { unimod := by
        rw [IsUnimodular, smul_N, dual_map g.1.2, hd.unimod]
      f_ne := fun P h => hd.f_ne P <| LinearMap.ext fun y => by
        obtain ⟨x, rfl⟩ := back_surj g.1.1 d.N y
        exact LinearMap.congr_fun h x
      be_surj := fun w => by
        rw [show ⇑((g • d).be w) = mv (E := E) (g.2.1 w) ∘ d.be w ∘ back g.1.1 d.N from rfl]
        exact (mv_surj _).comp ((hd.be_surj w).comp (back_surj _ _))
      be_ker := fun w x => by
        rw [smul_be, mv_eq_zero, hd.be_ker, back_apply]
        have key (y : Fin n → E) :
            act g.1.1⁻¹ y ∈ w.1.asIdeal • d.N ↔ y ∈ w.1.asIdeal • d.N.map (act g.1.1) := by
          rw [← Submodule.map_smul'', mem_map_act]
        exact key x }

variable {Λ} in
/-- The character `chr(γ, h) = χ_SG(h)`, trivial on `U_n(E)`. The character `χ_SG` of `Λ_SG` is a parameter. -/
def chr {R : Type*} [Monoid R] (χ : Λ →* R) : Grp E n SG Λ →* R := χ.comp (MonoidHom.snd _ _)

/-- The level-`T` kernel `N ∩ ⋂_{P ∈ ST} ker f_P`, as a lattice in `E^n`. -/
def kerLat (d : Deco E n ST SG) : Submodule (𝓞 E) (Fin n → E) :=
  d.N ⊓ ⨅ P, (LinearMap.ker (d.f P)).map d.N.subtype

/-- The attached lattice `Lsh(d) = (N ∩ ⋂_{P ∈ ST} ker f_P)^#`. -/
def Lsh (d : Deco E n ST SG) : Submodule (𝓞 E) (Fin n → E) := dual (kerLat d)

/-- **Sanity:** with no level-`T` places, the attached lattice of a unimodular `N` is `N`. -/
theorem Lsh_of_isEmpty [IsEmpty ST] (d : Deco E n ST SG) (h : IsUnimodular d.N) : Lsh d = d.N := by
  simpa [Lsh, kerLat, IsUnimodular] using h

/-- The diamond operators `dia_a`, `a ∈ ∏_{P ∈ ST} (O_E/P)^×`: `f_P ↦ a_P·f_P` (L4.2). The spec's `⟨a⟩_P` acts
through `dia (Pi.mulSingle P a)`. -/
def dia (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : Deco E n ST SG) : Deco E n ST SG :=
  { d with f := fun P => (a P : 𝓞 E ⧸ P.1.asIdeal) • d.f P }

/-- **Sanity:** the diamond operators commute with `𝒢`. -/
theorem dia_smul (a : ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ) (g : Grp E n SG Λ) (d : Deco E n ST SG) :
    dia a (g • d) = g • dia a d :=
  Deco.ext' rfl (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

end Deco

/-! ### Classes, stabilisers, mass weights -/

section Classes

variable (G X : Type*) [Group G] [MulAction G X]

/-- The classes `G\X`. -/
abbrev Cl := MulAction.orbitRel.Quotient G X

variable {G X}

/-- The stabiliser of the chosen representative of a class. -/
def stab (c : Cl G X) : Subgroup G := MulAction.stabilizer G c.out

/-- The mass weight `1/|Stab(c)|` (`0` if the stabiliser is infinite). -/
def mass (c : Cl G X) : ℚ := (Nat.card (stab c) : ℚ)⁻¹

/-- The mass-weighted sum `Σ_c F(c)/|Stab(c)|` over the classes, as a `finsum`. -/
def classSum {M : Type*} [AddCommMonoid M] [Module ℚ M] (F : Cl G X → M) : M := ∑ᶠ c, mass c • F c

/-- **Sanity:** the mass weight does not depend on the representative. -/
theorem mass_mk (x : X) :
    mass (Quotient.mk (MulAction.orbitRel G X) x) = (Nat.card (MulAction.stabilizer G x) : ℚ)⁻¹ := by
  obtain ⟨g, hg⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x))
  rw [mass, stab, Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv]

end Classes

section DecoClasses

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))

variable (E n ST) in
/-- The classes `Cl = 𝒢\D` of decorated lattices. -/
abbrev DCl := Cl (Grp E n SG Λ) (points (E := E) (n := n) (ST := ST) Λ)

variable {Λ}

/-- The chosen representative of a class, the decorated lattice that later layers read (L5.2). -/
def DCl.rep (c : DCl E n ST Λ) : Deco E n ST SG := (c.out : Deco E n ST SG)

/-- The lattice `N_c` of a class. -/
def DCl.N (c : DCl E n ST Λ) : Submodule (𝓞 E) (Fin n → E) := c.rep.N

/-- The representative is a decorated lattice: it satisfies `Deco.Good`. -/
theorem DCl.good (c : DCl E n ST Λ) : c.rep.Good := c.out.2

end DecoClasses

/-! ### The branching geometry -/

section Branch

variable {E : Type*} [Field E] {n : ℕ}

/-- The last basis vector `e_last = z` of `X = E^{n+1} = X′ ⊕ E·z`. -/
def eLast : Fin (n + 1) → E := Pi.single (Fin.last n) 1

/-- The inclusion `X′ = E^n ↪ X = E^{n+1}`, `x ↦ (x, 0)`. -/
def incl : (Fin n → E) →ₗ[𝓞 E] (Fin (n + 1) → E) :=
  (Function.ExtendByZero.linearMap E Fin.castSucc).restrictScalars (𝓞 E)

/-- The lift `til(L′) = L′ ⊕ tz⁻¹·O_E·e_last`. Here `tz` is a parameter; the spec puts `tz = conj(π_T)`. -/
def til (tz : E) (L' : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin (n + 1) → E) :=
  L'.map incl ⊔ Submodule.span (𝓞 E) {tz⁻¹ • eLast}

/-- The block-diagonal embedding `A ↦ diag(A, 1)` of matrices. -/
def blk : Matrix (Fin n) (Fin n) E →* Matrix (Fin (n + 1)) (Fin (n + 1)) E where
  toFun A := reindexAlgEquiv E E finSumFinEquiv (fromBlocks A 0 0 1)
  map_one' := by simp
  map_mul' A B := by rw [← map_mul, fromBlocks_multiply]; simp

/-- The embedding `ext : GL(X′) → GL(X)`, `γ ↦ diag(γ, 1)`. -/
def extGL : GL (Fin n) E →* GL (Fin (n + 1)) E := Units.map blk

/-- `diag(A, 1)` acts by `A` on the first `n` coordinates. -/
theorem blk_mulVec_castSucc (A : Matrix (Fin n) (Fin n) E) (x : Fin (n + 1) → E) (i : Fin n) :
    (blk A *ᵥ x) i.castSucc = (A *ᵥ fun j => x j.castSucc) i := by
  simp [blk, mulVec, dotProduct, Fin.sum_univ_castSucc]

/-- `diag(A, 1)` fixes the last coordinate. -/
theorem blk_mulVec_last (A : Matrix (Fin n) (Fin n) E) (x : Fin (n + 1) → E) :
    (blk A *ᵥ x) (Fin.last n) = x (Fin.last n) := by
  simp [blk, mulVec, dotProduct, Fin.sum_univ_castSucc]

variable [NumberField E] [IsCMField E]

/-- `h` on `X = X′ ⊕ E·z` is the orthogonal sum of `h` on `X′` and on `E·z`. -/
theorem herm_succ (x y : Fin (n + 1) → E) :
    herm x y = herm (fun j => x j.castSucc) (fun j => y j.castSucc) +
      IsCMField.complexConj E (x (Fin.last n)) * y (Fin.last n) := by
  simp [herm_def, Fin.sum_univ_castSucc]

/-- The embedding `ext : U(X′) → U(X)`, `γ ↦ diag(γ, 1)`; its image fixes `e_last`. -/
def ext : U E n →* U E (n + 1) :=
  (extGL.comp (U E n).subtype).codRestrict (U E (n + 1)) fun γ x y => by
    have h (z : Fin (n + 1) → E) : act (extGL γ.1) z = blk γ.1.1 *ᵥ z := rfl
    rw [herm_succ, herm_succ, MonoidHom.comp_apply, Subgroup.coe_subtype, h, h, blk_mulVec_last,
      blk_mulVec_last]
    simp only [blk_mulVec_castSucc]
    exact congrArg (· + _) (herm_act γ.2 _ _)

/-- **Sanity:** `ext(γ)` fixes `e_last`, so `ext` lands in the stabiliser of `e_last`. -/
theorem act_ext_eLast (γ : U E n) : act (ext γ).1 eLast = eLast := by
  have h (z : Fin (n + 1) → E) : act (ext γ).1 z = blk γ.1.1 *ᵥ z := rfl
  funext i
  induction i using Fin.lastCases with
  | last => rw [h, blk_mulVec_last]
  | cast i => simp [h, blk_mulVec_castSucc, eLast, ← Pi.zero_def]

end Branch

/-! ### The decorated lift -/

section Lift

variable {E : Type*} [Field E] {n : ℕ}

/-- `N × O_E → E^{n+1}`, `(y, a) ↦ incl y + a·e_last`: an isomorphism onto `til 1 N = N ⊕ O_E·e_last` (`tilEquiv`). -/
def tilEmb (N : Submodule (𝓞 E) (Fin n → E)) : (N × 𝓞 E) →ₗ[𝓞 E] (Fin (n + 1) → E) :=
  (incl ∘ₗ N.subtype).coprod (LinearMap.toSpanSingleton (𝓞 E) _ eLast)

/-- `tilEmb` is injective: the first `n` coordinates give `y`, the last gives `a`. -/
theorem tilEmb_injective (N : Submodule (𝓞 E) (Fin n → E)) : Function.Injective (tilEmb N) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨y, a⟩ h
  have hi (x : Fin n → E) (j) : incl (E := E) x j = Function.extend Fin.castSucc x 0 j := rfl
  have h1 (i : Fin n) := congrFun h i.castSucc
  have h2 := congrFun h (Fin.last n)
  simp only [tilEmb, LinearMap.coprod_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.toSpanSingleton_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, hi,
    (Fin.castSucc_injective n).extend_apply, eLast] at h1 h2
  rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => Fin.castSucc_ne_last i hi] at h2
  simp only [Pi.single_eq_same, Pi.zero_apply, zero_add] at h2
  simp only [Pi.single_eq_of_ne (Fin.castSucc_ne_last _), smul_zero, add_zero] at h1
  rw [Algebra.smul_def, mul_one, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)] at h2
  exact Prod.ext (Subtype.ext (funext h1)) h2

/-- The range of `tilEmb` is `til 1 N`. -/
theorem range_tilEmb (N : Submodule (𝓞 E) (Fin n → E)) : LinearMap.range (tilEmb N) = til 1 N := by
  rw [tilEmb, LinearMap.range_coprod, LinearMap.range_comp, Submodule.range_subtype,
    ← LinearMap.span_singleton_eq_range, til, inv_one, one_smul]

/-- `N × O_E ≃ til 1 N = N ⊕ O_E·e_last`, `(y, a) ↦ incl y + a·e_last`. For `tilQ`. -/
def tilEquiv (N : Submodule (𝓞 E) (Fin n → E)) : (N × 𝓞 E) ≃ₗ[𝓞 E] til 1 N :=
  (LinearEquiv.ofInjective _ (tilEmb_injective N)).trans (LinearEquiv.ofEq _ _ (range_tilEmb N))

variable [NumberField E] [IsCMField E] {ST SG ST' : Finset (HeightOneSpectrum (𝓞 E))}

/-- **The decorated lift** `tilQ tz d` (the archive's `tilQ` = `Deco.til π`, `π = conj(tz)`; audit 9, T1) of a
decorated lattice `d = (N, f, be)` of rank `n` on the places `ST′`, `SG`, to rank `n + 1` on `ST` and the same frame
places `SG` (all frames kept, as in the archive; L7: `SG ∪ Q` at the row points): the lattice
`til 1 N = N ⊕ O_E·e_last` (`tilEquiv`), the level-`T` decorations `f_P(y + a·e_last) = (tz·a) mod P` at `P ∈ ST`
(the archive's `red_P(conj(π)·x_last)`), and the frames `be_w(y + a·e_last) = (be_w y, (a/conj(tz)) mod w)` at
`w ∈ SG` (the archive's `red_w(x_last/π)`; `Ring.inverse` is `0` if `conj(tz) ∈ w`, which the archive excludes:
`π ∉ w`). The `f` of `d` is not read. For `N` unimodular and `ST` the places over `conj(tz)` (`conj(tz)·O_E`
squarefree), `Lsh(tilQ d) = til tz N` (the unit `tz` at `P ∈ ST` does not move `ker f_P`). Meant for L7: the top step
of the chain maps to each row point through its lift (`SharpChain.IsThetaCol`, `ThetaChain.Top`). -/
def tilQ (tz : 𝓞 E) (d : Deco E n ST' SG) : Deco E (n + 1) ST SG where
  N := til 1 d.N
  f P := tz • (P.1.asIdeal.mkQ ∘ₗ LinearMap.snd _ _ _ ∘ₗ (tilEquiv d.N).symm.toLinearMap)
  be w := LinearMap.pi (Fin.snoc (α := fun _ => d.N × 𝓞 E →ₗ[𝓞 E] 𝓞 E ⧸ w.1.asIdeal)
      (fun i => LinearMap.proj i ∘ₗ d.be w ∘ₗ LinearMap.fst _ _ _)
      (Ring.inverse (Ideal.Quotient.mk w.1.asIdeal (IsCMField.ringOfIntegersComplexConj E tz)) •
        (w.1.asIdeal.mkQ ∘ₗ LinearMap.snd _ _ _))) ∘ₗ (tilEquiv d.N).symm.toLinearMap

end Lift

/-! ### Frames and the level-`T` indicator -/

section Frames

variable {E : Type*} [Field E] [NumberField E] {n a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

/-- **The frame lift** at `w ∈ SG` (the archive's `Deco.liftFr`): the matrix whose column `i` is a chosen `v ∈ N`
with `be_w(v) = e_i` (Hilbert choice, as the archive's `ε`). For a good `d` the columns reduce to a basis of `N/wN`,
so `fr(O_(w)^n) = N_(w)` and `fr` is fixed up to `1 + w·M_n(O_(w))`. Meant for L7 (`frAt`, `SharpChain.IsDetIdele`). -/
def liftFr (d : Deco E n ST SG) (w : SG) : Matrix (Fin n) (Fin n) E :=
  Matrix.of fun r i => (@Classical.epsilon d.N ⟨0⟩ fun v => d.be w v = Pi.single i 1 : Fin n → E) r

open Classical in
/-- The frame of `d` at a place `P`: `liftFr` at `P ∈ SG`, the identity elsewhere (no frame there). The chain's
factors read every matrix at `inFr (frAt d P) (frAt d′ P) x` (`ThetaVol.xiStd`, `xiCpl`, `xiTop`). -/
def frAt (d : Deco E n ST SG) (P : HeightOneSpectrum (𝓞 E)) : Matrix (Fin n) (Fin n) E :=
  if h : P ∈ SG then liftFr d ⟨P, h⟩ else 1

/-- `inFr(fr, fr′, x) = fr′⁻¹·x·fr`: `x : E^a → E^b` read in the frames `fr` of the source and `fr′` of the target
(the archive's `inFr`). Meant for L7, as `frAt`. -/
def inFr (fr : Matrix (Fin a) (Fin a) E) (fr' : Matrix (Fin b) (Fin b) E) (x : Matrix (Fin b) (Fin a) E) :
    Matrix (Fin b) (Fin a) E :=
  fr'⁻¹ * x * fr

/-- **The level-`T` indicator** (the archive's `phiT`): at every `P ∈ ST`, `x` maps `N` into `N′_(P)` and
`f′_P(x y) = f_P(y)`, read on `N′` through a denominator `s ∉ P` (`f′_P(s·xy) = s·f_P(y)`; `f′_P` kills `P·N′`, so `s`
does not matter). The only place the chain reads the decorations `f`; a factor of every step (`ThetaVol.xiStd`,
`xiCpl`, and `xiTop` with the target the lift `tilQ`). -/
def phiT (d : Deco E a ST SG) (d' : Deco E b ST SG') (x : Matrix (Fin b) (Fin a) E) : Prop :=
  ∀ (P : ST) (y : d.N), ∃ s : 𝓞 E, s ∉ P.1.asIdeal ∧
    ∃ h : (s : E) • (x *ᵥ (y : Fin a → E)) ∈ d'.N, d'.f P ⟨_, h⟩ = s • d.f P y

end Frames

end

end HermClasses
