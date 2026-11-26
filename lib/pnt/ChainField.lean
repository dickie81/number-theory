import SharpCons

/-!
# The coefficient field of the explicit chain

The coefficient field `K` of the construction once its period data are the explicit theta chain (chain spec §3.2;
the C1d row of its module plan), and the chain's lift characters `μ_{0,j}` with values in `K`. The field must contain
`τ(E)`, the values of the lift characters, the jets of the coset thetas that the chain's kernels read, the local
constants at the level places `SG` and the coordinate generators `g_p` of the constants `cD(p) = σ₀(g_p)` of
`ChainCanon.chainTP`. The characters are `K`-valued and `K` must contain their values; the circularity is broken by
choosing `ℂ`-valued characters first, then the field, then reading the characters in it.

**The `ℂ`-valued lift characters** (`muC`). For the translate `u` and the step `j`, `μ^ℂ_{0,j}` is an `ε` on the
`ℂ`-valued Hecke characters of type `−e_j` (`chainE`: the weights `e_j` of `hc u`, `0` from `m` on), unramified away
from the places over `g₀g₁` (`chainSg`) and tame there (`IsLiftC`; that one exists is the input C3, `HeckeType`). From
`j = m` on the weights vanish, so the characters repeat (`muC_of_le`): the family has at most `m + 1` members per
translate. Their values, over all translates and steps, are `chiVals`.

**The jets** (`ThetaChain.Data.jets`, `ThetaChain.Top.jets`). The jets of the coset thetas that the first `m` steps
of a chain read, and those of its top step: the sets on which `Data.JetsRat` and `Top.JetsRat` ask rationality
(`Data.jetsRat_iff`, `Top.jetsRat_iff`). They are complex numbers built from the chain's complex data alone (the
thetas, `δ`, `s`, `sd`, `cD`, the lattices and the Heisenberg data, through `σ₀ ∘ τ`), not from its characters or its
factors. So the jets of the Stage-U chain over `K` are those of the same chain over `L = ℂ` (`σ₀ = id`, `τ = S.τ`,
`cD = g_p`; over `K`, `σ₀ ∘ τ_K = S.τ` and `σ₀(gτK p) = g_p` under `KOk`). The field takes the jet set `J` as an
argument: the Stage-U chain (C1e) passes the jets of its `ℂ`-valued instance, of the steps below `m − 1` and of the
top, over all translates.

**The coordinate generators** (`gτC`). With `h = h_E` the class number, `𝔟^h` is principal; `genB 𝔟` is an `ε`
generator `a`, and `g_p = τ_p(a)^{−1/h}` (the principal root). Then `g_p^h = τ_p(a)⁻¹` (`gτC_pow`), so `(g_p)^h`
generates `τ_p(𝔟⁻¹)^h`, and `g_p` generates `τ_p(𝔟⁻¹)O_K` by the uniqueness of `h`-th roots of ideals in a Dedekind
domain. The ideal `𝔟` is an argument.

**The local constants** (`locGens`): at each `P ∈ SG`, `ζ_{q_P} = e^{2πi/q_P}` and `√q_P`, `q_P = N(P)`, so that the
values of the residue character `ψ₀` (`psi0_mem`) and the root `√q_P` (`sqrt_mem`) lie in any field containing them:
the hypotheses of `ChainLocal.locOk` on the field. The residue characters `χ_P = ν_P⁻¹` take the values of the lift
characters, so no `ζ_{q_P − 1}` is needed.

**The field** (`chainField`). With the generators `G = τ(E) ∪ locGens(SG) ∪ {g_p} ∪ chiVals ∪ J` (`chainGens`), `K` is
the normal closure of `ℚ(G)` in `ℂ` (`CoeffField.coeffClosure`) when `ℚ(G)` is finite-dimensional (`KOk`), and the
setting's field `sharpField S` otherwise. In the spec's terms `ℚ(G)` is the compositum of `ℚ(τ(E))`, the local
constants, `F_cD = ℚ(g_p)`, `F_χ = ℚ(chiVals)` and `F_J = ℚ(J)`. Either way `K` is a number field normal over `ℚ`
containing `τ(E)` (`finiteDimensional_chainField`, `normal_chainField`, `τ_mem_chainField`), so it carries the
construction's coefficient structure (`chainCoeff`, a `SharpCoeff`; `SharpChainU` takes it as the construction's).
Under `KOk` it contains every generator (`subset_chainField`). That `KOk` holds is not proved here; it reduces to the
two infinite families (`kOk_of`): the other generators are finitely many algebraic numbers, so `KOk` follows once
`F_χ` (C3) and `F_J` (C1) are finite-dimensional.

**The lift characters in `K`** (`muK`). `ThetaChain.Hecke.restrict` reads a `ℂ`-valued character in a subfield `F`
of `ℂ` when its values lie in `F` (the trivial character otherwise); it keeps the values (`Hecke.coe_restrict`), the
kernel, and so the type, the unramifiedness and the tameness (`Hecke.hasType_restrict`, `Hecke.unramAway_restrict`,
`Hecke.tame_restrict`). So under `KOk` the characters `μ_{0,j} = σ₀⁻¹ ∘ μ^ℂ_{0,j}` are lift characters over `K`
(`isLift_muK`). The coordinate generators in `K` are `gτK` (`coe_gτK`).

**Main declarations** (read by the Stage-U chain, C1e): `chainE`, `chainSg`, `muC`, `muK`, `gτC`, `gτK`,
`ThetaChain.Data.jets`, `ThetaChain.Top.jets`, `chainField`, `chainCoeff`; `KOk` and `IsLiftC` (the conditions C2f and
C3 prove), and `kOk_of` (C2f's reduction).

**Sanity theorems:** `muC_spec`, `muC_of_le`, `genB_spec`, `gτC_pow`, `psi0_mem`, `sqrt_mem`, `subset_chainField`,
`Hecke.coe_restrict`, `isLift_muK`, `coe_gτK`, `Data.jetsRat_iff`, `Top.jetsRat_iff`.
-/

noncomputable section

namespace ThetaChain

open NumberField IsDedekindDomain

/-! ## Characters read in a subfield of `ℂ` -/

section Restrict

variable {E : Type*} [Field E] [NumberField E]

/-- **The trivial Hecke character**, whose kernel, everything, is open. -/
def Hecke.one {L : Type*} [Field L] : Hecke E L := ⟨1, by simp⟩

variable {G : Type*} [Group G] (F : IntermediateField ℚ ℂ)

/-- **A `ℂ`-valued character with values in `F`, read in `F`.** -/
def resHom (f : G →* ℂˣ) (h : ∀ g, (f g : ℂ) ∈ F) : G →* Fˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ⟨f g, h g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => Subtype.ext (by simp) }

/-- **It has the kernel of `f`**, as `F → ℂ` is injective. -/
theorem ker_resHom (f : G →* ℂˣ) (h : ∀ g, (f g : ℂ) ∈ F) : (resHom F f h).ker = f.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Units.ext_iff, Units.ext_iff, Subtype.ext_iff]
  rfl

open Classical in
/-- **A `ℂ`-valued Hecke character read in `F`**: `χ` with its values in `F` when they all lie there, the trivial
character otherwise. -/
def Hecke.restrict (χ : Hecke E ℂ) : Hecke E F :=
  if h : ∀ a, (χ.toHom a : ℂ) ∈ F then ⟨resHom F χ.toHom h, by rw [ker_resHom]; exact χ.isOpen_ker⟩ else Hecke.one

variable {F} {χ : Hecke E ℂ}

/-- **The restriction keeps the values.** -/
theorem Hecke.coe_restrict (h : ∀ a, (χ.toHom a : ℂ) ∈ F) (a : Ideles E) :
    (((χ.restrict F).toHom a : F) : ℂ) = χ.toHom a := by
  rw [Hecke.restrict, dite_eq_left h]
  rfl

/-- **The restriction keeps the kernel.** -/
theorem Hecke.restrict_eq_one_iff (h : ∀ a, (χ.toHom a : ℂ) ∈ F) (a : Ideles E) :
    (χ.restrict F).toHom a = 1 ↔ χ.toHom a = 1 := by
  rw [Hecke.restrict, dite_eq_left h]
  exact SetLike.ext_iff.1 (ker_resHom F χ.toHom h) a

/-- **The restriction is unramified where `χ` is.** -/
theorem Hecke.unramAway_restrict (h : ∀ a, (χ.toHom a : ℂ) ∈ F) (Sg : Set (HeightOneSpectrum (𝓞 E))) :
    (χ.restrict F).UnramAway Sg ↔ χ.UnramAway Sg :=
  forall₂_congr fun a _ => Hecke.restrict_eq_one_iff h a

/-- **The restriction is tame where `χ` is.** -/
theorem Hecke.tame_restrict (h : ∀ a, (χ.toHom a : ℂ) ∈ F) (Sg : Set (HeightOneSpectrum (𝓞 E))) :
    (χ.restrict F).Tame Sg ↔ χ.Tame Sg :=
  forall₂_congr fun _ _ => forall₂_congr fun a _ => Hecke.restrict_eq_one_iff h a

/-- **The restriction has `χ`'s type** for embeddings `τ_F` into `F` with `τ_F = τ` in `ℂ`. -/
theorem Hecke.hasType_restrict [IsCMField E] {Φ : Type*} [Fintype Φ] {τ : Φ → (E →+* ℂ)} {τF : Φ → (E →+* F)}
    (h : ∀ a, (χ.toHom a : ℂ) ∈ F) (hτ : ∀ p z, (τF p z : ℂ) = τ p z) (e : Φ → ℤ) :
    (χ.restrict F).HasType τF e ↔ χ.HasType τ e := by
  refine forall_congr' fun a => ?_
  rw [← (algebraMap F ℂ).injective.eq_iff, map_prod]
  simp only [map_zpow₀, IntermediateField.algebraMap_apply, Hecke.coe_restrict h, hτ]

end Restrict

/-! ## The jets that a chain reads -/

section Jets

variable {E L : Type*} [Field E] [NumberField E] [IsCMField E] [Field L] {Φ : Type*} [Fintype Φ] [DecidableEq Φ]
  {τ : Φ → (E →+* L)}

/-- **The jets that the first `m` steps read**: `cD^μ·∂^μ θ(0)` for the coset theta of every step `j < m`, every
pair of classes, every coset point and every monomial `μ` (the range of `Data.JetsRat` below `m`). -/
def Data.jets (D : Data τ) (m : ℕ) : Set ℂ :=
  {z | ∃ j < m, ∃ (c : Cls D.n D.ST D.SG D.Q D.β D.Λ j) (c' : Cls D.n D.ST D.SG D.Q D.β D.Λ (j + 1))
    (x : Cosets D.S (D.cA j) (D.cB j) c.2.N c'.2.N) (mm : Φ × Fin (D.n (j + 1)) × Fin (D.n j) →₀ ℕ),
    jetVal D.P (thInd D.P.s D.P.sd (D.XD j c c') (thMoved τ D.P (D.θ j) c.2.N c'.2.N)
      (iota τ D.P (liftW D.S (D.cA j) (D.cB j) c.2.N c'.2.N (D.HA j c c') x))) mm = z}

/-- **`JetsRat` is rationality of the jets of every first `m` steps.** -/
theorem Data.jetsRat_iff (D : Data τ) : D.JetsRat ↔ ∀ m, D.jets m ⊆ Set.range D.P.σ₀ :=
  ⟨fun h _ _ ⟨j, _, c, c', x, mm, hz⟩ => hz ▸ h j c c' x mm,
    fun h j c c' x mm => h (j + 1) ⟨j, Nat.lt_succ_self j, c, c', x, mm, rfl⟩⟩

variable {D : Data τ} {m2 : ℕ} {SF : Finset (HeightOneSpectrum (𝓞 E))} {Yb X : Type*}

/-- **The jets that the top step reads**: those of the coset thetas from each class of level `m2 + 1` to the lattice
of each point (the range of `Top.JetsRat`). -/
def Top.jets (T : Top D m2 SF Yb X) : Set ℂ :=
  {z | ∃ (c : Cls D.n D.ST D.SG D.Q D.β D.Λ (m2 + 1)) (x : X)
    (y : Cosets D.S (D.cA (m2 + 1)) (D.cB (m2 + 1)) c.2.N (T.pt x).N)
    (mm : Φ × Fin (D.n (m2 + 2)) × Fin (D.n (m2 + 1)) →₀ ℕ),
    jetVal D.P (thInd D.P.s D.P.sd (T.XD c x) (thMoved τ D.P (D.θ (m2 + 1)) c.2.N (T.pt x).N)
      (iota τ D.P (liftW D.S (D.cA (m2 + 1)) (D.cB (m2 + 1)) c.2.N (T.pt x).N (T.HA c x) y))) mm = z}

/-- **`Top.JetsRat` is rationality of the top's jets.** -/
theorem Top.jetsRat_iff (T : Top D m2 SF Yb X) : T.JetsRat ↔ T.jets ⊆ Set.range D.P.σ₀ :=
  ⟨fun h _ ⟨c, x, y, mm, hz⟩ => hz ▸ h c x y mm, fun h c x y mm => h ⟨c, x, y, mm, rfl⟩⟩

end Jets

end ThetaChain

namespace ZetaBalance

open NumberField IsDedekindDomain ThetaChain CoeffField IntermediateField

/-! ## The `ℂ`-valued lift characters -/

section Chars

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-- **The weights `e_j` of the translate `u`**: those of `hc u`, read on `ℕ` (`0` from `m` on). -/
def chainE (u : S.A) (j : ℕ) : Φ S.A → ℤ := fun ρ => finN (Dg.hc u ρ).e j

/-- **The places over `g₀g₁`**, where the lift characters may ramify, tamely. -/
def chainSg : Set (HeightOneSpectrum (𝓞 S.E)) := {v | ((Dg.g₀ * Dg.g₁ : ℕ) : 𝓞 S.E) ∈ v.asIdeal}

/-- **A `ℂ`-valued lift character of step `j`**: of type `−e_j`, unramified away from the places over `g₀g₁` and
tame there. -/
def IsLiftC (u : S.A) (j : ℕ) (χ : Hecke S.E ℂ) : Prop :=
  χ.HasType S.τ (-chainE Dg u j) ∧ χ.UnramAway (chainSg Dg) ∧ χ.Tame (chainSg Dg)

/-- **The `ℂ`-valued lift character `μ^ℂ_{0,j}`** of the translate `u`: an `ε` on `IsLiftC` (one exists by C3,
`HeckeType`). -/
def muC (u : S.A) (j : ℕ) : Hecke S.E ℂ :=
  haveI : Nonempty (Hecke S.E ℂ) := ⟨Hecke.one⟩
  Classical.epsilon (IsLiftC Dg u j)

variable {Dg}

/-- **`μ^ℂ_{0,j}` is a lift character** when there is one. -/
theorem muC_spec {u : S.A} {j : ℕ} (h : ∃ χ, IsLiftC Dg u j χ) : IsLiftC Dg u j (muC Dg u j) :=
  haveI : Nonempty (Hecke S.E ℂ) := ⟨Hecke.one⟩
  Classical.epsilon_spec h

/-- **From `j = m` on the characters repeat**, as the weights vanish. -/
theorem muC_of_le (u : S.A) {j : ℕ} (hj : Dg.R.m ≤ j) : muC Dg u j = muC Dg u Dg.R.m := by
  have e : ∀ i, Dg.R.m ≤ i → chainE Dg u i = 0 := fun i hi => funext fun ρ => by simp [chainE, finN, not_lt.2 hi]
  have hP : IsLiftC Dg u j = IsLiftC Dg u Dg.R.m := by
    funext χ
    rw [IsLiftC, IsLiftC, e j hj, e _ le_rfl]
  rw [muC, muC, hP]

variable (Dg) in
/-- **The values of the `ℂ`-valued lift characters**, over all translates and steps. -/
def chiVals : Set ℂ := ⋃ (u : S.A) (j : ℕ), Set.range fun a : Ideles S.E => ((muC Dg u j).toHom a : ℂ)

end Chars

/-! ## The coordinate generators and the local constants -/

section Gens

variable {E : Type*} [Field E] [NumberField E]

/-- **A generator of `𝔟^h`**, `h = h_E` (an `ε`; `𝔟^h` is principal). -/
def genB (𝔟 : Ideal (𝓞 E)) : 𝓞 E := Classical.epsilon fun a : 𝓞 E => Ideal.span {a} = 𝔟 ^ classNumber E

/-- **The generator generates `𝔟^h`** when `𝔟^h` is principal. -/
theorem genB_spec {𝔟 : Ideal (𝓞 E)} (h : ∃ a : 𝓞 E, Ideal.span {a} = 𝔟 ^ classNumber E) :
    Ideal.span {genB 𝔟} = 𝔟 ^ classNumber E :=
  Classical.epsilon_spec h

/-- **The coordinate generators** `g_p = τ_p(a)^{−1/h}` (the principal root), `a = genB 𝔟`: `g_p` generates
`τ_p(𝔟⁻¹)O_K`. -/
def gτC {Φ : Type*} (τ : Φ → (E →+* ℂ)) (𝔟 : Ideal (𝓞 E)) (p : Φ) : ℂ :=
  (τ p (genB 𝔟 : E))⁻¹ ^ ((classNumber E : ℂ)⁻¹)

/-- **`g_p^h = τ_p(a)⁻¹`.** -/
theorem gτC_pow {Φ : Type*} (τ : Φ → (E →+* ℂ)) (𝔟 : Ideal (𝓞 E)) (p : Φ) :
    gτC τ 𝔟 p ^ classNumber E = (τ p (genB 𝔟 : E))⁻¹ :=
  Complex.cpow_nat_inv_pow _ (classNumber_ne_zero E)

/-- **The local constants at the level places**: `ζ_{q_P} = e^{2πi/q_P}` and `√q_P`, `q_P = N(P)`, `P ∈ SG`. -/
def locGens (SG : Finset (HeightOneSpectrum (𝓞 E))) : Set ℂ :=
  ⋃ P ∈ SG, {Complex.exp (2 * Real.pi * Complex.I / (Ideal.absNorm P.asIdeal : ℂ)),
    (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)}

variable {SG : Finset (HeightOneSpectrum (𝓞 E))} {F : IntermediateField ℚ ℂ} {P : HeightOneSpectrum (𝓞 E)}

/-- **The residue character takes values in `F`** at `P ∈ SG`: `ψ₀(c) = ζ_{q_P}^b` (`ChainLocal.locOk`'s `hψ`). -/
theorem psi0_mem (hF : locGens SG ⊆ F) (hP : P ∈ SG) (xi0 : E) (c : 𝓞 E ⧸ P.asIdeal) : psi0 xi0 P c ∈ F := by
  have e : psi0 xi0 P c = Complex.exp (2 * Real.pi * Complex.I / (Ideal.absNorm P.asIdeal : ℂ)) ^ resRep xi0 P c := by
    rw [psi0, ← Complex.exp_nat_mul]
    ring_nf
  rw [e]
  exact pow_mem (hF (Set.mem_iUnion₂.2 ⟨P, hP, Or.inl rfl⟩)) _

/-- **`√q_P ∈ F`** at `P ∈ SG` (`ChainLocal.locOk`'s `hsq`). -/
theorem sqrt_mem (hF : locGens SG ⊆ F) (hP : P ∈ SG) : (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ∈ F :=
  hF (Set.mem_iUnion₂.2 ⟨P, hP, Or.inr rfl⟩)

open Classical in
/-- **A complex number read in `F`**: `z` when `z ∈ F`, `0` otherwise. -/
def ofC (F : IntermediateField ℚ ℂ) (z : ℂ) : F := if h : z ∈ F then ⟨z, h⟩ else 0

/-- **`ofC` keeps the elements of `F`.** -/
theorem coe_ofC {z : ℂ} (h : z ∈ F) : (ofC F z : ℂ) = z := by
  rw [ofC, dite_eq_left h]

end Gens

/-! ## The field -/

section Field

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X) (𝔟 : Ideal (𝓞 S.E)) (J : Set ℂ)

/-- **The generators of the coefficient field**: `τ(E)` (`sharpGens`), the local constants at `SG`, the coordinate
generators `g_p`, the values of the lift characters and the jets `J`. -/
def chainGens : Set ℂ := sharpGens S ∪ locGens (sharpSG Dg) ∪ Set.range (gτC S.τ 𝔟) ∪ chiVals Dg ∪ J

/-- **The field's condition**: `ℚ(G)` is finite-dimensional (C2f, from C1 and C3). -/
def KOk : Prop := FiniteDimensional ℚ (adjoin ℚ (chainGens Dg 𝔟 J))

open Classical in
/-- **The coefficient field of the chain**: the normal closure of `ℚ(G)` in `ℂ` when `ℚ(G)` is finite-dimensional
(`KOk`), the setting's field `sharpField S` otherwise. -/
def chainField : IntermediateField ℚ ℂ := if KOk Dg 𝔟 J then coeffClosure (chainGens Dg 𝔟 J) else sharpField S

variable {Dg 𝔟 J}

/-- **Under `KOk` the field is the closure of the generators.** -/
theorem chainField_of_kOk (h : KOk Dg 𝔟 J) : chainField Dg 𝔟 J = coeffClosure (chainGens Dg 𝔟 J) := ite_eq_left h

/-- **Under `KOk` the field contains the generators.** -/
theorem subset_chainField (h : KOk Dg 𝔟 J) : chainGens Dg 𝔟 J ⊆ chainField Dg 𝔟 J := by
  rw [chainField_of_kOk h]
  exact subset_coeffClosure _

/-- **Under `KOk` the generators are algebraic**, as they lie in the finite-dimensional `ℚ(G)`. -/
theorem isIntegral_of_kOk (h : KOk Dg 𝔟 J) {z : ℂ} (hz : z ∈ chainGens Dg 𝔟 J) : IsIntegral ℚ z :=
  have : FiniteDimensional ℚ (adjoin ℚ (chainGens Dg 𝔟 J)) := h
  IntermediateField.isIntegral_iff.1 (IsIntegral.of_finite ℚ (⟨z, subset_adjoin ℚ _ hz⟩ : adjoin ℚ (chainGens Dg 𝔟 J)))

/-- **`KOk` from the two infinite families** (what remains of C2f): the other generators are finitely many algebraic
numbers (`τ(E)`, roots of unity, square roots of integers, `h`-th roots of algebraic numbers), so `ℚ(G)` is
finite-dimensional once `F_χ = ℚ(chiVals)` (C3) and `F_J = ℚ(J)` (C1) are. -/
theorem kOk_of (hχ : FiniteDimensional ℚ (adjoin ℚ (chiVals Dg))) (hJ : FiniteDimensional ℚ (adjoin ℚ J)) :
    KOk Dg 𝔟 J := by
  have hl : ∀ z ∈ locGens (sharpSG Dg), IsIntegral ℚ z := by
    simp only [locGens, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro z ⟨P, -, rfl | rfl⟩
    · have hn : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
      exact IsIntegral.of_pow (Nat.pos_of_ne_zero hn)
        (by rw [(Complex.isPrimitiveRoot_exp _ hn).pow_eq_one]; exact isIntegral_one)
    · refine IsIntegral.of_pow two_pos ?_
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      exact_mod_cast isIntegral_natCast _
  have hg : ∀ p, IsIntegral ℚ (gτC S.τ 𝔟 p) := fun p => IsIntegral.of_pow (classNumber_pos S.E) (by
    rw [gτC_pow]
    exact ((Algebra.IsIntegral.isIntegral (R := ℚ) _).map (S.τ p).toRatAlgHom).inv)
  have hfin : (sharpGens S ∪ locGens (sharpSG Dg) ∪ Set.range (gτC S.τ 𝔟)).Finite :=
    ((Set.finite_range _).union ((sharpSG Dg).finite_toSet.biUnion fun _ _ => Set.toFinite _)).union
      (Set.finite_range _)
  have := hfin.to_subtype
  have : FiniteDimensional ℚ (adjoin ℚ (sharpGens S ∪ locGens (sharpSG Dg) ∪ Set.range (gτC S.τ 𝔟))) :=
    finiteDimensional_adjoin fun z hz => by
      rcases hz with (hz | hz) | ⟨p, rfl⟩
      exacts [isIntegral_sharpGens z hz, hl z hz, hg p]
  rw [KOk, chainGens, adjoin_union, adjoin_union]
  infer_instance

variable (Dg 𝔟 J)

/-- **The field is finite-dimensional**: the normal closure of a finite-dimensional field, or `sharpField S`. -/
theorem finiteDimensional_chainField : FiniteDimensional ℚ (chainField Dg 𝔟 J) := by
  by_cases h : KOk Dg 𝔟 J
  · rw [chainField_of_kOk h]
    have : FiniteDimensional ℚ (adjoin ℚ (chainGens Dg 𝔟 J)) := h
    exact normalClosure.is_finiteDimensional ℚ (adjoin ℚ (chainGens Dg 𝔟 J)) ℂ
  · rw [chainField, ite_eq_right h]
    exact finiteDimensional_coeffClosure (Set.finite_range _) isIntegral_sharpGens

/-- **The field is a number field.** -/
instance numberField_chainField : NumberField (chainField Dg 𝔟 J) :=
  haveI := finiteDimensional_chainField Dg 𝔟 J
  ⟨⟩

/-- **The field is normal over `ℚ`**: a normal closure of algebraic numbers either way. -/
instance normal_chainField : Normal ℚ (chainField Dg 𝔟 J) := by
  by_cases h : KOk Dg 𝔟 J
  · rw [chainField_of_kOk h]
    exact normal_coeffClosure fun _ => isIntegral_of_kOk h
  · rw [chainField, ite_eq_right h]
    exact normal_coeffClosure isIntegral_sharpGens

/-- **`τ_ρ` lands in the field**: in `sharpField S`, or in the closure of `G ⊇ τ(E)`. -/
theorem τ_mem_chainField (ρ : Φ S.A) (z : S.E) : S.τ ρ z ∈ chainField Dg 𝔟 J := by
  by_cases h : KOk Dg 𝔟 J
  · exact map_mem_of_basis (Module.finBasis ℚ S.E) (S.τ ρ)
      (fun i => subset_chainField h (Or.inl (Or.inl (Or.inl (Or.inl ⟨(ρ, i), rfl⟩))))) z
  · rw [chainField, ite_eq_right h]
    exact τ_mem_sharpField ρ z

/-- **The coefficient structure of the chain's field** (`SharpCoeff`): `K = chainField`,
totally complex as `E` embeds in it, with complex conjugation as its star; `τ_K ρ = τ_ρ` with its codomain restricted
to `K`. -/
def chainCoeff : SharpCoeff S where
  K := chainField Dg 𝔟 J
  totallyComplex := isTotallyComplex_of_ringHom ((S.τ (1, 1)).codRestrict _ (τ_mem_chainField Dg 𝔟 J (1, 1)))
  star := instStarRing _
  τK ρ := (S.τ ρ).codRestrict _ (τ_mem_chainField Dg 𝔟 J ρ)

/-- **The lift characters `μ_{0,j} = σ₀⁻¹ ∘ μ^ℂ_{0,j}`** of the translate `u`, with values in the field. -/
def muK (u : S.A) (j : ℕ) : Hecke S.E (chainField Dg 𝔟 J) := (muC Dg u j).restrict _

/-- **The coordinate generators in the field** (`ChainCanon.chainTP`'s `g_τ`): `g_p` read in `K`. -/
def gτK (p : Φ S.A) : chainField Dg 𝔟 J := ofC _ (gτC S.τ 𝔟 p)

variable {Dg 𝔟 J}

/-- **Under `KOk` the lift characters take values in the field.** -/
theorem muC_mem (h : KOk Dg 𝔟 J) (u : S.A) (j : ℕ) (a : Ideles S.E) :
    ((muC Dg u j).toHom a : ℂ) ∈ chainField Dg 𝔟 J :=
  subset_chainField h (Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨u, j, a, rfl⟩)))

/-- **Under `KOk`, `μ_{0,j}` is a lift character over `K`** (type `−e_j` for `τ_K`, unramified away from `g₀g₁`,
tame there) when `μ^ℂ_{0,j}` is one. -/
theorem isLift_muK (h : KOk Dg 𝔟 J) {u : S.A} {j : ℕ} (hl : IsLiftC Dg u j (muC Dg u j)) :
    (muK Dg 𝔟 J u j).HasType (chainCoeff Dg 𝔟 J).τK (-chainE Dg u j) ∧ (muK Dg 𝔟 J u j).UnramAway (chainSg Dg) ∧
      (muK Dg 𝔟 J u j).Tame (chainSg Dg) :=
  ⟨(Hecke.hasType_restrict (muC_mem h u j) (fun _ _ => rfl) _).2 hl.1,
    (Hecke.unramAway_restrict (muC_mem h u j) _).2 hl.2.1, (Hecke.tame_restrict (muC_mem h u j) _).2 hl.2.2⟩

/-- **Under `KOk` the coordinate generators in the field are the `g_p`.** -/
theorem coe_gτK (h : KOk Dg 𝔟 J) (p : Φ S.A) : (gτK Dg 𝔟 J p : ℂ) = gτC S.τ 𝔟 p :=
  coe_ofC (subset_chainField h (Or.inl (Or.inl (Or.inr ⟨p, rfl⟩))))

end Field

end ZetaBalance
