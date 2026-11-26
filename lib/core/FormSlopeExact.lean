import HermFree

/-!
# The exact cut: the source of the forms as a sum of scaled class blocks

Part VIII of the exact slope bound (F) for the source of the sharp frontier, first stage: the statements C1–C3 about
forms and polynomials that the final bound C4 needs. C4 feeds them to Fischer's inequality over blocks
(`KLattice.degK_ge_sum`, K4, in `KLatticeVolume`) once Part V (`DeltaVolume`: the lattices `Δ_N` in the dual-basis
coordinates `dcoord`, with the constant metric `Γ`) is available. The source is the whole cut `V_ω`, that is the
frontier's `X_c = ⊤`.

**Hypotheses.** Every class has a trivial stabiliser (`hst`), and the diamond group `D = Π_{P∈ST}(O_E/P)^×` acts
freely on the classes (`hfr`). Both hold when the level group is unipotent at two places of distinct residue
characteristics (`free_of_uniAt`, from Part VII in `HermFree`), so at step 0 of the theta chain.

**The blocks.** `Orb` is the set of `D`-orbits on the classes, with representatives `c_o = o.out`, and
`B = {g ∈ D : g_P ≠ 1 for every P ∈ ST}` (`Bset`, a subtype of `D`). For `(g, o) ∈ B × Orb` and `Q ∈ VV(λ)`, the
block map (`thetaV`, into `V_ω`) is
`Θ_{g,o}(Q) = Π_{P∈ST}(⟨g_P⟩_P − 1)·ext(c_o, Q) = Σ_{S⊆ST} (−1)^{|ST∖S|}·⟨g_S⟩ ext(c_o, Q)` (`thetaF_eq_sum`), where
`g_S` is `g` on `S` and `1` off it (`gS`). The diamond operators commute, so the product is taken in the commutative
group algebra `L[D]`, which acts on the functions by them (`dAlg`): `θ_g = Π_P(⟨g_P⟩_P − 1)` (`thetaA`), and
`Θ_{g,o} = dAlg(θ_g) ∘ ext(c_o, ·)`.

**Main results.**
* **C1** (`thetaV_mem_Mω`): for `Q ∈ Δ_{Lsh(c_o)}` (`DeltaA`), `Θ_{g,o}Q` is an integral cut form, in `M_ω`.
* **C2** (`petAt_thetaV`): `H_σ(Θ_{g,o}Q, Θ_{g,o}Q') = 2^{|ST|}·fock(σQ, σQ')/κ` at every embedding `σ`. In the
  coordinates `dcoord` this is (h3) of K4, with `s = 2^{|ST|}` and the block `Δ_{Lsh(c_o)}`.
* **C3** (`bijective_sum_thetaV`): `(y_{g,o}) ↦ Σ_{(g,o)} Θ_{g,o}(y_{g,o})` is a bijection from `B × Orb → VV(λ)`
  onto `V_ω`, which is (h2) of K4.
Distinct blocks are also orthogonal, but K4 needs only the diagonal (h3), so this is not stated.

**The route.**
* C1. `ext(c_o, Q)` is integral in every local basis (`MintA`): its value is `Q` at `c_o` and `0` at the other
  classes. `MintA` is closed under the diamond operators and integer combinations (`dOp_mem_MintA`), and lies in `M`
  (`MintA_subset`, `exists_sand_uniform`). In `L[D]`, `Nm_P = Σ_u ⟨u⟩_P` kills `⟨g_P⟩_P − 1` (`sum_mul_eP`), so
  `Nm_P Θ = 0` (`Nm_dAlg_thetaA`).
* Values at representatives. With trivial stabilisers, `(⟨a⟩ext(c, Q))(c') = actP_h Q` if `a·c' = c`, for an `h`
  independent of `Q` (`exists_dOp_ext_out`), and `0` otherwise (`dOp_ext_out_eq_zero`).
* C2. Expand both sides over the subsets and use sesquilinearity (`petAt_sum_smul`).
  `H_σ(⟨a⟩ext(c, Q), ⟨a'⟩ext(c, Q'))` is `fock(σQ, σQ')/κ` if `a = a'`: there is one class `a⁻¹c` in the support,
  of mass `1`, and `actP` is Fock-unitary (`fockWith_map_actP`). It is `0` if `a ≠ a'`, as the supports `a⁻¹c` and
  `a'⁻¹c` are distinct by freeness (`petAt_dOp_ext`). The `g_S` are distinct as every `g_P ≠ 1` (`gS_inj`), so the
  `2^{|ST|}` diagonal terms remain, each with sign `(±1)² = 1`.
* C3, injective (`sumF_injective`). At the class `g'^{-1}c_{o'}` only the block `(g', o')` and its term `S = ST`
  survive: `g_S·g'^{-1}c_{o'} = c_o` forces `o = o'` (orbits) and `g_S = g'` (freeness), hence `S = ST` and `g = g'`
  (`eq_of_gS_smul`). That term is `actP_h y_{g',o'}`, and `actP_h` is invertible.
* C3, onto (`mem_range_sumF`). Put `X = Π_P Σ_u (⟨u⟩_P − 1) ∈ L[D]`. On `V_ω`, `Σ_u(⟨u⟩_P − 1) = Nm_P − N_P = −N_P`,
  so `X` acts as the nonzero scalar `Π_P(−N_P)` (`dAlg_prod_eP`). Every form is `Σ_c ext(c, F(c))` (`eq_sum_ext`),
  and `ext(c, P) = ⟨b⟩ext(c_o, Q)` for the orbit `o` of `c` and some `b`, `Q` (`exists_ext_eq_dOp`: both are forms,
  with the same values at the representatives). In `L[D]`, `⟨b⟩Σ_u(⟨u⟩_P − 1) = Σ_u(⟨u⟩_P − 1) − N_P(⟨b_P⟩_P − 1)` at
  each place, so by distributivity (`Finset.prod_univ_sum`)
  `X·⟨b⟩ = Π_P Σ_u (1 − N_P[u = b_P])(⟨u⟩_P − 1) = Σ_{x∈D} (Π_P(1 − N_P[x_P = b_P]))·θ_x` (`prod_sum_eP_mul_of`).
  Here `θ_x = 0` unless `x ∈ B` (`thetaA_eq_zero`), and `θ_x·ext(c_o, Q) = Θ_{x,o}Q` for `x ∈ B`.

**What remains** (C4). Apply K4 with the blocks `Y_{g,o} = Δ_{Lsh(c_o)}` in `dcoord` coordinates, the maps
`Θ_{g,o}` composed with `dcoord⁻¹` and the coordinates of `V_ω`, and `s = 2^{|ST|}`: (h1) is C1, (h2) is C3, and (h3)
is C2 with `fock(σQ, σQ')/κ = Γ` on the `dcoord` basis (Part V). Then V6 and V7 give `μ(source) ≥ −c_F`.
-/

namespace HermForms

open NumberField IsDedekindDomain HermClasses WeylFock MvPolynomial

open scoped Classical

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))}
  {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type} [Field L]

attribute [local instance] finite_units

/-! ## The diamond group algebra -/

section Alg

variable (ST) in
/-- The diamond group `D = Π_{P ∈ ST} (O_E/P)^×`. -/
abbrev Dia := ∀ P : ST, (𝓞 E ⧸ P.1.asIdeal)ˣ

variable (ST) in
/-- The set `B = {g ∈ D : g_P ≠ 1 for every P ∈ ST}`, indexing the blocks of one orbit. -/
def Bset := {g : Dia ST // ∀ P, g P ≠ 1}

/-- `B` is finite, as the residue fields are. -/
instance : Fintype (Bset ST) := @Fintype.ofFinite _ (inferInstanceAs (Finite {g : Dia ST // ∀ P, g P ≠ 1}))

variable (E n ST Λ) in
/-- The orbits of the diamond group on the classes; the representative of `o` is `o.out`. -/
abbrev Orb := MulAction.orbitRel.Quotient (Dia ST) (DCl E n ST Λ)

/-- There are finitely many orbits, as there are finitely many classes (`finite_DCl`). -/
instance : Fintype (Orb E n ST Λ) :=
  have := finite_DCl E n ST SG Λ
  Fintype.ofFinite _

/-- **The hypotheses of the blocks, from two places** (Part VII): if `Λ` is unipotent at two places of distinct
residue characteristics, the stabilisers are trivial (`stab_eq_bot`) and the diamond action on the classes is free
(`diaCl_free`). -/
theorem free_of_uniAt (w₀ w₁ : SG) {p₀ p₁ : ℕ} (hp₀ : p₀.Prime) (hp₁ : p₁.Prime) (hp : p₀ ≠ p₁)
    (h₀ : (p₀ : 𝓞 E) ∈ w₀.1.asIdeal) (h₁ : (p₁ : 𝓞 E) ∈ w₁.1.asIdeal) (hu₀ : UniAt Λ w₀) (hu₁ : UniAt Λ w₁) :
    (∀ c : DCl E n ST Λ, stab c = ⊥) ∧ ∀ (a : Dia ST) (c : DCl E n ST Λ), a • c = c → a = 1 :=
  ⟨stab_eq_bot w₀ w₁ hp₀ hp₁ hp h₀ h₁ hu₀ hu₁, fun _ _ h => diaCl_free w₀ w₁ hp₀ hp₁ hp h₀ h₁ hu₀ hu₁ h⟩

variable (Λ Φ L) in
/-- The diamond operators as a monoid hom `D →* End_L(Fn)`: `⟨a⟩⟨b⟩ = ⟨ba⟩ = ⟨ab⟩` (`dOp_dOp`). -/
def dHom : Dia ST →* Module.End L (Fn ST Λ Φ L) where
  toFun := dOp
  map_one' := LinearMap.ext fun F => funext fun d => congrArg F (diaPt_one d)
  map_mul' a b := LinearMap.ext fun F => by rw [Module.End.mul_apply, dOp_dOp, mul_comm]

variable (Λ Φ L) in
/-- The group algebra `L[D]` acting on the functions by the diamond operators. -/
def dAlg : MonoidAlgebra L (Dia ST) →ₐ[L] Module.End L (Fn ST Λ Φ L) :=
  MonoidAlgebra.lift L (Module.End L (Fn ST Λ Φ L)) (Dia ST) (dHom Λ Φ L)

omit [Fintype Φ] [DecidableEq Φ] in
/-- `a ∈ D` acts as `⟨a⟩`. -/
theorem dAlg_of (a : Dia ST) : dAlg Λ Φ L (MonoidAlgebra.of L _ a) = dOp a :=
  MonoidAlgebra.lift_of _ _

omit [Fintype Φ] [DecidableEq Φ] in
/-- `r·a ∈ L[D]` acts as `r·⟨a⟩`. -/
theorem dAlg_single (a : Dia ST) (r : L) : dAlg Λ Φ L (MonoidAlgebra.single a r) = r • dOp a :=
  MonoidAlgebra.lift_single _ _ _

omit [Fintype Φ] [DecidableEq Φ] in
/-- The action is multiplicative. -/
theorem dAlg_mul_apply (x y : MonoidAlgebra L (Dia ST)) (F : Fn ST Λ Φ L) :
    dAlg Λ Φ L (x * y) F = dAlg Λ Φ L x (dAlg Λ Φ L y F) := by
  rw [map_mul, Module.End.mul_apply]

variable (L) in
/-- `⟨u⟩_P − 1 ∈ L[D]`, for `u ∈ (O_E/P)^×`. -/
def eP (P : ST) (u : (𝓞 E ⧸ P.1.asIdeal)ˣ) : MonoidAlgebra L (Dia ST) :=
  MonoidAlgebra.of L _ (Pi.mulSingle P u) - 1

variable (L) in
/-- `θ_g = Π_{P ∈ ST} (⟨g_P⟩_P − 1) ∈ L[D]`. -/
def thetaA (g : Dia ST) : MonoidAlgebra L (Dia ST) := ∏ P, eP L P (g P)

/-- `g_S = Π_{P ∈ S} ⟨g_P⟩_P`: the diamond `g` on `S` and `1` off it. -/
def gS (g : Dia ST) (S : Finset ST) : Dia ST := ∏ P ∈ S, Pi.mulSingle P (g P)

omit [NumberField E] [IsCMField E] in
/-- `g_S` at `P` is `g_P` on `S` and `1` off it. -/
theorem gS_apply (g : Dia ST) (S : Finset ST) (P : ST) : gS g S P = if P ∈ S then g P else 1 := by
  rw [gS, Finset.prod_apply, Finset.prod_pi_mulSingle]

omit [NumberField E] [IsCMField E] in
/-- `g_{ST} = g`. -/
theorem gS_univ (g : Dia ST) : gS g Finset.univ = g := Finset.univ_prod_mulSingle g

omit [NumberField E] [IsCMField E] in
/-- For `g ∈ B` the `g_S` are distinct: `g_S = g_{S'}` forces `S = S'`. -/
theorem gS_inj {g : Dia ST} (hg : ∀ P, g P ≠ 1) {S S' : Finset ST} : gS g S = gS g S' ↔ S = S' := by
  refine ⟨fun h => Finset.ext fun P => ?_, fun h => h ▸ rfl⟩
  have := congrFun h P
  rw [gS_apply, gS_apply] at this
  by_cases h1 : P ∈ S <;> by_cases h2 : P ∈ S' <;> simp only [h1, h2, ↓reduceIte] at this
  · simp [h1, h2]
  · exact absurd this (hg P)
  · exact absurd this.symm (hg P)
  · simp [h1, h2]

omit [NumberField E] [IsCMField E] in
/-- **The expansion over subsets**: `θ_g = Σ_{S⊆ST} (−1)^{|ST∖S|}·g_S` (`Finset.prod_add`). -/
theorem thetaA_eq_sum (g : Dia ST) :
    thetaA L g = ∑ S : Finset ST, MonoidAlgebra.single (gS g S) ((-1 : L) ^ (Finset.univ \ S).card) := by
  simp only [thetaA, eP, sub_eq_add_neg]
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_const, ← map_prod, show ((-1 : MonoidAlgebra L (Dia ST)) ^ (Finset.univ \ S).card) =
      algebraMap L _ ((-1) ^ (Finset.univ \ S).card) by rw [map_pow, map_neg, map_one], ← Algebra.commutes,
    ← Algebra.smul_def, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one, gS]

omit [NumberField E] [IsCMField E] in
/-- `θ_g = 0` if some `g_P = 1`. -/
theorem thetaA_eq_zero {g : Dia ST} {P : ST} (h : g P = 1) : thetaA L g = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ P) (by rw [eP, h, Pi.mulSingle_one, map_one, sub_self])

omit [NumberField E] [IsCMField E] in
/-- Translation by `⟨b⟩_P` permutes the `⟨u⟩_P`: `Σ_u ⟨u⟩_P⟨b⟩_P = Σ_u ⟨u⟩_P`. -/
theorem sum_of_mul_of (P : ST) [Fintype (𝓞 E ⧸ P.1.asIdeal)ˣ] (b : (𝓞 E ⧸ P.1.asIdeal)ˣ) :
    ∑ u, MonoidAlgebra.of L (Dia ST) (Pi.mulSingle P u) * MonoidAlgebra.of L (Dia ST) (Pi.mulSingle P b) =
      ∑ u, MonoidAlgebra.of L (Dia ST) (Pi.mulSingle P u) :=
  Fintype.sum_equiv (Equiv.mulRight b) _ _ fun u => by rw [← map_mul, ← Pi.mulSingle_mul]; rfl

omit [NumberField E] [IsCMField E] in
/-- `Nm_P·(⟨u⟩_P − 1) = 0` in `L[D]`. -/
theorem sum_mul_eP (P : ST) [Fintype (𝓞 E ⧸ P.1.asIdeal)ˣ] (u : (𝓞 E ⧸ P.1.asIdeal)ˣ) :
    (∑ v, MonoidAlgebra.of L (Dia ST) (Pi.mulSingle P v)) * eP L P u = 0 := by
  rw [eP, mul_sub, mul_one, Finset.sum_mul, sum_of_mul_of, sub_self]

omit [Fintype Φ] [DecidableEq Φ] in
/-- `Nm_P` is the action of `Σ_u ⟨u⟩_P ∈ L[D]`. -/
theorem Nm_eq_dAlg [NumberField L] (P : ST) [Fintype (𝓞 E ⧸ P.1.asIdeal)ˣ] :
    (Nm P : Module.End L (Fn ST Λ Φ L)) = dAlg Λ Φ L (∑ v, MonoidAlgebra.of L (Dia ST) (Pi.mulSingle P v)) := by
  rw [Nm, finsum_eq_sum_of_fintype, map_sum]
  simp only [dAlg_of]

omit [Fintype Φ] [DecidableEq Φ] in
/-- **`θ_g` maps into the kernel of every `Nm_P`**, as `Nm_P·(⟨g_P⟩_P − 1) = 0`. -/
theorem Nm_dAlg_thetaA [NumberField L] (P : ST) (g : Dia ST) (F : Fn ST Λ Φ L) :
    Nm P (dAlg Λ Φ L (thetaA L g) F) = 0 := by
  let := Fintype.ofFinite (𝓞 E ⧸ P.1.asIdeal)ˣ
  rw [Nm_eq_dAlg, ← dAlg_mul_apply, thetaA, ← Finset.mul_prod_erase _ _ (Finset.mem_univ P), ← mul_assoc,
    sum_mul_eP, zero_mul, map_zero, LinearMap.zero_apply]

end Alg

/-! ## The blocks of an orbit -/

section Blocks

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- `ext c` on `VV(λ)`, as a linear map (`ext_sum_smul`). -/
def extL (c : DCl E n ST Λ) : VV (L := L) lam →ₗ[L] Fn ST Λ Φ L where
  toFun Q := ext τ χ lam c Q
  map_add' P Q := by
    have := ext_sum_smul τ χ lam c (Finset.univ : Finset (Fin 2)) (fun _ => 1) ![(P : Pol Φ n L), Q]
    simpa [Fin.sum_univ_two] using this
  map_smul' a Q := by
    have := ext_sum_smul τ χ lam c (Finset.univ : Finset (Fin 1)) (fun _ => a) ![(Q : Pol Φ n L)]
    simpa using this

/-- **The block map** `Θ_{g,o}(Q) = θ_g·ext(c_o, Q) = Π_{P∈ST}(⟨g_P⟩_P − 1) ext(c_o, Q)` on the functions, for
`g ∈ B` and an orbit `o` with representative `c_o = o.out`. -/
def thetaF (i : Bset ST × Orb E n ST Λ) : VV (L := L) lam →ₗ[L] Fn ST Λ Φ L :=
  (dAlg Λ Φ L (thetaA L i.1.1)).comp (extL τ χ lam i.2.out)

/-- **The block map, expanded**: `Θ_{g,o}(Q) = Σ_{S⊆ST} (−1)^{|ST∖S|}·⟨g_S⟩ ext(c_o, Q)`. -/
theorem thetaF_eq_sum (i : Bset ST × Orb E n ST Λ) (Q : VV (L := L) lam) :
    thetaF τ χ lam i Q =
      ∑ S : Finset ST, ((-1 : L) ^ (Finset.univ \ S).card) • dOp (gS i.1.1 S) (ext τ χ lam i.2.out Q) := by
  rw [thetaF, LinearMap.comp_apply, thetaA_eq_sum, map_sum, LinearMap.sum_apply]
  simp only [dAlg_single, LinearMap.smul_apply]
  rfl

omit [DecidableEq Φ] in
/-- `⟨a⟩ext(c, Q)` vanishes at the representatives of the classes `c'` with `a·c' ≠ c`. -/
theorem dOp_ext_out_eq_zero {a : Dia ST} {c c' : DCl E n ST Λ} (h : a • c' ≠ c) (Q : Pol Φ n L) :
    dOp a (ext τ χ lam c Q) c'.out = 0 :=
  ext_eq_zero τ χ lam h Q

omit [DecidableEq Φ] in
/-- With trivial stabilisers every value is invariant. -/
theorem inv_of_stab (hst : ∀ c : DCl E n ST Λ, stab c = ⊥) (c : DCl E n ST Λ) (Q : Pol Φ n L) :
    Inv τ χ lam c Q := fun h hh => by
  rw [hst c, Subgroup.mem_bot] at hh
  rw [hh, actP_one]

omit [DecidableEq Φ] in
/-- If `a·c' = c`, then `⟨a⟩ext(c, Q)` has the value `actP_g Q` at the representative of `c'`, for one `g`
independent of `Q`: `dia_a(c'.out) = g·c.out`. -/
theorem exists_dOp_ext_out (hst : ∀ c : DCl E n ST Λ, stab c = ⊥) {a : Dia ST} {c c' : DCl E n ST Λ}
    (h : a • c' = c) : ∃ g : Grp E n SG Λ, ∀ Q, dOp a (ext τ χ lam c Q) c'.out = actP τ χ lam g Q := by
  obtain ⟨g, hg⟩ := exists_smul_out (c := c) (d := diaPt a c'.out) h
  exact ⟨g, fun Q => by
    show ext τ χ lam c Q (diaPt a c'.out) = _
    rw [← hg, ext_smul_out τ χ lam (inv_of_stab τ χ lam hst c Q)]⟩

/-- With trivial stabilisers every mass is `1`. -/
theorem mass_of_stab (hst : ∀ c : DCl E n ST Λ, stab c = ⊥) (c : DCl E n ST Λ) : mass c = 1 := by
  rw [mass, hst c, Subgroup.card_bot, Nat.cast_one, inv_one]

/-- For a free action, `a·c = b·c` forces `a = b`. -/
theorem eq_of_smul_eq (hfr : ∀ (a : Dia ST) (c : DCl E n ST Λ), a • c = c → a = 1) {a b : Dia ST}
    {c : DCl E n ST Λ} (h : a • c = b • c) : a = b :=
  (inv_mul_eq_one.1 (hfr (b⁻¹ * a) c (by rw [mul_smul, h, inv_smul_smul]))).symm

omit [DecidableEq Φ] in
/-- The action keeps the normalised Fock form at every embedding (`fockWith_map_actP`). -/
theorem fock_map_actP (g : Grp E n SG Λ) (σ : L →+* ℂ) (P Q : Pol Φ n L) :
    fock (fun ρ => natW (lam ρ)) (map σ (actP τ χ lam g P)) (map σ (actP τ χ lam g Q)) =
      fock (fun ρ => natW (lam ρ)) (map σ P) (map σ Q) := by
  rw [fock, fock, fockWith_map_actP]

omit [DecidableEq Φ] in
/-- **Diamond translates of one class block**: `H_σ(⟨a⟩ext(c, Q), ⟨a'⟩ext(c, Q'))` is `fock(σQ, σQ')` if `a = a'`
(one class `a⁻¹c`, mass `1`, `actP` unitary) and `0` otherwise (the classes `a⁻¹c ≠ a'⁻¹c`, by freeness). -/
theorem petAt_dOp_ext (hst : ∀ c : DCl E n ST Λ, stab c = ⊥)
    (hfr : ∀ (a : Dia ST) (c : DCl E n ST Λ), a • c = c → a = 1) (σ : L →+* ℂ) (a a' : Dia ST)
    (c : DCl E n ST Λ) (Q Q' : Pol Φ n L) :
    petAt ST lam σ (dOp a (ext τ χ lam c Q)) (dOp a' (ext τ χ lam c Q')) =
      if a = a' then fock (fun ρ => natW (lam ρ)) (map σ Q) (map σ Q') else 0 := by
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  rw [petAt_eq_sum]
  simp only [mass_of_stab hst, Rat.cast_one, one_mul]
  split_ifs with ha
  · subst ha
    rw [Finset.sum_eq_single (a⁻¹ • c)]
    · obtain ⟨g, hg⟩ := exists_dOp_ext_out τ χ lam hst (smul_inv_smul a c)
      rw [hg, hg, fock_map_actP]
    · intro c' _ hc'
      rw [dOp_ext_out_eq_zero τ χ lam (fun h => hc' (by rw [← h, inv_smul_smul])), map_zero]
      simp [fock, fockWith]
    · simp
  · refine Finset.sum_eq_zero fun c' _ => ?_
    by_cases h : a • c' = c
    · rw [dOp_ext_out_eq_zero τ χ lam (a := a') (fun h' => ha (eq_of_smul_eq hfr (h.trans h'.symm))) Q',
        map_zero]
      simp [fock, fockWith]
    · rw [dOp_ext_out_eq_zero τ χ lam h, map_zero]
      simp [fock, fockWith]

/-- The diamond operators, hence `θ_g`, keep the forms (`dOp_mem`). -/
theorem dAlg_thetaA_mem_Forms (g : Dia ST) {F : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) :
    dAlg Λ Φ L (thetaA L g) F ∈ Forms ST τ χ lam := by
  rw [thetaA_eq_sum, map_sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun S _ => by
    rw [dAlg_single, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (dOp_mem ST τ χ lam _ hF)

/-- With trivial stabilisers, `ext(c, Q)` is a form for every `Q ∈ VV(λ)` (`ext_mem_Forms`). -/
theorem ext_mem_Forms_of_stab (hst : ∀ c : DCl E n ST Λ, stab c = ⊥) (c : DCl E n ST Λ) (Q : VV (L := L) lam) :
    ext τ χ lam c Q ∈ Forms ST τ χ lam :=
  ext_mem_Forms τ χ lam Q.2 (inv_of_stab τ χ lam hst c Q)

/-- The block maps into the cut: `Θ_{g,o}Q` is a form killed by every `Nm_P` (`Nm_dAlg_thetaA`). -/
theorem thetaF_mem_Vω [NumberField L] (hst : ∀ c : DCl E n ST Λ, stab c = ⊥) (i : Bset ST × Orb E n ST Λ)
    (Q : VV (L := L) lam) : thetaF τ χ lam i Q ∈ Vω ST τ χ lam :=
  Submodule.mem_inf.2 ⟨dAlg_thetaA_mem_Forms τ χ lam _ (ext_mem_Forms_of_stab τ χ lam hst _ Q),
    (Submodule.mem_iInf _).2 fun P => LinearMap.mem_ker.2 (Nm_dAlg_thetaA P _ _)⟩

/-- **The block map into the cut**, `Θ_{g,o} : VV(λ) → V_ω` (`thetaF` with its values in `V_ω`). -/
def thetaV [NumberField L] (hst : ∀ c : DCl E n ST Λ, stab c = ⊥) (i : Bset ST × Orb E n ST Λ) :
    VV (L := L) lam →ₗ[L] Vω ST τ χ lam :=
  (thetaF τ χ lam i).codRestrict _ (thetaF_mem_Vω τ χ lam hst i)

/-- **C1 (integral, in the cut)**: for `Q ∈ Δ_{Lsh(c_o)}` (in every local basis), `Θ_{g,o}Q ∈ M_ω`. The form
`ext(c_o, Q)` is integral in every local basis, and so are its diamond translates and their integer combinations
(`dOp_mem_MintA`), which lie in `M` (`MintA_subset`). -/
theorem thetaV_mem_Mω [NumberField L] (hst : ∀ c : DCl E n ST Λ, stab c = ⊥) (i : Bset ST × Orb E n ST Λ)
    {Q : VV (L := L) lam} (hQ : (Q : Pol Φ n L) ∈ DeltaA τ lam (Lsh i.2.out.rep)) :
    (thetaV τ χ lam hst i Q : Fn ST Λ Φ L) ∈ Mω ST τ χ lam := by
  obtain ⟨a, b, hab⟩ := exists_sand_uniform (E := E) (n := n) (ST := ST) (Λ := Λ)
  refine ⟨MintA_subset τ χ lam hab ?_, thetaF_mem_Vω τ χ lam hst i Q⟩
  have hext : ext τ χ lam i.2.out Q ∈ MintA τ χ lam := ⟨ext_mem_Forms_of_stab τ χ lam hst _ Q, fun c => by
    rcases eq_or_ne c i.2.out with rfl | hc
    · rw [ext_out τ χ lam (inv_of_stab τ χ lam hst _ _)]
      exact hQ
    · rw [ext_out_ne τ χ lam hc]
      exact zero_mem_DeltaA⟩
  show thetaF τ χ lam i Q ∈ _
  rw [thetaF_eq_sum]
  refine sum_mem_MintA τ χ lam _ fun S _ => ?_
  have := zsmul_mem_MintA τ χ lam ((-1) ^ (Finset.univ \ S).card) (dOp_mem_MintA τ χ lam (gS i.1.1 S) hext)
  exact_mod_cast this

/-- **C2 (scaled isometry)**: `H_σ(Θ_{g,o}Q, Θ_{g,o}Q') = 2^{|ST|}·fock(σQ, σQ')/κ` at every embedding `σ`. Expand
over the subsets (`thetaF_eq_sum`, `petAt_sum_smul`): the cross terms vanish and the `2^{|ST|}` diagonal terms are
`fock(σQ, σQ')/κ` (`petAt_dOp_ext`, `gS_inj`). -/
theorem petAt_thetaV [NumberField L] (hst : ∀ c : DCl E n ST Λ, stab c = ⊥)
    (hfr : ∀ (a : Dia ST) (c : DCl E n ST Λ), a • c = c → a = 1) (σ : L →+* ℂ) (i : Bset ST × Orb E n ST Λ)
    (Q Q' : VV (L := L) lam) :
    petAt ST lam σ (thetaV τ χ lam hst i Q : Fn ST Λ Φ L) (thetaV τ χ lam hst i Q' : Fn ST Λ Φ L) =
      2 ^ ST.card * fockWith (starRingEnd ℂ) (map σ (Q : Pol Φ n L)) (map σ (Q' : Pol Φ n L)) / kappa lam := by
  show petAt ST lam σ (thetaF τ χ lam i Q) (thetaF τ χ lam i Q') = _
  rw [thetaF_eq_sum, thetaF_eq_sum, petAt_sum_smul]
  simp only [petAt_dOp_ext τ χ lam hst hfr, gS_inj i.1.2, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, map_pow, map_neg, map_one]
  simp only [← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_finset, Fintype.card_coe, nsmul_eq_mul, fock, fockWith_hw_C]
  push_cast
  ring

end Blocks

/-! ## The cut is the direct sum of the blocks -/

section Cut

variable (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

/-- `Σ_{(g,o)} Θ_{g,o}` on the functions. -/
def sumF : (Bset ST × Orb E n ST Λ → VV (L := L) lam) →ₗ[L] Fn ST Λ Φ L :=
  ∑ i, (thetaF τ χ lam i).comp (LinearMap.proj i)

/-- `Σ_{(g,o)} Θ_{g,o}` at a tuple `y`. -/
theorem sumF_apply (y : Bset ST × Orb E n ST Λ → VV (L := L) lam) :
    sumF τ χ lam y = ∑ i, thetaF τ χ lam i (y i) := by
  simp [sumF]

/-- **Where the terms of the blocks live**: `g_S·g'^{-1}c_{o'} = c_o` with `g' ∈ B` forces `o = o'` (orbits),
`g_S = g'` (freeness), hence `S = ST` and `g = g'`. -/
theorem eq_of_gS_smul (hfr : ∀ (a : Dia ST) (c : DCl E n ST Λ), a • c = c → a = 1) {g g' : Dia ST}
    (hg' : ∀ P, g' P ≠ 1) {o o' : Orb E n ST Λ} {S : Finset ST} (h : gS g S • g'⁻¹ • o'.out = o.out) :
    o = o' ∧ S = Finset.univ ∧ g = g' := by
  have ho : o = o' := by
    have : (Quotient.mk _ o.out : Orb E n ST Λ) = Quotient.mk _ o'.out :=
      Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2
        ⟨gS g S * g'⁻¹, by rw [mul_smul]; exact h⟩))
    rwa [Quotient.out_eq, Quotient.out_eq] at this
  subst ho
  have h1 : gS g S = g' := mul_inv_eq_one.1 (hfr _ o.out (by rw [mul_smul]; exact h))
  have hS : S = Finset.univ := Finset.eq_univ_iff_forall.2 fun P => by
    by_contra hP
    have := congrFun h1 P
    simp only [gS_apply, hP, ↓reduceIte] at this
    exact hg' P this.symm
  subst hS
  exact ⟨rfl, rfl, by rw [← h1, gS_univ]⟩

/-- **C3, injective**: at the class `g'^{-1}c_{o'}`, `Σ Θ_{g,o}(y_{g,o})` is `actP_h y_{g',o'}` for some `h`
(`eq_of_gS_smul`), and `actP_h` is invertible. -/
theorem sumF_injective (hst : ∀ c : DCl E n ST Λ, stab c = ⊥)
    (hfr : ∀ (a : Dia ST) (c : DCl E n ST Λ), a • c = c → a = 1) :
    Function.Injective (sumF (ST := ST) τ χ lam) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  funext i₀
  obtain ⟨⟨g', hg'⟩, o'⟩ := i₀
  have h0 := congrFun hy (g'⁻¹ • o'.out).out
  rw [sumF_apply, Finset.sum_apply, Finset.sum_eq_single (⟨g', hg'⟩, o')] at h0
  · rw [thetaF_eq_sum, Finset.sum_apply, Finset.sum_eq_single Finset.univ] at h0
    · obtain ⟨h, hh⟩ := exists_dOp_ext_out τ χ lam hst (a := g') (c := o'.out) (smul_inv_smul g' _)
      rw [Pi.smul_apply, Finset.sdiff_self, Finset.card_empty, pow_zero, one_smul, gS_univ, hh] at h0
      have := congrArg (actP τ χ lam h⁻¹) h0
      rw [← actP_mul, inv_mul_cancel, actP_one, Pi.zero_apply, actP_zero] at this
      exact Subtype.ext this
    · intro S _ hS
      rw [Pi.smul_apply, dOp_ext_out_eq_zero τ χ lam (fun h => hS (eq_of_gS_smul hfr hg' h).2.1), smul_zero]
    · simp
  · rintro ⟨⟨g, hg⟩, o⟩ _ hi
    rw [thetaF_eq_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [Pi.smul_apply, dOp_ext_out_eq_zero τ χ lam (fun h => hi ?_), smul_zero]
    obtain ⟨h1, -, h3⟩ := eq_of_gS_smul hfr hg' h
    subst h1 h3
    rfl
  · simp

/-- Forms with the same values at the representatives are equal (`eq_sum_ext`). -/
theorem eq_of_forall_out {F G : Fn ST Λ Φ L} (hF : F ∈ Forms ST τ χ lam) (hG : G ∈ Forms ST τ χ lam)
    (h : ∀ c : DCl E n ST Λ, F c.out = G c.out) : F = G := by
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  rw [eq_sum_ext τ χ lam hF, eq_sum_ext τ χ lam hG]
  simp only [h]

/-- **A class block is a diamond translate of the block of its orbit's representative**:
`ext(c, P) = ⟨b⟩ext(c_o, Q)` for the orbit `o` of `c`, with `b·c = c_o` and `Q = actP_g⁻¹ P`. -/
theorem exists_ext_eq_dOp (hst : ∀ c : DCl E n ST Λ, stab c = ⊥) (c : DCl E n ST Λ) {P : Pol Φ n L}
    (hP : P ∈ VV (L := L) lam) : ∃ (b : Dia ST) (Q : VV (L := L) lam),
      ext τ χ lam c P = dOp b (ext τ χ lam (Quotient.mk _ c : Orb E n ST Λ).out Q) := by
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1
    (Quotient.exact (Quotient.out_eq (Quotient.mk _ c : Orb E n ST Λ))))
  obtain ⟨g, hg⟩ := exists_dOp_ext_out τ χ lam hst hb
  refine ⟨b, ⟨actP τ χ lam g⁻¹ P, actP_mem_VV τ χ lam _ hP⟩, eq_of_forall_out τ χ lam
    (ext_mem_Forms τ χ lam hP (inv_of_stab τ χ lam hst c P))
    (dOp_mem ST τ χ lam b (ext_mem_Forms_of_stab τ χ lam hst _ _)) fun c' => ?_⟩
  rcases eq_or_ne c' c with rfl | hc
  · rw [ext_out τ χ lam (inv_of_stab τ χ lam hst _ _), hg, ← actP_mul, mul_inv_cancel, actP_one]
  · rw [ext_out_ne τ χ lam hc,
      dOp_ext_out_eq_zero τ χ lam (fun h => hc (smul_left_cancel b (h.trans hb.symm)))]

/-- `θ_x·ext(c_o, Q)` is in the range of `Σ Θ`: it is `Θ_{x,o}Q` if `x ∈ B`, and `0` otherwise
(`thetaA_eq_zero`). -/
theorem dAlg_thetaA_mem_range (x : Dia ST) (o : Orb E n ST Λ) (Q : VV (L := L) lam) :
    dAlg Λ Φ L (thetaA L x) (ext τ χ lam o.out Q) ∈ LinearMap.range (sumF (ST := ST) τ χ lam) := by
  by_cases hx : ∀ P, x P ≠ 1
  · refine ⟨Pi.single (⟨x, hx⟩, o) Q, ?_⟩
    rw [sumF_apply, Finset.sum_eq_single (⟨x, hx⟩, o)]
    · rw [Pi.single_eq_same]
      rfl
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, map_zero]
    · simp
  · obtain ⟨P, hP⟩ := not_forall.1 hx
    rw [thetaA_eq_zero (not_not.1 hP), map_zero, LinearMap.zero_apply]
    exact zero_mem _

section Units

variable [∀ P : ST, Fintype (𝓞 E ⧸ P.1.asIdeal)ˣ]

omit [Fintype Φ] [DecidableEq Φ] in
/-- On `ker Nm_P`, `Σ_u (⟨u⟩_P − 1) = Nm_P − N_P` acts as `−N_P`. -/
theorem dAlg_sum_eP [NumberField L] (P : ST) {F : Fn ST Λ Φ L} (hF : Nm P F = 0) :
    dAlg Λ Φ L (∑ u, eP L P u) F = -(NP P : L) • F := by
  simp only [eP, Finset.sum_sub_distrib, map_sub, ← Nm_eq_dAlg, LinearMap.sub_apply, hF, zero_sub,
    Finset.sum_const, Finset.card_univ, map_nsmul, map_one, LinearMap.smul_apply, Module.End.one_apply, NP,
    Nat.card_eq_fintype_card, neg_smul, Nat.cast_smul_eq_nsmul]

omit [Fintype Φ] [DecidableEq Φ] in
/-- On the cut, `X = Π_P Σ_u (⟨u⟩_P − 1)` acts as the scalar `Π_P (−N_P)`. -/
theorem dAlg_prod_eP [NumberField L] {F : Fn ST Λ Φ L} (hF : ∀ P, Nm P F = 0) (s : Finset ST) :
    dAlg Λ Φ L (∏ P ∈ s, ∑ u, eP L P u) F = (∏ P ∈ s, -(NP P : L)) • F := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert P s hP ih =>
    rw [Finset.prod_insert hP, Finset.prod_insert hP, dAlg_mul_apply, ih, map_smul, dAlg_sum_eP P (hF P),
      smul_smul, mul_comm]

omit [NumberField E] [IsCMField E] in
/-- `Σ_u (⟨u⟩_P − 1)·⟨b⟩_P = Σ_u (1 − N_P[u = b])(⟨u⟩_P − 1)`: both are `Σ_u ⟨u⟩_P − N_P⟨b⟩_P`. -/
theorem sum_eP_mul_of (P : ST) (b : (𝓞 E ⧸ P.1.asIdeal)ˣ) :
    (∑ u, eP L P u) * MonoidAlgebra.of L (Dia ST) (Pi.mulSingle P b) =
      ∑ u, (1 - if u = b then (NP P : L) else 0) • eP L P u := by
  simp only [eP, Finset.sum_mul, sub_mul, one_mul, Finset.sum_sub_distrib, sum_of_mul_of, sub_smul, one_smul,
    ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, NP,
    Nat.card_eq_fintype_card, smul_sub, Nat.cast_smul_eq_nsmul, smul_mul_assoc]
  abel

omit [NumberField E] [IsCMField E] in
/-- **`X·⟨b⟩` is a combination of the `θ_x`**: `X·⟨b⟩ = Σ_{x∈D} (Π_P (1 − N_P[x_P = b_P]))·θ_x`, place by place
(`sum_eP_mul_of`) and by distributivity (`Finset.prod_univ_sum`). -/
theorem prod_sum_eP_mul_of (b : Dia ST) :
    (∏ P, ∑ u, eP L P u) * MonoidAlgebra.of L _ b =
      ∑ x : Dia ST, (∏ P, (1 - if x P = b P then (NP P : L) else 0)) • thetaA L x := by
  conv_lhs => rw [← Finset.univ_prod_mulSingle b, map_prod, ← Finset.prod_mul_distrib]
  simp only [sum_eP_mul_of]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [thetaA, Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]
  simp only [Algebra.smul_def]

end Units

/-- **C3, onto**: every cut form is a sum of blocks. `X` acts on the cut as the nonzero scalar `Π_P (−N_P)`
(`dAlg_prod_eP`); a form is a sum of diamond translates `⟨b⟩ext(c_o, Q)` (`eq_sum_ext`, `exists_ext_eq_dOp`); and
`X·⟨b⟩` is a combination of the `θ_x` (`prod_sum_eP_mul_of`), which send `ext(c_o, Q)` into the range
(`dAlg_thetaA_mem_range`). -/
theorem mem_range_sumF [NumberField L] (hst : ∀ c : DCl E n ST Λ, stab c = ⊥) {F : Fn ST Λ Φ L}
    (hF : F ∈ Vω ST τ χ lam) : F ∈ LinearMap.range (sumF (ST := ST) τ χ lam) := by
  have := finite_DCl E n ST SG Λ
  let := Fintype.ofFinite (DCl E n ST Λ)
  let : ∀ P : ST, Fintype (𝓞 E ⧸ P.1.asIdeal)ˣ := fun P => Fintype.ofFinite _
  obtain ⟨hF1, hF2⟩ := Submodule.mem_inf.1 hF
  have hNm (P : ST) : Nm P F = 0 := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hF2 P)
  have hs : (∏ P : ST, -(NP P : L)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun P _ =>
    neg_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩))
  have h : dAlg Λ Φ L (∏ P, ∑ u, eP L P u) F ∈ LinearMap.range (sumF (ST := ST) τ χ lam) := by
    rw [eq_sum_ext τ χ lam hF1, map_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨b, Q, hbQ⟩ := exists_ext_eq_dOp τ χ lam hst c (hF1.1 c.out)
    rw [hbQ, ← dAlg_of, ← dAlg_mul_apply, prod_sum_eP_mul_of, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (dAlg_thetaA_mem_range τ χ lam x _ Q)
  rw [dAlg_prod_eP hNm Finset.univ] at h
  have := Submodule.smul_mem _ (∏ P : ST, -(NP P : L))⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at this

/-- **C3 (bijectivity)**: `(y_{g,o}) ↦ Σ_{(g,o)} Θ_{g,o}(y_{g,o})` is a bijection from `B × Orb → VV(λ)` onto the cut
`V_ω` (`sumF_injective`, `mem_range_sumF`). -/
theorem bijective_sum_thetaV [NumberField L] (hst : ∀ c : DCl E n ST Λ, stab c = ⊥)
    (hfr : ∀ (a : Dia ST) (c : DCl E n ST Λ), a • c = c → a = 1) :
    Function.Bijective fun y : Bset ST × Orb E n ST Λ → VV (L := L) lam => ∑ i, thetaV τ χ lam hst i (y i) := by
  have hco (y : Bset ST × Orb E n ST Λ → VV (L := L) lam) :
      ((∑ i, thetaV τ χ lam hst i (y i) : Vω ST τ χ lam) : Fn ST Λ Φ L) = sumF τ χ lam y := by
    rw [sumF_apply, Submodule.coe_sum]
    rfl
  refine ⟨fun y y' h => sumF_injective τ χ lam hst hfr ?_, fun F => ?_⟩
  · simpa only [hco] using congrArg Subtype.val h
  · obtain ⟨y, hy⟩ := mem_range_sumF τ χ lam hst F.2
    exact ⟨y, Subtype.ext ((hco y).trans hy)⟩

end Cut

end

end HermForms
