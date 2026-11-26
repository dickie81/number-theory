import SharpChain

/-!
# The sharp frontier from its inputs and its pieces — CONDITIONAL on the half-plane

The architecture for **proving** `SharpBoundPinned`: the deep classical inputs as hypotheses (`SharpInputs`), the
statements to prove in the library (`SharpPieces`), and the reduction `sharpBoundPinned_of_inputs`, which is logical
packaging: every witness and clause of the frontier comes from a field or a combination of fields.

**The construction is data.** The frontier is existential in many objects (the coefficient field, the words, the
auxiliary primes, the chain data, the rows, the twists, the cusp subspaces, `𝔞⁺`, `𝔞⁻`, the target metric, the
heights and the constants). Several pieces must hold for the *same* choices, and the library does not define the
archive's choices (the target metric is the archive's indefinite-side metric; `𝔞_ω` is the archive's `Iu⁻¹`, whose
local weights are not defined here). So the choices are one field of `SharpPieces`, `cons`: per design, a coefficient
field (`SharpCoeff`) and per translate an object (`SharpObj`) holding every choice; with `adm`, the conditions the
construction asks of the parameters (the archive's `TuSize`, `litThin`, …), these are the two data fields. Every
other field is a statement about `cons`, provable on its own once `cons` is defined. Only the frame (coordinates and
lattices) stays existential (`frame`), and every piece about frames holds for every frame realising the object
(`SharpObj.RealWith`), as all such frames are isometric.

**Pieces** (one per item of the proof plan, §3–§4): finite classes and stabilisers (`finiteClasses`), forms
finite-dimensional and integral forms a lattice (`formsLattice`), admissible parameters and windows (`params`), the
pins' satisfiability (`pins`), the frame's existence (`frame`), the auxiliary primes (`primes`, (T)), the slope bound
(F) with the index (V) (`slopeFV`), the gain in (G↓) (`gain`), (G↑) (`gUp`), (S) and (R) (`frameSR`).
`SharpObj.exists_sharpTr` assembles one translate from them. (Z) is not a piece: each piece bounds its own slack by a
share of the budget `x^{4ε} Σ_t a_t` (a quarter each for `c↓ = c_F + c_G`, `c↑`, `(Σ_t a_t)·c_T` and the frame loss),
and the reduction adds them up.

**Sanity theorem:** `SharpObj.exists_sharpTr` (the per-translate reduction).

**Inputs** (`SharpInputs`; proof plan §5): Siegel–Weil (with Rallis), the covolume bound `hX`, good twists, the
unitary mass formula, the local Weil representation and Howe duality, Chowla–Selberg/Colmez, `ShortNorm`. Where the
library cannot state the classical theorem, the field is a consequence, and its docstring says so.

**Pins** (`SharpDesign.pinBody`, `SharpDesign.PinsAt`): the per-translate body of `SharpData.RealisedPinned`,
restated over the design (its helpers `Shp`, `aBd`, `aBdN`, … read the design and the auxiliary prime instead of
sharp data). The reduction closes `RealisedPinned` by `exact`, so the restatement is checked against the frontier by
the kernel on every build: a change to the frontier that the restatement misses breaks the reduction.

**CONDITIONAL.** `rhAndGRH_of_inputs` rests on the half-plane `Re s > 11/12`, as `rhAndGRH_of_sharpBoundPinned` does.
-/

namespace ZetaBalance

open NumberField IsDedekindDomain HermClasses ThetaChain WeylFock HermitianLattice

noncomputable section

/-! ## The design: parameters at `x` -/

/-- **A design at `x`**: the parameters of sharp data that do not depend on the translate's objects (weights, ranks
`R`, Harish-Chandra families `hc u` with `w_{u,j} = e_j`, split primes `g₀ ≠ g₁` with `(−d/g₀) = (−d/g₁) = 1`), the
fields of `SharpData` before `fr`, and the first two clauses of `SharpData.Arith`. -/
structure SharpDesign (S : Setting) (κ : S.A →* ℂˣ) (x ε X : ℝ) extends Weights S κ x ε X where
  /-- The ranks `(k, m, t)`. -/
  R : S.Ranks
  /-- The number of weights is the rank `m`. -/
  hm : m = R.m
  /-- The Harish-Chandra family of each translate. -/
  hc : S.A → R.HCFamily
  /-- The weights are the parameters `e_j`. -/
  hw : ∀ u j ρ, w u j ρ = R.wj (hc u) (Fin.cast hm j) ρ
  /-- The split prime `g₀`. -/
  g₀ : ℕ
  /-- The split prime `g₁`. -/
  g₁ : ℕ
  /-- `g₀` is prime. -/
  g₀_prime : g₀.Prime
  /-- `g₁` is prime. -/
  g₁_prime : g₁.Prime
  /-- `g₀ ≠ g₁`. -/
  g₀_ne_g₁ : g₀ ≠ g₁
  /-- `(−d/g₀) = 1`. -/
  leg₀ : jacobiSym (-(S.d : ℤ)) g₀ = 1
  /-- `(−d/g₁) = 1`. -/
  leg₁ : jacobiSym (-(S.d : ℤ)) g₁ = 1

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-- `SharpData.sgW`, read on the design. -/
def sgW (u : S.A) : Φ S.A → Fin (Dg.R.N Dg.R.m - 1) → ℤ :=
  PeriodTarget.sgT Dg.R.k Dg.R.t Dg.R.m (fun ρ => finN (Dg.hc u ρ).v) (fun ρ => finN (Dg.hc u ρ).b)
    (fun ρ => finN (Dg.hc u ρ).e)

/-- `SharpData.N_sub_one_add_one`, read on the design. -/
theorem N_sub_one_add_one : Dg.R.N Dg.R.m - 1 + 1 = Dg.R.k + Dg.R.m * (Dg.R.t + 1) := by
  have := Dg.R.m_add_three_le
  unfold Setting.Ranks.N
  omega

/-- `SharpData.rr`, read on the design. -/
def rr : ℕ := Dg.R.k + Dg.R.m - 1

/-- `SharpData.rr_le`, read on the design. -/
theorem rr_le : Dg.rr ≤ Dg.R.N Dg.R.m - 1 := by
  have : Dg.R.m ≤ Dg.R.m * (Dg.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold rr Setting.Ranks.N
  omega

/-- `SharpData.eW`, read on the design. -/
def eW (u : S.A) : ℕ → Φ S.A → ℤ := fun j ρ => finN (Dg.hc u ρ).e j

/-- `SharpData.Sg`, read on the design. -/
def Sg : Set (HeightOneSpectrum (𝓞 S.E)) :=
  {v | ((Dg.g₀ * Dg.g₁ : ℕ) : 𝓞 S.E) ∈ v.asIdeal}

/-- `SharpData.lamW`, read on the design. -/
def lamW (hw : Dg.R.HCFamily) : Φ S.A → Fin (Dg.R.N Dg.R.m - 1 + 1) → ℤ :=
  fun ρ i => WeylFock.wt Dg.R.k Dg.R.t Dg.R.m (fun ρ i => ⌊(hw ρ).u i - 1 / 2⌋) (fun ρ => finN (hw ρ).e) ρ
    (Fin.cast Dg.N_sub_one_add_one i)

/-- `SharpData.wB`, read on the design. -/
def wB (u : S.A) : ℕ :=
  Dg.R.k + Dg.R.m + Dg.R.t + ∑ ρ, ((∑ i, ⌈|(Dg.hc u ρ).u i|⌉₊) + (∑ i, ((Dg.hc u ρ).v i).natAbs) +
    ∑ j, (((Dg.hc u ρ).b j).natAbs + ((Dg.hc u ρ).e j).natAbs))

/-- `SharpData.aBd`, read on the design and the word's auxiliary prime `T`. -/
def aBd (K : Type) [Field K] [NumberField K] (u : S.A) (T : ℕ) : ℕ :=
  (T * S.d * Dg.g₀ * Dg.g₁ * primorial ⌊S.cutX x ε⌋₊) ^ (Module.finrank ℚ K * Dg.R.N Dg.R.m * Dg.wB u)

/-- `SharpData.aBdN`, read on the design and the word's auxiliary prime `T`. -/
def aBdN (K : Type) [Field K] [NumberField K] (u : S.A) (T : ℕ) : ℕ :=
  (T * S.d * Dg.g₀ * Dg.g₁ * primorial (max ⌊S.cutX x ε⌋₊ (Dg.R.N Dg.R.m * Module.finrank ℚ S.E + 1))) ^
    (Module.finrank ℚ K * Dg.R.N Dg.R.m * Dg.wB u)

/-- The arithmetic of an auxiliary prime (`SharpData.Arith`): `T = ππ̄` with `π = (a + b√−d)/2 ≡ 1 (mod M)`,
`M = QS·q·d·(g₀g₁)²`. -/
def ArithT (T : ℕ) : Prop :=
  ∃ a b : ℤ, 4 * (T : ℤ) = a ^ 2 + S.d * b ^ 2 ∧
    ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℤ) ∣ b ∧
    a ≡ b + 2 [ZMOD 2 * ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℤ)]

open Classical in
/-- `SharpData.Shp`, read on the design and the word's auxiliary prime `T`. -/
def Shp {K : Type} [Field K] [NumberField K] {τK : Φ S.A → (S.E →+* K)} (u : S.A) (T : ℕ)
    (hw : Dg.R.HCFamily) (D' : Data τK) (m' : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 S.E))) : Prop :=
  (∀ j, D'.cA j = (∏ P ∈ D'.SG ∪ Q, Ideal.absNorm P.asIdeal) ^ (m' + 1) ∧
      D'.cB j = T * (∏ P ∈ D'.SG ∪ Q, Ideal.absNorm P.asIdeal) ^ (m' + 1)) ∧
  (m' = Dg.R.m ∧ (∀ j ≤ m', D'.n j = Dg.R.N j) ∧ (∀ j ≤ m', D'.e j = Dg.eW u j) ∧
    ∀ j ≤ m', ∀ (h : D'.n j = Dg.R.k + j * (Dg.R.t + 1)) ρ i, D'.lam j ρ i =
      WeylFock.wt Dg.R.k Dg.R.t j (fun ρ i => ⌊(hw ρ).u i - 1 / 2⌋) (fun ρ => finN (hw ρ).e) ρ
        (Fin.cast h i)) ∧
    D'.P.sd = Real.sqrt S.d / 2

end SharpDesign

/-! ## The coefficient field, frames on given words, the per-translate object -/

/-- **The coefficient field** of a design: `K` totally complex, normal over `ℚ`, with a star (the archive's
`Fields.Ok`), a CM type `τ_K` on `E = Setting.E` and an embedding `j : K → ℂ` (`pins` asks `j ∘ τ_K = Setting.τ`). -/
structure SharpCoeff (S : Setting) where
  /-- The field. -/
  K : Type
  [field : Field K]
  [numberField : NumberField K]
  [totallyComplex : IsTotallyComplex K]
  [normal : Normal ℚ K]
  [star : StarRing K]
  /-- The CM type `τ_K`. -/
  τK : Φ S.A → (S.E →+* K)
  /-- The embedding `j`. -/
  j : K →+* ℂ

attribute [instance] SharpCoeff.field SharpCoeff.numberField SharpCoeff.totallyComplex SharpCoeff.normal
  SharpCoeff.star

/-- **A hermitian frame on the words `Ω`**: `KFrame` with its words fixed, so that a frame built for an object
(whose sources are indexed by its words) has `ι = Ω` by definition (`toKFrame`). -/
structure FrameOn (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (Ω : Type) [Fintype Ω] where
  /-- The coordinates of the source of a word. -/
  n : Ω → Type
  [fintypeN : ∀ ω, Fintype (n ω)]
  /-- The coordinates of the target. -/
  κ : Type
  [fintypeκ : Fintype κ]
  [nonempty : Nonempty κ]
  /-- The sources `N_ω`. -/
  src : ∀ ω, KLattice K (n ω)
  /-- The target `C_u`. -/
  tgt : KLattice K κ
  /-- The maps `B_ω`. -/
  B : ∀ ω, (n ω → K) →ₗ[K] (κ → K)
  /-- `B_ω(N_ω) ⊆ C_u`. -/
  hB : ∀ ω, ∀ y ∈ (src ω).M, B ω y ∈ tgt.M
  /-- The log-norms of the maps at each complex place. -/
  ht : Ω → Pl K → ℝ
  /-- The maps are bounded by `e^{ht ω v}` on the part at `v`. -/
  hφ : ∀ ω v, ∀ y ∈ (KLattice.part v : Submodule ℂ (KLattice.Space K (n ω))),
    ‖(src ω).hom tgt (B ω) y‖ ≤ Real.exp (ht ω v) * ‖y‖

attribute [instance] FrameOn.fintypeN FrameOn.fintypeκ FrameOn.nonempty

/-- The frame on `Ω` as a `KFrame`, with words `ι = Ω` (reducibly, so instances on `Ω` serve `ι`). -/
abbrev FrameOn.toKFrame {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {Ω : Type} [Fintype Ω]
    (F : FrameOn K Ω) : KFrame K where
  ι := Ω
  n := F.n
  κ := F.κ
  src := F.src
  tgt := F.tgt
  B := F.B
  hB := F.hB
  ht := F.ht
  hφ := F.hφ

/-- **The object of a translate**: every choice the frontier leaves existential at `u`, the archive's construction.
The words `Ω` and their auxiliary primes `T`; the witnesses of `SharpData.RealisedPinned` at `u` (levels `Tμ` with
groups `G` acting on points `Xp`, sources `Vs`, place sets, period data `P` with untwisted level `μ0` and twist `tw`,
`𝔞⁺ = 𝔞p`, `𝔞⁻ = 𝔞n`, the words' HC families, step-0 data, cusp subspaces `Xc` and isomorphisms `e`, row places `QE`,
`xi0`, twists `ξT`, lift characters `mu0`, the theta pin, `tz`, the row points `eX`); the target metric `g` on
`V0_{μ0} → K` at each complex place (the archive's indefinite-side metric, existential in the frontier), the heights
`ht`; and the constants: the place `pl` and scalars `cω` of (S), `e = eS`, `η`, the range `U`, the depth `H`, and the
slacks `c_F` of (F), `c_G` of the gain (`c↓ = c_F + c_G`), `c↑` and `c_T`. -/
structure SharpObj {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X) (C : SharpCoeff S) where
  /-- The words. -/
  Ω : Type
  [fintypeΩ : Fintype Ω]
  /-- The auxiliary prime of each word. -/
  T : Ω → ℕ
  /-- The levels. -/
  Tμ : Type
  /-- The groups of the levels. -/
  G : Tμ → Type
  /-- The points of the levels. -/
  Xp : Tμ → Type
  [grp : ∀ μ, Group (G μ)]
  [act : ∀ μ, MulAction (G μ) (Xp μ)]
  /-- The source spaces. -/
  Vs : Ω → Type
  [acg : ∀ ω, AddCommGroup (Vs ω)]
  [modK : ∀ ω, Module C.K (Vs ω)]
  [modO : ∀ ω, Module (𝓞 C.K) (Vs ω)]
  [tower : ∀ ω, IsScalarTower (𝓞 C.K) C.K (Vs ω)]
  /-- The places `ST_ω`. -/
  ST : Ω → Finset (HeightOneSpectrum (𝓞 S.E))
  /-- The places `SG`. -/
  SG : Finset (HeightOneSpectrum (𝓞 S.E))
  /-- The period data. -/
  P : PeriodTarget.PerData (Φ S.A) (Dg.R.N Dg.R.m - 1) S.E C.K G Xp Vs
  /-- The untwisted level. -/
  μ0 : Tμ
  /-- The twist data. -/
  tw : PeriodTarget.Twist P μ0
  /-- `𝔞⁺`. -/
  𝔞p : Ω → Ideal (𝓞 C.K)
  /-- `𝔞⁻`. -/
  𝔞n : Ω → Ideal (𝓞 C.K)
  /-- The HC family of each word. -/
  hcW : Ω → Dg.R.HCFamily
  /-- The step-0 rank. -/
  n0 : ℕ
  /-- The step-0 weights. -/
  lam0 : Ω → Φ S.A → Fin n0 → ℤ
  /-- The step-0 characters. -/
  χ0 : Ω → (uniUT SG n0 →* C.K)
  /-- The cusp subspaces. -/
  Xc : ∀ ω, Submodule C.K (HermForms.Fn (ST ω) (uniUT SG n0) (Φ S.A) C.K)
  /-- The isomorphisms of the sources with `X ⊓ V_ω`. -/
  e : ∀ ω, Vs ω ≃ₗ[C.K] ↥(Xc ω ⊓ HermForms.Vω (ST ω) C.τK (χ0 ω) (lam0 ω))
  /-- The row places of each level. -/
  QE : Tμ → Finset (HeightOneSpectrum (𝓞 S.E))
  /-- `xi0`. -/
  xi0 : S.E
  /-- The twist of each level. -/
  ξT : Tμ → Hecke S.E C.K
  /-- The lift characters. -/
  mu0 : ℕ → Hecke S.E C.K
  /-- The pin's form. -/
  s : ℝ
  /-- The pin of the base thetas. -/
  pin : ThetaNorm.Pin (Φ S.A) s
  /-- `tz` of each word. -/
  tzO : Ω → 𝓞 S.E
  /-- The row points of each level. -/
  eX : ∀ μ, Xp μ ≃ points (E := S.E) (ST := (∅ : Finset (HeightOneSpectrum (𝓞 S.E))))
    (RowSpace.rowLevel (Dg.R.N Dg.R.m - 1) Dg.rr Dg.R.t SG (QE μ))
  /-- The target metric at each complex place, on `V0_{μ0} → K`. -/
  g : Pl C.K → (P.V0 μ0 → C.K) → (P.V0 μ0 → C.K) → ℂ
  /-- The heights of the maps. -/
  ht : Ω → Pl C.K → ℝ
  /-- The place of the frame condition. -/
  pl : Pl C.K
  /-- The scalars of the frame condition. -/
  cω : Ω → ℝ
  /-- The constant `e` of the frame condition. -/
  eS : ℝ
  /-- The constant `η` of the frame condition. -/
  η : ℝ
  /-- The range `U`. -/
  U : ℝ
  /-- The depth `H`. -/
  H : ℝ
  /-- The slack `c_F` of (F). -/
  cF : ℝ
  /-- The slack `c_G` of the gain. -/
  cG : ℝ
  /-- The slack `c↑`. -/
  cUp : ℝ
  /-- The slack `c_T`. -/
  cT : ℝ

attribute [instance] SharpObj.fintypeΩ SharpObj.grp SharpObj.act SharpObj.acg SharpObj.modK SharpObj.modO
  SharpObj.tower

/-- **The construction of a design**: its coefficient field and the object of every translate. -/
structure SharpCons {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X) where
  /-- The coefficient field. -/
  C : SharpCoeff S
  /-- The object of each translate. -/
  obj : S.A → SharpObj Dg C

/-! ## The pins -/

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

open Classical in
/-- **The pins of a translate**, the clauses of the per-translate body of `SharpData.RealisedPinned` before the caps
on `𝔞` and the realisation, followed by `Tail` (in the frontier: the caps and `KFrame.RealisesPet`). The text is the
frontier's, with the helpers of sharp data read on the design (`Shp`, `eW`, `Sg`, `lamW`, `sgW`, `rr`) and the
auxiliary primes `T` of the words. -/
def pinBody (C : SharpCoeff S) (u : S.A) {Ω : Type} (T : Ω → ℕ) {Tμ : Type} (G Xp : Tμ → Type)
    [∀ μ, Group (G μ)] [∀ μ, MulAction (G μ) (Xp μ)] (Vs : Ω → Type) [∀ ω, AddCommGroup (Vs ω)]
    [∀ ω, Module C.K (Vs ω)] [∀ ω, Module (𝓞 C.K) (Vs ω)] [∀ ω, IsScalarTower (𝓞 C.K) C.K (Vs ω)]
    (ST : Ω → Finset (HeightOneSpectrum (𝓞 S.E))) (SG : Finset (HeightOneSpectrum (𝓞 S.E)))
    (P : PeriodTarget.PerData (Φ S.A) (Dg.R.N Dg.R.m - 1) S.E C.K G Xp Vs) (μ0 : Tμ)
    (tw : PeriodTarget.Twist P μ0) (M : ∀ ω, Submodule (𝓞 C.K) (Vs ω)) (hcW : Ω → Dg.R.HCFamily) (n0 : ℕ)
    (lam0 : Ω → Φ S.A → Fin n0 → ℤ) (χ0 : Ω → (uniUT SG n0 →* C.K))
    (Xc : ∀ ω, Submodule C.K (HermForms.Fn (ST ω) (uniUT SG n0) (Φ S.A) C.K))
    (e : ∀ ω, Vs ω ≃ₗ[C.K] ↥(Xc ω ⊓ HermForms.Vω (ST ω) C.τK (χ0 ω) (lam0 ω)))
    (QE : Tμ → Finset (HeightOneSpectrum (𝓞 S.E))) (xi0 : S.E) (ξT : Tμ → Hecke S.E C.K)
    (mu0 : ℕ → Hecke S.E C.K) {s : ℝ} (pin : ThetaNorm.Pin (Φ S.A) s) (tzO : Ω → 𝓞 S.E)
    (eX : ∀ μ, Xp μ ≃ points (E := S.E) (ST := (∅ : Finset (HeightOneSpectrum (𝓞 S.E))))
      (RowSpace.rowLevel (Dg.R.N Dg.R.m - 1) Dg.rr Dg.R.t SG (QE μ))) (Tail : Prop) : Prop :=
  (∀ μ ω, IsThetaCol C.τK (Dg.eW u) Dg.Sg (Dg.R.N Dg.R.m - 1) (μ = μ0) (QE μ) xi0 mu0 pin
      (fun D' k Q ξ => Dg.Shp u (T ω) (hcW ω) D' k Q ∧ ∀ x, ξ.toHom x = (ξT μ).toHom x) (tzO ω)
      (fun x => (eX μ x).1) (e ω) (P.col μ ω)) ∧
    ((∃ (Ncc : ℕ) (s : S.E), 0 < Ncc ∧ s ^ 2 = -(S.d : S.E) ∧ xi0 * ((Ncc : S.E) * s) = -1) ∧
      ∀ w ∈ SG, w.valuation S.E xi0 = 1) ∧
    BrPinned C.τK P (fun ω => Dg.lamW (hcW ω)) (Dg.sgW u) ∧
    (∀ ω ρ, (hcW ω ρ).v = (Dg.hc u ρ).v ∧ (hcW ω ρ).b = (Dg.hc u ρ).b ∧ (hcW ω ρ).e = (Dg.hc u ρ).e ∧
      ∀ i : Fin Dg.R.k, ((i : ℕ) = 0 ∨ (i : ℕ) = Dg.R.k - 1) → (hcW ω ρ).u i = (Dg.hc u ρ).u i) ∧
    (∀ ω, M ω = Submodule.span (𝓞 C.K) {φ | (e ω φ).1 ∈ HermForms.Mω (ST ω) C.τK (χ0 ω) (lam0 ω)}) ∧
    (∃ (pde pde' : ℕ) (δ δ' : Hecke S.E C.K) (ψ : HeightOneSpectrum (𝓞 C.K) → Hecke S.E C.K)
        (Qψ : HeightOneSpectrum (𝓞 C.K) → Set (HeightOneSpectrum (𝓞 S.E))),
      pde.Prime ∧ pde'.Prime ∧ pde ≠ pde' ∧ δ.IsDelta pde ∧ δ'.IsDelta pde' ∧
      (∀ ω, T ω ≠ pde ∧ T ω ≠ pde') ∧
      ∀ w ∈ tw.Tw, let ℓ := ringChar (𝓞 C.K ⧸ w.asIdeal)
        let δℓ := if ℓ = pde then δ' else δ
        tw.μw w ≠ μ0 ∧ (ψ w).IsPsi ℓ (Qψ w) ∧ (∀ x, (ξT (tw.μw w)).toHom x = δℓ.toHom x * (ψ w).toHom x) ∧
        ∀ ω, let A := {φ : Vs ω | ∀ r ∈ P.R C.τK (tw.μw w), P.P (tw.μw w) ω φ r ∈ Ow w}
          let B := {φ : Vs ω | ∀ r ∈ P.R C.τK μ0, P.P μ0 ω φ r ∈ Ow w}
          (Submodule.span (Ow w) B).toAddSubgroup.relIndex (Submodule.span (Ow w) (A ∪ B)).toAddSubgroup ≠ 0) ∧
    (∀ w ∈ tw.Tw, P.V0 (tw.μw w) ≠ ⊥) ∧
    (∃ (cS : ℕ → ∀ w : HeightOneSpectrum (𝓞 S.E), MulChar (𝓞 S.E ⧸ w.asIdeal) C.K)
        (cQ : Tμ → ∀ w : HeightOneSpectrum (𝓞 S.E), MulChar (𝓞 S.E ⧸ w.asIdeal) C.K)
        (_ : Fintype (∀ w : SG, GL (Fin Dg.rr) (𝓞 S.E ⧸ w.1.asIdeal)))
        (_ : Fintype (RowSpace.Psym Dg.rr Dg.R.k (Dg.R.m / 2 - 1) SG))
        (ψ : RowSpace.Psym Dg.rr Dg.R.k (Dg.R.m / 2 - 1) SG →* C.K)
        (Xg : Finset ((∀ w : SG, GL (Fin Dg.rr) (𝓞 S.E ⧸ w.1.asIdeal)) → C.K)),
      (∀ s < Dg.R.m, ∀ w ∈ SG, (mu0 s).ResAt w (cS s w)) ∧ (∀ μ, ∀ w ∈ QE μ, (ξT μ).ResAt w (cQ μ w)) ∧
      (∀ g, C.j (ψ g) = RowSpace.chiSym xi0 Dg.rr Dg.R.k (g : ∀ w : SG, GL (Fin Dg.rr) (𝓞 S.E ⧸ w.1.asIdeal))) ∧
      Xg.Nonempty ∧ (∀ χ ∈ Xg, RowSpace.IsIrrChar χ) ∧
      ∀ μ, ∃ (eG : G μ ≃* Grp S.E (Dg.R.N Dg.R.m - 1) (SG ∪ QE μ)
            (RowSpace.rowLevel (Dg.R.N Dg.R.m - 1) Dg.rr Dg.R.t SG (QE μ))),
        (∀ (g : G μ) (x : Xp μ), (eX μ (g • x)).1 = eG g • (eX μ x).1) ∧ Finite (Cl (G μ) (Xp μ)) ∧
        (∀ x, P.lsh μ x = (eX μ x).1.N) ∧
        ∀ F, F ∈ P.V0 μ ↔ ∃ φ ∈ RowSpace.V0pt C.τK P.σ ∅ (RowSpace.rowLevel _ Dg.rr Dg.R.t SG (QE μ))
          (fun h => RowSpace.rowChar Dg.rr Dg.R.t Dg.R.m cS (cQ μ) h.1) (RowSpace.levi Dg.rr Dg.rr_le SG (QE μ))
          (RowSpace.Psym Dg.rr Dg.R.k (Dg.R.m / 2 - 1) SG) ψ Xg, ∀ c, F c = φ (eX μ c.out)) ∧
    (∀ v : HeightOneSpectrum (𝓞 S.E), ((Dg.g₀ * Dg.g₁ : ℕ) : 𝓞 S.E) ∈ v.asIdeal → v ∈ SG ∨
      ∃ w ∈ SG, v.asIdeal = w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj S.E : 𝓞 S.E →+* 𝓞 S.E)) ∧
    (∀ v ∈ SG, ((Dg.g₀ * Dg.g₁ : ℕ) : 𝓞 S.E) ∈ v.asIdeal) ∧
    (∀ v ∈ SG, ∀ w ∈ SG,
      v.asIdeal ≠ w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj S.E : 𝓞 S.E →+* 𝓞 S.E)) ∧
    (∀ ω v, v ∈ ST ω ↔ v.valuation S.E (IsCMField.complexConj S.E (P.tz ω)) < 1) ∧
    (∀ ω, (tzO ω : S.E) = P.tz ω) ∧
    (∀ ω, ∃ (a b : ℤ) (s : S.E), s ^ 2 = -(S.d : S.E) ∧ 4 * (T ω : ℤ) = a ^ 2 + S.d * b ^ 2 ∧
      ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℤ) ∣ b ∧
      a ≡ b + 2 [ZMOD 2 * ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℤ)] ∧
      P.tz ω = ((a : S.E) + (b : S.E) * s) / 2) ∧
    Tail

open Classical in
/-- **The pinned realisation at a translate**, for a frame `F` and auxiliary primes `T` on its words: the
per-translate body of `SharpData.RealisedPinned`, read on the design. -/
def PinsAt (C : SharpCoeff S) (u : S.A) (F : KFrame C.K) (T : F.ι → ℕ) : Prop :=
  ∃ (Tμ : Type) (G Xp : Tμ → Type) (_ : ∀ μ, Group (G μ)) (_ : ∀ μ, MulAction (G μ) (Xp μ))
    (Vs : F.ι → Type) (_ : ∀ ω, AddCommGroup (Vs ω)) (_ : ∀ ω, Module C.K (Vs ω))
    (_ : ∀ ω, Module (𝓞 C.K) (Vs ω)) (_ : ∀ ω, IsScalarTower (𝓞 C.K) C.K (Vs ω))
    (ST : F.ι → Finset (HeightOneSpectrum (𝓞 S.E))) (SG : Finset (HeightOneSpectrum (𝓞 S.E)))
    (P : PeriodTarget.PerData (Φ S.A) (Dg.R.N Dg.R.m - 1) S.E C.K G Xp Vs)
    (μ0 : Tμ) (tw : PeriodTarget.Twist P μ0) (𝔞p 𝔞n : F.ι → Ideal (𝓞 C.K))
    (M : ∀ ω, Submodule (𝓞 C.K) (Vs ω))
    (hcW : F.ι → Dg.R.HCFamily) (n0 : ℕ) (lam0 : F.ι → Φ S.A → Fin n0 → ℤ)
    (χ0 : F.ι → (uniUT SG n0 →* C.K))
    (Xc : ∀ ω, Submodule C.K (HermForms.Fn (ST ω) (uniUT SG n0) (Φ S.A) C.K))
    (e : ∀ ω, Vs ω ≃ₗ[C.K] ↥(Xc ω ⊓ HermForms.Vω (ST ω) C.τK (χ0 ω) (lam0 ω)))
    (QE : Tμ → Finset (HeightOneSpectrum (𝓞 S.E))) (xi0 : S.E) (ξT : Tμ → Hecke S.E C.K)
    (mu0 : ℕ → Hecke S.E C.K) (s : ℝ) (pin : ThetaNorm.Pin (Φ S.A) s)
    (tzO : F.ι → 𝓞 S.E) (eX : ∀ μ, Xp μ ≃ points (E := S.E) (ST := (∅ : Finset (HeightOneSpectrum (𝓞 S.E))))
      (RowSpace.rowLevel (Dg.R.N Dg.R.m - 1) Dg.rr Dg.R.t SG (QE μ))),
    Dg.pinBody C u T G Xp Vs ST SG P μ0 tw M hcW n0 lam0 χ0 Xc e QE xi0 ξT mu0 pin tzO eX
      ((∀ ω, ((Dg.aBd C.K u (T ω) : ℕ) : 𝓞 C.K) ∈ 𝔞p ω ∧ ((Dg.aBdN C.K u (T ω) : ℕ) : 𝓞 C.K) ∈ 𝔞n ω) ∧
        F.RealisesPet C.τK P μ0 tw 𝔞p 𝔞n M fun ω σ φ ψ => HermForms.petAt (ST ω) (lam0 ω) σ (e ω φ).1 (e ω ψ).1)

end SharpDesign

namespace SharpObj

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}
  (b : SharpObj Dg C)

/-- The source lattice `M_ω`: the `O_K`-span of the integral forms of `X ⊓ V_ω` (the frontier's pin). -/
def M (ω : b.Ω) : Submodule (𝓞 C.K) (b.Vs ω) :=
  Submodule.span (𝓞 C.K) {φ | (b.e ω φ).1 ∈ HermForms.Mω (b.ST ω) C.τK (b.χ0 ω) (b.lam0 ω)}

/-- The source `N_ω = {φ ∈ 𝔞_ω⁻¹M_ω : B_ωφ ∈ C_u}` (`PeriodTarget.Nsrc`). -/
def N (ω : b.Ω) : Submodule (𝓞 C.K) (b.Vs ω) := PeriodTarget.Nsrc C.τK b.tw b.𝔞p b.𝔞n b.M ω

/-- **The object is pinned at `u`**: the frontier's pins (`pinBody`), the transfers and `μ(w) = μ0` off `Tw`,
`𝔞⁺, 𝔞⁻ ≠ 0`, and the caps `𝔞⁺ ∣ aBd`, `𝔞⁻ ∣ aBdN` (the clauses of `RealisesPet` and of the body that do not read
the frame). -/
def Pinned (u : S.A) : Prop :=
  Dg.pinBody C u b.T b.G b.Xp b.Vs b.ST b.SG b.P b.μ0 b.tw b.M b.hcW b.n0 b.lam0 b.χ0 b.Xc b.e b.QE b.xi0 b.ξT
      b.mu0 b.pin b.tzO b.eX True ∧
    b.tw.IsTransfer ∧ (∀ w ∉ b.tw.Tw, b.tw.μw w = b.μ0) ∧ (∀ ω, b.𝔞p ω ≠ ⊥ ∧ b.𝔞n ω ≠ ⊥) ∧
    ∀ ω, ((Dg.aBd C.K u (b.T ω) : ℕ) : 𝓞 C.K) ∈ b.𝔞p ω ∧ ((Dg.aBdN C.K u (b.T ω) : ℕ) : 𝓞 C.K) ∈ b.𝔞n ω

open Classical in
/-- **A frame realises the object**, in coordinates `c ω` of the sources and `eC` of the target (the clauses of
`KFrame.RealisesPet` inside its existential, then two more): `N_ω`, `C_u`, `B_ω = P_{μ0}` and the Petersson metrics
of the sources (at each place `v`, the complex Petersson form `HermForms.petAt` at `σ_v`), the target metric is the
object's `g` on `W_u`, and the heights are the object's. -/
def RealWith (F : FrameOn C.K b.Ω) (c : ∀ ω, b.Vs ω ≃ₗ[C.K] (F.n ω → C.K))
    (eC : (b.P.V0 b.μ0 → C.K) →ₗ[C.K] (F.κ → C.K)) : Prop :=
  Set.InjOn eC (b.P.W b.μ0) ∧
    (∀ ω, (F.src ω).M = (b.N ω).map (((c ω : b.Vs ω →ₗ[C.K] (F.n ω → C.K))).restrictScalars (𝓞 C.K))) ∧
    F.tgt.M = (PeriodTarget.Ctgt C.τK b.tw).map (eC.restrictScalars (𝓞 C.K)) ∧
    (∀ ω φ, eC (b.P.P b.μ0 ω φ) = F.B ω (c ω φ)) ∧
    (∀ ω v i j, (F.src ω).G v i j = HermForms.petAt (b.ST ω) (b.lam0 ω) v.1.embedding
      (b.e ω ((c ω).symm (Pi.single i 1))).1 (b.e ω ((c ω).symm (Pi.single j 1))).1) ∧
    (∀ v, ∀ y ∈ b.P.W b.μ0, ∀ z ∈ b.P.W b.μ0,
      b.g v y z = ∑ i, ∑ k, starRingEnd ℂ (v.1.embedding (eC y i)) * F.tgt.G v i k * v.1.embedding (eC z k)) ∧
    ∀ ω v, F.ht ω v = b.ht ω v

/-- **The index term of (V)** in the archive's units: `2(log[N_ω : N_ω ∩ M_ω] − log[M_ω : N_ω ∩ M_ω])/rk`, `rk` the
`ℤ`-rank `[K:ℚ]·dim V_ω`. For lattices in one metric space it is the difference of the slopes `μ(N_ω) − μ(M_ω)`
(the metric cancels), so the gain is a statement about indices alone. -/
def idx (ω : b.Ω) : ℝ :=
  2 * (Real.log ((b.M ω).toAddSubgroup.relIndex (b.N ω).toAddSubgroup) -
      Real.log ((b.N ω).toAddSubgroup.relIndex (b.M ω).toAddSubgroup)) /
    (Module.finrank ℚ C.K * Module.finrank C.K (b.Vs ω))

/-- **The pins close the realisation**: a frame realising a pinned object satisfies `KFrame.RealisesPet`. -/
theorem realisesPet {F : FrameOn C.K b.Ω} {c : ∀ ω, b.Vs ω ≃ₗ[C.K] (F.n ω → C.K)}
    {eC : (b.P.V0 b.μ0 → C.K) →ₗ[C.K] (F.κ → C.K)} (h : b.RealWith F c eC) (htw : b.tw.IsTransfer)
    (hU : ∀ w ∉ b.tw.Tw, b.tw.μw w = b.μ0) (hne : ∀ ω, b.𝔞p ω ≠ ⊥ ∧ b.𝔞n ω ≠ ⊥) :
    F.toKFrame.RealisesPet C.τK b.P b.μ0 b.tw b.𝔞p b.𝔞n b.M
      fun ω σ φ ψ => HermForms.petAt (b.ST ω) (b.lam0 ω) σ (b.e ω φ).1 (b.e ω ψ).1 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨htw, hU, hne, c, eC, h1, h2, h3, h4, h5⟩

/-! ### The statements of the pieces at a translate -/

/-- **(T), the auxiliary primes** (archive: `levelPrime_unconditional`, `exists_levCh`): every word's `T_ω` is a
prime `ππ̄`, `π ≡ 1 (mod M)` (`ArithT`), with `log T_ω ≥ Λ_u − c_T`, and `(Σ_t a_t)·c_T` is within a quarter of the
budget `x^{4ε} Σ_t a_t`. -/
def Primes (u : S.A) : Prop :=
  0 ≤ b.cT ∧ (∑ s ∈ Dg.TT, Dg.a s) * b.cT ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 4 ∧
    ∀ ω, (b.T ω).Prime ∧ Dg.ArithT (b.T ω) ∧
      S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) - b.cT ≤ Real.log (b.T ω)

/-- **The frame exists**: some frame of `O_K`-lattices on the words realises the object (its sources and target are
lattices, the Petersson metrics are positive definite at every place, the target metric is `g`, the heights bound
the maps). -/
def FrameExists : Prop :=
  ∃ (F : FrameOn C.K b.Ω) (c : ∀ ω, b.Vs ω ≃ₗ[C.K] (F.n ω → C.K))
    (eC : (b.P.V0 b.μ0 → C.K) →ₗ[C.K] (F.κ → C.K)), b.RealWith F c eC

/-- **(F) and (V)** (archive: `lower_slope_inequality_family`, from `standard_slope_lower`, `hook_length_bound`,
`column_exact_slope_family`): in every realising frame, `μ(N_ω) ≥ −c_F + idx_ω`, i.e. `μ(M_ω) ≥ −c_F` (F) and
`μ(N_ω) − μ(M_ω) = idx_ω` (V, the index bookkeeping on `covol_eq_relIndex_mul`); `0 ≤ c_F ≤ x^{4ε} Σ_t a_t/8`.
Serves (G↓). -/
def SlopeFV : Prop :=
  0 ≤ b.cF ∧ b.cF ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8 ∧
    ∀ (F : FrameOn C.K b.Ω) c eC, b.RealWith F c eC → ∀ ω : F.toKFrame.frame.ι,
      -b.cF + b.idx ω ≤ (F.toKFrame.frame.N ω).deg ⊤ / (F.toKFrame.frame.N ω).rk ⊤

/-- **The gain in (G↓)** (archive: `closed_linkG_of_duty` with `duty_of_std`, `linkMu_of_full`): the index term is
at least `Σ_t Σ_j ASK(a_t, t, w_{u,j}) − m(Σ_t a_t)·lg + Fo(𝒫_u) − c_G`, a statement about indices alone (local
divisibility of the theta kernels at the inert places, the forced orders); `0 ≤ c_G ≤ x^{4ε} Σ_t a_t/8`. -/
def Gain (u : S.A) : Prop :=
  0 ≤ b.cG ∧ b.cG ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8 ∧
    ∀ ω, ∑ s ∈ Dg.TT, ∑ j, S.ASK (Dg.a s) s (Dg.w u j) - Dg.m * (∑ s ∈ Dg.TT, Dg.a s) * Real.log (Dg.g₀ * Dg.g₁) +
      Dg.R.Fo (Dg.hc u) (S.twA κ) Dg.g₀ Dg.g₁ (S.cutX x ε) - b.cG ≤ b.idx ω

/-- **(G↑)** (archive: `closed_linkDIVt_of_closed_bridge_kernel` with the bridge kernel `link_brest_alt`,
`wire_sel_alt`, `closed_family_admissible_twist_link_alt`, `selection_closed_of_wu_decay_alt`): in every realising
frame, `μ_g(C_u) + h_g(B_ω) − Fo(𝒫_u) ≤ MAIN_ω + c↑`, for the object's target metric `g`; `0 ≤ c↑ ≤ x^{4ε} Σ_t a_t/4`.
Not decomposed further here: its inputs (Rallis, `hX`, Colmez) bear on the target metric, which the library does
not define. -/
def GUp (u : S.A) : Prop :=
  0 ≤ b.cUp ∧ b.cUp ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 4 ∧
    ∀ (F : FrameOn C.K b.Ω) c eC, b.RealWith F c eC → ∀ ω,
      F.toKFrame.frame.C.deg ⊤ / F.toKFrame.frame.C.rk ⊤ + F.toKFrame.frame.h ω -
        Dg.R.Fo (Dg.hc u) (S.twA κ) Dg.g₀ Dg.g₁ (S.cutX x ε) ≤ S.mainW Dg.TT Dg.m Dg.a S.vE (b.T ω) + b.cUp

/-- **(S) and (R)** (archive: `link_alt_alt_bis` with `rowMainEqP_of_siegelWeil`, `rowNGP_of_siegelWeil`,
`rowsPos_typeP`, `wuDecayOfGap`, `rowsFinDim_link`; `slope_inequality_family_four`): in every realising frame, the
frame condition at `pl` for the `c_ω·B_ω` with constants `e`, `η`, positive total rank, the range
`μ_max(N_ω) − h_ω ≤ s_u + U` and the depth `μ_min(C_u) ≥ s_u − H`; the constants are signed and the frame loss
`αH + βU log(1 + H/U)` is within a quarter of the budget. One piece: the range and the depth are read at the same
mean `s_u` and their constants share one budget with `e`, `η`. -/
def FrameSR : Prop :=
  (∀ ω, 0 < b.cω ω) ∧ 0 ≤ b.eS ∧ 0 < b.U ∧ 0 ≤ b.H ∧
    (b.η + 2 * √b.eS / (1 - √b.eS)) * b.H + 2 / (1 - √b.eS) * b.U * Real.log (1 + b.H / b.U) ≤
      x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 4 ∧
    ∀ (F : FrameOn C.K b.Ω) c eC, b.RealWith F c eC →
      FrameAtPlace.FrameCond (fun ω : F.toKFrame.ι => b.cω ω • F.toKFrame.comp ω b.pl) b.eS b.η ∧
      0 < ∑ ω, ((F.toKFrame.frame.N ω).rk ⊤ : ℝ) ∧
      (∀ ω, (F.toKFrame.frame.N ω).SlopeLe (F.toKFrame.frame.mean + b.U + F.toKFrame.frame.h ω)) ∧
      F.toKFrame.frame.C.SlopeGe ⊤ (F.toKFrame.frame.mean - b.H)

end SharpObj

/-! ## The inputs (`SharpInputs`) -/

/-- The representation number `r_N(β) = #{x ∈ N^k : h(x_i, x_j) = β_ij}` of a hermitian matrix by a lattice. -/
def repNum {E : Type} [Field E] [NumberField E] [IsCMField E] {n k : ℕ} (N : Submodule (𝓞 E) (Fin n → E))
    (β : Matrix (Fin k) (Fin k) E) : ℕ :=
  Nat.card {y : Fin k → N // ∀ i j, herm (y i : Fin n → E) (y j) = β i j}

open scoped ComplexOrder in
/-- **Siegel–Weil, with Rallis** (permanent; archive: `SiegelWeilU.SiegelWeilUnitaryConvergent`). For the decorated
unimodular hermitian lattices of rank `n` at any level, in the convergent range `2k < n`, the mass-weighted sum of
the representation numbers of a totally positive `β` is a sum over genera of `c·|N_{F/ℚ} det β|^{n−k}` (the
archimedean Whittaker factor) times a product of local factors `α_w(β)`, each locally constant in `β` and `1` at
almost all `w`. **Precision:** the classical statement identifies the local factors with Siegel series; the library
has no local densities, so this is its structural consequence. Rallis's inner product formula is this identity for
the doubled space (the doubling see-saw) with local doubling integrals; the reduction uses it in that form. -/
def SiegelWeil : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n k : ℕ), 2 * k < n →
    ∀ (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))),
    ∃ (J : ℕ) (c : Fin J → ℝ) (α : Fin J → HeightOneSpectrum (𝓞 E) → Matrix (Fin k) (Fin k) E → ℝ),
      (∀ i β, (Function.mulSupport fun w => α i w β).Finite) ∧
      (∀ i w β, ∃ R : ℕ, ∀ β' : Matrix (Fin k) (Fin k) E,
        (∀ a a', ∃ z : 𝓞 E, z ∈ w.asIdeal ^ R ∧ β' a a' = β a a' + (z : E)) → α i w β' = α i w β) ∧
      ∀ β : Matrix (Fin k) (Fin k) E, (∀ σ : E →+* ℂ, (β.map σ).PosDef) →
        ((classSum fun c : DCl E n ST Λ => (repNum c.rep.N β : ℚ) : ℚ) : ℝ) =
          ∑ i, c i * √|((Algebra.norm ℚ β.det : ℚ) : ℝ)| ^ (n - k) * ∏ᶠ w, α i w β

/-- **The covolume bound `hX`** (permanent; archive: `GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries`).
**Precision:** the classical bound is on the integral rows of the indefinite side (toroidal compactification,
Arakelov degrees), which the library cannot state. Stated is the consequence the frame uses: at every pinned object
the integral rows `R_{μ0}` span `V0_{μ0}` and lie in a finitely generated `O_K`-module, so the target `C_u` is a
lattice in `W_u`. Its quantitative part enters `gUp` through the target metric. -/
def Covolume : Prop :=
  ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X) (C : SharpCoeff S) (u : S.A)
    (b : SharpObj Dg C), b.Pinned u →
      Submodule.span C.K (b.P.R C.τK b.μ0) = ⊤ ∧
      ∃ L : Submodule (𝓞 C.K) (Cl (b.G b.μ0) (b.Xp b.μ0) →₀ Pol (Φ S.A) (Dg.R.N Dg.R.m - 1) C.K),
        L.FG ∧ ∀ r ∈ b.P.R C.τK b.μ0, (r : Cl (b.G b.μ0) (b.Xp b.μ0) →₀ Pol (Φ S.A) (Dg.R.N Dg.R.m - 1) C.K) ∈ L

/-- **Good twists exist** (permanent; archive: `TwistTheoremAtIndex`). The twist characters of the pins: if `L` has
the `15`-th roots of unity, characters `δ` with `IsDelta p` at primes `p` beyond any bound; if `L` has the `ℓ`-th
roots of unity, characters `ψ` with `IsPsi ℓ Q`, ramified exactly at a nonempty set `Q` avoiding any finite set.
**Precision:** the theorem's index part (the twisted theta lattices `ℓ⁻²`-close to the untwisted ones, the
Bloch–Kato side) is on the step-`j` theta images, which the frontier does not reach (`SharpChain`, "Twist
characters"); its consequence at the frontier, the finiteness of `[A_ω + B_ω : B_ω]`, is a pin, proved in `pins`
from this input. -/
def GoodTwists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Type) [Field L] [NumberField L],
    ((∃ ζ : L, IsPrimitiveRoot ζ 15) → ∀ B : ℕ, ∃ p, B < p ∧ p.Prime ∧ ∃ δ : Hecke E L, δ.IsDelta p) ∧
    ∀ ℓ : ℕ, ℓ.Prime → (∃ ζ : L, IsPrimitiveRoot ζ ℓ) → ∀ avoid : Finset (HeightOneSpectrum (𝓞 E)),
      ∃ (Q : Set (HeightOneSpectrum (𝓞 E))) (ψ : Hecke E L), Q.Nonempty ∧ (∀ v ∈ Q, v ∉ avoid) ∧ ψ.IsPsi ℓ Q

open Classical in
/-- **The unitary mass formula** (for now; archive: `genusMassAt_two`, `MassRatioUnderVolume`, Gan–Hanke–Yu).
**Precision:** the classical formula is `Σ_c 1/|Aut c| = ∏ L(1 − j, χ^j) × local masses`; the library has no
Hecke `L`-values of the real subfield. Stated is the consequence (F), the gain and (R) use: the logarithm of the
total mass of every level is at most `C₀(n + 1)²[E:ℚ]·log((n + 2)|d_E|∏_{w ∈ ST ∪ SG} Nw)`. -/
def MassFormula : Prop :=
  ∃ C₀ : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))),
    Real.log ((classSum fun _ : DCl E n ST Λ => (1 : ℚ) : ℚ) : ℝ) ≤
      C₀ * (n + 1) ^ 2 * Module.finrank ℚ E *
        Real.log ((n + 2) * |(discr E : ℝ)| * ∏ w ∈ ST ∪ SG, (Ideal.absNorm w.asIdeal : ℝ))

/-- **The local Weil representation and Howe duality** (for now; archive: the Weil-representation bundles `P`, `F`,
`ThetaLocalInputs`). **Precision:** the local statements (the Weil representation preserves the integral Schwartz
functions at the unramified places; local theta correspondence) need local representations, which the library does
not define. Stated is the consequence the frame and the gain use: at every pinned object, the untwisted periods of
the integral forms `M_ω` are integral on the integral rows at every place `w` of `K` prime to the cap `aBdN` and to
`xi0`. -/
def Howe : Prop :=
  ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X) (C : SharpCoeff S) (u : S.A)
    (b : SharpObj Dg C), b.Pinned u → ∀ ω, ∀ φ ∈ b.M ω, ∀ w : HeightOneSpectrum (𝓞 C.K),
      ((Dg.aBdN C.K u (b.T ω) : ℕ) : 𝓞 C.K) ∉ w.asIdeal → (∀ ρ, w.valuation C.K (C.τK ρ b.xi0) = 1) →
        b.P.P b.μ0 ω φ ∈ PeriodTarget.IntOn w (b.P.R C.τK b.μ0)

/-- **Chowla–Selberg / Colmez** (for now; abelian CM: Colmez). **Precision:** the period side (the CM periods,
Faltings heights of CM abelian varieties) is not in the library. Stated is its `L`-function side, the form in which
`MAIN`'s `log Ω` (`Setting.logΩ`, through `L′/L(1, χ_d)` and the functional equation) is read: Lerch's formula
`L′(0, χ_d) + log d·L(0, χ_d) = Σ_a χ_d(a) log Γ(a/d)` for the quadratic character of a prime `d ≡ 3 (mod 4)`. -/
def Colmez : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 4 = 3 →
    deriv (DirichletCharacter.LFunction (legChar d)) 0 +
        (Real.log d : ℂ) * DirichletCharacter.LFunction (legChar d) 0 =
      ∑ a ∈ Finset.range d, legChar d (a : ZMod d) * (Real.log (Real.Gamma (a / d)) : ℂ)

/-- **`ShortNorm`: Chebotarev in short intervals for `ℚ(√−d)`** (for now; archive: `UpperTheory.T3.ShortNorm`,
`normPrimes_short_interval_lower`), the classical statement: for a prime `d ≡ 3 (mod 4)`, `d ≥ 100`, and `M ≥ 3` with
`log(4dM²) ≤ c√log Y`, every interval `(Y, Y(1 + h)]` with `e^{−c√log Y} ≤ h ≤ 1` holds at least
`c′hY/((4dM²)^A log Y)` primes `p = ππ̄`, `π = (a + b√−d)/2 ≡ 1 (mod M)`. -/
def ShortNorm : Prop :=
  ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → ∀ Y h : ℝ,
    Real.log (4 * d * M ^ 2) ≤ c * √(Real.log Y) → Real.exp (-(c * √(Real.log Y))) ≤ h → h ≤ 1 →
      c' * h * Y / ((4 * d * M ^ 2 : ℝ) ^ A * Real.log Y) ≤
        ({p : ℕ | Y < p ∧ (p : ℝ) ≤ Y * (1 + h) ∧ p.Prime ∧ ∃ a b : ℤ, 4 * (p : ℤ) = a ^ 2 + d * b ^ 2 ∧
          (M : ℤ) ∣ b ∧ a ≡ b + 2 [ZMOD 2 * M]}.ncard : ℝ)

/-- **The deep classical inputs**, as hypotheses (proof plan §5): permanent — Siegel–Weil with Rallis, the
covolume bound `hX`, good twists; for now — the unitary mass formula, the local Weil representation and Howe
duality, Chowla–Selberg/Colmez, `ShortNorm`. -/
structure SharpInputs : Prop where
  /-- Siegel–Weil, with Rallis. -/
  siegelWeil : SiegelWeil
  /-- The covolume bound `hX`. -/
  covolume : Covolume
  /-- Good twists exist. -/
  goodTwists : GoodTwists
  /-- The unitary mass formula. -/
  massFormula : MassFormula
  /-- The local Weil representation and Howe duality. -/
  howe : Howe
  /-- Chowla–Selberg / Colmez. -/
  colmez : Colmez
  /-- Chebotarev in short intervals for `ℚ(√−d)`. -/
  shortNorm : ShortNorm

/-! ## The pieces (`SharpPieces`) -/

/-- **Finitely many classes, finite stabilisers** (C1; archive: the finiteness inside the objects' construction):
the decorated unimodular hermitian lattices of every rank and level fall into finitely many classes, each with a
finite stabiliser (so `0 < mass c`). Serves the rows' `Finite (Cl …)` pin and the lattices of the frame. -/
def FiniteClasses : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E)))
    (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))),
    Finite (DCl E n ST Λ) ∧ ∀ c : DCl E n ST Λ, Finite (stab c)

open scoped ComplexOrder in
/-- **The forms are finite-dimensional, the integral forms a lattice** (C2; archive: `rowsFinDim_link`): for a
dominant weight, the forms are finite-dimensional, the `O_L`-span of the integral forms of the cut is a lattice
(`span_bidet`), and the Gram matrix of the Petersson form at every place (`HermForms.gram` at `σ_v`, of
`HermForms.petAt`) is positive definite: automatic given finitely many classes, each with a finite stabiliser
(`FiniteClasses`), as `H_σ(F, F)` is a positive combination of Fock norms of the `σF(rep c)` and a form vanishing at
every representative is `0`. Serves the sources `N_ω` of the frame (`HermForms.source` is then a `KLattice`). -/
def FormsLattice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E)))
    (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) (Φ : Type) [Fintype Φ] [DecidableEq Φ]
    (L : Type) [Field L] [NumberField L] (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ),
    (∀ ρ, Antitone (lam ρ)) →
    FiniteDimensional L (HermForms.Forms ST τ χ lam) ∧
      ∃ _ : FiniteDimensional L (HermForms.Vω ST τ χ lam), (HermForms.Mlat ST τ χ lam).IsLattice L ∧
        ∀ v : Pl L, (HermForms.gram ST τ χ lam v.1.embedding).PosDef

/-- **The statements to prove in the library** (proof plan §3–§4), with the inputs as hypotheses where a piece
uses them. Two fields are choices, not statements: `adm`, the conditions the construction asks of the parameters,
and `cons`, the construction itself (the archive's objects, the target metric, the constants), which the frontier
leaves existential and several pieces share. Every other field is a statement about them, provable on its own. -/
structure SharpPieces where
  /-- The admissible designs: the conditions the construction needs on the parameters. -/
  adm : ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}, SharpDesign S κ x ε X → Prop
  /-- The construction of a design. -/
  cons : ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X), SharpCons Dg
  /-- C1: finitely many classes, finite stabilisers. -/
  finiteClasses : FiniteClasses
  /-- C2: the forms finite-dimensional, the integral forms a lattice, the Petersson form positive. -/
  formsLattice : FormsLattice
  /-- **Admissible parameters and windows** (archive: `designExists_of_tuSize_aux4n_litThin`; the library's
  `ZetaPair`/`ZetaTwist` windows): the frontier's outer shape, with an admissible design at every `x` of the
  sub-window. Serves the outer quantifiers, `S.q = q`, `S.d = d`, `d ≡ 3 (mod 4)`, `κ` lifting `χ`, the weights and
  the parameters of `SharpData`, and `Arith`'s Legendre symbols. -/
  params : ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → ∀ ε₀ > 0, ∃ ε, 0 < ε ∧ ε < ε₀ ∧
    ∃ A ≥ (1 : ℝ), ∀ᶠ Y in Filter.atTop, ∀ q d, ZetaTwist.WinPair ε Y q d →
      ∃ Y' ∈ Set.Icc Y (Y ^ (A / 2)), ∀ x ∈ Set.Icc Y' (Y' ^ 2), ∃ (S : Setting) (κ : S.A →* ℂˣ), S.q = q ∧
        S.d = d ∧ S.d % 4 = 3 ∧ S.Lifts κ χ ∧ ∃ Dg : SharpDesign S κ x ε (((S.N : ℝ) * x) ^ Real.log x), adm Dg
  /-- **The pins are satisfiable** (archive: the definite-side objects of
  `nonempty_hyps_definite_side_of_closed_bound`): `j ∘ τ_K = Setting.τ`, and every translate's object is pinned
  (`SharpObj.Pinned`). Serves `RealisedPinned` but for the frame. -/
  pins : FiniteClasses → GoodTwists → Howe → ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}
    (Dg : SharpDesign S κ x ε X), adm Dg →
      (∀ ρ, (cons Dg).C.j.comp ((cons Dg).C.τK ρ) = S.τ ρ) ∧ ∀ u ∈ A₀ κ, ((cons Dg).obj u).Pinned u
  /-- **The frame exists** (C1, C2 and the lattices: `M_ω`, `N_ω`, `C_u` are `O_K`-lattices). Serves `SharpData.fr`
  and `KFrame.RealisesPet`. -/
  frame : FiniteClasses → FormsLattice → Covolume → Howe → ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}
    (Dg : SharpDesign S κ x ε X), adm Dg → ∀ u ∈ A₀ κ, ((cons Dg).obj u).FrameExists
  /-- **(T)**, with `Arith`'s auxiliary primes (`SharpObj.Primes`). -/
  primes : ShortNorm → ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X), adm Dg →
    ∀ u ∈ A₀ κ, ((cons Dg).obj u).Primes u
  /-- **(F) and (V)**, half of (G↓) (`SharpObj.SlopeFV`). -/
  slopeFV : MassFormula → ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X), adm Dg →
    ∀ u ∈ A₀ κ, ((cons Dg).obj u).SlopeFV
  /-- **The gain in (G↓)** (`SharpObj.Gain`). -/
  gain : Howe → MassFormula → ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X),
    adm Dg → ∀ u ∈ A₀ κ, ((cons Dg).obj u).Gain u
  /-- **(G↑)** (`SharpObj.GUp`). -/
  gUp : SiegelWeil → Covolume → Colmez → MassFormula → ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}
    (Dg : SharpDesign S κ x ε X), adm Dg → ∀ u ∈ A₀ κ, ((cons Dg).obj u).GUp u
  /-- **(S) and (R)** (`SharpObj.FrameSR`). -/
  frameSR : SiegelWeil → Covolume → MassFormula → ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}
    (Dg : SharpDesign S κ x ε X), adm Dg → ∀ u ∈ A₀ κ, ((cons Dg).obj u).FrameSR

/-! ## The reduction -/

/-- **The data of sharp data at one translate**: a frame, auxiliary primes on its words, and the constants. -/
structure SharpTr (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] where
  /-- The frame. -/
  F : KFrame K
  /-- The auxiliary primes. -/
  T : F.ι → ℕ
  /-- The place of the frame condition. -/
  pl : Pl K
  /-- The scalars of the frame condition. -/
  cω : F.ι → ℝ
  /-- `e`. -/
  e : ℝ
  /-- `η`. -/
  η : ℝ
  /-- The range. -/
  U : ℝ
  /-- The depth. -/
  H : ℝ
  /-- `c↓`. -/
  cDn : ℝ
  /-- `c↑`. -/
  cUp : ℝ
  /-- `c_T`. -/
  cT : ℝ

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}

/-- The clauses of `SharpData` and `SharpData.Arith` asked at every translate: primes with `Arith`, signs. -/
structure SharpTr.Basic {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (Dg : SharpDesign S κ x ε X)
    (t : SharpTr K) : Prop where
  /-- The auxiliary primes are prime. -/
  T_prime : ∀ ω, (t.T ω).Prime
  /-- `Arith` for the auxiliary primes. -/
  arith : ∀ ω, Dg.ArithT (t.T ω)
  /-- `c_ω > 0`. -/
  cω_pos : ∀ ω, 0 < t.cω ω
  /-- `0 ≤ e`. -/
  e_nonneg : 0 ≤ t.e
  /-- `c↓ ≥ 0`. -/
  cDn_nonneg : 0 ≤ t.cDn
  /-- `c↑ ≥ 0`. -/
  cUp_nonneg : 0 ≤ t.cUp
  /-- `c_T ≥ 0`. -/
  cT_nonneg : 0 ≤ t.cT

/-- The clauses of `SharpData` and `SharpData.RealisedPinned` asked at a translate `u ∈ A₀`, with (Z) for this
translate (`budget`). -/
structure SharpTr.Sharp (Dg : SharpDesign S κ x ε X) (C : SharpCoeff S) (u : S.A) (t : SharpTr C.K) : Prop where
  /-- (T). -/
  hT : ∀ ω, S.lam (Dg.w u) S.vE (Real.log (Dg.g₀ * Dg.g₁)) - t.cT ≤ Real.log (t.T ω)
  /-- (G↓). -/
  hGdn : ∀ ω, ∑ s ∈ Dg.TT, ∑ j, S.ASK (Dg.a s) s (Dg.w u j) -
      Dg.m * (∑ s ∈ Dg.TT, Dg.a s) * Real.log (Dg.g₀ * Dg.g₁) +
      Dg.R.Fo (Dg.hc u) (S.twA κ) Dg.g₀ Dg.g₁ (S.cutX x ε) - t.cDn ≤ (t.F.frame.N ω).deg ⊤ / (t.F.frame.N ω).rk ⊤
  /-- (G↑). -/
  hGup : ∀ ω, t.F.frame.C.deg ⊤ / t.F.frame.C.rk ⊤ + t.F.frame.h ω -
      Dg.R.Fo (Dg.hc u) (S.twA κ) Dg.g₀ Dg.g₁ (S.cutX x ε) ≤ S.mainW Dg.TT Dg.m Dg.a S.vE (t.T ω) + t.cUp
  /-- (S). -/
  hS : FrameAtPlace.FrameCond (fun ω => t.cω ω • t.F.comp ω t.pl) t.e t.η
  /-- (R): positive total rank. -/
  rk_pos : 0 < ∑ ω, ((t.F.frame.N ω).rk ⊤ : ℝ)
  /-- (R): the range. -/
  range : ∀ ω, (t.F.frame.N ω).SlopeLe (t.F.frame.mean + t.U + t.F.frame.h ω)
  /-- (R): the depth. -/
  depth : t.F.frame.C.SlopeGe ⊤ (t.F.frame.mean - t.H)
  /-- `U > 0`. -/
  U_pos : 0 < t.U
  /-- `H ≥ 0`. -/
  H_nonneg : 0 ≤ t.H
  /-- (Z) at this translate. -/
  budget : t.cDn + t.cUp + (∑ s ∈ Dg.TT, Dg.a s) * t.cT +
      ((t.η + 2 * √t.e / (1 - √t.e)) * t.H + 2 / (1 - √t.e) * t.U * Real.log (1 + t.H / t.U)) ≤
    x ^ (4 * ε) * ∑ s ∈ Dg.TT, Dg.a s
  /-- The pinned realisation at this translate. -/
  pins : Dg.PinsAt C u t.F t.T

/-- **One translate from its pieces**: a pinned object with a realising frame, whose primes, slopes, gain, (G↑),
(S) and (R) hold, gives the clauses of sharp data at `u`. (G↓) is (F) + (V) (`SlopeFV`) with the gain (`Gain`),
`c↓ = c_F + c_G`; (Z) at `u` adds the four quarter-budgets; the pins and the realisation (`realisesPet`) close
`RealisedPinned`'s body. -/
theorem SharpObj.exists_sharpTr {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S} (b : SharpObj Dg C) (u : S.A)
    (hpin : b.Pinned u) (hfr : b.FrameExists) (hT : b.Primes u) (hFV : b.SlopeFV) (hgain : b.Gain u)
    (hup : b.GUp u) (hSR : b.FrameSR) : ∃ t : SharpTr C.K, t.Basic Dg ∧ t.Sharp Dg C u := by
  obtain ⟨hbody, htw, huntw, hne, hcaps⟩ := hpin
  obtain ⟨F, c, eC, hR⟩ := hfr
  obtain ⟨hcT0, hcT, hT⟩ := hT
  obtain ⟨hcF0, hcF, hFV⟩ := hFV
  obtain ⟨hcG0, hcG, hgain⟩ := hgain
  obtain ⟨hcU0, hcU, hup⟩ := hup
  obtain ⟨hcω, he0, hU0, hH0, hloss, hSR⟩ := hSR
  obtain ⟨hS, hrk, hrange, hdepth⟩ := hSR F c eC hR
  refine ⟨⟨F.toKFrame, b.T, b.pl, b.cω, b.eS, b.η, b.U, b.H, b.cF + b.cG, b.cUp, b.cT⟩,
    ⟨fun ω => (hT ω).1, fun ω => (hT ω).2.1, hcω, he0, add_nonneg hcF0 hcG0, hcU0, hcT0⟩,
    ⟨fun ω => (hT ω).2.2, fun ω => ?_, hup F c eC hR, hS, hrk, hrange, hdepth, hU0, hH0, ?_, ?_⟩⟩
  · have h1 := hFV F c eC hR ω
    have h2 := hgain ω
    dsimp only
    linarith
  · dsimp only
    linarith
  · unfold SharpDesign.PinsAt
    refine ⟨b.Tμ, b.G, b.Xp, inferInstance, inferInstance, b.Vs, inferInstance, inferInstance, inferInstance,
      inferInstance, b.ST, b.SG, b.P, b.μ0, b.tw, b.𝔞p, b.𝔞n, b.M, b.hcW, b.n0, b.lam0, b.χ0, b.Xc, b.e, b.QE,
      b.xi0, b.ξT, b.mu0, b.s, b.pin, b.tzO, b.eX, ?_⟩
    unfold SharpDesign.pinBody at hbody ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -⟩ := hbody
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hcaps, b.realisesPet hR htw huntw hne⟩

/-- **One translate from the pieces**: at `u ∈ A₀`, the pieces about the construction's object, with the inputs
they use. -/
theorem exists_sharpTr (I : SharpInputs) (P : SharpPieces) (Dg : SharpDesign S κ x ε X) (hDg : P.adm Dg)
    (u : S.A) (hu : u ∈ A₀ κ) :
    ∃ t : SharpTr (P.cons Dg).C.K, t.Basic Dg ∧ t.Sharp Dg (P.cons Dg).C u :=
  ((P.cons Dg).obj u).exists_sharpTr u ((P.pins P.finiteClasses I.goodTwists I.howe Dg hDg).2 u hu)
    (P.frame P.finiteClasses P.formsLattice I.covolume I.howe Dg hDg u hu)
    (P.primes I.shortNorm Dg hDg u hu) (P.slopeFV I.massFormula Dg hDg u hu)
    (P.gain I.howe I.massFormula Dg hDg u hu) (P.gUp I.siegelWeil I.covolume I.colmez I.massFormula Dg hDg u hu)
    (P.frameSR I.siegelWeil I.covolume I.massFormula Dg hDg u hu)

/-- **Sharp data from the pieces**, for an admissible design: the translates of `A₀` from `exists_sharpTr`, the
others from the translate `1` (`SharpData` asks primes and signs at every translate); (Z) is the sum of the
translates' budgets. -/
theorem exists_sharpData (I : SharpInputs) (P : SharpPieces) (Dg : SharpDesign S κ x ε X) (hDg : P.adm Dg) :
    ∃ D : SharpData S κ x ε X (P.cons Dg).C.K, D.RealisedPinned ∧ D.Arith := by
  have h1 : (1 : S.A) ∈ A₀ κ := by simp [A₀]
  obtain ⟨t₁, hb₁, -⟩ := exists_sharpTr I P Dg hDg 1 h1
  have hex : ∀ u, ∃ t : SharpTr (P.cons Dg).C.K, t.Basic Dg ∧ (u ∈ A₀ κ → t.Sharp Dg (P.cons Dg).C u) := by
    intro u
    by_cases hu : u ∈ A₀ κ
    · obtain ⟨t, hb, hs⟩ := exists_sharpTr I P Dg hDg u hu
      exact ⟨t, hb, fun _ => hs⟩
    · exact ⟨t₁, hb₁, fun h => absurd h hu⟩
  choose tr htr using hex
  obtain ⟨hlift, -⟩ := P.pins P.finiteClasses I.goodTwists I.howe Dg hDg
  let D : SharpData S κ x ε X (P.cons Dg).C.K :=
    { toWeights := Dg.toWeights
      R := Dg.R
      hm := Dg.hm
      hc := Dg.hc
      hw := Dg.hw
      g₀ := Dg.g₀
      g₁ := Dg.g₁
      g₀_prime := Dg.g₀_prime
      g₁_prime := Dg.g₁_prime
      g₀_ne_g₁ := Dg.g₀_ne_g₁
      fr := fun u => (tr u).F
      T := fun u => (tr u).T
      T_prime := fun u => (htr u).1.T_prime
      pl := fun u => (tr u).pl
      cω := fun u => (tr u).cω
      e := fun u => (tr u).e
      η := fun u => (tr u).η
      U := fun u => (tr u).U
      H := fun u => (tr u).H
      cDn := fun u => (tr u).cDn
      cUp := fun u => (tr u).cUp
      cT := fun u => (tr u).cT
      cω_pos := fun u => (htr u).1.cω_pos
      e_nonneg := fun u => (htr u).1.e_nonneg
      U_pos := fun u hu => ((htr u).2 hu).U_pos
      H_nonneg := fun u hu => ((htr u).2 hu).H_nonneg
      cDn_nonneg := fun u => (htr u).1.cDn_nonneg
      cUp_nonneg := fun u => (htr u).1.cUp_nonneg
      cT_nonneg := fun u => (htr u).1.cT_nonneg
      hT := fun u hu => ((htr u).2 hu).hT
      hGdn := fun u hu => ((htr u).2 hu).hGdn
      hGup := fun u hu => ((htr u).2 hu).hGup
      hS := fun u hu => ((htr u).2 hu).hS
      rk_pos := fun u hu => ((htr u).2 hu).rk_pos
      range := fun u hu => ((htr u).2 hu).range
      depth := fun u hu => ((htr u).2 hu).depth
      sizes := (Finset.sum_le_card_nsmul _ _ _ fun u hu => ((htr u).2 hu).budget).trans_eq
        (by rw [nsmul_eq_mul, mul_assoc]) }
  exact ⟨D, ⟨inferInstance, inferInstance, (P.cons Dg).C.τK, (P.cons Dg).C.j, hlift,
    fun u hu => ((htr u).2 hu).pins⟩, Dg.leg₀, Dg.leg₁, fun u ω => (htr u).1.arith ω⟩

/-- **The sharp frontier from the inputs and the pieces**: `params` gives the outer shape and an admissible design
at every `x`; `exists_sharpData` the realised pinned sharp data with `Arith`. -/
theorem sharpBoundPinned_of_inputs (I : SharpInputs) (P : SharpPieces) : SharpBoundPinned := by
  intro f _ χ hχ ε₀ hε₀
  obtain ⟨ε, hε, hεε₀, A, hA, hY⟩ := P.params f χ hχ ε₀ hε₀
  refine ⟨ε, hε, hεε₀, A, hA, hY.mono fun Y hY q d hp => ?_⟩
  obtain ⟨Y', hY', hx⟩ := hY q d hp
  refine ⟨Y', hY', fun x hx' => ?_⟩
  obtain ⟨S, κ, hq, hd, hd4, hL, Dg, hDg⟩ := hx x hx'
  obtain ⟨D, hD, hAr⟩ := exists_sharpData I P Dg hDg
  exact ⟨S, κ, hq, hd, hd4, hL, _, _, _, _, D, hD, hAr⟩

/-- **CONDITIONAL. RH and GRH from the inputs and the pieces** (on the half-plane `Re s > 11/12`). -/
theorem rhAndGRH_of_inputs (I : SharpInputs) (P : SharpPieces) : HalfPlaneGRH.RHandGRH :=
  rhAndGRH_of_sharpBoundPinned (sharpBoundPinned_of_inputs I P)

end

end ZetaBalance
