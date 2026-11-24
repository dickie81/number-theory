import SharpBound
import ThetaChain
import HermForms

/-!
# The sharp frontier with the theta chain — CONDITIONAL on the half-plane

Closes the chain hook of `SharpBound` (L7): the canonical hook `thetaHook`, whose `col` is the last step of
`ThetaChain.Data.chain`, and the frontier `SharpBoundTheta := SharpBound thetaHook`.

**The reading** (`IsThetaCol`). `col φ = recast (Θ_m(inp(e φ)) ∘ lift)`, with
* (a) `lift`: lattices of rank `N_m` → classes at level `m`, existential, with the spec's property: a lattice that is
  `Lsh` of a decorated lattice goes to the class of a decorated lattice with that `Lsh` (L7 notes, item 4: the period
  reads `col` at `til`, and `Lsh(til d) = til(Lsh′ d)`);
* (b) the cast `N_m = n + 1` (`recast`);
* (c) `inp`: forms → the chain's input, `F ↦ (c ↦ F(rep c))` (`Data.inp`), after an `L`-isomorphism `e` of the source
  with `X ⊓ V_ω` (`HermForms.Vω` at step 0, with the explicit level `uniUT` and a character over `lamGen`), for a
  cusp subspace `X` stable under the diamond operators (L7 notes, item 3; `X ≤ Forms` adds nothing to `X ⊓ V_ω`);
* (d) `Data` existential, with `ChIdx`'s conditions on the fields `Data` has: `β 0` and `β(m−1)` singletons, every
  `β j` finite, `Λ 0 = uniUT`; its level data `(β, Λ)` are a `ChIdx`'s (`S = ST ∪ SG`, `σ₀` of `P`), up to a
  bijection of the index types; its characters are `μ_{0,j}ξ` with `μ_{0,j}` a `LiftChars` for given `e`, `Sg`.
  Against `κ ≡ 0`: `S = ST ∪ SG` (the archive's place set of `homAt`), `cA, cB > 0`, the Heisenberg data have
  `SA, SB ≠ ∅` and `vol > 0`, and every class at a level `j + 1 ≤ m` meets a nonzero `Ξ`.

**The pinned frontier** (`SharpBoundPinned`) adds what the hook cannot see: the chain's CM type is `τ_K`, the
branching maps are `PeriodTarget.br` with `c_Br ≠ 0` and `IsFockProj` at `λ = λ_m` and `σ = P.σ = sgT` of `hc u`
(`BrPinned`, `lamW`, `sgW`), the lift characters have `e_j` of `hc u` and `Sg` the places above `g₀g₁` (`eW`, `Sg`),
`(−d/g₀) = (−d/g₁) = 1`, and
`T_ω = ππ̄` with `π = (a + b√−d)/2 ≡ 1 (mod M)`, `M = QS·q·d·(g₀g₁)²` (`SharpData.Arith`; for `d ≡ 3 (mod 4)`,
`π − 1 ∈ M·O_{K₀}` iff `M ∣ b` and `a ≡ b + 2 (mod 2M)`). It implies `SharpBoundTheta`.

**Source pins** (L4.3, L6.5, audit of `KLattice.G`): `IsThetaCol` also reads, through `e`, a hermitian form `hV`
(the Petersson form `HermForms.pet` of `X ⊓ V_ω`) and a set `MV` (the integral forms `HermForms.Mω`); the pinned
frontier takes `K` CM, `M_ω = O_K·MV`, and the source metrics `G_v = σ_v(hV)` in the coordinates of the frame
(`KFrame.RealisesPet`). The target metric stays existential. Not pinned: the twisted levels' `lat`, `lsh` (only
`V0 ≠ 0` there), a lower bound on `X` or on the words.

**Open.** Existential: `Data`'s remaining fields (theta constants, `Ξ`, weights, `ξ`, `dI`), `xi0`, `lift`,
`X`, `e` (one per level and word), the branching projection, the `ChIdx` representatives and characters. `Ycos` (the
last step's coset `Y`) is not reached: `Data` has no field that reads it. Not stated: `Tw` closed under conjugation
(`K` is not assumed CM), `T_ω ∉ {pde, pde′}`, `cB = T·∏q^B`, `cA = ∏q^A` exactly, the later-step `ChIdx` ties.

**Sanity theorem:** `Data.comp_zero_inp`.
-/

namespace ZetaBalance

open NumberField IsDedekindDomain HermClasses ThetaChain WeylFock

noncomputable section

section Hook

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {E L : Type} [Field E] [NumberField E] [IsCMField E] [Field L]
  [NumberField L] {τ : Φ → (E →+* L)}

/-- (b) A function on the lattices of rank `N`, read at rank `N′ = N` (the cast `N_m = n + 1`). -/
def recast {N N' : ℕ} (h : N = N') (f : Submodule (𝓞 E) (Fin N → E) → Pol Φ N L) :
    Submodule (𝓞 E) (Fin N' → E) → Pol Φ N' L := by
  subst h; exact f

/-- (c) The chain's input from functions on decorated lattices: `F ↦ (c ↦ F(rep c))` on the step-0 classes. -/
def _root_.ThetaChain.Data.inp (D : Data τ) (Λ : Subgroup (∀ w : D.SG, GL (Fin (D.n 0)) (𝓞 E ⧸ w.1.asIdeal))) :
    HermForms.Fn D.ST Λ Φ L →ₗ[L] (D.chain.C 0 → Pol Φ (D.n 0) L) :=
  LinearMap.funLeft L _ fun c => ⟨c.2.rep, c.2.good⟩

omit [NumberField L] in
/-- **Sanity:** the chain of length `0` reads a form at the representative of each class. -/
theorem _root_.ThetaChain.Data.comp_zero_inp (D : Data τ)
    (Λ : Subgroup (∀ w : D.SG, GL (Fin (D.n 0)) (𝓞 E ⧸ w.1.asIdeal))) (F : HermForms.Fn D.ST Λ Φ L)
    (c : D.chain.C 0) : D.chain.comp 0 (D.inp Λ F) c = F ⟨c.2.rep, c.2.good⟩ :=
  rfl

open Classical in
/-- **`col` is the theta chain's** at one level and word: `col φ = recast (Θ_m(inp(e φ)) ∘ lift)` for theta data
`D` with `ChIdx`'s conditions and the anti-degeneracy conditions, a cusp subspace `X`, an isomorphism `e` of the
source with `X ⊓ V_ω`, and a lift of lattices to classes with the spec's property (module docstring, (a)–(d)). -/
def IsThetaCol [IsCMField L] (τ : Φ → (E →+* L)) (eF : ℕ → Φ → ℤ) (Sg : Set (HeightOneSpectrum (𝓞 E))) (n : ℕ)
    {V : Type} [AddCommGroup V] [Module L V] (hV : V → V → L) (MV : Set V)
    (col : V →ₗ[L] PeriodTarget.Col Φ n E L) : Prop :=
  ∃ (D : Data τ) (m : ℕ) (hm : D.n m = n + 1) (xi0 : E) (χ0 : uniUT D.SG (D.n 0) →* L)
    (X : Submodule L (HermForms.Fn D.ST (uniUT D.SG (D.n 0)) Φ L))
    (e : V ≃ₗ[L] ↥(X ⊓ HermForms.Vω D.ST τ χ0 (D.lam 0)))
    (lift : Submodule (𝓞 E) (Fin (D.n m) → E) → D.chain.C m),
    (Nonempty (Unique (D.β 0)) ∧ Nonempty (Unique (D.β (m - 1))) ∧ (∀ j, Finite (D.β j)) ∧
      (∀ b, D.Λ 0 b = uniUT D.SG (D.n 0)) ∧
      ∀ g, D.P.σ₀ (χ0 g) = lamGen xi0 (g : ∀ w : D.SG, GL (Fin (D.n 0)) (𝓞 E ⧸ w.1.asIdeal))) ∧
    (D.S = ↑D.ST ∪ ↑D.SG ∧ (∀ j, 0 < D.cA j ∧ 0 < D.cB j) ∧
      (∀ j c c', (D.XD j c c').SA.Nonempty ∧ (D.XD j c c').SB.Nonempty ∧ 0 < (D.XD j c c').vol) ∧
      ∀ j < m, ∀ c', ∃ c x, D.Xi j c c' x ≠ 0) ∧
    (∃ (C : ChIdx D.SG D.n m (D.ST ∪ D.SG) xi0 D.P.σ₀) (eβ : ∀ j, C.β j ≃ D.β j), ∀ j b, D.Λ j (eβ j b) = C.Λ j b) ∧
    (∃ (C : LiftChars τ m eF Sg) (ξ : Hecke E L), ∀ j < m, ∀ x, (D.mu j).toHom x = (C.mu j).toHom x * ξ.toHom x) ∧
    (∀ a, ∀ F ∈ X, HermForms.dOp a F ∈ X) ∧
    (∀ φ ψ, hV φ ψ = HermForms.pet D.ST (D.lam 0) (e φ).1 (e ψ).1) ∧
    MV = {φ | (e φ).1 ∈ HermForms.Mω D.ST τ χ0 (D.lam 0)} ∧
    (∀ (M : Submodule (𝓞 E) (Fin (D.n m) → E)) (b' : D.β m) (d' : points (E := E) (ST := D.ST) (D.Λ m b')),
      Lsh (d' : Deco E (D.n m) D.ST D.SG) = M → ∃ (b : D.β m) (d : points (E := E) (ST := D.ST) (D.Λ m b)),
        Lsh (d : Deco E (D.n m) D.ST D.SG) = M ∧ lift M = ⟨b, Quotient.mk'' d⟩) ∧
    ∀ φ, col φ = recast hm fun M => D.chain.comp m (D.inp _ (e φ).1) (lift M)

end Hook

-- CHAIN HOOK, closed: the canonical hook.
/-- **The theta hook**: `col μ ω` is the theta chain's (`IsThetaCol`) at every level `μ` and word `ω`, for a CM
structure on `E` and a CM type `τ`. -/
def thetaHook : ChainHook := fun Φ _ _ n E L _ _ _ T Ω Vs _ _ col =>
  ∃ (_ : IsCMField E) (_ : NumberField L) (_ : IsCMField L) (τ : Φ → (E →+* L)) (eF : ℕ → Φ → ℤ)
    (Sg : Set (HeightOneSpectrum (𝓞 E))), ∀ (μ : T) (ω : Ω),
      ∃ (hV : Vs ω → Vs ω → L) (MV : Set (Vs ω)), IsThetaCol τ eF Sg n hV MV (col μ ω)

/-- **The sharp frontier with the theta chain**: `SharpBound` at the canonical hook. -/
def SharpBoundTheta : Prop := SharpBound thetaHook

/-- **CONDITIONAL. RH and GRH from `SharpBoundTheta`** (on the half-plane `Re s > 11/12`). -/
theorem rhAndGRH_of_sharpBoundTheta (h : SharpBoundTheta) : HalfPlaneGRH.RHandGRH := rhAndGRH_of_sharpBound h

/-! ## The pinned frontier -/

/-- **The branching maps are pinned** at weights `λ`, `σ`: the rows' weight is `P.σ = σ`, and
`br ω = PeriodTarget.br τ tz Π_σ c_Br λ σ` with `c_Br ≠ 0` and `Π_σ` the Fock projection (`IsFockProj`). -/
def BrPinned {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E L : Type} [Field E] [NumberField E] [Field L]
    (τ : Φ → (E →+* L)) {T Ω : Type} {G X : T → Type} [∀ μ, Group (G μ)] [∀ μ, MulAction (G μ) (X μ)]
    {Vs : Ω → Type} [∀ ω, AddCommGroup (Vs ω)] [∀ ω, Module L (Vs ω)] (P : PeriodTarget.PerData Φ n E L G X Vs)
    (lam : Φ → Fin (n + 1) → ℤ) (σ : Φ → Fin n → ℤ) : Prop :=
  P.σ = σ ∧ ∀ ω, ∃ (Pr : Pol Φ n L →ₗ[L] Pol Φ n L) (cBr : L), cBr ≠ 0 ∧
    PeriodTarget.IsFockProj σ Pr ∧ P.br ω = PeriodTarget.br τ P.tz Pr cBr lam σ

section Pet

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ}
  {E : Type*} [Field E] [NumberField E] (τ : Φ → (E →+* K)) {T : Type*} {G X : T → Type*} [∀ μ, Group (G μ)]
  [∀ μ, MulAction (G μ) (X μ)]

open Classical in
/-- **Realised, with the source metrics pinned** (L4.3, L6.5): `KFrame.Realises`, and in the same coordinates `e ω`
as the lattices and the maps, the metric of `N_ω` at `v` is the Gram matrix of the hermitian form `hV ω` (in the
pinned frontier, the Petersson form `H_ω` of `X ⊓ V_ω`, `IsThetaCol`): `G_v(i, j) = σ_v(hV(e⁻¹δ_i, e⁻¹δ_j))`, as in
`HermForms.gram` and `HermForms.source_G`. -/
def KFrame.RealisesPet (F : KFrame K) {Vs : F.ι → Type*} [∀ ω, AddCommGroup (Vs ω)] [∀ ω, Module K (Vs ω)]
    [∀ ω, Module (𝓞 K) (Vs ω)] [∀ ω, IsScalarTower (𝓞 K) K (Vs ω)] (D : PeriodTarget.PerData Φ n E K G X Vs)
    (μ0 : T) (tw : PeriodTarget.Twist D μ0) (𝔞 : F.ι → Ideal (𝓞 K)) (M : ∀ ω, Submodule (𝓞 K) (Vs ω))
    (hV : ∀ ω, Vs ω → Vs ω → K) : Prop :=
  tw.IsTransfer ∧ (∀ w ∉ tw.Tw, tw.μw w = μ0) ∧ (∀ ω, 𝔞 ω ≠ ⊥) ∧
    ∃ (e : ∀ ω, Vs ω ≃ₗ[K] (F.n ω → K)) (eC : (D.V0 μ0 → K) →ₗ[K] (F.κ → K)), Set.InjOn eC (D.W μ0) ∧
      (∀ ω, (F.src ω).M =
        (PeriodTarget.Nsrc τ tw 𝔞 M ω).map (((e ω : Vs ω →ₗ[K] (F.n ω → K))).restrictScalars (𝓞 K))) ∧
      F.tgt.M = (PeriodTarget.Ctgt τ tw).map (eC.restrictScalars (𝓞 K)) ∧
      (∀ ω φ, eC (D.P μ0 ω φ) = F.B ω (e ω φ)) ∧
      ∀ ω v i j, (F.src ω).G v i j =
        v.1.embedding (hV ω ((e ω).symm (Pi.single i 1)) ((e ω).symm (Pi.single j 1)))

omit [NumberField E] in
/-- **Sanity:** realised with the metrics pinned is realised. -/
theorem KFrame.RealisesPet.realises {F : KFrame K} {Vs : F.ι → Type*} [∀ ω, AddCommGroup (Vs ω)]
    [∀ ω, Module K (Vs ω)] [∀ ω, Module (𝓞 K) (Vs ω)] [∀ ω, IsScalarTower (𝓞 K) K (Vs ω)]
    {D : PeriodTarget.PerData Φ n E K G X Vs} {μ0 : T} {tw : PeriodTarget.Twist D μ0} {𝔞 : F.ι → Ideal (𝓞 K)}
    {M : ∀ ω, Submodule (𝓞 K) (Vs ω)} {hV : ∀ ω, Vs ω → Vs ω → K} (h : F.RealisesPet τ D μ0 tw 𝔞 M hV) :
    F.Realises τ D μ0 tw 𝔞 M := by
  obtain ⟨h1, h2, h3, e, eC, h4, h5, h6, h7, -⟩ := h
  exact ⟨h1, h2, h3, e, eC, h4, h5, h6, h7⟩

end Pet

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

/-- A `Fin k`-indexed parameter read on `ℕ` (`0` from `k` on). -/
def finN {k : ℕ} (f : Fin k → ℤ) (j : ℕ) : ℤ := if h : j < k then f ⟨j, h⟩ else 0

/-- **The branching weight** of `u`: `σ = sgT(v, b, e)` of the HC parameters `hc u`, at rank `n = N_m − 1` (L6.1). -/
def SharpData.sgW (D : SharpData S κ x ε X K) (u : S.A) : Φ S.A → Fin (D.R.N D.R.m - 1) → ℤ :=
  PeriodTarget.sgT D.R.k D.R.t D.R.m (fun ρ => finN (D.hc u ρ).v) (fun ρ => finN (D.hc u ρ).b)
    (fun ρ => finN (D.hc u ρ).e)

theorem SharpData.N_sub_one_add_one (D : SharpData S κ x ε X K) :
    D.R.N D.R.m - 1 + 1 = D.R.k + D.R.m * (D.R.t + 1) := by
  have := D.R.m_add_three_le
  unfold Setting.Ranks.N
  omega

/-- The weights `e_j` of `hc u`, for the lift characters (`LiftChars`). -/
def SharpData.eW (D : SharpData S κ x ε X K) (u : S.A) : ℕ → Φ S.A → ℤ := fun j ρ => finN (D.hc u ρ).e j

/-- The places of `E` above `g₀g₁`, where the lift characters may ramify (tamely). -/
def SharpData.Sg (D : SharpData S κ x ε X K) : Set (HeightOneSpectrum (𝓞 S.E)) :=
  {v | ((D.g₀ * D.g₁ : ℕ) : 𝓞 S.E) ∈ v.asIdeal}

/-- **The weight `λ_m`** of `u` (`WeylFock.wt` at `j = m`, with `u_i − ½` and `e_j` of `hc u`), read at rank
`N_m = (N_m − 1) + 1`. -/
def SharpData.lamW (D : SharpData S κ x ε X K) (u : S.A) : Φ S.A → Fin (D.R.N D.R.m - 1 + 1) → ℤ := fun ρ i =>
  WeylFock.wt D.R.k D.R.t D.R.m (fun ρ i => ⌊(D.hc u ρ).u i - 1 / 2⌋) (fun ρ => finN (D.hc u ρ).e) ρ
    (Fin.cast D.N_sub_one_add_one i)

/-- **The arithmetic of the parameters** (L7.2): `(−d/g₀) = (−d/g₁) = 1`, and `T_ω = ππ̄` with
`π = (a + b√−d)/2 ≡ 1 (mod M)`, `M = QS·q·d·(g₀g₁)²`: `4T_ω = a² + db²`, `M ∣ b`, `a ≡ b + 2 (mod 2M)`. -/
def SharpData.Arith (D : SharpData S κ x ε X K) : Prop :=
  jacobiSym (-(S.d : ℤ)) D.g₀ = 1 ∧ jacobiSym (-(S.d : ℤ)) D.g₁ = 1 ∧
    ∀ u ω, ∃ a b : ℤ, 4 * (D.T u ω : ℤ) = a ^ 2 + S.d * b ^ 2 ∧
      ((S.QS * S.q * S.d * (D.g₀ * D.g₁) ^ 2 : ℕ) : ℤ) ∣ b ∧
      a ≡ b + 2 [ZMOD 2 * ((S.QS * S.q * S.d * (D.g₀ * D.g₁) ^ 2 : ℕ) : ℤ)]

/-- **Realised, pinned**: `SharpData.Realised thetaHook` over a CM field `K`, with the chain's CM type equal to `τ_K`,
the branching maps pinned (`BrPinned`) at `λ = λ_m` (`lamW`) and `σ = sgT` (`sgW`) of `hc u`, the source lattices
`M_ω` the `O_K`-span of the integral forms `HermForms.Mω` of `X ⊓ V_ω` and the source metrics the Petersson form
`H_ω` (both through the `IsThetaCol` isomorphism at `μ0`; metrics through `e ω` by `KFrame.RealisesPet`), and nonzero
row spaces at the twisted levels. -/
def SharpData.RealisedPinned (D : SharpData S κ x ε X K) : Prop :=
  ∃ (_ : IsCMField K) (τK : Φ S.A → (S.E →+* K)) (j : K →+* ℂ), (∀ ρ, j.comp (τK ρ) = S.τ ρ) ∧
    ∀ u ∈ A₀ κ, ∃ (T : Type) (G X : T → Type) (_ : ∀ μ, Group (G μ)) (_ : ∀ μ, MulAction (G μ) (X μ))
      (Vs : (D.fr u).ι → Type) (_ : ∀ ω, AddCommGroup (Vs ω)) (_ : ∀ ω, Module K (Vs ω))
      (_ : ∀ ω, Module (𝓞 K) (Vs ω)) (_ : ∀ ω, IsScalarTower (𝓞 K) K (Vs ω))
      (P : PeriodTarget.PerData (Φ S.A) (D.R.N D.R.m - 1) S.E K G X Vs) (μ0 : T) (tw : PeriodTarget.Twist P μ0)
      (𝔞 : (D.fr u).ι → Ideal (𝓞 K)) (M : ∀ ω, Submodule (𝓞 K) (Vs ω)) (hV : T → ∀ ω, Vs ω → Vs ω → K)
      (MV : T → ∀ ω, Set (Vs ω)),
      (∀ μ ω, IsThetaCol τK (D.eW u) D.Sg (D.R.N D.R.m - 1) (hV μ ω) (MV μ ω) (P.col μ ω)) ∧
        BrPinned τK P (D.lamW u) (D.sgW u) ∧ (∀ ω, M ω = Submodule.span (𝓞 K) (MV μ0 ω)) ∧
        (∀ w ∈ tw.Tw, P.V0 (tw.μw w) ≠ ⊥) ∧ (D.fr u).RealisesPet τK P μ0 tw 𝔞 M (hV μ0)

/-- Pinned realisation gives realisation with the theta hook. -/
theorem SharpData.RealisedPinned.realised {D : SharpData S κ x ε X K} (h : D.RealisedPinned) :
    D.Realised thetaHook := by
  obtain ⟨_, τK, j, hj, hu⟩ := h
  refine ⟨τK, j, hj, fun u hu' => ?_⟩
  obtain ⟨T, G, X, i1, i2, Vs, i3, i4, i5, i6, P, μ0, tw, 𝔞, M, hV, MV, hc, -, -, -, hR⟩ := hu u hu'
  exact ⟨T, G, X, i1, i2, Vs, i3, i4, i5, i6, P, μ0, tw, 𝔞, M,
    ⟨inferInstance, inferInstance, inferInstance, τK, _, _, fun μ ω => ⟨_, _, hc μ ω⟩⟩, hR.realises τK⟩

/-- **The pinned sharp frontier**: `SharpBoundTheta`'s shape, with pinned realisation (`τ_K` in the chain, `br`
pinned) and the arithmetic of the parameters (`SharpData.Arith`). -/
def SharpBoundPinned : Prop :=
  ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → ∀ ε₀ > 0, ∃ ε, 0 < ε ∧ ε < ε₀ ∧
    ∃ A ≥ (1 : ℝ), ∀ᶠ Y in Filter.atTop, ∀ q d, ZetaTwist.WinPair ε Y q d →
      ∃ Y' ∈ Set.Icc Y (Y ^ (A / 2)), ∀ x ∈ Set.Icc Y' (Y' ^ 2), ∃ (S : Setting) (κ : S.A →* ℂˣ), S.q = q ∧
        S.d = d ∧ S.d % 4 = 3 ∧ S.Lifts κ χ ∧ ∃ (K : Type) (_ : Field K) (_ : NumberField K)
          (_ : IsTotallyComplex K) (D : SharpData S κ x ε (((S.N : ℝ) * x) ^ Real.log x) K),
            D.RealisedPinned ∧ D.Arith

/-- The pinned frontier implies `SharpBoundTheta`. -/
theorem sharpBoundTheta_of_pinned (h : SharpBoundPinned) : SharpBoundTheta := by
  intro f _ χ hχ ε₀ hε₀
  obtain ⟨ε, hε, hεε₀, A, hA, hY⟩ := h f χ hχ ε₀ hε₀
  refine ⟨ε, hε, hεε₀, A, hA, hY.mono fun Y hY q d hp => ?_⟩
  obtain ⟨Y', hY', hx⟩ := hY q d hp
  refine ⟨Y', hY', fun x hx' => ?_⟩
  obtain ⟨S, κ, hq, hd, hd4, hL, K, _, _, _, D, hD, -⟩ := hx x hx'
  exact ⟨S, κ, hq, hd, hd4, hL, K, _, _, _, D, hD.realised⟩

/-- **CONDITIONAL. RH and GRH from the pinned frontier** (on the half-plane `Re s > 11/12`). -/
theorem rhAndGRH_of_sharpBoundPinned (h : SharpBoundPinned) : HalfPlaneGRH.RHandGRH :=
  rhAndGRH_of_sharpBoundTheta (sharpBoundTheta_of_pinned h)

end

end ZetaBalance
