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
  `β j` finite, `Λ 0 = uniUT`. Against `κ ≡ 0`: `S = ST ∪ SG` (the archive's place set of `homAt`), `cA, cB > 0`,
  the Heisenberg data have `SA, SB ≠ ∅` and `vol > 0`, and every class at a level `j + 1 ≤ m` meets a nonzero `Ξ`.

**The pinned frontier** (`SharpBoundPinned`) adds what the hook cannot see: the chain's CM type is `τ_K`, the
branching maps are `PeriodTarget.br` with `c_Br ≠ 0` and `IsFockProj` (`BrPinned`), `(−d/g₀) = (−d/g₁) = 1`, and
`T_ω = ππ̄` with `π = (a + b√−d)/2 ≡ 1 (mod M)`, `M = QS·q·d·(g₀g₁)²` (`SharpData.Arith`; for `d ≡ 3 (mod 4)`,
`π − 1 ∈ M·O_{K₀}` iff `M ∣ b` and `a ≡ b + 2 (mod 2M)`). It implies `SharpBoundTheta`.

**Open.** Existential: `Data`'s remaining fields (theta constants, `Ξ`, weights, characters, `dI`), `xi0`, `lift`,
`X`, `e` (one per level and word), the branching projection and weight. Not stated: `Tw` closed under conjugation
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

/-- **`col` is the theta chain's** at one level and word: `col φ = recast (Θ_m(inp(e φ)) ∘ lift)` for theta data
`D` with `ChIdx`'s conditions and the anti-degeneracy conditions, a cusp subspace `X`, an isomorphism `e` of the
source with `X ⊓ V_ω`, and a lift of lattices to classes with the spec's property (module docstring, (a)–(d)). -/
def IsThetaCol (τ : Φ → (E →+* L)) (n : ℕ) {V : Type} [AddCommGroup V] [Module L V]
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
    (∀ a, ∀ F ∈ X, HermForms.dOp a F ∈ X) ∧
    (∀ (M : Submodule (𝓞 E) (Fin (D.n m) → E)) (b' : D.β m) (d' : points (E := E) (ST := D.ST) (D.Λ m b')),
      Lsh (d' : Deco E (D.n m) D.ST D.SG) = M → ∃ (b : D.β m) (d : points (E := E) (ST := D.ST) (D.Λ m b)),
        Lsh (d : Deco E (D.n m) D.ST D.SG) = M ∧ lift M = ⟨b, Quotient.mk'' d⟩) ∧
    ∀ φ, col φ = recast hm fun M => D.chain.comp m (D.inp _ (e φ).1) (lift M)

end Hook

-- CHAIN HOOK, closed: the canonical hook.
/-- **The theta hook**: `col μ ω` is the theta chain's (`IsThetaCol`) at every level `μ` and word `ω`, for a CM
structure on `E` and a CM type `τ`. -/
def thetaHook : ChainHook := fun Φ _ _ n E L _ _ _ T Ω _ _ _ col =>
  ∃ (_ : IsCMField E) (_ : NumberField L) (τ : Φ → (E →+* L)), ∀ (μ : T) (ω : Ω), IsThetaCol τ n (col μ ω)

/-- **The sharp frontier with the theta chain**: `SharpBound` at the canonical hook. -/
def SharpBoundTheta : Prop := SharpBound thetaHook

/-- **CONDITIONAL. RH and GRH from `SharpBoundTheta`** (on the half-plane `Re s > 11/12`). -/
theorem rhAndGRH_of_sharpBoundTheta (h : SharpBoundTheta) : HalfPlaneGRH.RHandGRH := rhAndGRH_of_sharpBound h

/-! ## The pinned frontier -/

/-- **The branching maps are pinned**: `br ω = PeriodTarget.br τ tz Π_σ c_Br λ σ` with `c_Br ≠ 0` and `Π_σ` the
Fock projection (`IsFockProj`); `λ = λ_m(ω)` is left existential. -/
def BrPinned {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E L : Type} [Field E] [NumberField E] [Field L]
    (τ : Φ → (E →+* L)) {T Ω : Type} {G X : T → Type} [∀ μ, Group (G μ)] [∀ μ, MulAction (G μ) (X μ)]
    {Vs : Ω → Type} [∀ ω, AddCommGroup (Vs ω)] [∀ ω, Module L (Vs ω)] (P : PeriodTarget.PerData Φ n E L G X Vs) :
    Prop :=
  ∀ ω, ∃ (Pr : Pol Φ n L →ₗ[L] Pol Φ n L) (cBr : L) (lam : Φ → Fin (n + 1) → ℤ), cBr ≠ 0 ∧
    PeriodTarget.IsFockProj P.σ Pr ∧ P.br ω = PeriodTarget.br τ P.tz Pr cBr lam P.σ

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

/-- **The arithmetic of the parameters** (L7.2): `(−d/g₀) = (−d/g₁) = 1`, and `T_ω = ππ̄` with
`π = (a + b√−d)/2 ≡ 1 (mod M)`, `M = QS·q·d·(g₀g₁)²`: `4T_ω = a² + db²`, `M ∣ b`, `a ≡ b + 2 (mod 2M)`. -/
def SharpData.Arith (D : SharpData S κ x ε X K) : Prop :=
  jacobiSym (-(S.d : ℤ)) D.g₀ = 1 ∧ jacobiSym (-(S.d : ℤ)) D.g₁ = 1 ∧
    ∀ u ω, ∃ a b : ℤ, 4 * (D.T u ω : ℤ) = a ^ 2 + S.d * b ^ 2 ∧
      ((S.QS * S.q * S.d * (D.g₀ * D.g₁) ^ 2 : ℕ) : ℤ) ∣ b ∧
      a ≡ b + 2 [ZMOD 2 * ((S.QS * S.q * S.d * (D.g₀ * D.g₁) ^ 2 : ℕ) : ℤ)]

/-- **Realised, pinned**: `SharpData.Realised thetaHook` with the chain's CM type equal to `τ_K` and the branching
maps pinned (`BrPinned`). -/
def SharpData.RealisedPinned (D : SharpData S κ x ε X K) : Prop :=
  ∃ (τK : Φ S.A → (S.E →+* K)) (j : K →+* ℂ), (∀ ρ, j.comp (τK ρ) = S.τ ρ) ∧
    ∀ u ∈ A₀ κ, ∃ (T : Type) (G X : T → Type) (_ : ∀ μ, Group (G μ)) (_ : ∀ μ, MulAction (G μ) (X μ))
      (Vs : (D.fr u).ι → Type) (_ : ∀ ω, AddCommGroup (Vs ω)) (_ : ∀ ω, Module K (Vs ω))
      (_ : ∀ ω, Module (𝓞 K) (Vs ω)) (_ : ∀ ω, IsScalarTower (𝓞 K) K (Vs ω))
      (P : PeriodTarget.PerData (Φ S.A) (D.R.N D.R.m - 1) S.E K G X Vs) (μ0 : T) (tw : PeriodTarget.Twist P μ0)
      (𝔞 : (D.fr u).ι → Ideal (𝓞 K)) (M : ∀ ω, Submodule (𝓞 K) (Vs ω)),
      (∀ μ ω, IsThetaCol τK (D.R.N D.R.m - 1) (P.col μ ω)) ∧ BrPinned τK P ∧ (D.fr u).Realises τK P μ0 tw 𝔞 M

/-- Pinned realisation gives realisation with the theta hook. -/
theorem SharpData.RealisedPinned.realised {D : SharpData S κ x ε X K} (h : D.RealisedPinned) :
    D.Realised thetaHook := by
  obtain ⟨τK, j, hj, hu⟩ := h
  refine ⟨τK, j, hj, fun u hu' => ?_⟩
  obtain ⟨T, G, X, i1, i2, Vs, i3, i4, i5, i6, P, μ0, tw, 𝔞, M, hc, -, hR⟩ := hu u hu'
  exact ⟨T, G, X, i1, i2, Vs, i3, i4, i5, i6, P, μ0, tw, 𝔞, M, ⟨inferInstance, inferInstance, τK, hc⟩, hR⟩

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
