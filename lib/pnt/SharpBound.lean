import SixTerm
import KLattice
import FrameRescale
import CMHost
import ForcedOrders
import PeriodTarget

/-!
# The sharp frontier `SharpBound` and its bridge to `SixTermData` — CONDITIONAL on the half-plane

Layer L7 of the sharp frontier (`docs/rh-rebuild.md`; spec L7.1, L7.2, L7.5, L7.6): the frontier, stated with the
objects of the layers below, and its bridge to the six-term interface `SixTermData`.

**The objects.** At each translate `u`, a hermitian frame of `O_K`-lattices (`KFrame`): sources `N_ω` with their
metrics, a target `C_u` of positive rank (`W_u ≠ 0`) with its metric `g_u`, and `K`-linear maps `B_ω`. Its slope
frame is `KLattice.frame`, rescaled to the archive's units by `c = −log 2 + log|d_K|/[K:ℚ]` (`KFrame.frame`,
`Frame.rescale`). `KFrame.Realises` says that the frame is, in coordinates, the defined objects of L6: `N_ω = Nsrc`,
`C_u = Ctgt`, `B_ω = P_{μ0}`, with transfers, `μ(w) = μ0` off `Tw` and the fractional `𝔞_ω = 𝔞⁺(𝔞⁻)⁻¹` nonzero
(`𝔞⁺, 𝔞⁻ ≠ 0`).

**Sharp data** (`SharpData`, L7.5): weights, the parameters of the forced orders (ranks, Harish-Chandra families with
`w_{u,j} = e_j`, split primes `g₀ ≠ g₁`), and per translate a frame, auxiliary primes `T_ω`, the constants of the frame
condition and slacks `c↓, c↑, c_T ≥ 0`, meeting (T), (G↓), (G↑), (S), (R) and (Z). `Fo := ForcedOrders.Fo` at the
cut-off `X″ = x·|A|·exp(x^{ε/3})` (`Setting.cutX`, L7.1), with the twist `Setting.twA κ` of the archive's Artin map
for odd `χ` (verify-A F1; `ForcedOrders`, "The twist `c`"), is fixed, `v = v_E` and `lg = log(g₀g₁)`. (R) is stated with
`SlopeLe`/`SlopeGe` at the rank-weighted mean (FrameRescale: `muMax`/`muMin` need a bound).

**The bridge** (`SharpData.toSixTermData`, L7.6): `Ga = ΣΣASK`, `Ee = m·(Σ_t a_t)·lg`, `μM = μ(N_ω) − Ga − Fo + Ee`,
`c₁ = c₅ = c₆ = 0`; G1, G5, G6 hold with equality, G2 is (G↓), G3 is (G↑), G4 is (T). `spread` comes from (S) through
`KLattice.spread_of_frameCond` and from (R); `sizes` is (Z).

**The frontier** (`SharpBound`): `SixTermBound`'s outer shape, with `d ≡ 3 (mod 4)` (needed for `CMHost`'s `E`, `τ`
and classes to be the archive's) and realised sharp data over a totally complex coefficient field `K`, with a CM type
`τ_K` lifting `Setting.τ`. `rhAndGRH_of_sharpBound` goes through `rhAndGRH_of_sixTermBound`.

**Choices and open hooks.**
* `δ = 0` in (S): the target lattice spans `K^κ`, so no padding; `α = η + 2√e/(1 − √e)`, `β = 2/(1 − √e)`.
* **The chain** enters at one point, `ChainHook`, a predicate on the `col` of the period data (CHAIN HOOK below).
* The source spaces `V_ω` of `KFrame.Realises` are generic; the frontier means `X ⊓ HermForms.Vω` for a cusp subspace
  `X` stable under the diamond operators (L7 notes, item 3). `Tw` closed under conjugation is not yet stated.

**Sanity theorems:** `SharpData.nonempty_sixTermData`, `SharpData.toSixTermData_Fo`.

**CONDITIONAL.** `rhAndGRH_of_sharpBound` rests on the half-plane `Re s > 11/12`, as `rhAndGRH_of_sixTermBound` does.
-/

open NumberField DirichletCharacter SlopeFrame HermitianLattice

namespace ZetaBalance

/-! ## Units and scales (L7.1, L7.3) -/

/-- The shift `c = −log 2 + log|d_K|/[K:ℚ]` from the library's slopes to the archive's: `μ_arch = 2μ + c`
(`KLattice`, "The factor 2"). -/
noncomputable def archShift (K : Type) [Field K] [NumberField K] : ℝ :=
  -Real.log 2 + Real.log |(discr K : ℝ)| / Module.finrank ℚ K

/-- The cut-off `X″ = a/w″ = x·|A|·X′` of the inert places, with `X′ = exp(x^{ε/3})` (L7.1). -/
noncomputable def Setting.cutX (S : Setting) (x ε : ℝ) : ℝ :=
  x * Fintype.card S.A * Real.exp (x ^ (ε / 3))

/-- `v_E > 0`. -/
theorem Setting.vE_pos (S : Setting) : 0 < S.vE := by
  unfold Setting.vE
  have : (discr S.E : ℝ) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero S.E)
  positivity

/-! ## Hermitian frames of `O_K`-lattices -/

/-- **A hermitian frame of `O_K`-lattices** (L7.6): sources `X ω` (with their metrics, the Petersson metric in the
frontier), one target `Y` (with its metric `g_u`) of positive rank, and `K`-linear maps `B ω` with `B ω (M_ω) ⊆ M_Y`,
bounded by `e^{ht ω v}` on the part at each complex place `v`. -/
structure KFrame (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] where
  /-- The words. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The coordinates of the source of a word. -/
  n : ι → Type
  [fintypeN : ∀ ω, Fintype (n ω)]
  /-- The coordinates of the target. -/
  κ : Type
  [fintypeκ : Fintype κ]
  /-- The target is not zero (`W_u ≠ 0`, spec-2 item 3). -/
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
  ht : ι → Pl K → ℝ
  /-- The maps are bounded by `e^{ht ω v}` on the part at `v`. -/
  hφ : ∀ ω v, ∀ y ∈ (KLattice.part v : Submodule ℂ (KLattice.Space K (n ω))),
    ‖(src ω).hom tgt (B ω) y‖ ≤ Real.exp (ht ω v) * ‖y‖

attribute [instance] KFrame.fintype KFrame.fintypeN KFrame.fintypeκ KFrame.nonempty

namespace KFrame

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (F : KFrame K)

/-- The slope frame of a hermitian frame, in the archive's units (`Frame.rescale` by `archShift K`). -/
noncomputable def frame : Frame :=
  (KLattice.frame F.tgt F.src F.B F.hB F.ht F.hφ).rescale (archShift K)

/-- The component of `B_ω` at a complex place `v`, a `ℂ`-linear map between the parts at `v`. -/
noncomputable def comp (ω : F.ι) (v : Pl K) :=
  component ((F.src ω).hom_act F.tgt (F.B ω)) v

/-- **Rank spreading from the frame condition** at one place, for the rescaled frame: rescaling keeps ranks and
images (`KLattice.spread_of_frameCond`). -/
theorem rankSpread (v : Pl K) (c : F.ι → ℝ) {e η : ℝ}
    (hc : FrameAtPlace.FrameCond (fun ω => c ω • F.comp ω v) e η) :
    F.frame.RankSpread (η + 2 * √e / (1 - √e)) (2 / (1 - √e)) :=
  KLattice.spread_of_frameCond F.tgt F.src F.B F.hB F.ht F.hφ v c hc

end KFrame

/-! ## Sharp data (L7.5) -/

/-- **Sharp data at `x`** (spec L7.5): weights for the kernel `A₀` of `κ`, the parameters that fix the forced orders
(ranks `R`, Harish-Chandra families `hc u` with `w_{u,j} = e_j`, split primes `g₀ ≠ g₁`), and at each translate `u` a
hermitian frame of `O_K`-lattices (sources `N_ω`, target `C_u`, maps `B_ω`), auxiliary primes `T_ω`, the constants of
the frame condition and three nonnegative slacks, meeting (T), (G↓), (G↑), (S), (R) and (Z). All slopes and heights
are in the archive's units (`KFrame.frame`); `Fo := ForcedOrders.Fo` (twisted by `twA κ`) is fixed, `v := v_E` and
`lg = log(g₀g₁)`. -/
structure SharpData (S : Setting) (κ : S.A →* ℂˣ) (x ε X : ℝ) (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] extends Weights S κ x ε X where
  /-- The ranks `(k, m, t)`. -/
  R : S.Ranks
  /-- The number of weights is the rank `m`. -/
  hm : m = R.m
  /-- The Harish-Chandra family of each translate. -/
  hc : S.A → R.HCFamily
  /-- The weights are the parameters `e_j`: `w_{u,j}(ρ) = e_j(τ_ρ)`. -/
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
  /-- The hermitian frame of each translate. -/
  fr : S.A → KFrame K
  /-- The auxiliary prime `T_ω` of each word. -/
  T : ∀ u, (fr u).ι → ℕ
  /-- The auxiliary primes are prime. -/
  T_prime : ∀ u ω, (T u ω).Prime
  /-- The complex place `v` of the frame condition. -/
  pl : S.A → Pl K
  /-- The scalars `c_ω > 0` of the frame condition. -/
  cω : ∀ u, (fr u).ι → ℝ
  /-- The constant `e` of the frame condition. -/
  e : S.A → ℝ
  /-- The constant `η` of the frame condition. -/
  η : S.A → ℝ
  /-- The ranges `U_u`. -/
  U : S.A → ℝ
  /-- The depths `H_u`. -/
  H : S.A → ℝ
  /-- The slack `c↓` of (G↓). -/
  cDn : S.A → ℝ
  /-- The slack `c↑` of (G↑). -/
  cUp : S.A → ℝ
  /-- The slack `c_T` of (T). -/
  cT : S.A → ℝ
  /-- `c_ω > 0`. -/
  cω_pos : ∀ u ω, 0 < cω u ω
  /-- `0 ≤ e`. -/
  e_nonneg : ∀ u, 0 ≤ e u
  /-- `U > 0`. -/
  U_pos : ∀ u ∈ A₀ κ, 0 < U u
  /-- `H ≥ 0`. -/
  H_nonneg : ∀ u ∈ A₀ κ, 0 ≤ H u
  /-- `c↓ ≥ 0`. -/
  cDn_nonneg : ∀ u, 0 ≤ cDn u
  /-- `c↑ ≥ 0`. -/
  cUp_nonneg : ∀ u, 0 ≤ cUp u
  /-- `c_T ≥ 0`. -/
  cT_nonneg : ∀ u, 0 ≤ cT u
  /-- **(T)**: `log T_ω ≥ Λ_u − c_T`. -/
  hT : ∀ u ∈ A₀ κ, ∀ ω, S.lam (w u) S.vE (Real.log (g₀ * g₁)) - cT u ≤ Real.log (T u ω)
  /-- **(G↓)**: `μ(N_ω) ≥ Σ_t Σ_j ASK(a_t, t, w_{u,j}) − m(Σ_t a_t)·lg + Fo(𝒫_u) − c↓`. -/
  hGdn : ∀ u ∈ A₀ κ, ∀ ω, ∑ t ∈ TT, ∑ j, S.ASK (a t) t (w u j) - m * (∑ t ∈ TT, a t) * Real.log (g₀ * g₁) +
    R.Fo (hc u) (S.twA κ) g₀ g₁ (S.cutX x ε) - cDn u ≤ ((fr u).frame.N ω).deg ⊤ / ((fr u).frame.N ω).rk ⊤
  /-- **(G↑)**: `μ_g(C_u) + h_g(B_ω) − Fo(𝒫_u) ≤ MAIN_ω + c↑`. -/
  hGup : ∀ u ∈ A₀ κ, ∀ ω, (fr u).frame.C.deg ⊤ / (fr u).frame.C.rk ⊤ + (fr u).frame.h ω -
    R.Fo (hc u) (S.twA κ) g₀ g₁ (S.cutX x ε) ≤ S.mainW TT m a S.vE (T u ω) + cUp u
  /-- **(S)**: the frame condition at `v` for the `c_ω·B_ω`, with constants `e` and `η` (the target spans, so no
  padding: `δ = 0`). -/
  hS : ∀ u ∈ A₀ κ, FrameAtPlace.FrameCond (fun ω => cω u ω • (fr u).comp ω (pl u)) (e u) (η u)
  /-- **(R)**: the ranks of the words add up to a positive number. -/
  rk_pos : ∀ u ∈ A₀ κ, 0 < ∑ ω, (((fr u).frame.N ω).rk ⊤ : ℝ)
  /-- **(R)**: `μ_max(N_ω) − h_ω ≤ s_u + U`, with `s_u` the rank-weighted mean of `μ(N_ω) − h_ω`. -/
  range : ∀ u ∈ A₀ κ, ∀ ω, ((fr u).frame.N ω).SlopeLe ((fr u).frame.mean + U u + (fr u).frame.h ω)
  /-- **(R)**: `μ_min(C_u) ≥ s_u − H`. -/
  depth : ∀ u ∈ A₀ κ, (fr u).frame.C.SlopeGe ⊤ ((fr u).frame.mean - H u)
  /-- **(Z)**: `Σ_u [c↓ + c↑ + (Σ_t a_t)c_T + αH + βU log(1 + H/U)] ≤ |A₀|·x^{4ε}·Σ_t a_t`, with
  `α = η + 2√e/(1 − √e)` and `β = 2/(1 − √e)`. -/
  sizes : ∑ u ∈ A₀ κ, (cDn u + cUp u + (∑ t ∈ TT, a t) * cT u +
    ((η u + 2 * √(e u) / (1 - √(e u))) * H u + 2 / (1 - √(e u)) * U u * Real.log (1 + H u / U u))) ≤
      (A₀ κ).card * x ^ (4 * ε) * ∑ t ∈ TT, a t

namespace SharpData

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  (D : SharpData S κ x ε X K)

/-- The forced orders of a translate, `Fo(𝒫_u) = ForcedOrders.Fo`, in the archive's units. -/
noncomputable def Fo (u : S.A) : ℝ := D.R.Fo (D.hc u) (S.twA κ) D.g₀ D.g₁ (S.cutX x ε)

/-- `lg = log(g₀g₁)`. -/
noncomputable def lg : ℝ := Real.log (D.g₀ * D.g₁)

/-- The vanishing gain `Ga_u = Σ_t Σ_j ASK(a_t, t, w_{u,j})`. -/
noncomputable def Ga (u : S.A) : ℝ := ∑ t ∈ D.TT, ∑ j, S.ASK (D.a t) t (D.w u j)

/-- The split primes `Ee = m·(Σ_t a_t)·lg`. -/
noncomputable def Ee : ℝ := D.m * (∑ t ∈ D.TT, D.a t) * D.lg

/-- **The rank-spreading hypotheses** at the rank-weighted mean slope, from (S) and (R). -/
theorem spread {u : S.A} (hu : u ∈ A₀ κ) :
    (D.fr u).frame.Spread (D.fr u).frame.mean (D.U u) (D.H u) (D.η u + 2 * √(D.e u) / (1 - √(D.e u)))
      (2 / (1 - √(D.e u))) where
  U_pos := D.U_pos u hu
  H_nonneg := D.H_nonneg u hu
  β_nonneg := div_nonneg zero_le_two (sub_nonneg.2 (Real.sqrt_le_one.2 (D.hS u hu).e_lt_one.le))
  mean := by rw [Frame.mean, div_mul_cancel₀ _ (D.rk_pos u hu).ne']
  range := D.range u hu
  depth := D.depth u hu
  spread := (D.fr u).rankSpread (D.pl u) (D.cω u) (D.hS u hu)

/-- **The bridge** (spec L7.6): sharp data are six-term data, with the rescaled hermitian frames, `Ga = ΣΣASK`,
`Ee = m·(Σ_t a_t)·lg`, `μM = μ(N_ω) − Ga − Fo + Ee`, `v = v_E`, slacks `c₂ = c↓`, `c₃ = c↑`, `c₄ = c_T` and
`c₁ = c₅ = c₆ = 0`. G1, G5 and G6 hold with equality, G2 is (G↓), G3 is (G↑) and G4 is (T). -/
noncomputable def toSixTermData : SixTermData S κ x ε X where
  toWeights := D.toWeights
  frame u := (D.fr u).frame
  U := D.U
  H := D.H
  α u := D.η u + 2 * √(D.e u) / (1 - √(D.e u))
  β u := 2 / (1 - √(D.e u))
  μM u ω := ((D.fr u).frame.N ω).deg ⊤ / ((D.fr u).frame.N ω).rk ⊤ - D.Ga u - D.Fo u + D.Ee
  Ee _ _ := D.Ee
  T u ω := D.T u ω
  Ga := D.Ga
  Fo := D.Fo
  v _ := S.vE
  lg _ := D.lg
  c₁ _ := 0
  c₂ := D.cDn
  c₃ := D.cUp
  c₄ := D.cT
  c₅ _ := 0
  c₆ _ := 0
  rk_pos := D.rk_pos
  spread _ hu := D.spread hu
  v_pos _ _ := S.vE_pos
  G1 _ _ _ := by linarith
  G2 u hu ω := by have := D.hGdn u hu ω; simp only [Ga, Fo, Ee, lg] at *; linarith
  G3 u hu ω := D.hGup u hu ω
  G4 u hu ω := D.hT u hu ω
  G5 _ _ _ := by simp [Ee, lg]
  G6 _ _ := by simp [Ga]
  sizes := by simpa using D.sizes

/-- **Sanity:** the bridge, as a theorem: sharp data give six-term data. -/
theorem nonempty_sixTermData (h : Nonempty (SharpData S κ x ε X K)) : Nonempty (SixTermData S κ x ε X) :=
  h.map toSixTermData

/-- **Sanity:** the bridge keeps the forced orders of the parameters, `Fo = ForcedOrders.Fo`. -/
theorem toSixTermData_Fo (u : S.A) : D.toSixTermData.Fo u = D.R.Fo (D.hc u) (S.twA κ) D.g₀ D.g₁ (S.cutX x ε) :=
  rfl

end SharpData

/-! ## Realisation by the defined objects (L6, L7.6) -/

section Realise

open PeriodTarget IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {Φ : Type*} [Fintype Φ] [DecidableEq Φ]
  {n : ℕ} {E : Type*} [Field E] [NumberField E] (τ : Φ → (E →+* K)) {T : Type*} {G X : T → Type*}
  [∀ μ, Group (G μ)] [∀ μ, MulAction (G μ) (X μ)]

/-- **A hermitian frame realises the period data** (L6.3–L6.5): in coordinates `e ω` of the source spaces and a
linear map `eC` injective on `W_u`, the sources are `N_ω = {φ ∈ 𝔞_ω⁻¹M_ω : B_ωφ ∈ C_u}` (`PeriodTarget.Nsrc`, with
the fractional `𝔞_ω = 𝔞⁺(𝔞⁻)⁻¹`, `𝔞⁺ = 𝔞p ω`, `𝔞⁻ = 𝔞n ω`), the target is `C_u` (`PeriodTarget.Ctgt`) and the maps
are the period maps `B_ω = P_{μ0}(col ·)` (`PerData.P`). The twist data are transfers (`Twist.IsTransfer`),
`μ(w) = μ0` off `Tw`, and `𝔞⁺, 𝔞⁻ ≠ 0`. -/
def KFrame.Realises (F : KFrame K) {Vs : F.ι → Type*} [∀ ω, AddCommGroup (Vs ω)] [∀ ω, Module K (Vs ω)]
    [∀ ω, Module (𝓞 K) (Vs ω)] [∀ ω, IsScalarTower (𝓞 K) K (Vs ω)] (D : PerData Φ n E K G X Vs) (μ0 : T)
    (tw : Twist D μ0) (𝔞p 𝔞n : F.ι → Ideal (𝓞 K)) (M : ∀ ω, Submodule (𝓞 K) (Vs ω)) : Prop :=
  tw.IsTransfer ∧ (∀ w ∉ tw.Tw, tw.μw w = μ0) ∧ (∀ ω, 𝔞p ω ≠ ⊥ ∧ 𝔞n ω ≠ ⊥) ∧
    ∃ (e : ∀ ω, Vs ω ≃ₗ[K] (F.n ω → K)) (eC : (D.V0 μ0 → K) →ₗ[K] (F.κ → K)), Set.InjOn eC (D.W μ0) ∧
      (∀ ω, (F.src ω).M =
        (Nsrc τ tw 𝔞p 𝔞n M ω).map (((e ω : Vs ω →ₗ[K] (F.n ω → K))).restrictScalars (𝓞 K))) ∧
      F.tgt.M = (Ctgt τ tw).map (eC.restrictScalars (𝓞 K)) ∧ ∀ ω φ, eC (D.P μ0 ω φ) = F.B ω (e ω φ)

end Realise

/-! ## The frontier (L7.5) -/

-- CHAIN HOOK: the chain enters here, and only here. `ThetaChain.Data.chain` runs on the classes `Σ_b DCl`, while
-- `PerData.col` is a function on the row points `X μ` of each level (rank `n`, values of rank `n + 1`) of
-- `V_ω`-linear outputs; the reading (the top step to the points, the forms-to-classes input) is a predicate on the
-- `col` of the period data.
/-- **The chain hook**: which `col` of the period data (`PeriodTarget.PerData.col`) count as the theta chain's
output on the points `X μ` of each level. The frontier is meant for `X μ` the decorated row points of rank `N_m − 1`
and `col_μ` the top step of the theta chain of tuple `μ`, from its last classes to each point (`SharpChain`). -/
abbrev ChainHook : Type 1 :=
  ∀ (Φ : Type) [Fintype Φ] [DecidableEq Φ] (n : ℕ) (E L : Type) [Field E] [NumberField E] [Field L]
    (T Ω : Type) (X : T → Type) (Vs : Ω → Type) [∀ ω, AddCommGroup (Vs ω)] [∀ ω, Module L (Vs ω)],
    (∀ μ, ∀ ω, Vs ω →ₗ[L] PeriodTarget.Col Φ n L (X μ)) → Prop

/-- **Sharp data realised by the defined objects**: a CM type `τ_K` on `E = Setting.E` with values in `K` that lifts
`Setting.τ`, and at each translate `u ∈ A₀` period data whose chain is `chain`'s, of rank `n = N_m − 1`, realised by
the hermitian frame of `u` (`KFrame.Realises`: `N_ω = Nsrc`, `C_u = Ctgt`, `B_ω = P_{μ0}`, `𝔞⁺, 𝔞⁻ ≠ 0`). -/
def SharpData.Realised (chain : ChainHook) {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {K : Type} [Field K]
    [NumberField K] [IsTotallyComplex K] (D : SharpData S κ x ε X K) : Prop :=
  ∃ (τK : Φ S.A → (S.E →+* K)) (j : K →+* ℂ), (∀ ρ, j.comp (τK ρ) = S.τ ρ) ∧
    ∀ u ∈ A₀ κ, ∃ (T : Type) (G X : T → Type) (_ : ∀ μ, Group (G μ)) (_ : ∀ μ, MulAction (G μ) (X μ))
      (Vs : (D.fr u).ι → Type) (_ : ∀ ω, AddCommGroup (Vs ω)) (_ : ∀ ω, Module K (Vs ω))
      (_ : ∀ ω, Module (𝓞 K) (Vs ω)) (_ : ∀ ω, IsScalarTower (𝓞 K) K (Vs ω))
      (P : PeriodTarget.PerData (Φ S.A) (D.R.N D.R.m - 1) S.E K G X Vs) (μ0 : T) (tw : PeriodTarget.Twist P μ0)
      (𝔞p 𝔞n : (D.fr u).ι → Ideal (𝓞 K)) (M : ∀ ω, Submodule (𝓞 K) (Vs ω)),
      chain (Φ S.A) (D.R.N D.R.m - 1) S.E K T (D.fr u).ι X Vs P.col ∧ (D.fr u).Realises τK P μ0 tw 𝔞p 𝔞n M

/-- **The sharp frontier** (spec L7.5): `SixTermBound`'s outer shape, with realised sharp data in place of six-term
data. For every primitive `χ`, at arbitrarily small `ε` there is `A ≥ 1` such that, for every large `Y`, every pair
`(q, d)` meeting `ZetaTwist.WinPair ε Y` has a sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, at each `x` of which a
setting with that pair, `d ≡ 3 (mod 4)`, and a character `κ` lifting `χ` has sharp data, over a totally complex
coefficient field `K`, realised by the defined objects with the chain `chain`. -/
def SharpBound (chain : ChainHook) : Prop :=
  ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → ∀ ε₀ > 0, ∃ ε, 0 < ε ∧ ε < ε₀ ∧
    ∃ A ≥ (1 : ℝ), ∀ᶠ Y in Filter.atTop, ∀ q d, ZetaTwist.WinPair ε Y q d →
      ∃ Y' ∈ Set.Icc Y (Y ^ (A / 2)), ∀ x ∈ Set.Icc Y' (Y' ^ 2), ∃ (S : Setting) (κ : S.A →* ℂˣ), S.q = q ∧
        S.d = d ∧ S.d % 4 = 3 ∧ S.Lifts κ χ ∧ ∃ (K : Type) (_ : Field K) (_ : NumberField K)
          (_ : IsTotallyComplex K) (D : SharpData S κ x ε (((S.N : ℝ) * x) ^ Real.log x) K), D.Realised chain

/-- **The sharp frontier gives the six-term frontier**, through the bridge `SharpData.toSixTermData`. -/
theorem sixTermBound_of_sharpBound {chain : ChainHook} (h : SharpBound chain) : SixTermBound := by
  intro f _ χ hχ ε₀ hε₀
  obtain ⟨ε, hε, hεε₀, A, hA, hY⟩ := h f χ hχ ε₀ hε₀
  refine ⟨ε, hε, hεε₀, A, hA, hY.mono fun Y hY q d hp => ?_⟩
  obtain ⟨Y', hY', hx⟩ := hY q d hp
  refine ⟨Y', hY', fun x hx' => ?_⟩
  obtain ⟨S, κ, hq, hd, -, hL, K, _, _, _, D, -⟩ := hx x hx'
  exact ⟨S, κ, hq, hd, hL, ⟨D.toSixTermData⟩⟩

/-- **CONDITIONAL. The Riemann hypothesis for `ζ` and every Dirichlet `L`-function from the sharp frontier**
(conditional on the half-plane `Re s > 11/12`, through `rhAndGRH_of_sixTermBound`). -/
theorem rhAndGRH_of_sharpBound {chain : ChainHook} (h : SharpBound chain) : HalfPlaneGRH.RHandGRH :=
  rhAndGRH_of_sixTermBound (sixTermBound_of_sharpBound h)

end ZetaBalance
