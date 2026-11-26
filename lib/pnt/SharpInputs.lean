import SharpChain

/-!
# The six-term frontier from its inputs and its pieces — CONDITIONAL on the half-plane

The architecture for **proving** the six-term frontier `SixTermBound`, hence RH and GRH: the deep classical inputs as
hypotheses (`SharpInputs`), the statements to prove in the library (`SharpPieces`), and the reduction
`sixTermBound_of_inputs`, which is logical packaging: the pieces give sharp data (`SharpData`) at every design, and
the bridge `SharpData.toSixTermData` gives six-term data.

**No pins.** The sharp frontier `SharpBoundPinned` (`SharpChain`) asks the sharp data to be realised by the archive's
objects (the theta chain, the rows, the twists). Nothing downstream reads that realisation: the bridge to the six-term
frontier discards it (`sixTermBound_of_sharpBound`). So the target here is the six-term frontier itself, and the
archive's objects enter only as the construction (`cons`), with the properties the pieces' proofs use.

**The construction is data.** Several pieces must hold for the *same* choices (the coefficient field, the words, the
auxiliary primes, the period data, `𝔞⁺`, `𝔞⁻`, the target metric, the heights and the constants). So the choices are
one field of `SharpPieces`, `cons`: per design, a coefficient field (`SharpCoeff`) and per translate an object
(`SharpObj`) holding every choice; with `adm`, the conditions the construction asks of the parameters, these are the
two data fields. Every other field is a statement about `cons`, proved by unfolding the construction. Only the frame
(coordinates and lattices) stays existential (`frame`), and every piece about frames holds for every frame realising
the object (`SharpObj.RealWith`), as all such frames are isometric.

**Pieces** (one per item of the proof plan, §3–§4): finite classes and stabilisers (`finiteClasses`), forms
finite-dimensional and integral forms a lattice (`formsLattice`), admissible parameters and windows (`params`), the
frame's existence (`frame`), the auxiliary primes (`primes`, (T)), the slope bound (F) with the index (V)
(`slopeFV`), the gain in (G↓) (`gain`), (G↑) (`gUp`), (S) and (R) (`frameSR`). `SharpObj.exists_sharpTr` assembles
one translate from them. (Z) is not a piece: each piece bounds its own slack by a share of the budget
`x^{4ε} Σ_t a_t` (a quarter each for `c↓ = c_F + c_G`, `c↑`, `(Σ_t a_t)·c_T` and the frame loss), and the reduction
adds them up.

**Eventually in the design.** `adm` is data, chosen before the inputs, but some pieces hold only for `ε` small and
`x` large in terms of an input's existential constants: `primes` needs `log(4dM²) ≤ c√Λ_u` for `ShortNorm`'s `c`,
true only past some `x₀(c)`. Such thresholds cannot be conditions of `adm`. So the pieces about designs (`frame`,
`primes`, `slopeFV`, `gain`, `gUp`, `frameSR`) have the archive's quantifier form, `EventuallyAdm`: some `ε₁ > 0` such
that at every `ε ≤ ε₁` some `x₀` has the piece at every admissible design at `x ≥ x₀`. The reduction combines them
(`SharpPieces.eventually_holdAt`, below the least `ε₁`, past the greatest `x₀`), calls `params` below `min ε₀ ε₁`, and
starts its windows past `x₀`. `params` takes `ShortNorm`, with which the archive chooses the split primes `g₀, g₁` of
the design.

**Sanity theorem:** `SharpObj.exists_sharpTr` (the per-translate reduction).

**Inputs** (`SharpInputs`; proof plan §5): Siegel–Weil (with Rallis), good twists, the unitary mass formula,
Chowla–Selberg/Colmez, `ShortNorm`. Where the library cannot state the classical theorem, the field is a consequence,
and its docstring says so. The pieces still to prove (`frame`, `gain`, `gUp`, `frameSR`) take the whole bundle; the
inputs they need about the construction (the local Weil representation, the covolume bound) are to be stated with
them.

**CONDITIONAL.** `rhAndGRH_of_inputs` rests on the half-plane `Re s > 11/12`, as `rhAndGRH_of_sixTermBound` does.
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

/-- The arithmetic of an auxiliary prime (`SharpData.Arith`): `T = ππ̄` with `π = (a + b√−d)/2 ≡ 1 (mod M)`,
`M = QS·q·d·(g₀g₁)²`. -/
def ArithT (T : ℕ) : Prop :=
  ∃ a b : ℤ, 4 * (T : ℤ) = a ^ 2 + S.d * b ^ 2 ∧
    ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℤ) ∣ b ∧
    a ≡ b + 2 [ZMOD 2 * ((S.QS * S.q * S.d * (Dg.g₀ * Dg.g₁) ^ 2 : ℕ) : ℤ)]

end SharpDesign

/-! ## The coefficient field, frames on given words, the per-translate object -/

/-- **The coefficient field** of a design: `K` totally complex, normal over `ℚ`, with a star (the archive's
`Fields.Ok`), and a CM type `τ_K` on `E = Setting.E`. -/
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

/-- **The object of a translate**: the choices at `u` that the pieces read, from the archive's construction. The words
`Ω` and their auxiliary primes `T`; levels `Tμ` with groups `G` acting on points `Xp`, sources `Vs`, place sets,
period data `P` with untwisted level `μ0` and twist `tw`, `𝔞⁺ = 𝔞p`, `𝔞⁻ = 𝔞n`, step-0 data, cusp subspaces `Xc` and
isomorphisms `e`; the target metric `g` on `V0_{μ0} → K` at each complex place, the heights `ht`; and the constants:
the place `pl` and scalars `cω` of (S), `e = eS`, `η`, the range `U`, the depth `H`, and the slacks `c_F` of (F),
`c_G` of the gain (`c↓ = c_F + c_G`), `c↑` and `c_T`. -/
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

namespace SharpObj

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}
  (b : SharpObj Dg C)

/-- The source lattice `M_ω`: the `O_K`-span of the integral forms of `X ⊓ V_ω`. -/
def M (ω : b.Ω) : Submodule (𝓞 C.K) (b.Vs ω) :=
  Submodule.span (𝓞 C.K) {φ | (b.e ω φ).1 ∈ HermForms.Mω (b.ST ω) C.τK (b.χ0 ω) (b.lam0 ω)}

/-- The source `N_ω = {φ ∈ 𝔞_ω⁻¹M_ω : B_ωφ ∈ C_u}` (`PeriodTarget.Nsrc`). -/
def N (ω : b.Ω) : Submodule (𝓞 C.K) (b.Vs ω) := PeriodTarget.Nsrc C.τK b.tw b.𝔞p b.𝔞n b.M ω

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

/-- **Good twists exist** (permanent; archive: `TwistTheoremAtIndex`). The twist characters of the pins: if `L` has
the `15`-th roots of unity, characters `δ` with `IsDelta p` at primes `p` beyond any bound; if `L` has the `ℓ`-th
roots of unity, characters `ψ` with `IsPsi ℓ Q`, ramified exactly at a nonempty set `Q` avoiding any finite set.
**Precision:** the theorem's index part (the twisted theta lattices `ℓ⁻²`-close to the untwisted ones, the
Bloch–Kato side) is on the step-`j` theta images, not stated here; the construction's twisted levels, if (G↑) or the
gain needs them, use it in that form. -/
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

/-- **The deep classical inputs**, as hypotheses (proof plan §5): permanent — Siegel–Weil with Rallis, good twists;
for now — the unitary mass formula, Chowla–Selberg/Colmez, `ShortNorm`. -/
structure SharpInputs : Prop where
  /-- Siegel–Weil, with Rallis. -/
  siegelWeil : SiegelWeil
  /-- Good twists exist. -/
  goodTwists : GoodTwists
  /-- The unitary mass formula. -/
  massFormula : MassFormula
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

/-- **Eventually in the design** (the archive's quantifier form): there is `ε₁ > 0` such that at every
`ε ∈ (0, ε₁]` there is `x₀` with `p` at every design at `ε` and `x ≥ x₀` admissible for `adm`. The thresholds
`ε₁`, `x₀` may depend on the inputs' existential constants (`ShortNorm`'s `c`, `MassFormula`'s `C₀`), so they
cannot be conditions of `adm`, which is chosen before the inputs. -/
def EventuallyAdm (adm : ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}, SharpDesign S κ x ε X → Prop)
    (p : ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}, SharpDesign S κ x ε X → Prop) : Prop :=
  ∃ ε₁ > 0, ∀ ε, 0 < ε → ε ≤ ε₁ → ∃ x₀ : ℝ, ∀ {S : Setting} {κ : S.A →* ℂˣ} {x X : ℝ}
    (Dg : SharpDesign S κ x ε X), x₀ ≤ x → adm Dg → p Dg

/-- **Two statements eventually in the design hold together eventually**: below the lesser `ε₁`, past the greater
`x₀`. -/
theorem EventuallyAdm.and {adm p q : ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}, SharpDesign S κ x ε X → Prop}
    (hp : EventuallyAdm adm p) (hq : EventuallyAdm adm q) : EventuallyAdm adm fun Dg => p Dg ∧ q Dg := by
  obtain ⟨ε₁, hε₁, hp⟩ := hp
  obtain ⟨ε₂, hε₂, hq⟩ := hq
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hle => ?_⟩
  obtain ⟨x₁, hx₁⟩ := hp ε hε (hle.trans (min_le_left _ _))
  obtain ⟨x₂, hx₂⟩ := hq ε hε (hle.trans (min_le_right _ _))
  exact ⟨max x₁ x₂, fun Dg hx hDg =>
    ⟨hx₁ Dg ((le_max_left _ _).trans hx) hDg, hx₂ Dg ((le_max_right _ _).trans hx) hDg⟩⟩

/-- **Admissible parameters and windows** for `adm` (the frontier's outer shape): for every primitive `χ` and every
`ε₀ > 0`, some `ε ∈ (0, ε₀)` and `A ≥ 1` such that, for `Y` large, every pair of `WinPair ε Y` has a sub-window
`[Y′, Y′²]`, `Y ≤ Y′ ≤ Y^{A/2}`, at every `x` of which a setting of the pair, with `κ` lifting `χ`, carries a design
admissible for `adm`. -/
def Params (adm : ∀ {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}, SharpDesign S κ x ε X → Prop) : Prop :=
  ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → ∀ ε₀ > 0,
    ∃ ε, 0 < ε ∧ ε < ε₀ ∧ ∃ A ≥ (1 : ℝ), ∀ᶠ Y in Filter.atTop, ∀ q d, ZetaTwist.WinPair ε Y q d →
      ∃ Y' ∈ Set.Icc Y (Y ^ (A / 2)), ∀ x ∈ Set.Icc Y' (Y' ^ 2), ∃ (S : Setting) (κ : S.A →* ℂˣ), S.q = q ∧
        S.d = d ∧ S.d % 4 = 3 ∧ S.Lifts κ χ ∧ ∃ Dg : SharpDesign S κ x ε (((S.N : ℝ) * x) ^ Real.log x), adm Dg

/-- **The statements to prove in the library** (proof plan §3–§4), with the inputs as hypotheses where a piece
uses them. Two fields are choices, not statements: `adm`, the conditions the construction asks of the parameters,
and `cons`, the construction itself (the archive's objects, the target metric, the constants), which the frontier
leaves existential and several pieces share. Every other field is a statement about them, provable on its own.
The pieces about designs (`frame`, `primes`, `slopeFV`, `gain`, `gUp`, `frameSR`) hold eventually in the
design (`EventuallyAdm`): for `ε` small and `x` large in terms of the constants of the inputs they take. `adm` is
chosen before the inputs, so such thresholds cannot be conditions of `adm`; `params` gives designs at an `ε` below
any `ε₀` and at every `x` of windows starting arbitrarily far out, which meets them. -/
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
  sub-window. It takes `ShortNorm`, with which the archive chooses the design's split primes `g₀, g₁`. Serves the
  outer quantifiers, `S.q = q`, `S.d = d`, `d ≡ 3 (mod 4)`, `κ` lifting `χ`, the weights and the parameters of
  `SharpData`, and `Arith`'s Legendre symbols. -/
  params : ShortNorm → Params adm
  /-- **The frame exists** (the lattices: `M_ω`, `N_ω`, `C_u` are `O_K`-lattices, the target metric positive),
  eventually in the design. Serves `SharpData.fr`. -/
  frame : SharpInputs → EventuallyAdm adm
    fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ, ((cons Dg).obj u).FrameExists
  /-- **(T)**, with `Arith`'s auxiliary primes (`SharpObj.Primes`), eventually in the design (`ShortNorm` applies
  once `log(4dM²) ≤ c√Λ_u`, for its constant `c`). -/
  primes : ShortNorm → EventuallyAdm adm fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) =>
    ∀ u ∈ A₀ κ, ((cons Dg).obj u).Primes u
  /-- **(F) and (V)**, half of (G↓) (`SharpObj.SlopeFV`), eventually in the design. -/
  slopeFV : EventuallyAdm adm fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) =>
    ∀ u ∈ A₀ κ, ((cons Dg).obj u).SlopeFV
  /-- **The gain in (G↓)** (`SharpObj.Gain`), eventually in the design. -/
  gain : SharpInputs → EventuallyAdm adm fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) =>
    ∀ u ∈ A₀ κ, ((cons Dg).obj u).Gain u
  /-- **(G↑)** (`SharpObj.GUp`), eventually in the design. -/
  gUp : SharpInputs → EventuallyAdm adm
    fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ, ((cons Dg).obj u).GUp u
  /-- **(S) and (R)** (`SharpObj.FrameSR`), eventually in the design. -/
  frameSR : SharpInputs → EventuallyAdm adm
    fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ, ((cons Dg).obj u).FrameSR

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

/-- The clauses of `SharpData` asked at a translate `u ∈ A₀`, with (Z) for this translate (`budget`). -/
structure SharpTr.Sharp (Dg : SharpDesign S κ x ε X) (u : S.A) {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] (t : SharpTr K) : Prop where
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

/-- **One translate from its pieces**: an object with a realising frame, whose primes, slopes, gain, (G↑), (S) and
(R) hold, gives the clauses of sharp data at `u`. (G↓) is (F) + (V) (`SlopeFV`) with the gain (`Gain`),
`c↓ = c_F + c_G`; (Z) at `u` adds the four quarter-budgets. -/
theorem SharpObj.exists_sharpTr {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S} (b : SharpObj Dg C) (u : S.A)
    (hfr : b.FrameExists) (hT : b.Primes u) (hFV : b.SlopeFV) (hgain : b.Gain u) (hup : b.GUp u)
    (hSR : b.FrameSR) : ∃ t : SharpTr C.K, t.Basic Dg ∧ t.Sharp Dg u := by
  obtain ⟨F, c, eC, hR⟩ := hfr
  obtain ⟨hcT0, hcT, hT⟩ := hT
  obtain ⟨hcF0, hcF, hFV⟩ := hFV
  obtain ⟨hcG0, hcG, hgain⟩ := hgain
  obtain ⟨hcU0, hcU, hup⟩ := hup
  obtain ⟨hcω, he0, hU0, hH0, hloss, hSR⟩ := hSR
  obtain ⟨hS, hrk, hrange, hdepth⟩ := hSR F c eC hR
  refine ⟨⟨F.toKFrame, b.T, b.pl, b.cω, b.eS, b.η, b.U, b.H, b.cF + b.cG, b.cUp, b.cT⟩,
    ⟨fun ω => (hT ω).1, fun ω => (hT ω).2.1, hcω, he0, add_nonneg hcF0 hcG0, hcU0, hcT0⟩,
    ⟨fun ω => (hT ω).2.2, fun ω => ?_, hup F c eC hR, hS, hrk, hrange, hdepth, hU0, hH0, ?_⟩⟩
  · have h1 := hFV F c eC hR ω
    have h2 := hgain ω
    dsimp only
    linarith
  · dsimp only
    linarith

/-- **The pieces about a design hold at it**: the conclusions of `frame`, `primes`, `slopeFV`, `gain`, `gUp` and
`frameSR` at `Dg`, translate by translate. -/
def SharpPieces.HoldAt (P : SharpPieces) (Dg : SharpDesign S κ x ε X) : Prop :=
  ∀ u ∈ A₀ κ, ((P.cons Dg).obj u).FrameExists ∧ ((P.cons Dg).obj u).Primes u ∧
      ((P.cons Dg).obj u).SlopeFV ∧ ((P.cons Dg).obj u).Gain u ∧ ((P.cons Dg).obj u).GUp u ∧
      ((P.cons Dg).obj u).FrameSR

/-- **The pieces about designs hold together eventually in the design**, with the inputs they use: the six pieces
combined by `EventuallyAdm.and`, below the least of their `ε₁` and, at each `ε`, past the greatest of their `x₀`. -/
theorem SharpPieces.eventually_holdAt (I : SharpInputs) (P : SharpPieces) : EventuallyAdm P.adm P.HoldAt := by
  obtain ⟨ε₁, hε₁, h⟩ := (((((P.frame I).and (P.primes I.shortNorm)).and P.slopeFV).and (P.gain I)).and
    (P.gUp I)).and (P.frameSR I)
  refine ⟨ε₁, hε₁, fun ε hε hle => ?_⟩
  obtain ⟨x₀, hx₀⟩ := h ε hε hle
  refine ⟨x₀, fun Dg hx hDg => ?_⟩
  obtain ⟨⟨⟨⟨⟨hfr, hT⟩, hFV⟩, hgain⟩, hup⟩, hSR⟩ := hx₀ Dg hx hDg
  exact fun u hu => ⟨hfr u hu, hT u hu, hFV u hu, hgain u hu, hup u hu, hSR u hu⟩

/-- **One translate from the pieces**: at `u ∈ A₀`, the pieces about the construction's object, at a design where
they hold. -/
theorem exists_sharpTr (P : SharpPieces) (Dg : SharpDesign S κ x ε X) (h : P.HoldAt Dg) (u : S.A)
    (hu : u ∈ A₀ κ) : ∃ t : SharpTr (P.cons Dg).C.K, t.Basic Dg ∧ t.Sharp Dg u := by
  obtain ⟨hfr, hT, hFV, hgain, hup, hSR⟩ := h u hu
  exact ((P.cons Dg).obj u).exists_sharpTr u hfr hT hFV hgain hup hSR

/-- **Sharp data from the pieces**, at a design where the pieces about designs hold: the translates of `A₀` from
`exists_sharpTr`, the others from the translate `1` (`SharpData` asks primes and signs at every translate); (Z) is
the sum of the translates' budgets. -/
theorem exists_sharpData (P : SharpPieces) (Dg : SharpDesign S κ x ε X) (h : P.HoldAt Dg) :
    Nonempty (SharpData S κ x ε X (P.cons Dg).C.K) := by
  have h1 : (1 : S.A) ∈ A₀ κ := by simp [A₀]
  obtain ⟨t₁, hb₁, -⟩ := exists_sharpTr P Dg h 1 h1
  have hex : ∀ u, ∃ t : SharpTr (P.cons Dg).C.K, t.Basic Dg ∧ (u ∈ A₀ κ → t.Sharp Dg u) := by
    intro u
    by_cases hu : u ∈ A₀ κ
    · obtain ⟨t, hb, hs⟩ := exists_sharpTr P Dg h u hu
      exact ⟨t, hb, fun _ => hs⟩
    · exact ⟨t₁, hb₁, fun h => absurd h hu⟩
  choose tr htr using hex
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
  exact ⟨D⟩

/-- **The six-term frontier from the inputs and the pieces**: the pieces about designs hold below some `ε₁`
(`eventually_holdAt`); `params` below `min ε₀ ε₁` gives `ε`, the outer shape and an admissible design at every `x`;
at `ε` the pieces hold past some `x₀`, and the window is taken from `Y ≥ x₀` on (every `x` of it is `≥ Y' ≥ Y`);
`exists_sharpData` gives sharp data, and the bridge `toSixTermData` six-term data. -/
theorem sixTermBound_of_inputs (I : SharpInputs) (P : SharpPieces) : SixTermBound := by
  intro f _ χ hχ ε₀ hε₀
  obtain ⟨ε₁, hε₁, hP⟩ := P.eventually_holdAt I
  obtain ⟨ε, hε, hεε, A, hA, hY⟩ := P.params I.shortNorm f χ hχ (min ε₀ ε₁) (lt_min hε₀ hε₁)
  obtain ⟨x₀, hx₀⟩ := hP ε hε (hεε.le.trans (min_le_right _ _))
  refine ⟨ε, hε, hεε.trans_le (min_le_left _ _), A, hA,
    (hY.and (Filter.eventually_ge_atTop x₀)).mono fun Y hY q d hp => ?_⟩
  obtain ⟨Y', hY', hx⟩ := hY.1 q d hp
  refine ⟨Y', hY', fun x hx' => ?_⟩
  obtain ⟨S, κ, hq, hd, -, hL, Dg, hDg⟩ := hx x hx'
  exact ⟨S, κ, hq, hd, hL,
    SharpData.nonempty_sixTermData (exists_sharpData P Dg (hx₀ Dg (hY.2.trans (hY'.1.trans hx'.1)) hDg))⟩

/-- **CONDITIONAL. RH and GRH from the inputs and the pieces** (on the half-plane `Re s > 11/12`). -/
theorem rhAndGRH_of_inputs (I : SharpInputs) (P : SharpPieces) : HalfPlaneGRH.RHandGRH :=
  rhAndGRH_of_sixTermBound (sixTermBound_of_inputs I P)

end

end ZetaBalance
