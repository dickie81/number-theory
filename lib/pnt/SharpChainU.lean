import ChainField
import ChainCanon
import ChainLocal
import ChainHeis
import RowSpace

/-!
# The explicit Stage-U theta chain in the construction

The construction of the six-term frontier's proof (`SharpInputs`, the field `SharpPieces.cons`) with its period data
the explicit theta chain at Stage U (chain spec §2, §3.5–§3.8; the C1e row of its module plan): one word, one level,
no twist. Everything is a definition from the design, the setting and the four choices below; the construction carries
no proof. Facts it needs (that a choice exists, that a map is linear, that the field contains what it should) are the
consumers' (C2), and each definition takes its intended value whenever its fact holds.

**The chain of a translate** (`chainData`, `chainTop`), generic in the coefficient field `L`, the embeddings `τ`, the
theta constants `P` and the lift characters `μ`. It has length `m = R.m` and ranks `N_j = k + j(t + 1)`
(`Setting.Ranks.N`); the places are `ST` of the translate's auxiliary prime and `SG` over `g₀g₁` (`SharpCons`), with
no twist places (`Q = ∅`) and the coset places `S = ST ∪ SG` (`chainS`); one index per level (`β j = Unit`) with
the level groups `ChainLocal.levU` at `SG` (`uniUT` at step 0); the weights `e_j` (`ChainField.chainE`) and
`λ_j = wt(k, t, j)` of `hc u` (`chainLam`); the determinant ideles `ChainHeis.dICls` for the choice `sel = selU SG`;
the base thetas `θ_j = thetaStd(N_j, N_{j+1})` of `ChainCanon` for the lattice `Λ_M = ι(𝔟⁻¹)` (`ChainCanon.lamM`) and
the isometry `g` (`chainG`); the coset integers `cA = (∏_{P ∈ SG} N(P))^{m+1}`, `cB = T·cA` and the Heisenberg data
`ChainHeis.xdU`, `ChainHeis.haU`; and the local factors `ChainLocal.xiU`, built in two stages (`chainData0` has none,
and `xiU` does not read them). The top (`chainTop`) maps level `m − 1` to each row point `x` through its decorated
lift `tilQ π_T x` read at rank `N_m` (`chainPt`), with that lift's determinant idele and Heisenberg data, the coupled
factor `xiU` at step `m − 2` (no coset `Y` at Stage U, `Yb = Unit`) and the top factor `ChainLocal.xiTopU` at
`π = conj(π_T)`, reading the point's frames at rank `N_m − 1` (`chainFrd`).

**The choices.** The ideal `𝔟` with `𝔟 + 𝔟̄ = O_E` and `𝔟𝔟̄ = 𝔡_{E/K₀}`, `K₀ = ℚ(√−d)` (`chainB`, an `ε` on
`IsBIdeal`, stated through the inverse different as in `ThetaNorm.Pin.Canonical`); the isometry `g`, `K₀`-rational,
with `g(Λ_M⁴)` commensurable with `Lc^{4Φ}` (`chainG`, an `ε` on `IsGIso`); the lift characters (`ChainField.muC`)
and the half `sel` of the split places (`ChainHeis.selU`). The residue datum is `xi0 = −1/√−d` (`chainXi0`) and
`sd = √d/2` (`chainSd`).

**The coefficient field** (`sharpCoeff`). The chain's `ℂ`-valued instance (`σ₀ = id`, `τ = S.τ`, the `ℂ`-valued
lift characters `muC` and the coordinate generators `gτC`, `chainTPC`) has the jets of the one over the field under
`KOk`: the jets read only the complex data, `σ₀ ∘ τ_K = τ` (so `Λ_M` is the same lattice, by definition), and
`σ₀(gτK p) = g_p` (`ChainField.coe_gτK`). Its jets of the steps below `m − 1` and of the top, over all translates, are
`chainJ`, and the field is `ChainField.chainField` with them: the normal closure of `τ(E)`, the local constants at
`SG`, the coordinate generators, the values of the lift characters and the jets, when these generate a
finite-dimensional field (`ChainField.KOk`), and the setting's `sharpField` otherwise. Over it the chain is
`sharpData`, `sharpTop`, with `σ₀` the inclusion, `cD(p) = σ₀(gτK p)` (`sharpTP`) and the characters `muK`.

**The period data** (`sharpPer`, from the generic `perU`). With `n = N_m − 1` (`rowN`):
* `tz = π_T` (`sharpTz`);
* the weight of the rows `σ = sgT(k, t, m; v, b, e)` of `hc u` (`sharpσ`);
* the branching map `br = brConst(λ_m, σ)·∏_τ τ(tz)^{−nBr}·Π_σ ∘ coefLast` (`sharpBr`), with `λ_m = wt(k, t, m)` read
  at rank `n + 1` (`sharpLamM`) and `Π_σ` an `ε` on `PeriodTarget.IsFockProj` (`sharpPr`; it is unique);
* the points of the level: the row points (`RowPt`), the good decorated lattices of rank `n` with no level-`T` places
  and frames at `SG ∪ ∅`, moved by `RowG = U_n × rowLevel(r = k + m − 1, t)` (`rowLev`), with the lattice
  `lsh x = N_x`;
* all rows: the `VV(σ)`-valued rows on the classes (`V0all`, no type group);
* the column `col φ x = Θ_m(φ)(x)`, the top of the chain on the step-0 classes, read at rank `n + 1` (`sharpCol`), as
  a linear map when it is one (`linOr`).

The step-0 character is `χ0 = σ₀⁻¹ ∘ lamGen(xi0)` on `uniUT(SG, k)` when that is multiplicative (`sharpχ0`, through
`monoidHomOr`), and the source space is `V_ω = V(ST, τ_K, χ0, λ_0)` on the whole cut (`sharpVs`).

**The construction** (`sharpObj`, `sharpCons`). The fields that the proved pieces read (`SharpCores`: `T`, `ST`,
`SG`, `n0 = k`, `λ_0`, `X_c = ⊤`, `e = id` and the slacks) are those of Stage 0, unchanged. **Still placeholders:**
`𝔞⁺ = 𝔞⁻ = ⊤`, the target metric `g = 0` and the heights `0` (the gain and (G↑) will set them); the twist is empty
(`sharpTw`, Stage U); the forced orders are the archive's `ForcedOrders.Fo` (the gain's exponent module will define
the untwisted ones).

**What the consumers prove (C2)**, each a hypothesis of a lemma about these definitions: `KOk` (C2f, from the jets'
rationality and C3); that `𝔟`, `g`, the lift characters and `sel` exist (C2c, C3, `ChainHeis.IsSel`); `Δ(ℤ + ℤω) ≠ 0`
(C2c); that `col` is linear (C2a: finitely many classes, finite coset quotients); that `σ₀⁻¹ ∘ lamGen` is
multiplicative (C2b); that the Fock projection exists and `brConst ≠ 0` (`PeriodTarget.exists_isFockProj`,
`PeriodTarget.brConst_ne_zero`, with the interlacing `SharpDesign.PinnedTo.interlace`); the finiteness of the
Heisenberg indices (`ChainHeis.xdPin_xdU`) and of the determinant ideles' supports (`ChainHeis.isIdeleFam_detComp`).

**Sanity theorems:** `linOr_apply`, `monoidHomOr_apply`.
-/

namespace ZetaBalance

open NumberField IsDedekindDomain ThetaChain HermClasses ChainCanon ChainLocal ChainHeis
open WeylFock (Pol VV)

noncomputable section

/-! ## Linear maps and characters without proofs -/

section OrElse

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

open Classical in
/-- **`f` as a linear map** when it is one, `0` otherwise: the construction defines the column this way, so it
carries no linearity proof (C2a proves `IsLinearMap`). -/
def linOr (f : V → W) : V →ₗ[K] W := if h : IsLinearMap K f then IsLinearMap.mk' f h else 0

/-- **`linOr f` is `f`** when `f` is linear. -/
theorem linOr_apply {f : V → W} (h : IsLinearMap K f) (v : V) : linOr (K := K) f v = f v := by
  rw [linOr, dite_eq_left h]
  rfl

open Classical in
/-- **`f` as a monoid homomorphism** when it is one, `1` otherwise: the construction defines the step-0 character
this way (C2b proves that `σ₀⁻¹ ∘ lamGen` is multiplicative). -/
def monoidHomOr {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M → N) : M →* N :=
  if h : f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b then ⟨⟨f, h.1⟩, h.2⟩ else 1

/-- **`monoidHomOr f` is `f`** when `f` is multiplicative. -/
theorem monoidHomOr_apply {M N : Type*} [MulOneClass M] [MulOneClass N] {f : M → N}
    (h : f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b) (a : M) : monoidHomOr f a = f a := by
  rw [monoidHomOr, dite_eq_left h]
  rfl

end OrElse

/-! ## All rows, and the period data of one word -/

section Per

variable {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E L : Type*} [Field E] [Field L]
  {G X : Type*} [Group G] [MulAction G X] {V : Type*} [AddCommGroup V] [Module L V]

/-- **All rows**: the `VV(σ)`-valued rows, finitely supported on the classes of the points (chain spec §3.7). No type
group and no level idempotent, so the rows pair with the branched column at every class representative. -/
def V0all (σ : Φ → Fin n → ℤ) : Submodule L (HermClasses.Cl G X →₀ Pol Φ n L) where
  carrier := {F | ∀ c, F c ∈ VV σ}
  add_mem' hF hG c := by simpa using add_mem (hF c) (hG c)
  zero_mem' c := by simp
  smul_mem' a F hF c := by simpa using Submodule.smul_mem _ a (hF c)

/-- **The period data of one word at one level** (Stage U): `tz`, the weight `σ` of the rows, the branching map `b`,
the lattice of a point, all rows (`V0all`) and the column, read as a linear map (`linOr`). -/
def perU (tz : E) (σ : Φ → Fin n → ℤ) (b : Pol Φ (n + 1) L →ₗ[L] Pol Φ n L)
    (lsh : X → Submodule (𝓞 E) (Fin n → E)) (col : V → PeriodTarget.Col Φ n L X) :
    PeriodTarget.PerData Φ n E L (fun _ : Unit => G) (fun _ : Unit => X) (fun _ : Unit => V) where
  tz _ := tz
  σ := σ
  br _ := b
  lsh _ := lsh
  V0 _ := V0all σ
  col _ _ := linOr col

end Per

/-! ## The choices of the setting -/

section Choices

variable (S : Setting)

/-- **`sd = √d/2`**, the constant of the theta functions. -/
def chainSd : ℝ := Real.sqrt S.d / 2

/-- **The quadratic subfield `K₀ = ℚ(√−d)`** of `E` (`√−d = gaussE`). -/
def chainK0 : IntermediateField ℚ S.E := IntermediateField.adjoin ℚ {S.gaussE}

/-- **The conditions on `𝔟`**: `𝔟 + 𝔟̄ = O_E` and `𝔟𝔟̄ = 𝔡_{E/K₀}`, the latter through the inverse different,
`(𝔟𝔟̄)⁻¹ = {x : Tr_{E/K₀}(x·O_E) ⊆ O_{K₀}}` (as in `ThetaNorm.Pin.Canonical`). -/
def IsBIdeal (𝔟 : Ideal (𝓞 S.E)) : Prop :=
  𝔟 ⊔ 𝔟.comap (IsCMField.ringOfIntegersComplexConj S.E : 𝓞 S.E →+* 𝓞 S.E) = ⊤ ∧
    ∀ z : S.E, (∀ y ∈ 𝔟 * 𝔟.comap (IsCMField.ringOfIntegersComplexConj S.E : 𝓞 S.E →+* 𝓞 S.E),
      IsIntegral ℤ (z * (y : S.E))) ↔ ∀ y : 𝓞 S.E, IsIntegral ℤ (Algebra.trace (chainK0 S) S.E (z * (y : S.E)))

/-- **The ideal `𝔟`** of the theta constants: `𝔄 = 𝔟⁻¹` and `cD(p)` generates `τ_p(𝔟⁻¹)` (an `ε` on `IsBIdeal`;
that one exists is for C2). -/
def chainB : Ideal (𝓞 S.E) := Classical.epsilon (IsBIdeal S)

/-- **`xi0 = −1/√−d`**, the residue datum of step 0 (`N(cc) = 1`): it fixes `ψ₀`, so the step-0 character and the
additive characters `ψ_P` at `SG`. -/
def chainXi0 : S.E := -S.gaussE⁻¹

/-- **The theta constants of the `ℂ`-valued chain** (`ChainCanon.chainTP` at `σ₀ = id`, with the coordinate
generators `g_p = τ_p(a)^{−1/h}` of `ChainField.gτC`), whose jets the coefficient field adjoins. -/
def chainTPC : TP S.E ℂ (Φ S.A) := chainTP (RingHom.id ℂ) (chainSd S) (chainB S) (gτC S.τ (chainB S))

/-- **`K₀` in `ℂ`**: `{a + b√d·i : a, b ∈ ℚ}`, the image of `ℚ(√−d)` at either embedding. -/
def k0C : Set ℂ := {z | ∃ a b : ℚ, z = a + b * Real.sqrt S.d * Complex.I}

/-- **The conditions on the isometry `g`** of the base theta: an `H_s`-isometry (`s = sC`), `K₀`-rational (its matrix
entries lie in `K₀ ⊆ ℂ`), with `g(Λ_M⁴)` commensurable with `Lc^{4Φ}`, for `Λ_M = ι(𝔟⁻¹)` (`lamM`) and the canonical
CM lattice `Lc` (`cmLat`). -/
def IsGIso (g : (Fin 4 × Φ S.A → ℂ) ≃ₗ[ℂ] (Fin 4 × Φ S.A → ℂ)) : Prop :=
  (∀ z w, Hf (sC (chainSd S)) (g z) (g w) = Hf (sC (chainSd S)) z w) ∧
    (∀ i j, LinearMap.toMatrix' g.toLinearMap i j ∈ k0C S) ∧
    ((ThetaNorm.pow4 (lamM S.τ (chainTPC S))).map g.toLinearMap.toAddMonoidHom).relIndex
        (ThetaNorm.stdLat4 (cmLat (chainSd S)).lattice.toAddSubgroup) ≠ 0 ∧
    (ThetaNorm.stdLat4 (Φ := Φ S.A) (cmLat (chainSd S)).lattice.toAddSubgroup).relIndex
        ((ThetaNorm.pow4 (lamM S.τ (chainTPC S))).map g.toLinearMap.toAddMonoidHom) ≠ 0

/-- **The isometry `g`** of the base theta (an `ε` on `IsGIso`; that one exists, by Gram–Schmidt over `K₀` and four
squares, is for C2). -/
def chainG : (Fin 4 × Φ S.A → ℂ) ≃ₗ[ℂ] (Fin 4 × Φ S.A → ℂ) :=
  haveI : Nonempty ((Fin 4 × Φ S.A → ℂ) ≃ₗ[ℂ] (Fin 4 × Φ S.A → ℂ)) := ⟨LinearEquiv.refl ℂ _⟩
  Classical.epsilon (IsGIso S)

end Choices

/-! ## The row points -/

section Rows

open Classical

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-- **The rank of the rows**, `n = N_m − 1`. -/
abbrev rowN : ℕ := Dg.R.N Dg.R.m - 1

/-- **`n + 1 = N_m`**, as `N_m ≥ k ≥ 1`. -/
theorem rowN_add_one : rowN Dg + 1 = Dg.R.N Dg.R.m := by
  have := Dg.R.m_add_three_le
  unfold rowN Setting.Ranks.N
  omega

/-- **`n + 1` is the rank of the top level** `N_{(m − 2) + 2}`, as `m ≥ 2`. -/
theorem rowN_add_one_top : rowN Dg + 1 = Dg.R.N (Dg.R.m - 2 + 2) := by
  rw [Nat.sub_add_cancel Dg.R.two_le_m]
  exact rowN_add_one Dg

/-- **The level of the rows**: `RowSpace.rowLevel` at `SG`, with blocks `(r, t, …, t)`, `r = k + m − 1`, and no
twist places. -/
def rowLev : Subgroup (∀ w : ↥(sharpSG Dg ∪ ∅), GL (Fin (rowN Dg)) (𝓞 S.E ⧸ w.1.asIdeal)) :=
  RowSpace.rowLevel (rowN Dg) Dg.R.r Dg.R.t (sharpSG Dg) ∅

/-- **The group of the row points**, `U_n × rowLevel` (`HermClasses.Grp`). -/
abbrev RowG : Type := Grp S.E (rowN Dg) (sharpSG Dg ∪ ∅) (rowLev Dg)

/-- **The row points**: the good decorated lattices of rank `n` with no level-`T` places and frames at `SG ∪ ∅`
(`HermClasses.points`). -/
abbrev RowPt : Type :=
  ↥(points (E := S.E) (n := rowN Dg) (ST := (∅ : Finset (HeightOneSpectrum (𝓞 S.E)))) (rowLev Dg))

variable (u : S.A)

/-- **The decorated lift of a row point** `x`, `tilQ π_T x` (`HermClasses.tilQ`: the lattice `N_x ⊕ O_E·e_last`, the
level-`T` decoration at `ST`, all frames kept), read at the rank `N_{(m − 2) + 2}` of the chain's top. -/
def chainPt (x : RowPt Dg) : Deco S.E (Dg.R.N (Dg.R.m - 2 + 2)) (sharpST Dg u) (sharpSG Dg ∪ ∅) :=
  decoCast (rowN_add_one_top Dg) (tilQ (sharpTz Dg u) x.1)

/-- **The frames of a row point**, read at the rank `N_{(m − 2) + 2} − 1` of the top factor. -/
def chainFrd (x : RowPt Dg) (P : HeightOneSpectrum (𝓞 S.E)) :
    Matrix (Fin (Dg.R.N (Dg.R.m - 2 + 2) - 1)) (Fin (Dg.R.N (Dg.R.m - 2 + 2) - 1)) S.E :=
  (frAt x.1 P).submatrix (Fin.cast (by rw [← rowN_add_one_top Dg, Nat.add_sub_cancel]))
    (Fin.cast (by rw [← rowN_add_one_top Dg, Nat.add_sub_cancel]))

end Rows

/-! ## The chain of a translate -/

section Chain

open Classical

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X) (u : S.A)

/-- **The weights `λ_j`** of the translate's chain: `WeylFock.wt(k, t, j)` with `u_i − ½` and `e` of `hc u`. -/
def chainLam (j : ℕ) : Φ S.A → Fin (Dg.R.N j) → ℤ :=
  WeylFock.wt Dg.R.k Dg.R.t j (fun ρ i => ⌊(Dg.hc u ρ).u i - 1 / 2⌋) (fun ρ => finN (Dg.hc u ρ).e)

/-- **The places of the cosets**, `S = ST ∪ SG`. -/
def chainS : Set (HeightOneSpectrum (𝓞 S.E)) := ↑(sharpST Dg u) ∪ ↑(sharpSG Dg)

/-- **The coset integer `cA = (∏_{P ∈ SG} N(P))^{m+1}`** of every step (`ChainHeis.cAU`). -/
def chainCA : ℕ := cAU (sharpSG Dg) Dg.R.m

/-- **The coset integer `cB = T·cA`** of every step, `T` the translate's auxiliary prime (`ChainHeis.cBU`). -/
def chainCB : ℕ := cBU (sharpT Dg u) (sharpSG Dg) Dg.R.m

variable {L : Type} [Field L] (τ : Φ S.A → (S.E →+* L)) (P : TP S.E L (Φ S.A)) (mu : ℕ → Hecke S.E L)

/-- **The chain data with no local factors** (`Ξ = 0`), for the theta constants `P` and the lift characters `μ`: the
ranks `N_j`, the places `ST`, `SG`, `Q = ∅`, `S = ST ∪ SG`, one index per level with the groups `levU` at `SG`, the
weights `e_j` and `λ_j` of `hc u`, the determinant ideles for `sel = selU SG`, the base thetas
`thetaStd(N_j, N_{j+1})` for `Λ_M = ι(𝔟⁻¹)` and `g`, the coset integers and the Heisenberg data. The local factors
read the data but not their own field, so `chainData` adds them. -/
def chainData0 : Data τ where
  n := Dg.R.N
  mono j := by
    unfold Setting.Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ j)) _
  P := P
  ST := sharpST Dg u
  SG := sharpSG Dg
  Q := ∅
  S := chainS Dg u
  β _ := Unit
  Λ j _ := (levU (sharpSG Dg) Dg.R.N Dg.R.m Dg.R.k Dg.R.t j).prod ⊤
  e := chainE Dg u
  lam := chainLam Dg u
  mu := mu
  dI _ c := dICls (selU (sharpSG Dg)) c
  θ j := thetaStd (chainSd S) (lamM τ P) (chainG S) (Dg.R.N j) (Dg.R.N (j + 1))
  cA _ := chainCA Dg
  cB _ := chainCB Dg u
  XD _ c c' := xdU τ P (chainS Dg u) (chainCA Dg) (chainCB Dg u) c.2.N c'.2.N
  HA _ c c' := haU P (chainS Dg u) (chainCA Dg) (chainCB Dg u) c.2.N c'.2.N
  Xi _ _ _ _ := 0

/-- **The chain data of the translate** (Stage U): `chainData0` with the local factors `Ξ_j = xiU` (`ThetaVol.xiStd`
at `R = SG`, `h = 1`, depth `m + 1`, the parameters `ψ_P`, `μ_P`, `sq_P` of `xi0` and of the lift characters). -/
def chainData : Data τ :=
  { chainData0 Dg u τ P mu with Xi := xiU (chainData0 Dg u τ P mu) Dg.R.m Dg.R.k Dg.R.t (chainXi0 S) }

/-- **The top of the translate's chain** (length `m = (m − 2) + 2`, no coset `Y` at Stage U): each row point `x` is
reached through its lift `chainPt x`, with that lift's determinant idele and Heisenberg data; the coupled factor of
step `m − 2` is `xiU` (`xiCpl` with `Q \ SG = ∅`), and the top factor `xiTopU` reads the point's frames (`chainFrd`)
at `π = conj(π_T)`. -/
def chainTop : ThetaChain.Top (chainData Dg u τ P mu) (Dg.R.m - 2) (sharpSG Dg ∪ ∅) Unit (RowPt Dg) where
  pt := chainPt Dg u
  dI x := dIU (selU (sharpSG Dg)) (sharpSG Dg ∪ ∅) (chainPt Dg u x).N (frAt (chainPt Dg u x))
  XD c x := xdU τ P (chainS Dg u) (chainCA Dg) (chainCB Dg u) c.2.N (chainPt Dg u x).N
  HA c x := haU P (chainS Dg u) (chainCA Dg) (chainCB Dg u) c.2.N (chainPt Dg u x).N
  Xi1 c₀ c _ := xiU (chainData Dg u τ P mu) Dg.R.m Dg.R.k Dg.R.t (chainXi0 S) (Dg.R.m - 2) c₀ c
  Xi2 c _ x := xiTopU (chainData Dg u τ P mu) (Dg.R.m - 2) Dg.R.k Dg.R.t (chainXi0 S) c (chainPt Dg u x)
    (chainFrd Dg x) (IsCMField.complexConj S.E (sharpTz Dg u : S.E))

end Chain

/-! ## The coefficient field and the chain over it -/

section Field

open Classical

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-- **The jets of the chain**: over all translates, those of the steps below `m − 1` and of the top of the
`ℂ`-valued chain (`σ₀ = id`, `τ = S.τ`, `chainTPC`, the `ℂ`-valued lift characters `muC`), which under `KOk` are
those of the chain over the coefficient field (`sharpData`, `sharpTop`). -/
def chainJ : Set ℂ :=
  ⋃ u, (chainData Dg u S.τ (chainTPC S) (muC Dg u)).jets (Dg.R.m - 2 + 1) ∪
    (chainTop Dg u S.τ (chainTPC S) (muC Dg u)).jets

/-- **The coefficient field of the construction** (`SharpCoeff`): `ChainField.chainCoeff` with the ideal `𝔟` and the
chain's jets. -/
def sharpCoeff : SharpCoeff S := chainCoeff Dg (chainB S) (chainJ Dg)

/-- **The theta constants over the coefficient field**: `σ₀` the inclusion `K ⊆ ℂ`, `δ`, `s`, `sd`, `𝔄 = 𝔟⁻¹` and
`cD(p) = σ₀(g_p)` with `g_p` read in `K` (`ChainField.gτK`). -/
def sharpTP : TP S.E (sharpCoeff Dg).K (Φ S.A) :=
  chainTP (algebraMap (chainField Dg (chainB S) (chainJ Dg)) ℂ) (chainSd S) (chainB S)
    (gτK Dg (chainB S) (chainJ Dg))

/-- **The lift characters over the coefficient field**, `μ_{0,j} = σ₀⁻¹ ∘ μ^ℂ_{0,j}` (`ChainField.muK`). -/
def sharpMu (u : S.A) : ℕ → Hecke S.E (sharpCoeff Dg).K := muK Dg (chainB S) (chainJ Dg) u

/-- **The chain data of the translate over the coefficient field**: `chainData` at `τ_K`, `sharpTP` and the
characters `sharpMu`. -/
def sharpData (u : S.A) : Data (sharpCoeff Dg).τK := chainData Dg u (sharpCoeff Dg).τK (sharpTP Dg) (sharpMu Dg u)

/-- **The top of the translate's chain over the coefficient field**: `chainTop` at `τ_K`, `sharpTP` and the
characters `sharpMu`. -/
def sharpTop (u : S.A) : ThetaChain.Top (sharpData Dg u) (Dg.R.m - 2) (sharpSG Dg ∪ ∅) Unit (RowPt Dg) :=
  chainTop Dg u (sharpCoeff Dg).τK (sharpTP Dg) (sharpMu Dg u)

end Field

/-! ## The object of a translate -/

section Obj

open Classical

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-- **The step-0 character** `χ0 = σ₀⁻¹ ∘ lamGen(xi0)` on `uniUT(SG, k)`, when that is multiplicative (`monoidHomOr`;
it is by A11, C2b). -/
def sharpχ0 : uniUT (sharpSG Dg) Dg.R.k →* (sharpCoeff Dg).K :=
  monoidHomOr fun g => desc (sharpTP Dg)
    (lamGen (chainXi0 S) (g : ∀ w : sharpSG Dg, GL (Fin Dg.R.k) (𝓞 S.E ⧸ w.1.asIdeal)))

/-- **The source space of the word**: `V_ω = X_c ⊓ V(ST, τ_K, χ0, λ_0)` with `X_c = ⊤`, the whole cut. -/
abbrev sharpVs (u : S.A) : Type :=
  ↥((⊤ : Submodule (sharpCoeff Dg).K
      (HermForms.Fn (sharpST Dg u) (uniUT (sharpSG Dg) Dg.R.k) (Φ S.A) (sharpCoeff Dg).K)) ⊓
    HermForms.Vω (sharpST Dg u) (sharpCoeff Dg).τK (sharpχ0 Dg) (sharpLam0 Dg u))

/-- **`k = N_0`**, the step-0 rank of the source and of the chain. -/
theorem k_eq_N_zero : Dg.R.k = Dg.R.N 0 := by
  simp [Setting.Ranks.N]

/-- **The column of the word** at a row point `x`: the chain's top (`sharpTop`) on the output at level `m − 2` of
the chain (`sharpData`) started at the step-0 classes from the form `φ` (`Data.inp`, cast to the rank `N_0`), read at
rank `n + 1`. -/
def sharpCol (u : S.A) (φ : sharpVs Dg u) (x : RowPt Dg) : Pol (Φ S.A) (rowN Dg + 1) (sharpCoeff Dg).K :=
  polCast (rowN_add_one_top Dg).symm ((sharpTop Dg u).col ((sharpData Dg u).chain.comp (Dg.R.m - 2)
    ((sharpData Dg u).inp (uniUT (sharpSG Dg) (Dg.R.N 0)) (fnCast rfl rfl (k_eq_N_zero Dg) φ.1))) x)

/-- **The weight of the rows**: `σ = sgT(k, t, m; v, b, e)` of `hc u`, at rank `n = N_m − 1`. -/
def sharpσ (u : S.A) : Φ S.A → Fin (rowN Dg) → ℤ :=
  PeriodTarget.sgT Dg.R.k Dg.R.t Dg.R.m (fun ρ => finN (Dg.hc u ρ).v) (fun ρ => finN (Dg.hc u ρ).b)
    (fun ρ => finN (Dg.hc u ρ).e)

/-- **The weight of the column** `λ_m = wt(k, t, m)` of `hc u` (`chainLam` at `m`), read at rank `n + 1 = N_m`. -/
def sharpLamM (u : S.A) : Φ S.A → Fin (rowN Dg + 1) → ℤ :=
  fun ρ i => chainLam Dg u Dg.R.m ρ (Fin.cast (rowN_add_one Dg) i)

/-- **The Fock projection `Π_σ`** onto `VV(σ)` (an `ε` on `PeriodTarget.IsFockProj`; it exists for antitone `σ`,
`PeriodTarget.exists_isFockProj`, and is unique). -/
def sharpPr (u : S.A) : Pol (Φ S.A) (rowN Dg) (sharpCoeff Dg).K →ₗ[(sharpCoeff Dg).K] Pol (Φ S.A) (rowN Dg)
    (sharpCoeff Dg).K :=
  Classical.epsilon (PeriodTarget.IsFockProj (sharpσ Dg u))

/-- **The branching map** `br = brConst(λ_m, σ)·∏_τ τ(tz)^{−nBr}·Π_σ ∘ coefLast` (`PeriodTarget.br`), `tz = π_T`. -/
def sharpBr (u : S.A) :
    Pol (Φ S.A) (rowN Dg + 1) (sharpCoeff Dg).K →ₗ[(sharpCoeff Dg).K] Pol (Φ S.A) (rowN Dg) (sharpCoeff Dg).K :=
  PeriodTarget.br (sharpCoeff Dg).τK (sharpTz Dg u : S.E) (sharpPr Dg u)
    (PeriodTarget.brConst _ (sharpLamM Dg u) (sharpσ Dg u)) (sharpLamM Dg u) (sharpσ Dg u)

/-- **The period data of the translate** (`perU`): `tz = π_T`, the row weight `sharpσ`, the branching map `sharpBr`,
the lattice `N_x` of a row point, all rows, and the column `sharpCol`. -/
def sharpPer (u : S.A) :
    PeriodTarget.PerData (Φ S.A) (rowN Dg) S.E (sharpCoeff Dg).K (fun _ : Unit => RowG Dg)
      (fun _ : Unit => RowPt Dg) (fun _ : Unit => sharpVs Dg u) :=
  perU (sharpTz Dg u : S.E) (sharpσ Dg u) (sharpBr Dg u) (fun x => x.1.N) (sharpCol Dg u)

/-- **The twist data**: no twisted place (`Tw = ∅`), identity transfers, scalars `1` (Stage U). -/
def sharpTw (u : S.A) : PeriodTarget.Twist (sharpPer Dg u) () where
  Tw := ∅
  μw _ := ()
  tr _ := LinearMap.id
  ze _ _ := 1

/-- **The object of the translate `u`** (`SharpObj`), Stage U: one word and one level (`Unit`), the row group and
points, the auxiliary prime `sharpT`, the places `sharpST`, `sharpSG`, the step-0 data (`n0 = k`, `sharpLam0`,
`sharpχ0`, `X_c = ⊤`, `V_ω = sharpVs`, `e = id`), the period data `sharpPer` of the explicit chain with the twist
`sharpTw`; the archive's forced orders `Fo = ForcedOrders.Fo` (family `hc u`, twist `twA κ`, cut-off `cutX x ε`); the
slacks `c_F = c_G = x^{4ε}Σ_t a_t/8`, `c↑ = x^{4ε}Σ_t a_t/4`, `c_T = 0` and the frame loss `x^{4ε}Σ_t a_t/4`.
Placeholders, to be set by the gain and (G↑): `𝔞⁺ = 𝔞⁻ = ⊤`, the target metric `g = 0` and the heights `0`. -/
def sharpObj (u : S.A) : SharpObj Dg (sharpCoeff Dg) where
  Ω := Unit
  T _ := sharpT Dg u
  Tμ := Unit
  G _ := RowG Dg
  Xp _ := RowPt Dg
  Vs _ := sharpVs Dg u
  tower _ := Submodule.isScalarTower' _
  ST _ := sharpST Dg u
  SG := sharpSG Dg
  P := sharpPer Dg u
  μ0 := ()
  tw := sharpTw Dg u
  𝔞p _ := ⊤
  𝔞n _ := ⊤
  n0 := Dg.R.k
  lam0 _ := sharpLam0 Dg u
  χ0 _ := sharpχ0 Dg
  Xc _ := ⊤
  e _ := LinearEquiv.refl _ _
  g _ _ _ := 0
  ht _ _ := 0
  Fo := Dg.R.Fo (Dg.hc u) (S.twA κ) Dg.g₀ Dg.g₁ (S.cutX x ε)
  loss := x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 4
  cF := x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8
  cG := x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 8
  cUp := x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 4
  cT := 0

/-- **The construction of a design** (the field `SharpPieces.cons`): the coefficient field `sharpCoeff` of the
chain and the object `sharpObj` of every translate. -/
def sharpCons : SharpCons Dg := ⟨sharpCoeff Dg, sharpObj Dg⟩

end Obj

end

end ZetaBalance
