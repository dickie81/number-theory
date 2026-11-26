import ThetaVol

/-!
# The Heisenberg data and the determinant ideles of the chain

The finite data of the explicit theta chain's steps (chain spec §2, §3.5; the C1c row of its module plan) as closed
definitions: the coset integers, the half-lattice of the lifts, the lattice `BC`, the representatives `SA`, `SB` and
the volume of the coset thetas (`ThetaChain.XiData`), and the determinant ideles of the classes, from a choice `sel` of
half the split places. Everything is generic in the step's lattices `N ⊂ E^a`, `N′ ⊂ E^b`, the place set `S` and the
integers `cA`, `cB`; the Stage-U chain reads it at `S = ST ∪ SG`, at the lattices of the classes and of the row points.

**Coset integers.** `cA = (∏_{P ∈ SG} N(P))^{m+1}` and `cB = T·cA` (`cAU`, `cBU`), the same at every step.

**Heisenberg data.** With `M = perO(𝔄, N, N′) = O_E·𝔄·Hom(N, N′)`, the coset points are lifted into
`HA = halfAO(S, M, cA·cB)` (`haU`), and the finite Heisenberg sum transforms the indicator of
`BC = ι(halfBO(S, M, cB))`. The half-lattices (`ThetaChain.twist₂`) are additive groups (`twGrp`), so the additive map
`ι` (`iotaHom`) carries them to subgroups `AC = ι(HA)` and `BC` of the ambient space (`acGrp`, `bcGrp`). With
`Λ = La(N, N′) = ι(M)`, `SA` represents `(Λ ∩ AC)/(Λ ∩ AC ∩ BC)` and `SB` represents `BC/(BC ∩ Λ)`: each is the `Finset`
of the `Quotient.out` images of the classes, with `0` for the zero class (`repOut`, `repsOf`; empty if the quotient is
infinite). The volume is `volS(S, perO(std, std′), M)`. Together these are `xdU`, and they are the values that
`ThetaChain.XDPin` pins whenever the two quotients are finite (`xdPin_xdU`); `|SA|` is the index (`card_repsOf`). The
coset theta does not depend on the representatives (the semicharacter makes `U_x` invariant modulo the lattice), so
the `Quotient.out` choices are harmless.

**The choice `sel`.** `sel` contains `SG`, no self-conjugate place, and exactly one place `w` out of every pair
`{w, w̄}` with `w ≠ w̄` (`IsSel`, with the conjugate place `w̄ = conj⁻¹(w)`, `conjPl`, the `P̄` of `ThetaChain.expS`).
`selU` is an `ε` on this property. **The parity rule** (the D1 study, Q3 and R5), fixed here once for the chain, D0
and D2. It reads the embeddings of the CM type at an inert prime `ℓ`, `f = ι ∘ σ₀ ∘ τ_p` (`p ∈ Φ`, `ι : ℂ ≃ ℂ_ℓ`),
the positions that carry the weights `e_p`: `f` counts as **even** when the place of `E` it induces,
`{x ∈ O_E : ‖f x‖ < 1}`, lies in `sel`, and as **odd** otherwise (`EvenPos`), and then its conjugate `f ∘ conj ∈ Φ̄`
induces the place of `sel` (`induces_comp_conj`: `f ∘ conj` induces `w̄`). So in the orbit on the `sel` side of a split
pair the even positions are embeddings of `Φ` and the odd ones conjugates of embeddings of `Φ` (the d1 spec's "even
in `Φ`, odd in `Φ̄`"); of two conjugate embeddings at most one is even (`not_evenPos_comp_conj`), and exactly one at a
split place (`evenPos_or_comp_conj`). With this rule `v(μ_{0,j}(ϖ_w)) = Σ_{even} e_p − Σ_{odd} e_p` at `w ∈ sel`, the
valuation of D2's scalars `m_l`; switching `sel` at a pair would flip its sign, so every consumer reads this `sel`.
The predicate is not the orbit parity of an arbitrary embedding: an embedding of `Φ̄` on the `sel` side induces a
place of `sel` but sits at an odd position.

**The determinant ideles.** For a lattice `N ⊂ E^a` with frames `fr` at the places of `SF`, the idele `dIU` has the
component `det fr_P` at `P ∈ SF`, `ϖ_w^{v_w(det N)}` at `w ∈ sel \ SF`, and `1` elsewhere: at the conjugates of `sel`
and at the self-conjugate places (`detComp`; the archive's `muOff`, the predicate `SharpChain.IsDetIdele`). Here
`v_w(det N)` is the least `v_w(det f)` over `f ∈ N^a` with `det f ≠ 0` (`detOrd`), and `ϖ_w ∈ E` a uniformiser at `w`
(`unif`, an `ε`: the lift characters are unramified away from `SG`, so the uniformisers do not matter; `sel` does). An
idele is built from a nonzero family that is `1` almost everywhere (`IsIdeleFam`) by `ideleOf` (`1` otherwise), whose
components are the family's (`ideleOf_apply`); the family of `dIU` is one when the frames are invertible and
`v_w(det N) = 0` at almost every `w ∈ sel` (`isIdeleFam_detComp`). The idele of a class (`dICls`) reads its lattice
and its frames (`ThetaChain.DecoF.frAt`) at `SF = SG ∪ Q`.

**Main declarations** (read by the Stage-U chain, C1e): `cAU`, `cBU`, `haU`, `xdU`, `IsSel`, `selU`, `dIU`, `dICls`;
`EvenPos` (the parity rule, for D0 and D2).

**Sanity theorems:** `isReps_repsOf`, `zero_mem_repsOf`, `card_repsOf`, `xdPin_xdU`, `unif_spec`, `ideleOf_apply`,
`isIdeleFam_detComp`, `not_evenPos_comp_conj`, `evenPos_or_comp_conj`.
-/

namespace ChainHeis

open NumberField IsDedekindDomain ThetaChain HermClasses WeylFock

noncomputable section

/-! ## Coset integers and representatives -/

section Reps

/-- **The coset integer `cA = (∏_{P ∈ SG} N(P))^{m+1}`** of every step, `m` the length of the chain (the depth
`A = m + 1` of the local factors). -/
def cAU {E : Type*} [Field E] [NumberField E] (SG : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : ℕ :=
  (∏ P ∈ SG, Ideal.absNorm P.asIdeal) ^ (m + 1)

/-- **The coset integer `cB = T·cA`**, `T` the auxiliary prime of the translate. -/
def cBU {E : Type*} [Field E] [NumberField E] (T : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : ℕ :=
  T * cAU SG m

variable {X : Type*} [AddCommGroup X]

open Classical in
/-- **The representative of a class** `q ∈ Λ₂/(Λ₁ ∩ Λ₂)`: `0` for the zero class, `Quotient.out` otherwise. -/
def repOut (Λ₁ Λ₂ : AddSubgroup X) (q : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂) : X :=
  if q = 0 then 0 else ((q.out : Λ₂) : X)

open Classical in
/-- **The representatives of `Λ₂/(Λ₁ ∩ Λ₂)`**: the `Finset` of the `repOut` images when there are finitely many, `∅`
otherwise (so the definition carries no proof). -/
def repsOf (Λ₁ Λ₂ : AddSubgroup X) : Finset X :=
  if h : (Set.range (repOut Λ₁ Λ₂)).Finite then h.toFinset else ∅

variable (Λ₁ Λ₂ : AddSubgroup X)

/-- **The representative lies in `Λ₂`.** -/
theorem repOut_mem (q : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂) : repOut Λ₁ Λ₂ q ∈ Λ₂ := by
  unfold repOut
  split_ifs
  exacts [zero_mem _, (q.out).2]

/-- **The representative represents its class.** -/
theorem mk_repOut (q : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂) :
    (QuotientAddGroup.mk ⟨repOut Λ₁ Λ₂ q, repOut_mem Λ₁ Λ₂ q⟩ : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂) = q := by
  by_cases hq : q = 0
  · subst hq
    simp only [repOut]
    rfl
  · simp only [repOut, ite_eq_right hq]
    exact QuotientAddGroup.out_eq' q

/-- **Membership in `repsOf`** when the quotient is finite: the images of `repOut`. -/
theorem mem_repsOf (h : (Λ₁ ⊓ Λ₂).relIndex Λ₂ ≠ 0) {x : X} : x ∈ repsOf Λ₁ Λ₂ ↔ ∃ q, repOut Λ₁ Λ₂ q = x := by
  have : ((Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂).FiniteIndex := ⟨h⟩
  simp [repsOf, Set.finite_range]

/-- **`repsOf` is a set of representatives** (`ThetaChain.IsReps`) of `Λ₂/(Λ₁ ∩ Λ₂)` when the index is finite. -/
theorem isReps_repsOf {ι : Type*} [Fintype ι] (Λ₁ Λ₂ : AddSubgroup (ι → ℂ)) (h : (Λ₁ ⊓ Λ₂).relIndex Λ₂ ≠ 0) :
    IsReps (Λ₁ : Set (ι → ℂ)) Λ₂ (repsOf Λ₁ Λ₂) := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · obtain ⟨q, rfl⟩ := (mem_repsOf Λ₁ Λ₂ h).1 hx
    exact repOut_mem Λ₁ Λ₂ q
  · obtain ⟨q, rfl⟩ := (mem_repsOf Λ₁ Λ₂ h).1 hx
    obtain ⟨q', rfl⟩ := (mem_repsOf Λ₁ Λ₂ h).1 hy
    congr 1
    rw [← mk_repOut Λ₁ Λ₂ q, ← mk_repOut Λ₁ Λ₂ q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa [neg_add_eq_sub] using Λ₁.neg_mem hxy
    · exact Λ₂.add_mem (Λ₂.neg_mem (repOut_mem Λ₁ Λ₂ q)) (repOut_mem Λ₁ Λ₂ q')
  · set q : Λ₂ ⧸ (Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂ := QuotientAddGroup.mk ⟨y, hy⟩
    refine ⟨repOut Λ₁ Λ₂ q, (mem_repsOf Λ₁ Λ₂ h).2 ⟨q, rfl⟩, ?_⟩
    have hq := mk_repOut Λ₁ Λ₂ q
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hq
    simpa [neg_add_eq_sub] using (AddSubgroup.mem_inf.1 hq).1

/-- **`0` is the representative of the zero class** (as `ThetaChain.XDPin` asks of `SA`). -/
theorem zero_mem_repsOf (h : (Λ₁ ⊓ Λ₂).relIndex Λ₂ ≠ 0) : (0 : X) ∈ repsOf Λ₁ Λ₂ :=
  (mem_repsOf Λ₁ Λ₂ h).2 ⟨0, by simp [repOut]⟩

/-- **There are `[Λ₂ : Λ₁ ∩ Λ₂]` representatives** (the `|SA|` of the Fourier transform `ThetaChain.hatS`). -/
theorem card_repsOf (h : (Λ₁ ⊓ Λ₂).relIndex Λ₂ ≠ 0) : (repsOf Λ₁ Λ₂).card = (Λ₁ ⊓ Λ₂).relIndex Λ₂ := by
  have : ((Λ₁ ⊓ Λ₂).addSubgroupOf Λ₂).FiniteIndex := ⟨h⟩
  have hinj : Function.Injective (repOut Λ₁ Λ₂) := fun q q' hqq' => by
    rw [← mk_repOut Λ₁ Λ₂ q, ← mk_repOut Λ₁ Λ₂ q']
    congr 2
  have hfin : (Set.range (repOut Λ₁ Λ₂)).Finite := Set.finite_range _
  rw [repsOf, dite_eq_left hfin, ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq,
    Nat.card_range_of_injective hinj]
  rfl

end Reps

/-! ## The Heisenberg data of a step -/

section Heis

variable {E L : Type*} [Field E] [NumberField E] [IsCMField E] [Field L] {Φ : Type*} [Fintype Φ]
  (τ : Φ → (E →+* L)) (P : TP E L Φ) {a b : ℕ}

/-- **`ι` is additive**: `x ↦ (δ·σ₀(τ_p(x)))_p` as a homomorphism `M_{b×a}(E) → Amb Φ a b`. -/
def iotaHom : Matrix (Fin b) (Fin a) E →+ Amb Φ a b where
  toFun := iota τ P
  map_zero' := funext fun p => by simp [iota]
  map_add' x y := funext fun p => by simp [iota, mul_add]

/-- **The twisted lattice `twist₂(M, c, e)` as an additive group** (an intersection of preimages of the
localisations `M_(Q)` under the additive maps `w ↦ c^{−e(Q)}·w`). -/
def twGrp (M : Submodule (𝓞 E) (Matrix (Fin b) (Fin a) E)) (c : E) (ex : HeightOneSpectrum (𝓞 E) → ℤ) :
    AddSubgroup (Matrix (Fin b) (Fin a) E) where
  carrier := twist₂ M c ex
  add_mem' {x y} hx hy Q := by
    rw [smul_add]
    exact add_mem (hx Q) (hy Q)
  zero_mem' Q := by
    rw [smul_zero]
    exact zero_mem _
  neg_mem' {x} hx Q := by
    rw [smul_neg]
    exact neg_mem (hx Q)

variable (S : Set (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (N : Submodule (𝓞 E) (Fin a → E))
  (N' : Submodule (𝓞 E) (Fin b → E))

/-- **The half-lattice of the lifts** `HA = halfAO(S, perO(𝔄, N, N′), cA·cB)`: `(cA cB)⁻¹M` at the places of `S`,
`cA cB·M` at their conjugates, `M` elsewhere. -/
def haU : Set (Matrix (Fin b) (Fin a) E) :=
  halfAO S (perO P.A N N') ((cA * cB : ℕ) : E)

/-- **`AC = ι(HA)`** as a subgroup of the ambient space. -/
def acGrp : AddSubgroup (Amb Φ a b) :=
  (twGrp (perO P.A N N') ((cA * cB : ℕ) : E) fun Q => -expS S Q).map (iotaHom τ P)

/-- **`BC = ι(halfBO(S, perO(𝔄, N, N′), cB))`** as a subgroup of the ambient space: `cB·M` at the places of `S`,
`cB⁻¹M` at their conjugates, `M` elsewhere. -/
def bcGrp : AddSubgroup (Amb Φ a b) :=
  (twGrp (perO P.A N N') (cB : E) (expS S)).map (iotaHom τ P)

/-- **The finite Heisenberg data of a step** from `N` to `N′`: `SA` represents `(Λ ∩ AC)/(Λ ∩ AC ∩ BC)`, `SB`
represents `BC/(BC ∩ Λ)` (`Λ = La(N, N′)`), `BC = ι(halfBO(S, M, cB))` and `vol = volS(S, perO(std, std′), M)`,
`M = perO(𝔄, N, N′)` (the values of `ThetaChain.XDPin`, `xdPin_xdU`). -/
def xdU : XiData (Φ × Fin b × Fin a) where
  SA := repsOf (bcGrp τ P S cB N N') (La τ P N N' ⊓ acGrp τ P S cA cB N N')
  SB := repsOf (La τ P N N') (bcGrp τ P S cB N N')
  BC := iota τ P '' halfBO S (perO P.A N N') (cB : E)
  vol := volS S (perO P.A (stdLat (E := E) (n := a)) (stdLat (E := E) (n := b))) (perO P.A N N')

/-- **The explicit Heisenberg data are the pinned ones** (`ThetaChain.XDPin` with the half-lattice `haU`), whenever the
two quotients `(Λ ∩ AC)/(Λ ∩ AC ∩ BC)` and `BC/(BC ∩ Λ)` are finite (C2: `M` is a lattice and `cA`, `cB ≠ 0`). -/
theorem xdPin_xdU
    (hA : (bcGrp τ P S cB N N' ⊓ (La τ P N N' ⊓ acGrp τ P S cA cB N N')).relIndex
      (La τ P N N' ⊓ acGrp τ P S cA cB N N') ≠ 0)
    (hB : (La τ P N N' ⊓ bcGrp τ P S cB N N').relIndex (bcGrp τ P S cB N N') ≠ 0) :
    XDPin τ P S cA cB N N' (xdU τ P S cA cB N N') (haU P S cA cB N N') := by
  have eB : (bcGrp τ P S cB N N' : Set (Amb Φ a b)) = (xdU τ P S cA cB N N').BC := AddSubgroup.coe_map _ _
  have eA : ((La τ P N N' ⊓ acGrp τ P S cA cB N N' : AddSubgroup (Amb Φ a b)) : Set (Amb Φ a b)) =
      (La τ P N N' : Set (Amb Φ a b)) ∩ iota τ P '' haU P S cA cB N N' := by
    rw [AddSubgroup.coe_inf, acGrp, AddSubgroup.coe_map]
    rfl
  refine ⟨rfl, rfl, ?_, zero_mem_repsOf _ _ hA, ?_, rfl⟩
  · rw [← eB, ← eA]
    exact isReps_repsOf _ _ hA
  · rw [← eB]
    exact isReps_repsOf _ _ hB

end Heis

/-! ## The choice `sel` and the parity rule -/

section Sel

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- **`conj⁻¹(w) ≠ 0`**: it contains `conj x` for every `x ∈ w`. -/
theorem comap_conj_ne_bot (w : HeightOneSpectrum (𝓞 E)) :
    w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) ≠ ⊥ := fun h => by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hc : IsCMField.ringOfIntegersComplexConj E x ∈ w.asIdeal.comap
      (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) := by
    rw [Ideal.mem_comap]
    convert hx using 1
    exact RingOfIntegers.ext (IsCMField.complexConj_apply_apply _ _)
  rw [h, Ideal.mem_bot, map_eq_zero_iff _ (IsCMField.ringOfIntegersComplexConj E).injective] at hc
  exact hx0 hc

/-- **The conjugate place** `w̄ = conj⁻¹(w)` on `O_E` (the place `ThetaChain.expS` reads as `P̄`). -/
def conjPl (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := comap_conj_ne_bot w

/-- **`sel` chooses half the split places**: it contains `SG`, no self-conjugate place, and exactly one place of
every pair `{w, w̄}` with `w ≠ w̄`. -/
def IsSel (SG : Finset (HeightOneSpectrum (𝓞 E))) (sel : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ↑SG ⊆ sel ∧ (∀ w ∈ sel, conjPl w ≠ w) ∧ ∀ w, conjPl w ≠ w → (w ∈ sel ↔ conjPl w ∉ sel)

/-- **The choice `sel`** (an `ε` on `IsSel`; its existence, for `SG` split with no conjugate pair, is for C2). It
fixes the parity of the positions (`EvenPos`) and the determinant ideles (`dIU`). -/
def selU (SG : Finset (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 E)) :=
  Classical.epsilon (IsSel SG)

/-- **The parity rule** (the D1 study, Q3 and R5), for an embedding `f : E → K` of the CM type into a normed field
(`f = ι ∘ σ₀ ∘ τ_p`, `p ∈ Φ`, at an inert prime: the position carrying the weight `e_p`): `f` is **even** when the
place of `E` it induces, `{x ∈ O_E : ‖f x‖ < 1}`, is a place of `sel`, and **odd** otherwise (then `f ∘ conj` sits at
an odd position on the `sel` side). D0 and D2 read their positions by this rule, so that
`v(μ_{0,j}(ϖ_w)) = Σ_{even} e_p − Σ_{odd} e_p` at `w ∈ sel`. Read on embeddings of `Φ` only. -/
def EvenPos {K : Type*} [NormedField K] (sel : Set (HeightOneSpectrum (𝓞 E))) (f : E →+* K) : Prop :=
  ∃ w ∈ sel, ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ ‖f x‖ < 1

variable {K : Type*} [NormedField K]

/-- **`f ∘ conj` induces `w̄`** when `f` induces `w`. -/
theorem induces_comp_conj {f : E →+* K} {w : HeightOneSpectrum (𝓞 E)} (hw : ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ ‖f x‖ < 1)
    (x : 𝓞 E) : x ∈ (conjPl w).asIdeal ↔ ‖f.comp (IsCMField.complexConj E : E →+* E) x‖ < 1 := by
  change _ ∈ w.asIdeal ↔ _
  rw [hw]
  simp

/-- **Conjugate positions are not both even**: if `f` is even, `f ∘ conj` (which induces `w̄`) is odd. -/
theorem not_evenPos_comp_conj {SG : Finset (HeightOneSpectrum (𝓞 E))} {sel : Set (HeightOneSpectrum (𝓞 E))}
    (hs : IsSel SG sel) {f : E →+* K} (hf : EvenPos sel f) :
    ¬ EvenPos sel (f.comp (IsCMField.complexConj E : E →+* E)) := by
  obtain ⟨w, hw, hfw⟩ := hf
  rintro ⟨w', hw', hfw'⟩
  have hc : w' = conjPl w := HeightOneSpectrum.ext (Ideal.ext fun x => (hfw' x).trans (induces_comp_conj hfw x).symm)
  subst hc
  exact (hs.2.2 w (hs.2.1 w hw)).1 hw hw'

/-- **At a split place one of two conjugate positions is even**: if `f` induces `w ≠ w̄`, then `f` or `f ∘ conj` is
even (exactly one, by `not_evenPos_comp_conj`). -/
theorem evenPos_or_comp_conj {SG : Finset (HeightOneSpectrum (𝓞 E))} {sel : Set (HeightOneSpectrum (𝓞 E))}
    (hs : IsSel SG sel) {f : E →+* K} {w : HeightOneSpectrum (𝓞 E)} (hw : ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ ‖f x‖ < 1)
    (hsp : conjPl w ≠ w) : EvenPos sel f ∨ EvenPos sel (f.comp (IsCMField.complexConj E : E →+* E)) := by
  by_cases h : w ∈ sel
  · exact Or.inl ⟨w, h, hw⟩
  · exact Or.inr ⟨conjPl w, not_not.1 (mt (hs.2.2 w hsp).2 h), induces_comp_conj hw⟩

end Sel

/-! ## The determinant ideles -/

section Idele

variable {E : Type*} [Field E] [NumberField E]

/-- **A uniformiser at `w`** in `E` (an `ε`): `v_w(ϖ_w) = 1` (`unif_spec`). -/
def unif (w : HeightOneSpectrum (𝓞 E)) : E :=
  Classical.epsilon fun π : E => w.valuation E π = WithZero.exp (-1 : ℤ)

/-- **It is a uniformiser.** -/
theorem unif_spec (w : HeightOneSpectrum (𝓞 E)) : w.valuation E (unif w) = WithZero.exp (-1 : ℤ) :=
  Classical.epsilon_spec (w.valuation_exists_uniformizer E)

/-- **`v_w(det N)`**: the least `v_w(det f)` (`ThetaVol.vP`) over the `f ∈ N^a` with `det f ≠ 0`, the columns of `f`
the vectors (as in `SharpChain.IsDetIdele`); `sInf` in `ℤ`, so `0` when there is no least one. -/
def detOrd (w : HeightOneSpectrum (𝓞 E)) {a : ℕ} (N : Submodule (𝓞 E) (Fin a → E)) : ℤ :=
  sInf {k | ∃ f : Fin a → N, (Matrix.of fun i l => (f l : Fin a → E) i).det ≠ 0 ∧
    ThetaVol.vP w (Matrix.of fun i l => (f l : Fin a → E) i).det = k}

open Classical in
/-- **The components of the determinant idele** of a lattice `N` with frames `fr` at the places of `SF`: `det fr_P`
at `P ∈ SF`, `ϖ_w^{v_w(det N)}` at `w ∈ sel \ SF`, `1` elsewhere (the conjugates of `sel`, the self-conjugate
places). -/
def detComp (sel : Set (HeightOneSpectrum (𝓞 E))) (SF : Finset (HeightOneSpectrum (𝓞 E))) {a : ℕ}
    (N : Submodule (𝓞 E) (Fin a → E)) (fr : HeightOneSpectrum (𝓞 E) → Matrix (Fin a) (Fin a) E)
    (w : HeightOneSpectrum (𝓞 E)) : E :=
  if w ∈ SF then (fr w).det else if w ∈ sel then unif w ^ detOrd w N else 1

/-- **A family of components of an idele**: nonzero everywhere and `1` at almost every place. -/
def IsIdeleFam (x : HeightOneSpectrum (𝓞 E) → E) : Prop :=
  (∀ w, x w ≠ 0) ∧ {w | x w ≠ 1}.Finite

/-- **The components are almost everywhere integral**, with their inverses. -/
theorem IsIdeleFam.eventually {x : HeightOneSpectrum (𝓞 E) → E} (h : IsIdeleFam x) (k : ℤ) :
    ∀ᶠ w in Filter.cofinite, algebraMap E (w.adicCompletion E) (x w ^ k) ∈ w.adicCompletionIntegers E :=
  (Filter.eventually_cofinite.2 (by simpa using h.2)).mono fun w (hw : x w = 1) => by simp [hw]

/-- **The adeles with components `x` and `x⁻¹` are inverse.** -/
theorem IsIdeleFam.mul_inv {x : HeightOneSpectrum (𝓞 E) → E} (h : IsIdeleFam x) :
    (show FiniteAdeleRing (𝓞 E) E from ⟨fun w => algebraMap E (w.adicCompletion E) (x w ^ (1 : ℤ)), h.eventually 1⟩) *
      (show FiniteAdeleRing (𝓞 E) E from
        ⟨fun w => algebraMap E (w.adicCompletion E) (x w ^ (-1 : ℤ)), h.eventually (-1)⟩) = 1 :=
  FiniteAdeleRing.ext E fun w => by
    change algebraMap E (w.adicCompletion E) (x w ^ (1 : ℤ)) * algebraMap E (w.adicCompletion E) (x w ^ (-1 : ℤ)) = 1
    rw [← map_mul, zpow_one, zpow_neg_one, mul_inv_cancel₀ (h.1 w), map_one]

open Classical in
/-- **The idele with components `x`** (`ideleOf_apply`), `1` if `x` is not a family of components. -/
def ideleOf (x : HeightOneSpectrum (𝓞 E) → E) : Ideles E :=
  if h : IsIdeleFam x then Units.mkOfMulEqOne _ _ (IsIdeleFam.mul_inv h) else 1

/-- **The components of `ideleOf x`** are those of `x`. -/
theorem ideleOf_apply {x : HeightOneSpectrum (𝓞 E) → E} (h : IsIdeleFam x) (w : HeightOneSpectrum (𝓞 E)) :
    ((ideleOf x : Ideles E) : FiniteAdeleRing (𝓞 E) E) w = algebraMap E (w.adicCompletion E) (x w) := by
  rw [ideleOf, dite_eq_left h]
  change algebraMap E (w.adicCompletion E) (x w ^ (1 : ℤ)) = _
  rw [zpow_one]

/-- **The determinant idele** of a lattice `N` with frames `fr` at the places of `SF` (the archive's `muOff`; the
`SharpChain.IsDetIdele` of `N`): `ideleOf` of `detComp`. -/
def dIU (sel : Set (HeightOneSpectrum (𝓞 E))) (SF : Finset (HeightOneSpectrum (𝓞 E))) {a : ℕ}
    (N : Submodule (𝓞 E) (Fin a → E)) (fr : HeightOneSpectrum (𝓞 E) → Matrix (Fin a) (Fin a) E) : Ideles E :=
  ideleOf (detComp sel SF N fr)

/-- **The components of `dIU` form an idele** when the frames are invertible and `v_w(det N) = 0` at almost every
`w ∈ sel` (C2, for the lattices of the chain). -/
theorem isIdeleFam_detComp {sel : Set (HeightOneSpectrum (𝓞 E))} {SF : Finset (HeightOneSpectrum (𝓞 E))} {a : ℕ}
    {N : Submodule (𝓞 E) (Fin a → E)} {fr : HeightOneSpectrum (𝓞 E) → Matrix (Fin a) (Fin a) E}
    (hfr : ∀ P ∈ SF, (fr P).det ≠ 0) (hN : {w | w ∈ sel ∧ detOrd w N ≠ 0}.Finite) :
    IsIdeleFam (detComp sel SF N fr) := by
  classical
  refine ⟨fun w => ?_, (SF.finite_toSet.union hN).subset fun w hw => ?_⟩
  · have hu : unif w ≠ 0 := fun h0 => WithZero.exp_ne_zero ((unif_spec w).symm.trans (by rw [h0, map_zero]))
    unfold detComp
    split_ifs with h1 h2
    exacts [hfr w h1, zpow_ne_zero _ hu, one_ne_zero]
  · by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    apply hw
    unfold detComp
    rw [ite_eq_right hc.1]
    split_ifs with h2
    · rw [hc.2 h2, zpow_zero]
    · rfl

variable [IsCMField E]

open Classical in
/-- **The determinant idele of a class** `c`: `dIU` of its lattice `N_c` with the frames of its representative
(`ThetaChain.DecoF.frAt`: frame lifts at `SG`, lattice frames at `Q`) at `SF = SG ∪ Q`. -/
def dICls (sel : Set (HeightOneSpectrum (𝓞 E))) {n : ℕ → ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {β : ℕ → Type} {Λ : ∀ j, β j → Subgroup ((∀ w : SG, GL (Fin (n j)) (𝓞 E ⧸ w.1.asIdeal)) × ∀ w : Q, glInt (n j) w.1)}
    {j : ℕ} (c : Cls n ST SG Q β Λ j) : Ideles E :=
  dIU sel (SG ∪ Q) c.2.N c.2.rep.frAt

end Idele

end

end ChainHeis
