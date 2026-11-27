import SharpNI
import SharpTarget
import RowsLattice
import SharpInterlace
import BranchConst

/-!
# The frame of the construction, from (NI)

The piece `SharpPieces.frame` of the proof's architecture (`SharpInputs`), for the construction `sharpCons` with
`adm := fun Dg => Dg.Adm`, conditional on (NI) (`SharpNI`, which the frame loss needs too): eventually in the design,
at every translate `u ∈ A₀`, some frame realises the construction's object (`frame_of_sharpNI`). (NI) is used only for
`W_u ≠ 0`: the target of a frame lives in `K^κ` with `κ` nonempty (`FrameOn.nonempty`), and `κ` must index
coordinates of `W_u`. Every other fact is proved, with no input.

**The frame of an object of one word** `ω` (`SharpObj.frameExists_of`), at Stage U, with the quotient target metric
(`SharpObj.gQuot`) and heights `0`:
* *coordinates*: `c = ` Mathlib's basis of the source `V_ω`, and `eC = quotCoord P` on the target, a left inverse
  of the inclusion of `W_u = range P` followed by Mathlib's basis of `W_u`;
* *sources*: `N_ω` in coordinates, with the Gram matrix of the Petersson form in the basis (`SharpTarget.petGram`),
  positive definite (`HermForms.posDef_petAt`: the Gram matrix of the cut's basis, `HermForms.gram_posDef`,
  conjugated by the change of basis, `HermForms.petAt_sum_smul`);
* *target*: `C_u` in coordinates, with the quotient Gram matrix (`SharpTarget.quotGram`), positive definite
  (`quotGram_spec`), so the target-metric clause of `SharpObj.RealWith` holds by definition (`quotMetric_eq`);
* *maps*: `B_ω = eC ∘ P ∘ c⁻¹`, so `B_ω(N_ω) ⊆ C_u` is the definition of `N_ω` (`PeriodTarget.Nsrc`), and `B_ω` is a
  co-isometry from the Petersson metric to the quotient one (`KLattice.norm_hom_le_of_coisometry`), bounded by
  `e^0`.

**The lattices.**
* `M_ω` is an `O_K`-lattice (`HermForms.isLattice_span_Mω`).
* The periods are `K`-linear on the rows (`exists_linearMap_of_mem_W`: `P(φ, F) = Σ_c mass(c)·pair(br(Φ(rep c)), F(c))`
  is linear in `F`). So, when the integral rows lie in a finitely generated `O_K`-module `Lm`, every period has a
  nonzero integer multiple integral on them, that is in `C_u` at Stage U (`exists_int_smul_mem_Ctgt`: an integer
  clearing the denominators of the period on the generators of `Lm`).
* When the rows also span `V0`, `C_u` is finitely generated (`fg_Ctgt`): the `O_K`-span of the rows has finitely many
  generators `r_i`, still spanning `V0`, and `f ↦ (f(r_i))_i` maps `C_u` into `O_K^{r}` with no kernel on `W_u`.
* `N_ω` is an `O_K`-lattice for nonzero `𝔞⁺`, `𝔞⁻` (`isLattice_N`): `a·N_ω ⊆ 𝔞⁻M_ω ⊆ M_ω` for a nonzero `a ∈ 𝔞⁺`,
  and for `m ∈ M_ω` and a nonzero `c ∈ 𝔞⁻`, some nonzero integer multiple of `c·m` has its period in `C_u`.

**The construction** (`frame_of_sharpNI`): one word, `Tw = ∅`, `𝔞⁺ = 𝔞⁻ = ⊤`, antitone step-0 weights
(`Setting.Ranks.wt0_antitone`), the quotient metric and heights `0` by definition. Its integral rows, all
`VV(σ)`-valued rows over the finitely many classes of row points (`HermClasses.finite_DCl`), span `V0` and lie in a
finitely generated module (`HermForms.rows_span`, `HermForms.rows_fg`), as the row weight `σ` is antitone
(`sharpσ_antitone`, from the interlacing `SharpDesign.PinnedTo.interlace`) and the lattices of row points are
unimodular (`HermForms.exists_sand_of_unimodular`). (NI) gives `0 < rk P`.
-/

namespace HermForms

open NumberField IsDedekindDomain HermClasses WeylFock

open scoped ComplexOrder Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))} {Φ : Type} [Fintype Φ] [DecidableEq Φ] {L : Type}
  [Field L] [NumberField L] (τ : Φ → (E →+* L)) (χ : Λ →* L) (lam : Φ → Fin n → ℤ)

omit [NumberField L] in
/-- **The Petersson form is positive definite on every independent family of the cut** `V_ω`: in the cut's basis
`b`, `F_i = Σ_k Q_{ki} b_k` with `Q` injective, so the Gram matrix of the `F_i` at `σ` is `σ(Q)ᴴ·gram_σ·σ(Q)`
(`petAt_sum_smul`), and `gram_σ` is positive definite (`gram_posDef`). -/
theorem posDef_petAt [FiniteDimensional L (Vω ST τ χ lam)] {ι : Type} [Fintype ι] {F : ι → Vω ST τ χ lam}
    (hF : LinearIndependent L F) (σ : L →+* ℂ) :
    (Matrix.of fun i j => petAt ST lam σ (F i : Fn ST Λ Φ L) (F j)).PosDef := by
  classical
  set bV := Module.finBasis L (Vω ST τ χ lam)
  set Q : Matrix (Idx ST τ χ lam) ι L := fun k i => bV.repr (F i) k
  have hFQ : ∀ i, (F i : Fn ST Λ Φ L) = ∑ k, Q k i • (bV k : Fn ST Λ Φ L) := fun i => by
    conv_lhs => rw [← bV.sum_repr (F i)]
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun k _ => Submodule.coe_smul _ _
  have hQ : Function.Injective Q.mulVec := fun y z hyz => by
    have h0 : ∑ i, (y i - z i) • F i = 0 := bV.repr.injective (Finsupp.ext fun k => by
      have := congrFun hyz k
      simp only [Matrix.mulVec, dotProduct, Q] at this
      simp [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      simpa only [mul_comm] using this)
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hF _ h0 i)
  have hG : (Matrix.of fun i j => petAt ST lam σ (F i : Fn ST Λ Φ L) (F j)) =
      (Q.map σ)ᴴ * gram ST τ χ lam σ * Q.map σ := by
    ext i j
    rw [Matrix.of_apply, hFQ i, hFQ j, petAt_sum_smul]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, RCLike.star_def]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by simp only [gram, Hω]; ring
  rw [hG]
  exact (gram_posDef ST τ χ lam σ).conjTranspose_mul_mul_same (mulVec_map_injective σ hQ)

end HermForms

namespace ZetaBalance

open NumberField HermitianLattice Module

open scoped ComplexOrder Matrix

noncomputable section

namespace SharpObj

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}
  {b : SharpObj Dg C}

/-! ## The lattices of the frame -/

/-- **The periods are linear on the rows**: every `f ∈ W_u` is a `K`-linear form on `V0`. A period
`P(φ, F) = Σ_c mass(c)·pair_σ(br(Φ(rep c)), F(c))` (`PeriodTarget.per`) is linear in the row `F`, as the Fock form
is (`WeylFock.fockL`, `WeylFock.fock_comm`), and sums of linear forms are linear. -/
theorem exists_linearMap_of_mem_W {f : b.P.V0 b.μ0 → C.K} (hf : f ∈ b.P.W b.μ0) :
    ∃ ℓ : b.P.V0 b.μ0 →ₗ[C.K] C.K, ⇑ℓ = f := by
  refine Submodule.iSup_induction _ (motive := fun f => ∃ ℓ : b.P.V0 b.μ0 →ₗ[C.K] C.K, ⇑ℓ = f) hf ?_ ⟨0, rfl⟩
    fun _ _ ⟨ℓ, hℓ⟩ ⟨ℓ', hℓ'⟩ => ⟨ℓ + ℓ', by rw [LinearMap.coe_add, hℓ, hℓ']⟩
  rintro ω _ ⟨φ, rfl⟩
  set κ₀ := WeylFock.fockWith (RingHom.id C.K) (WeylFock.hw C.K fun ρ => WeylFock.natW (b.P.σ ρ))
    (WeylFock.hw C.K fun ρ => WeylFock.natW (b.P.σ ρ))
  refine ⟨Finsupp.lsum C.K (fun c => ((HermClasses.mass c : C.K) * κ₀⁻¹) •
    WeylFock.fockL C.K (b.P.br ω (b.P.col b.μ0 ω φ c.out))) ∘ₗ (b.P.V0 b.μ0).subtype, ?_⟩
  funext F
  simp only [PeriodTarget.PerData.P, LinearMap.comp_apply, LinearMap.funLeft_apply, PeriodTarget.perMap,
    LinearMap.coe_mk, AddHom.coe_mk, PeriodTarget.per, PeriodTarget.pair, Finsupp.lsum_apply, WeylFock.fockL,
    Submodule.coe_subtype]
  refine Finsupp.sum_congr fun c _ => ?_
  show (HermClasses.mass c * κ₀⁻¹ : C.K) * WeylFock.fockWith (RingHom.id C.K) _ _ = _
  rw [WeylFock.fock_comm]
  ring

/-- **Every period has a nonzero integer multiple in `C_u`**, at Stage U (`Tw = ∅`), when the integral rows lie in a
finitely generated `O_K`-module `Lm`: an integer clearing the denominators of the period (a linear form,
`exists_linearMap_of_mem_W`) on the finitely many generators of `Lm` (`HermForms.exists_int_mul_mem_one`) makes it
integral on `Lm`, hence on the rows, at every place. -/
theorem exists_int_smul_mem_Ctgt (hTw : b.tw.Tw = ∅) {Lm : Submodule (𝓞 C.K) (b.P.V0 b.μ0)} (hLm : Lm.FG)
    (hR : b.P.R C.τK b.μ0 ⊆ Lm) {f : b.P.V0 b.μ0 → C.K} (hf : f ∈ b.P.W b.μ0) :
    ∃ z : ℤ, z ≠ 0 ∧ (z : C.K) • f ∈ PeriodTarget.Ctgt C.τK b.tw := by
  classical
  obtain ⟨ℓ, rfl⟩ := exists_linearMap_of_mem_W hf
  obtain ⟨s, hs⟩ := hLm
  obtain ⟨z, hz0, hz⟩ := HermForms.exists_int_mul_mem_one fun r : s => ℓ r
  have hle : Lm ≤ (1 : Submodule (𝓞 C.K) C.K).comap (((z : C.K) • ℓ).restrictScalars (𝓞 C.K)) := by
    rw [← hs, Submodule.span_le]
    exact fun r hr => hz z dvd_rfl ⟨r, hr⟩
  refine ⟨z, hz0, (PeriodTarget.mem_Ctgt _ _ _).2 ⟨Submodule.smul_mem _ _ hf, fun w _ r hr => ?_,
    fun w hw => by simp [hTw] at hw⟩⟩
  exact HermForms.mem_Ow_of_mem_one (hle (hR hr)) w

/-- **`C_u` is finitely generated**, at Stage U, when the integral rows span `V0` and lie in a finitely generated
`O_K`-module: their `O_K`-span has finitely many generators `r_i`, which still span `V0`, and `f ↦ (f(r_i))_i` maps
`C_u` into `O_K^{r}` (the periods are linear, `exists_linearMap_of_mem_W`, and integral on the rows) with no kernel
on `W_u ⊇ C_u`. -/
theorem fg_Ctgt (hTw : b.tw.Tw = ∅) (hspan : Submodule.span C.K (b.P.R C.τK b.μ0) = ⊤)
    {Lm : Submodule (𝓞 C.K) (b.P.V0 b.μ0)} (hLm : Lm.FG) (hR : b.P.R C.τK b.μ0 ⊆ Lm) :
    (PeriodTarget.Ctgt C.τK b.tw).FG := by
  classical
  have hfgR : (Submodule.span (𝓞 C.K) (b.P.R C.τK b.μ0)).FG := by
    let ι := (b.P.V0 b.μ0).subtype.restrictScalars (𝓞 C.K)
    exact Submodule.fg_of_fg_map_injective ι Subtype.val_injective
      ((hLm.map ι).of_le (Submodule.map_mono (Submodule.span_le.2 hR)))
  obtain ⟨s, hs⟩ := hfgR
  have hsK : Submodule.span C.K (s : Set (b.P.V0 b.μ0)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 C.K), hs, Submodule.span_span_of_tower, hspan]
  let ev : (b.P.V0 b.μ0 → C.K) →ₗ[𝓞 C.K] (s → C.K) := LinearMap.pi fun r => LinearMap.proj (r : b.P.V0 b.μ0)
  refine Submodule.fg_of_fg_map_of_fg_inf_ker ev ?_ ?_
  · refine (Submodule.fg_span (Set.finite_range fun r : s => (Pi.single r 1 : s → C.K))).of_le ?_
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨hW, hint, -⟩ := (PeriodTarget.mem_Ctgt _ _ _).1 hf
    obtain ⟨ℓ, rfl⟩ := exists_linearMap_of_mem_W hW
    have hle : Submodule.span (𝓞 C.K) (b.P.R C.τK b.μ0) ≤
        (1 : Submodule (𝓞 C.K) C.K).comap (ℓ.restrictScalars (𝓞 C.K)) :=
      Submodule.span_le.2 fun r hr => HermForms.mem_one_of_forall_Ow fun w => hint w (by simp [hTw]) r hr
    choose a ha using fun r : s => Submodule.mem_one.1 (hle (hs ▸ Submodule.subset_span r.2))
    have : ev ℓ = ∑ r, a r • (Pi.single r 1 : s → C.K) := by
      funext r'
      simp [ev, Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [this]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  · convert Submodule.fg_bot
    refine eq_bot_iff.2 fun f hf => ?_
    obtain ⟨hfC, hfk⟩ := Submodule.mem_inf.1 hf
    obtain ⟨ℓ, rfl⟩ := exists_linearMap_of_mem_W ((PeriodTarget.mem_Ctgt _ _ _).1 hfC).1
    have h0 : ℓ = 0 := LinearMap.ext_on hsK fun r hr => congrFun hfk ⟨r, hr⟩
    rw [Submodule.mem_bot, h0]
    rfl

/-- **`N_ω` is an `O_K`-lattice**, for nonzero `𝔞⁺`, `𝔞⁻`, when `M_ω` is one and every period has a nonzero integer
multiple in `C_u`: `a·N_ω ⊆ 𝔞⁻M_ω ⊆ M_ω` for a nonzero `a ∈ 𝔞⁺` (finite generation), and for `m ∈ M_ω` and a nonzero
`c ∈ 𝔞⁻`, `c·m ∈ 𝔞⁻M_ω` has a nonzero integer multiple with its period in `C_u`, which lies in `N_ω`
(spanning). -/
theorem isLattice_N (ω : b.Ω) [hM : (b.M ω).IsLattice C.K] (h𝔞 : b.𝔞p ω ≠ ⊥ ∧ b.𝔞n ω ≠ ⊥)
    (habs : ∀ f ∈ b.P.W b.μ0, ∃ z : ℤ, z ≠ 0 ∧ (z : C.K) • f ∈ PeriodTarget.Ctgt C.τK b.tw) :
    (b.N ω).IsLattice C.K := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞.1
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞.2
  have hcK : algebraMap (𝓞 C.K) C.K c ≠ 0 := fun h =>
    hc0 (IsFractionRing.injective (𝓞 C.K) C.K (by rw [h, map_zero]))
  refine ⟨Submodule.fg_of_fg_map_injective (a • LinearMap.id) (fun y y' h => ?_) (hM.fg.of_le ?_), ?_⟩
  · have h' : (a : C.K) • y = (a : C.K) • y' := by simpa only [LinearMap.smul_apply, LinearMap.id_apply,
      algebraMap_smul] using h
    exact smul_right_injective _ (by exact_mod_cast ha0) h'
  · rintro _ ⟨y, hy, rfl⟩
    exact Submodule.smul_le_right ((Submodule.mem_inf.1 hy).1 a ha)
  · refine eq_top_iff.2 (hM.span_eq_top.symm.le.trans (Submodule.span_le.2 fun m hm => ?_))
    have h1 : c • m ∈ b.𝔞n ω • b.M ω := Submodule.smul_mem_smul hc hm
    obtain ⟨z, hz0, hz⟩ := habs _ (le_iSup (fun ω => LinearMap.range (b.P.P b.μ0 ω)) ω ⟨c • m, rfl⟩)
    have hzc : (z : C.K) • c • m = (z : 𝓞 C.K) • c • m := by
      rw [← algebraMap_smul C.K (z : 𝓞 C.K), map_intCast]
    have hy : (z : C.K) • c • m ∈ b.N ω := by
      refine Submodule.mem_inf.2 ⟨fun a' _ => ?_, ?_⟩
      · rw [hzc, smul_smul]
        exact Submodule.smul_mem _ _ h1
      · rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, map_smul]
        exact hz
    have : m = ((z : C.K) * algebraMap (𝓞 C.K) C.K c)⁻¹ • ((z : C.K) • c • m) := by
      rw [← algebraMap_smul C.K c m, smul_smul, smul_smul, mul_assoc,
        inv_mul_cancel₀ (mul_ne_zero (Int.cast_ne_zero.2 hz0) hcK), one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)

/-! ## The frame -/

/-- **The map of a word is a co-isometry** from the Petersson metric to the quotient one, in Mathlib's basis of the
source and the coordinates `quotCoord` of the target (`quotGram_spec`), at the word `ω'` of an object whose every
word is `ω`. -/
theorem coisometry_word {ω ω' : b.Ω} (h : ω' = ω) [∀ ω, FiniteDimensional C.K (b.Vs ω)] (v : Pl C.K)
    (hpos : (petGram (b.petForm ω') v).PosDef) :
    (LinearMap.toMatrix' (quotCoord (b.P.P b.μ0 ω) ∘ₗ b.P.P b.μ0 ω' ∘ₗ
      (finBasis C.K (b.Vs ω')).equivFun.symm.toLinearMap)).map v.1.embedding * (petGram (b.petForm ω') v)⁻¹ *
      ((LinearMap.toMatrix' (quotCoord (b.P.P b.μ0 ω) ∘ₗ b.P.P b.μ0 ω' ∘ₗ
        (finBasis C.K (b.Vs ω')).equivFun.symm.toLinearMap)).map v.1.embedding)ᴴ =
      (quotGram (b.petForm ω) (b.P.P b.μ0 ω) v)⁻¹ := by
  subst h
  exact (quotGram_spec _ _ v hpos).2.symm

/-- **An object of one word has a frame** (Stage U, nonzero `𝔞⁺`, `𝔞⁻`), when its step-0 weights are antitone, its
integral rows span `V0` and lie in a finitely generated `O_K`-module, its period map is nonzero (so `W_u ≠ 0`), its
target metric is the quotient metric (`gQuot`) and its heights are `0`. The coordinates are Mathlib's basis of `V_ω`
and `eC = quotCoord P` on the target; the sources and the target are `N_ω` and `C_u` in coordinates, with the Gram
matrix of the Petersson form (positive definite, `HermForms.posDef_petAt`) and the quotient Gram matrix (positive
definite, `quotGram_spec`); the map is `eC ∘ P ∘ c⁻¹`, a co-isometry (`KLattice.norm_hom_le_of_coisometry`), so
bounded by `e^0`. -/
theorem frameExists_of (ω : b.Ω) (hω : ∀ ω', ω' = ω) (hlam : ∀ ω ρ, Antitone (b.lam0 ω ρ))
    (h𝔞 : ∀ ω, b.𝔞p ω ≠ ⊥ ∧ b.𝔞n ω ≠ ⊥) (hTw : b.tw.Tw = ∅)
    (hspan : Submodule.span C.K (b.P.R C.τK b.μ0) = ⊤)
    (hfg : ∃ Lm : Submodule (𝓞 C.K) (b.P.V0 b.μ0), Lm.FG ∧ b.P.R C.τK b.μ0 ⊆ Lm)
    (hW : 0 < finrank C.K (LinearMap.range (b.P.P b.μ0 ω))) (hg : b.g = b.gQuot ω)
    (hht : ∀ ω v, b.ht ω v = 0) : b.FrameExists := by
  classical
  obtain ⟨Lm, hLm, hR⟩ := hfg
  have hVω : ∀ ω', FiniteDimensional C.K (HermForms.Vω (b.ST ω') C.τK (b.χ0 ω') (b.lam0 ω')) := fun ω' =>
    HermForms.finiteDimensional_Vω (b.ST ω') C.τK (b.χ0 ω') (b.lam0 ω') (hlam ω')
  have hfd : ∀ ω', FiniteDimensional C.K (b.Vs ω') := fun ω' =>
    have := Submodule.finiteDimensional_of_le (inf_le_right :
      b.Xc ω' ⊓ HermForms.Vω (b.ST ω') C.τK (b.χ0 ω') (b.lam0 ω') ≤ _)
    LinearEquiv.finiteDimensional (b.e ω').symm
  have hWP : b.P.W b.μ0 = LinearMap.range (b.P.P b.μ0 ω) :=
    le_antisymm (iSup_le fun ω' => by rw [hω ω']) (le_iSup (fun ω' => LinearMap.range (b.P.P b.μ0 ω')) ω)
  have : Nonempty (Fin (finrank C.K (LinearMap.range (b.P.P b.μ0 ω)))) := Fin.pos_iff_nonempty.1 hW
  have habs := fun f (hf : f ∈ b.P.W b.μ0) => exists_int_smul_mem_Ctgt hTw hLm hR hf
  have hM : ∀ ω', (b.M ω').IsLattice C.K := fun ω' =>
    HermForms.isLattice_span_Mω (b.ST ω') C.τK (b.χ0 ω') (b.lam0 ω') (hlam ω') (b.e ω')
  have hN : ∀ ω', (b.N ω').IsLattice C.K := fun ω' => isLattice_N ω' (h𝔞 ω') habs
  let c : ∀ ω', b.Vs ω' ≃ₗ[C.K] (Fin (finrank C.K (b.Vs ω')) → C.K) := fun ω' => (finBasis C.K (b.Vs ω')).equivFun
  obtain ⟨eC, heC⟩ : ∃ e, e = quotCoord (b.P.P b.μ0 ω) := ⟨_, rfl⟩
  have hsrc : ∀ ω', ((b.N ω').map ((c ω').toLinearMap.restrictScalars (𝓞 C.K))).IsLattice C.K :=
    fun ω' => ⟨(hN ω').fg.map _, by
      rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, (hN ω').span_eq_top,
        Submodule.map_top, LinearEquiv.range]⟩
  have htgt : ((PeriodTarget.Ctgt C.τK b.tw).map (eC.restrictScalars (𝓞 C.K))).IsLattice C.K := by
    have hsurj : ∀ y, ∃ φ, eC (b.P.P b.μ0 ω φ) = y := by
      rw [heC]
      exact surjective_quotCoord _
    refine ⟨(fg_Ctgt hTw hspan hLm hR).map _, eq_top_iff.2 fun y _ => ?_⟩
    obtain ⟨φ, rfl⟩ := hsurj y
    obtain ⟨z, hz0, hz⟩ := habs _ (by rw [hWP]; exact LinearMap.mem_range_self _ φ)
    have hmem : (z : C.K) • eC (b.P.P b.μ0 ω φ) ∈
        Submodule.span C.K ((PeriodTarget.Ctgt C.τK b.tw).map (eC.restrictScalars (𝓞 C.K)) : Set (_ → C.K)) :=
      Submodule.subset_span ⟨_, hz, by rw [LinearMap.restrictScalars_apply, map_smul]⟩
    exact (Submodule.smul_mem_iff _ (Int.cast_ne_zero.2 hz0)).1 hmem
  have hle : ∀ ω', b.Xc ω' ⊓ HermForms.Vω (b.ST ω') C.τK (b.χ0 ω') (b.lam0 ω') ≤
      HermForms.Vω (b.ST ω') C.τK (b.χ0 ω') (b.lam0 ω') := fun _ => inf_le_right
  have hpos : ∀ ω' v, (petGram (b.petForm ω') v).PosDef := fun ω' v =>
    HermForms.posDef_petAt (ST := b.ST ω') C.τK (b.χ0 ω') (b.lam0 ω')
      (F := fun i => Submodule.inclusion (hle ω') (b.e ω' (finBasis C.K (b.Vs ω') i)))
      ((finBasis C.K (b.Vs ω')).linearIndependent.map' ((Submodule.inclusion (hle ω')).comp (b.e ω').toLinearMap)
        (LinearMap.ker_eq_bot.2 ((Submodule.inclusion_injective (hle ω')).comp (b.e ω').injective))) v.1.embedding
  let src : ∀ ω', KLattice C.K (Fin (finrank C.K (b.Vs ω'))) := fun ω' =>
    ⟨(b.N ω').map ((c ω').toLinearMap.restrictScalars (𝓞 C.K)), petGram (b.petForm ω'), hpos ω'⟩
  let tgt : KLattice C.K (Fin (finrank C.K (LinearMap.range (b.P.P b.μ0 ω)))) :=
    ⟨(PeriodTarget.Ctgt C.τK b.tw).map (eC.restrictScalars (𝓞 C.K)), quotGram (b.petForm ω) (b.P.P b.μ0 ω),
      fun v => (quotGram_spec _ _ v (hpos ω v)).1⟩
  let B : ∀ ω', (Fin (finrank C.K (b.Vs ω')) → C.K) →ₗ[C.K]
      (Fin (finrank C.K (LinearMap.range (b.P.P b.μ0 ω))) → C.K) :=
    fun ω' => eC ∘ₗ b.P.P b.μ0 ω' ∘ₗ (c ω').symm.toLinearMap
  have hco : ∀ ω' v, (LinearMap.toMatrix' (B ω')).map v.1.embedding * ((src ω').G v)⁻¹ *
      ((LinearMap.toMatrix' (B ω')).map v.1.embedding)ᴴ = (tgt.G v)⁻¹ := fun ω' v => by
    simp only [src, tgt, B, heC]
    exact coisometry_word (hω ω') v (hpos ω' v)
  have hφ : ∀ ω' v, ∀ y ∈ (KLattice.part v : Submodule ℂ (KLattice.Space C.K (Fin (finrank C.K (b.Vs ω'))))),
      ‖(src ω').hom tgt (B ω') y‖ ≤ Real.exp (b.ht ω' v) * ‖y‖ := by
    intro ω' v y _
    simp only [hht, Real.exp_zero, one_mul]
    exact KLattice.norm_hom_le_of_coisometry _ _ _ (hco ω') y
  let F : FrameOn C.K b.Ω :=
    { n := fun ω' => Fin (finrank C.K (b.Vs ω'))
      κ := Fin (finrank C.K (LinearMap.range (b.P.P b.μ0 ω)))
      src := src
      tgt := tgt
      B := B
      hB := fun ω' => by
        rintro _ ⟨φ, hφ, rfl⟩
        exact ⟨b.P.P b.μ0 ω' φ, (Submodule.mem_inf.1 hφ).2,
          congrArg (fun φ' => eC (b.P.P b.μ0 ω' φ')) ((c ω').symm_apply_apply φ).symm⟩
      ht := b.ht
      hφ := hφ }
  refine ⟨F, c, eC, by rw [hWP, heC]; exact quotCoord_injOn _, fun ω' => rfl, rfl,
    fun ω' φ => congrArg (fun φ' => eC (b.P.P b.μ0 ω' φ')) ((c ω').symm_apply_apply φ).symm,
    fun ω' v i j => by simp only [F, src, c, petGram, petForm, Basis.equivFun_symm_single], fun v y _ z _ => ?_,
    fun _ _ => rfl⟩
  rw [hg, heC]
  exact quotMetric_eq _ _ v y z

end SharpObj

/-! ## The construction -/

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ}

/-- **A row on one class with a value in `VV(σ)` is a row of `V0all`.** -/
theorem single_mem_V0all {Φ' : Type} [Fintype Φ'] [DecidableEq Φ'] {n : ℕ} {L G X' : Type} [Field L] [Group G]
    [MulAction G X'] {σ : Φ' → Fin n → ℤ} (c : HermClasses.Cl G X') {P : WeylFock.Pol Φ' n L}
    (hP : P ∈ WeylFock.VV (n := n) (L := L) σ) : Finsupp.single c P ∈ V0all σ := fun c' => by
  classical
  rw [Finsupp.single_apply]
  split_ifs
  exacts [hP, zero_mem _]

/-- **The row weight of the construction is antitone**: it interlaces the column weight `λ_m`
(`SharpDesign.PinnedTo.interlace`, the base word's family `hc u` being pinned to `u`), so
`PeriodTarget.antitone_of_interlace_right` applies. -/
theorem sharpσ_antitone (Dg : SharpDesign S κ x ε X) (u : S.A) (ρ : Φ S.A) : Antitone (sharpσ Dg u ρ) :=
  PeriodTarget.antitone_of_interlace_right (fun j => WeylFock.wt Dg.R.k Dg.R.t Dg.R.m
    (fun ρ i => ⌊(Dg.hc u ρ).u i - 1 / 2⌋) (fun ρ => finN (Dg.hc u ρ).e) ρ (Fin.cast (rowN_add_one Dg) j)) fun i =>
    SharpDesign.PinnedTo.interlace (hw := Dg.hc u) (fun _ => ⟨rfl, rfl, rfl, fun _ _ => rfl⟩) (rowN_add_one Dg) ρ i

/-- **The frame of the construction, from (NI)** (`SharpPieces.frame` at `adm := Adm`, `cons := sharpCons`, with
(NI) for `SharpInputs`): eventually in the design (where (NI) holds), at every translate, the object of one word has
a frame (`SharpObj.frameExists_of`). Its step-0 weights are antitone (`Setting.Ranks.wt0_antitone`), `𝔞⁺ = 𝔞⁻ = ⊤`,
`Tw = ∅`, the metric is the quotient metric and the heights `0` by definition; the integral rows span `V0` and lie
in a finitely generated module (`HermForms.rows_span`, `HermForms.rows_fg`: finitely many classes of row points,
`HermClasses.finite_DCl`, with unimodular lattices, and the antitone row weight `sharpσ_antitone`); (NI) gives a
nonzero period map. -/
theorem frame_of_sharpNI (hNI : SharpNI) : EventuallyAdm (fun Dg => Dg.Adm)
    fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ, ((sharpCons Dg).obj u).FrameExists := by
  obtain ⟨ε₁, hε₁, H⟩ := hNI
  refine ⟨ε₁, hε₁, fun ε hε hle => ?_⟩
  obtain ⟨x₀, hx₀⟩ := H ε hε hle
  refine ⟨x₀, fun {S κ x X} Dg hx hA u hu => ?_⟩
  have hsand : ∀ y : RowPt Dg, ∃ a b, HermForms.Sand y.1.N a b := fun y =>
    let ⟨a, ha⟩ := HermForms.exists_sand_of_unimodular y.2.unimod
    ⟨a, a, ha⟩
  exact (sharpObj Dg u).frameExists_of () (fun _ => rfl) (fun _ => Setting.Ranks.wt0_antitone _ _)
    (fun _ => ⟨top_ne_bot, top_ne_bot⟩) rfl
    (HermForms.rows_span _ _ _ (sharpσ_antitone Dg u) hsand (fun F hF => hF) fun c _ hP => single_mem_V0all c hP)
    (HermForms.rows_fg _ _ _ (HermClasses.finite_DCl _ _ _ _ (rowLev Dg)) (sharpσ_antitone Dg u) hsand
      fun F hF => hF) (hx₀ Dg hx hA u hu).1 rfl
    fun _ _ => rfl

end

end ZetaBalance
