import SharpCores
import SlopeSingle

/-!
# The frame loss of the construction from (NI) and the range

The piece `SharpPieces.frameLoss` of the proof's architecture (`SharpInputs`), for the construction `sharpCons` with
`adm := fun Dg => Dg.Adm`, reduced to two named statements about the construction: (NI), the near-injectivity of the
period map of its one word (`SharpNI`), and (R′), the range of its sources in every realising frame (`SharpRange`).
Neither is proved in the library yet; `frameLoss_of_sharpNI` is the reduction.

**One word.** The construction has one word `ω` and one level (`Ω = Unit`), and the frame loss `x^{4ε}Σ_t a_t/4`.
In a frame realising its object (`SharpObj.RealWith`), in coordinates `c` of the source and `eC` of the target, the
frame's map is the period map `P = P_{μ0}(ω)` read in coordinates: `B ∘ c = eC ∘ P`, with `eC` injective on
`W_u = Σ_ω range P_{μ0}(ω)`, which for one word is `range P`. So `B` has the rank of `P`
(`SharpObj.finrank_range_B`), and its kernel the rest of `dim V_ω`, by rank–nullity. And `B` is onto: the target
lattice `C_u` lies in `W_u` (by definition, `PeriodTarget.Ctgt`), so its image `eC(C_u)`, a lattice spanning `K^κ`,
lies in `eC(W_u) = range B` (`SharpObj.range_B_eq_top`).

**The frame loss** (`SharpObj.frameLoss_of_one_word`). The one-word lemma (`KFrame.frame_le_of_one_word`, module
`SlopeSingle`) with the range `μ_max(N_ω) ≤ μ(N_ω) + U` bounds the frame's loss by `(dim ker B/rk B)·U`, whatever the
heights. (NI), `dim V_ω ≤ 2 rk P`, makes the ratio at most `1`, and (R′) gives `0 ≤ U ≤ x^{4ε}Σ_t a_t/4`, the frame
loss. The total rank is positive: `rk N_ω = [K:ℚ]·dim V_ω`, and `dim V_ω ≥ rk P > 0`.
-/

namespace ZetaBalance

open NumberField

namespace SharpObj

attribute [local instance] InnerProductSpace.complexToReal

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}
  (b : SharpObj Dg C)

/-- **The range (R′) of the sources** with constant `U`: in every frame realising the object, `μ_max(N_ω) ≤ μ(N_ω) + U`
at every word. -/
def RangeLe (U : ℝ) : Prop :=
  ∀ (F : FrameOn C.K b.Ω) c eC, b.RealWith F c eC → ∀ ω,
    (F.toKFrame.frame.N ω).SlopeLe ((F.toKFrame.frame.N ω).deg ⊤ / (F.toKFrame.frame.N ω).rk ⊤ + U)

variable {b} {F : FrameOn C.K b.Ω} {c : ∀ ω, b.Vs ω ≃ₗ[C.K] (F.n ω → C.K)}
  {eC : (b.P.V0 b.μ0 → C.K) →ₗ[C.K] (F.κ → C.K)}

/-- **A realising frame's map has the rank of the period map**: `B ∘ c = eC ∘ P` (`RealWith`, clause 4), `c` is an
isomorphism and `eC` is injective on `W_u ⊇ range P` (clause 1). -/
theorem finrank_range_B (hF : b.RealWith F c eC) (ω : b.Ω) :
    Module.finrank C.K (LinearMap.range (F.B ω)) = Module.finrank C.K (LinearMap.range (b.P.P b.μ0 ω)) := by
  set P := b.P.P b.μ0 ω
  have hW : LinearMap.range P ≤ b.P.W b.μ0 := le_iSup (fun ω => LinearMap.range (b.P.P b.μ0 ω)) ω
  have hinj : Function.Injective (eC ∘ₗ (LinearMap.range P).subtype) := fun y z h =>
    Subtype.ext (hF.1 (hW y.2) (hW z.2) h)
  have hB : F.B ω = (eC ∘ₗ (LinearMap.range P).subtype) ∘ₗ
      (P.rangeRestrict ∘ₗ ((c ω).symm : (F.n ω → C.K) →ₗ[C.K] b.Vs ω)) := by
    refine LinearMap.ext fun y => ?_
    conv_lhs => rw [← (c ω).apply_symm_apply y]
    exact (hF.2.2.2.1 ω _).symm
  rw [hB, LinearMap.range_comp_of_range_eq_top _ (by
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), LinearMap.range_rangeRestrict]),
    LinearMap.finrank_range_of_inj hinj]

/-- **A realising frame's map is onto, for one word**: the target lattice is `eC(C_u)` (clause 3), `C_u ⊆ W_u`
(`PeriodTarget.mem_Ctgt`), and `W_u = range P` for one word, so the lattice lies in
`eC(range P) = range (B ∘ c)` (clause 4); it spans `K^κ`. -/
theorem range_B_eq_top (hF : b.RealWith F c eC) (ω : b.Ω) (hω : ∀ ω', ω' = ω) :
    LinearMap.range (F.B ω) = ⊤ := by
  have hW : b.P.W b.μ0 ≤ LinearMap.range (b.P.P b.μ0 ω) := iSup_le fun ω' => by rw [hω ω']
  rw [eq_top_iff, ← Submodule.IsLattice.span_eq_top (A := C.K) (M := F.tgt.M), Submodule.span_le]
  intro y hy
  rw [SetLike.mem_coe, hF.2.2.1] at hy
  obtain ⟨f, hf, rfl⟩ := hy
  obtain ⟨φ, rfl⟩ := hW ((PeriodTarget.mem_Ctgt _ _ _).1 hf).1
  exact ⟨c ω φ, (hF.2.2.2.1 ω φ).symm⟩

variable (b)

/-- **The frame loss of one word from (NI) and the range**: for an object with one word `ω` and frame loss
`0 ≤ loss ≤ x^{4ε}Σ_t a_t/4`, if the period map has positive rank and `dim V_ω ≤ 2 rk P` (NI), and the range (R′)
holds with `0 ≤ U ≤ loss`, then the frame loss holds: in every realising frame the map is onto (`range_B_eq_top`),
of rank `rk P` (`finrank_range_B`), so `dim ker B ≤ rk B` and the one-word lemma
(`KFrame.frame_le_of_one_word`) gives `s − μ(C) ≤ (dim ker B/rk B)·U ≤ U`. -/
theorem frameLoss_of_one_word (ω : b.Ω) (hω : ∀ ω', ω' = ω) (hl0 : 0 ≤ b.loss)
    (hl : b.loss ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 4)
    (hpos : 0 < Module.finrank C.K (LinearMap.range (b.P.P b.μ0 ω)))
    (hNI : Module.finrank C.K (b.Vs ω) ≤ 2 * Module.finrank C.K (LinearMap.range (b.P.P b.μ0 ω)))
    {U : ℝ} (hU : 0 ≤ U) (hUl : U ≤ b.loss) (hR : b.RangeLe U) : b.FrameLoss := by
  refine ⟨hl0, hl, fun F c eC hF => ?_⟩
  have hsurj := range_B_eq_top hF ω hω
  have hrk := finrank_range_B hF ω
  have hrn := LinearMap.finrank_range_add_finrank_ker (F.B ω)
  have hV := (c ω).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card] at hrn hV
  refine ⟨Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _) ⟨ω, Finset.mem_univ _, ?_⟩, ?_⟩
  · show (0 : ℝ) < (F.src ω).toPlaceLattice.slopeLattice.rk ⊤
    rw [KLattice.rk_top]
    exact_mod_cast Nat.mul_pos Module.finrank_pos (by omega)
  have h := F.toKFrame.frame_le_of_one_word ω hω hsurj (hR F c eC hF ω)
  have hle : (Module.finrank C.K (LinearMap.ker (F.B ω)) : ℝ) / Module.finrank C.K (LinearMap.range (F.B ω)) ≤ 1 :=
    (div_le_one (Nat.cast_pos.2 (by omega))).2 (Nat.cast_le.2 (by omega))
  calc _ ≤ _ := h
    _ ≤ 1 * U := mul_le_mul_of_nonneg_right hle hU
    _ ≤ b.loss := by linarith

end SharpObj

/-- **(NI), the near-injectivity of the period map**, eventually in the design: at every admissible design with `ε`
small and `x` large, at every translate `u ∈ A₀`, the period map `P = P_{μ0}(ω)` of the construction's one word
(`sharpPer`, the explicit theta chain at Stage U: the chain's steps, its top on the row points and the branching map)
has positive rank and at least half the dimension of its source `V_ω = sharpVs`: `0 < rk P` and `dim V_ω ≤ 2 rk P`.
It is intrinsic: no frame, no metric. The library proves it nowhere yet, so it is a hypothesis of the frame loss
(`frameLoss_of_sharpNI`). The planned fresh route is the whole-word second moment (N1): `dim ker T ≤ ‖T − 1‖²_HS`
for `T = c⁻¹·Pu*Pu`, `Pu` a Poincaré lift whose kernel contains that of `P`, with the Gram entries evaluated by
Siegel–Braun and orbital integrals, so `rk P ≥ dim V_ω/2` once `‖T − 1‖²_HS ≤ dim V_ω/2`. It is stated at the
construction's auxiliary prime `T = sharpT`, whose window sits `c_T = x^{2ε}` (`sharpCT`) below `Λ_u`, so below
the threshold `T*` that the second-moment route needs (`Λ_u − log T* ≈ x^{7ε/8}`). -/
def SharpNI : Prop :=
  EventuallyAdm (fun Dg => Dg.Adm) fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ,
    0 < Module.finrank (sharpCoeff Dg).K (LinearMap.range ((sharpPer Dg u).P () ())) ∧
      Module.finrank (sharpCoeff Dg).K (sharpVs Dg u) ≤
        2 * Module.finrank (sharpCoeff Dg).K (LinearMap.range ((sharpPer Dg u).P () ()))

/-- **(R′), the range of the sources**, eventually in the design: at every admissible design with `ε` small and `x`
large, at every translate `u ∈ A₀`, some `U` with `0 ≤ U ≤ x^{4ε}Σ_t a_t/4` bounds the range of the construction's
sources in every realising frame, `μ_max(N_ω) ≤ μ(N_ω) + U` (`SharpObj.RangeLe`). Not proved in the library yet, it
is a hypothesis of the frame loss (`frameLoss_of_sharpNI`). It will come from the gain's certificate when the gain is
built, with `U = μ̂_max(M_ω) + c_F + colength`: the bound on `μ_max(M_ω)`, the slack `c_F` of (F) and the
certificate's colength. -/
def SharpRange : Prop :=
  EventuallyAdm (fun Dg => Dg.Adm) fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ,
    ∃ U, 0 ≤ U ∧ U ≤ x ^ (4 * ε) * (∑ s ∈ Dg.TT, Dg.a s) / 4 ∧ ((sharpCons Dg).obj u).RangeLe U

/-- **The frame loss of the construction from (NI) and the range** (`SharpPieces.frameLoss` at `adm := Adm`,
`cons := sharpCons`): eventually in the design (`EventuallyAdm.and`), at every translate, the object's one word meets
(NI) and (R′), and its frame loss is `x^{4ε}Σ_t a_t/4`, so `SharpObj.frameLoss_of_one_word` applies. -/
theorem frameLoss_of_sharpNI (hNI : SharpNI) (hR : SharpRange) : EventuallyAdm (fun Dg => Dg.Adm)
    fun {S κ x ε X} (Dg : SharpDesign S κ x ε X) => ∀ u ∈ A₀ κ, ((sharpCons Dg).obj u).FrameLoss := by
  obtain ⟨ε₁, hε₁, H⟩ := hNI.and hR
  refine ⟨ε₁, hε₁, fun ε hε hle => ?_⟩
  obtain ⟨x₀, hx₀⟩ := H ε hε hle
  refine ⟨x₀, fun {S κ x X} Dg hx hA u hu => ?_⟩
  obtain ⟨hni, hr⟩ := hx₀ Dg hx hA
  obtain ⟨hpos, hdim⟩ := hni u hu
  obtain ⟨U, hU, hUl, hRU⟩ := hr u hu
  have hA0 : 0 ≤ ∑ s ∈ Dg.TT, Dg.a s := Finset.sum_nonneg fun t ht => (Dg.a_pos t ht).le
  exact ((sharpCons Dg).obj u).frameLoss_of_one_word () (fun _ => rfl)
    (div_nonneg (mul_nonneg (Real.rpow_nonneg hA.big.pos.le _) hA0) (by norm_num)) le_rfl hpos hdim hU hUl hRU

end ZetaBalance
