import SharpInputs
import SlopeIndex

/-!
# The index bookkeeping (V): `SlopeFV` from the slope bound on `M_ω`

Piece (V) of the proof of the sharp frontier (`SharpInputs`): the frame clause of `SharpObj.SlopeFV`,
`μ(N_ω) ≥ −c_F + idx_ω` in every realising frame, follows from the (F) half, `μ(M_ω) ≥ −c_F` with `M_ω` taken in the
frame's coordinates and metrics (`SharpObj.slopeFV_of_slopeM`). Both slopes are in the archive's units.

**The frame's source.** The slope lattice of the word `ω` in `KFrame.frame` is that of the source `KLattice`, rescaled
to the archive's units, by definition (`KFrame.frame_N`); the source's lattice is `N_ω` in the coordinates `c ω`
(`SharpObj.RealWith`).

**The index.** With the source's metrics, `μ(N_ω) = μ(M_ω) + 2(log [N_ω : N_ω ∩ M_ω] − log [M_ω : N_ω ∩ M_ω])/rk`
(`KLattice.slope_rescale_withLattice_eq`). The indices are those in `V_ω`, as `c ω` is injective
(`AddSubgroup.relIndex_map_map_of_injective`), and `rk = [K:ℚ]·|n ω| = [K:ℚ]·dim V_ω`, as `c ω : V_ω ≃ K^{n ω}`: the
difference is `idx_ω`. So, once the image of `M_ω` is a lattice, the frame clause is equivalent to `μ(M_ω) ≥ −c_F`;
the theorem uses one direction.
-/

namespace ZetaBalance

open NumberField

attribute [local instance] InnerProductSpace.complexToReal

/-- **The frame's source**: the slope lattice of the word `ω` in `KFrame.frame` is the source's, in the archive's
units (`rescale (archShift K)`). -/
theorem KFrame.frame_N {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (F : KFrame K) (ω : F.ι) :
    F.frame.N ω = (F.src ω).toPlaceLattice.slopeLattice.rescale (archShift K) :=
  rfl

namespace SharpObj

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {Dg : SharpDesign S κ x ε X} {C : SharpCoeff S}
  (b : SharpObj Dg C)

/-- **(V): `SlopeFV` from the slope bound on `M_ω`.** If in every realising frame the image of `M_ω` in the
coordinates `c ω` is an `O_K`-lattice whose slope with the source's metrics, in the archive's units, is at least
`−c_F` (the (F) half), then `μ(N_ω) ≥ −c_F + idx_ω` (the index bookkeeping), and `SlopeFV` holds. -/
theorem slopeFV_of_slopeM (h0 : 0 ≤ b.cF) (h1 : b.cF ≤ x ^ ε * (∑ s ∈ Dg.TT, Dg.a s) / 8)
    (hM : ∀ (F : FrameOn C.K b.Ω) c eC, b.RealWith F c eC → ∀ ω,
      let M := (b.M ω).map ((c ω : b.Vs ω →ₗ[C.K] (F.n ω → C.K)).restrictScalars (𝓞 C.K))
      ∃ _ : M.IsLattice C.K, -b.cF ≤ (((F.src ω).withLattice M).toPlaceLattice.slopeLattice.rescale
        (archShift C.K)).deg ⊤ / (((F.src ω).withLattice M).toPlaceLattice.slopeLattice.rescale (archShift C.K)).rk ⊤) :
    b.SlopeFV := by
  refine ⟨h0, h1, fun F c eC hF (ω : b.Ω) => ?_⟩
  obtain ⟨_, hμ⟩ := hM F c eC hF ω
  set f := (c ω : b.Vs ω →ₗ[C.K] (F.n ω → C.K)).restrictScalars (𝓞 C.K)
  have hi (P Q : Submodule (𝓞 C.K) (b.Vs ω)) :
      (P.map f).toAddSubgroup.relIndex (Q.map f).toAddSubgroup = P.toAddSubgroup.relIndex Q.toAddSubgroup := by
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (c ω).injective
  have hrk : Module.finrank C.K (b.Vs ω) = Fintype.card (F.n ω) := by
    rw [(c ω).finrank_eq, Module.finrank_fintype_fun_eq_card]
  rw [KFrame.frame_N, idx, hrk, ← hi (b.M ω), ← hi (b.N ω), ← hF.2.1 ω]
  exact (add_le_add_left hμ _).trans_eq
    (((F.src ω).withLattice ((b.M ω).map f)).slope_rescale_withLattice_eq (F.src ω).M (archShift C.K)).symm

end SharpObj

end ZetaBalance
