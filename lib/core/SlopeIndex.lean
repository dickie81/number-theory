import KLattice
import FrameRescale

/-!
# The slope of a hermitian `O_K`-lattice moves by an index

The index bookkeeping (V) of the sharp frontier (`SharpInputs.SlopeFV`). Two `O_K`-lattices `M`, `N` in `K^ι`, with
the same metrics and neither assumed inside the other, have
`μ(N) = μ(M) + (log [N : N ∩ M] − log [M : N ∩ M])/rk`, `rk = [K:ℚ]·|ι|` (`KLattice.slope_withLattice_eq`; Mathlib's
`M.relIndex N` is `[N : M ∩ N]`). In the archive's units, `μ ↦ 2μ + c` (`SlopeFrame.SlopeLattice.rescale`), the
difference doubles (`KLattice.slope_rescale_withLattice_eq`): it is the term `idx_ω` of (V).

**Route.** `N + M` is an `O_K`-lattice (Mathlib's `IsLattice.sup`; the intersection would need more, as Mathlib has
`IsLattice.inf` over principal ideal domains only) containing both, so `KLattice.slope_withLattice` applies twice,
and the second isomorphism theorem `(N + M)/M ≅ N/(N ∩ M)` (`AddSubgroup.relIndex_sup_right`, `relIndex_sup_left`)
turns the indices in `N + M` into the indices of `N ∩ M` in `N` and in `M`.
-/

namespace KLattice

open Module NumberField

attribute [local instance] InnerProductSpace.complexToReal

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {ι : Type} [Fintype ι] (X : KLattice K ι)
  (N : Submodule (𝓞 K) (ι → K)) [N.IsLattice K]

/-- **The slope and the index**: with the metrics of `X`, any `O_K`-lattice `N` has
`μ(N) = μ(M) + (log [N : N ∩ M] − log [M : N ∩ M])/rk`, `M = X.M`, `rk = [K:ℚ]·|ι|`. -/
theorem slope_withLattice_eq :
    (X.withLattice N).toPlaceLattice.slopeLattice.deg ⊤ / (X.withLattice N).toPlaceLattice.slopeLattice.rk ⊤ =
      X.toPlaceLattice.slopeLattice.deg ⊤ / X.toPlaceLattice.slopeLattice.rk ⊤ +
        (Real.log (X.M.toAddSubgroup.relIndex N.toAddSubgroup) -
          Real.log (N.toAddSubgroup.relIndex X.M.toAddSubgroup)) / (finrank ℚ K * Fintype.card ι) := by
  have hN := slope_withLattice (X.withLattice (N ⊔ X.M)) (le_sup_left : N ≤ N ⊔ X.M)
  have hM : X.toPlaceLattice.slopeLattice.deg ⊤ / X.toPlaceLattice.slopeLattice.rk ⊤ = _ :=
    slope_withLattice (X.withLattice (N ⊔ X.M)) (le_sup_right : X.M ≤ N ⊔ X.M)
  rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left] at hN
  rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right] at hM
  simp only [rk_top, Nat.cast_mul] at hN hM ⊢
  rw [sub_div]
  linarith

/-- **The slope and the index in the archive's units** (`rescale c`, `μ ↦ 2μ + c`):
`μ(N) = μ(M) + 2(log [N : N ∩ M] − log [M : N ∩ M])/rk`. -/
theorem slope_rescale_withLattice_eq (c : ℝ) :
    ((X.withLattice N).toPlaceLattice.slopeLattice.rescale c).deg ⊤ /
        ((X.withLattice N).toPlaceLattice.slopeLattice.rescale c).rk ⊤ =
      (X.toPlaceLattice.slopeLattice.rescale c).deg ⊤ / (X.toPlaceLattice.slopeLattice.rescale c).rk ⊤ +
        2 * (Real.log (X.M.toAddSubgroup.relIndex N.toAddSubgroup) -
          Real.log (N.toAddSubgroup.relIndex X.M.toAddSubgroup)) / (finrank ℚ K * Fintype.card ι) := by
  have h := X.slope_withLattice_eq N
  simp only [SlopeFrame.SlopeLattice.rescale, rk_top, Nat.cast_mul] at h ⊢
  rw [add_div, add_div, mul_div_assoc, mul_div_assoc, mul_div_assoc, h]
  ring

end KLattice
