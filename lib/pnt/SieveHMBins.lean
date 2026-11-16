/-
# Proposition 3′ pointwise, by bins, with the Halász–Montgomery bound per bin

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`binTerm cnt P q V B` is the smaller of orthogonality's bound for a bin of `cnt` characters,
`cnt^{1/2}((P + q)V)^{1/2}`, and the Halász–Montgomery bound of `SieveHMBin.sum_bin_hm`,
`(e·V·(cnt·2P + cnt²·B))^{1/2}`, with `V = Σ|a|²` and `B` a bound on `|K_{2P}(ψ, 0)|` for `ψ ≠ 1`.
`sum_typeII_bins_hm` is the bound by bins with `binTerm` for each bin's `(#bin)^{1/2}(Σ_χ|W(χ)|²)^{1/2}`, after the
orthogonality step (T1, `Σ_χ|W(χ)|² ≤ (P + q)Σ|a|²`, inlined); `offK_bound` is such a `B`, from
`LinnikOffDiag.norm_offK_le` at `δ = ε′ = 1/1000` and `z = 0`: `C·Λ^{1/12 − 1/1000}·(2q)^{5/12 + 3/1000}` for every
`q`, `ψ ≠ 1` and `Λ ≥ 1`.

The file imports `SieveHMBin.lean`.
-/
import SieveHMBin

namespace SieveTypeIIHM

open Finset DirMean LinnikPower SieveTypeII

variable {q : ℕ} [NeZero q]

/-- The bins' bound with the better of orthogonality and Halász–Montgomery for each bin. -/
noncomputable def binTerm (cnt P q V B : ℝ) : ℝ :=
  min (Real.sqrt cnt * Real.sqrt ((P + q) * V)) (Real.sqrt (Real.exp 1 * V * (cnt * (2 * P) + cnt ^ 2 * B)))

/-- **A uniform kernel bound at `z = 0`** from `LinnikOffDiag.norm_offK_le` at `δ′ = ε′ = 1/1000`: there is `C` with
`|Σ_n kTerm ψ Λ 0 n| ≤ C·Λ^{1/12 − 1/1000}·(2q)^{5/12 + 3/1000}` for every `q`, `ψ ≠ 1` and `Λ ≥ 1`. -/
theorem offK_bound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 →
    ∀ Λ : ℝ, 1 ≤ Λ → ‖∑' n, kTerm ψ Λ 0 n‖ ≤
      C * Λ ^ (1 / 12 - 1 / 1000 : ℝ) * (2 * (q : ℝ)) ^ (5 / 12 + 3 / 1000 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := LinnikOffDiag.norm_offK_le (δ := 1 / 1000) (ε' := 1 / 1000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨C, hC0, fun q _ ψ hψ Λ hΛ => ?_⟩
  have h := hC q ψ hψ Λ hΛ 0 le_rfl (by norm_num) 0 (by simp)
  rw [show ((q : ℝ) * (0 + 2)) = 2 * (q : ℝ) by ring,
    show (5 / 12 + 1 / 1000 + 2 * (1 / 1000) : ℝ) = 5 / 12 + 3 / 1000 by norm_num] at h
  exact h

end SieveTypeIIHM

#print axioms SieveTypeIIHM.offK_bound
