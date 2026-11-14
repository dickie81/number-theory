/-
# Proposition 3′ pointwise, by any classes of the characters

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveHMBins.sum_typeII_bins_hm` bounds `Σ_{χ≠1} |W(χ)||B(χ)|` by the bins of the characters' zeros. Its proof uses
nothing of the bins but that they partition the characters: here the classes are those of any map `cl` from the
characters to a finite type. The resonant window classes the characters by the sizes of the rest's prime sums, with
their zeros' bins.

* `sum_typeII_cls`, **the bound by classes**: for `cl` into a finite type `ι`, `S ⊆ (P, 2P]` with `P ≥ 1`, bounds
  `M_i ≥ 0` with `|B(χ)| ≤ M_{cl χ}` for `χ ≠ 1`, and `B ≥ 0` bounding the kernel:
  `Σ_{χ≠1} |W(χ)||B(χ)| ≤ Σ_{i:ι} M_i · binTerm (#class i) P q (Σ|a|²) B`, `W(χ) = dp S (aχ) h₀`.

The file imports `SieveHMBins.lean`.
-/
import SieveHMBins

namespace SieveTypeIIHM

open Finset DirMean LinnikPower SieveTypeII

variable {q : ℕ} [NeZero q]

/-- **Proposition 3′ pointwise, by classes of the characters, with the better bound per class.** For a map `cl` into a
finite type `ι`, `S ⊆ (P, 2P]` (`hS`) with `P ≥ 1` (`hP`), bounds `M_i ≥ 0` (`hM`) with `|B(χ)| ≤ M_{cl χ}`
for `χ ≠ 1` (`hB`), and `B ≥ 0` (`hB0`) with `|K_{2P}(ψ, 0)| ≤ B` for `ψ ≠ 1` (`hK`):
`Σ_{χ≠1} |W(χ)||B(χ)| ≤ Σ_{i:ι} M_i · binTerm (#class i) P q (Σ|a|²) B`, `W(χ) = dp S (aχ) h₀`. -/
theorem sum_typeII_cls {ι : Type*} [Fintype ι] [DecidableEq ι] (cl : DirichletCharacter ℂ q → ι) {P : ℕ} (hP : 0 < P)
    {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ℕ → ℂ) (h₀ : ℝ) (Bf : DirichletCharacter ℂ q → ℂ) (M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖Bf χ‖ ≤ M (cl χ))
    {B : ℝ} (hB0 : 0 ≤ B) (hK : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P) 0 n‖ ≤ B) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖dp S (fun j => a j * χ j) h₀‖ * ‖Bf χ‖ ≤
      ∑ i : ι, M i *
        binTerm ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = i).card) P q
          (∑ j ∈ S, ‖a j‖ ^ 2) B := by
  classical
  set W : DirichletCharacter ℂ q → ℂ := fun χ => dp S (fun j => a j * χ j) h₀ with hW
  set V : ℝ := ∑ j ∈ S, ‖a j‖ ^ 2 with hV
  -- split the sum over the bins: `Σ_{χ≠1} |W||Bf| ≤ Σ_i M_i Σ_{χ ∈ bin i} |W χ|`
  have hsplit : ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖W χ‖ * ‖Bf χ‖ ≤
      ∑ i : ι, M i *
        ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = i), ‖W χ‖ := by
    calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖W χ‖ * ‖Bf χ‖
        ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖W χ‖ * M (cl χ) := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          exact mul_le_mul_of_nonneg_left (hB χ (Finset.mem_filter.1 hχ).2) (norm_nonneg _)
      _ = ∑ i : ι, ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
            cl χ = i), ‖W χ‖ * M i := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := cl) (t := Finset.univ) (fun χ _ => Finset.mem_univ _)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.filter_filter]
          exact Finset.sum_congr rfl fun χ hχ => by rw [(Finset.mem_filter.1 hχ).2.2]
      _ = ∑ i : ι, M i *
            ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = i), ‖W χ‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  refine hsplit.trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hM i))
  set R := (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ cl χ = i) with hR
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => by positivity
  -- the bin's sum is at most each of the two bounds
  have hT1 : ∑ χ ∈ R, ‖W χ‖ ≤ Real.sqrt R.card * Real.sqrt ((P + q) * V) := by
    -- Cauchy–Schwarz over the bin, then orthogonality over all characters (`sum_chars_dp_sq_le`)
    have hcs : (∑ χ ∈ R, ‖W χ‖) ^ 2 ≤ R.card * ∑ χ ∈ R, ‖W χ‖ ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq R (fun _ => (1 : ℝ)) (fun χ => ‖W χ‖)
      simpa using this
    have hle : ∑ χ ∈ R, ‖W χ‖ ^ 2 ≤ (P + q) * V :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) fun _ _ _ => by positivity).trans
        (sum_chars_dp_sq_le hS a q h₀)
    have h0 : 0 ≤ ∑ χ ∈ R, ‖W χ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq h0]
    exact Real.sqrt_le_sqrt (hcs.trans (mul_le_mul_of_nonneg_left hle (by positivity)))
  have hHM : ∑ χ ∈ R, ‖W χ‖ ≤ Real.sqrt (Real.exp 1 * V * (R.card * (2 * P) + R.card ^ 2 * B)) := by
    have h := sum_bin_hm hP hS a h₀ R hB0 hK
    have h0 : 0 ≤ ∑ χ ∈ R, ‖W χ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [← Real.sqrt_sq h0]
    exact Real.sqrt_le_sqrt h
  exact le_min hT1 hHM

end SieveTypeIIHM
