/-
# The certificate to depth 8, by parts

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements about the sums of `SieveDeepDefs.lean`, for a certificate checked by the kernel in parts.

* `rowsJD_eq`: `rowsJD a b j₀ j₁` is the double sum of the costs over `a ≤ i < b` and `j₀ ≤ j < j₁`.
* `totalD_eq_rowsJD`: the total is `rowsJD 0 n 0 n`.
* `rowsJD_le_of_splitJ`, `rowsJD_le_of_splitI`: a bound on the sum over a range of columns, or of rows, from bounds
  on two consecutive ranges.

The file imports `SieveDeepDefs.lean` and `SieveCert.lean`.
-/
import SieveDeepDefs
import SieveCert

namespace SieveDeep

open SieveCert

variable [Grid] [IBPar]

/-- `rowsJD a b j₀ j₁` is the double sum of the costs over `a ≤ i < b` and `j₀ ≤ j < j₁`. -/
theorem rowsJD_eq (a b j₀ j₁ : ℕ) :
    rowsJD a b j₀ j₁ = ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico j₀ j₁, costD i j := by
  rw [rowsJD, sumTo_eq, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sumTo_eq, Finset.sum_Ico_eq_sum_range]

/-- The certificate's total is `rowsJD 0 n 0 n`. -/
theorem totalD_eq_rowsJD : totalD = rowsJD 0 n 0 n := by
  simp only [rowsJD_eq, totalD, sumTo_eq, Finset.range_eq_Ico]

/-- For `j₀ ≤ j₁ ≤ j₂` (`h₁`, `h₂`), `rowsJD a b j₀ j₂ = rowsJD a b j₀ j₁ + rowsJD a b j₁ j₂`. -/
theorem rowsJD_splitJ (a b : ℕ) {j₀ j₁ j₂ : ℕ} (h₁ : j₀ ≤ j₁) (h₂ : j₁ ≤ j₂) :
    rowsJD a b j₀ j₂ = rowsJD a b j₀ j₁ + rowsJD a b j₁ j₂ := by
  simp only [rowsJD_eq, ← Finset.sum_add_distrib, Finset.sum_Ico_consecutive _ h₁ h₂]

/-- For `a ≤ b ≤ c` (`hab`, `hbc`), `rowsJD a c j₀ j₁ = rowsJD a b j₀ j₁ + rowsJD b c j₀ j₁`. -/
theorem rowsJD_splitI {a b c : ℕ} (j₀ j₁ : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    rowsJD a c j₀ j₁ = rowsJD a b j₀ j₁ + rowsJD b c j₀ j₁ := by
  simp only [rowsJD_eq, Finset.sum_Ico_consecutive _ hab hbc]

/-- A bound on `rowsJD a b j₀ j₂` from bounds on `rowsJD a b j₀ j₁` (`h₁`) and `rowsJD a b j₁ j₂` (`h₂`), for
`j₀ ≤ j₁ ≤ j₂` (`h₀₁`, `h₁₂`), with the bounds' sum at most `B` (`hB`). -/
theorem rowsJD_le_of_splitJ (a b : ℕ) {j₀ j₁ j₂ B₁ B₂ B : ℕ} (h₀₁ : j₀ ≤ j₁) (h₁₂ : j₁ ≤ j₂)
    (h₁ : rowsJD a b j₀ j₁ ≤ B₁) (h₂ : rowsJD a b j₁ j₂ ≤ B₂) (hB : B₁ + B₂ ≤ B) : rowsJD a b j₀ j₂ ≤ B := by
  rw [rowsJD_splitJ a b h₀₁ h₁₂]; exact (Nat.add_le_add h₁ h₂).trans hB

/-- A bound on `rowsJD a c j₀ j₁` from bounds on `rowsJD a b j₀ j₁` (`h₁`) and `rowsJD b c j₀ j₁` (`h₂`), for
`a ≤ b ≤ c` (`hab`, `hbc`), with the bounds' sum at most `B` (`hB`). -/
theorem rowsJD_le_of_splitI {a b c B₁ B₂ B : ℕ} (j₀ j₁ : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : rowsJD a b j₀ j₁ ≤ B₁) (h₂ : rowsJD b c j₀ j₁ ≤ B₂) (hB : B₁ + B₂ ≤ B) : rowsJD a c j₀ j₁ ≤ B := by
  rw [rowsJD_splitI j₀ j₁ hab hbc]; exact (Nat.add_le_add h₁ h₂).trans hB

end SieveDeep
