/-
# Outer products in the limit

Plain statement. A kernel that is a finite sum of outer products with nonnegative weights,
`g(m, n) = Σ_i w_i f_i(m) f_i(n)`, has nonnegative form (`formG_outer_nonneg`). Nonnegativity of the form is closed
under pointwise limits of kernels (`formG_nonneg_of_tendsto`). Hence, if the prime-side Gram kernel is a pointwise
limit of such outer-product sums, RH follows (`rh_of_outer_limit`); conversely, under RH the form is nonnegative
(`DeSitterTower.rh_iff_form_real`). The only such decomposition known is the sum over the zeros (Bochner), so this is
a reformulation.
-/
import Mathlib
import DeSitterTower

open Finset Filter Topology

noncomputable section

namespace OuterLimit

open BallWeil BallPole

/-- The kernel `Σ_{i ∈ s} w_i f_i(m) f_i(n)`. -/
def outer {ι : Type*} (s : Finset ι) (w : ι → ℝ) (f : ι → ℕ → ℝ) (m n : ℕ) : ℝ := ∑ i ∈ s, w i * f i m * f i n

/-- **Outer-product sums are positive.** -/
theorem formG_outer_nonneg {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (f : ι → ℕ → ℝ)
    (N : ℕ) (c : ℕ → ℝ) : 0 ≤ formG (outer s w f) N c := by
  have h : formG (outer s w f) N c = ∑ i ∈ s, w i * (∑ n ∈ Icc 1 N, c n * f i n) ^ 2 := by
    calc formG (outer s w f) N c
        = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ∑ i ∈ s, c m * c n * (w i * f i m * f i n) := by
          simp only [formG, outer, Finset.mul_sum]
      _ = ∑ m ∈ Icc 1 N, ∑ i ∈ s, ∑ n ∈ Icc 1 N, c m * c n * (w i * f i m * f i n) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i ∈ s, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * (w i * f i m * f i n) := Finset.sum_comm
      _ = ∑ i ∈ s, w i * (∑ n ∈ Icc 1 N, c n * f i n) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  rw [h]; exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)

/-- **Positivity is closed under pointwise limits of kernels.** -/
theorem formG_nonneg_of_tendsto (g : ℕ → ℕ → ℕ → ℝ) (g₀ : ℕ → ℕ → ℝ)
    (hg : ∀ m n, Tendsto (fun j => g j m n) atTop (𝓝 (g₀ m n))) (N : ℕ) (c : ℕ → ℝ)
    (hpos : ∀ j, 0 ≤ formG (g j) N c) : 0 ≤ formG g₀ N c := by
  have ht : Tendsto (fun j => formG (g j) N c) atTop (𝓝 (formG g₀ N c)) := by
    unfold formG
    refine tendsto_finsetSum _ fun m _ => tendsto_finsetSum _ fun n _ => ?_
    exact (hg m n).const_mul _
  exact ge_of_tendsto' ht hpos

/-- **An outer-product limit for the Gram kernel gives RH.** -/
theorem rh_of_outer_limit {ι : Type*} (s : ℕ → Finset ι) (w : ℕ → ι → ℝ) (hw : ∀ j, ∀ i ∈ s j, 0 ≤ w j i)
    (f : ℕ → ι → ℕ → ℝ) (hg : ∀ m n, Tendsto (fun j => outer (s j) (w j) (f j) m n) atTop (𝓝 (gram m n))) :
    RiemannHypothesis :=
  DeSitterTower.rh_iff_form_real.2 fun N c =>
    formG_nonneg_of_tendsto _ gram hg N c fun j => formG_outer_nonneg _ _ (hw j) _ N c
