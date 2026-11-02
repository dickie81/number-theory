/-
# Spheres meeting in a k-dimensional junction

Plain statement. If the cross terms between two blocks factor through a `k`-dimensional space,
`cross(x, y) = Σ_{i<k} p_i(x)·q_i(y)`, then the glued form `Q_S(x) + Q_T(y) + 2·cross(x, y)` is nonnegative as soon as
each block dominates its own junction coordinates: `Q_S(x) ≥ Σ p_i(x)²` and `Q_T(y) ≥ Σ q_i(y)²`
(`glued_nonneg`). The case `k = 4` is `glued_nonneg_four`. This is a sufficient condition only; it says nothing
about whether the orbit form's cross terms have such a factorisation (numerically they do not: full rank).
-/
import Mathlib

open Finset

namespace Junction4

/-- **Gluing through a `k`-dimensional junction**. -/
theorem glued_nonneg {k : ℕ} (QS QT : ℝ) (p q : Fin k → ℝ) (hS : ∑ i, p i ^ 2 ≤ QS)
    (hT : ∑ i, q i ^ 2 ≤ QT) : 0 ≤ QS + QT + 2 * ∑ i, p i * q i := by
  have h0 : 0 ≤ ∑ i, (p i + q i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have : ∑ i, (p i + q i) ^ 2 = ∑ i, p i ^ 2 + ∑ i, q i ^ 2 + 2 * ∑ i, p i * q i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- The four-dimensional junction. -/
theorem glued_nonneg_four (QS QT : ℝ) (p q : Fin 4 → ℝ) (hS : ∑ i, p i ^ 2 ≤ QS)
    (hT : ∑ i, q i ^ 2 ≤ QT) : 0 ≤ QS + QT + 2 * ∑ i, p i * q i :=
  glued_nonneg QS QT p q hS hT

/-- **Gluing by positive weights is a congruence** (area weighting). Scaling coordinate `i` by `√w_i` with all
`w_i > 0`, i.e. the form `x ↦ Σ_{ij} G_ij √w_i √w_j x_i x_j`, is nonnegative iff `G` is. So weighting the spheres by
surface areas (or any positive weights) cannot change whether the glued form is positive. -/
theorem weighted_nonneg_iff {n : ℕ} (G : Fin n → Fin n → ℝ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    (∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, G i j * (Real.sqrt (w i) * x i) * (Real.sqrt (w j) * x j)) ↔
      ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, G i j * x i * x j := by
  have hs : ∀ i, Real.sqrt (w i) ≠ 0 := fun i => (Real.sqrt_pos.2 (hw i)).ne'
  constructor
  · intro h x
    have := h fun i => x i / Real.sqrt (w i)
    simpa [mul_div_cancel₀ _ (hs _)] using this
  · intro h x
    exact h fun i => Real.sqrt (w i) * x i

end Junction4

#print axioms Junction4.glued_nonneg
#print axioms Junction4.glued_nonneg_four
#print axioms Junction4.weighted_nonneg_iff
