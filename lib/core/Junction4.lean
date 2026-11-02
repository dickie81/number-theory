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

end Junction4

#print axioms Junction4.glued_nonneg
#print axioms Junction4.glued_nonneg_four
