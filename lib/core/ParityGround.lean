/-
# A simple ground state of a parity-invariant form is even or odd

Plain statement. Let `P` be a linear involution (`P (P v) = v`) on a real vector space. If `v ≠ 0` and
`P v = c • v` (as happens when `v` spans a one-dimensional eigenspace of a symmetric form commuting with `P`:
`P v` lies in the same eigenspace), then `c = 1` or `c = -1`, i.e. `v` is even or odd (`parity_of_simple`).
Abstract linear algebra only; it says nothing about whether the Weil form's ground state is simple.
-/
import Mathlib

namespace ParityGround

theorem parity_of_simple {V : Type*} [AddCommGroup V] [Module ℝ V] (P : V →ₗ[ℝ] V)
    (hP : ∀ w, P (P w) = w) (v : V) (hv : v ≠ 0) (c : ℝ) (hc : P v = c • v) :
    c = 1 ∨ c = -1 := by
  have h1 : v = (c * c) • v := by
    have := hP v
    rw [hc, map_smul, hc, smul_smul] at this
    exact this.symm
  have h2 : (c * c - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  have h3 : c * c - 1 = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hv
  have h4 : (c - 1) * (c + 1) = 0 := by ring_nf; linarith [h3]
  rcases mul_eq_zero.mp h4 with h | h
  · left; linarith
  · right; linarith

end ParityGround
