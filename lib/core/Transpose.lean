/-
# Transposing the spheres: the negated form, the dual lattice and the pole plane

Plain statement. Swap the roles of the positive and negative parts of Weil's form for `ζ` (`BallWeil`, `BallPole`).
* **The negated form `B' = −B`.** The pole plane stays hyperbolic and, under RH, `B'` is positive on the pole
  complement: signature `(∞, 1)` rather than `(1, ∞)`. The transposed axioms of `HodgeAxioms` fail, unconditionally:
  - the transposed dichotomy `D² < 0 ⇒ ±D effective` fails for the cone of nonnegative classes: `D = e₁ − e₂` has
    `D² = −2` (`transposed_rr_fails`);
  - the natural ample class for `B'` is `h' = e₁ − e₂` (`B'(h', h') = 2`), and it is not positive on that cone:
    `B'(e₂, h') = −1` (`transposed_ample_fails`);
  - and the transposed conclusion, `D·h' = 0 ⇒ D² ≥ 0`, is false, unconditionally: the class
    `D = D_1 − e₁ − e₂` has `D·e₁ = D·e₂ = 0` and `D² = −K_H(1) < 0` (`transposed_hodge_false`).
  So `B'` is not of Hodge index type: the complement carries infinitely many positive directions of `B'`, and no
  single ample class controls them.
* **The dual lattice.** On a finite section the Gram matrix of the orbit is positive definite exactly when its inverse
  is (`posDef_iff_inv`): transposing to the dual basis is an equivalent statement, not a weaker one.
-/
import Mathlib
import HodgeAxioms

open Finset Matrix

noncomputable section

namespace Transpose

open BallWeil BallPole HodgeAxioms

/-- The polar form of `D² = selfInt`, `B(D, D') = ((D + D')² − D² − D'²)/2`. -/
def pairing (a b : ℝ) (N : ℕ) (c : ℕ → ℝ) (a' b' : ℝ) (c' : ℕ → ℝ) : ℝ :=
  (selfInt (a + a') (b + b') N (fun n => c n + c' n) - selfInt a b N c - selfInt a' b' N c') / 2

/-- **The transposed dichotomy fails**: `(e₁ − e₂)² = −2 < 0`, and `e₁ − e₂` has coefficients of both signs. -/
theorem transposed_rr_fails (N : ℕ) : selfInt 1 (-1) N (fun _ => 0) < 0 := by
  rw [selfInt_pole]; norm_num

/-- **The transposed ampleness fails**: `B(e₂, e₁ − e₂) = 1`, so `B'(e₂, h') = −1 < 0` for the effective class `e₂`. -/
theorem transposed_ample_fails (N : ℕ) : pairing 0 1 N (fun _ => 0) 1 (-1) (fun _ => 0) = 1 := by
  unfold pairing
  simp only [add_zero]
  rw [show (0 : ℝ) + 1 = 1 by norm_num, show (1 : ℝ) + -1 = 0 by norm_num]
  rw [show (fun _ : ℕ => (0 : ℝ)) = fun _ => 0 from rfl]
  simp only [selfInt_pole]
  norm_num

/-- **The transposed Hodge index statement is false**, unconditionally: `D = D_1 − e₁ − e₂` is orthogonal to `e₁` and
`e₂` (so to `e₁ − e₂`) and has `D² = −K_H(1) < 0`. -/
theorem transposed_hodge_false :
    PoleOrth (-1) (-1) 1 (fun n => if n = 1 then 1 else 0) ∧
      selfInt (-1) (-1) 1 (fun n => if n = 1 then 1 else 0) < 0 := by
  have ho : PoleOrth (-1) (-1) 1 (fun n => if n = 1 then 1 else 0) := by
    constructor <;> simp [deg₁, deg₂]
  refine ⟨ho, ?_⟩
  rw [selfInt_of_orth ho]
  have : form 1 (fun n => if n = 1 then 1 else 0) = gram 1 1 := by
    simp [form]
  rw [this, gram_self]
  have := kψ_one_pos
  simp only [Nat.cast_one, one_mul]
  linarith

/-- The Gram matrix of the orbit on `1, …, N`. -/
def gramMat (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := fun i j => gram ((i : ℕ) + 1) ((j : ℕ) + 1)

/-- **The dual lattice**: the Gram matrix is positive definite exactly when its inverse is. -/
theorem posDef_iff_inv (N : ℕ) : (gramMat N).PosDef ↔ (gramMat N)⁻¹.PosDef :=
  Matrix.posDef_inv_iff.symm

end Transpose

#print axioms Transpose.transposed_rr_fails
#print axioms Transpose.transposed_ample_fails
#print axioms Transpose.transposed_hodge_false
#print axioms Transpose.posDef_iff_inv
