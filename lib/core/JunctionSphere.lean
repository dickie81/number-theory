/-
# The junction as a sphere: Gram realisations and the remainder

Plain statement. If the kernel restricted to the classes is a Gram matrix of real vectors in one inner product space
(the junction lies in a common sphere), its form is a squared norm and is nonnegative (`formG_gram`). For any split of
the prime-side Gram kernel as `gram = g₁ − g₂` the form splits the same way (`formG_sub`), and **RH holds if and only if
the remainder form never exceeds the part form**: `Q_{g₂} ≤ Q_{g₁}` on every real vector (`rh_iff_remainder`). With
`g₁` a manifest Gram kernel, positivity of the glued form follows from the remainder bound, and is equivalent to it.
These are reformulations: no zero-free Gram realisation of the full kernel is given here.
-/
import Mathlib
import BallPole

open Finset

noncomputable section

namespace JunctionSphere

open BallWeil BallPole

/-- **A Gram kernel has nonnegative form**: `Σ c_m c_n ⟪v_m, v_n⟫ = ‖Σ c_n v_n‖²`. -/
theorem formG_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ℕ → E) (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ formG (fun m n => inner ℝ (v m) (v n)) N c := by
  have h : formG (fun m n => inner ℝ (v m) (v n)) N c =
      inner ℝ (∑ m ∈ Icc 1 N, c m • v m) (∑ n ∈ Icc 1 N, c n • v n) := by
    simp only [formG, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [real_inner_comm]; ring
  rw [h]; exact real_inner_self_nonneg

theorem formG_sub (g₁ g₂ : ℕ → ℕ → ℝ) (N : ℕ) (c : ℕ → ℝ) :
    formG (fun m n => g₁ m n - g₂ m n) N c = formG g₁ N c - formG g₂ N c := by
  simp only [formG, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  ring

theorem form_eq_formG (N : ℕ) (c : ℕ → ℝ) : form N c = formG gram N c := rfl

/-- **RH is the remainder bound**, for any split `gram = g₁ − g₂`. -/
theorem rh_iff_remainder (g₁ g₂ : ℕ → ℕ → ℝ) (h : ∀ m n, gram m n = g₁ m n - g₂ m n) :
    RiemannHypothesis ↔ ∀ (N : ℕ) (c : ℕ → ℝ), formG g₂ N c ≤ formG g₁ N c := by
  have hf : ∀ N c, form N c = formG g₁ N c - formG g₂ N c := by
    intro N c; rw [form_eq_formG, ← formG_sub]; congr 1; funext m n; exact h m n
  constructor
  · intro hRH N c; have := form_nonneg hRH N c; rw [hf] at this; linarith
  · intro H; refine rh_iff_form.2 fun N x => ?_; rw [hf]; linarith [H N (fun n => x n)]

/-- **Gram part plus bounded remainder gives positivity.** -/
theorem nonneg_of_remainder {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ℕ → E)
    (g₂ : ℕ → ℕ → ℝ) (h : ∀ m n, gram m n = inner ℝ (v m) (v n) - g₂ m n) (N : ℕ) (c : ℕ → ℝ)
    (hr : formG g₂ N c ≤ formG (fun m n => inner ℝ (v m) (v n)) N c) : 0 ≤ form N c := by
  rw [form_eq_formG, show (gram) = fun m n => inner ℝ (v m) (v n) - g₂ m n from funext fun m => funext (h m),
    formG_sub]; linarith
