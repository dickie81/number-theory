/-
# The gravastar margin

Plain statement. Say the tower has **margin** `f(N)` at level `N` when `f(N)·‖x‖² ≤ Q_N(x)` for every real vector on
`1, …, N`. Any nonnegative margin at every level gives RH (`rh_of_margin`), and RH gives the margin `0`
(`margin_zero_of_rh`). Contrapositive: if RH fails, some level has a vector with `Q_N(x) < 0`, and then every higher
level does too (`neg_persists`), so a failure, once it appears, never heals. A positive margin that tends to `0` is
consistent with RH and proves nothing by itself: the content is the sign, not the rate.
-/
import Mathlib
import GravastarTower

open Finset

noncomputable section

namespace GravastarMargin

open BallWeil GravastarTower

/-- The tower has margin `f` at level `N`. -/
def HasMargin (N : ℕ) (f : ℝ) : Prop := ∀ x : ℕ → ℝ, f * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ form N x

theorem margin_iff_excess (N : ℕ) (f : ℝ) : HasMargin N f ↔ ExcessLe N (-f) := by
  unfold HasMargin ExcessLe
  constructor <;> intro h x <;> have := h x <;> linarith

/-- **A nonnegative margin at every level gives RH.** -/
theorem rh_of_margin (f : ℕ → ℝ) (hf : ∀ N, 0 ≤ f N) (h : ∀ N, HasMargin N (f N)) : RiemannHypothesis := by
  refine rh_iff_balance.2 fun N x => ?_
  have h1 := h N x
  have h2 : 0 ≤ f N * ∑ n ∈ Icc 1 N, x n ^ 2 := mul_nonneg (hf N) (Finset.sum_nonneg fun n _ => sq_nonneg _)
  simp only [zero_mul]; linarith

theorem margin_zero_of_rh (hRH : RiemannHypothesis) (N : ℕ) : HasMargin N 0 := by
  intro x; simp only [zero_mul]; exact form_nonneg hRH N x

/-- **If RH fails, some level has a negative vector.** -/
theorem exists_neg_of_not_rh (h : ¬ RiemannHypothesis) : ∃ (N : ℕ) (x : ℕ → ℝ), form N x < 0 := by
  by_contra hc; push Not at hc
  exact h (rh_of_margin (fun _ => 0) (fun _ => le_rfl) fun N x => by simpa using hc N x)

/-- **Failures persist up the tower.** -/
theorem neg_persists {N N' : ℕ} (hNN' : N ≤ N') {x : ℕ → ℝ} (hx : form N x < 0) : ∃ y : ℕ → ℝ, form N' y < 0 := by
  by_contra hc; push Not at hc
  have hE : ExcessLe N' 0 := fun y => by simp only [zero_mul]; linarith [hc y]
  have := excess_mono hNN' hE x
  simp only [zero_mul] at this; linarith
