import Mathlib
import WeilOdd
import CmEncP

/-! # Unconditional positivity at `L = 1/2` for odd probes and for mixed even + odd probes, in `weilQg` -/

namespace WeilOdd

open Real Finset WeilPlanch WeilZhuRed

lemma QF_eq_zero (par : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → ℝ) (h : ∀ i ∈ range N, x i = 0) : QF par σ N x = 0 := by
  have hF : ∀ t, Fx par N x t = 0 := fun t => by
    unfold Fx; exact sum_eq_zero fun i hi => by rw [h i hi, zero_mul]
  unfold QF
  rw [sum_eq_zero fun i hi => by rw [h i hi, zero_mul]]
  simp [hF]

lemma hx_y0 (N : ℕ) (x : ℕ → ℝ) : hx N x 0 = fx N x := by
  funext u; unfold hx gx; simp

lemma hx_x0 (N : ℕ) (y : ℕ → ℝ) : hx N 0 y = gx N y := by
  funext u; unfold hx fx; simp

lemma weilQg_fx (N : ℕ) (x : ℕ → ℝ) : WeilForm.weilQg (1 / 2) (fx N x) = WeilForm.weilQ (1 / 2) (fx N x) := by
  have hR := poleR_hx N x 0
  have hL := poleL_hx N x 0
  rw [hx_y0] at hR hL
  simp only [Pi.zero_apply, zero_mul, sum_const_zero, add_zero, sub_zero] at hR hL
  rw [WeilForm.weilQ_eq']
  unfold WeilForm.weilQg
  rw [hL, ← hR]; ring

theorem QF0_eq (N : ℕ) (x : ℕ → ℝ) : QF 0 1 N x = WeilForm.weilQ (1 / 2) (fx N x) := by
  have := weilQg_hx N x 0
  rw [QF_eq_zero 1 (-1) N 0 (fun _ _ => rfl), add_zero, hx_y0, weilQg_fx] at this
  exact this.symm

lemma QF0_nonneg (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) : 0 ≤ QF 0 1 N x := by
  by_cases h : ∃ i ∈ range N, x i ≠ 0
  · rw [QF0_eq]; exact (CmFin.L05_even_uncond N hN x h).le
  · push Not at h; rw [QF_eq_zero 0 1 N x h]

lemma QF1_nonneg (N : ℕ) (hN : 28 ≤ N) (y : ℕ → ℝ) : 0 ≤ QF 1 (-1) N y := by
  by_cases h : ∃ i ∈ range N, y i ≠ 0
  · exact (CmFin.L05_odd_uncond N hN y h).le
  · push Not at h; rw [QF_eq_zero 1 (-1) N y h]

/-- **Mixed probes.** For `N ≥ 28` and `(x, y) ≠ 0`, the general Weil form is positive on
`Σ_{i<N} xᵢ T_{2i} + Σ_{i<N} yᵢ T_{2i+1}`. -/
theorem L05_mixed (N : ℕ) (hN : 28 ≤ N) (x y : ℕ → ℝ)
    (h : (∃ i ∈ range N, x i ≠ 0) ∨ (∃ i ∈ range N, y i ≠ 0)) :
    0 < WeilForm.weilQg (1 / 2) (fun u => fx N x u + gx N y u) := by
  show 0 < WeilForm.weilQg (1 / 2) (hx N x y)
  rw [weilQg_hx]
  rcases h with h | h
  · rw [QF0_eq]; have := CmFin.L05_even_uncond N hN x h; have := QF1_nonneg N hN y; linarith
  · have := CmFin.L05_odd_uncond N hN y h; have := QF0_nonneg N hN x; linarith

/-- **Odd probes, general Weil form.** -/
theorem L05_odd_weilQg (N : ℕ) (hN : 28 ≤ N) (y : ℕ → ℝ) (h : ∃ i ∈ range N, y i ≠ 0) :
    0 < WeilForm.weilQg (1 / 2) (gx N y) := by
  have := L05_mixed N hN 0 y (Or.inr h)
  rwa [show (fun u => fx N 0 u + gx N y u) = gx N y from hx_x0 N y] at this

/-- **Odd probes, the library's even-probe form `weilQ`.** For odd `g`, `weilQ = weilQg + 4 poleR² ≥ weilQg`. -/
theorem L05_odd_weilQ (N : ℕ) (hN : 28 ≤ N) (y : ℕ → ℝ) (h : ∃ i ∈ range N, y i ≠ 0) :
    0 < WeilForm.weilQ (1 / 2) (gx N y) := by
  have hg := L05_odd_weilQg N hN y h
  have hR := poleR_hx N 0 y
  have hL := poleL_hx N 0 y
  rw [hx_x0] at hR hL
  simp only [Pi.zero_apply, zero_mul, sum_const_zero, zero_add, zero_sub] at hR hL
  rw [WeilForm.weilQ_eq']
  unfold WeilForm.weilQg at hg
  rw [hL, hR] at hg; rw [hR]
  nlinarith [sq_nonneg (∑ i ∈ range N, y i * WeilTailB.pole (2 * i + 1))]

end WeilOdd
