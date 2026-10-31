import Mathlib

/-! # The saturation step, reduced to an envelope bound

The model assumes saturation: below the edge, every zeta zero `γ_j` has a zero of the
ground state's transform `ĝ` exponentially close to it. That statement is about the zeta zeros, so
it has to go through the explicit formula `Q(g) = Σ_ρ ĝ(t_ρ)²`. Off the critical line those terms are
complex and cannot be bounded one at a time, so full saturation from the prime side alone is as
hard as Hypothesis D (item 1(a)).

What is proved here is the step from a small value to a nearby zero, where the envelope `|ĝ'|` is
bounded below:
* `zero_near_of_deriv_ge` and `zero_near_of_deriv_le`: a function that is at most `η` in size at
  `γ`, with `|F'| ≥ m` of fixed sign on `[γ − r, γ + r]` and `η/m ≤ r`, vanishes within `η/m`
  of `γ`.

`Unconditional.lean` bounds `|ĝ|` at the verified zeros through the explicit formula and applies this
step there (`pinned_unconditional`). -/

open Set

namespace WeilForm

/-- **A small value and a steep increasing slope force a nearby zero.** -/
theorem zero_near_of_deriv_ge {F : ℝ → ℝ} {γ η m r : ℝ} (hm : 0 < m) (hη : 0 ≤ η) (hr : η / m ≤ r)
    (hc : ContinuousOn F (Icc (γ - r) (γ + r))) (hd : DifferentiableOn ℝ F (Ioo (γ - r) (γ + r)))
    (hslope : ∀ x ∈ Ioo (γ - r) (γ + r), m ≤ deriv F x) (hsmall : |F γ| ≤ η) :
    ∃ x ∈ Icc (γ - η / m) (γ + η / m), F x = 0 := by
  set s := η / m with hs
  have hs0 : 0 ≤ s := div_nonneg hη hm.le
  have hms : m * s = η := by rw [hs]; field_simp
  have hint : interior (Icc (γ - r) (γ + r)) = Ioo (γ - r) (γ + r) := interior_Icc
  have key := (convex_Icc (γ - r) (γ + r)).mul_sub_le_image_sub_of_le_deriv hc
    (by rwa [hint]) (fun x hx => hslope x (by rwa [hint] at hx))
  have hr0 : 0 ≤ r := hs0.trans hr
  have mem1 : γ - s ∈ Icc (γ - r) (γ + r) := ⟨by linarith, by linarith⟩
  have mem2 : γ ∈ Icc (γ - r) (γ + r) := ⟨by linarith, by linarith⟩
  have mem3 : γ + s ∈ Icc (γ - r) (γ + r) := ⟨by linarith, by linarith⟩
  have h1 := key _ mem1 _ mem2 (by linarith)
  have h2 := key _ mem2 _ mem3 (by linarith)
  have hab := abs_le.1 hsmall
  have hlo : F (γ - s) ≤ 0 := by
    have : m * (γ - (γ - s)) = η := by rw [← hms]; ring
    linarith
  have hhi : 0 ≤ F (γ + s) := by
    have : m * (γ + s - γ) = η := by rw [← hms]; ring
    linarith
  have hsub : Icc (γ - s) (γ + s) ⊆ Icc (γ - r) (γ + r) :=
    Icc_subset_Icc (by linarith) (by linarith)
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc (by linarith : γ - s ≤ γ + s) (hc.mono hsub)
    ⟨hlo, hhi⟩
  exact ⟨x, hx, hFx⟩

/-- The decreasing case. -/
theorem zero_near_of_deriv_le {F : ℝ → ℝ} {γ η m r : ℝ} (hm : 0 < m) (hη : 0 ≤ η) (hr : η / m ≤ r)
    (hc : ContinuousOn F (Icc (γ - r) (γ + r))) (hd : DifferentiableOn ℝ F (Ioo (γ - r) (γ + r)))
    (hslope : ∀ x ∈ Ioo (γ - r) (γ + r), deriv F x ≤ -m) (hsmall : |F γ| ≤ η) :
    ∃ x ∈ Icc (γ - η / m) (γ + η / m), F x = 0 := by
  obtain ⟨x, hx, h⟩ := zero_near_of_deriv_ge (F := fun x => -F x) hm hη hr hc.neg hd.neg
    (fun x hx => by
      have := hslope x hx
      rw [deriv.fun_neg]; linarith)
    (by simpa [abs_neg] using hsmall)
  exact ⟨x, hx, by simpa using h⟩

end WeilForm

#print axioms WeilForm.zero_near_of_deriv_ge
#print axioms WeilForm.zero_near_of_deriv_le
