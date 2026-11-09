/-
# Chen–Gupta–Li's density estimate for any continuation of the `L`-series

`LinnikCGL.CGLDensity` counts the characters `χ` mod `q` whose `LFunction χ` has a zero in `Re s ≥ σ`, `|Im s| ≤ T`.
`LFunction` is Mathlib's, built from Hurwitz zeta functions. This file states the estimate without it. Take any
functions `F χ`, differentiable on `ℂ ∖ {1}`, that agree on `Re s > 1` with the `L`-series `Σ χ(n) n^{−s}` (Mathlib's
`LSeries`). At most `C(qT)^{(7/3)(1−σ)+ε}` characters have an `F χ` with a zero in Chen, Gupta and Li's rectangle
`σ ≤ Re s ≤ 1`, `|Im s| ≤ T`, other than at the pole `s = 1`.

Such functions exist, and on `ℂ ∖ {1}` they are `LFunction χ`, by the identity theorem. So the statement is not
vacuous, and it follows from `CGLDensity` with the same constant. But what it says does not depend on how Mathlib
builds `LFunction`: its statement names only `LSeries`, complex differentiability, Dirichlet characters, finite sets
and real powers.

* `eqOn_LFunction`: a function differentiable on `ℂ ∖ {1}` that agrees with the `L`-series of `χ` on `Re s > 1`
  is `LFunction χ` on `ℂ ∖ {1}`.
* `exists_continuation`: such a function exists.
* `cglDensity_of_continuation`: the estimate, for any such functions.
-/
import LinnikCGLDensity

namespace LinnikCGLContinuation

open DirichletCharacter

/-- **`LFunction χ` is the continuation of the `L`-series.** A function differentiable on `ℂ ∖ {1}` that agrees with
the `L`-series `Σ χ(n) n^{−s}` on `Re s > 1` is `LFunction χ` on `ℂ ∖ {1}`, by the identity theorem. -/
theorem eqOn_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {1}ᶜ) (hL : ∀ s : ℂ, 1 < s.re → F s = LSeries (χ ·) s) :
    Set.EqOn F (LFunction χ) {1}ᶜ := by
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have hχ : DifferentiableOn ℂ (LFunction χ) {1}ᶜ := fun s hs =>
    (differentiableAt_LFunction χ s (.inl hs)).differentiableWithinAt
  refine (hF.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (hχ.analyticOnNhd isOpen_compl_singleton) hU (z₀ := 2) (by norm_num) ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
  rw [hL s hs, LFunction_eq_LSeries χ hs]

/-- **A continuation exists.** Some function, `LFunction χ`, is differentiable on `ℂ ∖ {1}` and agrees with the
`L`-series of `χ` on `Re s > 1`. -/
theorem exists_continuation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re → F s = LSeries (χ ·) s :=
  ⟨LFunction χ, fun s hs => (differentiableAt_LFunction χ s (.inl hs)).differentiableWithinAt,
    fun _ hs => LFunction_eq_LSeries χ hs⟩

open scoped Classical in
/-- **Chen–Gupta–Li's density estimate on `[5/7, 16/21]`, for any continuation of the `L`-series.** For every
`ε > 0` there is `C` such that for every `q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, and any functions `F χ`
differentiable on `ℂ ∖ {1}` that agree with the `L`-series of `χ` on `Re s > 1`, at most `C(qT)^{(7/3)(1−σ)+ε}`
characters `χ` mod `q` have an `F χ` with a zero `s ≠ 1` in `σ ≤ Re s ≤ 1`, `|Im s| ≤ T`. -/
theorem cglDensity_of_continuation : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 7 ≤ σ →
    σ ≤ 16 / 21 → 2 ≤ T → ∀ F : DirichletCharacter ℂ q → ℂ → ℂ, (∀ χ, DifferentiableOn ℂ (F χ) {1}ᶜ) →
      (∀ χ (s : ℂ), 1 < s.re → F χ s = LSeries (χ ·) s) →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ s ≠ 1 ∧ F χ s = 0).card : ℝ) ≤
        C * ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ := LinnikCGLDensity.cglDensity ε hε
  refine ⟨C, fun q _ σ T h₁ h₂ hT F hF hL => le_trans ?_ (hC q σ T h₁ h₂ hT)⟩
  refine Nat.cast_le.mpr (Finset.card_le_card fun χ hχ => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
  obtain ⟨s, hσ, -, hs, h1, h0⟩ := hχ
  exact ⟨s, hσ, hs, eqOn_LFunction χ (hF χ) (hL χ) h1 ▸ h0⟩

end LinnikCGLContinuation

#print axioms LinnikCGLContinuation.eqOn_LFunction
#print axioms LinnikCGLContinuation.exists_continuation
#print axioms LinnikCGLContinuation.cglDensity_of_continuation
