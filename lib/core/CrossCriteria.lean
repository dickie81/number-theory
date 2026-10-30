import WeilChiCriterion
import MertensOmega
import ShortPrimes
import WeilRate
import Zeta

/-! # GRH modulo real zeros, and the missing Props stated

With `hS`, GRH off the real axis is GRH (`grh_of_cross`); one-sided Liouville bounds at every `θ > ½` give RH. The
open inputs the density route and the `χ` chain would need are stated as named `Prop`s: `ZetaCritBound c`,
`ConvexityBound`, `WeylBound`, `Lindelof`, `DensityHypothesis`, `GRHCross χ`, `PsiOmegaSqrt`.
-/

open Real Complex MeasureTheory Filter Topology Set

noncomputable section

namespace CrossCriteria

open PsiOmega WeilForm WeilTest WeilStrip DirichletCharacter

/-! ### (A) Real zeros are invisible to even real probes -/

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- The converse direction of `grh_iff_twins` is the only place `hS` enters: with `hS` the cross
hypothesis is GRH. -/
theorem grh_of_cross (hcross : ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 ∨ s.im = 0)
    (hS : ∀ σ : ℝ, 0 < σ → σ < 1 → LFunction χ σ ≠ 0) : GRH χ := by
  intro s hs h0 h1
  rcases hcross s hs h0 h1 with h | h
  · exact h
  · exfalso
    have e : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [h])
    rw [e] at hs
    exact hS s.re h0 h1 hs

/-! ### (B) The θ-family Liouville route -/

/-- **RH from one-sided Liouville bounds at every exponent `θ > ½`.** Unlike `rh_of_liouville_bound`
(exponent exactly `½`), the hypothesis is the one RH is expected to give. -/
theorem rh_of_liouville_theta {ε : ℝ} (hε : ε ≠ 0)
    (h : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ c : ℝ, ∀ x : ℝ, 1 < x → ε * summ fLi x ≤ c * x ^ θ) :
    RiemannHypothesis := by
  refine PsiOmega.rh_of_zeroFree_half fun ρ hρ => ?_
  rcases le_or_gt 1 ρ.re with h1' | h1'
  · exact zeta_ne_zero_re_ge_one h1'
  · obtain ⟨c, hc⟩ := h ((1 / 2 + ρ.re) / 2) (by linarith) (by linarith)
    exact zeta_ne_zero_of_liouville (by linarith) (by linarith) hε hc (by linarith)

/-! ### (C) The exact missing Props

Well-typed; none was proved in the three layers. `lib/pnt/Subconvexity.lean` proves `ConvexityBound`,
`ZetaCritBound (5/24 + ε)` for every `ε > 0`, and `Lindelof` under `RiemannHypothesis`. -/

/-- Pointwise growth exponent `c` for `ζ` on the critical line. -/
def ZetaCritBound (c : ℝ) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ c

/-- The convexity bound (Lindelöf 1908: functional equation + Phragmén–Lindelöf + Stirling). -/
def ConvexityBound : Prop := ∀ ε > 0, ZetaCritBound (1 / 4 + ε)

/-- Weyl–Hardy–Littlewood (van der Corput's method). -/
def WeylBound : Prop := ∀ ε > 0, ZetaCritBound (1 / 6 + ε)

/-- The Lindelöf hypothesis. -/
def Lindelof : Prop := ∀ ε > 0, ZetaCritBound ε

/-- The density route's target (PAPER): pointwise `c` gives Ingham's exponent `2 + 4c`. -/
def InghamFromC (c : ℝ) : Prop :=
  ZetaCritBound c → ∀ ε > 0, ∃ B : ℝ, ShortWeil.DensityXi (2 + 4 * c + ε) B

/-- The density hypothesis in the library's normalisation. -/
def DensityHypothesis : Prop := ∀ ε > 0, ∃ B : ℝ, ShortWeil.DensityXi (2 + ε) B

/-- GRH modulo real zeros (the cross hypothesis of `grh_of_cross`). -/
def GRHCross (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 ∨ s.im = 0

/-- `ψ(x) − x = Ω±(√x)` (Ingham's twist of the Landau argument, PAPER). -/
def PsiOmegaSqrt : Prop :=
  ∃ c > 0, ∀ X : ℝ, (∃ x, X < x ∧ c * x ^ (1 / 2 : ℝ) < Chebyshev.psi x - x) ∧
    (∃ x, X < x ∧ Chebyshev.psi x - x < -(c * x ^ (1 / 2 : ℝ)))

end CrossCriteria

#print axioms CrossCriteria.grh_of_cross
#print axioms CrossCriteria.rh_of_liouville_theta
