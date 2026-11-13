import Mathlib
import PivotPhi

/-! # The archimedean minorant of the pivot inequality: definitions

Plain statement. In the scale `s = t/N`, the archimedean weight `L(Ns) − log N`, `L(t) = Re ψ(¼ + it/2) − log π`, is
bounded below on `φ`'s support by the band-limited `μ = φλ − r`, independent of `N ≥ 2`:

* `λ(s) = 23/100 + (693/1000)Σ_{k < 30}(1 − sinc²(s/(10·2^k)))`, a staircase whose steps have transform support
  `2/(10·2^k) ≤ 1/5`, so that `φλ` has transform support `≤ 4/5 + 1/5 = 1`; its steps of height `0.693 < log 2` at the
  scales `10·2^k` follow `log s` (`lam`);
* `r(s) = Σ_j b_j(sinc²((s − γ_j)/2) + sinc²((s + γ_j)/2))`, nine nonnegative bumps of transform support `1`
  centred at `γ_j ≤ 17/2`, paying for the heights `s < 12` where `λ` is above `log(s/2π)` (`rr`, `bumpData`).

The pointwise inequality `μ(s) ≤ φ(s)(L(Ns) − log N)` for every `N ≥ 2` is `PivotSharp.MuLe`; `PivotMinorFT` proves
that `μ`'s transform vanishes for `|v| ≥ 1` and that `∫μ ≥ (7/8)φ̂(0)`.
-/

open Real MeasureTheory

noncomputable section

namespace PivotMinor

/-- The staircase `λ(s) = 23/100 + (693/1000)Σ_{k < 30}(1 − sinc²(s/(10·2^k)))`. -/
def lam (s : ℝ) : ℝ := 23 / 100 + 693 / 1000 * ∑ k ∈ Finset.range 30, (1 - Real.sinc (s / (10 * 2 ^ k)) ^ 2)

/-- The bump `sinc²((s − γ)/2) + sinc²((s + γ)/2)`. -/
def bump (γ s : ℝ) : ℝ := Real.sinc ((s - γ) / 2) ^ 2 + Real.sinc ((s + γ) / 2) ^ 2

/-- The bumps' centres `γ_j` and weights `b_j`. -/
def bumpData : List (ℚ × ℚ) :=
  [(3 / 2, 193 / 1000000), (2, 23 / 500000), (3, 1021 / 1000000), (7 / 2, 593 / 1000000), (4, 71 / 125000),
    (9 / 2, 617 / 1000000), (7, 1433 / 1000000), (15 / 2, 39 / 500000), (17 / 2, 3 / 250000)]

/-- The correction `r(s) = Σ_j b_j·bump(γ_j, s)`. -/
def rr (s : ℝ) : ℝ := (bumpData.map fun p => (p.2 : ℝ) * bump p.1 s).sum

/-- **The minorant** `μ = φλ − r`. -/
def mu (s : ℝ) : ℝ := PivotPhi.phi s * lam s - rr s

end PivotMinor
