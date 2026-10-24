/-
# Chen–Gupta–Li's zero-density estimate on `[5/7, 16/21]`, as a hypothesis

`CGLDensity` states Chen–Gupta–Li's zero-density estimate as a hypothesis: for every `ε > 0` there is
`C` such that for every `q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, at most `C(qT)^{(7/3)(1−σ)+ε}` characters mod `q`
have an `L`-function with a zero in `Re s ≥ σ`, `|Im s| ≤ T`. The theorems that use it take it as an argument.
`LinnikCGLDensity.cglDensity` proves it, from `LinnikCGLHB101.prop31`.

Chen, Gupta and Li (arXiv:2507.08296v2) open their abstract with this sentence, here as arXiv's API returns the
abstract of 2507.08296v2, with the whitespace collapsed (the e-print's own abstract spells the same formulas
with `\chi`, `\sigma`, `\epsilon`, `\rho` and `\beta`): "It is proved
that \[ \sum_{χ\bmod q}N(σ,T,χ) \ll_ε (qT)^{7(1-σ)/3+ε}, \] where $N(σ,T,χ)$
denotes the number of zeros $ρ=β+it$ of $L(s,χ)$ in the rectangle $σ\leq β\leq 1$, $|t|\leq T$." A character counted
by `CGLDensity` has such a zero, except possibly the trivial character, for the value its `LFunction` takes at the
pole `s = 1`: `LFunction χ s ≠ 0` on `Re s ≥ 1` when `χ ≠ 1` or `s ≠ 1`
(`DirichletCharacter.LFunction_ne_zero_of_one_le_re`). So their bound as the abstract states it, with one constant
`C = C(ε)` for every `q` and `T`, gives `CGLDensity` with `C + 1`. (Their Theorem 1.2 states the bound
with `(qT)^{o(1)}`, as `qT → ∞`; below the threshold the count is at most `q < qT`, so `CGLDensity` follows from the
theorem too, with a constant depending on `ε`.)

The file imports only Mathlib.
-/
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace LinnikCGL

open DirichletCharacter

open scoped Classical in
/-- **Chen–Gupta–Li's zero-density estimate on `[5/7, 16/21]`.** For every `ε > 0` there is `C` such that for every
`q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, at most `C(qT)^{(7/3)(1−σ)+ε}` characters mod `q` have a zero of `L(·, χ)` in
`Re s ≥ σ`, `|Im s| ≤ T`. -/
def CGLDensity : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 7 ≤ σ → σ ≤ 16 / 21 → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤ C * ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + ε)

end LinnikCGL
