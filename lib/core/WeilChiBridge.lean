import Mathlib
import WeilChiCriterion
import ArchShift

/-! # `Q_χ` in u-space

`QC χ a g` (WeilChiCriterion.lean) is Weil's form for `L(s, χ)` in its Guinand–Weil presentation, with
`h = ĝ²` on the spectral side. For every probe it equals the u-space form:

  `Q_χ(g) = (Re ψ(q_χ) + log(N/π))‖g‖² + ∫_0^∞ [f(0) − f(u)] e^{(1−2q_χ)u}/sinh u du
            − 2Σ Λ(n)χ(n)n^{−1/2} f(log n)`   (`QC_eq_QCu`),

with `f = autocorr g` and `q_χ = (1 + 2δ)/4`: `¼` for even `χ` (ζ's kernel `e^{u/2}/sinh u`), `¾` for
odd `χ` (kernel `e^{−u/2}/sinh u`). The three instances `χ₋₃`, `χ₋₄`, `χ₋₈` are odd.

The proof is `gh_hsq` (Fourier inversion, `g_h = f`) for the constant and prime terms and
ArchShift.lean's `arch_termQ` for the archimedean term. No zero of `L` and no GoodChar hypothesis enter.
-/

open Real Complex MeasureTheory Set

noncomputable section

namespace PsiOmega

open DirichletCharacter WeilForm WeilTest

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {a : ℝ} {g : ℝ → ℝ}

/-- The digamma shift `q_χ = (1 + 2δ)/4`. -/
def qC (χ : DirichletCharacter ℂ N) : ℝ := (1 + 2 * parity χ) / 4

theorem quarter_le_qC : 1 / 4 ≤ qC χ := by
  unfold qC; linarith [parity_nonneg' χ]

/-- `z_χ(r) = q_χ + ir/2`. -/
theorem psiReC_eq : psiReC χ = psiReQ (qC χ) := by
  funext r; unfold psiReC psiReQ zC zQ qC; congr 2; push_cast; ring

/-- **Weil's form for `L(s, χ)` in u-space**. -/
def QCu [NeZero N] (χ : DirichletCharacter ℂ N) (g : ℝ → ℝ) : ℝ :=
  ((Complex.digamma (qC χ)).re + Real.log N - Real.log π) * normSq g + archEQ (qC χ) g
    - 2 * ∑' n : ℕ, fχ χ n / Real.sqrt n * autocorr g (Real.log n)

/-- **The u-space bridge for `χ`**: for every probe, `Q_χ(g) = Q_χ^u(g)`. -/
theorem QC_eq_QCu [NeZero N] (hp : Probe a g) (ha : 0 < a) : QC χ a g = QCu χ g := by
  unfold QC QCu weilRHSC
  rw [psiReC_eq, arch_termQ hp ha quarter_le_qC, psiReQ_zero]
  simp only [gh_hsq hp.toE ha, autocorr_zero]
  ring

end PsiOmega

#print axioms PsiOmega.QC_eq_QCu
