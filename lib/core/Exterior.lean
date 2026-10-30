import Mathlib
import BinetProof

open Real MeasureTheory
open Filter Topology

noncomputable section

namespace WeilForm

/-! ## 1ca(iv): the pole leftover `E_pole = 2ĝ(i/2)²χ(i/2)` -/

/-- The probe's transform `ĝ(z) = ∫_{−a}^{a} g(u) e^{izu} du` for a real probe `g` on `[−a, a]`. -/
def ghatC (g : ℝ → ℝ) (a : ℝ) (z : ℂ) : ℂ :=
  ∫ u in (-a)..a, ((g u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)

/-! ## 1ca(iv): the Stirling remainder, `|Re ψ(1/4 + ir/2) − ln(r/2)| ≤ 3/(2r²)` for `r ≥ 8` -/

/-- `z = 1/4 + ir/2`. -/
def zB (r : ℝ) : ℂ := 1 / 4 + Complex.I * r / 2

theorem zB_re (r : ℝ) : (zB r).re = 1 / 4 := by
  unfold zB; simp

theorem zB_im (r : ℝ) : (zB r).im = r / 2 := by
  unfold zB; simp

/-! ## 1ca(iv): the Stirling remainder `E_arch` and the exterior identity -/

/-- `Re ψ(1/4 + ir/2)`. -/
def psiRe (r : ℝ) : ℝ := (Complex.digamma (zB r)).re

/-- `g_h(u) = (1/2π)∫_ℝ h(r)cos(ru) dr` and the paper's `f_χ(u) = (1/π)∫_0^∞ h(r)cos(ru) dr`. -/
def gh (hR : ℝ → ℝ) (u : ℝ) : ℝ := 1 / (2 * π) * ∫ r, hR r * Real.cos (r * u)

/-- **Weil's explicit formula** (Guinand–Weil; the named classical input of 1ca(iv)) for a test
function `h` with real values `hR` on `ℝ`: `Σ_ρ h(t_ρ) = h(i/2) + h(−i/2) − g_h(0) ln π
+ (1/2π)∫_ℝ h(r) Re ψ(1/4 + ir/2) dr − 2Σ_n Λ(n) n^{−1/2} g_h(ln n)`, `t_ρ = (ρ − 1/2)/i`, the
zeros counted with multiplicity by the family `ρ`. -/
def WeilExplicit {ι : Type*} (ρ : ι → ℂ) (h : ℂ → ℂ) (hR : ℝ → ℝ) : Prop :=
  (∀ r : ℝ, h r = hR r) ∧ HasSum (fun i => h ((ρ i - 1 / 2) / Complex.I))
    (h (Complex.I / 2) + h (-(Complex.I / 2))
      + ((-(gh hR 0 * Real.log π) + 1 / (2 * π) * (∫ r, hR r * psiRe r)
        - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh hR (Real.log n) : ℝ) : ℂ))

/-- An even probe has an even transform: `ĝ(−z) = ĝ(z)`. -/
theorem ghatC_even {g : ℝ → ℝ} (hg : ∀ u, g (-u) = g u) (a : ℝ) (z : ℂ) :
    ghatC g a (-z) = ghatC g a z := by
  unfold ghatC
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a)
    (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))
  simp only [neg_neg] at h
  rw [← h]
  congr 1
  funext u
  simp only [hg, Complex.ofReal_neg]
  congr 2
  ring

end WeilForm
