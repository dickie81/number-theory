import Mathlib
import WeilConverse

/-! # The bilinear Weil form is the bilinear zero sum

Weil's explicit formula (`WeilExplicit`) equates the zero sum `Σ_ρ h(t_ρ)` with its prime side
`weilRHS h hR` (pole terms, archimedean integral, prime sum). `bil_zero_sum` is the polarised bridge for
probes: given the explicit formula for `h = ĝ²` at `g + k` and at `g − k`,
`Σ_ρ ĝ(t_ρ)k̂(t_ρ) = (Q(g + k) − Q(g − k))/4`.
-/

open Real Complex

noncomputable section

namespace WeilForm

open WeilTest

/-! ## The polarised bridge -/

variable {a : ℝ} {g k : ℝ → ℝ}

theorem ghatC_sub' (hg : MeasureTheory.MemLp g 2 MeasureTheory.volume) (hk : MeasureTheory.MemLp k 2 MeasureTheory.volume)
    (z : ℂ) : ghatC (fun t => g t - k t) a z = ghatC g a z - ghatC k a z := by
  unfold ghatC
  rw [← intervalIntegral.integral_sub (ii_mul_exp hg z _ _) (ii_mul_exp hk z _ _)]
  congr 1; funext u; push_cast; ring

/-- **The bilinear Weil form is the bilinear zero sum**: `Σ_ρ ĝ(t_ρ)k̂(t_ρ) = (Q(g + k) − Q(g − k))/4`. -/
theorem bil_zero_sum {ι : Type*} {ρ : ι → ℂ} (hg : Probe a g) (hk : Probe a k) (ha : 0 < a)
    (hEp : WeilExplicit ρ (fun z => ghatC (fun t => g t + k t) a z ^ 2) (hsq (fun t => g t + k t) a))
    (hEm : WeilExplicit ρ (fun z => ghatC (fun t => g t - k t) a z ^ 2) (hsq (fun t => g t - k t) a)) :
    HasSum (fun i => ghatC g a ((ρ i - 1 / 2) / I) * ghatC k a ((ρ i - 1 / 2) / I))
      (((weilQ a (fun t => g t + k t) - weilQ a (fun t => g t - k t)) / 4 : ℝ) : ℂ) := by
  obtain ⟨hpp, hpm⟩ := probe_add_sub hg hk
  have hp := weilQ_eq_zero_sum hpp ha hEp
  have hm := weilQ_eq_zero_sum hpm ha hEm
  have h := (hp.sub hm).div_const 4
  convert h using 1
  · funext i
    rw [show (fun t => g t + k t) = g + k from rfl, ghatC_add hg.memL2 hk.memL2,
      ghatC_sub' hg.memL2 hk.memL2]
    ring
  · push_cast; ring

end WeilForm

#print axioms WeilForm.bil_zero_sum
