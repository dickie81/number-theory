import Mathlib
import WeilConverse

/-! # Riemann's kernel is a null vector of the explicit formula

Weil's explicit formula (`WeilExplicit`) equates the zero sum `Σ_ρ h(t_ρ)` with its prime side
`weilRHS h hR` (pole terms, archimedean integral, prime sum). At every nontrivial zero of `ζ`,
`Ξ(t_ρ) = ξ(ρ) = 0` (`Xi_zeta_zero`). So every test transform divisible by `Ξ` is annihilated:

* `explicit_null_of_Xi`: `h = Ξ·m` ⟹ `weilRHS h hR = 0`;
* `explicit_null_RPhi`: Riemann's formula `Φ̂ = Ξ/2` (`RPhiHat_eq`, RiemannKernel.lean) makes
  `Φ̂·m` null for every `m`: **`Φ` is a null vector of the bilinear Weil functional**;
* `weil_energy_RPhi`: for `h = Φ̂²` the pole terms are `Ξ(±i/2)²/4 = ξ(0)²/4 = ξ(1)²/4 = 1/16`, so the
  archimedean-plus-prime side of `Φ̂²` equals exactly `−1/8`: Weil's energy of `Φ` is `0`.

`bil_zero_sum` is the polarised bridge for probes: `Σ_ρ ĝ(t_ρ)k̂(t_ρ) = (Q(g + k) − Q(g − k))/4`.

**Not formalised**: identifying the explicit formula's `g_h` for `h = Φ̂k̂` with the library's
cross-correlation `∫Φ(t)k(t + u) dt` (Fourier inversion and a signed Fubini for a non-compactly
supported `Φ`), which would state the nullity as `B(Φ, k) = 0` in the library's own prime-side form.
Scope: a restatement of the explicit formula at a function vanishing on the zeros; no bearing on RH.
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
