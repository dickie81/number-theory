/-
# Joins from the exponent `Θ` and the half-plane into older sockets

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For `σ ≥ 0`, `ζ`'s twin form is at least `−C e^{σλ}` at `λ ≥ 0` if and only if `2Θ − 1 ≤ σ`
(`weil_twins_rate_Theta`); if RH fails, `ψ(x) − x = Ω±(√x)` (`psiOmegaSqrt_of_not_RH`); and the Korobov–Vinogradov
region of `LandauKV.zeroFree_KV` holds with the constant `A = 1/6` (`zeroFree_KV_explicit`). No
hypothesis.

* `weil_twins_rate_Theta`: `WeilForm.weil_twins_rate` (the rate condition iff `|2 Re ρ − 1| ≤ σ` at
  every nontrivial zero) with `PsiExponent.Theta`: zeros with `Re ρ > Θ − ε` for every `ε > 0`
  (`exists_zero_re_gt`) and none with `Re ρ > Θ` (`zeta_ne_zero_of_Theta_lt`, through `PsiOmega.band_of_zeroFree`).
  `weil_twins_rate`'s docstring says this in prose.
* `psiOmegaSqrt_of_not_RH`: `CrossCriteria.PsiOmegaSqrt` when RH fails. Then `Θ > 1/2`
  (`MertensExponent.rh_iff_Theta_eq_half`), and `psi_omega_Theta` at `ε = (Θ − 1/2)/2`
  gives `ψ(x) − x` beyond `±x^{Θ−ε} ≥ ±√x` for arbitrarily large `x`.
* `zeroFree_KV_explicit`: for `|t| ≥ e³` the denominator `(log|t|)^{2/3}(log log|t|)^{1/3}` exceeds
  `3^{2/3} > 2`, so the region lies in `Re s > 11/12`, where the half-plane
  (`Eis.ne_zero_of_re_gt_eleven_twelfths`) applies.
-/
import MertensExponent
import CrossCriteria
import WeilLandau

open Complex Filter
open scoped Chebyshev

namespace HalfPlaneJoinsPNT

open WeilForm WeilTest WeilStrip PsiOmega PsiExponent

/-- **The exponential rate of the negative part of `ζ`'s twin form is exactly `2Θ − 1`.** -/
theorem weil_twins_rate_Theta {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ weilQ (l + 1) (twin (box 1) l)) ↔
      2 * Theta - 1 ≤ σ := by
  rw [weil_twins_rate hσ]
  constructor
  · intro h
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨ρ, hρ, hre⟩ := exists_zero_re_gt (ε := ε / 2) (by positivity)
    have := (abs_le.1 (h ρ hρ)).2
    linarith
  · intro h s hs
    exact (band_of_zeroFree (fun _ hρ => zeta_ne_zero_of_Theta_lt hρ) hs).trans h

/-- **If RH fails, `ψ(x) − x = Ω±(√x)`.** -/
theorem psiOmegaSqrt_of_not_RH (h : ¬ RiemannHypothesis) : CrossCriteria.PsiOmegaSqrt := by
  have hΘ : 1 / 2 < Theta := by
    rcases half_le_Theta.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (MertensExponent.rh_iff_Theta_eq_half.2 h'.symm) h
  set ε := (Theta - 1 / 2) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hεΘ : ε < Theta := by rw [hεdef]; linarith
  have hexp : (1 / 2 : ℝ) ≤ Theta - ε := by rw [hεdef]; linarith
  refine ⟨1, one_pos, fun X => ?_⟩
  obtain ⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩⟩ := psi_omega_Theta hε hεΘ 1 (max X 1)
  have hx1' : 1 ≤ x1 := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx1)
  have hx2' : 1 ≤ x2 := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx2)
  have e1 := Real.rpow_le_rpow_of_exponent_le hx1' hexp
  have e2 := Real.rpow_le_rpow_of_exponent_le hx2' hexp
  refine ⟨⟨x1, lt_of_le_of_lt (le_max_left _ _) hx1, ?_⟩, ⟨x2, lt_of_le_of_lt (le_max_left _ _) hx2, ?_⟩⟩
  · linarith
  · linarith

end HalfPlaneJoinsPNT
