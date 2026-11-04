import Mathlib
import WeilChi

/-!
# The zero sum `K₁ = Σ_ρ 1/(ρ(1 − ρ))` at `s = 1` for a good real character

For `χ` with `GoodChar χ` (an explicit hypothesis: primitive, real, `χ ≠ 1`, `L(½, χ) ≠ 0`), Hadamard's product for
`Ξ_χ` at `t = −i/2` (that is `s = 1`) gives
`Σ_u 2/(¼ + u) = log N − log π + ψ((1 + δ)/2) + 2 L′/L(1, χ)`, summed over the zeros `u = τ²` of `Ξ_χ(√w)`
(`PsiOmega.hasSum_K1`). Unconditional given `GoodChar χ`. This is the identity behind `hK1` of
`D2Density.d2_density_log`, with `K₁ = Σ_ρ 1/(ρ(1 − ρ)) = Σ_u 2/(¼ + u)`. See `formalisations/d2-density.md`.
-/

open Real Complex Filter Topology Set

noncomputable section

namespace PsiOmega

open DirichletCharacter WeilForm

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- `Λ*′/Λ* = ½ log N + Γ_ℝ′/Γ_ℝ(s + δ) + L′/L(s)` wherever `Re s > 0` and `L(s) ≠ 0`. -/
theorem logDeriv_LamG_of_ne (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) (hL : LFunction χ s ≠ 0) :
    logDeriv (LamG χ) s = (Real.log N : ℂ) / 2 + logDeriv Gammaℝ (s + parity χ)
      + logDeriv (LFunction χ) s := by
  set δ : ℂ := (parity χ : ℂ)
  set U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  set Pf : ℂ → ℂ := fun z => (N : ℂ) ^ (z / 2) * (Gammaℝ (z + δ) * LFunction χ z)
  have hEq : ∀ z ∈ U, LamG χ z = Pf z := by
    intro z hz
    simp only [Pf, LamG]
    rw [completed_eq_mul hz, gammaFactor_parity]
  have hev : LamG χ =ᶠ[𝓝 s] Pf := Filter.eventuallyEq_of_mem (hU.mem_nhds hs) hEq
  have hlog : logDeriv (LamG χ) s = logDeriv Pf s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hEq s hs]
  rw [hlog]
  have hN : (N : ℂ) ≠ 0 := natCast_ne_zero'
  have hsδ : 0 < (s + δ).re := by simp only [add_re, δ, natCast_re]; linarith [parity_nonneg' χ]
  have hGs : Gammaℝ (s + δ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos hsδ
  have hdG : DifferentiableAt ℂ (fun z => Gammaℝ (z + δ)) s :=
    (differentiableAt_Gammaℝ_of_re_pos hsδ).comp s (differentiableAt_id.add_const δ)
  have hdL : DifferentiableAt ℂ (LFunction χ) s := differentiable_LFunction hχ1 s
  have hc : HasDerivAt (fun z : ℂ => (N : ℂ) ^ (z / 2)) ((N : ℂ) ^ (s / 2) * Complex.log N * (1 / 2)) s := by
    simpa using ((hasDerivAt_id s).div_const 2).const_cpow (c := (N : ℂ)) (Or.inl hN)
  have hc0 : (N : ℂ) ^ (s / 2) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  have e1 : deriv (fun z : ℂ => z + δ) s = 1 := ((hasDerivAt_id s).add_const δ).deriv
  have hcomp : logDeriv (fun z => Gammaℝ (z + δ)) s = logDeriv Gammaℝ (s + δ) := by
    have hg : DifferentiableAt ℂ (fun z : ℂ => z + δ) s := differentiableAt_id.add_const δ
    have := logDeriv_comp (f := Gammaℝ) (g := fun z : ℂ => z + δ)
      (differentiableAt_Gammaℝ_of_re_pos hsδ) hg
    rw [e1, mul_one] at this
    exact this
  simp only [Pf]
  rw [logDeriv_fun_mul (f := fun z : ℂ => (N : ℂ) ^ (z / 2))
      (g := fun z => Gammaℝ (z + δ) * LFunction χ z) s hc0 (mul_ne_zero hGs hL) hc.differentiableAt
      (hdG.mul hdL),
    logDeriv_fun_mul (f := fun z => Gammaℝ (z + δ)) (g := LFunction χ) s hGs hL hdG hdL,
    hcomp, logDeriv_apply (f := fun z : ℂ => (N : ℂ) ^ (z / 2)), hc.deriv, ← Complex.natCast_log]
  field_simp
  ring

variable (hG : GoodChar χ)
include hG

/-- **The zero sum at `s = 1`.** `Σ_u 2/(¼ + u) = log N − log π + ψ((1 + δ)/2) + 2 L′/L(1, χ)`. -/
theorem hasSum_K1 :
    HasSum (fun i : ZeroIdx (sqF (XiC χ)) => 2 / (1 / 4 + i.1))
      ((Real.log N : ℂ) - (Real.log π : ℂ) + Complex.digamma ((1 + parity χ) / 2)
        + 2 * logDeriv (LFunction χ) 1) := by
  set t : ℂ := -I / 2
  have hs : (1 / 2 + I * t : ℂ) = 1 := by simp only [t]; ring_nf; rw [I_sq]; ring
  have hL1 : LFunction χ 1 ≠ 0 := LFunction_apply_one_ne_zero hG.ne_one
  have hX : XiC χ t ≠ 0 := by
    show LamG χ (1 / 2 + I * t) ≠ 0
    rw [hs]; exact LamG_ne_zero (by simp) hL1
  have h := hasSum_logDeriv_XiC hG hX
  have hg : HasDerivAt (fun z : ℂ => 1 / 2 + I * z) I t := by
    simpa using ((hasDerivAt_id t).const_mul I).const_add (1 / 2)
  have hdx : DifferentiableAt ℂ (LamG χ) (1 / 2 + I * t) := differentiable_LamG hG.ne_one _
  have e : XiC χ = LamG χ ∘ fun z : ℂ => 1 / 2 + I * z := by funext z; rfl
  have h1 : (0 : ℝ) < (1 + (parity χ : ℂ)).re := by
    simp only [add_re, one_re, natCast_re]; linarith [parity_nonneg' χ]
  have hlog : logDeriv (XiC χ) t = I * ((Real.log N : ℂ) / 2 - (Real.log π : ℂ) / 2 +
      Complex.digamma ((1 + parity χ) / 2) / 2 + logDeriv (LFunction χ) 1) := by
    rw [e, logDeriv_comp (f := LamG χ) (g := fun z : ℂ => 1 / 2 + I * z) hdx hg.differentiableAt,
      hg.deriv, hs, logDeriv_LamG_of_ne hG.ne_one (by simp) hL1, logDeriv_Gammaℝ h1]
    ring
  rw [hlog] at h
  have h2 := h.mul_left (-2 * I)
  convert h2 using 1
  · funext i
    have ht2 : t ^ 2 = -1 / 4 := by simp only [t]; ring_nf; rw [I_sq]; ring
    have h2t : 2 * t = -I := by simp only [t]; ring
    have hterm : 2 * t / (t ^ 2 - i.1) = I / (1 / 4 + i.1) := by
      rw [ht2, h2t, show (-1 / 4 - i.1 : ℂ) = -(1 / 4 + i.1) by ring, div_neg, neg_div, neg_neg]
    rw [hterm, ← mul_div_assoc]; congr 1; ring_nf; rw [I_sq]; ring
  · ring_nf; rw [I_sq]; ring

end PsiOmega
