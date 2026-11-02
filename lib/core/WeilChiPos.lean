import Mathlib
import WeilChiK1
import D2Density

/-!
# `Ξ_χ` has a zero, and `K₁ > 0`, for a good real character

For `χ` with `GoodChar χ` (an explicit hypothesis):
* `PsiOmega.nonempty_zeros`: `Ξ_χ` has a zero. Otherwise Hadamard's product (`PsiOmega.hadamard_XiC`) makes `Ξ_χ`
  constant, so `Λ*(σ + 2) = Λ*(σ)`. With `Γ_ℝ(s + 2) = Γ_ℝ(s)·s/(2π)` this gives
  `N(σ + δ)/(2π)·L(σ + 2) = L(σ)` for real `σ > 1`, impossible as `σ → ∞` since `L(σ) → 1`.
* `PsiOmega.K1C_pos`: `K₁ = Re Σ_u 2/(¼ + u) > 0`. Each term is `2/(ρ(1 − ρ))` with `0 < Re ρ < 1`
  (`D2Density.re_inv_pos`), and there is at least one.

Unconditional given `GoodChar χ`. See `formalisations/d2-density.md`.
-/

open Real Complex Filter Topology Set

noncomputable section

namespace PsiOmega

open DirichletCharacter WeilForm

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- `Λ*(z) = N^{z/2} Γ_ℝ(z + δ) L(z)` on `Re z > 0`. -/
theorem LamG_eq_mul {z : ℂ} (hz : 0 < z.re) :
    LamG χ z = (N : ℂ) ^ (z / 2) * (Gammaℝ (z + parity χ) * LFunction χ z) := by
  simp only [LamG]; rw [completed_eq_mul hz, gammaFactor_parity]

theorem tendsto_LFunction_atTop :
    Tendsto (fun σ : ℝ => LFunction χ σ) atTop (𝓝 1) := by
  have hb : (fun n : ℕ => χ n) =O[atTop] fun _ => (1 : ℝ) :=
    Asymptotics.isBigO_of_le _ fun n => by rw [norm_one]; exact DirichletCharacter.norm_le_one χ n
  have h := LSeries.tendsto_atTop (f := fun n : ℕ => χ n)
    ((LSeries.abscissaOfAbsConv_le_one_of_isBigO_one hb).trans_lt (EReal.coe_lt_top 1))
  simp only [Nat.cast_one, map_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
  exact (LFunction_eq_LSeries χ (by simpa using hσ)).symm

variable (hG : GoodChar χ)
include hG

/-- **`Ξ_χ` has a zero.** -/
theorem nonempty_zeros : Nonempty (ZeroIdx (sqF (XiC χ))) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hc : ∀ z, XiC χ z = XiC χ 0 := by
    intro z
    have h := ((hadamard_XiC hG).prod z).unique hasProd_empty
    have h0 := XiC_zero_ne hG
    field_simp at h; exact h
  -- `Λ*` is constant
  have hL : ∀ s, LamG χ s = XiC χ 0 := by
    intro s
    have : s = 1 / 2 + I * ((s - 1 / 2) / I) := by field_simp; ring
    rw [this]; exact hc _
  set δ : ℂ := (parity χ : ℂ)
  have hN : (N : ℂ) ≠ 0 := natCast_ne_zero'
  have key : ∀ σ : ℝ, 1 < σ →
      (N : ℂ) * ((σ + δ) / σ) / 2 / π * LFunction χ (σ + 2 : ℝ) = LFunction χ σ / σ := by
    intro σ hσ
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : σ ≠ 0)
    have h1 : 0 < ((σ : ℂ)).re := by simp; linarith
    have h2 : 0 < (((σ + 2 : ℝ) : ℂ)).re := by simp; linarith
    have hsδ : 0 < ((σ : ℂ) + δ).re := by simp only [add_re, ofReal_re, δ, natCast_re]; linarith [parity_nonneg' χ]
    have hsδ0 : (σ : ℂ) + δ ≠ 0 := fun h => by rw [h, zero_re] at hsδ; exact lt_irrefl _ hsδ
    have hGs : Gammaℝ ((σ : ℂ) + δ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos hsδ
    have hc0 : (N : ℂ) ^ ((σ : ℂ) / 2) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
    have e := (hL (σ + 2 : ℝ)).trans (hL σ).symm
    rw [LamG_eq_mul h2, LamG_eq_mul h1] at e
    have eG : Gammaℝ (((σ + 2 : ℝ) : ℂ) + δ) = Gammaℝ ((σ : ℂ) + δ) * ((σ : ℂ) + δ) / 2 / π := by
      rw [show (((σ + 2 : ℝ) : ℂ) + δ) = ((σ : ℂ) + δ) + 2 by push_cast; ring, Gammaℝ_add_two hsδ0]
    have eN : (N : ℂ) ^ (((σ + 2 : ℝ) : ℂ) / 2) = (N : ℂ) ^ ((σ : ℂ) / 2) * N := by
      rw [show (((σ + 2 : ℝ) : ℂ) / 2) = (σ : ℂ) / 2 + 1 by push_cast; ring, cpow_add _ _ hN, cpow_one]
    rw [eG, eN] at e
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have e3 : (N : ℂ) * ((σ : ℂ) + δ) / 2 / π * LFunction χ (σ + 2 : ℝ) = LFunction χ σ :=
      mul_left_cancel₀ (mul_ne_zero hc0 hGs) (by linear_combination e)
    rw [← e3]; field_simp
  -- limits
  have hσ : Tendsto (fun σ : ℝ => ((σ : ℂ) + δ) / σ) atTop (𝓝 1) := by
    have : Tendsto (fun σ : ℝ => 1 + δ * ((σ : ℂ))⁻¹) atTop (𝓝 (1 + δ * 0)) := by
      refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
      exact ((Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).congr (fun σ => by simp) |>.trans (by simp)
    rw [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ0
    have : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
    field_simp
  have hL2 : Tendsto (fun σ : ℝ => LFunction χ (σ + 2 : ℝ)) atTop (𝓝 1) :=
    tendsto_LFunction_atTop.comp (tendsto_atTop_add_const_right _ 2 tendsto_id)
  have hlhs := (((tendsto_const_nhds (x := (N : ℂ))).mul hσ).div_const 2).div_const (π : ℂ) |>.mul hL2
  have hrhs : Tendsto (fun σ : ℝ => LFunction χ σ / σ) atTop (𝓝 0) := by
    have h0 : Tendsto (fun σ : ℝ => ((σ : ℂ))⁻¹) atTop (𝓝 0) :=
      ((Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).congr (fun σ => by simp) |>.trans (by simp)
    simpa [div_eq_mul_inv] using tendsto_LFunction_atTop.mul h0
  have := tendsto_nhds_unique (hlhs.congr' (eventually_gt_atTop 1 |>.mono fun σ hσ => key σ hσ)) hrhs
  simp only [mul_one] at this
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  exact hN (by simpa using this)

/-- `K₁ = Re Σ_u 2/(¼ + u)`, the zero sum `Σ_ρ 1/(ρ(1 − ρ))`. -/
def K1C (χ : DirichletCharacter ℂ N) : ℝ := (∑' i : ZeroIdx (sqF (XiC χ)), 2 / (1 / 4 + i.1)).re

theorem re_term_pos (i : ZeroIdx (sqF (XiC χ))) : 0 < (2 / (1 / 4 + i.1)).re := by
  set τ := tauC (χ := χ) i
  have hτ := tauC_im hG i
  set ρ : ℂ := 1 / 2 + I * τ
  have hρ : ρ * (1 - ρ) = 1 / 4 + i.1 := by
    rw [← tauC_sq i]; simp only [ρ]; ring_nf; rw [I_sq]; ring
  have hre : ρ.re = 1 / 2 - τ.im := by simp [ρ]; ring
  have h := D2Density.re_inv_pos ρ (by rw [hre]; linarith [(abs_lt.1 hτ).2])
    (by rw [hre]; linarith [(abs_lt.1 hτ).1])
  rw [← hρ, show (2 : ℂ) / (ρ * (1 - ρ)) = ((2 : ℝ) : ℂ) * (1 / (ρ * (1 - ρ))) by push_cast; ring, Complex.re_ofReal_mul]
  linarith

/-- **`K₁ > 0`.** -/
theorem K1C_pos : 0 < K1C χ := by
  have hs := (hasSum_K1 hG).summable
  rw [K1C, Complex.re_tsum hs]
  obtain ⟨i⟩ := nonempty_zeros hG
  exact (Complex.reCLM.summable hs).tsum_pos (fun j => (re_term_pos hG j).le) i (re_term_pos hG i)

end PsiOmega
