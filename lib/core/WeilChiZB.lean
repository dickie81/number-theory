import Mathlib
import WeilChiZ
import WeilChiPos
import WeilChiB

/-!
# `K₁` and Theorem B with a central zero

For a primitive real `χ ≠ 1` (`PsiOmega.RealChar`, no hypothesis on `L(½, χ)`), let `m = PsiOmega.mC χ` be the order
of `Ξ_χ` at `0` and `Y = Ξ_χ/t^m` (`PsiOmega.YC`). Counting the zero `ρ = ½` with multiplicity `m`, the zero sums are
`K₁ = Σ_u 2/(¼ + u) + 4m` (`PsiOmega.K1Z`) and `K(x) = Σ_u 2cos(τ_u log x)/(¼ + u) + 4m` (`PsiOmega.KxZ`), summed over
the zeros `u = τ²` of `Y(√w)`. Then `K₁ = log N − log π + Re ψ((1 + δ)/2) + 2 Re L′/L(1, χ)` (`PsiOmega.K1Z_eq`),
`K₁ > 0` (`PsiOmega.K1Z_pos`) and Theorem B `K(2) = √2(K₁/2 + c_χ + ℓ/2)` (`PsiOmega.theoremBZ`) hold with no
hypothesis on `L(½, χ)`. Unconditional. See `formalisations/d2-density.md`.
-/

open Real Complex Filter Topology Set WeilForm WeilTest WeilStrip

noncomputable section

namespace PsiOmega

open DirichletCharacter BallPsi

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- `K₁ = Re Σ_u 2/(¼ + u) + 4m`, the zero sum `Σ_ρ 1/(ρ(1 − ρ))` with the central zero counted. -/
def K1Z (χ : DirichletCharacter ℂ N) : ℝ := (∑' i : ZeroIdx (sqF (YC χ)), 2 / (1 / 4 + i.1)).re + 4 * mC χ

/-- `K(x) = Σ_u 2cos(τ_u log x)/(¼ + u) + 4m`, that is `Σ_ρ x^{ρ−½}/(ρ(1 − ρ))`. -/
def KxZ (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  (∑' i : ZeroIdx (sqF (YC χ)), 2 * Complex.cos (tauY i * Real.log x) / (1 / 4 + i.1)) + 4 * mC χ

variable (hR : RealChar χ)
include hR

/-- **The zero sum at `s = 1`, central zero removed.** -/
theorem hasSum_K1Z :
    HasSum (fun i : ZeroIdx (sqF (YC χ)) => 2 / (1 / 4 + i.1))
      ((Real.log N : ℂ) - (Real.log π : ℂ) + Complex.digamma ((1 + parity χ) / 2)
        + 2 * logDeriv (LFunction χ) 1 - 4 * mC χ) := by
  set t : ℂ := -I / 2
  have hs : (1 / 2 + I * t : ℂ) = 1 := by simp only [t]; ring_nf; rw [I_sq]; ring
  have hL1 : LFunction χ 1 ≠ 0 := LFunction_apply_one_ne_zero hR.ne_one
  have hX : XiC χ t ≠ 0 := by
    show LamG χ (1 / 2 + I * t) ≠ 0
    rw [hs]; exact LamG_ne_zero (by simp) hL1
  have ht0 : t ≠ 0 := by simp [t]
  have hYt : YC χ t ≠ 0 := fun h => hX (by rw [XiC_eq_pow_mul hR, h, mul_zero])
  have h := hasSum_logDeriv_YC hR hYt
  have hg : HasDerivAt (fun z : ℂ => 1 / 2 + I * z) I t := by
    simpa using ((hasDerivAt_id t).const_mul I).const_add (1 / 2)
  have hdx : DifferentiableAt ℂ (LamG χ) (1 / 2 + I * t) := differentiable_LamG hR.ne_one _
  have e : XiC χ = LamG χ ∘ fun z : ℂ => 1 / 2 + I * z := by funext z; rfl
  have h1 : (0 : ℝ) < (1 + (parity χ : ℂ)).re := by
    simp only [add_re, one_re, natCast_re]; linarith [parity_nonneg' χ]
  have hlog : logDeriv (XiC χ) t = I * ((Real.log N : ℂ) / 2 - (Real.log π : ℂ) / 2 +
      Complex.digamma ((1 + parity χ) / 2) / 2 + logDeriv (LFunction χ) 1) := by
    rw [e, logDeriv_comp (f := LamG χ) (g := fun z : ℂ => 1 / 2 + I * z) hdx hg.differentiableAt,
      hg.deriv, hs, logDeriv_LamG_of_ne hR.ne_one (by simp) hL1, logDeriv_Gammaℝ h1]
    ring
  have hY : logDeriv (YC χ) t = logDeriv (XiC χ) t - (mC χ : ℂ) / t := by
    rw [logDeriv_XiC_split hR ht0 hYt]; ring
  rw [hY, hlog] at h
  have h2 := h.mul_left (-2 * I)
  convert h2 using 1
  · funext i
    have ht2 : t ^ 2 = -1 / 4 := by simp only [t]; ring_nf; rw [I_sq]; ring
    have h2t : 2 * t = -I := by simp only [t]; ring
    have hterm : 2 * t / (t ^ 2 - i.1) = I / (1 / 4 + i.1) := by
      rw [ht2, h2t, show (-1 / 4 - i.1 : ℂ) = -(1 / 4 + i.1) by ring, div_neg, neg_div, neg_neg]
    rw [hterm, ← mul_div_assoc]; congr 1; ring_nf; rw [I_sq]; ring
  · simp only [t]
    field_simp
    ring_nf; rw [I_sq]; ring

/-- **`K₁` in closed form**, any primitive real `χ ≠ 1`. -/
theorem K1Z_eq : K1Z χ = Real.log N - Real.log Real.pi + (Complex.digamma ((1 + parity χ) / 2)).re
    + 2 * (deriv (LFunction χ) 1 / LFunction χ 1).re := by
  rw [K1Z, (hasSum_K1Z hR).tsum_eq, logDeriv_apply]
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.log_re]

theorem re_term_posY (i : ZeroIdx (sqF (YC χ))) : 0 < (2 / (1 / 4 + i.1)).re := by
  set τ := tauY (χ := χ) i
  have hτ := tauY_im hR i
  set ρ : ℂ := 1 / 2 + I * τ
  have hρ : ρ * (1 - ρ) = 1 / 4 + i.1 := by
    rw [← tauY_sq i]; simp only [ρ]; ring_nf; rw [I_sq]; ring
  have hre : ρ.re = 1 / 2 - τ.im := by simp [ρ]; ring
  have h := D2Density.re_inv_pos ρ (by rw [hre]; linarith [(abs_lt.1 hτ).2])
    (by rw [hre]; linarith [(abs_lt.1 hτ).1])
  rw [← hρ, show (2 : ℂ) / (ρ * (1 - ρ)) = ((2 : ℝ) : ℂ) * (1 / (ρ * (1 - ρ))) by push_cast; ring,
    Complex.re_ofReal_mul]
  linarith

/-- **`K₁ > 0`**, any primitive real `χ ≠ 1`. -/
theorem K1Z_pos : 0 < K1Z χ := by
  have hs := (hasSum_K1Z hR).summable
  have hsr := Complex.reCLM.summable hs
  rw [K1Z, Complex.re_tsum hs]
  rcases Nat.eq_zero_or_pos (mC χ) with hm | hm
  · rw [hm]
    rcases isEmpty_or_nonempty (ZeroIdx (sqF (YC χ))) with he | ⟨⟨i⟩⟩
    · exfalso
      refine XiC_not_const (χ := χ) fun z => ?_
      have hc : ∀ z, YC χ z = YC χ 0 := by
        intro z
        have h := ((hadamard_YC hR).prod z).unique hasProd_empty
        have h0 := YC_zero_ne hR
        field_simp at h; exact h
      rw [XiC_eq_pow_mul hR, XiC_eq_pow_mul hR, hm, pow_zero, pow_zero, hc z]
    · have := hsr.tsum_pos (fun j => (re_term_posY hR j).le) i (re_term_posY hR i)
      simp only [Complex.reCLM_apply] at this
      push_cast; linarith
  · have : 0 ≤ ∑' j : ZeroIdx (sqF (YC χ)), (2 / (1 / 4 + j.1)).re :=
      tsum_nonneg (fun j => (re_term_posY hR j).le)
    have h4 : (0 : ℝ) < 4 * mC χ := by positivity
    linarith

theorem tauY_ne_half (i : ZeroIdx (sqF (YC χ))) : tauY i ≠ I / 2 := fun h => by
  have := tauY_im hR i; rw [h] at this; norm_num at this

theorem tauY_ne_neg_half (i : ZeroIdx (sqF (YC χ))) : tauY i ≠ -(I / 2) := fun h => by
  have := tauY_im hR i; rw [h] at this; norm_num at this

/-- The zero side over the zeros of `Y`. -/
theorem hasSum_KxY (u : ℝ) :
    HasSum (fun i : ZeroIdx (sqF (YC χ)) => 2 * Complex.cos (tauY i * u) / (1 / 4 + i.1))
      (((Real.cosh (u / 2) : ℝ) : ℂ) * ((Real.log N : ℂ) - (Real.log π : ℂ) +
        Complex.digamma ((1 + parity χ) / 2) + 2 * logDeriv (LFunction χ) 1 - 4 * mC χ)
        + ((weilRHSC χ (HuR u) - mC χ * HuR u 0 : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := stripTest_Hu u
  have hW := weil_XiZ hR hC (Hu_even u) (Hu_real u)
  have hK := (hasSum_K1Z hR).mul_left ((Real.cosh (u / 2) : ℝ) : ℂ)
  refine (hK.add hW).congr_fun fun i => ?_
  rw [Hu_eq u (tauY_ne_half hR i) (tauY_ne_neg_half hR i), tauY_sq, add_comm (i.1 : ℂ) (1 / 4)]
  have hne : (1 / 4 + i.1 : ℂ) ≠ 0 := by
    intro h
    have h2 : tauY i ^ 2 = -(1 / 4) := by rw [tauY_sq]; linear_combination h
    have : (tauY i - I / 2) * (tauY i + I / 2) = 0 := by
      linear_combination h2 - Complex.I_sq / 4
    rcases mul_eq_zero.1 this with h | h
    · exact tauY_ne_half hR i (sub_eq_zero.1 h)
    · exact tauY_ne_neg_half hR i (by linear_combination h)
  field_simp
  ring

/-- **The explicit formula for `K(x)`**, any primitive real `χ ≠ 1`, `u = log x`. -/
theorem KxZ_explicit {x : ℝ} (hx : 1 ≤ x) :
    KxZ χ x = (((Real.cosh (Real.log x / 2) : ℝ) : ℂ) * ((Real.log N : ℂ) - (Real.log π : ℂ) +
        Complex.digamma ((1 + parity χ) / 2) + 2 * logDeriv (LFunction χ) 1) +
      ((-Real.sinh (Real.log x / 2) * (Real.log N - Real.log π) + archC χ (Real.log x)
        - 2 * ∑' n : ℕ, fχ χ n / Real.sqrt n * gh (HuR (Real.log x)) (Real.log n) : ℝ) : ℂ)) := by
  rw [KxZ, (hasSum_KxY hR (Real.log x)).tsum_eq, weilRHSC, gh_Hu_zero (Real.log_nonneg hx), archC]
  have h0 : HuR (Real.log x) 0 = 4 * (1 - Real.cosh (Real.log x / 2)) := by
    simp [HuR]; ring
  rw [h0]
  push_cast
  ring

/-- **Theorem B**, any primitive real `χ ≠ 1`: `K(2) = √2(K₁/2 + c_χ + ℓ/2)`, with `K₁ = K1Z χ`,
`ℓ = Re L′/L(1, χ)` and `c_χ = cB χ`. -/
theorem theoremBZ :
    (KxZ χ 2).re = √2 * (K1Z χ / 2 + cB χ + (deriv (LFunction χ) 1 / LFunction χ 1).re / 2) := by
  have hK := K1Z_eq hR
  rw [← logDeriv_apply] at hK
  rw [KxZ_explicit hR (by norm_num : (1:ℝ) ≤ 2), prime_two (χ := χ), ← logDeriv_apply, hK, cB]
  obtain ⟨hc, hs⟩ := cosh_sinh_log_two
  set L := logDeriv (LFunction χ) 1
  set Ψ := Complex.digamma ((1 + parity χ) / 2)
  have e : ((((Real.cosh (Real.log 2 / 2) : ℝ) : ℂ) * ((Real.log N : ℂ) - (Real.log π : ℂ) + Ψ + 2 * L) +
      ((-Real.sinh (Real.log 2 / 2) * (Real.log N - Real.log π) + archC χ (Real.log 2) - 2 * 0 : ℝ) : ℂ))).re
      = Real.cosh (Real.log 2 / 2) * (Real.log N - Real.log π + Ψ.re + 2 * L.re)
        - Real.sinh (Real.log 2 / 2) * (Real.log N - Real.log π) + archC χ (Real.log 2) := by
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re]
    norm_num
    ring
  rw [e, hc, hs]
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : √2 ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [hs2]
  ring

end PsiOmega

#print axioms PsiOmega.K1Z_pos
#print axioms PsiOmega.theoremBZ
