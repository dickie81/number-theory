import Mathlib
import WeilChiPos
import BallPsi

/-!
# Theorem B for a good real character: `K(2) = √2(K₁/2 + c_a + ℓ/2)`

For `χ` with `GoodChar χ` (an explicit hypothesis) let `K(x) = Σ_ρ x^{ρ−½}/(ρ(1 − ρ)) = Σ_u 2cos(τ_u log x)/(¼ + u)`
(`PsiOmega.KxC`, summed over the zeros `u = τ²` of `Ξ_χ(√w)`). Weil's explicit formula `PsiOmega.weil_XiC` for the
test function `H_u(t) = (cos(tu) − cosh(u/2))/(t² + ¼)` of `BallPsi` (entire, so no poles are crossed; `L(s, χ)` is
entire) gives, for `u ≥ 0`,
`K(e^u) = cosh(u/2)K₁ − sinh(u/2)log(N/π) + A_χ(u) − 2Σ_{n < e^u} Λ(n)χ(n)n^{−1/2}ĝ(log n)`
(`PsiOmega.KxC_explicit`), with `A_χ(u) = (1/2π)∫H_u(r)Re ψ((½ + δ)/2 + ir/2)dr` (`PsiOmega.archC`). At `x = 2` the
prime sum vanishes, and with `K₁ = log(N/π) + ψ((1 + δ)/2) + 2ℓ` (`PsiOmega.hasSum_K1`) this is
**Theorem B** (`PsiOmega.theoremB`): `K(2) = √2(K₁/2 + c_χ + ℓ/2)`, `ℓ = Re L′/L(1, χ)`, with the constant
`c_χ = Re ψ((1 + δ)/2)/4 + A_χ(log 2)/√2` (`PsiOmega.cB`), which depends on `χ` only through its parity.
Unconditional given `GoodChar χ`. See `formalisations/d2-density.md`.
-/

open Real Complex Filter Topology Set WeilForm WeilTest WeilStrip

noncomputable section

namespace PsiOmega

open DirichletCharacter BallPsi

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- `ĝ_{H_u}(v) = 0` for `v ≥ u ≥ 0`: only `n < e^u` enter the prime sum. -/
theorem gh_Hu_eq_zero {u v : ℝ} (hu : 0 ≤ u) (hv : u ≤ v) : gh (HuR u) v = 0 := by
  rw [gh_Hu, abs_of_nonneg (by linarith : 0 ≤ u + v), abs_of_nonpos (by linarith : u - v ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ v), Real.cosh_eq]
  rw [show -(u + v) / 2 = -(u / 2) + -v / 2 by ring, show -(-(u - v)) / 2 = u / 2 + -v / 2 by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- `ĝ_{H_u}(0) = −sinh(u/2)`. -/
theorem gh_Hu_zero {u : ℝ} (hu : 0 ≤ u) : gh (HuR u) 0 = -Real.sinh (u / 2) := by
  rw [gh_Hu, add_zero, sub_zero, abs_zero, neg_zero, zero_div, Real.exp_zero, mul_one,
    Real.cosh_eq, Real.sinh_eq, abs_of_nonneg hu]
  ring_nf

/-- The archimedean term `A_χ(u) = (1/2π)∫H_u(r)Re ψ((½ + δ)/2 + ir/2)dr`. -/
def archC (χ : DirichletCharacter ℂ N) (u : ℝ) : ℝ := 1 / (2 * π) * ∫ r, HuR u r * psiReC χ r

/-- `K(x) = Σ_u 2cos(τ_u log x)/(¼ + u)`, that is `Σ_ρ x^{ρ−½}/(ρ(1 − ρ))`. -/
def KxC (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑' i : ZeroIdx (sqF (XiC χ)), 2 * Complex.cos (tauC i * Real.log x) / (1 / 4 + i.1)

variable (hG : GoodChar χ)
include hG

theorem tauC_ne_half (i : ZeroIdx (sqF (XiC χ))) : tauC i ≠ I / 2 := fun h => by
  have := tauC_im hG i; rw [h] at this; norm_num at this

theorem tauC_ne_neg_half (i : ZeroIdx (sqF (XiC χ))) : tauC i ≠ -(I / 2) := fun h => by
  have := tauC_im hG i; rw [h] at this; norm_num at this

/-- The zero side: `Σ_u 2cos(τ_u u)/(¼ + u) = cosh(u/2)·Σ_u 2/(¼ + u) + Σ_u 2H_u(τ_u)`. -/
theorem hasSum_Kx (u : ℝ) :
    HasSum (fun i : ZeroIdx (sqF (XiC χ)) => 2 * Complex.cos (tauC i * u) / (1 / 4 + i.1))
      (((Real.cosh (u / 2) : ℝ) : ℂ) * ((Real.log N : ℂ) - (Real.log π : ℂ) +
        Complex.digamma ((1 + parity χ) / 2) + 2 * logDeriv (LFunction χ) 1) + (weilRHSC χ (HuR u) : ℂ)) := by
  obtain ⟨C, hC⟩ := stripTest_Hu u
  have hW := weil_XiC hG hC (Hu_even u) (Hu_real u)
  have hK := (hasSum_K1 hG).mul_left ((Real.cosh (u / 2) : ℝ) : ℂ)
  refine (hK.add hW).congr_fun fun i => ?_
  have hne : (1 / 4 + i.1 : ℂ) ≠ 0 := by
    intro h
    have h2 : tauC i ^ 2 = -(1 / 4) := by rw [tauC_sq]; linear_combination h
    have : (tauC i - I / 2) * (tauC i + I / 2) = 0 := by
      linear_combination h2 - Complex.I_sq / 4
    rcases mul_eq_zero.1 this with h | h
    · exact tauC_ne_half hG i (sub_eq_zero.1 h)
    · exact tauC_ne_neg_half hG i (by linear_combination h)
  rw [Hu_eq u (tauC_ne_half hG i) (tauC_ne_neg_half hG i), tauC_sq, add_comm (i.1 : ℂ) (1 / 4)]
  field_simp
  ring

/-- **The explicit formula for `K(x)`** for a good real character, `u = log x` (the prime sum is over `n < x` when `x ≥ 1`). -/
theorem KxC_explicit {x : ℝ} (hx : 1 ≤ x) :
    KxC χ x = (((Real.cosh (Real.log x / 2) : ℝ) : ℂ) * ((Real.log N : ℂ) - (Real.log π : ℂ) +
        Complex.digamma ((1 + parity χ) / 2) + 2 * logDeriv (LFunction χ) 1) +
      ((-Real.sinh (Real.log x / 2) * (Real.log N - Real.log π) + archC χ (Real.log x)
        - 2 * ∑' n : ℕ, fχ χ n / Real.sqrt n * gh (HuR (Real.log x)) (Real.log n) : ℝ) : ℂ)) := by
  rw [KxC, (hasSum_Kx hG (Real.log x)).tsum_eq, weilRHSC, gh_Hu_zero (Real.log_nonneg hx), archC]

omit [NeZero N] hG in
/-- At `x = 2` the prime sum vanishes. -/
theorem prime_two : ∑' n : ℕ, fχ χ n / Real.sqrt n * gh (HuR (Real.log 2)) (Real.log n) = 0 := by
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp [fχ]
  · rw [gh_Hu_eq_zero (Real.log_nonneg (by norm_num)) (Real.log_le_log (by norm_num) (by exact_mod_cast h)),
      mul_zero]

omit hG in
/-- The archimedean integral for parity `δ`: `A_δ(u) = (1/2π)∫H_u(r)Re ψ((½ + δ + ir)/2)dr`. -/
def archA (δ : ℕ) (u : ℝ) : ℝ :=
  1 / (2 * π) * ∫ r : ℝ, HuR u r * (Complex.digamma ((1 / 2 + I * r + δ) / 2)).re

omit hG in
/-- **The constant `c_a`** of Theorem B for parity `a`: `c_a = Re ψ((1 + a)/2)/4 + A_a(log 2)/√2`. -/
def cA (a : ℕ) : ℝ := (Complex.digamma ((1 + a) / 2)).re / 4 + archA a (Real.log 2) / √2

omit hG in
/-- The constant `c_χ = c_δ` of Theorem B, `δ` the parity of `χ`. -/
def cB (χ : DirichletCharacter ℂ N) : ℝ :=
  (Complex.digamma ((1 + parity χ) / 2)).re / 4 + archC χ (Real.log 2) / √2

omit [NeZero N] hG in
theorem cB_eq (χ : DirichletCharacter ℂ N) : cB χ = cA (parity χ) := rfl

omit hG in
theorem cosh_sinh_log_two : Real.cosh (Real.log 2 / 2) = 3 / (2 * √2) ∧ Real.sinh (Real.log 2 / 2) = 1 / (2 * √2) := by
  have hE : Real.exp (Real.log 2 / 2) = √2 := exp_log_half (by norm_num)
  have hE' : Real.exp (-(Real.log 2 / 2)) = 1 / √2 := by rw [Real.exp_neg, hE, one_div]
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : √2 ≠ 0 := by positivity
  rw [Real.cosh_eq, Real.sinh_eq, hE, hE']
  constructor <;> field_simp <;> linarith

/-- **Theorem B**: for a good real character, `K(2) = √2(K₁/2 + c_χ + ℓ/2)`, with `K₁ = K1C χ`,
`ℓ = Re L′/L(1, χ)` and `c_χ = cB χ`. -/
theorem theoremB :
    (KxC χ 2).re = √2 * (K1C χ / 2 + cB χ + (deriv (LFunction χ) 1 / LFunction χ 1).re / 2) := by
  have hK : K1C χ = Real.log N - Real.log π + (Complex.digamma ((1 + parity χ) / 2)).re
      + 2 * (logDeriv (LFunction χ) 1).re := by
    rw [K1C, (hasSum_K1 hG).tsum_eq]
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.log_re]
  rw [KxC_explicit hG (by norm_num : (1:ℝ) ≤ 2), prime_two (χ := χ), ← logDeriv_apply, hK, cB]
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
