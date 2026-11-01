/-
# The dh column of the ball kernel: the kernel of `dh` is not positive-definite

Plain statement. For `r > 0` let `K_dh(r) = Σ_s e^{(s − ½)²/2} r^{s − ½}`, the sum over the zeros `s = ½ ± 3iτ_u` of
the Davenport–Heilbronn function `dh` that the zeros `±τ_u` of `Ξ₃(t) = Ξ_dh(3t)` give (`kerDH`), built as
`BallKernel.kerK` is from the zeros of `ζ`. It is not positive-definite on the positive rationals (`not_posDef_dh`):
some `Σ_{a,b ∈ S} x_a x̄_b K_dh(a/b)` with `S` a finite set of positive rationals is not real and nonnegative.

* Its `2 × 2` minors on `{1, r}` are the twin sum of `TwinLandau` over the poles `P_u = 2iτ_u`, with the Gaussian
  weights `2e^{9P_u²/8}`, at `λ = (3/2)log r` (`twin_eq_kerDH`).
* So positive-definiteness would put every `P_u` on the imaginary axis (`BallKernel.re_eq_zero_of_dense`), and with it
  every zero of `dh` with `Re s > 0` on the line (`abs_two_re_sub_one_eq`). The certificate `dh_offline_zero` refutes
  that.

This is the dh column of `BallKernel.rh_iff_posDef`. `dh` has a functional equation of `ζ`'s kind and no Euler product,
so positive-definiteness on `ℚ₊^×` does not follow from the functional equation.

So `K_dh` has no realization by similitudes either (`not_realization_dh`): no inner product space carries vectors `w_r`
and similitudes `φ_n` of factor `n` with `φ_n(w_r) = w_{nr}` and `⟨w_b, w_a⟩ = √(ab)·K_dh(a/b)`, since one would make
`K_dh` positive-definite (`BallLattice.posDefQ_of_realization`). This is the dh column of
`BallLattice.rh_iff_realization`.
-/
import Mathlib
import BallKernel
import BallLattice
import DHTwin

open Real Complex Finset ComplexConjugate WeilForm
open scoped ComplexOrder

noncomputable section

namespace PsiOmega

/-- **The kernel of `dh`**: `K_dh(r) = Σ_u e^{(3iτ_u)²/2}(r^{3iτ_u} + r^{−3iτ_u})`, the sum of
`e^{(s − ½)²/2} r^{s − ½}` over the zeros `s = ½ ± 3iτ_u`, with `r^w` written `e^{w log r}`. -/
def kerDH (r : ℝ) : ℂ :=
  ∑' i : ZeroIdx (sqF XiDH3), cexp ((3 * I * tau3 i) ^ 2 / 2) *
    (cexp (3 * I * tau3 i * Real.log r) + cexp (-(3 * I * tau3 i) * Real.log r))

/-- The weight `2e^{9P²/8}` at the pole `P = 2iτ`: `2e^{(3iτ)²/2}`. -/
def gwDH (p : ℂ) : ℂ := 2 * cexp (9 * p ^ 2 / 8)

/-- **The Gaussian weights are summable over the zeros of `Ξ₃`**, by Hadamard's `Σ_u |u|^{−1} < ∞`. -/
theorem summable_gwDH : Summable fun i : ZeroIdx (sqF XiDH3) => ‖gwDH (2 * I * tau3 i)‖ := by
  have hs : Summable fun i : ZeroIdx (sqF XiDH3) => ‖i.1⁻¹‖ := hadamard_XiDH3.summ
  refine (hs.mul_left (4 * Real.exp (9 / 8))).of_norm_bounded fun i => ?_
  rw [norm_norm]
  have e1 : ‖2 * I * tau3 i‖ = 2 * ‖tau3 i‖ := by simp
  have e2 : ‖i.1‖ = ‖tau3 i‖ ^ 2 := by rw [← tau3_sq, norm_pow]
  have hP : 0 < ‖2 * I * tau3 i‖ :=
    norm_pos_iff.2 fun h => im_pole3_ne i (by rw [h]; simp)
  have ht : 0 < ‖tau3 i‖ ^ 2 := by
    have : 0 < ‖tau3 i‖ := by rw [e1] at hP; linarith
    positivity
  have hb := BallKernel.norm_cexp_sq_mul_le (a := 9 / 8) (by norm_num) (abs_re_pole3_lt i)
  rw [e1] at hb
  have hg : gwDH (2 * I * tau3 i) = 2 * cexp (((9 / 8 : ℝ) : ℂ) * (2 * I * tau3 i) ^ 2) := by
    unfold gwDH; congr 2; push_cast; ring
  rw [hg, norm_mul, Complex.norm_two, norm_inv, e2, ← div_eq_mul_inv, le_div_iff₀ ht]
  nlinarith

/-- The poles `P_u = 2iτ_u` of `dh` with the Gaussian weights. -/
theorem twinPoles_gwDH :
    TwinLandau.TwinPoles (fun i : ZeroIdx (sqF XiDH3) => 2 * I * tau3 i) fun i => gwDH (2 * I * tau3 i) :=
  ⟨summable_gwDH, abs_re_pole3_lt, im_pole3_ne, finite_tau3⟩

lemma summable_kerDH (l : ℝ) :
    Summable fun i : ZeroIdx (sqF XiDH3) => gwDH (2 * I * tau3 i) * cexp (l * (2 * I * tau3 i)) :=
  TwinLandau.summable_cw_mul twinPoles_gwDH (B := Real.exp |l|) fun i => by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h := abs_re_pole3_lt i
    have e : ((l : ℂ) * (2 * I * tau3 i)).re = l * (2 * I * tau3 i).re := by simp
    rw [e]
    calc l * (2 * I * tau3 i).re ≤ |l * (2 * I * tau3 i).re| := le_abs_self _
      _ = |l| * |(2 * I * tau3 i).re| := abs_mul _ _
      _ ≤ |l| * 1 := mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
      _ = |l| := mul_one _

/-- The exponentials of a term of the kernel in the pole variable `P = 2iτ`. -/
lemma kerDH_exps (i : ZeroIdx (sqF XiDH3)) (L : ℝ) :
    cexp (9 * (2 * I * tau3 i) ^ 2 / 8) = cexp ((3 * I * tau3 i) ^ 2 / 2) ∧
    cexp (((3 / 2 * L : ℝ) : ℂ) * (2 * I * tau3 i)) = cexp (3 * I * tau3 i * L) ∧
    cexp (((-(3 / 2 * L) : ℝ) : ℂ) * (2 * I * tau3 i)) = cexp (-(3 * I * tau3 i) * L) :=
  ⟨by congr 1; ring, by congr 1; push_cast; ring, by congr 1; push_cast; ring⟩

/-- The terms of the kernel are summable at every `r`. -/
lemma summable_kerDH_term (L : ℝ) : Summable fun i : ZeroIdx (sqF XiDH3) =>
    cexp ((3 * I * tau3 i) ^ 2 / 2) * (cexp (3 * I * tau3 i * L) + cexp (-(3 * I * tau3 i) * L)) := by
  refine (((summable_kerDH (3 / 2 * L)).div_const 2).add ((summable_kerDH (-(3 / 2 * L))).div_const 2)).congr
    fun i => ?_
  obtain ⟨e1, e2, e3⟩ := kerDH_exps i L
  unfold gwDH
  rw [e1, e2, e3]
  ring

/-- **The `2 × 2` minors are the twin sum**: `2K_dh(1) + K_dh(r) + K_dh(1/r)` is the twin sum over the poles
`2iτ_u` with the weights `2e^{9P²/8}`, at `λ = (3/2)log r`. -/
theorem twin_eq_kerDH (r : ℝ) :
    TwinLandau.Wsum (fun i : ZeroIdx (sqF XiDH3) => 2 * I * tau3 i) (fun i => gwDH (2 * I * tau3 i))
      (3 / 2 * Real.log r) = 2 * kerDH 1 + kerDH r + kerDH r⁻¹ := by
  unfold kerDH
  rw [Real.log_one, Real.log_inv, ← tsum_mul_left,
    ← ((summable_kerDH_term 0).mul_left 2).tsum_add (summable_kerDH_term _),
    ← (((summable_kerDH_term 0).mul_left 2).add (summable_kerDH_term _)).tsum_add (summable_kerDH_term _)]
  unfold TwinLandau.Wsum TwinLandau.wq
  refine tsum_congr fun i => ?_
  obtain ⟨e1, e2, e3⟩ := kerDH_exps i (Real.log r)
  have e4 : cexp (3 * I * tau3 i * ((-Real.log r : ℝ) : ℂ)) = cexp (-(3 * I * tau3 i) * Real.log r) := by
    congr 1; push_cast; ring
  have e5 : cexp (-(3 * I * tau3 i) * ((-Real.log r : ℝ) : ℂ)) = cexp (3 * I * tau3 i * Real.log r) := by
    congr 1; push_cast; ring
  have e6 : cexp (-(((3 / 2 * Real.log r : ℝ) : ℂ) * (2 * I * tau3 i))) = cexp (-(3 * I * tau3 i) * Real.log r) := by
    congr 1; push_cast; ring
  unfold gwDH
  dsimp only
  rw [e1, e2, e4, e5, e6]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

/-- **The kernel of `dh` is not positive-definite on the positive rationals.** If it were, every pole `2iτ_u` would be
on the imaginary axis (`BallKernel.re_eq_zero_of_dense`), so every zero of `dh` with `Re s > 0` on the line, which
`dh_offline_zero` refutes. -/
theorem not_posDef_dh : ¬ BallKernel.PosDefQ kerDH := by
  intro hK
  have := countable_ZeroIdx3
  have hW : ∀ r : ℚ, 0 < r → 0 ≤ TwinLandau.Wsum (fun i : ZeroIdx (sqF XiDH3) => 2 * I * tau3 i)
      (fun i => gwDH (2 * I * tau3 i)) (3 / 2 * Real.log r) := fun r hr => by
    rw [twin_eq_kerDH]
    exact BallKernel.minor_nonneg hK hr
  have hre := BallKernel.re_eq_zero_of_dense twinPoles_gwDH (G := gwDH) (fun _ => rfl)
    (fun p => by unfold gwDH; rw [neg_sq]) (fun p _ => mul_ne_zero two_ne_zero (Complex.exp_ne_zero _))
    (by norm_num) hW
  obtain ⟨s, hs, h0, hne⟩ := dh_offline_zero
  obtain ⟨i, hi⟩ := tau3_of_dh_zero hs h0
  have h1 := abs_two_re_sub_one_eq hi
  rw [hre i, abs_zero, mul_zero, abs_eq_zero] at h1
  exact hne (by linarith)

/-- **The kernel of `dh` has no realization by similitudes** (`BallLattice.Realization`): a realization would make it
positive-definite on `ℚ₊^×` (`BallLattice.posDefQ_of_realization`), which `not_posDef_dh` refutes. -/
theorem not_realization_dh : IsEmpty (BallLattice.Realization kerDH) :=
  ⟨fun R => not_posDef_dh (BallLattice.posDefQ_of_realization R)⟩

end PsiOmega

#print axioms PsiOmega.summable_gwDH
#print axioms PsiOmega.twin_eq_kerDH
#print axioms PsiOmega.not_posDef_dh
#print axioms PsiOmega.not_realization_dh
