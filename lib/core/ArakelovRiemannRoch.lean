/-
# Riemann–Roch for the Arakelov divisors of `ℚ`, and Lagarias–Rains's `Z(w, s)` as an integral over them

Plain statement. An Arakelov divisor `D` of `ℚ` is determined by its degree `d = deg D ∈ ℝ`. Its sections are the
lattice `ℤ`, with the norm `‖n‖_D = e^{−d}|n|`, and G. van der Geer and R. Schoof (Selecta Math. 6 (2000)) measure
them by `h⁰(D) = log Σ_{n ∈ ℤ} e^{−π‖n‖_D²} = log θ(e^{−2d})` (`h0`), the logarithm of a Gaussian-weighted count of
the lattice points: the sections of norm at most about `1`.
* **Riemann–Roch** (`riemann_roch`): `h⁰(D) − h⁰(K − D) = deg D`, with `K = 0`, the canonical divisor of `ℚ`, of
  degree `log |d_ℚ| = 0`. It is the functional equation `θ(1/x) = √x·θ(x)` (`TwoVariableZeta.theta_inv`).
* **Riemann's inequality** (`le_h0`): `h⁰(D) ≥ max(0, deg D)`, from `θ ≥ 1` and Riemann–Roch.
* **Vanishing** (`tendsto_h0_atBot`, `tendsto_h0_sub_atTop`): `h⁰(D) → 0` as `deg D → −∞`, and `h⁰(D) − deg D → 0` as
  `deg D → ∞`: in large degree `h⁰` is the degree, as `h⁰ = deg + 1 − g` for a curve of genus `g` far from `0`.
* **The two-variable zeta function** (`Z_eq_integral`): `θ(e^{−2d})^w = e^{w·h⁰(D)}` (`thetaPow_exp`), so on
  `Re s > w` Lagarias and Rains's `Z(w, s)` (`TwoVariableZeta.Z`) is `∫_ℝ (e^{w·h⁰(D)} − 1) e^{−s·deg D} d(deg D)`: van
  der Geer and Schoof's integral over the Arakelov divisors of `ℚ` of the exponential of `w` times the size of the
  space of sections, regularised by the `−1`.
So the "degree as a growth rate of lattice points in balls" of `docs/ball-conjecture.md` is a theorem for `Spec ℤ`
itself: `h⁰` is the logarithm of a lattice-point count, Riemann–Roch is the functional equation of `θ`, and `h⁰`
grows like the degree. The lattices of `HodgeCounting` would have to do the same for the divisors built from the
primes.
-/
import Mathlib
import TwoVariableZeta

open Real Complex Filter Topology HurwitzZeta MeasureTheory

noncomputable section

namespace ArakelovRiemannRoch

open TwoVariableZeta

/-- **`h⁰` of the Arakelov divisor of degree `d` of `ℚ`**, after van der Geer and Schoof:
`log Σ_{n ∈ ℤ} e^{−πe^{−2d}n²}`, the logarithm of the Gaussian-weighted count of the sections `n ∈ ℤ`, of norm
`e^{−d}|n|`. -/
def h0 (d : ℝ) : ℝ := Real.log (evenKernel 0 (Real.exp (-2 * d)))

lemma theta_pos (d : ℝ) : 0 < evenKernel 0 (Real.exp (-2 * d)) :=
  lt_of_lt_of_le one_pos (one_le_theta (Real.exp_pos _))

/-- **Riemann–Roch for the Arakelov divisors of `ℚ`**: `h⁰(D) − h⁰(K − D) = deg D` with `K = 0`, which is the
functional equation of `θ`. -/
theorem riemann_roch (d : ℝ) : h0 d - h0 (-d) = d := by
  have h := theta_inv (Real.exp_pos (-2 * d))
  rw [one_div, ← Real.exp_neg, show -(-2 * d) = -2 * -d by ring] at h
  have e : Real.exp (-2 * d) ^ (1 / 2 : ℝ) = Real.exp (-d) := by
    rw [← Real.exp_mul]
    ring_nf
  unfold h0
  rw [h, e, Real.log_mul (Real.exp_pos _).ne' (theta_pos d).ne', Real.log_exp]
  ring

theorem h0_nonneg (d : ℝ) : 0 ≤ h0 d := Real.log_nonneg (one_le_theta (Real.exp_pos _))

/-- **Riemann's inequality**: `h⁰(D) ≥ max(0, deg D)`. -/
theorem le_h0 (d : ℝ) : max 0 d ≤ h0 d :=
  max_le (h0_nonneg d) (by linarith [riemann_roch d, h0_nonneg (-d)])

/-- `θ(t) → 1` as `t → ∞`. -/
lemma tendsto_theta : Tendsto (evenKernel 0) atTop (𝓝 1) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub 0
  simp only [ite_true] at hO
  have hexp : Tendsto (fun t : ℝ => Real.exp (-p * t)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hp)
  exact tendsto_sub_nhds_zero_iff.1 (hO.trans_tendsto hexp)

/-- **Vanishing in negative degree**: `h⁰(D) → 0` as `deg D → −∞`. -/
theorem tendsto_h0_atBot : Tendsto h0 atBot (𝓝 0) := by
  have h1 : Tendsto (fun d : ℝ => -2 * d) atBot atTop :=
    (tendsto_neg_atBot_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).congr fun d => by ring
  have h2 := tendsto_theta.comp (Real.tendsto_exp_atTop.comp h1)
  have h3 := ((Real.continuousAt_log one_ne_zero).tendsto).comp h2
  rw [Real.log_one] at h3
  exact h3.congr fun d => rfl

/-- **`h⁰` is the degree in large degree**: `h⁰(D) − deg D → 0` as `deg D → ∞`. -/
theorem tendsto_h0_sub_atTop : Tendsto (fun d => h0 d - d) atTop (𝓝 0) := by
  refine (tendsto_h0_atBot.comp tendsto_neg_atTop_atBot).congr fun d => ?_
  simp only [Function.comp_apply]
  linarith [riemann_roch d]

/-- `θ(e^{−2d})^w = e^{w·h⁰(D)}`: the integrand of `Z(w, ·)` is the exponential of `w` times the size of the
sections. -/
lemma thetaPow_exp (w d : ℝ) : thetaPow w (Real.exp (-2 * d)) = ((Real.exp (w * h0 d) : ℝ) : ℂ) := by
  unfold thetaPow h0
  rw [Real.rpow_def_of_pos (theta_pos d), mul_comm]

/-- The Mellin transform in the variable `u = −log t`. -/
lemma mellin_eq_integral (f : ℝ → ℂ) (s : ℂ) : mellin f s = ∫ u : ℝ, cexp (-s * u) * f (Real.exp (-u)) := by
  rw [mellin_eq_fourier, fourier_real_eq_integral_exp_smul]
  congr 1
  funext u
  rw [smul_eq_mul, Complex.real_smul, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  conv_rhs => rw [← Complex.re_add_im s]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
  push_cast
  field_simp
  ring_nf

/-- **Lagarias and Rains's `Z(w, s)` is van der Geer and Schoof's integral over the Arakelov divisors of `ℚ`**: on
`Re s > w`, `Z(w, s) = ∫_ℝ (e^{w·h⁰(D)} − 1) e^{−s·deg D} d(deg D)`. -/
theorem Z_eq_integral (w : ℝ) (hw : 0 < w) {s : ℂ} (hs : w < s.re) :
    Z w hw s = ∫ d : ℝ, cexp (-s * d) * ((Real.exp (w * h0 d) - 1 : ℝ) : ℂ) := by
  have hM := (hasMellin w hw hs).2
  rw [mellin_eq_integral] at hM
  have hsub := Measure.integral_comp_mul_left (fun u : ℝ => cexp (-(s / 2) * u) * (thetaPow w (Real.exp (-u)) - 1)) 2
  have e : ∀ d : ℝ, cexp (-(s / 2) * ((2 * d : ℝ) : ℂ)) * (thetaPow w (Real.exp (-(2 * d))) - 1) =
      cexp (-s * d) * ((Real.exp (w * h0 d) - 1 : ℝ) : ℂ) := fun d => by
    rw [show -(2 * d) = -2 * d by ring, thetaPow_exp]
    push_cast
    ring_nf
  simp only [e] at hsub
  rw [hsub, hM]
  norm_num
  ring

end ArakelovRiemannRoch

#print axioms ArakelovRiemannRoch.riemann_roch
#print axioms ArakelovRiemannRoch.le_h0
#print axioms ArakelovRiemannRoch.tendsto_h0_atBot
#print axioms ArakelovRiemannRoch.tendsto_h0_sub_atTop
#print axioms ArakelovRiemannRoch.Z_eq_integral
