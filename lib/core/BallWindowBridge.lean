import Mathlib
import BallPsi
import WindowGRH
import ExplicitBridge
import RiemannKernel

/-!
# The ball kernel and the rebuild's ramp error

A bridge between the library's ball kernel (`BallPsi.kerHψ`, the Hadamard kernel `K_H` from the primes) and the
ramp error of `ζ` in the rebuild of L. Alpöge's proof (`WindowGRH.zetaFamily.G`).

* **The archimedean constant** (`kappa_eq`): `κ = (1/2π)∫ Re ψ(¼ + ir/2)/(r² + ¼) dr = ψ(½) = −γ − 2 log 2`. The
  proof writes `Re ψ(¼ + ir/2) − ψ(¼) = ∫_0^∞ k(t)(1 − cos(rt/2)) dt` with `k(t) = e^{−t/4}/(1 − e^{−t})` (Gauss,
  `WeilForm.psiReQ_sub`), integrates in `r` first by Tonelli (`BallPsi.integral_cos_div`), and is left with
  `∫_0^∞ k(t)(1 − e^{−t/4}) dt = ψ(½) − ψ(¼)`, Gauss's integral again (`GammaIntegrals.digamma_sub_eq_integral`).
* **The archimedean term** (`archH_add_cosh_le`): `|A(u) + κ cosh(u/2)| ≤ M` for every `u`, with
  `M = (1/2π)∫|Re ψ(¼ + ir/2)|/(r² + ¼) dr` (`archM`): `A(u) + κ cosh(u/2)` is `(1/2π)∫cos(ru) Re ψ/(r² + ¼)`.
* **The bridge** (`kerHψ_sub_ramp`, `abs_kerHψ_sub_ramp_le`): for `x ≥ 1`, with `u = log x`,
  `K_H(x) − x^{−1/2}G(x) = (1 + γ − log π + u)/√x + A(u) + κ cosh(u/2)`, so
  `|K_H(x) − x^{−1/2}G(x)| ≤ B = |1 + γ − log π| + 2 + M` (`bridgeB`). The terms in `√x` cancel exactly, because
  `κ = −γ − 2 log 2`: the ball kernel is the ramp error of `ζ` scaled by `x^{−1/2}`, up to a bounded term.
* **RH as the window bound** (`WindowGRH.rh_iff_zetaWindowBound`): under RH `‖K_H(x)‖ ≤ ‖K_H(1)‖`
  (`norm_kerH_le_of_rh`), so `|G(x)| ≤ (‖K_H(1)‖ + B)√x` for `x ≥ 1` (`abs_zetaRamp_le_of_rh`, von Koch's bound for
  the ramp), which gives `WindowGRH.ZetaWindowBound`; `WindowGRH.riemannHypothesis_of_zetaWindowBound` is the converse.
* **The mirror sign** (`WindowGRH.riemannHypothesis_of_zetaWindowLowerBound`, `WindowGRH.rh_iff_zetaWindowLowerBound`):
  the lower bound `G(x) ≥ −Cx^θ` on windows also gives RH. Landau's theorem on windows (`LandauWindow.re_le_of_windows`)
  applies to `−G`, whose transform has residue of the opposite sign at each zero; its condition at a real pole is
  vacuous, as `ζ` has no zero in `(0, 1)` (`WeilForm.riemannZeta_ne_zero_of_mem_Ioo`).
* **The balance identity at a constant weight** (`ZetaBalance.Setting.balance_const`): with `W ≡ w`, Lemma B
  collapses to `ASK(a, t, w) − MAIN(a, w) = w(G(a/w) − Re g_{χ_d}(a/w))`, the ramp error of `ζ` less that of the
  primitive character of `χ_d`; and `ASK(m, t, n)` is the prime part `Σ_{k ≤ m/n} Λ(k)(m/k − n)` of the ball's Gram
  entry (`BallPsi.gram_explicit`, `gram_primePart`), each term weighted by `1[(k, QS·q) = 1](1 − χ_d(k))`
  (`ZetaBalance.Setting.ASK_const`).
-/

open Real MeasureTheory Set Filter
open WeilForm WeilTest WeilStrip
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace BallWindow

open BallKernel BallLattice BallHadamard BallPsi

/-! ## The archimedean constant -/

/-- `k(t) = e^{−t/4}/(1 − e^{−t})`, the kernel of Gauss's integral at `¼`. -/
abbrev kk (t : ℝ) : ℝ := kkQ (1 / 4) t

/-- Gauss's integral at `½` and `¼`: `∫_0^∞ k(t)(1 − e^{−t/4}) dt = ψ(½) − ψ(¼)`, integrably. -/
theorem gauss_half_quarter :
    IntegrableOn (fun t => kk t * (1 - Real.exp (-(t / 4)))) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), kk t * (1 - Real.exp (-(t / 4))) =
        (-2 * Real.log 2 - eulerMascheroniConstant) - psiRe 0 := by
  have hz : (0 : ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  have hw : (0 : ℝ) < ((1 / 4 : ℂ)).re := by norm_num
  obtain ⟨hI, hE⟩ := GammaIntegrals.digamma_sub_eq_integral hz hw
  have he : ∀ t : ℝ, GammaIntegrals.gaussK (1 / 2) (1 / 4) t = ((kk t * (1 - Real.exp (-(t / 4))) : ℝ) : ℂ) := by
    intro t
    unfold GammaIntegrals.gaussK kk kkQ
    have h1 : Complex.exp (-((1 / 4 : ℂ) * t)) = ((Real.exp (-(1 / 4 * t)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    have h2 : Complex.exp (-((1 / 2 : ℂ) * t)) = ((Real.exp (-(1 / 4 * t)) * Real.exp (-(t / 4)) : ℝ) : ℂ) := by
      rw [← Real.exp_add, Complex.ofReal_exp]; push_cast; ring_nf
    rw [h1, h2]
    push_cast
    ring
  have hI' : IntegrableOn (fun t => ((kk t * (1 - Real.exp (-(t / 4))) : ℝ) : ℂ)) (Ioi 0) :=
    hI.congr_fun (fun t _ => he t) measurableSet_Ioi
  refine ⟨?_, ?_⟩
  · have := hI'.re
    simp only [RCLike.re_to_complex, Complex.ofReal_re] at this
    exact this
  · have h := congrArg Complex.re hE
    rw [Complex.sub_re, Complex.digamma_one_half, setIntegral_congr_fun measurableSet_Ioi (fun t _ => he t),
      integral_complex_ofReal, Complex.ofReal_re] at h
    have h4 : (Complex.digamma (1 / 4)).re = psiRe 0 := by
      rw [← psiReQ_quarter, psiReQ_zero]; norm_num
    rw [← h, h4]
    have hl : (Complex.log 2).re = Real.log 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num), Complex.ofReal_re]
    simp [hl]

/-- `∫(1 − cos(rw))/(r² + ¼) dr = 2π(1 − e^{−|w|/2})`. -/
theorem integral_one_sub_cos_div (w : ℝ) :
    ∫ r : ℝ, (1 - Real.cos (r * w)) / (r ^ 2 + 1 / 4) = 2 * π * (1 - Real.exp (-|w| / 2)) := by
  have h0 := integral_cos_div 0
  simp only [mul_zero, Real.cos_zero, abs_zero, neg_zero, zero_div, Real.exp_zero, mul_one] at h0
  have e : (fun r : ℝ => (1 - Real.cos (r * w)) / (r ^ 2 + 1 / 4)) =
      fun r => 1 / (r ^ 2 + 1 / 4) - Real.cos (r * w) / (r ^ 2 + 1 / 4) := by
    funext r; ring
  rw [e, integral_sub integrable_cauchy (integrable_cos_div w), h0, integral_cos_div]
  ring

/-- The Tonelli integrand `k(t)(1 − cos(rt/2))/(r² + ¼)`. -/
def tonF (t r : ℝ) : ℝ := kk t * (1 - Real.cos (r * (t / 2))) / (r ^ 2 + 1 / 4)

theorem tonF_nonneg {t : ℝ} (ht : 0 < t) (r : ℝ) : 0 ≤ tonF t r :=
  div_nonneg (mul_nonneg (kkQ_nonneg _ ht) (by linarith [Real.cos_le_one (r * (t / 2))])) (by positivity)

theorem integrable_tonF (t : ℝ) : Integrable (tonF t) := by
  refine ((integrable_cauchy.sub (integrable_cos_div (t / 2))).const_mul (kk t)).congr
    (Eventually.of_forall fun r => ?_)
  simp only [tonF, Pi.sub_apply]
  ring

theorem integral_tonF {t : ℝ} (ht : 0 < t) :
    ∫ r, tonF t r = 2 * π * (kk t * (1 - Real.exp (-(t / 4)))) := by
  have e : (fun r => tonF t r) = fun r => kk t * ((1 - Real.cos (r * (t / 2))) / (r ^ 2 + 1 / 4)) := by
    funext r; unfold tonF; ring
  rw [e, integral_const_mul, integral_one_sub_cos_div, abs_of_pos (by linarith : 0 < t / 2)]
  ring_nf

theorem measurable_tonF : Measurable (Function.uncurry tonF) := by
  have hk : Measurable fun p : ℝ × ℝ => kk p.1 := (measurable_kkQ _).comp measurable_fst
  have hc : Measurable fun p : ℝ × ℝ => (1 - Real.cos (p.2 * (p.1 / 2))) / (p.2 ^ 2 + 1 / 4) := by
    fun_prop
  have e : Function.uncurry tonF =
      fun p : ℝ × ℝ => kk p.1 * ((1 - Real.cos (p.2 * (p.1 / 2))) / (p.2 ^ 2 + 1 / 4)) := by
    funext p
    show tonF p.1 p.2 = _
    unfold tonF
    ring
  rw [e]
  exact hk.mul hc

/-- **Tonelli**: `(t, r) ↦ k(t)(1 − cos(rt/2))/(r² + ¼)` is integrable on `(0, ∞) × ℝ`. -/
theorem integrable_tonF_prod :
    Integrable (Function.uncurry tonF) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  refine (integrable_prod_iff measurable_tonF.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Eventually.of_forall fun t => integrable_tonF t
  · have h := gauss_half_quarter.1.const_mul (2 * π)
    refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
    simp only [Function.uncurry_apply_pair]
    rw [← integral_tonF ht]
    exact (integral_congr_ae (Eventually.of_forall fun r =>
      Real.norm_of_nonneg (tonF_nonneg ht r))).symm

/-- The swapped inner integral: `∫_0^∞ k(t)(1 − cos(rt/2)) dt/(r² + ¼) = (Re ψ(¼ + ir/2) − ψ(¼))/(r² + ¼)`. -/
theorem integral_tonF_t (r : ℝ) :
    ∫ t in Ioi (0 : ℝ), tonF t r = (psiRe r - psiRe 0) / (r ^ 2 + 1 / 4) := by
  unfold tonF
  rw [integral_div]
  congr 1
  have h := (psiReQ_sub (q := 1 / 4) (by norm_num) r).2
  rw [psiReQ_quarter] at h
  rw [h]

/-- `r ↦ (Re ψ(¼ + ir/2) − ψ(¼))/(r² + ¼)` is integrable. -/
theorem integrable_psiRe_sub : Integrable fun r : ℝ => (psiRe r - psiRe 0) / (r ^ 2 + 1 / 4) := by
  have h := integrable_tonF_prod.integral_prod_right
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only [Function.uncurry_apply_pair]
  exact integral_tonF_t r

/-- `∫(Re ψ(¼ + ir/2) − ψ(¼))/(r² + ¼) dr = 2π(ψ(½) − ψ(¼))`. -/
theorem integral_psiRe_sub :
    ∫ r : ℝ, (psiRe r - psiRe 0) / (r ^ 2 + 1 / 4) =
      2 * π * ((-2 * Real.log 2 - eulerMascheroniConstant) - psiRe 0) := by
  have hs := integral_integral_swap integrable_tonF_prod
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => integral_tonF ht), integral_const_mul,
    gauss_half_quarter.2] at hs
  rw [hs]
  exact integral_congr_ae (Eventually.of_forall fun r => (integral_tonF_t r).symm)

/-- `g(r) = Re ψ(¼ + ir/2)/(r² + ¼)`. -/
def gpsi (r : ℝ) : ℝ := psiRe r / (r ^ 2 + 1 / 4)

theorem integrable_gpsi : Integrable gpsi := by
  refine ((integrable_cauchy.const_mul (psiRe 0)).add integrable_psiRe_sub).congr
    (Eventually.of_forall fun r => ?_)
  simp only [gpsi, Pi.add_apply]
  ring

/-- The archimedean constant `κ = (1/2π)∫ Re ψ(¼ + ir/2)/(r² + ¼) dr`. -/
def kappa : ℝ := 1 / (2 * π) * ∫ r, gpsi r

/-- **The archimedean constant**: `κ = (1/2π)∫ Re ψ(¼ + ir/2)/(r² + ¼) dr = −γ − 2 log 2`. -/
theorem kappa_eq : kappa = -eulerMascheroniConstant - 2 * Real.log 2 := by
  have h0 := integral_cos_div 0
  simp only [mul_zero, Real.cos_zero, abs_zero, neg_zero, zero_div, Real.exp_zero, mul_one] at h0
  have e : gpsi = fun r => psiRe 0 * (1 / (r ^ 2 + 1 / 4)) + (psiRe r - psiRe 0) / (r ^ 2 + 1 / 4) := by
    funext r; unfold gpsi; ring
  unfold kappa
  rw [e, integral_add (integrable_cauchy.const_mul _) integrable_psiRe_sub, integral_const_mul, h0,
    integral_psiRe_sub]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **`κ = ψ(½)`**, Mathlib's digamma function at `½`. -/
theorem kappa_eq_digamma : (kappa : ℂ) = Complex.digamma (1 / 2) := by
  rw [kappa_eq, Complex.digamma_one_half]
  have hl : ((Real.log 2 : ℝ) : ℂ) = Complex.log 2 := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  push_cast
  rw [hl]
  ring

/-! ## The archimedean term -/

/-- The bound `M = (1/2π)∫|Re ψ(¼ + ir/2)|/(r² + ¼) dr` on the oscillating part of `A(u)`. -/
def archM : ℝ := 1 / (2 * π) * ∫ r, |gpsi r|

theorem archM_nonneg : 0 ≤ archM :=
  mul_nonneg (by positivity) (integral_nonneg fun r => abs_nonneg _)

/-- `A(u) + κ cosh(u/2) = (1/2π)∫cos(ru) Re ψ(¼ + ir/2)/(r² + ¼) dr`. -/
theorem archH_add_cosh (u : ℝ) :
    archH u + kappa * Real.cosh (u / 2) = 1 / (2 * π) * ∫ r, Real.cos (r * u) * gpsi r := by
  have hc : Integrable fun r => Real.cos (r * u) * gpsi r :=
    integrable_gpsi.norm.mono' ((by fun_prop : Continuous fun r : ℝ => Real.cos (r * u)).aestronglyMeasurable.mul
      integrable_gpsi.aestronglyMeasurable) (Eventually.of_forall fun r => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
  have e : (fun r => HuR u r * psiRe r) = fun r => Real.cos (r * u) * gpsi r - Real.cosh (u / 2) * gpsi r := by
    funext r; unfold HuR gpsi; ring
  unfold archH kappa
  rw [e, integral_sub hc (integrable_gpsi.const_mul _), integral_const_mul]
  ring

/-- **The archimedean term less its growth is bounded**: `|A(u) + κ cosh(u/2)| ≤ M` for every `u`. -/
theorem archH_add_cosh_le (u : ℝ) : |archH u + kappa * Real.cosh (u / 2)| ≤ archM := by
  rw [archH_add_cosh, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  unfold archM
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun r => abs_nonneg _) integrable_gpsi.abs (Eventually.of_forall fun r => ?_))
  simp only [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)

/-! ## The bridge -/

/-- The bound of the bridge: `B = |1 + γ − log π| + 2 + M`. -/
def bridgeB : ℝ := |1 + eulerMascheroniConstant - Real.log π| + 2 + archM

theorem bridgeB_nonneg : 0 ≤ bridgeB := by
  unfold bridgeB; have := archM_nonneg; positivity

lemma Icc_one_eq_Ioc_zero (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
  ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

lemma ramp_sum_eq {x : ℝ} :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) =
      x * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / n - Chebyshev.psi x := by
  rw [Icc_one_eq_Ioc_zero, Chebyshev.psi, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **The bridge, exactly**: for `x ≥ 1`, with `u = log x`,
`K_H(x) − x^{−1/2}G(x) = (1 + γ − log π + u)/√x + (A(u) + κ cosh(u/2))`. -/
theorem kerHψ_sub_ramp {x : ℝ} (hx : 1 ≤ x) :
    kerHψ x - ((x ^ (-(1 / 2 : ℝ)) * WindowGRH.zetaFamily.G x : ℝ) : ℂ) =
      (((1 + eulerMascheroniConstant - Real.log π + Real.log x) / Real.sqrt x +
        (archH (Real.log x) + kappa * Real.cosh (Real.log x / 2)) : ℝ) : ℂ) := by
  have hx0 : 0 < x := by linarith
  have hmax : max x x⁻¹ = x := max_eq_left ((inv_le_one_of_one_le₀ hx).trans hx)
  unfold kerHψ
  rw [hmax, WindowGRH.zetaFamily_G, ramp_sum_eq, ← Complex.ofReal_sub, kappa_eq]
  congr 1
  set L := Real.log x with hL
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hss : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hE : Real.exp (L / 2) = s := exp_log_half hx0
  have hE' : Real.exp (-(L / 2)) = s⁻¹ := by rw [Real.exp_neg, hE]
  have hr : x ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
  have h4 : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hr, Real.cosh_eq, Real.sinh_eq, hE, hE', h4, ← hss]
  field_simp
  ring

/-- **The ball kernel is the ramp error of `ζ`, up to a bounded term**: for `x ≥ 1`,
`|K_H(x) − x^{−1/2}G(x)| ≤ B`, with `G` the rebuild's error `Σ_{n ≤ x} Λ(n)(x/n − 1) − x log x + (1 + γ)x`. -/
theorem abs_kerHψ_sub_ramp_le {x : ℝ} (hx : 1 ≤ x) :
    ‖kerHψ x - ((x ^ (-(1 / 2 : ℝ)) * WindowGRH.zetaFamily.G x : ℝ) : ℂ)‖ ≤ bridgeB := by
  have hx0 : 0 < x := by linarith
  rw [kerHψ_sub_ramp hx, Complex.norm_real, Real.norm_eq_abs]
  set L := Real.log x with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hs1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx
  have hs0 : 0 < Real.sqrt x := by linarith
  have hE : Real.exp (L / 2) = Real.sqrt x := exp_log_half hx0
  have hLs : L ≤ 2 * Real.sqrt x := by
    have := Real.add_one_le_exp (L / 2)
    rw [hE] at this
    linarith
  have h1 : |(1 + eulerMascheroniConstant - Real.log π + L) / Real.sqrt x| ≤
      |1 + eulerMascheroniConstant - Real.log π| + 2 := by
    rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    have := abs_add_le (1 + eulerMascheroniConstant - Real.log π) L
    rw [abs_of_nonneg hL0] at this
    have hc := abs_nonneg (1 + eulerMascheroniConstant - Real.log π)
    nlinarith
  unfold bridgeB
  exact (abs_add_le _ _).trans (add_le_add h1 (archH_add_cosh_le L))

/-- The two names of the kernel agree on `(0, ∞)`, so the bridge holds for `K_H` itself. -/
theorem abs_kerH_sub_ramp_le {x : ℝ} (hx : 1 ≤ x) :
    ‖kerH x - ((x ^ (-(1 / 2 : ℝ)) * WindowGRH.zetaFamily.G x : ℝ) : ℂ)‖ ≤ bridgeB := by
  rw [kerH_eq_kerHψ (by linarith)]
  exact abs_kerHψ_sub_ramp_le hx

/-! ## Under RH -/

/-- Under RH every term of `K_H(x)` has the modulus of the term of `K_H(1)`. -/
lemma norm_term_of_rh (hRH : RiemannHypothesis) (x : ℝ) (q : ZIdx) :
    ‖Complex.exp ((zetaZeroFamily q - 1 / 2) * Real.log x) / (zetaZeroFamily q * (1 - zetaZeroFamily q))‖ =
      ‖1 / (zetaZeroFamily q * (1 - zetaZeroFamily q))‖ := by
  rw [norm_div, norm_div, norm_one, zZF_sub_half hRH q, Complex.norm_exp]
  simp

/-- Under RH, `K_H(1) = Σ_ρ |1/(ρ(1 − ρ))|`: each `ρ(1 − ρ) = ¼ + γ²` is positive. -/
lemma kerH_one_of_rh (hRH : RiemannHypothesis) :
    kerH 1 = ((∑' q : ZIdx, ‖1 / (zetaZeroFamily q * (1 - zetaZeroFamily q))‖ : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold kerH
  refine tsum_congr fun q => ?_
  set t : ℝ := (zetaZeroFamily q).im
  have hρ : zetaZeroFamily q = 1 / 2 + Complex.I * t := by linear_combination zZF_sub_half hRH q
  have hp : zetaZeroFamily q * (1 - zetaZeroFamily q) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    rw [hρ]; push_cast; linear_combination (-(t : ℂ) ^ 2) * Complex.I_sq
  have hpos : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  rw [Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, hp, ← Complex.ofReal_one,
    ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **Under RH, `‖K_H(x)‖ ≤ ‖K_H(1)‖`** for every real `x`. -/
theorem norm_kerH_le_of_rh (hRH : RiemannHypothesis) (x : ℝ) : ‖kerH x‖ ≤ ‖kerH 1‖ := by
  rw [kerH_one_of_rh hRH, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun q => norm_nonneg _)]
  unfold kerH
  refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
  · exact summable_hw.congr fun q => (norm_term_of_rh hRH x q).symm
  · exact tsum_congr fun q => norm_term_of_rh hRH x q

/-- **Von Koch's bound for the ramp, under RH**: for `x ≥ 1`,
`|Σ_{n ≤ x} Λ(n)(x/n − 1) − x log x + (1 + γ)x| ≤ (‖K_H(1)‖ + B)√x`. -/
theorem abs_zetaRamp_le_of_rh (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |WindowGRH.zetaFamily.G x| ≤ (‖kerH 1‖ + bridgeB) * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hr : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
  have h := norm_sub_le (kerH x) (kerH x - ((x ^ (-(1 / 2 : ℝ)) * WindowGRH.zetaFamily.G x : ℝ) : ℂ))
  rw [sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs, hr, abs_mul, abs_inv, abs_of_pos hs0] at h
  have h2 := abs_kerH_sub_ramp_le hx
  have h3 := norm_kerH_le_of_rh hRH x
  rw [hr] at h2
  have h4 : (Real.sqrt x)⁻¹ * |WindowGRH.zetaFamily.G x| ≤ ‖kerH 1‖ + bridgeB := by linarith
  rw [inv_mul_le_iff₀ hs0] at h4
  linarith

end BallWindow

namespace WindowGRH

open BallWindow DirichletCharacter

/-- **RH is the frontier for `ζ` alone**: Mathlib's `RiemannHypothesis` holds if and only if
`WindowGRH.ZetaWindowBound`. Under RH the ball kernel bounds the ramp error (`BallWindow.abs_zetaRamp_le_of_rh`). -/
theorem rh_iff_zetaWindowBound : RiemannHypothesis ↔ ZetaWindowBound := by
  refine ⟨fun hRH θ hθ => ?_, riemannHypothesis_of_zetaWindowBound⟩
  refine ⟨2, one_lt_two, ‖BallHadamard.kerH 1‖ + bridgeB, fun Y₀ => ⟨max Y₀ 1, le_max_left _ _, fun x hx => ?_⟩⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx.1
  rw [← zetaFamily_G]
  have h := (le_abs_self _).trans (abs_zetaRamp_le_of_rh hRH hx1)
  have hC : 0 ≤ ‖BallHadamard.kerH 1‖ + bridgeB := add_nonneg (norm_nonneg _) bridgeB_nonneg
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hC)
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hx1 hθ.le

/-! ## The mirror sign -/

/-- **The mirror frontier for `ζ`**: for every `θ > 1/2`, on windows `[Y, Y^λ]` with `Y` arbitrarily large,
`Σ_{n ≤ x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≥ −C x^θ`, for some `λ > 1` and `C`. -/
def ZetaWindowLowerBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → ∃ lam : ℝ, 1 < lam ∧ ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Icc Y (Y ^ lam),
    -(C * x ^ θ) ≤
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

/-- At a real point of `ζ`'s set of poles there is nothing: `ζ` has no zero in `(0, 1)`. -/
theorem zetaFamily_Z_im_ne_zero {ρ : ℂ} (hρ : ρ ∈ zetaFamily.Z) : ρ.im ≠ 0 := by
  intro him
  have hre1 := zetaFamily.re_lt_one ρ hρ
  obtain ⟨hre0, i, hi⟩ := hρ
  have hc : (starRingEnd ℂ) ρ = ρ := Complex.conj_eq_iff_im.2 him
  rw [hc, or_self] at hi
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hre1; exact lt_irrefl _ hre1
  have hL : LFunction (1 : DirichletCharacter ℂ 1) ρ = 0 :=
    (LFunction_eq_zero_iff_entire (zetaFamily.χ i) (zetaFamily.adm i) (Or.inr hρ1)).2 hi
  rw [LFunction_modOne_eq] at hL
  have hρr : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hρr] at hL
  exact WeilForm.riemannZeta_ne_zero_of_mem_Ioo hre0 hre1 hL

/-- Landau's hypotheses for `−G`, the error of `ζ` with the opposite sign, and the opposite transform. -/
theorem zetaFamily_neg_poleData :
    LandauWindow.PoleData (fun u => -zetaFamily.G (Real.exp u)) (fun s => -zetaFamily.Φ s) zetaFamily.Z 3 where
  measurable := (zetaFamily.measurable_G.comp Real.measurable_exp).neg
  growth := by
    obtain ⟨C, hC⟩ := zetaFamily.growth
    exact ⟨C, fun u hu => by rw [abs_neg]; exact hC u hu⟩
  laplace_eq := fun s hs => by
    rw [zetaFamily.laplace_eq hs]
    unfold LandauWindow.laplace
    rw [← integral_neg]
    congr 1
    funext u
    push_cast
    ring
  re_lt_one := zetaFamily.re_lt_one
  isolated := zetaFamily.isolated
  differentiableAt := fun s hs hsZ => (zetaFamily.differentiableAt_Φ s hs hsZ).neg
  pole := fun ρ hρ => by
    obtain ⟨c, hc0, -, h, hh, hev⟩ := zetaFamily.pole ρ hρ
    refine ⟨-c, neg_ne_zero.2 hc0, fun him => absurd him (zetaFamily_Z_im_ne_zero hρ), fun s => -h s, hh.neg, ?_⟩
    filter_upwards [hev] with s hs
    rw [hs]
    ring

/-- **The Riemann hypothesis from the mirror frontier**: a lower bound `G(x) ≥ −Cx^θ` on windows, for every
`θ > 1/2`, gives RH, through Landau's theorem on windows for `−G`. -/
theorem riemannHypothesis_of_zetaWindowLowerBound (h : ZetaWindowLowerBound) : RiemannHypothesis := by
  refine HalfPlaneGRH.riemannHypothesis_of_zeta_ne_zero fun s hs => ?_
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero
  set θ := (1 / 2 + s.re) / 2 with hθdef
  obtain ⟨lam, hlam, C, hW⟩ := h θ (by linarith)
  have hθ0 : 0 < θ := by linarith
  have hθs : θ < s.re := by linarith
  have hW' : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U (lam * U), -zetaFamily.G (Real.exp u) ≤ C * Real.exp (θ * u) := by
    intro U₀
    obtain ⟨Y, hY, hYW⟩ := hW (Real.exp U₀)
    have hY0 : 0 < Y := (Real.exp_pos U₀).trans_le hY
    refine ⟨Real.log Y, (Real.le_log_iff_exp_le hY0).2 hY, fun u hu => ?_⟩
    have hx := hYW (Real.exp u) ⟨?_, ?_⟩
    · rw [← zetaFamily_G, ← Real.exp_mul, mul_comm u θ] at hx
      linarith
    · rw [← Real.exp_log hY0]; exact Real.exp_le_exp.2 hu.1
    · rw [Real.rpow_def_of_pos hY0]; exact Real.exp_le_exp.2 (by linarith [hu.2])
  intro hz
  have hL : LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
    rw [LFunction_modOne_eq]; exact hz
  have : NeZero (zetaFamily.N ()) := zetaFamily.neZero ()
  have hsZ : s ∈ zetaFamily.Z := ⟨hθ0.trans hθs, (), Or.inl
    ((LFunction_eq_zero_iff_entire (zetaFamily.χ ()) (zetaFamily.adm ()) (Or.inr hs1)).1 hL)⟩
  exact absurd (LandauWindow.re_le_of_windows zetaFamily_neg_poleData hθ0 hlam hW' s hsZ) (not_le.2 hθs)

/-- **RH is the mirror frontier for `ζ`**: Mathlib's `RiemannHypothesis` holds if and only if
`ZetaWindowLowerBound`; one half of von Koch's bound for the ramp suffices, either half. -/
theorem rh_iff_zetaWindowLowerBound : RiemannHypothesis ↔ ZetaWindowLowerBound := by
  refine ⟨fun hRH θ hθ => ?_, riemannHypothesis_of_zetaWindowLowerBound⟩
  refine ⟨2, one_lt_two, ‖BallHadamard.kerH 1‖ + bridgeB, fun Y₀ => ⟨max Y₀ 1, le_max_left _ _, fun x hx => ?_⟩⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx.1
  rw [← zetaFamily_G]
  have h := abs_zetaRamp_le_of_rh hRH hx1
  have hC : 0 ≤ ‖BallHadamard.kerH 1‖ + bridgeB := add_nonneg (norm_nonneg _) bridgeB_nonneg
  have h2 : Real.sqrt x ≤ x ^ θ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 hθ.le
  have h3 := mul_le_mul_of_nonneg_left h2 hC
  have h4 := neg_abs_le (zetaFamily.G x)
  linarith

end WindowGRH

#print axioms BallWindow.kappa_eq
#print axioms BallWindow.kappa_eq_digamma
#print axioms BallWindow.archH_add_cosh_le
#print axioms BallWindow.kerHψ_sub_ramp
#print axioms BallWindow.abs_kerHψ_sub_ramp_le
#print axioms BallWindow.abs_kerH_sub_ramp_le
#print axioms BallWindow.norm_kerH_le_of_rh
#print axioms BallWindow.abs_zetaRamp_le_of_rh
#print axioms WindowGRH.rh_iff_zetaWindowBound
#print axioms WindowGRH.riemannHypothesis_of_zetaWindowLowerBound
#print axioms WindowGRH.rh_iff_zetaWindowLowerBound
