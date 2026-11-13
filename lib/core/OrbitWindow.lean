import Mathlib
import ParityGap
import ArchShift
import ExplicitBridge
import GroundStateExists
import StripShift
import WeilZeta
import PivotSharp

/-! # The orbit form is Weil's form on a window: the step functions of the orbit

Plain statement. Let `Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn)·K_H(m/n)` be the orbit form (`BallWeil.form`), and let
`g_x(t) = e^{t/2}·Σ_{n ≤ N} x_n 1_{(0, log n]}(t)` (`stepProbe`), in `u = e^t` the function `u^{1/2}Σ_n x_n 1_{(1, n]}(u)`.
**On the hyperplane `Σ_n x_n = 0`, `Q_N(x)` is Weil's form of `g_x`** (`form_eq_weilQg`, no RH input): the library's
`weilQg`, with its pole, archimedean and prime terms, on the window `[−log N, log N]`. On the hyperplane `g_x` is
`u^{1/2}Σ_n x_n 1_{(0, n]}(u)`, supported in `[1, N]`; after the dilation `u ↦ u/√N` it lies in the window
`[λ⁻¹, λ]` with `λ = √N`, the windows of A. Connes and his collaborators, and its form involves the prime powers up to
`N` only. The integer vectors `x` are the integer-valued step functions `y = Σ_n x_n 1_{(0, n]}`.

So two results on the orbit translate into statements about Weil's form on the window, under RH:
* `weilQg_step_int_ge`: `Q(u^{1/2}y) ≥ (999/1000)(2/45)(13/10) = 0.0577` for every nonzero integer-valued `y`, constant
  on the unit intervals of `[1, N]` (from `PivotSharp.lattice_gap`);
* `weilQg_step_ge`: `Q(g_x) ≥ (√log N/(220e⁸N³))‖g_x‖²` on the hyperplane, in the norm of `L²(d*u)` (from
  `BallGap.rate_gap` and `‖g_x‖² ≤ N²Σx_n²`, `normSq_stepProbe_le`).

On the whole window the least eigenvalue of Weil's form is of order `e^{−4πλ²}` (R. Andrews, A. Connes and A. La Gatta,
arXiv:2611.13129, numerically, with the upper bound of Connes and Kastoris): the step functions of the orbit stay
polynomially far from its nearly null directions.

The proof.
- **The explicit formula for any parity** (`weilQg_hasSum`). `weilQg` is defined for real probes of either parity, with
  pole term `2ĝ(i/2)ĝ(−i/2)`. Weil's explicit formula for `h(z) = ĝ(z)ĝ(−z)`, which is `|ĝ|²` on `ℝ`, gives
  `Σ_ρ ĝ(t_ρ)ĝ(−t_ρ) = weilQg a g`. Its archimedean term is `arch_term_gen`: Gauss's digamma integral and Tonelli, as in
  `ArchShift`, with `|ĝ|²` and the parity-free Fourier inversion of `ParityGap` in place of `ĝ²`.
- **The step function is a probe** (`stepProbe_sprobe`). The autocorrelation of each atom `e^{t/2}1_{(0, L]}` is
  `e^{L − u/2} − e^{u/2}` on `[0, L]` (`autocorr_stepAtom`), Lipschitz at `0`, so `f(0) − f(u) ≤ B·u` for `g_x` too
  (`stepProbe_lip`), through `‖g − g(· + u)‖² = 2(f(0) − f(u))` and Cauchy–Schwarz over the atoms.
- **Its transform** (`ghatC_stepProbe`) is `Σ_n x_n ∫_0^{log n} e^{(1/2 + iz)u} du`, which decays like
  `1/(1 + |Re z|)` on the strip `|Im z| ≤ 1` (`norm_expInt_le`): so `h` is a `StripTest`, and `weilExplicit_zeta`
  applies (`weil_hStep`).
- **The zero side, term by term** (`hStep_zero`). At `t = (ρ − ½)/i`, `½ + it = ρ`, and on `Σ x_n = 0` the transform
  is `(Σ_n x_n n^ρ)/ρ`, so `ĝ_x(t)ĝ_x(−t) = Σ_{m,n} x_m x_n √(mn)(m/n)^{ρ − ½}/(ρ(1 − ρ))`. Summed over the zeros this
  is `Σ_{m,n} x_m x_n √(mn)K_H(m/n)` (`hasSum_kerH_term`), and `K_H = kψ` (`BallWeil.kerH_eq_kψ`) gives `Q_N(x)`.
-/

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace OrbitWindow

open WeilForm WeilTest

variable {a : ℝ} {g : ℝ → ℝ}

/-! ## A. The archimedean identity for a probe of either parity -/

/-- `|ĝ|²` on `ℝ` is integrable, for every real `L²` function on `[−a, a]`. -/
theorem integrable_gN (hp : RSupp a g) (ha : 0 < a) : Integrable (gN g a) := by
  have h := (integrable_PhiG hp ha).comp_div (show (2 * π) ≠ 0 by positivity)
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only [PhiG]
  congr 1
  field_simp

/-- `∫ |ĝ(r)|² cos(ru) dr = 2π f(u)`, `f` the autocorrelation, for any parity. -/
theorem integral_gN_cos (hp : RSupp a g) (ha : 0 < a) (u : ℝ) :
    ∫ r, gN g a r * Real.cos (r * u) = 2 * π * autocorr g u := by
  have e : (fun r => gN g a r * Real.cos (r * u))
      = fun r => (fun v => PhiG g a v * Real.cos (2 * π * v * u)) (r / (2 * π)) := by
    funext r
    simp only [PhiG]
    have h1 : 2 * π * (r / (2 * π)) = r := by field_simp
    rw [h1]
  calc ∫ r, gN g a r * Real.cos (r * u)
      = ∫ r, (fun v => PhiG g a v * Real.cos (2 * π * v * u)) (r / (2 * π)) := by rw [e]
    _ = |2 * π| • ∫ v, PhiG g a v * Real.cos (2 * π * v * u) :=
        Measure.integral_comp_div (fun v => PhiG g a v * Real.cos (2 * π * v * u)) (2 * π)
    _ = 2 * π * autocorr g u := by
        rw [← autocorr_eq_inv_gen hp ha, smul_eq_mul, abs_of_pos (by positivity)]

theorem integral_gN (hp : RSupp a g) (ha : 0 < a) : ∫ r, gN g a r = 2 * π * autocorr g 0 := by
  have h := integral_gN_cos hp ha 0
  simpa using h

theorem integrable_gN_cos (hp : RSupp a g) (ha : 0 < a) (u : ℝ) :
    Integrable (fun r => gN g a r * Real.cos (r * u)) :=
  (integrable_gN hp ha).mul_bdd (c := 1)
    (by fun_prop : Continuous fun r : ℝ => Real.cos (r * u)).aestronglyMeasurable
    (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- The archimedean condition at `q = ¼` makes `φ_A` integrable, for any parity. -/
theorem phiA_integrable (hp : SProbe a g) : IntegrableOn (phiAQ (1 / 4) g) (Ioi 0) := by
  have harch : IntegrableOn (archIntegrandQ (1 / 4) g) (Ioi 0) := by
    rw [archIntegrandQ_quarter]; exact hp.arch
  have h : IntegrableOn (fun u => phiAQ (1 / 4) g (2 * u)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (harch.div_const 2) (fun u hu => ?_) measurableSet_Ioi
    rw [← phiAQ_two_mul (1 / 4) g hu]; ring
  simpa using (integrableOn_Ioi_comp_mul_left_iff (phiAQ (1 / 4) g) 0 (by norm_num : (0 : ℝ) < 2)).1 h

/-- **Tonelli, any parity**: `∫ |ĝ(r)|²(Re ψ(¼ + ir/2) − Re ψ(¼)) dr = 2π·E(g)`. -/
theorem gN_psi_sub (hp : SProbe a g) (ha : 0 < a) :
    Integrable (fun r => gN g a r * (psiRe r - psiRe 0)) ∧
      ∫ r, gN g a r * (psiRe r - psiRe 0) = 2 * π * archE g := by
  have hR : RSupp a g := ⟨hp.supp, hp.memL2⟩
  have hq0 : (0 : ℝ) < 1 / 4 := by norm_num
  set ν := volume.restrict (Ioi (0 : ℝ))
  set F : ℝ × ℝ → ℝ := fun p => gN g a p.1 * (kkQ (1 / 4) p.2 * (1 - Real.cos (p.1 * (p.2 / 2))))
    with hFd
  have hFm : AEStronglyMeasurable F (volume.prod ν) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((continuous_gN hR).measurable.comp measurable_fst).mul
      (((measurable_kkQ (1 / 4)).comp measurable_snd).mul ?_)
    exact (Continuous.measurable (by fun_prop))
  have e : ∀ t, (fun r => F (r, t))
      = fun r => kkQ (1 / 4) t * (gN g a r - gN g a r * Real.cos (r * (t / 2))) := by
    intro t; funext r; simp only [hFd]; ring
  have hinner : ∀ t, ∫ r, F (r, t) = 2 * π * phiAQ (1 / 4) g t := by
    intro t
    rw [e, integral_const_mul, integral_sub (integrable_gN hR ha) (integrable_gN_cos hR ha _),
      integral_gN hR ha, integral_gN_cos hR ha, phiAQ]
    ring
  have hFint : ∀ t, Integrable (fun r => F (r, t)) := by
    intro t
    rw [e]; exact ((integrable_gN hR ha).sub (integrable_gN_cos hR ha _)).const_mul _
  have hFnn : ∀ r, ∀ t, 0 < t → 0 ≤ F (r, t) := fun r t ht =>
    mul_nonneg (gN_nonneg r)
      (mul_nonneg (kkQ_nonneg (1 / 4) ht) (by linarith [Real.cos_le_one (r * (t / 2))]))
  have hF : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Eventually.of_forall hFint, ?_⟩
    refine ((phiA_integrable hp).const_mul (2 * π)).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    show 2 * π * phiAQ (1 / 4) g t = ∫ r, ‖F (r, t)‖
    rw [← hinner t]
    congr 1; funext r
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn r t ht)]
  have hG : ∀ r, ∫ t, F (r, t) ∂ν = gN g a r * (psiRe r - psiRe 0) := by
    intro r
    simp only [hFd, ν]
    rw [integral_const_mul, ← (psiReQ_sub hq0 r).2, psiReQ_quarter]
  have hGi := hF.integral_prod_left
  simp only [hG] at hGi
  refine ⟨hGi, ?_⟩
  calc ∫ r, gN g a r * (psiRe r - psiRe 0) = ∫ r, ∫ t, F (r, t) ∂ν := by simp only [hG]
    _ = ∫ t, (∫ r, F (r, t)) ∂ν := integral_integral_swap (f := fun r t => F (r, t)) hF
    _ = ∫ t in Ioi (0 : ℝ), 2 * π * phiAQ (1 / 4) g t := by simp only [hinner, ν]
    _ = 2 * π * archE g := by rw [integral_const_mul, phiAQ_integral, archEQ_quarter]

/-- **The archimedean term, any parity**: `(1/2π)∫|ĝ|² Re ψ(¼ + ir/2) = Re ψ(¼)‖g‖² + E(g)`. -/
theorem arch_term_gen (hp : SProbe a g) (ha : 0 < a) :
    1 / (2 * π) * ∫ r, gN g a r * psiRe r = psiRe 0 * normSq g + archE g := by
  have hR : RSupp a g := ⟨hp.supp, hp.memL2⟩
  obtain ⟨hi, he⟩ := gN_psi_sub hp ha
  have e : (fun r => gN g a r * psiRe r)
      = fun r => gN g a r * (psiRe r - psiRe 0) + psiRe 0 * gN g a r := by
    funext r; ring
  rw [e, integral_add hi ((integrable_gN hR ha).const_mul _), he, integral_const_mul,
    integral_gN hR ha, autocorr_zero]
  field_simp
  ring

/-- **The explicit-formula bridge, any parity**: Weil's explicit formula for `h(z) = ĝ(z)ĝ(−z)` gives
`Σ_ρ ĝ(t_ρ)ĝ(−t_ρ) = Q(g)`, the library's form `weilQg` with pole term `2ĝ(i/2)ĝ(−i/2)`. -/
theorem weilQg_hasSum {ι : Type*} {ρ : ι → ℂ} (hp : SProbe a g) (ha : 0 < a)
    (hEF : WeilExplicit ρ (fun z => ghatC g a z * ghatC g a (-z)) (gN g a)) :
    HasSum (fun i => ghatC g a ((ρ i - 1 / 2) / Complex.I) * ghatC g a (-((ρ i - 1 / 2) / Complex.I)))
      (weilQg a g : ℂ) := by
  have hR : RSupp a g := ⟨hp.supp, hp.memL2⟩
  obtain ⟨-, hS⟩ := hEF
  convert hS using 1
  have hgh : ∀ u, gh (gN g a) u = autocorr g u := by
    intro u; unfold gh; rw [integral_gN_cos hR ha]; field_simp
  have hpr : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh (gN g a) (Real.log n)
      = primeS g := by
    unfold primeS; congr 1; funext n; rw [hgh]
  have hz0 : psiRe 0 = (Complex.digamma (1 / 4)).re := by unfold psiRe zB; simp
  simp only [neg_neg]
  rw [ghatC_I_div_two, ghatC_neg_I_div_two, hgh 0, autocorr_zero, hpr, arch_term_gen hp ha, hz0,
    weilQg, weilConst]
  push_cast
  ring


/-! ## B. The orbit's step function -/

/-- The atom `e^{t/2}·1_{(0, L]}(t)`. -/
def stepAtom (L t : ℝ) : ℝ := Set.indicator (Ioc 0 L) (fun t => Real.exp (t / 2)) t

/-- **The orbit's step function** `g_x(t) = e^{t/2}·Σ_{n ≤ N} x_n 1_{(0, log n]}(t)`. In `u = e^t` it is
`u^{1/2}Σ_n x_n 1_{(1, n]}(u)`, supported in `[1, N]`. -/
def stepProbe (N : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 N, x n * stepAtom (Real.log n) t

theorem stepAtom_nonneg (L t : ℝ) : 0 ≤ stepAtom L t :=
  Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) t

theorem stepAtom_of_notMem {L t : ℝ} (ht : t ∉ Ioc 0 L) : stepAtom L t = 0 :=
  Set.indicator_of_notMem ht _

theorem stepAtom_memLp (L : ℝ) : MemLp (stepAtom L) 2 volume :=
  memLp_indicator_of_continuous (by fun_prop) measurableSet_Ioc measure_Ioc_lt_top.ne
    (C := Real.exp (|L| / 2)) fun t ht => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (by have := ht.2; have := le_abs_self L; linarith)

theorem stepProbe_memLp (N : ℕ) (x : ℕ → ℝ) : MemLp (stepProbe N x) 2 volume := by
  have e : stepProbe N x = ∑ n ∈ Finset.Icc 1 N, fun t => x n * stepAtom (Real.log n) t := by
    funext t; simp [stepProbe, Finset.sum_apply]
  rw [e]
  exact memLp_finsetSum' _ fun n _ => (stepAtom_memLp _).const_mul (x n)

theorem stepProbe_supp {N : ℕ} (x : ℕ → ℝ) {t : ℝ} (ht : Real.log N < |t|) : stepProbe N x t = 0 := by
  unfold stepProbe
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.1 hn).2
  have hlog : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)
  rw [stepAtom_of_notMem, mul_zero]
  intro h
  rw [abs_of_pos h.1] at ht
  linarith [h.2]

/-- For `u ≥ 0`, `φ_L(t)φ_L(t + u) = e^{t + u/2}` on `(0, L − u]`, and `0` elsewhere. -/
theorem stepAtom_mul_shift {L u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    stepAtom L t * stepAtom L (t + u) = Set.indicator (Ioc 0 (L - u)) (fun t => Real.exp (t + u / 2)) t := by
  by_cases h : t ∈ Ioc 0 (L - u)
  · rw [Set.indicator_of_mem h]
    have h1 : t ∈ Ioc 0 L := ⟨h.1, by linarith [h.2]⟩
    have h2 : t + u ∈ Ioc 0 L := ⟨by linarith [h.1], by linarith [h.2]⟩
    unfold stepAtom
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, ← Real.exp_add]
    congr 1; ring
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at h
    rcases h with h | h
    · rw [stepAtom_of_notMem (L := L) (t := t) (fun hm => by linarith [hm.1]), zero_mul]
    · rw [stepAtom_of_notMem (L := L) (t := t + u) (fun hm => by linarith [hm.2]), mul_zero]

/-- The atom's autocorrelation: `f(u) = e^{L − u/2} − e^{u/2}` for `0 ≤ u ≤ L`. -/
theorem autocorr_stepAtom {L u : ℝ} (hu : 0 ≤ u) (huL : u ≤ L) :
    autocorr (stepAtom L) u = Real.exp (L - u / 2) - Real.exp (u / 2) := by
  unfold autocorr
  simp_rw [stepAtom_mul_shift hu]
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_add_right (fun t => Real.exp t), integral_exp]
  congr 1 <;> congr 1 <;> ring

theorem autocorr_stepAtom_nonneg (L u : ℝ) : 0 ≤ autocorr (stepAtom L) u :=
  integral_nonneg fun _ => mul_nonneg (stepAtom_nonneg _ _) (stepAtom_nonneg _ _)

theorem autocorr_stepAtom_ge {L u : ℝ} (hu : 0 ≤ u) :
    Real.exp (L - u / 2) - Real.exp (u / 2) ≤ autocorr (stepAtom L) u := by
  rcases le_or_gt u L with h | h
  · rw [autocorr_stepAtom hu h]
  · have h1 : Real.exp (L - u / 2) ≤ Real.exp (u / 2) := Real.exp_le_exp.2 (by linarith)
    linarith [autocorr_stepAtom_nonneg L u]

/-- **The atom's autocorrelation is Lipschitz at `0`**: `f(0) − f(u) ≤ (e^L + 1)u` for `u > 0`. -/
theorem autocorr_stepAtom_lip {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    autocorr (stepAtom L) 0 - autocorr (stepAtom L) u ≤ (Real.exp L + 1) * u := by
  have h0 : autocorr (stepAtom L) 0 = Real.exp L - 1 := by
    rw [autocorr_stepAtom le_rfl hL]; simp
  rw [h0]
  have hEL := Real.exp_pos L
  rcases le_or_gt u 1 with h1 | h1
  · have hlow := autocorr_stepAtom_ge (L := L) hu.le
    have e1 : Real.exp (L - u / 2) = Real.exp L * Real.exp (-(u / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have hA : 1 - u / 2 ≤ Real.exp (-(u / 2)) := by linarith [Real.add_one_le_exp (-(u / 2))]
    have hB : Real.exp (u / 2) ≤ 1 + u := by
      have h := Real.abs_exp_sub_one_sub_id_le (x := u / 2) (by rw [abs_of_pos (by linarith)]; linarith)
      have h' := (abs_le.1 h).2
      nlinarith
    have hC : Real.exp L * (1 - u / 2) ≤ Real.exp L * Real.exp (-(u / 2)) :=
      mul_le_mul_of_nonneg_left hA hEL.le
    rw [e1] at hlow
    nlinarith
  · have h2 := autocorr_stepAtom_nonneg L u
    nlinarith

/-- `‖Σ_{i ∈ s} c_i d_i‖² ≤ #s·Σ_{i ∈ s} c_i²‖d_i‖²`. -/
theorem normSq_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (d : ι → ℝ → ℝ)
    (hd : ∀ i ∈ s, MemLp (d i) 2 volume) :
    WeilForm.normSq (fun t => ∑ i ∈ s, c i * d i t) ≤ s.card * ∑ i ∈ s, c i ^ 2 * WeilForm.normSq (d i) := by
  unfold WeilForm.normSq
  have hsum : MemLp (fun t => ∑ i ∈ s, c i * d i t) 2 volume := by
    have e : (fun t => ∑ i ∈ s, c i * d i t) = ∑ i ∈ s, fun t => c i * d i t := by
      funext t; simp [Finset.sum_apply]
    rw [e]; exact memLp_finsetSum' _ fun i hi => (hd i hi).const_mul (c i)
  have hI : ∀ i ∈ s, Integrable (fun t => (c i * d i t) ^ 2) := fun i hi => by
    have := ((hd i hi).integrable_sq).const_mul (c i ^ 2)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only; ring
  calc ∫ t, (∑ i ∈ s, c i * d i t) ^ 2 ≤ ∫ t, (s.card : ℝ) * ∑ i ∈ s, (c i * d i t) ^ 2 :=
        integral_mono hsum.integrable_sq ((integrable_finsetSum _ hI).const_mul _)
          fun t => sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ i ∈ s, c i ^ 2 * ∫ t, d i t ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ hI]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← integral_const_mul]
        congr 1; funext t; ring

/-- **The step function's autocorrelation is Lipschitz at `0`**: `f(0) − f(u) ≤ B·u`. -/
theorem stepProbe_lip (N : ℕ) (x : ℕ → ℝ) {u : ℝ} (hu : 0 < u) :
    autocorr (stepProbe N x) 0 - autocorr (stepProbe N x) u
      ≤ (N * ∑ n ∈ Finset.Icc 1 N, x n ^ 2 * ((n : ℝ) + 1)) * u := by
  have hg := stepProbe_memLp N x
  have h2 := normSq_sub_shift hg u
  have e : (fun t => stepProbe N x t - stepProbe N x (t + u))
      = fun t => ∑ n ∈ Finset.Icc 1 N,
          x n * (stepAtom (Real.log n) t - stepAtom (Real.log n) (t + u)) := by
    funext t; unfold stepProbe; rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_; ring
  have hle := normSq_sum_le (Finset.Icc 1 N) x
    (fun n t => stepAtom (Real.log n) t - stepAtom (Real.log n) (t + u))
    (fun n _ => (stepAtom_memLp _).sub (memLp_shift (stepAtom_memLp _) u))
  rw [← e, h2] at hle
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      x n ^ 2 * WeilForm.normSq (fun t => stepAtom (Real.log n) t - stepAtom (Real.log n) (t + u))
        ≤ x n ^ 2 * (2 * (((n : ℝ) + 1) * u)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    rw [normSq_sub_shift (stepAtom_memLp _) u]
    have hlip := autocorr_stepAtom_lip (Real.log_nonneg hn1) hu
    rw [Real.exp_log (by linarith)] at hlip
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have hsum := Finset.sum_le_sum hterm
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  rw [hcard] at hle
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e2 : ∑ n ∈ Finset.Icc 1 N, x n ^ 2 * (2 * (((n : ℝ) + 1) * u))
      = 2 * (∑ n ∈ Finset.Icc 1 N, x n ^ 2 * ((n : ℝ) + 1)) * u := by
    rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun n _ => ?_; ring
  rw [e2] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hsum hN]

/-- **The step function is a probe** (of no parity) on the window `[−log N, log N]`. -/
theorem stepProbe_sprobe (N : ℕ) (x : ℕ → ℝ) : SProbe (Real.log N) (stepProbe N x) :=
  ⟨fun _ ht => stepProbe_supp x ht, stepProbe_memLp N x,
    archIntegrand_integrableOn_of_lin (stepProbe_memLp N x) (by positivity) fun _ hu => stepProbe_lip N x hu⟩


/-! ## C. The transform of the step function -/

/-- `∫_0^L e^{wu} du`. -/
def expInt (w : ℂ) (L : ℝ) : ℂ := ∫ u in (0 : ℝ)..L, Complex.exp (w * u)

theorem expInt_eq {w : ℂ} (hw : w ≠ 0) (L : ℝ) : expInt w L = (Complex.exp (w * L) - 1) / w := by
  unfold expInt; rw [integral_exp_mul_complex hw]; simp

/-- **The atom's transform**: `ĝ(z) = ∫_0^L e^{(1/2 + iz)u} du` on any window `[−a, a] ⊇ [0, L]`. -/
theorem ghatC_stepAtom {L a : ℝ} (hL : 0 ≤ L) (hLa : L ≤ a) (z : ℂ) :
    ghatC (stepAtom L) a z = expInt (1 / 2 + Complex.I * z) L := by
  unfold ghatC expInt
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le hL]
  have e : (fun u : ℝ => ((stepAtom L u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u))
      = Set.indicator (Ioc 0 L) (fun u : ℝ => Complex.exp ((1 / 2 + Complex.I * z) * u)) := by
    funext u
    by_cases h : u ∈ Ioc 0 L
    · rw [Set.indicator_of_mem h]
      unfold stepAtom
      rw [Set.indicator_of_mem h, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
    · rw [Set.indicator_of_notMem h, stepAtom_of_notMem h]; simp
  rw [e, setIntegral_indicator measurableSet_Ioc]
  have hs : Ioc (-a) a ∩ Ioc 0 L = Ioc 0 L := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, by linarith⟩, h1, h2⟩
  rw [hs]

/-- **The step function's transform**: `ĝ_x(z) = Σ_n x_n ∫_0^{log n} e^{(1/2 + iz)u} du`. -/
theorem ghatC_stepProbe (N : ℕ) (x : ℕ → ℝ) (z : ℂ) :
    ghatC (stepProbe N x) (Real.log N) z
      = ∑ n ∈ Finset.Icc 1 N, (x n : ℂ) * expInt (1 / 2 + Complex.I * z) (Real.log n) := by
  have hat : ∀ n ∈ Finset.Icc 1 N,
      ghatC (stepAtom (Real.log n)) (Real.log N) z = expInt (1 / 2 + Complex.I * z) (Real.log n) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    exact ghatC_stepAtom (Real.log_natCast_nonneg n)
      (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (Finset.mem_Icc.1 hn).2)) z
  have hii : ∀ n ∈ Finset.Icc 1 N, IntervalIntegrable
      (fun u : ℝ => (x n : ℂ) * (((stepAtom (Real.log n) u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)))
      volume (-Real.log N) (Real.log N) := by
    intro n _
    refine IntervalIntegrable.const_mul ?_ _
    have h := memLp_intervalIntegrable (stepAtom_memLp (Real.log n)) (-Real.log N) (Real.log N)
    have hc : IntervalIntegrable (fun u : ℝ => ((stepAtom (Real.log n) u : ℝ) : ℂ)) volume
        (-Real.log N) (Real.log N) := ⟨h.1.ofReal, h.2.ofReal⟩
    exact hc.mul_continuousOn (by fun_prop)
  unfold ghatC stepProbe
  have e : (fun u : ℝ => (((∑ n ∈ Finset.Icc 1 N, x n * stepAtom (Real.log n) u : ℝ)) : ℂ)
      * Complex.exp (Complex.I * z * u))
      = fun u => ∑ n ∈ Finset.Icc 1 N,
          (x n : ℂ) * (((stepAtom (Real.log n) u : ℝ) : ℂ) * Complex.exp (Complex.I * z * u)) := by
    funext u; push_cast; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun n _ => ?_; ring
  rw [e, intervalIntegral.integral_finsetSum hii]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [intervalIntegral.integral_const_mul, ← hat n hn]
  rfl

/-- `|∫_0^L e^{wu} du| ≤ L e^{3L/2}` when `Re w ≤ 3/2`. -/
theorem norm_expInt_le_of_re {w : ℂ} {L : ℝ} (hL : 0 ≤ L) (hw : w.re ≤ 3 / 2) :
    ‖expInt w L‖ ≤ L * Real.exp (3 / 2 * L) := by
  unfold expInt
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L)
    (C := Real.exp (3 / 2 * L)) (f := fun u : ℝ => Complex.exp (w * u)) ?_
  · rwa [sub_zero, abs_of_nonneg hL, mul_comm] at h
  · intro u hu
    rw [Set.uIoc_of_le hL] at hu
    rw [Complex.norm_exp]
    have e : (w * (u : ℂ)).re = w.re * u := by simp [Complex.mul_re]
    rw [e]
    exact Real.exp_le_exp.2 (by nlinarith [hu.1, hu.2])

/-- `|∫_0^L e^{wu} du| ≤ (e^{3L/2} + 1)/|Im w|` when `Re w ≤ 3/2` and `Im w ≠ 0`. -/
theorem norm_expInt_le_of_im {w : ℂ} {L : ℝ} (hL : 0 ≤ L) (hw : w.re ≤ 3 / 2) (him : w.im ≠ 0) :
    ‖expInt w L‖ ≤ (Real.exp (3 / 2 * L) + 1) / |w.im| := by
  have hw0 : w ≠ 0 := fun h => him (by rw [h]; simp)
  rw [expInt_eq hw0, norm_div]
  have h1 : ‖Complex.exp (w * L) - 1‖ ≤ Real.exp (3 / 2 * L) + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp, norm_one]
    have e : (w * (L : ℂ)).re = w.re * L := by simp [Complex.mul_re]
    rw [e]
    have : Real.exp (w.re * L) ≤ Real.exp (3 / 2 * L) := Real.exp_le_exp.2 (by nlinarith)
    linarith
  have h2 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h3 : 0 < |w.im| := abs_pos.2 him
  calc ‖Complex.exp (w * L) - 1‖ / ‖w‖ ≤ (Real.exp (3 / 2 * L) + 1) / ‖w‖ :=
        div_le_div_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (Real.exp (3 / 2 * L) + 1) / |w.im| :=
        div_le_div_of_nonneg_left (by positivity) h3 h2

/-- **Decay on the strip**: `|∫_0^L e^{(1/2 + iz)u} du| ≤ 2(L + 2)e^{3L/2}/(1 + |Re z|)` for `Im z ≥ −1`. -/
theorem norm_expInt_le {z : ℂ} (hz : -1 ≤ z.im) {L : ℝ} (hL : 0 ≤ L) :
    ‖expInt (1 / 2 + Complex.I * z) L‖ ≤ 2 * (L + 2) * Real.exp (3 / 2 * L) / (1 + |z.re|) := by
  set w := 1 / 2 + Complex.I * z with hwd
  have hre : w.re = 1 / 2 - z.im := by simp [w]; ring
  have him : w.im = z.re := by simp [w]
  have hw : w.re ≤ 3 / 2 := by rw [hre]; linarith
  have hE1 : 1 ≤ Real.exp (3 / 2 * L) := Real.one_le_exp (by positivity)
  have hx0 := abs_nonneg z.re
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt |z.re| 1 with h | h
  · have h1 := norm_expInt_le_of_re hL hw
    have hn := norm_nonneg (expInt w L)
    nlinarith
  · have hne : w.im ≠ 0 := by
      rw [him]; intro h0; rw [h0, abs_zero] at h; linarith
    have h1 := norm_expInt_le_of_im hL hw hne
    rw [him] at h1
    have hx : 0 < |z.re| := by linarith
    rw [le_div_iff₀ hx] at h1
    have hn := norm_nonneg (expInt w L)
    nlinarith

/-- The constant of the strip bound. -/
def stepConst (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, |x n| * (2 * (Real.log n + 2) * Real.exp (3 / 2 * Real.log n))

theorem stepConst_nonneg (N : ℕ) (x : ℕ → ℝ) : 0 ≤ stepConst N x := by
  unfold stepConst
  refine Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) ?_
  have := Real.log_natCast_nonneg n
  positivity

theorem norm_ghatC_stepProbe_le (N : ℕ) (x : ℕ → ℝ) {z : ℂ} (hz : -1 ≤ z.im) :
    ‖ghatC (stepProbe N x) (Real.log N) z‖ ≤ stepConst N x / (1 + |z.re|) := by
  rw [ghatC_stepProbe N x z, stepConst, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_expInt_le hz (Real.log_natCast_nonneg n)) (abs_nonneg _)

/-- `h(z) = ĝ_x(z)ĝ_x(−z)`. -/
def hStep (N : ℕ) (x : ℕ → ℝ) (z : ℂ) : ℂ :=
  ghatC (stepProbe N x) (Real.log N) z * ghatC (stepProbe N x) (Real.log N) (-z)

theorem striptest_hStep (N : ℕ) (x : ℕ → ℝ) : WeilStrip.StripTest (hStep N x) (stepConst N x ^ 2) := by
  have hd : Differentiable ℂ (ghatC (stepProbe N x) (Real.log N)) :=
    ghatC_differentiable (memLp_intervalIntegrable (stepProbe_memLp N x) _ _)
  refine ⟨?_, fun t ht => ?_⟩
  · exact (hd.mul (hd.comp differentiable_neg)).differentiableOn
  · have h1 := norm_ghatC_stepProbe_le N x (z := t) ht.1
    have h2 := norm_ghatC_stepProbe_le N x (z := -t) (by rw [Complex.neg_im]; linarith [ht.2])
    rw [Complex.neg_re, abs_neg] at h2
    have hM := stepConst_nonneg N x
    have hx := abs_nonneg t.re
    unfold hStep
    rw [norm_mul]
    calc ‖ghatC (stepProbe N x) (Real.log N) t‖ * ‖ghatC (stepProbe N x) (Real.log N) (-t)‖
        ≤ (stepConst N x / (1 + |t.re|)) * (stepConst N x / (1 + |t.re|)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = stepConst N x ^ 2 / (1 + |t.re|) ^ 2 := by rw [div_mul_div_comm, sq, sq]
      _ ≤ stepConst N x ^ 2 / (1 + t.re ^ 2) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [sq_abs t.re]

/-- **Weil's explicit formula for `h = ĝ_x(z)ĝ_x(−z)`** (`weilExplicit_zeta`, no RH input). -/
theorem weil_hStep (N : ℕ) (x : ℕ → ℝ) :
    WeilExplicit zetaZeroFamily (hStep N x) (gN (stepProbe N x) (Real.log N)) :=
  weilExplicit_zeta (striptest_hStep N x) (fun t => by unfold hStep; rw [neg_neg, mul_comm])
    (fun r => by unfold hStep; exact mul_neg_eq_gN (Real.log_natCast_nonneg N) r)


/-! ## D. The dictionary: the orbit form is Weil's form of the step function -/

theorem I_mul_t (ρ : ℂ) : Complex.I * ((ρ - 1 / 2) / Complex.I) = ρ - 1 / 2 := by
  field_simp

/-- On `Σ x_n = 0`, `Σ_n x_n ∫_0^{log n} e^{wu} du = (Σ_n x_n n^w)/w` for `w ≠ 0`. -/
theorem sum_expInt {N : ℕ} (x : ℕ → ℝ) (hx : ∑ n ∈ Finset.Icc 1 N, x n = 0) {w : ℂ} (hw : w ≠ 0) :
    ∑ n ∈ Finset.Icc 1 N, (x n : ℂ) * expInt w (Real.log n)
      = (∑ n ∈ Finset.Icc 1 N, (x n : ℂ) * Complex.exp (w * (Real.log n : ℝ))) / w := by
  have hx' : ∑ n ∈ Finset.Icc 1 N, (x n : ℂ) = 0 := by exact_mod_cast hx
  have e : ∀ n ∈ Finset.Icc 1 N, (x n : ℂ) * expInt w (Real.log n)
      = (x n : ℂ) * Complex.exp (w * (Real.log n : ℝ)) / w - (x n : ℂ) / w := by
    intro n _; rw [expInt_eq hw]; ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, hx', zero_div,
    sub_zero]

/-- `√(mn)·(m/n)^{ρ − ½} = m^ρ n^{1 − ρ}`. -/
theorem sqrt_mul_cexp {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (ρ : ℂ) :
    ((Real.sqrt ((m : ℝ) * n) : ℝ) : ℂ) * Complex.exp ((ρ - 1 / 2) * (Real.log ((m : ℝ) / n) : ℝ))
      = Complex.exp (ρ * (Real.log m : ℝ)) * Complex.exp ((1 - ρ) * (Real.log n : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← BallPsi.exp_log_half (mul_pos hm0 hn0), Real.log_mul hm0.ne' hn0.ne', Real.log_div hm0.ne' hn0.ne',
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The zero side, term by term**: at `t = (ρ − ½)/i`, `ĝ_x(t)ĝ_x(−t) = Σ_{m,n} x_m x_n √(mn)(m/n)^{ρ − ½}/(ρ(1 − ρ))`. -/
theorem hStep_zero {N : ℕ} (x : ℕ → ℝ) (hx : ∑ n ∈ Finset.Icc 1 N, x n = 0) {ρ : ℂ} (h0 : ρ ≠ 0)
    (h1 : 1 - ρ ≠ 0) :
    hStep N x ((ρ - 1 / 2) / Complex.I)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ((x m * x n * Real.sqrt ((m : ℝ) * n) : ℝ) : ℂ)
            * (Complex.exp ((ρ - 1 / 2) * (Real.log ((m : ℝ) / n) : ℝ)) / (ρ * (1 - ρ))) := by
  unfold hStep
  have e1 : 1 / 2 + Complex.I * ((ρ - 1 / 2) / Complex.I) = ρ := by rw [I_mul_t]; ring
  have e2 : 1 / 2 + Complex.I * -((ρ - 1 / 2) / Complex.I) = 1 - ρ := by rw [mul_neg, I_mul_t]; ring
  rw [ghatC_stepProbe, ghatC_stepProbe, e1, e2, sum_expInt x hx h0, sum_expInt x hx h1,
    div_mul_div_comm, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  have key := sqrt_mul_cexp (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hn).1 ρ
  rw [Complex.ofReal_mul, Complex.ofReal_mul]
  linear_combination (-((x m : ℂ) * (x n : ℂ)) / (ρ * (1 - ρ))) * key

/-- `K_H(r) = Σ_ρ r^{ρ − ½}/(ρ(1 − ρ))`, as a `HasSum`. -/
theorem hasSum_kerH_term (r : ℝ) :
    HasSum (fun q : ZIdx => Complex.exp ((zetaZeroFamily q - 1 / 2) * (Real.log r : ℝ)) /
      (zetaZeroFamily q * (1 - zetaZeroFamily q))) (BallHadamard.kerH r) := by
  have hs : Summable fun q : ZIdx => Complex.exp ((zetaZeroFamily q - 1 / 2) * (Real.log r : ℝ)) /
      (zetaZeroFamily q * (1 - zetaZeroFamily q)) := by
    refine (BallHadamard.summable_kerH (Real.log r / 2)).congr fun q => ?_
    rw [BallHadamard.hG_poleP, one_div_mul_eq_div]
    congr 2
    unfold poleP
    push_cast
    ring
  exact hs.hasSum

/-- **The dictionary** (no RH input): on the hyperplane `Σ_{n ≤ N} x_n = 0` the orbit form is Weil's form of the
step function, `Q_N(x) = Q(g_x)` with `g_x(t) = e^{t/2}Σ_n x_n 1_{(0, log n]}(t)`. In `u = e^t`, `g_x` is
`u^{1/2}Σ_n x_n 1_{(0, n]}(u)` on `[1, N]`; after the dilation `u ↦ u/√N` it lies in the window `[λ⁻¹, λ]`,
`λ = √N`, and `Q(g_x)` involves the prime powers up to `N` only. -/
theorem form_eq_weilQg {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) (hx : ∑ n ∈ Finset.Icc 1 N, x n = 0) :
    BallWeil.form N x = weilQg (Real.log N) (stepProbe N x) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < Real.log N := Real.log_pos hN1
  have hW : HasSum (fun q : ZIdx => hStep N x ((zetaZeroFamily q - 1 / 2) / Complex.I))
      (weilQg (Real.log N) (stepProbe N x) : ℂ) :=
    weilQg_hasSum (stepProbe_sprobe N x) ha (weil_hStep N x)
  have hK : HasSum (fun q : ZIdx => hStep N x ((zetaZeroFamily q - 1 / 2) / Complex.I))
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ((x m * x n * Real.sqrt ((m : ℝ) * n) : ℝ) : ℂ) * BallHadamard.kerH ((m : ℝ) / n)) := by
    have hfun : (fun q : ZIdx => hStep N x ((zetaZeroFamily q - 1 / 2) / Complex.I))
        = fun q => ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            ((x m * x n * Real.sqrt ((m : ℝ) * n) : ℝ) : ℂ)
              * (Complex.exp ((zetaZeroFamily q - 1 / 2) * (Real.log ((m : ℝ) / n) : ℝ))
                / (zetaZeroFamily q * (1 - zetaZeroFamily q))) := by
      funext q
      have hre := BallLattice.re_zero_mem q
      have h0 : zetaZeroFamily q ≠ 0 := fun h => by rw [h] at hre; simp at hre
      have h1 : 1 - zetaZeroFamily q ≠ 0 := fun h => by
        have h' : zetaZeroFamily q = 1 := by linear_combination -h
        rw [h'] at hre; simp at hre
      exact hStep_zero x hx h0 h1
    rw [hfun]
    exact hasSum_sum fun m _ => hasSum_sum fun n _ => (hasSum_kerH_term _).mul_left _
  have heq := hW.unique hK
  have hreal : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ((x m * x n * Real.sqrt ((m : ℝ) * n) : ℝ) : ℂ) * BallHadamard.kerH ((m : ℝ) / n))
      = ((BallWeil.form N x : ℝ) : ℂ) := by
    unfold BallWeil.form BallWeil.gram
    push_cast
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    rw [BallWeil.kerH_eq_kψ (div_pos hm0 hn0)]
    ring
  rw [hreal] at heq
  exact_mod_cast heq.symm

/-! ## E. Two consequences under RH -/

/-- **The integrality gap in the window**: under RH, Weil's form is at least `(999/1000)(2/45)(13/10) = 0.0577` at
every nonzero integer-valued step function `u^{1/2}y(u)`, `y` constant on the unit intervals of `[1, N]`
(`y = Σ_n k_n 1_{(0, n]}` with `Σ_n k_n = 0`), although the window's ground state is minuscule. -/
theorem weilQg_step_int_ge (hRH : RiemannHypothesis) {N : ℕ} (hN : 2 ≤ N) (k : ℕ → ℤ)
    (hk : ∑ n ∈ Finset.Icc 1 N, k n = 0) (hne : ∃ n ∈ Finset.Icc 1 N, k n ≠ 0) :
    999 / 1000 * (2 / 45) * (13 / 10) ≤ weilQg (Real.log N) (stepProbe N fun n => (k n : ℝ)) := by
  have hx : ∑ n ∈ Finset.Icc 1 N, ((k n : ℤ) : ℝ) = 0 := by exact_mod_cast hk
  rw [← form_eq_weilQg hN _ hx]
  refine PivotSharp.lattice_gap hRH k ?_
  by_contra hc
  push Not at hc
  obtain ⟨n₀, hn₀, hk₀⟩ := hne
  have hsplit : ∑ n ∈ Finset.Icc 1 N, k n = k 1 := by
    refine Finset.sum_eq_single 1 (fun b hb hb1 => hc b ?_) (fun h1 => ?_)
    · have := (Finset.mem_Icc.1 hb).1
      exact Finset.mem_Icc.2 ⟨by omega, (Finset.mem_Icc.1 hb).2⟩
    · exact absurd (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩) h1
  have hk1 : k 1 = 0 := by rw [← hsplit, hk]
  rcases (show n₀ = 1 ∨ 2 ≤ n₀ by have := (Finset.mem_Icc.1 hn₀).1; omega) with h | h
  · exact hk₀ (h ▸ hk1)
  · exact hk₀ (hc n₀ (Finset.mem_Icc.2 ⟨h, (Finset.mem_Icc.1 hn₀).2⟩))

theorem normSq_stepAtom {L : ℝ} (hL : 0 ≤ L) : WeilForm.normSq (stepAtom L) = Real.exp L - 1 := by
  rw [← autocorr_zero, autocorr_stepAtom le_rfl hL]; simp

/-- `‖g_x‖² ≤ N²Σ_n x_n²`. -/
theorem normSq_stepProbe_le (N : ℕ) (x : ℕ → ℝ) :
    WeilForm.normSq (stepProbe N x) ≤ N ^ 2 * ∑ n ∈ Finset.Icc 1 N, x n ^ 2 := by
  have h := normSq_sum_le (Finset.Icc 1 N) x (fun n => stepAtom (Real.log n)) (fun n _ => stepAtom_memLp _)
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  rw [hcard] at h
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      x n ^ 2 * WeilForm.normSq (stepAtom (Real.log n)) ≤ x n ^ 2 * N := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.1 hn).2
    rw [normSq_stepAtom (Real.log_nonneg hn1), Real.exp_log (by linarith)]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have hs := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hs
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc WeilForm.normSq (stepProbe N x)
      ≤ N * ∑ n ∈ Finset.Icc 1 N, x n ^ 2 * WeilForm.normSq (stepAtom (Real.log n)) := h
    _ ≤ N * ((∑ n ∈ Finset.Icc 1 N, x n ^ 2) * N) := mul_le_mul_of_nonneg_left hs hN0
    _ = N ^ 2 * ∑ n ∈ Finset.Icc 1 N, x n ^ 2 := by ring

/-- **The step functions stay polynomially far from the radical**: under RH, for `N ≥ 3` and `Σ_n x_n = 0`,
`Q(g_x) ≥ (√log N/(220e⁸N³))‖g_x‖²`, in the norm of `L²(d*u)`; on the whole window the least eigenvalue is far
smaller. -/
theorem weilQg_step_ge (hRH : RiemannHypothesis) {N : ℕ} (hN : 3 ≤ N) (x : ℕ → ℝ)
    (hx : ∑ n ∈ Finset.Icc 1 N, x n = 0) :
    Real.sqrt (Real.log N) / (220 * Real.exp 8 * N ^ 3) * WeilForm.normSq (stepProbe N x)
      ≤ weilQg (Real.log N) (stepProbe N x) := by
  rw [← form_eq_weilQg (by omega) x hx]
  have hg := BallGap.rate_gap hRH hN x
  have hn := normSq_stepProbe_le N x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc Real.sqrt (Real.log N) / (220 * Real.exp 8 * N ^ 3) * WeilForm.normSq (stepProbe N x)
      ≤ Real.sqrt (Real.log N) / (220 * Real.exp 8 * N ^ 3) * (N ^ 2 * ∑ n ∈ Finset.Icc 1 N, x n ^ 2) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = Real.sqrt (Real.log N) / (220 * Real.exp 8 * N) * ∑ n ∈ Finset.Icc 1 N, x n ^ 2 := by
        field_simp
    _ ≤ BallWeil.form N x := hg

end OrbitWindow
