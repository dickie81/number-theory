import Mathlib
import HalfPlaneGRH
import LandauWindow
import RampLaplace

/-!
# The Riemann hypothesis from a windowed bound on smoothed prime sums

The second step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`), and its frontier.

For a primitive Dirichlet character `χ`, the ramp sum `R_χ(x) = Σ_{n ≤ x} Λ(n) χ(n) (x/n − 1)` less its main term
is the error `E_χ(x)` (`rampErr`): the main term is `x log x − (1 + γ)x` for the character mod `1`, and
`−x·L'/L(1, χ)` otherwise. In `u = log x` the Laplace transform of `E_χ` is `Ψ_χ(s) = N(s)/(s(s − 1))`, with
`N(s) = −F'/F(s) + s·F'/F(1)` for the entire function `F = (s − 1)ζ(s)` or `F = L(s, χ)` (`Ψ`; for `ζ` plus the
`1/s` that the main term `x log x` leaves), continued across `s = 1`, where `N` vanishes. So `Ψ_χ` has a simple
pole at each zero `ρ` of `L(s, χ)` right of `0`, of residue `−m/(ρ(ρ − 1))` for a zero of order `m`
(`phi_local`), and no other singularity there.

A family of such characters with positive weights `w_i` has the error `G(x) = Σ w_i Re E_{χ_i}(x)`, whose
transform is `Σ (w_i/2)(Ψ_i(s) + conj Ψ_i(conj s))`: at a zero `ρ` of some member, or the conjugate of one, the
residue is `−S/(ρ(ρ − 1))` with `S > 0` the weighted count of zeros at `ρ` and `conj ρ`; at a real zero `β` it is
positive. Landau's theorem on windows (`LandauWindow.re_le_of_windows`) then gives `Family.zeroFree_of_windows`:
a bound `G(x) ≤ C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large leaves no zero of any member right of
`θ`. Taking real parts of the transform needs no symmetry of the `L`-functions under conjugation.

The frontier `WindowBound` asks this for the cyclic family of every primitive `χ` (`cyclic`): the primitive
characters inducing the powers of `χ`, the trivial one (`ζ`) with weight `1` and the others with `1/(3o + 1)`,
`o` the order of `χ`, the family that the next step of the proof works with. `rhAndGRH_of_windowBound`: it gives
the Riemann hypothesis for `ζ` and every Dirichlet `L`-function.
-/

open Complex ComplexConjugate Filter Topology Set MeasureTheory DirichletCharacter
open scoped ArithmeticFunction.vonMangoldt

namespace WindowGRH

/-! ## The logarithmic derivative near a zero -/

/-- Near a point `ρ` where an analytic `F` is not locally zero, `F'/F = m/(s − ρ) + h(s)` on a punctured
neighbourhood: `m` is the order of the zero of `F` at `ρ` (`0` when `F ρ ≠ 0`), `h` is analytic at `ρ`. -/
theorem logDeriv_local {F : ℂ → ℂ} {ρ : ℂ} (hF : AnalyticAt ℂ F ρ) (hne : ¬ ∀ᶠ s in 𝓝 ρ, F s = 0) :
    ∃ m : ℕ, (m = 0 ↔ F ρ ≠ 0) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, logDeriv F s = m / (s - ρ) + h s := by
  obtain ⟨m, g, hg, hg0, hFg⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.2 hne
  refine ⟨m, ?_, logDeriv g, hg.deriv.div hg hg0, ?_⟩
  · have hρ := hFg.self_of_nhds
    simp only [sub_self, smul_eq_mul] at hρ
    rw [hρ]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using hg0
    · simp [zero_pow hm.ne', hm.ne']
  · have hev : ∀ᶠ s in 𝓝 ρ, (F =ᶠ[𝓝 s] fun t => (t - ρ) ^ m • g t) ∧ g s ≠ 0 ∧ DifferentiableAt ℂ g s :=
      hFg.eventually_nhds.and ((hg.continuousAt.eventually_ne hg0).and
        (hg.eventually_analyticAt.mono fun s hs => hs.differentiableAt))
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s ⟨hFs, hgs, hdg⟩ (hsρ : s ≠ ρ)
    have hsρ' : s - ρ ≠ 0 := sub_ne_zero.2 hsρ
    simp only [smul_eq_mul] at hFs
    rw [(logDeriv_congr_nhds hFs).eq_of_nhds]
    show logDeriv ((fun t : ℂ => (t - ρ) ^ m) * g) s = _
    rw [logDeriv_mul (f := fun t : ℂ => (t - ρ) ^ m) (g := g) s (pow_ne_zero m hsρ') hgs (by fun_prop) hdg,
      logDeriv_fun_pow (by fun_prop) m]
    have : logDeriv (fun t : ℂ => t - ρ) s = 1 / (s - ρ) := by
      rw [logDeriv_apply, deriv_sub_const, deriv_id'']
    rw [this, mul_one_div]

/-! ## The transform of one character's error -/

/-- `N_F(s) = −F'/F(s) + s·F'/F(1)`, which vanishes at `s = 1`. -/
noncomputable def numer (F : ℂ → ℂ) (s : ℂ) : ℂ := -logDeriv F s + s * logDeriv F 1

/-- `Φ_F(s) = N_F(s)/(s(s − 1))`, continued across `s = 1`. -/
noncomputable def phi (F : ℂ → ℂ) (s : ℂ) : ℂ := dslope (numer F) 1 s / s

theorem phi_of_ne_one (F : ℂ → ℂ) {s : ℂ} (hs : s ≠ 1) : phi F s = numer F s / (s * (s - 1)) := by
  have h1 : numer F 1 = 0 := by simp [numer]
  rw [phi, dslope_of_ne _ hs, slope_def_field, h1, sub_zero, div_div, mul_comm (s - 1)]

theorem differentiableAt_numer {F : ℂ → ℂ} (hF : Differentiable ℂ F) {s : ℂ} (hs : F s ≠ 0) :
    DifferentiableAt ℂ (numer F) s := by
  have hd : DifferentiableAt ℂ (deriv F) s := (hF.analyticAt s).deriv.differentiableAt
  have hl : DifferentiableAt ℂ (logDeriv F) s := by
    show DifferentiableAt ℂ (fun w => deriv F w / F w) s
    exact hd.div (hF s) hs
  unfold numer
  fun_prop

/-- `Φ_F` is holomorphic at every `s ≠ 0` where `F` does not vanish, `s = 1` included. -/
theorem differentiableAt_phi {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h1 : F 1 ≠ 0) {s : ℂ} (hs0 : s ≠ 0)
    (hs : F s ≠ 0) : DifferentiableAt ℂ (phi F) s := by
  refine DifferentiableAt.div ?_ differentiableAt_id hs0
  rcases eq_or_ne s 1 with rfl | hs1
  · have hU : {w | F w ≠ 0} ∈ 𝓝 (1 : ℂ) := (isOpen_ne_fun hF.continuous continuous_const).mem_nhds h1
    have hdiff : DifferentiableOn ℂ (numer F) {w | F w ≠ 0} := fun w hw =>
      (differentiableAt_numer hF hw).differentiableWithinAt
    exact ((differentiableOn_dslope hU).2 hdiff).differentiableAt hU
  · exact (differentiableAt_dslope_of_ne hs1).2 (differentiableAt_numer hF hs)

/-- An entire function that is not identically zero is not locally zero anywhere. -/
theorem not_eventually_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) {a : ℂ} (ha : F a ≠ 0) (ρ : ℂ) :
    ¬ ∀ᶠ s in 𝓝 ρ, F s = 0 := fun h =>
  ha ((hF.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ ρ) h (mem_univ a))

/-- **The poles of `Φ_F`**: at every `ρ ≠ 0`, `Φ_F = c/(s − ρ) + h` near `ρ`, with `c = −m/(ρ(ρ − 1))`, `m` the
order of the zero of `F` at `ρ`, and `h` analytic at `ρ`. -/
theorem phi_local {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h1 : F 1 ≠ 0) {ρ : ℂ} (hρ0 : ρ ≠ 0) :
    ∃ m : ℕ, (m = 0 ↔ F ρ ≠ 0) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, phi F s = -(m : ℂ) / (ρ * (ρ - 1)) / (s - ρ) + h s := by
  by_cases hFρ : F ρ = 0
  · have hρ1 : ρ ≠ 1 := fun e => h1 (e ▸ hFρ)
    obtain ⟨m, hm, h₁, hh₁, hev⟩ := logDeriv_local (hF.analyticAt ρ) (not_eventually_zero hF h1 ρ)
    let q : ℂ → ℂ := fun s => 1 / (s * (s - 1))
    have hqU : DifferentiableOn ℂ q {s | s ≠ 0 ∧ s ≠ 1} := by
      intro s hs
      have h : DifferentiableAt ℂ (fun w : ℂ => 1 / (w * (w - 1))) s :=
        (differentiableAt_const (1 : ℂ)).div (by fun_prop) (mul_ne_zero hs.1 (sub_ne_zero.2 hs.2))
      exact h.differentiableWithinAt
    have hUo : IsOpen {s : ℂ | s ≠ 0 ∧ s ≠ 1} := isOpen_ne.inter isOpen_ne
    have hU : {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∈ 𝓝 ρ := hUo.mem_nhds ⟨hρ0, hρ1⟩
    have hdq : AnalyticAt ℂ (dslope q ρ) ρ :=
      ((differentiableOn_dslope hU).2 hqU).analyticAt hU
    have hqρ : AnalyticAt ℂ q ρ := hqU.analyticAt hU
    refine ⟨m, hm, fun s => -(m : ℂ) * dslope q ρ s + (-h₁ s + s * logDeriv F 1) * q s, ?_, ?_⟩
    · exact (analyticAt_const.mul hdq).add ((hh₁.neg.add (analyticAt_id.mul analyticAt_const)).mul hqρ)
    · filter_upwards [hev, nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with s hs ⟨hs0, hs1⟩ (hsρ : s ≠ ρ)
      have hsρ' : s - ρ ≠ 0 := sub_ne_zero.2 hsρ
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
      have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
      rw [phi_of_ne_one F hs1, numer, hs, dslope_of_ne _ hsρ, slope_def_field]
      simp only [q]
      field_simp
      ring
  · refine ⟨0, by simp [hFρ], phi F, ?_, ?_⟩
    · have hU : {s : ℂ | s ≠ 0 ∧ F s ≠ 0} ∈ 𝓝 ρ :=
        (isOpen_ne.inter (isOpen_ne_fun hF.continuous continuous_const)).mem_nhds ⟨hρ0, hFρ⟩
      exact analyticAt_iff_eventually_differentiableAt.2
        (Filter.mem_of_superset hU fun s hs => differentiableAt_phi hF h1 hs.1 hs.2)
    · filter_upwards with s
      simp

/-! ## `ζ` with its pole multiplied away: Mathlib's `riemannZeta₁` -/

theorem riemannZeta₁_of_ne_one {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 hs), one_mul]

/-- `ζ₁'(1)/ζ₁(1) = γ` (Mathlib's `deriv_riemannZeta₁_one`). -/
theorem logDeriv_riemannZeta₁_one : logDeriv riemannZeta₁ 1 = Real.eulerMascheroniConstant := by
  rw [logDeriv_apply, deriv_riemannZeta₁_one, riemannZeta₁_one, div_one]

theorem logDeriv_riemannZeta₁ {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = 1 / (s - 1) + deriv riemannZeta s / riemannZeta s := by
  have hev : riemannZeta₁ =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w := by
    filter_upwards [eventually_ne_nhds hs] with w hw using riemannZeta₁_of_ne_one hw
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  show logDeriv ((fun w : ℂ => w - 1) * riemannZeta) s = _
  rw [logDeriv_mul (f := fun w : ℂ => w - 1) (g := riemannZeta) s (sub_ne_zero.2 hs) hz (by fun_prop)
    (differentiableAt_riemannZeta hs), logDeriv_apply, logDeriv_apply, deriv_sub_const, deriv_id'']

/-! ## The error of one character, and its transform -/

/-- The error of the ramp sum of `χ`: `R_χ(x) − x log x + (1 + γ)x` for the trivial character, and
`R_χ(x) + x·L'/L(1, χ)` for the others. -/
noncomputable def rampErr {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  if χ = 1 then
    RampLaplace.rampSum (fun n => χ n) x - ((x * Real.log x : ℝ) : ℂ) +
      (((1 + Real.eulerMascheroniConstant) * x : ℝ) : ℂ)
  else RampLaplace.rampSum (fun n => χ n) x + (x : ℂ) * logDeriv (LFunction χ) 1

/-- The entire function with the zeros of `L(s, χ)` right of `0`: `ζ₁` for the trivial character, `L(s, χ)`
for the others. -/
noncomputable def entire {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  if χ = 1 then riemannZeta₁ else LFunction χ

/-- The transform of `E_χ`: `Φ_F` for that entire function, plus `1/s` for the trivial character. -/
noncomputable def Ψ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  if χ = 1 then fun s => phi riemannZeta₁ s + 1 / s else phi (LFunction χ)

section OneCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem differentiable_entire : Differentiable ℂ (entire χ) := by
  unfold entire
  split_ifs with h
  · exact differentiable_riemannZeta₁
  · exact differentiable_LFunction h

theorem entire_one_ne_zero : entire χ 1 ≠ 0 := by
  unfold entire
  split_ifs with h
  · rw [riemannZeta₁_one]; exact one_ne_zero
  · exact LFunction_apply_one_ne_zero h

theorem entire_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : entire χ s ≠ 0 := by
  unfold entire
  split_ifs with h
  · rcases eq_or_ne s 1 with rfl | hs1
    · rw [riemannZeta₁_one]; exact one_ne_zero
    · rw [riemannZeta₁_of_ne_one hs1]
      exact mul_ne_zero (sub_ne_zero.2 hs1) (riemannZeta_ne_zero_of_one_le_re hs)
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl h) hs

/-- For an admissible `χ`, `L(s, χ)` and `entire χ` have the same zeros (the pole of `ζ` aside). -/
theorem LFunction_eq_zero_iff_entire (hadm : N = 1 ∨ χ ≠ 1) {s : ℂ} (hs : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s = 0 ↔ entire χ s = 0 := by
  by_cases h : χ = 1
  · have hN : N = 1 := hadm.resolve_right (not_not.2 h)
    subst hN
    have hs1 : s ≠ 1 := hs.resolve_left (not_not.2 h)
    simp only [entire, h, ite_true, riemannZeta₁_of_ne_one hs1, LFunction_modOne_eq, mul_eq_zero, sub_eq_zero, hs1,
      false_or]
  · simp [entire, h]

theorem differentiableAt_Ψ {s : ℂ} (hs0 : s ≠ 0) (hs : entire χ s ≠ 0) : DifferentiableAt ℂ (Ψ χ) s := by
  have hphi := differentiableAt_phi (differentiable_entire χ) (entire_one_ne_zero χ) hs0 hs
  unfold Ψ
  unfold entire at hphi
  split_ifs with h
  · rw [ite_eq_left h] at hphi
    exact hphi.add ((differentiableAt_const _).div differentiableAt_id hs0)
  · rwa [ite_eq_right h] at hphi

/-- **The poles of `Ψ_χ`**: at every `ρ ≠ 0`, `Ψ_χ = −m/(ρ(ρ − 1))/(s − ρ) + h` near `ρ`, `m` the order of the
zero of `entire χ` at `ρ` and `h` analytic at `ρ`. -/
theorem Ψ_local {ρ : ℂ} (hρ0 : ρ ≠ 0) :
    ∃ m : ℕ, (m = 0 ↔ entire χ ρ ≠ 0) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, Ψ χ s = -(m : ℂ) / (ρ * (ρ - 1)) / (s - ρ) + h s := by
  obtain ⟨m, hm, h, hh, hev⟩ := phi_local (differentiable_entire χ) (entire_one_ne_zero χ) hρ0
  refine ⟨m, hm, ?_⟩
  unfold Ψ
  unfold entire at hm hev
  split_ifs with hχ
  · rw [ite_eq_left hχ] at hev
    refine ⟨fun s => h s + 1 / s, hh.add (analyticAt_const.div analyticAt_id hρ0), ?_⟩
    filter_upwards [hev] with s hs
    rw [hs]; ring
  · rw [ite_eq_right hχ] at hev
    exact ⟨h, hh, hev⟩

/-- `‖E_χ(e^u)‖ ≤ C e^{3u}` for `u ≥ 0`. -/
theorem norm_rampErr_exp_le : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖rampErr χ (Real.exp u)‖ ≤ C * Real.exp (3 * u) := by
  refine ⟨3 + 2 * Real.eulerMascheroniConstant + ‖logDeriv (LFunction χ) 1‖, fun u hu => ?_⟩
  have hx : 1 ≤ Real.exp u := Real.one_le_exp hu
  have hR := RampLaplace.norm_rampSum_le (f := fun n => χ n) (fun n => χ.norm_le_one _) hx
  have h3 : Real.exp u ^ 3 = Real.exp (3 * u) := by rw [← Real.exp_nat_mul]; norm_num
  have hu1 : Real.exp u ≤ Real.exp (3 * u) := Real.exp_le_exp.2 (by linarith)
  have hu2 : u * Real.exp u ≤ Real.exp (3 * u) := by
    calc u * Real.exp u ≤ Real.exp u * Real.exp u := by gcongr; linarith [Real.add_one_le_exp u]
      _ = Real.exp (2 * u) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (3 * u) := Real.exp_le_exp.2 (by linarith)
  have hγ : 0 ≤ Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hE : 0 ≤ Real.exp (3 * u) := (Real.exp_pos _).le
  rw [h3] at hR
  unfold rampErr
  split_ifs with h
  · calc ‖RampLaplace.rampSum (fun n => χ n) (Real.exp u) - ((Real.exp u * Real.log (Real.exp u) : ℝ) : ℂ) +
          (((1 + Real.eulerMascheroniConstant) * Real.exp u : ℝ) : ℂ)‖
        ≤ ‖RampLaplace.rampSum (fun n => χ n) (Real.exp u)‖ + ‖((Real.exp u * Real.log (Real.exp u) : ℝ) : ℂ)‖ +
          ‖(((1 + Real.eulerMascheroniConstant) * Real.exp u : ℝ) : ℂ)‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ _ := by
          rw [Complex.norm_real, Complex.norm_real, Real.log_exp, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
          nlinarith [norm_nonneg (logDeriv (LFunction χ) 1)]
  · calc ‖RampLaplace.rampSum (fun n => χ n) (Real.exp u) + (Real.exp u : ℂ) * logDeriv (LFunction χ) 1‖
        ≤ ‖RampLaplace.rampSum (fun n => χ n) (Real.exp u)‖ + Real.exp u * ‖logDeriv (LFunction χ) 1‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos u)]
      _ ≤ _ := by
          have hl := mul_le_mul_of_nonneg_right hu1 (norm_nonneg (logDeriv (LFunction χ) 1))
          nlinarith [norm_nonneg (logDeriv (LFunction χ) 1)]

theorem measurable_rampErr : Measurable (rampErr χ) := by
  unfold rampErr
  split_ifs
  · exact ((RampLaplace.measurable_rampSum _).sub (by fun_prop)).add (by fun_prop)
  · exact (RampLaplace.measurable_rampSum _).add (by fun_prop)

/-- A function of growth `e^{3u}` times `e^{−su}`, `Re s > 3`, is integrable on `(0, ∞)`. -/
theorem integrableOn_of_growth {E : ℝ → ℂ} (hE : Measurable E) {C : ℝ}
    (hC : ∀ u : ℝ, 0 ≤ u → ‖E u‖ ≤ C * Real.exp (3 * u)) {s : ℂ} (hs : 3 < s.re) :
    IntegrableOn (fun u : ℝ => E u * cexp (-(s * u))) (Ioi 0) := by
  have hint : IntegrableOn (fun u : ℝ => C * Real.exp (-(s.re - 3) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul C
  refine hint.mono' (hE.mul (Continuous.measurable (by fun_prop))).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
  rw [norm_mul, Complex.norm_exp]
  have hre : (-(s * (u : ℂ))).re = -(s.re * u) := by simp
  rw [hre]
  calc ‖E u‖ * Real.exp (-(s.re * u)) ≤ C * Real.exp (3 * u) * Real.exp (-(s.re * u)) :=
        mul_le_mul_of_nonneg_right (hC u hu.le) (Real.exp_pos _).le
    _ = C * Real.exp (-(s.re - 3) * u) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **The transform of `E_χ`**: `∫₀^∞ E_χ(e^u) e^{−su} du = Ψ_χ(s)` for `Re s > 3`. -/
theorem laplace_rampErr (hadm : N = 1 ∨ χ ≠ 1) {s : ℂ} (hs : 3 < s.re) :
    ∫ u in Ioi (0 : ℝ), rampErr χ (Real.exp u) * cexp (-(s * u)) = Ψ χ s := by
  have hs1 : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := fun e => by rw [e, zero_re] at hs1; linarith
  have hs1' : s ≠ 1 := fun e => by rw [e, one_re] at hs1; exact lt_irrefl _ hs1
  have hsub : s - 1 ≠ 0 := sub_ne_zero.2 hs1'
  have h3 : ∀ u : ℝ, Real.exp u ^ 3 = Real.exp (3 * u) := fun u => by rw [← Real.exp_nat_mul]; norm_num
  have hR : IntegrableOn (fun u : ℝ => RampLaplace.rampSum (fun n => χ n) (Real.exp u) * cexp (-(s * u)))
      (Ioi 0) := by
    refine integrableOn_of_growth ((RampLaplace.measurable_rampSum _).comp Real.measurable_exp) (C := 1)
      (fun u hu => ?_) hs
    rw [one_mul, ← h3]
    exact RampLaplace.norm_rampSum_le (f := fun n => χ n) (fun n => χ.norm_le_one _) (Real.one_le_exp hu)
  have hX : IntegrableOn (fun u : ℝ => (Real.exp u : ℂ) * cexp (-(s * u))) (Ioi 0) := by
    refine integrableOn_of_growth (by fun_prop) (C := 1) (fun u hu => ?_) hs
    rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos u)]
    exact Real.exp_le_exp.2 (by linarith)
  have hXL : IntegrableOn (fun u : ℝ => ((u * Real.exp u : ℝ) : ℂ) * cexp (-(s * u))) (Ioi 0) := by
    refine integrableOn_of_growth (by fun_prop) (C := 1) (fun u hu => ?_) hs
    rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc u * Real.exp u ≤ Real.exp u * Real.exp u := by gcongr; linarith [Real.add_one_le_exp u]
      _ = Real.exp (2 * u) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (3 * u) := Real.exp_le_exp.2 (by linarith)
  have hIR := RampLaplace.laplace_rampSum (f := fun n => χ n) (fun n => χ.norm_le_one _) hs1
  by_cases h : χ = 1
  · have hN : N = 1 := hadm.resolve_right (not_not.2 h)
    subst hN
    subst h
    -- the three pieces
    have hsplit : (fun u : ℝ => rampErr (1 : DirichletCharacter ℂ 1) (Real.exp u) * cexp (-(s * u))) =
        fun u => RampLaplace.rampSum (fun n => (1 : DirichletCharacter ℂ 1) n) (Real.exp u) * cexp (-(s * u)) -
          ((u * Real.exp u : ℝ) : ℂ) * cexp (-(s * u)) +
          ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) * ((Real.exp u : ℂ) * cexp (-(s * u))) := by
      ext u
      simp only [rampErr, ite_true, Real.log_exp]
      push_cast
      ring
    have hRX : IntegrableOn (fun u : ℝ => RampLaplace.rampSum (fun n => (1 : DirichletCharacter ℂ 1) n)
        (Real.exp u) * cexp (-(s * u)) - ((u * Real.exp u : ℝ) : ℂ) * cexp (-(s * u))) (Ioi 0) := hR.sub hXL
    rw [hsplit, integral_add hRX (hX.const_mul _), integral_sub hR hXL, integral_const_mul, hIR,
      RampLaplace.laplace_mul_exp hs1, RampLaplace.laplace_exp hs1]
    have hL : LSeries (fun n => (Λ n : ℂ) * (1 : DirichletCharacter ℂ 1) n) s =
        -deriv riemannZeta s / riemannZeta s := by
      rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1]
      refine LSeries_congr (fun {n} _ => ?_) s
      rw [MulChar.one_apply (isUnit_of_subsingleton _), mul_one]
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
    simp only [Ψ, ite_true, phi_of_ne_one _ hs1', numer, logDeriv_riemannZeta₁ hs1' hz, logDeriv_riemannZeta₁_one, hL]
    field_simp
    push_cast
    ring
  · have hsplit : (fun u : ℝ => rampErr χ (Real.exp u) * cexp (-(s * u))) =
        fun u => RampLaplace.rampSum (fun n => χ n) (Real.exp u) * cexp (-(s * u)) +
          logDeriv (LFunction χ) 1 * ((Real.exp u : ℂ) * cexp (-(s * u))) := by
      ext u
      simp only [rampErr, h, ite_false]
      ring
    rw [hsplit, integral_add hR (hX.const_mul _), integral_const_mul, hIR, RampLaplace.laplace_exp hs1]
    have hL : LSeries (fun n => (Λ n : ℂ) * χ n) s = -deriv (LFunction χ) s / LFunction χ s := by
      have h' := LSeries_twist_vonMangoldt_eq χ hs1
      rw [← LFunction_eq_LSeries χ hs1, ← deriv_LFunction_eq_deriv_LSeries χ hs1] at h'
      rw [← h']
      exact LSeries_congr (fun {n} _ => by simp [mul_comm]) s
    simp only [Ψ, h, ite_false, phi_of_ne_one _ hs1', numer, hL, logDeriv_apply]
    field_simp

end OneCharacter

/-! ## Real parts -/

/-- `∫ Re E(u) e^{−su} du = (∫ E(u) e^{−su} du + conj ∫ E(u) e^{−s̄u} du)/2`. -/
theorem integral_re_mul {E : ℝ → ℂ} {s : ℂ}
    (h1 : IntegrableOn (fun u : ℝ => E u * cexp (-(s * u))) (Ioi 0))
    (h2 : IntegrableOn (fun u : ℝ => E u * cexp (-(conj s * u))) (Ioi 0)) :
    ∫ u in Ioi (0 : ℝ), ((E u).re : ℂ) * cexp (-(s * u)) =
      ((∫ u in Ioi (0 : ℝ), E u * cexp (-(s * u))) + conj (∫ u in Ioi (0 : ℝ), E u * cexp (-(conj s * u)))) / 2 := by
  have h2' : IntegrableOn (fun u : ℝ => conj (E u * cexp (-(conj s * u)))) (Ioi 0) :=
    h2.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable h2.aestronglyMeasurable)
      (Eventually.of_forall fun u => by simp)
  rw [← integral_conj, ← integral_add h1 h2', ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [map_mul, ← Complex.exp_conj, map_neg, conj_conj, conj_ofReal]
  rw [Complex.re_eq_add_conj]
  ring

/-! ## A weighted family of characters -/

/-- A finite family of Dirichlet characters, none of them a principal character of modulus `> 1`, with positive
weights. -/
structure Family where
  ι : Type
  [fintype : Fintype ι]
  N : ι → ℕ
  [neZero : ∀ i, NeZero (N i)]
  χ : ∀ i, DirichletCharacter ℂ (N i)
  w : ι → ℝ
  w_pos : ∀ i, 0 < w i
  adm : ∀ i, N i = 1 ∨ χ i ≠ 1

attribute [instance] Family.fintype Family.neZero

namespace Family

variable (F : Family)

/-- The weighted error `G(x) = Σ w_i Re E_{χ_i}(x)`. -/
noncomputable def G (x : ℝ) : ℝ := ∑ i, F.w i * (rampErr (F.χ i) x).re

/-- Its transform, `Σ (w_i/2)(Ψ_i(s) + conj Ψ_i(conj s))`. -/
noncomputable def Φ (s : ℂ) : ℂ := ∑ i, ((F.w i / 2 : ℝ) : ℂ) * (Ψ (F.χ i) s + conj (Ψ (F.χ i) (conj s)))

/-- The zeros right of `0` of the members' entire functions, and their conjugates. -/
def Z : Set ℂ := {ρ | 0 < ρ.re ∧ ∃ i, entire (F.χ i) ρ = 0 ∨ entire (F.χ i) (conj ρ) = 0}

theorem measurable_G : Measurable F.G :=
  Finset.measurable_sum _ fun _ _ => measurable_const.mul (Complex.measurable_re.comp (measurable_rampErr _))

theorem growth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |F.G (Real.exp u)| ≤ C * Real.exp (3 * u) := by
  choose C hC using fun i => norm_rampErr_exp_le (F.χ i)
  refine ⟨∑ i, F.w i * |C i|, fun u hu => ?_⟩
  unfold G
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_pos (F.w_pos i), mul_assoc]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ((hC i u hu).trans ?_)) (F.w_pos i).le
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le

theorem laplace_eq {s : ℂ} (hs : 3 < s.re) : F.Φ s = LandauWindow.laplace (fun u => F.G (Real.exp u)) s := by
  have hcs : 3 < (conj s).re := by rwa [conj_re]
  have hint : ∀ i, ∀ t : ℂ, 3 < t.re →
      IntegrableOn (fun u : ℝ => rampErr (F.χ i) (Real.exp u) * cexp (-(t * u))) (Ioi 0) := fun i t ht => by
    obtain ⟨C, hC⟩ := norm_rampErr_exp_le (F.χ i)
    exact integrableOn_of_growth ((measurable_rampErr _).comp Real.measurable_exp) hC ht
  have hintre : ∀ i, IntegrableOn
      (fun u : ℝ => ((F.w i * (rampErr (F.χ i) (Real.exp u)).re : ℝ) : ℂ) * cexp (-(s * u))) (Ioi 0) := by
    intro i
    obtain ⟨C, hC⟩ := norm_rampErr_exp_le (F.χ i)
    refine integrableOn_of_growth (E := fun u => ((F.w i * (rampErr (F.χ i) (Real.exp u)).re : ℝ) : ℂ))
      (C := F.w i * C) (Complex.measurable_ofReal.comp (measurable_const.mul
      (Complex.measurable_re.comp ((measurable_rampErr _).comp Real.measurable_exp)))) ?_ hs
    intro u hu
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (F.w_pos i), mul_assoc]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hC u hu)) (F.w_pos i).le
  unfold LandauWindow.laplace G Φ
  have hsum : (fun u : ℝ => ((∑ i, F.w i * (rampErr (F.χ i) (Real.exp u)).re : ℝ) : ℂ) * cexp (-(s * u))) =
      fun u => ∑ i, ((F.w i * (rampErr (F.χ i) (Real.exp u)).re : ℝ) : ℂ) * cexp (-(s * u)) := by
    ext u
    push_cast
    rw [Finset.sum_mul]
  rw [hsum, integral_finsetSum _ fun i _ => hintre i]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hre := integral_re_mul (E := fun u => rampErr (F.χ i) (Real.exp u)) (hint i s hs)
    (hint i (conj s) hcs)
  rw [laplace_rampErr _ (F.adm i) hs, laplace_rampErr _ (F.adm i) hcs] at hre
  have hpull : ∫ u in Ioi (0 : ℝ), ((F.w i * (rampErr (F.χ i) (Real.exp u)).re : ℝ) : ℂ) * cexp (-(s * u)) =
      (F.w i : ℂ) * ∫ u in Ioi (0 : ℝ), (((rampErr (F.χ i) (Real.exp u)).re : ℝ) : ℂ) * cexp (-(s * u)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    push_cast
    ring
  rw [hpull, hre]
  push_cast
  ring

theorem re_lt_one (ρ : ℂ) (hρ : ρ ∈ F.Z) : ρ.re < 1 := by
  obtain ⟨-, i, hi | hi⟩ := hρ
  · exact not_le.1 fun h => entire_ne_zero_of_one_le_re (F.χ i) h hi
  · exact not_le.1 fun h => entire_ne_zero_of_one_le_re (F.χ i) (by rwa [conj_re]) hi

/-- `conj` carries punctured neighbourhoods to punctured neighbourhoods. -/
theorem tendsto_conj (z : ℂ) : Tendsto (fun w : ℂ => conj w) (𝓝[≠] z) (𝓝[≠] (conj z)) :=
  (Complex.conjLIE.toHomeomorph.map_punctured_nhds_eq z).le

theorem isolated (z : ℂ) (_hz : 0 < z.re) : ∀ᶠ w in 𝓝[≠] z, w ∉ F.Z := by
  have hne : ∀ i, ∀ a : ℂ, ∀ᶠ w in 𝓝[≠] a, entire (F.χ i) w ≠ 0 := fun i a =>
    ((differentiable_entire (F.χ i)).analyticAt a).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (not_eventually_zero (differentiable_entire _) (entire_one_ne_zero _) a)
  have h1 : ∀ᶠ w in 𝓝[≠] z, ∀ i, entire (F.χ i) w ≠ 0 := eventually_all.2 fun i => hne i z
  have h2 : ∀ᶠ w in 𝓝[≠] z, ∀ i, entire (F.χ i) (conj w) ≠ 0 :=
    eventually_all.2 fun i => (tendsto_conj z).eventually (hne i (conj z))
  filter_upwards [h1, h2] with w hw1 hw2
  rintro ⟨-, i, hi | hi⟩
  · exact hw1 i hi
  · exact hw2 i hi

theorem differentiableAt_Φ (s : ℂ) (hs : 0 < s.re) (hsZ : s ∉ F.Z) : DifferentiableAt ℂ F.Φ s := by
  have hs0 : s ≠ 0 := fun e => by rw [e, zero_re] at hs; exact lt_irrefl _ hs
  have hcs0 : conj s ≠ 0 := by simpa using hs0
  unfold Φ
  refine DifferentiableAt.fun_sum fun i _ => (differentiableAt_const _).mul ((differentiableAt_Ψ _ hs0
    fun h => hsZ ⟨hs, i, Or.inl h⟩).add ?_)
  have h := (differentiableAt_Ψ (F.χ i) hcs0 fun h => hsZ ⟨hs, i, Or.inr h⟩).conj_conj
  rwa [conj_conj] at h

/-- `s ↦ conj (h (conj s))` is analytic at `ρ` when `h` is analytic at `conj ρ`. -/
theorem analyticAt_conj_conj {h : ℂ → ℂ} {ρ : ℂ} (hh : AnalyticAt ℂ h (conj ρ)) :
    AnalyticAt ℂ (fun s => conj (h (conj s))) ρ := by
  have hd := analyticAt_iff_eventually_differentiableAt.1 hh
  refine analyticAt_iff_eventually_differentiableAt.2 ?_
  have ht : Tendsto (fun w : ℂ => conj w) (𝓝 ρ) (𝓝 (conj ρ)) := Complex.continuous_conj.continuousAt.tendsto
  filter_upwards [ht.eventually hd] with w hw
  have := hw.conj_conj
  rwa [conj_conj] at this

theorem pole (ρ : ℂ) (hρ : ρ ∈ F.Z) : ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re) ∧
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, F.Φ s = c / (s - ρ) + h s := by
  have hre1 := F.re_lt_one ρ hρ
  obtain ⟨hρre, i₀, hi₀⟩ := hρ
  have hρ0 : ρ ≠ 0 := fun e => by rw [e, zero_re] at hρre; exact lt_irrefl _ hρre
  have hρ1 : ρ - 1 ≠ 0 := fun e => by
    have := congrArg re e; rw [sub_re, one_re, zero_re] at this; linarith
  have hcρ0 : conj ρ ≠ 0 := by simpa using hρ0
  choose m hm h hh hev using fun i => Ψ_local (F.χ i) hρ0
  choose m' hm' h' hh' hev' using fun i => Ψ_local (F.χ i) hcρ0
  set S : ℝ := ∑ i, F.w i / 2 * ((m i : ℝ) + m' i) with hS_def
  have hS : 0 < S := by
    refine Finset.sum_pos' (fun i _ => by have := F.w_pos i; positivity) ⟨i₀, Finset.mem_univ _, ?_⟩
    have hpos : 0 < (m i₀ : ℝ) + m' i₀ := by
      rcases hi₀ with hz | hz
      · have : m i₀ ≠ 0 := fun e => (hm i₀).1 e hz
        have : (0 : ℝ) < m i₀ := by exact_mod_cast Nat.pos_of_ne_zero this
        positivity
      · have : m' i₀ ≠ 0 := fun e => (hm' i₀).1 e hz
        have : (0 : ℝ) < m' i₀ := by exact_mod_cast Nat.pos_of_ne_zero this
        positivity
    have := F.w_pos i₀
    positivity
  refine ⟨-(S : ℂ) / (ρ * (ρ - 1)), ?_, ?_, fun s => ∑ i, ((F.w i / 2 : ℝ) : ℂ) * (h i s + conj (h' i (conj s))),
    ?_, ?_⟩
  · exact div_ne_zero (neg_ne_zero.2 (ofReal_ne_zero.2 hS.ne')) (mul_ne_zero hρ0 hρ1)
  · intro him
    have hρr : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hρr, ← ofReal_one, ← ofReal_sub, ← ofReal_mul, ← ofReal_neg, ← ofReal_div, ofReal_re]
    have h1 : ρ.re * (ρ.re - 1) < 0 := mul_neg_of_pos_of_neg hρre (by linarith)
    exact div_pos_of_neg_of_neg (by linarith) h1
  · have ha := Finset.analyticAt_sum (f := fun i s => ((F.w i / 2 : ℝ) : ℂ) * (h i s + conj (h' i (conj s))))
      Finset.univ fun i _ => analyticAt_const.mul ((hh i).add (analyticAt_conj_conj (hh' i)))
    convert ha using 1
    ext s
    simp [Finset.sum_apply]
  · have hev2 : ∀ i, ∀ᶠ s in 𝓝[≠] ρ, Ψ (F.χ i) (conj s) =
        -(m' i : ℂ) / (conj ρ * (conj ρ - 1)) / (conj s - conj ρ) + h' i (conj s) :=
      fun i => (tendsto_conj ρ).eventually (hev' i)
    filter_upwards [eventually_all.2 hev, eventually_all.2 hev2, self_mem_nhdsWithin] with s hs hs' (hsρ : s ≠ ρ)
    have hsρ' : s - ρ ≠ 0 := sub_ne_zero.2 hsρ
    unfold Φ
    have hterm : ∀ i, ((F.w i / 2 : ℝ) : ℂ) * (Ψ (F.χ i) s + conj (Ψ (F.χ i) (conj s))) =
        ((F.w i / 2 * ((m i : ℝ) + m' i) : ℝ) : ℂ) * (-1 / (ρ * (ρ - 1)) / (s - ρ)) +
          ((F.w i / 2 : ℝ) : ℂ) * (h i s + conj (h' i (conj s))) := by
      intro i
      rw [hs i, hs' i]
      simp only [map_add, map_div₀, map_neg, map_mul, map_sub, map_natCast, map_one, conj_conj]
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.sum_mul, hS_def]
    push_cast
    field_simp

/-- **Landau's theorem on windows for a family of characters**: if `G(x) ≤ C x^θ` on windows `[Y, Y^λ]` with
`Y` arbitrarily large, no member's `L`-function vanishes right of `θ`. -/
theorem zeroFree_of_windows {θ lam C : ℝ} (hθ : 0 < θ) (hlam : 1 < lam)
    (hW : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Icc Y (Y ^ lam), F.G x ≤ C * x ^ θ) (i : F.ι) {s : ℂ}
    (hs : θ < s.re) (hχs : F.χ i ≠ 1 ∨ s ≠ 1) : LFunction (F.χ i) s ≠ 0 := by
  have hP : LandauWindow.PoleData (fun u => F.G (Real.exp u)) F.Φ F.Z 3 :=
    { measurable := F.measurable_G.comp Real.measurable_exp
      growth := F.growth
      laplace_eq := fun s hs => F.laplace_eq hs
      re_lt_one := F.re_lt_one
      isolated := F.isolated
      differentiableAt := F.differentiableAt_Φ
      pole := F.pole }
  have hW' : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U (lam * U), F.G (Real.exp u) ≤ C * Real.exp (θ * u) := by
    intro U₀
    obtain ⟨Y, hY, hYW⟩ := hW (Real.exp U₀)
    have hY0 : 0 < Y := (Real.exp_pos U₀).trans_le hY
    refine ⟨Real.log Y, (Real.le_log_iff_exp_le hY0).2 hY, fun u hu => ?_⟩
    have hx := hYW (Real.exp u) ⟨?_, ?_⟩
    · rwa [← Real.exp_mul, mul_comm u θ] at hx
    · rw [← Real.exp_log hY0]; exact Real.exp_le_exp.2 hu.1
    · rw [Real.rpow_def_of_pos hY0]; exact Real.exp_le_exp.2 (by linarith [hu.2])
  intro hz
  have hzZ : s ∈ F.Z := ⟨hθ.trans hs, i, Or.inl ((LFunction_eq_zero_iff_entire (F.χ i) (F.adm i) hχs).1 hz)⟩
  exact absurd (LandauWindow.re_le_of_windows hP hθ hlam hW' s hzZ) (not_le.2 hs)

end Family

/-! ## The frontier -/

/-- The cyclic family of `χ`: the primitive characters inducing the powers of `χ`, the trivial one (`ζ`) with
weight `1` and the others with weight `1/(3o + 1)`, `o` the order of `χ`. -/
noncomputable def cyclic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Family where
  ι := Subgroup.zpowers χ
  fintype := Fintype.ofFinite _
  N := fun η => (η : DirichletCharacter ℂ N).conductor
  neZero := fun η => ⟨(η : DirichletCharacter ℂ N).conductor_ne_zero⟩
  χ := fun η => (η : DirichletCharacter ℂ N).primitiveCharacter
  w := fun η => if (η : DirichletCharacter ℂ N) = 1 then 1 else (3 * (orderOf χ : ℝ) + 1)⁻¹
  w_pos := fun η => by split_ifs <;> positivity
  adm := fun η => by
    by_cases h : (η : DirichletCharacter ℂ N) = 1
    · left
      rw [h]
      exact conductor_one
    · exact .inr (HalfPlaneGRH.primitiveCharacter_ne_one h)

/-- **The frontier**: for every primitive `χ` and every `θ > 1/2`, the weighted error of the cyclic family of `χ`
is at most `C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large, for some `λ > 1` and `C`. -/
def WindowBound : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ θ : ℝ, 1 / 2 < θ →
    ∃ lam : ℝ, 1 < lam ∧ ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Icc Y (Y ^ lam), (cyclic χ).G x ≤ C * x ^ θ

/-- The frontier gives the zero-free half-plane `Re s > 1/2` for every primitive character. -/
theorem zeroFreeRightOf_half_of_windowBound (h : WindowBound) : HalfPlaneGRH.ZeroFreeRightOf (1 / 2) := by
  intro N _ χ hχ s hs hχs
  obtain ⟨lam, hlam, C, hW⟩ := h N χ hχ ((1 / 2 + s.re) / 2) (by linarith)
  have hθ0 : 0 < (1 / 2 + s.re) / 2 := by linarith
  have hθs : (1 / 2 + s.re) / 2 < s.re := by linarith
  have hne := (cyclic χ).zeroFree_of_windows hθ0 hlam hW (⟨χ, Subgroup.mem_zpowers χ⟩ : Subgroup.zpowers χ) hθs
    (hχs.imp_left HalfPlaneGRH.primitiveCharacter_ne_one)
  rw [ne_eq, HalfPlaneGRH.LFunction_eq_zero_iff_primitive χ (hθ0.trans hθs) hχs]
  exact hne

/-- **The Riemann hypothesis for `ζ` and every Dirichlet `L`-function, from the frontier `WindowBound`.** -/
theorem rhAndGRH_of_windowBound (h : WindowBound) : HalfPlaneGRH.RHandGRH :=
  HalfPlaneGRH.rhAndGRH_of_zeroFreeRightOf (zeroFreeRightOf_half_of_windowBound h)

/-! ## The frontier for `ζ` alone -/

/-- The family of `ζ` alone: the character mod `1`, with weight `1`. -/
noncomputable def zetaFamily : Family where
  ι := Unit
  N := fun _ => 1
  χ := fun _ => 1
  w := fun _ => 1
  w_pos := fun _ => one_pos
  adm := fun _ => Or.inl rfl

/-- The error of `ζ`'s family is `Σ_{n ≤ x} Λ(n)(x/n − 1) − x log x + (1 + γ)x`. -/
theorem zetaFamily_G (x : ℝ) : zetaFamily.G x =
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x := by
  have h1 : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) n = 1 := fun n => MulChar.one_apply (isUnit_of_subsingleton _)
  have hG : zetaFamily.G x = (rampErr (1 : DirichletCharacter ℂ 1) x).re := by
    show ∑ _i : Unit, (1 : ℝ) * (rampErr (1 : DirichletCharacter ℂ 1) x).re = _
    simp
  rw [hG, rampErr, ite_eq_left rfl, add_re, sub_re, ofReal_re, ofReal_re, RampLaplace.rampSum, re_sum]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [h1, mul_one, ← ofReal_mul, ofReal_re]

/-- **The frontier for `ζ` alone**: for every `θ > 1/2`, on windows `[Y, Y^λ]` with `Y` arbitrarily large,
`Σ_{n ≤ x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ C x^θ`, for some `λ > 1` and `C`. -/
def ZetaWindowBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → ∃ lam : ℝ, 1 < lam ∧ ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Icc Y (Y ^ lam),
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1) - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x ≤
      C * x ^ θ

/-- **The Riemann hypothesis from the frontier for `ζ` alone.** -/
theorem riemannHypothesis_of_zetaWindowBound (h : ZetaWindowBound) : RiemannHypothesis := by
  refine HalfPlaneGRH.riemannHypothesis_of_zeta_ne_zero fun s hs => ?_
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero
  obtain ⟨lam, hlam, C, hW⟩ := h ((1 / 2 + s.re) / 2) (by linarith)
  have hθ0 : 0 < (1 / 2 + s.re) / 2 := by linarith
  have hne : LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 :=
    zetaFamily.zeroFree_of_windows hθ0 hlam (fun Y₀ => by
      obtain ⟨Y, hY, hYW⟩ := hW Y₀
      exact ⟨Y, hY, fun x hx => (zetaFamily_G x).trans_le (hYW x hx)⟩) () (by linarith) (Or.inr hs1)
  rwa [LFunction_modOne_eq] at hne

end WindowGRH

#print axioms WindowGRH.rhAndGRH_of_windowBound
#print axioms WindowGRH.riemannHypothesis_of_zetaWindowBound
