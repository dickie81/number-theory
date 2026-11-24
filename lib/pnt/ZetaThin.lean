import Mathlib
import ZetaFrame
import D2Tail
import HalfPlaneFinal
import PsiExplicit

/-!
# The thin scales for `ζ` — CONDITIONAL on the half-plane

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, "The analytic inputs"): once `x` is
large, every setting is thin at `X = (Nx)^{log x}` (`Setting.Thin`), so the frontier after step 4 loses that input
(`ZetaTwistBound`).

**CONDITIONAL.** The results here use the half-plane `Re s > 11/12` for `ζ` and every Dirichlet `L`-function
(`Eis.LFunction_ne_zero_of_re_gt`), an input formalised in the library that no referee has read (see
`formalisations/openai-half-plane.md`), through `HalfPlanePNT.psi_isBigO_eleven_twelfths`,
`ChiUniform.psiChi_le_uniform` and `GSTail.logDeriv_one_tail`. Lean checks them with the standard axioms only, but
they are only as good as that input, and must be cited as conditional on it.

* `norm_rampErr_le`: for `0 < η < 1/24`, the error `g_χ = WindowGRH.rampErr χ` satisfies
  `‖g_χ(y)‖ ≤ C log(N + 2) y^{11/12+2η}` for every primitive `χ` mod `N` and `y > 1`.
  - For `χ ≠ 1`, `g_χ(y) = y(L′/L(1, χ) + Σ_{n≤y} χ(n)Λ(n)/n) − ψ(y, χ)`: `GSTail.logDeriv_one_tail` and
    `ChiUniform.psiChi_le_uniform`.
  - For `χ = 1`, so `N = 1`, `g_1(y) = y(Σ_{n≤y} Λ(n)/n − log y + γ) − (ψ(y) − y)`.
* `mertens_error_le`, Mertens' theorem with a power saving: `Σ_{n≤y} Λ(n)/n = log y − γ + O(y^{2η−1/12})`. It is
  `GSTail.tail_le_of_sum_le` for `Λ − 1`. Its `L`-series `−ζ′/ζ(s) − ζ(s) = −ζ₁′/ζ₁(s) − ζ₀(s)` is continuous at `1`,
  with value `−2γ` (Mathlib's `riemannZeta₁` and `riemannZeta₀`), and its partial sums `ψ(t) − ⌊t⌋` are
  `O(t^{11/12+η})` (`PsiExplicit.abs_psi_sub_le`). Then `H_n = log n + γ + O(1/n)` for the harmonic numbers.
* `Setting.norm_g_le`: `‖g_χ(y)‖ ≤ C log(N + 2) y^{23/24}` in every setting, from `η = 1/48`, as the conductor of
  `D_χ` divides `N`.
* `thin_of_large`: for `x` large, every setting is thin at `(Nx)^{log x}`, with `θ = 1/(8|A|x²)`. Here `|A| ≤ N`,
  `log(N + 2) ≤ 2N` and `y^{1/24} ≥ (Nx)^{(log x)/24} ≥ 16C(Nx)²`.
* `riemannHypothesis_of_zetaTwistBound`: the Riemann hypothesis from `ZetaTwistBound`, the frontier after step 4 with
  the thin scales proved.
-/

open Complex ArithmeticFunction Finset

namespace ZetaBalance

/-- **CONDITIONAL. Mertens' theorem with a power saving** (conditional on the half-plane, through
`PsiExplicit.abs_psi_sub_le`): for `0 < η < 1/24` there is `C ≥ 0` with `|Σ_{n≤y} Λ(n)/n − log y + γ| ≤ C y^{2η−1/12}`
for every `y > 1`. -/
theorem mertens_error_le {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 < y →
      |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / n - Real.log y + Real.eulerMascheroniConstant| ≤ C * y ^ (2 * η - 1 / 12) := by
  obtain ⟨C₀, hC₀, hψ⟩ := PsiExplicit.abs_psi_sub_le hη
  refine ⟨4 * (C₀ + 1) / η + 2, by positivity, fun y hy => ?_⟩
  set γ := Real.eulerMascheroniConstant
  set Y := ⌊y⌋₊
  have hy0 : 0 < y := by linarith
  -- `L(Λ − 1, s) = −ζ′/ζ(s) − ζ(s) = −ζ₁′/ζ₁(s) − ζ₀(s)` for `Re s > 1`, continuous at `1`
  have hz1 : riemannZeta₁ 1 ≠ 0 := by rw [riemannZeta₁_one]; exact one_ne_zero
  have h := GSTail.tail_le_of_sum_le (a := fun n => (Λ n : ℂ) - 1)
    (F := fun s => -(deriv riemannZeta₁ s / riemannZeta₁ s) - riemannZeta₀ s) (θ := 11 / 12 + η) (K := C₀ + 1)
    (by linarith) hη (by linarith)
    (fun σ hσ => (LSeriesSummable_vonMangoldt (by simpa using hσ)).sub
      (LSeriesSummable_one_iff.2 (by simpa using hσ)))
    (fun σ hσ => by
      have hs : 1 < (σ : ℂ).re := by simpa using hσ
      have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.ne'
      calc LSeries (fun n => (Λ n : ℂ) - 1) σ = LSeries (fun n => (Λ n : ℂ)) σ - LSeries 1 σ :=
            LSeries_sub (LSeriesSummable_vonMangoldt hs) (LSeriesSummable_one_iff.2 hs)
        _ = _ := by
            rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries_one_eq_riemannZeta hs, ← logDeriv_apply,
              WindowGRH.logDeriv_riemannZeta₁ hs1 (riemannZeta_ne_zero_of_one_lt_re hs),
              riemannZeta_eq_inv_sub_add hs1]
            ring)
    ((((differentiable_riemannZeta₁.analyticAt 1).deriv.continuousAt.div
      differentiable_riemannZeta₁.continuous.continuousAt hz1).neg).sub
      differentiable_riemannZeta₀.continuous.continuousAt)
    (fun t ht => by
      -- the partial sums are `ψ(t) − ⌊t⌋`
      have e : ∑ n ∈ Icc 1 ⌊t⌋₊, ((Λ n : ℂ) - 1) = ((Chebyshev.psi t - ⌊t⌋₊ : ℝ) : ℂ) := by
        rw [sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, Chebyshev.psi,
          ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
        push_cast
        simp
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hψ t ht.le
      have h2 := Nat.floor_le (by linarith : 0 ≤ t)
      have h3 := Nat.lt_floor_add_one t
      have h4 : 1 ≤ t ^ (11 / 12 + η) := Real.one_le_rpow ht.le (by linarith)
      rw [abs_le] at h1 ⊢
      constructor <;> nlinarith)
    hy
  -- the value at `1` is `−2γ`
  have hH : (harmonic Y : ℝ) = ∑ n ∈ Icc 1 Y, 1 / (n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp [one_div]
  have e : -(deriv riemannZeta₁ 1 / riemannZeta₁ 1) - riemannZeta₀ 1 -
      ∑ n ∈ Icc 1 Y, ((Λ n : ℂ) - 1) / n = ((-2 * γ - (∑ n ∈ Icc 1 Y, Λ n / n - harmonic Y) : ℝ) : ℂ) := by
    rw [deriv_riemannZeta₁_one, riemannZeta₁_one, riemannZeta₀_one, hH]
    push_cast
    simp only [sub_div, sum_sub_distrib]
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, show 11 / 12 + η + η - 1 = 2 * η - 1 / 12 by ring] at h
  -- the harmonic numbers: `|H_Y − log y − γ| ≤ 1/Y ≤ 2y^{2η−1/12}`
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast Nat.le_floor (by simpa using hy.le)
  have hY0 : (0 : ℝ) < Y := by linarith
  have hγ1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant Y
  have hγ2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' Y
  rw [Real.eulerMascheroniSeq] at hγ1
  rw [Real.eulerMascheroniSeq', ite_eq_right (by rintro h; simp [h] at hY0)] at hγ2
  have hYy : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyY : y < Y + 1 := Nat.lt_floor_add_one y
  have hl1 : Real.log Y ≤ Real.log y := Real.log_le_log hY0 hYy
  have hl2 : Real.log y ≤ Real.log (Y + 1) := Real.log_le_log hy0 hyY.le
  have hl3 : Real.log (Y + 1) - Real.log Y ≤ 1 / Y := by
    rw [← Real.log_div (by positivity) hY0.ne']
    calc Real.log (((Y : ℝ) + 1) / Y) ≤ ((Y : ℝ) + 1) / Y - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / Y := by rw [add_div, div_self hY0.ne']; ring
  have hl4 : 1 / (Y : ℝ) ≤ 2 * y ^ (2 * η - 1 / 12) := by
    calc 1 / (Y : ℝ) ≤ 2 / y := by rw [div_le_div_iff₀ hY0 hy0]; linarith
      _ = 2 * y ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; ring
      _ ≤ 2 * y ^ (2 * η - 1 / 12) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy.le (by linarith)) (by norm_num)
  rw [add_mul]
  rw [abs_le] at h ⊢
  constructor <;> linarith

/-- **CONDITIONAL. The error of a primitive character's ramp sum** (conditional on the half-plane, through
`GSTail.logDeriv_one_tail`, `ChiUniform.psiChi_le_uniform`, `mertens_error_le` and `PsiExplicit.abs_psi_sub_le`): for
`0 < η < 1/24` there is `C ≥ 0` with `‖g_χ(y)‖ ≤ C log(N + 2) y^{11/12+2η}` for every primitive `χ` mod every `N` and
every `y > 1`. -/
theorem norm_rampErr_le {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ y : ℝ, 1 < y →
      ‖WindowGRH.rampErr χ y‖ ≤ C * Real.log (N + 2) * y ^ (11 / 12 + 2 * η) := by
  obtain ⟨C₁, hC₁, hT⟩ := GSTail.logDeriv_one_tail hη hη'
  obtain ⟨C₂, hC₂, hψχ⟩ := ChiUniform.psiChi_le_uniform hη
  obtain ⟨C₃, hC₃, hM⟩ := mertens_error_le hη hη'
  obtain ⟨C₄, hC₄, hψ⟩ := PsiExplicit.abs_psi_sub_le hη
  refine ⟨C₁ + C₂ + C₃ + C₄, by positivity, fun N _ χ hχ y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hL : 1 ≤ Real.log (N + 2) := by
    have : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (NeZero.pos N)
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9]
  have hy1 : y * y ^ (2 * η - 1 / 12) = y ^ (11 / 12 + 2 * η) := by
    rw [show (11 / 12 + 2 * η : ℝ) = 1 + (2 * η - 1 / 12) by ring, Real.rpow_add hy0, Real.rpow_one]
  have hy2 : y ^ (11 / 12 + η) ≤ y ^ (11 / 12 + 2 * η) := Real.rpow_le_rpow_of_exponent_le hy.le (by linarith)
  have hP : 0 ≤ y ^ (11 / 12 + 2 * η) := by positivity
  by_cases h1 : χ = 1
  · -- `χ = 1` is primitive only mod `1`, and `g_1(y) = y(Σ_{n≤y} Λ(n)/n − log y + γ) − (ψ(y) − y)`
    have hN : N = 1 := by
      have := (DirichletCharacter.isPrimitive_def χ).1 hχ
      rw [h1, DirichletCharacter.conductor_one] at this
      exact this.symm
    subst hN h1
    have e : WindowGRH.rampErr (1 : DirichletCharacter ℂ 1) y = ((y * (∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / n - Real.log y +
        Real.eulerMascheroniConstant) - (Chebyshev.psi y - y) : ℝ) : ℂ) := by
      have hs : ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (y / n - 1) = y * ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / n - Chebyshev.psi y := by
        rw [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc, zero_add, mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun n _ => by ring
      have hs' := congrArg (fun r : ℝ => (r : ℂ)) hs
      rw [WindowGRH.rampErr, ite_eq_left rfl, RampLaplace.rampSum]
      simp only [fun n : ℕ => (MulChar.one_apply (isUnit_of_subsingleton _) : (1 : DirichletCharacter ℂ 1) n = 1),
        mul_one]
      push_cast at hs' ⊢
      linear_combination hs'
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ y * |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / n - Real.log y + Real.eulerMascheroniConstant| +
          |Chebyshev.psi y - y| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_pos hy0]
      _ ≤ y * (C₃ * y ^ (2 * η - 1 / 12)) + C₄ * y ^ (11 / 12 + η) := by
          gcongr
          exacts [hM y hy, hψ y hy.le]
      _ = C₃ * y ^ (11 / 12 + 2 * η) + C₄ * y ^ (11 / 12 + η) := by rw [← hy1]; ring
      _ ≤ _ := by
          nlinarith [mul_le_mul_of_nonneg_left hy2 hC₄, mul_nonneg (add_nonneg hC₁ hC₂) hP,
            mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ (C₃ + C₄) * y ^ (11 / 12 + 2 * η)),
            mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ (C₁ + C₂) * y ^ (11 / 12 + 2 * η))]
  · -- `g_χ(y) = y(L′/L(1, χ) + Σ_{n≤y} χ(n)Λ(n)/n) − ψ(y, χ)`
    have e : WindowGRH.rampErr χ y = y * (deriv (DirichletCharacter.LFunction χ) 1 /
        DirichletCharacter.LFunction χ 1 + ∑ n ∈ Icc 1 ⌊y⌋₊, χ n * (Λ n : ℂ) / n) - ChiPNT.psiChi χ y := by
      have hs : RampLaplace.rampSum (fun n => χ n) y =
          y * ∑ n ∈ Icc 1 ⌊y⌋₊, χ n * (Λ n : ℂ) / n - ChiPNT.psiChi χ y := by
        rw [RampLaplace.rampSum, ChiPNT.psiChi, mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun n _ => ?_
        push_cast
        ring
      rw [WindowGRH.rampErr, ite_eq_right h1, hs, logDeriv_apply]
      ring
    have hL0 : 0 ≤ Real.log (N + 2) := by linarith
    rw [e]
    calc _ ≤ y * ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 +
          ∑ n ∈ Icc 1 ⌊y⌋₊, χ n * (Λ n : ℂ) / n‖ + ‖ChiPNT.psiChi χ y‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0.le]
      _ ≤ y * (C₁ * Real.log (N + 2) * y ^ (2 * η - 1 / 12)) +
          C₂ * Real.log (N + 2) * y ^ (11 / 12 + η) := by
          gcongr
          exacts [hT N χ h1 y hy, hψχ N χ h1 y hy]
      _ = C₁ * Real.log (N + 2) * y ^ (11 / 12 + 2 * η) + C₂ * Real.log (N + 2) * y ^ (11 / 12 + η) := by
          rw [← hy1]
          ring
      _ ≤ _ := by
          nlinarith [mul_le_mul_of_nonneg_left hy2 (mul_nonneg hC₂ hL0),
            mul_nonneg (mul_nonneg (add_nonneg hC₃ hC₄) hL0) hP]

/-- **CONDITIONAL. The errors of a setting** (conditional on the half-plane, through `norm_rampErr_le` at
`η = 1/48`): there is `C ≥ 0` with `‖g_χ(y)‖ ≤ C log(N + 2) y^{23/24}` for every setting, every `χ` and every
`y > 1`. The conductor of `D_χ` divides `N`. -/
theorem Setting.norm_g_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Setting) (χ : Dual S.A) (y : ℝ), 1 < y →
    ‖S.g χ y‖ ≤ C * Real.log (S.N + 2) * y ^ (23 / 24 : ℝ) := by
  obtain ⟨C, hC, h⟩ := norm_rampErr_le (η := 1 / 48) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun S χ y hy => ?_⟩
  have h' := h _ (S.D χ).primitiveCharacter (S.D χ).primitiveCharacter_isPrimitive y hy
  rw [show (11 / 12 + 2 * (1 / 48) : ℝ) = 23 / 24 by norm_num] at h'
  refine h'.trans ?_
  gcongr
  exact Nat.le_of_dvd (NeZero.pos _) (S.D χ).conductor_dvd_level

/-- **CONDITIONAL. The thin scales** (conditional on the half-plane, through `Setting.norm_g_le`): there is `x₀` such
that for `x ≥ x₀` every setting is thin at `(Nx)^{log x}`, with `θ = 1/(8|A|x²)`. -/
theorem thin_of_large : ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ S : Setting, S.Thin x (((S.N : ℝ) * x) ^ Real.log x) := by
  obtain ⟨C, hC, hg⟩ := Setting.norm_g_le
  refine ⟨max (Real.exp 72) (16 * C + 1), fun x hx S => ?_⟩
  have hx1 : 16 * C + 1 ≤ x := (le_max_right _ _).trans hx
  have hxe : 1 < x := (Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 72)).trans_le ((le_max_left _ _).trans hx)
  have hlog : 72 ≤ Real.log x := (Real.le_log_iff_exp_le (by linarith)).2 ((le_max_left _ _).trans hx)
  have hN : (1 : ℝ) ≤ S.N := Nat.one_le_cast.2 (NeZero.pos S.N)
  set u := (S.N : ℝ) * x with hu
  have hxu : x ≤ u := le_mul_of_one_le_left (by linarith) hN
  -- `|A| ≤ N` and `log(N + 2) ≤ 2N`
  have hA : (Fintype.card S.A : ℝ) ≤ S.N := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast (Nat.card_le_card_of_surjective _ S.mkA_surjective).trans <|
      (Nat.card_le_card_of_injective _ Units.val_injective).trans <|
        (Nat.card_zmod _).le.trans (Nat.le_of_dvd (NeZero.pos _) S.QS_dvd_N)
  have hL : Real.log (S.N + 2) ≤ 2 * S.N := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < S.N + 2)]
  have hL0 : 0 ≤ Real.log (S.N + 2) := Real.log_nonneg (by linarith)
  have hD : 0 < 8 * (Fintype.card S.A : ℝ) * x ^ 2 :=
    mul_pos (mul_pos (by norm_num) (Nat.cast_pos.2 Fintype.card_pos)) (by positivity)
  refine ⟨(8 * Fintype.card S.A * x ^ 2)⁻¹, fun χ y hy => ?_, (mul_inv_cancel₀ hD.ne').le⟩
  have hy1 : 1 < y := (Real.one_lt_rpow (by linarith) (by linarith)).trans_le hy
  have hy0 : 0 < y := by linarith
  -- `8|A|x²·C log(N + 2) ≤ 16C u² ≤ u³ ≤ u^{(log x)/24} ≤ y^{1/24}`
  have key : 8 * Fintype.card S.A * x ^ 2 * (C * Real.log (S.N + 2)) ≤ y ^ (1 / 24 : ℝ) := by
    calc _ ≤ 8 * S.N * x ^ 2 * (C * (2 * S.N)) :=
          mul_le_mul (by gcongr) (mul_le_mul_of_nonneg_left hL hC) (mul_nonneg hC hL0) (by positivity)
      _ = 16 * C * u ^ 2 := by rw [hu]; ring
      _ ≤ x * u ^ 2 := by gcongr; linarith
      _ ≤ u ^ (3 : ℝ) := by
          rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
          nlinarith [sq_nonneg u]
      _ ≤ u ^ (Real.log x / 24) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (u ^ Real.log x) ^ (1 / 24 : ℝ) := by rw [← Real.rpow_mul (by linarith)]; ring_nf
      _ ≤ y ^ (1 / 24 : ℝ) := Real.rpow_le_rpow (Real.rpow_pos_of_pos (by linarith) _).le hy (by norm_num)
  calc ‖S.g χ y‖ ≤ C * Real.log (S.N + 2) * y ^ (23 / 24 : ℝ) := hg S χ y hy1
    _ ≤ (8 * Fintype.card S.A * x ^ 2)⁻¹ * y := by
        rw [← div_eq_inv_mul, le_div_iff₀ hD]
        calc C * Real.log (S.N + 2) * y ^ (23 / 24 : ℝ) * (8 * Fintype.card S.A * x ^ 2)
            = 8 * Fintype.card S.A * x ^ 2 * (C * Real.log (S.N + 2)) * y ^ (23 / 24 : ℝ) := by ring
          _ ≤ y ^ (1 / 24 : ℝ) * y ^ (23 / 24 : ℝ) := by gcongr
          _ = y := by rw [← Real.rpow_add hy0]; norm_num

/-- **The frontier for `ζ` with the thin scales proved**: for every `ε > 0`, at every `x` of windows `[Y, Y^λ]` with
`Y` arbitrarily large, a setting with small twists and lattice data whose thin classes lie beyond `(Nx)^{log x}`. -/
def ZetaTwistBound : Prop :=
  ∀ ε > 0, ∃ lam > (1 : ℝ), ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ x ∈ Set.Icc Y (Y ^ lam),
    ∃ S : Setting, S.Twists 1 x ε ∧ Nonempty (LatticeData S 1 x ε (((S.N : ℝ) * x) ^ Real.log x))

/-- **CONDITIONAL. The Riemann hypothesis from lattice data with small twists** (conditional on the half-plane
`Re s > 11/12`, through `thin_of_large`): the frontier after step 4, with the thin scales proved. -/
theorem riemannHypothesis_of_zetaTwistBound (h : ZetaTwistBound) : RiemannHypothesis := by
  obtain ⟨x₀, hx₀⟩ := thin_of_large
  refine riemannHypothesis_of_zetaLatticeBound fun ε hε => ?_
  obtain ⟨lam, hlam, hY⟩ := h ε hε
  refine ⟨lam, hlam, fun Y₀ => ?_⟩
  obtain ⟨Y, hY₀, hx⟩ := hY (max Y₀ x₀)
  refine ⟨Y, (le_max_left _ _).trans hY₀, fun x hxY => ?_⟩
  obtain ⟨S, htw, hD⟩ := hx x hxY
  exact ⟨S, _, hx₀ x ((le_max_right _ _).trans (hY₀.trans hxY.1)) S, htw, hD⟩

end ZetaBalance

#print axioms ZetaBalance.mertens_error_le
#print axioms ZetaBalance.norm_rampErr_le
#print axioms ZetaBalance.thin_of_large
#print axioms ZetaBalance.riemannHypothesis_of_zetaTwistBound
