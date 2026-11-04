import Mathlib
import WeilZhuRed
import Roadmap
import DigammaGauss

/-! # Toward closing `ModePlancherel` at L = 1/2, and the Weil form on Legendre modes

* `ModePlancherel` is derived from two smaller inputs: `ModeDecay` (`|T̂ₙ(t)| ≤ Cₙ/(1+t)`) and `ModeOrth`
  (Plancherel orthonormality). Integrability of `T̂ₙT̂ₘ` and `Ψ_L T̂ₙT̂ₘ` on `(0,∞)` is proved from the decay, the
  continuity of `T̂ₙ` (parametric integral) and of `Ψ_L` (the stack's `differentiableOn_digamma`), and the
  growth bound `|Ψ_L(t)| ≤ 21√(1+t)` (the stack's `norm_digamma_le`).
* Even sector: the concrete Weil form is the repo's `WeilForm.weilQ (1/2)` on `f = Σ xᵢ T_{2i}`, where `T_n` is
  the normalised Legendre function built from Mathlib's `shiftedLegendre`. The prime sum is reduced to the
  single `n = 2` term (proved: the autocorrelation vanishes beyond `|u| > 1`). `weilQ = QF` is proved from three
  named identities (`EvenBridge`): the pole (Legendre–Bessel), archimedean (Zhu Lemma 2.5) and autocorrelation
  (Wiener–Khinchin) identities.
-/

namespace WeilPlanch

open Finset Real WeilTail WeilTailB WeilZhuRed MeasureTheory

/-! ## Continuity -/

theorem jP_cont (n : ℕ) : Continuous (jP n) := by
  unfold jP
  have : Continuous fun x : ℝ => ∫ t in (-1:ℝ)..1, Real.cos (x * t) * (1 - t ^ 2) ^ n :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  fun_prop

theorem That_cont (n : ℕ) : Continuous (That n) := by
  unfold That; have := jP_cont n; fun_prop

theorem Psi_cont : Continuous Psi := by
  have hpath : Continuous fun t : ℝ => (1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by fun_prop
  have hmem : ∀ t : ℝ, (1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I ∈ GammaIntegrals.U := by
    intro t; show 0 < ((1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).re; simp
  have hd := (GammaIntegrals.differentiableOn_digamma.continuousOn).comp_continuous hpath hmem
  unfold Psi
  exact ((Complex.continuous_re.comp hd).sub continuous_const).sub
    (continuous_const.mul (Real.continuous_cos.comp (continuous_id.mul continuous_const)))

/-! ## Growth of Ψ_L -/

theorem Psi_growth {t : ℝ} (h0 : 0 ≤ t) : |Psi t| ≤ 21 * Real.sqrt (1 + t) := by
  set z : ℂ := 1 / 4 + (t / 2 : ℝ) * Complex.I
  have hzre : z.re = 1 / 4 := by simp [z]
  have hz : 1 / 4 ≤ z.re := by rw [hzre]
  have hnz : ‖z‖ ≤ 1 / 4 + t / 2 := by
    refine (norm_add_le _ _).trans ?_
    have : ‖((1:ℂ) / 4)‖ = 1 / 4 := by norm_num
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hψ := WeilForm.norm_digamma_le hz
  have hs1 : 1 ≤ Real.sqrt (1 + t) := by
    exact Real.one_le_sqrt.2 (by linarith)
  have hsq : Real.sqrt (1 + ‖z‖) ≤ Real.sqrt 2 * Real.sqrt (1 + t) := by
    rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (by linarith)
  have s2 := sqrt2_le
  have hre : |(Complex.digamma z).re| ≤ 17 * Real.sqrt (1 + t) := by
    refine (Complex.abs_re_le_norm _).trans (hψ.trans ?_)
    nlinarith [Real.sqrt_nonneg (1 + t), Real.sqrt_nonneg 2]
  have hlogπ : |Real.log π| ≤ 1.39 := by
    have hπ := Real.pi_lt_d2; have hπ3 := Real.pi_gt_three
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    have : Real.log π ≤ Real.log 4 := Real.log_le_log (by positivity) (by linarith)
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  have hc : |Real.sqrt 2 * Real.log 2 * Real.cos (t * Real.log 2)| ≤ 0.99 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.log_nonneg (by norm_num)))]
    have := abs_cos_le_one (t * Real.log 2)
    have := Real.log_two_lt_d9
    have : Real.sqrt 2 * Real.log 2 ≤ 0.99 := by
      nlinarith [Real.sqrt_nonneg 2, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
    nlinarith [abs_nonneg (Real.cos (t * Real.log 2)), mul_nonneg (Real.sqrt_nonneg 2) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
  unfold Psi
  rw [abs_le] at hre hlogπ hc ⊢
  constructor <;> linarith [hre.1, hre.2, hlogπ.1, hlogπ.2, hc.1, hc.2]

/-! ## Integrability from decay -/

/-- **Named input (special functions)**: `|T̂ₙ(t)| ≤ Cₙ/(1+t)` on `t ≥ 0` (classical: `|jₙ(x)| = O(1/x)`). -/
def ModeDecay : Prop := ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |That n t| ≤ C / (1 + t)

/-- **Named input (functional analysis)**: `(1/π)∫₀^∞ T̂ₙT̂ₘ = δₙₘ` within a sector (Legendre–Fourier identity,
Legendre orthonormality on `[−1/2, 1/2]` and Plancherel). -/
def ModeOrth (par : ℕ) : Prop := ∀ i j, (1 / π) * ∫ t in Set.Ioi 0, G par i j t = if i = j then 1 else 0

lemma maj_int (K : ℝ) : IntegrableOn (fun t : ℝ => K * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) (Set.Ioi 0) :=
  ((integrable_one_add_norm (μ := volume) (E := ℝ) (by norm_num)).const_mul K).integrableOn

lemma rpow_facts {t : ℝ} (ht : 0 ≤ t) :
    1 / (1 + t) ^ 2 ≤ (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) ∧ Real.sqrt (1 + t) / (1 + t) ^ 2 = (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
  rw [Real.norm_eq_abs, abs_of_nonneg ht]
  have hs : 0 < 1 + t := by linarith
  have e : (1 + t) ^ (-(3 / 2 : ℝ)) = Real.sqrt (1 + t) / (1 + t) ^ 2 := by
    rw [Real.sqrt_eq_rpow, show (-(3 / 2 : ℝ)) = 1 / 2 - 2 by norm_num, Real.rpow_sub hs,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hs1 : 1 ≤ Real.sqrt (1 + t) := by
    exact Real.one_le_sqrt.2 (by linarith)
  refine ⟨?_, e.symm⟩
  rw [e]; exact div_le_div_of_nonneg_right hs1 (by positivity)

theorem modePlancherel_of (D : ModeDecay) (par : ℕ) (O : ModeOrth par) : ModePlancherel par := by
  have hG : ∀ i j, ∃ K, ∀ t : ℝ, 0 ≤ t → |G par i j t| ≤ K / (1 + t) ^ 2 ∧ 0 ≤ K := by
    intro i j
    obtain ⟨C1, hC1, h1⟩ := D (2 * i + par)
    obtain ⟨C2, hC2, h2⟩ := D (2 * j + par)
    refine ⟨C1 * C2, fun t ht => ⟨?_, mul_nonneg hC1 hC2⟩⟩
    unfold G; rw [abs_mul]
    calc |That (2 * i + par) t| * |That (2 * j + par) t| ≤ C1 / (1 + t) * (C2 / (1 + t)) :=
          mul_le_mul (h1 t ht) (h2 t ht) (abs_nonneg _) (div_nonneg hC1 (by linarith))
      _ = C1 * C2 / (1 + t) ^ 2 := by rw [div_mul_div_comm, sq]
  have hGc : ∀ i j, Continuous (G par i j) := fun i j => by
    unfold G; exact (That_cont _).mul (That_cont _)
  refine ⟨O, fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨K, hK⟩ := hG i j
    refine Integrable.mono' (maj_int K) (hGc i j).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_))
    obtain ⟨hb, hK0⟩ := hK t ht.le
    rw [Real.norm_eq_abs]
    refine hb.trans ?_
    have := (rpow_facts ht.le).1
    calc K / (1 + t) ^ 2 = K * (1 / (1 + t) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hK0
  · obtain ⟨K, hK⟩ := hG i j
    refine Integrable.mono' (maj_int (21 * K)) (Psi_cont.mul (hGc i j)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_))
    obtain ⟨hb, hK0⟩ := hK t ht.le
    rw [Real.norm_eq_abs, abs_mul]
    have hp := Psi_growth ht.le
    have e := (rpow_facts ht.le).2
    calc |Psi t| * |G par i j t| ≤ (21 * Real.sqrt (1 + t)) * (K / (1 + t) ^ 2) :=
          mul_le_mul hp hb (abs_nonneg _) (by positivity)
      _ = 21 * K * (Real.sqrt (1 + t) / (1 + t) ^ 2) := by ring
      _ = _ := by rw [e]

/-! ## Even sector: the repo's Weil form on Legendre modes -/

/-- Normalised Legendre function `T_n(u) = √(2n+1) P_n(2u)` on `[−1/2, 1/2]`, `P_n(x) = P̃_n((x+1)/2)`
with Mathlib's shifted Legendre polynomial `P̃_n`. -/
noncomputable def legT (n : ℕ) (u : ℝ) : ℝ :=
  if |u| ≤ 1 / 2 then Real.sqrt (2 * n + 1) * Polynomial.aeval (u + 1 / 2) (Polynomial.shiftedLegendre n) else 0

noncomputable def fx (N : ℕ) (x : ℕ → ℝ) (u : ℝ) : ℝ := ∑ i ∈ range N, x i * legT (2 * i) u

lemma fx_supp (N : ℕ) (x : ℕ → ℝ) {u : ℝ} (hu : 1 / 2 < |u|) : fx N x u = 0 := by
  unfold fx; refine sum_eq_zero (fun i _ => ?_); unfold legT; rw [ite_eq_right (by linarith)]; ring

lemma autocorr_supp (N : ℕ) (x : ℕ → ℝ) {u : ℝ} (hu : 1 < |u|) : WeilForm.autocorr (fx N x) u = 0 := by
  unfold WeilForm.autocorr
  have : ∀ t, fx N x t * fx N x (t + u) = 0 := by
    intro t
    by_cases ht : 1 / 2 < |t|
    · rw [fx_supp N x ht, zero_mul]
    · have : 1 / 2 < |t + u| := by
        have := abs_sub_abs_le_abs_sub u (-(t)); rw [abs_neg] at this
        have e : u - -t = t + u := by ring
        rw [e] at this; push Not at ht; linarith
      rw [fx_supp N x this, mul_zero]
  simp [this]

/-- **The prime sum at L = 1/2 is the single `n = 2` term** (proved). -/
theorem prime_sum_L05 (N : ℕ) (x : ℕ → ℝ) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * WeilForm.autocorr (fx N x) (Real.log n)
      = ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 * WeilForm.autocorr (fx N x) (Real.log 2) := by
  rw [tsum_eq_single (2:ℕ)]
  · push_cast; ring
  · intro n hn
    by_cases hl : ArithmeticFunction.vonMangoldt n = 0
    · simp [hl]
    · have h2 : 2 ≤ n := by
        rcases Nat.lt_or_ge n 2 with h' | h'
        · interval_cases n <;> simp at hl
        · exact h'
      have h3 : (3:ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have he := Real.exp_one_lt_d9
      have l3 : 1 < Real.log 3 := by rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith
      have := Real.log_le_log (by norm_num) h3
      have hpos : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
      rw [autocorr_supp N x (by rw [abs_of_nonneg hpos]; linarith), mul_zero]

/-- **Named inputs (even sector bridge)**, for `f = fx N x` and `F = Fx 0 N x`:
* `pole` (special functions): `∫ f e^{−u/2} = Σ xᵢ pᵢ` (Legendre–Bessel: `∫₋₁¹Pₙ(x)e^{ax}dx = 2iₙ(a)`).
* `arch` (Zhu analytic, Lemma 2.5): `(Re ψ(1/4) − log π)‖f‖² + ∫₀^∞[f⋆f(0) − f⋆f(u)]e^{u/2}/sinh u du
  = (1/π)∫₀^∞ (Re ψ(1/4 + it/2) − log π) F(t)² dt`.
* `acorr` (Fourier, Wiener–Khinchin): `f⋆f(log 2) = (1/π)∫₀^∞ cos(t log 2) F(t)² dt`. -/
structure EvenBridge : Prop where
  pole : ∀ N x, WeilForm.poleR (fx N x) (1 / 2) = ∑ i ∈ range N, x i * pole (2 * i + 0)
  arch : ∀ N x, ((Complex.digamma (1 / 4)).re - Real.log π) * WeilForm.normSq (fx N x)
      + (∫ u in Set.Ioi (0:ℝ), WeilForm.archIntegrand (fx N x) u)
      = (1 / π) * ∫ t in Set.Ioi 0, ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π) * Fx 0 N x t ^ 2
  acorr : ∀ N x, WeilForm.autocorr (fx N x) (Real.log 2) = (1 / π) * ∫ t in Set.Ioi 0, Real.cos (t * Real.log 2) * Fx 0 N x t ^ 2

/-- **`weilQ = QF`** on the even modes, from the bridge and the decay. -/
theorem weilQ_eq_QF (D : ModeDecay) (O : ModeOrth 0) (B : EvenBridge) (N : ℕ) (x : ℕ → ℝ) :
    WeilForm.weilQ (1 / 2) (fx N x) = QF 0 1 N x := by
  have P := modePlancherel_of D 0 O
  have hF2 := (expand_int 0 N x (fun _ => 1) (Set.Ioi 0) (fun i j => by simpa using P.int1 i j)).1
  have hPs := (expand_int 0 N x Psi (Set.Ioi 0) P.int2).1
  have hcos : IntegrableOn (fun t => Real.cos (t * Real.log 2) * Fx 0 N x t ^ 2) (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun t => Fx 0 N x t ^ 2) (Set.Ioi 0) := by simpa using hF2
    refine h1.bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _
  have hsplit : (∫ t in Set.Ioi 0, Psi t * Fx 0 N x t ^ 2)
      = (∫ t in Set.Ioi 0, ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π) * Fx 0 N x t ^ 2)
        - Real.sqrt 2 * Real.log 2 * ∫ t in Set.Ioi 0, Real.cos (t * Real.log 2) * Fx 0 N x t ^ 2 := by
    have e : (fun t => ((Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π) * Fx 0 N x t ^ 2)
        = fun t => Psi t * Fx 0 N x t ^ 2 + Real.sqrt 2 * Real.log 2 * (Real.cos (t * Real.log 2) * Fx 0 N x t ^ 2) := by
      funext t; unfold Psi; ring
    rw [e, integral_add hPs (hcos.const_mul _), integral_const_mul]; ring
  unfold WeilForm.weilQ QF
  rw [prime_sum_L05, B.pole, B.acorr]
  have ha := B.arch N x
  have hc := prime_coeff_L05
  set Ic := ∫ t in Set.Ioi 0, Real.cos (t * Real.log 2) * Fx 0 N x t ^ 2
  linear_combination ha - (1 / π) * hsplit - (1 / π) * Ic * hc

/-- **Final even-sector theorem, concrete Weil form.** For every `N ≥ 28` and nonzero `x`, the repo's Weil form
`weilQ (1/2)` is strictly positive on `f = Σ_{i<N} xᵢ T_{2i}`. Inputs: `EvenHead` (arb numerics), `ModeDecay`
(special functions), `ModeOrth 0` (functional analysis), `EvenBridge` (pole: special functions; arch: Zhu
analytic; acorr: Fourier). -/
theorem L05_even_weilQ (D : ModeDecay) (O : ModeOrth 0) (B : EvenBridge) (H : EvenHead) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < WeilForm.weilQ (1 / 2) (fx N x) := by
  rw [weilQ_eq_QF D O B N x]
  exact QF_even_pos (modePlancherel_of D 0 O) H N hN x hx

/-- **Final odd-sector theorem** (frequency form; the repo's `weilQ` covers even probes only). -/
theorem L05_odd_QF (D : ModeDecay) (O : ModeOrth 1) (H : OddHead) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < QF 1 (-1) N x :=
  QF_odd_pos (modePlancherel_of D 1 O) H N hN x hx

end WeilPlanch
