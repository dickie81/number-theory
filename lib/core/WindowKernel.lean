import Mathlib

/-!
# The kernel `uᵏ e^{−bu}/k!` and its tails

Real analysis for Landau's theorem on windows (`LandauWindow.lean`). The `k`-th Taylor coefficient of a Laplace
transform at a real point `σ` is the integral of the function against `uᵏ e^{−σu}/k!`, and for large `k` this
kernel lives near `u = k/σ`. A bound on the function in a window `[U, λU]`, with `k` chosen so that `k/σ` lies
inside it, controls the coefficient up to the kernel's tails outside the window.

* `kernel_integrableOn`, `kernel_integral`: `∫₀^∞ uᵏ e^{−bu} du / k! = b^{−(k+1)}`.
* `kernel_tails`: the Chernoff bound outside `[U, V]`, `e^{−tV}(b − t)^{−(k+1)} + e^{tU}(b + t)^{−(k+1)}` for
  `0 ≤ t < b`: past `V`, `e^{−bu} ≤ e^{−tV} e^{−(b−t)u}`, and before `U`, `e^{−bu} ≤ e^{tU} e^{−(b+t)u}`.
* `window_choice`: for a window ratio `λ > 1`, a growth exponent `a ≥ 0` and any `θ`, a point `σ ≥ a + 1` and a
  rate `E > max (σ − θ) 0` such that for every `U ≥ 1` some `k ≥ U` leaves at most `C E^{−k}` of the kernel
  `uᵏ e^{−(σ−a)u}/k!` outside `[U, λU]`. Put the kernel's peak `k/(σ − a)` at `mU` with `1 < m < λ`: the tails
  then decay at a rate `(σ − a)κ` with `κ > 1` fixed by `λ` and `m`, and `σ` large makes it exceed `σ − θ`.
-/

open Real MeasureTheory Set
open scoped Nat

namespace LandauWindow

/-- The kernel is integrable on `(0, ∞)`. -/
theorem kernel_integrableOn (k : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ k * exp (-(b * u))) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (s := k) (by linarith [k.cast_nonneg (α := ℝ)]) one_pos hb

/-- `∫₀^∞ uᵏ e^{−bu} du / k! = b^{−(k+1)}`. -/
theorem kernel_integral (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), u ^ k * exp (-(b * u)) / k ! = 1 / b ^ (k + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := k + 1) (by positivity) hb
  rw [Gamma_nat_eq_factorial, add_sub_cancel_right, ← Nat.cast_add_one, rpow_natCast] at h
  simp_rw [rpow_natCast] at h
  rw [integral_div, h, mul_div_cancel_right₀ _ (by positivity), one_div_pow]

/-- **Chernoff's bound** for the kernel outside the window `[U, V]`. -/
theorem kernel_tails (k : ℕ) {b t U V : ℝ} (ht : 0 ≤ t) (htb : t < b) :
    ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * exp (-(b * u)) / k ! ≤
      exp (-(t * V)) / (b - t) ^ (k + 1) + exp (t * U) / (b + t) ^ (k + 1) := by
  have hi : ∀ c : ℝ, 0 < c → IntegrableOn (fun u : ℝ => u ^ k * exp (-(c * u)) / k !) (Ioi 0) :=
    fun c hc => (kernel_integrableOn k hc).div_const _
  have hbt : 0 < b - t := sub_pos.mpr htb
  have hbt' : 0 < b + t := by linarith
  have hg := IntegrableOn.fun_add ((hi _ hbt).mul_const (exp (-(t * V)))) ((hi _ hbt').mul_const (exp (t * U)))
  have hS : Ioi 0 \ Icc U V ⊆ Ioi (0 : ℝ) := sdiff_subset
  calc _ ≤ ∫ u in Ioi (0 : ℝ) \ Icc U V, (u ^ k * exp (-((b - t) * u)) / k ! * exp (-(t * V)) +
          u ^ k * exp (-((b + t) * u)) / k ! * exp (t * U)) := by
        refine setIntegral_mono_on ((hi b (by linarith)).mono_set hS) (hg.mono_set hS)
          (measurableSet_Ioi.diff measurableSet_Icc) fun u hu => ?_
        simp only [mem_sdiff, mem_Ioi, mem_Icc, not_and_or, not_le] at hu
        have key : exp (-(b * u)) ≤
            exp (-((b - t) * u)) * exp (-(t * V)) + exp (-((b + t) * u)) * exp (t * U) := by
          rw [← exp_add, ← exp_add]
          rcases hu.2 with h | h
          · exact (exp_le_exp.mpr (by nlinarith)).trans (le_add_of_nonneg_left (exp_pos _).le)
          · exact (exp_le_exp.mpr (by nlinarith)).trans (le_add_of_nonneg_right (exp_pos _).le)
        have := hu.1
        calc _ ≤ u ^ k * (exp (-((b - t) * u)) * exp (-(t * V)) + exp (-((b + t) * u)) * exp (t * U)) / k ! := by
              gcongr
          _ = _ := by ring
    _ ≤ ∫ u in Ioi (0 : ℝ), (u ^ k * exp (-((b - t) * u)) / k ! * exp (-(t * V)) +
          u ^ k * exp (-((b + t) * u)) / k ! * exp (t * U)) :=
        setIntegral_mono_set hg (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => by positivity)
          hS.eventuallyLE
    _ = _ := by
        rw [integral_add ((hi _ hbt).mul_const _) ((hi _ hbt').mul_const _), integral_mul_const,
          integral_mul_const, kernel_integral k hbt, kernel_integral k hbt']
        ring

/-- One term `e^w / B^{K+1}` of Chernoff's bound decays at the rate `E`: if `w ≤ w₀ + K y` and `E ≤ B (1 − y)`,
then `e^y E ≤ B`, and the term is at most `e^{w₀} / B / E^K`. -/
lemma tail_term_le {w w₀ y B E : ℝ} {K : ℕ} (hB : 0 < B) (hE : 0 < E) (hw : w ≤ w₀ + K * y)
    (hy : E ≤ B * (1 - y)) : exp w / B ^ (K + 1) ≤ exp w₀ / B / E ^ K := by
  have hyE : exp y * E ≤ B := by
    calc exp y * E ≤ exp y * (B * exp (-y)) := by
          gcongr; exact hy.trans (by gcongr; linarith [add_one_le_exp (-y)])
      _ = B := by rw [mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc exp w * (B * E ^ K) ≤ exp (w₀ + K * y) * (B * E ^ K) := by gcongr
    _ = exp w₀ * B * (exp y * E) ^ K := by rw [exp_add, exp_nat_mul]; ring
    _ ≤ exp w₀ * B * B ^ K := by gcongr
    _ = exp w₀ * B ^ (K + 1) := by ring

/-- **The choice of `σ` and `k`**: for every window `[U, λU]`, a `k ≥ U` that leaves at most `C E^{−k}` of the
kernel `uᵏ e^{−(σ−a)u}/k!` outside the window, with `E > σ − θ`. -/
theorem window_choice {a θ lam : ℝ} (ha : 0 ≤ a) (hlam : 1 < lam) :
    ∃ σ : ℝ, a + 1 ≤ σ ∧ 1 < σ ∧ ∃ E : ℝ, 0 < E ∧ σ - θ < E ∧ ∃ C : ℝ, ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧
      ∫ u in Ioi (0 : ℝ) \ Icc U (lam * U), u ^ k * exp (-((σ - a) * u)) / k ! ≤ C / E ^ k := by
  -- `δ = (λ − 1)/(λ + 1)`, so that `λ(1 − δ) = 1 + δ`
  obtain ⟨δ, hδ0, hδ1, hδl⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ lam * (1 - δ) = 1 + δ := by
    have h : 0 < lam + 1 := by linarith
    exact ⟨(lam - 1) / (lam + 1), div_pos (by linarith) h, (div_lt_one h).mpr (by linarith), by field_simp; ring⟩
  -- `b = σ − a`, large enough that the rate `E = b (1 + δ²/8)` exceeds `σ − θ`
  obtain ⟨b, hb1, hbθ⟩ : ∃ b : ℝ, 1 < b ∧ a - θ < b * δ ^ 2 / 8 := by
    refine ⟨8 * (|a - θ| + 1) / δ ^ 2, ?_, ?_⟩
    · rw [lt_div_iff₀ (by positivity)]; nlinarith [abs_nonneg (a - θ)]
    · rw [div_mul_cancel₀ _ (by positivity)]; linarith [le_abs_self (a - θ)]
  -- Chernoff's `t = bδ/4`, and `x = t/c` for `k ≈ cU` with `c = b/(1 − δ)`: the peak `k/b` at `(1 + λ)U/2`
  obtain ⟨t, x, ht, hx, hxt, htb, hlo, hhi⟩ : ∃ t x : ℝ, 0 ≤ t ∧ 0 < x ∧ x ≤ t ∧ t < b ∧
      b * (1 + δ ^ 2 / 8) ≤ (b + t) * (1 - x) ∧ b * (1 + δ ^ 2 / 8) ≤ (b - t) * (1 - -(x * lam)) := by
    have h1 : 0 < 1 - δ := by linarith
    have h2 : 0 ≤ b * δ ^ 2 := by positivity
    refine ⟨b * δ / 4, δ * (1 - δ) / 4, by positivity, by positivity, by nlinarith, by nlinarith,
      by nlinarith [mul_nonneg h2 (by linarith : 0 ≤ 1 + δ)], ?_⟩
    rw [show δ * (1 - δ) / 4 * lam = δ * (1 + δ) / 4 by linear_combination δ / 4 * hδl]
    nlinarith [mul_nonneg h2 h1.le]
  refine ⟨a + b, by linarith, by linarith, b * (1 + δ ^ 2 / 8), by positivity, by linarith,
    exp (x * lam) / (b - t) + exp 0 / (b + t), fun U hU => ?_⟩
  -- `k = ⌈tU/x⌉`, so that `tU ≤ kx < tU + x`
  have hK := (div_le_iff₀ hx).1 (Nat.le_ceil (t * U / x))
  have hK1 := (lt_div_iff₀ hx).1 (sub_lt_iff_lt_add.2 (Nat.ceil_lt_add_one (by positivity : 0 ≤ t * U / x)))
  refine ⟨⌈t * U / x⌉₊, le_of_mul_le_mul_right (by nlinarith) hx, ?_⟩
  rw [add_sub_cancel_left, add_div]
  refine (kernel_tails _ ht htb).trans (add_le_add (tail_term_le (by linarith) (by positivity) ?_ hhi)
    (tail_term_le (by linarith) (by positivity) (by linarith) hlo))
  nlinarith [mul_lt_mul_of_pos_right hK1 (by linarith : (0 : ℝ) < lam)]

end LandauWindow

#print axioms LandauWindow.kernel_integral
#print axioms LandauWindow.window_choice
