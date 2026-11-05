import Mathlib
import BallSharp

/-! # The upper bound for the rate: the mean value from above, and the alternating vector

Plain statement. Under RH, for every `N ≥ 1`, every `r ≥ 8N` and every real `x` on `[1, N]`, with `c_n = x_n√n`,
`Σ_{|γ_ρ| ≤ r}|V_x(ρ)|² ≤ (πr/4)((log(r/2π) + 1/5 + 22/π)Σc_n² − L(c)) + 46(Σ_j|c_j|√j)(Σ_j|c_j|/√j)`
(`upper_mean`), where `V_x(s) = Σ_{n ≤ N}x_n n^s` and `L(c) = 2Σ_{n ≤ N}Λ(n)n^{−1/2}Σ_{jn ≤ N}c_j c_{jn}` is Landau's
form. At the alternating vector `x_n = (−1)^{n+1}/n` (`xa`) Landau's form is `(log N)² + O(H_N)`, with
`H_N = Σ_{j ≤ N}1/j`, and this turns the `log r` of the diagonal into `log(r/N)`:
`Σ_{|γ| ≤ r}|V_x(ρ)|² ≤ ((πr/4)(log(r/N) + 12) + 46N)H_N` (`mean_xa_le`). Summed over dyadic shells against
`Q_N(x) = Σ_ρ|V_x(ρ)|²/(¼ + γ²)`, given `|V_x(ρ)|² ≤ 400/N` at the zeros of height `|γ| ≤ 2N`, it gives
`Q_N(x) ≤ (400K_H(1) + 45)H_N/N` (`form_xa_le`). `BallUpperEta` proves the hypothesis on the low zeros from PNT+'s `ζ₀`,
and concludes `λ_N ≤ 67(1 + log N)/N` under RH, and `λ_N ≪ log N/N` unconditionally.

The proof is `BallSharp`'s with the inequalities reversed, and three changes.

- **The test function** is `|D(t)|²M_r(t)` with `BallCutoff`'s majorant `M_r(t) = (r/t)²sin²(πt/2r) ≥ 1_{[−r, r]}`,
  whose transform `(πr²/2)(π/r − |v|)⁺` is supported in `|v| ≤ π/r ≤ 1/(2N)`. So the diagonal `(π²r/2)Σc_n²` and the
  prime side `(πr/4)L(c)` are exact (`integral_hRM`, `prime_eq_M`).
- **Stirling from above, for every `t`**: `Re ψ(¼ + it/2) ≤ ½log(81/16 + t²/4) + 1/50` (`psiRe_le_all`), so the
  archimedean weight is at most `log(r/2π) + 1/5 + log⁺(|t|/r)` (`psiRe_sub_le`). The excess
  `M_r(t)log(|t|/r) ≤ r²log(|t|/r)/t²` on `|t| > r` is dominated by `BallSharp`'s envelope smoothed by the Fejér
  kernel of `a = 1/(2N)`, now on the windows `|u| ≤ r/2` (`tail_conv_le_U`), and its `|D|²`-mass is exact
  (`BallSharp.integral_Kc_conv`).
- **Landau's form from below at the alternating vector** (`landau_xa_ge`): `c_j c_{jn} = (−1)^{j+jn}/(j√n)` is
  `1/(j√n)` for odd `n`, and the even `n` with `Λ(n) ≠ 0` are the powers of `2`, so with `Σ_{n ∣ m}Λ(n) = log m`,
  `L(c) ≥ 2Σ_{m ≤ N}(log m)/m − 4H_N log 2 ≥ (log N)² − 2 − 4H_N log 2`.

`tail_le`, used by `BallUpperEta`, is the alternating tail by Abel summation: for `Re s = ½` and `|Im s| ≤ 2N`,
`|Σ_{N < n ≤ N + M}(−1)^{n+1}n^{−s}| ≤ 20/√N` for every `M`.
-/

open Real Complex Finset MeasureTheory WeilForm WeilTest DirMean BallDensity ShortWeil BallCutoff BallSharp
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace BallUpper

/-! ## The alternating tail, by Abel summation -/

/-- `u_n = (−1)^{n+1}e^{−s log n}`. -/
def ua (s : ℂ) (n : ℕ) : ℂ := (-1) ^ (n + 1) * cexp (-(s * Real.log n))

/-- `ℓ_n = log(n + 1) − log n`. -/
def ell (n : ℕ) : ℝ := Real.log ((n : ℝ) + 1) - Real.log n

/-- The ratio `τ_n = u_{n+1}/(−u_n) = e^{−sℓ_n}`. -/
def tau (s : ℂ) (n : ℕ) : ℂ := cexp (-(s * (ell n : ℂ)))

/-- `d_n = 1/(1 + τ_n)`. -/
def dd (s : ℂ) (n : ℕ) : ℂ := 1 / (1 + tau s n)

lemma ua_succ (s : ℂ) (n : ℕ) : ua s (n + 1) = -(tau s n * ua s n) := by
  unfold ua tau
  have e : cexp (-(s * ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ))) =
      cexp (-(s * (ell n : ℂ))) * cexp (-(s * (Real.log n : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; unfold ell; push_cast; ring
  rw [e]; ring

lemma norm_cexp_neg_mul_log {s : ℂ} (hs : s.re = 1 / 2) {x : ℝ} (hx : 0 < x) :
    ‖cexp (-(s * Real.log x))‖ = 1 / Real.sqrt x := by
  rw [Complex.norm_exp]
  have e : (-(s * (Real.log x : ℂ))).re = -(Real.log x / 2) := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hs, mul_zero, sub_zero]
    ring
  rw [e, Real.exp_neg, BallPsi.exp_log_half hx, one_div]

lemma norm_ua {s : ℂ} (hs : s.re = 1 / 2) {n : ℕ} (hn : 1 ≤ n) : ‖ua s n‖ = 1 / Real.sqrt n := by
  unfold ua
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_cexp_neg_mul_log hs (by exact_mod_cast (show 0 < n by omega))

lemma ell_pos {n : ℕ} (hn : 1 ≤ n) : 0 < ell n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have := Real.log_lt_log hn0 (show (n : ℝ) < n + 1 by linarith)
  unfold ell; linarith

lemma ell_le {n : ℕ} (hn : 1 ≤ n) : ell n ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold ell
  rw [← Real.log_div (by positivity) hn0.ne']
  have h := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
  rw [div_sub_one hn0.ne'] at h
  calc Real.log (((n : ℝ) + 1) / n) ≤ ((n : ℝ) + 1 - n) / n := h
    _ = 1 / n := by ring

lemma ell_sub_le {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ell n - ell (n + 1) ∧ ell n - ell (n + 1) ≤ 1 / ((n : ℝ) * (n + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have e : ell n - ell (n + 1) = Real.log (((n : ℝ) + 1) ^ 2 / (n * ((n : ℝ) + 1 + 1))) := by
    unfold ell
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  have hy : 1 ≤ ((n : ℝ) + 1) ^ 2 / (n * ((n : ℝ) + 1 + 1)) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  refine ⟨Real.log_nonneg hy, ?_⟩
  have h1 := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) ^ 2 / (n * ((n : ℝ) + 1 + 1)) by positivity)
  have h2 : ((n : ℝ) + 1) ^ 2 / (n * ((n : ℝ) + 1 + 1)) - 1 ≤ 1 / ((n : ℝ) * (n + 1)) := by
    rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

lemma cos_ge_neg_half {θ : ℝ} (hθ : |θ| ≤ 2) : -(1 / 2) ≤ Real.cos θ := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := θ / 2)
  have h2 : (θ / 2) ^ 2 ≤ 1 := by
    have h3 : |θ / 2| ≤ 1 := by rw [abs_div, abs_two]; linarith
    nlinarith [abs_nonneg (θ / 2), sq_abs (θ / 2)]
  have h3 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; congr 1; ring
  have hc : 1 / 2 ≤ Real.cos (θ / 2) := by linarith
  nlinarith

lemma re_tau_ge {s : ℂ} (hs : s.re = 1 / 2) {n : ℕ} (hn : 1 ≤ n) (h2 : |s.im| * (1 / n) ≤ 2) :
    -(1 / 2) ≤ (tau s n).re := by
  have hℓ0 := ell_pos hn
  have hℓ1 := ell_le hn
  unfold tau
  rw [Complex.exp_re]
  have hre : (-(s * (ell n : ℂ))).re = -(ell n / 2) := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hs, mul_zero, sub_zero]
    ring
  have him : (-(s * (ell n : ℂ))).im = -(s.im * ell n) := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [hre, him, Real.cos_neg]
  have hθ : |s.im * ell n| ≤ 2 := by
    rw [abs_mul, abs_of_pos hℓ0]
    calc |s.im| * ell n ≤ |s.im| * (1 / n) := mul_le_mul_of_nonneg_left hℓ1 (abs_nonneg _)
      _ ≤ 2 := h2
  have hc := cos_ge_neg_half hθ
  have he0 : 0 < Real.exp (-(ell n / 2)) := Real.exp_pos _
  have he1 : Real.exp (-(ell n / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rcases le_or_gt 0 (Real.cos (s.im * ell n)) with h | h
  · nlinarith
  · nlinarith

lemma norm_one_add_tau_ge {s : ℂ} (hs : s.re = 1 / 2) {n : ℕ} (hn : 1 ≤ n) (h2 : |s.im| * (1 / n) ≤ 2) :
    1 / 2 ≤ ‖1 + tau s n‖ := by
  have h := re_tau_ge hs hn h2
  have h3 : (1 + tau s n).re ≤ ‖1 + tau s n‖ := Complex.re_le_norm _
  rw [Complex.add_re, Complex.one_re] at h3
  linarith

lemma norm_dd_le {s : ℂ} (hs : s.re = 1 / 2) {n : ℕ} (hn : 1 ≤ n) (h2 : |s.im| * (1 / n) ≤ 2) :
    ‖dd s n‖ ≤ 2 := by
  have h := norm_one_add_tau_ge hs hn h2
  unfold dd
  rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
  linarith

lemma norm_tau_sub_le {s : ℂ} (hs : s.re = 1 / 2) {n : ℕ} (hn : 1 ≤ n)
    (h1 : ‖s‖ * (1 / ((n : ℝ) * (n + 1))) ≤ 1) :
    ‖tau s n - tau s (n + 1)‖ ≤ 2 * ‖s‖ * (1 / ((n : ℝ) * (n + 1))) := by
  obtain ⟨d0, d1⟩ := ell_sub_le hn
  have e1 : -(s * (ell n : ℂ)) = -(s * (ell (n + 1) : ℂ)) + -(s * ((ell n - ell (n + 1) : ℝ) : ℂ)) := by
    push_cast; ring
  have e : tau s n - tau s (n + 1) = tau s (n + 1) * (cexp (-(s * ((ell n - ell (n + 1) : ℝ) : ℂ))) - 1) := by
    unfold tau; rw [e1, Complex.exp_add]; ring
  rw [e, norm_mul]
  have ht : ‖tau s (n + 1)‖ ≤ 1 := by
    have hl := ell_pos (n := n + 1) (by omega)
    unfold tau
    rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.2 ?_
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hs, mul_zero, sub_zero]
    linarith
  have hw : ‖-(s * ((ell n - ell (n + 1) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg d0]
    calc ‖s‖ * (ell n - ell (n + 1)) ≤ ‖s‖ * (1 / ((n : ℝ) * (n + 1))) :=
          mul_le_mul_of_nonneg_left d1 (norm_nonneg _)
      _ ≤ 1 := h1
  have hexp := Complex.norm_exp_sub_one_le hw
  rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg d0] at hexp
  have hd2 : ‖s‖ * (ell n - ell (n + 1)) ≤ ‖s‖ * (1 / ((n : ℝ) * (n + 1))) :=
    mul_le_mul_of_nonneg_left d1 (norm_nonneg _)
  calc ‖tau s (n + 1)‖ * ‖cexp (-(s * ((ell n - ell (n + 1) : ℝ) : ℂ))) - 1‖
      ≤ 1 * (2 * (‖s‖ * (ell n - ell (n + 1)))) := mul_le_mul ht hexp (norm_nonneg _) zero_le_one
    _ ≤ 2 * ‖s‖ * (1 / ((n : ℝ) * (n + 1))) := by linarith

lemma norm_dd_sub_le {s : ℂ} (hs : s.re = 1 / 2) {n : ℕ} (hn : 1 ≤ n) (h2 : |s.im| * (1 / n) ≤ 2)
    (h2' : |s.im| * (1 / ((n : ℝ) + 1)) ≤ 2) (h1 : ‖s‖ * (1 / ((n : ℝ) * (n + 1))) ≤ 1) :
    ‖dd s (n + 1) - dd s n‖ ≤ 8 * ‖s‖ * (1 / ((n : ℝ) * (n + 1))) := by
  have ha := norm_one_add_tau_ge hs hn h2
  have hb := norm_one_add_tau_ge hs (n := n + 1) (by omega) (by push_cast; exact h2')
  have ha0 : 1 + tau s n ≠ 0 := by intro h; rw [h, norm_zero] at ha; linarith
  have hb0 : 1 + tau s (n + 1) ≠ 0 := by intro h; rw [h, norm_zero] at hb; linarith
  have e : dd s (n + 1) - dd s n = (tau s n - tau s (n + 1)) / ((1 + tau s n) * (1 + tau s (n + 1))) := by
    unfold dd; field_simp; ring
  rw [e, norm_div, norm_mul]
  have ht := norm_tau_sub_le hs hn h1
  have hab : 1 / 4 ≤ ‖1 + tau s n‖ * ‖1 + tau s (n + 1)‖ := by nlinarith
  rw [div_le_iff₀ (by nlinarith)]
  have h0 : 0 ≤ 2 * ‖s‖ * (1 / ((n : ℝ) * (n + 1))) := by positivity
  nlinarith

/-- **The alternating tail by Abel summation**: for `Re s = ½` and `|Im s| ≤ 2N`,
`|Σ_{N < n ≤ N + M}(−1)^{n+1}n^{−s}| ≤ 20/√N`, uniformly in `M`. With `τ_n = e^{−s(log(n+1) − log n)}` and
`d_n = 1/(1 + τ_n)`, `u_n = (u_n d_n − u_{n+1}d_{n+1}) + u_{n+1}(d_{n+1} − d_n)`: the phase `Im s·ℓ_n` stays in
`[−2, 2]`, so `Re τ_n ≥ −½` and `|d_n| ≤ 2`, and `|d_{n+1} − d_n| ≤ 8|s|/(n(n + 1))`. -/
lemma tail_le {s : ℂ} (hs : s.re = 1 / 2) {N : ℕ} (hN : 1 ≤ N) (him : |s.im| ≤ 2 * N) (M : ℕ) :
    ‖∑ i ∈ range M, ua s (N + 1 + i)‖ ≤ 20 / Real.sqrt N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsn : ‖s‖ ≤ 1 / 2 + 2 * N := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [hs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    linarith
  have c2 : ∀ n : ℕ, N + 1 ≤ n → |s.im| * (1 / (n : ℝ)) ≤ 2 := by
    intro n hn
    have hn' : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    rw [mul_one_div, div_le_iff₀ (by linarith)]
    linarith
  have c1 : ∀ n : ℕ, N + 1 ≤ n → ‖s‖ * (1 / ((n : ℝ) * (n + 1))) ≤ 1 := by
    intro n hn
    have hn' : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    rw [mul_one_div, div_le_one (by positivity)]
    nlinarith
  have hsqle : ∀ n : ℕ, N ≤ n → 1 / Real.sqrt n ≤ 1 / Real.sqrt N := fun n hn =>
    one_div_le_one_div_of_le hsq (Real.sqrt_le_sqrt (by exact_mod_cast hn))
  have key : ∀ n : ℕ, N + 1 ≤ n → ua s n = (ua s n * dd s n - ua s (n + 1) * dd s (n + 1)) +
      ua s (n + 1) * (dd s (n + 1) - dd s n) := by
    intro n hn
    have ha := norm_one_add_tau_ge hs (n := n) (by omega) (c2 n hn)
    have h0 : 1 + tau s n ≠ 0 := by intro h; rw [h, norm_zero] at ha; linarith
    have hd : dd s n * (1 + tau s n) = 1 := by unfold dd; field_simp
    rw [ua_succ s n]
    linear_combination (-(ua s n)) * hd
  have hw : ∀ n : ℕ, N + 1 ≤ n → ‖ua s n * dd s n‖ ≤ 2 / Real.sqrt N := by
    intro n hn
    rw [norm_mul, norm_ua hs (by omega)]
    have hd := norm_dd_le hs (n := n) (by omega) (c2 n hn)
    calc 1 / Real.sqrt n * ‖dd s n‖ ≤ 1 / Real.sqrt N * 2 :=
          mul_le_mul (hsqle n (by omega)) hd (norm_nonneg _) (by positivity)
      _ = 2 / Real.sqrt N := by ring
  set f : ℕ → ℂ := fun i => ua s (N + 1 + i) * dd s (N + 1 + i) with hf
  set fN : ℕ → ℝ := fun i => 1 / ((N + 1 + i : ℕ) : ℝ) with hfN
  have ht : ∑ i ∈ range M, (f i - f (i + 1)) = f 0 - f M := Finset.sum_range_sub' f M
  have htN : ∑ i ∈ range M, (fN i - fN (i + 1)) = fN 0 - fN M := Finset.sum_range_sub' fN M
  have hsum : ∑ i ∈ range M, ua s (N + 1 + i) = ∑ i ∈ range M, (f i - f (i + 1)) +
      ∑ i ∈ range M, ua s (N + 1 + i + 1) * (dd s (N + 1 + i + 1) - dd s (N + 1 + i)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (key (N + 1 + i) (by omega)).trans ?_
    simp only [hf, ← add_assoc]
  have hg : ∀ i ∈ range M, ‖ua s (N + 1 + i + 1) * (dd s (N + 1 + i + 1) - dd s (N + 1 + i))‖ ≤
      8 * ‖s‖ / Real.sqrt N * (fN i - fN (i + 1)) := by
    intro i _
    have hn1 : N + 1 ≤ N + 1 + i := by omega
    have hnR : (N : ℝ) + 1 ≤ ((N + 1 + i : ℕ) : ℝ) := by exact_mod_cast hn1
    rw [norm_mul, norm_ua hs (by omega)]
    have hdd := norm_dd_sub_le hs (n := N + 1 + i) (by omega) (c2 _ hn1)
      (by have := c2 (N + 1 + i + 1) (by omega); push_cast at this ⊢; exact this) (c1 _ hn1)
    have e : fN i - fN (i + 1) = 1 / (((N + 1 + i : ℕ) : ℝ) * (((N + 1 + i : ℕ) : ℝ) + 1)) := by
      simp only [hfN]
      have h1 : (0 : ℝ) < ((N + 1 + i : ℕ) : ℝ) := by linarith
      rw [show ((N + 1 + (i + 1) : ℕ) : ℝ) = ((N + 1 + i : ℕ) : ℝ) + 1 by push_cast; ring]
      field_simp
      ring
    rw [e]
    calc 1 / Real.sqrt ((N + 1 + i + 1 : ℕ) : ℝ) * ‖dd s (N + 1 + i + 1) - dd s (N + 1 + i)‖
        ≤ 1 / Real.sqrt N * (8 * ‖s‖ * (1 / (((N + 1 + i : ℕ) : ℝ) * (((N + 1 + i : ℕ) : ℝ) + 1)))) :=
          mul_le_mul (hsqle _ (by omega)) hdd (norm_nonneg _) (by positivity)
      _ = 8 * ‖s‖ / Real.sqrt N * (1 / (((N + 1 + i : ℕ) : ℝ) * (((N + 1 + i : ℕ) : ℝ) + 1))) := by ring
  have hG : ‖∑ i ∈ range M, ua s (N + 1 + i + 1) * (dd s (N + 1 + i + 1) - dd s (N + 1 + i))‖ ≤
      16 / Real.sqrt N := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hg).trans ?_)
    rw [← Finset.mul_sum, htN]
    have hf0 : fN 0 = 1 / ((N : ℝ) + 1) := by simp only [hfN]; push_cast; ring
    have hfM : 0 ≤ fN M := by simp only [hfN]; positivity
    rw [hf0]
    have h8 : 8 * ‖s‖ * (1 / ((N : ℝ) + 1)) ≤ 16 := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      linarith
    calc 8 * ‖s‖ / Real.sqrt N * (1 / ((N : ℝ) + 1) - fN M) ≤ 8 * ‖s‖ / Real.sqrt N * (1 / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 8 * ‖s‖ * (1 / ((N : ℝ) + 1)) / Real.sqrt N := by ring
      _ ≤ 16 / Real.sqrt N := div_le_div_of_nonneg_right h8 hsq.le
  rw [hsum, ht]
  have h0 : ‖f 0‖ ≤ 2 / Real.sqrt N := by simp only [hf, add_zero]; exact hw _ le_rfl
  have hM : ‖f M‖ ≤ 2 / Real.sqrt N := by simp only [hf]; exact hw _ (by omega)
  calc ‖f 0 - f M + ∑ i ∈ range M, ua s (N + 1 + i + 1) * (dd s (N + 1 + i + 1) - dd s (N + 1 + i))‖
      ≤ ‖f 0‖ + ‖f M‖ + 16 / Real.sqrt N := by
        refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) hG)
    _ ≤ 2 / Real.sqrt N + 2 / Real.sqrt N + 16 / Real.sqrt N := by linarith
    _ = 20 / Real.sqrt N := by ring

/-! ## The alternating vector -/

/-- The test vector `x_n = (−1)^{n+1}/n`. -/
def xa (n : ℕ) : ℝ := (-1) ^ (n + 1) / n

/-- Its Dirichlet polynomial at a zero is the alternating sum at `1 − ρ`:
`V_x(ρ) = Σ_{n ≤ N}(−1)^{n+1}n^{−(1−ρ)}`. -/
lemma dpoly_xa (N : ℕ) (q : ZIdx) :
    BallRate.dpoly N xa q = ∑ n ∈ Icc 1 N, ua (1 - zetaZeroFamily q) n := by
  unfold BallRate.dpoly
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
  unfold xa ua BallLattice.pw
  have e1 : cexp (-((1 - zetaZeroFamily q) * (Real.log n : ℂ))) =
      cexp (zetaZeroFamily q * (Real.log n : ℂ)) * cexp (-(Real.log n : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : cexp (-(Real.log n : ℂ)) = ((n : ℂ))⁻¹ := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hn0]; simp
  rw [e1, e2]
  push_cast
  ring

/-! ## The majorant `M_r` as a test function -/

/-- `‖ĝ_box(z)‖² ≤ 16e^{2a}/(1 + (Re z)²)` on the strip `|Im z| ≤ 1`, for `0 < a ≤ 1`. -/
lemma norm_sq_ghatC_bx_le {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {z : ℂ} (him : |z.im| ≤ 1) :
    ‖ghatC (bx a) a z‖ ^ 2 ≤ 16 * Real.exp (2 * a) / (1 + z.re ^ 2) := by
  have hq0 : 0 < 1 + a * ‖z‖ := by have := mul_nonneg ha0.le (norm_nonneg z); linarith
  have hg : ‖ghatC (bx a) a z‖ ≤ 4 * a * Real.exp a / (1 + a * ‖z‖) := by
    refine (norm_ghatC_bx_le' a ha0.le z).trans (div_le_div_of_nonneg_right ?_ hq0.le)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_of_le_one_right ha0.le him)) (by linarith)
  have hre : a ^ 2 * (1 + z.re ^ 2) ≤ (1 + a * ‖z‖) ^ 2 := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h2 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hb2 : a ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm_nonneg z, mul_nonneg ha0.le (norm_nonneg z)]
  have he : Real.exp (2 * a) = Real.exp a ^ 2 := by rw [two_mul, Real.exp_add, sq]
  have hpos : 0 < 1 + z.re ^ 2 := by positivity
  have h1 : ‖ghatC (bx a) a z‖ ^ 2 ≤ (4 * a * Real.exp a / (1 + a * ‖z‖)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hg 2
  have h3 : (4 * a * Real.exp a / (1 + a * ‖z‖)) ^ 2 ≤ 16 * Real.exp (2 * a) / (1 + z.re ^ 2) := by
    rw [div_pow, he, div_le_div_iff₀ (pow_pos hq0 2) hpos]
    have hE : 0 ≤ 16 * Real.exp a ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hre hE]
  linarith

/-- The entire extension of the majorant `M_r = (r²/4)ĝ²` of `1_{[−r, r]}`, with the box of width `π/2r`. -/
def majC (r : ℝ) (z : ℂ) : ℂ := ((r ^ 2 / 4 : ℝ) : ℂ) * ghatC (bx (π / (2 * r))) (π / (2 * r)) z ^ 2

lemma majC_ofReal {r : ℝ} (hr : 0 < r) (t : ℝ) : majC r t = (majR r t : ℂ) := by
  unfold majC majR hsq
  rw [ghatC_real (esupp_bx _) (div_nonneg Real.pi_pos.le (by linarith)) t]
  push_cast
  ring

lemma majC_even (r : ℝ) (z : ℂ) : majC r (-z) = majC r z := by
  unfold majC
  rw [ghatC_even (esupp_bx _).even]

lemma differentiable_majC (r : ℝ) : Differentiable ℂ (majC r) := by
  have d0 : Differentiable ℂ (ghatC (bx (π / (2 * r))) (π / (2 * r))) :=
    ghatC_differentiable (esupp_bx _).integrable.intervalIntegrable
  unfold majC
  fun_prop

/-- **The strip bound**: `‖M_r(z)‖ ≤ 4r²e^{π/r}/(1 + (Re z)²)` on `|Im z| ≤ 1`, for `r ≥ π/2`. -/
lemma norm_majC_le {r : ℝ} (hr : π / 2 ≤ r) {z : ℂ} (hz : z ∈ WeilStrip.strip (-1) 1) :
    ‖majC r z‖ ≤ 4 * r ^ 2 * Real.exp (2 * (π / (2 * r))) / (1 + z.re ^ 2) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have ha0 : 0 < π / (2 * r) := div_pos Real.pi_pos (by linarith)
  have ha1 : π / (2 * r) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h := norm_sq_ghatC_bx_le ha0 ha1 (z := z) (abs_le.2 ⟨hz.1, hz.2⟩)
  unfold majC
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc r ^ 2 / 4 * ‖ghatC (bx (π / (2 * r))) (π / (2 * r)) z‖ ^ 2
      ≤ r ^ 2 / 4 * (16 * Real.exp (2 * (π / (2 * r))) / (1 + z.re ^ 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 4 * r ^ 2 * Real.exp (2 * (π / (2 * r))) / (1 + z.re ^ 2) := by ring

/-- `h(z) = D(z)D(−z)M_r(z)`. -/
def htM (N : ℕ) (c : ℕ → ℝ) (r : ℝ) (z : ℂ) : ℂ := DC N c z * DC N c (-z) * majC r z

/-- `h` on `ℝ`: `|D(t)|²M_r(t)`. -/
def hRM (N : ℕ) (c : ℕ → ℝ) (r t : ℝ) : ℝ := Kc N c t * majR r t

lemma htM_ofReal {r : ℝ} (hr : 0 < r) (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : htM N c r t = (hRM N c r t : ℂ) := by
  unfold htM hRM
  rw [DC_ofReal, DC_neg_ofReal, majC_ofReal hr, Kc_eq]
  push_cast
  linear_combination (-(Bc N c t : ℂ) ^ 2 * (majR r t : ℂ)) * Complex.I_sq

lemma htM_even (N : ℕ) (c : ℕ → ℝ) (r : ℝ) (z : ℂ) : htM N c r (-z) = htM N c r z := by
  unfold htM; rw [neg_neg, majC_even]; ring

lemma striptest_htM {r : ℝ} (hr : π / 2 ≤ r) (N : ℕ) (c : ℕ → ℝ) :
    WeilStrip.StripTest (htM N c r) ((N * S1 N c) ^ 2 * (4 * r ^ 2 * Real.exp (2 * (π / (2 * r))))) := by
  refine ⟨(((differentiable_DC N c).mul ((differentiable_DC N c).comp differentiable_neg)).mul
    (differentiable_majC r)).differentiableOn, fun t ht => ?_⟩
  have him : |t.im| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  have h1 := norm_DC_le N c him
  have h2 := norm_DC_le N c (z := -t) (by rwa [Complex.neg_im, abs_neg])
  have h3 := norm_majC_le hr ht
  have hS := S1_nonneg N c
  unfold htM
  rw [norm_mul, norm_mul]
  calc ‖DC N c t‖ * ‖DC N c (-t)‖ * ‖majC r t‖ ≤ (N * S1 N c) * (N * S1 N c) *
        (4 * r ^ 2 * Real.exp (2 * (π / (2 * r))) / (1 + t.re ^ 2)) := by gcongr
    _ = (N * S1 N c) ^ 2 * (4 * r ^ 2 * Real.exp (2 * (π / (2 * r)))) / (1 + t.re ^ 2) := by ring

/-- **Weil's explicit formula for `|D|²M_r`** (`weilExplicit_zeta`, no RH input). -/
lemma weil_htM {r : ℝ} (hr : π / 2 ≤ r) (N : ℕ) (c : ℕ → ℝ) :
    WeilExplicit zetaZeroFamily (htM N c r) (hRM N c r) :=
  weilExplicit_zeta (striptest_htM hr N c) (htM_even N c r)
    (htM_ofReal (lt_of_lt_of_le (by positivity) hr) N c)

/-! ## The diagonal and the prime side, exactly -/

lemma mhat_eq_zero {r v : ℝ} (hv : π / r ≤ |v|) : mhat r v = 0 := by
  unfold mhat; rw [max_eq_right (by linarith)]; ring

lemma mhat_zero {r : ℝ} (hr : 0 < r) : mhat r 0 = π ^ 2 * r / 2 := by
  unfold mhat
  rw [abs_zero, sub_zero, max_eq_left (by positivity)]
  field_simp

lemma gh_hRM {r : ℝ} (hr : 0 < r) (N : ℕ) (c : ℕ → ℝ) (u : ℝ) :
    gh (hRM N c r) u = 1 / (2 * π) *
      ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * mhat r (Real.log j' - Real.log j - u) := by
  unfold gh hRM
  rw [integral_Kc_mul_cos N c (integrable_majR_cos hr) (integral_majR_cos hr), sum_symm_of_even N c (mhat_neg r)]

/-- **Exactness**: for `r ≥ 2πN` only the exact matches `j' = jn` survive. -/
lemma sum_mhat_exact {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 1 ≤ N) (hrN : 2 * π * N ≤ r) (c : ℕ → ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, c j * c j' * mhat r (Real.log j' - Real.log j - Real.log n) =
      mhat r 0 * ex N c n := by
  rw [← sum_exact N c hn (mhat r 0)]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsep : π / r ≤ 1 / (2 * N) := by
    rw [div_le_div_iff₀ hr (by positivity)]; linarith
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  congr 1
  by_cases h : j * n = j'
  · rw [ite_eq_left h, ← h, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      show Real.log j + Real.log n - Real.log j - Real.log n = 0 by ring]
  · rw [ite_eq_right h]
    apply mhat_eq_zero
    have hsep' := sep_log hj hj' hn h
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at hsep'
    rw [show Real.log j' - Real.log j - Real.log n = -(Real.log j + Real.log n - Real.log j') by ring, abs_neg]
    linarith

/-- **The diagonal**: `∫|D|²M_r = (π²r/2)Σc_n²` for `r ≥ 2πN`. -/
lemma integral_hRM {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 1 ≤ N) (hrN : 2 * π * N ≤ r) (c : ℕ → ℝ) :
    ∫ t, hRM N c r t = mhat r 0 * S2 N c := by
  have h := integral_Kc_mul_cos N c (integrable_majR_cos hr) (integral_majR_cos hr) 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [sum_symm_of_even N c (mhat_neg r) 0] at h
  have hx := sum_mhat_exact hr hN hrN c (n := 1) le_rfl
  rw [ex_one] at hx
  simp only [Nat.cast_one, Real.log_one, sub_zero] at hx h
  unfold hRM
  rw [h, hx]

lemma gh_hRM_log {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 1 ≤ N) (hrN : 2 * π * N ≤ r) (c : ℕ → ℝ) {n : ℕ}
    (hn : 1 ≤ n) : gh (hRM N c r) (Real.log n) = mhat r 0 / (2 * π) * ex N c n := by
  rw [gh_hRM hr, sum_mhat_exact hr hN hrN c hn]; ring

/-- **The prime side is Landau's form**, exactly, for `r ≥ 2πN`. -/
lemma prime_eq_M {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 1 ≤ N) (hrN : 2 * π * N ≤ r) (c : ℕ → ℝ) :
    2 * ∑' n : ℕ, Λ n / Real.sqrt n * gh (hRM N c r) (Real.log n) =
      mhat r 0 / (2 * π) * (2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n) := by
  have h0 : ∀ n ∉ Icc 1 N, Λ n / Real.sqrt n * gh (hRM N c r) (Real.log n) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have : N < n := by
        by_contra h
        push Not at h
        exact hn (Finset.mem_Icc.2 ⟨hn0, h⟩)
      rw [gh_hRM_log hr hN hrN c hn0, ex_eq_zero N c this, mul_zero, mul_zero]
  rw [tsum_eq_sum h0]
  have e : ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * gh (hRM N c r) (Real.log n) =
      mhat r 0 / (2 * π) * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [gh_hRM_log hr hN hrN c (Finset.mem_Icc.1 hn).1]; ring
  rw [e]
  ring

/-! ## The archimedean term from above -/

/-- **Stirling from above, for every `t`**: `Re ψ(¼ + it/2) ≤ ½log(81/16 + t²/4) + 1/50`. -/
lemma psiRe_le_all (t : ℝ) : psiRe t ≤ Real.log (81 / 16 + t ^ 2 / 4) / 2 + 1 / 50 := by
  have hq := DigammaStirling.re_digamma_quarter 2 (t / 2)
  have e : psiRe t = (Complex.digamma (1 / 4 + ((t / 2 : ℝ) : ℂ) * Complex.I)).re := by
    unfold psiRe; rw [zB_eq]
  rw [← e, psiApx2_eq] at hq
  have herr : (1 : ℝ) / (120 * (((2 : ℕ) : ℝ) + 1 / 4) ^ 4) ≤ 1 / 3000 := by norm_num
  have hrt : (9 / 4 : ℝ) ^ 2 + (t / 2) ^ 2 = 81 / 16 + t ^ 2 / 4 := by ring
  rw [hrt] at hq
  have hr0 : 81 / 16 ≤ 81 / 16 + t ^ 2 / 4 := by nlinarith [sq_nonneg t]
  have hrpos : 0 < 81 / 16 + t ^ 2 / 4 := by linarith
  have hb2 : (t / 2) ^ 2 ≤ 81 / 16 + t ^ 2 / 4 := by nlinarith
  have t1 : 0 ≤ 9 / 4 / (2 * (81 / 16 + t ^ 2 / 4)) := by positivity
  have t2 : -(((9 / 4 : ℝ) ^ 2 - (t / 2) ^ 2) / (12 * (81 / 16 + t ^ 2 / 4) ^ 2)) ≤ 4 / 243 := by
    have h1 : -(((9 / 4 : ℝ) ^ 2 - (t / 2) ^ 2) / (12 * (81 / 16 + t ^ 2 / 4) ^ 2)) ≤
        (81 / 16 + t ^ 2 / 4) / (12 * (81 / 16 + t ^ 2 / 4) ^ 2) := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have h2 : (81 / 16 + t ^ 2 / 4) / (12 * (81 / 16 + t ^ 2 / 4) ^ 2) = 1 / (12 * (81 / 16 + t ^ 2 / 4)) := by
      field_simp
    have h3 : 1 / (12 * (81 / 16 + t ^ 2 / 4)) ≤ 4 / 243 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have t3 : 0 ≤ 1 / 4 / ((1 / 4 : ℝ) ^ 2 + (t / 2) ^ 2) + 5 / 4 / ((5 / 4 : ℝ) ^ 2 + (t / 2) ^ 2) := by
    positivity
  have hq' := (abs_le.1 hq).2
  linarith

/-- `Re ψ(¼ + it/2) − log π ≤ log(max(|t|, r)/2π) + 1/5` for `r ≥ 8`. -/
lemma psiRe_sub_le {r : ℝ} (hr : 8 ≤ r) (t : ℝ) :
    psiRe t - Real.log π ≤ Real.log (max |t| r / (2 * π)) + 1 / 5 := by
  have hm8 : 8 ≤ max |t| r := le_trans hr (le_max_right _ _)
  have hmt : |t| ≤ max |t| r := le_max_left _ _
  have hm0 : 0 < max |t| r := by linarith
  have h1 := psiRe_le_all t
  have ht2 : t ^ 2 ≤ max |t| r ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have hA : 81 / 16 + t ^ 2 / 4 ≤ (max |t| r / 2) ^ 2 * (337 / 256) := by
    nlinarith [mul_le_mul hm8 hm8 (by norm_num) hm0.le]
  have hm2 : 0 < max |t| r / 2 := by linarith
  have hlog : Real.log (81 / 16 + t ^ 2 / 4) ≤ 2 * Real.log (max |t| r / 2) + 81 / 256 := by
    calc Real.log (81 / 16 + t ^ 2 / 4) ≤ Real.log ((max |t| r / 2) ^ 2 * (337 / 256)) :=
          Real.log_le_log (by positivity) hA
      _ = 2 * Real.log (max |t| r / 2) + Real.log (337 / 256) := by
          rw [Real.log_mul (pow_pos hm2 2).ne' (by norm_num), Real.log_pow]; push_cast; ring
      _ ≤ 2 * Real.log (max |t| r / 2) + 81 / 256 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 337 / 256 by norm_num)
          linarith
  have e : Real.log (max |t| r / (2 * π)) = Real.log (max |t| r / 2) - Real.log π := by
    rw [← div_div, Real.log_div hm2.ne' Real.pi_ne_zero]
  rw [e]
  linarith

lemma majR_le_sq {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : t ≠ 0) : majR r t ≤ r ^ 2 / t ^ 2 := by
  unfold majR
  rw [hsq_bx_eq (div_nonneg Real.pi_pos.le (by linarith)) ht]
  have hs := Real.sin_sq_le_one (π / (2 * r) * t)
  have ht2 : 0 < t ^ 2 := by positivity
  calc r ^ 2 / 4 * (4 * Real.sin (π / (2 * r) * t) ^ 2 / t ^ 2)
      = r ^ 2 * Real.sin (π / (2 * r) * t) ^ 2 / t ^ 2 := by ring
    _ ≤ r ^ 2 * 1 / t ^ 2 := by gcongr
    _ = r ^ 2 / t ^ 2 := by ring

/-- The smoothed tail envelope `(E ⋆ F_a)(t)` with the window `δ = r/2`, `a = 1/(2N)`. -/
def EcU (N : ℕ) (r t : ℝ) : ℝ :=
  ∫ u, envT ((r + r / 2) ^ 2 / 729) (r - r / 2) (t - u) * fej (1 / (2 * N)) u

lemma EcU_nonneg {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : 0 < r) (t : ℝ) : 0 ≤ EcU N r t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact integral_nonneg fun u => mul_nonneg (envT_nonneg (by positivity) (by linarith) _)
    (fej_nonneg (by positivity) u)

/-- **The smoothed envelope dominates the tail weight**: for `|t| > r ≥ 8N`,
`(1 − 1/π)·r²(log(|t|/r) + c₁)/(729t²) ≤ (E ⋆ F_a)(t)`. -/
lemma tail_conv_le_U {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hrN : 8 * N ≤ r) {t : ℝ} (htr : r < |t|) :
    (1 - 1 / π) * (r ^ 2 * (Real.log (|t| / r) + c1) / (729 * t ^ 2)) ≤ EcU N r t := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hr0 : 0 < r := by linarith
  have ha : 0 < 1 / (2 * (N : ℝ)) := by positivity
  have hδ : 0 < r / 2 := by positivity
  have hA : 0 ≤ Real.log (|t| / r) + c1 := by
    have := Real.log_nonneg (show 1 ≤ |t| / r by rw [le_div_iff₀ hr0]; linarith)
    linarith [c1_nonneg]
  have hw0 : 0 ≤ r ^ 2 * (Real.log (|t| / r) + c1) / (729 * t ^ 2) :=
    div_nonneg (mul_nonneg (sq_nonneg r) hA) (by positivity)
  have h := conv_ge ha hδ (envT_nonneg (K := (r + r / 2) ^ 2 / 729) (by positivity) (by linarith))
    (integrable_envT _ (by linarith)) hw0
    (fun u hu => envT_ge hr0 hδ (by linarith) htr (abs_le.2 ⟨hu.1, hu.2⟩))
  have hε : 2 / (π * (1 / (2 * N)) * (r / 2)) ≤ 1 / π := by
    have e : π * (1 / (2 * (N : ℝ))) * (r / 2) = π * r / (4 * N) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) Real.pi_pos, one_mul, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hrN Real.pi_pos.le]
  have h3 : (1 - 1 / π) * (r ^ 2 * (Real.log (|t| / r) + c1) / (729 * t ^ 2)) ≤
      (1 - 2 / (π * (1 / (2 * N)) * (r / 2))) * (r ^ 2 * (Real.log (|t| / r) + c1) / (729 * t ^ 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) hw0
  unfold EcU
  exact h3.trans h

lemma one_sub_inv_pi_pos : 0 < 1 - 1 / π := by
  have := Real.pi_gt_three
  rw [sub_pos, div_lt_one Real.pi_pos]; linarith

/-- **The pointwise bound**: `M_r(t)(L(t) − log π) ≤ (log(r/2π) + 1/5)M_r(t) + (729/(1 − 1/π))(E ⋆ F_a)(t)`
for `r ≥ 8N`, with `L(t) = Re ψ(¼ + it/2)`. -/
lemma majR_L_le {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hrN : 8 * N ≤ r) (t : ℝ) :
    majR r t * (psiRe t - Real.log π) ≤
      (Real.log (r / (2 * π)) + 1 / 5) * majR r t + 729 / (1 - 1 / π) * EcU N r t := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr8 : 8 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hM0 := majR_nonneg r t
  have hE0 := EcU_nonneg hN hr0 t
  have hpi := one_sub_inv_pi_pos
  have hK0 : 0 ≤ 729 / (1 - 1 / π) * EcU N r t := mul_nonneg (div_nonneg (by norm_num) hpi.le) hE0
  have hps := psiRe_sub_le hr8 t
  rcases le_or_gt |t| r with h | h
  · rw [max_eq_right h] at hps
    have := mul_le_mul_of_nonneg_left hps hM0
    linarith
  · rw [max_eq_left h.le] at hps
    have ht0 : 0 < |t| := by linarith
    have hsplit : Real.log (|t| / (2 * π)) = Real.log (r / (2 * π)) + Real.log (|t| / r) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    rw [hsplit] at hps
    have hl0 : 0 ≤ Real.log (|t| / r) := Real.log_nonneg (by rw [le_div_iff₀ hr0]; linarith)
    have ht0' : t ≠ 0 := by intro h0; rw [h0, abs_zero] at h; linarith
    have hmaj : majR r t ≤ r ^ 2 / t ^ 2 := majR_le_sq hr0 ht0'
    have htail := tail_conv_le_U hN hrN h
    have h1 : majR r t * Real.log (|t| / r) ≤ r ^ 2 * (Real.log (|t| / r) + c1) / t ^ 2 := by
      calc majR r t * Real.log (|t| / r) ≤ r ^ 2 / t ^ 2 * Real.log (|t| / r) :=
            mul_le_mul_of_nonneg_right hmaj hl0
        _ ≤ r ^ 2 / t ^ 2 * (Real.log (|t| / r) + c1) :=
            mul_le_mul_of_nonneg_left (by linarith [c1_nonneg]) (by positivity)
        _ = r ^ 2 * (Real.log (|t| / r) + c1) / t ^ 2 := by ring
    have h2 : r ^ 2 * (Real.log (|t| / r) + c1) / t ^ 2 ≤ 729 / (1 - 1 / π) * EcU N r t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
      have e : r ^ 2 * (Real.log (|t| / r) + c1) / t ^ 2 * (1 - 1 / π) =
          729 * ((1 - 1 / π) * (r ^ 2 * (Real.log (|t| / r) + c1) / (729 * t ^ 2))) := by
        field_simp
      rw [e]
      linarith
    have h3 := mul_le_mul_of_nonneg_left hps hM0
    have e2 : majR r t * (Real.log (r / (2 * π)) + Real.log (|t| / r) + 1 / 5) =
        (Real.log (r / (2 * π)) + 1 / 5) * majR r t + majR r t * Real.log (|t| / r) := by ring
    linarith

lemma integrable_Kc_EcU {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable fun t => Kc N c t * EcU N r t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact integrable_Kc_conv (N := N) c (show 0 < 1 / (2 * (N : ℝ)) by positivity)
    (integrable_envT ((r + r / 2) ^ 2 / 729) (show 0 < r - r / 2 by linarith))

lemma integral_Kc_EcU {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ t, Kc N c t * EcU N r t = S2 N c * (9 * r * (1 + c1) / 729) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < 1 / (2 * (N : ℝ)) := by positivity
  have haN : 2 * (1 / (2 * (N : ℝ))) * N ≤ 1 := le_of_eq (by field_simp)
  have hR : 0 < r - r / 2 := by linarith
  unfold EcU
  rw [integral_Kc_conv c ha haN (integrable_envT _ hR), integral_envT _ hR]
  congr 1
  field_simp
  ring

lemma integrable_hRM {r : ℝ} (hr : 0 < r) (N : ℕ) (c : ℕ → ℝ) : Integrable (hRM N c r) := by
  have h := integrable_Kc_mul_cos N c (integrable_majR_cos hr) 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  exact h

lemma integrable_hRM_psi {r : ℝ} (hr : π / 2 ≤ r) (N : ℕ) (c : ℕ → ℝ) :
    Integrable (fun t => hRM N c r t * psiRe t) := by
  refine (integrable_psi_real (striptest_htM hr N c)).re.congr
    (Filter.Eventually.of_forall fun t => ?_)
  show RCLike.re (htM N c r t * Complex.digamma (zB t)) = hRM N c r t * psiRe t
  rw [htM_ofReal (lt_of_lt_of_le (by positivity) hr)]
  simp [psiRe]

/-- **The archimedean term from above**: for `r ≥ 8N`,
`−g_h(0)log π + (1/2π)∫h Re ψ ≤ (πr/4)(log(r/2π) + 1/5)Σc_n² + (11/2)rΣc_n²`. -/
lemma arch_le_M {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hrN : 8 * N ≤ r) (c : ℕ → ℝ) :
    -(gh (hRM N c r) 0 * Real.log π) + 1 / (2 * π) * ∫ t, hRM N c r t * psiRe t ≤
      π * r / 4 * (Real.log (r / (2 * π)) + 1 / 5) * S2 N c + 11 / 2 * (r * S2 N c) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr0 : 0 < r := by linarith
  have hpi4 := Real.pi_lt_four
  have hr2 : π / 2 ≤ r := by linarith
  have hrN' : 2 * π * N ≤ r := by nlinarith
  have hpi := one_sub_inv_pi_pos
  have hiR := integrable_hRM hr0 N c
  have hiP := integrable_hRM_psi hr2 N c
  have hiE := integrable_Kc_EcU hN c hr0
  have hpt : ∀ t, hRM N c r t * psiRe t - Real.log π * hRM N c r t ≤
      (Real.log (r / (2 * π)) + 1 / 5) * hRM N c r t + 729 / (1 - 1 / π) * (Kc N c t * EcU N r t) := by
    intro t
    have h1 := majR_L_le hN hrN t
    have h3 := mul_le_mul_of_nonneg_left h1 (Kc_nonneg N c t)
    unfold hRM
    linarith
  have hint : ∫ t, (hRM N c r t * psiRe t - Real.log π * hRM N c r t) ≤
      ∫ t, ((Real.log (r / (2 * π)) + 1 / 5) * hRM N c r t + 729 / (1 - 1 / π) * (Kc N c t * EcU N r t)) :=
    integral_mono (hiP.sub (hiR.const_mul (Real.log π))) ((hiR.const_mul _).add (hiE.const_mul _)) hpt
  rw [integral_sub hiP (hiR.const_mul _), integral_add (hiR.const_mul _) (hiE.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_hRM hr0 hN hrN' c,
    integral_Kc_EcU hN c hr0, mhat_zero hr0] at hint
  have hgh0 : gh (hRM N c r) 0 = 1 / (2 * π) * ∫ t, hRM N c r t := by
    unfold gh; simp only [mul_zero, Real.cos_zero, mul_one]
  rw [hgh0, integral_hRM hr0 hN hrN' c, mhat_zero hr0]
  have hpi2 : 0 < 1 / (2 * π) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hint hpi2.le
  have hc1 := c1_le
  have hS2 := S2_nonneg N c
  have hrS : 0 ≤ r * S2 N c := mul_nonneg hr0.le hS2
  have key : 1 / (2 * π) * (729 / (1 - 1 / π) * (S2 N c * (9 * r * (1 + c1) / 729))) ≤
      11 / 2 * (r * S2 N c) := by
    have hpi1 : 0 < π - 1 := by linarith [Real.pi_gt_three]
    have e : 1 / (2 * π) * (729 / (1 - 1 / π) * (S2 N c * (9 * r * (1 + c1) / 729))) =
        9 * (1 + c1) / (2 * (π - 1)) * (r * S2 N c) := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hrS
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_gt_d2]
  have e1 : 1 / (2 * π) * ((Real.log (r / (2 * π)) + 1 / 5) * (π ^ 2 * r / 2 * S2 N c)) =
      π * r / 4 * (Real.log (r / (2 * π)) + 1 / 5) * S2 N c := by
    field_simp; ring
  have e2 : 1 / (2 * π) * ((∫ t, hRM N c r t * psiRe t) - Real.log π * (π ^ 2 * r / 2 * S2 N c)) =
      1 / (2 * π) * (∫ t, hRM N c r t * psiRe t) - 1 / (2 * π) * (π ^ 2 * r / 2 * S2 N c) * Real.log π := by
    ring
  have e3 : 1 / (2 * π) * ((Real.log (r / (2 * π)) + 1 / 5) * (π ^ 2 * r / 2 * S2 N c) +
      729 / (1 - 1 / π) * (S2 N c * (9 * r * (1 + c1) / 729))) =
      1 / (2 * π) * ((Real.log (r / (2 * π)) + 1 / 5) * (π ^ 2 * r / 2 * S2 N c)) +
      1 / (2 * π) * (729 / (1 - 1 / π) * (S2 N c * (9 * r * (1 + c1) / 729))) := by ring
  rw [e2, e3, e1] at h1
  linarith

/-! ## The pole and the zero side -/

lemma norm_DC_I_half_le (N : ℕ) (c : ℕ → ℝ) : ‖DC N c (I / 2)‖ ≤ ∑ j ∈ Icc 1 N, |c j| * Real.sqrt j := by
  unfold DC
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have e : ∀ L : ℝ, -(I * (I / 2) * (L : ℂ)) = ((L / 2 : ℝ) : ℂ) := fun L => by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]; linear_combination (-(L : ℂ) / 2) * Complex.I_sq
  rw [e, Complex.ofReal_re, BallPsi.exp_log_half hj0]

lemma norm_DC_neg_I_half_le (N : ℕ) (c : ℕ → ℝ) :
    ‖DC N c (-(I / 2))‖ ≤ ∑ j ∈ Icc 1 N, |c j| / Real.sqrt j := by
  unfold DC
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have e : ∀ L : ℝ, -(I * -(I / 2) * (L : ℂ)) = ((-(L / 2) : ℝ) : ℂ) := fun L => by
    rw [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    linear_combination ((L : ℂ) / 2) * Complex.I_sq
  rw [e, Complex.ofReal_re, Real.exp_neg, BallPsi.exp_log_half hj0, div_eq_mul_inv]

lemma norm_majC_I_half_le {r : ℝ} (hr : π / 2 ≤ r) : ‖majC r (I / 2)‖ ≤ 23 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have ha0 : 0 ≤ π / (2 * r) := div_nonneg Real.pi_pos.le (by linarith)
  have ha1 : π / (2 * r) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hg := norm_ghatC_bx_le (π / (2 * r)) ha0 (I / 2)
  have him : |(I / 2 : ℂ).im| = 1 / 2 := by norm_num
  rw [him] at hg
  have he : Real.exp (π / (2 * r) * (1 / 2)) ≤ 3 := by
    have := Real.exp_one_lt_d9
    calc Real.exp (π / (2 * r) * (1 / 2)) ≤ Real.exp 1 := Real.exp_le_exp.2 (by nlinarith)
      _ ≤ 3 := by linarith
  have hg3 : ‖ghatC (bx (π / (2 * r))) (π / (2 * r)) (I / 2)‖ ≤ 6 * (π / (2 * r)) := by
    calc ‖ghatC (bx (π / (2 * r))) (π / (2 * r)) (I / 2)‖ ≤ 2 * (π / (2 * r)) * Real.exp (π / (2 * r) * (1 / 2)) := hg
      _ ≤ 2 * (π / (2 * r)) * 3 := mul_le_mul_of_nonneg_left he (by positivity)
      _ = 6 * (π / (2 * r)) := by ring
  have hra : r * (π / (2 * r)) = π / 2 := by field_simp
  unfold majC
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h2 : ‖ghatC (bx (π / (2 * r))) (π / (2 * r)) (I / 2)‖ ^ 2 ≤ (6 * (π / (2 * r))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hg3 2
  calc r ^ 2 / 4 * ‖ghatC (bx (π / (2 * r))) (π / (2 * r)) (I / 2)‖ ^ 2
      ≤ r ^ 2 / 4 * (6 * (π / (2 * r))) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 9 * (r * (π / (2 * r))) ^ 2 := by ring
    _ = 9 * (π / 2) ^ 2 := by rw [hra]
    _ ≤ 23 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- **The pole term**: `Re(h(i/2) + h(−i/2)) ≤ 46·(Σ_j|c_j|√j)(Σ_j|c_j|/√j)`. -/
lemma pole_le_M {r : ℝ} (hr : π / 2 ≤ r) (N : ℕ) (c : ℕ → ℝ) :
    (htM N c r (I / 2) + htM N c r (-(I / 2))).re ≤
      46 * ((∑ j ∈ Icc 1 N, |c j| * Real.sqrt j) * ∑ j ∈ Icc 1 N, |c j| / Real.sqrt j) := by
  rw [htM_even, ← two_mul]
  have hA : 0 ≤ ∑ j ∈ Icc 1 N, |c j| * Real.sqrt j := Finset.sum_nonneg fun j _ => by positivity
  have hB : 0 ≤ ∑ j ∈ Icc 1 N, |c j| / Real.sqrt j := Finset.sum_nonneg fun j _ => by positivity
  have h1 : ‖htM N c r (I / 2)‖ ≤
      (∑ j ∈ Icc 1 N, |c j| * Real.sqrt j) * (∑ j ∈ Icc 1 N, |c j| / Real.sqrt j) * 23 := by
    unfold htM
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (norm_DC_I_half_le N c) (norm_DC_neg_I_half_le N c) (norm_nonneg _) hA)
      (norm_majC_I_half_le hr) (norm_nonneg _) (mul_nonneg hA hB)
  have h2 := Complex.re_le_norm (2 * htM N c r (I / 2))
  rw [norm_mul, Complex.norm_two] at h2
  linarith

/-- Under RH, `h(t_ρ) = |V_x(ρ)|²M_r(γ)` with `c_n = x_n√n`. -/
lemma zero_term_M (hRH : RiemannHypothesis) {r : ℝ} (hr : 0 < r) (N : ℕ) (x : ℕ → ℝ) (q : ZIdx) :
    htM N (fun n => x n * Real.sqrt n) r ((zetaZeroFamily q - 1 / 2) / I) =
      ((‖BallRate.dpoly N x q‖ ^ 2 * majR r (zetaZeroFamily q).im : ℝ) : ℂ) := by
  have ht : (zetaZeroFamily q - 1 / 2) / I = ((zetaZeroFamily q).im : ℂ) := by
    rw [BallHadamard.zZF_sub_half hRH q, mul_div_cancel_left₀ _ Complex.I_ne_zero]
  rw [ht, htM_ofReal hr]
  congr 1
  unfold hRM
  rw [BallSampling.dpoly_eq_conj hRH, Complex.norm_conj, dp_eq_DC, norm_DC_ofReal_sq]

/-- **The zero side**: `Σ_{|γ| ≤ r}|V_x(ρ)|² ≤ Σ_ρ |V_x(ρ)|²M_r(γ)`, as `M_r ≥ 1` on `[−r, r]` and `M_r ≥ 0`. -/
lemma zero_side_M {r : ℝ} (hr : 0 < r) (N : ℕ) (x : ℕ → ℝ) {Z : ℝ}
    (hZ : HasSum (fun q => ‖BallRate.dpoly N x q‖ ^ 2 * majR r (zetaZeroFamily q).im) Z) :
    ∑ q ∈ BallRate.zerosUpTo r, ‖BallRate.dpoly N x q‖ ^ 2 ≤ Z := by
  have h1 : ∑ q ∈ BallRate.zerosUpTo r, ‖BallRate.dpoly N x q‖ ^ 2 ≤
      ∑ q ∈ BallRate.zerosUpTo r, ‖BallRate.dpoly N x q‖ ^ 2 * majR r (zetaZeroFamily q).im :=
    Finset.sum_le_sum fun q hq => by
      have := one_le_majR hr (BallRate.mem_zerosUpTo.1 hq)
      nlinarith [sq_nonneg ‖BallRate.dpoly N x q‖]
  exact h1.trans (sum_le_hasSum _ (fun q _ => mul_nonneg (sq_nonneg _) (majR_nonneg r _)) hZ)

/-- **The mean value from above** (RH): for `N ≥ 1`, `r ≥ 8N` and real `x`, with `c_n = x_n√n`,
`Σ_{|γ| ≤ r}|V_x(ρ)|² ≤ (πr/4)((log(r/2π) + 1/5 + 22/π)Σc_n² − L(c)) + 46(Σ|c_j|√j)(Σ|c_j|/√j)`,
`L(c) = 2Σ_{n ≤ N}Λ(n)n^{−1/2}Σ_{jn ≤ N}c_j c_{jn}` Landau's form. -/
theorem upper_mean (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hrN : 8 * N ≤ r) (x : ℕ → ℝ) :
    ∑ q ∈ BallRate.zerosUpTo r, ‖BallRate.dpoly N x q‖ ^ 2 ≤
      π * r / 4 * ((Real.log (r / (2 * π)) + 1 / 5 + 22 / π) * S2 N (fun n => x n * Real.sqrt n) -
        2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N (fun n => x n * Real.sqrt n) n) +
      46 * ((∑ j ∈ Icc 1 N, |x j * Real.sqrt j| * Real.sqrt j) *
        ∑ j ∈ Icc 1 N, |x j * Real.sqrt j| / Real.sqrt j) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr0 : 0 < r := by linarith
  have hpi4 := Real.pi_lt_four
  have hr2 : π / 2 ≤ r := by linarith
  have hrN' : 2 * π * N ≤ r := by nlinarith
  set c : ℕ → ℝ := fun n => x n * Real.sqrt n with hc
  have hsum := (weil_htM hr2 N c).2
  have hre := Complex.hasSum_re hsum
  have hterm : ∀ q, (htM N c r ((zetaZeroFamily q - 1 / 2) / I)).re =
      ‖BallRate.dpoly N x q‖ ^ 2 * majR r (zetaZeroFamily q).im := fun q => by
    rw [hc, zero_term_M hRH hr0 N x q, Complex.ofReal_re]
  simp only [hterm] at hre
  rw [Complex.add_re, Complex.ofReal_re] at hre
  have hZ := zero_side_M hr0 N x hre
  have hpole := pole_le_M hr2 N c
  have harch := arch_le_M hN hrN c
  have hprime := prime_eq_M hr0 hN hrN' c
  have e : mhat r 0 / (2 * π) = π * r / 4 := by rw [mhat_zero hr0]; field_simp; ring
  rw [e] at hprime
  have h22 : 11 / 2 * (r * S2 N c) = π * r / 4 * (22 / π * S2 N c) := by field_simp; ring
  have e2 : π * r / 4 * ((Real.log (r / (2 * π)) + 1 / 5 + 22 / π) * S2 N c -
      2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n) =
      π * r / 4 * (Real.log (r / (2 * π)) + 1 / 5) * S2 N c + π * r / 4 * (22 / π * S2 N c) -
        π * r / 4 * (2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n) := by ring
  rw [e2]
  linarith

/-! ## Landau's form at the alternating vector -/

/-- The harmonic number `H_N = Σ_{j ≤ N} 1/j`. -/
def Hn (N : ℕ) : ℝ := ∑ j ∈ Icc 1 N, 1 / (j : ℝ)

lemma Hn_nonneg (N : ℕ) : 0 ≤ Hn N := Finset.sum_nonneg fun j _ => by positivity

lemma Hn_eq_harmonic (N : ℕ) : Hn N = harmonic N := by
  unfold Hn; rw [harmonic_eq_sum_Icc]; push_cast; simp only [one_div]

lemma Hn_le (N : ℕ) : Hn N ≤ 1 + Real.log N := by rw [Hn_eq_harmonic]; exact harmonic_le_one_add_log N

lemma log_le_Hn (N : ℕ) : Real.log N ≤ Hn N := by
  rw [Hn_eq_harmonic]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have h1 := log_add_one_le_harmonic N
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) := Real.log_le_log hN0 (by push_cast; linarith)
    linarith

lemma one_le_Hn {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Hn N := by
  unfold Hn
  have := Finset.single_le_sum (f := fun j : ℕ => 1 / (j : ℝ)) (fun j _ => by positivity)
    (Finset.mem_Icc.2 ⟨le_rfl, hN⟩)
  simpa using this

/-- `c_j = x_j√j = (−1)^{j+1}/√j`. -/
lemma cxa_eq {j : ℕ} (hj : 1 ≤ j) : xa j * Real.sqrt j = (-1) ^ (j + 1) / Real.sqrt j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hs0 : 0 < Real.sqrt j := Real.sqrt_pos.2 hj0
  unfold xa
  rw [div_mul_eq_mul_div, div_eq_div_iff hj0.ne' hs0.ne', mul_assoc, Real.mul_self_sqrt hj0.le]

lemma abs_cxa {j : ℕ} (hj : 1 ≤ j) : |xa j * Real.sqrt j| = 1 / Real.sqrt j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  rw [cxa_eq hj, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (Real.sqrt_pos.2 hj0)]

lemma S2_xa (N : ℕ) : S2 N (fun n => xa n * Real.sqrt n) = Hn N := by
  unfold S2 Hn
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← sq_abs, abs_cxa (Finset.mem_Icc.1 hj).1, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg j)]

lemma sumA_xa (N : ℕ) : ∑ j ∈ Icc 1 N, |xa j * Real.sqrt j| * Real.sqrt j = N := by
  rw [show (N : ℝ) = ∑ j ∈ Icc 1 N, (1 : ℝ) by simp]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  rw [abs_cxa (Finset.mem_Icc.1 hj).1, one_div, inv_mul_cancel₀ (Real.sqrt_pos.2 hj0).ne']

lemma sumB_xa (N : ℕ) : ∑ j ∈ Icc 1 N, |xa j * Real.sqrt j| / Real.sqrt j = Hn N := by
  unfold Hn
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  rw [abs_cxa (Finset.mem_Icc.1 hj).1, div_div, Real.mul_self_sqrt hj0.le]

lemma sum_xa_sq_ge {N : ℕ} (hN : 1 ≤ N) : 1 ≤ ∑ n ∈ Icc 1 N, xa n ^ 2 := by
  have := Finset.single_le_sum (f := fun n => xa n ^ 2) (fun n _ => sq_nonneg _) (Finset.mem_Icc.2 ⟨le_rfl, hN⟩)
  simpa [xa] using this

/-- `H_f(n) = Σ_{j ≤ N, jn ≤ N} 1/j`. -/
def Hf (N n : ℕ) : ℝ := ∑ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N), 1 / (j : ℝ)

lemma Hf_le (N n : ℕ) : Hf N n ≤ Hn N :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => by positivity

/-- `c_j c_{jn} = (−1)^{j+1}(−1)^{jn+1}/(j√n)`. -/
lemma cxa_mul {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    xa j * Real.sqrt j * (xa (j * n) * Real.sqrt ((j * n : ℕ) : ℝ)) =
      (-1) ^ (j + 1) * (-1) ^ (j * n + 1) / (j * Real.sqrt n) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  rw [cxa_eq hj, cxa_eq (show 1 ≤ j * n by nlinarith), Nat.cast_mul, Real.sqrt_mul hj0.le,
    div_mul_div_comm, ← mul_assoc, Real.mul_self_sqrt hj0.le]

lemma ex_xa_odd {N n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) :
    ex N (fun m => xa m * Real.sqrt m) n = Hf N n / Real.sqrt n := by
  unfold ex Hf
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 (Finset.mem_filter.1 hj).1).1
  rw [cxa_mul hj1 hn]
  have hsign : (-1 : ℝ) ^ (j + 1) * (-1) ^ (j * n + 1) = 1 := by
    rw [← pow_add]
    obtain ⟨k, hk⟩ := hodd
    exact Even.neg_one_pow ⟨j + j * k + 1, by subst hk; ring⟩
  rw [hsign, div_div]

lemma ex_xa_ge {N n : ℕ} (hn : 1 ≤ n) :
    -(Hf N n / Real.sqrt n) ≤ ex N (fun m => xa m * Real.sqrt m) n := by
  unfold ex Hf
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 (Finset.mem_filter.1 hj).1).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [cxa_mul hj1 hn, div_div, ← neg_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← pow_add]
  rcases neg_one_pow_eq_or ℝ (j + 1 + (j * n + 1)) with h | h
  · rw [h]; norm_num
  · rw [h]

/-- `Σ_{n ≤ N}Λ(n)H_f(n)/n = Σ_{m ≤ N}(log m)/m`, from `Σ_{n ∣ m}Λ(n) = log m`. -/
lemma sum_vonMangoldt_Hf (N : ℕ) :
    ∑ n ∈ Icc 1 N, Λ n * Hf N n / n = ∑ m ∈ Icc 1 N, Real.log m / m := by
  have h1 : ∀ n ∈ Icc 1 N, Λ n * Hf N n / n = ∑ m ∈ (Icc 1 N).filter (n ∣ ·), Λ n / m := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    unfold Hf
    rw [← sum_mul_eq_sum_dvd N hn1 (fun m => Λ n / m), Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.1 (Finset.mem_filter.1 hj).1).1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ m ∈ Icc 1 N, Real.log m / m = ∑ n ∈ m.divisors, Λ n / m := by
    intro m _
    rw [← Finset.sum_div, ArithmeticFunction.vonMangoldt_sum]
  rw [Finset.sum_congr rfl h2]
  refine Finset.sum_comm' fun n m => ?_
  simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, ⟨hm1, hmN⟩, hnm⟩
    exact ⟨⟨hnm, by omega⟩, hm1, hmN⟩
  · rintro ⟨⟨hnm, -⟩, hm1, hmN⟩
    have hn1 : 1 ≤ n := Nat.pos_of_dvd_of_pos hnm (by omega)
    exact ⟨⟨hn1, (Nat.le_of_dvd (by omega) hnm).trans hmN⟩, ⟨hm1, hmN⟩, hnm⟩

lemma eq_two_pow_of_even {n : ℕ} (hn : Even n) (hΛ : Λ n ≠ 0) : ∃ k, 1 ≤ k ∧ n = 2 ^ k := by
  rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hΛ
  obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
  have h2 : 2 ∣ p ^ k := even_iff_two_dvd.1 hn
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.nat_prime).1
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  exact ⟨k, hk, by rw [hp2]⟩

/-- The even prime powers are the powers of `2`: `Σ_{n ≤ N even}Λ(n)/n ≤ log 2`. -/
lemma sum_even_vonMangoldt_le (N : ℕ) : ∑ n ∈ (Icc 1 N).filter Even, Λ n / n ≤ Real.log 2 := by
  classical
  have hsub : ((Icc 1 N).filter Even).filter (fun n => Λ n ≠ 0) ⊆ (Icc 1 N).image (fun k => 2 ^ k) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnN⟩, he⟩, hΛ⟩ := hn
    obtain ⟨k, hk, rfl⟩ := eq_two_pow_of_even he hΛ
    exact Finset.mem_image.2 ⟨k, Finset.mem_Icc.2 ⟨hk, Nat.lt_two_pow_self.le.trans hnN⟩, rfl⟩
  have hnn : ∀ n : ℕ, 0 ≤ Λ n / (n : ℝ) :=
    fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  calc ∑ n ∈ (Icc 1 N).filter Even, Λ n / n
      = ∑ n ∈ ((Icc 1 N).filter Even).filter (fun n => Λ n ≠ 0), Λ n / n := by
        symm
        apply Finset.sum_filter_of_ne
        intro n _ h hΛ
        exact h (by rw [hΛ, zero_div])
    _ ≤ ∑ n ∈ (Icc 1 N).image (fun k => 2 ^ k), Λ n / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hnn n
    _ = ∑ k ∈ Icc 1 N, Λ (2 ^ k) / ((2 ^ k : ℕ) : ℝ) :=
        Finset.sum_image fun a _ b _ h => Nat.pow_right_injective le_rfl h
    _ = ∑ k ∈ Icc 1 N, Real.log 2 * (1 / 2) ^ k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk1 := (Finset.mem_Icc.1 hk).1
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        push_cast
        rw [one_div_pow, mul_one_div]
    _ ≤ Real.log 2 := by
        rw [← Finset.mul_sum]
        have hgeom : ∑ k ∈ Icc 1 N, (1 / 2 : ℝ) ^ k ≤ 1 := by
          rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
          have h := sum_geometric_two_le N
          have e : ∑ k ∈ range (N + 1 - 1), (1 / 2 : ℝ) ^ (1 + k) = 1 / 2 * ∑ k ∈ range N, (1 / 2 : ℝ) ^ k := by
            rw [show N + 1 - 1 = N by omega, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by rw [pow_add, pow_one]
          rw [e]; linarith
        have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
        nlinarith

/-- **Landau's form at the alternating vector, from below**: `L(c) ≥ 2Σ_{m ≤ N}(log m)/m − 4H_N log 2`. On odd `n`,
`Σ_{jn ≤ N}c_j c_{jn} = n^{−1/2}Σ_{jn ≤ N}1/j`; on even `n` it is at least the negative of that, and the even `n`
with `Λ(n) ≠ 0` are the powers of `2`. -/
lemma landau_xa_ge (N : ℕ) :
    2 * ∑ m ∈ Icc 1 N, Real.log m / m - 4 * Real.log 2 * Hn N ≤
      2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N (fun m => xa m * Real.sqrt m) n := by
  classical
  have hpt : ∀ n ∈ Icc 1 N, Λ n * Hf N n / n - (if Even n then 2 * (Λ n / n) * Hf N n else 0) ≤
      Λ n / Real.sqrt n * ex N (fun m => xa m * Real.sqrt m) n := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq := Real.mul_self_sqrt hn0.le
    have hs0 := Real.sqrt_pos.2 hn0
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hval : Λ n / Real.sqrt n * (Hf N n / Real.sqrt n) = Λ n * Hf N n / n := by
      rw [div_mul_div_comm, hsq]
    by_cases he : Even n
    · rw [ite_eq_left he]
      have h1 := mul_le_mul_of_nonneg_left (ex_xa_ge (N := N) hn1) (div_nonneg hΛ hs0.le)
      rw [mul_neg, hval] at h1
      have e : Λ n * Hf N n / n - 2 * (Λ n / n) * Hf N n = -(Λ n * Hf N n / n) := by ring
      linarith
    · rw [ite_eq_right he, sub_zero, ex_xa_odd hn1 (Nat.not_even_iff_odd.1 he), hval]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, sum_vonMangoldt_Hf] at hsum
  have heven : ∑ n ∈ Icc 1 N, (if Even n then 2 * (Λ n / n) * Hf N n else 0) ≤ 2 * Real.log 2 * Hn N := by
    rw [← Finset.sum_filter]
    have hΛn : ∀ n : ℕ, 0 ≤ 2 * (Λ n / (n : ℝ)) :=
      fun n => mul_nonneg two_pos.le (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
    calc ∑ n ∈ (Icc 1 N).filter Even, 2 * (Λ n / n) * Hf N n
        ≤ ∑ n ∈ (Icc 1 N).filter Even, 2 * (Λ n / n) * Hn N :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (Hf_le N n) (hΛn n)
      _ = 2 * Hn N * ∑ n ∈ (Icc 1 N).filter Even, Λ n / n := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ 2 * Hn N * Real.log 2 :=
          mul_le_mul_of_nonneg_left (sum_even_vonMangoldt_le N) (mul_nonneg two_pos.le (Hn_nonneg N))
      _ = 2 * Real.log 2 * Hn N := by ring
  linarith

lemma sum_log_div_aux {N : ℕ} (hN : 1 ≤ N) :
    Real.log N ^ 2 / 2 - ∑ m ∈ Icc 1 N, Real.log m / m + Real.log N / N ≤ 1 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have hl := ell_le hN
    unfold ell at hl
    have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hl1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hsq : Real.log ((N : ℝ) + 1) ^ 2 ≤ (Real.log N + 1 / N) ^ 2 :=
      pow_le_pow_left₀ hl1 (by linarith) 2
    have h2 : 1 / (N : ℝ) ^ 2 / 2 ≤ 1 / N - 1 / (N + 1) := by
      rw [div_sub_div _ _ hN0.ne' (by positivity), div_div,
        div_le_div_iff₀ (mul_pos (pow_pos hN0 2) two_pos) (mul_pos hN0 (by linarith))]
      nlinarith
    have e : (Real.log N + 1 / N) ^ 2 = Real.log N ^ 2 + 2 * (Real.log N / N) + 1 / (N : ℝ) ^ 2 := by
      field_simp; ring
    linarith

/-- `Σ_{m ≤ N}(log m)/m ≥ (log N)²/2 − 1`. -/
lemma sum_log_div_ge {N : ℕ} (hN : 1 ≤ N) : Real.log N ^ 2 / 2 - 1 ≤ ∑ m ∈ Icc 1 N, Real.log m / m := by
  have h := sum_log_div_aux hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 0 ≤ Real.log N / N := div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) hN0.le
  have h2 : 0 ≤ 1 / (N : ℝ) := by positivity
  linarith

/-- **The mean value at the alternating vector, from above** (RH): for `N ≥ 1` and `r ≥ 8N`,
`Σ_{|γ| ≤ r}|V_x(ρ)|² ≤ ((πr/4)(log(r/N) + 12) + 46N)H_N`. Landau's form at this vector is
`(log N)² + O(H_N)`, so the `log r` of the diagonal drops to `log(r/N)`. -/
theorem mean_xa_le (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hrN : 8 * N ≤ r) :
    ∑ q ∈ BallRate.zerosUpTo r, ‖BallRate.dpoly N xa q‖ ^ 2 ≤
      (π * r / 4 * (Real.log (r / N) + 12) + 46 * N) * Hn N := by
  have h := upper_mean hRH hN hrN xa
  rw [S2_xa, sumA_xa, sumB_xa] at h
  have hL := landau_xa_ge N
  have hS := sum_log_div_ge hN
  have hH1 := one_le_Hn hN
  have hHl := Hn_le N
  have hlH := log_le_Hn N
  have hHn := Hn_nonneg N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hr0 : 0 < r := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog2 := Real.log_two_lt_d9
  have hlogpi : 1 ≤ Real.log π := by
    rw [Real.le_log_iff_exp_le Real.pi_pos]
    have := Real.exp_one_lt_d9; have := Real.pi_gt_three; linarith
  have hpi := Real.pi_gt_d2
  have h22 : 22 / π ≤ 7.01 := by rw [div_le_iff₀ Real.pi_pos]; linarith
  have hlr : Real.log (r / (2 * π)) = Real.log (r / N) + Real.log N - Real.log 2 - Real.log π := by
    rw [Real.log_div hr0.ne' (by positivity), Real.log_mul two_ne_zero Real.pi_ne_zero,
      Real.log_div hr0.ne' hN0.ne']; ring
  have hLogSq : -(Real.log N ^ 2) ≤ -(Real.log N * Hn N) + Hn N := by nlinarith
  have p1 := mul_le_mul_of_nonneg_right h22 hHn
  have p2 := mul_le_mul_of_nonneg_right hlogpi hHn
  have p3 := mul_le_mul_of_nonneg_right hlog2.le hHn
  have hbr : (Real.log (r / (2 * π)) + 1 / 5 + 22 / π) * Hn N -
      2 * ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N (fun n => xa n * Real.sqrt n) n ≤
      (Real.log (r / N) + 12) * Hn N := by
    rw [hlr]
    nlinarith
  have hpos : 0 ≤ π * r / 4 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hbr hpos
  nlinarith

/-! ## The sum over the zeros -/

lemma exists_dyadic {y : ℝ} (hy : 1 < y) {K : ℕ} (hK : y ≤ 2 ^ K) :
    ∃ k < K, 2 ^ k < y ∧ y ≤ 2 ^ (k + 1) := by
  induction K with
  | zero => norm_num at hK; linarith
  | succ K ih =>
    by_cases h : y ≤ 2 ^ K
    · obtain ⟨k, hk, h1, h2⟩ := ih h
      exact ⟨k, by omega, h1, h2⟩
    · push Not at h
      exact ⟨K, by omega, h, hK⟩

/-- The form of `δ₁` is `K_H(1)`. -/
lemma form_delta : BallWeil.form 1 (fun n => if n = 1 then 1 else 0) = BallWeil.kψ 1 := by
  unfold BallWeil.form
  simp [BallWeil.gram_self]

/-- A vector vanishing beyond `M` has the same form at every `N ≥ M`. -/
lemma form_extend {M N : ℕ} (hMN : M ≤ N) {y : ℕ → ℝ} (hy : ∀ n, M < n → y n = 0) :
    BallWeil.form N y = BallWeil.form M y := by
  induction N, hMN using Nat.le_induction with
  | base => rfl
  | succ N hMN ih => rw [BallWeil.form_succ_of_zero (hy _ (by omega)), ih]

/-- Under RH, `Σ_ρ 1/(¼ + γ²) = K_H(1)`: the form of `δ₁`. -/
lemma hasSum_inv_quarter (hRH : RiemannHypothesis) :
    HasSum (fun q : ZIdx => 1 / (1 / 4 + (zetaZeroFamily q).im ^ 2)) (BallWeil.kψ 1) := by
  have h := BallRate.hasSum_form hRH 1 (fun n => if n = 1 then 1 else 0)
  have hf := form_delta
  have hd : ∀ q, BallRate.dpoly 1 (fun n => if n = 1 then 1 else 0) q = 1 := by
    intro q
    unfold BallRate.dpoly BallLattice.pw
    simp
  rw [hf] at h
  simpa [hd] using h

lemma sum_ite_le (S : Finset ZIdx) {ρ w : ℝ} (hw : 0 ≤ w) (g : ZIdx → ℝ) (hg : ∀ q, 0 ≤ g q) :
    ∑ q ∈ S, (if |(zetaZeroFamily q).im| ≤ ρ then g q * w else 0) ≤ w * ∑ q ∈ BallRate.zerosUpTo ρ, g q := by
  classical
  rw [← Finset.sum_filter, Finset.mul_sum]
  calc ∑ q ∈ S.filter (fun q => |(zetaZeroFamily q).im| ≤ ρ), g q * w
      ≤ ∑ q ∈ BallRate.zerosUpTo ρ, g q * w :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun q hq => BallRate.mem_zerosUpTo.2 (Finset.mem_filter.1 hq).2)
          fun q _ _ => mul_nonneg (hg q) hw
    _ = ∑ q ∈ BallRate.zerosUpTo ρ, w * g q := Finset.sum_congr rfl fun q _ => mul_comm _ _

/-- The dyadic shell term: `B(2^{k+1}·8N)/(2^k·8N)² ≤ (π/16 + 23/640)(k + 20)2^{−k}H_N/N`. -/
lemma shell_le {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    1 / (2 ^ k * (8 * N)) ^ 2 * ((π * (2 ^ (k + 1) * (8 * N)) / 4 *
      (Real.log (2 ^ (k + 1) * (8 * N) / N) + 12) + 46 * N) * Hn N) ≤
      (π / 16 + 23 / 640) * (((k : ℝ) + 20) / 2 ^ k) * (Hn N / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hHn := Hn_nonneg N
  have hu : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have hu0 : (0 : ℝ) < 2 ^ k := by positivity
  have hlog : Real.log (2 ^ (k + 1) * (8 * N) / N) = (k + 4) * Real.log 2 := by
    rw [show (2 : ℝ) ^ (k + 1) * (8 * N) / N = 2 ^ (k + 4) by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num]; field_simp; ring]
    rw [Real.log_pow]; push_cast; ring
  rw [hlog]
  have hl2 : (k + 4) * Real.log 2 + 12 ≤ k + 20 := by
    have := Real.log_two_lt_d9
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have e : 1 / (2 ^ k * (8 * N)) ^ 2 * ((π * (2 ^ (k + 1) * (8 * N)) / 4 * ((k + 4) * Real.log 2 + 12) +
      46 * N) * Hn N) =
      (π / 16 * (((k : ℝ) + 4) * Real.log 2 + 12) / 2 ^ k + 23 / 32 / (2 ^ k) ^ 2) * (Hn N / N) := by
    rw [pow_succ]; field_simp; ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hHn hN0.le)
  have h1 : π / 16 * (((k : ℝ) + 4) * Real.log 2 + 12) / 2 ^ k ≤ π / 16 * (((k : ℝ) + 20) / 2 ^ k) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hl2 hu0.le) (by positivity)
  have h2 : 23 / 32 / ((2 : ℝ) ^ k) ^ 2 ≤ 23 / 640 * (((k : ℝ) + 20) / 2 ^ k) := by
    rw [div_le_iff₀ (by positivity)]
    have e2 : (23 / 640 : ℝ) * (((k : ℝ) + 20) / 2 ^ k) * ((2 : ℝ) ^ k) ^ 2 = 23 / 640 * ((k : ℝ) + 20) * 2 ^ k := by
      field_simp
    rw [e2]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  linarith

/-- **The form of the alternating vector** (RH, with the low zeros as a hypothesis): if
`|V_x(ρ)|² ≤ 400/N` at every zero of height `|γ| ≤ 2N`, then `Q_N(x) ≤ (400K_H(1) + 45)H_N/N`. The zeros of height
`2N < |γ| ≤ 8N` and the dyadic shells `2^k·8N < |γ| ≤ 2^{k+1}·8N` are paid for by `mean_xa_le`. -/
theorem form_xa_le (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N)
    (hlow : ∀ q : ZIdx, |(zetaZeroFamily q).im| ≤ 2 * N → ‖BallRate.dpoly N xa q‖ ^ 2 ≤ 400 / N) :
    BallWeil.form N xa ≤ (400 * BallWeil.kψ 1 + 45) * Hn N / N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hH1 := one_le_Hn hN
  have hH0 := Hn_nonneg N
  have hk1 : 0 < BallWeil.kψ 1 := BallWeil.kψ_one_pos
  have hdelta := hasSum_inv_quarter hRH
  have hsum := BallRate.hasSum_form hRH N xa
  refine hasSum_le_of_sum_le hsum fun S => ?_
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((∑ q ∈ S, |(zetaZeroFamily q).im|) / (8 * N)) one_lt_two
  have hSK : ∀ q ∈ S, |(zetaZeroFamily q).im| ≤ 2 ^ K * (8 * N) := by
    intro q hq
    have h1 : |(zetaZeroFamily q).im| ≤ ∑ q ∈ S, |(zetaZeroFamily q).im| :=
      Finset.single_le_sum (f := fun q => |(zetaZeroFamily q).im|) (fun q _ => abs_nonneg _) hq
    rw [div_lt_iff₀ (by positivity)] at hK
    linarith
  set V : ZIdx → ℝ := fun q => ‖BallRate.dpoly N xa q‖ ^ 2 with hV
  have hV0 : ∀ q, 0 ≤ V q := fun q => sq_nonneg _
  have hpt : ∀ q ∈ S, V q / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤
      400 / N * (1 / (1 / 4 + (zetaZeroFamily q).im ^ 2)) +
      (if |(zetaZeroFamily q).im| ≤ 8 * N then V q * (1 / (4 * N ^ 2)) else 0) +
      ∑ k ∈ range K, (if |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) then
        V q * (1 / (2 ^ k * (8 * N)) ^ 2) else 0) := by
    intro q hq
    have hden : 0 < 1 / 4 + (zetaZeroFamily q).im ^ 2 := by positivity
    have hT1 : 0 ≤ 400 / N * (1 / (1 / 4 + (zetaZeroFamily q).im ^ 2)) := by positivity
    have hT2 : 0 ≤ (if |(zetaZeroFamily q).im| ≤ 8 * N then V q * (1 / (4 * N ^ 2)) else 0) := by
      split_ifs
      · exact mul_nonneg (hV0 q) (by positivity)
      · exact le_rfl
    have hT3n : ∀ k, 0 ≤ (if |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) then
        V q * (1 / (2 ^ k * (8 * N)) ^ 2) else 0) := by
      intro k
      split_ifs
      · exact mul_nonneg (hV0 q) (by positivity)
      · exact le_rfl
    have hT3 := Finset.sum_nonneg fun k (_ : k ∈ range K) => hT3n k
    have hγ2 : |(zetaZeroFamily q).im| ^ 2 = (zetaZeroFamily q).im ^ 2 := sq_abs _
    rcases le_or_gt |(zetaZeroFamily q).im| (2 * N) with h1 | h1
    · have hl := hlow q h1
      have : V q / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤ 400 / N * (1 / (1 / 4 + (zetaZeroFamily q).im ^ 2)) := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_right hl hden.le
      linarith
    rcases le_or_gt |(zetaZeroFamily q).im| (8 * N) with h2 | h2
    · rw [ite_eq_left h2]
      have : V q / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤ V q * (1 / (4 * N ^ 2)) := by
        rw [mul_one_div]
        refine div_le_div_of_nonneg_left (hV0 q) (by positivity) ?_
        nlinarith [abs_nonneg (zetaZeroFamily q).im]
      linarith
    · have hy : 1 < |(zetaZeroFamily q).im| / (8 * N) := by rw [lt_div_iff₀ (by positivity)]; linarith
      have hyK : |(zetaZeroFamily q).im| / (8 * N) ≤ 2 ^ K := by
        rw [div_le_iff₀ (by positivity)]; exact hSK q hq
      obtain ⟨k, hk, hk1, hk2⟩ := exists_dyadic hy hyK
      have hRk : 2 ^ k * (8 * N) < |(zetaZeroFamily q).im| := by
        rw [lt_div_iff₀ (by positivity)] at hk1; linarith
      have hRk1 : |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) := by
        rw [div_le_iff₀ (by positivity)] at hk2; linarith
      have hsingle := Finset.single_le_sum (f := fun k => if |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) then
        V q * (1 / (2 ^ k * (8 * N)) ^ 2) else 0) (fun k _ => hT3n k) (Finset.mem_range.2 hk)
      simp only [ite_eq_left hRk1] at hsingle
      have hR0 : (0 : ℝ) < 2 ^ k * (8 * N) := by positivity
      have : V q / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤ V q * (1 / (2 ^ k * (8 * N)) ^ 2) := by
        rw [mul_one_div]
        refine div_le_div_of_nonneg_left (hV0 q) (by positivity) ?_
        nlinarith [abs_nonneg (zetaZeroFamily q).im]
      linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm (s := S), ← Finset.mul_sum]
  -- the three pieces
  have hA : ∑ q ∈ S, 1 / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤ BallWeil.kψ 1 :=
    sum_le_hasSum S (fun q _ => by positivity) hdelta
  have hB : ∑ q ∈ S, (if |(zetaZeroFamily q).im| ≤ 8 * N then V q * (1 / (4 * N ^ 2)) else 0) ≤
      1 / (4 * N ^ 2) * ((π * (8 * N) / 4 * (Real.log (8 * N / N) + 12) + 46 * N) * Hn N) := by
    refine (sum_ite_le S (by positivity) V hV0).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mean_xa_le hRH hN le_rfl
  have hC : ∀ k ∈ range K, ∑ q ∈ S, (if |(zetaZeroFamily q).im| ≤ 2 ^ (k + 1) * (8 * N) then
      V q * (1 / (2 ^ k * (8 * N)) ^ 2) else 0) ≤
      (π / 16 + 23 / 640) * (((k : ℝ) + 20) / 2 ^ k) * (Hn N / N) := by
    intro k _
    refine (sum_ite_le S (by positivity) V hV0).trans ?_
    refine le_trans (mul_le_mul_of_nonneg_left (mean_xa_le hRH hN ?_) (by positivity)) (shell_le hN k)
    have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ one_le_two
    nlinarith
  have hCs := Finset.sum_le_sum hC
  rw [← Finset.sum_mul, ← Finset.mul_sum] at hCs
  have hgeom := sum_geom_le K
  have hlog8 : Real.log (8 * N / N) = 3 * Real.log 2 := by
    rw [mul_div_assoc, div_self hN0.ne', mul_one, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  rw [hlog8] at hB
  have hl2 := Real.log_two_lt_d9
  have hpi := Real.pi_lt_d2
  have hB' : 1 / (4 * N ^ 2) * ((π * (8 * N) / 4 * (3 * Real.log 2 + 12) + 46 * N) * Hn N) ≤ 34 * (Hn N / N) := by
    have e : 1 / (4 * N ^ 2) * ((π * (8 * N) / 4 * (3 * Real.log 2 + 12) + 46 * N) * Hn N) =
        (π / 2 * (3 * Real.log 2 + 12) + 23 / 2) * (Hn N / N) := by field_simp; ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hH0 hN0.le)
    nlinarith [Real.pi_pos]
  have hC' : (π / 16 + 23 / 640) * (∑ k ∈ range K, ((k : ℝ) + 20) / 2 ^ k) * (Hn N / N) ≤ 10 * (Hn N / N) := by
    refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hH0 hN0.le)
    have : 0 ≤ π / 16 + 23 / 640 := by positivity
    nlinarith
  have hA' : 400 / N * ∑ q ∈ S, 1 / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤ 400 * BallWeil.kψ 1 * (Hn N / N) := by
    have h1 : 400 / N * ∑ q ∈ S, 1 / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤ 400 / N * BallWeil.kψ 1 :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have h2 : 400 / N * BallWeil.kψ 1 ≤ 400 * BallWeil.kψ 1 * (Hn N / N) := by
      rw [show 400 * BallWeil.kψ 1 * (Hn N / N) = 400 / N * BallWeil.kψ 1 * Hn N by ring]
      nlinarith [mul_pos (show (0 : ℝ) < 400 / N by positivity) hk1]
    linarith
  have e : (400 * BallWeil.kψ 1 + 45) * Hn N / N = (400 * BallWeil.kψ 1 + 45) * (Hn N / N) := by ring
  have hHN : 0 ≤ Hn N / N := div_nonneg hH0 hN0.le
  rw [e]
  linarith

end BallUpper
