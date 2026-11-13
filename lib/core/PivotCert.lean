import Mathlib
import PivotMinor

/-! # The archimedean minorant lies below `φ(s)(L(Ns) − log N)`: an exact interval certificate

Plain statement. For every `N ≥ 2` and every real `s`, `μ(s) ≤ φ(s)(L(Ns) − log N)` (`mu_le`), where `μ = φλ − r` is
`PivotMinor`'s band-limited minorant, `φ` is `PivotPhi.phi` and `L(t) = Re ψ(¼ + it/2) − log π`. This is
`PivotSharp.MuLe`.

The proof. `μ`, `φ` and `L` are even (`mu_neg`, `phi_neg`, `psiRe_neg`), and at `s = 0` the inequality is
`−r(0) ≤ 0`. For `s > 0`:

- **The archimedean weight, uniformly in `N`** (`gR_le`). Stirling with two recurrence steps
  (`DigammaStirling.re_digamma_quarter 2`) gives `Re ψ(¼ + it/2) ≥ log(t/2) − ē(t)`, with a rational `ē` that
  decreases in `t` (`psiRe_ge`, `ebR_anti`); so `L(Ns) − log N ≥ g(s) = log s − log 2 − log π − ē(2s)`, and it
  suffices that `φ(λ − g) ≤ r`.
- **The staircase** (`lam_le`). `1 − sinc²x ≤ u(x) = min(1, x²/3 − 2x⁴/45 + x⁶/315)` (`one_sub_sinc_sq_le`, from
  `cos ≤ T₈`), so `λ(s) ≤ 23/100 + (693/1000)S₃₀(s/10)` with `S_n(x) = Σ_{k<n}u(x/2^k)`. Past the eighth term the
  sum is at most `x²/147456` (`sR_le_tR`), and at `x = 2^j y` the first `j − 1` terms are at most `1`
  (`sR_pow_le`).
- **`φ` from above, `r` from below** on an interval (`phi_le_phiupF`, `rloF_le`): `sinc x ≥ sl(x) = 1 − x²/6 +
  x⁴/120 − x⁶/5040`, which decreases (`slAR_le_sin_div`, `slAR_anti`), and `1 − K(x) ≤ x²ρ(x²)` with `ρ` largest at
  `x² = 3` (`one_sub_kk_le_rho`, `rhoR_mono`, `rhoR_le_three`).
- **The certificate.** `log` is bounded below by `log y ≥ 2v + 2v³/3`, `v = (y − 1)/(y + 1)` (`lgR_le_log`), after
  halving, with `0.6931471803 < log 2 < 0.6931471808` and `log π ≤ 1.1558`. Each range of `s` is cut into the cells
  of an arithmetic progression, and the cells are checked by kernel evaluation in exact arithmetic `(p − m)/(d + 1)`,
  `p, m, d ∈ ℕ` (`Fr`):
  * `s ≥ 20` (`region1`): `s = 10·2^j y`, `j ≥ 1`, `y ∈ [1, 2)` in 400 cells, where `λ ≤ g`, since the steps of
    height `0.693 < log 2` follow `log s` (`ok1`);
  * `12 ≤ s < 20` (`region0`): 320 cells, `λ ≤ g` (`ok0`);
  * `1/2 ≤ s < 12` (`region2`): 460 cells, `λ ≤ g` or `φ_up·(λ − g) ≤ r_lo` (`ok2`);
  * `0 < s ≤ 1/2` (`region3`): `φ(s) ≤ s²/3000` and `s²log(1/s) ≤ s`, against `r ≥ r_lo(0, 1/2)` (`ok3`).
-/

open Real

noncomputable section

namespace PivotCert

/-! ## Taylor bounds for `sin` and `cos` to order 8 -/

/-- `cos x ≥ 1 − x²/2 + x⁴/24 − x⁶/720` for `x ≥ 0`. -/
lemma cos_ge_six {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  let f (t : ℝ) : ℝ := Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
  have hderiv (t : ℝ) : deriv f t = t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    linarith [BallSharp.sin_le_quintic (le_of_lt ht)]
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [f, Real.cos_zero] at h
  linarith

/-- `sin x ≥ x − x³/6 + x⁵/120 − x⁷/5040` for `x ≥ 0`. -/
lemma sin_ge_seven {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  let f (t : ℝ) : ℝ := Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
  have hderiv (t : ℝ) : deriv f t = Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    linarith [cos_ge_six (le_of_lt ht)]
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [f, Real.sin_zero] at h
  linarith

/-- `cos x ≤ 1 − x²/2 + x⁴/24 − x⁶/720 + x⁸/40320` for `x ≥ 0`. -/
lemma cos_le_eight_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  let f (t : ℝ) : ℝ := 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - Real.cos t
  have hderiv (t : ℝ) : deriv f t = Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    linarith [sin_ge_seven (le_of_lt ht)]
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [f, Real.cos_zero] at h
  linarith

/-- `cos x ≤ 1 − x²/2 + x⁴/24 − x⁶/720 + x⁸/40320` for every `x`. -/
lemma cos_le_eight (x : ℝ) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  rcases le_total 0 x with h | h
  · exact cos_le_eight_of_nonneg h
  · have := cos_le_eight_of_nonneg (neg_nonneg.2 h)
    rw [Real.cos_neg] at this
    convert this using 1
    ring

/-! ## `1 − sinc² ≤ u = min(1, P₆)` -/

/-- `P₆(x) = x²/3 − 2x⁴/45 + x⁶/315`. -/
def p6R (x : ℝ) : ℝ := x ^ 2 / 3 - 2 * x ^ 4 / 45 + x ^ 6 / 315

/-- `u(x) = min(1, P₆(x))`. -/
def uR (x : ℝ) : ℝ := min 1 (p6R x)

/-- **`1 − sinc²x ≤ u(x)`**, from `sinc²x = (1 − cos 2x)/(2x²)` and `cos ≤ T₈`. -/
lemma one_sub_sinc_sq_le (x : ℝ) : 1 - Real.sinc x ^ 2 ≤ uR x := by
  refine le_min (by nlinarith [sq_nonneg (Real.sinc x)]) ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp [p6R]
  rw [Real.sinc_of_ne_zero hx, div_pow]
  have hx2 : 0 < x ^ 2 := by positivity
  have hc := cos_le_eight (2 * x)
  have hs : Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
    rw [Real.cos_two_mul, Real.cos_sq']; ring
  have key : x ^ 2 * (1 - p6R x) ≤ Real.sin x ^ 2 := by
    rw [hs]; unfold p6R; nlinarith [hc]
  have : 1 - p6R x ≤ Real.sin x ^ 2 / x ^ 2 := by rw [le_div_iff₀ hx2]; linarith
  linarith

/-- `P₆ ≥ 0`: `P₆(x) = x²((x² − 7)² + 56)/315`. -/
lemma p6R_nonneg (x : ℝ) : 0 ≤ p6R x := by
  have e : p6R x = x ^ 2 * ((x ^ 2 - 7) ^ 2 + 56) / 315 := by unfold p6R; ring
  rw [e]; positivity

/-- `P₆` is monotone on `[0, ∞)`. -/
lemma p6R_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : p6R x ≤ p6R y := by
  have hAB : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  have e : p6R y - p6R x = (y ^ 2 - x ^ 2) *
      (105 - 14 * (x ^ 2 + y ^ 2) + (x ^ 2) ^ 2 + x ^ 2 * y ^ 2 + (y ^ 2) ^ 2) / 315 := by
    unfold p6R; ring
  have hq : 0 ≤ 105 - 14 * (x ^ 2 + y ^ 2) + (x ^ 2) ^ 2 + x ^ 2 * y ^ 2 + (y ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2 + y ^ 2 - 28 / 3), sq_nonneg (x ^ 2 - y ^ 2)]
  have : 0 ≤ p6R y - p6R x := by
    rw [e]; exact div_nonneg (mul_nonneg (by linarith) hq) (by norm_num)
  linarith

/-- `u ≥ 0`. -/
lemma uR_nonneg (x : ℝ) : 0 ≤ uR x := le_min zero_le_one (p6R_nonneg x)

/-- `u ≤ 1`. -/
lemma uR_le_one (x : ℝ) : uR x ≤ 1 := min_le_left _ _

/-- `u(x) ≤ x²/3`. -/
lemma uR_le_sq (x : ℝ) : uR x ≤ x ^ 2 / 3 := by
  rcases le_or_gt (x ^ 2) 14 with h | h
  · refine (min_le_right _ _).trans ?_
    have e : p6R x = x ^ 2 / 3 + x ^ 4 * (x ^ 2 - 14) / 315 := by unfold p6R; ring
    rw [e]
    have : x ^ 4 * (x ^ 2 - 14) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  · exact (uR_le_one x).trans (by linarith)

/-- `u` is monotone on `[0, ∞)`. -/
lemma uR_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : uR x ≤ uR y :=
  min_le_min_left _ (p6R_mono hx hxy)

/-! ## The staircase: `Σ_{k<30}(1 − sinc²(s/(10·2^k))) ≤ S₃₀(s/10)` -/

/-- `S_n(x) = Σ_{k<n} u(x/2^k)`. -/
def sR (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range n, uR (x / 2 ^ k)

/-- `S₀ = 0`. -/
lemma sR_zero (x : ℝ) : sR 0 x = 0 := by simp [sR]

/-- Peeling the first term: `S_{n+1}(x) = u(x) + S_n(x/2)`. -/
lemma sR_succ (n : ℕ) (x : ℝ) : sR (n + 1) x = uR x + sR n (x / 2) := by
  unfold sR
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ', div_div]

/-- `S_n ≥ 0`. -/
lemma sR_nonneg (n : ℕ) (x : ℝ) : 0 ≤ sR n x := Finset.sum_nonneg fun _ _ => uR_nonneg _

/-- `S_n(x) ≤ (4/9)x²`, from `u(x) ≤ x²/3`. -/
lemma sR_le_sq (n : ℕ) (x : ℝ) : sR n x ≤ 4 / 9 * x ^ 2 := by
  induction n generalizing x with
  | zero => rw [sR_zero]; positivity
  | succ n ih =>
    rw [sR_succ]
    have h1 := uR_le_sq x
    have h2 := ih (x / 2)
    have e : 4 / 9 * (x / 2) ^ 2 = x ^ 2 / 9 := by ring
    linarith

/-- Peeling the first `m` terms: `S_{m+n}(x) = S_m(x) + S_n(x/2^m)`. -/
lemma sR_add (m n : ℕ) (x : ℝ) : sR (m + n) x = sR m x + sR n (x / 2 ^ m) := by
  unfold sR
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_add, div_div]

/-- `T(x) = S₈(x) + x²/147456`, the majorant of every `S_n(x)`. -/
def tR (x : ℝ) : ℝ := sR 8 x + x ^ 2 / 147456

/-- `T ≥ 0`. -/
lemma tR_nonneg (x : ℝ) : 0 ≤ tR x := by unfold tR; have := sR_nonneg 8 x; positivity

/-- `S_n(x) ≤ T(x)`: the terms after the eighth sum to at most `(4/9)(x/256)²`. -/
lemma sR_le_tR (n : ℕ) (x : ℝ) : sR n x ≤ tR x := by
  unfold tR
  rcases le_or_gt n 8 with h | h
  · have : sR n x ≤ sR 8 x := by
      unfold sR
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
        fun _ _ _ => uR_nonneg _
    have : 0 ≤ x ^ 2 / 147456 := by positivity
    linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h.le
    rw [sR_add]
    have h2 := sR_le_sq m (x / 2 ^ 8)
    have e : 4 / 9 * (x / 2 ^ 8) ^ 2 = x ^ 2 / 147456 := by ring
    linarith

/-- **The dyadic bound**: `S_n(2^j y) ≤ (j − 1) + u(2y) + T(y)` for `j ≥ 1`. -/
lemma sR_pow_le (y : ℝ) (j : ℕ) : ∀ n, sR n (2 ^ (j + 1) * y) ≤ j + uR (2 * y) + tR y := by
  have h0 := uR_nonneg (2 * y)
  have h1 := tR_nonneg y
  induction j with
  | zero =>
    intro n
    rcases n with _ | n
    · rw [sR_zero]; push_cast; linarith
    · rw [sR_succ]
      have := sR_le_tR n y
      have e : 2 ^ (0 + 1) * y / 2 = y := by ring
      rw [e, show (2 : ℝ) ^ (0 + 1) * y = 2 * y by ring]
      push_cast; linarith
  | succ j ih =>
    intro n
    rcases n with _ | n
    · rw [sR_zero]; positivity
    · rw [sR_succ]
      have e : 2 ^ (j + 1 + 1) * y / 2 = 2 ^ (j + 1) * y := by rw [pow_succ]; ring
      rw [e]
      have := ih n
      have := uR_le_one (2 ^ (j + 1 + 1) * y)
      push_cast; linarith

/-- `S_n` is monotone on `[0, ∞)`. -/
lemma sR_mono (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : sR n x ≤ sR n y :=
  Finset.sum_le_sum fun k _ => uR_mono (by positivity) (div_le_div_of_nonneg_right hxy (by positivity))

/-- `T` is monotone on `[0, ∞)`. -/
lemma tR_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : tR x ≤ tR y := by
  unfold tR
  have := sR_mono 8 hx hxy
  have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  linarith

/-- **The staircase bound**: `λ(s) ≤ 23/100 + (693/1000)S₃₀(s/10)`. -/
lemma lam_le (s : ℝ) : PivotMinor.lam s ≤ 23 / 100 + 693 / 1000 * sR 30 (s / 10) := by
  unfold PivotMinor.lam sR
  gcongr
  rw [div_div]
  exact one_sub_sinc_sq_le _

/-! ## `log y ≥ 2v + (2/3)v³`, `v = (y − 1)/(y + 1)` -/

/-- `ℓ(y) = 2v + (2/3)v³` with `v = (y − 1)/(y + 1)`. -/
def lgR (y : ℝ) : ℝ := (y - 1) / (y + 1) * (2 + 2 / 3 * ((y - 1) / (y + 1) * ((y - 1) / (y + 1))))

/-- **`ℓ(y) ≤ log y` for `y ≥ 1`**: the first two terms of `log((1 + v)/(1 − v)) = 2Σ v^{2k+1}/(2k + 1)`. -/
lemma lgR_le_log {y : ℝ} (hy : 1 ≤ y) : lgR y ≤ Real.log y := by
  have hy1 : 0 < y + 1 := by linarith
  set v := (y - 1) / (y + 1) with hv
  have hv0 : 0 ≤ v := div_nonneg (by linarith) hy1.le
  have hv1 : v < 1 := by rw [hv, div_lt_one hy1]; linarith
  have habs : |v| < 1 := by rw [abs_of_nonneg hv0]; exact hv1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hle := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hs
  have hlog : Real.log (1 + v) - Real.log (1 - v) = Real.log y := by
    have h1 : 1 + v = 2 * y / (y + 1) := by rw [hv]; field_simp; ring
    have h2 : 1 - v = 2 / (y + 1) := by rw [hv]; field_simp; ring
    rw [← Real.log_div (by rw [h1]; positivity) (by rw [h2]; positivity), h1, h2]
    congr 1
    field_simp
  rw [hlog] at hle
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one] at hle
  unfold lgR
  rw [← hv]
  linarith

/-! ## The archimedean weight: `Re ψ(¼ + it/2) ≥ log(t/2) − ē(t)` -/

/-- `ē` as a function of `b² = t²/4`. -/
def ebBR (b2 : ℝ) : ℝ := 9 / (8 * (81 / 16 + b2)) + 81 / (192 * ((81 / 16 + b2) * (81 / 16 + b2)))
  + 1 / 4 / (1 / 16 + b2) + 5 / 4 / (25 / 16 + b2) + 1 / 3000

/-- `ē(t) = 9/(8r) + 81/(192r²) + (1/4)/(1/16 + b²) + (5/4)/(25/16 + b²) + 1/3000`, `b = t/2`, `r = 81/16 + b²`. -/
def ebR (t : ℝ) : ℝ := ebBR (t * t * (1 / 4))

/-- `ē` is antitone on `[0, ∞)`. -/
lemma ebR_anti {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') : ebR t' ≤ ebR t := by
  unfold ebR ebBR
  have hb : t * t * (1 / 4) ≤ t' * t' * (1 / 4) := by nlinarith
  have hb0 : 0 ≤ t * t * (1 / 4) := by positivity
  have hb1 : 0 ≤ t' * t' * (1 / 4) := by linarith
  gcongr

/-- **Stirling with two recurrence steps**: `Re ψ(¼ + it/2) ≥ log t − log 2 − ē(t)` for `t > 0`. -/
lemma psiRe_ge {t : ℝ} (ht : 0 < t) : Real.log t - Real.log 2 - ebR t ≤ WeilForm.psiRe t := by
  have hq := DigammaStirling.re_digamma_quarter 2 (t / 2)
  have e : WeilForm.psiRe t = (Complex.digamma (1 / 4 + ((t / 2 : ℝ) : ℂ) * Complex.I)).re := by
    unfold WeilForm.psiRe; rw [BallDensity.zB_eq]
  rw [← e, BallSharp.psiApx2_eq] at hq
  have herr : (1 : ℝ) / (120 * (((2 : ℕ) : ℝ) + 1 / 4) ^ 4) ≤ 1 / 3000 := by norm_num
  have hq' := (abs_le.1 hq).1
  set b := t / 2 with hb
  have hb0 : 0 < b := by positivity
  set r := (9 / 4 : ℝ) ^ 2 + b ^ 2 with hr
  have hr0 : 0 < r := by positivity
  have hlog : Real.log t - Real.log 2 ≤ Real.log r / 2 := by
    have h1 : Real.log t - Real.log 2 = Real.log b := by rw [hb, Real.log_div ht.ne' two_ne_zero]
    have h2 : Real.log (b ^ 2) ≤ Real.log r :=
      Real.log_le_log (by positivity) (le_add_of_nonneg_left (by positivity))
    rw [Real.log_pow, Nat.cast_ofNat] at h2
    linarith only [h1, h2]
  have hdrop : -(81 / 16) / (12 * r ^ 2) ≤ -((9 / 4 : ℝ) ^ 2 - b ^ 2) / (12 * r ^ 2) :=
    div_le_div_of_nonneg_right (by linarith only [sq_nonneg b, show ((9 : ℝ) / 4) ^ 2 = 81 / 16 by norm_num])
      (by positivity)
  have eb : ebR t = 9 / 4 / (2 * r) + (81 / 16) / (12 * r ^ 2) + 1 / 4 / ((1 / 4) ^ 2 + b ^ 2)
      + 5 / 4 / ((5 / 4) ^ 2 + b ^ 2) + 1 / 3000 := by
    unfold ebR ebBR
    have e1 : t * t * (1 / 4) = b ^ 2 := by rw [hb]; ring
    rw [e1, hr]
    field_simp
    ring
  rw [eb]
  have e3 : -(((9 / 4 : ℝ) ^ 2 - b ^ 2) / (12 * r ^ 2)) = -((9 / 4 : ℝ) ^ 2 - b ^ 2) / (12 * r ^ 2) := by ring
  have e4 : -((81 / 16 : ℝ) / (12 * r ^ 2)) = -(81 / 16) / (12 * r ^ 2) := by ring
  linarith only [hq', herr, hlog, hdrop, e3, e4]

/-- `Re ψ(¼ + it/2)` is even in `t`. -/
lemma psiRe_neg (t : ℝ) : WeilForm.psiRe (-t) = WeilForm.psiRe t := by
  unfold WeilForm.psiRe
  rw [WeilForm.digamma_zB_neg, Complex.conj_re]

/-- `g(s) = log s − log 2 − log π − ē(2s)`. -/
def gR (s : ℝ) : ℝ := Real.log s - Real.log 2 - Real.log π - ebR (2 * s)

/-- **Uniformly in `N ≥ 2`**: `L(Ns) − log N ≥ g(s)` for `s > 0`. -/
lemma gR_le {N : ℕ} (hN : 2 ≤ N) {s : ℝ} (hs : 0 < s) :
    gR s ≤ WeilForm.psiRe ((N : ℝ) * s) - Real.log π - Real.log N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h := psiRe_ge (mul_pos hN0 hs)
  have ha := ebR_anti (by positivity : (0 : ℝ) ≤ 2 * s) (by nlinarith : 2 * s ≤ (N : ℝ) * s)
  rw [Real.log_mul hN0.ne' hs.ne'] at h
  unfold gR
  linarith

/-! ## `sinc` from below: `sl(x) = 1 − x²/6 + x⁴/120 − x⁶/5040` -/

/-- `sl` as a function of `z = x²`. -/
def slAR (z : ℝ) : ℝ := 1 - z * (1 / 6 - z * (1 / 120 - z * (1 / 5040)))

/-- `sin x/x ≥ sl(x)` for `x > 0`. -/
lemma slAR_le_sin_div {x : ℝ} (hx : 0 < x) : slAR (x * x) ≤ Real.sin x / x := by
  rw [le_div_iff₀ hx]
  have := sin_ge_seven hx.le
  unfold slAR
  nlinarith

/-- `sl` decreases in `z = x²`: `sl(z) − sl(w) = (w − z)(840 − 42(z + w) + z² + zw + w²)/5040`. -/
lemma slAR_anti {z w : ℝ} (hzw : z ≤ w) : slAR w ≤ slAR z := by
  have e : slAR z - slAR w = (w - z) * (840 - 42 * (z + w) + z ^ 2 + z * w + w ^ 2) / 5040 := by
    unfold slAR; ring
  have hq : 0 ≤ 840 - 42 * (z + w) + z ^ 2 + z * w + w ^ 2 := by
    nlinarith [sq_nonneg (z + w - 28), sq_nonneg (z - w)]
  have : 0 ≤ slAR z - slAR w := by
    rw [e]; exact div_nonneg (mul_nonneg (by linarith) hq) (by norm_num)
  linarith

/-- `sl(0) = 1`. -/
lemma slAR_zero : slAR 0 = 1 := by unfold slAR; ring

/-- **`sinc²z ≥ sl(D/2)²`** for `|z| ≤ D/2`, when `sl(D/2) > 0`. -/
lemma sq_le_sinc_sq {z D : ℝ} (hz : |z| ≤ D / 2) (hpos : 0 < slAR (D * D / 4)) :
    slAR (D * D / 4) ^ 2 ≤ Real.sinc z ^ 2 := by
  have hD : 0 ≤ D / 2 := (abs_nonneg z).trans hz
  have hzz : |z| * |z| ≤ D * D / 4 := by
    have := mul_le_mul hz hz (abs_nonneg z) hD
    linarith
  have hw : slAR (D * D / 4) ≤ slAR (|z| * |z|) := slAR_anti hzz
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [Real.sinc_zero, one_pow]
    have : slAR (D * D / 4) ≤ 1 := by
      have := slAR_anti (by positivity : (0 : ℝ) ≤ D * D / 4)
      rwa [slAR_zero] at this
    nlinarith
  · have habs : 0 < |z| := abs_pos.2 hz0
    have hs := slAR_le_sin_div habs
    have hsinc : Real.sinc z = Real.sin |z| / |z| := by
      rw [← Real.sinc_of_ne_zero habs.ne']
      rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, Real.sinc_neg]
    rw [hsinc]
    exact pow_le_pow_left₀ hpos.le (hw.trans hs) 2

/-! ## `φ` from above -/

/-- `ρ(a) = 7a/36 − a²/18 + a³/162 − a⁴/3888`. -/
def rhoR (a : ℝ) : ℝ := a * (7 / 36 - a * (1 / 18 - a * (1 / 162 - a * (1 / 3888))))

/-- `1 − K(x) ≤ x²ρ(x²)` for `x² ≤ 6`, from `sin²x ≥ x²(1 − x²/6)²`. -/
lemma one_sub_kk_le_rho {x : ℝ} (hx0 : x ≠ 0) (hx6 : x ^ 2 ≤ 6) : 1 - PivotPhi.kk x ≤ x ^ 2 * rhoR (x ^ 2) := by
  have hxpos : 0 < x ^ 2 := by positivity
  have hsin := PivotPhi.sin_sq_ge' hx6
  have hsinc : (1 - x ^ 2 / 6) ^ 2 ≤ (Real.sin x / x) ^ 2 := by
    rw [div_pow, le_div_iff₀ hxpos]; linarith
  set a := x ^ 2 with ha
  have hK : (1 - a / 6) ^ 2 * (1 + a * (1 - a / 6) ^ 2 / 3) ≤ PivotPhi.kk x := by
    unfold PivotPhi.kk
    have h1 : 1 + a * (1 - a / 6) ^ 2 / 3 ≤ 1 + Real.sin x ^ 2 / 3 := by linarith
    have h2 : 0 ≤ 1 + a * (1 - a / 6) ^ 2 / 3 := by positivity
    calc (1 - a / 6) ^ 2 * (1 + a * (1 - a / 6) ^ 2 / 3)
        ≤ (Real.sin x / x) ^ 2 * (1 + a * (1 - a / 6) ^ 2 / 3) := mul_le_mul_of_nonneg_right hsinc h2
      _ ≤ (Real.sin x / x) ^ 2 * (1 + Real.sin x ^ 2 / 3) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have e : 1 - (1 - a / 6) ^ 2 * (1 + a * (1 - a / 6) ^ 2 / 3) = a * rhoR a := by unfold rhoR; ring
  linarith

/-- **`φ(s) ≤ (999/1000)ρ((s/5)²)/25`** while `(s/5)² ≤ 6`. -/
lemma phi_le_rho {s : ℝ} (hs : 0 < s) (h6 : s * s / 25 ≤ 6) :
    PivotPhi.phi s ≤ 999 / 1000 * rhoR (s * s / 25) / 25 := by
  have hxa : (s / 5) ^ 2 = s * s / 25 := by ring
  have h := one_sub_kk_le_rho (x := s / 5) (by positivity) (by rw [hxa]; exact h6)
  rw [hxa] at h
  have hs2 : 0 < s ^ 2 := by positivity
  rw [PivotPhi.phi_eq]
  have : (1 - PivotPhi.kk (s / 5)) / s ^ 2 ≤ rhoR (s * s / 25) / 25 := by
    rw [div_le_div_iff₀ hs2 (by norm_num)]
    have e : s * s / 25 * rhoR (s * s / 25) * 25 = rhoR (s * s / 25) * s ^ 2 := by ring
    nlinarith
  have e : 999 / 1000 * rhoR (s * s / 25) / 25 = 999 / 1000 * (rhoR (s * s / 25) / 25) := by ring
  rw [e]
  linarith

/-- `ρ ≤ ρ(3)`: `ρ(3) − ρ(a) = (a − 3)²(a² − 18a + 99)/3888`. -/
lemma rhoR_le_three (a : ℝ) : rhoR a ≤ rhoR 3 := by
  have e : rhoR 3 - rhoR a = (a - 3) ^ 2 * ((a - 9) ^ 2 + 18) / 3888 := by unfold rhoR; ring
  have : 0 ≤ rhoR 3 - rhoR a := by rw [e]; positivity
  linarith

/-- `ρ` is monotone on `[0, 3]`: in `p = 3 − a`, `ρ′ = p(p² + 9p + 27)/972`. -/
lemma rhoR_mono {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 3) : rhoR a ≤ rhoR b := by
  have e : rhoR b - rhoR a = (b - a) * (((3 - a) ^ 3 + (3 - a) ^ 2 * (3 - b) + (3 - a) * (3 - b) ^ 2
      + (3 - b) ^ 3) / 4 + 3 * ((3 - a) ^ 2 + (3 - a) * (3 - b) + (3 - b) ^ 2)
      + 27 * ((3 - a) + (3 - b)) / 2) / 972 := by unfold rhoR; ring
  have h1 : 0 ≤ 3 - a := by linarith
  have h2 : 0 ≤ 3 - b := by linarith
  have : 0 ≤ rhoR b - rhoR a := by
    rw [e]
    exact div_nonneg (mul_nonneg (by linarith) (by positivity)) (by norm_num)
  linarith

/-- **`φ` from `sinc ≥ sl`** on `[s_a, s_b]`: `K(x) ≥ w²(1 + (s_a/5)²w²/3)`, `w = sl(s_b/5) > 0`. -/
lemma phi_le_klo {sa sb s : ℝ} (hsa : 0 < sa) (h1 : sa ≤ s) (h2 : s ≤ sb)
    (hw : 0 < slAR (sb * sb / 25)) :
    PivotPhi.phi s ≤ 999 / 1000 * (1 - slAR (sb * sb / 25) * slAR (sb * sb / 25) *
      (1 + sa * sa / 25 * (slAR (sb * sb / 25) * slAR (sb * sb / 25)) / 3)) / (sa * sa) := by
  set w := slAR (sb * sb / 25) with hwdef
  have hs : 0 < s := by linarith
  set x := s / 5 with hx
  have hx0 : 0 < x := by positivity
  have hxx : x * x ≤ sb * sb / 25 := by
    have h5 : x ≤ sb / 5 := by rw [hx]; linarith only [h2]
    have := mul_le_mul h5 h5 hx0.le (by linarith only [hx0, h5])
    linarith only [this]
  have hsinc : w ≤ Real.sin x / x := (slAR_anti hxx).trans (slAR_le_sin_div hx0)
  have hsin : sa / 5 * w ≤ Real.sin x := by
    have : Real.sin x = x * (Real.sin x / x) := by field_simp
    rw [this]
    exact mul_le_mul (by rw [hx]; linarith) hsinc hw.le hx0.le
  have hsin2 : sa * sa / 25 * (w * w) ≤ Real.sin x ^ 2 := by
    have h0 : 0 ≤ sa / 5 * w := by positivity
    have := pow_le_pow_left₀ h0 hsin 2
    have e : (sa / 5 * w) ^ 2 = sa * sa / 25 * (w * w) := by ring
    linarith only [this, e]
  have hK : w * w * (1 + sa * sa / 25 * (w * w) / 3) ≤ PivotPhi.kk x := by
    unfold PivotPhi.kk
    have hq : w * w ≤ (Real.sin x / x) ^ 2 := by rw [sq]; exact mul_self_le_mul_self hw.le hsinc
    have hA : 0 ≤ 1 + sa * sa / 25 * (w * w) / 3 := by positivity
    calc w * w * (1 + sa * sa / 25 * (w * w) / 3) ≤ (Real.sin x / x) ^ 2 * (1 + sa * sa / 25 * (w * w) / 3) :=
          mul_le_mul_of_nonneg_right hq hA
      _ ≤ (Real.sin x / x) ^ 2 * (1 + Real.sin x ^ 2 / 3) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have hk1 := PivotPhi.kk_le_one x
  rw [PivotPhi.phi_eq, ← hx]
  have hsa2 : 0 < sa * sa := by positivity
  have hss : sa * sa ≤ s ^ 2 := by rw [sq]; exact mul_self_le_mul_self hsa.le h1
  have hnum : 0 ≤ 1 - w * w * (1 + sa * sa / 25 * (w * w) / 3) := by linarith
  have : (1 - PivotPhi.kk x) / s ^ 2 ≤ (1 - w * w * (1 + sa * sa / 25 * (w * w) / 3)) / (sa * sa) := by
    calc (1 - PivotPhi.kk x) / s ^ 2 ≤ (1 - w * w * (1 + sa * sa / 25 * (w * w) / 3)) / s ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (1 - w * w * (1 + sa * sa / 25 * (w * w) / 3)) / (sa * sa) :=
          div_le_div_of_nonneg_left hnum hsa2 hss
  have e : 999 / 1000 * (1 - w * w * (1 + sa * sa / 25 * (w * w) / 3)) / (sa * sa) =
      999 / 1000 * ((1 - w * w * (1 + sa * sa / 25 * (w * w) / 3)) / (sa * sa)) := by ring
  rw [e]
  linarith

/-! ## Exact arithmetic for the kernel: `(p − m)/(d + 1)` with `p, m, d ∈ ℕ` -/

/-- A rational `(p − m)/(d + 1)`, `p m d : ℕ`. Its arithmetic is `ℕ`-arithmetic, which the kernel does with
GMP, and it needs no normalisation and no invariant. -/
structure Fr where
  /-- the positive part of the numerator -/
  p : ℕ
  /-- the negative part of the numerator -/
  m : ℕ
  /-- the denominator, minus one -/
  d : ℕ

namespace Fr

/-- The value `(p − m)/(d + 1)`. -/
def val (a : Fr) : ℝ := ((a.p : ℝ) - a.m) / (a.d + 1)

instance : Add Fr :=
  ⟨fun a b => ⟨a.p * (b.d + 1) + b.p * (a.d + 1), a.m * (b.d + 1) + b.m * (a.d + 1), a.d * b.d + a.d + b.d⟩⟩

instance : Sub Fr :=
  ⟨fun a b => ⟨a.p * (b.d + 1) + b.m * (a.d + 1), a.m * (b.d + 1) + b.p * (a.d + 1), a.d * b.d + a.d + b.d⟩⟩

instance : Mul Fr := ⟨fun a b => ⟨a.p * b.p + a.m * b.m, a.p * b.m + a.m * b.p, a.d * b.d + a.d + b.d⟩⟩

instance : Div Fr := ⟨fun a b =>
  if b.m < b.p then ⟨a.p * (b.d + 1), a.m * (b.d + 1), (a.d + 1) * (b.p - b.m) - 1⟩
  else if b.p < b.m then ⟨a.m * (b.d + 1), a.p * (b.d + 1), (a.d + 1) * (b.m - b.p) - 1⟩
  else ⟨0, 0, 0⟩⟩

/-- The constant `n/d`. -/
def fr (n d : ℕ) : Fr := ⟨n, 0, d - 1⟩

/-- The constant `n`. -/
def nat (n : ℕ) : Fr := ⟨n, 0, 0⟩

/-- `a ≤ b`, by cross-multiplication. -/
def ble (a b : Fr) : Bool := Nat.ble (a.p * (b.d + 1) + b.m * (a.d + 1)) (b.p * (a.d + 1) + a.m * (b.d + 1))

/-- `a < b`. -/
def blt (a b : Fr) : Bool := !ble b a

/-- `min a b`. -/
def fmin (a b : Fr) : Fr := if ble a b then a else b

/-- `max a b`. -/
def fmax (a b : Fr) : Fr := if ble a b then b else a

/-- The denominator `d + 1` is positive. -/
lemma den_pos (a : Fr) : (0 : ℝ) < a.d + 1 := by positivity

/-- `val` is additive. -/
@[simp] lemma val_add (a b : Fr) : (a + b).val = a.val + b.val := by
  have h1 := a.den_pos; have h2 := b.den_pos
  show val ⟨_, _, _⟩ = _
  simp only [val]; push_cast; field_simp; ring

/-- `val` commutes with subtraction. -/
@[simp] lemma val_sub (a b : Fr) : (a - b).val = a.val - b.val := by
  have h1 := a.den_pos; have h2 := b.den_pos
  show val ⟨_, _, _⟩ = _
  simp only [val]; push_cast; field_simp; ring

/-- `val` is multiplicative. -/
@[simp] lemma val_mul (a b : Fr) : (a * b).val = a.val * b.val := by
  have h1 := a.den_pos; have h2 := b.den_pos
  show val ⟨_, _, _⟩ = _
  simp only [val]; push_cast; field_simp; ring

/-- `(k − 1) + 1 = k` in `ℝ` for `k ≥ 1`. -/
lemma cast_pred {k : ℕ} (hk : 1 ≤ k) : (((k - 1 : ℕ) : ℝ) + 1) = k := by
  rw [Nat.cast_sub hk]; ring

/-- `val` commutes with division (by a value of either sign, or `0`). -/
@[simp] lemma val_div (a b : Fr) : (a / b).val = a.val / b.val := by
  have h1 := a.den_pos; have h2 := b.den_pos
  show val (if b.m < b.p then _ else _) = _
  split_ifs with h h'
  · have hk : 1 ≤ (a.d + 1) * (b.p - b.m) := Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt h)
    have hb : (b.p : ℝ) - b.m ≠ 0 := by
      have : (b.m : ℝ) < b.p := by exact_mod_cast h
      exact ne_of_gt (by linarith)
    simp only [val]
    rw [cast_pred hk]
    push_cast [Nat.cast_sub h.le]
    field_simp
  · have hk : 1 ≤ (a.d + 1) * (b.m - b.p) := Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt h')
    have hb : (b.m : ℝ) - b.p ≠ 0 := by
      have : (b.p : ℝ) < b.m := by exact_mod_cast h'
      exact ne_of_gt (by linarith)
    have hb' : (b.p : ℝ) - b.m ≠ 0 := by
      have : (b.p : ℝ) < b.m := by exact_mod_cast h'
      exact ne_of_lt (by linarith)
    simp only [val]
    rw [cast_pred hk]
    push_cast [Nat.cast_sub h'.le]
    field_simp
    ring
  · have : b.p = b.m := by omega
    simp [val, this]

/-- The value of `nat n`. -/
@[simp] lemma val_nat (n : ℕ) : (nat n).val = n := by simp [val, nat]

/-- The value of `fr n d`. -/
@[simp] lemma val_fr (n d : ℕ) (hd : d ≠ 0) : (fr n d).val = n / d := by
  simp only [val, fr]
  rw [cast_pred (Nat.one_le_iff_ne_zero.2 hd)]
  simp

/-- `ble` decides `≤` of the values. -/
lemma ble_iff (a b : Fr) : ble a b = true ↔ a.val ≤ b.val := by
  have h1 := a.den_pos; have h2 := b.den_pos
  rw [ble, Nat.ble_eq, val, val, div_le_div_iff₀ h1 h2, ← Nat.cast_le (α := ℝ)]
  push_cast
  constructor <;> intro h <;> nlinarith

/-- `blt` decides `<` of the values. -/
lemma blt_iff (a b : Fr) : blt a b = true ↔ a.val < b.val := by
  rw [blt, Bool.not_eq_true', ← not_le, ← ble_iff, Bool.not_eq_true]

/-- `val` commutes with `min`. -/
@[simp] lemma val_fmin (a b : Fr) : (fmin a b).val = min a.val b.val := by
  unfold fmin
  split_ifs with h
  · exact (min_eq_left ((ble_iff a b).1 h)).symm
  · rw [Bool.not_eq_true] at h
    have : ¬ a.val ≤ b.val := fun h' => by rw [(ble_iff a b).2 h'] at h; exact Bool.noConfusion h
    exact (min_eq_right (le_of_not_ge this)).symm

/-- `val` commutes with `max`. -/
@[simp] lemma val_fmax (a b : Fr) : (fmax a b).val = max a.val b.val := by
  unfold fmax
  split_ifs with h
  · exact (max_eq_right ((ble_iff a b).1 h)).symm
  · rw [Bool.not_eq_true] at h
    have : ¬ a.val ≤ b.val := fun h' => by rw [(ble_iff a b).2 h'] at h; exact Bool.noConfusion h
    exact (max_eq_left (le_of_not_ge this)).symm

end Fr

/-! ## The bound functions, in exact arithmetic

Each `…F` computes its real counterpart `…R` exactly (`val_…F`), or bounds it (`logloF_le`, `phi_le_phiupF`,
`oneF_le`, `rloF_le`, `gloF_le`). -/

open Fr

/-- `L2LO = 0.6931471803 < log 2`. -/
def l2lo : Fr := fr 6931471803 10000000000

/-- `L2HI = 0.6931471808 > log 2`. -/
def l2hi : Fr := fr 6931471808 10000000000

/-- `LPIHI = 1.1558 ≥ log π`. -/
def lpihi : Fr := fr 11558 10000

/-- `L2LO ≤ log 2`. -/
lemma l2lo_le : l2lo.val ≤ Real.log 2 := by
  rw [l2lo, val_fr _ _ (by norm_num)]; have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

/-- `log 2 ≤ L2HI`. -/
lemma l2hi_ge : Real.log 2 ≤ l2hi.val := by
  rw [l2hi, val_fr _ _ (by norm_num)]; have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

/-- `log π ≤ LPIHI`. -/
lemma lpihi_ge : Real.log π ≤ lpihi.val := by
  rw [lpihi, val_fr _ _ (by norm_num)]; have := BallSharp.log_pi_le_s; norm_num at this ⊢; linarith

/-- `P₆`. -/
def p6F (x : Fr) : Fr := x * x * (fr 1 3 - x * x * (fr 2 45 - x * x * fr 1 315))

lemma val_p6F (x : Fr) : (p6F x).val = p6R x.val := by
  simp [p6F, p6R]; ring

/-- `u = min(1, P₆)`. -/
def uF (x : Fr) : Fr := fmin (nat 1) (p6F x)

lemma val_uF (x : Fr) : (uF x).val = uR x.val := by simp [uF, uR, val_p6F]

/-- `S_n`. -/
def sF : ℕ → Fr → Fr
  | 0, _ => nat 0
  | n + 1, y => uF y + sF n (y * fr 1 2)

lemma val_sF (n : ℕ) (y : Fr) : (sF n y).val = sR n y.val := by
  induction n generalizing y with
  | zero => simp [sF, sR_zero]
  | succ n ih => rw [sF, val_add, val_uF, ih, sR_succ]; simp; ring_nf

/-- `T`. -/
def tF (y : Fr) : Fr := sF 8 y + y * y * fr 1 147456

lemma val_tF (y : Fr) : (tF y).val = tR y.val := by simp [tF, tR, val_sF]; ring

/-- `ē` in `b²`. -/
def ebBF (b2 : Fr) : Fr := nat 9 / (nat 8 * (fr 81 16 + b2)) + nat 81 / (nat 192 * ((fr 81 16 + b2) * (fr 81 16 + b2)))
  + fr 1 4 / (fr 1 16 + b2) + fr 5 4 / (fr 25 16 + b2) + fr 1 3000

/-- `ē`. -/
def ebF (t : Fr) : Fr := ebBF (t * t * fr 1 4)

lemma val_ebF (t : Fr) : (ebF t).val = ebR t.val := by simp [ebF, ebBF, ebR, ebBR]

/-- `ℓ`. -/
def lgF (y : Fr) : Fr :=
  (y - nat 1) / (y + nat 1) * (nat 2 + fr 2 3 * ((y - nat 1) / (y + nat 1) * ((y - nat 1) / (y + nat 1))))

lemma val_lgF (y : Fr) : (lgF y).val = lgR y.val := by simp [lgF, lgR]

/-- The number of halvings that bring `y ≥ 1` into `[1, 2)` (with `n` steps of fuel). -/
def klog : ℕ → Fr → ℕ
  | 0, _ => 0
  | n + 1, y => if ble (nat 2) y then klog n (y * fr 1 2) + 1 else 0

/-- `2^k ≤ y` for the `k = klog n y` halvings of `y ≥ 1`. -/
lemma two_pow_klog_le (n : ℕ) : ∀ y : Fr, 1 ≤ y.val → (2 : ℝ) ^ klog n y ≤ y.val := by
  induction n with
  | zero => intro y hy; simpa [klog] using hy
  | succ n ih =>
    intro y hy
    unfold klog
    split_ifs with h
    · rw [ble_iff, val_nat] at h
      have h2 := ih (y * fr 1 2) (by simp; push_cast at h; linarith)
      simp at h2
      rw [pow_succ]
      linarith
    · simpa using hy

/-- `log p` from below: `k·L2LO + ℓ(p/2^k)` with `p/2^k ∈ [1, 2)`, or `ℓ(2p) − L2HI` for `p < 1`. -/
def logloF (p : Fr) : Fr :=
  if blt p (nat 1) then lgF (nat 2 * p) - l2hi else nat (klog 20 p) * l2lo + lgF (p / nat (2 ^ klog 20 p))

/-- **`log p` from below**, for `p ≥ 1/2`. -/
lemma logloF_le {p : Fr} (hp : 1 / 2 ≤ p.val) : (logloF p).val ≤ Real.log p.val := by
  unfold logloF
  split_ifs with h
  · rw [blt_iff, val_nat] at h
    simp only [val_sub, val_lgF, val_mul, val_nat]
    have h2 : 1 ≤ (2 : ℝ) * p.val := by linarith
    have hl := lgR_le_log h2
    rw [Real.log_mul two_ne_zero (by linarith)] at hl
    have := l2hi_ge
    push_cast at hl ⊢
    linarith
  · rw [blt_iff, not_lt, val_nat] at h
    push_cast at h
    have hk := two_pow_klog_le 20 p h
    simp only [val_add, val_mul, val_nat, val_lgF, val_div]
    push_cast
    set k := klog 20 p
    have hk0 : (0 : ℝ) < 2 ^ k := by positivity
    have hy : 1 ≤ p.val / 2 ^ k := by rw [le_div_iff₀ hk0]; linarith
    have hl := lgR_le_log hy
    rw [Real.log_div (by linarith) hk0.ne', Real.log_pow] at hl
    have := l2lo_le
    have : (k : ℝ) * l2lo.val ≤ k * Real.log 2 := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg k)
    linarith

/-- `sl` in `z = x²`. -/
def slAF (z : Fr) : Fr := nat 1 - z * (fr 1 6 - z * (fr 1 120 - z * fr 1 5040))

lemma val_slAF (z : Fr) : (slAF z).val = slAR z.val := by simp [slAF, slAR]

/-- `ρ`. -/
def rhoF (a : Fr) : Fr := a * (fr 7 36 - a * (fr 1 18 - a * (fr 1 162 - a * fr 1 3888)))

lemma val_rhoF (a : Fr) : (rhoF a).val = rhoR a.val := by simp [rhoF, rhoR]

/-- The bound of `φ` on `[s_a, s_b]` from `sinc ≥ sl`. -/
def phiB1F (sa w : Fr) : Fr :=
  fr 999 1000 * (nat 1 - w * w * (nat 1 + sa * sa * fr 1 25 * (w * w) * fr 1 3)) / (sa * sa)

/-- The bound of `φ` on `[s_a, s_b]` from `ρ`. -/
def phiB2F (ab : Fr) : Fr := fr 999 1000 * (if ble ab (nat 3) then rhoF ab else rhoF (nat 3)) * fr 1 25

/-- `φ` from above on `[s_a, s_b]`. -/
def phiupF (sa sb : Fr) : Fr := fmin (phiB1F sa (slAF (sb * sb * fr 1 25))) (phiB2F (sb * sb * fr 1 25))

/-- **`φ ≤ φ_up` on `[s_a, s_b]`**, while `sl(s_b/5) > 0` and `(s_b/5)² ≤ 6`. -/
lemma phi_le_phiupF {sa sb : Fr} {s : ℝ} (hsa : 0 < sa.val) (h1 : sa.val ≤ s) (h2 : s ≤ sb.val)
    (hw : 0 < slAR (sb.val * sb.val / 25)) (h6 : sb.val * sb.val / 25 ≤ 6) :
    PivotPhi.phi s ≤ (phiupF sa sb).val := by
  have hs : 0 < s := by linarith
  have hss : s * s / 25 ≤ sb.val * sb.val / 25 := by
    have := mul_self_le_mul_self hs.le h2
    linarith only [this]
  rw [phiupF, val_fmin]
  refine le_min ?_ ?_
  · have h := phi_le_klo hsa h1 h2 hw
    have e : (phiB1F sa (slAF (sb * sb * fr 1 25))).val = 999 / 1000 * (1 - slAR (sb.val * sb.val / 25) *
        slAR (sb.val * sb.val / 25) * (1 + sa.val * sa.val / 25 *
        (slAR (sb.val * sb.val / 25) * slAR (sb.val * sb.val / 25)) / 3)) / (sa.val * sa.val) := by
      simp only [phiB1F, val_mul, val_div, val_sub, val_add, val_nat, val_slAF, val_fr _ _ (by norm_num : 1000 ≠ 0),
        val_fr _ _ (by norm_num : 25 ≠ 0), val_fr _ _ (by norm_num : 3 ≠ 0)]
      push_cast
      ring_nf
    rw [e]; exact h
  · have h := phi_le_rho hs (hss.trans h6)
    unfold phiB2F
    split_ifs with hb
    · rw [ble_iff] at hb
      simp only [val_mul, val_nat, val_rhoF, val_fr _ _ (by norm_num : 1000 ≠ 0),
        val_fr _ _ (by norm_num : 25 ≠ 0)] at hb ⊢
      push_cast at hb ⊢
      have e : sb.val * sb.val / 25 = sb.val * sb.val * (1 / 25) := by ring
      have := rhoR_mono (a := s * s / 25) (b := sb.val * sb.val * (1 / 25)) (by linarith only [hss, e])
        (by linarith only [hb])
      linarith only [h, this]
    · simp only [val_mul, val_nat, val_rhoF, val_fr _ _ (by norm_num : 1000 ≠ 0),
        val_fr _ _ (by norm_num : 25 ≠ 0)]
      push_cast
      have := rhoR_le_three (s * s / 25)
      linarith only [h, this]

/-- `w² if w > 0`, else `0`. -/
def sq0F (w : Fr) : Fr := if blt (nat 0) w then w * w else nat 0

/-- `sinc²z ≥ one(D)` for `|z| ≤ D/2`. -/
def oneF (D : Fr) : Fr := if ble D (nat 6) then sq0F (slAF (D * D * fr 1 4)) else nat 0

/-- **`one(D) ≤ sinc²z`** for `|z| ≤ D/2`. -/
lemma oneF_le {D : Fr} {z : ℝ} (hz : |z| ≤ D.val / 2) : (oneF D).val ≤ Real.sinc z ^ 2 := by
  unfold oneF sq0F
  split_ifs with h1 h2
  · rw [blt_iff, val_nat, val_slAF] at h2
    simp only [val_mul, val_slAF, val_fr _ _ (by norm_num : 4 ≠ 0)] at h2 ⊢
    push_cast at h2 ⊢
    have e : D.val * D.val * (1 / 4) = D.val * D.val / 4 := by ring
    rw [e] at h2 ⊢
    have := sq_le_sinc_sq hz h2
    rw [sq] at this
    exact this
  · simp only [val_nat]; push_cast; positivity
  · simp only [val_nat]; push_cast; positivity

/-- The two `sinc²` of a bump, from below on `[s_a, s_b]`. -/
def bumploF (sa sb g : Fr) : Fr := oneF (fmax (g - sa) (sb - g)) + oneF (sb + g)

/-- **A bump from below** on `[s_a, s_b] ⊆ [0, ∞)`, centred at `γ ≥ 0`. -/
lemma bumploF_le {sa sb g : Fr} {s : ℝ} (h1 : sa.val ≤ s) (h2 : s ≤ sb.val) (hs : 0 ≤ s) (hg : 0 ≤ g.val) :
    (bumploF sa sb g).val ≤ PivotMinor.bump g.val s := by
  unfold bumploF PivotMinor.bump
  rw [val_add]
  refine add_le_add (oneF_le ?_) (oneF_le ?_)
  · rw [val_fmax, val_sub, val_sub, abs_le]
    constructor
    · have := le_max_left (g.val - sa.val) (sb.val - g.val); linarith
    · have := le_max_right (g.val - sa.val) (sb.val - g.val); linarith
  · rw [val_add, abs_of_nonneg (by linarith)]
    linarith

/-- The bumps' centres and weights. -/
def bumpF : List (Fr × Fr) :=
  [(fr 3 2, fr 193 1000000), (nat 2, fr 23 500000), (nat 3, fr 1021 1000000), (fr 7 2, fr 593 1000000),
    (nat 4, fr 71 125000), (fr 9 2, fr 617 1000000), (nat 7, fr 1433 1000000), (fr 15 2, fr 39 500000),
    (fr 17 2, fr 3 250000)]

/-- `r` with the bumps' data in `Fr`. -/
lemma rr_eq (s : ℝ) : PivotMinor.rr s = (bumpF.map fun q => q.2.val * PivotMinor.bump q.1.val s).sum := by
  simp only [PivotMinor.rr, PivotMinor.bumpData, bumpF, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, val_nat, val_fr _ _ (by norm_num : 2 ≠ 0), val_fr _ _ (by norm_num : 1000000 ≠ 0),
    val_fr _ _ (by norm_num : 500000 ≠ 0), val_fr _ _ (by norm_num : 125000 ≠ 0),
    val_fr _ _ (by norm_num : 250000 ≠ 0)]
  push_cast
  ring_nf

/-- The centres and weights are nonnegative. -/
lemma bumpF_nonneg : ∀ q ∈ bumpF, 0 ≤ q.1.val ∧ 0 ≤ q.2.val := by
  intro q hq
  simp only [bumpF, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [val_fr, val_nat]

/-- `Σ_j b_j·bump_j` from below on `[s_a, s_b]`. -/
def rloL (sa sb : Fr) : List (Fr × Fr) → Fr
  | [] => nat 0
  | q :: l => q.2 * bumploF sa sb q.1 + rloL sa sb l

/-- `r` from below on `[s_a, s_b]`. -/
def rloF (sa sb : Fr) : Fr := rloL sa sb bumpF

/-- `Σ_j b_j·bump_j` from below on `[s_a, s_b]`, by induction on the list. -/
lemma rloL_le {sa sb : Fr} {s : ℝ} (h1 : sa.val ≤ s) (h2 : s ≤ sb.val) (hs : 0 ≤ s) :
    ∀ l : List (Fr × Fr), (∀ q ∈ l, 0 ≤ q.1.val ∧ 0 ≤ q.2.val) →
      (rloL sa sb l).val ≤ (l.map fun q => q.2.val * PivotMinor.bump q.1.val s).sum
  | [], _ => by simp [rloL]
  | q :: l, hl => by
    rw [rloL, val_add, val_mul, List.map_cons, List.sum_cons]
    have hq := hl q List.mem_cons_self
    refine add_le_add (mul_le_mul_of_nonneg_left (bumploF_le h1 h2 hs hq.1) hq.2) ?_
    exact rloL_le h1 h2 hs l fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')

/-- **`r ≥ r_lo` on `[s_a, s_b] ⊆ [0, ∞)`**. -/
lemma rloF_le {sa sb : Fr} {s : ℝ} (h1 : sa.val ≤ s) (h2 : s ≤ sb.val) (hs : 0 ≤ s) :
    (rloF sa sb).val ≤ PivotMinor.rr s := by
  rw [rr_eq]; exact rloL_le h1 h2 hs bumpF bumpF_nonneg

/-- `g(s_a)` from below. -/
def gloF (sa : Fr) : Fr := logloF sa - l2hi - lpihi - ebF (nat 2 * sa)

/-- **`g ≥ g_lo(s_a)` on `[s_a, ∞)`**, for `s_a ≥ 1/2`. -/
lemma gloF_le {sa : Fr} {s : ℝ} (hsa : 1 / 2 ≤ sa.val) (h : sa.val ≤ s) : (gloF sa).val ≤ gR s := by
  have h1 := logloF_le hsa
  have h2 := Real.log_le_log (by linarith) h
  have h3 := ebR_anti (by linarith : (0 : ℝ) ≤ 2 * sa.val) (by linarith : 2 * sa.val ≤ 2 * s)
  have := l2hi_ge
  have := lpihi_ge
  simp only [gloF, val_sub, val_ebF, val_mul, val_nat] at h1 ⊢
  unfold gR
  push_cast
  linarith

/-! ## The certificate -/

/-- `f i` for `a ≤ i < a + n`. -/
def all (f : ℕ → Bool) (a : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => f (a + n) && all f a n

/-- A passed `all f a n` gives `f i` for `a ≤ i < a + n`. -/
lemma all_spec {f : ℕ → Bool} {a n : ℕ} (h : all f a n = true) {i : ℕ} (h1 : a ≤ i) (h2 : i < a + n) :
    f i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [all, Bool.and_eq_true] at h
    rcases (show i < a + n ∨ i = a + n by omega) with hi | rfl
    · exact ih h.2 hi
    · exact h.1

/-- **R1**, `y ∈ [1 + i/400, 1 + (i + 1)/400]`: `23/100 + (693/1000)(u(2y_b) + T(y_b) − 1) ≤ log(10y_a) − log 2 −
log π − ē(40y_a)`. -/
def ok1 (i : ℕ) : Bool :=
  ble (fr 23 100 + fr 693 1000 * (uF (nat 2 * fr (401 + i) 400) + tF (fr (401 + i) 400) - nat 1))
    (logloF (nat 10 * fr (400 + i) 400) - l2hi - lpihi - ebF (nat 40 * fr (400 + i) 400))

/-- **R0**, `s ∈ [12 + i/40, 12 + (i + 1)/40]`: `23/100 + (693/1000)T(s_b/10) ≤ g(s_a)`. -/
def ok0 (i : ℕ) : Bool := ble (fr 23 100 + fr 693 1000 * tF (fr (481 + i) 400)) (gloF (fr (480 + i) 40))

/-- `Δ = 23/100 + (693/1000)T(s_b/10) − g(s_a) ≥ λ − g` on `[s_a, s_b]`. -/
def del2 (sa sb : Fr) : Fr := fr 23 100 + fr 693 1000 * tF (sb * fr 1 10) - gloF sa

/-- `Δ ≤ 0`, or `φ_up·Δ ≤ r_lo`. -/
def ok2' (sa sb dl : Fr) : Bool :=
  ble dl (nat 0) ||
    (blt (nat 0) (slAF (sb * sb * fr 1 25)) && ble (sb * sb) (nat 150) && ble (phiupF sa sb * dl) (rloF sa sb))

/-- **R2**, `s ∈ [1/2 + i/40, 1/2 + (i + 1)/40]`. -/
def ok2 (i : ℕ) : Bool := ok2' (fr (20 + i) 40) (fr (21 + i) 40) (del2 (fr (20 + i) 40) (fr (21 + i) 40))

/-- **R3**, `s ∈ (0, 1/2]`: `(1/3000)(C₀/4 + 1/2) ≤ r_lo(0, 1/2)`, `C₀ = 23/100 + (693/1000)T(1/20) + L2HI + LPIHI +
ē(0)`. -/
def ok3 : Bool :=
  ble (fr 1 3000 * ((fr 23 100 + fr 693 1000 * tF (fr 1 20) + l2hi + lpihi + ebF (nat 0)) * fr 1 4 + fr 1 2))
    (rloF (nat 0) (fr 1 2))

/-- The kernel computation for R1, `i < 200`. -/
theorem ok1_a : all ok1 0 200 = true := by decide +kernel

/-- The kernel computation for R1, `200 ≤ i < 400`. -/
theorem ok1_b : all ok1 200 200 = true := by decide +kernel

/-- The kernel computation for R0, `i < 160`. -/
theorem ok0_a : all ok0 0 160 = true := by decide +kernel

/-- The kernel computation for R0, `160 ≤ i < 320`. -/
theorem ok0_b : all ok0 160 160 = true := by decide +kernel

/-- The kernel computation for R2, `i < 115`. -/
theorem ok2_a : all ok2 0 115 = true := by decide +kernel

/-- The kernel computation for R2, `115 ≤ i < 230`. -/
theorem ok2_b : all ok2 115 115 = true := by decide +kernel

/-- The kernel computation for R2, `230 ≤ i < 345`. -/
theorem ok2_c : all ok2 230 115 = true := by decide +kernel

/-- The kernel computation for R2, `345 ≤ i < 460`. -/
theorem ok2_d : all ok2 345 115 = true := by decide +kernel

/-- The kernel computation for R3. -/
theorem ok3_ok : ok3 = true := by decide +kernel

/-- Every R1 cell passes. -/
lemma ok1_all {i : ℕ} (hi : i < 400) : ok1 i = true := by
  rcases lt_or_ge i 200 with h | h
  · exact all_spec ok1_a (Nat.zero_le i) (by omega)
  · exact all_spec ok1_b h (by omega)

/-- Every R0 cell passes. -/
lemma ok0_all {i : ℕ} (hi : i < 320) : ok0 i = true := by
  rcases lt_or_ge i 160 with h | h
  · exact all_spec ok0_a (Nat.zero_le i) (by omega)
  · exact all_spec ok0_b h (by omega)

/-- Every R2 cell passes. -/
lemma ok2_all {i : ℕ} (hi : i < 460) : ok2 i = true := by
  rcases lt_or_ge i 115 with h | h
  · exact all_spec ok2_a (Nat.zero_le i) (by omega)
  rcases lt_or_ge i 230 with h' | h'
  · exact all_spec ok2_b h (by omega)
  rcases lt_or_ge i 345 with h'' | h''
  · exact all_spec ok2_c h' (by omega)
  · exact all_spec ok2_d h'' (by omega)

/-! ## Symmetry and `r ≥ 0` -/

/-- `φ` is even. -/
lemma phi_neg (s : ℝ) : PivotPhi.phi (-s) = PivotPhi.phi s := by
  rw [PivotPhi.phi_eq, PivotPhi.phi_eq, neg_div, neg_sq]
  unfold PivotPhi.kk
  rw [Real.sin_neg]
  ring

/-- `λ` is even. -/
lemma lam_neg (s : ℝ) : PivotMinor.lam (-s) = PivotMinor.lam s := by
  unfold PivotMinor.lam
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [neg_div, Real.sinc_neg]

/-- Each bump is even in `s`. -/
lemma bump_neg (γ s : ℝ) : PivotMinor.bump γ (-s) = PivotMinor.bump γ s := by
  unfold PivotMinor.bump
  rw [show (-s - γ) / 2 = -((s + γ) / 2) by ring, show (-s + γ) / 2 = -((s - γ) / 2) by ring,
    Real.sinc_neg, Real.sinc_neg]
  ring

/-- `μ` is even. -/
lemma mu_neg (s : ℝ) : PivotMinor.mu (-s) = PivotMinor.mu s := by
  unfold PivotMinor.mu PivotMinor.rr
  rw [phi_neg, lam_neg]
  congr 2
  exact List.map_congr_left fun p _ => by rw [bump_neg]

/-- `r ≥ 0`. -/
lemma rr_nonneg (s : ℝ) : 0 ≤ PivotMinor.rr s := by
  rw [rr_eq]
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  exact mul_nonneg (bumpF_nonneg q hq).2 (by unfold PivotMinor.bump; positivity)

/-! ## The four ranges of `s > 0` -/

/-- Locating `s` in the progression `a + i·h`. -/
lemma exists_cell {a h s : ℝ} (hh : 0 < h) (has : a ≤ s) {n : ℕ} (hsn : s < a + n * h) :
    ∃ i : ℕ, i < n ∧ a + i * h ≤ s ∧ s ≤ a + (i + 1) * h := by
  set q := (s - a) / h with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hh.le
  refine ⟨⌊q⌋₊, ?_, ?_, ?_⟩
  · have h1 : q < n := by rw [hq, div_lt_iff₀ hh]; linarith
    exact_mod_cast (Nat.floor_le hq0).trans_lt h1
  · have := Nat.floor_le hq0
    rw [hq, le_div_iff₀ hh] at this
    linarith
  · have := Nat.lt_floor_add_one q
    rw [hq, div_lt_iff₀ hh] at this
    linarith

/-- `φλ − r ≤ φg` once `λ ≤ g`. -/
lemma key_of_lam_le {s : ℝ} (h : PivotMinor.lam s ≤ gR s) :
    PivotPhi.phi s * PivotMinor.lam s - PivotMinor.rr s ≤ PivotPhi.phi s * gR s := by
  have := mul_le_mul_of_nonneg_left h (PivotPhi.phi_nonneg s)
  have := rr_nonneg s
  linarith

/-- **R1**, `s ≥ 20`: with `s = 10·2^j·y`, `j ≥ 1`, `y ∈ [1, 2)`, the steps of `λ` follow `log s`. -/
lemma region1 {s : ℝ} (hs : 20 ≤ s) :
    PivotPhi.phi s * PivotMinor.lam s - PivotMinor.rr s ≤ PivotPhi.phi s * gR s := by
  apply key_of_lam_le
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ s / 10 by linarith) (show (1 : ℝ) < 2 by norm_num)
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := by
    rcases j with _ | j
    · norm_num at hj2; linarith
    · exact ⟨j, rfl⟩
  have hp : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = s / 10 / 2 ^ (j + 1) := ⟨_, rfl⟩
  have hsy : s / 10 = 2 ^ (j + 1) * y := by rw [hy]; field_simp
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hp]; linarith
  have hy2 : y < 2 := by rw [hy, div_lt_iff₀ hp]; rw [pow_succ] at hj2; linarith
  obtain ⟨i, hi, hia, hib⟩ := exists_cell (a := 1) (h := 1 / 400) (n := 400) (by norm_num) hy1
    (by norm_num; linarith)
  obtain ⟨ya, hya⟩ : ∃ v : ℝ, v = 1 + i * (1 / 400) := ⟨_, rfl⟩
  obtain ⟨yb, hyb⟩ : ∃ v : ℝ, v = 1 + (i + 1) * (1 / 400) := ⟨_, rfl⟩
  rw [← hya] at hia
  rw [← hyb] at hib
  have hya1 : 1 ≤ ya := by rw [hya]; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
  have e1 : (fr (401 + i) 400).val = yb := by rw [hyb, val_fr _ _ (by norm_num)]; push_cast; ring
  have e0 : (fr (400 + i) 400).val = ya := by rw [hya, val_fr _ _ (by norm_num)]; push_cast; ring
  have hok := ok1_all hi
  rw [ok1, ble_iff] at hok
  have hL := logloF_le (p := nat 10 * fr (400 + i) 400) (by rw [val_mul, val_nat, e0]; push_cast; linarith)
  rw [val_mul, val_nat, e0] at hL
  generalize logloF (nat 10 * fr (400 + i) 400) = L at hok hL
  simp only [val_add, val_sub, val_mul, val_nat, val_uF, val_tF, val_ebF, e1, e0,
    val_fr _ _ (by norm_num : 100 ≠ 0), val_fr _ _ (by norm_num : 1000 ≠ 0)] at hok
  push_cast at hok hL
  -- `λ(s) ≤ 23/100 + (693/1000)(j + u(2y_b) + T(y_b))`
  have hlam := lam_le s
  rw [hsy] at hlam
  have h1 := sR_pow_le y j 30
  have h2 := uR_mono (by linarith only [hy1] : (0 : ℝ) ≤ 2 * y) (by linarith only [hib] : 2 * y ≤ 2 * yb)
  have h3 := tR_mono (by linarith only [hy1] : (0 : ℝ) ≤ y) hib
  -- `g(s) ≥ log(10y_a) + j log 2 − log π − ē(40y_a)`
  have hs10 : s = 10 * y * 2 ^ (j + 1) := by linarith only [hsy]
  have hlogs : Real.log s = Real.log (10 * y) + (j + 1) * Real.log 2 := by
    rw [hs10, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hl10 := Real.log_le_log (by positivity : (0 : ℝ) < 10 * ya) (by linarith only [hia] : 10 * ya ≤ 10 * y)
  have heb : ebR (2 * s) ≤ ebR (40 * ya) := by
    apply ebR_anti (by positivity)
    have h2j : (2 : ℝ) ≤ 2 ^ (j + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h40 := mul_le_mul_of_nonneg_left h2j (by linarith only [hy1] : (0 : ℝ) ≤ 20 * y)
    rw [hs10]
    linarith only [h40, hia]
  have hl2 := l2lo_le
  have hl2' := l2hi_ge
  have hpi := lpihi_ge
  have hl2v : l2lo.val = 6931471803 / 10000000000 := by rw [l2lo, val_fr _ _ (by norm_num)]; norm_num
  rw [hl2v] at hl2
  have hjl : (j : ℝ) * (693 / 1000) ≤ j * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith only [hl2]) (Nat.cast_nonneg j)
  unfold gR
  linarith only [hok, hL, hlam, h1, h2, h3, hlogs, hl10, heb, hl2, hl2', hpi, hjl]

/-- **R0**, `12 ≤ s < 20`: `λ ≤ g`. -/
lemma region0 {s : ℝ} (hs : 12 ≤ s) (hs' : s < 20) :
    PivotPhi.phi s * PivotMinor.lam s - PivotMinor.rr s ≤ PivotPhi.phi s * gR s := by
  apply key_of_lam_le
  obtain ⟨i, hi, hia, hib⟩ := exists_cell (a := 12) (h := 1 / 40) (n := 320) (by norm_num) hs
    (by norm_num; linarith)
  have e1 : (fr (481 + i) 400).val = (12 + (i + 1) * (1 / 40)) / 10 := by
    rw [val_fr _ _ (by norm_num)]; push_cast; ring
  have e0 : (fr (480 + i) 40).val = 12 + i * (1 / 40) := by rw [val_fr _ _ (by norm_num)]; push_cast; ring
  have hok := ok0_all hi
  rw [ok0, ble_iff] at hok
  have hg := gloF_le (sa := fr (480 + i) 40) (s := s)
    (by rw [e0]; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith) (by rw [e0]; exact hia)
  generalize gloF (fr (480 + i) 40) = G at hok hg
  simp only [val_add, val_mul, val_tF, e1, val_fr _ _ (by norm_num : 100 ≠ 0),
    val_fr _ _ (by norm_num : 1000 ≠ 0)] at hok
  push_cast at hok
  have hlam := lam_le s
  have h1 := sR_le_tR 30 (s / 10)
  have h2 := tR_mono (by linarith only [hs] : (0 : ℝ) ≤ s / 10)
    (by linarith only [hib] : s / 10 ≤ (12 + ((i : ℝ) + 1) * (1 / 40)) / 10)
  linarith only [hok, hg, hlam, h1, h2]

/-- **R2**, `1/2 ≤ s < 12`: `φ(λ − g) ≤ φ_up·Δ ≤ r_lo ≤ r` where `Δ > 0`. -/
lemma region2 {s : ℝ} (hs : 1 / 2 ≤ s) (hs' : s < 12) :
    PivotPhi.phi s * PivotMinor.lam s - PivotMinor.rr s ≤ PivotPhi.phi s * gR s := by
  obtain ⟨i, hi, hia, hib⟩ := exists_cell (a := 1 / 2) (h := 1 / 40) (n := 460) (by norm_num) hs
    (by norm_num; linarith)
  have hok := ok2_all hi
  rw [ok2] at hok
  have ea : (fr (20 + i) 40).val = 1 / 2 + i * (1 / 40) := by rw [val_fr _ _ (by norm_num)]; push_cast; ring
  have eb : (fr (21 + i) 40).val = 1 / 2 + (i + 1) * (1 / 40) := by
    rw [val_fr _ _ (by norm_num)]; push_cast; ring
  generalize fr (20 + i) 40 = sa at hok ea
  generalize fr (21 + i) 40 = sb at hok eb
  have h1 : sa.val ≤ s := by rw [ea]; exact hia
  have h2 : s ≤ sb.val := by rw [eb]; exact hib
  have hsa0 : 1 / 2 ≤ sa.val := by rw [ea]; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
  -- `λ − g ≤ Δ`
  have hdel : PivotMinor.lam s - gR s ≤ (del2 sa sb).val := by
    have hg := gloF_le hsa0 h1
    have hlam := lam_le s
    have ht1 := sR_le_tR 30 (s / 10)
    have ht2 := tR_mono (by linarith only [hs] : (0 : ℝ) ≤ s / 10)
      (by linarith only [h2] : s / 10 ≤ sb.val * (1 / 10))
    unfold del2
    generalize gloF sa = G at hg
    simp only [val_sub, val_add, val_mul, val_tF, val_fr _ _ (by norm_num : 100 ≠ 0),
      val_fr _ _ (by norm_num : 1000 ≠ 0), val_fr _ _ (by norm_num : 10 ≠ 0)]
    push_cast
    linarith only [hg, hlam, ht1, ht2]
  have hphi := PivotPhi.phi_nonneg s
  have hrr := rr_nonneg s
  rcases le_or_gt (del2 sa sb).val 0 with hd | hd
  · have := mul_le_mul_of_nonneg_left (hdel.trans hd) hphi
    linarith only [this, hrr]
  have hnot : ble (del2 sa sb) (nat 0) = false := by
    rw [← Bool.not_eq_true, ble_iff, val_nat]; push_cast; linarith only [hd]
  rw [ok2', hnot, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at hok
  obtain ⟨⟨hw, h150⟩, hmain⟩ := hok
  rw [blt_iff, val_nat, val_slAF] at hw
  simp only [val_mul, val_fr _ _ (by norm_num : 25 ≠ 0)] at hw
  push_cast at hw
  rw [ble_iff, val_mul, val_nat] at h150
  push_cast at h150
  rw [ble_iff, val_mul] at hmain
  have e : sb.val * sb.val * (1 / 25) = sb.val * sb.val / 25 := by ring
  rw [e] at hw
  have hup := phi_le_phiupF (by linarith only [hsa0]) h1 h2 hw (by linarith only [h150])
  have hrlo := rloF_le h1 h2 (by linarith only [hs])
  have hA : PivotPhi.phi s * (PivotMinor.lam s - gR s) ≤ PivotPhi.phi s * (del2 sa sb).val :=
    mul_le_mul_of_nonneg_left hdel hphi
  have hB : PivotPhi.phi s * (del2 sa sb).val ≤ (phiupF sa sb).val * (del2 sa sb).val :=
    mul_le_mul_of_nonneg_right hup hd.le
  linarith only [hA, hB, hmain, hrlo]

/-- **R3**, `0 < s ≤ 1/2`: `φ(s) ≤ s²/3000` and `s²log(1/s) ≤ s`. -/
lemma region3 {s : ℝ} (hs : 0 < s) (hs' : s ≤ 1 / 2) :
    PivotPhi.phi s * PivotMinor.lam s - PivotMinor.rr s ≤ PivotPhi.phi s * gR s := by
  have hok := ok3_ok
  rw [ok3, ble_iff] at hok
  have hrlo := rloF_le (sa := nat 0) (sb := fr 1 2) (s := s) (by rw [val_nat]; push_cast; linarith)
    (by rw [val_fr _ _ (by norm_num)]; push_cast; linarith) hs.le
  have hC0 : (fr 23 100 + fr 693 1000 * tF (fr 1 20) + l2hi + lpihi + ebF (nat 0)).val =
      23 / 100 + 693 / 1000 * tR (1 / 20) + l2hi.val + lpihi.val + ebR 0 := by
    simp only [val_add, val_mul, val_tF, val_ebF, val_nat, val_fr _ _ (by norm_num : 100 ≠ 0),
      val_fr _ _ (by norm_num : 1000 ≠ 0), val_fr _ _ (by norm_num : 20 ≠ 0)]
    push_cast; ring
  generalize fr 23 100 + fr 693 1000 * tF (fr 1 20) + l2hi + lpihi + ebF (nat 0) = X at hok hC0
  generalize rloF (nat 0) (fr 1 2) = R at hok hrlo
  simp only [val_mul, val_add, val_fr _ _ (by norm_num : 3000 ≠ 0), val_fr _ _ (by norm_num : 4 ≠ 0),
    val_fr _ _ (by norm_num : 2 ≠ 0)] at hok
  push_cast at hok
  -- `λ − g ≤ C₀ − log s`
  have hlg : PivotMinor.lam s - gR s ≤ X.val - Real.log s := by
    have hlam := lam_le s
    have ht1 := sR_le_tR 30 (s / 10)
    have ht2 := tR_mono (by positivity : (0 : ℝ) ≤ s / 10) (by linarith only [hs'] : s / 10 ≤ 1 / 20)
    have heb := ebR_anti (le_refl 0) (by positivity : (0 : ℝ) ≤ 2 * s)
    have h2 := l2hi_ge
    have h3 := lpihi_ge
    unfold gR
    rw [hC0]
    linarith only [hlam, ht1, ht2, heb, h2, h3]
  have hlogs : Real.log s < 0 := Real.log_neg hs (by linarith only [hs'])
  have hX0 : 0 ≤ X.val := by
    rw [hC0]
    have := tR_nonneg (1 / 20)
    have := l2hi_ge; have := lpihi_ge
    have : 0 ≤ ebR 0 := by unfold ebR ebBR; positivity
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have := Real.log_pos (by linarith [Real.pi_gt_three] : (1 : ℝ) < π)
    linarith
  have hs4 : s ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ hs.le hs' 2
    norm_num at this ⊢
    exact this
  have hphi := PivotPhi.phi_le_sq (s := s) (by linarith only [hs4])
  have hphi0 := PivotPhi.phi_nonneg s
  -- `s²(C₀ − log s) ≤ C₀/4 + 1/2`
  have hsl : -(s ^ 2 * Real.log s) ≤ s := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
    rw [Real.log_inv] at this
    have h1 : s ^ 2 * (-Real.log s) ≤ s ^ 2 * (s⁻¹ - 1) := mul_le_mul_of_nonneg_left this (by positivity)
    have h2 : s ^ 2 * (s⁻¹ - 1) = s - s ^ 2 := by field_simp
    have h3 : 0 ≤ s ^ 2 := by positivity
    linarith
  have hA : PivotPhi.phi s * (PivotMinor.lam s - gR s) ≤ PivotPhi.phi s * (X.val - Real.log s) :=
    mul_le_mul_of_nonneg_left hlg hphi0
  have hB : PivotPhi.phi s * (X.val - Real.log s) ≤ s ^ 2 / 3000 * (X.val - Real.log s) :=
    mul_le_mul_of_nonneg_right hphi (by linarith)
  have hC : s ^ 2 * X.val ≤ 1 / 4 * X.val := mul_le_mul_of_nonneg_right hs4 hX0
  have hrr := rr_nonneg s
  linarith

/-! ## The theorem -/

/-- **The minorant lies below the archimedean weight at every scale**: the band-limited `μ = φλ − r` lies below
`φ(s)(L(Ns) − log N)` at every scale `N ≥ 2`, `L(t) = Re ψ(¼ + it/2) − log π`. -/
theorem mu_le {N : ℕ} (hN : 2 ≤ N) (s : ℝ) :
    PivotMinor.mu s ≤ PivotPhi.phi s * (WeilForm.psiRe ((N : ℝ) * s) - Real.log π - Real.log N) := by
  have pos : ∀ s : ℝ, 0 < s →
      PivotMinor.mu s ≤ PivotPhi.phi s * (WeilForm.psiRe ((N : ℝ) * s) - Real.log π - Real.log N) := by
    intro s hs
    have key : PivotPhi.phi s * PivotMinor.lam s - PivotMinor.rr s ≤ PivotPhi.phi s * gR s := by
      rcases le_or_gt s (1 / 2) with h | h
      · exact region3 hs h
      rcases lt_or_ge s 12 with h' | h'
      · exact region2 h.le h'
      rcases lt_or_ge s 20 with h'' | h''
      · exact region0 h' h''
      · exact region1 h''
    have hg := mul_le_mul_of_nonneg_left (gR_le hN hs) (PivotPhi.phi_nonneg s)
    unfold PivotMinor.mu
    linarith
  rcases lt_trichotomy s 0 with h | rfl | h
  · have := pos (-s) (by linarith)
    rwa [mu_neg, phi_neg, mul_neg, psiRe_neg] at this
  · have h0 : PivotPhi.phi 0 = 0 := by rw [PivotPhi.phi_eq]; simp
    unfold PivotMinor.mu
    rw [h0, zero_mul, zero_mul, zero_sub, neg_nonpos]
    exact rr_nonneg 0
  · exact pos s h

end PivotCert
