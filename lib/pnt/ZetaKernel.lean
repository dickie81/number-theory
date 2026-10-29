/-
# The Halász–Montgomery inequality at well-spaced heights, and the kernel of `ζ` past its pole

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For `0 < ε ≤ 7/12` there is `C` with
`|Σ_{n≥1} n^{−z}e^{−n/Λ}| ≤ KE·Λe^{−|Im z|} + CΛ^{1/12}(|Im z| + 2)^{5/12+ε}` for every `Λ ≥ 1` and every
`0 ≤ Re z ≤ 1/24` (`norm_kz_le`). Take points `β_r + iγ_r` with `σ_b ≤ β_r < σ_b + 1/48`, 1-separated heights within
`T₀` of each other, at which a block `F` on `(P, 2P]` with `|c_j| ≤ d(j)` is at least `V`. They number at most
`2e·G_m·Λ(1 + KE(2 log Λ + 1))/V^{2m}`, `Λ = (2P)^m`, if the kernel is at most `KE·Λe^{−|Im z|} + B` for
`|Im z| ≤ T₀` and `2e·G_m(KE + B) ≤ V^{2m}` (`power_count_pts`). These are the inputs of the density estimate with
Huxley's exponent `12/5` for `ζ` (`ZetaHuxley.lean`), as `LinnikPower.hm_duality` and `LinnikOffDiag.norm_offK_le`
are over the characters.

* `hm_duality_pts`: `LinnikPower.hm_duality` with the points in place of the characters. The kernel is
  `K_Λ(z) = Σ_{n≥1} n^{−z}e^{−n/Λ}` (the trivial character mod `1`) at every pair, and its bound is a function of the
  pair.
* `kz_eq_line`, `kz_eq`: `K_Λ(z) = (1/2π)∫ ζ(z + 3/2 + it)Γ(3/2 + it)Λ^{3/2+it} dt` (`Linnik.perron_exp`). Moved to
  `Re(z + w) = 1/12` across the pole of `ζ`, `K_Λ(z) = Γ(1 − z)Λ^{1−z} + (1/2π)∫ ζ(1/12 + it)Γ(1/12 + it − z)
  Λ^{1/12+it−z} dt` (`LinnikGamma.verticalIntegral_sub_eq`, with Mathlib's `isBigO_riemannZeta_sub_one_div`).
* `norm_kz_le`: `|Γ(1 − z)| ≤ KE e^{−|Im z|}` (`InghamDensity.norm_Gamma_exp_le`); on the line
  `|ζ(1/12 + it)| ≤ C(|t| + 2)^{5/12+ε}` (`Subconvexity.zeta_strip_eleven_twelfths`) and
  `|Γ(c′ + iv)|(1 + |v|)⁵ ≤ 24 KG` (`LinnikOffDiag.norm_Gamma_small`).
* `sum_pole_le`, `power_count_pts`: the residue terms `Λe^{−|γ_r − γ_{r′}|}` sum over `r′ ≠ r` to at most
  `Λ(2 log Λ + 1) + |R|`, since at most `2 log Λ + 1` of the heights lie within `log Λ` of `γ_r`; then
  `hm_duality_pts` for `F^m`, with the mass of `LinnikHuxley.mass_pow_le`.
-/

import ZetaFourth
import LinnikHuxley

open Complex Real Finset MeasureTheory Filter Topology Asymptotics

noncomputable section

namespace ZetaKernel

open LinnikPower LinnikHuxley InghamDensity ZetaFourth DirichletCharacter ShortWeil DirMean

/-! ### The Halász–Montgomery inequality at points -/

/-- **The Halász–Montgomery duality inequality at points**, one point `β_r + iγ_r` per `r ∈ R`, `β_r ≥ σ`:
`(Σ_r |D_r|)² ≤ e·G·Σ_{r,r′} B_{rr′}`, with `D_r = Σ_{n∈S} a_n n^{−β_r−iγ_r}`, `G = Σ_{n∈S}|a_n|²n^{−2σ}` for
`S ⊆ [1, Λ]`, `B_{rr} = Λ`, and `|K_Λ(z_{rr′})| ≤ B_{rr′}` for `r ≠ r′`, where `K_Λ(z) = Σ_{n≥1} n^{−z}e^{−n/Λ}` and
`z_{rr′} = (β_r + β_{r′} − 2σ) + i(γ_r − γ_{r′})`. -/
theorem hm_duality_pts {ι : Type*} [DecidableEq ι] {R : Finset ι} {S : Finset ℕ} (hS0 : 0 ∉ S) {Λ : ℝ} (hΛ : 0 < Λ)
    (hSΛ : ∀ n ∈ S, (n : ℝ) ≤ Λ) (a : ℕ → ℂ) {σ : ℝ} (β γ : ι → ℝ) (hβ : ∀ r ∈ R, σ ≤ β r) (B : ι → ι → ℝ)
    (hB : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' →
      ‖∑' n : ℕ, kTerm χ₁ Λ (((β r + β r' - 2 * σ : ℝ) : ℂ) + ((γ r - γ r' : ℝ) : ℂ) * I) n‖ ≤ B r r') :
    (∑ r ∈ R, ‖pv S a χ₁ ((β r : ℂ) + γ r * I)‖) ^ 2 ≤
      Real.exp 1 * (∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) *
        ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else B r r') := by
  classical
  set u : ι → ℂ := fun r => ((β r - σ : ℝ) : ℂ) + (γ r : ℂ) * I with hu
  set D : ι → ℂ := fun r => pv S a χ₁ ((β r : ℂ) + γ r * I) with hD
  set η : ι → ℂ := fun r => phase (D r) with hη
  set Φ : ℕ → ℂ := fun n => ∑ r ∈ R, η r * (n : ℂ) ^ (-u r) with hΦ
  set x : ℕ → ℂ := fun n => a n * (n : ℂ) ^ (-(σ : ℂ)) with hx
  -- (1) the sum of the moduli as a bilinear form
  have hηD : ∀ r, η r * D r = (‖D r‖ : ℂ) := fun r => phase_mul (D r)
  have h1 : ((∑ r ∈ R, ‖D r‖ : ℝ) : ℂ) = ∑ n ∈ S, x n * Φ n := by
    push_cast
    rw [← sum_congr rfl fun r _ => hηD r]
    simp only [hD, pv, hΦ, hx, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n hn => sum_congr rfl fun r _ => ?_
    have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
    rw [cpow_split hn0 σ (β r) (γ r), χ₁_apply]
    simp only [hu]
    ring
  -- (2) the moduli of the terms
  have hnx : ∀ n ∈ S, ‖x n‖ = ‖a n‖ * (n : ℝ) ^ (-σ) := by
    intro n hn
    have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
    rw [hx, norm_mul, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0)]
    simp
  -- (3) Cauchy–Schwarz with the weight `e^{−n/Λ}`
  set w : ℕ → ℝ := fun n => Real.exp (-((n : ℝ) / Λ)) with hw
  have hwpos : ∀ n, 0 < w n := fun n => Real.exp_pos _
  have hcs : (∑ n ∈ S, ‖x n‖ * ‖Φ n‖) ^ 2 ≤ (∑ n ∈ S, ‖x n‖ ^ 2 / w n) * (∑ n ∈ S, w n * ‖Φ n‖ ^ 2) := by
    have h := sum_mul_sq_le_sq_mul_sq S (fun n => ‖x n‖ * (Real.sqrt (w n))⁻¹) (fun n => Real.sqrt (w n) * ‖Φ n‖)
    have e1 : ∀ n, ‖x n‖ * (Real.sqrt (w n))⁻¹ * (Real.sqrt (w n) * ‖Φ n‖) = ‖x n‖ * ‖Φ n‖ := fun n => by
      have : Real.sqrt (w n) ≠ 0 := (Real.sqrt_pos.2 (hwpos n)).ne'
      field_simp
    have e2 : ∀ n, (‖x n‖ * (Real.sqrt (w n))⁻¹) ^ 2 = ‖x n‖ ^ 2 / w n := fun n => by
      rw [mul_pow, inv_pow, Real.sq_sqrt (hwpos n).le, div_eq_mul_inv]
    have e3 : ∀ n, (Real.sqrt (w n) * ‖Φ n‖) ^ 2 = w n * ‖Φ n‖ ^ 2 := fun n => by
      rw [mul_pow, Real.sq_sqrt (hwpos n).le]
    simp only [e1, e2, e3] at h
    exact h
  have hG : ∑ n ∈ S, ‖x n‖ ^ 2 / w n ≤ Real.exp 1 * ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [hnx n hn, hw, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    have : Real.exp ((n : ℝ) / Λ) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 ((div_le_one hΛ).2 (hSΛ n hn))
    calc (‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2 * Real.exp ((n : ℝ) / Λ)
        ≤ (‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2 * Real.exp 1 := by gcongr
      _ = Real.exp 1 * (‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) := by ring
  -- (4) the weighted square sum as a double sum of kernels
  set z : ι → ι → ℂ := fun r r' => ((β r + β r' - 2 * σ : ℝ) : ℂ) + ((γ r - γ r' : ℝ) : ℂ) * I with hz
  have hzre : ∀ r ∈ R, ∀ r' ∈ R, 0 ≤ (z r r').re := by
    intro r hr r' hr'
    simp only [hz, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
    linarith [hβ r hr, hβ r' hr']
  have hzu : ∀ r r', z r r' = u r + (starRingEnd ℂ) (u r') := by
    intro r r'
    simp only [hz, hu, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  set F : ℕ → ℂ := fun n => ∑ r ∈ R, ∑ r' ∈ R, η r * (starRingEnd ℂ) (η r') * kTerm χ₁ Λ (z r r') n with hF
  have hFeq : ∀ n, n ≠ 0 → F n = (w n : ℂ) * Φ n * (starRingEnd ℂ) (Φ n) := by
    intro n hn
    have hterm : ∀ r r', kTerm χ₁ Λ (z r r') n
        = (w n : ℂ) * (n : ℂ) ^ (-u r) * (starRingEnd ℂ) ((n : ℂ) ^ (-u r')) := by
      intro r r'
      simp only [kTerm, hn, ite_false, hw, χ₁_apply]
      rw [hzu, ← cpow_mul_conj_cpow hn]
      ring
    have hΦexp : (w n : ℂ) * Φ n * (starRingEnd ℂ) (Φ n) = ∑ r ∈ R, ∑ r' ∈ R,
        (w n : ℂ) * (η r * (n : ℂ) ^ (-u r)) * (starRingEnd ℂ) (η r' * (n : ℂ) ^ (-u r')) := by
      simp only [hΦ, map_sum]
      rw [mul_assoc, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun r' _ => ?_
      ring
    rw [hΦexp]
    simp only [hF]
    refine sum_congr rfl fun r _ => sum_congr rfl fun r' _ => ?_
    rw [hterm, map_mul]
    ring
  have hFre : ∀ n, (F n).re = (if n = 0 then 0 else w n * ‖Φ n‖ ^ 2) := by
    intro n
    split_ifs with hn
    · simp [hF, kTerm, hn]
    · rw [hFeq n hn, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- (5) summability and the bound on the double sum
  have hsumk : ∀ r ∈ R, ∀ r' ∈ R, Summable (kTerm χ₁ Λ (z r r')) :=
    fun r hr r' hr' => summable_kTerm _ hΛ (hzre r hr r' hr')
  have hηle : ∀ r, ‖η r‖ ≤ 1 := fun r => norm_phase_le _
  have hFsum : Summable F := by
    simp only [hF]
    exact summable_sum fun r hr => summable_sum fun r' hr' => (hsumk r hr r' hr').mul_left _
  have hFbd : ∀ n, ‖F n‖ ≤ (R.card : ℝ) ^ 2 * LinnikPower.wt Λ n := by
    intro n
    simp only [hF]
    calc ‖∑ r ∈ R, ∑ r' ∈ R, η r * (starRingEnd ℂ) (η r') * kTerm χ₁ Λ (z r r') n‖
        ≤ ∑ r ∈ R, ∑ r' ∈ R, ‖η r * (starRingEnd ℂ) (η r') * kTerm χ₁ Λ (z r r') n‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun r _ => norm_sum_le _ _)
      _ ≤ ∑ _r ∈ R, ∑ _r' ∈ R, LinnikPower.wt Λ n := by
          refine sum_le_sum fun r hr => sum_le_sum fun r' hr' => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          have h1 := hηle r
          have h2 := hηle r'
          have h3 := norm_kTerm_le χ₁ Λ (hzre r hr r' hr') n
          have h0 := norm_nonneg (kTerm χ₁ Λ (z r r') n)
          calc ‖η r‖ * ‖η r'‖ * ‖kTerm χ₁ Λ (z r r') n‖ ≤ 1 * 1 * LinnikPower.wt Λ n := by gcongr
            _ = LinnikPower.wt Λ n := by ring
      _ = (R.card : ℝ) ^ 2 * LinnikPower.wt Λ n := by
          rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
  have hwt := wt_summable_le hΛ
  have hFresum : Summable fun n => (F n).re :=
    Summable.of_norm_bounded (hwt.1.mul_left ((R.card : ℝ) ^ 2))
      (fun n => (Real.norm_eq_abs _).trans_le ((Complex.abs_re_le_norm (F n)).trans (hFbd n)))
  -- (6) the finite weighted sum against the full series
  have hFre0 : ∀ n, 0 ≤ (F n).re := fun n => by
    rw [hFre n]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hwpos n).le (by positivity)
  have h6 : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ ∑' n, (F n).re := by
    have e : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 = ∑ n ∈ S, (F n).re := by
      refine sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
      rw [hFre n, ite_eq_right_iff.2 fun h => absurd h hn0]
    rw [e]
    exact hFresum.sum_le_tsum S (fun n _ => hFre0 n)
  -- (7)–(8) the series as a double sum of kernels
  have h7 : ∑' n, (F n).re ≤ ‖∑' n, F n‖ := by
    rw [← Complex.re_tsum hFsum]; exact Complex.re_le_norm _
  have h8 : ∑' n, F n = ∑ r ∈ R, ∑ r' ∈ R, η r * (starRingEnd ℂ) (η r') *
      ∑' n, kTerm χ₁ Λ (z r r') n := by
    simp only [hF]
    rw [Summable.tsum_finsetSum fun r hr => summable_sum fun r' hr' => (hsumk r hr r' hr').mul_left _]
    refine sum_congr rfl fun r hr => ?_
    rw [Summable.tsum_finsetSum fun r' hr' => (hsumk r hr r' hr').mul_left _]
    exact sum_congr rfl fun r' _ => tsum_mul_left
  -- (9) the diagonal and the off-diagonal
  have hdiag : ∀ r ∈ R, ‖∑' n, kTerm χ₁ Λ (z r r) n‖ ≤ Λ := by
    intro r hr
    have hn := fun n => norm_kTerm_le χ₁ Λ (hzre r hr r hr) n
    have hns : Summable fun n => ‖kTerm χ₁ Λ (z r r) n‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hn hwt.1
    calc ‖∑' n, kTerm χ₁ Λ (z r r) n‖ ≤ ∑' n, ‖kTerm χ₁ Λ (z r r) n‖ := norm_tsum_le_tsum_norm hns
      _ ≤ ∑' n, LinnikPower.wt Λ n := hns.tsum_le_tsum hn hwt.1
      _ ≤ Λ := hwt.2
  have h9 : ‖∑ r ∈ R, ∑ r' ∈ R, η r * (starRingEnd ℂ) (η r') * ∑' n, kTerm χ₁ Λ (z r r') n‖
      ≤ ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else B r r') := by
    have hpt : ∀ r ∈ R, ∀ r' ∈ R,
        ‖η r * (starRingEnd ℂ) (η r') * ∑' n, kTerm χ₁ Λ (z r r') n‖ ≤ (if r = r' then Λ else B r r') := by
      intro r hr r' hr'
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hK : ‖∑' n, kTerm χ₁ Λ (z r r') n‖ ≤ (if r = r' then Λ else B r r') := by
        split_ifs with h
        · subst h; exact hdiag r hr
        · exact hB r hr r' hr' h
      have h11 : ‖η r‖ * ‖η r'‖ ≤ 1 := by nlinarith [hηle r, hηle r', norm_nonneg (η r), norm_nonneg (η r')]
      exact (mul_le_of_le_one_left (norm_nonneg _) h11).trans hK
    calc ‖∑ r ∈ R, ∑ r' ∈ R, η r * (starRingEnd ℂ) (η r') * ∑' n, kTerm χ₁ Λ (z r r') n‖
        ≤ ∑ r ∈ R, ∑ r' ∈ R, ‖η r * (starRingEnd ℂ) (η r') * ∑' n, kTerm χ₁ Λ (z r r') n‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun r _ => norm_sum_le _ _)
      _ ≤ ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else B r r') :=
          sum_le_sum fun r hr => sum_le_sum fun r' hr' => hpt r hr r' hr'
  -- (10) assemble
  have hDnn : 0 ≤ ∑ r ∈ R, ‖D r‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hmod : ∑ r ∈ R, ‖D r‖ ≤ ∑ n ∈ S, ‖x n‖ * ‖Φ n‖ := by
    have := congrArg norm h1
    rw [Complex.norm_real, Real.norm_of_nonneg hDnn] at this
    rw [this]
    exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => norm_mul _ _))
  have hW : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else B r r') := by
    calc ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ ∑' n, (F n).re := h6
      _ ≤ ‖∑' n, F n‖ := h7
      _ = _ := by rw [h8]
      _ ≤ _ := h9
  have hWnn : 0 ≤ ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 := sum_nonneg fun n _ => mul_nonneg (hwpos n).le (by positivity)
  calc (∑ r ∈ R, ‖pv S a χ₁ ((β r : ℂ) + γ r * I)‖) ^ 2 = (∑ r ∈ R, ‖D r‖) ^ 2 := rfl
    _ ≤ (∑ n ∈ S, ‖x n‖ * ‖Φ n‖) ^ 2 := pow_le_pow_left₀ hDnn hmod 2
    _ ≤ (∑ n ∈ S, ‖x n‖ ^ 2 / w n) * (∑ n ∈ S, w n * ‖Φ n‖ ^ 2) := hcs
    _ ≤ (Real.exp 1 * ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) *
          ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else B r r') :=
        mul_le_mul hG hW hWnn (by positivity)

/-! ### The kernel past the pole of `ζ` -/

/-- `ζ(s)Γ(s − z)Λ^{s−z}`: the integrand of `K_Λ(z)` in the variable `s = z + w`. -/
def zG (Λ : ℝ) (z s : ℂ) : ℂ := riemannZeta s * Complex.Gamma (s - z) * (Λ : ℂ) ^ (s - z)

/-- For `M ≥ 0`, a bound `M(1 + |y + τ|)^{−2}` for `|y| ≥ 2`, with continuity on the rectangle `[a, b] × [−2, 2]`,
gives one for every `y`. -/
lemma bound_of_far {G : ℂ → ℂ} {a b M τ : ℝ} (hM : 0 ≤ M)
    (hc : ContinuousOn (fun p : ℝ × ℝ => G (p.1 + p.2 * I)) (Set.Icc a b ×ˢ Set.Icc (-2) 2))
    (hfar : ∀ x ∈ Set.Icc a b, ∀ y : ℝ, 2 ≤ |y| → ‖G (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x ∈ Set.Icc a b, ∀ y : ℝ, ‖G (x + y * I)‖ ≤ M' * ((1 + |y + τ|) ^ 2)⁻¹ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨M + |C| * (3 + |τ|) ^ 2, by positivity, fun x hx y => ?_⟩
  have hpos : 0 < (1 + |y + τ|) ^ 2 := by positivity
  rcases le_or_gt 2 |y| with hy | hy
  · refine (hfar x hx y hy).trans ?_
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have hmem : (x, y) ∈ Set.Icc a b ×ˢ Set.Icc (-2 : ℝ) 2 := ⟨hx, abs_le.1 hy.le⟩
    have h1 := hC (x, y) hmem
    have hyt : 1 + |y + τ| ≤ 3 + |τ| := by
      have := abs_add_le y τ
      linarith
    have h2 : (1 + |y + τ|) ^ 2 ≤ (3 + |τ|) ^ 2 := pow_le_pow_left₀ (by positivity) hyt 2
    calc ‖G (x + y * I)‖ ≤ |C| := h1.trans (le_abs_self C)
      _ = |C| * (3 + |τ|) ^ 2 * ((3 + |τ|) ^ 2)⁻¹ := by field_simp
      _ ≤ |C| * (3 + |τ|) ^ 2 * ((1 + |y + τ|) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hpos h2) (by positivity)
      _ ≤ (M + |C| * (3 + |τ|) ^ 2) * ((1 + |y + τ|) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) (by positivity)

/-- Continuity on a rectangle from differentiability at its points. -/
lemma continuousOn_rect {G : ℂ → ℂ} {a b : ℝ} (h : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc (-2 : ℝ) 2,
    DifferentiableAt ℂ G (x + y * I)) :
    ContinuousOn (fun p : ℝ × ℝ => G (p.1 + p.2 * I)) (Set.Icc a b ×ˢ Set.Icc (-2) 2) := by
  intro p hp
  have hinner : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) p := by fun_prop
  exact (ContinuousAt.comp (g := G) (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
    (h p.1 hp.1 p.2 hp.2).continuousAt hinner).continuousWithinAt

lemma continuous_line {G : ℂ → ℂ} {x : ℝ} (h : ∀ y : ℝ, DifferentiableAt ℂ G (x + y * I)) :
    Continuous fun y : ℝ => G (x + y * I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hinner : ContinuousAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) y := by fun_prop
  exact ContinuousAt.comp (g := G) (h y).continuousAt hinner

/-- **Integrability on a line** from `|G(x + iy)| ≤ M(1 + |y + τ|)^{−2}`. -/
lemma integrable_of_bound {G : ℂ → ℂ} {x M τ : ℝ} (hcont : Continuous fun y : ℝ => G (x + y * I))
    (hb : ∀ y : ℝ, ‖G (x + y * I)‖ ≤ M * ((1 + |y + τ|) ^ 2)⁻¹) : Integrable fun y : ℝ => G (x + y * I) := by
  have hd : ∀ y : ℝ, M * ((1 + |y + τ|) ^ 2)⁻¹ ≤ |M| * (1 + (y + τ) ^ 2)⁻¹ := by
    intro y
    have h1 : 1 + (y + τ) ^ 2 ≤ (1 + |y + τ|) ^ 2 := by nlinarith [abs_nonneg (y + τ), sq_abs (y + τ)]
    have h2 : ((1 + |y + τ|) ^ 2)⁻¹ ≤ (1 + (y + τ) ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
    calc M * ((1 + |y + τ|) ^ 2)⁻¹ ≤ |M| * ((1 + |y + τ|) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
      _ ≤ |M| * (1 + (y + τ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (abs_nonneg M)
  exact ((integrable_inv_one_add_sq.comp_add_right τ).const_mul |M|).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => (hb y).trans (hd y))

lemma differentiableAt_zG {Λ : ℝ} (hΛ : 0 < Λ) (z : ℂ) {s : ℂ} (hs1 : s ≠ 1) (hsz : 0 < (s - z).re) :
    DifferentiableAt ℂ (zG Λ z) s := by
  have h1 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have h2 : DifferentiableAt ℂ (fun s => Complex.Gamma (s - z)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp s (differentiableAt_id.sub_const z)
    have := congrArg Complex.re h
    simp only [neg_re, natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h3 : DifferentiableAt ℂ (fun s : ℂ => (Λ : ℂ) ^ (s - z)) s :=
    (differentiableAt_id.sub_const z).const_cpow (Or.inl (ofReal_ne_zero.2 hΛ.ne'))
  exact (h1.mul h2).mul h3

/-- **Mellin inversion on `Re w = 3/2`** (`Linnik.perron_exp`): for `Re z ≥ 0`,
`K_Λ(z) = (1/2π)∫ ζ(Re z + 3/2 + it)Γ(Re z + 3/2 + it − z)Λ^{Re z + 3/2 + it − z} dt`. -/
lemma kz_eq_line {Λ : ℝ} (hΛ : 0 < Λ) {z : ℂ} (hz0 : 0 ≤ z.re) :
    ∑' n, kTerm χ₁ Λ z n = (1 / (2 * π) : ℂ) * ∫ t : ℝ, zG Λ z ((z.re + 3 / 2 : ℝ) + t * I) := by
  set a : ℕ → ℂ := fun n => if n = 0 then 0 else χ₁ n * (n : ℂ) ^ (-z) with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have hsum : LSeriesSummable a ((3 / 2 : ℝ) : ℂ) := by
    have h := ZMod.LSeriesSummable_of_one_lt_re (fun n => χ₁ n) (s := z + ((3 / 2 : ℝ) : ℂ))
      (by simp; linarith)
    unfold LSeriesSummable at h ⊢
    have e : LSeries.term a ((3 / 2 : ℝ) : ℂ) = LSeries.term (fun n => χ₁ n) (z + ((3 / 2 : ℝ) : ℂ)) :=
      funext fun n => LinnikOffDiag.term_twist χ₁ z _ n
    rw [e]; exact h
  have hp := Linnik.perron_exp ha0 (c := 3 / 2) (by norm_num) (by norm_num) hΛ hsum
  have hleft : ∑' n, kTerm χ₁ Λ z n = ∑' n, a n * (Real.exp (-((n : ℝ) / Λ)) : ℂ) := by
    congr 1; funext n; rw [LinnikOffDiag.kTerm_eq]
  rw [hleft, hp]
  congr 1
  have hpt : ∀ t : ℝ, LSeries a ((3 / 2 : ℝ) + t * I) * Complex.Gamma ((3 / 2 : ℝ) + t * I) *
      (Λ : ℂ) ^ ((3 / 2 : ℝ) + t * I) = zG Λ z ((z.re + 3 / 2 : ℝ) + (t + z.im : ℝ) * I) := by
    intro t
    have hs : ((z.re + 3 / 2 : ℝ) : ℂ) + ((t + z.im : ℝ) : ℂ) * I = z + ((3 / 2 : ℝ) + t * I) := by
      apply Complex.ext <;> simp; ring
    have hL : LSeries a ((3 / 2 : ℝ) + t * I) = riemannZeta (z + ((3 / 2 : ℝ) + t * I)) := by
      rw [← LFunction_χ₁, LFunction_eq_LSeries χ₁ (by simp; linarith)]
      unfold LSeries; congr 1; funext n; exact LinnikOffDiag.term_twist χ₁ z _ n
    rw [hL, hs, zG, add_sub_cancel_left]
  simp_rw [hpt]
  exact integral_add_right_eq_self (fun t : ℝ => zG Λ z ((z.re + 3 / 2 : ℝ) + (t : ℂ) * I)) z.im

/-- **The pole**: `ζ(u + 1)Γ(u + 1 − z)Λ^{u+1−z} − Γ(1 − z)Λ^{1−z}/u` stays bounded near `u = 0` for `Re z < 1`. -/
lemma zG_isBigO {Λ : ℝ} (hΛ : 0 < Λ) {z : ℂ} (hz : z.re < 1) :
    ((fun u => zG Λ z (u + 1)) - fun u => (Complex.Gamma (1 - z) * (Λ : ℂ) ^ (1 - z)) / (u - 0))
      =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
  set g : ℂ → ℂ := fun s => Complex.Gamma (s - z) * (Λ : ℂ) ^ (s - z) with hg
  have hgd : DifferentiableAt ℂ g 1 := by
    have h2 : DifferentiableAt ℂ (fun s => Complex.Gamma (s - z)) 1 := by
      refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp (1 : ℂ) (differentiableAt_id.sub_const z)
      have := congrArg Complex.re h
      simp only [sub_re, one_re, neg_re, natCast_re] at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact h2.mul ((differentiableAt_id.sub_const z).const_cpow (Or.inl (ofReal_ne_zero.2 hΛ.ne')))
  have ht : Tendsto (fun w : ℂ => w + 1) (𝓝[≠] 0) (𝓝 1) := by
    have : Tendsto (fun w : ℂ => w + 1) (𝓝 0) (𝓝 (0 + 1)) := (continuous_id.add continuous_const).tendsto 0
    rw [zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  have ha : (fun w : ℂ => riemannZeta (w + 1) - 1 / w) =O[𝓝[≠] 0] (fun _ => (1 : ℂ)) := by
    have h := (isBigO_riemannZeta_sub_one_div (F := ℂ)).comp_tendsto ht
    refine h.congr_left fun w => ?_
    simp only [Function.comp, add_sub_cancel_right]
  have hb : (fun w : ℂ => g (w + 1)) =O[𝓝[≠] 0] (fun _ => (1 : ℂ)) :=
    (hgd.continuousAt.tendsto.comp ht).isBigO_one ℂ
  have hc : (fun w : ℂ => (g (w + 1) - g 1) / w) =O[𝓝[≠] 0] (fun _ => (1 : ℂ)) := by
    have hd := (hasDerivAt_iff_tendsto_slope_zero.1 hgd.hasDerivAt).isBigO_one ℂ
    refine hd.congr_left fun w => ?_
    rw [smul_eq_mul, add_comm 1 w, div_eq_inv_mul]
  have hab : (fun w : ℂ => (riemannZeta (w + 1) - 1 / w) * g (w + 1)) =O[𝓝[≠] 0] (fun _ => (1 : ℂ)) := by
    simpa using ha.mul hb
  have hsum := hab.add hc
  refine (hsum.congr' ?_ (Eventually.of_forall fun _ => by simp)).trans (isBigO_refl _ _)
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : w ≠ 0 := Set.mem_compl_singleton_iff.1 hw
  have hg1 : g 1 = Complex.Gamma (1 - z) * (Λ : ℂ) ^ (1 - z) := rfl
  simp only [Pi.sub_apply, zG, sub_zero]
  rw [← hg1]
  simp only [hg]
  field_simp
  ring

/-- **Off the line, far up**: `|ζ(x + 1 + iy)Γ(x + 1 + iy − z)Λ^{x+1+iy−z}| ≤ M(1 + |y − Im z|)^{−2}` on
`−11/12 ≤ x ≤ Re z + 1/2`, `|y| ≥ 2`, with `M = 576 KG Λ²(1 + |Im z|)`. -/
lemma zG_far {Λ : ℝ} (hΛ : 1 ≤ Λ) {z : ℂ} (hz1 : z.re ≤ 1 / 24) :
    ∀ x ∈ Set.Icc (-11 / 12 : ℝ) (z.re + 1 / 2), ∀ y : ℝ, 2 ≤ |y| →
      ‖zG Λ z ((x : ℂ) + y * I + 1)‖ ≤ (576 * KG * Λ ^ (2 : ℝ) * (1 + |z.im|)) * ((1 + |y + -z.im|) ^ 2)⁻¹ := by
  intro x hx y hy
  obtain ⟨hx1, hx2⟩ := hx
  have hKG := KG_pos
  have hs : (x : ℂ) + y * I + 1 = ((x + 1 : ℝ) : ℂ) + y * I := by push_cast; ring
  have hw : ((x + 1 : ℝ) : ℂ) + y * I - z = ((x + 1 - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hs]
  unfold zG
  rw [hw, norm_mul, norm_mul]
  have hζ : ‖riemannZeta (((x + 1 : ℝ) : ℂ) + y * I)‖ ≤ 24 * (1 + |y|) := by
    have h := norm_zeta_le_strip (σ := x + 1) (t := y) (by linarith) (by linarith) hy
    have : 2 * |y| / (x + 1) ≤ 24 * |y| := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [abs_nonneg y]
    linarith
  have hΓ : ‖Complex.Gamma (((x + 1 - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I)‖ * (1 + |y - z.im|) ^ 5
      ≤ 24 * KG := by
    have h := LinnikOffDiag.norm_Gamma_small (w := ((x + 1 - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I)
      (c' := 1 / 24) (by norm_num) (by simp; linarith) (by simp; linarith)
    have him : (((x + 1 - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I).im = y - z.im := by simp
    rw [him] at h
    calc _ ≤ KG / (1 / 24) := h
      _ = 24 * KG := by ring
  have hΛw : ‖(Λ : ℂ) ^ (((x + 1 - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I)‖ ≤ Λ ^ (2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hΛ (by simp; linarith)
  have hu : 0 < 1 + |y - z.im| := by positivity
  have hyb : 1 + |y| ≤ (1 + |z.im|) * (1 + |y - z.im|) := by
    have := abs_sub_abs_le_abs_sub y z.im
    nlinarith [abs_nonneg z.im, abs_nonneg (y - z.im)]
  have hΓ' : ‖Complex.Gamma (((x + 1 - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I)‖
      ≤ 24 * KG / (1 + |y - z.im|) ^ 5 := by
    rw [le_div_iff₀ (by positivity)]; exact hΓ
  have hneg : y + -z.im = y - z.im := by ring
  rw [hneg]
  have h25 : (1 + |y - z.im|) ^ 2 ≤ (1 + |y - z.im|) ^ 4 :=
    pow_le_pow_right₀ (by linarith [abs_nonneg (y - z.im)]) (by norm_num)
  calc ‖riemannZeta (((x + 1 : ℝ) : ℂ) + y * I)‖ *
        ‖Complex.Gamma (((x + 1 - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I)‖ *
        ‖(Λ : ℂ) ^ (((x + 1 - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I)‖
      ≤ (24 * ((1 + |z.im|) * (1 + |y - z.im|))) * (24 * KG / (1 + |y - z.im|) ^ 5) * Λ ^ (2 : ℝ) := by
        gcongr; linarith
    _ = 576 * KG * Λ ^ (2 : ℝ) * (1 + |z.im|) * ((1 + |y - z.im|) ^ 4)⁻¹ := by
        field_simp; ring
    _ ≤ 576 * KG * Λ ^ (2 : ℝ) * (1 + |z.im|) * ((1 + |y - z.im|) ^ 2)⁻¹ := by
        gcongr

/-- **The kernel past the pole**: for `Λ ≥ 1` and `0 ≤ Re z ≤ 1/24`,
`K_Λ(z) = Γ(1 − z)Λ^{1−z} + (1/2π)∫ ζ(1/12 + it)Γ(1/12 + it − z)Λ^{1/12+it−z} dt`. -/
theorem kz_eq {Λ : ℝ} (hΛ : 1 ≤ Λ) {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1 / 24) :
    ∑' n, kTerm χ₁ Λ z n = Complex.Gamma (1 - z) * (Λ : ℂ) ^ (1 - z) +
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, zG Λ z ((1 / 12 : ℝ) + t * I) := by
  have hΛ0 : 0 < Λ := by linarith
  rw [kz_eq_line hΛ0 hz0]
  set R : ℂ := Complex.Gamma (1 - z) * (Λ : ℂ) ^ (1 - z) with hR
  set G : ℂ → ℂ := fun u => zG Λ z (u + 1) with hG
  have hdiff : ∀ u : ℂ, -11 / 12 ≤ u.re → u ≠ 0 → DifferentiableAt ℂ G u := by
    intro u hu hu0
    refine (differentiableAt_zG hΛ0 z (fun h => hu0 (by linear_combination h)) ?_).comp u
      (differentiableAt_id.add_const 1)
    simp only [sub_re, add_re, one_re]; linarith
  have hhol : HolomorphicOn G ((Set.Icc (-11 / 12 : ℝ) (z.re + 1 / 2) ×ℂ Set.univ) \ {0}) := fun u hu => by
    have hu1 := hu.1
    rw [mem_reProdIm] at hu1
    exact (hdiff u hu1.1.1 hu.2).differentiableWithinAt
  have hO := zG_isBigO hΛ0 (z := z) (by linarith)
  set M : ℝ := 576 * KG * Λ ^ (2 : ℝ) * (1 + |z.im|) with hM
  have hM0 : 0 ≤ M := by have := KG_pos; positivity
  have hfar : ∀ x ∈ Set.Icc (-11 / 12 : ℝ) (z.re + 1 / 2), ∀ y : ℝ, 2 ≤ |y| →
      ‖G (x + y * I)‖ ≤ M * ((1 + |y + -z.im|) ^ 2)⁻¹ :=
    fun x hx y hy => zG_far hΛ hz1 x hx y hy
  have hline : ∀ x : ℝ, x ∈ Set.Icc (-11 / 12 : ℝ) (z.re + 1 / 2) → x ≠ 0 →
      Integrable fun t : ℝ => G (x + t * I) := by
    intro x hx hx0
    have hd : ∀ y : ℝ, DifferentiableAt ℂ G (x + y * I) := fun y => hdiff _ (by simp; exact hx.1) (by
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hx0 this)
    have hc : ContinuousOn (fun p : ℝ × ℝ => G (p.1 + p.2 * I)) (Set.Icc x x ×ˢ Set.Icc (-2) 2) :=
      continuousOn_rect fun x' hx' y _ => by rw [show x' = x by linarith [hx'.1, hx'.2]]; exact hd y
    obtain ⟨M', hM'0, hM'⟩ := bound_of_far hM0 hc fun x' hx' y hy => by
      rw [show x' = x by linarith [hx'.1, hx'.2]]
      exact hfar x hx y hy
    exact integrable_of_bound (continuous_line hd) (hM' x ⟨le_rfl, le_rfl⟩)
  have hint1 := hline (z.re + 1 / 2) ⟨by linarith, le_rfl⟩ (by linarith)
  have hint2 := hline (-11 / 12) ⟨le_rfl, by linarith⟩ (by norm_num)
  have hdec : ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Set.Icc (-11 / 12 : ℝ) (z.re + 1 / 2), ∀ y : ℝ, T₀ ≤ |y| →
      ‖G (x + y * I)‖ ≤ η := by
    intro η hη
    refine ⟨max 2 (|-z.im| + M / η + 1), fun x hx y hy => (hfar x hx y (le_trans (le_max_left _ _) hy)).trans ?_⟩
    have hy' : |-z.im| + M / η + 1 ≤ |y| := le_trans (le_max_right _ _) hy
    have h0 : |y| ≤ |y + -z.im| + |-z.im| := by
      calc |y| = |(y + -z.im) + (-(-z.im))| := by ring_nf
        _ ≤ |y + -z.im| + |-(-z.im)| := abs_add_le _ _
        _ = |y + -z.im| + |-z.im| := by rw [abs_neg]
    have h1 : M / η + 1 ≤ 1 + |y + -z.im| := by linarith
    have h2 : 1 + |y + -z.im| ≤ (1 + |y + -z.im|) ^ 2 := by nlinarith [abs_nonneg (y + -z.im)]
    have hpos : 0 < (1 + |y + -z.im|) ^ 2 := by positivity
    rw [mul_inv_le_iff₀ hpos]
    have h3 : M = η * (M / η) := by field_simp
    have h4 : 0 ≤ M / η := div_nonneg hM0 hη.le
    nlinarith
  have key := LinnikGamma.verticalIntegral_sub_eq (G := G) (σ' := -11 / 12) (σ := z.re + 1 / 2) (by norm_num)
    (by linarith) R hhol hO hint1 hint2 hdec
  unfold VerticalIntegral at key
  have e1 : (fun t : ℝ => G ((z.re + 1 / 2 : ℝ) + t * I)) = fun t : ℝ => zG Λ z ((z.re + 3 / 2 : ℝ) + t * I) := by
    funext t; simp only [hG]; congr 1; push_cast; ring
  have e2 : (fun t : ℝ => G ((-11 / 12 : ℝ) + t * I)) = fun t : ℝ => zG Λ z ((1 / 12 : ℝ) + t * I) := by
    funext t; simp only [hG]; congr 1; push_cast; ring
  rw [e1, e2, smul_eq_mul, smul_eq_mul, ← mul_sub] at key
  have h2 : (∫ t : ℝ, zG Λ z ((z.re + 3 / 2 : ℝ) + t * I)) =
      2 * π * R + ∫ t : ℝ, zG Λ z ((1 / 12 : ℝ) + t * I) := by
    have := mul_left_cancel₀ I_ne_zero (key.trans (by ring : 2 * π * I * R = I * (2 * π * R)))
    linear_combination this
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hR2 : (1 / (2 * π) : ℂ) * (2 * π * R) = R := by field_simp
  rw [h2, mul_add, hR2]

/-- `|ζ(1/12 + it)| ≤ C(|t| + 2)^{5/12+ε}` for every `t` (`Subconvexity.zeta_strip_eleven_twelfths` for `|t| ≥ 2`). -/
lemma zeta_left_line {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖riemannZeta ((1 / 12 : ℝ) + t * I)‖ ≤ C * (|t| + 2) ^ (5 / 12 + ε) := by
  obtain ⟨C₁, hC₁⟩ := Subconvexity.zeta_strip_eleven_twelfths (σ := 1 / 12) (ε := ε) (by norm_num) (by norm_num) hε
  have hc : ContinuousOn (fun t : ℝ => riemannZeta ((1 / 12 : ℝ) + t * I)) (Set.Icc (-2) 2) := by
    intro t _
    have hne : ((1 / 12 : ℝ) : ℂ) + t * I ≠ 1 := fun h => by
      have := congrArg Complex.re h; norm_num at this
    exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => ((1 / 12 : ℝ) : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨|C₁| + |C₂|, by positivity, fun t => ?_⟩
  have h1 : (1 : ℝ) ≤ (|t| + 2) ^ (5 / 12 + ε) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by linarith)
  rcases le_or_gt 2 |t| with ht | ht
  · have h := hC₁ t ht
    have e : (11 / 12 - 1 / 12 : ℝ) / 2 + ε = 5 / 12 + ε := by ring
    rw [e] at h
    have h2 : |t| ^ (5 / 12 + ε) ≤ (|t| + 2) ^ (5 / 12 + ε) :=
      Real.rpow_le_rpow (abs_nonneg t) (by linarith) (by linarith)
    have h0 : 0 ≤ |t| ^ (5 / 12 + ε) := by positivity
    calc ‖riemannZeta ((1 / 12 : ℝ) + t * I)‖ ≤ C₁ * |t| ^ (5 / 12 + ε) := h
      _ ≤ |C₁| * |t| ^ (5 / 12 + ε) := mul_le_mul_of_nonneg_right (le_abs_self C₁) h0
      _ ≤ |C₁| * (|t| + 2) ^ (5 / 12 + ε) := by gcongr
      _ ≤ (|C₁| + |C₂|) * (|t| + 2) ^ (5 / 12 + ε) := by gcongr; exact le_add_of_nonneg_right (abs_nonneg _)
  · have h := hC₂ t ⟨by linarith [(abs_lt.1 ht).1], by linarith [(abs_lt.1 ht).2]⟩
    calc ‖riemannZeta ((1 / 12 : ℝ) + t * I)‖ ≤ |C₂| := h.trans (le_abs_self C₂)
      _ ≤ (|C₁| + |C₂|) * 1 := by linarith [abs_nonneg C₁]
      _ ≤ (|C₁| + |C₂|) * (|t| + 2) ^ (5 / 12 + ε) := by gcongr

/-- **The kernel bound**: for `0 < ε ≤ 7/12` there is `C` with
`|Σ_{n≥1} n^{−z}e^{−n/Λ}| ≤ KE·Λe^{−|Im z|} + CΛ^{1/12}(|Im z| + 2)^{5/12+ε}` for `Λ ≥ 1` and `0 ≤ Re z ≤ 1/24`. -/
theorem norm_kz_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 7 / 12) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 24 →
      ‖∑' n, kTerm χ₁ Λ z n‖ ≤ KE * Λ * Real.exp (-|z.im|) + C * Λ ^ (1 / 12 : ℝ) * (|z.im| + 2) ^ (5 / 12 + ε) := by
  obtain ⟨Cζ, hCζ0, hCζ⟩ := zeta_left_line hε
  have hKG := KG_pos
  refine ⟨12 * KG * Cζ, by positivity, fun Λ hΛ z hz0 hz1 => ?_⟩
  have hΛ0 : 0 < Λ := by linarith
  rw [kz_eq hΛ hz0 hz1]
  set e : ℝ := 5 / 12 + ε with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by linarith
  -- the residue
  have hRb : ‖Complex.Gamma (1 - z) * (Λ : ℂ) ^ (1 - z)‖ ≤ KE * Λ * Real.exp (-|z.im|) := by
    rw [norm_mul]
    have hw : (1 : ℂ) - z = ((1 - z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I := by apply Complex.ext <;> simp
    have hG := norm_Gamma_exp_le (x := 1 - z.re) (by linarith) (by linarith) (-z.im)
    rw [← hw, abs_neg] at hG
    have hΛw : ‖(Λ : ℂ) ^ (1 - z)‖ ≤ Λ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hΛ0]
      calc Λ ^ (1 - z).re ≤ Λ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ (by simp; linarith)
        _ = Λ := Real.rpow_one Λ
    have hKEe : 0 ≤ KE * Real.exp (-|z.im|) := by have := KE_pos; positivity
    calc ‖Complex.Gamma (1 - z)‖ * ‖(Λ : ℂ) ^ (1 - z)‖ ≤ KE * Real.exp (-|z.im|) * Λ := by gcongr
      _ = KE * Λ * Real.exp (-|z.im|) := by ring
  -- the line `Re s = 1/12`
  set A : ℝ := 24 * KG * Cζ * Λ ^ (1 / 12 : ℝ) * (|z.im| + 2) ^ e with hA
  have hA0 : 0 ≤ A := by positivity
  have hpt : ∀ t : ℝ, ‖zG Λ z ((1 / 12 : ℝ) + t * I)‖ ≤ A * (1 + (t - z.im) ^ 2)⁻¹ := by
    intro t
    have hw : ((1 / 12 : ℝ) : ℂ) + t * I - z = ((1 / 12 - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have hΓ := LinnikOffDiag.norm_Gamma_small (w := ((1 / 12 - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I)
      (c' := 1 / 24) (by norm_num) (by simp; linarith) (by simp; linarith)
    have him : (((1 / 12 - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I).im = t - z.im := by simp
    rw [him] at hΓ
    have hΛw : ‖(Λ : ℂ) ^ (((1 / 12 - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I)‖ ≤ Λ ^ (1 / 12 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hΛ0]
      exact Real.rpow_le_rpow_of_exponent_le hΛ (by simp; linarith)
    have hbase : (|t| + 2) ^ e ≤ (|z.im| + 2) ^ e * (1 + |t - z.im|) := by
      have h1 : |t| + 2 ≤ (|z.im| + 2) * (1 + |t - z.im|) := by
        have := abs_sub_abs_le_abs_sub t z.im
        nlinarith [abs_nonneg z.im, abs_nonneg (t - z.im)]
      calc (|t| + 2) ^ e ≤ ((|z.im| + 2) * (1 + |t - z.im|)) ^ e :=
            Real.rpow_le_rpow (by positivity) h1 he0
        _ = (|z.im| + 2) ^ e * (1 + |t - z.im|) ^ e := Real.mul_rpow (by positivity) (by positivity)
        _ ≤ (|z.im| + 2) ^ e * (1 + |t - z.im|) := by
            gcongr
            calc (1 + |t - z.im|) ^ e ≤ (1 + |t - z.im|) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (t - z.im)]) he1
              _ = 1 + |t - z.im| := Real.rpow_one _
    have h4 : (1 + |t - z.im|) * (1 + (t - z.im) ^ 2) ≤ (1 + |t - z.im|) ^ 5 := by
      have hsq : 1 + (t - z.im) ^ 2 ≤ (1 + |t - z.im|) ^ 2 := by
        nlinarith [abs_nonneg (t - z.im), sq_abs (t - z.im)]
      have h11 : 1 ≤ 1 + |t - z.im| := by linarith [abs_nonneg (t - z.im)]
      calc (1 + |t - z.im|) * (1 + (t - z.im) ^ 2) ≤ (1 + |t - z.im|) * (1 + |t - z.im|) ^ 2 := by gcongr
        _ = (1 + |t - z.im|) ^ 3 := by ring
        _ ≤ (1 + |t - z.im|) ^ 5 := pow_le_pow_right₀ h11 (by norm_num)
    have hΓ' : ‖Complex.Gamma (((1 / 12 - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I)‖
        ≤ 24 * KG / (1 + |t - z.im|) ^ 5 := by
      rw [le_div_iff₀ (by positivity)]
      calc _ ≤ KG / (1 / 24) := hΓ
        _ = 24 * KG := by ring
    have hζ : ‖riemannZeta ((1 / 12 : ℝ) + t * I)‖ ≤ Cζ * ((|z.im| + 2) ^ e * (1 + |t - z.im|)) :=
      (hCζ t).trans (mul_le_mul_of_nonneg_left hbase hCζ0)
    unfold zG
    rw [hw, norm_mul, norm_mul]
    calc ‖riemannZeta ((1 / 12 : ℝ) + t * I)‖ *
          ‖Complex.Gamma (((1 / 12 - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I)‖ *
          ‖(Λ : ℂ) ^ (((1 / 12 - z.re : ℝ) : ℂ) + ((t - z.im : ℝ) : ℂ) * I)‖
        ≤ (Cζ * ((|z.im| + 2) ^ e * (1 + |t - z.im|))) * (24 * KG / (1 + |t - z.im|) ^ 5) *
            Λ ^ (1 / 12 : ℝ) := by gcongr
      _ = A * ((1 + |t - z.im|) / (1 + |t - z.im|) ^ 5) := by rw [hA]; field_simp
      _ ≤ A * (1 + (t - z.im) ^ 2)⁻¹ := by
          gcongr
          rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
          linarith
  have hint : Integrable fun t : ℝ => A * (1 + (t - z.im) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_sub_right z.im).const_mul A
  have hI : ‖∫ t : ℝ, zG Λ z ((1 / 12 : ℝ) + t * I)‖ ≤ A * π := by
    calc ‖∫ t : ℝ, zG Λ z ((1 / 12 : ℝ) + t * I)‖ ≤ ∫ t : ℝ, A * (1 + (t - z.im) ^ 2)⁻¹ :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
      _ = A * π := by
          rw [integral_const_mul, integral_sub_right_eq_self (fun t : ℝ => (1 + t ^ 2)⁻¹) z.im,
            integral_univ_inv_one_add_sq]
  have hc2 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hpi := Real.pi_pos
  have hsplit : ‖(1 / (2 * π) : ℂ) * ∫ t : ℝ, zG Λ z ((1 / 12 : ℝ) + t * I)‖ =
      1 / (2 * π) * ‖∫ t : ℝ, zG Λ z ((1 / 12 : ℝ) + t * I)‖ := by rw [norm_mul, hc2]
  calc ‖Complex.Gamma (1 - z) * (Λ : ℂ) ^ (1 - z) + (1 / (2 * π) : ℂ) * ∫ t : ℝ, zG Λ z ((1 / 12 : ℝ) + t * I)‖
      ≤ ‖Complex.Gamma (1 - z) * (Λ : ℂ) ^ (1 - z)‖ +
          ‖(1 / (2 * π) : ℂ) * ∫ t : ℝ, zG Λ z ((1 / 12 : ℝ) + t * I)‖ := norm_add_le _ _
    _ = ‖Complex.Gamma (1 - z) * (Λ : ℂ) ^ (1 - z)‖ + 1 / (2 * π) * ‖∫ t : ℝ, zG Λ z ((1 / 12 : ℝ) + t * I)‖ := by
        rw [hsplit]
    _ ≤ KE * Λ * Real.exp (-|z.im|) + 1 / (2 * π) * (A * π) := by gcongr
    _ = KE * Λ * Real.exp (-|z.im|) + 12 * KG * Cζ * Λ ^ (1 / 12 : ℝ) * (|z.im| + 2) ^ e := by
        rw [hA]; field_simp; ring

/-! ### The power count at points -/

/-- **The residue terms**: for 1-separated heights and `Λ ≥ 1`, `Σ_{r′ ≠ r} Λe^{−|γ_r − γ_{r′}|} ≤
Λ(2 log Λ + 1) + |R|`: at most `2 log Λ + 1` of the heights lie within `log Λ` of `γ_r`
(`ZetaFourth.card_le_of_sep`), and the others contribute at most `1` each. -/
lemma sum_pole_le {ι : Type*} [DecidableEq ι] (R : Finset ι) (γ : ι → ℝ)
    (hsep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 1 ≤ |γ r - γ r'|) {Λ : ℝ} (hΛ : 1 ≤ Λ) (r : ι) :
    ∑ r' ∈ R.erase r, Λ * Real.exp (-|γ r - γ r'|) ≤ Λ * (2 * Real.log Λ + 1) + R.card := by
  have hΛ0 : 0 < Λ := by linarith
  have hl0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  rw [← sum_filter_add_sum_filter_not (R.erase r) (fun r' => |γ r - γ r'| ≤ Real.log Λ)]
  have h1 : ∑ r' ∈ (R.erase r).filter (fun r' => |γ r - γ r'| ≤ Real.log Λ), Λ * Real.exp (-|γ r - γ r'|)
      ≤ Λ * (2 * Real.log Λ + 1) := by
    have hcard : (((R.erase r).filter (fun r' => |γ r - γ r'| ≤ Real.log Λ)).card : ℝ) ≤ 2 * Real.log Λ + 1 :=
      card_le_of_sep _ (fun r' => γ r' - γ r)
        (fun a ha b hb hab => by
          have := hsep a (mem_of_mem_erase (mem_filter.1 ha).1) b (mem_of_mem_erase (mem_filter.1 hb).1) hab
          rwa [show γ a - γ r - (γ b - γ r) = γ a - γ b by ring])
        hl0 (fun a ha => by rw [abs_sub_comm]; exact (mem_filter.1 ha).2)
    calc ∑ r' ∈ (R.erase r).filter (fun r' => |γ r - γ r'| ≤ Real.log Λ), Λ * Real.exp (-|γ r - γ r'|)
        ≤ ∑ _r' ∈ (R.erase r).filter (fun r' => |γ r - γ r'| ≤ Real.log Λ), Λ := by
          refine sum_le_sum fun r' _ => ?_
          have : Real.exp (-|γ r - γ r'|) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [abs_nonneg (γ r - γ r')])
          nlinarith
      _ = ((R.erase r).filter (fun r' => |γ r - γ r'| ≤ Real.log Λ)).card * Λ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 * Real.log Λ + 1) * Λ := by gcongr
      _ = Λ * (2 * Real.log Λ + 1) := by ring
  have h2 : ∑ r' ∈ (R.erase r).filter (fun r' => ¬ |γ r - γ r'| ≤ Real.log Λ), Λ * Real.exp (-|γ r - γ r'|)
      ≤ R.card := by
    calc ∑ r' ∈ (R.erase r).filter (fun r' => ¬ |γ r - γ r'| ≤ Real.log Λ), Λ * Real.exp (-|γ r - γ r'|)
        ≤ ∑ _r' ∈ (R.erase r).filter (fun r' => ¬ |γ r - γ r'| ≤ Real.log Λ), (1 : ℝ) := by
          refine sum_le_sum fun r' hr' => ?_
          have hlt : Real.log Λ < |γ r - γ r'| := lt_of_not_ge (mem_filter.1 hr').2
          have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith : -|γ r - γ r'| ≤ -Real.log Λ))
            hΛ0.le
          have he : Λ * Real.exp (-Real.log Λ) = 1 := by
            rw [Real.exp_neg, Real.exp_log hΛ0, mul_inv_cancel₀ hΛ0.ne']
          linarith
      _ = ((R.erase r).filter (fun r' => ¬ |γ r - γ r'| ≤ Real.log Λ)).card := by
          rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ R.card := by exact_mod_cast (card_filter_le _ _).trans (card_erase_le)
  linarith

/-- **Large values of a power at well-spaced heights**: points `β_r + iγ_r`, `σ_b ≤ β_r < σ_b + 1/48`, with
1-separated heights within `T₀` of each other, at which a block `F = Σ_{j∈S} c_j j^{−s}` on `(P, 2P]` with
`|c_j| ≤ d(j)` is at least `V`, number at most `2e·G_m·Λ(1 + KE(2 log Λ + 1))/V^{2m}`, `Λ = (2P)^m`, when
`|K_Λ(z)| ≤ KE·Λe^{−|Im z|} + B` for `0 ≤ Re z ≤ 1/24`, `|Im z| ≤ T₀`, and `2e·G_m(KE + B) ≤ V^{2m}`. -/
theorem power_count_pts {ι : Type*} {R : Finset ι} {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P)
    (hS : S ⊆ Ioc P (2 * P)) {c : ℕ → ℂ} (hc : ∀ j ∈ S, ‖c j‖ ≤ (j.divisors.card : ℝ)) {m : ℕ} (hm : 1 ≤ m)
    {σb : ℝ} (hσb : 0 ≤ σb) (β γ : ι → ℝ) (hβ : ∀ r ∈ R, σb ≤ β r ∧ β r < σb + 1 / 48)
    (hsep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 1 ≤ |γ r - γ r'|) {T₀ : ℝ}
    (hT₀ : ∀ r ∈ R, ∀ r' ∈ R, |γ r - γ r'| ≤ T₀)
    {V : ℝ} (hV : 0 < V) (hbig : ∀ r ∈ R, V ≤ ‖pv S c χ₁ ((β r : ℂ) + γ r * I)‖)
    {εd : ℝ} (hεd : 0 < εd) (hεd1 : εd ≤ 1) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 / 24 → |z.im| ≤ T₀ →
      ‖∑' n, kTerm χ₁ (((2 * P : ℕ) : ℝ) ^ m) z n‖ ≤ KE * ((2 * P : ℕ) : ℝ) ^ m * Real.exp (-|z.im|) + B)
    (hfeas : 2 * Real.exp 1 * Gm εd P m σb * (KE + B) ≤ V ^ (2 * m)) :
    (R.card : ℝ) ≤ 2 * Real.exp 1 * Gm εd P m σb * ((2 * P : ℕ) : ℝ) ^ m *
      (1 + KE * (2 * Real.log (((2 * P : ℕ) : ℝ) ^ m) + 1)) / V ^ (2 * m) := by
  classical
  set Λ : ℝ := ((2 * P : ℕ) : ℝ) ^ m with hΛ
  have hS0 : 0 ∉ powSupp S m := fun h => by
    have := mem_Ioc.1 (powSupp_sub hS hm h); omega
  have h2P : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P)
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h2P
  have hΛ0 : 0 < Λ := by linarith
  have hSΛ : ∀ n ∈ powSupp S m, (n : ℝ) ≤ Λ := fun n hn => by
    have := (mem_Ioc.1 (powSupp_sub hS hm hn)).2
    rw [hΛ]; push_cast; exact_mod_cast this
  have hKE := KE_pos
  set Bf : ι → ι → ℝ := fun r r' => KE * Λ * Real.exp (-|γ r - γ r'|) + B with hBf
  have hdual := hm_duality_pts hS0 hΛ0 hSΛ (powCo S c m) β γ (fun r hr => (hβ r hr).1) Bf (by
    intro r hr r' hr' _
    have hzre : (((β r + β r' - 2 * σb : ℝ) : ℂ) + ((γ r - γ r' : ℝ) : ℂ) * I).re = β r + β r' - 2 * σb := by
      simp
    have hzim : (((β r + β r' - 2 * σb : ℝ) : ℂ) + ((γ r - γ r' : ℝ) : ℂ) * I).im = γ r - γ r' := by simp
    have h1 := hβ r hr
    have h2 := hβ r' hr'
    have := hK _ (by rw [hzre]; linarith) (by rw [hzre]; linarith) (by rw [hzim]; exact hT₀ r hr r' hr')
    rw [hzim] at this
    exact this)
  have hmass := mass_pow_le hP hS hc hm hσb hεd hεd1
  set G := Gm εd P m σb with hG
  have hG0 : 0 ≤ G := by rw [hG, Gm]; have := one_le_Cdiv hεd hεd1; positivity
  set L : ℝ := 1 + KE * (2 * Real.log Λ + 1) with hL
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg hΛ1
    rw [hL]; nlinarith
  set R0 : ℝ := (R.card : ℝ) with hR0
  have hR00 : 0 ≤ R0 := Nat.cast_nonneg _
  -- each row of the double sum
  have hrow : ∀ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else Bf r r') ≤ Λ * L + R0 * (KE + B) := by
    intro r hr
    rw [← add_sum_erase R _ hr, ite_eq_left rfl]
    have hoff : ∀ r' ∈ R.erase r, (if r = r' then Λ else Bf r r') = KE * (Λ * Real.exp (-|γ r - γ r'|)) + B :=
      fun r' hr' => by rw [ite_eq_right (Ne.symm (ne_of_mem_erase hr'))]; simp only [hBf]; ring
    rw [sum_congr rfl hoff, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    have hpole := sum_pole_le R γ hsep hΛ1 r
    have hcard : ((R.erase r).card : ℝ) ≤ R0 := by rw [hR0]; exact_mod_cast card_erase_le
    have h1 : KE * ∑ r' ∈ R.erase r, Λ * Real.exp (-|γ r - γ r'|) ≤ KE * (Λ * (2 * Real.log Λ + 1) + R0) :=
      mul_le_mul_of_nonneg_left hpole hKE.le
    have h2 : ((R.erase r).card : ℝ) * B ≤ R0 * B := mul_le_mul_of_nonneg_right hcard hB0
    rw [hL]; nlinarith
  have hdsum : ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else Bf r r') ≤ R0 * (Λ * L + R0 * (KE + B)) := by
    calc ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else Bf r r') ≤ ∑ _r ∈ R, (Λ * L + R0 * (KE + B)) :=
          sum_le_sum hrow
      _ = R0 * (Λ * L + R0 * (KE + B)) := by rw [sum_const, nsmul_eq_mul]
  have hd0 : 0 ≤ ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else Bf r r') := by
    refine sum_nonneg fun r _ => sum_nonneg fun r' _ => ?_
    split_ifs
    · linarith
    · simp only [hBf]; positivity
  -- each point contributes at least `V^m`
  have hlow : R0 * V ^ m ≤ ∑ r ∈ R, ‖pv (powSupp S m) (powCo S c m) χ₁ ((β r : ℂ) + γ r * I)‖ := by
    rw [hR0, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun r hr => ?_
    rw [← pv_pow, norm_pow]
    exact pow_le_pow_left₀ hV.le (hbig r hr) m
  have hVm : 0 < V ^ m := by positivity
  have hsq : (R0 * V ^ m) ^ 2 ≤ Real.exp 1 * G * (R0 * (Λ * L + R0 * (KE + B))) := by
    have h1 : (R0 * V ^ m) ^ 2 ≤ (∑ r ∈ R, ‖pv (powSupp S m) (powCo S c m) χ₁ ((β r : ℂ) + γ r * I)‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    refine h1.trans (hdual.trans ?_)
    calc Real.exp 1 * (∑ n ∈ powSupp S m, ‖powCo S c m n‖ ^ 2 * ((n : ℝ) ^ (-σb)) ^ 2) *
          ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else Bf r r')
        ≤ Real.exp 1 * G * ∑ r ∈ R, ∑ r' ∈ R, (if r = r' then Λ else Bf r r') := by gcongr
      _ ≤ Real.exp 1 * G * (R0 * (Λ * L + R0 * (KE + B))) := by gcongr
  -- solve for `|R|`
  have hV2 : V ^ (2 * m) = (V ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [le_div_iff₀ (by positivity)]
  rcases eq_or_lt_of_le hR00 with h0 | hpos
  · rw [← h0, zero_mul]; positivity
  · have h2 : R0 * (V ^ m) ^ 2 ≤ Real.exp 1 * G * (Λ * L) + Real.exp 1 * G * (KE + B) * R0 := by
      have e1 : (R0 * V ^ m) ^ 2 = R0 * (R0 * (V ^ m) ^ 2) := by ring
      have e2 : Real.exp 1 * G * (R0 * (Λ * L + R0 * (KE + B))) =
          R0 * (Real.exp 1 * G * (Λ * L) + Real.exp 1 * G * (KE + B) * R0) := by ring
      rw [e1, e2] at hsq
      exact le_of_mul_le_mul_left hsq hpos
    have h3 : Real.exp 1 * G * (KE + B) * R0 ≤ R0 * (V ^ m) ^ 2 / 2 := by
      rw [← hV2]; nlinarith
    rw [hV2]
    nlinarith

/-- A dyadic block of `Pv b` is a Dirichlet polynomial `pv` at `s = β + iγ`, with the trivial character mod `1`. -/
theorem Fkb_eq_pv (b : ℕ → ℂ) (X N k : ℕ) (β γ : ℝ) :
    Fkb b X N k β γ = pv ((Ioc X (X * N)).filter (fun j => blk X j = k)) b χ₁ ((β : ℂ) + γ * I) := by
  unfold Fkb dp pv
  refine sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := by have := (mem_Ioc.1 (mem_filter.1 hj).1).1; omega
  have hn0 : (j : ℂ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hnr : (0 : ℝ) < j := by exact_mod_cast hj1
  have hc : (j : ℂ) ^ (-((β : ℂ) + γ * I))
      = (((j : ℝ) ^ (-β) : ℝ) : ℂ) * Complex.exp (-(I * ((γ * Real.log j : ℝ) : ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Real.rpow_def_of_pos hnr]
    have hlog : Complex.log (j : ℂ) = (Real.log j : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hnr.le]
    rw [hlog, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hc, χ₁_apply]; ring

end ZetaKernel

#print axioms ZetaKernel.hm_duality_pts
#print axioms ZetaKernel.kz_eq
#print axioms ZetaKernel.norm_kz_le
#print axioms ZetaKernel.power_count_pts
#print axioms ZetaKernel.Fkb_eq_pv
