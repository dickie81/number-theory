/-
# Primes in almost all short intervals, part 1: the explicit formula at one point

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`ShortWeil.lower_bound` bounds the zero sum of Weil's formula for `h = 2cos(Lz)ĝ_J(z)²` by the sum of the moduli of
its terms, and the archimedean term by `(4b)^k log(1/b)/b`. Both bounds lose what the almost-all argument needs: the
zero sum is small only on average over `L`, and the archimedean term is in fact of size `e^{−L/2}`, not
`b^{k−1}log(1/b)`, once the test function vanishes at `0`. This file keeps both:
* `explicit_identity`: for `L > 2^{J+1}b`, the weighted prime sum equals the pole term plus the archimedean term minus
  `Re(2Σ_τ h(τ))`, the zero sum over the zeros of `Ξ` (`summable_hmod_tau`, `norm_hmod_tau_le`).
* `arch_far`: for `L ≥ 2^{J+1}b + 1/2` the archimedean term is at most `8D(2b)^{k−1}e^{−(L−D)/2}`, `D = 2^{J+1}b`,
  `k = 2^{J+1}`. Gauss's digamma integral (`WeilForm.psiReQ_sub`) and Fubini turn it into
  `−∫_0^∞ k_{1/4}(t) f(L − t/2) dt` with `f = g_{J+1}`, which is supported on `|L − t/2| ≤ D`, where
  `k_{1/4}(t) = e^{−t/4}/(1 − e^{−t}) ≤ 2e^{−(L−D)/2}`.
* `sum_vonMangoldt_nonprime_le`: the prime powers `p^m`, `m ≥ 2`, in `[a, c]` carry at most
  `log c · log₂ c · ((c − a)/(2√a) + 1)` of `Λ`-mass, since for each `m` at most `(c − a)/(2√a) + 1` integers `d` have
  `a ≤ d^m ≤ c` (`card_pow_mem_le`). `ShortWeil.exists_prime_of_window` uses `ψ − θ ≤ 2√c log c` instead, which is
  too large for windows shorter than `√c`.
* `prime_of_P`: a lower bound `√x(2be^{−b/2})^k ≤ 2P` on the weighted prime sum `P` at `x` gives a prime in
  `[xe^{−D}, xe^D]`, once the window's mass `bxe^{−(k+1)/2}` beats that prime-power bound.
-/
import ShortPrimes
import ExplicitBridge

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace AlmostAll

open ShortWeil WeilForm WeilTest WeilStrip

/-! ## The archimedean term at large `L` -/

/-- `ĝ_J(r)² ≤ (4b)^k/(1 + b|r|)^k` with `k = 2^{J+1}`. -/
theorem hsq_gI_le {b : ℝ} (hb : 0 < b) (J : ℕ) (r : ℝ) :
    hsq (gI b J) (2 ^ J * b) r ≤ (4 * b) ^ (2 ^ (J + 1)) / (1 + b * |r|) ^ (2 ^ (J + 1)) := by
  have hE := gI_esupp hb J
  set q := 1 + b * |r| with hq
  have hq1 : 1 ≤ q := by have := abs_nonneg r; nlinarith
  have hg : |gH (gI b J) (2 ^ J * b) r| ≤ (4 * b / q) ^ (2 ^ J) := by
    have h1 := norm_ghatC_gI_le hb J (r : ℂ)
    rw [ghatC_real hE (by positivity) r, Complex.norm_real, Real.norm_eq_abs] at h1
    simpa [Complex.norm_real, Real.norm_eq_abs] using h1
  unfold hsq
  rw [← sq_abs]
  calc |gH (gI b J) (2 ^ J * b) r| ^ 2 ≤ ((4 * b / q) ^ (2 ^ J)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hg 2
    _ = (4 * b) ^ (2 ^ (J + 1)) / q ^ (2 ^ (J + 1)) := by rw [← pow_mul, div_pow, pow_succ]

/-- `ĝ_J(r)²(|Re ψ(¼ + ir/2)| + |Re ψ(¼)|) ≤ 2(4b)^k C₁/(1 + (br)²)`, `C₁ = log(1/b) + 5 + |Re ψ(¼)|`. -/
theorem hsq_psi_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {J : ℕ} (hJ : 1 ≤ J) (r : ℝ) :
    hsq (gI b J) (2 ^ J * b) r * (|psiRe r| + |psiRe 0|)
      ≤ 2 * (4 * b) ^ (2 ^ (J + 1)) * (Real.log (1 / b) + 5 + |psiRe 0|) * (1 + (b * r) ^ 2)⁻¹ := by
  set k := 2 ^ (J + 1) with hk
  set B := (4 * b) ^ k with hB
  set C1 := Real.log (1 / b) + 5 + |psiRe 0| with hC1
  have hlb : 0 ≤ Real.log (1 / b) := Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith)
  have hk4 : 4 ≤ k := by
    have : 2 ≤ 2 ^ J := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ
    rw [hk, pow_succ]; omega
  set q := 1 + b * |r| with hq
  have hq1 : 1 ≤ q := by have := abs_nonneg r; nlinarith
  have hsq_le : hsq (gI b J) (2 ^ J * b) r ≤ B / q ^ k := hsq_gI_le hb J r
  have hps : |psiRe r| + |psiRe 0| ≤ 2 * C1 * q := by
    have h1 := abs_psiRe_le r
    have h2 : Real.log (1 + |r|) ≤ Real.log (1 / b) + Real.log q := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      apply Real.log_le_log (by positivity)
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hb, hq]; nlinarith [abs_nonneg r]
    have h3 : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
    nlinarith [abs_nonneg (psiRe 0)]
  have hqk : q ^ 3 ≤ q ^ k := pow_le_pow_right₀ hq1 (by omega)
  have hq2 : 1 + (b * r) ^ 2 ≤ q ^ 2 := by
    rw [hq, mul_pow, ← sq_abs r]; nlinarith [abs_nonneg r, hb.le]
  have hC1 : 0 ≤ C1 := by positivity
  have hB0 : 0 ≤ B := by positivity
  calc hsq (gI b J) (2 ^ J * b) r * (|psiRe r| + |psiRe 0|) ≤ B / q ^ k * (2 * C1 * q) :=
        mul_le_mul hsq_le hps (by positivity) (by positivity)
    _ = 2 * B * C1 * (q / q ^ k) := by ring
    _ ≤ 2 * B * C1 * (1 + (b * r) ^ 2)⁻¹ := by
        gcongr
        rw [div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
        calc q * (1 + (b * r) ^ 2) ≤ q * q ^ 2 := by gcongr
          _ = q ^ 3 := by ring
          _ ≤ q ^ k := hqk

/-- `k_{1/4}(t) ≤ 2e^{−t/4}` for `t ≥ 1`. -/
theorem kkQ_quarter_le {t : ℝ} (ht : 1 ≤ t) : kkQ (1 / 4) t ≤ 2 * Real.exp (-(t / 4)) := by
  unfold kkQ
  have h1 : Real.exp (-t) ≤ 1 / 2 := by
    have : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg]; rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.add_one_le_exp (1 : ℝ); norm_num at this ⊢; linarith
    linarith
  rw [div_le_iff₀ (by linarith), show -(1 / 4 * t) = -(t / 4) by ring]
  have := Real.exp_pos (-(t / 4))
  nlinarith

/-- **The archimedean term far from `0`**: for `L ≥ D + 1/2`, `D = 2^{J+1}b`,
`|(1/2π)∫h_R(r) Re ψ(¼ + ir/2) dr| ≤ 8D(2b)^{k−1}e^{−(L−D)/2}`. -/
theorem arch_far {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {J : ℕ} (hJ : 1 ≤ J) {L : ℝ}
    (hL : 2 ^ (J + 1) * b + 1 / 2 ≤ L) :
    |1 / (2 * π) * ∫ r, hmodR b J L r * psiRe r|
      ≤ 8 * (2 ^ (J + 1) * b) * (2 * b) ^ (2 ^ (J + 1) - 1) * Real.exp (-((L - 2 ^ (J + 1) * b) / 2)) := by
  set D : ℝ := 2 ^ (J + 1) * b with hD
  set a : ℝ := 2 ^ J * b with ha
  set g := gI b J with hg
  set f := gI b (J + 1) with hf
  have hE : ESupp a g := gI_esupp hb J
  have hfE : ESupp D f := gI_esupp hb (J + 1)
  have ha0 : 0 < a := by positivity
  have hD0 : 0 < D := by positivity
  have hfa : ∀ u, autocorr g u = f u := fun u => rfl
  set ν := volume.restrict (Ioi (0 : ℝ)) with hν
  set F : ℝ × ℝ → ℝ := fun p => hsq g a p.1 * (kkQ (1 / 4) p.2 * (1 - Real.cos (p.1 * (p.2 / 2))))
    with hFd
  have hFm : AEStronglyMeasurable F (volume.prod ν) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((continuous_hsq hE).measurable.comp measurable_fst).mul
      (((measurable_kkQ (1 / 4)).comp measurable_snd).mul ?_)
    exact (Continuous.measurable (by fun_prop))
  have hFnn : ∀ r, ∀ t, 0 < t → 0 ≤ F (r, t) := fun r t ht =>
    mul_nonneg (hsq_nonneg r)
      (mul_nonneg (kkQ_nonneg _ ht) (by linarith [Real.cos_le_one (r * (t / 2))]))
  have hq0 : (0 : ℝ) < 1 / 4 := by norm_num
  -- the `t`-integral at each `r` is Gauss's digamma integral
  have hFr : ∀ r, Integrable (fun t => F (r, t)) ν ∧
      ∫ t, F (r, t) ∂ν = hsq g a r * (psiRe r - psiRe 0) := by
    intro r
    obtain ⟨hi, he⟩ := psiReQ_sub hq0 r
    rw [psiReQ_quarter] at he
    refine ⟨hi.const_mul (hsq g a r), ?_⟩
    simp only [hFd]
    rw [integral_const_mul, he]
  have hF : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff hFm]
    refine ⟨Eventually.of_forall fun r => (hFr r).1, ?_⟩
    have heq : (fun r => ∫ t, ‖F (r, t)‖ ∂ν) = fun r => hsq g a r * (psiRe r - psiRe 0) := by
      funext r
      rw [← (hFr r).2]
      refine integral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      show ‖F (r, t)‖ = F (r, t)
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn r t ht)]
    have hmeas : AEStronglyMeasurable (fun r => ∫ t, ‖F (r, t)‖ ∂ν) volume :=
      hFm.norm.integral_prod_right'
    rw [heq] at hmeas ⊢
    refine Integrable.mono' (((integrable_inv_one_add_sq.comp_mul_left' hb.ne').const_mul
      (2 * (4 * b) ^ (2 ^ (J + 1)) * (Real.log (1 / b) + 5 + |psiRe 0|)))) hmeas
      (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hsq_nonneg r)]
    refine le_trans ?_ (hsq_psi_le hb hb1 hJ r)
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (hsq_nonneg r)
  set G : ℝ × ℝ → ℝ := fun p => Real.cos (L * p.1) * F p with hGd
  have hG : Integrable G (volume.prod ν) := by
    refine hF.mono ?_ (Eventually.of_forall fun p => ?_)
    · exact ((Continuous.measurable (by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos (L * p.1))
        ).aestronglyMeasurable).mul hFm
    · simp only [hGd, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
  -- the `t`-integrals
  have htint : ∀ r, ∫ t, G (r, t) ∂ν = Real.cos (L * r) * (hsq g a r * (psiRe r - psiRe 0)) := by
    intro r
    simp only [hGd]
    rw [integral_const_mul, (hFr r).2]
  -- the `r`-integrals
  have hLD : D < L := by linarith
  have hrint : ∀ t, 0 < t → ∫ r, G (r, t) = -(π * (kkQ (1 / 4) t * f (L - t / 2))) := by
    intro t ht
    have e : (fun r => G (r, t)) = fun r => kkQ (1 / 4) t * (hsq g a r * Real.cos (r * L)
        - 1 / 2 * (hsq g a r * Real.cos (r * (L + t / 2)))
        - 1 / 2 * (hsq g a r * Real.cos (r * (L - t / 2)))) := by
      funext r
      simp only [hGd, hFd]
      rw [show r * (L + t / 2) = L * r + r * (t / 2) by ring, show r * (L - t / 2) = L * r - r * (t / 2) by ring,
        show r * L = L * r by ring, Real.cos_add, Real.cos_sub]
      ring
    have i0 := integrable_hsq_cos hE ha0 L
    have i1 : Integrable fun r => 1 / 2 * (hsq g a r * Real.cos (r * (L + t / 2))) :=
      (integrable_hsq_cos hE ha0 (L + t / 2)).const_mul _
    have i2 : Integrable fun r => 1 / 2 * (hsq g a r * Real.cos (r * (L - t / 2))) :=
      (integrable_hsq_cos hE ha0 (L - t / 2)).const_mul _
    have i01 : Integrable fun r => hsq g a r * Real.cos (r * L)
        - 1 / 2 * (hsq g a r * Real.cos (r * (L + t / 2))) := i0.sub i1
    rw [e, integral_const_mul, integral_sub i01 i2,
      integral_sub i0 i1, integral_const_mul, integral_const_mul,
      integral_hsq_cos hE ha0, integral_hsq_cos hE ha0, integral_hsq_cos hE ha0, hfa, hfa, hfa,
      hfE.supp L (by rw [abs_of_pos (by linarith)]; exact hLD),
      hfE.supp (L + t / 2) (by rw [abs_of_pos (by linarith)]; linarith)]
    ring
  -- assemble
  have hsplit : ∫ r, hmodR b J L r * psiRe r
      = 2 * (∫ r, ∫ t, G (r, t) ∂ν) + 2 * psiRe 0 * (2 * π * f L) := by
    have e1 : (fun r => hmodR b J L r * psiRe r) = fun r =>
        2 * (Real.cos (L * r) * (hsq g a r * (psiRe r - psiRe 0)))
          + 2 * psiRe 0 * (hsq g a r * Real.cos (r * L)) := by
      funext r; unfold hmodR; rw [show r * L = L * r by ring]; ring
    have i1 : Integrable fun r => Real.cos (L * r) * (hsq g a r * (psiRe r - psiRe 0)) := by
      have := hG.integral_prod_left
      simp only [htint] at this
      exact this
    rw [e1, integral_add (i1.const_mul 2) ((integrable_hsq_cos hE ha0 L).const_mul _),
      integral_const_mul, integral_const_mul, integral_hsq_cos hE ha0, hfa]
    simp only [htint]
  have hswap : ∫ r, ∫ t, G (r, t) ∂ν = ∫ t, (∫ r, G (r, t)) ∂ν :=
    integral_integral_swap (f := fun r t => G (r, t)) hG
  have hfL : f L = 0 := hfE.supp L (by rw [abs_of_pos (by linarith)]; exact hLD)
  have hint2 : ∫ t, (∫ r, G (r, t)) ∂ν = -(π * ∫ t, kkQ (1 / 4) t * f (L - t / 2) ∂ν) := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
    exact hrint t ht
  have hval : 1 / (2 * π) * ∫ r, hmodR b J L r * psiRe r = -∫ t, kkQ (1 / 4) t * f (L - t / 2) ∂ν := by
    rw [hsplit, hswap, hint2, hfL]
    field_simp
    ring
  -- the bound
  set c0 := 2 * (2 * b) ^ (2 ^ (J + 1) - 1) * Real.exp (-((L - D) / 2)) with hc0
  set s := Icc (2 * (L - D)) (2 * (L + D)) with hs
  have hpt : ∀ᵐ t ∂ν, ‖kkQ (1 / 4) t * f (L - t / 2)‖ ≤ s.indicator (fun _ => c0) t := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    by_cases hin : t ∈ s
    · rw [indicator_of_mem hin]
      have ht1 : 1 ≤ t := by have := hin.1; linarith
      have hk := kkQ_quarter_le ht1
      have hke : Real.exp (-(t / 4)) ≤ Real.exp (-((L - D) / 2)) :=
        Real.exp_le_exp.2 (by have := hin.1; linarith)
      have hf0 := gI_nonneg b (J + 1) (L - t / 2)
      have hf1 := gI_le hb (J + 1) (L - t / 2)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kkQ_nonneg _ ht0), abs_of_nonneg hf0]
      calc kkQ (1 / 4) t * f (L - t / 2) ≤ (2 * Real.exp (-((L - D) / 2))) * (2 * b) ^ (2 ^ (J + 1) - 1) :=
            mul_le_mul (hk.trans (by linarith)) hf1 hf0 (by positivity)
        _ = c0 := by rw [hc0]; ring
    · rw [indicator_of_notMem hin]
      have hout : D < |L - t / 2| := by
        rw [hs, mem_Icc, not_and_or, not_le, not_le] at hin
        rcases hin with h | h
        · rw [abs_of_pos (by linarith)]; linarith
        · rw [abs_of_neg (by linarith)]; linarith
      rw [hfE.supp _ hout, mul_zero, norm_zero]
  have hsm : MeasurableSet s := measurableSet_Icc
  have hνs : ν s = ENNReal.ofReal (4 * D) := by
    rw [hν, Measure.restrict_apply hsm, show s ∩ Ioi 0 = s by
      ext t; simp only [hs, mem_inter_iff, mem_Icc, mem_Ioi]
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, by linarith [h.1]⟩, hs, Real.volume_Icc]
    congr 1; ring
  have hint : Integrable (s.indicator fun _ => c0) ν := by
    rw [integrable_indicator_iff hsm]
    have hfin : ν s ≠ ⊤ := by rw [hνs]; exact ENNReal.ofReal_ne_top
    exact integrableOn_const hfin
  have hle := norm_integral_le_of_norm_le hint hpt
  rw [integral_indicator_const _ hsm, measureReal_def, hνs, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul] at hle
  rw [hval, abs_neg, ← Real.norm_eq_abs]
  calc ‖∫ t, kkQ (1 / 4) t * f (L - t / 2) ∂ν‖ ≤ 4 * D * c0 := hle
    _ = 8 * D * (2 * b) ^ (2 ^ (J + 1) - 1) * Real.exp (-((L - D) / 2)) := by rw [hc0]; ring

/-! ## The explicit formula with the zero sum kept -/

/-- `‖h(τ)‖ ≤ 2e^{L/2}(4be^{b/2})^k w(τ)` at `x = e^L`, for every zero ordinate `τ` of `Ξ`. -/
theorem norm_hmod_tau_le {b : ℝ} (hb : 0 < b) (J : ℕ) {L : ℝ} (hL : 0 ≤ L) (i : ZeroIdx (sqF Xi)) :
    ‖hmod b J L (tau i)‖ ≤ 2 * Real.exp (L / 2) * (4 * b * Real.exp (b / 2)) ^ (2 ^ (J + 1))
      * wT (Real.exp L) b (2 ^ (J + 1)) (tau i) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 (tau_im i)
  set ρ : ℂ := 1 / 2 + I * tau i with hρ
  have hre : ρ.re = 1 / 2 - (tau i).im := by simp [hρ]; ring
  have hρim : ρ.im = (tau i).re := by simp [hρ]
  have h0 : 0 < ρ.re := by rw [hre]; linarith
  have h1' : ρ.re < 1 := by rw [hre]; linarith
  have key := norm_hmod_zero_le hb J (Real.one_le_exp hL) h0 h1'
  have ht : (ρ - 1 / 2) / I = tau i := by rw [hρ]; field_simp; ring
  rw [Real.log_exp, ht] at key
  have hsq : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; congr 1; ring
  have hW : Wz (Real.exp L) b (2 ^ (J + 1)) ρ = wT (Real.exp L) b (2 ^ (J + 1)) (tau i) := by
    unfold Wz wT
    rw [hre, hρim, show 1 / 2 - (tau i).im - 1 / 2 = -(tau i).im by ring, abs_neg]
  rw [hsq, hW] at key
  exact key

theorem two_le_two_pow_succ (J : ℕ) : 2 ≤ 2 ^ (J + 1) := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem summable_hmod_tau {b : ℝ} (hb : 0 < b) (J : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Summable fun i : ZeroIdx (sqF Xi) => hmod b J L (tau i) :=
  Summable.of_norm_bounded ((summable_wT (Real.one_le_exp hL) hb (two_le_two_pow_succ J)).mul_left
    (2 * Real.exp (L / 2) * (4 * b * Real.exp (b / 2)) ^ (2 ^ (J + 1)))) (norm_hmod_tau_le hb J hL)

/-- **The explicit formula at one point, with the zero sum kept**: for `L > 2^{J+1}b`,
`2Σ Λ(n)n^{−½}g_{J+1}(log n − L) = 4cosh(L/2)·P_b^k + E(L) − Re(2Σ_τ h(τ))`, where `P_b = poleR (bx b) b`,
`E(L)` is the archimedean term and `τ` runs over the zeros of `Ξ` with multiplicity. -/
theorem explicit_identity {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (J : ℕ) {L : ℝ} (hL : 2 ^ (J + 1) * b < L) :
    2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gI b (J + 1) (Real.log n - L)
      = 4 * Real.cosh (L / 2) * poleR (bx b) b ^ (2 ^ (J + 1))
        + 1 / (2 * π) * (∫ r, hmodR b J L r * psiRe r)
        - (2 * ∑' i : ZeroIdx (sqF Xi), hmod b J L (tau i)).re := by
  have hD0 : (0 : ℝ) < 2 ^ (J + 1) * b := by positivity
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨-, hS⟩ := weil_hmod hb hb1 J hL0
  have hE1 := gI_esupp hb (J + 1)
  have eP : ∀ n : ℕ, gh (hmodR b J L) (Real.log n) = gI b (J + 1) (Real.log n - L) := by
    intro n
    have hn := Real.log_natCast_nonneg n
    rw [gh_hmodR hb J L, hE1.supp (Real.log n + L) (by rw [abs_of_nonneg (by linarith)]; linarith),
      add_zero]
  have e0 : gh (hmodR b J L) 0 = 0 := by
    rw [gh_hmodR hb J L, hE1.supp (0 - L) (by rw [zero_sub, abs_neg, abs_of_nonneg hL0]; exact hL),
      hE1.supp (0 + L) (by rw [zero_add, abs_of_nonneg hL0]; exact hL), add_zero]
  simp_rw [eP, e0] at hS
  rw [hmod_even hb J L, hmod_I_half hb J L] at hS
  set Si := ∑' i : ZeroIdx (sqF Xi), hmod b J L (tau i) with hSi
  have hs : HasSum (fun i : ZeroIdx (sqF Xi) => hmod b J L (tau i)) Si := (summable_hmod_tau hb J hL0).hasSum
  have h2 : HasSum (fun p : Bool × ZeroIdx (sqF Xi) => hmod b J L ((rhoXi p - 1 / 2) / I)) (Si + Si) := by
    have hsum : HasSum (fun s : ZeroIdx (sqF Xi) ⊕ ZeroIdx (sqF Xi) =>
        Sum.elim (fun i => hmod b J L (tau i)) (fun i => hmod b J L (tau i)) s) (Si + Si) :=
      HasSum.sum hs hs
    have := (Equiv.boolProdEquivSum (ZeroIdx (sqF Xi))).hasSum_iff.2 hsum
    convert this using 2 with p
    rw [ordinate_rhoXi]
    rcases p with ⟨_ | _, i⟩ <;> simp [Equiv.boolProdEquivSum, hmod_even hb J L]
  have h3 := zetaEquiv.hasSum_iff.2 h2
  have h4 : HasSum (fun q => hmod b J L ((zetaZeroFamily q - 1 / 2) / I)) (Si + Si) := by
    convert h3 using 2 with q
    simp [rhoXi_zetaEquiv]
  have heq := hS.unique h4
  have hre := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  have h2re : (2 * Si).re = Si.re + Si.re := by simp [Complex.mul_re]; ring
  rw [h2re]
  linarith

/-! ## A prime from the weighted sum, with the prime powers counted locally -/

/-- `(x − y)·m·y^{m−1} ≤ x^m − y^m` for `0 ≤ y ≤ x`. -/
theorem pow_sub_pow_ge {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (m : ℕ) :
    (x - y) * (m * y ^ (m - 1)) ≤ x ^ m - y ^ m := by
  rw [← geom_sum₂_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  calc (m : ℝ) * y ^ (m - 1) = ∑ i ∈ Finset.range m, y ^ (m - 1) := by simp
    _ ≤ ∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.1 hi
      calc y ^ (m - 1) = y ^ i * y ^ (m - 1 - i) := by rw [← pow_add]; congr 1; omega
        _ ≤ x ^ i * y ^ (m - 1 - i) := by gcongr

/-- **At most `(c − a)/(2√a) + 1` integers `d` have `a ≤ d^m ≤ c`**, for `m ≥ 2` and `1 ≤ a ≤ c`. -/
theorem card_pow_mem_le {a c : ℝ} (ha : 1 ≤ a) (hac : a ≤ c) {m : ℕ} (hm : 2 ≤ m) (s : Finset ℕ)
    (hs : ∀ d ∈ s, a ≤ (d : ℝ) ^ m ∧ (d : ℝ) ^ m ≤ c) :
    (s.card : ℝ) ≤ (c - a) / (2 * Real.sqrt a) + 1 := by
  have hsa : 0 < 2 * Real.sqrt a := by positivity
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ (c - a) / (2 * Real.sqrt a) := div_nonneg (by linarith) hsa.le
    linarith
  set d0 := s.min' hne
  set d1 := s.max' hne
  have h01 : d0 ≤ d1 := s.min'_le d1 (s.max'_mem hne)
  have hsub : s ⊆ Finset.Icc d0 d1 := fun d hd => Finset.mem_Icc.2 ⟨s.min'_le d hd, s.le_max' d hd⟩
  have hcard : (s.card : ℝ) ≤ (d1 : ℝ) - d0 + 1 := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    have h' : (s.card : ℝ) ≤ ((d1 + 1 - d0 : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at h'
    linarith
  obtain ⟨ha0, -⟩ := hs d0 (s.min'_mem hne)
  obtain ⟨-, hc1⟩ := hs d1 (s.max'_mem hne)
  have hd0 : (1 : ℝ) ≤ d0 := by
    by_contra h
    push Not at h
    have : d0 = 0 := by
      have : (d0 : ℝ) < 1 := h
      exact_mod_cast (show (d0 : ℝ) = 0 by
        have h0 : d0 < 1 := by exact_mod_cast this
        have : d0 = 0 := by omega
        simp [this])
    rw [this, Nat.cast_zero, zero_pow (by omega)] at ha0
    linarith
  have h01' : (d0 : ℝ) ≤ d1 := by exact_mod_cast h01
  have hge := pow_sub_pow_ge (by linarith : (0 : ℝ) ≤ d0) h01' m
  have hroot : 2 * Real.sqrt a ≤ m * (d0 : ℝ) ^ (m - 1) := by
    have h1 : Real.sqrt a ≤ (d0 : ℝ) ^ (m - 1) := by
      rw [Real.sqrt_le_left]
      · calc a ≤ (d0 : ℝ) ^ m := ha0
          _ ≤ ((d0 : ℝ) ^ (m - 1)) ^ 2 := by
            rw [← pow_mul]; exact pow_le_pow_right₀ hd0 (by omega)
      · positivity
    have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have h3 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    nlinarith
  have hdiff : (0 : ℝ) ≤ (d1 : ℝ) - d0 := by linarith
  have key : ((d1 : ℝ) - d0) * (2 * Real.sqrt a) ≤ c - a :=
    calc ((d1 : ℝ) - d0) * (2 * Real.sqrt a) ≤ ((d1 : ℝ) - d0) * (m * (d0 : ℝ) ^ (m - 1)) :=
          mul_le_mul_of_nonneg_left hroot hdiff
      _ ≤ (d1 : ℝ) ^ m - (d0 : ℝ) ^ m := hge
      _ ≤ c - a := by linarith
  have : (d1 : ℝ) - d0 ≤ (c - a) / (2 * Real.sqrt a) := by rw [le_div_iff₀ hsa]; linarith
  linarith

/-- **Prime powers in a window**: `Σ_{a ≤ n ≤ c, n not prime} Λ(n) ≤ log c · log₂ c · ((c − a)/(2√a) + 1)`. -/
theorem sum_vonMangoldt_nonprime_le {a c : ℕ} (ha : 1 ≤ a) (hac : a ≤ c) :
    ∑ n ∈ (Finset.Icc a c).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n
      ≤ Real.log c * (Nat.log 2 c : ℝ) * (((c : ℝ) - a) / (2 * Real.sqrt a) + 1) := by
  set A := (Finset.Icc a c).filter (fun n => ¬ n.Prime ∧ IsPrimePow n) with hA
  set K := Nat.log 2 c with hK
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hac' : (a : ℝ) ≤ c := by exact_mod_cast hac
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
  -- only prime powers carry mass
  have e1 : ∑ n ∈ (Finset.Icc a c).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n
      = ∑ n ∈ A, ArithmeticFunction.vonMangoldt n := by
    rw [hA, ← Finset.filter_filter,
      ← Finset.sum_filter_add_sum_filter_not ((Finset.Icc a c).filter fun n => ¬ n.Prime) (fun n => IsPrimePow n)]
    have h0 : ∑ n ∈ ((Finset.Icc a c).filter fun n => ¬ n.Prime).filter (fun n => ¬ IsPrimePow n),
        ArithmeticFunction.vonMangoldt n = 0 :=
      Finset.sum_eq_zero fun n hn => by
        rw [ArithmeticFunction.vonMangoldt_apply]; simp [(Finset.mem_filter.1 hn).2]
    rw [h0, add_zero]
  -- each carries at most `log c`
  have e2 : ∑ n ∈ A, ArithmeticFunction.vonMangoldt n ≤ A.card * Real.log c := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' := (Finset.mem_filter.1 hn).1
    have hnc : (n : ℝ) ≤ c := by exact_mod_cast (Finset.mem_Icc.1 hn').2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans ha (Finset.mem_Icc.1 hn').1
    exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by linarith) hnc)
  -- the count, by exponent
  set B : ℕ → Finset ℕ := fun m => (Finset.Icc 1 c).filter (fun d => a ≤ d ^ m ∧ d ^ m ≤ c) with hB
  have hsub : A ⊆ (Finset.Icc 2 K).biUnion fun m => (B m).image fun d => d ^ m := by
    intro n hn
    obtain ⟨hn', hnp, hpp⟩ := Finset.mem_filter.1 hn
    obtain ⟨hna, hnc⟩ := Finset.mem_Icc.1 hn'
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this; exact hnp (by simpa using hp)
    have hp2 : 2 ≤ p := hp.two_le
    have hkK : k ≤ K := by
      rw [hK]
      apply Nat.le_log_of_pow_le (by norm_num)
      calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp2 k
        _ ≤ c := hnc
    refine Finset.mem_biUnion.2 ⟨k, Finset.mem_Icc.2 ⟨hk2, hkK⟩, Finset.mem_image.2 ⟨p, ?_, rfl⟩⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, ?_⟩, hna, hnc⟩
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ c := hnc
  have hcount : (A.card : ℝ) ≤ K * (((c : ℝ) - a) / (2 * Real.sqrt a) + 1) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := Finset.Icc 2 K) (t := fun m => (B m).image fun d => d ^ m)
    have h3 : ∀ m ∈ Finset.Icc 2 K, (((B m).image fun d => d ^ m).card : ℝ)
        ≤ ((c : ℝ) - a) / (2 * Real.sqrt a) + 1 := by
      intro m hm
      have hm2 := (Finset.mem_Icc.1 hm).1
      refine le_trans (Nat.cast_le.2 Finset.card_image_le) ?_
      refine card_pow_mem_le ha1 hac' hm2 (B m) fun d hd => ?_
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hd
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    have h4 : ((∑ m ∈ Finset.Icc 2 K, ((B m).image fun d => d ^ m).card : ℕ) : ℝ)
        ≤ ∑ m ∈ Finset.Icc 2 K, (((c : ℝ) - a) / (2 * Real.sqrt a) + 1) := by
      push_cast; exact Finset.sum_le_sum h3
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h4
    have h5 : ((K + 1 - 2 : ℕ) : ℝ) ≤ K := by
      rcases Nat.lt_or_ge K 1 with h | h
      · rw [show K + 1 - 2 = 0 by omega]; simp
      · rw [Nat.cast_sub (by omega)]; push_cast; linarith
    have h6 : (0 : ℝ) ≤ ((c : ℝ) - a) / (2 * Real.sqrt a) + 1 := by
      have : 0 ≤ ((c : ℝ) - a) / (2 * Real.sqrt a) := div_nonneg (by linarith) (by positivity)
      linarith
    calc (A.card : ℝ) ≤ ((∑ m ∈ Finset.Icc 2 K, ((B m).image fun d => d ^ m).card : ℕ) : ℝ) := by
          exact_mod_cast h1.trans h2
      _ ≤ ((K + 1 - 2 : ℕ) : ℝ) * (((c : ℝ) - a) / (2 * Real.sqrt a) + 1) := h4
      _ ≤ K * (((c : ℝ) - a) / (2 * Real.sqrt a) + 1) := mul_le_mul_of_nonneg_right h5 h6
  rw [e1]
  calc ∑ n ∈ A, ArithmeticFunction.vonMangoldt n ≤ A.card * Real.log c := e2
    _ ≤ K * (((c : ℝ) - a) / (2 * Real.sqrt a) + 1) * Real.log c := mul_le_mul_of_nonneg_right hcount hlogc
    _ = _ := by ring

/-- **A prime from the weighted sum.** With `k = 2^{J+1}`, `D = kb ≤ 1`: if `√x(2be^{−b/2})^k ≤ 2P` for
`P = Σ Λ(n)n^{−½}g_{J+1}(log n − log x)`, and `2log(3x)²(8D√x + 1) < bxe^{−(k+1)/2}`, then `[xe^{−D}, xe^D]` holds a
prime. The proof of `ShortWeil.prime_of_bounds`, with `sum_vonMangoldt_nonprime_le` for the prime powers. -/
theorem prime_of_P {b x : ℝ} {J : ℕ} (hb : 0 < b) (hD : 2 ^ (J + 1) * b ≤ 1) (hx : 3 ≤ x)
    (hP : Real.sqrt x * (2 * b * Real.exp (-(b / 2))) ^ (2 ^ (J + 1))
      ≤ 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gI b (J + 1) (Real.log n - Real.log x))
    (hW : 2 * Real.log (3 * x) ^ 2 * (8 * (2 ^ (J + 1) * b) * Real.sqrt x + 1)
      < b * x * Real.exp (-((2 ^ (J + 1) + 1) / 2))) :
    ∃ p : ℕ, p.Prime ∧ x * Real.exp (-(2 ^ (J + 1) * b)) ≤ p ∧ (p : ℝ) ≤ x * Real.exp (2 ^ (J + 1) * b) := by
  set k := 2 ^ (J + 1) with hk
  set D := (2 : ℝ) ^ (J + 1) * b with hDdef
  have hkR : (k : ℝ) = (2 : ℝ) ^ (J + 1) := by rw [hk]; push_cast; ring
  have hk2 : 2 ≤ k := two_le_two_pow_succ J
  have hx0 : 0 < x := by linarith
  have hb1 : b ≤ 1 := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (J + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hD0 : 0 ≤ D := by positivity
  set P := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gI b (J + 1) (Real.log n - Real.log x)
    with hPdef
  set m := (2 * b * Real.exp (-(b / 2))) ^ k with hm
  have hmlow : (2 * b * Real.exp (-(1 / 2))) ^ k ≤ m := by
    rw [hm]; apply pow_le_pow_left₀ (by positivity)
    have := Real.exp_le_exp.2 (show -(1 / 2 : ℝ) ≤ -(b / 2) by linarith)
    nlinarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  -- the window
  have hwin := weighted_le_window hb J hx0
  set lo := x * Real.exp (-D) with hlo
  set hi := x * Real.exp D with hhi
  set W := ∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊, ArithmeticFunction.vonMangoldt n with hWdef
  have hlo0 : 0 < lo := by positivity
  have hslo : 0 < Real.sqrt lo := Real.sqrt_pos.2 hlo0
  have hb2 : 0 < (2 * b) ^ (k - 1) := by positivity
  have hWlow : b * x * Real.exp (-((k + 1) / 2)) ≤ W := by
    have h1 : Real.sqrt x * m / 2 ≤ (2 * b) ^ (k - 1) / Real.sqrt lo * W := by
      rw [← hk] at hwin; linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hslo] at h1
    have hmk : (2 * b) ^ k * Real.exp (-(k / 2)) ≤ m := by
      calc (2 * b) ^ k * Real.exp (-(k / 2)) = (2 * b) ^ k * Real.exp (-(1 / 2)) ^ k := by
            rw [← Real.exp_nat_mul]; congr 2; ring
        _ = (2 * b * Real.exp (-(1 / 2))) ^ k := (mul_pow _ _ _).symm
        _ ≤ m := hmlow
    have hsq : Real.sqrt x * Real.sqrt lo = x * Real.exp (-(D / 2)) := by
      rw [hlo, ← Real.sqrt_mul hx0.le, show x * (x * Real.exp (-D)) = (x * Real.exp (-(D / 2))) ^ 2 by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf,
        Real.sqrt_sq (by positivity)]
    have hk1 : (2 * b) ^ k = (2 * b) ^ (k - 1) * (2 * b) := by
      rw [← pow_succ]; congr 1; omega
    have hexp : Real.exp (-((k + 1) / 2)) ≤ Real.exp (-(k / 2)) * Real.exp (-(D / 2)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have key : (2 * b) ^ (k - 1) * (b * x * Real.exp (-((k + 1) / 2)))
        ≤ (2 * b) ^ (k - 1) * W := by
      have : (2 * b) ^ (k - 1) * (b * x * Real.exp (-((k + 1) / 2)))
          ≤ Real.sqrt x * m / 2 * Real.sqrt lo := by
        calc (2 * b) ^ (k - 1) * (b * x * Real.exp (-((k + 1) / 2)))
            ≤ (2 * b) ^ (k - 1) * (b * x * (Real.exp (-(k / 2)) * Real.exp (-(D / 2)))) := by gcongr
          _ = (2 * b) ^ k * Real.exp (-(k / 2)) * (x * Real.exp (-(D / 2))) / 2 := by rw [hk1]; ring
          _ ≤ m * (x * Real.exp (-(D / 2))) / 2 := by gcongr
          _ = Real.sqrt x * m / 2 * Real.sqrt lo := by rw [← hsq]; ring
      linarith
    exact le_of_mul_le_mul_left key hb2
  -- the prime powers in the window
  have hexpD : Real.exp D ≤ 3 := (Real.exp_le_exp.2 hD).trans (by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith)
  have hhi3 : hi ≤ 3 * x := by rw [hhi]; nlinarith
  have hlo3 : x / 3 ≤ lo := by
    rw [hlo]
    have h1 : Real.exp D * Real.exp (-D) = 1 := by rw [← Real.exp_add]; simp
    have h2 : 0 < Real.exp (-D) := Real.exp_pos _
    nlinarith
  set a := ⌈lo⌉₊ with ha
  set c := ⌊hi⌋₊ with hc
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (by rw [ha, Ne, Nat.ceil_eq_zero, not_le]; exact hlo0)
  have hW' : 2 * Real.log (3 * x) ^ 2 * (8 * D * Real.sqrt x + 1) < b * x * Real.exp (-((k + 1) / 2)) := by
    rw [hkR]; exact hW
  have hWpos : 0 < W := lt_of_lt_of_le (by
    have : 0 ≤ 2 * Real.log (3 * x) ^ 2 * (8 * D * Real.sqrt x + 1) := by positivity
    linarith) hWlow
  have hac : a ≤ c := by
    by_contra h
    push Not at h
    have : Finset.Icc a c = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hWdef, this, Finset.sum_empty] at hWpos
    exact lt_irrefl _ hWpos
  have hcx : (c : ℝ) ≤ 3 * x := (Nat.floor_le (by positivity)).trans hhi3
  have hax : lo ≤ a := Nat.le_ceil lo
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast le_trans ha1 hac
  have hlogc : Real.log c ≤ Real.log (3 * x) := Real.log_le_log (by linarith) hcx
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hnatlog : (Nat.log 2 c : ℝ) ≤ 2 * Real.log (3 * x) := by
    have h1 := Real.natLog_le_logb c 2
    rw [Real.logb] at h1
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have h3 : Real.log c / Real.log 2 ≤ 2 * Real.log c := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    push_cast at h1
    linarith
  have hca : ((c : ℝ) - a) / (2 * Real.sqrt a) ≤ 8 * D * Real.sqrt x := by
    have hca' : (c : ℝ) - a ≤ hi - lo := by
      have := Nat.floor_le (show 0 ≤ hi by positivity)
      linarith
    have hhl : hi - lo ≤ 4 * D * x := by
      have h1 : |Real.exp D - 1| ≤ 2 * |D| := Real.abs_exp_sub_one_le (by rw [abs_of_nonneg hD0]; exact hD)
      have h2 : |Real.exp (-D) - 1| ≤ 2 * |(-D)| := Real.abs_exp_sub_one_le (by
        rw [abs_neg, abs_of_nonneg hD0]; exact hD)
      rw [abs_of_nonneg hD0] at h1
      rw [abs_neg, abs_of_nonneg hD0] at h2
      have h3 := (abs_le.1 h1).2
      have h4 := (abs_le.1 h2).1
      have h5 : Real.exp D - Real.exp (-D) ≤ 4 * D := by linarith
      calc hi - lo = x * (Real.exp D - Real.exp (-D)) := by rw [hhi, hlo]; ring
        _ ≤ x * (4 * D) := mul_le_mul_of_nonneg_left h5 hx0.le
        _ = 4 * D * x := by ring
    have hsa : Real.sqrt (x / 3) ≤ Real.sqrt a := Real.sqrt_le_sqrt (hlo3.trans hax)
    have hsx3 : Real.sqrt x ≤ 2 * Real.sqrt (x / 3) := by
      rw [show x = 3 * (x / 3) by ring, Real.sqrt_mul (by norm_num), show 3 * (x / 3) / 3 = x / 3 by ring]
      have : Real.sqrt 3 ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      have := Real.sqrt_nonneg (x / 3)
      nlinarith
    have hsxa : Real.sqrt x ≤ 2 * Real.sqrt a := hsx3.trans (by linarith)
    have hpos : 0 < 2 * Real.sqrt a := by
      have : 0 < Real.sqrt (x / 3) := Real.sqrt_pos.2 (by positivity)
      linarith
    rw [div_le_iff₀ hpos]
    have hxs : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
    calc (c : ℝ) - a ≤ 4 * D * x := hca'.trans hhl
      _ = 4 * D * Real.sqrt x * Real.sqrt x := by rw [mul_assoc (4 * D) (Real.sqrt x) (Real.sqrt x), ← hxs]
      _ ≤ 4 * D * Real.sqrt x * (2 * Real.sqrt a) := by gcongr
      _ = 8 * D * Real.sqrt x * (2 * Real.sqrt a) / 2 := by ring
      _ ≤ 8 * D * Real.sqrt x * (2 * Real.sqrt a) := by
          have : 0 ≤ 8 * D * Real.sqrt x * (2 * Real.sqrt a) := by positivity
          linarith
  have hnp := sum_vonMangoldt_nonprime_le ha1 hac
  have hnp' : ∑ n ∈ (Finset.Icc a c).filter (fun n => ¬ n.Prime), ArithmeticFunction.vonMangoldt n
      < W := by
    refine lt_of_le_of_lt hnp (lt_of_le_of_lt ?_ (lt_of_lt_of_le hW' hWlow))
    have h1 : 0 ≤ ((c : ℝ) - a) / (2 * Real.sqrt a) + 1 := by
      have : 0 ≤ ((c : ℝ) - a) / (2 * Real.sqrt a) :=
        div_nonneg (by have : (a : ℝ) ≤ c := by exact_mod_cast hac
                       linarith) (by positivity)
      linarith
    have hl3 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
    calc Real.log c * (Nat.log 2 c : ℝ) * (((c : ℝ) - a) / (2 * Real.sqrt a) + 1)
        ≤ Real.log (3 * x) * (2 * Real.log (3 * x)) * (8 * D * Real.sqrt x + 1) := by
          gcongr
      _ = 2 * Real.log (3 * x) ^ 2 * (8 * D * Real.sqrt x + 1) := by ring
  -- a prime in `[a, c]`
  by_contra hno
  push Not at hno
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc a c) (fun n => n.Prime)
    (fun n => ArithmeticFunction.vonMangoldt n)
  have hzero : ∑ n ∈ (Finset.Icc a c).filter (fun n => n.Prime), ArithmeticFunction.vonMangoldt n = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    obtain ⟨hn', hp⟩ := Finset.mem_filter.1 hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn'
    exfalso
    have hlo' : x * Real.exp (-(2 ^ (J + 1) * b)) ≤ n := (Nat.ceil_le.1 h1)
    have hhi' : (n : ℝ) ≤ x * Real.exp (2 ^ (J + 1) * b) := (Nat.le_floor_iff (by positivity)).1 h2
    exact absurd hhi' (not_le.2 (hno n hp hlo'))
  rw [hzero, zero_add] at hsplit
  rw [← hWdef] at hsplit
  linarith

end AlmostAll

#print axioms AlmostAll.arch_far
#print axioms AlmostAll.explicit_identity
#print axioms AlmostAll.sum_vonMangoldt_nonprime_le
#print axioms AlmostAll.prime_of_P
