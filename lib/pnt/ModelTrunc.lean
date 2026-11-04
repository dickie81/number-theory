import ModelMoments
import MomentConv

/-!
# Model-side truncation (unconditional)

`ModelTrunc.moment_A_tendsto`: the moments of the truncated model `A_N = Σ_{n ≤ N} Λ(n) X(n)/n` tend to those of
`-X`. Regrouping by prime powers (`ModelTrunc.vm_regroup`) and a geometric tail per prime (`ModelTrunc.trunc_prime`)
give `|A_N + T_{N+1}| ≤ 2 log N (1 + log N)/√N` almost surely (`ModelTrunc.abs_A_add_T_le`); with the a.s.
convergence and the mgf of `RandModel`, a truncation argument (`ModelTrunc.tendsto_integral_of_sq_bdd`) passes the
moments to the limit.
-/

namespace ModelTrunc
open MeasureTheory ProbabilityTheory Filter Topology Finset ArithmeticFunction
open RandModel ModelMoments

/-- Regrouping `Σ_{n ≤ N} Λ(n) F(n)` by prime powers. -/
theorem vm_regroup (N : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Λ n * F n =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, ∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ N), Real.log p * F (p ^ j) := by
  rw [sum_sigma']
  symm
  refine sum_bij_ne_zero (fun x _ _ => x.1 ^ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, j⟩ hx -
    simp only [mem_sigma, mem_filter, mem_Icc] at hx ⊢
    exact ⟨Nat.one_le_pow _ _ hx.1.2.pos, hx.2.2⟩
  · rintro ⟨p, j⟩ hx - ⟨q, i⟩ hy - h
    simp only [mem_sigma, mem_filter, mem_Icc] at hx hy
    obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' hx.1.2 hy.1.2 (Nat.one_le_iff_ne_zero.1 hx.2.1.1) (Nat.one_le_iff_ne_zero.1 hy.2.1.1) h
    rfl
  · intro n hn hne
    have hpp : IsPrimePow n := vonMangoldt_ne_zero_iff.1 (left_ne_zero_of_mul hne)
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    simp only [mem_Icc] at hn
    have hpN : p ≤ N := (Nat.le_self_pow hk.ne' p).trans hn.2
    have hkN : k ≤ N := (Nat.lt_pow_self hp.one_lt).le.trans hn.2
    refine ⟨⟨p, k⟩, ?_, ?_, rfl⟩
    · simp only [mem_sigma, mem_filter, mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpN⟩, hp⟩, ⟨hk, hkN⟩, hn.2⟩
    · rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp] at hne
      exact hne
  · rintro ⟨p, j⟩ hx -
    simp only [mem_sigma, mem_filter, mem_Icc] at hx
    simp only
    rw [vonMangoldt_apply_pow (Nat.one_le_iff_ne_zero.1 hx.2.1.1), vonMangoldt_apply_prime hx.1.2]


theorem geom_Icc (q : ℝ) (hq : q ≠ 1) (J : ℕ) :
    ∑ j ∈ Icc 1 J, q ^ j = q / (1 - q) - q ^ (J + 1) / (1 - q) := by
  have h1 : (1 : ℝ) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    field_simp; ring

/-- The filter `{1 ≤ j ≤ N : p^j ≤ N}` is `[1, log_p N]`. -/
theorem filter_eq {p N : ℕ} (hp : 1 < p) :
    (Icc 1 N).filter (fun j => p ^ j ≤ N) = Icc 1 (Nat.log p N) := by
  ext j
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, Nat.le_log_of_pow_le hp h2⟩
  · rintro ⟨h1, h2⟩
    have hN : N ≠ 0 := by
      rintro rfl; simp at h2; try omega
    have hpow : p ^ j ≤ N := (Nat.pow_le_pow_right (by omega) h2).trans (Nat.pow_log_le_self p hN)
    exact ⟨⟨h1, (Nat.lt_pow_self hp).le.trans hpow⟩, hpow⟩

theorem geom_tail {q : ℝ} (hq : |q| ≤ 1 / 2) (J : ℕ) :
    |∑ j ∈ Icc 1 J, q ^ j - q / (1 - q)| ≤ 2 * |q| ^ (J + 1) := by
  have hq1 : q ≠ 1 := by intro h; rw [h] at hq; norm_num at hq
  have hpos : 1 / 2 ≤ 1 - q := by linarith [le_abs_self q]
  have h0 : (0 : ℝ) < 1 - q := by linarith
  rw [geom_Icc q hq1, sub_sub_cancel_left, abs_neg, abs_div, abs_pow, abs_of_pos h0,
    div_le_iff₀ h0]
  have := pow_nonneg (abs_nonneg q) (J + 1)
  nlinarith

/-- **Per-prime truncation.** For `w ∈ {-1, 0, 1}` and a prime `p ≤ N`,
`|Σ_{1 ≤ j, p^j ≤ N} w^j/p^j - w/(p - w)| ≤ 2/(√N p)`. -/
theorem trunc_prime {p N : ℕ} (hp : p.Prime) (hpN : p ≤ N) {w : ℝ} (hw : w = -1 ∨ w = 0 ∨ w = 1) :
    |∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ N), w ^ j / (p : ℝ) ^ j - w / (p - w)| ≤
      2 / (Real.sqrt N * p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hp.pos.trans_le hpN)
  have hpos : 0 < 2 / (Real.sqrt N * p) := by positivity
  rw [filter_eq hp.one_lt]
  set J := Nat.log p N
  have hJ1 : 1 ≤ J := Nat.le_log_of_pow_le hp.one_lt (by simpa using hpN)
  have hlt : (N : ℝ) < (p : ℝ) ^ (J + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self hp.one_lt N
  have hpp : (p : ℝ) * p ≤ (p : ℝ) ^ (J + 1) := by
    rw [pow_succ]; exact mul_le_mul_of_nonneg_right
      (by simpa using pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ p) hJ1) (by linarith)
  have hP0 : 0 < (p : ℝ) ^ (J + 1) := by positivity
  have hsq : Real.sqrt N * p ≤ (p : ℝ) ^ (J + 1) := by
    have : (Real.sqrt N * p) ^ 2 ≤ ((p : ℝ) ^ (J + 1)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hN0.le]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hP0.le two_ne_zero).1 this
  have hw' : |w| ≤ 1 := by rcases hw with rfl | rfl | rfl <;> norm_num
  have hq : |w / p| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < p), div_le_iff₀ (by linarith)]; linarith
  have e1 : ∀ j, w ^ j / (p : ℝ) ^ j = (w / p) ^ j := fun j => (div_pow _ _ _).symm
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have e2 : w / (p - w) = (w / p) / (1 - w / p) := by
    have : (p : ℝ) - w ≠ 0 := by have := le_abs_self w; intro h; linarith
    field_simp
  simp_rw [e1]; rw [e2]
  refine (geom_tail hq J).trans ?_
  have h3 : |w / p| ^ (J + 1) ≤ 1 / (p : ℝ) ^ (J + 1) := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < p), div_pow, one_div]
    exact div_le_div_of_nonneg_right (by simpa using pow_le_one₀ (abs_nonneg w) hw') hP0.le |>.trans
      (by rw [one_div])
  calc 2 * |w / p| ^ (J + 1) ≤ 2 * (1 / (p : ℝ) ^ (J + 1)) := by gcongr
    _ ≤ 2 / (Real.sqrt N * p) := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq


theorem ae_law_nonprime {n : ℕ} (hn : ¬ n.Prime) : ∀ᵐ y ∂(law n), y = 0 := by
  rw [ae_iff]
  simp [law, r, hn, Measure.dirac_apply]

theorem ae_good : ∀ᵐ ω ∂(RandModel.P), (∀ p, ω p = -1 ∨ ω p = 0 ∨ ω p = 1) ∧ ∀ n, ¬ n.Prime → ω n = 0 := by
  refine (ae_all_iff.2 ae_coord).and (ae_all_iff.2 fun n => ?_)
  by_cases hn : n.Prime
  · exact Eventually.of_forall fun _ h => absurd hn h
  · have := ae_law_nonprime hn
    rw [← map_eval] at this
    filter_upwards [ae_of_ae_map (measurable_pi_apply n).aemeasurable this] with ω h _ using h

theorem Xm_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) (ω : Ω) : Xm (p ^ j) ω = ω p ^ j := by
  rw [Xm, hp.factorization_pow]
  exact Finsupp.prod_single_index (h := fun p e => ω p ^ e) (pow_zero _)

/-- The truncated model `A_N = Σ_{n ≤ N} Λ(n) X(n)/n`. -/
noncomputable def A (N : ℕ) (ω : Ω) : ℝ := ∑ n ∈ Icc 1 N, Λ n * (Xm n ω / n)

theorem A_eq (N : ℕ) (ω : Ω) : A N ω = ∑ p ∈ (Icc 1 N).filter Nat.Prime,
    Real.log p * ∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ N), ω p ^ j / (p : ℝ) ^ j := by
  rw [A, vm_regroup]
  refine sum_congr rfl fun p hp => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Xm_prime_pow (mem_filter.1 hp).2]; push_cast; rfl

theorem T_eq (N : ℕ) {ω : Ω} (h0 : ∀ n, ¬ n.Prime → ω n = 0) :
    T (N + 1) ω = ∑ p ∈ (Icc 1 N).filter Nat.Prime, g p (ω p) := by
  rw [T]
  symm
  refine sum_subset (fun n hn => ?_) (fun n _ hn => ?_)
  · simp only [mem_filter, mem_Icc] at hn; rw [mem_range]; omega
  · have : ¬ n.Prime := fun hp => hn (by
      simp only [mem_filter, mem_Icc]
      exact ⟨⟨hp.one_le, by simp only [mem_range] at *; omega⟩, hp⟩)
    rw [h0 n this, g_zero]

/-- The truncation error bound `2 log N (1 + log N)/√N`. -/
noncomputable def ε (N : ℕ) : ℝ := 2 * Real.log N * (1 + Real.log N) / Real.sqrt N

/-- **Deterministic truncation.** On the full-measure set, `|A_N + T_{N+1}| ≤ ε N`. -/
theorem abs_A_add_T_le (N : ℕ) {ω : Ω} (hω : (∀ p, ω p = -1 ∨ ω p = 0 ∨ ω p = 1) ∧ ∀ n, ¬ n.Prime → ω n = 0) :
    |A N ω + T (N + 1) ω| ≤ ε N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [A, T, ε, g_small (show 0 < 2 by norm_num)]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  rw [A_eq, T_eq N hω.2, ← sum_add_distrib]
  have hterm : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      |Real.log p * ∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ N), ω p ^ j / (p : ℝ) ^ j + g p (ω p)| ≤
        2 * Real.log N / Real.sqrt N * (1 / (p : ℝ)) := by
    intro p hp
    simp only [mem_filter, mem_Icc] at hp
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_le)
    have hlp : Real.log p ≤ Real.log N := Real.log_le_log (by exact_mod_cast hp.2.pos) (by exact_mod_cast hp.1.2)
    have e : Real.log p * ∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ N), ω p ^ j / (p : ℝ) ^ j + g p (ω p) =
        Real.log p * (∑ j ∈ (Icc 1 N).filter (fun j => p ^ j ≤ N), ω p ^ j / (p : ℝ) ^ j - ω p / (p - ω p)) := by
      rw [g]; ring
    rw [e, abs_mul, abs_of_nonneg hl]
    have := trunc_prime hp.2 hp.1.2 (hω.1 p)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    calc Real.log p * |_| ≤ Real.log N * (2 / (Real.sqrt N * p)) :=
          mul_le_mul hlp this (abs_nonneg _) hlN
      _ = 2 * Real.log N / Real.sqrt N * (1 / (p : ℝ)) := by field_simp
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [← mul_sum]
  have hh : ∑ p ∈ (Icc 1 N).filter Nat.Prime, 1 / (p : ℝ) ≤ 1 + Real.log N := by
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity).trans ?_
    have := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at this; push_cast at this
    simpa [one_div] using this
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  calc 2 * Real.log N / Real.sqrt N * ∑ p ∈ (Icc 1 N).filter Nat.Prime, 1 / (p : ℝ)
      ≤ 2 * Real.log N / Real.sqrt N * (1 + Real.log N) := by gcongr
    _ = ε N := by rw [ε]; ring


/-! ### Moments along an a.s. convergent sequence with bounded second moments -/

theorem continuous_clamp (R : ℝ) : Continuous (MomentConv.clamp R) := by
  unfold MomentConv.clamp; fun_prop

theorem integrable_clamp {μ : Measure Ω} [IsProbabilityMeasure μ] {R : ℝ} (hR : 0 < R) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) : Integrable (fun ω => MomentConv.clamp R (f ω)) μ :=
  Integrable.of_bound ((continuous_clamp R).comp_aestronglyMeasurable hf) R
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact MomentConv.abs_clamp hR.le _)

theorem clamp_err_int {μ : Measure Ω} [IsProbabilityMeasure μ] {R : ℝ} (hR : 0 < R) {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    |∫ ω, f ω ∂μ - ∫ ω, MomentConv.clamp R (f ω) ∂μ| ≤ 2 * (∫ ω, f ω ^ 2 ∂μ) / R := by
  have hc := integrable_clamp hR hf.aestronglyMeasurable
  rw [← integral_sub hf hc]
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_const_mul, ← integral_div]
  refine integral_mono (hf.sub hc).abs ((hf2.const_mul 2).div_const R) fun ω => ?_
  have := MomentConv.pow_clamp_err hR 1 (f ω)
  simpa using this

/-- **Moments along an a.s. convergent sequence.** If `f n → g` a.s. and the second moments are eventually
bounded, then `∫ f n → ∫ g`. -/
theorem tendsto_integral_of_sq_bdd {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hf2 : ∀ n, Integrable (fun ω => f n ω ^ 2) μ)
    (hg : Integrable g μ) (hg2 : Integrable (fun ω => g ω ^ 2) μ) (K : ℝ)
    (hK : ∀ᶠ n in atTop, ∫ ω, f n ω ^ 2 ∂μ ≤ K) (hKg : ∫ ω, g ω ^ 2 ∂μ ≤ K)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by
  have hK0 : 0 ≤ K := (integral_nonneg fun ω => sq_nonneg (g ω)).trans hKg
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R := max 1 (8 * (K + 1) / ε)
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hsmall : 2 * K / R < ε / 4 := by
    have h8 : 8 * (K + 1) / ε ≤ R := le_max_right _ _
    rw [div_le_iff₀ hε] at h8
    rw [div_lt_iff₀ hR]; nlinarith
  have hdom : Tendsto (fun n => ∫ ω, MomentConv.clamp R (f n ω) ∂μ) atTop
      (𝓝 (∫ ω, MomentConv.clamp R (g ω) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => R)
      (fun n => (integrable_clamp hR (hf n).aestronglyMeasurable).aestronglyMeasurable)
      (integrable_const R) (fun n => Eventually.of_forall fun ω => ?_) ?_
    · rw [Real.norm_eq_abs]; exact MomentConv.abs_clamp hR.le _
    · filter_upwards [hlim] with ω hω
      exact ((continuous_clamp R).tendsto _).comp hω
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hdom (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hK
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have e1 := clamp_err_int hR (hf n) (hf2 n)
  have e2 := clamp_err_int hR hg hg2
  have b1 : 2 * (∫ ω, f n ω ^ 2 ∂μ) / R ≤ 2 * K / R := by
    gcongr; exact hN2 n (le_of_max_le_right hn)
  have b2 : 2 * (∫ ω, g ω ^ 2 ∂μ) / R ≤ 2 * K / R := by gcongr
  have e3 := hN1 n (le_of_max_le_left hn)
  rw [Real.dist_eq] at e3 ⊢
  have t1 := abs_sub_le (∫ ω, f n ω ∂μ) (∫ ω, MomentConv.clamp R (f n ω) ∂μ) (∫ ω, g ω ∂μ)
  have t2 := abs_sub_le (∫ ω, MomentConv.clamp R (f n ω) ∂μ) (∫ ω, MomentConv.clamp R (g ω) ∂μ)
    (∫ ω, g ω ∂μ)
  rw [abs_sub_comm (∫ ω, MomentConv.clamp R (g ω) ∂μ)] at t2
  linarith


/-! ### Applying it to the truncated model -/

theorem tendsto_ε : Tendsto ε atTop (𝓝 0) := by
  have hf : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hg : Tendsto (fun x : ℝ => x ^ (-(1 / 4 : ℝ)) + Real.log x / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1 / 4)).add hf
  have hprod := (hf.mul hg).const_mul 2
  rw [mul_zero, mul_zero] at hprod
  refine (hprod.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hx : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : (0 : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  have hs : Real.sqrt N = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx, Real.sqrt_eq_rpow]; norm_num
  have hn : (N : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_neg hx.le, one_div]; norm_num
  simp only [Function.comp, ε, hs, hn]
  field_simp

theorem exp_T_int_le (t : ℝ) (N : ℕ) :
    Integrable (fun ω => Real.exp (t * T (N + 1) ω)) (RandModel.P) ∧
      ∫ ω, Real.exp (t * T (N + 1) ω) ∂(RandModel.P) ≤
        Real.exp (|t| * M) * Real.exp (V * t ^ 2 / 2) := by
  have hi := ((subG_S N).integrable_exp_mul t).const_mul (Real.exp (|t| * M))
  have hm : AEStronglyMeasurable (fun ω => Real.exp (t * T (N + 1) ω)) (RandModel.P) :=
    (Real.measurable_exp.comp ((measurable_T _).const_mul t)).aestronglyMeasurable
  have hint : Integrable (fun ω => Real.exp (t * T (N + 1) ω)) (RandModel.P) :=
    hi.mono' hm (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact exp_T_le t N ω)
  refine ⟨hint, (integral_mono hint hi fun ω => exp_T_le t N ω).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (mgf_S_le N t) (Real.exp_pos _).le

theorem pow_le_fact_exp (n : ℕ) {y : ℝ} (hy : 0 ≤ y) : y ^ n ≤ n.factorial * Real.exp y := by
  have := Real.pow_div_factorial_le_exp _ hy n
  rwa [div_le_iff₀ (by positivity), mul_comm] at this

theorem exp_abs_le (x : ℝ) : Real.exp |x| ≤ Real.exp (1 * x) + Real.exp ((-1) * x) := by
  have h1 := Real.exp_pos x; have h2 := Real.exp_pos (-x)
  rcases abs_cases x with ⟨hx, -⟩ | ⟨hx, -⟩ <;> rw [hx] <;> simp <;> linarith

theorem measurable_A (N : ℕ) : Measurable (A N) :=
  Finset.measurable_sum _ fun n _ => ((measurable_Xm n).div_const _).const_mul _

/-- `A N` is a.s. bounded. -/
theorem ae_abs_A_le (N : ℕ) : ∀ᵐ ω ∂(RandModel.P), |A N ω| ≤ ∑ n ∈ Icc 1 N, Λ n / n := by
  have h : ∀ᵐ ω ∂(RandModel.P), ∀ n, |Xm n ω| ≤ 1 := ae_all_iff.2 ae_abs_Xm_le
  filter_upwards [h] with ω hω
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  have hn0 : (0 : ℝ) < n := by simp only [mem_Icc] at hn; exact_mod_cast hn.1
  rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg, abs_div, abs_of_pos hn0]
  calc Λ n * (|Xm n ω| / n) ≤ Λ n * (1 / n) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hω n) hn0.le) vonMangoldt_nonneg
    _ = Λ n / n := by ring

theorem integrable_A_pow (N k : ℕ) : Integrable (fun ω => A N ω ^ k) (RandModel.P) :=
  Integrable.of_bound ((measurable_A N).pow_const k).aestronglyMeasurable ((∑ n ∈ Icc 1 N, Λ n / n) ^ k)
    ((ae_abs_A_le N).mono fun ω h => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h k)


theorem abs_pow_le_exp (n : ℕ) (y : ℝ) :
    |y| ^ n ≤ n.factorial * (Real.exp (1 * y) + Real.exp ((-1) * y)) :=
  (pow_le_fact_exp n (abs_nonneg y)).trans (mul_le_mul_of_nonneg_left (exp_abs_le y) (by positivity))

theorem ae_tendsto_A : ∀ᵐ ω ∂(RandModel.P), Tendsto (fun N => A N ω) atTop (𝓝 (-X ω)) := by
  filter_upwards [ae_good, ae_tendsto_X] with ω hg hX
  have h1 : Tendsto (fun N => A N ω + T (N + 1) ω) atTop (𝓝 0) :=
    squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact abs_A_add_T_le N hg) tendsto_ε
  have h2 := hX.comp (tendsto_add_atTop_nat 1)
  simpa using h1.sub h2

/-- **Model-side `L^k` convergence.** The moments of `A_N = Σ_{n ≤ N} Λ(n) X(n)/n` tend to those of `-X`. -/
theorem moment_A_tendsto (k : ℕ) :
    Tendsto (fun N => ∫ ω, A N ω ^ k ∂(RandModel.P)) atTop (𝓝 (∫ ω, (-X ω) ^ k ∂(RandModel.P))) := by
  set Kt := Real.exp (|(1:ℝ)| * M) * Real.exp (V * 1 ^ 2 / 2)
  have hKt1 := exp_T_int_le 1
  have hKt2 := exp_T_int_le (-1)
  simp only [abs_neg, neg_one_sq] at hKt2
  have hXm : AEMeasurable (fun ω => -X ω) (RandModel.P) := aemeasurable_X.neg
  have hX1 : Integrable (fun ω => Real.exp (1 * -X ω)) (RandModel.P) := by
    simpa using integrable_exp_X (-1)
  have hX2 : Integrable (fun ω => Real.exp ((-1) * -X ω)) (RandModel.P) := by
    simpa using integrable_exp_X 1
  have hgi : ∀ n, Integrable (fun ω => (-X ω) ^ n) (RandModel.P) := fun n =>
    ((hX1.add hX2).const_mul (n.factorial : ℝ)).mono' (hXm.pow_const n).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_pow]; exact abs_pow_le_exp n _)
  set Kg := ((2 * k).factorial : ℝ) * (∫ ω, Real.exp (1 * -X ω) ∂(RandModel.P) +
    ∫ ω, Real.exp ((-1) * -X ω) ∂(RandModel.P))
  set KA := ((2 * k).factorial : ℝ) * Real.exp 1 * (Kt + Kt)
  have sq : ∀ y : ℝ, (y ^ k) ^ 2 = |y| ^ (2 * k) := fun y => by
    rw [← pow_mul, mul_comm, (even_two_mul k).pow_abs]
  refine tendsto_integral_of_sq_bdd (fun N => integrable_A_pow N k)
    (fun N => by simpa [← pow_mul, mul_comm] using integrable_A_pow N (k * 2)) (hgi k)
    (by simpa [← pow_mul, mul_comm] using hgi (k * 2)) (max KA Kg) ?_ ?_ ?_
  · filter_upwards [(tendsto_order.1 tendsto_ε).2 1 one_pos] with N hN
    refine le_trans ?_ (le_max_left _ _)
    have hb : ∀ᵐ ω ∂(RandModel.P), (A N ω ^ k) ^ 2 ≤
        ((2 * k).factorial : ℝ) * Real.exp 1 * (Real.exp (1 * T (N + 1) ω) + Real.exp ((-1) * T (N + 1) ω)) := by
      filter_upwards [ae_good] with ω hg
      have h1 := abs_A_add_T_le N hg
      have hA : |A N ω| ≤ |T (N + 1) ω| + 1 := by
        have := abs_sub_abs_le_abs_sub (A N ω) (-T (N + 1) ω)
        rw [sub_neg_eq_add, abs_neg] at this; linarith
      rw [sq]
      calc |A N ω| ^ (2 * k) ≤ (|T (N + 1) ω| + 1) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _) hA _
        _ ≤ ((2 * k).factorial : ℝ) * Real.exp (|T (N + 1) ω| + 1) := pow_le_fact_exp _ (by positivity)
        _ = ((2 * k).factorial : ℝ) * Real.exp 1 * Real.exp |T (N + 1) ω| := by rw [Real.exp_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (exp_abs_le _) (by positivity)
    refine (integral_mono_ae (by simpa [← pow_mul, mul_comm] using integrable_A_pow N (k * 2))
      ((hKt1 N).1.add (hKt2 N).1 |>.const_mul _) hb).trans ?_
    simp only [Pi.add_apply]
    rw [integral_const_mul, integral_add (hKt1 N).1 (hKt2 N).1]
    have := (hKt1 N).2; have := (hKt2 N).2
    exact mul_le_mul_of_nonneg_left (by simp only [Kt, abs_one] at *; linarith) (by positivity)
  · refine le_trans ?_ (le_max_right _ _)
    refine (integral_mono (by simpa [← pow_mul, mul_comm] using hgi (k * 2)) ((hX1.add hX2).const_mul ((2 * k).factorial : ℝ))
      fun ω => ?_).trans (le_of_eq ?_)
    · simp only; rw [sq]; exact abs_pow_le_exp _ _
    · simp only [Pi.add_apply]; rw [integral_const_mul, integral_add hX1 hX2]
  · filter_upwards [ae_tendsto_A] with ω h
    exact h.pow k

end ModelTrunc
