import Mathlib
import OddPositivity

/-! # Continuity of `weilQg (1/2)` under bounded pointwise convergence with a uniform interior Lipschitz bound

`Good B M g`: `g` measurable, zero off `[−1/2, 1/2]`, `|g| ≤ B`, and `M`-Lipschitz on `[−1/2, 1/2]`
(no continuity across `±1/2` is assumed: cut polynomials jump there). If `g k → f` pointwise with all `g k` and `f`
`Good B M`, every term of `weilQg (1/2)` converges (dominated convergence; the archimedean term is dominated by
`B(M+B)·u·e^{u/2}/sinh u ≤ 8B(M+B)e^{−u/4}`). -/

namespace WeilCont

open Real Filter Topology MeasureTheory Set WeilForm

structure Good (B M : ℝ) (g : ℝ → ℝ) : Prop where
  meas : Measurable g
  supp : ∀ u, 1 / 2 < |u| → g u = 0
  bd : ∀ u, |g u| ≤ B
  lip : ∀ s t, |s| ≤ 1 / 2 → |t| ≤ 1 / 2 → |g s - g t| ≤ M * |s - t|

lemma Good.B_nonneg {B M : ℝ} {g : ℝ → ℝ} (h : Good B M g) : 0 ≤ B := (abs_nonneg _).trans (h.bd 0)

/-- indicator bound on `[−1/2, 1/2]` -/
noncomputable def ind (C : ℝ) : ℝ → ℝ := (Icc (-(1/2):ℝ) (1/2)).indicator (fun _ => C)

lemma ind_int (C : ℝ) : Integrable (ind C) :=
  (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) (by simp))

lemma ind_eq {C t : ℝ} (ht : |t| ≤ 1 / 2) : ind C t = C := by
  unfold ind; rw [indicator_of_mem]; exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

lemma le_ind {φ : ℝ → ℝ} {C : ℝ} (hb : ∀ t, |φ t| ≤ C) (hs : ∀ t, 1 / 2 < |t| → φ t = 0) (t : ℝ) :
    ‖φ t‖ ≤ ind C t := by
  rw [Real.norm_eq_abs]
  by_cases ht : |t| ≤ 1 / 2
  · rw [ind_eq ht]; exact hb t
  · push_neg at ht
    have : t ∉ Icc (-(1/2):ℝ) (1/2) := fun h => by
      have := abs_le.2 ⟨h.1, h.2⟩; linarith
    rw [hs t ht, ind, indicator_of_notMem this, abs_zero]

lemma intble {φ : ℝ → ℝ} {C : ℝ} (hm : Measurable φ) (hb : ∀ t, |φ t| ≤ C)
    (hs : ∀ t, 1 / 2 < |t| → φ t = 0) : Integrable φ :=
  (ind_int C).mono' hm.aestronglyMeasurable (ae_of_all _ (le_ind hb hs))

lemma prod_supp {g : ℝ → ℝ} (hs : ∀ t, 1 / 2 < |t| → g t = 0) (v t : ℝ) (ht : 1 / 2 < |t|) :
    g t * g (t + v) = 0 := by rw [hs t ht, zero_mul]

lemma prod_bd {B M : ℝ} {g : ℝ → ℝ} (h : Good B M g) (v t : ℝ) : |g t * g (t + v)| ≤ B * B := by
  rw [abs_mul]; exact mul_le_mul (h.bd _) (h.bd _) (abs_nonneg _) h.B_nonneg

lemma prod_meas {g : ℝ → ℝ} (hm : Measurable g) (v : ℝ) : Measurable fun t => g t * g (t + v) :=
  hm.mul (hm.comp (measurable_id.add_const v))

/-- autocorrelations converge -/
theorem tendsto_autocorr {B M : ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hg : ∀ k, Good B M (g k))
    (hlim : ∀ t, Tendsto (fun k => g k t) atTop (𝓝 (f t))) (v : ℝ) :
    Tendsto (fun k => autocorr (g k) v) atTop (𝓝 (autocorr f v)) := by
  unfold autocorr
  refine tendsto_integral_of_dominated_convergence (ind (B * B))
    (fun k => (prod_meas (hg k).meas v).aestronglyMeasurable) (ind_int _)
    (fun k => ae_of_all _ (le_ind (prod_bd (hg k) v) (prod_supp (hg k).supp v))) (ae_of_all _ fun t => ?_)
  exact (hlim t).mul (hlim (t + v))

theorem tendsto_normSq {B M : ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hg : ∀ k, Good B M (g k))
    (hlim : ∀ t, Tendsto (fun k => g k t) atTop (𝓝 (f t))) :
    Tendsto (fun k => normSq (g k)) atTop (𝓝 (normSq f)) := by
  simp_rw [← autocorr_zero]; exact tendsto_autocorr hg hlim 0

/-- pole terms converge -/
theorem tendsto_pole {B M : ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hg : ∀ k, Good B M (g k))
    (hlim : ∀ t, Tendsto (fun k => g k t) atTop (𝓝 (f t))) (s : ℝ) :
    Tendsto (fun k => ∫ u in (-(1/2):ℝ)..(1/2), g k u * Real.exp (s * u)) atTop
      (𝓝 (∫ u in (-(1/2):ℝ)..(1/2), f u * Real.exp (s * u))) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun u => B * Real.exp (s * u))
    (Eventually.of_forall fun k => ((hg k).meas.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun k => ae_of_all _ fun u _ => ?_)
    ((by fun_prop : Continuous fun u => B * Real.exp (s * u)).intervalIntegrable _ _)
    (ae_of_all _ fun u _ => (hlim u).mul_const _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right ((hg k).bd u) (Real.exp_pos _).le

lemma poleR_eq (g : ℝ → ℝ) : poleR g (1 / 2) = ∫ u in (-(1/2):ℝ)..(1/2), g u * Real.exp ((-(1/2)) * u) := by
  unfold poleR; congr 1; funext u; congr 2; ring

lemma poleL_eq (g : ℝ → ℝ) : poleL g (1 / 2) = ∫ u in (-(1/2):ℝ)..(1/2), g u * Real.exp ((1/2) * u) := by
  unfold poleL; congr 1; funext u; congr 2; ring

/-! ## prime term: only `n = 2` survives -/

lemma autocorr_supp {g : ℝ → ℝ} (hs : ∀ t, 1 / 2 < |t| → g t = 0) {u : ℝ} (hu : 1 < |u|) :
    autocorr g u = 0 := by
  unfold autocorr
  have : ∀ t, g t * g (t + u) = 0 := by
    intro t
    by_cases ht : 1 / 2 < |t|
    · rw [hs t ht, zero_mul]
    · have : 1 / 2 < |t + u| := by
        have := abs_sub_abs_le_abs_sub u (-(t)); rw [abs_neg] at this
        have e : u - -t = t + u := by ring
        rw [e] at this; push_neg at ht; linarith
      rw [hs _ this, mul_zero]
  simp [this]

theorem primeS_eq {g : ℝ → ℝ} (hs : ∀ t, 1 / 2 < |t| → g t = 0) :
    primeS g = ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 * autocorr g (Real.log 2) := by
  unfold primeS
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
      rw [autocorr_supp hs (by rw [abs_of_nonneg hpos]; linarith), mul_zero]


/-! ## archimedean term -/

lemma kernel_bd {u : ℝ} (hu : 0 < u) : u * (Real.exp (u / 2) / Real.sinh u) ≤ 8 * Real.exp (-(u / 4)) := by
  set w := Real.exp (u / 4) with hw
  have w1 : 1 + u / 4 ≤ w := by have := Real.add_one_le_exp (u / 4); linarith
  have wpos : 0 < w := Real.exp_pos _
  have e2 : Real.exp (u / 2) = w ^ 2 := by rw [hw, ← Real.exp_nat_mul]; congr 1; ring
  have e4 : Real.exp u = w ^ 4 := by rw [hw, ← Real.exp_nat_mul]; congr 1; ring
  have em : Real.exp (-(u / 4)) = w⁻¹ := by rw [hw, Real.exp_neg]
  have hs : Real.sinh u = (w ^ 4 - (w ^ 4)⁻¹) / 2 := by rw [Real.sinh_eq, e4, Real.exp_neg, e4]
  have spos : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
  rw [e2, em, mul_div_assoc', div_le_iff₀ spos, hs]
  have w7 : 1 ≤ w ^ 7 := one_le_pow₀ (by linarith)
  have key : u * w ^ 7 ≤ 4 * (w ^ 8 - 1) := by nlinarith
  have w4 : 0 < w ^ 4 := by positivity
  rw [show 8 * w⁻¹ * ((w ^ 4 - (w ^ 4)⁻¹) / 2) = 4 * (w ^ 8 - 1) / (w * w ^ 4) by field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma diff_bd {B M : ℝ} {g : ℝ → ℝ} (h : Good B M g) {u : ℝ} (hu : 0 < u) :
    |autocorr g 0 - autocorr g u| ≤ B * (M + B) * u := by
  have hB := h.B_nonneg
  have hM : 0 ≤ M := by
    have := h.lip (1/2) 0 (by norm_num) (by norm_num)
    have := abs_nonneg (g (1/2) - g 0)
    norm_num at *; nlinarith [abs_nonneg (g (1/2) - g 0)]
  have i0 : Integrable fun t => g t * g (t + 0) :=
    intble (prod_meas h.meas 0) (prod_bd h 0) (prod_supp h.supp 0)
  have iu : Integrable fun t => g t * g (t + u) :=
    intble (prod_meas h.meas u) (prod_bd h u) (prod_supp h.supp u)
  unfold autocorr
  rw [← integral_sub i0 iu]
  set J : Set ℝ := Ioc (1 / 2 - u) (1 / 2)
  have bnd : ∀ t, ‖g t * g (t + 0) - g t * g (t + u)‖ ≤ ind (B * M * u) t + J.indicator (fun _ => B * B) t := by
    intro t
    rw [Real.norm_eq_abs, add_zero, ← mul_sub, abs_mul]
    have i1 : 0 ≤ J.indicator (fun _ => B * B) t := indicator_nonneg (fun _ _ => mul_nonneg hB hB) _
    by_cases ht : |t| ≤ 1 / 2
    · rw [ind_eq ht]
      by_cases htu : |t + u| ≤ 1 / 2
      · have := h.lip t (t + u) ht htu
        rw [show t - (t + u) = -u by ring, abs_neg, abs_of_pos hu] at this
        have := mul_le_mul (h.bd t) this (abs_nonneg _) hB
        linarith
      · push_neg at htu
        have hJ : t ∈ J := by
          constructor
          · have := abs_le.1 ht
            rcases lt_abs.1 htu with h1 | h1 <;> linarith
          · exact (abs_le.1 ht).2
        rw [indicator_of_mem hJ, h.supp _ htu, sub_zero]
        have := mul_le_mul (h.bd t) (h.bd t) (abs_nonneg _) hB
        nlinarith [mul_nonneg (mul_nonneg hB hM) hu.le]
    · push_neg at ht
      rw [h.supp t ht, abs_zero, zero_mul]
      exact add_nonneg (by unfold ind; exact indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hB hM) hu.le) _) i1
  have iJ : Integrable (J.indicator fun _ => B * B) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp) (by simp [ENNReal.mul_eq_top]))
  calc |∫ t, (g t * g (t + 0) - g t * g (t + u))|
      ≤ ∫ t, (ind (B * M * u) t + J.indicator (fun _ => B * B) t) := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_of_norm_le ((ind_int _).add iJ) (ae_of_all _ bnd)
    _ = B * M * u + B * B * u := by
        rw [integral_add (ind_int _) iJ, ind, integral_indicator_const _ measurableSet_Icc,
          integral_indicator_const _ measurableSet_Ioc]
        simp [hu.le]; norm_num; ring
    _ = B * (M + B) * u := by ring

lemma autocorr_meas {g : ℝ → ℝ} (hm : Measurable g) : StronglyMeasurable fun u => autocorr g u := by
  unfold autocorr
  have : StronglyMeasurable fun p : ℝ × ℝ => g p.2 * g (p.2 + p.1) :=
    ((hm.comp measurable_snd).mul (hm.comp (measurable_snd.add measurable_fst))).stronglyMeasurable
  exact this.integral_prod_right'

lemma arch_meas {g : ℝ → ℝ} (hm : Measurable g) : AEStronglyMeasurable (archIntegrand g) (volume.restrict (Ioi 0)) := by
  unfold archIntegrand
  have := (autocorr_meas hm).measurable
  exact ((measurable_const.sub this).mul (by fun_prop)).aestronglyMeasurable

lemma arch_bd {B M : ℝ} {g : ℝ → ℝ} (h : Good B M g) {u : ℝ} (hu : 0 < u) :
    ‖archIntegrand g u‖ ≤ B * (M + B) * (8 * Real.exp (-(u / 4))) := by
  unfold archIntegrand
  have hB := h.B_nonneg
  have hK : 0 < Real.exp (u / 2) / Real.sinh u := div_pos (Real.exp_pos _) (Real.sinh_pos_iff.2 hu)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hK]
  have hd := diff_bd h hu
  have hMB : 0 ≤ B * (M + B) := by
    have := (abs_nonneg _).trans hd; exact nonneg_of_mul_nonneg_left (by linarith) hu
  calc _ ≤ B * (M + B) * u * (Real.exp (u / 2) / Real.sinh u) := mul_le_mul_of_nonneg_right hd hK.le
    _ = B * (M + B) * (u * (Real.exp (u / 2) / Real.sinh u)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_bd hu) hMB

theorem tendsto_archE {B M : ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hg : ∀ k, Good B M (g k))
    (hlim : ∀ t, Tendsto (fun k => g k t) atTop (𝓝 (f t))) :
    Tendsto (fun k => archE (g k)) atTop (𝓝 (archE f)) := by
  unfold archE
  have hint : Integrable (fun u => B * (M + B) * (8 * Real.exp (-(u / 4)))) (volume.restrict (Ioi 0)) := by
    have : IntegrableOn (fun u : ℝ => Real.exp (-(1/4) * u)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 (by norm_num)
    have e : (fun u => B * (M + B) * (8 * Real.exp (-(u / 4)))) = fun u => B * (M + B) * 8 * Real.exp (-(1/4) * u) := by
      funext u; ring_nf
    rw [e]; exact this.const_mul _
  refine tendsto_integral_of_dominated_convergence _ (fun k => arch_meas (hg k).meas) hint
    (fun k => (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u hu => arch_bd (hg k) hu))
    (ae_of_all _ fun u => ?_)
  unfold archIntegrand
  exact ((tendsto_autocorr hg hlim 0).sub (tendsto_autocorr hg hlim u)).mul_const _

/-- **`weilQg (1/2)` is continuous along bounded, uniformly interior-Lipschitz pointwise convergence.** -/
theorem tendsto_weilQg {B M : ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hg : ∀ k, Good B M (g k)) (hf : Good B M f)
    (hlim : ∀ t, Tendsto (fun k => g k t) atTop (𝓝 (f t))) :
    Tendsto (fun k => weilQg (1 / 2) (g k)) atTop (𝓝 (weilQg (1 / 2) f)) := by
  unfold weilQg
  simp_rw [poleR_eq, poleL_eq, primeS_eq (hg _).supp, primeS_eq hf.supp]
  exact ((((tendsto_pole hg hlim _).const_mul 2).mul (tendsto_pole hg hlim _)).add
    ((tendsto_normSq hg hlim).const_mul _)).add (tendsto_archE hg hlim) |>.sub
    (((tendsto_autocorr hg hlim _).const_mul _).const_mul 2)

end WeilCont
