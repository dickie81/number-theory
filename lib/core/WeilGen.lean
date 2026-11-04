import Mathlib
import WeilCoer
import LegSpan
import WeilCont

/-! # `L = 1/2` positivity for general test functions

Class: `f : ℝ → ℝ` of class `C¹` on `ℝ` with `f u = 0` for `|u| > 1/2`.
Then `weilQg (1/2) f ≥ 10⁻⁸ ‖f‖²`, hence `> 0` for `f ≠ 0`; for even `f` the same holds for `weilQ`.

Proof: Weierstrass-approximate `f'` on `[−1/2, 1/2]` by `q_k` (`|q_k − f'| < 1/(k+1)`), integrate to a polynomial
`p_k` with `p_k(−1/2) = f(−1/2)`, cut it to `[−1/2, 1/2]`. The cut polynomials are Legendre mode sums (coercive bound),
are uniformly bounded and uniformly Lipschitz on `[−1/2, 1/2]` (they jump at `±1/2`), and converge pointwise to `f`;
pass to the limit with `WeilCont.tendsto_weilQg`. -/

namespace WeilGen

open Real Filter Topology MeasureTheory Set WeilForm Polynomial LegSpan WeilCont Interval

/-- the test-function class -/
def TestFn (f : ℝ → ℝ) : Prop := ContDiff ℝ 1 f ∧ ∀ u, 1 / 2 < |u| → f u = 0

lemma mem_Icc_of_abs {u : ℝ} (h : |u| ≤ 1 / 2) : u ∈ Icc (-(1/2):ℝ) (1/2) := ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩

lemma uIoc_sub {s t : ℝ} (hs : |s| ≤ 1 / 2) (ht : |t| ≤ 1 / 2) : uIoc t s ⊆ Icc (-(1/2):ℝ) (1/2) :=
  uIoc_subset_uIcc.trans (uIcc_subset_Icc (mem_Icc_of_abs ht) (mem_Icc_of_abs hs))

/-- the approximation scheme -/
theorem approx {f : ℝ → ℝ} (hf : TestFn f) : ∃ (B M : ℝ) (g : ℕ → ℝ → ℝ), (∀ k, Good B M (g k)) ∧ Good B M f ∧
    (∀ t, Tendsto (fun k => g k t) atTop (𝓝 (f t))) ∧ ∀ k, ∃ p : ℝ[X], g k = cutp (fun u => p.eval u) := by
  obtain ⟨hcd, hs⟩ := hf
  have hdif : Differentiable ℝ f := hcd.differentiable one_ne_zero
  have hdc : Continuous (deriv f) := hcd.continuous_deriv le_rfl
  obtain ⟨B0, hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcd.continuous.continuousOn (s := Icc (-(1/2):ℝ) (1/2)))
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hdc.continuousOn (s := Icc (-(1/2):ℝ) (1/2)))
  have B0p : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0 (mem_Icc_of_abs (by norm_num)))
  have M0p : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0 (mem_Icc_of_abs (by norm_num)))
  have ftc : ∀ s t, f s - f t = ∫ x in t..s, deriv f x := fun s t =>
    (intervalIntegral.integral_deriv_eq_sub (fun x _ => hdif x) (hdc.intervalIntegrable _ _)).symm
  choose q hq using fun k : ℕ => exists_polynomial_near_of_continuousOn (-(1/2)) (1/2) (deriv f)
    hdc.continuousOn (1 / ((k:ℝ) + 1)) (by positivity)
  set p : ℕ → ℝ[X] := fun k => anti (q k) + C (f (-(1/2)) - (anti (q k)).eval (-(1/2)))
  have pftc : ∀ k s t, (p k).eval s - (p k).eval t = ∫ x in t..s, (q k).eval x := by
    intro k s t
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_anti (q k) x)
      ((q k).continuous.intervalIntegrable _ _)]
    simp [p]
  have p0 : ∀ k, (p k).eval (-(1/2)) = f (-(1/2)) := fun k => by simp [p]
  have eps1 : ∀ k : ℕ, 1 / ((k:ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have qbd : ∀ k x, x ∈ Icc (-(1/2):ℝ) (1/2) → |(q k).eval x| ≤ M0 + 1 := by
    intro k x hx
    have h1 := hq k x hx; have h2 := hM0 x hx; rw [Real.norm_eq_abs] at h2
    have := eps1 k
    calc |(q k).eval x| ≤ |(q k).eval x - deriv f x| + |deriv f x| := by
          have := abs_add_le ((q k).eval x - deriv f x) (deriv f x); simpa using this
      _ ≤ _ := by linarith
  have perr : ∀ k x, |x| ≤ 1 / 2 → |(p k).eval x - f x| ≤ 1 / ((k:ℝ) + 1) := by
    intro k x hx
    have e : (p k).eval x - f x = ∫ y in (-(1/2):ℝ)..x, ((q k).eval y - deriv f y) := by
      rw [intervalIntegral.integral_sub ((q k).continuous.intervalIntegrable _ _) (hdc.intervalIntegrable _ _),
        ← pftc, ← ftc, p0]; ring
    rw [e]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1/2)) (b := x)
      (C := 1 / ((k:ℝ) + 1)) (f := fun y => (q k).eval y - deriv f y)
      (fun y hy => by rw [Real.norm_eq_abs]; exact (hq k y (uIoc_sub hx (by norm_num) hy)).le)
    rw [Real.norm_eq_abs] at hb
    have : |x - -(1/2)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [abs_le.1 hx]
    have hk : 0 < 1 / ((k:ℝ) + 1) := by positivity
    nlinarith [abs_nonneg (x - -(1/2))]
  set g : ℕ → ℝ → ℝ := fun k => cutp (fun u => (p k).eval u)
  refine ⟨B0 + 1, M0 + 1, g, fun k => ⟨?_, ?_, ?_, ?_⟩, ⟨hcd.continuous.measurable, hs, ?_, ?_⟩, ?_, fun k => ⟨p k, rfl⟩⟩
  · exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) (p k).continuous.measurable
      measurable_const
  · intro u hu; simp only [g, cutp, ite_eq_right (not_le.2 hu)]
  · intro u; simp only [g, cutp]; split_ifs with hu
    · have := perr k u hu; have := hB0 u (mem_Icc_of_abs hu); rw [Real.norm_eq_abs] at this
      have := eps1 k
      calc |(p k).eval u| ≤ |(p k).eval u - f u| + |f u| := by
            have := abs_add_le ((p k).eval u - f u) (f u); simpa using this
        _ ≤ _ := by linarith
    · simp; linarith
  · intro s t hs' ht'
    simp only [g, cutp, ite_eq_left hs', ite_eq_left ht']
    rw [pftc]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := s) (C := M0 + 1)
      (f := fun y => (q k).eval y) (fun y hy => by rw [Real.norm_eq_abs]; exact qbd k y (uIoc_sub hs' ht' hy))
    rwa [Real.norm_eq_abs] at this
  · intro u
    by_cases hu : |u| ≤ 1 / 2
    · have := hB0 u (mem_Icc_of_abs hu); rw [Real.norm_eq_abs] at this; linarith
    · rw [hs u (not_le.1 hu)]; simp; linarith
  · intro s t hs' ht'
    rw [ftc]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := s) (C := M0 + 1)
      (f := deriv f) (fun y hy => by have := hM0 y (uIoc_sub hs' ht' hy); linarith)
    rwa [Real.norm_eq_abs] at this
  · intro t
    by_cases ht : |t| ≤ 1 / 2
    · have hε : Tendsto (fun k : ℕ => 1 / ((k:ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (f := fun k => g k t) (g := fun k => f t - 1 / ((k:ℝ) + 1))
        (h := fun k => f t + 1 / ((k:ℝ) + 1)) ?_ ?_ (fun k => ?_) (fun k => ?_)
      · simpa using (tendsto_const_nhds (x := f t)).sub hε
      · simpa using (tendsto_const_nhds (x := f t)).add hε
      · have := abs_le.1 (perr k t ht); simp only [g, cutp, ite_eq_left ht]; linarith
      · have := abs_le.1 (perr k t ht); simp only [g, cutp, ite_eq_left ht]; linarith
    · have : ∀ k, g k t = f t := fun k => by simp only [g, cutp, ite_eq_right ht, hs t (not_le.1 ht)]
      simp only [this]; exact tendsto_const_nhds

/-- **Coercivity on the test class**: `weilQg (1/2) f ≥ 10⁻⁸ ‖f‖²`. -/
theorem coer {f : ℝ → ℝ} (hf : TestFn f) : WeilCoer.cW * normSq f ≤ weilQg (1 / 2) f := by
  obtain ⟨B, M, g, hg, hfg, hlim, hp⟩ := approx hf
  refine le_of_tendsto_of_tendsto' ((tendsto_normSq hg hlim).const_mul _) (tendsto_weilQg hg hfg hlim) fun k => ?_
  obtain ⟨p, hpk⟩ := hp k
  obtain ⟨N, x, y, hxy⟩ := poly_hx p
  rw [hpk, ← hxy]; exact WeilCoer.coer_hx' N x y

lemma normSq_pos {f : ℝ → ℝ} (hf : TestFn f) (hne : f ≠ 0) : 0 < normSq f := by
  obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by by_contra h; push Not at h; exact hne (funext h)
  unfold normSq
  have hc : Continuous fun t => f t ^ 2 := (hf.1.continuous).pow 2
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := u) ?_ (fun t => sq_nonneg _) (pow_ne_zero 2 hu)
  refine HasCompactSupport.intro (isCompact_Icc (a := -(1/2)) (b := 1/2)) fun t ht => ?_
  have : 1 / 2 < |t| := by
    by_contra h; push Not at h; exact ht (mem_Icc_of_abs h)
  simp [hf.2 t this]

/-- **`L = 1/2` positivity for general test functions.** -/
theorem pos {f : ℝ → ℝ} (hf : TestFn f) (hne : f ≠ 0) : 0 < weilQg (1 / 2) f := by
  have := coer hf; have := normSq_pos hf hne
  have : (0:ℝ) < WeilCoer.cW := by unfold WeilCoer.cW; norm_num
  nlinarith

lemma poleL_even {f : ℝ → ℝ} (he : ∀ u, f (-u) = f u) : poleL f (1 / 2) = poleR f (1 / 2) := by
  unfold poleL poleR
  have := intervalIntegral.integral_comp_neg (a := -(1/2:ℝ)) (b := 1/2) (fun u => f u * Real.exp (u / 2))
  simp only [neg_neg] at this
  rw [← this]; congr 1; funext u; rw [he]; congr 2; ring

theorem weilQ_eq_weilQg {f : ℝ → ℝ} (he : ∀ u, f (-u) = f u) : weilQ (1 / 2) f = weilQg (1 / 2) f := by
  rw [weilQ_eq']; unfold weilQg; rw [poleL_even he]; ring

/-- **Even corollary for the repo's `weilQ`.** -/
theorem coer_even {f : ℝ → ℝ} (hf : TestFn f) (he : ∀ u, f (-u) = f u) :
    WeilCoer.cW * normSq f ≤ weilQ (1 / 2) f := by rw [weilQ_eq_weilQg he]; exact coer hf

theorem pos_even {f : ℝ → ℝ} (hf : TestFn f) (he : ∀ u, f (-u) = f u) (hne : f ≠ 0) :
    0 < weilQ (1 / 2) f := by rw [weilQ_eq_weilQg he]; exact pos hf hne

end WeilGen
