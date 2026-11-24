import Mathlib
import LandauLaplace

/-!
# Taylor coefficients of a Laplace transform, and of a function with a simple pole

Complex analysis for Landau's theorem on windows (`LandauWindow.lean`).

* `laplace g s = ∫_{u>0} g(u) e^{−su} du`, and the moments `moment g k z = ∫_{u>0} g(u) uᵏ e^{−zu} du / k!`.
* `iteratedDeriv_eq_moment`: if `|g(u)| ≤ C e^{au}` and `Φ` agrees with `laplace g` on `Re s > a`, then
  `Φ⁽ᵏ⁾(z)/k! = (−1)ᵏ M_k(z)` for `Re z > a`. This is the library's `LandauLaplace.lap_hasFPowerSeriesOnBall`
  applied to `g⁺ = max g 0` and `g⁻ = max (−g) 0`, whose transforms differ by that of `g`.
* `taylor_bound` (Cauchy's estimate): `H` holomorphic on `B(z, r)` has `‖H⁽ᵏ⁾(z)/k!‖ ≤ M r'^{−k}` for each
  `0 < r' < r`.
* `pole_asymptotic`: if `Φ` is holomorphic on `B(z, r)` except at `p ≠ z`, where `Φ = c/(s − p) + h` with `h`
  analytic at `p`, then `(−1)ᵏ Φ⁽ᵏ⁾(z)/k! = c/(z − p)^{k+1} + O(r'^{−k})` for each `0 < r' < r`: `Φ − c/(s − p)`
  extends holomorphically to `B(z, r)`, and the `k`-th derivative of `c/(s − p)` at `z` is
  `(−1)ᵏ k! c/(z − p)^{k+1}`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Nat

namespace LandauWindow

/-- The Laplace transform `∫_{u>0} g(u) e^{−su} du`. -/
noncomputable def laplace (g : ℝ → ℝ) (s : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-(s * u))

/-- The `k`-th moment `∫_{u>0} g(u) uᵏ e^{−zu} du / k!`. -/
noncomputable def moment (g : ℝ → ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-(z * u)) / (k ! : ℂ)

open LandauLaplace in
/-- A function with `0 ≤ A(u) ≤ C e^{au}` for `u ≥ 0` meets `LandauLaplace.Hyp` on `(0, ∞)` with `ph = id`, and its
transform converges at every real `σ > a`. -/
theorem hyp_conv {A : ℝ → ℝ} (hA : Measurable A) (h0 : ∀ u, 0 ≤ A u) {a C : ℝ}
    (hC : ∀ u, 0 ≤ u → A u ≤ C * Real.exp (a * u)) :
    Hyp (volume.restrict (Ioi 0)) A id ∧ ∀ σ, a < σ → Conv (volume.restrict (Ioi 0)) A id σ := by
  have h : Hyp (volume.restrict (Ioi 0)) A id := ⟨ae_of_all _ h0,
    (ae_restrict_mem measurableSet_Ioi).mono fun _ hu => le_of_lt hu, hA.aestronglyMeasurable,
    measurable_id.aestronglyMeasurable⟩
  refine ⟨h, fun σ hσ => ((integrableOn_exp_mul_Ioi (sub_neg.2 hσ) 0).const_mul C).mono' (h.meas_exp σ) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
  calc ‖A u * Real.exp (-σ * u)‖ ≤ C * Real.exp (a * u) * Real.exp (-σ * u) := by
        rw [Real.norm_of_nonneg (mul_nonneg (h0 u) (Real.exp_pos _).le)]; gcongr; exact hC u hu.le
    _ = C * Real.exp ((a - σ) * u) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

open LandauLaplace in
/-- **The Taylor coefficients of a Laplace transform are its moments**, up to sign. -/
theorem iteratedDeriv_eq_moment {g : ℝ → ℝ} (hg : Measurable g) {a C : ℝ}
    (hC : ∀ u, 0 ≤ u → |g u| ≤ C * Real.exp (a * u)) {Φ : ℂ → ℂ}
    (hΦ : ∀ s : ℂ, a < s.re → Φ s = laplace g s) {z : ℂ} (hz : a < z.re) (k : ℕ) :
    iteratedDeriv k Φ z / (k ! : ℂ) = (-1) ^ k * moment g k z := by
  -- `g = g⁺ − g⁻` with `0 ≤ g^± ≤ |g|`
  obtain ⟨h₁, c₁⟩ := hyp_conv (A := fun u => max (g u) 0) (hg.max measurable_const)
    (fun u => le_max_right _ _) fun u hu => (max_le (le_abs_self _) (abs_nonneg _)).trans (hC u hu)
  obtain ⟨h₂, c₂⟩ := hyp_conv (A := fun u => max (-g u) 0) (hg.neg.max measurable_const)
    (fun u => le_max_right _ _) fun u hu => (max_le (neg_le_abs _) (abs_nonneg _)).trans (hC u hu)
  have hsplit : ∀ u (w : ℂ), (g u : ℂ) * w = ((max (g u) 0 : ℝ) : ℂ) * w - ((max (-g u) 0 : ℝ) : ℂ) * w :=
    fun u w => by rw [← sub_mul, ← ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
  -- the power series of `lap g⁺ − lap g⁻` at `z`, which is `Φ` on `Re s > σ`
  obtain ⟨σ, hσ, hσz⟩ := exists_between hz
  have hr0 : 0 < ((z.re - σ) / 2).toNNReal := Real.toNNReal_pos.2 (by linarith)
  have hr : σ < z.re - ((z.re - σ) / 2).toNNReal := by rw [Real.coe_toNNReal _ (by linarith)]; linarith
  have H := ((lap_hasFPowerSeriesOnBall h₁ (c₁ σ hσ) hr0 hr).sub
    (lap_hasFPowerSeriesOnBall h₂ (c₂ σ hσ) hr0 hr)).hasFPowerSeriesAt.congr (g := Φ) (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hσz] with s (hs : σ < s.re)
      have i₁ := integrable_mom h₁ (c₁ σ hσ) hs 0
      have i₂ := integrable_mom h₂ (c₂ σ hσ) hs 0
      simp only [pow_zero, mul_one] at i₁ i₂
      rw [Pi.sub_apply, hΦ s (hσ.trans hs), lap, lap, laplace, ← integral_sub i₁ i₂]
      congr 1; funext u
      rw [hsplit, id_eq, neg_mul])
  rw [← FormalMultilinearSeries.ofScalars_sub] at H
  have e := congrFun (FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (H.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries H)) k
  simp only [Pi.sub_apply, coef] at e
  rw [e, moment, integral_div, mul_div_assoc, mul_div_assoc, ← mul_sub, ← sub_div, mom, mom,
    ← integral_sub (integrable_mom h₁ (c₁ σ hσ) hσz k) (integrable_mom h₂ (c₂ σ hσ) hσz k)]
  congr 3; funext u
  simp only [id_eq, neg_mul, mul_assoc]
  exact (hsplit u _).symm

/-- **Cauchy's estimate** for the Taylor coefficients of a function holomorphic on a disc. -/
theorem taylor_bound {H : ℂ → ℂ} {z : ℂ} {r r' : ℝ} (hH : DifferentiableOn ℂ H (Metric.ball z r))
    (hr' : 0 < r') (hrr : r' < r) : ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k H z / (k ! : ℂ)‖ ≤ M / r' ^ k := by
  have hcl : Metric.closedBall z r' ⊆ Metric.ball z r := Metric.closedBall_subset_ball hrr
  obtain ⟨M, hM⟩ := (isCompact_sphere z r').exists_bound_of_continuousOn
    (hH.continuousOn.mono (Metric.sphere_subset_closedBall.trans hcl))
  refine ⟨M, fun k => ?_⟩
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  calc ‖iteratedDeriv k H z‖ ≤ k ! * M / r' ^ k :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr' (hH.diffContOnCl_ball hcl) hM
    _ = M / r' ^ k * k ! := by ring

/-- **The Taylor coefficients near a simple pole**: the pole's term, up to `O(r'^{−k})`. -/
theorem pole_asymptotic {Φ : ℂ → ℂ} {z p c : ℂ} {r r' : ℝ} (hpz : p ≠ z)
    (hΦ : DifferentiableOn ℂ Φ (Metric.ball z r \ {p}))
    (hpole : ∃ h : ℂ → ℂ, AnalyticAt ℂ h p ∧ ∀ᶠ s in 𝓝[≠] p, Φ s = c / (s - p) + h s)
    (hr' : 0 < r') (hrr : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ, ‖(-1) ^ k * iteratedDeriv k Φ z / (k ! : ℂ) - c / (z - p) ^ (k + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨h, hh, hev⟩ := hpole
  -- `H = Φ − c/(s − p)` off `p`, and `h p` at `p`
  obtain ⟨H, hHp, hHne⟩ : ∃ H : ℂ → ℂ, H p = h p ∧ ∀ s, s ≠ p → H s = Φ s - c / (s - p) :=
    ⟨Function.update (fun s => Φ s - c / (s - p)) p (h p), Function.update_self .., fun s hs =>
      Function.update_of_ne hs ..⟩
  have hHs : ∀ s, s ≠ p → H =ᶠ[𝓝 s] fun t => Φ t - c / (t - p) := fun s hs => by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with t ht using hHne t ht
  -- `H` is holomorphic on the disc: it is `h` near `p`, and `Φ − c/(s − p)` near any other point
  have hHd : DifferentiableOn ℂ H (Metric.ball z r) := fun s hs => by
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases eq_or_ne s p with rfl | hsp
    · refine hh.differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [eventually_nhdsWithin_iff.1 hev] with t ht
      rcases eq_or_ne t s with rfl | hts
      · exact hHp
      · rw [hHne t hts, ht hts, add_sub_cancel_left]
    · have hΦs : DifferentiableAt ℂ Φ s :=
        hΦ.differentiableAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hs, hsp⟩)
      have hsp' : s - p ≠ 0 := sub_ne_zero.2 hsp
      exact (show DifferentiableAt ℂ (fun t => Φ t - c / (t - p)) s by
        fun_prop (disch := exact hsp')).congr_of_eventuallyEq (hHs s hsp)
  obtain ⟨M, hM⟩ := taylor_bound hHd hr' hrr
  refine ⟨M, fun k => ?_⟩
  have hzp : z - p ≠ 0 := sub_ne_zero.2 hpz.symm
  -- the `k`-th Taylor coefficient of `c/(s − p)` at `z`
  have hQ : iteratedDeriv k (fun s => c / (s - p)) z / k ! = (-1) ^ k * (c / (z - p) ^ (k + 1)) := by
    have e := congrFun (iter_deriv_inv_linear_sub k (1 : ℂ) p) z
    simp only [one_mul, one_pow, mul_one] at e
    have e' : (z - p) ^ (-1 - (k : ℤ)) = ((z - p) ^ (k + 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
    simp_rw [div_eq_mul_inv, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, e, e']
    have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    field_simp
  have hΦH : Φ =ᶠ[𝓝 z] fun s => H s + c / (s - p) := by
    filter_upwards [hHs z hpz.symm] with s hs
    rw [hs, sub_add_cancel]
  have hHc : ContDiffAt ℂ k H z :=
    (hHd.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr'.trans hrr)))).contDiffAt
  have hQc : ContDiffAt ℂ k (fun s => c / (s - p)) z := by fun_prop (disch := exact hzp)
  have h1 : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  calc ‖(-1) ^ k * iteratedDeriv k Φ z / (k ! : ℂ) - c / (z - p) ^ (k + 1)‖
      = ‖(-1) ^ k * (iteratedDeriv k H z / (k ! : ℂ))‖ := by
        rw [mul_div_assoc, hΦH.iteratedDeriv_eq k, iteratedDeriv_fun_add hHc hQc, add_div, hQ]
        congr 1
        linear_combination (c / (z - p) ^ (k + 1)) * h1
    _ ≤ M / r' ^ k := by rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]; exact hM k

end LandauWindow

#print axioms LandauWindow.iteratedDeriv_eq_moment
#print axioms LandauWindow.pole_asymptotic
