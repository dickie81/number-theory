import Mathlib
import WindowKernel
import WindowPole
import WindowNearest

/-!
# Landau's theorem on windows

Let `g` be a real function on `[0, ∞)` of at most exponential growth whose Laplace transform `Φ` continues
meromorphically to the right half-plane, with simple poles only, at an isolated set `Z` left of `Re s = 1`; and
at a real pole let the residue have positive real part. Landau's theorem says that if `g ≤ C e^{θu}` for all
large `u`, there is no pole right of `θ`. Here the bound is asked only on windows `[U, λU]`, `λ > 1` fixed, for
arbitrarily large `U`, and the conclusion is the same (`re_le_of_windows`).

The proof compares Taylor coefficients. At a point `z` right of every pole, `(−1)ᵏ Φ⁽ᵏ⁾(z)/k!` is the moment
`M_k(z) = ∫ g(u) uᵏ e^{−zu} du / k!` (`iteratedDeriv_eq_moment`), and for a real `σ` and any `γ`,
`‖M_k(σ + iγ)‖ + M_k(σ) ≤ ∫ (|g| + g) uᵏ e^{−σu} / k! = 2 ∫ g⁺ uᵏ e^{−σu} / k!`. Only `g ≤ …` is needed for
`g⁺`, and for `k` matched to the window the kernel's mass outside it is negligible (`window_choice`), so the
right side is `O((σ − θ)^{−k})` (`window_estimate`). A pole `p` right of `θ` makes the left side grow faster.
Take `z` on the line `Re s = σ` with a unique nearest pole `p` (`nearest_pole`): its term `c/(z − p)^{k+1}`
dominates `M_k(z)` (`pole_asymptotic`), and either no pole is as near to `σ`, so that `M_k(σ)` is smaller
(`taylor_bound`), or the nearest pole to `σ` is real with a positive residue, and `M_k(σ)` itself is large and
positive.

* `PoleData`: the hypotheses on `g`, `Φ` and `Z`.
* `window_estimate`: the bound on `‖M_k(σ + iγ)‖ + Re M_k(σ)` from the window.
* `re_le_of_windows`: **Landau's theorem on windows**.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Nat

namespace LandauWindow

/-- The hypotheses of Landau's theorem on windows: `g` measurable of growth `e^{au}`, its Laplace transform
`Φ` on `Re s > a`, holomorphic on the right half-plane off an isolated set `Z` left of `Re s = 1`, with a
simple pole at each point of `Z`, of positive real part at a real point. -/
structure PoleData (g : ℝ → ℝ) (Φ : ℂ → ℂ) (Z : Set ℂ) (a : ℝ) : Prop where
  measurable : Measurable g
  growth : ∃ C : ℝ, ∀ u, 0 ≤ u → |g u| ≤ C * Real.exp (a * u)
  laplace_eq : ∀ s : ℂ, a < s.re → Φ s = laplace g s
  re_lt_one : ∀ ρ ∈ Z, ρ.re < 1
  isolated : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z
  differentiableAt : ∀ s : ℂ, 0 < s.re → s ∉ Z → DifferentiableAt ℂ Φ s
  pole : ∀ ρ ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re) ∧
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s

/-! ## The window estimate -/

/-- **The window estimate**: if `g ≤ C e^{θu}` on `[U, V]` and `|g| ≤ C₀ e^{au}` on `[0, ∞)`, then for
`σ > max a θ` and every `γ`, `‖M_k(σ + iγ)‖ + Re M_k(σ)` is at most `2 max C 0 / (σ − θ)^{k+1}` plus `2C₀`
times the mass of the kernel `uᵏ e^{−(σ−a)u}/k!` outside `[U, V]`. -/
theorem window_estimate {g : ℝ → ℝ} (hg : Measurable g) {a C₀ : ℝ}
    (hC₀ : ∀ u, 0 ≤ u → |g u| ≤ C₀ * Real.exp (a * u)) {θ C σ U V : ℝ} (haσ : a < σ) (hθσ : θ < σ)
    (hW : ∀ u ∈ Icc U V, g u ≤ C * Real.exp (θ * u)) (k : ℕ) (γ : ℝ) :
    ‖moment g k (σ + γ * I)‖ + (moment g k σ).re ≤
      2 * max C 0 / (σ - θ) ^ (k + 1) +
        2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp (-((σ - a) * u)) / k ! := by
  have hb : 0 < σ - a := by linarith
  have hb' : 0 < σ - θ := by linarith
  -- `K u = uᵏ e^{−σu}/k!`, and `|g| K` is dominated by `C₀` times the kernel at `σ − a`
  have hdom : ∀ u, 0 ≤ u → |g u| * (u ^ k * Real.exp (-(σ * u)) / k !) ≤
      C₀ * (u ^ k * Real.exp (-((σ - a) * u)) / k !) := by
    intro u hu
    have hK : 0 ≤ u ^ k * Real.exp (-(σ * u)) / k ! := by positivity
    calc |g u| * (u ^ k * Real.exp (-(σ * u)) / k !)
        ≤ C₀ * Real.exp (a * u) * (u ^ k * Real.exp (-(σ * u)) / k !) :=
          mul_le_mul_of_nonneg_right (hC₀ u hu) hK
      _ = C₀ * (u ^ k * Real.exp (-((σ - a) * u)) / k !) := by
          rw [show -((σ - a) * u) = a * u + -(σ * u) by ring, Real.exp_add]; ring
  have hkint : IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-((σ - a) * u)) / k !) (Ioi 0) :=
    (kernel_integrableOn k hb).div_const _
  have hint : IntegrableOn (fun u : ℝ => g u * (u ^ k * Real.exp (-(σ * u)) / k !)) (Ioi 0) := by
    refine (hkint.const_mul C₀).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ u ^ k * Real.exp (-(σ * u)) / k !)]
    exact hdom u hu.le
  have hint_abs : IntegrableOn (fun u : ℝ => |g u| * (u ^ k * Real.exp (-(σ * u)) / k !)) (Ioi 0) := by
    refine IntegrableOn.congr_fun hint.abs (fun u (hu : 0 < u) => ?_) measurableSet_Ioi
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ u ^ k * Real.exp (-(σ * u)) / k !)]
  have hint_pos : IntegrableOn (fun u : ℝ => 2 * max (g u) 0 * (u ^ k * Real.exp (-(σ * u)) / k !)) (Ioi 0) := by
    refine (hint_abs.add hint).congr_fun (fun u _ => ?_) measurableSet_Ioi
    rcases le_total 0 (g u) with h | h
    · simp only [Pi.add_apply, abs_of_nonneg h, max_eq_left h]; ring
    · simp only [Pi.add_apply, abs_of_nonpos h, max_eq_right h]; ring
  -- `‖M_k(σ + iγ)‖ ≤ ∫ |g| K` and `Re M_k(σ) = ∫ g K`
  have hn : ‖moment g k (σ + γ * I)‖ ≤ ∫ u in Ioi (0 : ℝ), |g u| * (u ^ k * Real.exp (-(σ * u)) / k !) := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (setIntegral_congr_fun measurableSet_Ioi
      fun u (hu : 0 < u) => ?_))
    have hre : (-((σ + γ * I) * (u : ℂ))).re = -(σ * u) := by simp
    rw [norm_div, norm_mul, norm_mul, Complex.norm_exp, hre, norm_pow, Complex.norm_real, Complex.norm_real,
      Complex.norm_natCast, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu]
    ring
  have hre : (moment g k σ).re = ∫ u in Ioi (0 : ℝ), g u * (u ^ k * Real.exp (-(σ * u)) / k !) := by
    have : moment g k σ = ((∫ u in Ioi (0 : ℝ), g u * (u ^ k * Real.exp (-(σ * u)) / k !) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      push_cast
      ring
    rw [this, ofReal_re]
  -- so the left side is at most `∫ 2 g⁺ K`, split at the window
  have hsum : ‖moment g k (σ + γ * I)‖ + (moment g k σ).re ≤
      ∫ u in Ioi (0 : ℝ), 2 * max (g u) 0 * (u ^ k * Real.exp (-(σ * u)) / k !) := by
    rw [hre]
    refine (add_le_add hn le_rfl).trans (le_of_eq ?_)
    rw [← integral_add hint_abs hint]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rcases le_total 0 (g u) with h | h
    · simp only [abs_of_nonneg h, max_eq_left h]; ring
    · simp only [abs_of_nonpos h, max_eq_right h]; ring
  rw [← integral_inter_add_sdiff measurableSet_Icc hint_pos] at hsum
  -- inside the window `g⁺ ≤ max C 0 · e^{θu}`
  have hk2 : IntegrableOn (fun u : ℝ => 2 * max C 0 * (u ^ k * Real.exp (-((σ - θ) * u)) / k !)) (Ioi 0) :=
    ((kernel_integrableOn k hb').div_const _).const_mul _
  have hwin : ∫ u in Ioi (0 : ℝ) ∩ Icc U V, 2 * max (g u) 0 * (u ^ k * Real.exp (-(σ * u)) / k !) ≤
      2 * max C 0 / (σ - θ) ^ (k + 1) := by
    calc ∫ u in Ioi (0 : ℝ) ∩ Icc U V, 2 * max (g u) 0 * (u ^ k * Real.exp (-(σ * u)) / k !)
        ≤ ∫ u in Ioi (0 : ℝ) ∩ Icc U V, 2 * max C 0 * (u ^ k * Real.exp (-((σ - θ) * u)) / k !) := by
          refine setIntegral_mono_on (hint_pos.mono_set inter_subset_left) (hk2.mono_set inter_subset_left)
            (measurableSet_Ioi.inter measurableSet_Icc) fun u hu => ?_
          have hu0 : 0 < u := hu.1
          have hmax : max (g u) 0 ≤ max C 0 * Real.exp (θ * u) :=
            max_le ((hW u hu.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
              (by positivity)
          calc 2 * max (g u) 0 * (u ^ k * Real.exp (-(σ * u)) / k !)
              ≤ 2 * (max C 0 * Real.exp (θ * u)) * (u ^ k * Real.exp (-(σ * u)) / k !) := by gcongr
            _ = 2 * max C 0 * (u ^ k * Real.exp (-((σ - θ) * u)) / k !) := by
                rw [show -((σ - θ) * u) = θ * u + -(σ * u) by ring, Real.exp_add]; ring
      _ ≤ ∫ u in Ioi (0 : ℝ), 2 * max C 0 * (u ^ k * Real.exp (-((σ - θ) * u)) / k !) := by
          refine setIntegral_mono_set hk2 ?_ inter_subset_left.eventuallyLE
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
          positivity
      _ = 2 * max C 0 / (σ - θ) ^ (k + 1) := by
          rw [integral_const_mul, kernel_integral k hb']; ring
  -- outside it `g⁺ ≤ |g| ≤ C₀ e^{au}`
  have htail : ∫ u in Ioi (0 : ℝ) \ Icc U V, 2 * max (g u) 0 * (u ^ k * Real.exp (-(σ * u)) / k !) ≤
      2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp (-((σ - a) * u)) / k ! := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hint_pos.mono_set sdiff_subset)
      (IntegrableOn.mono_set (hkint.const_mul (2 * C₀)) sdiff_subset) (measurableSet_Ioi.diff measurableSet_Icc)
      fun u hu => ?_
    have hu0 : 0 < u := hu.1
    have hK : 0 ≤ u ^ k * Real.exp (-(σ * u)) / k ! := by positivity
    have hm : max (g u) 0 ≤ |g u| := max_le (le_abs_self _) (abs_nonneg _)
    calc 2 * max (g u) 0 * (u ^ k * Real.exp (-(σ * u)) / k !)
        ≤ 2 * (|g u| * (u ^ k * Real.exp (-(σ * u)) / k !)) := by
          rw [mul_assoc]; gcongr
      _ ≤ 2 * (C₀ * (u ^ k * Real.exp (-((σ - a) * u)) / k !)) :=
          mul_le_mul_of_nonneg_left (hdom u hu0.le) (by norm_num)
      _ = 2 * C₀ * (u ^ k * Real.exp (-((σ - a) * u)) / k !) := by ring
  exact hsum.trans (add_le_add hwin htail)

/-! ## Rates -/

/-- A term decaying at a rate `e' ≥ e > 0` is at most `|B| e^{−k}`. -/
theorem div_pow_le_abs_div_pow {B e e' : ℝ} (he : 0 < e) (hee : e ≤ e') (k : ℕ) :
    B / e' ^ k ≤ |B| / e ^ k := by
  have h1 : 0 < e ^ k := pow_pos he k
  have h2 : e ^ k ≤ e' ^ k := pow_le_pow_left₀ he.le hee k
  calc B / e' ^ k ≤ |B| / e' ^ k := div_le_div_of_nonneg_right (le_abs_self B) (h1.trans_le h2).le
    _ ≤ |B| / e ^ k := div_le_div_of_nonneg_left (abs_nonneg B) h1 h2

/-- **Rates**: `A d^{−k} ≤ B e^{−k}` for arbitrarily large `k`, with `A > 0` and `0 < d < e`, is impossible. -/
theorem false_of_rate {A B d e : ℝ} (hA : 0 < A) (hd : 0 < d) (hde : d < e)
    (h : ∀ K : ℕ, ∃ k ≥ K, A / d ^ k ≤ B / e ^ k) : False := by
  have he : 0 < e := hd.trans hde
  have hlim : Filter.Tendsto (fun k : ℕ => B * (d / e) ^ k) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hd he).le ((div_lt_one he).2 hde)).const_mul B
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds hA))
  obtain ⟨k, hk, hle⟩ := h K
  have hdk : 0 < d ^ k := pow_pos hd k
  have : A ≤ B * (d / e) ^ k := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos he k)]
    rw [div_le_div_iff₀ hdk (pow_pos he k)] at hle
    linarith
  exact absurd (hK k hk) (not_lt.2 this)

/-! ## The theorem -/

/-- **Landau's theorem on windows**: a bound `g ≤ C e^{θu}` on windows `[U, λU]` for arbitrarily large `U`
leaves no pole right of `θ`. -/
theorem re_le_of_windows {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} {a : ℝ} (hP : PoleData g Φ Z a)
    {θ lam C : ℝ} (hθ : 0 < θ) (hlam : 1 < lam)
    (hW : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U (lam * U), g u ≤ C * Real.exp (θ * u)) :
    ∀ ρ ∈ Z, ρ.re ≤ θ := by
  intro ρ₀ h₀
  by_contra hlt'
  have hlt : θ < ρ₀.re := not_le.1 hlt'
  -- a nonnegative growth exponent
  obtain ⟨C₀, hC₀⟩ := hP.growth
  have hC₀0 : 0 ≤ C₀ := by
    have h := (abs_nonneg (g 0)).trans (hC₀ 0 le_rfl)
    rwa [mul_zero, Real.exp_zero, mul_one] at h
  set a' := max a 0 with ha'
  have hC₀' : ∀ u, 0 ≤ u → |g u| ≤ C₀ * Real.exp (a' * u) := fun u hu =>
    (hC₀ u hu).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)) hC₀0)
  obtain ⟨σ, hσa, hσ1, E, hE0, hEθ, CT, hchoice⟩ := window_choice (θ := θ) (le_max_right a 0) hlam
  have hθσ : θ < σ := by linarith [hP.re_lt_one ρ₀ h₀]
  have hZσ : ∀ ρ ∈ Z, ρ.re < σ := fun ρ hρ => (hP.re_lt_one ρ hρ).trans hσ1
  -- right of `a'` the moments are the Taylor coefficients
  have hTaylor : ∀ z : ℂ, z.re = σ → ∀ k : ℕ, (-1) ^ k * iteratedDeriv k Φ z / (k ! : ℂ) = moment g k z := by
    intro z hz k
    have hΦ' : ∀ s : ℂ, a' < s.re → Φ s = laplace g s := fun s hs =>
      hP.laplace_eq s (lt_of_le_of_lt (le_max_left _ _) hs)
    have h := iteratedDeriv_eq_moment hP.measurable hC₀' hΦ' (by rw [hz]; linarith) k
    rw [mul_div_assoc, h, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  -- the window estimate, at a `k` past any bound
  set B₀ := 2 * max C 0 / (σ - θ) with hB₀
  have hkey : ∀ K : ℕ, ∃ k ≥ K, ∀ γ : ℝ,
      ‖moment g k (σ + γ * I)‖ + (moment g k σ).re ≤ B₀ / (σ - θ) ^ k + 2 * C₀ * CT / E ^ k := by
    intro K
    obtain ⟨U, hUK, hU⟩ := hW (max K 1)
    obtain ⟨k, hUk, htail⟩ := hchoice U ((le_max_right _ _).trans hUK)
    refine ⟨k, by exact_mod_cast ((le_max_left _ _).trans hUK).trans hUk, fun γ => ?_⟩
    have h := window_estimate hP.measurable hC₀' (by linarith : a' < σ) hθσ hU k γ
    have hθ' : 0 < σ - θ := by linarith
    calc _ ≤ _ := h
      _ ≤ 2 * max C 0 / (σ - θ) ^ (k + 1) + 2 * C₀ * (CT / E ^ k) := by gcongr
      _ = B₀ / (σ - θ) ^ k + 2 * C₀ * CT / E ^ k := by
          rw [hB₀, pow_succ]; field_simp
  -- the points of the half-plane near the line `Re s = σ`
  have hdiff : ∀ w : ℂ, θ < w.re → w ∉ Z → DifferentiableAt ℂ Φ w := fun w hw hwZ =>
    hP.differentiableAt w (hθ.trans hw) hwZ
  have hre_ball : ∀ {z w : ℂ} {r : ℝ}, z.re = σ → r ≤ σ - θ → w ∈ ball z r → θ < w.re := by
    intro z w r hz hr hw
    have := (abs_re_le_norm (w - z)).trans_lt (mem_ball_iff_norm.1 hw)
    rw [sub_re, hz] at this
    linarith [neg_abs_le (w.re - σ)]
  rcases nearest_pole hP.isolated hθ hZσ h₀ hlt with
    ⟨D, hDθ, hD, γ, p, hpZ, r, hpr, hrD, huniq⟩ | ⟨β, hβZ, hθβ, r, hβr, hrθ, huniq⟩
  · -- (a): the pole `p` nearest to `z = σ + iγ` is nearer than every pole is to `σ`
    set z : ℂ := σ + γ * I with hz
    have hzre : z.re = σ := by simp [hz]
    have hpz : p ≠ z := fun e => by have := hZσ p hpZ; rw [e, hzre] at this; exact lt_irrefl _ this
    set d := ‖z - p‖ with hd
    have hd0 : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hpz.symm)
    obtain ⟨c, hc0, -, hpole⟩ := hP.pole p hpZ
    have hΦz : DifferentiableOn ℂ Φ (ball z r \ {p}) := fun w hw =>
      (hdiff w (hre_ball hzre (hrD.trans hDθ) hw.1) fun hwZ => hw.2 (huniq w hwZ
        (by rw [← mem_ball_iff_norm']; exact hw.1))).differentiableWithinAt
    obtain ⟨r₁, hdr₁, hr₁r⟩ : ∃ r₁, d < r₁ ∧ r₁ < r := ⟨(d + r) / 2, by linarith, by linarith⟩
    obtain ⟨M, hM⟩ := pole_asymptotic hpz hΦz hpole (r' := r₁) (by linarith) hr₁r
    have hΦσ : DifferentiableOn ℂ Φ (ball (σ : ℂ) D) := fun w hw =>
      (hdiff w (hre_ball (by simp) hDθ hw) fun hwZ => by
        have := hD w hwZ
        rw [mem_ball_iff_norm'] at hw
        linarith).differentiableWithinAt
    obtain ⟨D₁, hdD₁, hD₁D⟩ : ∃ D₁, d < D₁ ∧ D₁ < D := ⟨(d + D) / 2, by linarith, by linarith⟩
    obtain ⟨M', hM'⟩ := taylor_bound hΦσ (r' := D₁) (by linarith) hD₁D
    set e := min (min r₁ D₁) (min (σ - θ) E) with he
    have he0 : 0 < e := by
      simp only [he, lt_min_iff]; refine ⟨⟨by linarith, by linarith⟩, by linarith, hE0⟩
    refine false_of_rate (A := ‖c‖ / d) (d := d) (e := e)
      (B := |M| + |M'| + |B₀| + |2 * C₀ * CT|) (div_pos (norm_pos_iff.2 hc0) hd0) hd0 ?_ fun K => ?_
    · simp only [he, lt_min_iff]
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    obtain ⟨k, hk, hkey'⟩ := hkey K
    refine ⟨k, hk, ?_⟩
    -- the pole's term in `M_k(z)`, and `M_k(σ)` bounded
    have h1 : ‖c‖ / d ^ (k + 1) - M / r₁ ^ k ≤ ‖moment g k z‖ := by
      have := hM k
      rw [hTaylor z hzre k] at this
      have hn : ‖c / (z - p) ^ (k + 1)‖ = ‖c‖ / d ^ (k + 1) := by rw [norm_div, norm_pow]
      linarith [norm_sub_norm_le (c / (z - p) ^ (k + 1)) (moment g k z), norm_sub_rev (moment g k z)
        (c / (z - p) ^ (k + 1))]
    have h2 : -(M' / D₁ ^ k) ≤ (moment g k σ).re := by
      have := hM' k
      have hm : ‖moment g k σ‖ = ‖iteratedDeriv k Φ σ / (k ! : ℂ)‖ := by
        rw [← hTaylor σ (by simp) k, mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      linarith [neg_abs_le (moment g k σ).re, abs_re_le_norm (moment g k σ)]
    have h3 := hkey' γ
    have hsplit : ‖c‖ / d / d ^ k = ‖c‖ / d ^ (k + 1) := by rw [pow_succ]; field_simp
    rw [hsplit]
    have hmin1 : e ≤ min r₁ D₁ := min_le_left _ _
    have hmin2 : e ≤ min (σ - θ) E := min_le_right _ _
    have t1 := div_pow_le_abs_div_pow (B := M) he0 ((hmin1.trans (min_le_left _ _))) k
    have t2 := div_pow_le_abs_div_pow (B := M') he0 ((hmin1.trans (min_le_right _ _))) k
    have t3 := div_pow_le_abs_div_pow (B := B₀) he0 ((hmin2.trans (min_le_left _ _))) k
    have t4 := div_pow_le_abs_div_pow (B := 2 * C₀ * CT) he0 ((hmin2.trans (min_le_right _ _))) k
    have hsum : (|M| + |M'| + |B₀| + |2 * C₀ * CT|) / e ^ k
        = |M| / e ^ k + |M'| / e ^ k + |B₀| / e ^ k + |2 * C₀ * CT| / e ^ k := by ring
    rw [hsum]
    linarith
  · -- (b): a real pole `β > θ`, the only one near `σ`, with residue of positive real part
    have hβσ : β < σ := by have := hZσ _ hβZ; simpa using this
    obtain ⟨c, -, hcre, hpole⟩ := hP.pole _ hβZ
    have hc : 0 < c.re := hcre (by simp)
    have hpz : (β : ℂ) ≠ σ := fun e => by have := congrArg re e; simp at this; linarith
    have hΦσ : DifferentiableOn ℂ Φ (ball (σ : ℂ) r \ {(β : ℂ)}) := fun w hw =>
      (hdiff w (hre_ball (by simp) hrθ hw.1) fun hwZ => hw.2 (huniq w hwZ
        (by rw [← mem_ball_iff_norm']; exact hw.1))).differentiableWithinAt
    set d := σ - β with hd
    have hd0 : 0 < d := by linarith
    obtain ⟨r₁, hdr₁, hr₁r⟩ : ∃ r₁, d < r₁ ∧ r₁ < r := ⟨(d + r) / 2, by linarith, by linarith⟩
    obtain ⟨M, hM⟩ := pole_asymptotic hpz hΦσ hpole (r' := r₁) (by linarith) hr₁r
    set e := min r₁ (min (σ - θ) E) with he
    have he0 : 0 < e := by simp only [he, lt_min_iff]; refine ⟨by linarith, by linarith, hE0⟩
    refine false_of_rate (A := 2 * c.re / d) (d := d) (e := e) (B := 2 * |M| + |B₀| + |2 * C₀ * CT|)
      (div_pos (by linarith) hd0) hd0 ?_ fun K => ?_
    · simp only [he, lt_min_iff]; refine ⟨by linarith, by linarith, by linarith⟩
    obtain ⟨k, hk, hkey'⟩ := hkey K
    refine ⟨k, hk, ?_⟩
    have hdk : 0 < d ^ (k + 1) := pow_pos hd0 _
    -- `Re M_k(σ) ≥ Re c / d^{k+1} − M/r'^k`
    have h1 : c.re / d ^ (k + 1) - M / r₁ ^ k ≤ (moment g k σ).re := by
      have h := hM k
      rw [hTaylor σ (by simp) k] at h
      have hw : (c / ((σ : ℂ) - β) ^ (k + 1)).re = c.re / d ^ (k + 1) := by
        rw [← ofReal_sub, ← hd, ← ofReal_pow, div_ofReal_re]
      have hre := re_le_norm (c / ((σ : ℂ) - β) ^ (k + 1) - moment g k σ)
      rw [norm_sub_rev, sub_re, hw] at hre
      linarith
    have h3 := hkey' 0
    rw [ofReal_zero, zero_mul, add_zero] at h3
    have h4 : (moment g k σ).re ≤ ‖moment g k σ‖ := re_le_norm _
    have hsplit : 2 * c.re / d / d ^ k = 2 * (c.re / d ^ (k + 1)) := by rw [pow_succ]; field_simp
    rw [hsplit]
    have t1 := div_pow_le_abs_div_pow (B := M) he0 (min_le_left _ _) k
    have t3 := div_pow_le_abs_div_pow (B := B₀) he0 ((min_le_right _ _).trans (min_le_left _ _)) k
    have t4 := div_pow_le_abs_div_pow (B := 2 * C₀ * CT) he0 ((min_le_right _ _).trans (min_le_right _ _)) k
    have hsum : (2 * |M| + |B₀| + |2 * C₀ * CT|) / e ^ k = 2 * (|M| / e ^ k) + |B₀| / e ^ k +
        |2 * C₀ * CT| / e ^ k := by ring
    rw [hsum]
    linarith

end LandauWindow

#print axioms LandauWindow.re_le_of_windows
