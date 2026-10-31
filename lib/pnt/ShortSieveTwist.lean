import ChiPNT
import DirMean

/-!
# A twisted prime number theorem with a power saving

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For every `κ < 1/50` and `A > 0`, uniformly in `N^κ ≤ |t| ≤ N^A` and `N ≤ M ≤ 2N`,
`Σ_{N < n ≤ M} Λ(n) n^{−it} = O(N^{1−κ})` (`norm_sum_Ioc_le_of`) and `Σ_{N < p ≤ M} p^{−it} = O(N^{1−κ})`, the
Dirichlet polynomial `DirMean.dp` of the primes with coefficient `1` (`norm_dp_primes_Ioc_le_of`). There is no
hypothesis: the only analytic input is the half-plane `Re s > 11/12` free of zeros of `ζ`
(`Eis.ne_zero_of_re_gt_eleven_twelfths`), through the log-derivative bound `HalfPlanePNT.logDeriv_le_of_zeroFree`.

The Dirichlet series of `Λ(n)n^{−it}` is `−ζ′/ζ(s + it)` (`LSeries_twist_eq`), holomorphic on `Re s > 11/12` but for a
simple pole of residue `1` at `s = 1 − it` (`isBigO_logDerivTwist`, from PNT+'s `riemannZetaLogDerivResidueBigO`).
The smoothed Perron integral (`SmoothPerron`) is moved from `Re s = 2` to `Re s = 23/24`, past the pole, which leaves
the residue `𝓜(Smooth1)(1 − it)X^{1−it}`, of size `O(X/(1 + |t|))`: small once `|t| ≥ N^κ`. On the line
`|ζ′/ζ(23/24 + iu)| ≤ M + C log(1 + |u|)`, so the integral is `O(ε^{−1/2}X^{23/24} log(2 + |t|))`, where
`log|t| = O(log N)` when `|t| ≤ N^A`; the smoothing costs `O(εX log X)`, and `ε = X^{−1/24}`.

* `verticalIntegral_sub_eq`: `∫_{(σ)} G − ∫_{(σ′)} G = 2πiA` for `G` with a simple pole of residue `A` in the strip
  `σ′ < Re s < σ`: `SmoothPerron.verticalIntegral_shift` with the rectangle integral `2πiA` (PNT+'s
  `ResidueTheoremOnRectangleWithSimplePole'`) once the rectangle holds the pole.
* `verticalIntegral'_integrand_eq`, `smoothedSum_eq_verticalIntegral_add`: the Perron integral and the smoothed sum
  moved left of a simple pole `p` of residue `r` of `L(f, s)`, which leaves `r 𝓜(Smooth1)(p) X^p` (`isBigO_mul_sub`:
  the residue of `L(s)𝓜(Smooth1)(s)X^s`); the counterparts of `SmoothPerron.verticalIntegral_integrand_shift` and
  `SmoothPerron.smoothedSum_eq_verticalIntegral_left`.
* `norm_psi_twist_le`: `|Σ_{n ≤ X} Λ(n)n^{−it}| ≤ K₁X/(1 + |t|) + K₂(1 + log(1 + |t|))X^{49/50}` for every `X > 1` and
  every real `t`: the residue through `SmoothPerron.mellin_le_geom` at `κ = 0`, the integral on `Re s = 23/24`
  through `mellin_le_geom` at `κ = 1/2` and `logDeriv_bounds`, and the unsmoothing
  `SmoothPerron.norm_smoothedSum_sub_le`.
* `norm_sum_Ioc_le_of`: `|Σ_{N < n ≤ m} Λ(n)n^{−it}| ≤ C N^{1−κ}` for `κ < 1/50`, `N ≤ m ≤ 2N` and
  `N^κ ≤ |t| ≤ N^A`, the difference of `norm_psi_twist_le` at `X = m` and `X = N`: there `X/(1 + |t|) ≤ 2N^{1−κ}`,
  and `log(1 + |t|) = O(N^{1/50−κ})` against `X^{49/50}`.
* `norm_dp_primes_Ioc_le_of`: Abel summation with the weights `1/log n` (`norm_sum_mul_le`) over the partial sums of
  `Λ(p)p^{−it}` on the primes, which are those of `norm_sum_Ioc_le_of` up to the prime powers; these contribute at
  most `ψ(2N) − θ(2N) = O(N^{3/4})` (`sum_not_prime_le_rpow`, from Mathlib's `Chebyshev.psi_sub_theta_le`).
-/

set_option lang.lemmaCmd true

open Complex Set Real Filter Topology MeasureTheory Asymptotics

local notation (name := mellintransform7) "𝓜" => mellin

namespace ShortSieveTwist

open SmoothPerron

/-! ### Moving the line past a simple pole -/

/-- **Moving the line of integration past a simple pole.** If `G` is holomorphic on the closed strip
`σ' ≤ Re s ≤ σ` except at a point `p` of the open strip, where `G(s) − A/(s − p)` stays bounded, integrable on
both lines, and tends to `0` uniformly on the strip as `|Im s| → ∞`, then `∫_{(σ)} G − ∫_{(σ')} G = 2πiA`. -/
theorem verticalIntegral_sub_eq {G : ℂ → ℂ} {σ' σ : ℝ} {p A : ℂ} (hσ'p : σ' < p.re) (hpσ : p.re < σ)
    (hG : HolomorphicOn G ((Icc σ' σ ×ℂ univ) \ {p}))
    (hp : (G - fun s ↦ A / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hint : Integrable fun t : ℝ ↦ G (σ + t * I)) (hint' : Integrable fun t : ℝ ↦ G (σ' + t * I))
    (hdecay : ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc σ' σ, ∀ y : ℝ, T₀ ≤ |y| → ‖G (x + y * I)‖ ≤ η) :
    VerticalIntegral G σ - VerticalIntegral G σ' = 2 * π * I * A := by
  have hσ : σ' ≤ σ := by linarith
  have hdiff : ∀ T : ℝ, |p.im| < T → VerticalIntegral G σ - VerticalIntegral G σ' - 2 * π * I * A =
      UpperUIntegral G σ' σ T - LowerUIntegral G σ' σ T := by
    intro T hT
    have h := DiffVertRect_eq_UpperLowerUs (f := G) (σ := σ') (σ' := σ) (T := T) hint' hint
    have hpT := abs_lt.1 hT
    have hzw_re : ((σ' : ℂ) - I * T).re ≤ ((σ : ℂ) + I * T).re := by simp; linarith
    have hzw_im : ((σ' : ℂ) - I * T).im ≤ ((σ : ℂ) + I * T).im := by simp; linarith
    have hres := ResidueTheoremOnRectangleWithSimplePole' (f := G) (A := A) hzw_re hzw_im ?_ ?_ hp
    · have hR : RectangleIntegral G (σ' - I * T) (σ + I * T) = 2 * π * I * A := by
        rw [RectangleIntegral', smul_eq_mul] at hres
        have hπ : (2 * π * I : ℂ) ≠ 0 := by
          simp [Real.pi_ne_zero, I_ne_zero]
        rw [← hres]
        field_simp
      rw [hR] at h
      exact h
    · rw [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le hzw_re, uIoo_of_le hzw_im]
      simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, mul_zero, I_im, zero_mul, sub_zero, add_re,
        add_zero, sub_im, mul_im, one_mul, zero_sub, add_im, zero_add, mem_Ioo]
      exact ⟨⟨hσ'p, hpσ⟩, by linarith, by linarith⟩
    · refine hG.mono fun z hz ↦ ⟨?_, hz.2⟩
      have h1 := hz.1
      rw [Rectangle, mem_reProdIm] at h1
      rw [mem_reProdIm]
      refine ⟨?_, mem_univ _⟩
      have h2 := h1.1
      simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, sub_zero,
        mul_zero, add_re, add_zero] at h2
      rwa [uIcc_of_le hσ] at h2
  have habs : Tendsto (fun T : ℝ ↦ |T|) atTop atTop :=
    tendsto_abs_atTop_atTop.comp tendsto_id
  have habs' : Tendsto (fun T : ℝ ↦ |-T|) atTop atTop := by
    simpa only [abs_neg] using habs
  have hU : Tendsto (fun T ↦ UpperUIntegral G σ' σ T) atTop (𝓝 0) := by
    have := ((tendsto_HIntegral hσ hdecay habs).add ((tendsto_integral_Ici hint).const_smul I)).sub
      ((tendsto_integral_Ici hint').const_smul I)
    simpa [UpperUIntegral] using this
  have hL : Tendsto (fun T ↦ LowerUIntegral G σ' σ T) atTop (𝓝 0) := by
    have := ((tendsto_HIntegral hσ hdecay habs').sub ((tendsto_integral_Iic_neg hint).const_smul I)).add
      ((tendsto_integral_Iic_neg hint').const_smul I)
    simpa [LowerUIntegral] using this
  have hlim := hU.sub hL
  rw [sub_zero] at hlim
  have hconst : Tendsto (fun T ↦ UpperUIntegral G σ' σ T - LowerUIntegral G σ' σ T) atTop
      (𝓝 (VerticalIntegral G σ - VerticalIntegral G σ' - 2 * π * I * A)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop |p.im|] with T hT
    exact hdiff T hT
  exact sub_eq_zero.1 (tendsto_nhds_unique hconst hlim)

/-- If `L(s) − r/(s − p)` is bounded near `p` and `h` is differentiable at `p`, then
`L(s)h(s) − r h(p)/(s − p)` is bounded near `p`. -/
lemma isBigO_mul_sub {L h : ℂ → ℂ} {p r : ℂ} (hL : (L - fun s ↦ r / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hh : DifferentiableAt ℂ h p) :
    ((fun s ↦ L s * h s) - fun s ↦ r * h p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have e : ((fun s ↦ L s * h s) - fun s ↦ r * h p / (s - p)) =ᶠ[𝓝[≠] p]
      fun s ↦ (L - fun s ↦ r / (s - p)) s * h s + r * slope h p s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s - p ≠ 0 := sub_ne_zero.2 hs
    simp only [Pi.sub_apply, slope_def_module, smul_eq_mul]
    field_simp
    ring
  refine IsBigO.congr' ?_ e.symm EventuallyEq.rfl
  have h1 : h =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have h2 : slope h p =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (hasDerivAt_iff_tendsto_slope.1 hh.hasDerivAt).isBigO_one ℂ
  have h4 := hL.mul h1
  have e1 : (fun x : ℂ ↦ (1 : ℂ → ℂ) x * (1 : ℂ → ℂ) x) = (1 : ℂ → ℂ) := by
    funext x; simp
  rw [e1] at h4
  exact h4.add (h2.const_mul_left r)

variable {ν : ℝ → ℝ}

/-- **Moving the Perron integral past a simple pole.** Let `L` be holomorphic on `Re s ≥ σ′` (`σ′ > 0`) except
for a simple pole at `p`, `σ′ < Re p < 2`, with `L(s) − r/(s − p)` bounded near `p`; bounded by `B` on `Re s = 2`
and of at most linear growth `|L(σ + it)| ≤ C|t|` on `σ′ ≤ σ ≤ 2`, `|t| ≥ T`. Then for `0 < ε < 1`, `X ≥ 1`, and
the integrand integrable on `Re s = σ′`: `(1/2πi)∫_{(2)} L 𝓜(Smooth1) X^s ds = (1/2πi)∫_{(σ′)} L 𝓜(Smooth1) X^s ds
+ r 𝓜(Smooth1)(p) X^p`. -/
theorem verticalIntegral'_integrand_eq {L : ℂ → ℂ} {σ' : ℝ} {p r : ℂ} (hσ'0 : 0 < σ') (hσ'p : σ' < p.re)
    (hp2 : p.re < 2) (hLd : ∀ s : ℂ, σ' ≤ s.re → s ≠ p → DifferentiableAt ℂ L s)
    (hLp : (L - fun s ↦ r / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) {B : ℝ}
    (hB : ∀ t : ℝ, ‖L ((2 : ℝ) + t * I)‖ ≤ B)
    {T C : ℝ} (hgrowth : ∀ σ t : ℝ, σ' ≤ σ → σ ≤ 2 → T ≤ |t| → ‖L (σ + t * I)‖ ≤ C * |t|)
    (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {X : ℝ} (hX : 1 ≤ X) (hint' : Integrable fun t : ℝ ↦ integrand ν ε X L (σ' + t * I)) :
    VerticalIntegral' (integrand ν ε X L) 2 =
      VerticalIntegral' (integrand ν ε X L) σ' + r * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) p * (X : ℂ) ^ p := by
  have Xpos : 0 < X := by linarith
  set h : ℂ → ℂ := fun s ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s with hhdef
  have hhd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ h s := fun s hs ↦
    (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩ νnonneg mass_one hs).mul
      ((differentiableAt_id).const_cpow (Or.inl (ofReal_ne_zero.2 Xpos.ne')))
  have hGe : integrand ν ε X L = fun s ↦ L s * h s := by
    funext s; simp only [integrand, hhdef, mul_assoc]
  have hcont2 : Continuous fun t : ℝ ↦ L ((2 : ℝ) + t * I) := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    have hs : ((2 : ℝ) + t * I : ℂ) ≠ p := fun h ↦ by
      have := congrArg Complex.re h
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith
    have hre : σ' ≤ ((2 : ℝ) + t * I : ℂ).re := by simp; linarith
    exact (hLd _ hre hs).continuousAt.comp (f := fun t : ℝ ↦ ((2 : ℝ) : ℂ) + t * I) (by fun_prop)
  obtain ⟨C₂, C₂pos, hC₂⟩ := MellinOfSmooth1b diffν suppν
  have key := verticalIntegral_sub_eq (G := integrand ν ε X L) (A := r * h p) hσ'p hp2 ?_ ?_ ?_ hint' ?_
  · have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have h2 := eq_add_of_sub_eq' key
    simp only [VerticalIntegral', smul_eq_mul]
    rw [h2, mul_add]
    congr 1
    simp only [hhdef]
    field_simp
  · -- holomorphy off the pole
    intro s hs
    have hre : σ' ≤ s.re := (mem_reProdIm.1 hs.1).1.1
    have hsp : s ≠ p := hs.2
    rw [hGe]
    exact ((hLd s hre hsp).mul (hhd s (by linarith))).differentiableWithinAt
  · -- the residue
    rw [hGe]
    exact isBigO_mul_sub hLp (hhd p (by linarith))
  · -- integrable on `Re s = 2`
    have hM2 : Integrable fun t : ℝ ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I) :=
      SmoothedChebyshevDirichlet_aux_integrable diffν νnonneg suppν mass_one εpos ε_lt_one
        (by norm_num) le_rfl
    refine Integrable.mono' (hM2.norm.const_mul (B * X ^ (2 : ℝ)))
      (continuous_integrand_line (by norm_num) hcont2 diffν νnonneg suppν mass_one εpos ε_lt_one
        Xpos).aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
    rw [norm_integrand Xpos]
    have hre : ((2 : ℝ) + t * I : ℂ).re = 2 := by simp
    rw [hre]
    calc ‖L ((2 : ℝ) + t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I)‖ * X ^ (2 : ℝ)
        ≤ B * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((2 : ℝ) + t * I)‖ * X ^ (2 : ℝ) := by
          gcongr
          exact hB t
      _ = _ := by ring
  · -- decay on horizontal segments
    intro η hη
    set A : ℝ := max C 0 * C₂ * X ^ (2 : ℝ) / ε with hAdef
    have hA : 0 ≤ A := by positivity
    refine ⟨max (max T 1) (A / η), fun x hx y hy ↦ ?_⟩
    have hy1 : 1 ≤ |y| := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
    have hyT : T ≤ |y| := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
    have hyA : A / η ≤ |y| := (le_max_right _ _).trans hy
    have hy0 : 0 < |y| := by linarith
    set s : ℂ := x + y * I with hsdef
    have hsre : s.re = x := by simp [hsdef]
    have hsim : s.im = y := by simp [hsdef]
    have hsy : |y| ≤ ‖s‖ := by have := Complex.abs_im_le_norm s; rwa [hsim] at this
    rw [norm_integrand Xpos, hsre]
    have hL' : ‖L s‖ ≤ max C 0 * |y| :=
      (hgrowth x y hx.1 hx.2 hyT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0.le)
    have hM' : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C₂ * (ε * |y| ^ 2)⁻¹ := by
      refine (hC₂ σ' hσ'0 s (by rw [hsre]; exact hx.1) (by rw [hsre]; exact hx.2) ε εpos
        ε_lt_one).trans ?_
      gcongr
    have hXx : X ^ x ≤ X ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hx.2
    calc ‖L s‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ * X ^ x
        ≤ (max C 0 * |y|) * (C₂ * (ε * |y| ^ 2)⁻¹) * X ^ (2 : ℝ) := by gcongr
      _ = A / |y| := by
        rw [hAdef]
        field_simp
      _ ≤ η := by
        rw [div_le_iff₀ hy0]
        rw [div_le_iff₀ hη] at hyA
        linarith

/-- **The smoothed sum as an integral on a line left of a simple pole.** Let `L(f, s) = L(s)` on `Re s > 1`, with
`L(f, 2)` absolutely convergent, and `L` as in `verticalIntegral'_integrand_eq`, with its simple pole at `p`,
`σ′ < Re p < 2`, of residue `r`. Then for `0 < ε < 1`, `X ≥ 1`, and the integrand integrable on `Re s = σ′`:
`Σ_n f(n) Smooth1(n/X) = (1/2πi)∫_{(σ′)} L(s) 𝓜(Smooth1)(s) X^s ds + r 𝓜(Smooth1)(p) X^p`. -/
theorem smoothedSum_eq_verticalIntegral_add {f : ℕ → ℂ} (hf0 : f 0 = 0)
    (hf : LSeriesSummable f ((2 : ℝ) : ℂ)) {L : ℂ → ℂ} (hL : ∀ s : ℂ, 1 < s.re → LSeries f s = L s)
    {σ' : ℝ} {p r : ℂ} (hσ'0 : 0 < σ') (hσ'p : σ' < p.re) (hp2 : p.re < 2)
    (hLd : ∀ s : ℂ, σ' ≤ s.re → s ≠ p → DifferentiableAt ℂ L s)
    (hLp : (L - fun s ↦ r / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    {T C : ℝ} (hgrowth : ∀ σ t : ℝ, σ' ≤ σ → σ ≤ 2 → T ≤ |t| → ‖L (σ + t * I)‖ ≤ C * |t|)
    (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {X : ℝ} (hX : 1 ≤ X) (hint' : Integrable fun t : ℝ ↦ integrand ν ε X L (σ' + t * I)) :
    smoothedSum ν ε X f =
      VerticalIntegral' (integrand ν ε X L) σ' + r * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) p * (X : ℂ) ^ p := by
  have Xpos : 0 < X := by linarith
  rw [← verticalIntegral_eq_smoothedSum hf0 diffν νnonneg suppν mass_one εpos ε_lt_one Xpos
    (by norm_num : (1 : ℝ) < 2) le_rfl hf]
  have hline : VerticalIntegral' (integrand ν ε X (LSeries f)) 2 =
      VerticalIntegral' (integrand ν ε X L) 2 := by
    simp only [VerticalIntegral', VerticalIntegral]
    congr 3
    funext t
    simp only [integrand]
    rw [hL _ (by simp)]
  rw [hline]
  refine verticalIntegral'_integrand_eq hσ'0 hσ'p hp2 hLd hLp (B := ∑' n, ‖LSeries.term f (2 : ℝ) n‖)
    (fun t ↦ ?_) hgrowth diffν νnonneg suppν mass_one εpos ε_lt_one hX hint'
  have hre : ((2 : ℝ) + t * I : ℂ).re = 2 := by simp
  rw [← hL _ (by rw [hre]; norm_num)]
  exact norm_LSeries_le_of_le_re hf (by rw [hre])

/-! ### The twisted log-derivative -/

/-- `−ζ′/ζ(s + it)`, the Dirichlet series of `Λ(n)n^{−it}`. -/
noncomputable def logDerivTwist (t : ℝ) (s : ℂ) : ℂ :=
  -(deriv riemannZeta (s + t * I) / riemannZeta (s + t * I))

/-- `ζ′/ζ` is differentiable at every `w ≠ 1` with `Re w > 11/12`. -/
lemma differentiableAt_logDeriv {w : ℂ} (hw : 11 / 12 < w.re) (hw1 : w ≠ 1) :
    DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s / riemannZeta s) w :=
  (differentiableAt_deriv_riemannZeta hw1).div (differentiableAt_riemannZeta hw1)
    (Eis.ne_zero_of_re_gt_eleven_twelfths hw).1

/-- `−ζ′/ζ(s + it)` is differentiable at every `s ≠ 1 − it` with `Re s > 11/12`. -/
lemma differentiableAt_logDerivTwist (t : ℝ) {s : ℂ} (hs : 11 / 12 < s.re) (hs1 : s ≠ 1 - t * I) :
    DifferentiableAt ℂ (logDerivTwist t) s := by
  have hw : 11 / 12 < (s + t * I).re := by simpa using hs
  have hw1 : s + t * I ≠ 1 := fun h ↦ hs1 (by rw [← h]; ring)
  exact ((differentiableAt_logDeriv hw hw1).comp s ((differentiableAt_id).add_const (t * I))).neg

/-- `L(Λ(n)n^{−it}, s) = −ζ′/ζ(s + it)` on `Re s > 1`. -/
lemma LSeries_twist_eq (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I))) s =
      logDerivTwist t s := by
  have e : LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I))) s =
      LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) (s + t * I) := by
    unfold LSeries
    congr 1
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      have h1 : (n : ℂ) ^ s ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hn' h.1
      have h2 : (n : ℂ) ^ ((t : ℂ) * I) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hn' h.1
      rw [cpow_add _ _ hn', cpow_neg]
      field_simp
  rw [e, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs), logDerivTwist,
    neg_div]

/-- `−ζ′/ζ(s + it)` has a simple pole of residue `1` at `s = 1 − it`. -/
lemma isBigO_logDerivTwist (t : ℝ) :
    (logDerivTwist t - fun s ↦ 1 / (s - (1 - t * I))) =O[𝓝[≠] (1 - t * I)] (1 : ℂ → ℂ) := by
  have hτ : Tendsto (fun s : ℂ ↦ s + t * I) (𝓝[≠] (1 - t * I)) (𝓝[≠] 1) := by
    have hc : ContinuousWithinAt (fun s : ℂ ↦ s + t * I) {1 - t * I}ᶜ (1 - t * I) :=
      (by fun_prop : Continuous fun s : ℂ ↦ s + t * I).continuousWithinAt
    have := hc.tendsto_nhdsWithin (t := {1}ᶜ) (fun s hs h ↦ hs (by
      simp only [mem_singleton_iff] at h ⊢
      rw [← h]; ring))
    simpa using this
  have h := riemannZetaLogDerivResidueBigO.comp_tendsto hτ
  refine h.congr' (Eventually.of_forall fun s ↦ ?_) (Eventually.of_forall fun s ↦ ?_)
  · simp only [Function.comp, Pi.sub_apply, Pi.div_apply, Pi.neg_apply, logDerivTwist, neg_div, one_div]
    congr 2
    ring
  · rfl

/-- Bounds on `ζ′/ζ` right of `Re s = 23/24`, from the half-plane `Re s > 11/12`: `|ζ′/ζ(σ + iu)| ≤ C log|u|`
for `σ ≥ 23/24`, `|u| > 3` (`HalfPlanePNT.logDeriv_le_of_zeroFree`), and `|ζ′/ζ(23/24 + iu)| ≤ M + C log(1 + |u|)`
for every `u` (by compactness for `|u| ≤ 3`). -/
lemma logDeriv_bounds : ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧
    (∀ σ u : ℝ, 3 < |u| → 23 / 24 ≤ σ →
      ‖deriv riemannZeta (σ + u * I) / riemannZeta (σ + u * I)‖ ≤ C * Real.log |u|) ∧
    ∀ u : ℝ, ‖deriv riemannZeta ((23 / 24 : ℝ) + u * I) / riemannZeta ((23 / 24 : ℝ) + u * I)‖ ≤
      M + C * Real.log (1 + |u|) := by
  obtain ⟨C, hC, hb⟩ := HalfPlanePNT.logDeriv_le_of_zeroFree (θ := 11 / 12) (θ' := 23 / 24) (by norm_num)
    (by norm_num) (by norm_num) (fun s hs ↦ (Eis.ne_zero_of_re_gt_eleven_twelfths hs).1)
  have hcont : Continuous fun u : ℝ ↦
      deriv riemannZeta ((23 / 24 : ℝ) + u * I) / riemannZeta ((23 / 24 : ℝ) + u * I) := by
    refine continuous_iff_continuousAt.2 fun u ↦ ?_
    have hw : 11 / 12 < (((23 / 24 : ℝ) : ℂ) + u * I).re := by simp; norm_num
    have hw1 : (((23 / 24 : ℝ) : ℂ) + u * I) ≠ 1 := fun h ↦ by
      have := congrArg Complex.re h
      simp at this
      norm_num at this
    exact (differentiableAt_logDeriv hw hw1).continuousAt.comp
      (f := fun u : ℝ ↦ ((23 / 24 : ℝ) : ℂ) + u * I) (by fun_prop)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-3 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨C, max M 0, hC, le_max_right _ _, fun σ u hu hσ ↦ hb σ u hu hσ, fun u ↦ ?_⟩
  have hl : 0 ≤ Real.log (1 + |u|) := Real.log_nonneg (by linarith [abs_nonneg u])
  by_cases h3 : |u| ≤ 3
  · calc _ ≤ M := hM u (abs_le.1 h3)
      _ ≤ max M 0 := le_max_left _ _
      _ ≤ max M 0 + C * Real.log (1 + |u|) := le_add_of_nonneg_right (by positivity)
  · push Not at h3
    calc _ ≤ C * Real.log |u| := hb _ u h3 le_rfl
      _ ≤ C * Real.log (1 + |u|) := by gcongr; linarith
      _ ≤ max M 0 + C * Real.log (1 + |u|) := le_add_of_nonneg_left (le_max_right _ _)

/-- `x + iy + it = x + i(y + t)`. -/
lemma add_mul_I_add (x y t : ℝ) : (x : ℂ) + y * I + t * I = (x : ℂ) + ((y + t : ℝ) : ℂ) * I := by
  push_cast; ring

/-- `|ζ′/ζ(23/24 + i(y + t))| ≤ (M + 4C + C log(1 + |t|))(1 + |y|)^{1/4}`. -/
lemma norm_logDerivTwist_line {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hline : ∀ u : ℝ, ‖deriv riemannZeta ((23 / 24 : ℝ) + u * I) / riemannZeta ((23 / 24 : ℝ) + u * I)‖ ≤
      M + C * Real.log (1 + |u|)) (t y : ℝ) :
    ‖logDerivTwist t ((23 / 24 : ℝ) + y * I)‖ ≤
      (M + 4 * C + C * Real.log (1 + |t|)) * (1 + |y|) ^ (1 / 4 : ℝ) := by
  rw [logDerivTwist, norm_neg, add_mul_I_add]
  have hy1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hr1 : 1 ≤ (1 + |y|) ^ (1 / 4 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
  have hlt : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg ht1
  have h1 : Real.log (1 + |y + t|) ≤ Real.log (1 + |y|) + Real.log (1 + |t|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have := abs_add_le y t
    nlinarith [abs_nonneg y, abs_nonneg t]
  have h2 : Real.log (1 + |y|) ≤ 4 * (1 + |y|) ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div (x := 1 + |y|) (by positivity) (ε := 1 / 4) (by norm_num)
    linarith
  calc _ ≤ M + C * Real.log (1 + |y + t|) := hline (y + t)
    _ ≤ M + C * (4 * (1 + |y|) ^ (1 / 4 : ℝ) + Real.log (1 + |t|)) := by gcongr; linarith
    _ ≤ (M + 4 * C + C * Real.log (1 + |t|)) * (1 + |y|) ^ (1 / 4 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ M + C * Real.log (1 + |t|))
      nlinarith

/-- `|ζ′/ζ(x + i(y + t))| ≤ 2C|y|` for `x ≥ 23/24`, `|y| ≥ |t| + 4`. -/
lemma norm_logDerivTwist_growth {C : ℝ} (hC : 0 < C)
    (hlog : ∀ σ u : ℝ, 3 < |u| → 23 / 24 ≤ σ →
      ‖deriv riemannZeta (σ + u * I) / riemannZeta (σ + u * I)‖ ≤ C * Real.log |u|)
    (t x y : ℝ) (hx : 23 / 24 ≤ x) (hy : |t| + 4 ≤ |y|) :
    ‖logDerivTwist t (x + y * I)‖ ≤ 2 * C * |y| := by
  rw [logDerivTwist, norm_neg, add_mul_I_add]
  have h1 : |y| - |t| ≤ |y + t| := by
    have := abs_sub_abs_le_abs_sub y (-t)
    rwa [abs_neg, sub_neg_eq_add] at this
  have h3 : 3 < |y + t| := by linarith
  have h4 : Real.log |y + t| ≤ 2 * |y| := by
    have := Real.log_le_sub_one_of_pos (show 0 < |y + t| by linarith)
    have := abs_add_le y t
    linarith [abs_nonneg t]
  calc _ ≤ C * Real.log |y + t| := hlog x (y + t) h3 hx
    _ ≤ C * (2 * |y|) := by gcongr
    _ = 2 * C * |y| := by ring

/-! ### The twisted prime number theorem -/

/-- **The twisted prime number theorem, uniformly in the twist.** There are `K₁, K₂` with
`|Σ_{n ≤ X} Λ(n)n^{−it}| ≤ K₁X/(1 + |t|) + K₂(1 + log(1 + |t|))X^{49/50}` for every `X > 1` and every real `t`.
The smoothed Perron integral for `−ζ′/ζ(s + it)` (`smoothedSum_eq_verticalIntegral_add`), moved to
`Re s = 23/24` past the pole at `s = 1 − it`, with smoothing width `ε = X^{−1/24}`: the residue
`𝓜(Smooth1)(1 − it)X^{1−it}` is at most `K₁X/(1 + |t|)` (`mellin_le_geom` at `κ = 0`), the integral at most
`8K(M + 4C + C log(1 + |t|))ε^{−1/2}X^{23/24}` (`mellin_le_geom` at `κ = 1/2` with constant `K`,
`norm_logDerivTwist_line`), and the smoothing costs `log(3X)(3 log 2·εX + 1)` (`norm_smoothedSum_sub_le`). -/
theorem norm_psi_twist_le : ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ X : ℝ, 1 < X → ∀ t : ℝ,
    ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I))‖ ≤
      K₁ * X / (1 + |t|) + K₂ * (1 + Real.log (1 + |t|)) * X ^ (49 / 50 : ℝ) := by
  obtain ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have diffν : ContDiff ℝ 1 ν := ContDiffν.of_le (by simp)
  have νnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have mass_one : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨KM, hKM0, hKM⟩ := mellin_le_geom diffν ν_supp (κ := 1 / 2) (by norm_num) (by norm_num)
    (σ := 23 / 24) (by norm_num) (by norm_num)
  obtain ⟨K₀, hK₀0, hK₀⟩ := mellin_le_geom diffν ν_supp (κ := 0) le_rfl zero_le_one
    (σ := 1) one_pos le_rfl
  obtain ⟨C, M, hC, hM, hlog, hline⟩ := logDeriv_bounds
  refine ⟨K₀, 8 * KM * (M + 5 * C) + 208, hK₀0, by positivity, fun X hX t ↦ ?_⟩
  have Xpos : 0 < X := by linarith
  set f : ℕ → ℂ := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I)) with hfdef
  set ε : ℝ := X ^ (-(1 / 24 : ℝ)) with hεdef
  have εpos : 0 < ε := Real.rpow_pos_of_pos Xpos _
  have ε_lt_one : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg hX (by norm_num)
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hfΛ : ∀ n, ‖f n‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hfdef]
    · rw [hfdef, norm_mul, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  -- the integrand on `Re s = 23/24`
  set Kt : ℝ := M + 4 * C + C * Real.log (1 + |t|) with hKtdef
  have hlt : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hKt0 : 0 ≤ Kt := by positivity
  have hpt : ∀ y : ℝ, ‖integrand ν ε X (logDerivTwist t) ((23 / 24 : ℝ) + y * I)‖ ≤
      Kt * KM * ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ) * (1 + |y|) ^ (-(5 / 4 : ℝ)) := by
    intro y
    rw [norm_integrand Xpos]
    have hre : (((23 / 24 : ℝ) : ℂ) + y * I).re = 23 / 24 := by simp
    rw [hre]
    have h1 := norm_logDerivTwist_line hC hM hline t y
    have h2 := hKM ε εpos ε_lt_one y
    have hpow : (1 + |y|) ^ (1 / 4 : ℝ) * (1 + |y|) ^ (-(1 + 1 / 2 : ℝ)) = (1 + |y|) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add (by positivity)]
      norm_num
    calc ‖logDerivTwist t ((23 / 24 : ℝ) + y * I)‖ *
          ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) ((23 / 24 : ℝ) + y * I)‖ * X ^ (23 / 24 : ℝ)
        ≤ (Kt * (1 + |y|) ^ (1 / 4 : ℝ)) * (KM * ε ^ (-(1 / 2 : ℝ)) * (1 + |y|) ^ (-(1 + 1 / 2 : ℝ))) *
          X ^ (23 / 24 : ℝ) := by gcongr
      _ = Kt * KM * ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ) *
          ((1 + |y|) ^ (1 / 4 : ℝ) * (1 + |y|) ^ (-(1 + 1 / 2 : ℝ))) := by ring
      _ = Kt * KM * ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ) * (1 + |y|) ^ (-(5 / 4 : ℝ)) := by rw [hpow]
  have hIr : Integrable fun y : ℝ ↦ (1 + |y|) ^ (-(5 / 4 : ℝ)) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5 / 4) (by simp; norm_num)
    simpa only [Real.norm_eq_abs] using this
  have hIr8 : ∫ y : ℝ, (1 + |y|) ^ (-(5 / 4 : ℝ)) = 8 := by
    rw [ChiPNT.integral_one_add_abs_rpow (by norm_num)]
    norm_num
  have hcont : Continuous fun y : ℝ ↦ logDerivTwist t ((23 / 24 : ℝ) + y * I) := by
    refine continuous_iff_continuousAt.2 fun y ↦ ?_
    have hre : 11 / 12 < (((23 / 24 : ℝ) : ℂ) + y * I).re := by simp; norm_num
    have hne : (((23 / 24 : ℝ) : ℂ) + y * I) ≠ 1 - t * I := fun h ↦ by
      have := congrArg Complex.re h
      simp at this
      norm_num at this
    exact (differentiableAt_logDerivTwist t hre hne).continuousAt.comp
      (f := fun y : ℝ ↦ ((23 / 24 : ℝ) : ℂ) + y * I) (by fun_prop)
  have hint' : Integrable fun y : ℝ ↦ integrand ν ε X (logDerivTwist t) ((23 / 24 : ℝ) + y * I) :=
    Integrable.mono' (hIr.const_mul (Kt * KM * ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ)))
      (continuous_integrand_line (by norm_num) hcont diffν νnonneg ν_supp mass_one εpos ε_lt_one
        Xpos).aestronglyMeasurable (Eventually.of_forall hpt)
  -- the smoothed sum
  have hid := smoothedSum_eq_verticalIntegral_add (f := f) hf0
    (ChiPNT.LSeriesSummable_of_le_vonMangoldt hfΛ (by norm_num)) (fun s hs ↦ LSeries_twist_eq t hs)
    (σ' := 23 / 24) (p := 1 - t * I) (r := 1) (by norm_num) (by simp; norm_num) (by simp)
    (fun s hs hsp ↦ differentiableAt_logDerivTwist t (by linarith) hsp) (isBigO_logDerivTwist t)
    (T := |t| + 4) (C := 2 * C)
    (fun σ y hσ _ hy ↦ norm_logDerivTwist_growth hC hlog t σ y hσ hy)
    diffν νnonneg ν_supp mass_one εpos ε_lt_one hX.le hint'
  have hvi : ‖VerticalIntegral' (integrand ν ε X (logDerivTwist t)) (23 / 24)‖ ≤
      Kt * KM * ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ) * 8 := by
    calc _ ≤ ∫ y, Kt * KM * ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ) * (1 + |y|) ^ (-(5 / 4 : ℝ)) :=
          norm_verticalIntegral'_le (hIr.const_mul _) hpt
      _ = Kt * KM * ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ) * 8 := by
          rw [integral_const_mul, hIr8]
  have hres : ‖(1 : ℂ) * 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (1 - t * I) * (X : ℂ) ^ (1 - t * I)‖ ≤
      K₀ * X / (1 + |t|) := by
    have e : (1 : ℂ) - t * I = ((1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    have h1 := hK₀ ε εpos ε_lt_one (-t)
    rw [abs_neg, neg_zero, Real.rpow_zero, mul_one, add_zero, Real.rpow_neg_one] at h1
    rw [one_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos Xpos, e]
    have hre : (((1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I).re = 1 := by simp
    rw [hre, Real.rpow_one]
    calc _ ≤ K₀ * (1 + |t|)⁻¹ * X := by gcongr
      _ = K₀ * X / (1 + |t|) := by ring
  have hlog3X : 0 ≤ Real.log (3 * X) := Real.log_nonneg (by linarith)
  have hB : ∀ n : ℕ, (n : ℝ) ≤ 3 * X → ‖f n‖ ≤ Real.log (3 * X) := by
    intro n hn
    refine (hfΛ n).trans (ArithmeticFunction.vonMangoldt_le_log.trans ?_)
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h, hlog3X]
    · exact Real.log_le_log (by exact_mod_cast h) hn
  have hun := norm_smoothedSum_sub_le hf0 Xpos hB νnonneg ν_supp mass_one εpos ε_lt_one
  -- the exponents
  have hε2 : ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ) ≤ X ^ (49 / 50 : ℝ) := by
    rw [hεdef, ← Real.rpow_mul Xpos.le, ← Real.rpow_add Xpos]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
  have hεX : ε * X = X ^ (23 / 24 : ℝ) := by
    rw [hεdef, ← Real.rpow_add_one Xpos.ne']
    norm_num
  have h1X : 1 ≤ X ^ (23 / 24 : ℝ) := Real.one_le_rpow hX.le (by norm_num)
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlogX : Real.log (3 * X) ≤ 52 * X ^ (1 / 50 : ℝ) := by
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    have hX1 := Real.log_le_rpow_div (x := X) Xpos.le (ε := 1 / 50) (by norm_num)
    have hXκ : 1 ≤ X ^ (1 / 50 : ℝ) := Real.one_le_rpow hX.le (by norm_num)
    rw [Real.log_mul (by norm_num) Xpos.ne']
    linarith
  have hsm : Real.log (3 * X) * (3 * Real.log 2 * ε * X + 1) ≤ 208 * X ^ (49 / 50 : ℝ) := by
    have h2 : 3 * Real.log 2 * ε * X + 1 ≤ 4 * X ^ (23 / 24 : ℝ) := by
      rw [mul_assoc (3 * Real.log 2), hεX]
      have := mul_le_mul_of_nonneg_right hlog2.le (by positivity : (0 : ℝ) ≤ X ^ (23 / 24 : ℝ))
      linarith
    have h3 : X ^ (1 / 50 : ℝ) * X ^ (23 / 24 : ℝ) ≤ X ^ (49 / 50 : ℝ) := by
      rw [← Real.rpow_add Xpos]
      exact Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
    calc Real.log (3 * X) * (3 * Real.log 2 * ε * X + 1) ≤ (52 * X ^ (1 / 50 : ℝ)) * (4 * X ^ (23 / 24 : ℝ)) :=
          mul_le_mul hlogX h2 (by positivity) (by positivity)
      _ = 208 * (X ^ (1 / 50 : ℝ) * X ^ (23 / 24 : ℝ)) := by ring
      _ ≤ 208 * X ^ (49 / 50 : ℝ) := by gcongr
  have hKt : Kt ≤ (M + 5 * C) * (1 + Real.log (1 + |t|)) := by
    rw [hKtdef]
    nlinarith
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n =
      smoothedSum ν ε X f - (smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n) := by ring
  have hX49 : 0 ≤ X ^ (49 / 50 : ℝ) := by positivity
  rw [hsplit]
  calc ‖smoothedSum ν ε X f - (smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n)‖
      ≤ ‖smoothedSum ν ε X f‖ + ‖smoothedSum ν ε X f - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n‖ := norm_sub_le _ _
    _ ≤ (Kt * KM * ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ) * 8 + K₀ * X / (1 + |t|)) +
        Real.log (3 * X) * (3 * Real.log 2 * ε * X + 1) := by
        gcongr
        rw [hid]
        exact (norm_add_le _ _).trans (add_le_add hvi hres)
    _ ≤ (8 * KM * ((M + 5 * C) * (1 + Real.log (1 + |t|))) * X ^ (49 / 50 : ℝ) + K₀ * X / (1 + |t|)) +
        208 * X ^ (49 / 50 : ℝ) := by
        gcongr ?_ + _ + ?_
        · calc Kt * KM * ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ) * 8
              = 8 * KM * Kt * (ε ^ (-(1 / 2 : ℝ)) * X ^ (23 / 24 : ℝ)) := by ring
            _ ≤ 8 * KM * ((M + 5 * C) * (1 + Real.log (1 + |t|))) * X ^ (49 / 50 : ℝ) := by
              gcongr
    _ ≤ K₀ * X / (1 + |t|) + (8 * KM * (M + 5 * C) + 208) * (1 + Real.log (1 + |t|)) * X ^ (49 / 50 : ℝ) := by
        have : 208 * X ^ (49 / 50 : ℝ) ≤ 208 * (1 + Real.log (1 + |t|)) * X ^ (49 / 50 : ℝ) := by
          have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + Real.log (1 + |t|))
            (by positivity : (0 : ℝ) ≤ 208 * X ^ (49 / 50 : ℝ))
          linarith
        nlinarith

/-- `Σ_{N < n ≤ m} g(n) = Σ_{1 ≤ n ≤ m} g(n) − Σ_{1 ≤ n ≤ N} g(n)` for `N ≤ m`. -/
lemma sum_Ioc_eq_sub (g : ℕ → ℂ) {N m : ℕ} (h : N ≤ m) :
    ∑ n ∈ Finset.Ioc N m, g n =
      ∑ n ∈ Finset.Icc 1 ⌊(m : ℝ)⌋₊, g n - ∑ n ∈ Finset.Icc 1 ⌊(N : ℝ)⌋₊, g n := by
  have e : ∀ k : ℕ, Finset.Icc 1 k = Finset.Ioc 0 k := fun k ↦ by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [Nat.floor_natCast, Nat.floor_natCast, e, e]
  exact eq_sub_of_add_eq' (Finset.sum_Ioc_consecutive g (Nat.zero_le N) h)

/-- **The twisted prime number theorem on `(N, m]`, `N ≤ m ≤ 2N`, with a general exponent.** For `κ < 1/50` and
`A > 0` there is `C` with `|Σ_{N < n ≤ m} Λ(n)n^{−it}| ≤ C N^{1−κ}` for all `N ≥ 2`, `N ≤ m ≤ 2N` and
`N^κ ≤ |t| ≤ N^A`: the difference of `norm_psi_twist_le` at `X = m` and `X = N`, where `X/(1 + |t|) ≤ 2N^{1−κ}`
and `1 + log(1 + |t|) ≤ (2 + A/ε)N^ε` for `ε = 1/50 − κ`, so that `N^ε X^{49/50} ≤ 2N^{1−κ}`. -/
theorem norm_sum_Ioc_le_of {κ A : ℝ} (hκ : κ < 1 / 50) (hA : 0 < A) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ m : ℕ, N ≤ m → m ≤ 2 * N → ∀ t : ℝ, (N : ℝ) ^ κ ≤ |t| → |t| ≤ (N : ℝ) ^ A →
      ‖∑ n ∈ Finset.Ioc N m, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I))‖ ≤
        C * (N : ℝ) ^ (1 - κ) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hb⟩ := norm_psi_twist_le
  set ε : ℝ := 1 / 50 - κ with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  refine ⟨2 * (2 * K₁ + 2 * K₂ * (2 + A / ε)), by positivity, fun N hN m hNm hm2 t ht1 ht2 ↦ ?_⟩
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1.le hε.le
  have hlogt : 1 + Real.log (1 + |t|) ≤ (2 + A / ε) * (N : ℝ) ^ ε := by
    have h1 : 1 + |t| ≤ 2 * (N : ℝ) ^ A := by
      have : 1 ≤ (N : ℝ) ^ A := Real.one_le_rpow hN1.le hA.le
      linarith
    have h2 : Real.log (1 + |t|) ≤ Real.log 2 + A * Real.log N := by
      calc Real.log (1 + |t|) ≤ Real.log (2 * (N : ℝ) ^ A) :=
            Real.log_le_log (by linarith [abs_nonneg t]) h1
        _ = Real.log 2 + A * Real.log N := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hNpos]
    have h3 : A * Real.log N ≤ A / ε * (N : ℝ) ^ ε := by
      have := Real.log_le_rpow_div (x := (N : ℝ)) hNpos.le hε
      calc A * Real.log N ≤ A * ((N : ℝ) ^ ε / ε) := by gcongr
        _ = A / ε * (N : ℝ) ^ ε := by ring
    have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    nlinarith
  have hNN : (N : ℝ) ^ ε * (N : ℝ) ^ (49 / 50 : ℝ) = (N : ℝ) ^ (1 - κ) := by
    rw [← Real.rpow_add hNpos, hεdef]
    congr 1
    ring
  have hNN' : (N : ℝ) ^ (1 - κ) * (N : ℝ) ^ κ = N := by
    rw [← Real.rpow_add hNpos, sub_add_cancel, Real.rpow_one]
  have key : ∀ X : ℝ, (N : ℝ) ≤ X → X ≤ 2 * N →
      K₁ * X / (1 + |t|) + K₂ * (1 + Real.log (1 + |t|)) * X ^ (49 / 50 : ℝ) ≤
        (2 * K₁ + 2 * K₂ * (2 + A / ε)) * (N : ℝ) ^ (1 - κ) := by
    intro X hX1 hX2
    have hXpos : 0 < X := by linarith
    have h1 : K₁ * X / (1 + |t|) ≤ 2 * K₁ * (N : ℝ) ^ (1 - κ) := by
      rw [div_le_iff₀ (by positivity)]
      calc K₁ * X ≤ K₁ * (2 * N) := by gcongr
        _ = 2 * K₁ * ((N : ℝ) ^ (1 - κ) * (N : ℝ) ^ κ) := by rw [hNN']; ring
        _ ≤ 2 * K₁ * ((N : ℝ) ^ (1 - κ) * (1 + |t|)) := by gcongr; linarith
        _ = 2 * K₁ * (N : ℝ) ^ (1 - κ) * (1 + |t|) := by ring
    have hX49 : X ^ (49 / 50 : ℝ) ≤ 2 * (N : ℝ) ^ (49 / 50 : ℝ) := by
      calc X ^ (49 / 50 : ℝ) ≤ (2 * (N : ℝ)) ^ (49 / 50 : ℝ) := Real.rpow_le_rpow hXpos.le hX2 (by norm_num)
        _ = 2 ^ (49 / 50 : ℝ) * (N : ℝ) ^ (49 / 50 : ℝ) := Real.mul_rpow (by norm_num) hNpos.le
        _ ≤ 2 * (N : ℝ) ^ (49 / 50 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (49 / 50 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
    have hl0 : 0 ≤ 1 + Real.log (1 + |t|) := by
      have := Real.log_nonneg (by linarith [abs_nonneg t] : (1 : ℝ) ≤ 1 + |t|)
      linarith
    have h2 : K₂ * (1 + Real.log (1 + |t|)) * X ^ (49 / 50 : ℝ) ≤
        2 * K₂ * (2 + A / ε) * (N : ℝ) ^ (1 - κ) := by
      calc K₂ * (1 + Real.log (1 + |t|)) * X ^ (49 / 50 : ℝ)
          ≤ K₂ * ((2 + A / ε) * (N : ℝ) ^ ε) * (2 * (N : ℝ) ^ (49 / 50 : ℝ)) := by gcongr
        _ = 2 * K₂ * (2 + A / ε) * ((N : ℝ) ^ ε * (N : ℝ) ^ (49 / 50 : ℝ)) := by ring
        _ = 2 * K₂ * (2 + A / ε) * (N : ℝ) ^ (1 - κ) := by rw [hNN]
    linarith
  have hNm' : (N : ℝ) ≤ m := by exact_mod_cast hNm
  have hm2' : (m : ℝ) ≤ 2 * N := by exact_mod_cast hm2
  rw [sum_Ioc_eq_sub _ hNm]
  calc _ ≤ ‖∑ n ∈ Finset.Icc 1 ⌊(m : ℝ)⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I))‖ +
        ‖∑ n ∈ Finset.Icc 1 ⌊(N : ℝ)⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I))‖ :=
        norm_sub_le _ _
    _ ≤ (2 * K₁ + 2 * K₂ * (2 + A / ε)) * (N : ℝ) ^ (1 - κ) +
        (2 * K₁ + 2 * K₂ * (2 + A / ε)) * (N : ℝ) ^ (1 - κ) :=
        add_le_add ((hb m (by linarith) t).trans (key m hNm' hm2'))
          ((hb N hN1 t).trans (key N le_rfl (by linarith)))
    _ = 2 * (2 * K₁ + 2 * K₂ * (2 + A / ε)) * (N : ℝ) ^ (1 - κ) := by ring

/-! ### Primes -/

/-- **Abel summation, as an inequality.** If `w` is nonnegative and nonincreasing on `(N, M + 1]` and every
partial sum `Σ_{N < n ≤ m} a(n)`, `N ≤ m ≤ M`, has norm at most `B`, then `|Σ_{N < n ≤ M} w(n)a(n)| ≤ B w(N + 1)`. -/
lemma norm_sum_mul_le {a : ℕ → ℂ} {w : ℕ → ℝ} {N M : ℕ} (hNM : N ≤ M)
    (hw : ∀ n, N < n → n ≤ M → w (n + 1) ≤ w n) (hw0 : 0 ≤ w (M + 1)) {B : ℝ}
    (hB : ∀ m, N ≤ m → m ≤ M → ‖∑ n ∈ Finset.Ioc N m, a n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n‖ ≤ B * w (N + 1) := by
  have key : ∀ K, N ≤ K → K ≤ M → ‖∑ n ∈ Finset.Ioc N K, (w n : ℂ) * a n -
      (w (K + 1) : ℂ) * ∑ n ∈ Finset.Ioc N K, a n‖ ≤ B * (w (N + 1) - w (K + 1)) := by
    intro K hNK
    induction K, hNK using Nat.le_induction with
    | base => intro _; simp
    | succ K hNK ih =>
      intro hKM
      have ih' := ih (by omega)
      have hb := hB (K + 1) (by omega) hKM
      rw [Finset.sum_Ioc_succ_top hNK] at hb
      rw [Finset.sum_Ioc_succ_top hNK, Finset.sum_Ioc_succ_top hNK]
      have e : (∑ n ∈ Finset.Ioc N K, (w n : ℂ) * a n + (w (K + 1) : ℂ) * a (K + 1)) -
          (w (K + 1 + 1) : ℂ) * (∑ n ∈ Finset.Ioc N K, a n + a (K + 1)) =
          (∑ n ∈ Finset.Ioc N K, (w n : ℂ) * a n - (w (K + 1) : ℂ) * ∑ n ∈ Finset.Ioc N K, a n) +
            ((w (K + 1) - w (K + 1 + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ioc N K, a n + a (K + 1)) := by
        push_cast; ring
      rw [e]
      have hd : 0 ≤ w (K + 1) - w (K + 1 + 1) := sub_nonneg.2 (hw (K + 1) (by omega) hKM)
      calc _ ≤ B * (w (N + 1) - w (K + 1)) + (w (K + 1) - w (K + 1 + 1)) * B := by
            refine (norm_add_le _ _).trans (add_le_add ih' ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
            exact mul_le_mul_of_nonneg_left hb hd
        _ = B * (w (N + 1) - w (K + 1 + 1)) := by ring
  have h := key M hNM le_rfl
  have hA := hB M hNM le_rfl
  calc ‖∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n‖
      = ‖(∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n - (w (M + 1) : ℂ) * ∑ n ∈ Finset.Ioc N M, a n) +
          (w (M + 1) : ℂ) * ∑ n ∈ Finset.Ioc N M, a n‖ := by rw [sub_add_cancel]
    _ ≤ B * (w (N + 1) - w (M + 1)) + w (M + 1) * B := by
        refine (norm_add_le _ _).trans (add_le_add h ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
        exact mul_le_mul_of_nonneg_left hA hw0
    _ = B * w (N + 1) := by ring

/-- `e^{−it log j} = j^{−it}` for `j ≠ 0`. -/
lemma exp_eq_cpow (t : ℝ) {j : ℕ} (hj : j ≠ 0) :
    Complex.exp (-(I * ((t * Real.log j : ℝ) : ℂ))) = (j : ℂ) ^ (-(t * I)) := by
  rw [cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hj), ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- The prime powers: `Σ_{N < n ≤ m, n not prime} Λ(n) ≤ ψ(2N) − θ(2N) ≤ 16N^e` for `1 ≤ N ≤ m ≤ 2N` and
`e ≥ 3/4` (Mathlib's `Chebyshev.psi_sub_theta_le`). -/
lemma sum_not_prime_le_rpow {N m : ℕ} (hN : 1 ≤ N) (hm : m ≤ 2 * N) {e : ℝ} (he : 3 / 4 ≤ e) :
    ∑ n ∈ Finset.Ioc N m with ¬ n.Prime, ArithmeticFunction.vonMangoldt n ≤ 16 * (N : ℝ) ^ e := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set x : ℝ := ((2 * N : ℕ) : ℝ) with hxdef
  have hx : x = 2 * N := by rw [hxdef]; push_cast; ring
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  have hsub : (Finset.Ioc N m).filter (fun n ↦ ¬ n.Prime) ⊆ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬ n.Prime) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    rw [hxdef, Nat.floor_natCast]
    exact ⟨⟨by omega, by omega⟩, hn.2⟩
  calc ∑ n ∈ Finset.Ioc N m with ¬ n.Prime, ArithmeticFunction.vonMangoldt n
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬ n.Prime, ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg
    _ = Chebyshev.psi x - Chebyshev.theta x := (Chebyshev.psi_sub_theta_eq_sum_not_prime x).symm
    _ ≤ 2 * √x * Real.log x := Chebyshev.psi_sub_theta_le hx1
    _ ≤ 2 * x ^ (1 / 2 : ℝ) * (4 * x ^ (1 / 4 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        gcongr
        have := Real.log_le_rpow_div (x := x) (by linarith) (ε := 1 / 4) (by norm_num)
        linarith
    _ = 8 * x ^ (3 / 4 : ℝ) := by
        rw [show 2 * x ^ (1 / 2 : ℝ) * (4 * x ^ (1 / 4 : ℝ)) = 8 * (x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) by ring,
          ← Real.rpow_add (by linarith)]
        norm_num
    _ ≤ 8 * (2 * (N : ℝ) ^ e) := by
        have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
          calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        have h3 : (N : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) ^ e := Real.rpow_le_rpow_of_exponent_le hN1 he
        have h4 : x ^ (3 / 4 : ℝ) ≤ 2 * (N : ℝ) ^ e := by
          rw [hx, Real.mul_rpow (by norm_num) hNpos.le]
          exact mul_le_mul h2 h3 (by positivity) (by norm_num)
        linarith
    _ = 16 * (N : ℝ) ^ e := by ring

/-- **Primes in `(N, M]`, `M ≤ 2N`, twisted, with a power saving, for a general exponent.** For `κ < 1/50` and
`A > 0` there is `C` with `|Σ_{N < p ≤ M} p^{−it}| ≤ C N^{1−κ}` for all `N ≥ 2`, `N ≤ M ≤ 2N` and
`N^κ ≤ |t| ≤ N^A`, as the Dirichlet polynomial `DirMean.dp` of the primes with coefficient `1`. Abel summation
(`norm_sum_mul_le`) with the weights `1/log n` over the partial sums of `Λ(p)p^{−it}`, which are those of
`norm_sum_Ioc_le_of` up to the prime powers (`sum_not_prime_le_rpow`, as `1 − κ > 3/4`). -/
theorem norm_dp_primes_Ioc_le_of {κ A : ℝ} (hκ : κ < 1 / 50) (hA : 0 < A) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ M : ℕ, N ≤ M → M ≤ 2 * N → ∀ t : ℝ, (N : ℝ) ^ κ ≤ |t| → |t| ≤ (N : ℝ) ^ A →
      ‖DirMean.dp ((Finset.Ioc N M).filter Nat.Prime) (fun _ => 1) t‖ ≤ C * (N : ℝ) ^ (1 - κ) := by
  obtain ⟨C, hC0, hC⟩ := norm_sum_Ioc_le_of hκ hA
  refine ⟨C + 16, by positivity, fun N hN' M hNM hM2 t ht1 ht2 ↦ ?_⟩
  set a : ℕ → ℂ := fun n ↦
    if n.Prime then (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I)) else 0 with hadef
  set w : ℕ → ℝ := fun n ↦ 1 / Real.log n with hwdef
  have hdp : DirMean.dp ((Finset.Ioc N M).filter Nat.Prime) (fun _ => 1) t =
      ∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n := by
    rw [DirMean.dp, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp only [hadef, hwdef]
    split_ifs with hp
    · rw [ArithmeticFunction.vonMangoldt_apply_prime hp, exp_eq_cpow t hp.ne_zero]
      have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      rw [← mul_assoc, ← ofReal_mul, one_div_mul_cancel hl, ofReal_one]
    · simp
  rw [hdp]
  have hpart : ∀ m, N ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ioc N m, a n‖ ≤ (C + 16) * (N : ℝ) ^ (1 - κ) := by
    intro m hNm hm
    have e : ∑ n ∈ Finset.Ioc N m, a n =
        ∑ n ∈ Finset.Ioc N m, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I)) -
          ∑ n ∈ Finset.Ioc N m,
            (if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      simp only [hadef]
      split_ifs <;> ring
    rw [e]
    have h2 : ‖∑ n ∈ Finset.Ioc N m,
        (if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(t * I)))‖ ≤
          16 * (N : ℝ) ^ (1 - κ) := by
      refine (norm_sum_le _ _).trans ?_
      refine le_trans ?_ (sum_not_prime_le_rpow (by omega) (by omega : m ≤ 2 * N) (by linarith))
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun n hn ↦ ?_
      have hn0 : 0 < n := by have := (Finset.mem_Ioc.1 hn).1; omega
      by_cases hp : n.Prime
      · simp [hp]
      · simp only [hp, not_false_eq_true, ↓reduceIte]
        rw [norm_mul, norm_natCast_cpow_of_pos hn0]
        simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ C * (N : ℝ) ^ (1 - κ) + 16 * (N : ℝ) ^ (1 - κ) :=
          add_le_add (hC N hN' m hNm (by omega) t ht1 ht2) h2
      _ = (C + 16) * (N : ℝ) ^ (1 - κ) := by ring
  have hlog : ∀ n : ℕ, 2 ≤ n → 0 < Real.log n := fun n hn ↦
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hw : ∀ n, N < n → n ≤ M → w (n + 1) ≤ w n := by
    intro n hn _
    simp only [hwdef]
    have h1 := hlog n (by omega)
    exact one_div_le_one_div_of_le h1
      (Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by push_cast; linarith))
  have hw0 : 0 ≤ w (M + 1) := by
    simp only [hwdef]
    exact one_div_nonneg.2 (hlog _ (by omega)).le
  have hw1 : w (N + 1) ≤ 1 := by
    simp only [hwdef]
    have he : Real.exp 1 ≤ ((N + 1 : ℕ) : ℝ) := by
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ N + 1 by omega)
      linarith
    have h1 : 1 ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      exact he
    rw [div_le_one (by linarith)]
    exact h1
  calc _ ≤ (C + 16) * (N : ℝ) ^ (1 - κ) * w (N + 1) := norm_sum_mul_le hNM hw hw0 hpart
    _ ≤ (C + 16) * (N : ℝ) ^ (1 - κ) * 1 := by gcongr
    _ = (C + 16) * (N : ℝ) ^ (1 - κ) := mul_one _

end ShortSieveTwist

#print axioms ShortSieveTwist.verticalIntegral_sub_eq
#print axioms ShortSieveTwist.verticalIntegral'_integrand_eq
#print axioms ShortSieveTwist.smoothedSum_eq_verticalIntegral_add
#print axioms ShortSieveTwist.norm_psi_twist_le
#print axioms ShortSieveTwist.norm_sum_Ioc_le_of
#print axioms ShortSieveTwist.norm_dp_primes_Ioc_le_of
