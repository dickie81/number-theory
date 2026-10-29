/-
# The approximate functional equation for `ξ(s)²`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. Riemann's `ξ(s) = (s(s − 1)Λ₀(s) + 1)/2`, built from Mathlib's entire `Λ₀` (`xi`), is entire, satisfies
`ξ(1 − s) = ξ(s)` (`xi_one_sub`) and equals `½s(s − 1)Γ_ℝ(s)ζ(s)` on `Re s > 0`, `s ≠ 1` (`xi_eq_mul`). For
`0 ≤ Re s ≤ 1`, `ξ(s)² = J(s) + J(1 − s)` with `J(s) = (1/2πi)∫_{(2)} ξ(s + w)²e^{w²} dw/w` (`afe_xi`). This is the
input of the fourth moment of `ζ` at well-spaced points in `ZetaFourth.lean`, as `LinnikGamma.afe` is for `L(s, χ)²`.

* `xi_eq_Zr`: `ξ(s) = (s/2)Z(s)Γ_ℝ(s)` on `Re s > 0`, with `Z(s) = (s − 1)ζ(s)` (`PsiOmega.Zr`), also at `s = 1`.
* `norm_xi_le`: `|ξ(z)| ≤ Cξ(3 + |Im z|)³` on `−2 ≤ Re z ≤ 3`: `InghamDensity.Zr_strip_bound` and `|Γ_ℝ| ≤ 8` right
  of `Re z = ½`, `ξ(1 − z) = ξ(z)` left of it.
* `afe_xi`: `LinnikGamma.verticalIntegral_sub_eq` for `w ↦ ξ(s + w)²e^{w²}/w` between `Re w = 2` and `Re w = −2`, where
  `ξ(1 − z) = ξ(z)` turns the left integral into `J(1 − s)`. Unlike `Λ(s)`, `ξ` has no poles, so no other residue
  is crossed.
-/
import LinnikAFE
import InghamDetect

open Complex Real Set MeasureTheory

noncomputable section

namespace ZetaFourth

open LinnikGamma

/-! ### Riemann's `ξ` -/

/-- Riemann's `ξ(s) = (s(s − 1)Λ₀(s) + 1)/2`, with Mathlib's entire `Λ₀`. -/
def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

theorem differentiable_xi : Differentiable ℂ xi := by
  unfold xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul differentiable_completedZeta₀).add_const
    1).div_const 2

/-- **The functional equation** `ξ(1 − s) = ξ(s)`. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- The factor `½s(s − 1)Γ_ℝ(s)` of `ξ`. -/
def xiF (s : ℂ) : ℂ := s * (s - 1) / 2 * Gammaℝ s

/-- `ξ(s) = ½s(s − 1)Γ_ℝ(s)ζ(s)` on `Re s > 0`, `s ≠ 1`. -/
theorem xi_eq_mul {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) : xi s = xiF s * riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  unfold xi xiF
  field_simp
  ring

/-- `ξ(s) = (s/2)Z(s)Γ_ℝ(s)` on `Re s > 0`, with `Z(s) = (s − 1)ζ(s)` and `Z(1) = 1`. -/
theorem xi_eq_Zr {s : ℂ} (h0 : 0 < s.re) : xi s = s / 2 * PsiOmega.Zr s * Gammaℝ s := by
  rcases eq_or_ne s 1 with rfl | h1
  · unfold xi PsiOmega.Zr
    simp
  · rw [xi_eq_mul h0 h1, PsiOmega.Zr_of_ne h1]
    unfold xiF
    ring

/-- `|ξ(z)| ≤ C(3 + |Im z|)³` on `−2 ≤ Re z ≤ 3`. -/
theorem norm_xi_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, -2 ≤ z.re → z.re ≤ 3 → ‖xi z‖ ≤ C * (3 + |z.im|) ^ 3 := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := InghamDensity.Zr_strip_bound
  refine ⟨4 * CZ, by positivity, ?_⟩
  -- right of `Re z = ½`
  have hright : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 → ‖xi z‖ ≤ 4 * CZ * (3 + |z.im|) ^ 3 := by
    intro z h1 h2
    rw [xi_eq_Zr (by linarith), norm_mul, norm_mul, norm_div, Complex.norm_two]
    have hz : ‖z‖ ≤ 3 + |z.im| := by
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_nonneg (by linarith : 0 ≤ z.re)] at this; linarith
    have hG : ‖Gammaℝ z‖ ≤ 8 :=
      (PsiOmega.norm_Gammaℝ_le' (by linarith)).trans (real_Gamma_le_eight (by linarith) (by linarith))
    have hZ := hCZ z h1 h2
    have hi : 1 + |z.im| ≤ 3 + |z.im| := by linarith
    have hZ' : ‖PsiOmega.Zr z‖ ≤ CZ * (3 + |z.im|) ^ 2 := hZ.trans (by gcongr)
    calc ‖z‖ / 2 * ‖PsiOmega.Zr z‖ * ‖Gammaℝ z‖ ≤ (3 + |z.im|) / 2 * (CZ * (3 + |z.im|) ^ 2) * 8 := by
          gcongr
      _ = 4 * CZ * (3 + |z.im|) ^ 3 := by ring
  intro z h1 h2
  rcases le_total (1 / 2) z.re with h | h
  · exact hright z h h2
  · have hre : (1 - z).re = 1 - z.re := by simp
    have him : (1 - z).im = -z.im := by simp
    have hb := hright (1 - z) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rwa [xi_one_sub, him, abs_neg] at hb

/-! ### Gaussian tails -/

/-- `(a + |y|)⁶e^{−y²} ≤ 64(a⁶ + 48)e^{−y²/2}` for `a ≥ 0`. -/
lemma pow6_mul_exp_le {a : ℝ} (ha : 0 ≤ a) (y : ℝ) :
    (a + |y|) ^ 6 * Real.exp (-y ^ 2) ≤ 64 * (a ^ 6 + 48) * Real.exp (-y ^ 2 / 2) := by
  have hy := abs_nonneg y
  have h1 : (a + |y|) ^ 6 ≤ 64 * (a ^ 6 + |y| ^ 6) := by
    rcases le_total a |y| with h | h
    · calc (a + |y|) ^ 6 ≤ (2 * |y|) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
        _ = 64 * |y| ^ 6 := by ring
        _ ≤ 64 * (a ^ 6 + |y| ^ 6) := by nlinarith [pow_nonneg ha 6]
    · calc (a + |y|) ^ 6 ≤ (2 * a) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
        _ = 64 * a ^ 6 := by ring
        _ ≤ 64 * (a ^ 6 + |y| ^ 6) := by nlinarith [pow_nonneg hy 6]
  have h2 : |y| ^ 6 * Real.exp (-y ^ 2 / 2) ≤ 48 := by
    have hf := Real.pow_div_factorial_le_exp (x := y ^ 2 / 2) (by positivity) 3
    have e6 : |y| ^ 6 = 48 * ((y ^ 2 / 2) ^ 3 / (Nat.factorial 3 : ℝ)) := by
      rw [show |y| ^ 6 = (|y| ^ 2) ^ 3 by ring, sq_abs]; norm_num [Nat.factorial]; ring
    have hpos := Real.exp_pos (y ^ 2 / 2)
    rw [e6, show -y ^ 2 / 2 = -(y ^ 2 / 2) by ring, Real.exp_neg]
    rw [mul_assoc, ← div_eq_mul_inv]
    have : (y ^ 2 / 2) ^ 3 / (Nat.factorial 3 : ℝ) / Real.exp (y ^ 2 / 2) ≤ 1 := by
      rw [div_le_one hpos]; exact hf
    nlinarith
  have e : Real.exp (-y ^ 2) = Real.exp (-y ^ 2 / 2) * Real.exp (-y ^ 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hE := Real.exp_pos (-y ^ 2 / 2)
  have hE1 : Real.exp (-y ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg y])
  rw [e]
  calc (a + |y|) ^ 6 * (Real.exp (-y ^ 2 / 2) * Real.exp (-y ^ 2 / 2))
      ≤ 64 * (a ^ 6 + |y| ^ 6) * (Real.exp (-y ^ 2 / 2) * Real.exp (-y ^ 2 / 2)) := by gcongr
    _ = 64 * a ^ 6 * Real.exp (-y ^ 2 / 2) * Real.exp (-y ^ 2 / 2) +
          64 * (|y| ^ 6 * Real.exp (-y ^ 2 / 2)) * Real.exp (-y ^ 2 / 2) := by ring
    _ ≤ 64 * a ^ 6 * Real.exp (-y ^ 2 / 2) * 1 + 64 * 48 * Real.exp (-y ^ 2 / 2) := by
        gcongr
    _ = 64 * (a ^ 6 + 48) * Real.exp (-y ^ 2 / 2) := by ring

/-- `|y|e^{−y²/2} ≤ 1`. -/
lemma abs_mul_exp_neg_sq_half_le (y : ℝ) : |y| * Real.exp (-y ^ 2 / 2) ≤ 1 := by
  have hpos := Real.exp_pos (y ^ 2 / 2)
  have h := Real.add_one_le_exp (y ^ 2 / 2)
  rw [show -y ^ 2 / 2 = -(y ^ 2 / 2) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
  nlinarith [sq_nonneg (|y| - 1), sq_abs y]

/-! ### The approximate functional equation -/

/-- The integrand `ξ(s + w)²e^{w²}/w`. -/
def afeGx (s w : ℂ) : ℂ := xi (s + w) ^ 2 * Complex.exp (w ^ 2) / w

/-- `J(s) = (1/2πi)∫_{(2)} ξ(s + w)²e^{w²} dw/w`. -/
def afeJx (s : ℂ) : ℂ := VerticalIntegral' (afeGx s) 2

lemma differentiable_afeFx (s : ℂ) : Differentiable ℂ fun w : ℂ => xi (s + w) ^ 2 * Complex.exp (w ^ 2) :=
  ((differentiable_xi.comp (differentiable_const s |>.add differentiable_id)).pow 2).mul
    (Complex.differentiable_exp.comp (differentiable_id.pow 2))

/-- The bound on `afeGx` in the strip `|Re w| ≤ 2`, for `0 ≤ Re s ≤ 1`. -/
lemma norm_afeGx_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z : ℂ, -2 ≤ z.re → z.re ≤ 3 → ‖xi z‖ ≤ C * (3 + |z.im|) ^ 3)
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) {x y : ℝ} (hx1 : -2 ≤ x) (hx2 : x ≤ 2) (hw : (x : ℂ) + y * I ≠ 0) :
    ‖afeGx s (x + y * I)‖ ≤ C ^ 2 * Real.exp 4 * ((3 + |s.im| + |y|) ^ 6 * Real.exp (-y ^ 2)) /
      ‖(x : ℂ) + y * I‖ := by
  have hre : (s + (x + y * I)).re = s.re + x := by simp
  have him : (s + (x + y * I)).im = s.im + y := by simp
  have hL := hC (s + (x + y * I)) (by rw [hre]; linarith) (by rw [hre]; linarith)
  rw [him] at hL
  have him' : |s.im + y| ≤ |s.im| + |y| := abs_add_le _ _
  have hL' : ‖xi (s + (x + y * I))‖ ≤ C * (3 + |s.im| + |y|) ^ 3 := by
    exact hL.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 3) hC0)
  have hexp : ‖Complex.exp (((x : ℂ) + y * I) ^ 2)‖ ≤ Real.exp 4 * Real.exp (-y ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (((x : ℂ) + y * I) ^ 2).re = x ^ 2 - y ^ 2 := by simp [sq]
    rw [this]; nlinarith
  unfold afeGx
  rw [norm_div, norm_mul, norm_pow]
  have hwpos : 0 < ‖(x : ℂ) + y * I‖ := norm_pos_iff.2 hw
  rw [div_le_div_iff_of_pos_right hwpos]
  calc ‖xi (s + (x + y * I))‖ ^ 2 * ‖Complex.exp (((x : ℂ) + y * I) ^ 2)‖
      ≤ (C * (3 + |s.im| + |y|) ^ 3) ^ 2 * (Real.exp 4 * Real.exp (-y ^ 2)) := by gcongr
    _ = _ := by ring

open Filter Topology in
/-- **The approximate functional equation for `ξ(s)²`.** For `0 ≤ Re s ≤ 1`, `ξ(s)² = J(s) + J(1 − s)`, with
`J(s) = (1/2πi)∫_{(2)} ξ(s + w)²e^{w²} dw/w`: `verticalIntegral_sub_eq` across the pole at `w = 0`, and
`ξ(1 − z) = ξ(z)` on `Re w = −2`. -/
theorem afe_xi {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) : xi s ^ 2 = afeJx s + afeJx (1 - s) := by
  obtain ⟨C, hC0, hC⟩ := norm_xi_le
  set G := afeGx s with hG
  set F : ℂ → ℂ := fun w => xi (s + w) ^ 2 * Complex.exp (w ^ 2) with hF
  have hFd := differentiable_afeFx s
  have hGF : ∀ w, G w = F w / w := fun w => rfl
  set B := C ^ 2 * Real.exp 4 with hB
  have hB0 : 0 ≤ B := by positivity
  set a := 3 + |s.im| with ha
  have ha0 : 0 ≤ a := by positivity
  -- holomorphy off `0`
  have hhol : HolomorphicOn G ((Icc (-2) 2 ×ℂ univ) \ {0}) := by
    intro w hw
    have hw0 : w ≠ 0 := hw.2
    exact ((hFd w).div differentiableAt_id hw0).differentiableWithinAt
  -- the residue
  have hres : (G - fun w ↦ xi s ^ 2 / (w - 0)) =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
    have hF0 : F 0 = xi s ^ 2 := by simp [hF]
    have hb : (fun w => slope F 0 w) =O[𝓝[≠] 0] (1 : ℂ → ℂ) := by
      have h1 : Tendsto (fun w => slope F 0 w) (𝓝[≠] 0) (𝓝 (deriv F 0)) := (hFd 0).hasDerivAt.tendsto_slope
      exact h1.isBigO_one ℂ
    refine hb.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [Pi.sub_apply, hGF, slope_def_field, sub_zero, hF0]
    rw [sub_div]
  -- integrability on the two lines
  have hline : ∀ x : ℝ, (x = 2 ∨ x = -2) → Integrable fun t : ℝ => G (x + t * I) := by
    intro x hx
    have hx1 : -2 ≤ x := by rcases hx with h | h <;> linarith
    have hx2 : x ≤ 2 := by rcases hx with h | h <;> linarith
    have hxn : ∀ t : ℝ, (x : ℂ) + t * I ≠ 0 := fun t h => by
      have := congrArg Complex.re h; simp at this; rcases hx with h' | h' <;> linarith
    have hcont : Continuous fun t : ℝ => G (x + t * I) := by
      have hc1 : Continuous fun t : ℝ => (x : ℂ) + t * I := by fun_prop
      exact (hFd.continuous.comp hc1).div hc1 hxn
    refine Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (B * (64 * (a ^ 6 + 48)) / 2)) hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have h := norm_afeGx_le hC0 hC hs0 hs1 hx1 hx2 (hxn t) (y := t)
    have hn2 : 2 ≤ ‖(x : ℂ) + t * I‖ := by
      have h0 := Complex.abs_re_le_norm ((x : ℂ) + t * I)
      have hre : ((x : ℂ) + t * I).re = x := by simp
      rw [hre] at h0
      have hax : |x| = 2 := by rcases hx with h' | h' <;> rw [h'] <;> norm_num
      linarith
    have h2 := pow6_mul_exp_le ha0 t
    have hnum : 0 ≤ (a + |t|) ^ 6 * Real.exp (-t ^ 2) := by positivity
    calc ‖G (x + t * I)‖ ≤ B * ((a + |t|) ^ 6 * Real.exp (-t ^ 2)) / ‖(x : ℂ) + t * I‖ := by
          simpa [hG, hB, ha, add_assoc, mul_assoc] using h
      _ ≤ B * ((a + |t|) ^ 6 * Real.exp (-t ^ 2)) / 2 := by gcongr
      _ ≤ B * (64 * (a ^ 6 + 48) * Real.exp (-t ^ 2 / 2)) / 2 := by gcongr
      _ = B * (64 * (a ^ 6 + 48)) / 2 * Real.exp (-(1 / 2) * t ^ 2) := by ring_nf
  -- uniform decay
  have hdecay : ∀ η > 0, ∃ T₀ : ℝ, ∀ x ∈ Icc (-2 : ℝ) 2, ∀ y : ℝ, T₀ ≤ |y| → ‖G (x + y * I)‖ ≤ η := by
    intro η hη
    set K := B * (64 * (a ^ 6 + 48)) with hK
    have hK0 : 0 ≤ K := by positivity
    refine ⟨max 1 (K / η), fun x hx y hy => ?_⟩
    have hy1 : 1 ≤ |y| := (le_max_left _ _).trans hy
    have hyK : K / η ≤ |y| := (le_max_right _ _).trans hy
    have hyn : (x : ℂ) + y * I ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; rw [this] at hy1; simp at hy1; linarith
    have h := norm_afeGx_le hC0 hC hs0 hs1 hx.1 hx.2 hyn
    have hn : |y| ≤ ‖(x : ℂ) + y * I‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + y * I); simpa using this
    have hk := pow6_mul_exp_le ha0 y
    have hk2 := abs_mul_exp_neg_sq_half_le y
    have hpos : 0 < |y| := by linarith
    have hE := Real.exp_pos (-y ^ 2 / 2)
    calc ‖G (x + y * I)‖ ≤ B * ((a + |y|) ^ 6 * Real.exp (-y ^ 2)) / ‖(x : ℂ) + y * I‖ := by
          simpa [hG, hB, ha, add_assoc, mul_assoc] using h
      _ ≤ B * ((a + |y|) ^ 6 * Real.exp (-y ^ 2)) / 1 := by gcongr; linarith
      _ ≤ B * (64 * (a ^ 6 + 48) * Real.exp (-y ^ 2 / 2)) := by rw [div_one]; gcongr
      _ = K * Real.exp (-y ^ 2 / 2) := by rw [hK]; ring
      _ ≤ K * (1 / |y|) := by
          gcongr
          rw [le_div_iff₀ hpos]; linarith
      _ = K / |y| := by ring
      _ ≤ η := by
          rw [div_le_iff₀ hpos]
          rw [div_le_iff₀ hη] at hyK
          linarith
  have hsub := verticalIntegral_sub_eq (G := G) (σ' := -2) (σ := 2) (by norm_num) (by norm_num) _ hhol hres
    (hline 2 (Or.inl rfl)) (by simpa using hline (-2) (Or.inr rfl)) hdecay
  -- the left line through the functional equation
  set G' := afeGx (1 - s) with hG'
  have hrefl : ∀ u : ℂ, u ≠ 0 → G (-u) = -G' u := by
    intro u hu
    simp only [hG, hG', afeGx]
    rw [show s + -u = 1 - (1 - s + u) by ring, xi_one_sub, neg_sq]
    have hnu : (-u : ℂ) ≠ 0 := neg_ne_zero.2 hu
    field_simp
  have hleft : VerticalIntegral G (-2) = -VerticalIntegral G' 2 := by
    simp only [VerticalIntegral]
    have h1 : ∫ t : ℝ, G ((-2 : ℝ) + t * I) = ∫ t : ℝ, G ((-2 : ℝ) + (-t) * I) := by
      rw [← integral_neg_eq_self]; simp only [ofReal_neg]
    rw [h1]
    have h2 : ∀ t : ℝ, G ((-2 : ℝ) + (-t) * I) = -G' ((2 : ℝ) + t * I) := by
      intro t
      have hu : ((2 : ℝ) : ℂ) + t * I ≠ 0 := fun h => by
        have := congrArg Complex.re h; norm_num at this
      rw [← hrefl _ hu]
      congr 1; push_cast; ring
    simp_rw [h2]
    rw [integral_neg, smul_neg]
  rw [hleft, hG, hG'] at hsub
  unfold afeJx VerticalIntegral'
  simp only [smul_eq_mul]
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    simp [this, I_ne_zero]
  have hsum : VerticalIntegral (afeGx s) 2 + VerticalIntegral (afeGx (1 - s)) 2 = 2 * π * I * xi s ^ 2 := by
    linear_combination hsub
  calc xi s ^ 2 = 1 / (2 * π * I) * (2 * π * I * xi s ^ 2) := by field_simp
    _ = 1 / (2 * π * I) * (VerticalIntegral (afeGx s) 2 + VerticalIntegral (afeGx (1 - s)) 2) := by rw [hsum]
    _ = _ := by ring

end ZetaFourth

#print axioms ZetaFourth.xi_one_sub
#print axioms ZetaFourth.xi_eq_mul
#print axioms ZetaFourth.norm_xi_le
#print axioms ZetaFourth.afe_xi
