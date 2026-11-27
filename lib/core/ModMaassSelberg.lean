/-
# The Maass–Selberg relation for `SL(2, ℤ)`

Milestone B of the scattering theory of `SL(2, ℤ)\ℍ²`. With `E*^Y` the truncated completed Eisenstein series of
`ModTruncation` (`E*` below the horocycle `Im z = Y`, `E* − a₀` above it), `Λ` the completed zeta function and
`φ(s) = Λ(2s − 1)/Λ(2s)` (`PavlovFaddeev.scatteringMatrix`):
* **Unfolding** (`integral_fd_tsum`): `∫_𝒟 Σ_{Γ_∞\Γ} f(γz) dμ = 2∫_{0 ≤ Re z < 1} f dμ` for `T`-periodic integrable `f`.
* **Truncation as a Poincaré series** (`EstarY_eq_P`): for `Y ≥ 1`, `Re s > 1` and `z ∈ 𝒟`,
  `E*^Y(z, s) = Λ(2s) · ½Σ_{(c,d)} H_Y(Im γ_{(c,d)} z, s)` with `H_Y(u, s) = u^s` (`u ≤ Y`), `−φ(s)u^{1−s}` (`u > Y`).
* **Region of absolute convergence** (`integral_EstarY_mul_region`): for `Y ≥ 1` and `1 < Re s₁ < Re s₂`,
  `∫_𝒟 E*^Y(s₁)E*^Y(s₂) dμ = MS Y s₁ s₂` where
  `MS Y s₁ s₂ = (Λ(2s₁)Λ(2s₂)Y^{s₁+s₂−1} − Λ(2s₁−1)Λ(2s₂−1)Y^{1−s₁−s₂})/(s₁ + s₂ − 1)
    + (Λ(2s₁)Λ(2s₂−1)Y^{s₁−s₂} − Λ(2s₁−1)Λ(2s₂)Y^{s₂−s₁})/(s₁ − s₂)`,
  by unfolding against `E*(s₁)` (Rankin–Selberg), Fubini, and the constant term `a₀`.
* **Analytic continuation** (`IY_cleared`, `maass_selberg`): by the identity theorem in each variable on the connected
  set `ℂ \ {0, ½, 1}` (using the holomorphy of `ModTruncation.differentiableOn_integral_EstarY`), the relation holds
  for all `s₁, s₂ ∉ {0, ½, 1}` with `s₁ + s₂ ≠ 1`, `s₁ ≠ s₂`; in cleared form everywhere on `U × U`.
* **The anti-diagonal** (`maass_selberg_diag`): differentiating the cleared identity at `s₂ = 1 − s₁`,
  `∫_𝒟 E*^Y(s)E*^Y(1 − s) dμ = 2Λ(2s)Λ(2s−1) log Y − 2Λ(2s)Λ'(2s−1) + 2Λ(2s−1)Λ'(2s)
    + (Λ(2s)²Y^{2s−1} − Λ(2s−1)²Y^{1−2s})/(2s − 1)`.
* **Normalised forms** (`maass_selberg_phi`, `maass_selberg_phi_diag`, `memLp_EY`): for `E^Y = E*^Y/Λ(2s)`,
  `∫_𝒟 E^Y(s₁)E^Y(s₂) dμ = (Y^{s₁+s₂−1} − φ(s₁)φ(s₂)Y^{1−s₁−s₂})/(s₁ + s₂ − 1)
    + (φ(s₂)Y^{s₁−s₂} − φ(s₁)Y^{s₂−s₁})/(s₁ − s₂)` and
  `∫_𝒟 E^Y(s)E^Y(1 − s) dμ = 2 log Y − (φ'/φ)(s) + (φ(1 − s)Y^{2s−1} − φ(s)Y^{1−2s})/(2s − 1)`.

The proof is by unfolding and analytic continuation; the Laplacian eigen-equation and Green's identity are not used.
-/
import Mathlib
import ModTruncation

open Complex Real Filter Topology Set MeasureTheory UpperHalfPlane Metric ModularGroup
open scoped MatrixGroups ENNReal NNReal

noncomputable section

namespace ModMaassSelberg

open ModEisenstein ModContinuation ModFourier ModTruncation ModFD

/-! ## Unfolding for integrable functions -/

lemma measurable_gam_smul (v : CoprimeRow) : Measurable fun z : ℍ => gam v • z := measurable_smul_SL _

/-- **Unfolding for `g ≥ 0` integrable on the strip**: then `Σ_v g(γ_v z)` converges for almost every `z ∈ 𝒟`, is
integrable on `𝒟`, and `∫_𝒟 Σ_v g(γ_v z) dμ = 2∫_{0 ≤ re < 1} g dμ`. -/
theorem integral_fd_tsum_nonneg (g : ℍ → ℝ) (hg : Measurable g) (h0 : ∀ z, 0 ≤ g z)
    (hper : ∀ z, g (T • z) = g z) (hint : IntegrableOn g strip) :
    (∀ᵐ z ∂volume.restrict fd, Summable fun v : CoprimeRow => g (gam v • z)) ∧
      Integrable (fun z => ∑' v : CoprimeRow, g (gam v • z)) (volume.restrict fd) ∧
        ∫ z in fd, ∑' v : CoprimeRow, g (gam v • z) = 2 * ∫ z in strip, g z := by
  have hL := lintegral_fd_tsum_coprime (fun z => ENNReal.ofReal (g z)) (ENNReal.measurable_ofReal.comp hg)
    (fun z => by simp only [hper])
  have hfin : ∫⁻ z in strip, ENNReal.ofReal (g z) < ∞ := by
    have := hint.hasFiniteIntegral
    rw [HasFiniteIntegral] at this
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) this
    rw [Real.enorm_eq_ofReal (h0 z)]
  have hfin' : ∫⁻ z in fd, ∑' v : CoprimeRow, ENNReal.ofReal (g (gam v • z)) < ∞ := by
    rw [hL]; exact ENNReal.mul_lt_top (by norm_num) hfin
  have hmeasG : Measurable fun z => ∑' v : CoprimeRow, ENNReal.ofReal (g (gam v • z)) :=
    Measurable.tsum fun v => ENNReal.measurable_ofReal.comp (hg.comp (measurable_gam_smul v))
  have hae := ae_lt_top hmeasG hfin'.ne
  have hsum : ∀ᵐ z ∂volume.restrict fd, Summable fun v : CoprimeRow => g (gam v • z) := by
    filter_upwards [hae] with z hz
    have := ENNReal.summable_toReal hz.ne
    refine this.congr fun v => ?_
    rw [ENNReal.toReal_ofReal (h0 _)]
  have heq : ∀ᵐ z ∂volume.restrict fd, ENNReal.ofReal (∑' v : CoprimeRow, g (gam v • z)) =
      ∑' v : CoprimeRow, ENNReal.ofReal (g (gam v • z)) := by
    filter_upwards [hsum] with z hz
    exact ENNReal.ofReal_tsum_of_nonneg (fun v => h0 _) hz
  have hmeasS : Measurable fun z => ∑' v : CoprimeRow, g (gam v • z) :=
    Measurable.tsum fun v => hg.comp (measurable_gam_smul v)
  have hnn : ∀ z, 0 ≤ ∑' v : CoprimeRow, g (gam v • z) := fun z => tsum_nonneg fun v => h0 _
  refine ⟨hsum, ?_, ?_⟩
  · refine ⟨hmeasS.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ z in fd, ‖∑' v : CoprimeRow, g (gam v • z)‖ₑ
        = ∫⁻ z in fd, ENNReal.ofReal (∑' v : CoprimeRow, g (gam v • z)) :=
          lintegral_congr fun z => Real.enorm_eq_ofReal (hnn z)
      _ = ∫⁻ z in fd, ∑' v : CoprimeRow, ENNReal.ofReal (g (gam v • z)) := lintegral_congr_ae heq
      _ < ∞ := hfin'
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hmeasS.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hg.aestronglyMeasurable,
      lintegral_congr_ae heq, hL, ENNReal.toReal_mul]
    simp

/-- Unfolding for real `g` integrable on the strip. -/
theorem integral_fd_tsum_real (g : ℍ → ℝ) (hg : Measurable g) (hper : ∀ z, g (T • z) = g z)
    (hint : IntegrableOn g strip) :
    (∀ᵐ z ∂volume.restrict fd, Summable fun v : CoprimeRow => g (gam v • z)) ∧
      Integrable (fun z => ∑' v : CoprimeRow, g (gam v • z)) (volume.restrict fd) ∧
        ∫ z in fd, ∑' v : CoprimeRow, g (gam v • z) = 2 * ∫ z in strip, g z := by
  obtain ⟨s1, i1, e1⟩ := integral_fd_tsum_nonneg (fun z => max (g z) 0) (hg.max measurable_const)
    (fun z => le_max_right _ _) (fun z => by simp only [hper]) hint.pos_part
  obtain ⟨s2, i2, e2⟩ := integral_fd_tsum_nonneg (fun z => max (-g z) 0) (hg.neg.max measurable_const)
    (fun z => le_max_right _ _) (fun z => by simp only [hper]) hint.neg_part
  have hsplit : ∀ᵐ z ∂volume.restrict fd, ∑' v : CoprimeRow, g (gam v • z) =
      ∑' v : CoprimeRow, max (g (gam v • z)) 0 - ∑' v : CoprimeRow, max (-g (gam v • z)) 0 := by
    filter_upwards [s1, s2] with z h1 h2
    rw [← h1.tsum_sub h2]
    exact tsum_congr fun v => (max_zero_sub_eq_self _).symm
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [s1, s2] with z h1 h2
    exact (h1.sub h2).congr fun v => max_zero_sub_eq_self _
  · exact (i1.sub i2).congr (hsplit.mono fun z h => h.symm)
  · rw [integral_congr_ae hsplit, integral_sub i1 i2, e1, e2, ← mul_sub,
      ← integral_sub hint.pos_part hint.neg_part]
    congr 2
    funext z
    exact max_zero_sub_eq_self _

/-- **Unfolding over `Γ_∞\SL(2, ℤ)` for integrable functions**: for `T`-periodic measurable `f : ℍ → ℂ` integrable on
the strip `0 ≤ re z < 1`, `∫_𝒟 Σ_{(c, d) coprime} f(γ_{(c,d)} z) dμ = 2∫_{0 ≤ re z < 1} f dμ`. -/
theorem integral_fd_tsum (f : ℍ → ℂ) (hf : Measurable f) (hper : ∀ z, f (T • z) = f z)
    (hint : IntegrableOn f strip) :
    ∫ z in fd, ∑' v : CoprimeRow, f (gam v • z) = 2 * ∫ z in strip, f z := by
  obtain ⟨sr, ir, er⟩ := integral_fd_tsum_real (fun z => (f z).re) (Complex.measurable_re.comp hf)
    (fun z => by simp only [hper]) hint.re
  obtain ⟨si, ii, ei⟩ := integral_fd_tsum_real (fun z => (f z).im) (Complex.measurable_im.comp hf)
    (fun z => by simp only [hper]) hint.im
  have hsplit : ∀ᵐ z ∂volume.restrict fd, ∑' v : CoprimeRow, f (gam v • z) =
      ((∑' v : CoprimeRow, (f (gam v • z)).re : ℝ) : ℂ) + ((∑' v : CoprimeRow, (f (gam v • z)).im : ℝ) : ℂ) * Complex.I := by
    filter_upwards [sr, si] with z h1 h2
    have h : HasSum (fun v : CoprimeRow => f (gam v • z))
        (((∑' v : CoprimeRow, (f (gam v • z)).re : ℝ) : ℂ) + ((∑' v : CoprimeRow, (f (gam v • z)).im : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.hasSum_iff]
      simp only [add_re, ofReal_re, mul_re, Complex.I_re, mul_zero, ofReal_im, Complex.I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add]
      exact ⟨h1.hasSum, h2.hasSum⟩
    exact h.tsum_eq
  have hre : ∫ z in strip, f z =
      ((∫ z in strip, (f z).re : ℝ) : ℂ) + ((∫ z in strip, (f z).im : ℝ) : ℂ) * Complex.I :=
    (integral_re_add_im hint).symm
  rw [integral_congr_ae hsplit, integral_add (ir.ofReal) (ii.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, er, ei, hre]
  push_cast
  ring


/-! ## The truncation as a Poincaré series -/

lemma nq_re_im (z : ℍ) (v : Fin 2 → ℤ) :
    nq z v = ((v 0 : ℝ) * z.re + v 1) ^ 2 + ((v 0 : ℝ) * z.im) ^ 2 := by
  have h := nq_pt z.re z.im_pos v
  rwa [pt_re_im] at h

/-- On `𝒟`, `|cz + d|² ≥ Im z` whenever `c ≠ 0`; so `Im(γz) ≤ 1` unless `γ ∈ ±Γ_∞`. -/
lemma im_le_nq_of_mem_fd {z : ℍ} (hz : z ∈ fd) {v : Fin 2 → ℤ} (hv : v 0 ≠ 0) : z.im ≤ nq z v := by
  have hy := half_le_im_of_mem_fd hz
  have h1 : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have := hz.1
    rw [Complex.normSq_apply] at this
    simpa [sq] using this
  have h2 := abs_le.1 hz.2
  rw [nq_re_im]
  set x := z.re
  set y := z.im
  have hc : v 0 = 1 ∨ v 0 = -1 ∨ 2 ≤ v 0 ∨ v 0 ≤ -2 := by omega
  have hd : v 1 = 0 ∨ 1 ≤ v 1 ∨ v 1 ≤ -1 := by omega
  rcases hc with hc | hc | hc | hc
  · have : ((v 0 : ℤ) : ℝ) = 1 := by exact_mod_cast hc
    rw [this]
    rcases hd with hd | hd | hd
    · have : ((v 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hd
      rw [this]; nlinarith [sq_nonneg (y - 1)]
    · have : (1 : ℝ) ≤ ((v 1 : ℤ) : ℝ) := by exact_mod_cast hd
      nlinarith [sq_nonneg (y - 1)]
    · have : ((v 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hd
      nlinarith [sq_nonneg (y - 1)]
  · have : ((v 0 : ℤ) : ℝ) = -1 := by exact_mod_cast hc
    rw [this]
    rcases hd with hd | hd | hd
    · have : ((v 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hd
      rw [this]; nlinarith [sq_nonneg (y - 1)]
    · have : (1 : ℝ) ≤ ((v 1 : ℤ) : ℝ) := by exact_mod_cast hd
      nlinarith [sq_nonneg (y - 1)]
    · have : ((v 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hd
      nlinarith [sq_nonneg (y - 1)]
  · have : (2 : ℝ) ≤ ((v 0 : ℤ) : ℝ) := by exact_mod_cast hc
    nlinarith [sq_nonneg ((v 0 : ℝ) * x + v 1), mul_le_mul this this (by norm_num) (by linarith)]
  · have : ((v 0 : ℤ) : ℝ) ≤ -2 := by exact_mod_cast hc
    nlinarith [sq_nonneg ((v 0 : ℝ) * x + v 1), mul_le_mul_of_nonpos_left this (by linarith : (v 0 : ℝ) ≤ 0)]

/-- The two coprime rows `±(0, 1)`. -/
def vp : CoprimeRow := ⟨![0, 1], by simp [isCoprime_zero_left]⟩
def vm : CoprimeRow := ⟨![0, -1], by simp [isCoprime_zero_left]⟩

lemma vp_ne_vm : vp ≠ vm := by
  intro h
  have := congrArg (fun v : CoprimeRow => v.1 1) h
  simp [vp, vm] at this

lemma eq_vp_or_vm {v : CoprimeRow} (h0 : v.1 0 = 0) : v = vp ∨ v = vm := by
  have h := v.2
  rw [h0, isCoprime_zero_left, Int.isUnit_iff] at h
  rcases h with h | h
  · left; ext i; fin_cases i <;> simp [vp, h0, h]
  · right; ext i; fin_cases i <;> simp [vm, h0, h]

lemma nq_of_zero {z : ℍ} {v : CoprimeRow} (h0 : v.1 0 = 0) : nq z v.1 = 1 := by
  rcases eq_vp_or_vm h0 with rfl | rfl <;> simp [nq, vp, vm]

/-- The profile of the truncated Poincaré series: `u^s` below the horocycle `u = Y`, and `−φ(s)u^{1−s}` above it,
with `φ = PavlovFaddeev.scatteringMatrix`. -/
def H (Y : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  if u ≤ Y then (u : ℂ) ^ s else -(PavlovFaddeev.scatteringMatrix s * (u : ℂ) ^ (1 - s))

/-- **The truncated Poincaré series** `P^Y(z, s) = ½Σ_{(c, d) coprime} H_Y(Im γ_{(c,d)} z, s)`: Arthur's truncation
of `E(z, s)`, written as a series over `Γ_∞\SL(2, ℤ)`. -/
def P (Y : ℝ) (s : ℂ) (z : ℍ) : ℂ := (1 / 2) * ∑' v : CoprimeRow, H Y s (z.im / nq z v.1)

lemma scattering_mul {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (2 * s) * PavlovFaddeev.scatteringMatrix s = completedRiemannZeta (2 * s - 1) := by
  have hΛ : completedRiemannZeta (2 * s) ≠ 0 :=
    PavlovFaddeev.completed_ne_zero_of_one_le_re (by simp; linarith)
  rw [PavlovFaddeev.scatteringMatrix]
  field_simp

/-- **On `𝒟`, for `Y ≥ 1` and `Re s > 1`, `E*^Y(z, s) = Λ(2s)P^Y(z, s)`**: on `𝒟` only the two rows `±(0, 1)` reach
above the horocycle `Im = Y`. -/
theorem EstarY_eq_P {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ} (hs : 1 < s.re) {z : ℍ} (hz : z ∈ fd) :
    EstarY Y s z = completedRiemannZeta (2 * s) * P Y s z := by
  have hy := z.im_pos
  set d₀ : ℂ := H Y s z.im - (z.im : ℂ) ^ s
  have hD : ∀ v : CoprimeRow, H Y s (z.im / nq z v.1) - term z s v.1 = if v.1 0 = 0 then d₀ else 0 := by
    intro v
    split_ifs with h0
    · rw [nq_of_zero h0, div_one, term, nq_of_zero h0, div_one]
    · have hn := im_le_nq_of_mem_fd hz h0
      have hu : z.im / nq z v.1 ≤ Y := by
        rw [div_le_iff₀ (hy.trans_le hn)]; nlinarith
      simp only [H, hu, ↓reduceIte, term, sub_self]
  have hsumD : ∑' v : CoprimeRow, (if v.1 0 = 0 then d₀ else 0) = 2 * d₀ := by
    rw [tsum_eq_sum (s := {vp, vm}), Finset.sum_pair vp_ne_vm]
    · simp [vp, vm]; ring
    · intro v hv
      refine ite_eq_right_iff.2 fun h0 => ?_
      rcases eq_vp_or_vm h0 with rfl | rfl <;> simp at hv
  have hsT : Summable fun v : CoprimeRow => term z s v.1 := (summable_norm_E z hs).of_norm
  have hsD : Summable fun v : CoprimeRow => (if v.1 0 = 0 then d₀ else 0) :=
    summable_of_ne_finset_zero (s := {vp, vm}) fun v hv => by
      refine ite_eq_right_iff.2 fun h0 => ?_
      rcases eq_vp_or_vm h0 with rfl | rfl <;> simp at hv
  have hP : P Y s z = E z s + d₀ := by
    have : ∑' v : CoprimeRow, H Y s (z.im / nq z v.1) =
        ∑' v : CoprimeRow, (term z s v.1 + if v.1 0 = 0 then d₀ else 0) :=
      tsum_congr fun v => by rw [← hD v]; ring
    rw [P, this, hsT.tsum_add hsD, hsumD, E]
    ring
  rw [hP, mul_add, ← Estar_eq z hs]
  unfold EstarY
  split_ifs with hY'
  · simp [d₀, H, hY']
  · rw [ct_eq_a0_of_one_lt hy hs, a0]
    simp only [d₀, H, hY', ↓reduceIte]
    rw [show completedRiemannZeta (2 * s - 1) = completedRiemannZeta (2 * s) *
      PavlovFaddeev.scatteringMatrix s from (scattering_mul hs).symm]
    ring


lemma measurable_ofXY : Measurable ofXY := by
  refine measurableEmbedding_coe.measurable_comp_iff.1 ?_
  have e : (UpperHalfPlane.coe ∘ ofXY) = fun p : ℝ × ℝ =>
      if 0 < p.2 then Complex.measurableEquivRealProd.symm p else ((Classical.choice inferInstance : ℍ) : ℂ) := by
    funext p
    simp only [Function.comp_apply, ofXY, ofComplex_apply_eq_ite]
    split_ifs <;> rfl
  rw [e]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    Complex.measurableEquivRealProd.symm.measurable measurable_const

lemma ofXY_im {p : ℝ × ℝ} (hp : 0 < p.2) : (ofXY p).im = p.2 := by
  rw [show p = (p.1, p.2) from rfl, ofXY_eq_pt hp, pt_im]

lemma ofXY_re {p : ℝ × ℝ} (hp : 0 < p.2) : (ofXY p).re = p.1 := by
  rw [show p = (p.1, p.2) from rfl, ofXY_eq_pt hp, pt_re]

/-- `y^a e^{−by}` is bounded on `y ≥ 1`. -/
lemma exists_rpow_mul_exp_le (a : ℝ) {b : ℝ} (hb : 0 < b) : ∃ B, ∀ y : ℝ, 1 ≤ y → y ^ a * rexp (-b * y) ≤ B := by
  set n := ⌈a⌉₊
  refine ⟨n.factorial / b ^ n, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have h1 : y ^ a ≤ y ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hy (Nat.le_ceil a)
  rw [Real.rpow_natCast] at h1
  have h2 := Real.pow_div_factorial_le_exp (b * y) (by positivity) n
  rw [mul_pow, div_le_iff₀ (by positivity)] at h2
  have h3 : y ^ n ≤ rexp (b * y) * n.factorial / b ^ n := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have he : rexp (-b * y) * rexp (b * y) = 1 := by rw [← Real.exp_add]; simp
  calc y ^ a * rexp (-b * y) ≤ (rexp (b * y) * n.factorial / b ^ n) * rexp (-b * y) :=
        mul_le_mul_of_nonneg_right (h1.trans h3) (Real.exp_pos _).le
    _ = n.factorial / b ^ n * (rexp (-b * y) * rexp (b * y)) := by ring
    _ = _ := by rw [he, mul_one]

/-- `|a₀(y, s)| ≤ (|Λ(2s)| + |Λ(2s − 1)|) y^{|Re s| + 1}` for `y ≥ 1`. -/
lemma norm_a0_le (s : ℂ) {y : ℝ} (hy : 1 ≤ y) :
    ‖a0 y s‖ ≤ (‖completedRiemannZeta (2 * s)‖ + ‖completedRiemannZeta (2 * s - 1)‖) * y ^ (|s.re| + 1) := by
  have hy0 : 0 < y := by linarith
  rw [a0]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
    add_mul]
  have e1 : y ^ s.re ≤ y ^ (|s.re| + 1) :=
    Real.rpow_le_rpow_of_exponent_le hy (by linarith [le_abs_self s.re])
  have e2 : y ^ (1 - s).re ≤ y ^ (|s.re| + 1) :=
    Real.rpow_le_rpow_of_exponent_le hy (by simp; linarith [neg_abs_le s.re])
  gcongr

lemma measurableSet_fd' : MeasurableSet (fd : Set ℍ) := measurableSet_fd

/-- The function `1_{Im z > Y} a₀(Im z, s₁)(E*(z, s₂) − a₀(Im z, s₂))`. -/
def gY (Y : ℝ) (s₁ s₂ : ℂ) (z : ℍ) : ℂ := if Y < z.im then ct z.im s₁ * (Estar z s₂ - ct z.im s₂) else 0

lemma measurable_gY (Y : ℝ) {s₁ s₂ : ℂ} (hs₁ : s₁ ∈ U) (hs₂ : s₂ ∈ U) : Measurable (gY Y s₁ s₂) := by
  obtain ⟨h0, hh, h1⟩ := mem_U.1 hs₁
  obtain ⟨h0', hh', h1'⟩ := mem_U.1 hs₂
  have e : gY Y s₁ s₂ = fun z => if Y < z.im then a0 z.im s₁ * (Estar z s₂ - a0 z.im s₂) else 0 := by
    funext z
    simp only [gY, ct_eq_a0 z.im_pos h0 hh h1, ct_eq_a0 z.im_pos h0' hh' h1']
  rw [e]
  exact Measurable.ite (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_coe))
    ((measurable_a0 s₁).mul ((measurable_Estar s₂).sub (measurable_a0 s₂))) measurable_const

lemma integrable_gY {Y : ℝ} (hY : 1 ≤ Y) {s₁ s₂ : ℂ} (hs₁ : s₁ ∈ U) (hs₂ : s₂ ∈ U) :
    Integrable (gY Y s₁ s₂) (volume.restrict fd) := by
  obtain ⟨h0, hh, h1⟩ := mem_U.1 hs₁
  obtain ⟨C, hC⟩ := norm_Estar_sub_ct_le (R := |(s₂ - 1 / 2).re|) (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨B, hB⟩ := exists_rpow_mul_exp_le (|s₁.re| + 1) (show 0 < π / 4 by positivity)
  set A := ‖completedRiemannZeta (2 * s₁)‖ + ‖completedRiemannZeta (2 * s₁ - 1)‖
  refine Integrable.mono' (integrable_const (A * |C| * |B|)) (measurable_gY Y hs₁ hs₂).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_fd).2 (Eventually.of_forall fun z hz => ?_)
  have hA : 0 ≤ A := by positivity
  unfold gY
  split_ifs with hYz
  · have hy1 : 1 ≤ z.im := hY.trans hYz.le
    rw [norm_mul, ct_eq_a0 z.im_pos h0 hh h1]
    have b1 := norm_a0_le s₁ hy1
    have b2 := hC s₂ le_rfl z (half_le_im_of_mem_fd hz)
    have b3 := hB z.im hy1
    have hp : 0 ≤ z.im ^ (|s₁.re| + 1) := Real.rpow_nonneg z.im_pos.le _
    calc ‖a0 z.im s₁‖ * ‖Estar z s₂ - ct z.im s₂‖
        ≤ (A * z.im ^ (|s₁.re| + 1)) * (|C| * rexp (-(π / 4) * z.im)) :=
          mul_le_mul b1 (b2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le))
            (norm_nonneg _) (by positivity)
      _ = A * |C| * (z.im ^ (|s₁.re| + 1) * rexp (-(π / 4) * z.im)) := by ring
      _ ≤ A * |C| * |B| := mul_le_mul_of_nonneg_left (b3.trans (le_abs_self B)) (by positivity)
  · simp only [norm_zero]; positivity

/-- On `Im z > Y ≥ 1`, `z ∈ 𝒟` iff `|re z| ≤ ½`. -/
lemma ofXY_mem_fd_iff {Y : ℝ} (hY : 1 ≤ Y) {p : ℝ × ℝ} (hp : Y < p.2) : ofXY p ∈ fd ↔ |p.1| ≤ 1 / 2 := by
  have hp0 : 0 < p.2 := by linarith
  have hre := ofXY_re hp0
  have him := ofXY_im hp0
  change 1 ≤ Complex.normSq (ofXY p : ℂ) ∧ |(ofXY p).re| ≤ 1 / 2 ↔ _
  rw [Complex.normSq_apply, hre]
  have : (ofXY p : ℂ).re = p.1 := hre
  have h2 : (ofXY p : ℂ).im = p.2 := him
  rw [this, h2]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by nlinarith [mul_self_nonneg p.1], h⟩

/-- **The constant term kills the cusp correction**: `∫_{𝒟, Im z > Y} a₀(Im z, s₁)(E*(z, s₂) − a₀(Im z, s₂)) dμ = 0`
for `Y ≥ 1`, by Fubini and `∫_{−1/2}^{1/2} E*(x + iy, s₂) dx = a₀(y, s₂)`. -/
theorem integral_gY {Y : ℝ} (hY : 1 ≤ Y) {s₁ s₂ : ℂ} (hs₁ : s₁ ∈ U) (hs₂ : s₂ ∈ U) :
    ∫ z in fd, gY Y s₁ s₂ z = 0 := by
  have hint := integrable_gY hY hs₁ hs₂
  rw [← integral_indicator measurableSet_fd, integral_eq_coords]
  have hint' := (integrable_iff_coords _).1 ((integrable_indicator_iff measurableSet_fd).2 hint)
  set F := fun p : ℝ × ℝ => (p.2 ^ (-2 : ℝ)) • (fd.indicator (gY Y s₁ s₂)) (ofXY p)
  set T : Set (ℝ × ℝ) := Icc (-(1 / 2)) (1 / 2) ×ˢ Ioi Y
  have hT : T ⊆ {p : ℝ × ℝ | 0 < p.2} := fun p hp => by
    have : Y < p.2 := hp.2
    show 0 < p.2
    linarith
  have hmT : MeasurableSet T := measurableSet_Icc.prod measurableSet_Ioi
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_lt measurable_const measurable_snd) hT
    (fun p hp => ?_)]
  swap
  · obtain ⟨hp1, hp2⟩ := hp
    have hp0 : 0 < p.2 := hp1
    try simp only [F]
    by_cases hY' : Y < p.2
    · have : ofXY p ∉ fd := by
        rw [ofXY_mem_fd_iff hY hY', abs_le]
        intro h
        exact hp2 ⟨h, hY'⟩
      rw [indicator_of_notMem this, smul_zero]
    · by_cases hm : ofXY p ∈ fd
      · rw [indicator_of_mem hm, gY, ofXY_im hp0]
        simp only [hY', ↓reduceIte, smul_zero]
      · rw [indicator_of_notMem hm, smul_zero]
  have hintT : IntegrableOn F T := hint'.mono_set hT
  rw [show T = Icc (-(1 / 2)) (1 / 2) ×ˢ Ioi Y from rfl, IntegrableOn, Measure.volume_eq_prod,
    ← Measure.prod_restrict] at hintT
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod_symm _ hintT]
  refine integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_))
  have hy : Y < y := hy
  have hy0 : 0 < y := by linarith
  have hcont := continuous_Estar_x hy0 s₂
  have e : ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), F (x, y) =
      (y ^ (-2 : ℝ)) • (ct y s₁ * (Estar (pt x y hy0) s₂ - ct y s₂)) := by
    intro x hx
    have hm : ofXY (x, y) ∈ fd := (ofXY_mem_fd_iff hY hy).2 (abs_le.2 hx)
    simp only [F]
    rw [indicator_of_mem hm, gY, ofXY_eq_pt hy0, pt_im]
    simp only [hy, ↓reduceIte]
  show ∫ x in Icc (-(1 / 2) : ℝ) (1 / 2), F (x, y) = 0
  rw [setIntegral_congr_fun measurableSet_Icc e, integral_smul, integral_const_mul,
    integral_sub (hcont.integrableOn_Icc) (integrableOn_const (by simp) (by simp))]
  have hper : ∫ x in Icc (-(1 / 2) : ℝ) (1 / 2), Estar (pt x y hy0) s₂ = ct y s₂ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), ct_pos hy0]
    have := (Estar_periodic hy0 s₂).intervalIntegral_add_eq (-(1 / 2)) 0
    norm_num at this ⊢
    exact this
  rw [hper, setIntegral_const]
  norm_num

/-- **Dropping one truncation**: for `Y ≥ 1` and `s₁, s₂ ∈ ℂ \ {0, ½, 1}`,
`∫_𝒟 E*^Y(z, s₁)E*^Y(z, s₂) dμ = ∫_𝒟 E*(z, s₁)E*^Y(z, s₂) dμ`. -/
theorem integral_EstarY_mul_eq {Y : ℝ} (hY : 1 ≤ Y) {s₁ s₂ : ℂ} (hs₁ : s₁ ∈ U) (hs₂ : s₂ ∈ U) :
    ∫ z in fd, EstarY Y s₁ z * EstarY Y s₂ z = ∫ z in fd, Estar z s₁ * EstarY Y s₂ z := by
  have e : ∀ z ∈ (fd : Set ℍ), Estar z s₁ * EstarY Y s₂ z = EstarY Y s₁ z * EstarY Y s₂ z + gY Y s₁ s₂ z := by
    intro z _
    unfold EstarY gY
    split_ifs with h1 h2 <;> first | (exfalso; linarith) | ring
  rw [setIntegral_congr_fun measurableSet_fd e, integral_add (integrable_EstarY_mul Y hs₁ hs₂)
    (integrable_gY hY hs₁ hs₂), integral_gY hY hs₁ hs₂, add_zero]

/-! ## The real majorant `E(z, σ)` -/

/-- `E(z, σ) = ½Σ_{(c, d) coprime}(y/|cz + d|²)^σ` for real `σ`, as a real number. -/
def Er (z : ℍ) (σ : ℝ) : ℝ := (1 / 2) * ∑' v : CoprimeRow, (z.im / nq z v.1) ^ σ

lemma Er_nonneg (z : ℍ) (σ : ℝ) : 0 ≤ Er z σ :=
  mul_nonneg (by norm_num) (tsum_nonneg fun v => Real.rpow_nonneg (div_nonneg z.im_pos.le (nq_nonneg _ _)) _)

lemma E_ofReal (z : ℍ) (σ : ℝ) : E z σ = (Er z σ : ℂ) := by
  rw [E, Er, Complex.ofReal_mul, Complex.ofReal_tsum]
  push_cast
  congr 1
  refine tsum_congr fun v => ?_
  rw [term, ← Complex.ofReal_cpow (div_nonneg z.im_pos.le (nq_nonneg _ _))]

lemma norm_E_le (z : ℍ) {s : ℂ} (hs : 1 < s.re) : ‖E z s‖ ≤ Er z s.re := by
  rw [E, Er, norm_mul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [this]
  refine mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm (summable_norm_E z hs)).trans (le_of_eq ?_))
    (by norm_num)
  exact tsum_congr fun v => norm_term z (by linarith) v.1

lemma norm_Estar_le (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    ‖Estar z s‖ ≤ ‖completedRiemannZeta (2 * s)‖ * Er z s.re := by
  rw [Estar_eq z hs, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_E_le z hs) (norm_nonneg _)

lemma measurable_Er (σ : ℝ) : Measurable fun z : ℍ => Er z σ := by
  unfold Er
  refine measurable_const.mul (Measurable.tsum fun v => ?_)
  have hn : Measurable fun z : ℍ => nq z v.1 := by
    unfold nq
    exact Complex.continuous_normSq.measurable.comp
      ((measurable_const.mul measurable_coe).add measurable_const)
  exact ((Complex.measurable_im.comp measurable_coe).div hn).pow_const _

lemma E_eq_div (z : ℍ) {s : ℂ} (hs : 1 < s.re) : E z s = Estar z s / completedRiemannZeta (2 * s) := by
  have hΛ : completedRiemannZeta (2 * s) ≠ 0 :=
    PavlovFaddeev.completed_ne_zero_of_one_le_re (by simp; linarith)
  rw [Estar_eq z hs]
  field_simp

lemma continuous_Er_x {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : 1 < σ) : Continuous fun x => Er (pt x y hy) σ := by
  have h : Continuous fun x => E (pt x y hy) σ := by
    have hs : 1 < (σ : ℂ).re := by simpa using hσ
    simp_rw [E_eq_div _ hs]
    exact (continuous_Estar_x hy _).div_const _
  simp_rw [E_ofReal] at h
  have := Complex.continuous_re.comp h
  exact this.congr fun x => by simp

lemma Er_T (z : ℍ) (σ : ℝ) : Er (T • z) σ = Er z σ := by
  have h := E_smul T z σ
  rw [E_ofReal, E_ofReal] at h
  exact_mod_cast h

lemma integral_Er {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : 1 < σ) :
    ((∫ x in (0 : ℝ)..1, Er (pt x y hy) σ : ℝ) : ℂ) =
      (y : ℂ) ^ (σ : ℂ) + PavlovFaddeev.scatteringMatrix σ * (y : ℂ) ^ (1 - (σ : ℂ)) := by
  rw [← constTerm_eq hy (by simpa using hσ)]
  simp_rw [E_ofReal]
  rw [intervalIntegral.integral_ofReal]

lemma integral_Er_le {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : 1 < σ) :
    ∫ x in Ico (0 : ℝ) 1, Er (pt x y hy) σ ≤ y ^ σ + ‖PavlovFaddeev.scatteringMatrix σ‖ * y ^ (1 - σ) := by
  have e : ∫ x in Ico (0 : ℝ) 1, Er (pt x y hy) σ = ∫ x in (0 : ℝ)..1, Er (pt x y hy) σ := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  rw [e]
  refine (Real.le_norm_self _).trans ?_
  rw [← Complex.norm_real, integral_Er hy hσ]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-! ## Integrability of the profile -/

lemma integrableOn_Ioc_rpow {Y a : ℝ} (ha : -1 < a) : IntegrableOn (fun y : ℝ => y ^ a) (Ioc 0 Y) := by
  rcases le_or_gt 0 Y with hY | hY
  · exact (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Y) ha).1
  · rw [Ioc_eq_empty (by linarith)]; exact integrableOn_empty

lemma integrableOn_profile {Y σ₁ σ₂ A B : ℝ} (hY : 0 < Y) (h1 : 1 < σ₁ + σ₂) (h2 : σ₁ < σ₂) :
    IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ) * (if y ≤ Y then y ^ σ₂ else B * y ^ (1 - σ₂)) *
      (y ^ σ₁ + A * y ^ (1 - σ₁))) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hY.le]
  refine IntegrableOn.union ?_ ?_
  · have hi : IntegrableOn (fun y : ℝ => y ^ (σ₁ + σ₂ - 2) + A * y ^ (σ₂ - σ₁ - 1)) (Ioc 0 Y) :=
      (integrableOn_Ioc_rpow (by linarith)).add ((integrableOn_Ioc_rpow (by linarith)).const_mul A)
    refine hi.congr_fun (fun y hy => ?_) measurableSet_Ioc
    have hy0 : 0 < y := hy.1
    simp only [hy.2, ↓reduceIte]
    have e1 : y ^ (-2 : ℝ) * y ^ σ₂ * y ^ σ₁ = y ^ (σ₁ + σ₂ - 2) := by
      rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]; ring_nf
    have e2 : y ^ (-2 : ℝ) * y ^ σ₂ * y ^ (1 - σ₁) = y ^ (σ₂ - σ₁ - 1) := by
      rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]; ring_nf
    rw [← e1, ← e2]
    ring
  · have hi : IntegrableOn (fun y : ℝ => B * y ^ (σ₁ - σ₂ - 1) + B * A * y ^ (-σ₁ - σ₂)) (Ioi Y) :=
      ((integrableOn_Ioi_rpow_of_lt (by linarith) hY).const_mul B).add
        ((integrableOn_Ioi_rpow_of_lt (by linarith) hY).const_mul (B * A))
    refine hi.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := hY.trans hy
    have : ¬ y ≤ Y := not_le.2 hy
    simp only [this, ↓reduceIte]
    have e1 : y ^ (-2 : ℝ) * y ^ (1 - σ₂) * y ^ σ₁ = y ^ (σ₁ - σ₂ - 1) := by
      rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]; ring_nf
    have e2 : y ^ (-2 : ℝ) * y ^ (1 - σ₂) * y ^ (1 - σ₁) = y ^ (-σ₁ - σ₂) := by
      rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]; ring_nf
    rw [← e1, ← e2]
    ring

lemma measurable_H (Y : ℝ) (s : ℂ) : Measurable (H Y s) := by
  unfold H
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    (Complex.measurable_ofReal.pow_const _)
    ((measurable_const.mul (Complex.measurable_ofReal.pow_const _)).neg)

lemma norm_H {Y : ℝ} (s : ℂ) {y : ℝ} (hy : 0 < y) :
    ‖H Y s y‖ = if y ≤ Y then y ^ s.re else ‖PavlovFaddeev.scatteringMatrix s‖ * y ^ (1 - s.re) := by
  unfold H
  split_ifs
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  · rw [norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp


/-! ## The unfolded integrand on the strip -/

/-- The unfolded integrand `E*(w, s₁)H_Y(Im w, s₂)`. -/
def fS (Y : ℝ) (s₁ s₂ : ℂ) (w : ℍ) : ℂ := Estar w s₁ * H Y s₂ w.im

lemma measurable_fS (Y : ℝ) (s₁ s₂ : ℂ) : Measurable (fS Y s₁ s₂) :=
  (measurable_Estar s₁).mul ((measurable_H Y s₂).comp (Complex.measurable_im.comp measurable_coe))

lemma ofXY_mem_strip_iff {p : ℝ × ℝ} (hp : 0 < p.2) : ofXY p ∈ strip ↔ p.1 ∈ Ico (0 : ℝ) 1 := by
  change 0 ≤ (ofXY p).re ∧ (ofXY p).re < 1 ↔ _
  rw [ofXY_re hp]
  rfl

/-- **The unfolded integrand is integrable on the strip** for `1 < Re s₁ < Re s₂`: in coordinates it is dominated by
`|Λ(2s₁)|E(x + iy, Re s₁)|H_Y(y, s₂)|y^{−2}`, whose `x`-integral is `≤ |Λ(2s₁)|(y^{σ₁} + |φ(σ₁)|y^{1−σ₁})|H_Y(y, s₂)|y^{−2}`,
integrable on `y > 0`. -/
theorem integrableOn_fS {Y : ℝ} (hY : 0 < Y) {s₁ s₂ : ℂ} (h1 : 1 < s₁.re) (h12 : s₁.re < s₂.re) :
    IntegrableOn (fS Y s₁ s₂) strip := by
  rw [← integrable_indicator_iff measurableSet_strip, integrable_iff_coords]
  set A := ‖completedRiemannZeta (2 * s₁)‖
  set σ₁ := s₁.re
  set Gc : ℝ × ℝ → ℝ := fun p => (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)).indicator
    (fun p => p.2 ^ (-2 : ℝ) * (A * Er (ofXY p) σ₁ * ‖H Y s₂ p.2‖)) p
  have hGm : Measurable Gc := by
    refine Measurable.indicator ?_ (measurableSet_Ico.prod measurableSet_Ioi)
    exact (measurable_snd.pow_const _).mul ((measurable_const.mul ((measurable_Er σ₁).comp measurable_ofXY)).mul
      ((measurable_H Y s₂).comp measurable_snd).norm)
  have hG0 : ∀ p, 0 ≤ Gc p := fun p => by
    simp only [Gc]
    refine indicator_nonneg (fun p hp => ?_) p
    have : 0 < p.2 := hp.2
    have := Er_nonneg (ofXY p) σ₁
    positivity
  have hsec : ∀ {y : ℝ} (hy : 0 < y), (fun x => Gc (x, y)) =
      (Ico (0 : ℝ) 1).indicator (fun x => y ^ (-2 : ℝ) * (A * Er (pt x y hy) σ₁ * ‖H Y s₂ y‖)) := by
    intro y hy
    funext x
    by_cases hx : x ∈ Ico (0 : ℝ) 1
    · rw [indicator_of_mem hx]
      simp only [Gc]
      rw [indicator_of_mem (show (x, y) ∈ Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) from ⟨hx, hy⟩), ofXY_eq_pt hy]
    · rw [indicator_of_notMem hx]
      simp only [Gc]
      exact indicator_of_notMem (fun h => hx h.1) _
  have hG : Integrable Gc := by
    rw [Measure.volume_eq_prod, integrable_prod_iff' hGm.aestronglyMeasurable]
    constructor
    · refine Eventually.of_forall fun y => ?_
      by_cases hy : 0 < y
      · rw [hsec hy]
        refine IntegrableOn.integrable_indicator ?_ measurableSet_Ico
        exact ((continuous_const.mul ((continuous_const.mul (continuous_Er_x hy h1)).mul
          continuous_const)).integrableOn_Icc).mono_set Ico_subset_Icc_self
      · have e : (fun x => Gc (x, y)) = 0 := funext fun x => indicator_of_notMem (fun h => hy h.2) _
        rw [e]; exact integrable_zero _ _ _
    · have hprof := (integrableOn_profile (A := ‖PavlovFaddeev.scatteringMatrix σ₁‖)
        (B := ‖PavlovFaddeev.scatteringMatrix s₂‖) hY (show 1 < σ₁ + s₂.re by linarith) h12).const_mul A
      refine Integrable.mono' ((integrable_indicator_iff measurableSet_Ioi).2 hprof)
        (hGm.norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      have hnn : 0 ≤ ∫ x, ‖Gc (x, y)‖ := integral_nonneg fun x => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      by_cases hy : 0 < y
      · rw [indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy)]
        simp_rw [Real.norm_of_nonneg (hG0 _)]
        rw [hsec hy, integral_indicator measurableSet_Ico]
        simp_rw [show ∀ x, y ^ (-2 : ℝ) * (A * Er (pt x y hy) σ₁ * ‖H Y s₂ y‖) =
          (y ^ (-2 : ℝ) * A * ‖H Y s₂ y‖) * Er (pt x y hy) σ₁ from fun x => by ring]
        rw [integral_const_mul, norm_H s₂ hy]
        have hb := integral_Er_le hy h1
        have hc : 0 ≤ y ^ (-2 : ℝ) * A * (if y ≤ Y then y ^ s₂.re
            else ‖PavlovFaddeev.scatteringMatrix s₂‖ * y ^ (1 - s₂.re)) := by
          have : 0 ≤ (if y ≤ Y then y ^ s₂.re else ‖PavlovFaddeev.scatteringMatrix s₂‖ * y ^ (1 - s₂.re)) := by
            split_ifs <;> positivity
          positivity
        calc _ ≤ y ^ (-2 : ℝ) * A * (if y ≤ Y then y ^ s₂.re
              else ‖PavlovFaddeev.scatteringMatrix s₂‖ * y ^ (1 - s₂.re)) *
              (y ^ σ₁ + ‖PavlovFaddeev.scatteringMatrix σ₁‖ * y ^ (1 - σ₁)) := mul_le_mul_of_nonneg_left hb hc
          _ = _ := by ring
      · have e : (fun x => ‖Gc (x, y)‖) = 0 := funext fun x => by
          simp only [Gc, Pi.zero_apply, norm_eq_zero]
          exact indicator_of_notMem (fun h => hy h.2) _
        rw [e, indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy)]
        simp
  refine Integrable.mono' hG.integrableOn
    (((measurable_snd.pow_const _).smul (((measurable_fS Y s₁ s₂).indicator measurableSet_strip).comp
      measurable_ofXY)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' (measurableSet_lt measurable_const measurable_snd)).2
    (Eventually.of_forall fun p (hp : 0 < p.2) => ?_)
  by_cases hx : p.1 ∈ Ico (0 : ℝ) 1
  · have hm : ofXY p ∈ strip := (ofXY_mem_strip_iff hp).2 hx
    simp only [Gc]
    rw [indicator_of_mem hm, indicator_of_mem (show p ∈ Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) from ⟨hx, hp⟩), norm_smul,
      Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), fS, norm_mul, ofXY_im hp]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (Real.rpow_nonneg hp.le _)
    exact norm_Estar_le _ h1
  · have hm : ofXY p ∉ strip := fun h => hx ((ofXY_mem_strip_iff hp).1 h)
    rw [indicator_of_notMem hm, smul_zero, norm_zero]
    exact hG0 p

/-- **The unfolded integral in coordinates**:
`∫_{0 ≤ re < 1} E*(w, s₁)H_Y(Im w, s₂) dμ = ∫_0^∞ a₀(y, s₁)H_Y(y, s₂) y^{−2} dy`, by Fubini. -/
theorem integral_fS {Y : ℝ} (hY : 0 < Y) {s₁ s₂ : ℂ} (h1 : 1 < s₁.re) (h12 : s₁.re < s₂.re) :
    ∫ z in strip, fS Y s₁ s₂ z = ∫ y in Ioi (0 : ℝ), (y ^ (-2 : ℝ)) • (ct y s₁ * H Y s₂ y) := by
  have hint := integrableOn_fS hY h1 h12
  have hint' := (integrable_iff_coords _).1 ((integrable_indicator_iff measurableSet_strip).2 hint)
  rw [← integral_indicator measurableSet_strip, integral_eq_coords]
  set F := fun p : ℝ × ℝ => (p.2 ^ (-2 : ℝ)) • (strip.indicator (fS Y s₁ s₂)) (ofXY p)
  have hT : Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) ⊆ {p : ℝ × ℝ | 0 < p.2} := fun p hp => hp.2
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_lt measurable_const measurable_snd) hT
    (fun p hp => ?_)]
  swap
  · obtain ⟨hp1, hp2⟩ := hp
    have hp0 : 0 < p.2 := hp1
    have hx : p.1 ∉ Ico (0 : ℝ) 1 := fun h => hp2 ⟨h, hp0⟩
    have hm : ofXY p ∉ strip := fun h => hx ((ofXY_mem_strip_iff hp0).1 h)
    try simp only [F]
    rw [indicator_of_notMem hm, smul_zero]
  have hintT := hint'.mono_set hT
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hintT
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hintT]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
  have e : ∀ x ∈ Ico (0 : ℝ) 1, F (x, y) = (y ^ (-2 : ℝ)) • (Estar (pt x y hy) s₁ * H Y s₂ y) := by
    intro x hx
    have hm : ofXY (x, y) ∈ strip := (ofXY_mem_strip_iff hy).2 hx
    simp only [F]
    rw [indicator_of_mem hm, fS, ofXY_eq_pt hy, pt_im]
  show ∫ x in Ico (0 : ℝ) 1, F (x, y) = _
  rw [setIntegral_congr_fun measurableSet_Ico e, integral_smul, integral_mul_const, ct_pos hy,
    intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

/-! ## The one-dimensional integral -/

lemma integrableOn_Ioc_cpow {Y : ℝ} (_hY : 0 < Y) {a : ℂ} (ha : -1 < a.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ a) (Ioc 0 Y) :=
  (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := Y) ha).1

lemma integral_Ioc_cpow {Y : ℝ} (hY : 0 < Y) {a : ℂ} (ha : -1 < a.re) :
    ∫ y in Ioc (0 : ℝ) Y, (y : ℂ) ^ a = (Y : ℂ) ^ (a + 1) / (a + 1) := by
  have ha1 : a + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [← intervalIntegral.integral_of_le hY.le, integral_cpow (Or.inl ha), Complex.ofReal_zero,
    Complex.zero_cpow ha1, sub_zero]

lemma cpow_combine {y : ℝ} (hy : 0 < y) (a b : ℂ) :
    (y : ℂ) ^ a * (y : ℂ) ^ b * (y : ℂ) ^ (-2 : ℂ) = (y : ℂ) ^ (a + b - 2) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [← Complex.cpow_add _ _ hy0, ← Complex.cpow_add _ _ hy0]
  ring_nf

/-- **The profile integral**: for `Y > 0`, `Re(s₁ + s₂) > 1` and `Re s₁ < Re s₂`,
`∫_0^∞ a₀(y, s₁)H_Y(y, s₂)y^{−2} dy = Λ(2s₁)Y^{s₁+s₂−1}/(s₁ + s₂ − 1) + Λ(2s₁ − 1)Y^{s₂−s₁}/(s₂ − s₁)
  − φ(s₂)(Λ(2s₁)Y^{s₁−s₂}/(s₂ − s₁) + Λ(2s₁ − 1)Y^{1−s₁−s₂}/(s₁ + s₂ − 1))`. -/
theorem integral_a0_H {Y : ℝ} (hY : 0 < Y) {s₁ s₂ : ℂ} (h1 : 1 < (s₁ + s₂).re) (h2 : s₁.re < s₂.re) :
    ∫ y in Ioi (0 : ℝ), (y ^ (-2 : ℝ)) • (a0 y s₁ * H Y s₂ y) =
      completedRiemannZeta (2 * s₁) * ((Y : ℂ) ^ (s₁ + s₂ - 2 + 1) / (s₁ + s₂ - 2 + 1)) +
        completedRiemannZeta (2 * s₁ - 1) * ((Y : ℂ) ^ ((1 - s₁) + s₂ - 2 + 1) / ((1 - s₁) + s₂ - 2 + 1)) +
      -PavlovFaddeev.scatteringMatrix s₂ *
        (completedRiemannZeta (2 * s₁) * (-(Y : ℂ) ^ (s₁ + (1 - s₂) - 2 + 1) / (s₁ + (1 - s₂) - 2 + 1)) +
          completedRiemannZeta (2 * s₁ - 1) *
            (-(Y : ℂ) ^ ((1 - s₁) + (1 - s₂) - 2 + 1) / ((1 - s₁) + (1 - s₂) - 2 + 1))) := by
  set L₁ := completedRiemannZeta (2 * s₁)
  set L₁' := completedRiemannZeta (2 * s₁ - 1)
  set φ₂ := PavlovFaddeev.scatteringMatrix s₂
  simp only [add_re] at h1
  have r1 : -1 < (s₁ + s₂ - 2).re := by simp; linarith
  have r2 : -1 < ((1 - s₁) + s₂ - 2).re := by simp; linarith
  have r3 : (s₁ + (1 - s₂) - 2).re < -1 := by simp; linarith
  have r4 : ((1 - s₁) + (1 - s₂) - 2).re < -1 := by simp; linarith
  have eA : ∀ y ∈ Ioc (0 : ℝ) Y, (y ^ (-2 : ℝ)) • (a0 y s₁ * H Y s₂ y) =
      L₁ * (y : ℂ) ^ (s₁ + s₂ - 2) + L₁' * (y : ℂ) ^ ((1 - s₁) + s₂ - 2) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    rw [Complex.real_smul, Complex.ofReal_cpow hy0.le, a0, H]
    simp only [hy.2, ↓reduceIte]
    rw [← cpow_combine hy0, ← cpow_combine hy0]
    push_cast
    ring
  have eB : ∀ y ∈ Ioi Y, (y ^ (-2 : ℝ)) • (a0 y s₁ * H Y s₂ y) =
      -φ₂ * (L₁ * (y : ℂ) ^ (s₁ + (1 - s₂) - 2) + L₁' * (y : ℂ) ^ ((1 - s₁) + (1 - s₂) - 2)) := by
    intro y hy
    have hy0 : 0 < y := hY.trans hy
    have hy' : ¬y ≤ Y := not_le.2 hy
    rw [Complex.real_smul, Complex.ofReal_cpow hy0.le, a0, H]
    simp only [hy', ↓reduceIte]
    rw [← cpow_combine hy0, ← cpow_combine hy0]
    push_cast
    ring
  have iA : IntegrableOn (fun y : ℝ => L₁ * (y : ℂ) ^ (s₁ + s₂ - 2) + L₁' * (y : ℂ) ^ ((1 - s₁) + s₂ - 2))
      (Ioc 0 Y) :=
    ((integrableOn_Ioc_cpow hY r1).const_mul _).add ((integrableOn_Ioc_cpow hY r2).const_mul _)
  have iB : IntegrableOn (fun y : ℝ => -φ₂ * (L₁ * (y : ℂ) ^ (s₁ + (1 - s₂) - 2) +
      L₁' * (y : ℂ) ^ ((1 - s₁) + (1 - s₂) - 2))) (Ioi Y) :=
    (((integrableOn_Ioi_cpow_of_lt r3 hY).const_mul _).add
      ((integrableOn_Ioi_cpow_of_lt r4 hY).const_mul _)).const_mul _
  rw [← Ioc_union_Ioi_eq_Ioi hY.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (iA.congr_fun (fun y hy => (eA y hy).symm) measurableSet_Ioc)
    (iB.congr_fun (fun y hy => (eB y hy).symm) measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioc eA, setIntegral_congr_fun measurableSet_Ioi eB,
    integral_add ((integrableOn_Ioc_cpow hY r1).const_mul _) ((integrableOn_Ioc_cpow hY r2).const_mul _),
    integral_const_mul, integral_const_mul, integral_Ioc_cpow hY r1, integral_Ioc_cpow hY r2,
    integral_const_mul, integral_add ((integrableOn_Ioi_cpow_of_lt r3 hY).const_mul _)
      ((integrableOn_Ioi_cpow_of_lt r4 hY).const_mul _),
    integral_const_mul, integral_const_mul, integral_Ioi_cpow_of_lt r3 hY, integral_Ioi_cpow_of_lt r4 hY]


/-! ## The Maass–Selberg relation in the region of absolute convergence -/

/-- The right-hand side of the **Maass–Selberg relation** for `E*`. -/
def MS (Y : ℝ) (s₁ s₂ : ℂ) : ℂ :=
  (completedRiemannZeta (2 * s₁) * completedRiemannZeta (2 * s₂) * (Y : ℂ) ^ (s₁ + s₂ - 1) -
      completedRiemannZeta (2 * s₁ - 1) * completedRiemannZeta (2 * s₂ - 1) * (Y : ℂ) ^ (1 - s₁ - s₂)) /
      (s₁ + s₂ - 1) +
    (completedRiemannZeta (2 * s₁) * completedRiemannZeta (2 * s₂ - 1) * (Y : ℂ) ^ (s₁ - s₂) -
      completedRiemannZeta (2 * s₁ - 1) * completedRiemannZeta (2 * s₂) * (Y : ℂ) ^ (s₂ - s₁)) / (s₁ - s₂)

lemma mem_U_of_one_lt {s : ℂ} (hs : 1 < s.re) : s ∈ U := by
  rw [mem_U]
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> norm_num at hs

lemma fS_T (Y : ℝ) (s₁ s₂ : ℂ) (z : ℍ) : fS Y s₁ s₂ (T • z) = fS Y s₁ s₂ z := by
  simp only [fS, Estar_smul, im_T_smul]

/-- **Maass–Selberg, region of absolute convergence**: for `Y ≥ 1` and `1 < Re s₁ < Re s₂`,
`∫_F E*^Y(z, s₁)E*^Y(z, s₂) dμ = MS Y s₁ s₂`. -/
theorem integral_EstarY_mul_region {Y : ℝ} (hY : 1 ≤ Y) {s₁ s₂ : ℂ} (h1 : 1 < s₁.re) (h12 : s₁.re < s₂.re) :
    ∫ z in fd, EstarY Y s₁ z * EstarY Y s₂ z = MS Y s₁ s₂ := by
  have h2 : 1 < s₂.re := h1.trans h12
  have hY0 : 0 < Y := one_pos.trans_le hY
  rw [integral_EstarY_mul_eq hY (mem_U_of_one_lt h1) (mem_U_of_one_lt h2),
    setIntegral_congr_fun measurableSet_fd (fun z hz => by rw [EstarY_eq_P hY h2 hz])]
  have hpt : ∀ z, Estar z s₁ * (completedRiemannZeta (2 * s₂) * P Y s₂ z) =
      completedRiemannZeta (2 * s₂) * ((1 / 2) * ∑' v : CoprimeRow, fS Y s₁ s₂ (gam v • z)) := by
    intro z
    have : ∑' v : CoprimeRow, fS Y s₁ s₂ (gam v • z) =
        Estar z s₁ * ∑' v : CoprimeRow, H Y s₂ (z.im / nq z v.1) := by
      rw [← tsum_mul_left]
      congr 1; ext v
      rw [fS, Estar_smul, im_gam_smul]
    rw [this, P]; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_const_mul,
    integral_fd_tsum _ (measurable_fS Y s₁ s₂) (fS_T Y s₁ s₂) (integrableOn_fS hY0 h1 h12),
    integral_fS hY0 h1 h12,
    setIntegral_congr_fun measurableSet_Ioi (fun y (hy : 0 < y) => by rw [ct_eq_a0_of_one_lt hy h1]),
    integral_a0_H hY0 (by simp; linarith) h12]
  have hφ := scattering_mul h2
  have d1 : s₁ + s₂ - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have d2 : s₁ - s₂ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have d3 : s₂ - s₁ ≠ 0 := fun h => d2 (by linear_combination -h)
  have d4 : 1 - s₁ - s₂ ≠ 0 := fun h => d1 (by linear_combination -h)
  have e1 : s₁ + s₂ - 2 + 1 = s₁ + s₂ - 1 := by ring
  have e2 : (1 - s₁) + s₂ - 2 + 1 = s₂ - s₁ := by ring
  have e3 : s₁ + (1 - s₂) - 2 + 1 = s₁ - s₂ := by ring
  have e4 : (1 - s₁) + (1 - s₂) - 2 + 1 = 1 - s₁ - s₂ := by ring
  rw [e1, e2, e3, e4, MS, ← hφ]
  field_simp
  ring

/-! ## Analytic continuation to `s₁, s₂ ∉ {0, ½, 1}` -/

/-- The truncated inner product `I_Y(s₁, s₂) = ∫_F E*^Y(z, s₁)E*^Y(z, s₂) dμ(z)`. -/
def IY (Y : ℝ) (s₁ s₂ : ℂ) : ℂ := ∫ z in fd, EstarY Y s₁ z * EstarY Y s₂ z

lemma IY_comm (Y : ℝ) (s₁ s₂ : ℂ) : IY Y s₁ s₂ = IY Y s₂ s₁ := by
  simp only [IY, mul_comm]

/-- The Maass–Selberg right-hand side with denominators cleared: `(s₁ + s₂ − 1)(s₁ − s₂) · MS`. -/
def NS (Y : ℝ) (s₁ s₂ : ℂ) : ℂ :=
  (s₁ - s₂) * (completedRiemannZeta (2 * s₁) * completedRiemannZeta (2 * s₂) * (Y : ℂ) ^ (s₁ + s₂ - 1) -
      completedRiemannZeta (2 * s₁ - 1) * completedRiemannZeta (2 * s₂ - 1) * (Y : ℂ) ^ (1 - s₁ - s₂)) +
    (s₁ + s₂ - 1) * (completedRiemannZeta (2 * s₁) * completedRiemannZeta (2 * s₂ - 1) * (Y : ℂ) ^ (s₁ - s₂) -
      completedRiemannZeta (2 * s₁ - 1) * completedRiemannZeta (2 * s₂) * (Y : ℂ) ^ (s₂ - s₁))

lemma NS_swap (Y : ℝ) (s₁ s₂ : ℂ) : NS Y s₂ s₁ = -NS Y s₁ s₂ := by
  simp only [NS]
  rw [show s₂ + s₁ - 1 = s₁ + s₂ - 1 by ring, show 1 - s₂ - s₁ = 1 - s₁ - s₂ by ring]
  try ring

lemma differentiableAt_Lam {s : ℂ} (hs : s ∈ U) :
    DifferentiableAt ℂ (fun s => completedRiemannZeta (2 * s)) s ∧
      DifferentiableAt ℂ (fun s => completedRiemannZeta (2 * s - 1)) s := by
  obtain ⟨h0, h12, h1⟩ := mem_U.1 hs
  refine ⟨(differentiableAt_completedZeta ?_ ?_).comp s (differentiableAt_id.const_mul 2),
    (differentiableAt_completedZeta ?_ ?_).comp s ((differentiableAt_id.const_mul 2).sub_const 1)⟩
  · exact mul_ne_zero two_ne_zero h0
  · intro h; apply h12; linear_combination h / 2
  · intro h; apply h12; linear_combination h / 2
  · intro h; apply h1; linear_combination h / 2

lemma differentiableAt_NS {Y : ℝ} (hY : 0 < Y) {s₁ s : ℂ} (hs : s ∈ U) :
    DifferentiableAt ℂ (fun s₂ => NS Y s₁ s₂) s := by
  obtain ⟨d1, d2⟩ := differentiableAt_Lam hs
  have hc : ∀ {f : ℂ → ℂ}, DifferentiableAt ℂ f s → DifferentiableAt ℂ (fun w => (Y : ℂ) ^ f w) s :=
    fun hf => hf.const_cpow (Or.inl (by exact_mod_cast hY.ne'))
  simp only [NS]
  refine ((differentiableAt_const _).sub differentiableAt_id).mul
    ((((differentiableAt_const _).mul d1).mul (hc ?_)).sub
      (((differentiableAt_const _).mul d2).mul (hc ?_))) |>.add
    ((((differentiableAt_const _).add differentiableAt_id).sub (differentiableAt_const _)).mul
    ((((differentiableAt_const _).mul d2).mul (hc ?_)).sub
      (((differentiableAt_const _).mul d1).mul (hc ?_)))) <;> fun_prop

lemma differentiableAt_IY (Y : ℝ) {s₁ s : ℂ} (hs₁ : s₁ ∈ U) (hs : s ∈ U) :
    DifferentiableAt ℂ (fun s₂ => IY Y s₁ s₂) s :=
  (differentiableOn_integral_EstarY Y hs₁ s hs).differentiableAt (isOpen_U.mem_nhds hs)

lemma MS_cleared {Y : ℝ} {s₁ s₂ : ℂ} (h1 : s₁ + s₂ - 1 ≠ 0) (h2 : s₁ - s₂ ≠ 0) :
    (s₁ + s₂ - 1) * (s₁ - s₂) * MS Y s₁ s₂ = NS Y s₁ s₂ := by
  simp only [MS, NS]
  field_simp

/-- The identity theorem on the connected open set `U = ℂ ∖ {0, ½, 1}`. -/
lemma eq_on_U {g : ℂ → ℂ} (hg : ∀ s ∈ U, DifferentiableAt ℂ g s) {V : Set ℂ} (hV : IsOpen V) {z₀ : ℂ}
    (hz₀ : z₀ ∈ V) (hzU : z₀ ∈ U) (h0 : ∀ s ∈ V, g s = 0) {s : ℂ} (hs : s ∈ U) : g s = 0 := by
  have ha : AnalyticOnNhd ℂ g U :=
    (show DifferentiableOn ℂ g U from fun s hs => (hg s hs).differentiableWithinAt).analyticOnNhd isOpen_U
  have hev : g =ᶠ[𝓝 z₀] 0 := Filter.eventually_of_mem (hV.mem_nhds hz₀) fun s hs => h0 s hs
  exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_U hzU hev hs

lemma IY_cleared_aux {Y : ℝ} (hY : 1 ≤ Y) {s₁ s₂ : ℂ} (h1 : 1 < s₁.re) (hs₂ : s₂ ∈ U) :
    (s₁ + s₂ - 1) * (s₁ - s₂) * IY Y s₁ s₂ = NS Y s₁ s₂ := by
  have hY0 : 0 < Y := one_pos.trans_le hY
  have hs₁ := mem_U_of_one_lt h1
  have key := eq_on_U (g := fun s => (s₁ + s - 1) * (s₁ - s) * IY Y s₁ s - NS Y s₁ s)
    (fun s hs => (((by fun_prop : DifferentiableAt ℂ (fun s => (s₁ + s - 1) * (s₁ - s)) s).mul
      (differentiableAt_IY Y hs₁ hs)).sub (differentiableAt_NS hY0 hs)))
    (V := {s | s₁.re < s.re}) (isOpen_lt continuous_const continuous_re) (z₀ := ((s₁.re + 1 : ℝ) : ℂ))
    (by simp) (mem_U_of_one_lt (by simp; linarith))
    (fun s (hs : s₁.re < s.re) => by
      have d1 : s₁ + s - 1 ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have d2 : s₁ - s ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      simp only [IY]
      rw [integral_EstarY_mul_region hY h1 hs, MS_cleared d1 d2, sub_self]) hs₂
  exact sub_eq_zero.1 key

/-- **The cleared Maass–Selberg relation** on all of `U × U`:
`(s₁ + s₂ − 1)(s₁ − s₂) · ∫_F E*^Y(s₁)E*^Y(s₂) dμ = NS Y s₁ s₂`. -/
theorem IY_cleared {Y : ℝ} (hY : 1 ≤ Y) {s₁ s₂ : ℂ} (hs₁ : s₁ ∈ U) (hs₂ : s₂ ∈ U) :
    (s₁ + s₂ - 1) * (s₁ - s₂) * IY Y s₁ s₂ = NS Y s₁ s₂ := by
  have hY0 : 0 < Y := one_pos.trans_le hY
  have key := eq_on_U (g := fun s => (s + s₂ - 1) * (s - s₂) * IY Y s₂ s + NS Y s₂ s)
    (fun s hs => (((by fun_prop : DifferentiableAt ℂ (fun s => (s + s₂ - 1) * (s - s₂)) s).mul
      (differentiableAt_IY Y hs₂ hs)).add (differentiableAt_NS hY0 hs)))
    (V := {s | 1 < s.re}) (isOpen_lt continuous_const continuous_re) (z₀ := 2)
    (by simp) (mem_U_of_one_lt (by simp))
    (fun s (hs : 1 < s.re) => by
      rw [IY_comm, IY_cleared_aux hY hs hs₂, NS_swap Y s s₂, add_neg_cancel]) hs₁
  rw [IY_comm Y s₂ s₁, NS_swap] at key
  linear_combination key

/-- **The Maass–Selberg relation** for `E*`: for `Y ≥ 1` and `s₁, s₂ ∉ {0, ½, 1}` with `s₁ + s₂ ≠ 1` and `s₁ ≠ s₂`,
`∫_F E*^Y(z, s₁)E*^Y(z, s₂) dμ(z) = MS Y s₁ s₂`. -/
theorem maass_selberg {Y : ℝ} (hY : 1 ≤ Y) {s₁ s₂ : ℂ} (hs₁ : s₁ ∈ U) (hs₂ : s₂ ∈ U) (h1 : s₁ + s₂ ≠ 1)
    (h2 : s₁ ≠ s₂) : ∫ z in fd, EstarY Y s₁ z * EstarY Y s₂ z = MS Y s₁ s₂ := by
  have d1 : s₁ + s₂ - 1 ≠ 0 := sub_ne_zero.2 h1
  have d2 : s₁ - s₂ ≠ 0 := sub_ne_zero.2 h2
  have h := IY_cleared hY hs₁ hs₂
  rw [← MS_cleared d1 d2] at h
  exact mul_left_cancel₀ (mul_ne_zero d1 d2) h

lemma deriv_completed_one_sub (w : ℂ) :
    deriv completedRiemannZeta (1 - w) = -deriv completedRiemannZeta w := by
  have h : (fun w => completedRiemannZeta (1 - w)) = completedRiemannZeta := funext completedRiemannZeta_one_sub
  have h' := deriv_comp_const_sub (f := completedRiemannZeta) (a := 1) (x := w)
  rw [h] at h'
  rw [h', neg_neg]

theorem maass_selberg_diag {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ} (hs : s ∈ U) :
    ∫ z in fd, EstarY Y s z * EstarY Y (1 - s) z =
      2 * completedRiemannZeta (2 * s) * completedRiemannZeta (2 * s - 1) * (Real.log Y : ℂ) -
        2 * completedRiemannZeta (2 * s) * deriv completedRiemannZeta (2 * s - 1) +
        2 * completedRiemannZeta (2 * s - 1) * deriv completedRiemannZeta (2 * s) +
        (completedRiemannZeta (2 * s) ^ 2 * (Y : ℂ) ^ (2 * s - 1) -
          completedRiemannZeta (2 * s - 1) ^ 2 * (Y : ℂ) ^ (1 - 2 * s)) / (2 * s - 1) := by
  obtain ⟨h0, h12, h1⟩ := mem_U.1 hs
  have hY0 : 0 < Y := one_pos.trans_le hY
  have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast hY0.ne'
  have hs' : 1 - s ∈ U := mem_U.2 ⟨sub_ne_zero.2 (Ne.symm h1),
    by intro h; apply h12; linear_combination -h, by intro h; apply h0; linear_combination -h⟩
  have d : 2 * s - 1 ≠ 0 := by intro h; apply h12; linear_combination h / 2
  have hI := (differentiableAt_IY Y hs hs').hasDerivAt
  have hp := (((hasDerivAt_id (1 - s)).const_add s).sub_const 1).mul ((hasDerivAt_id (1 - s)).const_sub s)
  have hg := hp.mul hI
  have hev : (fun w => NS Y s w) =ᶠ[𝓝 (1 - s)]
      (fun w => (s + id w - 1) * (s - id w) * IY Y s w) :=
    Filter.eventually_of_mem (isOpen_U.mem_nhds hs') fun w hw => (IY_cleared hY hs hw).symm
  have hg' := hg.congr_of_eventuallyEq hev
  have hA : 2 * (1 - s) ≠ 0 := mul_ne_zero two_ne_zero (sub_ne_zero.2 (Ne.symm h1))
  have hA' : 2 * (1 - s) ≠ 1 := by intro h; apply h12; linear_combination -h / 2
  have hB : 2 * (1 - s) - 1 ≠ 0 := by intro h; apply h12; linear_combination -h / 2
  have hB' : 2 * (1 - s) - 1 ≠ 1 := by intro h; apply h0; linear_combination -h / 2
  have L1 := (differentiableAt_completedZeta hA hA').hasDerivAt.comp (1 - s)
    ((hasDerivAt_id (1 - s)).const_mul 2)
  have L2 := (differentiableAt_completedZeta hB hB').hasDerivAt.comp (1 - s)
    (((hasDerivAt_id (1 - s)).const_mul 2).sub_const 1)
  have P1 := (((hasDerivAt_id (1 - s)).const_add s).sub_const 1).const_cpow (c := (Y : ℂ)) (Or.inl hYc)
  have P2 := ((hasDerivAt_id (1 - s)).const_sub (1 - s)).const_cpow (c := (Y : ℂ)) (Or.inl hYc)
  have P3 := ((hasDerivAt_id (1 - s)).const_sub s).const_cpow (c := (Y : ℂ)) (Or.inl hYc)
  have P4 := ((hasDerivAt_id (1 - s)).sub_const s).const_cpow (c := (Y : ℂ)) (Or.inl hYc)
  have hN := (((hasDerivAt_id (1 - s)).const_sub s).mul
      ((((hasDerivAt_const (1 - s) (completedRiemannZeta (2 * s))).mul L1).mul P1).sub
        (((hasDerivAt_const (1 - s) (completedRiemannZeta (2 * s - 1))).mul L2).mul P2))).add
    ((((hasDerivAt_id (1 - s)).const_add s).sub_const 1).mul
      ((((hasDerivAt_const (1 - s) (completedRiemannZeta (2 * s))).mul L2).mul P3).sub
        (((hasDerivAt_const (1 - s) (completedRiemannZeta (2 * s - 1))).mul L1).mul P4)))
  have hN' := hN.congr_of_eventuallyEq (f₁ := fun w => NS Y s w) (Filter.Eventually.of_forall fun w => rfl)
  have heq := hg'.unique hN'
  simp only [id, Function.comp_apply, Pi.mul_apply, Pi.sub_apply] at heq
  have f1 : completedRiemannZeta (2 * (1 - s)) = completedRiemannZeta (2 * s - 1) := by
    rw [← completedRiemannZeta_one_sub]; ring_nf
  have f2 : completedRiemannZeta (2 * (1 - s) - 1) = completedRiemannZeta (2 * s) := by
    rw [← completedRiemannZeta_one_sub]; ring_nf
  have f3 : deriv completedRiemannZeta (2 * (1 - s)) = -deriv completedRiemannZeta (2 * s - 1) := by
    rw [← deriv_completed_one_sub]; ring_nf
  have f4 : deriv completedRiemannZeta (2 * (1 - s) - 1) = -deriv completedRiemannZeta (2 * s) := by
    rw [← deriv_completed_one_sub]; ring_nf
  have f5 : (Y : ℂ) ^ (s + (1 - s) - 1) = 1 := by rw [show s + (1 - s) - 1 = 0 by ring, Complex.cpow_zero]
  have f6 : (Y : ℂ) ^ (1 - s - (1 - s)) = 1 := by rw [show 1 - s - (1 - s) = 0 by ring, Complex.cpow_zero]
  have f7 : (Y : ℂ) ^ (s - (1 - s)) = (Y : ℂ) ^ (2 * s - 1) := by ring_nf
  have f8 : (Y : ℂ) ^ (1 - s - s) = (Y : ℂ) ^ (1 - 2 * s) := by ring_nf
  have f9 : Complex.log (Y : ℂ) = (Real.log Y : ℂ) := (Complex.ofReal_log hY0.le).symm
  rw [f1, f2, f3, f4, f5, f6, f7, f8, f9] at heq
  change IY Y s (1 - s) = _
  apply mul_right_cancel₀ d
  rw [add_mul _ (_ / _), div_mul_cancel₀ _ d]
  linear_combination heq

/-! ## The normalised form, with the scattering matrix `φ(s) = Λ(2s − 1)/Λ(2s)` -/

/-- The truncated Eisenstein series `E^Y(z, s) = E*^Y(z, s)/Λ(2s)`. -/
def EY (Y : ℝ) (s : ℂ) (z : ℍ) : ℂ := EstarY Y s z / completedRiemannZeta (2 * s)

lemma memLp_EY (Y : ℝ) {s : ℂ} (hs : s ∈ U) : MemLp (EY Y s) 2 (volume.restrict fd) :=
  by
    have h : EY Y s = fun z => EstarY Y s z * (completedRiemannZeta (2 * s))⁻¹ := by
      funext z; rw [EY, div_eq_mul_inv]
    rw [h]
    exact MemLp.mul_const (memLp_EstarY Y hs) _

/-- **The Maass–Selberg relation** for `E^Y`: for `Y ≥ 1`, `s₁, s₂ ∉ {0, ½, 1}`, `s₁ + s₂ ≠ 1`, `s₁ ≠ s₂` and
`Λ(2s₁), Λ(2s₂) ≠ 0`,
`∫_F E^Y(s₁)E^Y(s₂) dμ = (Y^{s₁+s₂−1} − φ(s₁)φ(s₂)Y^{1−s₁−s₂})/(s₁ + s₂ − 1)
  + (φ(s₂)Y^{s₁−s₂} − φ(s₁)Y^{s₂−s₁})/(s₁ − s₂)`. -/
theorem maass_selberg_phi {Y : ℝ} (hY : 1 ≤ Y) {s₁ s₂ : ℂ} (hs₁ : s₁ ∈ U) (hs₂ : s₂ ∈ U) (h1 : s₁ + s₂ ≠ 1)
    (h2 : s₁ ≠ s₂) (hΛ₁ : completedRiemannZeta (2 * s₁) ≠ 0) (hΛ₂ : completedRiemannZeta (2 * s₂) ≠ 0) :
    ∫ z in fd, EY Y s₁ z * EY Y s₂ z =
      ((Y : ℂ) ^ (s₁ + s₂ - 1) - PavlovFaddeev.scatteringMatrix s₁ * PavlovFaddeev.scatteringMatrix s₂ *
          (Y : ℂ) ^ (1 - s₁ - s₂)) / (s₁ + s₂ - 1) +
        (PavlovFaddeev.scatteringMatrix s₂ * (Y : ℂ) ^ (s₁ - s₂) -
          PavlovFaddeev.scatteringMatrix s₁ * (Y : ℂ) ^ (s₂ - s₁)) / (s₁ - s₂) := by
  have d1 : s₁ + s₂ - 1 ≠ 0 := sub_ne_zero.2 h1
  have d2 : s₁ - s₂ ≠ 0 := sub_ne_zero.2 h2
  simp_rw [EY, div_mul_div_comm]
  rw [integral_div, maass_selberg hY hs₁ hs₂ h1 h2, MS]
  simp only [PavlovFaddeev.scatteringMatrix]
  field_simp

lemma hasDerivAt_scatteringMatrix {s : ℂ} (hs : s ∈ U) (hΛ : completedRiemannZeta (2 * s) ≠ 0) :
    HasDerivAt PavlovFaddeev.scatteringMatrix
      ((deriv completedRiemannZeta (2 * s - 1) * 2 * completedRiemannZeta (2 * s) -
        completedRiemannZeta (2 * s - 1) * (deriv completedRiemannZeta (2 * s) * 2)) /
        completedRiemannZeta (2 * s) ^ 2) s := by
  obtain ⟨h0, h12, h1⟩ := mem_U.1 hs
  have hA : 2 * s ≠ 0 := mul_ne_zero two_ne_zero h0
  have hA' : 2 * s ≠ 1 := by intro h; apply h12; linear_combination h / 2
  have hB : 2 * s - 1 ≠ 0 := by intro h; apply h12; linear_combination h / 2
  have hB' : 2 * s - 1 ≠ 1 := by intro h; apply h1; linear_combination h / 2
  have L1 := (differentiableAt_completedZeta hA hA').hasDerivAt.comp s ((hasDerivAt_id s).const_mul 2)
  have L2 := (differentiableAt_completedZeta hB hB').hasDerivAt.comp s
    (((hasDerivAt_id s).const_mul 2).sub_const 1)
  have := L2.div L1 hΛ
  simp only [id, Function.comp_def, mul_one] at this
  exact this

/-- **The Maass–Selberg relation on the anti-diagonal** `s₂ = 1 − s`, normalised: for `Y ≥ 1`, `s ∉ {0, ½, 1}` and
`Λ(2s), Λ(2s − 1) ≠ 0`,
`∫_F E^Y(z, s)E^Y(z, 1 − s) dμ = 2 log Y − (φ'/φ)(s) + (φ(1 − s)Y^{2s−1} − φ(s)Y^{1−2s})/(2s − 1)`.
On the critical line `1 − s = s̄`, so this is the `L²` norm of `E^Y(·, ½ + it)` once `E^Y(z, s̄)` is identified
with `conj E^Y(z, s)`. -/
theorem maass_selberg_phi_diag {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ} (hs : s ∈ U)
    (hΛ₁ : completedRiemannZeta (2 * s) ≠ 0) (hΛ₂ : completedRiemannZeta (2 * s - 1) ≠ 0) :
    ∫ z in fd, EY Y s z * EY Y (1 - s) z =
      2 * (Real.log Y : ℂ) - deriv PavlovFaddeev.scatteringMatrix s / PavlovFaddeev.scatteringMatrix s +
        (PavlovFaddeev.scatteringMatrix (1 - s) * (Y : ℂ) ^ (2 * s - 1) -
          PavlovFaddeev.scatteringMatrix s * (Y : ℂ) ^ (1 - 2 * s)) / (2 * s - 1) := by
  obtain ⟨h0, h12, h1⟩ := mem_U.1 hs
  have d : 2 * s - 1 ≠ 0 := by intro h; apply h12; linear_combination h / 2
  have f1 : completedRiemannZeta (2 * (1 - s)) = completedRiemannZeta (2 * s - 1) := by
    rw [← completedRiemannZeta_one_sub]; ring_nf
  have f2 : completedRiemannZeta (2 * (1 - s) - 1) = completedRiemannZeta (2 * s) := by
    rw [← completedRiemannZeta_one_sub]; ring_nf
  simp_rw [EY, div_mul_div_comm]
  rw [integral_div, maass_selberg_diag hY hs, (hasDerivAt_scatteringMatrix hs hΛ₁).deriv]
  simp only [PavlovFaddeev.scatteringMatrix, f1, f2]
  field_simp
  ring

end ModMaassSelberg
