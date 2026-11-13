import Mathlib
import PivotMinor

/-! # The archimedean minorant's transform: band limit and mass

Plain statement. The minorant `μ = φλ − r` of `PivotMinor` has a cosine transform supported in `|v| < 1` and mass at
least `(7/8)φ̂(0)`:

* **Band limit** (`integral_mu_cos_eq_zero`): `∫μ(s)cos(sv) ds = 0` for `|v| ≥ 1`, and `μ(s)cos(sv)` is integrable for
  every `v` (`integrable_mu_cos`).
* **Mass** (`integral_mu_ge`): `∫μ ≥ (7/8)φ̂(0)`, with `φ̂(0) = (999/1000)·4π/45`.

The proofs.

- **A step against `φ`.** `sinc²y = ¼∫_{−2}^{2}(2 − |w|)⁺cos(wy) dw` (`sinc_sq_eq_mix`), so by Fubini
  `∫φ(s)sinc²(s/A)cos(sv) ds = ⅛∫(2 − |w|)⁺(φ̂(v + w/A) + φ̂(v − w/A)) dw` (`integral_phi_sinc_sq_cos`). For
  `A ≥ 10` and `|v| ≥ 1` both arguments have modulus `≥ 4/5`, where `φ̂` vanishes (`integral_phi_sinc_sq_cos_far`). At
  `v = 0` and `A ≥ 5` the integrand is a polynomial and the step keeps `φ̂(0)(1 − κ(A))`,
  `κ(A) = 15/(2A) − 175/(8A²) + 375/(16A³)` (`integral_phi_sinc_sq_zero`).
- **A bump.** `∫sinc²((s − γ)/2)cos(sv) ds = 2π(1 − |v|)⁺cos(γv)` (`integral_shift_cos`), from the Fejér triangle and
  the oddness of the sine part.
- **The mass.** `∫μ = (23/100)φ̂(0) + (693/1000)φ̂(0)Σ_{k<30}κ(10·2^k) − 4πΣ_j b_j`, with `Σκ ≥ 1.2351`
  (`sum_kap_ge`) and `Σb_j = 0.004561` (`integral_rr`): `∫μ/φ̂(0) ≥ 0.8804 > 7/8`.
-/

open Real MeasureTheory WeilForm WeilTest DirMean BallDensity ShortWeil BallCutoff BallSharp PivotPhi PivotMinor

noncomputable section

namespace PivotMinorFT

/-- **sinc² as a triangle mixture**: `sinc²y = ¼∫_{−2}^{2}(2 − |w|)⁺cos(wy) dw`. -/
lemma sinc_sq_eq_mix (y : ℝ) : Real.sinc y ^ 2 = 1 / 4 * ∫ w in (-2 : ℝ)..2, tri w * Real.cos (w * y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [Real.sinc_zero, mul_zero, Real.cos_zero, mul_one, integral_tri']; norm_num
  have e : ∫ w in (-2 : ℝ)..2, tri w * Real.cos (w * y) = ∫ w in (-2 : ℝ)..2, (2 - |w|) * Real.cos (y * w) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hw
    rw [tri_eq (abs_le.2 hw), mul_comm w y]
  rw [e, integral_tri_cos hy, Real.sinc_of_ne_zero hy]
  field_simp

lemma integrable_phi : Integrable phi := by
  have h := integrable_phi_cos 0
  simpa using h

/-- The product-to-sum step of the mixture. -/
lemma cos_mul_cos' (a b : ℝ) : Real.cos a * Real.cos b = (Real.cos (b + a) + Real.cos (b - a)) / 2 := by
  rw [Real.cos_add, Real.cos_sub]; ring

/-- **`φ·sinc²(·/A)` against a cosine**: `∫φ(s)sinc²(s/A)cos(sv) ds = ⅛∫(2 − |w|)⁺(φ̂(v + w/A) + φ̂(v − w/A)) dw`. -/
lemma integral_phi_sinc_sq_cos (A v : ℝ) :
    ∫ s, phi s * Real.sinc (s / A) ^ 2 * Real.cos (s * v) =
      1 / 8 * ∫ w in (-2 : ℝ)..2, tri w * (phiT (v + w / A) + phiT (v - w / A)) := by
  set f : ℝ → ℝ → ℝ := fun s w => tri w * (phi s * Real.cos (w * (s / A)) * Real.cos (s * v)) with hf
  set ν := volume.restrict (Set.Ioc (-2 : ℝ) 2) with hν
  have hmix : ∀ s, phi s * Real.sinc (s / A) ^ 2 * Real.cos (s * v) = 1 / 4 * ∫ w, f s w ∂ν := by
    intro s
    rw [sinc_sq_eq_mix, intervalIntegral.integral_of_le (by norm_num)]
    have : ∫ w, f s w ∂ν = (phi s * Real.cos (s * v)) * ∫ w, tri w * Real.cos (w * (s / A)) ∂ν := by
      rw [← integral_const_mul]
      congr 1; funext w; simp only [hf]; ring
    rw [this, hν]
    ring
  have hint : Integrable (Function.uncurry f) (volume.prod ν) := by
    have hM := (integrable_phi.norm.const_mul 2).mul_prod (integrable_const (1 : ℝ) (μ := ν))
    refine hM.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have h1 := measurable_tri
      have h2 := continuous_phi.measurable
      refine Measurable.aestronglyMeasurable ?_
      simp only [hf, Function.uncurry_def]
      fun_prop
    · simp only [hf, Function.uncurry_def, Real.norm_eq_abs, mul_one]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (tri_nonneg _)]
      have c1 := Real.abs_cos_le_one (p.2 * (p.1 / A))
      have c2 := Real.abs_cos_le_one (p.1 * v)
      have t2 := tri_le_two p.2
      have := abs_nonneg (phi p.1)
      calc tri p.2 * (|phi p.1| * |Real.cos (p.2 * (p.1 / A))| * |Real.cos (p.1 * v)|)
          ≤ 2 * (|phi p.1| * 1 * 1) := by gcongr
        _ = 2 * ‖phi p.1‖ := by rw [Real.norm_eq_abs]; ring
  simp_rw [hmix]
  rw [integral_const_mul, integral_integral_swap hint]
  have hinner : ∀ w, ∫ s, f s w = tri w * ((phiT (v + w / A) + phiT (v - w / A)) / 2) := by
    intro w
    simp only [hf]
    rw [integral_const_mul]
    congr 1
    have e : ∀ s, phi s * Real.cos (w * (s / A)) * Real.cos (s * v) =
        (phi s * Real.cos (s * (v + w / A)) + phi s * Real.cos (s * (v - w / A))) / 2 := by
      intro s
      rw [mul_assoc, cos_mul_cos', show s * v + w * (s / A) = s * (v + w / A) by ring,
        show s * v - w * (s / A) = s * (v - w / A) by ring]
      ring
    simp_rw [e]
    rw [integral_div, integral_add (integrable_phi_cos _) (integrable_phi_cos _), integral_phi_cos,
      integral_phi_cos]
  simp_rw [hinner]
  rw [hν, ← intervalIntegral.integral_of_le (by norm_num)]
  have e2 : ∀ w, tri w * ((phiT (v + w / A) + phiT (v - w / A)) / 2) =
      1 / 2 * (tri w * (phiT (v + w / A) + phiT (v - w / A))) := fun w => by ring
  simp_rw [e2]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma integrable_phi_sinc_sq_cos (A v : ℝ) :
    Integrable fun s => phi s * Real.sinc (s / A) ^ 2 * Real.cos (s * v) := by
  refine (integrable_phi.norm).mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
  · have := continuous_phi; have := Real.continuous_sinc
    exact (by fun_prop : Continuous fun s => phi s * Real.sinc (s / A) ^ 2 * Real.cos (s * v)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    have c2 := Real.abs_cos_le_one (s * v)
    have hs : |Real.sinc (s / A) ^ 2| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)
    calc |phi s| * |Real.sinc (s / A) ^ 2| * |Real.cos (s * v)| ≤ |phi s| * 1 * 1 := by gcongr
      _ = |phi s| := by ring


/-! ## The bumps -/

lemma sinc_half_sq_eq {s : ℝ} (hs : s ≠ 0) : Real.sinc (s / 2) ^ 2 = hsq (bx (1 / 2)) (1 / 2) s := by
  rw [hsq_bx_eq (by norm_num) hs, Real.sinc_of_ne_zero (by positivity)]
  field_simp
  ring_nf

lemma sinc_half_ae (v : ℝ) :
    (fun s => Real.sinc (s / 2) ^ 2 * Real.cos (s * v)) =ᵐ[volume]
      fun s => hsq (bx (1 / 2)) (1 / 2) s * Real.cos (s * v) := by
  filter_upwards [PivotPhi.ae_ne_zero] with s hs
  rw [sinc_half_sq_eq hs]

/-- **The Fejér kernel's transform**: `∫sinc²(s/2)cos(sv) ds = 2π(1 − |v|)⁺`. -/
lemma integral_sinc_half_sq_cos (v : ℝ) :
    ∫ s, Real.sinc (s / 2) ^ 2 * Real.cos (s * v) = 2 * π * max (1 - |v|) 0 := by
  rw [integral_congr_ae (sinc_half_ae v), integral_hsq_cos (esupp_bx _) (by norm_num), autocorr_bx]
  norm_num

lemma integrable_sinc_half_sq_cos (v : ℝ) : Integrable fun s => Real.sinc (s / 2) ^ 2 * Real.cos (s * v) :=
  (integrable_hsq_cos (esupp_bx (1 / 2)) (by norm_num) v).congr (sinc_half_ae v).symm

lemma integrable_sinc_half_sq : Integrable fun s => Real.sinc (s / 2) ^ 2 := by
  simpa using integrable_sinc_half_sq_cos 0

lemma integrable_sinc_half_sq_sin (v : ℝ) : Integrable fun s => Real.sinc (s / 2) ^ 2 * Real.sin (s * v) := by
  refine integrable_sinc_half_sq.mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
  · have := Real.continuous_sinc
    exact (by fun_prop : Continuous fun s => Real.sinc (s / 2) ^ 2 * Real.sin (s * v)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc Real.sinc (s / 2) ^ 2 * |Real.sin (s * v)| ≤ Real.sinc (s / 2) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (sq_nonneg _)
      _ = _ := mul_one _

/-- The odd part vanishes: `∫sinc²(s/2)sin(sv) ds = 0`. -/
lemma integral_sinc_half_sq_sin (v : ℝ) : ∫ s, Real.sinc (s / 2) ^ 2 * Real.sin (s * v) = 0 := by
  have h := integral_neg_eq_self (fun s => Real.sinc (s / 2) ^ 2 * Real.sin (s * v)) volume
  have e : (fun s => Real.sinc (-s / 2) ^ 2 * Real.sin (-s * v)) =
      fun s => -(Real.sinc (s / 2) ^ 2 * Real.sin (s * v)) := by
    funext s
    rw [neg_div, Real.sinc_neg, neg_mul, Real.sin_neg]; ring
  have h2 : ∫ s, Real.sinc (-s / 2) ^ 2 * Real.sin (-s * v) = ∫ s, Real.sinc (s / 2) ^ 2 * Real.sin (s * v) := h
  rw [e, integral_neg] at h2
  linarith

/-- **A shifted Fejér kernel**: `∫sinc²((s − γ)/2)cos(sv) ds = cos(γv)·2π(1 − |v|)⁺`. -/
lemma integral_shift_cos (γ v : ℝ) :
    ∫ s, Real.sinc ((s - γ) / 2) ^ 2 * Real.cos (s * v) = Real.cos (γ * v) * (2 * π * max (1 - |v|) 0) := by
  have h := integral_add_right_eq_self (μ := volume) (fun s => Real.sinc ((s - γ) / 2) ^ 2 * Real.cos (s * v)) γ
  simp only [add_sub_cancel_right] at h
  rw [← h]
  have e : (fun t => Real.sinc (t / 2) ^ 2 * Real.cos ((t + γ) * v)) = fun t =>
      Real.cos (γ * v) * (Real.sinc (t / 2) ^ 2 * Real.cos (t * v)) -
        Real.sin (γ * v) * (Real.sinc (t / 2) ^ 2 * Real.sin (t * v)) := by
    funext t; rw [add_mul, Real.cos_add]; ring
  rw [e, integral_sub ((integrable_sinc_half_sq_cos v).const_mul _) ((integrable_sinc_half_sq_sin v).const_mul _),
    integral_const_mul, integral_const_mul, integral_sinc_half_sq_cos, integral_sinc_half_sq_sin]
  ring

lemma integrable_shift_cos (γ v : ℝ) : Integrable fun s => Real.sinc ((s - γ) / 2) ^ 2 * Real.cos (s * v) := by
  refine (integrable_sinc_half_sq.comp_sub_right γ).mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
  · have := Real.continuous_sinc
    exact (by fun_prop : Continuous fun s => Real.sinc ((s - γ) / 2) ^ 2 * Real.cos (s * v)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc Real.sinc ((s - γ) / 2) ^ 2 * |Real.cos (s * v)| ≤ Real.sinc ((s - γ) / 2) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg _)
      _ = _ := mul_one _

/-- **A bump's transform**: `∫bump(γ, s)cos(sv) ds = 2cos(γv)·2π(1 − |v|)⁺`. -/
lemma integral_bump_cos (γ v : ℝ) :
    ∫ s, bump γ s * Real.cos (s * v) = 2 * Real.cos (γ * v) * (2 * π * max (1 - |v|) 0) := by
  have e : (fun s => bump γ s * Real.cos (s * v)) = fun s =>
      Real.sinc ((s - γ) / 2) ^ 2 * Real.cos (s * v) + Real.sinc ((s - -γ) / 2) ^ 2 * Real.cos (s * v) := by
    funext s; unfold bump; rw [sub_neg_eq_add]; ring
  rw [e, integral_add (integrable_shift_cos _ _) (integrable_shift_cos _ _), integral_shift_cos, integral_shift_cos,
    neg_mul, Real.cos_neg]
  ring

lemma integrable_bump_cos (γ v : ℝ) : Integrable fun s => bump γ s * Real.cos (s * v) := by
  have e : (fun s => bump γ s * Real.cos (s * v)) = fun s =>
      Real.sinc ((s - γ) / 2) ^ 2 * Real.cos (s * v) + Real.sinc ((s - -γ) / 2) ^ 2 * Real.cos (s * v) := by
    funext s; unfold bump; rw [sub_neg_eq_add]; ring
  rw [e]
  exact (integrable_shift_cos _ _).add (integrable_shift_cos _ _)

/-- The correction against a cosine, for any list of bumps. -/
lemma integral_list_cos (l : List (ℚ × ℚ)) (v : ℝ) :
    Integrable (fun s => (l.map fun p => (p.2 : ℝ) * bump p.1 s).sum * Real.cos (s * v)) ∧
      ∫ s, (l.map fun p => (p.2 : ℝ) * bump p.1 s).sum * Real.cos (s * v) =
        (l.map fun p => (p.2 : ℝ) * (2 * Real.cos (p.1 * v) * (2 * π * max (1 - |v|) 0))).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    have e : (fun s => ((p.2 : ℝ) * bump p.1 s + (l.map fun p => (p.2 : ℝ) * bump p.1 s).sum) * Real.cos (s * v)) =
        fun s => (p.2 : ℝ) * (bump p.1 s * Real.cos (s * v)) +
          (l.map fun p => (p.2 : ℝ) * bump p.1 s).sum * Real.cos (s * v) := by
      funext s; ring
    have hi := (integrable_bump_cos (p.1 : ℝ) v).const_mul (p.2 : ℝ)
    rw [e]
    refine ⟨hi.add ih.1, ?_⟩
    rw [integral_add hi ih.1, integral_const_mul, integral_bump_cos, ih.2]


/-! ## The staircase -/

/-- The step scales `A_k = 10·2^k`. -/
lemma scale_ge (k : ℕ) : (10 : ℝ) ≤ 10 * 2 ^ k := by
  have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  linarith

lemma phi_lam_cos_eq (v s : ℝ) : phi s * PivotMinor.lam s * Real.cos (s * v) =
    23 / 100 * (phi s * Real.cos (s * v)) + 693 / 1000 * ∑ k ∈ Finset.range 30,
      (phi s * Real.cos (s * v) - phi s * Real.sinc (s / (10 * 2 ^ k)) ^ 2 * Real.cos (s * v)) := by
  unfold PivotMinor.lam
  rw [mul_add, add_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_; ring

lemma integrable_phi_lam_cos (v : ℝ) : Integrable fun s => phi s * PivotMinor.lam s * Real.cos (s * v) := by
  simp_rw [phi_lam_cos_eq v]
  refine ((integrable_phi_cos v).const_mul _).add (Integrable.const_mul ?_ _)
  exact integrable_finsetSum _ fun k _ => (integrable_phi_cos v).sub (integrable_phi_sinc_sq_cos _ v)

lemma integral_phi_lam_cos (v : ℝ) : ∫ s, phi s * PivotMinor.lam s * Real.cos (s * v) =
    23 / 100 * phiT v + 693 / 1000 * ∑ k ∈ Finset.range 30,
      (phiT v - ∫ s, phi s * Real.sinc (s / (10 * 2 ^ k)) ^ 2 * Real.cos (s * v)) := by
  simp_rw [phi_lam_cos_eq v]
  have hi : ∀ k ∈ Finset.range 30, Integrable fun s =>
      phi s * Real.cos (s * v) - phi s * Real.sinc (s / (10 * 2 ^ k)) ^ 2 * Real.cos (s * v) :=
    fun k _ => (integrable_phi_cos v).sub (integrable_phi_sinc_sq_cos _ v)
  rw [integral_add ((integrable_phi_cos v).const_mul _) ((integrable_finsetSum _ hi).const_mul _),
    integral_const_mul, integral_const_mul, integral_finsetSum _ hi, integral_phi_cos]
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_sub (integrable_phi_cos v) (integrable_phi_sinc_sq_cos _ v), integral_phi_cos]

/-- Far out the steps contribute nothing: for `|v| ≥ 1`, `∫φ sinc²(s/A_k)cos(sv) = 0`. -/
lemma integral_phi_sinc_sq_cos_far {A v : ℝ} (hA : 10 ≤ A) (hv : 1 ≤ |v|) :
    ∫ s, phi s * Real.sinc (s / A) ^ 2 * Real.cos (s * v) = 0 := by
  rw [integral_phi_sinc_sq_cos]
  have hA0 : 0 < A := by linarith
  have h0 : ∀ w ∈ Set.uIcc (-2 : ℝ) 2, tri w * (phiT (v + w / A) + phiT (v - w / A)) = 0 := by
    intro w hw
    rw [Set.uIcc_of_le (by norm_num)] at hw
    have hwA : |w / A| ≤ 1 / 5 := by
      rw [abs_div, abs_of_pos hA0, div_le_iff₀ hA0]
      have := abs_le.2 hw; linarith
    have h1 : 4 / 5 ≤ |v + w / A| := by
      have := abs_sub_abs_le_abs_sub v (-(w / A)); rw [sub_neg_eq_add, abs_neg] at this; linarith
    have h2 : 4 / 5 ≤ |v - w / A| := by
      have := abs_sub_abs_le_abs_sub v (w / A); linarith
    rw [phiT_eq_zero h1, phiT_eq_zero h2]; ring
  rw [intervalIntegral.integral_congr h0]; simp

/-! ## The minorant -/

lemma integrable_rr_cos (v : ℝ) : Integrable fun s => rr s * Real.cos (s * v) := (integral_list_cos bumpData v).1

lemma integral_rr_cos (v : ℝ) : ∫ s, rr s * Real.cos (s * v) =
    (bumpData.map fun p => (p.2 : ℝ) * (2 * Real.cos (p.1 * v) * (2 * π * max (1 - |v|) 0))).sum :=
  (integral_list_cos bumpData v).2

lemma integrable_mu_cos (v : ℝ) : Integrable fun s => mu s * Real.cos (s * v) := by
  have e : (fun s => mu s * Real.cos (s * v)) = fun s => phi s * PivotMinor.lam s * Real.cos (s * v) - rr s * Real.cos (s * v) := by
    funext s; unfold mu; ring
  rw [e]
  exact (integrable_phi_lam_cos v).sub (integrable_rr_cos v)

lemma integral_mu_cos (v : ℝ) : ∫ s, mu s * Real.cos (s * v) =
    (∫ s, phi s * PivotMinor.lam s * Real.cos (s * v)) - ∫ s, rr s * Real.cos (s * v) := by
  have e : (fun s => mu s * Real.cos (s * v)) = fun s => phi s * PivotMinor.lam s * Real.cos (s * v) - rr s * Real.cos (s * v) := by
    funext s; unfold mu; ring
  rw [e, integral_sub (integrable_phi_lam_cos v) (integrable_rr_cos v)]

/-- **Band limit**: `μ`'s transform vanishes for `|v| ≥ 1`. -/
theorem integral_mu_cos_eq_zero {v : ℝ} (hv : 1 ≤ |v|) : ∫ s, mu s * Real.cos (s * v) = 0 := by
  rw [integral_mu_cos, integral_phi_lam_cos, phiT_eq_zero (by linarith), integral_rr_cos]
  have hk : ∀ k ∈ Finset.range 30, (0 : ℝ) - ∫ s, phi s * Real.sinc (s / (10 * 2 ^ k)) ^ 2 * Real.cos (s * v) = 0 :=
    fun k _ => by rw [integral_phi_sinc_sq_cos_far (scale_ge k) hv]; ring
  rw [Finset.sum_congr rfl hk, max_eq_right (by linarith)]
  simp


/-! ## The mass -/

/-- `κ(A) = 15/(2A) − 175/(8A²) + 375/(16A³)`: the share of `φ̂(0)` that a step at scale `A` removes. -/
def kap (A : ℝ) : ℝ := 15 / (2 * A) - 175 / (8 * A ^ 2) + 375 / (16 * A ^ 3)

/-- `∫₀²(2 − w)F(wx)dw = 8/45 − 4x/3 + 35x²/9 − 25x³/6` for `F(y) = (25/9)(2/5 − y)³ − (25/144)(4/5 − y)³`. -/
lemma integral_tri_poly (x : ℝ) :
    ∫ w in (0 : ℝ)..2, (2 - w) * (25 / 9 * (2 / 5 - w * x) ^ 3 - 25 / 144 * (4 / 5 - w * x) ^ 3) =
      8 / 45 - 4 / 3 * x + 35 / 9 * x ^ 2 - 25 / 6 * x ^ 3 := by
  have hP : ∀ w : ℝ, HasDerivAt (fun w => 25 * x ^ 3 / 48 * w ^ 5 + (-(125 * x ^ 3 / 96) - 35 * x ^ 2 / 48) * w ^ 4 +
      (35 * x ^ 2 / 18 + x / 3) * w ^ 3 + (-x - 2 / 45) * w ^ 2 + 8 / 45 * w)
      ((2 - w) * (25 / 9 * (2 / 5 - w * x) ^ 3 - 25 / 144 * (4 / 5 - w * x) ^ 3)) w := by
    intro w
    have h5 := (hasDerivAt_pow 5 w).const_mul (25 * x ^ 3 / 48)
    have h4 := (hasDerivAt_pow 4 w).const_mul (-(125 * x ^ 3 / 96) - 35 * x ^ 2 / 48)
    have h3 := (hasDerivAt_pow 3 w).const_mul (35 * x ^ 2 / 18 + x / 3)
    have h2 := (hasDerivAt_pow 2 w).const_mul (-x - 2 / 45)
    have h1 := (hasDerivAt_id w).const_mul (8 / 45 : ℝ)
    refine ((((h5.add h4).add h3).add h2).add h1).congr_deriv ?_
    push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hP w)
    ((by fun_prop : Continuous fun w : ℝ =>
      (2 - w) * (25 / 9 * (2 / 5 - w * x) ^ 3 - 25 / 144 * (4 / 5 - w * x) ^ 3)).intervalIntegrable _ _)]
  ring

/-- The symmetric version on `[−2, 2]` with the triangle `tri`. -/
lemma integral_tri_sym (x : ℝ) :
    ∫ w in (-2 : ℝ)..2, tri w * (25 / 9 * (2 / 5 - |w| * x) ^ 3 - 25 / 144 * (4 / 5 - |w| * x) ^ 3) =
      2 * (8 / 45 - 4 / 3 * x + 35 / 9 * x ^ 2 - 25 / 6 * x ^ 3) := by
  have hcont : Continuous fun w : ℝ =>
      tri w * (25 / 9 * (2 / 5 - |w| * x) ^ 3 - 25 / 144 * (4 / 5 - |w| * x) ^ 3) := by
    have := continuous_tri; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  have hneg : ∫ w in (-2 : ℝ)..0, tri w * (25 / 9 * (2 / 5 - |w| * x) ^ 3 - 25 / 144 * (4 / 5 - |w| * x) ^ 3) =
      ∫ w in (0 : ℝ)..2, (2 - w) * (25 / 9 * (2 / 5 - w * x) ^ 3 - 25 / 144 * (4 / 5 - w * x) ^ 3) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 2)
      (fun w : ℝ => tri w * (25 / 9 * (2 / 5 - |w| * x) ^ 3 - 25 / 144 * (4 / 5 - |w| * x) ^ 3))
    simp only [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hw
    rw [tri_eq (by rw [abs_neg, abs_of_nonneg hw.1]; exact hw.2), abs_neg, abs_of_nonneg hw.1]
  have hpos : ∫ w in (0 : ℝ)..2, tri w * (25 / 9 * (2 / 5 - |w| * x) ^ 3 - 25 / 144 * (4 / 5 - |w| * x) ^ 3) =
      ∫ w in (0 : ℝ)..2, (2 - w) * (25 / 9 * (2 / 5 - w * x) ^ 3 - 25 / 144 * (4 / 5 - w * x) ^ 3) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hw
    rw [tri_eq (by rw [abs_of_nonneg hw.1]; exact hw.2), abs_of_nonneg hw.1]
  rw [hneg, hpos, integral_tri_poly]
  ring

/-- **A step's mass**: for `A ≥ 5`, `∫φ(s)sinc²(s/A)ds = φ̂(0)(1 − κ(A))`. -/
lemma integral_phi_sinc_sq_zero {A : ℝ} (hA : 5 ≤ A) :
    ∫ s, phi s * Real.sinc (s / A) ^ 2 * Real.cos (s * 0) = PivotPhi.phiT 0 * (1 - kap A) := by
  have hA0 : 0 < A := by linarith
  rw [integral_phi_sinc_sq_cos]
  have h0 : ∀ w ∈ Set.uIcc (-2 : ℝ) 2, tri w * (PivotPhi.phiT (0 + w / A) + PivotPhi.phiT (0 - w / A)) =
      2 * (999 / 1000 * π) *
        (tri w * (25 / 9 * (2 / 5 - |w| * A⁻¹) ^ 3 - 25 / 144 * (4 / 5 - |w| * A⁻¹) ^ 3)) := by
    intro w hw
    rw [Set.uIcc_of_le (by norm_num)] at hw
    have hwA : |w| / A ≤ 2 / 5 := by
      rw [div_le_iff₀ hA0]; have := abs_le.2 hw; linarith
    rw [zero_add, zero_sub, PivotPhi.phihat_neg]
    unfold PivotPhi.phiT
    rw [abs_div, abs_of_pos hA0, max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  rw [intervalIntegral.integral_congr h0, intervalIntegral.integral_const_mul, integral_tri_sym, PivotPhi.phihat_zero]
  unfold kap
  field_simp
  ring

/-- The steps' total share: `Σ_{k<30} κ(10·2^k) ≥ 1.2351`. -/
lemma sum_kap_ge : (12351 : ℝ) / 10000 ≤ ∑ k ∈ Finset.range 30, kap (10 * 2 ^ k) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, kap]
  norm_num

/-- The bumps' total mass: `∫r = 4π·Σb = 4π·0.004561`. -/
lemma integral_rr : ∫ s, rr s * Real.cos (s * 0) = 4561 / 1000000 * (4 * π) := by
  rw [integral_rr_cos]
  simp only [mul_zero, Real.cos_zero, abs_zero, sub_zero, max_eq_left (zero_le_one : (0 : ℝ) ≤ 1),
    bumpData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- **The mass of the minorant**: `∫μ ≥ (7/8)φ̂(0)`. -/
theorem integral_mu_ge : 7 / 8 * PivotPhi.phiT 0 ≤ ∫ s, mu s := by
  have e : (∫ s, mu s) = ∫ s, mu s * Real.cos (s * 0) := by
    simp only [mul_zero, Real.cos_zero, mul_one]
  have hk : ∀ k ∈ Finset.range 30,
      PivotPhi.phiT 0 - ∫ s, phi s * Real.sinc (s / (10 * 2 ^ k)) ^ 2 * Real.cos (s * 0) = PivotPhi.phiT 0 * kap (10 * 2 ^ k) := by
    intro k _
    rw [integral_phi_sinc_sq_zero (by linarith [scale_ge k])]; ring
  rw [e, integral_mu_cos, integral_phi_lam_cos, integral_rr, Finset.sum_congr rfl hk, ← Finset.mul_sum]
  have hP := PivotPhi.phihat_zero
  have hmul : PivotPhi.phiT 0 * (12351 / 10000) ≤ PivotPhi.phiT 0 * ∑ k ∈ Finset.range 30, kap (10 * 2 ^ k) :=
    mul_le_mul_of_nonneg_left sum_kap_ge (by rw [hP]; positivity)
  linarith [Real.pi_pos]

end PivotMinorFT
