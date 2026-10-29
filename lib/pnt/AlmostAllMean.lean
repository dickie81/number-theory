/-
# Primes in almost all short intervals, part 2: the zero sum in mean square

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

The zero sum `Σ_τ h(τ)` of `AlmostAll.explicit_identity` oscillates in `L = log x`. Over a window `[L₀, L₀ + 2π]`
with the weight `W(L) = 1 − cos(L − L₀)`, which vanishes to second order at both ends, its mean square is controlled
by the zeros' local density instead of their number:
* `kerW_eq`, `norm_kerW_le`: `∫ e^{vL}W(L) dL = (e^{vL₁} − e^{vL₀})/(v(v² + 1))`, hence at most
  `20π e^{L₁|Re v|}/(1 + (Im v)²)` for `|Re v| ≤ 1`, `L₀ ≥ 0`, `L₁ = L₀ + 2π`.
* `pair_le`: `2cos(Lτ)·conj(2cos(Lτ'))` is a sum of four exponentials, so its weighted integral is at most
  `40π e^{L₁(|Im τ| + |Im τ'|)}(1/(1 + (Re τ + Re τ')²) + 1/(1 + (Re τ − Re τ')²))`.
* `inv_le_pk`, `pair_kernel_le`: that kernel is at most `(9π/2)V_{τ'}(Re τ)`, the zero weight of `Kaiser`, whose sum
  over the zeros is at most `(5 + kLam + ½ log(|x| + 2))/π` (`Kaiser.tsum_Vz_le`).
* `head_mean_square`: for a finite set `S` of zeros with `|Re τ| ≤ T`,
  `∫ |Σ_S h(τ)|² W ≤ 180π(5 + kLam + ½ log(T + 2)) Σ_S |ĝ(τ)|⁴ e^{2L₁|Im τ|}`, by `|c_i c_j| ≤ (|c_i|² + |c_j|²)/2`
  and the symmetry of the kernel.
-/
import ZeroLocal
import AlmostAllArch

open Real Filter Topology Complex MeasureTheory Set

noncomputable section

namespace AlmostAll

open ShortWeil WeilForm WeilTest WeilStrip Kaiser

/-! ## The weighted kernel -/

/-- `∫_{L₀}^{L₀+2π} e^{vL}(1 − cos(L − L₀)) dL`. -/
def kerW (L₀ : ℝ) (v : ℂ) : ℂ :=
  ∫ L in L₀..L₀ + 2 * π, Complex.exp (v * L) * (1 - (Real.cos (L - L₀) : ℂ))

theorem kerW_eq (L₀ : ℝ) {v : ℂ} (hv0 : v ≠ 0) (hv1 : v ^ 2 + 1 ≠ 0) :
    kerW L₀ v = (Complex.exp (v * (L₀ + 2 * π : ℝ)) - Complex.exp (v * L₀)) / (v * (v ^ 2 + 1)) := by
  unfold kerW
  set F : ℝ → ℂ := fun L => Complex.exp (v * L) / v
      - Complex.exp (v * L) * (v * (Real.cos (L - L₀) : ℂ) + (Real.sin (L - L₀) : ℂ)) / (v ^ 2 + 1) with hF
  have hd : ∀ L : ℝ, HasDerivAt F (Complex.exp (v * L) * (1 - (Real.cos (L - L₀) : ℂ))) L := by
    intro L
    have he : HasDerivAt (fun L : ℝ => Complex.exp (v * L)) (Complex.exp (v * L) * v) L := by
      have h1 : HasDerivAt (fun L : ℝ => v * (L : ℂ)) v L := by
        simpa using ((hasDerivAt_id L).ofReal_comp).const_mul v
      exact h1.cexp
    have hc : HasDerivAt (fun L : ℝ => (Real.cos (L - L₀) : ℂ)) (-(Real.sin (L - L₀) : ℂ)) L := by
      have h := ((Real.hasDerivAt_cos (L - L₀)).comp L ((hasDerivAt_id L).sub_const L₀)).ofReal_comp
      refine h.congr_deriv ?_
      push_cast; ring
    have hs : HasDerivAt (fun L : ℝ => (Real.sin (L - L₀) : ℂ)) (Real.cos (L - L₀) : ℂ) L := by
      have h := ((Real.hasDerivAt_sin (L - L₀)).comp L ((hasDerivAt_id L).sub_const L₀)).ofReal_comp
      refine h.congr_deriv ?_
      push_cast; ring
    have := (he.div_const v).sub ((he.mul ((hc.const_mul v).add hs)).div_const (v ^ 2 + 1))
    convert this using 1
    simp only [Pi.add_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun L _ => hd L)
    ((by fun_prop : Continuous fun L : ℝ =>
      Complex.exp (v * L) * (1 - (Real.cos (L - L₀) : ℂ))).intervalIntegrable _ _)]
  simp only [hF, add_sub_cancel_left, sub_self, Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero]
  push_cast
  field_simp
  ring

theorem norm_exp_mul_le {v : ℂ} {L L₁ : ℝ} (hL : 0 ≤ L) (hL₁ : L ≤ L₁) :
    ‖Complex.exp (v * L)‖ ≤ Real.exp (L₁ * |v.re|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (v * (L : ℂ)).re = v.re * L := by simp
  rw [this]
  calc v.re * L ≤ |v.re| * L := mul_le_mul_of_nonneg_right (le_abs_self _) hL
    _ ≤ |v.re| * L₁ := mul_le_mul_of_nonneg_left hL₁ (abs_nonneg _)
    _ = L₁ * |v.re| := by ring

/-- **The kernel's decay**: `‖∫ e^{vL}W(L) dL‖ ≤ 20π e^{L₁|Re v|}/(1 + (Im v)²)` for `|Re v| ≤ 1`. -/
theorem norm_kerW_le {L₀ : ℝ} (hL₀ : 0 ≤ L₀) {v : ℂ} (hv : |v.re| ≤ 1) :
    ‖kerW L₀ v‖ ≤ 20 * π * Real.exp ((L₀ + 2 * π) * |v.re|) / (1 + v.im ^ 2) := by
  set L₁ := L₀ + 2 * π with hL₁
  set E := Real.exp (L₁ * |v.re|) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hpi := Real.pi_pos
  have hden : 0 < 1 + v.im ^ 2 := by positivity
  rcases le_or_gt |v.im| 2 with h | h
  · have h1 : ‖kerW L₀ v‖ ≤ 2 * E * |L₁ - L₀| := by
      unfold kerW
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun L hL => ?_
      have hL' : L₀ < L ∧ L ≤ L₁ := by
        rw [Set.uIoc_of_le (by linarith)] at hL; exact hL
      rw [norm_mul]
      have hw : ‖(1 - (Real.cos (L - L₀) : ℂ))‖ ≤ 2 := by
        rw [show (1 - (Real.cos (L - L₀) : ℂ)) = ((1 - Real.cos (L - L₀) : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [Real.cos_le_one (L - L₀), Real.neg_one_le_cos (L - L₀)]
      calc ‖Complex.exp (v * L)‖ * ‖(1 - (Real.cos (L - L₀) : ℂ))‖ ≤ E * 2 :=
            mul_le_mul (norm_exp_mul_le (by linarith) hL'.2) hw (norm_nonneg _) hE0.le
        _ = 2 * E := by ring
    rw [show L₁ - L₀ = 2 * π by rw [hL₁]; ring, abs_of_pos (by positivity)] at h1
    have him : v.im ^ 2 ≤ 4 := by
      have := sq_abs v.im
      nlinarith [abs_nonneg v.im]
    rw [le_div_iff₀ hden]
    calc ‖kerW L₀ v‖ * (1 + v.im ^ 2) ≤ 2 * E * (2 * π) * 5 :=
          mul_le_mul h1 (by linarith) hden.le (by positivity)
      _ = 20 * π * E := by ring
  · have hv0 : v ≠ 0 := fun h0 => by rw [h0] at h; simp at h; linarith
    have hre2 : (v ^ 2 + 1).re = v.re ^ 2 - v.im ^ 2 + 1 := by simp [sq]
    have hvre2 : v.re ^ 2 ≤ 1 := by
      have := sq_abs v.re
      nlinarith [abs_nonneg v.re]
    have him4 : 4 < v.im ^ 2 := by
      have := sq_abs v.im
      nlinarith [abs_nonneg v.im]
    have hv1 : v ^ 2 + 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      rw [hre2] at this
      simp at this
      linarith
    rw [kerW_eq L₀ hv0 hv1, norm_div, norm_mul]
    have hnum : ‖Complex.exp (v * (L₁ : ℝ)) - Complex.exp (v * L₀)‖ ≤ 2 * E := by
      refine (norm_sub_le _ _).trans ?_
      have h1 := norm_exp_mul_le (v := v) (L := L₁) (L₁ := L₁) (by positivity) le_rfl
      have h2 := norm_exp_mul_le (v := v) (L := L₀) (L₁ := L₁) hL₀ (by linarith)
      linarith
    have hnv : |v.im| ≤ ‖v‖ := Complex.abs_im_le_norm v
    have hn2 : v.im ^ 2 / 2 ≤ ‖v ^ 2 + 1‖ := by
      have := Complex.abs_re_le_norm (v ^ 2 + 1)
      rw [hre2] at this
      have h3 : -(v.re ^ 2 - v.im ^ 2 + 1) ≤ |v.re ^ 2 - v.im ^ 2 + 1| := neg_le_abs _
      linarith
    have hprod : v.im ^ 2 ≤ ‖v‖ * ‖v ^ 2 + 1‖ := by
      have h2 : (2 : ℝ) ≤ ‖v‖ := by linarith
      have h3 : 0 ≤ v.im ^ 2 / 2 := by positivity
      calc v.im ^ 2 = 2 * (v.im ^ 2 / 2) := by ring
        _ ≤ ‖v‖ * ‖v ^ 2 + 1‖ := mul_le_mul h2 hn2 h3 (norm_nonneg _)
    have hpos : 0 < ‖v‖ * ‖v ^ 2 + 1‖ := by linarith
    rw [div_le_div_iff₀ hpos hden]
    calc ‖Complex.exp (v * (L₁ : ℝ)) - Complex.exp (v * L₀)‖ * (1 + v.im ^ 2)
        ≤ 2 * E * (5 / 4 * v.im ^ 2) := mul_le_mul hnum (by linarith) hden.le (by positivity)
      _ = 5 / 2 * E * v.im ^ 2 := by ring
      _ ≤ 20 * π * E * (‖v‖ * ‖v ^ 2 + 1‖) := by
          have h20 : 5 / 2 * E ≤ 20 * π * E := by nlinarith [Real.pi_gt_three]
          calc 5 / 2 * E * v.im ^ 2 ≤ 20 * π * E * v.im ^ 2 :=
                mul_le_mul_of_nonneg_right h20 (sq_nonneg _)
            _ ≤ 20 * π * E * (‖v‖ * ‖v ^ 2 + 1‖) := mul_le_mul_of_nonneg_left hprod (by positivity)

/-! ## A pair of zeros -/

theorem two_cos_mul_conj (L : ℝ) (τ τ' : ℂ) :
    2 * Complex.cos (L * τ) * (starRingEnd ℂ) (2 * Complex.cos (L * τ'))
      = Complex.exp (I * (τ + (starRingEnd ℂ) τ') * L) + Complex.exp (I * (τ - (starRingEnd ℂ) τ') * L)
        + Complex.exp (-(I * (τ - (starRingEnd ℂ) τ')) * L)
        + Complex.exp (-(I * (τ + (starRingEnd ℂ) τ')) * L) := by
  have hc : (starRingEnd ℂ) (2 * Complex.cos (L * τ')) = 2 * Complex.cos (L * (starRingEnd ℂ) τ') := by
    rw [map_mul, map_ofNat, ← Complex.cos_conj, map_mul, Complex.conj_ofReal]
  rw [hc]
  set σ := (starRingEnd ℂ) τ'
  have e1 : Complex.exp (I * (τ + σ) * L) = Complex.exp (L * τ * I) * Complex.exp (L * σ * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (I * (τ - σ) * L) = Complex.exp (L * τ * I) * Complex.exp (-(L * σ) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e3 : Complex.exp (-(I * (τ - σ)) * L) = Complex.exp (-(L * τ) * I) * Complex.exp (L * σ * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e4 : Complex.exp (-(I * (τ + σ)) * L) = Complex.exp (-(L * τ) * I) * Complex.exp (-(L * σ) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2, e3, e4, Complex.cos, Complex.cos]
  ring

/-- **A pair of zeros**: the weighted integral of `2cos(Lτ)·conj(2cos(Lτ'))`. -/
theorem pair_le {τ τ' : ℂ} (hτ : |τ.im| < 1 / 2) (hτ' : |τ'.im| < 1 / 2) {L₀ : ℝ} (hL₀ : 0 ≤ L₀) :
    ‖∫ L in L₀..L₀ + 2 * π, 2 * Complex.cos (L * τ) * (starRingEnd ℂ) (2 * Complex.cos (L * τ'))
        * (1 - (Real.cos (L - L₀) : ℂ))‖
      ≤ 40 * π * Real.exp ((L₀ + 2 * π) * (|τ.im| + |τ'.im|))
        * (1 / (1 + (τ.re + τ'.re) ^ 2) + 1 / (1 + (τ.re - τ'.re) ^ 2)) := by
  set σ := (starRingEnd ℂ) τ' with hσ
  set v₁ := I * (τ + σ) with hv₁
  set v₂ := I * (τ - σ) with hv₂
  have hint : ∀ v : ℂ, IntervalIntegrable (fun L : ℝ => Complex.exp (v * L) * (1 - (Real.cos (L - L₀) : ℂ)))
      volume L₀ (L₀ + 2 * π) := fun v =>
    (by fun_prop : Continuous fun L : ℝ => Complex.exp (v * L) * (1 - (Real.cos (L - L₀) : ℂ))).intervalIntegrable _ _
  have e : (fun L : ℝ => 2 * Complex.cos (L * τ) * (starRingEnd ℂ) (2 * Complex.cos (L * τ'))
      * (1 - (Real.cos (L - L₀) : ℂ)))
      = fun L : ℝ => Complex.exp (v₁ * L) * (1 - (Real.cos (L - L₀) : ℂ))
        + Complex.exp (v₂ * L) * (1 - (Real.cos (L - L₀) : ℂ))
        + Complex.exp (-v₂ * L) * (1 - (Real.cos (L - L₀) : ℂ))
        + Complex.exp (-v₁ * L) * (1 - (Real.cos (L - L₀) : ℂ)) := by
    funext L
    rw [two_cos_mul_conj]
    ring
  rw [e, intervalIntegral.integral_add (((hint _).add (hint _)).add (hint _)) (hint _),
    intervalIntegral.integral_add ((hint _).add (hint _)) (hint _),
    intervalIntegral.integral_add (hint _) (hint _)]
  have hre₁ : v₁.re = τ'.im - τ.im := by simp [hv₁, hσ]; ring
  have him₁ : v₁.im = τ.re + τ'.re := by simp [hv₁, hσ]
  have hre₂ : v₂.re = -(τ.im + τ'.im) := by simp [hv₂, hσ]
  have him₂ : v₂.im = τ.re - τ'.re := by simp [hv₂, hσ]
  set s := |τ.im| + |τ'.im| with hs
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hb₁ : |v₁.re| ≤ s := by rw [hre₁]; exact (abs_sub _ _).trans (by rw [hs]; linarith)
  have hb₂ : |v₂.re| ≤ s := by rw [hre₂, abs_neg]; exact abs_add_le _ _
  have hL₁ : 0 ≤ L₀ + 2 * π := by positivity
  have key : ∀ v : ℂ, |v.re| ≤ s → ‖kerW L₀ v‖ ≤ 20 * π * Real.exp ((L₀ + 2 * π) * s) / (1 + v.im ^ 2) := by
    intro v hv
    refine (norm_kerW_le hL₀ (hv.trans hs1)).trans ?_
    gcongr
  have k₁ := key v₁ hb₁
  have k₂ := key v₂ hb₂
  have k₃ := key (-v₂) (by rw [Complex.neg_re, abs_neg]; exact hb₂)
  have k₄ := key (-v₁) (by rw [Complex.neg_re, abs_neg]; exact hb₁)
  rw [Complex.neg_im, neg_sq] at k₃ k₄
  rw [him₁] at k₁ k₄
  rw [him₂] at k₂ k₃
  unfold kerW at k₁ k₂ k₃ k₄
  refine norm_add₄_le.trans ?_
  have : 20 * π * Real.exp ((L₀ + 2 * π) * s) / (1 + (τ.re + τ'.re) ^ 2)
      + 20 * π * Real.exp ((L₀ + 2 * π) * s) / (1 + (τ.re - τ'.re) ^ 2)
      + 20 * π * Real.exp ((L₀ + 2 * π) * s) / (1 + (τ.re - τ'.re) ^ 2)
      + 20 * π * Real.exp ((L₀ + 2 * π) * s) / (1 + (τ.re + τ'.re) ^ 2)
      = 40 * π * Real.exp ((L₀ + 2 * π) * s)
        * (1 / (1 + (τ.re + τ'.re) ^ 2) + 1 / (1 + (τ.re - τ'.re) ^ 2)) := by ring
  linarith

/-! ## The local density of the zeros -/

theorem inv_le_pk {y d : ℝ} (hy1 : 1 / 2 < y) (hy2 : y < 3 / 2) : 1 / (1 + d ^ 2) ≤ 9 * π / 2 * pk y d := by
  unfold pk
  have hpi := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  rw [show 9 * π / 2 * (y / (π * (d ^ 2 + y ^ 2))) * (1 + d ^ 2) = 9 * y * (1 + d ^ 2) / (2 * (d ^ 2 + y ^ 2)) by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg d]

/-- The kernel of `pair_le` against the zero weight `V_{τ'}(Re τ)`. -/
theorem pair_kernel_le {τ' : ℂ} (hτ' : |τ'.im| < 1 / 2) (x : ℝ) :
    1 / (1 + (x + τ'.re) ^ 2) + 1 / (1 + (x - τ'.re) ^ 2) ≤ 9 * π / 2 * Vz τ' x := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hτ'
  unfold Vz
  have a1 := inv_le_pk (y := 1 + τ'.im) (d := x - τ'.re) (by linarith) (by linarith)
  have a2 := inv_le_pk (y := 1 - τ'.im) (d := x + τ'.re) (by linarith) (by linarith)
  linarith

/-! ## The mean square of a finite part of the zero sum -/

/-- **The head in mean square**: for a finite set `S` of zeros of `Ξ` with `|Re τ| ≤ T`,
`∫_{L₀}^{L₀+2π} |Σ_S h(τ)|² W ≤ 180π(5 + kLam + ½ log(T + 2)) Σ_S |ĝ(τ)|⁴ e^{2L₁|Im τ|}`. -/
theorem head_mean_square {b : ℝ} (J : ℕ) {L₀ T : ℝ} (hL₀ : 0 ≤ L₀) (hT : 0 ≤ T)
    (S : Finset (ZeroIdx (sqF Xi))) (hS : ∀ i ∈ S, |(tau i).re| ≤ T) :
    ∫ L in L₀..L₀ + 2 * π, ‖∑ i ∈ S, hmod b J L (tau i)‖ ^ 2 * (1 - Real.cos (L - L₀))
      ≤ 180 * π * (5 + kLam + Real.log (T + 2) / 2)
        * ∑ i ∈ S, ‖ghatC (gI b J) (2 ^ J * b) (tau i)‖ ^ 4 * Real.exp (2 * (L₀ + 2 * π) * |(tau i).im|) := by
  set L₁ := L₀ + 2 * π with hL₁
  have hL₁0 : 0 ≤ L₁ := by positivity
  set c : ZeroIdx (sqF Xi) → ℂ := fun i => ghatC (gI b J) (2 ^ J * b) (tau i) ^ 2 with hc
  set a : ZeroIdx (sqF Xi) → ℝ := fun i => ‖c i‖ * Real.exp (L₁ * |(tau i).im|) with ha
  set K : ZeroIdx (sqF Xi) → ZeroIdx (sqF Xi) → ℝ := fun i j =>
    1 / (1 + ((tau i).re + (tau j).re) ^ 2) + 1 / (1 + ((tau i).re - (tau j).re) ^ 2) with hK
  set C0 := 5 + kLam + Real.log (T + 2) / 2 with hC0
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => by simp only [hK]; positivity
  have hKs : ∀ i j, K i j = K j i := fun i j => by
    simp only [hK]
    rw [show (tau j).re + (tau i).re = (tau i).re + (tau j).re by ring,
      show ((tau j).re - (tau i).re) ^ 2 = ((tau i).re - (tau j).re) ^ 2 by ring]
  -- the hmod terms
  have hh : ∀ (L : ℝ) i, hmod b J L (tau i) = 2 * Complex.cos (L * tau i) * c i := fun L i => by
    simp only [hc]; unfold hmod; ring
  set W : ℝ → ℝ := fun L => 1 - Real.cos (L - L₀) with hW
  -- step 1: the integrand as a complex double sum
  have hpt : ∀ L : ℝ, ((‖∑ i ∈ S, hmod b J L (tau i)‖ ^ 2 * W L : ℝ) : ℂ)
      = ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j)
        * (2 * Complex.cos (L * tau i) * (starRingEnd ℂ) (2 * Complex.cos (L * tau j))
          * (1 - (Real.cos (L - L₀) : ℂ))) := by
    intro L
    set Z := ∑ i ∈ S, hmod b J L (tau i) with hZ
    have e1 : ((‖Z‖ ^ 2 : ℝ) : ℂ) = Z * (starRingEnd ℂ) Z := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.ofReal_mul, e1, hZ, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hh, hh, hW]
    push_cast
    rw [map_mul, map_mul]
    ring
  have hcontC : ∀ i j, Continuous (fun L : ℝ => c i * (starRingEnd ℂ) (c j)
      * (2 * Complex.cos (L * tau i) * (starRingEnd ℂ) (2 * Complex.cos (L * tau j))
        * (1 - (Real.cos (L - L₀) : ℂ)))) := fun i j => by
    have hconj : Continuous fun L : ℝ => (starRingEnd ℂ) (2 * Complex.cos (L * tau j)) :=
      Complex.continuous_conj.comp (by fun_prop)
    exact continuous_const.mul ((by fun_prop : Continuous fun L : ℝ => 2 * Complex.cos (L * tau i)).mul
      hconj |>.mul (by fun_prop))
  have hcont : ∀ i j, IntervalIntegrable (fun L : ℝ => c i * (starRingEnd ℂ) (c j)
      * (2 * Complex.cos (L * tau i) * (starRingEnd ℂ) (2 * Complex.cos (L * tau j))
        * (1 - (Real.cos (L - L₀) : ℂ)))) volume L₀ L₁ := fun i j => (hcontC i j).intervalIntegrable _ _
  have hint : ∫ L in L₀..L₁, ‖∑ i ∈ S, hmod b J L (tau i)‖ ^ 2 * W L
      = (∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j)
          * ∫ L in L₀..L₁, 2 * Complex.cos (L * tau i) * (starRingEnd ℂ) (2 * Complex.cos (L * tau j))
            * (1 - (Real.cos (L - L₀) : ℂ))).re := by
    have h1 := intervalIntegral.integral_ofReal (a := L₀) (b := L₁) (μ := volume)
      (f := fun L => ‖∑ i ∈ S, hmod b J L (tau i)‖ ^ 2 * W L)
    rw [← Complex.ofReal_re (∫ L in L₀..L₁, ‖∑ i ∈ S, hmod b J L (tau i)‖ ^ 2 * W L), ← h1]
    congr 1
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum fun i _ =>
      (continuous_finsetSum S fun j _ => hcontC i j).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => hcont i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
  -- step 2: each pair
  have hpair : ∀ i ∈ S, ∀ j ∈ S, ‖c i * (starRingEnd ℂ) (c j)
      * ∫ L in L₀..L₁, 2 * Complex.cos (L * tau i) * (starRingEnd ℂ) (2 * Complex.cos (L * tau j))
        * (1 - (Real.cos (L - L₀) : ℂ))‖ ≤ 40 * π * (a i * a j * K i j) := by
    intro i _ j _
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hp := pair_le (tau_im i) (tau_im j) hL₀ (L₀ := L₀)
    have hexp : Real.exp (L₁ * (|(tau i).im| + |(tau j).im|))
        = Real.exp (L₁ * |(tau i).im|) * Real.exp (L₁ * |(tau j).im|) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖c i‖ * ‖c j‖ * ‖∫ L in L₀..L₁, 2 * Complex.cos (L * tau i)
          * (starRingEnd ℂ) (2 * Complex.cos (L * tau j)) * (1 - (Real.cos (L - L₀) : ℂ))‖
        ≤ ‖c i‖ * ‖c j‖ * (40 * π * Real.exp (L₁ * (|(tau i).im| + |(tau j).im|)) * K i j) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 40 * π * (a i * a j * K i j) := by rw [hexp]; simp only [ha]; ring
  -- step 3: AM–GM and symmetry
  have hamgm : ∑ i ∈ S, ∑ j ∈ S, a i * a j * K i j ≤ ∑ i ∈ S, ∑ j ∈ S, a i ^ 2 * K i j := by
    have h1 : ∑ i ∈ S, ∑ j ∈ S, a i * a j * K i j
        ≤ ∑ i ∈ S, ∑ j ∈ S, (a i ^ 2 * K i j + a j ^ 2 * K i j) / 2 := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      have := hK0 i j
      nlinarith [sq_nonneg (a i - a j), mul_nonneg (sq_nonneg (a i - a j)) this]
    have h2 : ∑ i ∈ S, ∑ j ∈ S, a j ^ 2 * K i j = ∑ i ∈ S, ∑ j ∈ S, a i ^ 2 * K i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hKs]
    have h3 : ∑ i ∈ S, ∑ j ∈ S, (a i ^ 2 * K i j + a j ^ 2 * K i j) / 2
        = (∑ i ∈ S, ∑ j ∈ S, a i ^ 2 * K i j + ∑ i ∈ S, ∑ j ∈ S, a j ^ 2 * K i j) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div]
    rw [h3, h2] at h1
    linarith
  -- step 4: the local density
  have hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ 9 / 2 * C0 := by
    intro i hi
    have h1 : ∀ j ∈ S, K i j ≤ 9 * π / 2 * Vz (tau j) (tau i).re := fun j _ => by
      simp only [hK]
      have := pair_kernel_le (tau_im j) (tau i).re
      linarith
    have h2 : ∑ j ∈ S, Vz (tau j) (tau i).re ≤ ∑' j, Vz (tau j) (tau i).re :=
      (summable_Vz _).sum_le_tsum S fun j _ => Vz_nonneg (tau_im j) _
    have h3 := tsum_Vz_le (tau i).re
    have h4 : Real.log (|(tau i).re| + 2) ≤ Real.log (T + 2) :=
      Real.log_le_log (by positivity) (by linarith [hS i hi])
    have hpi := Real.pi_pos
    calc ∑ j ∈ S, K i j ≤ ∑ j ∈ S, 9 * π / 2 * Vz (tau j) (tau i).re := Finset.sum_le_sum h1
      _ = 9 * π / 2 * ∑ j ∈ S, Vz (tau j) (tau i).re := by rw [Finset.mul_sum]
      _ ≤ 9 * π / 2 * ((5 + kLam + Real.log (|(tau i).re| + 2) / 2) / π) := by gcongr; linarith
      _ ≤ 9 * π / 2 * ((5 + kLam + Real.log (T + 2) / 2) / π) := by gcongr
      _ = 9 / 2 * C0 := by rw [hC0]; field_simp
  -- assemble
  have hC00 : 0 ≤ C0 := by
    have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    have := kLam_nonneg
    rw [hC0]; positivity
  rw [hint]
  calc (∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j)
          * ∫ L in L₀..L₁, 2 * Complex.cos (L * tau i) * (starRingEnd ℂ) (2 * Complex.cos (L * tau j))
            * (1 - (Real.cos (L - L₀) : ℂ))).re
      ≤ ‖∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j)
          * ∫ L in L₀..L₁, 2 * Complex.cos (L * tau i) * (starRingEnd ℂ) (2 * Complex.cos (L * tau j))
            * (1 - (Real.cos (L - L₀) : ℂ))‖ := Complex.re_le_norm _
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, 40 * π * (a i * a j * K i j) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hpair i hi j hj)
    _ = 40 * π * ∑ i ∈ S, ∑ j ∈ S, a i * a j * K i j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
    _ ≤ 40 * π * ∑ i ∈ S, ∑ j ∈ S, a i ^ 2 * K i j := by gcongr
    _ = 40 * π * ∑ i ∈ S, a i ^ 2 * ∑ j ∈ S, K i j := by
        congr 1; refine Finset.sum_congr rfl fun i _ => ?_; rw [Finset.mul_sum]
    _ ≤ 40 * π * ∑ i ∈ S, a i ^ 2 * (9 / 2 * C0) := by
        gcongr with i hi
        exact hrow i hi
    _ = 180 * π * C0 * ∑ i ∈ S, a i ^ 2 := by rw [← Finset.sum_mul]; ring
    _ = 180 * π * C0 * ∑ i ∈ S, ‖ghatC (gI b J) (2 ^ J * b) (tau i)‖ ^ 4
          * Real.exp (2 * L₁ * |(tau i).im|) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [ha, hc]
        rw [norm_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul]
        congr 2
        push_cast; ring

end AlmostAll

#print axioms AlmostAll.norm_kerW_le
#print axioms AlmostAll.pair_le
#print axioms AlmostAll.head_mean_square
