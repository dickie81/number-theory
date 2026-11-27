/-
# The fundamental domain of `SL(2, ℤ)`: its area, and unfolding over `Γ_∞\SL(2, ℤ)`

Milestone A of the scattering theory of `SL(2, ℤ)\ℍ²`, on the side of the measure. For Mathlib's fundamental domain
`𝒟 = ModularGroup.fd` and its invariant measure `dx dy/y²` on `ℍ`:
* **The area** (`volume_fd`): `vol(𝒟) = π/3`, by Tonelli in the coordinates `(x, y)`:
  `∫_{−1/2}^{1/2} dx/√(1 − x²) = π/3`.
* **The tiling** (`volume_fd_diff_fdo`, `ae_tsum_indicator_fd`): the boundary `𝒟 \ 𝒟ᵒ` is null, so almost every
  point of `ℍ` has exactly two translates in `𝒟`, by `±g` (Mathlib's `exists_smul_mem_fd` and
  `eq_one_or_neg_one_of_mem_fdo_mem_fd`).
* **Unfolding over `SL(2, ℤ)`** (`lintegral_fd_tsum_SL`): `∫_𝒟 Σ_{γ ∈ SL(2, ℤ)} h(γz) dμ = 2∫_ℍ h dμ` for
  measurable `h ≥ 0`, by the invariance of `μ` under `GL(2, ℝ)`.
* **Unfolding over `Γ_∞\SL(2, ℤ)`** (`rowEquiv`, `lintegral_fd_tsum_coprime`): `(v, n) ↦ Tⁿγ_v` is a bijection from
  the coprime pairs times `ℤ` onto `SL(2, ℤ)`, so for `T`-periodic measurable `f ≥ 0`,
  `∫_𝒟 Σ_{(c, d) coprime} f(γ_{(c, d)}z) dμ = 2∫_{0 ≤ x < 1} f dμ`.
* **Rankin–Selberg** (`lintegral_fd_tsum_coprime_im`, `lintegral_fd_tsum_nq`): for measurable `φ ≥ 0`,
  `∫_𝒟 Σ_{(c, d) coprime} φ(y/|cz + d|²) dμ = 2∫_0^∞ φ(y)y^{−2} dy`, the unfolding of `E` against `𝒟`.
The factor `2` is `±1`: both `γ` and `−γ` act as the same map of `ℍ`, and both `(c, d)` and `(−c, −d)` are summed.
-/
import Mathlib
import ModEisenstein

open MeasureTheory Set Real UpperHalfPlane Filter ModularGroup
open scoped MatrixGroups ENNReal NNReal

noncomputable section

namespace ModFD

/-! ## The volume of `𝒟` -/

/-- `∫_a^∞ y^{−2} dy = 1/a`. -/
lemma lintegral_Ici_rpow {a : ℝ} (ha : 0 < a) :
    ∫⁻ y in Ici a, ENNReal.ofReal (y ^ (-2 : ℝ)) = ENNReal.ofReal (1 / a) := by
  rw [← setLIntegral_congr Ioi_ae_eq_Ici, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ha)]
  · rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
    congr 1
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : a < y)
    exact Real.rpow_nonneg (by linarith) _

/-- `arcsin(½) = π/6`. -/
lemma arcsin_half : Real.arcsin (1 / 2) = π / 6 := by
  rw [← Real.sin_pi_div_six, Real.arcsin_sin] <;> linarith [pi_pos]

lemma continuousOn_inv_sqrt : ContinuousOn (fun x : ℝ => 1 / √(1 - x ^ 2)) (Icc (-(1 / 2)) (1 / 2)) := by
  refine continuousOn_const.div (by fun_prop) fun x hx => ?_
  have : x ^ 2 ≤ 1 / 4 := by nlinarith [hx.1, hx.2]
  exact (Real.sqrt_pos.2 (by linarith)).ne'

/-- `∫_{−1/2}^{1/2} dx/√(1 − x²) = π/3`. -/
lemma integral_inv_sqrt : ∫ x in (-(1 / 2) : ℝ)..(1 / 2), 1 / √(1 - x ^ 2) = π / 3 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.arcsin)]
  · rw [Real.arcsin_neg, arcsin_half]; ring
  · intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    exact Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])
  · exact (continuousOn_inv_sqrt.mono (by rw [uIcc_of_le (by norm_num)])).intervalIntegrable

/-- The region `𝒟` in coordinates: `y > 0`, `x² + y² ≥ 1`, `|x| ≤ 1/2`. -/
def R : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2 ∧ |p.1| ≤ 1 / 2}

lemma measurableSet_R : MeasurableSet R := by
  refine (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_le measurable_const ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))).inter
      (measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const))

/-- The integrand `y^{−2}` on `R`. -/
def Fp : ℝ × ℝ → ℝ≥0∞ := R.indicator fun p => ENNReal.ofReal (p.2 ^ (-2 : ℝ))

lemma measurable_Fp : Measurable Fp :=
  (Measurable.ennreal_ofReal (measurable_snd.pow_const _)).indicator measurableSet_R

lemma inner_Fp (x : ℝ) :
    ∫⁻ y, Fp (x, y) = (Icc (-(1 / 2)) (1 / 2)).indicator (fun x => ENNReal.ofReal (1 / √(1 - x ^ 2))) x := by
  by_cases hx : |x| ≤ 1 / 2
  · have hx' : x ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := abs_le.1 hx
    rw [indicator_of_mem hx']
    have h1 : x ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.1 hx, sq_abs x]
    have ha : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 (by linarith)
    have hfun : (fun y => Fp (x, y)) = (Ici (√(1 - x ^ 2))).indicator fun y => ENNReal.ofReal (y ^ (-2 : ℝ)) := by
      funext y
      simp only [Fp, R, indicator, Set.mem_ofPred_eq, mem_Ici]
      congr 1
      apply propext
      constructor
      · rintro ⟨hy, h, -⟩
        rw [Real.sqrt_le_left]
        · linarith
        · exact hy.le
      · intro h
        have hy : 0 < y := lt_of_lt_of_le ha h
        refine ⟨hy, ?_⟩
        have h2 : (√(1 - x ^ 2)) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ ha.le h 2
        rw [Real.sq_sqrt (by linarith)] at h2
        exact ⟨by linarith, hx⟩
    rw [hfun, lintegral_indicator measurableSet_Ici, lintegral_Ici_rpow ha]
  · have hx' : x ∉ Icc (-(1 / 2) : ℝ) (1 / 2) := fun h => hx (abs_le.2 h)
    rw [indicator_of_notMem hx']
    have : (fun y => Fp (x, y)) = fun _ => 0 := by
      funext y
      exact Set.indicator_of_notMem (fun h => hx h.2.2) _
    rw [this, lintegral_zero]

lemma lintegral_Fp : ∫⁻ p, Fp p = ENNReal.ofReal (π / 3) := by
  rw [Measure.volume_eq_prod ℝ ℝ, lintegral_prod _ measurable_Fp.aemeasurable]
  simp_rw [inner_Fp]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal
    (continuousOn_inv_sqrt.integrableOn_compact isCompact_Icc)]
  · rw [← integral_inv_sqrt, intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
  · filter_upwards with x
    positivity

/-- `𝒟` in `ℂ`. -/
def A : Set ℂ := {z | 0 < z.im ∧ 1 ≤ ‖z‖ ∧ |z.re| ≤ 1 / 2}

lemma measurableSet_A : MeasurableSet A :=
  (measurableSet_lt measurable_const Complex.measurable_im).inter
    ((measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_le (continuous_abs.measurable.comp Complex.measurable_re) measurable_const))

lemma measurable_dens : Measurable fun z : ℂ => (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) :=
  Measurable.coe_nnreal_ennreal ((measurable_const.div Complex.measurable_im.nnnorm).pow_const 2)

lemma dens_eq {y : ℝ} (hy : 0 < y) : (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (y ^ (-2 : ℝ)) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [Real.rpow_neg hy.le, Real.norm_eq_abs, abs_of_pos hy]
  norm_num

lemma one_le_norm_iff (x y : ℝ) : 1 ≤ ‖(⟨x, y⟩ : ℂ)‖ ↔ 1 ≤ x ^ 2 + y ^ 2 := by
  rw [show ‖(⟨x, y⟩ : ℂ)‖ = |‖(⟨x, y⟩ : ℂ)‖| from (abs_norm _).symm, ← one_le_sq_iff_one_le_abs,
    Complex.sq_norm, Complex.normSq_apply]
  simp [sq]

/-- **The hyperbolic area of the fundamental domain**: `vol(𝒟) = π/3`, for Mathlib's `ModularGroup.fd` and its
invariant measure `dx dy/y²` on `ℍ`. -/
theorem volume_fd : volume (ModularGroup.fd : Set ℍ) = ENNReal.ofReal (π / 3) := by
  rw [UpperHalfPlane.volume_eq_lintegral, ModularGroup.coe_fd, ← lintegral_Fp]
  change ∫⁻ z in A, _ = _
  rw [← lintegral_indicator measurableSet_A,
    ← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp (measurable_dens.indicator measurableSet_A)]
  congr 1
  funext p
  obtain ⟨x, y⟩ := p
  rw [Complex.measurableEquivRealProd_symm_apply]
  by_cases h : 0 < y ∧ 1 ≤ x ^ 2 + y ^ 2 ∧ |x| ≤ 1 / 2
  · have hA : (⟨x, y⟩ : ℂ) ∈ A := ⟨h.1, (one_le_norm_iff x y).2 h.2.1, h.2.2⟩
    rw [indicator_of_mem hA, Fp, indicator_of_mem (show (x, y) ∈ R from h)]
    exact dens_eq h.1
  · have hA : (⟨x, y⟩ : ℂ) ∉ A := fun hA => h ⟨hA.1, (one_le_norm_iff x y).1 hA.2.1, hA.2.2⟩
    rw [indicator_of_notMem hA, Fp, indicator_of_notMem (show (x, y) ∉ R from h)]

/-! ## `𝒟` tiles `ℍ` up to a null set -/

instance : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  exact inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})

lemma measurableSet_fd : MeasurableSet (ModularGroup.fd : Set ℍ) :=
  measurable_coe ((measurableSet_le measurable_const Complex.continuous_normSq.measurable).inter
    (measurableSet_le (continuous_abs.measurable.comp Complex.measurable_re) measurable_const))

lemma measurable_smul_SL (g : SL(2, ℤ)) : Measurable fun z : ℍ => g • z :=
  (measurePreserving_smul (g : GL (Fin 2) ℝ) volume).measurable

/-- A line `re = c` in `ℂ` is Lebesgue-null. -/
lemma volume_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod
  have : {z : ℂ | z.re = c} = Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ univ) := by
    ext z; simp [Complex.measurableEquivRealProd]
  rw [this, h.measure_preimage (((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet),
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- The boundary `𝒟 \ 𝒟ᵒ` is null for the invariant measure. -/
lemma volume_fd_diff_fdo : volume ((ModularGroup.fd : Set ℍ) \ ModularGroup.fdo) = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  have hsub : (↑) '' ((ModularGroup.fd : Set ℍ) \ ModularGroup.fdo) ⊆
      Metric.sphere (0 : ℂ) 1 ∪ ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)}) := by
    rintro _ ⟨z, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    have h3' : ¬(1 < Complex.normSq (z : ℂ) ∧ |z.re| < 1 / 2) := h3
    rw [not_and_or, not_lt, not_lt] at h3'
    rcases h3' with h3 | h3
    · left
      have : Complex.normSq (z : ℂ) = 1 := le_antisymm h3 h1
      rw [Complex.normSq_eq_norm_sq] at this
      rw [mem_sphere_zero_iff_norm]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
    · right
      have : |z.re| = 1 / 2 := le_antisymm h2 h3
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.1 this with h | h
      · exact Or.inl h
      · exact Or.inr h
  have h0 : volume ((↑) '' ((ModularGroup.fd : Set ℍ) \ ModularGroup.fdo) : Set ℂ) = 0 :=
    measure_mono_null hsub (measure_union_null (Measure.addHaar_sphere _ _ _)
      (measure_union_null (volume_re_eq _) (volume_re_eq _)))
  rw [Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]

lemma SL_ne_neg (g : SL(2, ℤ)) : g ≠ -g := by
  intro h
  have h' : ∀ i j, (g : Matrix (Fin 2) (Fin 2) ℤ) i j = 0 := fun i j => by
    have := congrArg (fun k : SL(2, ℤ) => (k : Matrix (Fin 2) (Fin 2) ℤ) i j) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at this
    omega
  have := g.2
  rw [Matrix.det_fin_two, h' 0 0, h' 1 1, h' 0 1] at this
  simp at this

/-- Off a null set, each point has exactly two `SL(2,ℤ)`-translates (`±g`) in `𝒟`. -/
lemma ae_tsum_indicator_fd :
    ∀ᵐ w : ℍ, ∑' g : SL(2, ℤ), (ModularGroup.fd : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (g • w) = 2 := by
  have hN : volume (⋃ g : SL(2, ℤ), (fun w : ℍ => g • w) ⁻¹' ((ModularGroup.fd : Set ℍ) \ ModularGroup.fdo)) = 0 :=
    measure_iUnion_null fun g => by
      rw [show (fun w : ℍ => g • w) = fun w => (g : GL (Fin 2) ℝ) • w from rfl,
        measure_preimage_smul, volume_fd_diff_fdo]
  rw [ae_iff]
  refine measure_mono_null (fun w hw => ?_) hN
  simp only [mem_iUnion, mem_preimage]
  by_contra hcon
  push Not at hcon
  apply hw
  obtain ⟨g₀, hg₀⟩ := exists_smul_mem_fd w
  have ho : g₀ • w ∈ ModularGroup.fdo := by
    by_contra h; exact hcon g₀ ⟨hg₀, h⟩
  have hsupp : ∀ g : SL(2, ℤ), g • w ∈ ModularGroup.fd → g = g₀ ∨ g = -g₀ := fun g hg => by
    have : (g * g₀⁻¹) • (g₀ • w) ∈ ModularGroup.fd := by rwa [← mul_smul, inv_mul_cancel_right]
    rcases eq_one_or_neg_one_of_mem_fdo_mem_fd ho this with h | h
    · exact Or.inl (mul_inv_eq_one.1 h)
    · right; rw [mul_inv_eq_iff_eq_mul] at h; rw [h]; simp
  rw [tsum_eq_sum (s := {g₀, -g₀}) (fun g hg => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hg
    exact indicator_of_notMem (fun h => (hsupp g h).elim hg.1 hg.2) _),
    Finset.sum_pair (SL_ne_neg g₀), SL_neg_smul, indicator_of_mem hg₀]
  norm_num

/-- **Unfolding over `SL(2,ℤ)`**: `∫_𝒟 Σ_{γ ∈ SL(2,ℤ)} h(γz) dμ = 2 ∫_ℍ h dμ`. -/
theorem lintegral_fd_tsum_SL (h : ℍ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z in ModularGroup.fd, ∑' g : SL(2, ℤ), h (g • z) = 2 * ∫⁻ z, h z := by
  rw [lintegral_tsum (f := fun g z => h (g • z)) fun g => (hh.comp (measurable_smul_SL g)).aemeasurable]
  have key : ∀ g : SL(2, ℤ), ∫⁻ z in ModularGroup.fd, h (g • z) =
      ∫⁻ w, (ModularGroup.fd : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (g⁻¹ • w) * h w := fun g => by
    have hF : Measurable fun w : ℍ =>
        (ModularGroup.fd : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (g⁻¹ • w) * h w :=
      ((measurable_const.indicator measurableSet_fd).comp (measurable_smul_SL g⁻¹)).mul hh
    rw [← lintegral_indicator measurableSet_fd]
    refine Eq.trans ?_ ((measurePreserving_smul (g : GL (Fin 2) ℝ) volume).lintegral_comp hF)
    congr 1; funext z
    change _ = (ModularGroup.fd : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (g⁻¹ • g • z) * h (g • z)
    rw [inv_smul_smul]
    by_cases hz : z ∈ (ModularGroup.fd : Set ℍ)
    · simp [indicator_of_mem hz]
    · simp [indicator_of_notMem hz]
  simp_rw [key]
  rw [← lintegral_tsum (f := fun g w => (ModularGroup.fd : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (g⁻¹ • w) * h w)
      fun g => (((measurable_const.indicator measurableSet_fd).comp
      (measurable_smul_SL g⁻¹)).mul hh).aemeasurable, ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_tsum_indicator_fd] with w hw
  have e := (Equiv.inv SL(2, ℤ)).tsum_eq
    (fun g => (ModularGroup.fd : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (g • w))
  simp only [Equiv.inv_apply] at e
  rw [ENNReal.tsum_mul_right, e, hw]

/-! ## Unfolding over `Γ∞\Γ` -/

/-- Coprime integer rows `(c, d)`, i.e. the cosets `Γ∞\SL(2,ℤ)` up to the sign `±1 ∈ Γ∞`. -/
abbrev CoprimeRow := {v : Fin 2 → ℤ // IsCoprime (v 0) (v 1)}

/-- A chosen `γ_v ∈ SL(2,ℤ)` with bottom row `v`. -/
def gam (v : CoprimeRow) : SL(2, ℤ) := (bottom_row_surj (R := ℤ) v.2).choose

lemma gam_row (v : CoprimeRow) : (gam v : Matrix (Fin 2) (Fin 2) ℤ) 1 = v.1 :=
  (bottom_row_surj (R := ℤ) v.2).choose_spec.2

lemma row_T_zpow_mul (n : ℤ) (g : SL(2, ℤ)) :
    ((T ^ n * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 := by
  funext j
  simp

/-- Two elements of `SL(2,ℤ)` with the same bottom row differ by a power of `T` on the left. -/
lemma eq_T_zpow_mul {g γ : SL(2, ℤ)}
    (h : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 = (γ : Matrix (Fin 2) (Fin 2) ℤ) 1) :
    g = T ^ ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) * γ := by
  have h10 := congrFun h 0
  have h11 := congrFun h 1
  have hg := g.2
  have hγ := γ.2
  rw [Matrix.det_fin_two] at hg hγ
  rw [h10, h11] at hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
  · linear_combination (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hg - (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hγ
  · linear_combination (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hg - (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hγ

/-- `Γ∞`-decomposition: `(v, n) ↦ Tⁿ γ_v` is a bijection `CoprimeRow × ℤ ≃ SL(2,ℤ)`. -/
def rowEquiv : CoprimeRow × ℤ ≃ SL(2, ℤ) :=
  Equiv.ofBijective (fun p => T ^ p.2 * gam p.1) (by
    constructor
    · rintro ⟨v, n⟩ ⟨w, m⟩ h
      have hr := congrArg (fun k : SL(2, ℤ) => (k : Matrix (Fin 2) (Fin 2) ℤ) 1) h
      simp only [row_T_zpow_mul, gam_row] at hr
      have hvw : v = w := Subtype.ext hr
      subst hvw
      have hT := mul_right_cancel h
      have := congrArg (fun k : SL(2, ℤ) => (k : Matrix (Fin 2) (Fin 2) ℤ) 0 1) hT
      simp [coe_T_zpow] at this
      simp [this]
    · intro g
      let v : CoprimeRow := ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 1, bottom_row_coprime g⟩
      exact ⟨(v, _), (eq_T_zpow_mul (γ := gam v) (by rw [gam_row])).symm⟩)

/-- The strip `0 ≤ re z < 1`, a fundamental domain for `Γ∞`. -/
def strip : Set ℍ := {z | 0 ≤ z.re ∧ z.re < 1}

lemma measurableSet_strip : MeasurableSet strip :=
  measurable_coe ((measurableSet_le measurable_const Complex.measurable_re).inter
    (measurableSet_lt Complex.measurable_re measurable_const))

lemma tsum_indicator_strip (w : ℍ) (c : ℝ≥0∞) :
    ∑' n : ℤ, strip.indicator (fun _ => c) (T ^ n • w) = c := by
  rw [tsum_eq_single (-⌊w.re⌋)]
  · refine indicator_of_mem (show (T ^ (-⌊w.re⌋) • w) ∈ strip from ?_) _
    change 0 ≤ (T ^ (-⌊w.re⌋) • w).re ∧ (T ^ (-⌊w.re⌋) • w).re < 1
    rw [re_T_zpow_smul]
    push_cast
    exact ⟨by linarith [Int.floor_le w.re], by linarith [Int.lt_floor_add_one w.re]⟩
  · intro n hn
    refine indicator_of_notMem (fun hm => hn ?_) _
    have hm' : 0 ≤ (T ^ n • w).re ∧ (T ^ n • w).re < 1 := hm
    rw [re_T_zpow_smul] at hm'
    have : ⌊w.re⌋ = -n := Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    omega

lemma periodic_zpow {f : ℍ → ℝ≥0∞} (hper : ∀ z, f (T • z) = f z) (n : ℤ) (z : ℍ) :
    f (T ^ n • z) = f z := by
  induction n using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih => rw [zpow_add_one, mul_smul, ih, hper]
  | pred n ih => rw [zpow_sub_one, mul_smul, ih, ← hper, smul_inv_smul]

/-- **Unfolding over `Γ∞\Γ`**: for `T`-periodic measurable `f ≥ 0`,
`∫_𝒟 Σ_{(c,d) coprime} f(γ_{(c,d)} z) dμ = 2 ∫_{0 ≤ re z < 1} f dμ`. -/
theorem lintegral_fd_tsum_coprime (f : ℍ → ℝ≥0∞) (hf : Measurable f) (hper : ∀ z, f (T • z) = f z) :
    ∫⁻ z in ModularGroup.fd, ∑' v : CoprimeRow, f (gam v • z) = 2 * ∫⁻ z in strip, f z := by
  rw [← lintegral_indicator measurableSet_strip,
    ← lintegral_fd_tsum_SL _ (hf.indicator measurableSet_strip)]
  congr 1
  funext z
  rw [← rowEquiv.tsum_eq]
  refine Eq.trans ?_ (ENNReal.tsum_prod (f := fun v n => strip.indicator f (rowEquiv (v, n) • z))).symm
  congr 1
  funext v
  change f (gam v • z) = ∑' n : ℤ, strip.indicator f ((T ^ n * gam v) • z)
  simp only [mul_smul]
  have : ∀ n : ℤ, strip.indicator f (T ^ n • gam v • z) =
      strip.indicator (fun _ => f (gam v • z)) (T ^ n • gam v • z) := fun n => by
    by_cases h : T ^ n • gam v • z ∈ strip
    · rw [indicator_of_mem h, indicator_of_mem h, periodic_zpow hper]
    · rw [indicator_of_notMem h, indicator_of_notMem h]
  simp_rw [this]
  exact (tsum_indicator_strip _ _).symm

/-- Integrating a function of `im z` over the strip: `∫_{0≤re<1} φ(im z) dμ = ∫_0^∞ φ(y) y^{−2} dy`. -/
lemma lintegral_strip_im (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ z in strip, φ z.im = ∫⁻ y in Ioi 0, φ y * ENNReal.ofReal (y ^ (-2 : ℝ)) := by
  set S : Set ℂ := {w | 0 ≤ w.re ∧ w.re < 1}
  have hS : MeasurableSet S := (measurableSet_le measurable_const Complex.measurable_re).inter
    (measurableSet_lt Complex.measurable_re measurable_const)
  set H : ℂ → ℝ≥0∞ := S.indicator fun w => φ w.im * ENNReal.ofReal (w.im ^ (-2 : ℝ))
  have hH : Measurable H := (Measurable.mul (hφ.comp Complex.measurable_im)
    (ENNReal.measurable_ofReal.comp (Complex.measurable_im.pow_const _))).indicator hS
  have step1 : ∫⁻ z in strip, φ z.im = ∫⁻ z, H z ∂(volume.comap UpperHalfPlane.coe) := by
    rw [volume_def, setLIntegral_withDensity_eq_setLIntegral_mul _ (by fun_prop) (by fun_prop)
      measurableSet_strip, ← lintegral_indicator measurableSet_strip]
    congr 1; funext z
    by_cases hz : z ∈ strip
    · change _ = S.indicator (fun w : ℂ => φ w.im * ENNReal.ofReal (w.im ^ (-2 : ℝ))) (z : ℂ)
      rw [indicator_of_mem hz, indicator_of_mem (show (z : ℂ) ∈ S from hz), Pi.mul_apply, mul_comm]
      congr 1
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      push_cast
      rw [show (z : ℂ).im = z.im from rfl, Real.rpow_neg z.im_pos.le, Real.rpow_two,
        one_div, inv_pow]
    · change _ = S.indicator (fun w : ℂ => φ w.im * ENNReal.ofReal (w.im ^ (-2 : ℝ))) (z : ℂ)
      rw [indicator_of_notMem hz, indicator_of_notMem (show (z : ℂ) ∉ S from hz)]
  have hU : MeasurableSet upperHalfPlaneSet := measurableSet_lt measurable_const Complex.measurable_im
  rw [step1, ← measurableEmbedding_coe.lintegral_map, measurableEmbedding_coe.map_comap, range_coe,
    ← lintegral_indicator hU,
    ← Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp (hH.indicator hU),
    Measure.volume_eq_prod ℝ ℝ]
  have key : ∀ p : ℝ × ℝ, upperHalfPlaneSet.indicator H (Complex.measurableEquivRealProd.symm p) =
      (Ico (0 : ℝ) 1).indicator 1 p.1 *
        (Ioi (0 : ℝ)).indicator (fun y => φ y * ENNReal.ofReal (y ^ (-2 : ℝ))) p.2 := by
    rintro ⟨x, y⟩
    rw [Complex.measurableEquivRealProd_symm_apply]
    by_cases hy : 0 < y
    · rw [indicator_of_mem (show (⟨x, y⟩ : ℂ) ∈ upperHalfPlaneSet from hy),
        indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy)]
      change S.indicator (fun w : ℂ => φ w.im * ENNReal.ofReal (w.im ^ (-2 : ℝ))) ⟨x, y⟩ = _
      by_cases hx : x ∈ Ico (0 : ℝ) 1
      · rw [indicator_of_mem (show (⟨x, y⟩ : ℂ) ∈ S from hx), indicator_of_mem hx]
        simp
      · rw [indicator_of_notMem (show (⟨x, y⟩ : ℂ) ∉ S from hx), indicator_of_notMem hx]
        simp
    · rw [indicator_of_notMem (show (⟨x, y⟩ : ℂ) ∉ upperHalfPlaneSet from hy),
        indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy)]
      simp
  simp_rw [key]
  rw [lintegral_prod_mul (f := (Ico (0 : ℝ) 1).indicator 1)
    (g := (Ioi (0 : ℝ)).indicator fun y => φ y * ENNReal.ofReal (y ^ (-2 : ℝ)))
    (measurable_one.indicator measurableSet_Ico).aemeasurable
    ((hφ.mul (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))).indicator
      measurableSet_Ioi).aemeasurable, lintegral_indicator_one measurableSet_Ico,
    lintegral_indicator measurableSet_Ioi]
  simp

/-- **Rankin–Selberg unfolding**: for measurable `φ ≥ 0`,
`∫_𝒟 Σ_{(c,d) coprime} φ(im(γ_{(c,d)} z)) dμ = 2 ∫_0^∞ φ(y) y^{−2} dy`. -/
theorem lintegral_fd_tsum_coprime_im (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ z in ModularGroup.fd, ∑' v : CoprimeRow, φ (gam v • z).im =
      2 * ∫⁻ y in Ioi 0, φ y * ENNReal.ofReal (y ^ (-2 : ℝ)) := by
  rw [lintegral_fd_tsum_coprime (fun z => φ z.im) (hφ.comp (by fun_prop)) (fun z => by
    simp only [im_T_smul]), lintegral_strip_im φ hφ]

/-- `Im(γ_v z) = y/|v₀z + v₁|²`: it depends on `v` only. -/
lemma im_gam_smul (v : CoprimeRow) (z : ℍ) : (gam v • z).im = z.im / ModEisenstein.nq z v.1 := by
  rw [ModEisenstein.im_smul, ModEisenstein.nq, ModEisenstein.dn, ← gam_row v]

/-- **Rankin–Selberg unfolding, in the coordinates of `E`**: for measurable `φ ≥ 0`,
`∫_𝒟 Σ_{(c,d) coprime} φ(y/|cz + d|²) dμ = 2 ∫_0^∞ φ(y) y^{−2} dy`. -/
theorem lintegral_fd_tsum_nq (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ z in ModularGroup.fd, ∑' v : CoprimeRow, φ (z.im / ModEisenstein.nq z v.1) =
      2 * ∫⁻ y in Ioi 0, φ y * ENNReal.ofReal (y ^ (-2 : ℝ)) := by
  simp_rw [← im_gam_smul]
  exact lintegral_fd_tsum_coprime_im φ hφ

end ModFD
