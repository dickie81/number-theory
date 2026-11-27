import EllipticAdd

/-!
# Legendre's relation

Item (4) of the Weierstrass theory that the gain's CM theta needs: Legendre's relation `η₁ω₂ − η₂ω₁ = 2πi` for the
quasi-periods `η_i = 2ζ_W(ω_i/2)` and `Im(ω₂/ω₁) > 0` is a theorem (`legendre`, of type `CMThetaOne.Legendre`), so the
hypothesis `Legendre` of `CMThetaOne` is discharged.

**Cauchy's theorem for a parallelogram.** Mathlib integrates holomorphic functions over rectangles. The parallelogram
`a + [0, 1]u + [0, 1]v` is the image of the unit square under an `ℝ`-affine map, which is not holomorphic, so Cauchy's
theorem for it (`parInt_eq_zero`) comes from Mathlib's divergence theorem on `[0, 1]²`
(`integral2_divergence_prod_of_hasFDerivAt`) for the pair `(v·f, −u·f)` composed with the map, whose divergence is
`v·f′·u − u·f′·v = 0`. The boundary integral `parInt` lists the four sides.

**`∮ dz/z = 2πi`.** Along a segment `d·∫₀¹ dt/(p + td) = log(1 + d/p)` when `Im(d/p) ≠ 0` (`integral_inv_segment`:
`log` is a primitive of `1/z` on the slit plane). For the parallelogram centred at `0` the four sides give
`log r + log(−1/r) − log(1/r) − log(−r)` with `r = (v − u)/(u + v)`, `Im r > 0`, which is `2πi` (`log_four`,
`parInt_inv`).

**The relation.** `ζ_W = 1/z + zetaE` with `zetaE` holomorphic off the nonzero periods (`zetaW_eq_add`,
`differentiableOn_zetaE`). The centred fundamental parallelogram meets the lattice only at its centre `0` (`par_coord`,
`par_boundary`, `par_mem`), so `∮ζ_W = ∮dz/z + ∮zetaE = 2πi`; pairing opposite sides by quasi-periodicity,
`∮ζ_W = η₁ω₂ − η₂ω₁` (`parInt_zetaW`).

**Main declarations:** `legendre`; for the later modules `zetaE`, `zetaW_eq_add`, `differentiableOn_zetaE`,
`zetaW_add_basis`.
-/

namespace EllipticLegendre

noncomputable section

open PeriodPair ThetaNorm CMThetaOne EllipticAdd Complex Filter Topology MeasureTheory Set

open scoped Interval

/-! ## Contour integrals over a parallelogram -/

/-- **The boundary integral of `f` over the parallelogram** with vertex `a` and sides `u`, `v` (positively oriented when
`Im(v/u) > 0`), side by side: `∫_{a}^{a+u} + ∫_{a+u}^{a+u+v} − ∫_{a+v}^{a+u+v} − ∫_{a}^{a+v}`. -/
def parInt (f : ℂ → ℂ) (a u v : ℂ) : ℂ :=
  u * (∫ s : ℝ in (0)..1, f (a + s * u)) + v * (∫ t : ℝ in (0)..1, f (a + u + t * v)) -
    u * (∫ s : ℝ in (0)..1, f (a + s * u + v)) - v * (∫ t : ℝ in (0)..1, f (a + t * v))

/-- **Cauchy's theorem for a parallelogram**: the boundary integral of a function holomorphic on the closed
parallelogram vanishes (the divergence theorem on `[0, 1]²` for `(s, t) ↦ (v·f, −u·f)(a + su + tv)`, whose divergence
`v·f′·u − u·f′·v` is `0`). -/
theorem parInt_eq_zero {f : ℂ → ℂ} {a u v : ℂ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ f (a + s * u + t * v)) :
    parInt f a u v = 0 := by
  set L : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v with hLdef
  have hLp : ∀ p : ℝ × ℝ, L p = (p.1 : ℂ) * u + (p.2 : ℂ) * v := fun p => by
    simp [hLdef, Complex.real_smul]
  set φ : ℝ × ℝ → ℂ := fun p => a + L p with hφ
  have hφp : ∀ p : ℝ × ℝ, φ p = a + (p.1 : ℂ) * u + (p.2 : ℂ) * v := fun p => by
    simp only [hφ, hLp]; ring
  have hL : ∀ p, HasFDerivAt φ L p := fun p => L.hasFDerivAt.const_add a
  have hbox : ∀ p ∈ [[(0 : ℝ), 1]] ×ˢ [[(0 : ℝ), 1]], DifferentiableAt ℂ f (φ p) := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    rw [uIcc_of_le zero_le_one] at hs ht
    rw [hφp]
    exact hf s hs t ht
  set F : ℝ × ℝ → ℂ := fun p => f (φ p) with hF
  have hdF : ∀ p ∈ [[(0 : ℝ), 1]] ×ˢ [[(0 : ℝ), 1]], HasFDerivAt F (deriv f (φ p) • L) p :=
    fun p hp => (hbox p hp).hasDerivAt.comp_hasFDerivAt p (hL p)
  have hIoo : Ioo (min (0 : ℝ) 1) (max 0 1) ×ˢ Ioo (min (0 : ℝ) 1) (max 0 1) ⊆ [[(0 : ℝ), 1]] ×ˢ [[(0 : ℝ), 1]] :=
    prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have key := integral2_divergence_prod_of_hasFDerivAt (fun p => v * F p) (fun p => -u * F p)
    (fun p => v • (deriv f (φ p) • L)) (fun p => (-u) • (deriv f (φ p) • L)) 0 0 1 1
    (fun p hp => ((hdF p hp).continuousAt.continuousWithinAt).const_smul v)
    (fun p hp => ((hdF p hp).continuousAt.continuousWithinAt).const_smul (-u))
    (fun p hp => (hdF p (hIoo hp)).const_mul v) (fun p hp => (hdF p (hIoo hp)).const_mul (-u)) (by
      have h0 : (fun p : ℝ × ℝ => (v • (deriv f (φ p) • L)) (1, 0) + ((-u) • (deriv f (φ p) • L)) (0, 1)) = 0 := by
        funext p
        simp only [FunLike.coe_smul, Pi.smul_apply, hLp, smul_eq_mul, Pi.zero_apply]
        push_cast
        ring
      rw [h0]
      exact integrableOn_zero)
  have h0 : ∀ p : ℝ × ℝ, (v • (deriv f (φ p) • L)) (1, 0) + ((-u) • (deriv f (φ p) • L)) (0, 1) = 0 := by
    intro p
    simp only [FunLike.coe_smul, Pi.smul_apply, hLp, smul_eq_mul]
    push_cast
    ring
  simp only [h0, intervalIntegral.integral_zero] at key
  simp only [intervalIntegral.integral_const_mul, hF, hφp] at key
  simp only [ofReal_one, ofReal_zero, one_mul, zero_mul, add_zero] at key
  rw [parInt]
  linear_combination -key

/-- **Integrability on the four sides.** -/
def ParIntegrable (f : ℂ → ℂ) (a u v : ℂ) : Prop :=
  IntervalIntegrable (fun s : ℝ => f (a + s * u)) volume 0 1 ∧
    IntervalIntegrable (fun t : ℝ => f (a + u + t * v)) volume 0 1 ∧
    IntervalIntegrable (fun s : ℝ => f (a + s * u + v)) volume 0 1 ∧
    IntervalIntegrable (fun t : ℝ => f (a + t * v)) volume 0 1

/-- **A function continuous on the boundary is integrable on the four sides.** -/
theorem parIntegrable_of_continuousAt {f : ℂ → ℂ} {a u v : ℂ}
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      ContinuousAt f (a + s * u + t * v)) : ParIntegrable f a u v := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hI : ∀ g : ℝ → ℂ, Continuous g → (∀ s ∈ Icc (0 : ℝ) 1, ContinuousAt f (g s)) →
      IntervalIntegrable (fun s => f (g s)) volume 0 1 := fun g hg hfg =>
    (ContinuousOn.intervalIntegrable fun s hs => by
      rw [uIcc_of_le zero_le_one] at hs
      exact ((hfg s hs).comp hg.continuousAt).continuousWithinAt)
  refine ⟨hI _ (by fun_prop) fun s hs => ?_, hI _ (by fun_prop) fun t ht => ?_,
    hI _ (by fun_prop) fun s hs => ?_, hI _ (by fun_prop) fun t ht => ?_⟩
  · simpa using h s hs 0 h01 (by tauto)
  · simpa using h 1 h11 t ht (by tauto)
  · simpa using h s hs 1 h11 (by tauto)
  · simpa using h 0 h01 t ht (by tauto)

/-- **The boundary integral is additive.** -/
theorem parInt_add {f g : ℂ → ℂ} {a u v : ℂ} (hf : ParIntegrable f a u v) (hg : ParIntegrable g a u v) :
    parInt (fun z => f z + g z) a u v = parInt f a u v + parInt g a u v := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  simp only [parInt]
  rw [intervalIntegral.integral_add hf1 hg1, intervalIntegral.integral_add hf2 hg2,
    intervalIntegral.integral_add hf3 hg3, intervalIntegral.integral_add hf4 hg4]
  ring

/-! ## The integral of `dz/z` around the parallelogram -/

/-- **`dz/z` along a segment**: `d·∫₀¹ dt/(p + td) = log(1 + d/p)` when `Im(d/p) ≠ 0` (the segment `1 + t·d/p` stays in
the slit plane, where `log` is a primitive of `1/z`). -/
theorem integral_inv_segment {p d : ℂ} (hp : p ≠ 0) (hd : (d / p).im ≠ 0) :
    d * ∫ t : ℝ in (0)..1, 1 / (p + t * d) = Complex.log (1 + d / p) := by
  set r := d / p with hr
  have hw : ∀ t ∈ uIcc (0 : ℝ) 1, 1 + (t : ℂ) * r ∈ slitPlane := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0; simp
    · refine mem_slitPlane_iff.mpr (Or.inr ?_)
      simp only [add_im, one_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_add]
      exact mul_ne_zero h0.ne' hd
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => Complex.log (1 + t * r)) (r / (1 + t * r)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 + (t : ℂ) * r) r t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const r).const_add 1
    exact h1.clog_real (hw t ht)
  have hcont : ContinuousOn (fun t : ℝ => r / (1 + t * r)) (uIcc 0 1) :=
    continuousOn_const.div (by fun_prop) fun t ht => slitPlane_ne_zero (hw t ht)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero, Complex.log_one, sub_zero] at hint
  rw [← intervalIntegral.integral_const_mul, ← hint]
  congr 1
  funext t
  rw [show p + t * d = p * (1 + t * r) by rw [hr]; field_simp, mul_one_div, ← div_div, hr]

/-- **A logarithm identity**: `log r + log(−1/r) − log(1/r) − log(−r) = 2πi` for `Im r > 0` (the moduli cancel and the
arguments add up to `θ + (π − θ) + θ − (θ − π)`). -/
theorem log_four {r : ℂ} (hr : 0 < r.im) :
    Complex.log r + Complex.log (-1 / r) - Complex.log (1 / r) - Complex.log (-r) = 2 * Real.pi * I := by
  have hne : arg r ≠ Real.pi := by
    rw [Ne, arg_eq_pi_iff]; intro h; linarith [h.2]
  have hr0 : r ≠ 0 := fun h => by simp [h] at hr
  have him : (r⁻¹).im < 0 := by
    rw [inv_im, neg_div]
    exact neg_neg_of_pos (div_pos hr (normSq_pos.mpr hr0))
  have h1 : arg (-r) = arg r - Real.pi := arg_neg_eq_arg_sub_pi_of_im_pos hr
  have h2 : arg r⁻¹ = -arg r := by simp [arg_inv, hne]
  have h3 : arg (-r⁻¹) = arg r⁻¹ + Real.pi := arg_neg_eq_arg_add_pi_of_im_neg him
  apply Complex.ext
  · simp only [sub_re, add_re, log_re, norm_neg, neg_div, one_div, norm_inv]
    simp
  · simp only [sub_im, add_im, log_im, neg_div, one_div, h1, h2, h3]
    simp
    ring

/-- **`∮ dz/z = 2πi` around the parallelogram centred at `0`** with sides `u`, `v`, `Im(v/u) > 0`: the four sides give
`log r`, `log(−1/r)`, `−log(1/r)`, `−log(−r)` for `r = (v − u)/(u + v)`, and `Im r > 0`. -/
theorem parInt_inv {u v : ℂ} (hu : u ≠ 0) (hτ : 0 < (v / u).im) :
    parInt (fun z => 1 / z) (-(u + v) / 2) u v = 2 * Real.pi * I := by
  set τ := v / u with hτdef
  have hv : v = τ * u := by rw [hτdef]; field_simp
  have hτ1 : τ + 1 ≠ 0 := fun h => by
    have : τ = -1 := by linear_combination h
    rw [this] at hτ; simp at hτ
  have hτ1' : τ - 1 ≠ 0 := fun h => by
    have : τ = 1 := by linear_combination h
    rw [this] at hτ; simp at hτ
  set r := (τ - 1) / (τ + 1) with hrdef
  have hr : 0 < r.im := by
    rw [hrdef, div_im]
    have hn := normSq_pos.mpr hτ1
    simp only [sub_im, one_im, sub_zero, add_re, one_re, sub_re, add_im, add_zero]
    rw [← sub_div]
    exact div_pos (by nlinarith) hn
  have hr0 : r ≠ 0 := fun h => by simp [h] at hr
  have hrim : r.im ≠ 0 := hr.ne'
  have hinvim : (r⁻¹).im ≠ 0 := by
    rw [inv_im]; exact div_ne_zero (neg_ne_zero.mpr hrim) (normSq_pos.mpr hr0).ne'
  set a := -(u + v) / 2 with ha
  have hpa : a ≠ 0 := by
    rw [ha, hv]; intro h; apply hτ1
    have : u * (τ + 1) = 0 := by linear_combination -2 * h
    exact (mul_eq_zero.mp this).resolve_left hu
  have hpu : a + u ≠ 0 := by
    rw [ha, hv]; intro h; apply hτ1'
    have : u * (τ - 1) = 0 := by linear_combination -2 * h
    exact (mul_eq_zero.mp this).resolve_left hu
  have hpv : a + v ≠ 0 := by
    rw [ha, hv]; intro h; apply hτ1'
    have : u * (τ - 1) = 0 := by linear_combination 2 * h
    exact (mul_eq_zero.mp this).resolve_left hu
  have n1 : 1 + τ ≠ 0 := by rw [add_comm]; exact hτ1
  have n2 : 1 - τ ≠ 0 := fun h => hτ1' (by linear_combination -h)
  have n3 : -1 + τ ≠ 0 := fun h => hτ1' (by linear_combination h)
  have e1 : 1 + u / a = r := by rw [ha, hv, hrdef]; field_simp; ring
  have e2 : 1 + v / (a + u) = -1 / r := by
    rw [show a + u = u * (1 - τ) / 2 by rw [ha, hv]; ring, hv, hrdef]; field_simp; ring
  have e3 : 1 + u / (a + v) = 1 / r := by
    rw [show a + v = -(u * (1 - τ)) / 2 by rw [ha, hv]; ring, hrdef]; field_simp; ring
  have e4 : 1 + v / a = -r := by rw [ha, hv, hrdef]; field_simp; ring
  have im1 : (u / a).im ≠ 0 := by rw [show u / a = r - 1 by rw [← e1]; ring]; simpa using hrim
  have im2 : (v / (a + u)).im ≠ 0 := by
    rw [show v / (a + u) = -1 / r - 1 by rw [← e2]; ring]
    simpa [neg_div, one_div] using hinvim
  have im3 : (u / (a + v)).im ≠ 0 := by
    rw [show u / (a + v) = 1 / r - 1 by rw [← e3]; ring]
    simpa [one_div] using hinvim
  have im4 : (v / a).im ≠ 0 := by rw [show v / a = -r - 1 by rw [← e4]; ring]; simpa using hrim
  have i1 := integral_inv_segment hpa im1
  have i2 := integral_inv_segment hpu im2
  have i3 := integral_inv_segment hpv im3
  have i4 := integral_inv_segment hpa im4
  rw [e1] at i1
  rw [e2] at i2
  rw [e3] at i3
  rw [e4] at i4
  have h3 : (fun s : ℝ => 1 / (a + s * u + v)) = fun s : ℝ => 1 / (a + v + s * u) := by
    funext s; ring_nf
  simp only [parInt]
  rw [h3, i1, i2, i3, i4]
  exact log_four hr

/-! ## `ζ_W` without its pole at `0` -/

variable (Λ : PeriodPair)

/-- **`ζ_W` without its `0`-term**: `ζ_W(z) − 1/z` (`zetaW_eq_add`), holomorphic at `0`. -/
def zetaE (z : ℂ) : ℂ :=
  ∑' l : Λ.lattice, if (l : ℂ) = 0 then 0 else 1 / (z - l) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2

/-- **`zetaE` is the locally uniform sum of its summands.** -/
theorem hasSumLocallyUniformly_zetaE :
    HasSumLocallyUniformly (fun (l : Λ.lattice) (z : ℂ) =>
      if (l : ℂ) = 0 then 0 else 1 / (z - l) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) (zetaE Λ) := by
  refine Λ.hasSumLocallyUniformly_aux (u := fun r l => 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ)) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r _ =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simp only [norm_zero]; positivity
  · exact zeta_bound hs h

/-- **`ζ_W(z) = 1/z + zetaE(z)`** for all `z` (both sides are `0` at `z = 0`). -/
theorem zetaW_eq_add (z : ℂ) : zetaW Λ z = 1 / z + zetaE Λ z := by
  have h1 : HasSum (fun l : Λ.lattice => 1 / (z - l) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) (zetaW Λ z) :=
    (hasSumLocallyUniformly_zetaW Λ).hasSum
  have h2 := (hasSum_ite_eq (0 : Λ.lattice) (1 / z)).add ((hasSumLocallyUniformly_zetaE Λ).hasSum (x := z))
  refine h1.unique ?_
  convert h2 using 1
  funext l
  by_cases hl : (l : ℂ) = 0
  · have : l = 0 := Subtype.ext hl
    simp [this]
  · have : l ≠ 0 := fun h => hl (by simp [h])
    simp [this, hl]

/-- **`zetaE` is holomorphic off the nonzero periods.** -/
theorem differentiableOn_zetaE : DifferentiableOn ℂ (zetaE Λ) (Λ.lattice \ {0})ᶜ := by
  refine (hasSumLocallyUniformly_zetaE Λ).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s => .fun_sum fun l _ => ?_) Λ.isOpen_compl_lattice_sdiff
  split_ifs with hl
  · exact differentiableOn_const _
  · refine .add (.add (.div (by fun_prop) (by fun_prop) fun z hz => ?_) (by fun_prop)) (by fun_prop)
    intro h
    exact hz ⟨sub_eq_zero.mp h ▸ l.2, by simpa [sub_eq_zero.mp h] using hl⟩

/-! ## Legendre's relation -/

/-- **The lattice points of the centred parallelogram**: `−(ω₁ + ω₂)/2 + sω₁ + tω₂ ∈ Λ` with `s, t ∈ [0, 1]` only for
`s = t = 1/2` (the point `0`). -/
theorem par_coord {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (h : -(Λ.ω₁ + Λ.ω₂) / 2 + s * Λ.ω₁ + t * Λ.ω₂ ∈ Λ.lattice) : s = 1 / 2 ∧ t = 1 / 2 := by
  obtain ⟨m, n, e⟩ := mem_lattice.mp h
  have hp := LinearIndependent.pair_iff.mp Λ.indep (s - 1 / 2 - m) (t - 1 / 2 - n) (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination -e)
  obtain ⟨h1, h2⟩ := hp
  have hm : m = 0 := by
    have a1 : (m : ℝ) < 1 := by linarith [hs.2]
    have a2 : (-1 : ℝ) < m := by linarith [hs.1]
    have b1 : m < 1 := by exact_mod_cast a1
    have b2 : -1 < m := by exact_mod_cast a2
    omega
  have hn : n = 0 := by
    have a1 : (n : ℝ) < 1 := by linarith [ht.2]
    have a2 : (-1 : ℝ) < n := by linarith [ht.1]
    have b1 : n < 1 := by exact_mod_cast a1
    have b2 : -1 < n := by exact_mod_cast a2
    omega
  subst hm hn
  constructor <;> linarith

/-- **The boundary of the centred parallelogram avoids the lattice.** -/
theorem par_boundary {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) : -(Λ.ω₁ + Λ.ω₂) / 2 + s * Λ.ω₁ + t * Λ.ω₂ ∉ Λ.lattice := by
  intro h
  obtain ⟨h1, h2⟩ := par_coord Λ hs ht h
  rcases hb with rfl | rfl | rfl | rfl
  · norm_num at h1
  · norm_num at h1
  · norm_num at h2
  · norm_num at h2

/-- **The only period in the closed centred parallelogram is `0`.** -/
theorem par_mem {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (h : -(Λ.ω₁ + Λ.ω₂) / 2 + s * Λ.ω₁ + t * Λ.ω₂ ∈ Λ.lattice) : -(Λ.ω₁ + Λ.ω₂) / 2 + s * Λ.ω₁ + t * Λ.ω₂ = 0 := by
  obtain ⟨rfl, rfl⟩ := par_coord Λ hs ht h
  push_cast
  ring

/-- **The quasi-period of a basis period**: `ζ_W(z + ω) − ζ_W(z) = 2ζ_W(ω/2)` off the lattice. -/
theorem zetaW_add_basis {ω : ℂ} (hω : ω ∈ Λ.lattice) (hh : ω / 2 ∉ Λ.lattice) {z : ℂ} (hz : z ∉ Λ.lattice) :
    zetaW Λ (z + ω) - zetaW Λ z = 2 * zetaW Λ (ω / 2) := by
  have hmh : -(ω / 2) ∉ Λ.lattice := fun h => hh (by simpa using neg_mem h)
  rw [zetaW_add_sub_const Λ hω hz hmh, show -(ω / 2) + ω = ω / 2 by ring, zetaW_neg]
  ring

/-- **The boundary integral of `ζ_W` by quasi-periodicity**: opposite sides differ by the quasi-periods, so
`∮ ζ_W = η₁ω₂ − η₂ω₁` with `η_i = 2ζ_W(ω_i/2)`. -/
theorem parInt_zetaW : parInt (zetaW Λ) (-(Λ.ω₁ + Λ.ω₂) / 2) Λ.ω₁ Λ.ω₂ =
    2 * zetaW Λ (Λ.ω₁ / 2) * Λ.ω₂ - 2 * zetaW Λ (Λ.ω₂ / 2) * Λ.ω₁ := by
  set a := -(Λ.ω₁ + Λ.ω₂) / 2 with ha
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  have hcont : ∀ z ∉ Λ.lattice, ContinuousAt (zetaW Λ) z := fun z hz =>
    ((differentiableOn_zetaW Λ z hz).differentiableAt (hU.mem_nhds hz)).continuousAt
  obtain ⟨hi1, hi2, hi3, hi4⟩ := parIntegrable_of_continuousAt (f := zetaW Λ) (a := a) (u := Λ.ω₁) (v := Λ.ω₂)
    fun s hs t ht hb => hcont _ (par_boundary Λ hs ht hb)
  have hb1 : ∀ s ∈ uIcc (0 : ℝ) 1, a + s * Λ.ω₁ ∉ Λ.lattice := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    have h := par_boundary Λ hs h01 (Or.inr (Or.inr (Or.inl rfl)))
    rwa [ofReal_zero, zero_mul, add_zero] at h
  have hb4 : ∀ t ∈ uIcc (0 : ℝ) 1, a + t * Λ.ω₂ ∉ Λ.lattice := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    have h := par_boundary Λ h01 ht (Or.inl rfl)
    rwa [ofReal_zero, zero_mul, add_zero] at h
  have d1 : (∫ s : ℝ in (0)..1, zetaW Λ (a + s * Λ.ω₁)) - ∫ s : ℝ in (0)..1, zetaW Λ (a + s * Λ.ω₁ + Λ.ω₂) =
      -(2 * zetaW Λ (Λ.ω₂ / 2)) := by
    rw [← intervalIntegral.integral_sub hi1 hi3, intervalIntegral.integral_congr (g := fun _ => -(2 *
      zetaW Λ (Λ.ω₂ / 2))) fun s hs => ?_]
    · simp
    · simp only
      rw [← zetaW_add_basis Λ Λ.ω₂_mem_lattice Λ.ω₂_div_two_notMem_lattice (hb1 s hs)]
      ring
  have d2 : (∫ t : ℝ in (0)..1, zetaW Λ (a + Λ.ω₁ + t * Λ.ω₂)) - ∫ t : ℝ in (0)..1, zetaW Λ (a + t * Λ.ω₂) =
      2 * zetaW Λ (Λ.ω₁ / 2) := by
    rw [← intervalIntegral.integral_sub hi2 hi4, intervalIntegral.integral_congr (g := fun _ =>
      2 * zetaW Λ (Λ.ω₁ / 2)) fun t ht => ?_]
    · simp
    · simp only
      rw [← zetaW_add_basis Λ Λ.ω₁_mem_lattice Λ.ω₁_div_two_notMem_lattice (hb4 t ht)]
      ring_nf
  rw [parInt]
  linear_combination Λ.ω₁ * d1 + Λ.ω₂ * d2

/-- **Legendre's relation** `η₁ω₂ − η₂ω₁ = 2πi` (`CMThetaOne.Legendre`, now a theorem): `∮ ζ_W` around the centred
fundamental parallelogram is `η₁ω₂ − η₂ω₁` by quasi-periodicity (`parInt_zetaW`) and `2πi` by `ζ_W = 1/z + zetaE`, with
`∮ dz/z = 2πi` (`parInt_inv`) and `∮ zetaE = 0` (`parInt_eq_zero`, Cauchy: the only period inside is `0`). -/
theorem legendre : Legendre := by
  intro Λ hor
  set a := -(Λ.ω₁ + Λ.ω₂) / 2 with ha
  have hu : Λ.ω₁ ≠ 0 := Λ.indep.ne_zero 0
  have hsE : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ (zetaE Λ) (a + s * Λ.ω₁ + t * Λ.ω₂) := by
    intro s hs t ht
    refine (differentiableOn_zetaE Λ _ ?_).differentiableAt (Λ.isOpen_compl_lattice_sdiff.mem_nhds ?_) <;>
    · rintro ⟨h1, h2⟩
      exact h2 (par_mem Λ hs ht h1)
  have hiE := parIntegrable_of_continuousAt (f := zetaE Λ) (a := a) (u := Λ.ω₁) (v := Λ.ω₂)
    fun s hs t ht _ => (hsE s hs t ht).continuousAt
  have hiI := parIntegrable_of_continuousAt (f := fun z : ℂ => 1 / z) (a := a) (u := Λ.ω₁) (v := Λ.ω₂)
    fun s hs t ht hb => by
      have hne : a + s * Λ.ω₁ + t * Λ.ω₂ ≠ 0 := fun h => par_boundary Λ hs ht hb (h ▸ zero_mem _)
      exact (continuousAt_const.div continuousAt_id hne)
  have hsplit := parInt_add hiI hiE
  rw [parInt_inv hu hor, parInt_eq_zero hsE, add_zero] at hsplit
  have hfun : (fun z => 1 / z + zetaE Λ z) = zetaW Λ := funext fun z => (zetaW_eq_add Λ z).symm
  rw [hfun, parInt_zetaW] at hsplit
  exact hsplit

end

end EllipticLegendre
