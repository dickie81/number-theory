/-
# The orbit curve: a realization of `K` along the positive reals

Plain statement. `BallLattice.Realization` places a vector `w_r` at each positive rational `r`, with similitudes `φ_n`
for the positive integers. A *curve realization* (`CurveRealization`) places a vector `w_x` at every positive real `x`,
with commuting similitudes `ψ_s` of factor `s` for every real `s > 0`, `ψ_s(w_x) = w_{sx}` and
`⟨w_y, w_x⟩ = √(xy)·k(x/y)`. In log coordinates `v_t = e^{−t/2}w_{e^t}` and `U_s = e^{−s/2}ψ_{e^s}`, the maps `U_s`
preserve the inner product and `v_{t+s} = U_s v_t` (`flow_inner`, `flow_orbit`): the curve is the orbit of `v_0` under
a one-parameter group of isometries, the infinite-dimensional analogue of the Frobenius orbit of `ManinFrobenius`.
* A curve realization restricts to a realization on the rationals (`toRealization`), so it forces RH.
* Under RH, `ℓ²` of the zeros with `w_x = (e^{(ρ − ½)²/4} x^ρ)_ρ` and `ψ_s` multiplying the coordinate of `ρ` by `s^ρ`
  is a curve realization of `K` (`curveRealization`). So RH holds exactly when `K` has a curve realization
  (`rh_iff_curveRealization`).
* For a kernel with `‖k(r) + k(1/r) − 2k(1)‖ ≤ M(log r)²` on `[1, 2]`, every curve realization is continuous on
  `(0, ∞)` (`continuousOn_of_smooth`); this applies to `K` (`continuousOn_kerK`). In a curve realization of `K` the map
  `x ↦ w_x` is injective (`injective_kerK`), and, as on the rationals, `‖w_{n+1} − w_n‖ → 0` (`not_discrete`).
So the orbit is a continuous injective curve through the Hilbert space, along which the integer points crowd together:
it spans no lattice.
-/
import Mathlib
import BallLattice

open Real Complex Filter Topology ComplexConjugate Set WeilForm WeilTest
open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace BallCurve

open BallKernel BallLattice

/-- A **curve realization** of a kernel `k`: vectors `w_x` for real `x > 0` and similitudes `ψ_s` of factor `s` for
real `s > 0`, with `ψ_sψ_t = ψ_{st}`, `ψ_s(w_x) = w_{sx}` and `⟨w_y, w_x⟩ = √(xy)·k(x/y)`. -/
structure CurveRealization (k : ℝ → ℂ) where
  /-- The space. -/
  E : Type
  [normedAddCommGroup : NormedAddCommGroup E]
  [innerProductSpace : InnerProductSpace ℂ E]
  /-- The curve `x ↦ w_x`. -/
  w : ℝ → E
  /-- The similitudes `ψ_s`. -/
  ψ : ℝ → E →ₗ[ℂ] E
  similitude : ∀ s : ℝ, 0 < s → ∀ x y : E, ⟪ψ s x, ψ s y⟫_ℂ = (s : ℂ) * ⟪x, y⟫_ℂ
  comp : ∀ s t : ℝ, 0 < s → 0 < t → (ψ s).comp (ψ t) = ψ (s * t)
  orbit : ∀ s x : ℝ, 0 < s → 0 < x → ψ s (w x) = w (s * x)
  gram : ∀ a b : ℝ, 0 < a → 0 < b → ⟪w b, w a⟫_ℂ = (Real.sqrt (a * b) : ℂ) * k (a / b)

attribute [instance] CurveRealization.normedAddCommGroup CurveRealization.innerProductSpace

variable {k : ℝ → ℂ}

/-! ## Log coordinates: a one-parameter group of isometries -/

/-- The curve in log coordinates, `v_t = e^{−t/2}w_{e^t}`. -/
def CurveRealization.v (C : CurveRealization k) (t : ℝ) : C.E := (Real.exp (-t / 2) : ℂ) • C.w (Real.exp t)

/-- The flow `U_s = e^{−s/2}ψ_{e^s}`. -/
def CurveRealization.U (C : CurveRealization k) (s : ℝ) : C.E →ₗ[ℂ] C.E := (Real.exp (-s / 2) : ℂ) • C.ψ (Real.exp s)

/-- **`U_s` preserves the inner product.** -/
theorem flow_inner (C : CurveRealization k) (s : ℝ) (x y : C.E) : ⟪C.U s x, C.U s y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [CurveRealization.U, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    C.similitude _ (Real.exp_pos s)]
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  rw [show -s / 2 + -s / 2 + s = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- **The curve is an orbit of the flow**: `v_{t+s} = U_s v_t`. -/
theorem flow_orbit (C : CurveRealization k) (s t : ℝ) : C.v (t + s) = C.U s (C.v t) := by
  simp only [CurveRealization.v, CurveRealization.U, LinearMap.smul_apply, map_smul,
    C.orbit _ _ (Real.exp_pos s) (Real.exp_pos t), smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  · ring_nf
  · rw [add_comm]

/-- `U_s U_t = U_{s+t}`. -/
theorem flow_add (C : CurveRealization k) (s t : ℝ) : (C.U s).comp (C.U t) = C.U (s + t) := by
  refine LinearMap.ext fun x => ?_
  simp only [CurveRealization.U, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul]
  rw [← LinearMap.comp_apply (C.ψ _), C.comp _ _ (Real.exp_pos s) (Real.exp_pos t), ← Complex.ofReal_mul,
    ← Real.exp_add, ← Real.exp_add]
  congr 3; ring

/-! ## Restriction to the rationals -/

/-- **A curve realization restricts to a realization on the rationals.** -/
def toRealization (C : CurveRealization k) : Realization k where
  E := C.E
  w r := C.w r
  φ n := C.ψ n
  similitude n hn x y := by
    have := C.similitude n (by exact_mod_cast hn) x y
    simpa using this
  comp m n hm hn := by
    rw [C.comp _ _ (by exact_mod_cast hm) (by exact_mod_cast hn)]
    push_cast
    rfl
  orbit n r hn hr := by
    rw [C.orbit _ _ (by exact_mod_cast hn) (by exact_mod_cast hr)]
    push_cast
    rfl
  gram a b ha hb := C.gram a b (by exact_mod_cast ha) (by exact_mod_cast hb)

/-- **A curve realization of `K` forces RH.** -/
theorem rh_of_curveRealization (C : CurveRealization BallKernel.kerK) : RiemannHypothesis :=
  rh_iff_realization.2 ⟨toRealization C⟩

/-! ## Under RH, a curve realization in `ℓ²` of the zeros -/

/-- The vector `w_x = (c_ρ x^ρ)_ρ` for real `x`. -/
def wvR (x : ℝ) : L2 :=
  ⟨fun q => BallLattice.cw q * pw q x, memℓp_of_sq <| by
    refine (summable_cw_sq.mul_right (Real.exp |Real.log x| ^ 2)).of_nonneg_of_le (fun q => by positivity)
      fun q => ?_
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_pw_le q x) 2) (by positivity)⟩

/-- The map multiplying the coordinate of `ρ` by `s^ρ`, for real `s`. -/
def psiL (s : ℝ) : L2 →ₗ[ℂ] L2 where
  toFun x := ⟨fun q => pw q s * x q, memℓp_of_sq <| by
    refine ((summable_sq_of_mem x).mul_left (Real.exp |Real.log s| ^ 2)).of_nonneg_of_le
      (fun q => by positivity) fun q => ?_
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_pw_le q s) 2) (by positivity)⟩
  map_add' x y := by
    ext q
    show pw q s * (x + y) q = pw q s * x q + pw q s * y q
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    ext q
    show pw q s * (c • x) q = c * (pw q s * x q)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

lemma psiL_apply (s : ℝ) (x : L2) (q : ZIdx) : psiL s x q = pw q s * x q := rfl

lemma wvR_apply (x : ℝ) (q : ZIdx) : wvR x q = BallLattice.cw q * pw q x := rfl

/-- Under RH, the real version of `BallLattice.gram_cw`. -/
lemma gram_cwR (hRH : RiemannHypothesis) (a b : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) :
    ∑' q, BallLattice.cw q * pw q a * conj (BallLattice.cw q * pw q b) = (Real.sqrt (a * b) : ℂ) * BallKernel.kerK (a / b) := by
  unfold BallKernel.kerK
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  set t : ℝ := (zetaZeroFamily q).im with ht
  have hline : zetaZeroFamily q = 1 / 2 + I * t := by
    have h := line_of_RH hRH q
    apply Complex.ext <;> simp [ht, h]
  have hsq : (Real.sqrt (a * b) : ℂ) = cexp ((Real.log a + Real.log b) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (mul_pos ha0 hb0), Real.log_mul ha0.ne' hb0.ne']
    push_cast
    ring_nf
  unfold BallLattice.cw pw
  rw [hsq, hline, Real.log_div ha0.ne' hb0.ne', map_mul, ← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_add, map_mul, map_div₀, map_pow, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_sub]
  push_cast
  ring

/-- **Under RH, `K` has a curve realization**: `ℓ²` of the zeros, `w_x = (e^{(ρ − ½)²/4} x^ρ)_ρ`, and `ψ_s` multiplying
the coordinate of `ρ` by `s^ρ`. -/
def curveRealization (hRH : RiemannHypothesis) : CurveRealization BallKernel.kerK where
  E := L2
  w := wvR
  ψ := psiL
  similitude s hs x y := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [psiL_apply, psiL_apply, RCLike.inner_apply, RCLike.inner_apply]
    dsimp only
    rw [map_mul]
    have hn2 : ‖pw q s‖ ^ 2 = s := by
      rw [norm_pw_of_rh hRH, ← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (Real.log s / 2) = Real.log s by ring, Real.exp_log hs]
    have h : conj (pw q s) * pw q s = s := by
      rw [Complex.conj_mul']
      exact_mod_cast hn2
    linear_combination (y q * conj (x q)) * h
  comp s t hs ht := by
    refine LinearMap.ext fun x => ?_
    ext q
    rw [LinearMap.comp_apply, psiL_apply, psiL_apply, psiL_apply, ← mul_assoc]
    congr 1
    rw [pw_mul q hs.ne' ht.ne']
  orbit s x hs hx := by
    ext q
    rw [psiL_apply, wvR_apply, wvR_apply, pw_mul q hs.ne' hx.ne']
    ring
  gram a b ha hb := by
    rw [lp.inner_eq_tsum, ← gram_cwR hRH a b ha hb]
    refine tsum_congr fun q => ?_
    rw [wvR_apply, wvR_apply, RCLike.inner_apply]

/-- **The Riemann hypothesis is the existence of a curve realization of `K`.** -/
theorem rh_iff_curveRealization : RiemannHypothesis ↔ Nonempty (CurveRealization BallKernel.kerK) :=
  ⟨fun h => ⟨curveRealization h⟩, fun ⟨C⟩ => rh_of_curveRealization C⟩

/-! ## Continuity, injectivity, and no lattice -/

/-- In a curve realization, `‖w_x‖² = x·k(1)`. -/
lemma norm_sq_w (C : CurveRealization k) {x : ℝ} (hx : 0 < x) : ((‖C.w x‖ ^ 2 : ℝ) : ℂ) = (x : ℂ) * k 1 := by
  have h := C.gram x x hx hx
  rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, Real.sqrt_mul_self hx.le, div_self hx.ne'] at h
  exact_mod_cast h

/-- In a curve realization, `‖w_{ry} − w_y‖² = y((√r − 1)²k(1) − √r(k(r) + k(1/r) − 2k(1)))`. -/
lemma norm_sub_sq (C : CurveRealization k) {r y : ℝ} (hr : 0 < r) (hy : 0 < y) :
    ((‖C.w (r * y) - C.w y‖ ^ 2 : ℝ) : ℂ) =
      (y : ℂ) * (((Real.sqrt r - 1) ^ 2 : ℝ) * k 1 - (Real.sqrt r : ℂ) * (k r + k r⁻¹ - 2 * k 1)) := by
  have ha := mul_pos hr hy
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (C.w (r * y) - C.w y)
  rw [← RCLike.ofReal_pow] at h
  have e : ((‖C.w (r * y) - C.w y‖ ^ 2 : ℝ) : ℂ) = ⟪C.w (r * y) - C.w y, C.w (r * y) - C.w y⟫_ℂ := h.symm
  have h1 : Real.sqrt (r * y * y) = Real.sqrt r * y := by
    rw [mul_assoc, Real.sqrt_mul hr.le, Real.sqrt_mul_self hy.le]
  have h2 : Real.sqrt (y * (r * y)) = Real.sqrt r * y := by rw [mul_comm, h1]
  have hs : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr.le
  rw [e, inner_sub_left, inner_sub_right, inner_sub_right, C.gram _ _ ha ha, C.gram _ _ hy ha, C.gram _ _ ha hy,
    C.gram _ _ hy hy, Real.sqrt_mul_self ha.le, Real.sqrt_mul_self hy.le, div_self ha.ne', div_self hy.ne', h1, h2,
    mul_div_cancel_right₀ _ hy.ne', show y / (r * y) = r⁻¹ by field_simp]
  have hs' : ((Real.sqrt r : ℝ) : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast hs
  push_cast
  linear_combination (-(y : ℂ) * k 1) * hs'

/-- **A curve realization of a kernel smooth at `1` is continuous on `(0, ∞)`.** -/
theorem continuousOn_of_smooth (C : CurveRealization k) {M : ℝ}
    (hk : ∀ r : ℝ, 1 ≤ r → r ≤ 2 → ‖k r + k r⁻¹ - 2 * k 1‖ ≤ M * Real.log r ^ 2) :
    ContinuousOn C.w (Ioi 0) := by
  -- two-sided version of the hypothesis
  have hk2 : ∀ r : ℝ, 1 / 2 ≤ r → r ≤ 2 → ‖k r + k r⁻¹ - 2 * k 1‖ ≤ |M| * Real.log r ^ 2 := by
    intro r h1 h2
    rcases le_total 1 r with h | h
    · exact (hk r h h2).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg _))
    · have hr0 : 0 < r := by linarith
      have hi1 : 1 ≤ r⁻¹ := one_le_inv₀ hr0 |>.2 h
      have hi2 : r⁻¹ ≤ 2 := by rw [inv_le_comm₀ hr0 two_pos]; linarith
      have := hk r⁻¹ hi1 hi2
      rw [inv_inv, Real.log_inv, neg_sq, add_comm (k r⁻¹)] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg _))
  intro y hy
  have hy : 0 < y := hy
  refine ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set g : ℝ → ℝ := fun x => Real.sqrt (y * ((Real.sqrt (x / y) - 1) ^ 2 * ‖k 1‖ +
    Real.sqrt (x / y) * (|M| * Real.log (x / y) ^ 2))) with hg
  have hgc : ContinuousAt g y := by
    have hd : ContinuousAt (fun x : ℝ => x / y) y := continuousAt_id.div_const y
    have hl : ContinuousAt (fun x : ℝ => Real.log (x / y)) y :=
      (Real.continuousAt_log (by rw [div_self hy.ne']; exact one_ne_zero)).comp hd
    have hs : ContinuousAt (fun x : ℝ => Real.sqrt (x / y)) y := Real.continuous_sqrt.continuousAt.comp hd
    exact Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.mul (((hs.sub continuousAt_const).pow 2).mul continuousAt_const |>.add
        (hs.mul (continuousAt_const.mul (hl.pow 2)))))
  have hg0 : g y = 0 := by simp [hg, div_self hy.ne']
  have hlim : Tendsto g (𝓝 y) (𝓝 0) := hg0 ▸ hgc.tendsto
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hlim
  have hnb : Icc (y / 2) (2 * y) ∈ 𝓝 y := Icc_mem_nhds (by linarith) (by linarith)
  filter_upwards [hnb] with x hx
  obtain ⟨hx1, hx2⟩ := hx
  set r := x / y with hrdef
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < r := div_pos hx0 hy
  have hr1 : 1 / 2 ≤ r := by rw [hrdef, le_div_iff₀ hy]; linarith
  have hr2 : r ≤ 2 := by rw [hrdef, div_le_iff₀ hy]; linarith
  have hxr : x = r * y := by rw [hrdef, div_mul_cancel₀ _ hy.ne']
  rw [hxr]
  have e := norm_sub_sq C hr0 hy
  have hsq0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hbound : ‖C.w (r * y) - C.w y‖ ^ 2 ≤
      y * ((Real.sqrt r - 1) ^ 2 * ‖k 1‖ + Real.sqrt r * (|M| * Real.log r ^ 2)) := by
    have hn : ‖C.w (r * y) - C.w y‖ ^ 2 = ‖((‖C.w (r * y) - C.w y‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hn, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy.le]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hy.le
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg hsq0]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hk2 r hr1 hr2) hsq0)
  show ‖C.w (r * y) - C.w y‖ ≤ g (r * y)
  have hrr : r * y / y = r := mul_div_cancel_right₀ _ hy.ne'
  simp only [hg, hrr]
  rw [← Real.sqrt_sq (norm_nonneg (C.w (r * y) - C.w y))]
  exact Real.sqrt_le_sqrt hbound

/-- **Every curve realization of `K` is continuous on `(0, ∞)`.** -/
theorem continuousOn_kerK (C : CurveRealization BallKernel.kerK) : ContinuousOn C.w (Ioi 0) := by
  obtain ⟨M, hM⟩ := kerK_smooth
  exact continuousOn_of_smooth C hM

/-- **In a curve realization of `K` the curve is injective on `(0, ∞)`**, since `‖w_x‖² = x·K(1)` and `K(1) ≠ 0`. -/
theorem injective_kerK (C : CurveRealization BallKernel.kerK) : InjOn C.w (Ioi 0) := by
  intro x hx y hy h
  have hRH := rh_of_curveRealization C
  have h1 := norm_sq_w C (show 0 < x from hx)
  have h2 := norm_sq_w C (show 0 < y from hy)
  rw [h] at h1
  have h3 : ((x : ℂ) - y) * BallKernel.kerK 1 = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact_mod_cast sub_eq_zero.1 h4
  · exact absurd h4 (kerK_one_ne_zero hRH)

/-- **The orbit curve spans no lattice**: at the integers, `w_{n+1} − w_n ≠ 0` and `‖w_{n+1} − w_n‖ → 0`. -/
theorem not_discrete (C : CurveRealization BallKernel.kerK) :
    (∀ n : ℕ, 0 < n → C.w ((n : ℝ) + 1) ≠ C.w n) ∧
      Tendsto (fun n : ℕ => ‖C.w ((n : ℝ) + 1) - C.w n‖) atTop (𝓝 0) := by
  obtain ⟨h1, h2⟩ := BallLattice.not_discrete (toRealization C)
  have e1 : ∀ n : ℕ, ((((n : ℚ) + 1 : ℚ)) : ℝ) = (n : ℝ) + 1 := fun n => by push_cast; rfl
  have e2 : ∀ n : ℕ, (((n : ℚ)) : ℝ) = (n : ℝ) := fun n => Rat.cast_natCast n
  refine ⟨fun n hn => ?_, ?_⟩
  · have := h1 n hn
    simp only [toRealization, e1, e2] at this
    exact this
  · simp only [toRealization, e1, e2] at h2
    exact h2

/-! ## Strong continuity of the flow

For an abstract curve realization, `s ↦ U_s x` need not be continuous off the closed span of the curve: `U_s` is
unconstrained there. (Take `E = ℓ²(zeros) ⊕ ℂ` with `U_s` acting on `ℂ` by a discontinuous character of `ℝ`, which
exists by a Hamel basis.) So continuity is proved on the closed span of the curve, on the whole space when the curve
spans densely, and on the whole of `ℓ²` for the model `curveRealization`. -/

/-- **ε/3**: a family of isometric linear maps that is strongly continuous on a set is strongly continuous on the
closure of its span. -/
theorem continuous_of_mem_closure_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : ℝ → E →ₗ[ℂ] E) (hT : ∀ s x, ‖T s x‖ = ‖x‖) (S : Set E) (hS : ∀ x ∈ S, Continuous fun s => T s x)
    {x : E} (hx : x ∈ closure (Submodule.span ℂ S : Set E)) : Continuous fun s => T s x := by
  have hspan : ∀ y ∈ Submodule.span ℂ S, Continuous fun s => T s y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y h => exact hS y h
    | zero => simpa using (continuous_const : Continuous fun _ : ℝ => (0 : E))
    | add a b _ _ ha hb => simp only [map_add]; exact ha.add hb
    | smul c a _ ha => simp only [map_smul]; exact ha.const_smul c
  rw [Metric.continuous_iff]
  intro s0 ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 3) (by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 (hspan y hy) s0 (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have h1 := hδ' s hs
  rw [dist_eq_norm] at h1 hxy ⊢
  have e : T s x - T s0 x = T s (x - y) + (T s y - T s0 y) + T s0 (y - x) := by
    simp only [map_sub]; abel
  calc ‖T s x - T s0 x‖ ≤ ‖T s (x - y)‖ + ‖T s y - T s0 y‖ + ‖T s0 (y - x)‖ := by rw [e]; exact norm_add₃_le
    _ = ‖x - y‖ + ‖T s y - T s0 y‖ + ‖x - y‖ := by rw [hT, hT, norm_sub_rev y x]
    _ < ε := by linarith

/-- `U_s` is an isometry. -/
theorem norm_U (C : CurveRealization k) (s : ℝ) (x : C.E) : ‖C.U s x‖ = ‖x‖ := by
  have h := flow_inner C s x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖C.U s x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- In a curve realization of `K`, the curve `t ↦ v_t` is continuous. -/
theorem continuous_v_kerK (C : CurveRealization BallKernel.kerK) : Continuous C.v := by
  have hw := continuousOn_kerK C
  have hc : Continuous fun t => C.w (Real.exp t) :=
    hw.comp_continuous Real.continuous_exp fun t => Real.exp_pos t
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_neg.div_const 2))).smul hc

/-- **The flow is strongly continuous on the closed span of the curve.** -/
theorem flow_continuous_closure (C : CurveRealization BallKernel.kerK) {x : C.E}
    (hx : x ∈ closure (Submodule.span ℂ (Set.range C.v) : Set C.E)) : Continuous fun s => C.U s x := by
  refine continuous_of_mem_closure_span C.U (norm_U C) _ ?_ hx
  rintro _ ⟨t, rfl⟩
  have e : (fun s => C.U s (C.v t)) = fun s => C.v (t + s) := funext fun s => (flow_orbit C s t).symm
  rw [e]
  exact (continuous_v_kerK C).comp (continuous_const.add continuous_id)

/-- **If the curve spans densely, the flow is strongly continuous on the whole space.** -/
theorem flow_continuous_of_dense (C : CurveRealization BallKernel.kerK)
    (hd : Dense (Submodule.span ℂ (Set.range C.v) : Set C.E)) (x : C.E) : Continuous fun s => C.U s x :=
  flow_continuous_closure C (hd.closure_eq ▸ Set.mem_univ x)

open scoped Classical in
lemma U_single (hRH : RiemannHypothesis) (q : ZIdx) (s : ℝ) :
    (curveRealization hRH).U s (lp.single 2 q (1 : ℂ) : L2) =
      ((Real.exp (-s / 2) : ℂ) * cexp (zetaZeroFamily q * s)) • (lp.single 2 q (1 : ℂ) : L2) := by
  apply lp.ext
  funext i
  show (Real.exp (-s / 2) : ℂ) * (pw i (Real.exp s) * ((lp.single 2 q (1 : ℂ) : L2) : ZIdx → ℂ) i) = _
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  rcases eq_or_ne i q with rfl | h
  · unfold pw; rw [Real.log_exp]; ring
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero, mul_zero]

open scoped Classical in
/-- **In the model `curveRealization`, the flow is strongly continuous on all of `ℓ²`.** -/
theorem flow_continuous_model (hRH : RiemannHypothesis) (y : L2) :
    Continuous fun s => (curveRealization hRH).U s y := by
  refine continuous_of_mem_closure_span (curveRealization hRH).U (norm_U _)
    (Set.range fun q : ZIdx => ((lp.single 2 q (1 : ℂ) : L2))) ?_ ?_
  · rintro _ ⟨q, rfl⟩
    have e := funext (U_single hRH q)
    rw [e]
    refine Continuous.smul (f := fun s : ℝ => (Real.exp (-s / 2) : ℂ) * cexp (zetaZeroFamily q * s)) ?_
      (continuous_const : Continuous fun _ : ℝ => (lp.single 2 q (1 : ℂ) : L2))
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_neg.div_const 2))).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  · refine mem_closure_of_tendsto (lp.hasSum_single (by norm_num) y) (Eventually.of_forall fun F => ?_)
    refine Submodule.sum_mem _ fun q _ => ?_
    have : (lp.single 2 q (y q) : L2) = y q • (lp.single 2 q (1 : ℂ) : L2) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

end BallCurve

#print axioms BallCurve.rh_iff_curveRealization
#print axioms BallCurve.flow_inner
#print axioms BallCurve.flow_orbit
#print axioms BallCurve.flow_add
#print axioms BallCurve.continuousOn_kerK
#print axioms BallCurve.injective_kerK
#print axioms BallCurve.not_discrete
#print axioms BallCurve.continuous_of_mem_closure_span
#print axioms BallCurve.flow_continuous_closure
#print axioms BallCurve.flow_continuous_of_dense
#print axioms BallCurve.flow_continuous_model
