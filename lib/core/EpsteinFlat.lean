/-
# Flat lattices: the Epstein zeta function of `ℤ ⊕ yℤ` has a zero off its critical line once `y > e²`

Plain statement. For `y > 0` let `Q_y(m, n) = m² + y²n²`, the norm form of the rectangular lattice `ℤ ⊕ yℤ` of
covolume `y`, and `θ_y(t) = Σ_{(m, n) ∈ ℤ²} e^{−πtQ_y(m, n)/y} = θ(t/y)θ(ty)` (`theta`, `hasSum_theta`), for Jacobi's
`θ = evenKernel 0`.
* **The construction of `ℤ²` and `x² + 2y²`.** `θ_y` is self-dual, `θ_y(1/t) = tθ_y(t)` (`theta_inv`), so its
  regularised Mellin transform `Λ_y` (`Lambda`, Mathlib's `WeakFEPair.Λ`) has `Λ_y(1 − s) = Λ_y(s)`
  (`Lambda_one_sub`), is holomorphic off `s = 0, 1` (`differentiableAt_Lambda`), and on `Re s > 1` is the Epstein zeta
  function `π^{−s}Γ(s)Σ_{(m, n) ≠ 0}(Q_y(m, n)/y)^{−s}` (`hasMellin_theta`, `hasSum_Lambda`).
* **Where its RH is `RH ∧ GRH`.** At `y = 1`, `Λ_1(s) = 2Z(2, 2s)`, Lagarias and Rains's function at `w = 2`
  (`Lambda_one`), and RH for it is `RH ∧ GRH(χ₋₄)` (`rh_one_iff`). At `y = √2`, `Λ_{√2}` is the completed Dedekind zeta
  function of `ℚ(√−2)` (`Lambda_sqrt_two`, `EpsteinTwo.LambdaQ_eq`), and RH for it is `RH ∧ GRH(χ₋₈)`
  (`rh_sqrt_two_iff`).
* **On the real axis** (`Lambda_ofReal`): for real `σ`, `Λ_y(σ) = ∫₁^∞ (θ_y(t) − 1)(t^{σ−1} + t^{−σ}) dt − 1/σ −
  1/(1 − σ)`, a real number, from Mathlib's `Λ = Λ₀ − 1/s − 1/(1 − s)` and the self-duality; so `Λ_y(σ) → −∞` as
  `σ → 1⁻` (`tendsto_Lambda_re`).
* **At the centre** (`le_Lambda_half`): `Λ_y(½) ≥ 2√y(log y − 2)` for `y ≥ 1`. The self-duality of `θ` gives
  `θ(x) ≥ x^{−1/2}`, so `θ_y(t) − 1 ≥ √(y/t) − 1` for `1 ≤ t ≤ y`, and `∫₁^y (√y/t − t^{−1/2}) dt = √y(log y − 2) + 2`.
* **A zero off the line** (`exists_zero_off_line`, `not_rh`): for `y > e²`, `Λ_y(½) > 0` and `Λ_y(σ) → −∞` at `1`,
  so `Λ_y` vanishes at a real `σ ∈ (½, 1)` and at `1 − σ`: RH fails for the Epstein zeta function of every rectangular
  lattice with `y > e² ≈ 7.389`, with no hypothesis. The true threshold is near `4πe^{−γ} ≈ 7.0555`: for `y ≥ 1` the
  constant term `y^s ζ̂(2s) + y^{1−s} ζ̂(2s − 1)` of the Eisenstein series has all its zeros on the line but two real
  ones, which exist exactly when `y > 4πe^{−γ}` (J. C. Lagarias and M. Suzuki, J. Number Theory 118 (2006)), and the
  Epstein zeta function differs from it by terms of size `e^{−2πy}` (S. Chowla and A. Selberg, J. reine angew. Math.
  227 (1967)).
* **An arithmetic example** (`exists_zero_fiftyEight`, `not_rh_fiftyEight`): `y = √58`, the form `x² + 58y²` of class
  number `2`. By genus theory (not formalised here) its Epstein zeta function is `ζ(s)L(s, χ₋₂₃₂) + L(s, χ₋₈)L(s, χ₂₉)`,
  a sum of two Euler products; it has a real zero in `(½, 1)`.
So the lattice-point construction that gives `RH ∧ GRH` at `y = 1` and `y = √2` (a self-dual theta function, the
functional equation `s ↦ 1 − s`, poles at `0` and `1`) gives a function with zeros off its line once the lattice is
flat. An argument that uses only the geometry of the lattice and the functional equation cannot prove RH: the Euler
product, which `Λ_1` and `Λ_{√2}` have, must enter.
-/
import Mathlib
import TwoVariableZetaTwo
import EpsteinTwo

open Real Complex Filter Topology Asymptotics Set MeasureTheory HurwitzZeta

noncomputable section

namespace EpsteinFlat

/-! ## The theta function of `ℤ ⊕ yℤ` -/

/-- **The theta function of the rectangular lattice `ℤ ⊕ yℤ`**, `θ_y(t) = θ(t/y)θ(ty)`. -/
def theta (y t : ℝ) : ℝ := evenKernel 0 (t / y) * evenKernel 0 (t * y)

/-- **`θ_y(t) = Σ_{(m, n) ∈ ℤ²} e^{−πt(m² + y²n²)/y}`**. -/
theorem hasSum_theta {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    HasSum (fun p : ℤ × ℤ => rexp (-π * t * ((p.1 : ℝ) ^ 2 + y ^ 2 * (p.2 : ℝ) ^ 2) / y)) (theta y t) :=
  (EpsteinHexagonal.hasSum_prod (div_pos ht hy) (mul_pos ht hy)).congr_fun fun p => by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring

/-- `θ_y(t) ≥ 1`, its term at `(m, n) = 0`. -/
lemma one_le_theta {y t : ℝ} (hy : 0 < y) (ht : 0 < t) : 1 ≤ theta y t :=
  one_le_mul_of_one_le_of_one_le (TwoVariableZeta.one_le_theta (div_pos ht hy))
    (TwoVariableZeta.one_le_theta (mul_pos ht hy))

/-- **`θ_y(1/t) = tθ_y(t)`**: the dual of `ℤ ⊕ yℤ` is `ℤ ⊕ y⁻¹ℤ`, similar to it, and `θ_y` is normalised by the
covolume so that it is self-dual. -/
theorem theta_inv {y t : ℝ} (hy : 0 < y) (ht : 0 < t) : theta y (1 / t) = t * theta y t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hy0 : y ≠ 0 := hy.ne'
  have e1 : 1 / t / y = 1 / (t * y) := by field_simp
  have e2 : 1 / t * y = 1 / (t / y) := by field_simp
  have h : Real.sqrt (t * y) * Real.sqrt (t / y) = t := by
    rw [← Real.sqrt_mul (mul_pos ht hy).le, show t * y * (t / y) = t ^ 2 by field_simp, Real.sqrt_sq ht.le]
  unfold theta
  rw [e1, e2, EpsteinHexagonal.theta_inv (mul_pos ht hy), EpsteinHexagonal.theta_inv (div_pos ht hy)]
  linear_combination (evenKernel 0 (t * y) * evenKernel 0 (t / y)) * h

/-- At `y = 1`, `θ_1 = θ²`, the theta function of `ℤ²`: Lagarias and Rains's `θ^w` at `w = 2`. -/
lemma theta_one (t : ℝ) : ((theta 1 t : ℝ) : ℂ) = TwoVariableZeta.thetaPow 2 t := by
  simp only [theta, div_one, mul_one, TwoVariableZeta.thetaPow, Real.rpow_two, sq]

/-- At `y = √2`, `θ_{√2}` is the theta function of `x² + 2y²` (`EpsteinTwo.thetaQ`). -/
lemma theta_sqrt_two {t : ℝ} (ht : 0 < t) : theta (Real.sqrt 2) t = EpsteinTwo.thetaQ t := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have e : 2 * (t / Real.sqrt 2) = t * Real.sqrt 2 := by
    rw [mul_div_assoc', div_eq_iff hs]
    linear_combination (-t) * h2
  unfold theta EpsteinTwo.thetaQ
  rw [EpsteinTwo.Θ_eq (by positivity), e]

/-- `θ(x) ≥ x^{−1/2}`: the self-duality `θ(x) = x^{−1/2}θ(1/x)` and `θ ≥ 1`. -/
lemma rpow_le_evenKernel {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2 : ℝ)) ≤ evenKernel 0 x := by
  have h := TwoVariableZeta.theta_inv (one_div_pos.2 hx)
  rw [one_div_one_div] at h
  have e : (1 / x) ^ (1 / 2 : ℝ) = x ^ (-(1 / 2 : ℝ)) := by
    rw [one_div x, Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  rw [h, e]
  exact le_mul_of_one_le_right (by positivity) (TwoVariableZeta.one_le_theta (one_div_pos.2 hx))

/-! ## The weak FE-pair -/

lemma continuousOn_theta {y : ℝ} (hy : 0 < y) : ContinuousOn (theta y) (Ioi 0) := by
  have h1 : ContinuousOn (fun t => evenKernel 0 (t / y)) (Ioi 0) :=
    (continuousOn_evenKernel 0).comp (continuous_id.div_const y).continuousOn
      fun t (ht : 0 < t) => show 0 < t / y from div_pos ht hy
  have h2 : ContinuousOn (fun t => evenKernel 0 (t * y)) (Ioi 0) :=
    (continuousOn_evenKernel 0).comp (continuous_id.mul continuous_const).continuousOn
      fun t (ht : 0 < t) => show 0 < t * y from mul_pos ht hy
  exact h1.mul h2

lemma locallyIntegrableOn_theta {y : ℝ} (hy : 0 < y) :
    LocallyIntegrableOn (fun t => (theta y t : ℂ)) (Ioi 0) :=
  (continuous_ofReal.comp_continuousOn (continuousOn_theta hy)).locallyIntegrableOn measurableSet_Ioi

/-- `θ(ct) − 1` decays faster than any power of `t`, for `c > 0`. -/
lemma isBigO_evenKernel_sub {c : ℝ} (hc : 0 < c) (r : ℝ) :
    (fun t => evenKernel 0 (t * c) - 1) =O[atTop] (· ^ r) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub 0
  simp only [ite_true] at hO
  have h : (fun t => evenKernel 0 (t * c) - 1) =O[atTop] fun t => rexp (-(p * c) * t) :=
    ((hO.comp_tendsto (tendsto_id.atTop_mul_const hc)).congr_left fun t => rfl).congr_right fun t => by
      simp only [Function.comp, id]
      ring_nf
  exact h.trans (isLittleO_exp_neg_mul_rpow_atTop (mul_pos hp hc) r).isBigO

/-- `θ_y(t) − 1` decays faster than any power of `t`. -/
lemma isBigO_theta_sub {y : ℝ} (hy : 0 < y) (r : ℝ) :
    (fun t => (theta y t : ℂ) - 1) =O[atTop] (· ^ r) := by
  have hA : (fun t => evenKernel 0 (t / y) - 1) =O[atTop] (· ^ r) := by
    simpa only [div_eq_mul_inv] using isBigO_evenKernel_sub (inv_pos.2 hy) r
  have hB := isBigO_evenKernel_sub hy r
  have hB0 : (fun t => evenKernel 0 (t * y)) =O[atTop] fun _ => (1 : ℝ) := by
    have h1 := (isBigO_evenKernel_sub hy 0).congr_right fun t => Real.rpow_zero t
    exact (h1.add (isBigO_const_const (1 : ℝ) one_ne_zero atTop)).congr_left fun t => by ring
  have hsum : (fun t => theta y t - 1) =O[atTop] (· ^ r) := by
    have h := ((hA.mul hB0).congr_right fun t => mul_one _).add hB
    exact h.congr_left fun t => by unfold theta; ring
  exact (isBigO_ofReal_left.mpr hsum).congr_left fun t => by push_cast; ring

/-- **`θ_y` is a weak FE-pair** of weight `1` and root number `1`, its own dual, with constant term `1` at both
ends. -/
def thetaFEPair (y : ℝ) (hy : 0 < y) : WeakFEPair ℂ where
  f t := (theta y t : ℂ)
  g t := (theta y t : ℂ)
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := locallyIntegrableOn_theta hy
  hg_int := locallyIntegrableOn_theta hy
  hk := one_pos
  hε := one_ne_zero
  h_feq x hx := by
    show ((theta y (1 / x) : ℝ) : ℂ) = ((1 : ℂ) * ((x ^ (1 : ℝ) : ℝ) : ℂ)) • ((theta y x : ℝ) : ℂ)
    rw [theta_inv hy hx, Real.rpow_one, one_mul, smul_eq_mul, ofReal_mul]
  hf_top := isBigO_theta_sub hy
  hg_top := isBigO_theta_sub hy

lemma thetaFEPair_symm {y : ℝ} (hy : 0 < y) : (thetaFEPair y hy).symm = thetaFEPair y hy := by
  unfold thetaFEPair WeakFEPair.symm
  congr 1
  exact inv_one

/-! ## The Epstein zeta function of `ℤ ⊕ yℤ` -/

/-- **The completed Epstein zeta function of `ℤ ⊕ yℤ`**, `Λ_y(s) = ∫₀^∞ θ_y(t)t^s dt/t` regularised: Mathlib's
`WeakFEPair.Λ` for `θ_y`. -/
def Lambda (y : ℝ) (hy : 0 < y) (s : ℂ) : ℂ := (thetaFEPair y hy).Λ s

/-- **The functional equation** `Λ_y(1 − s) = Λ_y(s)`. -/
theorem Lambda_one_sub {y : ℝ} (hy : 0 < y) (s : ℂ) : Lambda y hy (1 - s) = Lambda y hy s := by
  have h := (thetaFEPair y hy).functional_equation s
  rw [thetaFEPair_symm] at h
  have hk : (((thetaFEPair y hy).k : ℝ) : ℂ) = 1 := by simp [thetaFEPair]
  unfold Lambda
  rw [← hk, h]
  simp [thetaFEPair]

/-- `Λ_y` is holomorphic away from its poles `s = 0` and `s = 1`. -/
theorem differentiableAt_Lambda {y : ℝ} (hy : 0 < y) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (Lambda y hy) s :=
  (thetaFEPair y hy).differentiableAt_Λ (Or.inl h0) (Or.inl (by simpa [thetaFEPair] using h1))

/-- **On `Re s > 1`, `Λ_y(s)` is the Mellin transform** `∫₀^∞ (θ_y(t) − 1)t^s dt/t`. -/
theorem hasMellin_theta {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t => (theta y t : ℂ) - 1) s (Lambda y hy s) :=
  (thetaFEPair y hy).hasMellin (by simpa [thetaFEPair] using hs)

/-- `Q_y(m, n)/y = (m² + y²n²)/y` vanishes only at `(0, 0)`. -/
lemma qy_eq_zero_iff {y : ℝ} (hy : 0 < y) (p : ℤ × ℤ) :
    ((p.1 : ℝ) ^ 2 + y ^ 2 * (p.2 : ℝ) ^ 2) / y = 0 ↔ p = 0 := by
  constructor
  · intro h
    have h' : (p.1 : ℝ) ^ 2 + y ^ 2 * (p.2 : ℝ) ^ 2 = 0 := by
      rcases div_eq_zero_iff.1 h with h | h
      · exact h
      · exact absurd h hy.ne'
    have h0 : 0 ≤ y ^ 2 * (p.2 : ℝ) ^ 2 := by positivity
    have hm : (p.1 : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 : ℝ)]
    have hn : y ^ 2 * (p.2 : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 : ℝ)]
    have hy2 : y ^ 2 ≠ 0 := by positivity
    have h1 : p.1 = 0 := by exact_mod_cast pow_eq_zero_iff (two_ne_zero) |>.1 hm
    have h2 : p.2 = 0 := by
      have := (mul_eq_zero.1 hn).resolve_left hy2
      exact_mod_cast pow_eq_zero_iff (two_ne_zero) |>.1 this
    exact Prod.ext h1 h2
  · rintro rfl
    simp

/-- `Σ_{(m, n) ≠ 0} (Q_y(m, n)/y)^{−σ}` converges for `σ > 1`: `Q_y(m, n)/y ≥ c·max(|m|, |n|)²`, and Mathlib's
`EisensteinSeries.summable_one_div_norm_rpow`. -/
lemma summable_qy {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : ℤ × ℤ => ‖(1 : ℂ)‖ / (((p.1 : ℝ) ^ 2 + y ^ 2 * (p.2 : ℝ) ^ 2) / y) ^ σ := by
  set c : ℝ := min 1 (y ^ 2) / y with hc
  have hmin0 : 0 < min 1 (y ^ 2) := lt_min one_pos (by positivity)
  have hc0 : 0 < c := div_pos hmin0 hy
  have hS : Summable fun p : ℤ × ℤ => ‖(finTwoArrowEquiv ℤ).symm p‖ ^ (-(2 * σ)) :=
    (finTwoArrowEquiv ℤ).symm.summable_iff.2 (EisensteinSeries.summable_one_div_norm_rpow (by linarith))
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hS.mul_left (c ^ (-σ)))
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [Prod.fst_zero, Prod.snd_zero, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero, zero_div, Real.zero_rpow (by linarith : σ ≠ 0), div_zero]
    positivity
  obtain ⟨m, n⟩ := p
  set N : ℝ := ‖(finTwoArrowEquiv ℤ).symm (m, n)‖ with hN
  have habs : ∀ k : ℤ, ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := fun k => by rw [Nat.cast_natAbs, Int.cast_abs]
  have hN' : N = max |(m : ℝ)| |(n : ℝ)| := by
    rw [hN, EisensteinSeries.norm_eq_max_natAbs]
    simp [habs]
  have hN1 : 1 ≤ N := by
    rw [hN']
    rcases eq_or_ne m 0 with hm | hm
    · have hn : n ≠ 0 := fun hn => hp (by rw [hm, hn]; rfl)
      exact le_max_of_le_right (by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hn)
    · exact le_max_of_le_left (by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hm)
  have hNsq : N ^ 2 ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    rw [hN']
    rcases le_total |(m : ℝ)| |(n : ℝ)| with h | h
    · rw [max_eq_right h, sq_abs]
      nlinarith [sq_nonneg (m : ℝ)]
    · rw [max_eq_left h, sq_abs]
      nlinarith [sq_nonneg (n : ℝ)]
  have hQ : c * N ^ 2 ≤ ((m : ℝ) ^ 2 + y ^ 2 * (n : ℝ) ^ 2) / y := by
    have hm1 : min 1 (y ^ 2) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (y ^ 2) ≤ y ^ 2 := min_le_right _ _
    rw [hc, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hy.le
    nlinarith [mul_le_mul_of_nonneg_left hNsq hmin0.le, mul_le_mul_of_nonneg_right hm1 (sq_nonneg (m : ℝ)),
      mul_le_mul_of_nonneg_right hm2 (sq_nonneg (n : ℝ))]
  have hpos : 0 < c * N ^ 2 := by positivity
  have hN0 : 0 ≤ N := by linarith
  calc ‖(1 : ℂ)‖ / (((m : ℝ) ^ 2 + y ^ 2 * (n : ℝ) ^ 2) / y) ^ σ
        ≤ 1 / (c * N ^ 2) ^ σ := by
          rw [norm_one]
          exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hpos σ)
            (Real.rpow_le_rpow hpos.le hQ (by linarith))
    _ = c ^ (-σ) * N ^ (-(2 * σ)) := by
          rw [Real.mul_rpow hc0.le (by positivity), ← Real.rpow_natCast N 2, ← Real.rpow_mul hN0,
            Real.rpow_neg hc0.le, Real.rpow_neg hN0]
          push_cast
          field_simp

/-- **On `Re s > 1`, `Λ_y(s) = π^{−s}Γ(s)Σ_{(m, n) ≠ 0}(Q_y(m, n)/y)^{−s}`**: `Λ_y` is the completed Epstein zeta
function of `ℤ ⊕ yℤ`. The term at `(0, 0)` is `0`, Lean's `1/0`. -/
theorem hasSum_Lambda {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : ℤ × ℤ => (π : ℂ) ^ (-s) * Gamma s /
      ((((p.1 : ℝ) ^ 2 + y ^ 2 * (p.2 : ℝ) ^ 2) / y : ℝ) : ℂ) ^ s) (Lambda y hy s) := by
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun p : ℤ × ℤ => if ((p.1 : ℝ) ^ 2 + y ^ 2 * (p.2 : ℝ) ^ 2) / y = 0 then 0
      else (1 : ℂ) * rexp (-π * (((p.1 : ℝ) ^ 2 + y ^ 2 * (p.2 : ℝ) ^ 2) / y) * t)) ((theta y t : ℂ) - 1) := by
    intro t (ht : 0 < t)
    have h := (hasSum_ofReal.2 (hasSum_theta hy ht)).update 0 0
    convert h using 1
    · funext p
      rcases eq_or_ne p 0 with rfl | hp
      · simp
      · rw [Function.update_of_ne hp, ite_eq_right ((qy_eq_zero_iff hy p).not.2 hp), one_mul]
        congr 2
        ring
    · simp
      ring
  have h := hasSum_mellin_pi_mul₀ (fun p => by positivity) (by linarith) hF (summable_qy hy hs)
  rw [(hasMellin_theta hy hs).2] at h
  simpa using h

/-! ## `y = 1` and `y = √2` -/

lemma thetaFEPair_one : thetaFEPair 1 one_pos = TwoVariableZeta.thetaPowFEPair 2 two_pos := by
  unfold thetaFEPair TwoVariableZeta.thetaPowFEPair
  congr 1
  · funext t
    exact theta_one t
  · funext t
    exact theta_one t
  · norm_num

/-- **At `y = 1`, `Λ_1(s) = 2Z(2, 2s)`**, for Lagarias and Rains's `Z(2, ·)` (`TwoVariableZeta.Z`). -/
theorem Lambda_one (s : ℂ) : Lambda 1 one_pos s = 2 * TwoVariableZeta.Z 2 two_pos (2 * s) := by
  unfold Lambda TwoVariableZeta.Z
  rw [thetaFEPair_one, show 2 * s / 2 = s by ring]
  ring

/-- Two weak FE-pairs with the same constants and the same `f` on `(0, ∞)` have the same `Λ`. -/
lemma Λ_congr {P Q : WeakFEPair ℂ} (hf : ∀ t : ℝ, 0 < t → P.f t = Q.f t) (hk : P.k = Q.k) (hε : P.ε = Q.ε)
    (hf₀ : P.f₀ = Q.f₀) (hg₀ : P.g₀ = Q.g₀) : P.Λ = Q.Λ := by
  funext s
  have h0 : P.Λ₀ s = Q.Λ₀ s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator, hf t ht, hk, hε, hf₀, hg₀]
  simp only [WeakFEPair.Λ, h0, hk, hε, hf₀, hg₀]

/-- **At `y = √2`, `Λ_{√2}` is the completed Epstein zeta function of `x² + 2y²`** (`EpsteinTwo.LambdaQ`), the
completed Dedekind zeta function of `ℚ(√−2)` (`EpsteinTwo.LambdaQ_eq`). -/
theorem Lambda_sqrt_two : Lambda (Real.sqrt 2) (by positivity) = EpsteinTwo.LambdaQ :=
  Λ_congr (fun t ht => by simp only [thetaFEPair, EpsteinTwo.thetaFEPair, theta_sqrt_two ht])
    (by simp [thetaFEPair, EpsteinTwo.thetaFEPair]) (by simp [thetaFEPair, EpsteinTwo.thetaFEPair])
    (by simp [thetaFEPair, EpsteinTwo.thetaFEPair]) (by simp [thetaFEPair, EpsteinTwo.thetaFEPair])

/-- **The Riemann hypothesis for a function `Λ`** with the functional equation `s ↦ 1 − s`: its zeros in the strip
`0 < Re s < 1` lie on `Re s = ½`. -/
def RHFor (L : ℂ → ℂ) : Prop := ∀ s : ℂ, 0 < s.re → s.re < 1 → L s = 0 → s.re = 1 / 2

/-- **At `y = 1`, RH for `Λ_1` is RH for `ζ` and GRH for `χ₋₄`** (`TwoVariableZetaTwo.rh_two_iff`). -/
theorem rh_one_iff : RHFor (Lambda 1 one_pos) ↔ RiemannHypothesis ∧ PsiOmega.GRH PsiOmega.chi4 := by
  rw [← TwoVariableZetaTwo.rh_two_iff]
  constructor
  · intro h u h0 h1 hz
    have hz' : Lambda 1 one_pos (u / 2) = 0 := by
      rw [Lambda_one, show 2 * (u / 2) = u by ring, hz, mul_zero]
    have := h (u / 2) (by simp; linarith) (by simp; linarith) hz'
    simp at this
    linarith
  · intro h s h0 h1 hz
    have hz' : TwoVariableZeta.Z 2 two_pos (2 * s) = 0 := by
      rw [Lambda_one] at hz
      simpa using hz
    have := h (2 * s) (by simp; linarith) (by simp; linarith) hz'
    simp at this
    linarith

/-- **At `y = √2`, RH for `Λ_{√2}` is RH for `ζ` and GRH for `χ₋₈`** (`EpsteinTwo.rh_iff`). -/
theorem rh_sqrt_two_iff :
    RHFor (Lambda (Real.sqrt 2) (by positivity)) ↔ RiemannHypothesis ∧ PsiOmega.GRH PsiOmega.chi8 := by
  rw [Lambda_sqrt_two]
  exact EpsteinTwo.rh_iff

/-! ## On the real axis -/

/-- `1_{t > 1}(θ_y(t) − 1)`, the part of `θ_y − 1` beyond `1`. -/
def tail (y : ℝ) : ℝ → ℂ := (Ioi 1).indicator fun t => (theta y t : ℂ) - 1

/-- `∫₁^∞ t^{σ−1}(θ_y(t) − 1) dt`. -/
def tailInt (y σ : ℝ) : ℝ := ∫ t in Ioi 1, t ^ (σ - 1) * (theta y t - 1)

/-- Mathlib's `f_modif` for `θ_y` is the tail plus its image under `t ↦ 1/t`: the self-duality. -/
lemma f_modif_eq {y : ℝ} (hy : 0 < y) {t : ℝ} (ht : 0 < t) :
    (thetaFEPair y hy).f_modif t = tail y t + (t : ℂ) ^ (-1 : ℂ) • tail y t⁻¹ := by
  simp only [WeakFEPair.f_modif, thetaFEPair, tail, Pi.add_apply]
  rcases lt_trichotomy 1 t with h | rfl | h
  · have h' : t⁻¹ ∉ Ioi (1 : ℝ) := notMem_Ioi.2 (inv_le_one_of_one_le₀ h.le)
    simp only [indicator_of_mem (mem_Ioi.2 h), indicator_of_notMem (notMem_Ioo_of_ge h.le),
      indicator_of_notMem h']
    simp
  · simp
  · have h1 : t ∉ Ioi (1 : ℝ) := notMem_Ioi.2 h.le
    have h2 : t⁻¹ ∈ Ioi (1 : ℝ) := mem_Ioi.2 ((one_lt_inv₀ ht).2 h)
    simp only [indicator_of_notMem h1, indicator_of_mem (mem_Ioo.2 ⟨ht, h⟩), indicator_of_mem h2]
    have hinv := theta_inv hy ht
    rw [one_div] at hinv
    rw [hinv, Real.rpow_neg_one, Complex.cpow_neg_one, smul_eq_mul, smul_eq_mul]
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    push_cast
    field_simp

lemma tail_eq_indicator {y : ℝ} (hy : 0 < y) : tail y = (Ioi 1).indicator (thetaFEPair y hy).f_modif := by
  funext t
  by_cases h : t ∈ Ioi (1 : ℝ)
  · rw [tail, indicator_of_mem h, indicator_of_mem h, WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem h,
      indicator_of_notMem (notMem_Ioo_of_ge (le_of_lt h)), add_zero]
    rfl
  · rw [tail, indicator_of_notMem h, indicator_of_notMem h]

/-- The tail's Mellin transform converges everywhere. -/
lemma mellinConvergent_tail {y : ℝ} (hy : 0 < y) (s : ℂ) : MellinConvergent (tail y) s := by
  have hF : MellinConvergent (thetaFEPair y hy).f_modif s :=
    ((thetaFEPair y hy).isStrongFEPair_toStrongFEPair.hasMellin s).1
  rw [tail_eq_indicator hy]
  unfold MellinConvergent at hF ⊢
  have h2 : IntegrableOn ((Ioi (1 : ℝ)).indicator fun t => (t : ℂ) ^ (s - 1) • (thetaFEPair y hy).f_modif t)
      (Ioi 0) := hF.indicator measurableSet_Ioi
  refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Set.indicator]
  split_ifs <;> simp

/-- **`Λ₀(s) = M(s) + M(1 − s)`**, for the tail's Mellin transform `M`. -/
lemma Λ₀_eq {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (thetaFEPair y hy).Λ₀ s = mellin (tail y) s + mellin (tail y) (1 - s) := by
  have hG := mellinConvergent_tail hy s
  have hF : MellinConvergent (thetaFEPair y hy).f_modif s :=
    ((thetaFEPair y hy).isStrongFEPair_toStrongFEPair.hasMellin s).1
  set H : ℝ → ℂ := fun t => (t : ℂ) ^ (-1 : ℂ) • tail y t⁻¹ with hH
  have hHc : MellinConvergent H s := by
    refine (hF.sub hG).congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hH, f_modif_eq hy ht, smul_add, add_sub_cancel_left]
  have e : mellin (thetaFEPair y hy).f_modif s = mellin (fun t => tail y t + H t) s :=
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => by rw [f_modif_eq hy ht]
  unfold WeakFEPair.Λ₀
  rw [e]
  have hadd : mellin (fun t => tail y t + H t) s = mellin (tail y) s + mellin H s := by
    unfold mellin
    simp_rw [smul_add]
    exact integral_add hG hHc
  rw [hadd, hH, mellin_cpow_smul, mellin_comp_inv]
  congr 2
  ring

/-- The tail's Mellin transform at real `σ` is real. -/
lemma tail_smul_eq {y σ t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ ((σ : ℂ) - 1) • tail y t = (((Ioi 1).indicator (fun t => t ^ (σ - 1) * (theta y t - 1)) t : ℝ) : ℂ) := by
  by_cases h : t ∈ Ioi (1 : ℝ)
  · rw [tail, indicator_of_mem h, indicator_of_mem h, smul_eq_mul, ofReal_mul,
      ofReal_cpow ht.le, ofReal_sub, ofReal_one]
    push_cast
    ring
  · rw [tail, indicator_of_notMem h, indicator_of_notMem h]
    simp

lemma mellin_tail_ofReal {y : ℝ} (σ : ℝ) : mellin (tail y) σ = (tailInt y σ : ℂ) := by
  unfold mellin tailInt
  rw [setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => tail_smul_eq (y := y) (σ := σ) ht,
    integral_complex_ofReal, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.2 (Ioi_subset_Ioi zero_le_one)]

/-- **`Λ_y` on the real axis**: `Λ_y(σ) = ∫₁^∞ (θ_y(t) − 1)(t^{σ−1} + t^{−σ}) dt − 1/σ − 1/(1 − σ)`, a real number. -/
theorem Lambda_ofReal {y : ℝ} (hy : 0 < y) (σ : ℝ) :
    Lambda y hy σ = ((tailInt y σ + tailInt y (1 - σ) - 1 / σ - 1 / (1 - σ) : ℝ) : ℂ) := by
  have e : (1 : ℂ) - σ = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
  unfold Lambda WeakFEPair.Λ
  rw [Λ₀_eq hy, e, mellin_tail_ofReal, mellin_tail_ofReal]
  simp only [thetaFEPair, smul_eq_mul, mul_one]
  push_cast
  ring

/-- `Λ_y(σ) = Re Λ₀(σ) − 1/σ − 1/(1 − σ)` on the real axis. -/
lemma Lambda_re {y : ℝ} (hy : 0 < y) (σ : ℝ) :
    (Lambda y hy σ).re = ((thetaFEPair y hy).Λ₀ σ).re - 1 / σ - 1 / (1 - σ) := by
  have e : (1 : ℂ) - σ = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
  have h0 : (thetaFEPair y hy).Λ₀ σ = ((tailInt y σ + tailInt y (1 - σ) : ℝ) : ℂ) := by
    rw [Λ₀_eq hy, e, mellin_tail_ofReal, mellin_tail_ofReal]
    push_cast
    ring
  rw [Lambda_ofReal hy, h0, ofReal_re, ofReal_re]

/-- **`Λ_y(σ) → −∞` as `σ → 1⁻`**: its pole at `1` has residue `−1`. -/
theorem tendsto_Lambda_re {y : ℝ} (hy : 0 < y) :
    Tendsto (fun σ : ℝ => (Lambda y hy σ).re) (𝓝[<] 1) atBot := by
  set f : ℝ → ℝ := fun σ => ((thetaFEPair y hy).Λ₀ σ).re - 1 / σ with hf
  have hc : ContinuousAt f 1 := by
    have hΛ := (thetaFEPair y hy).differentiable_Λ₀.continuous
    exact (continuous_re.comp (hΛ.comp continuous_ofReal)).continuousAt.sub
      (continuousAt_const.div continuousAt_id one_ne_zero)
  have h1 : Tendsto (fun σ : ℝ => 1 - σ) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun σ : ℝ => 1 - σ) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ (hσ : σ < 1)
      exact mem_Ioi.2 (by linarith)
  have h2 : Tendsto (fun σ : ℝ => -(1 / (1 - σ))) (𝓝[<] 1) atBot := by
    have h := tendsto_inv_nhdsGT_zero.comp h1
    exact tendsto_neg_atTop_atBot.comp (by simpa only [Function.comp_def, one_div] using h)
  have h3 : ∀ᶠ σ in 𝓝[<] (1 : ℝ), f σ ≤ f 1 + 1 :=
    (hc.tendsto.mono_left nhdsWithin_le_nhds).eventually (eventually_le_nhds (by linarith))
  refine (tendsto_atBot_add_left_of_ge' _ (f 1 + 1) h3 h2).congr fun σ => ?_
  rw [Lambda_re hy σ, hf]
  ring

/-- `t^{σ−1}(θ_y(t) − 1)` is integrable on `(1, ∞)`. -/
lemma integrableOn_tail {y : ℝ} (hy : 0 < y) (σ : ℝ) :
    IntegrableOn (fun t => t ^ (σ - 1) * (theta y t - 1)) (Ioi 1) := by
  have h := mellinConvergent_tail hy σ
  unfold MellinConvergent at h
  have h' : IntegrableOn (fun t => (((Ioi 1).indicator (fun t => t ^ (σ - 1) * (theta y t - 1)) t : ℝ) : ℂ))
      (Ioi 0) := h.congr_fun (fun t (ht : 0 < t) => tail_smul_eq ht) measurableSet_Ioi
  have h'' : IntegrableOn ((Ioi 1).indicator fun t => t ^ (σ - 1) * (theta y t - 1)) (Ioi 0) := by
    simpa using h'.re
  have h3 := (integrable_indicator_iff measurableSet_Ioi).1 h''
  rwa [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.2 (Ioi_subset_Ioi zero_le_one)] at h3

/-- **`∫₁^∞ t^{−1/2}(θ_y(t) − 1) dt ≥ √y(log y − 2) + 2`** for `y ≥ 1`: on `1 ≤ t ≤ y`,
`θ_y(t) − 1 ≥ θ(t/y) − 1 ≥ √(y/t) − 1`. -/
lemma le_tailInt_half {y : ℝ} (hy : 1 ≤ y) :
    Real.sqrt y * Real.log y - 2 * Real.sqrt y + 2 ≤ tailInt y (1 / 2) := by
  have hy0 : 0 < y := by linarith
  have hint := integrableOn_tail hy0 (1 / 2)
  have e : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  rw [e] at hint
  unfold tailInt
  rw [e]
  set g : ℝ → ℝ := fun t => Real.sqrt y * t⁻¹ - t ^ (-(1 / 2 : ℝ)) with hg
  have hcont : ContinuousOn g (Icc 1 y) := by
    have hne : ∀ t ∈ Icc (1 : ℝ) y, t ≠ 0 := fun t ht => (lt_of_lt_of_le one_pos ht.1).ne'
    exact (continuousOn_const.mul (continuousOn_inv₀.mono fun t ht => hne t ht)).sub
      (continuousOn_id.rpow_const fun t ht => Or.inl (hne t ht))
  have hgi : IntegrableOn g (Ioc 1 y) := hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hle : ∀ t ∈ Ioc (1 : ℝ) y, g t ≤ t ^ (-(1 / 2 : ℝ)) * (theta y t - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht.1
    have h1 : evenKernel 0 (t / y) ≤ theta y t :=
      le_mul_of_one_le_right (by linarith [TwoVariableZeta.one_le_theta (div_pos ht0 hy0)])
        (TwoVariableZeta.one_le_theta (mul_pos ht0 hy0))
    have h2 := rpow_le_evenKernel (div_pos ht0 hy0)
    have e2 : t ^ (-(1 / 2 : ℝ)) * (t / y) ^ (-(1 / 2 : ℝ)) = Real.sqrt y * t⁻¹ := by
      rw [Real.div_rpow ht0.le hy0.le, Real.rpow_neg ht0.le, Real.rpow_neg hy0.le, ← Real.sqrt_eq_rpow,
        ← Real.sqrt_eq_rpow]
      have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
      have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht0).ne'
      have hy' : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy0).ne'
      field_simp
      linear_combination (-1 : ℝ) * Real.sq_sqrt ht0.le
    have hpos : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
    calc g t = t ^ (-(1 / 2 : ℝ)) * ((t / y) ^ (-(1 / 2 : ℝ)) - 1) := by
          rw [hg, mul_sub, e2, mul_one]
      _ ≤ t ^ (-(1 / 2 : ℝ)) * (theta y t - 1) := mul_le_mul_of_nonneg_left (by linarith) hpos
  have h1 : ∫ t in Ioc 1 y, g t ≤ ∫ t in Ioc 1 y, t ^ (-(1 / 2 : ℝ)) * (theta y t - 1) :=
    setIntegral_mono_on hgi (hint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hle
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 1)] fun t => t ^ (-(1 / 2 : ℝ)) * (theta y t - 1) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 1 < t) => ?_)
    have ht0 : 0 < t := lt_trans one_pos ht
    exact mul_nonneg (Real.rpow_nonneg ht0.le _) (by linarith [one_le_theta hy0 ht0])
  have h2 : ∫ t in Ioc 1 y, t ^ (-(1 / 2 : ℝ)) * (theta y t - 1) ≤
      ∫ t in Ioi 1, t ^ (-(1 / 2 : ℝ)) * (theta y t - 1) :=
    setIntegral_mono_set hint hnn Ioc_subset_Ioi_self.eventuallyLE
  have h3 : ∫ t in Ioc 1 y, g t = Real.sqrt y * Real.log y - 2 * Real.sqrt y + 2 := by
    have hi1 : IntervalIntegrable (fun t : ℝ => Real.sqrt y * t⁻¹) volume 1 y :=
      (continuousOn_const.mul (continuousOn_inv₀.mono fun t ht =>
        (lt_of_lt_of_le one_pos (by simpa [hy] using ht.1)).ne')).intervalIntegrable
    have hi2 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 1 y :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    rw [← intervalIntegral.integral_of_le hy, hg, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos hy0, integral_rpow (Or.inl (by norm_num)),
      div_one, Real.one_rpow, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    ring
  linarith

/-- **`Λ_y(½) ≥ 2√y(log y − 2)`** for `y ≥ 1`. -/
theorem le_Lambda_half {y : ℝ} (hy : 1 ≤ y) :
    2 * Real.sqrt y * (Real.log y - 2) ≤ (Lambda y (by linarith) (1 / 2)).re := by
  have h := le_tailInt_half hy
  have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [← e, Lambda_ofReal, ofReal_re, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  linarith

/-- `e² < 15/2`. -/
lemma exp_two_lt : Real.exp 2 < 15 / 2 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
  rw [e]
  nlinarith

/-- **A zero off the critical line**: for `y > e²`, `Λ_y` vanishes at a real `σ ∈ (½, 1)` and at `1 − σ`, with no
hypothesis. -/
theorem exists_zero_off_line {y : ℝ} (hy : Real.exp 2 < y) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ Lambda y (lt_trans (Real.exp_pos 2) hy) σ = 0 ∧
      Lambda y (lt_trans (Real.exp_pos 2) hy) (1 - σ) = 0 := by
  have hy0 : 0 < y := lt_trans (Real.exp_pos 2) hy
  have hy1 : 1 ≤ y := by linarith [Real.add_one_le_exp 2]
  set F : ℝ → ℝ := fun σ => (Lambda y hy0 σ).re with hF
  have hreal : ∀ σ : ℝ, Lambda y hy0 σ = (F σ : ℂ) := fun σ => by
    rw [hF]
    simp only
    rw [Lambda_ofReal hy0, ofReal_re]
  have hpos : 0 < F (1 / 2) := by
    have h := le_Lambda_half hy1
    have hlog : 2 < Real.log y := (Real.lt_log_iff_exp_lt hy0).2 hy
    have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
    have h' : 0 < 2 * Real.sqrt y * (Real.log y - 2) := by
      have : 0 < Real.log y - 2 := by linarith
      positivity
    have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
    simp only [hF, e]
    linarith
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ℝ, F σ₁ < 0 ∧ 1 / 2 < σ₁ ∧ σ₁ < 1 := by
    have h1 := (tendsto_Lambda_re hy0).eventually (eventually_lt_atBot 0)
    have h2 : ∀ᶠ σ in 𝓝[<] (1 : ℝ), 1 / 2 < σ ∧ σ < 1 := by
      have ha : ∀ᶠ σ in 𝓝[<] (1 : ℝ), 1 / 2 < σ :=
        nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
      exact ha.and self_mem_nhdsWithin
    exact (h1.and h2).exists
  obtain ⟨hF1, hσ₁a, hσ₁b⟩ := hσ₁
  have hcont : ContinuousOn F (Icc (1 / 2) σ₁) := fun σ hσ => by
    have h0 : (σ : ℂ) ≠ 0 := ofReal_ne_zero.2 (by linarith [hσ.1])
    have h1 : (σ : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith [hσ.2]
    exact (continuous_re.continuousAt.comp ((differentiableAt_Lambda hy0 h0 h1).continuousAt.comp
      continuous_ofReal.continuousAt)).continuousWithinAt
  obtain ⟨σ₀, hσ₀, hF0⟩ := intermediate_value_Icc' hσ₁a.le hcont ⟨hF1.le, hpos.le⟩
  have hne : σ₀ ≠ 1 / 2 := fun h => by
    rw [h] at hF0
    linarith
  have hz : Lambda y hy0 σ₀ = 0 := by rw [hreal, hF0, ofReal_zero]
  refine ⟨σ₀, lt_of_le_of_ne hσ₀.1 (Ne.symm hne), lt_of_le_of_lt hσ₀.2 hσ₁b, hz, ?_⟩
  rw [Lambda_one_sub, hz]

/-- **RH fails for the Epstein zeta function of `ℤ ⊕ yℤ` when `y > e²`.** -/
theorem not_rh {y : ℝ} (hy : Real.exp 2 < y) : ¬ RHFor (Lambda y (lt_trans (Real.exp_pos 2) hy)) := by
  intro h
  obtain ⟨σ, h1, h2, h3, -⟩ := exists_zero_off_line hy
  have := h σ (by simp; linarith) (by simp; linarith) h3
  simp at this
  linarith

lemma exp_two_lt_sqrt_fiftyEight : Real.exp 2 < Real.sqrt 58 :=
  lt_trans exp_two_lt ((Real.lt_sqrt (by norm_num)).2 (by norm_num))

/-- **`x² + 58y²`**, of class number `2` (`y = √58`): its Epstein zeta function has a real zero in `(½, 1)`. -/
theorem exists_zero_fiftyEight :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧ Lambda (Real.sqrt 58) (by positivity) σ = 0 :=
  let ⟨σ, h1, h2, h3, _⟩ := exists_zero_off_line exp_two_lt_sqrt_fiftyEight
  ⟨σ, h1, h2, h3⟩

/-- **RH fails for `x² + 58y²`.** -/
theorem not_rh_fiftyEight : ¬ RHFor (Lambda (Real.sqrt 58) (by positivity)) :=
  not_rh exp_two_lt_sqrt_fiftyEight

end EpsteinFlat

#print axioms EpsteinFlat.hasSum_theta
#print axioms EpsteinFlat.theta_inv
#print axioms EpsteinFlat.Lambda_one_sub
#print axioms EpsteinFlat.differentiableAt_Lambda
#print axioms EpsteinFlat.hasMellin_theta
#print axioms EpsteinFlat.hasSum_Lambda
#print axioms EpsteinFlat.Lambda_one
#print axioms EpsteinFlat.Lambda_sqrt_two
#print axioms EpsteinFlat.rh_one_iff
#print axioms EpsteinFlat.rh_sqrt_two_iff
#print axioms EpsteinFlat.Lambda_ofReal
#print axioms EpsteinFlat.tendsto_Lambda_re
#print axioms EpsteinFlat.le_Lambda_half
#print axioms EpsteinFlat.exists_zero_off_line
#print axioms EpsteinFlat.not_rh
#print axioms EpsteinFlat.exists_zero_fiftyEight
#print axioms EpsteinFlat.not_rh_fiftyEight
