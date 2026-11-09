/-
# The integral quaternions: zeros on the line do not rescue positivity

Plain statement. The Dirichlet series of the integral quaternions of each norm is `(1 − 4^{1−s})ζ(s)ζ(s − 1)`, an eighth
of `Σ r₄(n)n^{−s}` (`FourSquareTeeth.lseries_r4`): the zeta function of `ℙ¹` over `ℤ` with its Euler factor at `2`
changed. Completed with `ζ̂`, `ξ_Q(s) = (1 − 4^{1−s})ζ̂(s)ζ̂(s − 1)` (`xiQ`) vanishes at the zeros `ρ` and `ρ + 1` of
`ℙ¹` (`PurityRational.xiP1_zP1`) and also at `s = 1 + πik/log 2`, `k ≠ 0`, the zeros of `1 − 4^{1−s}`, which lie on the
line `Re s = 1` (`xiQ_poleQ`). Build the kernel over all of them as `PurityRational.kerP1` is built: `K_Q(r) = Σ_{ρ'}
r^{ρ' − 1}/(ρ'(2 − ρ'))` (`kerQ`). Each new zero on the line adds a positive-definite term `r^{iπk/log 2}/(1 + (πk/log
2)²)`, and still `K_Q` is not positive-definite on the positive rationals (`not_posDef_quaternion`), with no hypothesis:
the zeros `ρ` with `0 < Re ρ < 1` stay off the line. This is the counterpart of the numerics of `scripts/ball_orbit.py
--purity`, which find the quaternion orbit form indefinite from `N = 17`.
* The argument is the Landau argument of `BallKernel.re_eq_zero_of_dense` for any countable family of poles with an
  even weight that has no zero on `Re p > 0`: one pole off the imaginary axis is enough (`not_posDef_of_re_ne`).
-/
import Mathlib
import PurityRational

open Real Complex Finset Filter Topology WeilForm WeilTest
open scoped ComplexOrder

noncomputable section

namespace PurityQuaternion

open BallKernel PurityRational

/-! ## The Landau argument for any family of poles -/

/-- **One pole off the axis forbids positivity**: for poles `P` with twin data and an even weight `G` without zeros on
`Re p > 0`, if some `Re P_q ≠ 0` the kernel `Σ_q G(P_q)e^{(log r)P_q}` is not positive-definite on the positive
rationals. -/
theorem not_posDef_of_re_ne {ι : Type*} [Countable ι] {P : ι → ℂ} {G : ℂ → ℂ}
    (D : TwinLandau.TwinPoles P fun q => G (P q)) (he : ∀ p, G (-p) = G p) (hn : ∀ p, 0 < p.re → G p ≠ 0)
    {q₀ : ι} (hq₀ : (P q₀).re ≠ 0) :
    ¬ PosDefQ fun r : ℝ => ∑' q, G (P q) * cexp ((Real.log r : ℝ) * P q) := by
  have hsum (l : ℝ) : Summable fun q => G (P q) * cexp (l * P q) :=
    TwinLandau.summable_cw_mul D (B := Real.exp |l|) fun q => by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.2 ?_
      have h := D.re_lt q
      have e : ((l : ℂ) * P q).re = l * (P q).re := by simp
      rw [e]
      calc l * (P q).re ≤ |l * (P q).re| := le_abs_self _
        _ = |l| * |(P q).re| := abs_mul _ _
        _ ≤ |l| * 1 := mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
        _ = |l| := mul_one _
  intro hK
  have hW : ∀ r : ℚ, 0 < r → 0 ≤ TwinLandau.Wsum P (fun q => G (P q)) (1 * Real.log r) := by
    intro r hr
    have htwin : TwinLandau.Wsum P (fun q => G (P q)) (Real.log r) =
        2 * (∑' q, G (P q) * cexp ((Real.log (1 : ℝ) : ℝ) * P q)) +
          (∑' q, G (P q) * cexp ((Real.log (r : ℝ) : ℝ) * P q)) +
          ∑' q, G (P q) * cexp ((Real.log ((r : ℝ)⁻¹) : ℝ) * P q) := by
      unfold TwinLandau.Wsum TwinLandau.wq
      have h0 := hsum 0
      have h1 := hsum (Real.log r)
      have h2 := hsum (-Real.log r)
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h0
      have e : ∀ q, G (P q) * (2 + cexp ((Real.log r : ℝ) * P q) + cexp (-((Real.log r : ℝ) * P q))) =
          2 * G (P q) + G (P q) * cexp ((Real.log r : ℝ) * P q) +
            G (P q) * cexp ((-Real.log r : ℝ) * P q) := fun q => by
        push_cast; ring_nf
      rw [tsum_congr e, ((h0.mul_left 2).add h1).tsum_add h2, (h0.mul_left 2).tsum_add h1, tsum_mul_left,
        Real.log_one, Real.log_inv]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [one_mul, htwin]
    exact minor_nonneg hK hr
  exact hq₀ (re_eq_zero_of_dense D (G := G) (fun _ => rfl) he hn one_ne_zero hW q₀)

/-! ## The zeros of the quaternion zeta function -/

/-- **The completed zeta function of the integral quaternions**, `(1 − 4^{1−s})ζ̂(s)ζ̂(s − 1)`. -/
def xiQ (s : ℂ) : ℂ := (1 - 4 ^ (1 - s)) * xiP1 s

/-- The spacing `π/log 2` of the zeros of `1 − 4^{1−s}` on the line `Re s = 1`. -/
def gap : ℝ := π / Real.log 2

lemma gap_pos : 0 < gap := div_pos Real.pi_pos (Real.log_pos one_lt_two)

/-- The poles of the quaternion kernel, `P = ρ' − 1`: those of `ℙ¹` (left) and `iπk/log 2`, `k ≠ 0` (right). -/
def poleQ : (ZIdx ⊕ ZIdx) ⊕ {k : ℤ // k ≠ 0} → ℂ :=
  Sum.elim poleP1 fun k => ((gap * k : ℝ) : ℂ) * I

/-- **`ξ_Q` vanishes at every `1 + P`**: at the zeros of `ℙ¹`, and at `1 + iπk/log 2`, where `4^{1−s} = e^{−2πik}`. -/
theorem xiQ_poleQ (q : (ZIdx ⊕ ZIdx) ⊕ {k : ℤ // k ≠ 0}) : xiQ (1 + poleQ q) = 0 := by
  rcases q with q | ⟨k, hk⟩
  · rw [xiQ, poleQ, Sum.elim_inl, poleP1, add_sub_cancel, xiP1_zP1, mul_zero]
  · have h4 : (4 : ℂ) ^ (1 - (1 + ((gap * k : ℝ) : ℂ) * I)) = 1 := by
      rw [show (1 : ℂ) - (1 + ((gap * k : ℝ) : ℂ) * I) = -(((gap * k : ℝ) : ℂ) * I) by ring,
        Complex.cpow_def_of_ne_zero (by norm_num), ← Complex.exp_int_mul_two_pi_mul_I (-k)]
      congr 1
      have hl : Complex.log 4 = ((2 * Real.log 2 : ℝ) : ℂ) := by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast; ring
      have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      rw [hl, gap]
      push_cast
      field_simp
    rw [xiQ, poleQ, Sum.elim_inr, h4, sub_self, zero_mul]

/-! ## The kernel -/

lemma gP1_poleQ_inr (k : {k : ℤ // k ≠ 0}) : ‖gP1 (poleQ (Sum.inr k))‖ = 1 / (1 + (gap * k) ^ 2) := by
  have e : poleQ (Sum.inr k) ^ 2 = ((-(gap * k) ^ 2 : ℝ) : ℂ) := by
    simp only [poleQ, Sum.elim_inr]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hne : poleQ (Sum.inr k) ^ 2 ≠ 1 := by
    rw [e]
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at this
    nlinarith [sq_nonneg (gap * k)]
  unfold gP1
  rw [ite_eq_right hne, e, show (1 : ℂ) - ((-(gap * k) ^ 2 : ℝ) : ℂ) = ((1 + (gap * k) ^ 2 : ℝ) : ℂ) by push_cast; ring,
    norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

lemma summable_inr : Summable fun k : {k : ℤ // k ≠ 0} => ‖gP1 (poleQ (Sum.inr k))‖ := by
  have hs : Summable fun k : ℤ => 1 / (k : ℝ) ^ 2 := Real.summable_one_div_int_pow.2 one_lt_two
  refine ((hs.subtype fun k : ℤ => k ≠ 0).mul_left (1 / gap ^ 2)).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun k => ?_
  rw [gP1_poleQ_inr]
  have hk : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (k.1 : ℝ) ≠ 0 := Int.cast_ne_zero.2 k.2
    positivity
  have hg := gap_pos
  simp only [Function.comp_apply]
  rw [div_mul_div_comm, one_mul, one_div_le_one_div (by positivity) (by positivity)]
  nlinarith [sq_nonneg (gap * k)]

lemma finite_inr (R : ℝ) : {k : {k : ℤ // k ≠ 0} | ‖poleQ (Sum.inr k)‖ ≤ R}.Finite := by
  have hg := gap_pos
  refine ((Set.finite_Icc (-⌈R / gap⌉) ⌈R / gap⌉).preimage Subtype.val_injective.injOn).subset fun k hk => ?_
  simp only [Set.mem_ofPred_eq, poleQ, Sum.elim_inr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one] at hk
  simp only [Set.mem_preimage, Set.mem_Icc]
  have h1 : |(k.1 : ℝ)| ≤ R / gap := by
    rw [le_div_iff₀ hg, mul_comm]
    rwa [abs_of_pos hg] at hk
  have h2 := Int.le_ceil (R / gap)
  constructor
  · have : -(R / gap) ≤ (k.1 : ℝ) := (abs_le.1 h1).1
    exact_mod_cast (by linarith : (-(⌈R / gap⌉ : ℝ)) ≤ k.1)
  · have : (k.1 : ℝ) ≤ R / gap := (abs_le.1 h1).2
    exact_mod_cast (by linarith : (k.1 : ℝ) ≤ ⌈R / gap⌉)

theorem twinPoles_Q : TwinLandau.TwinPoles poleQ fun q => gP1 (poleQ q) where
  summ := Summable.sum _ summable_wP1 summable_inr
  re_lt := by
    rintro (q | k)
    · exact abs_re_poleP1 q
    · simp [poleQ]
  im_ne := by
    rintro (q | ⟨k, hk⟩)
    · exact im_poleP1_ne q
    · simp only [poleQ, Sum.elim_inr, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
        Complex.I_re, mul_one, mul_zero, add_zero]
      exact mul_ne_zero gap_pos.ne' (Int.cast_ne_zero.2 hk)
  finite := fun R => by
    have h := ((finite_poleP1 R).image Sum.inl).union ((finite_inr R).image Sum.inr)
    refine h.subset ?_
    rintro (q | k) hq
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact Or.inr ⟨k, hq, rfl⟩

/-- **The kernel of the integral quaternions**, `K_Q(r) = Σ_{ρ'} r^{ρ' − 1}/(ρ'(2 − ρ'))` over the zeros `1 + P` of
`ξ_Q`, in the pole variable `P = ρ' − 1`: `PurityRational.kerP1` plus the terms of the zeros on the line. -/
def kerQ (r : ℝ) : ℂ := ∑' q : (ZIdx ⊕ ZIdx) ⊕ {k : ℤ // k ≠ 0}, gP1 (poleQ q) * cexp ((Real.log r : ℝ) * poleQ q)

/-- **The kernel of the integral quaternions is not positive-definite** on the positive rationals, with no hypothesis:
the zeros `1 + πik/log 2` on the line do not compensate for the nontrivial zeros of `ζ`, which are off it. -/
theorem not_posDef_quaternion : ¬ PosDefQ kerQ := by
  have := ZerosInfinite.infinite_ZIdx
  obtain ⟨q⟩ := (inferInstance : Nonempty ZIdx)
  have hq : (poleQ (Sum.inl (Sum.inl q))).re ≠ 0 := by
    have h1 := (nontrivial_zZF q).re_lt_one
    simp only [poleQ, Sum.elim_inl, re_poleP1, zP1]
    linarith
  exact not_posDef_of_re_ne twinPoles_Q gP1_neg (fun p _ => gP1_ne p) hq

end PurityQuaternion

#print axioms PurityQuaternion.not_posDef_of_re_ne
#print axioms PurityQuaternion.xiQ_poleQ
#print axioms PurityQuaternion.not_posDef_quaternion
