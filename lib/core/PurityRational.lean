/-
# Purity over `ℚ`: the zeta function of `ℙ¹` over `ℤ`

Plain statement. `ζ(s)ζ(s − 1)`, the zeta function of the projective line over `ℤ`, has the Euler product
`∏_p (1 − p^{−s})^{−1}(1 − p^{1−s})^{−1}` on `Re s > 2` (`euler_product`), and its completion `ζ̂(s)ζ̂(s − 1)` is
invariant under `s ↦ 2 − s` (`functional_equation`), so its line is `Re s = 1`. It vanishes at the nontrivial zeros
`ρ` of `ζ` and at the `ρ + 1` (`xiP1_zP1`), off that line (`exists_zero_re_ne_one`). Build its kernel from these zeros
as `BallHadamard.kerH` is built from those of `ζ`: `K(r) = Σ_{ρ'} r^{ρ' − 1}/(ρ'(2 − ρ'))` over `ρ' = ρ` and
`ρ' = ρ + 1`, with multiplicity (`kerP1`). It is not positive-definite on the positive rationals (`not_posDef`),
with no hypothesis. This is the number-field form of `PurityTest`: an Euler product and a functional equation of
`ζ`'s kind do not give the positivity, and what `ζ` has and `ζ(s)ζ(s − 1)` lacks is purity, all its zeros on one line.
* The weights are summable (`summable_wP1`): in the critical strip `|2 − ρ| ≥ |1 − ρ|` and `|ρ + 1| ≥ |ρ|`, so each
  weight is at most Hadamard's `|1/(ρ(1 − ρ))|` (`BallHadamard.summable_hw`).
* In the pole variable `P = ρ' − 1`, with `|Re P| < 1`, and the weight `G(p) = 1/(1 − p²)`, the `2 × 2` minor on
  `{1, r}` is the twin sum of `TwinLandau` at `λ = log r` (`twin_eq_kerP1`). If `K` were positive-definite,
  `BallKernel.re_eq_zero_of_dense` would put every `ρ'` on `Re s = 1`, and the nontrivial zeros of `ζ` are not there.
-/
import Mathlib
import BallHadamard

open Real Complex Finset Filter Topology ComplexConjugate WeilForm WeilTest
open scoped ComplexOrder

noncomputable section

namespace PurityRational

open BallKernel

/-! ## The functional equation and the Euler product -/

/-- **The completed zeta function of `ℙ¹` over `ℤ`**, `ζ̂(s)ζ̂(s − 1)`. -/
def xiP1 (s : ℂ) : ℂ := completedRiemannZeta s * completedRiemannZeta (s - 1)

/-- **The functional equation of `ℙ¹`**: `ζ̂(2 − s)ζ̂(1 − s) = ζ̂(s)ζ̂(s − 1)`, so its line is `Re s = 1`. -/
theorem functional_equation (s : ℂ) : xiP1 (2 - s) = xiP1 s := by
  unfold xiP1
  rw [show (2 : ℂ) - s - 1 = 1 - s by ring, completedRiemannZeta_one_sub,
    show (2 : ℂ) - s = 1 - (s - 1) by ring, completedRiemannZeta_one_sub, mul_comm]

/-- **The Euler product of `ℙ¹`**: on `Re s > 2`, `ζ(s)ζ(s − 1) = ∏_p (1 − p^{−s})^{−1}(1 − p^{1−s})^{−1}`. -/
theorem euler_product {s : ℂ} (hs : 2 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (p : ℂ) ^ (1 - s))⁻¹)
      (riemannZeta s * riemannZeta (s - 1)) := by
  have h1 := riemannZeta_eulerProduct_hasProd (s := s) (by linarith)
  have h2 := riemannZeta_eulerProduct_hasProd (s := s - 1) (by simp; linarith)
  rw [show -(s - 1) = 1 - s by ring] at h2
  exact h1.mul h2

/-! ## Its zeros -/

/-- `ζ̂` vanishes at the nontrivial zeros of `ζ`. -/
lemma completedRiemannZeta_eq_zero {ρ : ℂ} (h : IsNontrivialZero ρ) : completedRiemannZeta ρ = 0 := by
  have hpos := h.re_pos
  have hρ0 : ρ ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hpos; exact lt_irrefl 0 hpos
  have e := riemannZeta_def_of_ne_zero hρ0
  rw [h.1, eq_comm, div_eq_zero_iff] at e
  exact e.resolve_right (Gammaℝ_ne_zero_of_re_pos hpos)

/-- The zeros of `ζ̂(s)ζ̂(s − 1)` used here: the nontrivial zeros `ρ` of `ζ` (left) and the `ρ + 1` (right), with
multiplicity. -/
def zP1 : ZIdx ⊕ ZIdx → ℂ := Sum.elim zetaZeroFamily fun q => zetaZeroFamily q + 1

/-- **Each `ρ` and each `ρ + 1` is a zero of `ζ̂(s)ζ̂(s − 1)`.** -/
theorem xiP1_zP1 (q : ZIdx ⊕ ZIdx) : xiP1 (zP1 q) = 0 := by
  rcases q with q | q
  · simp only [xiP1, zP1, Sum.elim_inl, completedRiemannZeta_eq_zero (nontrivial_zZF q), zero_mul]
  · simp only [xiP1, zP1, Sum.elim_inr, add_sub_cancel_right,
      completedRiemannZeta_eq_zero (nontrivial_zZF q), mul_zero]

/-- **`ζ̂(s)ζ̂(s − 1)` has zeros off its line `Re s = 1`**: every nontrivial zero `ρ` of `ζ` has `0 < Re ρ < 1`. -/
theorem exists_zero_re_ne_one : ∃ s : ℂ, xiP1 s = 0 ∧ s.re ≠ 1 := by
  have := ZerosInfinite.infinite_ZIdx
  obtain ⟨q⟩ := (inferInstance : Nonempty ZIdx)
  exact ⟨zP1 (Sum.inl q), xiP1_zP1 _, (nontrivial_zZF q).re_lt_one.ne⟩

/-! ## The poles and the weights -/

/-- The pole variable `P = ρ' − 1`, centred on the line `Re s = 1`. -/
def poleP1 (q : ZIdx ⊕ ZIdx) : ℂ := zP1 q - 1

/-- The weight in the pole variable, `G(p) = 1/(1 − p²)`: at `P = ρ' − 1` it is `1/(ρ'(2 − ρ'))`. At `p = ±1`,
where no pole lies, it is set to `1`, so that `G` has no zero. -/
def gP1 (p : ℂ) : ℂ := if p ^ 2 = 1 then 1 else 1 / (1 - p ^ 2)

lemma gP1_ne (p : ℂ) : gP1 p ≠ 0 := by
  unfold gP1
  split_ifs with h
  · exact one_ne_zero
  · exact one_div_ne_zero (sub_ne_zero.2 (Ne.symm h))

lemma gP1_neg (p : ℂ) : gP1 (-p) = gP1 p := by unfold gP1; rw [neg_sq]

lemma re_poleP1 (q : ZIdx ⊕ ZIdx) : (poleP1 q).re = (zP1 q).re - 1 := by simp [poleP1]

lemma abs_re_poleP1 (q : ZIdx ⊕ ZIdx) : |(poleP1 q).re| < 1 := by
  rw [re_poleP1, abs_lt]
  rcases q with q | q
  · have h0 := (nontrivial_zZF q).re_pos
    have h1 := (nontrivial_zZF q).re_lt_one
    simp only [zP1, Sum.elim_inl]
    constructor <;> linarith
  · have h0 := (nontrivial_zZF q).re_pos
    have h1 := (nontrivial_zZF q).re_lt_one
    simp only [zP1, Sum.elim_inr, Complex.add_re, Complex.one_re]
    constructor <;> linarith

lemma im_poleP1_ne (q : ZIdx ⊕ ZIdx) : (poleP1 q).im ≠ 0 := by
  rcases q with q | q <;> simpa [poleP1, zP1] using im_zetaZeroFamily_ne q

lemma finite_poleP1 (R : ℝ) : {q : ZIdx ⊕ ZIdx | ‖poleP1 q‖ ≤ R}.Finite := by
  have hA := finite_poleP (2 * R + 1)
  refine ((hA.image Sum.inl).union (hA.image Sum.inr)).subset ?_
  rintro (q | q) hq
  · refine Or.inl ⟨q, ?_, rfl⟩
    have hq' : ‖zetaZeroFamily q - 1‖ ≤ R := by simpa [poleP1, zP1] using hq
    have e : poleP q = 2 * (zetaZeroFamily q - 1) + 1 := by unfold poleP; ring
    show ‖poleP q‖ ≤ 2 * R + 1
    calc ‖poleP q‖ ≤ ‖2 * (zetaZeroFamily q - 1)‖ + ‖(1 : ℂ)‖ := by rw [e]; exact norm_add_le _ _
      _ = 2 * ‖zetaZeroFamily q - 1‖ + 1 := by rw [norm_mul]; simp
      _ ≤ 2 * R + 1 := by linarith
  · refine Or.inr ⟨q, ?_, rfl⟩
    have hq' : ‖zetaZeroFamily q‖ ≤ R := by simpa [poleP1, zP1] using hq
    have e : poleP q = 2 * zetaZeroFamily q - 1 := by unfold poleP; ring
    show ‖poleP q‖ ≤ 2 * R + 1
    calc ‖poleP q‖ ≤ ‖2 * zetaZeroFamily q‖ + ‖(1 : ℂ)‖ := by rw [e]; exact norm_sub_le _ _
      _ = 2 * ‖zetaZeroFamily q‖ + 1 := by rw [norm_mul]; simp
      _ ≤ 2 * R + 1 := by linarith

lemma gP1_poleP1 (q : ZIdx ⊕ ZIdx) : gP1 (poleP1 q) = 1 / (zP1 q * (2 - zP1 q)) := by
  have hne : poleP1 q ^ 2 ≠ 1 := fun h => by
    have hre := abs_re_poleP1 q
    have h' : (poleP1 q - 1) * (poleP1 q + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h1 | h1
    · rw [sub_eq_zero.1 h1] at hre; simp at hre
    · rw [eq_neg_of_add_eq_zero_left h1] at hre; simp at hre
  unfold gP1
  simp only [hne, ↓reduceIte]
  rw [show 1 - poleP1 q ^ 2 = zP1 q * (2 - zP1 q) by unfold poleP1; ring]

/-- `|1/(ρ'(2 − ρ'))| ≤ |1/(ρ(1 − ρ))|` for both kinds of zero `ρ'` of `ℙ¹`. -/
lemma norm_w_le (q : ZIdx) :
    ‖1 / (zetaZeroFamily q * (2 - zetaZeroFamily q))‖ ≤
      ‖1 / (zetaZeroFamily q * (1 - zetaZeroFamily q))‖ ∧
    ‖1 / ((zetaZeroFamily q + 1) * (2 - (zetaZeroFamily q + 1)))‖ ≤
      ‖1 / (zetaZeroFamily q * (1 - zetaZeroFamily q))‖ := by
  have h0 := (nontrivial_zZF q).re_pos
  have h1 := (nontrivial_zZF q).re_lt_one
  set ρ := zetaZeroFamily q
  have hρ : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have h1ρ : 1 - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hprod : 0 < ‖ρ * (1 - ρ)‖ := norm_pos_iff.2 (mul_ne_zero hρ h1ρ)
  -- `|2 − ρ| ≥ |1 − ρ|` and `|ρ + 1| ≥ |ρ|` in the strip, from the squared norms
  have hA : ‖1 - ρ‖ ≤ ‖2 - ρ‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.re_ofNat,
      Complex.im_ofNat]
    nlinarith
  have hB : ‖ρ‖ ≤ ‖ρ + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith
  constructor
  · rw [norm_div, norm_div, norm_one, norm_mul, norm_mul]
    exact one_div_le_one_div_of_le (by rw [← norm_mul]; exact hprod)
      (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
  · rw [norm_div, norm_div, norm_one, norm_mul, norm_mul, show 2 - (ρ + 1) = 1 - ρ by ring]
    exact one_div_le_one_div_of_le (by rw [← norm_mul]; exact hprod)
      (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

/-- **The weights are summable**, by comparison with Hadamard's `Σ_ρ |1/(ρ(1 − ρ))| < ∞`. -/
lemma summable_wP1 : Summable fun q : ZIdx ⊕ ZIdx => ‖gP1 (poleP1 q)‖ := by
  refine Summable.sum _ ?_ ?_
  · refine BallHadamard.summable_hw.of_nonneg_of_le (fun _ => norm_nonneg _) fun q => ?_
    simp only [Function.comp_apply, gP1_poleP1, zP1, Sum.elim_inl]
    exact (norm_w_le q).1
  · refine BallHadamard.summable_hw.of_nonneg_of_le (fun _ => norm_nonneg _) fun q => ?_
    simp only [Function.comp_apply, gP1_poleP1, zP1, Sum.elim_inr]
    exact (norm_w_le q).2

theorem twinPoles_P1 : TwinLandau.TwinPoles poleP1 fun q => gP1 (poleP1 q) :=
  ⟨summable_wP1, abs_re_poleP1, im_poleP1_ne, finite_poleP1⟩

/-! ## The kernel -/

/-- **The kernel of `ℙ¹`**, `K(r) = Σ_{ρ'} r^{ρ' − 1}/(ρ'(2 − ρ'))` over the zeros `ρ' = ρ` and `ρ' = ρ + 1` of
`ζ̂(s)ζ̂(s − 1)`, with `r^{ρ' − 1}` written `e^{(ρ' − 1)log r}`: `BallHadamard.kerH` for the line `Re s = 1`. -/
def kerP1 (r : ℝ) : ℂ :=
  ∑' q : ZIdx ⊕ ZIdx, cexp ((zP1 q - 1) * Real.log r) / (zP1 q * (2 - zP1 q))

/-- The kernel in the pole variable: `K(r) = Σ_q G(P_q)e^{(log r)P_q}`. -/
lemma kerP1_eq (r : ℝ) :
    kerP1 r = ∑' q : ZIdx ⊕ ZIdx, gP1 (poleP1 q) * cexp ((Real.log r : ℝ) * poleP1 q) := by
  unfold kerP1
  refine tsum_congr fun q => ?_
  rw [gP1_poleP1, one_div_mul_eq_div, mul_comm (Real.log r : ℂ)]
  rfl

lemma summable_kerP1 (l : ℝ) : Summable fun q : ZIdx ⊕ ZIdx => gP1 (poleP1 q) * cexp (l * poleP1 q) :=
  TwinLandau.summable_cw_mul twinPoles_P1 (B := Real.exp |l|) fun q => by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h := abs_re_poleP1 q
    have e : ((l : ℂ) * poleP1 q).re = l * (poleP1 q).re := by simp
    rw [e]
    calc l * (poleP1 q).re ≤ |l * (poleP1 q).re| := le_abs_self _
      _ = |l| * |(poleP1 q).re| := abs_mul _ _
      _ ≤ |l| * 1 := mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
      _ = |l| := mul_one _

/-- **The `2 × 2` minors are the twin sum**: `2K(1) + K(r) + K(1/r) = Σ_q G(P_q)(2 + e^{λP_q} + e^{−λP_q})` at
`λ = log r`. -/
theorem twin_eq_kerP1 (r : ℝ) :
    TwinLandau.Wsum poleP1 (fun q => gP1 (poleP1 q)) (Real.log r) = 2 * kerP1 1 + kerP1 r + kerP1 r⁻¹ := by
  unfold TwinLandau.Wsum TwinLandau.wq
  have h0 := summable_kerP1 0
  have h1 := summable_kerP1 (Real.log r)
  have h2 := summable_kerP1 (-Real.log r)
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h0
  have e : ∀ q : ZIdx ⊕ ZIdx, gP1 (poleP1 q) * (2 + cexp ((Real.log r : ℝ) * poleP1 q) +
      cexp (-((Real.log r : ℝ) * poleP1 q))) = 2 * gP1 (poleP1 q) +
      gP1 (poleP1 q) * cexp ((Real.log r : ℝ) * poleP1 q) +
      gP1 (poleP1 q) * cexp ((-Real.log r : ℝ) * poleP1 q) := fun q => by
    push_cast; ring_nf
  rw [tsum_congr e, ((h0.mul_left 2).add h1).tsum_add h2, (h0.mul_left 2).tsum_add h1, tsum_mul_left,
    kerP1_eq, kerP1_eq, kerP1_eq, Real.log_one, Real.log_inv]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]

/-- **The kernel of `ℙ¹` is not positive-definite on the positive rationals.** If it were, its `2 × 2` minors would
be nonnegative twin sums, and the Landau argument of `BallKernel.re_eq_zero_of_dense` would put every zero `ρ'` of
`ζ̂(s)ζ̂(s − 1)` on the line `Re s = 1`; but `ζ` has a nontrivial zero (`ZerosInfinite.infinite_ZIdx`), and it has
`Re ρ < 1`. No hypothesis: the Euler product and the functional equation of `ℙ¹` do not give the positivity. -/
theorem not_posDef : ¬ PosDefQ kerP1 := by
  intro hK
  have hW : ∀ r : ℚ, 0 < r →
      0 ≤ TwinLandau.Wsum poleP1 (fun q => gP1 (poleP1 q)) (1 * Real.log r) := by
    intro r hr
    rw [one_mul, twin_eq_kerP1]
    exact minor_nonneg hK hr
  have := ZerosInfinite.infinite_ZIdx
  obtain ⟨q⟩ := (inferInstance : Nonempty ZIdx)
  have h := re_eq_zero_of_dense twinPoles_P1 (G := gP1) (fun _ => rfl) gP1_neg (fun p _ => gP1_ne p)
    one_ne_zero hW (Sum.inl q)
  have hlt := (nontrivial_zZF q).re_lt_one
  rw [re_poleP1] at h
  simp only [zP1, Sum.elim_inl] at h
  linarith

end PurityRational

#print axioms PurityRational.functional_equation
#print axioms PurityRational.euler_product
#print axioms PurityRational.xiP1_zP1
#print axioms PurityRational.exists_zero_re_ne_one
#print axioms PurityRational.not_posDef
