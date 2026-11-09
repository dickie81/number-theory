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
  `{1, r}` is the twin sum of `TwinLandau` at `λ = log r`. If `K` were positive-definite,
  `BallKernel.re_eq_zero_of_dense` would put every `ρ'` on `Re s = 1`, and the nontrivial zeros of `ζ` are not there.
  The argument needs only an even weight with no zero on `Re p > 0`, summable over the zeros (`not_posDef_kerG`), so it
  also gives the `ℙ¹` column of the Gaussian criterion `BallKernel.rh_iff_posDef`: the kernel
  `Σ_{ρ'} e^{(ρ' − 1)²/2} r^{ρ' − 1}` is not positive-definite either (`not_posDef_gauss`).
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

/-! ## The kernels -/

/-- **The kernel of `ℙ¹` with weight `G`**, `K_G(r) = Σ_q G(P_q)e^{(log r)P_q}` over the poles `P = ρ' − 1`. -/
def kerG (G : ℂ → ℂ) (r : ℝ) : ℂ := ∑' q : ZIdx ⊕ ZIdx, G (poleP1 q) * cexp ((Real.log r : ℝ) * poleP1 q)

/-- **No weight makes the kernel of `ℙ¹` positive-definite**: if `G` is even, has no zero on `Re p > 0` and is
summable over the poles, `K_G` is not positive-definite on the positive rationals. Its `2 × 2` minors are the twin
sums of `TwinLandau` at `λ = log r`; positivity would put every zero of `ζ̂(s)ζ̂(s − 1)` on `Re s = 1`
(`BallKernel.re_eq_zero_of_dense`), and the nontrivial zeros of `ζ` have `Re ρ < 1`. -/
theorem not_posDef_kerG {G : ℂ → ℂ} (hs : Summable fun q : ZIdx ⊕ ZIdx => ‖G (poleP1 q)‖)
    (he : ∀ p, G (-p) = G p) (hn : ∀ p, 0 < p.re → G p ≠ 0) : ¬ PosDefQ (kerG G) := by
  have D : TwinLandau.TwinPoles poleP1 fun q => G (poleP1 q) :=
    ⟨hs, abs_re_poleP1, im_poleP1_ne, finite_poleP1⟩
  have hsum (l : ℝ) : Summable fun q : ZIdx ⊕ ZIdx => G (poleP1 q) * cexp (l * poleP1 q) :=
    TwinLandau.summable_cw_mul D (B := Real.exp |l|) fun q => by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.2 ?_
      have h := abs_re_poleP1 q
      have e : ((l : ℂ) * poleP1 q).re = l * (poleP1 q).re := by simp
      rw [e]
      calc l * (poleP1 q).re ≤ |l * (poleP1 q).re| := le_abs_self _
        _ = |l| * |(poleP1 q).re| := abs_mul _ _
        _ ≤ |l| * 1 := mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
        _ = |l| := mul_one _
  have htwin (r : ℝ) : TwinLandau.Wsum poleP1 (fun q => G (poleP1 q)) (Real.log r) =
      2 * kerG G 1 + kerG G r + kerG G r⁻¹ := by
    unfold TwinLandau.Wsum TwinLandau.wq kerG
    have h0 := hsum 0
    have h1 := hsum (Real.log r)
    have h2 := hsum (-Real.log r)
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h0
    have e : ∀ q : ZIdx ⊕ ZIdx, G (poleP1 q) * (2 + cexp ((Real.log r : ℝ) * poleP1 q) +
        cexp (-((Real.log r : ℝ) * poleP1 q))) = 2 * G (poleP1 q) +
        G (poleP1 q) * cexp ((Real.log r : ℝ) * poleP1 q) +
        G (poleP1 q) * cexp ((-Real.log r : ℝ) * poleP1 q) := fun q => by
      push_cast; ring_nf
    rw [tsum_congr e, ((h0.mul_left 2).add h1).tsum_add h2, (h0.mul_left 2).tsum_add h1, tsum_mul_left,
      Real.log_one, Real.log_inv]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  intro hK
  have hW : ∀ r : ℚ, 0 < r →
      0 ≤ TwinLandau.Wsum poleP1 (fun q => G (poleP1 q)) (1 * Real.log r) := by
    intro r hr
    rw [one_mul, htwin]
    exact minor_nonneg hK hr
  have := ZerosInfinite.infinite_ZIdx
  obtain ⟨q⟩ := (inferInstance : Nonempty ZIdx)
  have h := re_eq_zero_of_dense D (G := G) (fun _ => rfl) he hn one_ne_zero hW (Sum.inl q)
  have hlt := (nontrivial_zZF q).re_lt_one
  rw [re_poleP1] at h
  simp only [zP1, Sum.elim_inl] at h
  linarith

/-- **The kernel of `ℙ¹`**, `K(r) = Σ_{ρ'} r^{ρ' − 1}/(ρ'(2 − ρ'))` over the zeros `ρ' = ρ` and `ρ' = ρ + 1` of
`ζ̂(s)ζ̂(s − 1)`, with `r^{ρ' − 1}` written `e^{(ρ' − 1)log r}`: `BallHadamard.kerH` for the line `Re s = 1`. -/
def kerP1 (r : ℝ) : ℂ :=
  ∑' q : ZIdx ⊕ ZIdx, cexp ((zP1 q - 1) * Real.log r) / (zP1 q * (2 - zP1 q))

/-- The kernel in the pole variable: `K = K_G` for `G(p) = 1/(1 − p²)`. -/
lemma kerP1_eq : kerP1 = kerG gP1 := by
  funext r
  unfold kerP1 kerG
  refine tsum_congr fun q => ?_
  rw [gP1_poleP1, one_div_mul_eq_div, mul_comm (Real.log r : ℂ)]
  rfl

/-- **The kernel of `ℙ¹` is not positive-definite on the positive rationals**, with no hypothesis: the Euler product
and the functional equation of `ℙ¹` do not give the positivity. -/
theorem not_posDef : ¬ PosDefQ kerP1 := by
  rw [kerP1_eq]
  exact not_posDef_kerG summable_wP1 gP1_neg fun p _ => gP1_ne p

/-! ## The Gaussian kernel of `ℙ¹` -/

/-- The Gaussian weight in the pole variable, `e^{P²/2}`: at `P = ρ' − 1` it is `e^{(ρ' − 1)²/2}`, the weight of
`BallKernel.kerK` moved to the line `Re s = 1`. -/
def gwP1 (p : ℂ) : ℂ := cexp (p ^ 2 / 2)

/-- `|e^{(ρ' − 1)²/2}| ≤ e^{3/8}|e^{(ρ − ½)²/2}|` for both kinds of zero `ρ'` of `ℙ¹`, since `0 < Re ρ < 1`. -/
lemma norm_gwP1_le (q : ZIdx) :
    ‖gwP1 (zetaZeroFamily q - 1)‖ ≤ Real.exp (3 / 8) * ‖gw (poleP q)‖ ∧
      ‖gwP1 (zetaZeroFamily q)‖ ≤ Real.exp (3 / 8) * ‖gw (poleP q)‖ := by
  have h0 := (nontrivial_zZF q).re_pos
  have h1 := (nontrivial_zZF q).re_lt_one
  unfold gwP1 gw poleP
  simp only [Complex.norm_exp, ← Real.exp_add]
  have e1 : ((zetaZeroFamily q - 1) ^ 2 / 2).re =
      ((zetaZeroFamily q).re - 1) ^ 2 / 2 - (zetaZeroFamily q).im ^ 2 / 2 := by
    simp only [sq, Complex.div_ofNat_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  have e2 : ((zetaZeroFamily q) ^ 2 / 2).re = (zetaZeroFamily q).re ^ 2 / 2 - (zetaZeroFamily q).im ^ 2 / 2 := by
    simp only [sq, Complex.div_ofNat_re, Complex.mul_re]
    ring
  have e3 : ((2 * (zetaZeroFamily q - 1 / 2)) ^ 2 / 8).re =
      ((zetaZeroFamily q).re - 1 / 2) ^ 2 / 2 - (zetaZeroFamily q).im ^ 2 / 2 := by
    rw [show (2 * (zetaZeroFamily q - 1 / 2)) ^ 2 / 8 = (zetaZeroFamily q - ((1 / 2 : ℝ) : ℂ)) ^ 2 / 2 by
      push_cast; ring]
    simp only [sq, Complex.div_ofNat_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [e1, e2, e3]
  constructor <;> exact Real.exp_le_exp.2 (by nlinarith)

lemma summable_gwP1 : Summable fun q : ZIdx ⊕ ZIdx => ‖gwP1 (poleP1 q)‖ := by
  refine Summable.sum _ ?_ ?_
  · refine (summable_gw.mul_left (Real.exp (3 / 8))).of_nonneg_of_le (fun _ => norm_nonneg _) fun q => ?_
    simpa [poleP1, zP1] using (norm_gwP1_le q).1
  · refine (summable_gw.mul_left (Real.exp (3 / 8))).of_nonneg_of_le (fun _ => norm_nonneg _) fun q => ?_
    simpa [poleP1, zP1] using (norm_gwP1_le q).2

/-- **The Gaussian kernel of `ℙ¹`**, `K(r) = Σ_{ρ'} e^{(ρ' − 1)²/2} r^{ρ' − 1}` over the zeros `ρ' = ρ` and
`ρ' = ρ + 1` of `ζ̂(s)ζ̂(s − 1)`: `BallKernel.kerK` for the line `Re s = 1`. -/
def kerP1G (r : ℝ) : ℂ :=
  ∑' q : ZIdx ⊕ ZIdx, cexp ((zP1 q - 1) ^ 2 / 2) * cexp ((zP1 q - 1) * Real.log r)

/-- **The Gaussian kernel of `ℙ¹` is not positive-definite on the positive rationals**, with no hypothesis: the
`ℙ¹` column of `BallKernel.rh_iff_posDef`. -/
theorem not_posDef_gauss : ¬ PosDefQ kerP1G := by
  have e : kerP1G = kerG gwP1 := by
    funext r
    unfold kerP1G kerG gwP1
    refine tsum_congr fun q => ?_
    rw [mul_comm (Real.log r : ℂ)]
    rfl
  rw [e]
  exact not_posDef_kerG summable_gwP1 (fun p => by unfold gwP1; rw [neg_sq]) fun p _ => Complex.exp_ne_zero _

end PurityRational

#print axioms PurityRational.functional_equation
#print axioms PurityRational.euler_product
#print axioms PurityRational.xiP1_zP1
#print axioms PurityRational.exists_zero_re_ne_one
#print axioms PurityRational.not_posDef
#print axioms PurityRational.not_posDef_kerG
#print axioms PurityRational.not_posDef_gauss
