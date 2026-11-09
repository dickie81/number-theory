/-
# The `ℙ¹` column of Weil's twin criterion: its defect is never subexponential

Plain statement. `WeilForm.rh_iff_twins_subexp` says that RH holds exactly when Weil's form of `ζ` on the twin boxes
`g_l = twin (box 1) l` has a subexponential defect, and `WeilForm.weil_twins_rate` that `Q(g_l) ≥ −Ce^{σl}` exactly
when every nontrivial zero has `|2 Re ρ − 1| ≤ σ`. This file builds the same form for `ζ(s)ζ(s − 1)`, the zeta function
of `ℙ¹` over `ℤ` (`PurityRational`), whose zeros are the `ρ` and the `ρ + 1` and whose line is `Re s = 1`.
* **The test function** (`HP1`): `H_l(t) = ĝ_l(t + i/2)² + ĝ_l(t − i/2)²`. At `t = t_ρ = (ρ − ½)/i` the two terms are
  `ĝ_l(t′)²` at `t′ = (ρ′ − 1)/i` for `ρ′ = ρ` and `ρ′ = ρ + 1`, so the sum of `H_l` over the zeros of `ζ` is the sum
  of `ĝ_l²` over the zeros of `ℙ¹`, centred on its line. `H_l` is even, real on `ℝ` (`HP1_conj`) and in the strip
  class of `WeilForm.weilExplicit_zeta` (`stripTest_HP1`).
* **The form** (`QP1`): the right side of Weil's explicit formula (`WeilForm.WeilExplicit`) for `H_l`, its pole terms,
  `−g_H(0) log π`, the archimedean integral and the prime sum: built from the primes, with no zero in it, as
  `WeilForm.weilQ` is for `ζ`. By the explicit formula it is the zero sum `Σ_{ρ′} ĝ₀(t′)²(2 + e^{2lP} + e^{−2lP})` over
  the zeros of `ℙ¹`, `P = ρ′ − 1`, `ĝ₀` the transform of the box (`explicit_formula`).
* **The rate** (`rate_iff`): `QP1(l) ≥ −Ce^{σl}` for some `C` and all `l ≥ 0` if and only if every nontrivial zero has
  `|2 Re ρ − 1| ≤ σ − 1`; that is, the rate of `ℙ¹`'s defect is `ζ`'s plus one (`rate_iff_zeta`). The poles `P = ρ − 1`
  and `P = ρ` straddle the line: `max(1 − Re ρ, Re ρ) ≥ ½`, so the Landau argument (`TwinLandau.abs_re_le`) keeps
  the defect at least of rate `1` whatever the truth of RH.
* So **the defect of `ℙ¹` is never subexponential** (`not_subexp`), where for `ζ` it is subexponential exactly under RH;
  and **RH holds exactly when it is `O(e^l)`**, the least rate it can have (`rh_iff_rate_one`). The Euler product and
  the functional equation of `ℙ¹` do not give Weil positivity; the zeros on one line do.
-/
import Mathlib
import PurityRational
import WeilLandau
import WeilDischarge
import HadamardApply
import PhiLadder
import FourierInv

open Real Complex Filter Topology Set WeilForm WeilTest WeilStrip

noncomputable section

namespace PurityTwins

open PurityRational

/-! ## The test function -/

/-- **The test function of `ℙ¹`**: `H_l(t) = ĝ_l(t + i/2)² + ĝ_l(t − i/2)²` for the twin boxes `g_l = twin (box 1) l`
on `[−(l + 1), l + 1]`. -/
def HP1 (l : ℝ) (t : ℂ) : ℂ :=
  ghatC (twin (box 1) l) (l + 1) (t + I / 2) ^ 2 + ghatC (twin (box 1) l) (l + 1) (t - I / 2) ^ 2

/-- `H_l` on the real line, where it is real (`HP1_conj`). -/
def HP1R (l r : ℝ) : ℝ := (HP1 l r).re

/-- **The twin form of `ℙ¹`, from the primes**: the right side of Weil's explicit formula for `H_l`, with the pole terms
`H_l(±i/2)`, the constant `−g_H(0)log π`, the archimedean integral and the prime sum. No zero of `ζ` enters. -/
def QP1 (l : ℝ) : ℝ :=
  (HP1 l (I / 2) + HP1 l (-(I / 2))).re + (-(gh (HP1R l) 0 * Real.log π) + 1 / (2 * π) * (∫ r, HP1R l r * psiRe r) -
    2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh (HP1R l) (Real.log n))

lemma twin_even {l : ℝ} (hl : 0 ≤ l) (u : ℝ) : twin (box 1) l (-u) = twin (box 1) l u :=
  (twin_probe (box_probe 1) hl).even u

lemma HP1_conj {l : ℝ} (hl : 0 ≤ l) (t : ℂ) : HP1 l ((starRingEnd ℂ) t) = (starRingEnd ℂ) (HP1 l t) := by
  have hc := ghatC_conj (twin_even hl) (a := l + 1) (by linarith)
  have e1 : (starRingEnd ℂ) t + I / 2 = (starRingEnd ℂ) (t - I / 2) := by
    rw [map_sub, map_div₀, Complex.conj_I, map_ofNat]; ring
  have e2 : (starRingEnd ℂ) t - I / 2 = (starRingEnd ℂ) (t + I / 2) := by
    rw [map_add, map_div₀, Complex.conj_I, map_ofNat]; ring
  unfold HP1
  rw [e1, e2, hc, hc, map_add, map_pow, map_pow, add_comm]

lemma HP1_real {l : ℝ} (hl : 0 ≤ l) (r : ℝ) : HP1 l r = ((HP1R l r : ℝ) : ℂ) := by
  have h := HP1_conj hl (r : ℂ)
  rw [Complex.conj_ofReal] at h
  refine Complex.ext rfl ?_
  have him := congrArg Complex.im h
  rw [Complex.conj_im] at him
  simp only [Complex.ofReal_im]
  linarith

lemma HP1_even {l : ℝ} (hl : 0 ≤ l) (t : ℂ) : HP1 l (-t) = HP1 l t := by
  unfold HP1
  rw [show -t + I / 2 = -(t - I / 2) by ring, show -t - I / 2 = -(t + I / 2) by ring,
    even_ghat_sq (twin_even hl), even_ghat_sq (twin_even hl), add_comm]

/-- The pole terms are real. -/
lemma pole_real {l : ℝ} (hl : 0 ≤ l) :
    HP1 l (I / 2) + HP1 l (-(I / 2)) = (((HP1 l (I / 2) + HP1 l (-(I / 2))).re : ℝ) : ℂ) := by
  have h := HP1_conj hl (I / 2)
  rw [map_div₀, Complex.conj_I, map_ofNat, neg_div] at h
  rw [h]
  refine Complex.ext rfl ?_
  simp

/-! ## The strip class -/

/-- `ĝ_l` on `|Im z| ≤ 3/2`: `‖ĝ_l(z)‖²(1 + (Re z)²) ≤ K`. -/
lemma ghat_twin_strip {l : ℝ} (hl : 0 ≤ l) : ∃ K, ∀ z : ℂ, |z.im| ≤ 3 / 2 →
    ‖ghatC (twin (box 1) l) (l + 1) z‖ ^ 2 * (1 + z.re ^ 2) ≤ K := by
  have hint := (box_probe 1).intervalIntegrable
  set τ0 := 2 * Real.exp (l * (3 / 2)) * (Real.exp (3 / 2) * ∫ u in (-1 : ℝ)..1, |box 1 u|)
  set τ1 := 2 * Real.exp (l * (3 / 2)) * (2 * box 1 0 * Real.cosh (3 / 2))
  refine ⟨τ0 ^ 2 + τ1 ^ 2, fun z hz => ?_⟩
  have hcos : ‖2 * Complex.cos (l * z)‖ ≤ 2 * Real.exp (l * (3 / 2)) := by
    refine (norm_two_cos_le _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
    have e : ((l : ℂ) * z).im = l * z.im := by simp [Complex.mul_im]
    rw [e, abs_mul, abs_of_nonneg hl]
    exact mul_le_mul_of_nonneg_left hz hl
  refine sq_strip_bound (G := ghatC (twin (box 1) l) (l + 1)) ?_ ?_
  · rw [ghatC_twin one_pos (box_probe 1) hl, norm_mul]
    have h0 := norm_ghatC_le_exp_im (g := box 1) zero_le_one hint z
    have h1 : Real.exp (1 * |z.im|) ≤ Real.exp (3 / 2) := Real.exp_le_exp.2 (by linarith)
    have hI : 0 ≤ ∫ u in (-1 : ℝ)..1, |box 1 u| :=
      intervalIntegral.integral_nonneg (by norm_num) fun u _ => abs_nonneg _
    exact mul_le_mul hcos (h0.trans (mul_le_mul_of_nonneg_right h1 hI)) (norm_nonneg _) (by positivity)
  · rw [ghatC_twin one_pos (box_probe 1) hl, norm_mul]
    rcases eq_or_ne z 0 with rfl | hz0
    · simp only [norm_zero, zero_mul]
      have : 0 ≤ box 1 0 := box_nonneg 0 ⟨le_rfl, zero_le_one⟩
      positivity
    have h0 := norm_ghatC_le_of_antitone one_pos (box_probe 1).even box_antitone box_nonneg hz0
    have hb : 0 ≤ box 1 0 := box_nonneg 0 ⟨le_rfl, zero_le_one⟩
    have hch : Real.cosh (1 * |z.im|) ≤ Real.cosh (3 / 2) := by
      rw [Real.cosh_le_cosh, one_mul, abs_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      exact hz
    have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have h1 : ‖z‖ * ‖ghatC (box 1) 1 z‖ ≤ 2 * box 1 0 * Real.cosh (3 / 2) := by
      rw [le_div_iff₀ hz'] at h0
      have h2 := mul_le_mul_of_nonneg_left hch (by positivity : (0 : ℝ) ≤ 2 * box 1 0)
      linarith
    have h3 := mul_le_mul hcos h1 (by positivity) (by positivity)
    rw [show ‖z‖ * (‖2 * Complex.cos (l * z)‖ * ‖ghatC (box 1) 1 z‖) =
      ‖2 * Complex.cos (l * z)‖ * (‖z‖ * ‖ghatC (box 1) 1 z‖) by ring]
    exact h3

/-- **`H_l` is in the strip class** of `WeilForm.weilExplicit_zeta`. -/
lemma stripTest_HP1 {l : ℝ} (hl : 0 ≤ l) : ∃ C, StripTest (HP1 l) C := by
  obtain ⟨K, hK⟩ := ghat_twin_strip hl
  have hd := ghatC_differentiable (twin_probe (box_probe 1) hl).intervalIntegrable
  refine ⟨2 * K, ⟨fun t _ => ?_, fun t ht => ?_⟩⟩
  · exact (((hd.comp (differentiable_id.add_const _)).pow 2).add
      ((hd.comp (differentiable_id.sub_const _)).pow 2)).differentiableAt.differentiableWithinAt
  · have hp : |(t + I / 2).im| ≤ 3 / 2 := by
      have := ht.1; have := ht.2; simp only [Complex.add_im, Complex.div_ofNat_im, Complex.I_im]
      rw [abs_le]; constructor <;> linarith
    have hm : |(t - I / 2).im| ≤ 3 / 2 := by
      have := ht.1; have := ht.2; simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.I_im]
      rw [abs_le]; constructor <;> linarith
    have e1 : (t + I / 2).re = t.re := by simp
    have e2 : (t - I / 2).re = t.re := by simp
    have h1 := hK _ hp
    have h2 := hK _ hm
    rw [e1] at h1
    rw [e2] at h2
    have hpos : 0 < 1 + t.re ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    unfold HP1
    calc ‖ghatC (twin (box 1) l) (l + 1) (t + I / 2) ^ 2 + ghatC (twin (box 1) l) (l + 1) (t - I / 2) ^ 2‖ *
          (1 + t.re ^ 2)
        ≤ (‖ghatC (twin (box 1) l) (l + 1) (t + I / 2)‖ ^ 2 +
            ‖ghatC (twin (box 1) l) (l + 1) (t - I / 2)‖ ^ 2) * (1 + t.re ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos.le
          rw [← norm_pow, ← norm_pow]; exact norm_add_le _ _
      _ ≤ 2 * K := by linarith

/-- **Weil's explicit formula for `H_l`** over the zeros of `ζ`. -/
lemma hasSum_zeta {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun q : ZIdx => HP1 l ((zetaZeroFamily q - 1 / 2) / I)) ((QP1 l : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := stripTest_HP1 hl
  obtain ⟨-, hS⟩ := weilExplicit_zeta hC (HP1_even hl) (HP1_real hl)
  convert hS using 1
  unfold QP1
  push_cast
  rw [← pole_real hl]

/-! ## The zeros of `ℙ¹` and their weights -/

/-- The weight `G(p) = ĝ₀(p/i)²` of a pole `p`, `ĝ₀` the transform of the box. -/
def Gw (p : ℂ) : ℂ := ghatC (box 1) 1 (p / I) ^ 2

/-- The weight of the zero `ρ′` of `ℙ¹`: `ĝ₀(t′)²` with `t′ = (ρ′ − 1)/i`. -/
def cw (q : ZIdx ⊕ ZIdx) : ℂ := Gw (poleP1 q)

/-- `‖ĝ₀(t′)‖² ≤ 8cosh²1·|1/(ρ′(2 − ρ′))|` for the poles off the unit disc. -/
lemma norm_cw_le (q : ZIdx ⊕ ZIdx) (hq : 1 < ‖poleP1 q‖) : ‖cw q‖ ≤ 8 * Real.cosh 1 ^ 2 * ‖gP1 (poleP1 q)‖ := by
  set P := poleP1 q with hPdef
  have hP0 : P ≠ 0 := fun h => by rw [h, norm_zero] at hq; linarith
  have hI0 : P / I ≠ 0 := div_ne_zero hP0 I_ne_zero
  have h0 := norm_ghatC_le_of_antitone one_pos (box_probe 1).even box_antitone box_nonneg hI0
  have hbox : box 1 0 = 1 / Real.sqrt 2 := by rw [box_apply]; norm_num
  have him : |(P / I).im| = |P.re| := by simp
  have hch : Real.cosh (1 * |(P / I).im|) ≤ Real.cosh 1 := by
    rw [Real.cosh_le_cosh, one_mul, abs_abs, him, abs_one]; exact (abs_re_poleP1 q).le
  have hnP : ‖P / I‖ = ‖P‖ := by rw [norm_div, Complex.norm_I, div_one]
  have hPpos : 0 < ‖P‖ := by linarith
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  -- `‖ĝ₀(P/i)‖ ≤ √2·cosh 1/‖P‖`
  have hg : ‖ghatC (box 1) 1 (P / I)‖ ≤ Real.sqrt 2 * Real.cosh 1 / ‖P‖ := by
    refine h0.trans ?_
    rw [hnP, hbox]
    apply div_le_div_of_nonneg_right _ hPpos.le
    have e : 2 * (1 / Real.sqrt 2) = Real.sqrt 2 := by
      field_simp; rw [Real.sq_sqrt zero_le_two]
    rw [e]
    exact mul_le_mul_of_nonneg_left hch hs2.le
  -- `‖gP1 P‖ = 1/‖1 − P²‖ ≥ 1/(4‖P‖²)`
  have hg1 : gP1 P = 1 / (1 - P ^ 2) := by
    rw [hPdef, gP1_poleP1, show zP1 q = poleP1 q + 1 by unfold poleP1; ring]; ring_nf
  have hn1 : ‖1 - P ^ 2‖ ≤ 4 * ‖P‖ ^ 2 := by
    have e : 1 - P ^ 2 = (1 - P) * (1 + P) := by ring
    rw [e, norm_mul]
    have a1 : ‖1 - P‖ ≤ 1 + ‖P‖ := (norm_sub_le _ _).trans (by rw [norm_one])
    have a2 : ‖1 + P‖ ≤ 1 + ‖P‖ := (norm_add_le _ _).trans (by rw [norm_one])
    nlinarith [norm_nonneg (1 - P), norm_nonneg (1 + P)]
  have hne : 1 - P ^ 2 ≠ 0 := by
    intro h
    have e : (1 - P) * (1 + P) = 0 := by linear_combination h
    rcases mul_eq_zero.1 e with h' | h'
    · have hP1 : P = 1 := by linear_combination -h'
      have him0 := im_poleP1_ne q
      rw [← hPdef, hP1] at him0; simp at him0
    · have hP1 : P = -1 := by linear_combination h'
      have him0 := im_poleP1_ne q
      rw [← hPdef, hP1] at him0; simp at him0
  have hn1pos : 0 < ‖1 - P ^ 2‖ := norm_pos_iff.2 hne
  unfold cw Gw
  rw [← hPdef, norm_pow, hg1, norm_div, norm_one]
  calc ‖ghatC (box 1) 1 (P / I)‖ ^ 2 ≤ (Real.sqrt 2 * Real.cosh 1 / ‖P‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hg 2
    _ = 2 * Real.cosh 1 ^ 2 / ‖P‖ ^ 2 := by rw [div_pow, mul_pow, Real.sq_sqrt zero_le_two]
    _ ≤ 8 * Real.cosh 1 ^ 2 * (1 / ‖1 - P ^ 2‖) := by
        rw [div_le_iff₀ (by positivity)]
        have hc : 0 ≤ Real.cosh 1 ^ 2 := sq_nonneg _
        have := mul_le_mul_of_nonneg_left hn1 (by positivity : (0 : ℝ) ≤ 2 * Real.cosh 1 ^ 2 / ‖1 - P ^ 2‖)
        calc 2 * Real.cosh 1 ^ 2 = 2 * Real.cosh 1 ^ 2 / ‖1 - P ^ 2‖ * ‖1 - P ^ 2‖ := by field_simp
          _ ≤ 2 * Real.cosh 1 ^ 2 / ‖1 - P ^ 2‖ * (4 * ‖P‖ ^ 2) := this
          _ = 8 * Real.cosh 1 ^ 2 * (1 / ‖1 - P ^ 2‖) * ‖P‖ ^ 2 := by ring

/-- **The weights are summable**, by comparison with `PurityRational.summable_wP1`. -/
lemma summable_cw : Summable fun q : ZIdx ⊕ ZIdx => ‖cw q‖ := by
  refine Summable.of_norm_bounded_eventually (summable_wP1.mul_left (8 * Real.cosh 1 ^ 2)) ?_
  have hfin := finite_poleP1 1
  filter_upwards [hfin.compl_mem_cofinite] with q hq
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hq
  rw [norm_norm]
  exact norm_cw_le q hq

/-- The poles of `ℙ¹` with the box weights. -/
lemma twinPoles : TwinLandau.TwinPoles poleP1 cw :=
  ⟨summable_cw, abs_re_poleP1, im_poleP1_ne, finite_poleP1⟩

/-- **One zero of `ζ`, two zeros of `ℙ¹`**: `H_l(t_ρ)` is the twin term of `ρ′ = ρ` plus that of `ρ′ = ρ + 1`. -/
lemma HP1_zero {l : ℝ} (hl : 0 ≤ l) (q : ZIdx) :
    HP1 l ((zetaZeroFamily q - 1 / 2) / I) =
      TwinLandau.wq poleP1 cw (Sum.inl q) (2 * l) + TwinLandau.wq poleP1 cw (Sum.inr q) (2 * l) := by
  have term : ∀ p : ℂ, ghatC (twin (box 1) l) (l + 1) (p / I) ^ 2 =
      Gw p * (2 + cexp (((2 * l : ℝ) : ℂ) * p) + cexp (-(((2 * l : ℝ) : ℂ) * p))) := fun p => by
    rw [ghatC_twin one_pos (box_probe 1) hl, TwinLandau.twin_sq]
    have e : (l : ℂ) * (2 * I * (p / I)) = ((2 * l : ℝ) : ℂ) * p := by
      push_cast; field_simp
    rw [e]; rfl
  have e1 : (zetaZeroFamily q - 1 / 2) / I + I / 2 = poleP1 (Sum.inl q) / I := by
    simp only [poleP1, zP1, Sum.elim_inl]; rw [div_I, div_I]; ring
  have e2 : (zetaZeroFamily q - 1 / 2) / I - I / 2 = poleP1 (Sum.inr q) / I := by
    simp only [poleP1, zP1, Sum.elim_inr]; rw [div_I, div_I]; ring
  unfold HP1 TwinLandau.wq cw
  rw [e1, e2, term, term]

/-- **The explicit formula for the twins of `ℙ¹`**: the form `QP1(l)` from the primes is the sum over the zeros `ρ′` of
`ℙ¹` of `ĝ₀(t′)²(2 + e^{2lP} + e^{−2lP})`, `P = ρ′ − 1`. -/
theorem explicit_formula {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun q : ZIdx ⊕ ZIdx => TwinLandau.wq poleP1 cw q (2 * l)) ((QP1 l : ℝ) : ℂ) := by
  have hs : Summable fun q : ZIdx ⊕ ZIdx => TwinLandau.wq poleP1 cw q (2 * l) :=
    (summable_cw.mul_right _).of_norm_bounded fun q => TwinLandau.norm_wq_le twinPoles q (2 * l)
  have hA := (hs.comp_injective Sum.inl_injective).hasSum
  have hB := (hs.comp_injective Sum.inr_injective).hasSum
  have hAB := hA.add hB
  have hZ := hasSum_zeta hl
  have e : (fun q : ZIdx => HP1 l ((zetaZeroFamily q - 1 / 2) / I)) =
      fun q => ((fun q => TwinLandau.wq poleP1 cw q (2 * l)) ∘ Sum.inl) q +
        ((fun q => TwinLandau.wq poleP1 cw q (2 * l)) ∘ Sum.inr) q := by
    funext q; exact HP1_zero hl q
  rw [e] at hZ
  rw [hZ.unique hAB]
  exact hA.sum hB

/-! ## The rate -/

/-- **The `ℙ¹` data of the twin-form Landau argument**, in the variable `λ = 2l`. -/
lemma twinData : TwinLandau.TwinData poleP1 cw Gw (fun x => QP1 (x / 2)) where
  toTwinPoles := twinPoles
  c_eq _ := rfl
  G_even p := by unfold Gw; rw [neg_div, ghatC_even (box_probe 1).even]
  G_ne p hp := by
    refine pow_ne_zero 2 (ghat_box_ne ?_)
    have e : (p / I).im = -p.re := by simp
    rw [e]; intro h; linarith
  hasSum x hx := by
    have h := explicit_formula (l := x / 2) (by linarith)
    rw [show 2 * (x / 2) = x by ring] at h
    exact h

/-- **The rate of `ℙ¹`'s twin defect**: `QP1(l) ≥ −Ce^{σl}` for some `C` and all `l ≥ 0` if and only if every
nontrivial zero of `ζ` has `|2 Re ρ − 1| ≤ σ − 1`. -/
theorem rate_iff {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QP1 l) ↔
      ∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ - 1 := by
  have key := TwinLandau.rate_iff twinData (σ := σ / 2) (by positivity)
  have hL : (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QP1 l) ↔
      ∃ C, ∀ x : ℝ, 0 ≤ x → -(C * Real.exp (σ / 2 * x)) ≤ QP1 (x / 2) := by
    constructor
    · rintro ⟨C, h⟩
      exact ⟨C, fun x hx => by
        have := h (x / 2) (by linarith); rwa [show σ * (x / 2) = σ / 2 * x by ring] at this⟩
    · rintro ⟨C, h⟩
      exact ⟨C, fun l hl => by
        have := h (2 * l) (by linarith)
        rwa [show σ / 2 * (2 * l) = σ * l by ring, show 2 * l / 2 = l by ring] at this⟩
  have hR : (∀ q : ZIdx ⊕ ZIdx, |(poleP1 q).re| ≤ σ / 2) ↔
      ∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ - 1 := by
    constructor
    · intro h s hs
      have h1 := h (Sum.inl ⟨⟨s, hs⟩, ⟨0, zeroMult_pos _⟩⟩)
      have h2 := h (Sum.inr ⟨⟨s, hs⟩, ⟨0, zeroMult_pos _⟩⟩)
      rw [re_poleP1] at h1 h2
      simp only [zP1, Sum.elim_inl, Sum.elim_inr, Complex.add_re, Complex.one_re] at h1 h2
      change |s.re - 1| ≤ σ / 2 at h1
      change |s.re + 1 - 1| ≤ σ / 2 at h2
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · intro h q
      rw [re_poleP1]
      rcases q with q | q
      · have := h _ (nontrivial_zZF q)
        simp only [zP1, Sum.elim_inl]
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
      · have := h _ (nontrivial_zZF q)
        simp only [zP1, Sum.elim_inr, Complex.add_re, Complex.one_re]
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
  rw [hL, key, hR]

/-- **The rate of `ℙ¹` is that of `ζ` plus one**: for `σ ≥ 1`, `QP1(l) ≥ −Ce^{σl}` for some `C` if and only if Weil's
form of `ζ` on the same twin boxes has `Q(g_l) ≥ −C′e^{(σ − 1)l}` for some `C′`. -/
theorem rate_iff_zeta {σ : ℝ} (hσ : 1 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QP1 l) ↔
      ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp ((σ - 1) * l)) ≤ weilQ (l + 1) (twin (box 1) l) := by
  rw [rate_iff (by linarith), weil_twins_rate (by linarith)]

/-- **The defect of `ℙ¹` is never subexponential**, with no hypothesis: where `WeilForm.rh_iff_twins_subexp` asks
for `ζ`, the twin form of `ℙ¹` cannot be bounded below by `−Ce^{σl}` for every `σ > 0`. -/
theorem not_subexp : ¬ ∀ σ > 0, ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ QP1 l := by
  intro h
  have hr := (rate_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).1 (h (1 / 2) (by norm_num))
  have := ZerosInfinite.infinite_ZIdx
  obtain ⟨q⟩ := (inferInstance : Nonempty ZIdx)
  have h1 := hr _ (nontrivial_zZF q)
  have h2 := abs_nonneg (2 * (zetaZeroFamily q).re - 1)
  linarith

/-- **RH is the least rate for `ℙ¹`**: Mathlib's `RiemannHypothesis` holds if and only if the twin form of `ℙ¹` has
defect `O(e^l)`. -/
theorem rh_iff_rate_one :
    RiemannHypothesis ↔ ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp l) ≤ QP1 l := by
  have h := rate_iff (σ := 1) zero_le_one
  simp only [one_mul, sub_self] at h
  rw [h]
  constructor
  · intro hRH s hs
    have h1 : s ≠ 1 := fun e => by have := hs.re_lt_one; rw [e, one_re] at this; exact lt_irrefl _ this
    rw [hRH s hs.1 hs.2 h1]; norm_num
  · intro h s hs htriv _
    have := h s ⟨hs, htriv⟩
    have h0 := abs_nonneg (2 * s.re - 1)
    have : 2 * s.re - 1 = 0 := abs_eq_zero.1 (le_antisymm this h0)
    linarith

end PurityTwins

#print axioms PurityTwins.explicit_formula
#print axioms PurityTwins.rate_iff
#print axioms PurityTwins.rate_iff_zeta
#print axioms PurityTwins.not_subexp
#print axioms PurityTwins.rh_iff_rate_one
