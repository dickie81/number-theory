/-
# The ladder of `ζ(s)ζ(s − k)`: RH as the least rate of an impure twin form

Plain statement. `PurityTwins` builds Weil's form of `ℙ¹`, the zeta function `ζ(s)ζ(s − 1)`, on the twin boxes
`g_l = twin (box 1) l` from the primes and proves that its rate is `ζ`'s plus one. The same holds for every
`ζ(s)ζ(s − k)`, `k ∈ ℕ`, with `k` in place of one: its zeros are the `ρ` and the `ρ + k`, and its line is
`Re s = (k + 1)/2`.
* **The test function** (`Hk`): `H_l(t) = ĝ_l(t + ik/2)² + ĝ_l(t − ik/2)²`. At `t = t_ρ = (ρ − ½)/i` the two terms are
  `ĝ_l(t′)²` at `t′ = (ρ′ − (k + 1)/2)/i` for `ρ′ = ρ` and `ρ′ = ρ + k`. `H_l` is even, real on `ℝ`, and in the strip
  class of `WeilForm.weilExplicit_zeta`, since `‖ĝ_l(z)‖²(1 + (Re z)²)` is bounded on `|Im z| ≤ 1 + k/2`
  (`ghat_twin_strip`).
* **The form** (`Qk`): the right side of Weil's explicit formula for `H_l`, built from the primes with no zero in it;
  `PurityTwins.QP1` is the case `k = 1` (`Qk_one`). By the explicit formula it is the sum over the zeros `ρ′` of
  `ζ(s)ζ(s − k)` of `ĝ₀(t′)²(2 + e^{2lP} + e^{−2lP})`, `P = ρ′ − (k + 1)/2` (`explicit_formula_k`).
* **The rate** (`rate_iff_k`): `Qk(l) ≥ −Ce^{σl}` for some `C` and all `l ≥ 0` if and only if every nontrivial zero has
  `|2 Re ρ − 1| ≤ σ − k`, so that the rate of `ζ(s)ζ(s − k)` is `ζ`'s plus `k` (`rate_iff_zeta_k`). Of the two poles
  `ρ − (k + 1)/2` and `ρ + (k − 1)/2` of a zero `ρ`, the one farther from the imaginary axis has
  `|Re P| = k/2 + |Re ρ − ½|`. The Landau argument (`TwinLandau.rate_iff`) runs on the poles divided by `(k + 1)/2`, so
  that `|Re P| < 1`, in the variable `(k + 1)l`.
* So **for `k ≥ 1` the defect is never subexponential** (`not_subexp_k`), and for every `k`, **RH holds exactly when the
  defect of `ζ(s)ζ(s − k)` is `O(e^{kl})`**, the least rate it can have (`rh_iff_rate_k`): a ladder of criteria for RH,
  one for each product. Its rung `k = 0`, `ζ(s)²`, is `ζ`'s own twin form at rate zero (`WeilForm.weil_twins_rate` at
  `σ = 0`), and its rung `k = 1` is `PurityTwins.rh_iff_rate_one`.
-/
import PurityTwins

open Real Complex Filter Topology Set WeilForm WeilTest WeilStrip

noncomputable section

namespace PurityLadder

open PurityRational

variable (k : ℕ)

/-! ## The test function -/

/-- **The test function of `ζ(s)ζ(s − k)`**: `H_l(t) = ĝ_l(t + ik/2)² + ĝ_l(t − ik/2)²` for the twin boxes
`g_l = twin (box 1) l` on `[−(l + 1), l + 1]`. -/
def Hk (l : ℝ) (t : ℂ) : ℂ :=
  ghatC (twin (box 1) l) (l + 1) (t + I * k / 2) ^ 2 + ghatC (twin (box 1) l) (l + 1) (t - I * k / 2) ^ 2

/-- `H_l` on the real line, where it is real (`Hk_conj`). -/
def HkR (l r : ℝ) : ℝ := (Hk k l r).re

/-- **The twin form of `ζ(s)ζ(s − k)`, from the primes**: the right side of Weil's explicit formula for `H_l`, with the
pole terms `H_l(±i/2)`, the constant `−g_H(0)log π`, the archimedean integral and the prime sum. -/
def Qk (l : ℝ) : ℝ :=
  (Hk k l (I / 2) + Hk k l (-(I / 2))).re + (-(gh (HkR k l) 0 * Real.log π) +
    1 / (2 * π) * (∫ r, HkR k l r * psiRe r) -
    2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh (HkR k l) (Real.log n))

/-- **The first rung is `ℙ¹`**: `Qk 1` is `PurityTwins.QP1`. -/
theorem Qk_one : Qk 1 = PurityTwins.QP1 := by
  have hH : Hk 1 = PurityTwins.HP1 := by
    funext l t
    simp [Hk, PurityTwins.HP1]
  funext l
  unfold Qk PurityTwins.QP1 HkR PurityTwins.HP1R
  rw [hH]

variable {k}

lemma Hk_conj {l : ℝ} (hl : 0 ≤ l) (t : ℂ) : Hk k l ((starRingEnd ℂ) t) = (starRingEnd ℂ) (Hk k l t) := by
  have hc := ghatC_conj (PurityTwins.twin_even hl) (a := l + 1) (by linarith)
  have e1 : (starRingEnd ℂ) t + I * k / 2 = (starRingEnd ℂ) (t - I * k / 2) := by
    rw [map_sub, map_div₀, map_mul, Complex.conj_I, Complex.conj_natCast, map_ofNat]; ring
  have e2 : (starRingEnd ℂ) t - I * k / 2 = (starRingEnd ℂ) (t + I * k / 2) := by
    rw [map_add, map_div₀, map_mul, Complex.conj_I, Complex.conj_natCast, map_ofNat]; ring
  unfold Hk
  rw [e1, e2, hc, hc, map_add, map_pow, map_pow, add_comm]

lemma Hk_real {l : ℝ} (hl : 0 ≤ l) (r : ℝ) : Hk k l r = ((HkR k l r : ℝ) : ℂ) := by
  have h := Hk_conj (k := k) hl (r : ℂ)
  rw [Complex.conj_ofReal] at h
  refine Complex.ext rfl ?_
  have him := congrArg Complex.im h
  rw [Complex.conj_im] at him
  simp only [Complex.ofReal_im]
  linarith

lemma Hk_even {l : ℝ} (hl : 0 ≤ l) (t : ℂ) : Hk k l (-t) = Hk k l t := by
  unfold Hk
  rw [show -t + I * k / 2 = -(t - I * k / 2) by ring, show -t - I * k / 2 = -(t + I * k / 2) by ring,
    even_ghat_sq (PurityTwins.twin_even hl), even_ghat_sq (PurityTwins.twin_even hl), add_comm]

/-- The pole terms are real. -/
lemma pole_real {l : ℝ} (hl : 0 ≤ l) :
    Hk k l (I / 2) + Hk k l (-(I / 2)) = (((Hk k l (I / 2) + Hk k l (-(I / 2))).re : ℝ) : ℂ) := by
  have h := Hk_conj (k := k) hl (I / 2)
  rw [map_div₀, Complex.conj_I, map_ofNat, neg_div] at h
  rw [h]
  refine Complex.ext rfl ?_
  simp

/-! ## The strip class -/

variable (k) in
/-- `ĝ_l` on `|Im z| ≤ 1 + k/2`: `‖ĝ_l(z)‖²(1 + (Re z)²) ≤ K`. -/
lemma ghat_twin_strip {l : ℝ} (hl : 0 ≤ l) : ∃ K, ∀ z : ℂ, |z.im| ≤ 1 + k / 2 →
    ‖ghatC (twin (box 1) l) (l + 1) z‖ ^ 2 * (1 + z.re ^ 2) ≤ K := by
  have hint := (box_probe 1).intervalIntegrable
  set Y : ℝ := 1 + k / 2
  have hY0 : 0 ≤ Y := by positivity
  set τ0 := 2 * Real.exp (l * Y) * (Real.exp Y * ∫ u in (-1 : ℝ)..1, |box 1 u|)
  set τ1 := 2 * Real.exp (l * Y) * (2 * box 1 0 * Real.cosh Y)
  refine ⟨τ0 ^ 2 + τ1 ^ 2, fun z hz => ?_⟩
  have hcos : ‖2 * Complex.cos (l * z)‖ ≤ 2 * Real.exp (l * Y) := by
    refine (norm_two_cos_le _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
    have e : ((l : ℂ) * z).im = l * z.im := by simp [Complex.mul_im]
    rw [e, abs_mul, abs_of_nonneg hl]
    exact mul_le_mul_of_nonneg_left hz hl
  refine sq_strip_bound (G := ghatC (twin (box 1) l) (l + 1)) ?_ ?_
  · rw [ghatC_twin one_pos (box_probe 1) hl, norm_mul]
    have h0 := norm_ghatC_le_exp_im (g := box 1) zero_le_one hint z
    have h1 : Real.exp (1 * |z.im|) ≤ Real.exp Y := Real.exp_le_exp.2 (by linarith)
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
    have hch : Real.cosh (1 * |z.im|) ≤ Real.cosh Y := by
      rw [Real.cosh_le_cosh, one_mul, abs_abs, abs_of_nonneg hY0]
      exact hz
    have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have h1 : ‖z‖ * ‖ghatC (box 1) 1 z‖ ≤ 2 * box 1 0 * Real.cosh Y := by
      rw [le_div_iff₀ hz'] at h0
      have h2 := mul_le_mul_of_nonneg_left hch (by positivity : (0 : ℝ) ≤ 2 * box 1 0)
      linarith
    have h3 := mul_le_mul hcos h1 (by positivity) (by positivity)
    rw [show ‖z‖ * (‖2 * Complex.cos (l * z)‖ * ‖ghatC (box 1) 1 z‖) =
      ‖2 * Complex.cos (l * z)‖ * (‖z‖ * ‖ghatC (box 1) 1 z‖) by ring]
    exact h3

variable (k) in
/-- **`H_l` is in the strip class** of `WeilForm.weilExplicit_zeta`. -/
lemma stripTest_Hk {l : ℝ} (hl : 0 ≤ l) : ∃ C, StripTest (Hk k l) C := by
  obtain ⟨K, hK⟩ := ghat_twin_strip k hl
  have hd := ghatC_differentiable (twin_probe (box_probe 1) hl).intervalIntegrable
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨2 * K, ⟨fun t _ => ?_, fun t ht => ?_⟩⟩
  · exact (((hd.comp (differentiable_id.add_const _)).pow 2).add
      ((hd.comp (differentiable_id.sub_const _)).pow 2)).differentiableAt.differentiableWithinAt
  · have him : (I * (k : ℂ) / 2).im = k / 2 := by simp
    have hre : (I * (k : ℂ) / 2).re = 0 := by simp
    have hp : |(t + I * k / 2).im| ≤ 1 + k / 2 := by
      have := ht.1; have := ht.2
      rw [Complex.add_im, him, abs_le]; constructor <;> linarith
    have hm : |(t - I * k / 2).im| ≤ 1 + k / 2 := by
      have := ht.1; have := ht.2
      rw [Complex.sub_im, him, abs_le]; constructor <;> linarith
    have e1 : (t + I * k / 2).re = t.re := by rw [Complex.add_re, hre, add_zero]
    have e2 : (t - I * k / 2).re = t.re := by rw [Complex.sub_re, hre, sub_zero]
    have h1 := hK _ hp
    have h2 := hK _ hm
    rw [e1] at h1
    rw [e2] at h2
    have hpos : 0 < 1 + t.re ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    unfold Hk
    calc ‖ghatC (twin (box 1) l) (l + 1) (t + I * k / 2) ^ 2 + ghatC (twin (box 1) l) (l + 1) (t - I * k / 2) ^ 2‖ *
          (1 + t.re ^ 2)
        ≤ (‖ghatC (twin (box 1) l) (l + 1) (t + I * k / 2)‖ ^ 2 +
            ‖ghatC (twin (box 1) l) (l + 1) (t - I * k / 2)‖ ^ 2) * (1 + t.re ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos.le
          rw [← norm_pow, ← norm_pow]; exact norm_add_le _ _
      _ ≤ 2 * K := by linarith

variable (k) in
/-- **Weil's explicit formula for `H_l`** over the zeros of `ζ`. -/
lemma hasSum_zeta {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun q : ZIdx => Hk k l ((zetaZeroFamily q - 1 / 2) / I)) ((Qk k l : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := stripTest_Hk k hl
  obtain ⟨-, hS⟩ := weilExplicit_zeta hC (Hk_even hl) (Hk_real hl)
  convert hS using 1
  unfold Qk
  push_cast
  rw [← pole_real hl]

/-! ## The zeros of `ζ(s)ζ(s − k)` and their weights -/

variable (k)

/-- `κ = (k + 1)/2`: the line of `ζ(s)ζ(s − k)` is `Re s = κ`, and its nontrivial zeros lie in `|Re s − κ| < κ`. -/
def kap : ℝ := ((k : ℝ) + 1) / 2

lemma kap_pos : 0 < kap k := by unfold kap; positivity

/-- The zeros of `ζ(s)ζ(s − k)`: the nontrivial zeros `ρ` of `ζ` (left) and the `ρ + k` (right). -/
def zk : ZIdx ⊕ ZIdx → ℂ := Sum.elim zetaZeroFamily fun q => zetaZeroFamily q + k

/-- The pole variable centred on the line: `P = ρ′ − (k + 1)/2`. -/
def poleK (q : ZIdx ⊕ ZIdx) : ℂ := zk k q - (kap k : ℂ)

/-- The poles divided by `κ = (k + 1)/2`, so that `|Re P| < 1`. -/
def poleR (q : ZIdx ⊕ ZIdx) : ℂ := poleK k q / (kap k : ℂ)

/-- The weight of the zero `ρ′`: `ĝ₀(t′)²`, `t′ = (ρ′ − (k + 1)/2)/i`. -/
def cwK (q : ZIdx ⊕ ZIdx) : ℂ := PurityTwins.Gw (poleK k q)

lemma re_poleK_inl (q : ZIdx) : (poleK k (Sum.inl q)).re = (zetaZeroFamily q).re - kap k := by
  simp [poleK, zk]

lemma re_poleK_inr (q : ZIdx) : (poleK k (Sum.inr q)).re = (zetaZeroFamily q).re + k - kap k := by
  simp [poleK, zk]

lemma abs_re_poleK (q : ZIdx ⊕ ZIdx) : |(poleK k q).re| < kap k := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases q with q | q
  · have h0 := (nontrivial_zZF q).re_pos
    have h1 := (nontrivial_zZF q).re_lt_one
    rw [re_poleK_inl, abs_lt]
    unfold kap
    constructor <;> linarith
  · have h0 := (nontrivial_zZF q).re_pos
    have h1 := (nontrivial_zZF q).re_lt_one
    rw [re_poleK_inr, abs_lt]
    unfold kap
    constructor <;> linarith

lemma im_poleK_ne (q : ZIdx ⊕ ZIdx) : (poleK k q).im ≠ 0 := by
  rcases q with q | q <;> simpa [poleK, zk] using im_zetaZeroFamily_ne q

/-- `‖P₁‖ ≤ ‖P_k‖ + k + 1` for the poles `P₁` of `ℙ¹` (`PurityRational.poleP1`) of the same zero. -/
lemma norm_poleP1_le (q : ZIdx ⊕ ZIdx) : ‖poleP1 q‖ ≤ ‖poleK k q‖ + (k + 1) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases q with q | q
  · have e : poleP1 (Sum.inl q) = poleK k (Sum.inl q) + ((kap k - 1 : ℝ) : ℂ) := by
      simp only [poleP1, poleK, zP1, zk, Sum.elim_inl]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : |kap k - 1| ≤ k + 1 := by rw [abs_le]; unfold kap; constructor <;> linarith
    linarith
  · have e : poleP1 (Sum.inr q) = poleK k (Sum.inr q) + ((kap k - k : ℝ) : ℂ) := by
      simp only [poleP1, poleK, zP1, zk, Sum.elim_inr]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : |kap k - k| ≤ k + 1 := by rw [abs_le]; unfold kap; constructor <;> linarith
    linarith

lemma finite_poleK (R : ℝ) : {q : ZIdx ⊕ ZIdx | ‖poleK k q‖ ≤ R}.Finite :=
  (finite_poleP1 (R + (k + 1))).subset fun q hq => by
    simp only [mem_ofPred_eq] at hq ⊢
    linarith [norm_poleP1_le k q]

/-- `‖(P + a)(b − P)‖ ≤ 4‖P‖²` for real shifts `|a|, |b| ≤ ‖P‖`. -/
lemma norm_shift_mul_le {P : ℂ} {a b : ℝ} (ha : |a| ≤ ‖P‖) (hb : |b| ≤ ‖P‖) :
    ‖(P + a) * (b - P)‖ ≤ 4 * ‖P‖ ^ 2 := by
  rw [norm_mul]
  have h1 : ‖P + a‖ ≤ 2 * ‖P‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have h2 : ‖(b : ℂ) - P‖ ≤ 2 * ‖P‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  nlinarith [norm_nonneg (P + a), norm_nonneg ((b : ℂ) - P)]

/-- `‖ĝ₀(t′)‖² ≤ 8cosh²((k + 1)/2)·|1/(ρ″(2 − ρ″))|` off a finite set, `ρ″` the zero of `ℙ¹` of the same index. -/
lemma norm_cwK_le (q : ZIdx ⊕ ZIdx) (hq : (k : ℝ) + 2 ≤ ‖poleK k q‖) :
    ‖cwK k q‖ ≤ 8 * Real.cosh (kap k) ^ 2 * ‖gP1 (poleP1 q)‖ := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set P := poleK k q with hPdef
  have hPpos : 0 < ‖P‖ := by linarith
  have hP0 : P ≠ 0 := norm_pos_iff.1 hPpos
  have hI0 : P / I ≠ 0 := div_ne_zero hP0 I_ne_zero
  have h0 := norm_ghatC_le_of_antitone one_pos (box_probe 1).even box_antitone box_nonneg hI0
  have hbox : box 1 0 = 1 / Real.sqrt 2 := by rw [box_apply]; norm_num
  have him : |(P / I).im| = |P.re| := by simp
  have hch : Real.cosh (1 * |(P / I).im|) ≤ Real.cosh (kap k) := by
    rw [Real.cosh_le_cosh, one_mul, abs_abs, him, abs_of_pos (kap_pos k)]
    exact (abs_re_poleK k q).le
  have hnP : ‖P / I‖ = ‖P‖ := by rw [norm_div, Complex.norm_I, div_one]
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hg : ‖ghatC (box 1) 1 (P / I)‖ ≤ Real.sqrt 2 * Real.cosh (kap k) / ‖P‖ := by
    refine h0.trans ?_
    rw [hnP, hbox]
    apply div_le_div_of_nonneg_right _ hPpos.le
    have e : 2 * (1 / Real.sqrt 2) = Real.sqrt 2 := by
      field_simp; rw [Real.sq_sqrt zero_le_two]
    rw [e]
    exact mul_le_mul_of_nonneg_left hch hs2.le
  -- `‖ρ″(2 − ρ″)‖ ≤ 4‖P‖²`, `ρ″ = zP1 q`
  have hX : ‖zP1 q * (2 - zP1 q)‖ ≤ 4 * ‖P‖ ^ 2 := by
    rcases q with q | q
    · have e : zP1 (Sum.inl q) * (2 - zP1 (Sum.inl q)) = (P + (kap k : ℝ)) * ((2 - kap k : ℝ) - P) := by
        simp only [hPdef, poleK, zP1, zk, Sum.elim_inl]; push_cast; ring
      rw [e]
      refine norm_shift_mul_le ?_ ?_
      · rw [abs_of_pos (kap_pos k)]; unfold kap at *; linarith
      · rw [abs_le]; unfold kap at *; constructor <;> linarith
    · have e : zP1 (Sum.inr q) * (2 - zP1 (Sum.inr q)) = (P + (kap k - k + 1 : ℝ)) * ((kap k : ℝ) - P) := by
        simp only [hPdef, poleK, zP1, zk, Sum.elim_inr]; unfold kap; push_cast; ring
      rw [e]
      refine norm_shift_mul_le ?_ ?_
      · rw [abs_le]; unfold kap at *; constructor <;> linarith
      · rw [abs_of_pos (kap_pos k)]; unfold kap at *; linarith
  have hXne : zP1 q * (2 - zP1 q) ≠ 0 := by
    have hre := re_poleP1 q
    have habs := abs_re_poleP1 q
    rw [abs_lt] at habs
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp only [Complex.zero_re] at this; linarith
    · have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have hXpos : 0 < ‖zP1 q * (2 - zP1 q)‖ := norm_pos_iff.2 hXne
  unfold cwK PurityTwins.Gw
  rw [← hPdef, norm_pow, gP1_poleP1, norm_div, norm_one]
  calc ‖ghatC (box 1) 1 (P / I)‖ ^ 2 ≤ (Real.sqrt 2 * Real.cosh (kap k) / ‖P‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hg 2
    _ = 2 * Real.cosh (kap k) ^ 2 / ‖P‖ ^ 2 := by rw [div_pow, mul_pow, Real.sq_sqrt zero_le_two]
    _ ≤ 8 * Real.cosh (kap k) ^ 2 * (1 / ‖zP1 q * (2 - zP1 q)‖) := by
        rw [div_le_iff₀ (by positivity)]
        calc 2 * Real.cosh (kap k) ^ 2
            = 2 * Real.cosh (kap k) ^ 2 / ‖zP1 q * (2 - zP1 q)‖ * ‖zP1 q * (2 - zP1 q)‖ := by field_simp
          _ ≤ 2 * Real.cosh (kap k) ^ 2 / ‖zP1 q * (2 - zP1 q)‖ * (4 * ‖P‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hX (by positivity)
          _ = 8 * Real.cosh (kap k) ^ 2 * (1 / ‖zP1 q * (2 - zP1 q)‖) * ‖P‖ ^ 2 := by ring

/-- **The weights are summable**, by comparison with `PurityRational.summable_wP1`. -/
lemma summable_cwK : Summable fun q : ZIdx ⊕ ZIdx => ‖cwK k q‖ := by
  refine Summable.of_norm_bounded_eventually (summable_wP1.mul_left (8 * Real.cosh (kap k) ^ 2)) ?_
  have hfin := finite_poleK k ((k : ℝ) + 2)
  filter_upwards [hfin.compl_mem_cofinite] with q hq
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hq
  rw [norm_norm]
  exact norm_cwK_le k q hq.le

/-- The poles divided by `(k + 1)/2`, with the box weights. -/
lemma twinPoles : TwinLandau.TwinPoles (poleR k) (cwK k) where
  summ := summable_cwK k
  re_lt q := by
    rw [poleR, Complex.div_ofReal_re, abs_div, abs_of_pos (kap_pos k), div_lt_one (kap_pos k)]
    exact abs_re_poleK k q
  im_ne q := by
    rw [poleR, Complex.div_ofReal_im]
    exact div_ne_zero (im_poleK_ne k q) (kap_pos k).ne'
  finite R := (finite_poleK k (kap k * R)).subset fun q hq => by
    simp only [mem_ofPred_eq] at hq ⊢
    rw [poleR, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (kap_pos k),
      div_le_iff₀ (kap_pos k)] at hq
    linarith

/-- **One zero of `ζ`, two zeros of `ζ(s)ζ(s − k)`**: `H_l(t_ρ)` is the twin term of `ρ′ = ρ` plus that of
`ρ′ = ρ + k`, in the variable `(k + 1)l`. -/
lemma Hk_zero {l : ℝ} (hl : 0 ≤ l) (q : ZIdx) :
    Hk k l ((zetaZeroFamily q - 1 / 2) / I) =
      TwinLandau.wq (poleR k) (cwK k) (Sum.inl q) (((k : ℝ) + 1) * l) +
        TwinLandau.wq (poleR k) (cwK k) (Sum.inr q) (((k : ℝ) + 1) * l) := by
  have term : ∀ p : ℂ, ghatC (twin (box 1) l) (l + 1) (p / I) ^ 2 =
      PurityTwins.Gw p * (2 + cexp (((((k : ℝ) + 1) * l : ℝ) : ℂ) * (p / (kap k : ℂ))) +
        cexp (-(((((k : ℝ) + 1) * l : ℝ) : ℂ) * (p / (kap k : ℂ))))) := fun p => by
    rw [ghatC_twin one_pos (box_probe 1) hl, TwinLandau.twin_sq]
    have e : (l : ℂ) * (2 * I * (p / I)) = ((((k : ℝ) + 1) * l : ℝ) : ℂ) * (p / (kap k : ℂ)) := by
      unfold kap
      push_cast
      field_simp
    rw [e]; rfl
  have e1 : (zetaZeroFamily q - 1 / 2) / I + I * k / 2 = poleK k (Sum.inl q) / I := by
    simp only [poleK, zk, Sum.elim_inl, kap]; push_cast; rw [div_I, div_I]; ring
  have e2 : (zetaZeroFamily q - 1 / 2) / I - I * k / 2 = poleK k (Sum.inr q) / I := by
    simp only [poleK, zk, Sum.elim_inr, kap]; push_cast; rw [div_I, div_I]; ring
  unfold Hk TwinLandau.wq cwK poleR
  rw [e1, e2, term, term]

/-- **The explicit formula for the twins of `ζ(s)ζ(s − k)`**: the form `Qk(l)` from the primes is the sum over the
zeros `ρ′` of `ζ(s)ζ(s − k)` of `ĝ₀(t′)²(2 + e^{2lP} + e^{−2lP})`, `P = ρ′ − (k + 1)/2`, written in the variable
`(k + 1)l` and the poles `P/((k + 1)/2)`. -/
theorem explicit_formula_k {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun q : ZIdx ⊕ ZIdx => TwinLandau.wq (poleR k) (cwK k) q (((k : ℝ) + 1) * l)) ((Qk k l : ℝ) : ℂ) := by
  have hs : Summable fun q : ZIdx ⊕ ZIdx => TwinLandau.wq (poleR k) (cwK k) q (((k : ℝ) + 1) * l) :=
    ((summable_cwK k).mul_right _).of_norm_bounded fun q =>
      TwinLandau.norm_wq_le (twinPoles k) q (((k : ℝ) + 1) * l)
  have hA := (hs.comp_injective Sum.inl_injective).hasSum
  have hB := (hs.comp_injective Sum.inr_injective).hasSum
  have hAB := hA.add hB
  have hZ := hasSum_zeta k hl
  have e : (fun q : ZIdx => Hk k l ((zetaZeroFamily q - 1 / 2) / I)) =
      fun q => ((fun q => TwinLandau.wq (poleR k) (cwK k) q (((k : ℝ) + 1) * l)) ∘ Sum.inl) q +
        ((fun q => TwinLandau.wq (poleR k) (cwK k) q (((k : ℝ) + 1) * l)) ∘ Sum.inr) q := by
    funext q; exact Hk_zero k hl q
  rw [e] at hZ
  rw [hZ.unique hAB]
  exact hA.sum hB

/-! ## The rate -/

/-- **The data of the twin-form Landau argument** for `ζ(s)ζ(s − k)`, in the variable `y = (k + 1)l`. -/
lemma twinData : TwinLandau.TwinData (poleR k) (cwK k) (fun p => PurityTwins.Gw ((kap k : ℂ) * p))
    (fun y => Qk k (y / ((k : ℝ) + 1))) where
  toTwinPoles := twinPoles k
  c_eq q := by
    unfold cwK poleR
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 (kap_pos k).ne')]
  G_even p := by
    unfold PurityTwins.Gw
    rw [mul_neg, neg_div, ghatC_even (box_probe 1).even]
  G_ne p hp := by
    refine pow_ne_zero 2 (ghat_box_ne ?_)
    have e : ((kap k : ℂ) * p / I).im = -(kap k * p.re) := by simp [div_I]
    rw [e]
    have := mul_pos (kap_pos k) hp
    intro h; linarith
  hasSum y hy := by
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h := explicit_formula_k k (l := y / ((k : ℝ) + 1)) (div_nonneg hy hk1.le)
    rw [show ((k : ℝ) + 1) * (y / ((k : ℝ) + 1)) = y by field_simp] at h
    exact h

/-- **The rate of `ζ(s)ζ(s − k)`'s twin defect**: `Qk(l) ≥ −Ce^{σl}` for some `C` and all `l ≥ 0` if and only if every
nontrivial zero of `ζ` has `|2 Re ρ − 1| ≤ σ − k`. -/
theorem rate_iff_k {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ Qk k l) ↔
      ∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ - k := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have key := TwinLandau.rate_iff (twinData k) (σ := σ / ((k : ℝ) + 1)) (div_nonneg hσ hk1.le)
  have hL : (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ Qk k l) ↔
      ∃ C, ∀ y : ℝ, 0 ≤ y → -(C * Real.exp (σ / ((k : ℝ) + 1) * y)) ≤ Qk k (y / ((k : ℝ) + 1)) := by
    constructor
    · rintro ⟨C, h⟩
      exact ⟨C, fun y hy => by
        have := h (y / ((k : ℝ) + 1)) (div_nonneg hy hk1.le)
        rwa [show σ * (y / ((k : ℝ) + 1)) = σ / ((k : ℝ) + 1) * y by ring] at this⟩
    · rintro ⟨C, h⟩
      exact ⟨C, fun l hl => by
        have := h (((k : ℝ) + 1) * l) (by positivity)
        rwa [show σ / ((k : ℝ) + 1) * (((k : ℝ) + 1) * l) = σ * l by field_simp,
          show ((k : ℝ) + 1) * l / ((k : ℝ) + 1) = l by field_simp] at this⟩
  have hiff : ∀ q, |(poleR k q).re| ≤ σ / ((k : ℝ) + 1) ↔ |(poleK k q).re| ≤ σ / 2 := fun q => by
    rw [poleR, Complex.div_ofReal_re, abs_div, abs_of_pos (kap_pos k), div_le_div_iff₀ (kap_pos k) hk1]
    unfold kap
    constructor <;> intro h <;> nlinarith
  have hR : (∀ q : ZIdx ⊕ ZIdx, |(poleR k q).re| ≤ σ / ((k : ℝ) + 1)) ↔
      ∀ s, IsNontrivialZero s → |2 * s.re - 1| ≤ σ - k := by
    simp only [hiff]
    constructor
    · intro h s hs
      have h1 := h (Sum.inl ⟨⟨s, hs⟩, ⟨0, zeroMult_pos _⟩⟩)
      have h2 := h (Sum.inr ⟨⟨s, hs⟩, ⟨0, zeroMult_pos _⟩⟩)
      rw [re_poleK_inl] at h1
      rw [re_poleK_inr] at h2
      change |s.re - kap k| ≤ σ / 2 at h1
      change |s.re + k - kap k| ≤ σ / 2 at h2
      unfold kap at h1 h2
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · intro h q
      rcases q with q | q
      · have := h _ (nontrivial_zZF q)
        rw [re_poleK_inl]
        unfold kap
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
      · have := h _ (nontrivial_zZF q)
        rw [re_poleK_inr]
        unfold kap
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
  rw [hL, key, hR]

/-- **The rate of `ζ(s)ζ(s − k)` is that of `ζ` plus `k`**: for `σ ≥ k`, `Qk(l) ≥ −Ce^{σl}` for some `C` if and only
if Weil's form of `ζ` on the same twin boxes has `Q(g_l) ≥ −C′e^{(σ − k)l}` for some `C′`. -/
theorem rate_iff_zeta_k {σ : ℝ} (hσ : (k : ℝ) ≤ σ) :
    (∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ Qk k l) ↔
      ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp ((σ - k) * l)) ≤ weilQ (l + 1) (twin (box 1) l) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [rate_iff_k k (by linarith), weil_twins_rate (by linarith)]

variable {k} in
/-- **For `k ≥ 1` the defect of `ζ(s)ζ(s − k)` is never subexponential**, with no hypothesis. -/
theorem not_subexp_k (hk : 1 ≤ k) : ¬ ∀ σ > 0, ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (σ * l)) ≤ Qk k l := by
  intro h
  have hr := (rate_iff_k k (by norm_num : (0 : ℝ) ≤ 1 / 2)).1 (h (1 / 2) (by norm_num))
  have := ZerosInfinite.infinite_ZIdx
  obtain ⟨q⟩ := (inferInstance : Nonempty ZIdx)
  have h1 := hr _ (nontrivial_zZF q)
  have h2 := abs_nonneg (2 * (zetaZeroFamily q).re - 1)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- **The ladder**: for every `k`, Mathlib's `RiemannHypothesis` holds if and only if the twin form of `ζ(s)ζ(s − k)`
has defect `O(e^{kl})`, the least rate it can have. -/
theorem rh_iff_rate_k :
    RiemannHypothesis ↔ ∃ C, ∀ l : ℝ, 0 ≤ l → -(C * Real.exp (k * l)) ≤ Qk k l := by
  have h := rate_iff_k k (σ := k) (Nat.cast_nonneg k)
  simp only [sub_self] at h
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

end PurityLadder

#print axioms PurityLadder.Qk_one
#print axioms PurityLadder.explicit_formula_k
#print axioms PurityLadder.rate_iff_k
#print axioms PurityLadder.rate_iff_zeta_k
#print axioms PurityLadder.not_subexp_k
#print axioms PurityLadder.rh_iff_rate_k
