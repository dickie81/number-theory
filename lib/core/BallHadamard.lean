/-
# A kernel with a cusp: `K_H(r) = Σ_ρ r^{ρ − ½}/(ρ(1 − ρ))`

Plain statement. For `r > 0` let `K_H(r) = Σ_ρ r^{ρ − ½}/(ρ(1 − ρ))`, the sum over the nontrivial zeros `ρ` of `ζ` with
multiplicity (`kerH`). At `ρ = ½ + iγ` the term is `r^{iγ}/(¼ + γ²)`.
* `K_H(1) = 2 + γ_E − log 4π` (`kerH_one`), Hadamard's identity, and `K_H(1/r) = K_H(r)` (`kerH_inv`).
* Mathlib's `RiemannHypothesis` holds if and only if `K_H` is positive-definite on the positive rationals
  (`rh_iff_posDefH`), and if and only if it has a realization by similitudes (`rh_iff_realizationH`): the theorems of
  `BallKernel` and `BallLattice` for the Gaussian kernel `K`.
* Unlike `K`, `K_H` is not smooth at `1` in any realization: no `M` has `‖K_H(r) + K_H(1/r) − 2K_H(1)‖ ≤ M(log r)²`
  for `1 ≤ r ≤ 2` (`not_smooth`). So the obstruction of `BallLattice.tendsto_norm_sub_of_smooth`, which shows that no
  realization of `K` spans a lattice, does not apply to `K_H`.

* The weight `1/(ρ(1 − ρ))` is `G(P) = 4/(1 − P²)` at the pole `P = 2(ρ − ½)` of the twin form (`hG`), so the
  `2 × 2` minors of `K_H` are the twin sum of `TwinLandau` with these weights, and the converse is the Landau argument
  of `BallKernel.re_eq_zero_of_dense`. The weights are summable by Hadamard's identity.
* Under RH one realization is `ℓ²` of the zeros with `w_r = (r^ρ/|ρ|)_ρ` (`realizationH`, by
  `BallLattice.realizationOf`).
* Under RH, `2K_H(1) − K_H(r) − K_H(1/r) = Σ_ρ (2 − 2cos(γ log r))/(¼ + γ²)`. Each of the infinitely many zeros with
  `|γ| ≥ 1` (`ZerosInfinite.infinite_ZIdx`) gives at least `(log r)²·(2/5)` once `|γ log r| ≤ 1`, so the sum is not
  `O((log r)²)`.

The weights `1/(¼ + γ²)` decay like `γ^{−2}`, against the Gaussian `e^{−γ²/2}` of `K`: the cusp of `K_H` at `1` comes
from the zeros high up. This is the kernel suggested in `docs/ball-conjecture.md` after `BallLattice`. Whether the orbit
of a realization of `K_H` spans a lattice is not decided here: that needs the zeros to be dense enough, near every
height, which the library does not prove.
-/
import Mathlib
import BallLattice
import ZerosInfinite

open Real Complex Finset Filter Topology ComplexConjugate WeilForm WeilTest
open scoped ComplexOrder

noncomputable section

namespace BallHadamard

open BallKernel BallLattice

/-! ## The weights -/

/-- The weight in the pole variable, `G(P) = 4/(1 − P²)`: at `P = 2(ρ − ½)` it is `1/(ρ(1 − ρ))`. At `P = ±1`, where
no pole lies, it is set to `1`, so that `G` has no zero. -/
def hG (p : ℂ) : ℂ := if p ^ 2 = 1 then 1 else 4 / (1 - p ^ 2)

lemma hG_ne (p : ℂ) : hG p ≠ 0 := by
  unfold hG
  split_ifs with h
  · exact one_ne_zero
  · exact div_ne_zero four_ne_zero (sub_ne_zero.2 (Ne.symm h))

lemma hG_neg (p : ℂ) : hG (-p) = hG p := by unfold hG; rw [neg_sq]

lemma hG_poleP (q : ZIdx) : hG (poleP q) = 1 / (zetaZeroFamily q * (1 - zetaZeroFamily q)) := by
  have hne : poleP q ^ 2 ≠ 1 := fun h => by
    have hre := abs_re_poleP q
    have h' : (poleP q - 1) * (poleP q + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h1 | h1
    · rw [sub_eq_zero.1 h1] at hre; simp at hre
    · rw [eq_neg_of_add_eq_zero_left h1] at hre; simp at hre
  unfold hG
  simp only [hne, ↓reduceIte]
  rw [show 1 - poleP q ^ 2 = 4 * (zetaZeroFamily q * (1 - zetaZeroFamily q)) by unfold poleP; ring,
    div_mul_eq_div_div, div_self four_ne_zero]

/-- **The Hadamard weights are summable**: `Σ_ρ |1/(ρ(1 − ρ))| < ∞`, from Hadamard's identity. -/
lemma summable_hw : Summable fun q : ZIdx => ‖1 / (zetaZeroFamily q * (1 - zetaZeroFamily q))‖ :=
  summable_norm_iff.2 hadamard_zeta.summable

theorem twinPoles_hG : TwinLandau.TwinPoles poleP fun q => hG (poleP q) :=
  ⟨summable_hw.congr fun q => by rw [hG_poleP], abs_re_poleP, im_poleP_ne, finite_poleP⟩

/-! ## The kernel -/

/-- **The Hadamard kernel** `K_H(r) = Σ_ρ r^{ρ − ½}/(ρ(1 − ρ))`, with `r^{ρ − ½}` written `e^{(ρ − ½)log r}`. -/
def kerH (r : ℝ) : ℂ :=
  ∑' q : ZIdx, cexp ((zetaZeroFamily q - 1 / 2) * Real.log r) / (zetaZeroFamily q * (1 - zetaZeroFamily q))

/-- The kernel in the pole variable: `K_H(r) = Σ_ρ G(P)e^{(log r/2)P}`. -/
lemma kerH_eq (r : ℝ) : kerH r = ∑' q : ZIdx, hG (poleP q) * cexp ((Real.log r / 2 : ℝ) * poleP q) := by
  unfold kerH
  refine tsum_congr fun q => ?_
  rw [hG_poleP, one_div_mul_eq_div]
  congr 2
  unfold poleP
  push_cast
  ring

lemma summable_kerH (l : ℝ) : Summable fun q : ZIdx => hG (poleP q) * cexp (l * poleP q) :=
  TwinLandau.summable_cw_mul twinPoles_hG (B := Real.exp |l|) fun q => by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h := abs_re_poleP q
    have e : ((l : ℂ) * poleP q).re = l * (poleP q).re := by simp
    rw [e]
    calc l * (poleP q).re ≤ |l * (poleP q).re| := le_abs_self _
      _ = |l| * |(poleP q).re| := abs_mul _ _
      _ ≤ |l| * 1 := mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
      _ = |l| := mul_one _

/-- **`K_H(1)` is Hadamard's constant**: `K_H(1) = Σ_ρ 1/(ρ(1 − ρ)) = 2 + γ − log 4π`. -/
theorem kerH_one : kerH 1 = ((2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) : ℂ) := by
  unfold kerH
  rw [← hadamard_zeta.tsum_eq]
  refine tsum_congr fun q => ?_
  rw [Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- **The `2 × 2` minors are the twin sum**: `2K_H(1) + K_H(r) + K_H(1/r) = Σ_ρ G(P_ρ)(2 + e^{λP_ρ} + e^{−λP_ρ})` at
`λ = (log r)/2`. -/
theorem twin_eq_kerH (r : ℝ) :
    TwinLandau.Wsum poleP (fun q => hG (poleP q)) (Real.log r / 2) = 2 * kerH 1 + kerH r + kerH r⁻¹ := by
  unfold TwinLandau.Wsum TwinLandau.wq
  have h0 := summable_kerH 0
  have h1 := summable_kerH (Real.log r / 2)
  have h2 := summable_kerH (-(Real.log r / 2))
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h0
  have e : ∀ q : ZIdx, hG (poleP q) * (2 + cexp ((Real.log r / 2 : ℝ) * poleP q) +
      cexp (-((Real.log r / 2 : ℝ) * poleP q))) = 2 * hG (poleP q) +
      hG (poleP q) * cexp ((Real.log r / 2 : ℝ) * poleP q) +
      hG (poleP q) * cexp ((-(Real.log r / 2) : ℝ) * poleP q) := fun q => by
    push_cast; ring_nf
  rw [tsum_congr e, ((h0.mul_left 2).add h1).tsum_add h2, (h0.mul_left 2).tsum_add h1, tsum_mul_left,
    kerH_eq, kerH_eq, kerH_eq, Real.log_one, Real.log_inv]
  simp only [zero_div, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, neg_div]

/-- **The kernel is even**: `K_H(1/r) = K_H(r)`, as the zeros come in pairs `ρ, 1 − ρ` with the same weight. -/
theorem kerH_inv (r : ℝ) : kerH r⁻¹ = kerH r := by
  rw [kerH_eq, kerH_eq, Real.log_inv, ← zetaEquiv.symm.tsum_eq, ← zetaEquiv.symm.tsum_eq]
  set fl : Bool × ZeroIdx (sqF Xi) ≃ Bool × ZeroIdx (sqF Xi) := Equiv.prodCongr Equiv.boolNot (Equiv.refl _)
  rw [← fl.tsum_eq]
  refine tsum_congr fun p => ?_
  have hz : ∀ p, poleP (zetaEquiv.symm p) = 2 * (rhoXi p - 1 / 2) := fun p => by
    unfold poleP
    rw [← rhoXi_zetaEquiv, Equiv.apply_symm_apply]
  have h : rhoXi (fl p) - 1 / 2 = -(rhoXi p - 1 / 2) := by
    rcases p with ⟨b, i⟩
    cases b <;> simp [fl, rhoXi, Equiv.boolNot]
  rw [hz, hz, h, show 2 * -(rhoXi p - 1 / 2) = -(2 * (rhoXi p - 1 / 2)) by ring, hG_neg]
  congr 2
  push_cast
  ring

/-! ## The Riemann hypothesis as positive-definiteness -/

/-- **Positive-definite on `ℚ₊^×` gives the Riemann hypothesis**: the `2 × 2` minors are the twin sum, and the Landau
argument puts every pole on the imaginary axis. -/
theorem rh_of_posDefH (hK : PosDefQ kerH) : RiemannHypothesis := by
  have hW : ∀ r : ℚ, 0 < r → 0 ≤ TwinLandau.Wsum poleP (fun q => hG (poleP q)) ((1 / 2) * Real.log r) := by
    intro r hr
    rw [show (1 / 2 : ℝ) * Real.log r = Real.log r / 2 by ring, twin_eq_kerH]
    exact minor_nonneg hK hr
  have hline : ∀ q : ZIdx, (zetaZeroFamily q).re = 1 / 2 := fun q => by
    have h := re_eq_zero_of_dense twinPoles_hG (G := hG) (fun _ => rfl) hG_neg (fun p _ => hG_ne p) (by norm_num) hW q
    rw [re_poleP] at h
    linarith
  intro s hs htriv _
  exact hline ⟨⟨s, hs, htriv⟩, ⟨0, zeroMult_pos _⟩⟩

/-- The weights `c_ρ = |ρ(1 − ρ)|^{−1/2}` of the realization. -/
def cH (q : ZIdx) : ℂ := (Real.sqrt ‖zetaZeroFamily q * (1 - zetaZeroFamily q)‖⁻¹ : ℝ)

lemma summable_cH_sq : Summable fun q => ‖cH q‖ ^ 2 := by
  refine summable_hw.congr fun q => ?_
  unfold cH
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (inv_nonneg.2 (norm_nonneg _)),
    norm_div, norm_one, one_div]

/-- Under RH, `a^ρ/|ρ|` paired with `b^ρ/|ρ|` is `√(ab)·(a/b)^{iγ}/(¼ + γ²)`. -/
lemma gram_cH (hRH : RiemannHypothesis) (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    ∑' q, cH q * pw q a * conj (cH q * pw q b) = (Real.sqrt ((a : ℝ) * b) : ℂ) * kerH ((a : ℝ) / b) := by
  unfold kerH
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  set t : ℝ := (zetaZeroFamily q).im with ht
  have hline : zetaZeroFamily q = 1 / 2 + I * t := by
    have h := line_of_RH hRH q
    apply Complex.ext <;> simp [ht, h]
  have hrr : zetaZeroFamily q * (1 - zetaZeroFamily q) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    rw [hline]
    push_cast
    linear_combination (-(t : ℂ) ^ 2) * Complex.I_sq
  have hpos : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hc : conj (cH q) * cH q = ((1 / 4 + t ^ 2 : ℝ) : ℂ)⁻¹ := by
    unfold cH
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (inv_nonneg.2 (norm_nonneg _)), hrr,
      Complex.norm_real, Real.norm_of_nonneg hpos.le, Complex.ofReal_inv]
  have hsq : (Real.sqrt ((a : ℝ) * b) : ℂ) = cexp ((Real.log a + Real.log b) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (mul_pos ha0 hb0), Real.log_mul ha0.ne' hb0.ne']
    push_cast
    ring_nf
  have hp : pw q a * conj (pw q b) = (Real.sqrt ((a : ℝ) * b) : ℂ) *
      cexp ((zetaZeroFamily q - 1 / 2) * Real.log ((a : ℝ) / b)) := by
    unfold pw
    rw [hsq, hline, Real.log_div ha0.ne' hb0.ne', ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hrr]
  calc cH q * pw q a * conj (cH q * pw q b) = (conj (cH q) * cH q) * (pw q a * conj (pw q b)) := by
        rw [map_mul]; ring
    _ = _ := by rw [hc, hp]; field_simp

/-- **Under RH, `K_H` has a realization**: `ℓ²` of the zeros with `w_r = (r^ρ/|ρ|)_ρ` and `φ_n` multiplying the
coordinate of `ρ` by `n^ρ`. -/
def realizationH (hRH : RiemannHypothesis) : Realization kerH :=
  realizationOf hRH cH summable_cH_sq (gram_cH hRH)

/-- **The Riemann hypothesis is positive-definiteness of `K_H` on the positive rationals**: Mathlib's
`RiemannHypothesis` holds if and only if `Σ_{a,b ∈ S} x_a x̄_b K_H(a/b) ≥ 0` for every finite set `S` of positive
rationals and all complex `x`. -/
theorem rh_iff_posDefH : RiemannHypothesis ↔ PosDefQ kerH :=
  ⟨fun h => posDefQ_of_realization (realizationH h), rh_of_posDefH⟩

/-- **The Riemann hypothesis is the existence of a realization of `K_H`** by similitudes. -/
theorem rh_iff_realizationH : RiemannHypothesis ↔ Nonempty (Realization kerH) :=
  ⟨fun h => ⟨realizationH h⟩, fun ⟨R⟩ => rh_of_posDefH (posDefQ_of_realization R)⟩

/-! ## `K_H` is not smooth at `1` -/

/-- Under RH, `K_H(r) + K_H(1/r) − 2K_H(1) = −Σ_ρ (2 − 2cos(γ log r))/(¼ + γ²)`. -/
lemma kerH_second_diff (hRH : RiemannHypothesis) (r : ℝ) :
    kerH r + kerH r⁻¹ - 2 * kerH 1 = -(((∑' q : ZIdx, (2 - 2 * Real.cos ((zetaZeroFamily q).im * Real.log r)) /
      (1 / 4 + (zetaZeroFamily q).im ^ 2) : ℝ)) : ℂ) := by
  have hW := twin_eq_kerH r
  have hW0 := twin_eq_kerH 1
  rw [Real.log_one, zero_div, inv_one] at hW0
  have e : kerH r + kerH r⁻¹ - 2 * kerH 1 = TwinLandau.Wsum poleP (fun q => hG (poleP q)) (Real.log r / 2) -
      TwinLandau.Wsum poleP (fun q => hG (poleP q)) 0 := by rw [hW, hW0]; ring
  rw [e]
  unfold TwinLandau.Wsum
  have hsum : ∀ l' : ℝ, Summable fun q => TwinLandau.wq poleP (fun q => hG (poleP q)) q l' := fun l' =>
    (twinPoles_hG.summ.mul_right (4 * Real.exp |l'|)).of_norm_bounded fun q =>
      TwinLandau.norm_wq_le twinPoles_hG q l'
  rw [← (hsum _).tsum_sub (hsum 0), Complex.ofReal_tsum, ← tsum_neg]
  refine tsum_congr fun q => ?_
  set t : ℝ := (zetaZeroFamily q).im with ht
  have hline : zetaZeroFamily q - 1 / 2 = I * t := by
    have h := line_of_RH hRH q
    apply Complex.ext <;> simp [ht, h]
  have hrr : zetaZeroFamily q * (1 - zetaZeroFamily q) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    have : zetaZeroFamily q = 1 / 2 + I * t := by linear_combination hline
    rw [this]
    push_cast
    linear_combination (-(t : ℂ) ^ 2) * Complex.I_sq
  have hP : poleP q = 2 * I * t := by unfold poleP; rw [hline]; ring
  unfold TwinLandau.wq
  dsimp only
  rw [hG_poleP, hrr, hP]
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero]
  have hc : cexp (((Real.log r / 2 : ℝ) : ℂ) * (2 * I * t)) + cexp (-(((Real.log r / 2 : ℝ) : ℂ) * (2 * I * t))) =
      2 * ((Real.cos (t * Real.log r) : ℝ) : ℂ) := by
    have e1 : ((Real.log r / 2 : ℝ) : ℂ) * (2 * I * t) = ((t * Real.log r : ℝ) : ℂ) * I := by push_cast; ring
    rw [Complex.ofReal_cos, Complex.cos, e1, neg_mul]
    ring
  push_cast at hc ⊢
  linear_combination (1 / (1 / 4 + (t : ℂ) ^ 2)) * hc

/-- **`K_H` is not smooth at `1`** in any realization: no `M` has `‖K_H(r) + K_H(1/r) − 2K_H(1)‖ ≤ M(log r)²` for
`1 ≤ r ≤ 2`. A realization gives RH, and then each of the infinitely many zeros with `|γ| ≥ 1` adds at least
`(2/5)(log r)²` to `2K_H(1) − K_H(r) − K_H(1/r)` once `|γ log r| ≤ 1`. -/
theorem not_smooth (R : Realization kerH) :
    ¬ ∃ M : ℝ, ∀ r : ℝ, 1 ≤ r → r ≤ 2 → ‖kerH r + kerH r⁻¹ - 2 * kerH 1‖ ≤ M * Real.log r ^ 2 := by
  have hRH := rh_of_posDefH (posDefQ_of_realization R)
  rintro ⟨M, hM⟩
  set t : ZIdx → ℝ := fun q => (zetaZeroFamily q).im with ht
  -- the zeros with `|γ| ≥ 1` are infinitely many
  have hfin : {q : ZIdx | |t q| < 1}.Finite := by
    refine (finite_poleP 2).subset fun q hq => ?_
    have hline : zetaZeroFamily q - 1 / 2 = I * t q := by
      have h := line_of_RH hRH q
      apply Complex.ext <;> simp [ht, h]
    simp only [Set.mem_ofPred_eq] at hq ⊢
    unfold poleP
    rw [hline, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, Complex.norm_two]
    linarith
  have := ZerosInfinite.infinite_ZIdx
  have hinf : {q : ZIdx | 1 ≤ |t q|}.Infinite := by
    have h := hfin.infinite_compl
    refine h.mono fun q hq => ?_
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hq ⊢
    exact hq
  obtain ⟨F, hFs, hFc⟩ := hinf.exists_subset_card_eq (⌈4 * M⌉₊ + 1)
  -- a small `u = log r`
  set T : ℝ := ∑ q ∈ F, |t q| + 1 with hT
  have hT1 : 1 ≤ T := by have := Finset.sum_nonneg (s := F) fun q _ => abs_nonneg (t q); linarith
  set u : ℝ := min (Real.log 2) (1 / T) with hu
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hu0 : 0 < u := lt_min hl2 (by positivity)
  have hr1 : 1 ≤ Real.exp u := Real.one_le_exp hu0.le
  have hr2 : Real.exp u ≤ 2 := by
    calc Real.exp u ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (min_le_left _ _)
      _ = 2 := Real.exp_log two_pos
  have hbound := hM (Real.exp u) hr1 hr2
  rw [kerH_second_diff hRH, Real.log_exp, norm_neg, Complex.norm_real] at hbound
  change ‖∑' q : ZIdx, (2 - 2 * Real.cos (t q * u)) / (1 / 4 + t q ^ 2)‖ ≤ M * u ^ 2 at hbound
  -- each term of `F` gives at least `(2/5)u²`
  have hterm : ∀ q ∈ F, 2 / 5 * u ^ 2 ≤ (2 - 2 * Real.cos (t q * u)) / (1 / 4 + t q ^ 2) := by
    intro q hq
    have h1 : 1 ≤ |t q| := hFs hq
    have hle : |t q| ≤ T := by
      have := Finset.single_le_sum (f := fun q => |t q|) (fun q _ => abs_nonneg (t q)) hq
      linarith
    have hx : |t q * u| ≤ 1 := by
      rw [abs_mul, abs_of_pos hu0]
      calc |t q| * u ≤ T * (1 / T) := mul_le_mul hle (min_le_right _ _) hu0.le (by linarith)
        _ = 1 := by field_simp
    have hcos := Real.cos_bound hx
    have hx2 : (t q * u) ^ 2 ≤ 1 := by
      have := sq_abs (t q * u)
      nlinarith [abs_nonneg (t q * u)]
    have h4 : |t q * u| ^ 4 = ((t q * u) ^ 2) ^ 2 := by rw [← sq_abs (t q * u)]; ring
    have hlow : (t q * u) ^ 2 / 4 ≤ 1 - Real.cos (t q * u) := by
      rw [h4] at hcos
      have := (abs_le.1 hcos).2
      nlinarith [sq_nonneg (t q * u)]
    have ht2 : 1 ≤ t q ^ 2 := by nlinarith [sq_abs (t q)]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg u]
  have hS : ∑ q ∈ F, (2 - 2 * Real.cos (t q * u)) / (1 / 4 + t q ^ 2) ≤
      ∑' q : ZIdx, (2 - 2 * Real.cos (t q * u)) / (1 / 4 + t q ^ 2) := by
    refine Summable.sum_le_tsum F (fun q _ => ?_) ?_
    · exact div_nonneg (by linarith [Real.cos_le_one (t q * u)]) (by positivity)
    · refine (summable_hw.mul_left 4).of_nonneg_of_le (fun q => ?_) fun q => ?_
      · exact div_nonneg (by linarith [Real.cos_le_one (t q * u)]) (by positivity)
      · have hline : zetaZeroFamily q - 1 / 2 = I * t q := by
          have h := line_of_RH hRH q
          apply Complex.ext <;> simp [ht, h]
        have hrr : ‖1 / (zetaZeroFamily q * (1 - zetaZeroFamily q))‖ = 1 / (1 / 4 + t q ^ 2) := by
          have : zetaZeroFamily q = 1 / 2 + I * t q := by linear_combination hline
          rw [this, show (1 / 2 + I * t q) * (1 - (1 / 2 + I * t q)) = ((1 / 4 + t q ^ 2 : ℝ) : ℂ) by
            push_cast; linear_combination (-(t q : ℂ) ^ 2) * Complex.I_sq]
          rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        rw [hrr]
        have := Real.neg_one_le_cos (t q * u)
        rw [div_le_iff₀ (by positivity)]
        field_simp
        linarith
  have hsum : (⌈4 * M⌉₊ + 1 : ℝ) * (2 / 5 * u ^ 2) ≤ M * u ^ 2 := by
    have h := Finset.card_nsmul_le_sum F _ _ hterm
    rw [hFc, nsmul_eq_mul] at h
    push_cast at h
    have hnn : 0 ≤ ∑' q : ZIdx, (2 - 2 * Real.cos (t q * u)) / (1 / 4 + t q ^ 2) :=
      tsum_nonneg fun q => div_nonneg (by linarith [Real.cos_le_one (t q * u)]) (by positivity)
    rw [Real.norm_of_nonneg hnn] at hbound
    linarith
  have hu2 : 0 < u ^ 2 := by positivity
  have hceil : 4 * M ≤ ⌈4 * M⌉₊ := Nat.le_ceil _
  have hc0 : (0 : ℝ) ≤ ⌈4 * M⌉₊ := Nat.cast_nonneg _
  nlinarith

end BallHadamard

#print axioms BallHadamard.kerH_one
#print axioms BallHadamard.kerH_inv
#print axioms BallHadamard.rh_iff_posDefH
#print axioms BallHadamard.rh_iff_realizationH
#print axioms BallHadamard.not_smooth
