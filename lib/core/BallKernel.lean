/-
# The kernel of the ball conjecture: the Riemann hypothesis as positive-definiteness on `ℚ₊^×`

Plain statement. For `r > 0` let `K(r) = Σ_ρ e^{(ρ − ½)²/2} r^{ρ − ½}`, the sum over the nontrivial zeros `ρ` of `ζ`
with multiplicity (`kerK`). Writing `ρ = ½ + iγ` it is `Σ_ρ e^{−γ²/2} r^{iγ}`: the kernel of the fifth of the first
steps in `docs/ball-conjecture.md`, with the Gaussian `ĥ(γ) = e^{−γ²/2}`. Then Mathlib's `RiemannHypothesis` holds
if and only if `K` is positive-definite on the positive rationals (`rh_iff_posDef`):
`Σ_{a,b ∈ S} x_a x̄_b K(a/b) ≥ 0` for every finite set `S` of positive rationals and all complex `x`. No hypothesis
beyond these. So under RH the positive rationals sit on the unit sphere of a Hilbert space, after scaling by `K(1)`,
with `K(a/b)` for their inner products, and RH is exactly the existence of that configuration.

* RH to positive: on the line, `Σ_{a,b} x_a x̄_b K(a/b) = Σ_ρ e^{−γ²/2}|Σ_a x_a a^{iγ}|²` (`posDef_of_rh`).
* Positive to RH (`rh_of_posDef`): the `2 × 2` minor on `{1, r}` is `2K(1) + K(r) + K(1/r) ≥ 0`. That is the twin sum
  `Σ_ρ c_ρ(2 + e^{λP_ρ} + e^{−λP_ρ})` of `TwinLandau` at `λ = (log r)/2`, with the poles `P_ρ = 2(ρ − ½)` and the
  weights `c_ρ = e^{P_ρ²/8}` (`twin_eq_kerK`). The `λ` with `r` rational are dense and the twin sum is continuous,
  so it is real and nonnegative at every `λ`. Then `TwinLandau.abs_re_le`, Landau's theorem for the Laplace transform
  with the residue at the rightmost pole on a horizontal line, puts every pole on the imaginary axis
  (`re_eq_zero_of_dense`).
* The Gaussian weights are summable over the zeros by Hadamard's `Σ_ρ |ρ − ½|^{−2} < ∞` (`summable_gw`).

The same argument shows that the kernel of the Davenport–Heilbronn function, built in the same way from its zeros, is
not positive-definite (`PsiOmega.not_posDef_dh`, `lib/dh/DHBallKernel.lean`), since some of those zeros are off the
line. Like Weil's criterion, the equivalence has no bearing on whether RH holds.
-/
import Mathlib
import WeilRH

open Real Complex Finset Filter Topology ComplexConjugate WeilForm WeilTest
open scoped ComplexOrder

noncomputable section

namespace BallKernel

/-- A function `k` on the positive reals is **positive-definite on the positive rationals** when
`Σ_{a,b ∈ S} x_a x̄_b k(a/b) ≥ 0` for every finite set `S` of positive rationals and all complex `x`. In `ℂ`'s order
this says that the sum is real and nonnegative. -/
def PosDefQ (k : ℝ → ℂ) : Prop :=
  ∀ (S : Finset ℚ) (x : ℚ → ℂ), (∀ a ∈ S, 0 < a) → 0 ≤ ∑ a ∈ S, ∑ b ∈ S, x a * conj (x b) * k ((a : ℝ) / b)

/-! ## The twin sum on a dense set of points -/

/-- The values `κ log r` at positive rationals `r` are dense in `ℝ`, for `κ ≠ 0`. -/
lemma mem_closure_log {κ : ℝ} (hκ : κ ≠ 0) (l : ℝ) :
    l ∈ closure {y : ℝ | ∃ r : ℚ, 0 < r ∧ y = κ * Real.log r} := by
  set x₀ := Real.exp (l / κ) with hx₀
  have hx0 : 0 < x₀ := Real.exp_pos _
  have hr : ∀ n : ℕ, ∃ r : ℚ, x₀ < r ∧ (r : ℝ) < x₀ + 1 / (n + 1) := fun n =>
    exists_rat_btwn (by linarith [show (0 : ℝ) < 1 / (n + 1) by positivity])
  choose r hr1 hr2 using hr
  have hup : Tendsto (fun n : ℕ => x₀ + 1 / ((n : ℝ) + 1)) atTop (𝓝 (x₀ + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hup
  have hlim : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 x₀) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (hr1 n).le)
      (fun n => (hr2 n).le)
  have hlog : Tendsto (fun n => κ * Real.log (r n)) atTop (𝓝 (κ * Real.log x₀)) :=
    ((Real.continuousAt_log hx0.ne').tendsto.comp hlim).const_mul κ
  rw [hx₀, Real.log_exp, mul_div_cancel₀ _ hκ] at hlog
  exact mem_closure_of_tendsto hlog (Eventually.of_forall fun n =>
    ⟨r n, by exact_mod_cast hx0.trans (hr1 n), rfl⟩)

open TwinLandau in
/-- **Twin positivity on the positive rationals puts every pole on the imaginary axis.** For poles and weights as in
`TwinLandau.TwinPoles`, with `c_q = G(P_q)`, `G` even and nonzero on `Re p > 0`: if the twin sum
`Σ_q c_q(2 + e^{λP_q} + e^{−λP_q})` is real and nonnegative at `λ = κ log r` for every positive rational `r`, then
every `Re P_q = 0`. -/
theorem re_eq_zero_of_dense {ι : Type*} [Countable ι] {P c : ι → ℂ} {G : ℂ → ℂ} (D : TwinPoles P c)
    (hc : ∀ q, c q = G (P q)) (hGe : ∀ p, G (-p) = G p) (hGn : ∀ p, 0 < p.re → G p ≠ 0) {κ : ℝ}
    (hκ : κ ≠ 0) (hW : ∀ r : ℚ, 0 < r → 0 ≤ Wsum P c (κ * Real.log r)) (q : ι) : (P q).re = 0 := by
  have hall : ∀ l : ℝ, 0 ≤ Wsum P c l := by
    have hcl : IsClosed {l : ℝ | 0 ≤ Wsum P c l} := isClosed_le continuous_const (continuous_Wsum D)
    intro l
    refine (hcl.closure_subset_iff.2 ?_) (mem_closure_log hκ l)
    rintro y ⟨r, hr, rfl⟩
    exact hW r hr
  have hsum : ∀ l : ℝ, HasSum (fun q => c q * (2 + cexp (l * P q) + cexp (-(l * P q))))
      ((Wsum P c l).re : ℂ) := by
    intro l
    have hs : Summable fun q => wq P c q l :=
      (D.summ.mul_right (4 * Real.exp |l|)).of_norm_bounded fun q => norm_wq_le D q l
    have e : ((Wsum P c l).re : ℂ) = Wsum P c l :=
      Complex.ext rfl (by simp [(Complex.nonneg_iff.1 (hall l)).2])
    rw [e]
    exact hs.hasSum
  have D' : TwinData P c G (fun l => (Wsum P c l).re) := ⟨D, hc, hGe, hGn, fun l _ => hsum l⟩
  have h := abs_re_le D' (C := 0) le_rfl (fun l _ => by
    rw [zero_mul, neg_zero]; exact (Complex.nonneg_iff.1 (hall l)).1) q
  exact abs_nonpos_iff.1 h

/-! ## The Gaussian weights -/

/-- `‖e^{ap²}‖·‖p‖² ≤ 8e^a` on `|Re p| < 1`, for `a ≥ 1/8`. -/
lemma norm_cexp_sq_mul_le {a : ℝ} (ha : 1 / 8 ≤ a) {p : ℂ} (hp : |p.re| < 1) :
    ‖cexp (a * p ^ 2)‖ * ‖p‖ ^ 2 ≤ 8 * Real.exp a := by
  rw [Complex.norm_exp]
  have hsq : (p ^ 2).re = p.re ^ 2 - p.im ^ 2 := by simp [sq]
  have hre : ((a : ℂ) * p ^ 2).re = a * (p.re ^ 2 - p.im ^ 2) := by rw [Complex.re_ofReal_mul, hsq]
  have hn : ‖p‖ ^ 2 = p.re ^ 2 + p.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hre, hn]
  have h1 : p.re ^ 2 ≤ 1 := by
    have := abs_lt.1 hp
    nlinarith
  have h2 : 1 + p.im ^ 2 ≤ 8 * Real.exp (a * p.im ^ 2) := by
    have := Real.add_one_le_exp (a * p.im ^ 2)
    nlinarith [sq_nonneg p.im]
  have h3 : Real.exp (a * (p.re ^ 2 - p.im ^ 2)) * Real.exp (a * p.im ^ 2) ≤ Real.exp a := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc Real.exp (a * (p.re ^ 2 - p.im ^ 2)) * (p.re ^ 2 + p.im ^ 2)
      ≤ Real.exp (a * (p.re ^ 2 - p.im ^ 2)) * (8 * Real.exp (a * p.im ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = 8 * (Real.exp (a * (p.re ^ 2 - p.im ^ 2)) * Real.exp (a * p.im ^ 2)) := by ring
    _ ≤ 8 * Real.exp a := by linarith

/-- The Gaussian weight in the pole variable: `e^{P²/8}`, which at `P = 2iγ` is `ĥ(γ) = e^{−γ²/2}`. -/
def gw (p : ℂ) : ℂ := cexp (p ^ 2 / 8)

/-- **The Gaussian weights are summable over the zeros of `ζ`**, by Hadamard's `Σ_ρ |ρ − ½|^{−2} < ∞`. -/
theorem summable_gw : Summable fun q : ZIdx => ‖gw (poleP q)‖ := by
  have hs : Summable fun i : ZeroIdx (sqF Xi) => ‖i.1⁻¹‖ := (hadamardW_Xi xiGrowth Xi_zero_ne_zero).summ
  have hs2 : Summable fun p : Bool × ZeroIdx (sqF Xi) => ‖p.2.1⁻¹‖ :=
    (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun _ => hs, Summable.of_finite⟩
  have hs3 : Summable fun q : ZIdx => ‖((zetaEquiv q).2.1)⁻¹‖ :=
    (zetaEquiv.summable_iff (f := fun p : Bool × ZeroIdx (sqF Xi) => ‖p.2.1⁻¹‖)).2 hs2
  refine (hs3.mul_left (2 * Real.exp (1 / 8))).of_norm_bounded fun q => ?_
  rw [norm_norm]
  have e1 : ‖poleP q‖ = 2 * ‖tau (zetaEquiv q).2‖ := by
    unfold poleP; rw [norm_mul, norm_zZF_sub]; simp
  have e2 : ‖(zetaEquiv q).2.1‖ = ‖tau (zetaEquiv q).2‖ ^ 2 := by rw [← tau_sq, norm_pow]
  have hP : 0 < ‖poleP q‖ := norm_pos_iff.2 fun h => im_poleP_ne q (by rw [h]; simp)
  have ht : 0 < ‖tau (zetaEquiv q).2‖ ^ 2 := by
    have : 0 < ‖tau (zetaEquiv q).2‖ := by rw [e1] at hP; linarith
    positivity
  have hb := norm_cexp_sq_mul_le (a := 1 / 8) le_rfl (abs_re_poleP q)
  rw [e1] at hb
  have hg : gw (poleP q) = cexp (((1 / 8 : ℝ) : ℂ) * poleP q ^ 2) := by unfold gw; congr 1; push_cast; ring
  rw [hg, norm_inv, e2, ← div_eq_mul_inv, le_div_iff₀ ht]
  nlinarith

/-- The poles `P_ρ = 2(ρ − ½)` of `ζ` with the Gaussian weights `e^{P_ρ²/8}`. -/
theorem twinPoles_gw : TwinLandau.TwinPoles poleP fun q => gw (poleP q) :=
  ⟨summable_gw, abs_re_poleP, im_poleP_ne, finite_poleP⟩

/-! ## The kernel -/

/-- **The kernel** `K(r) = Σ_ρ e^{(ρ − ½)²/2} r^{ρ − ½}` over the nontrivial zeros of `ζ` with multiplicity, with
`r^{ρ − ½}` written `e^{(ρ − ½)log r}`. At `ρ = ½ + iγ` the term is `e^{−γ²/2} r^{iγ}`. -/
def kerK (r : ℝ) : ℂ :=
  ∑' q : ZIdx, cexp ((zetaZeroFamily q - 1 / 2) ^ 2 / 2) * cexp ((zetaZeroFamily q - 1 / 2) * Real.log r)

/-- The kernel in the pole variable `P = 2(ρ − ½)`: `K(r) = Σ_ρ e^{P²/8} e^{(log r/2)P}`. -/
lemma kerK_eq (r : ℝ) : kerK r = ∑' q : ZIdx, gw (poleP q) * cexp ((Real.log r / 2 : ℝ) * poleP q) := by
  unfold kerK gw poleP
  congr 1
  funext q
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The summands of the kernel are summable at every `r`. -/
lemma summable_kerK (l : ℝ) : Summable fun q : ZIdx => gw (poleP q) * cexp (l * poleP q) :=
  TwinLandau.summable_cw_mul twinPoles_gw (B := Real.exp |l|) fun q => by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h := abs_re_poleP q
    have e : ((l : ℂ) * poleP q).re = l * (poleP q).re := by simp
    rw [e]
    calc l * (poleP q).re ≤ |l * (poleP q).re| := le_abs_self _
      _ = |l| * |(poleP q).re| := abs_mul _ _
      _ ≤ |l| * 1 := mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
      _ = |l| := mul_one _

/-- **The `2 × 2` minors are the twin sum**: `2K(1) + K(r) + K(1/r) = Σ_ρ e^{P_ρ²/8}(2 + e^{λP_ρ} + e^{−λP_ρ})` at
`λ = (log r)/2`. -/
theorem twin_eq_kerK (r : ℝ) :
    TwinLandau.Wsum poleP (fun q => gw (poleP q)) (Real.log r / 2) = 2 * kerK 1 + kerK r + kerK r⁻¹ := by
  unfold TwinLandau.Wsum TwinLandau.wq
  have h0 := summable_kerK 0
  have h1 := summable_kerK (Real.log r / 2)
  have h2 := summable_kerK (-(Real.log r / 2))
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h0
  have e : ∀ q : ZIdx, gw (poleP q) * (2 + cexp ((Real.log r / 2 : ℝ) * poleP q) +
      cexp (-((Real.log r / 2 : ℝ) * poleP q))) = 2 * gw (poleP q) +
      gw (poleP q) * cexp ((Real.log r / 2 : ℝ) * poleP q) +
      gw (poleP q) * cexp ((-(Real.log r / 2) : ℝ) * poleP q) := fun q => by
    push_cast; ring_nf
  rw [tsum_congr e, ((h0.mul_left 2).add h1).tsum_add h2, (h0.mul_left 2).tsum_add h1, tsum_mul_left,
    kerK_eq, kerK_eq, kerK_eq, Real.log_one, Real.log_inv]
  simp only [zero_div, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, neg_div]

/-! ## The equivalence -/

/-- **The `2 × 2` minor on `{1, r}`**: a kernel positive-definite on `ℚ₊^×` has `2k(1) + k(r) + k(1/r) ≥ 0` at every
positive rational `r`. -/
theorem minor_nonneg {k : ℝ → ℂ} (hk : PosDefQ k) {r : ℚ} (hr : 0 < r) : 0 ≤ 2 * k 1 + k r + k (r : ℝ)⁻¹ := by
  by_cases h1 : r = 1
  · subst h1
    have h := hk {1} (fun _ => 2) (by simp)
    simp only [Finset.sum_singleton, Rat.cast_one, div_one, map_ofNat] at h
    simp only [Rat.cast_one, inv_one]
    calc (0 : ℂ) ≤ 2 * 2 * k 1 := h
      _ = 2 * k 1 + k 1 + k 1 := by ring
  · have h := hk {1, r} (fun _ => 1) (by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact one_pos
      · rw [Finset.mem_singleton.1 ha]; exact hr)
    rw [Finset.sum_pair (Ne.symm h1)] at h
    simp only [Finset.sum_pair (Ne.symm h1), map_one, one_mul, Rat.cast_one, div_one] at h
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [div_self hr0, one_div] at h
    calc (0 : ℂ) ≤ k 1 + k (↑r)⁻¹ + (k ↑r + k 1) := h
      _ = 2 * k 1 + k r + k (↑r)⁻¹ := by ring

/-- **Positive-definite on `ℚ₊^×` gives the Riemann hypothesis.** -/
theorem rh_of_posDef (hK : PosDefQ kerK) : RiemannHypothesis := by
  have hW : ∀ r : ℚ, 0 < r → 0 ≤ TwinLandau.Wsum poleP (fun q => gw (poleP q)) ((1 / 2) * Real.log r) := by
    intro r hr
    rw [show (1 / 2 : ℝ) * Real.log r = Real.log r / 2 by ring, twin_eq_kerK]
    exact minor_nonneg hK hr
  have hline : ∀ q : ZIdx, (zetaZeroFamily q).re = 1 / 2 := fun q => by
    have h := re_eq_zero_of_dense twinPoles_gw (G := gw) (fun _ => rfl)
      (fun p => by unfold gw; rw [neg_sq]) (fun p _ => Complex.exp_ne_zero _) (by norm_num) hW q
    rw [re_poleP] at h
    linarith
  intro s hs htriv _
  exact hline ⟨⟨s, hs, htriv⟩, ⟨0, zeroMult_pos _⟩⟩

/-- **The Riemann hypothesis gives positive-definiteness on `ℚ₊^×`**: on the line,
`Σ_{a,b} x_a x̄_b K(a/b) = Σ_ρ e^{−γ²/2}|Σ_a x_a a^{iγ}|²`. -/
theorem posDef_of_rh (hRH : RiemannHypothesis) : PosDefQ kerK := by
  intro S x hS
  set t : ZIdx → ℝ := fun q => (zetaZeroFamily q).im with ht
  have hline : ∀ q : ZIdx, zetaZeroFamily q - 1 / 2 = I * (t q : ℂ) := fun q => by
    have h := line_of_RH hRH q
    apply Complex.ext <;> simp [ht, h]
  set w : ZIdx → ℝ := fun q => Real.exp (-(t q) ^ 2 / 2) with hw
  set e : ZIdx → ℚ → ℂ := fun q a => cexp (I * (t q : ℂ) * Real.log a) with he
  have hsw : Summable w := by
    refine summable_gw.congr fun q => ?_
    unfold gw poleP
    rw [hline, Complex.norm_exp]
    simp only [hw]
    congr 1
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hterm : ∀ q : ZIdx, ∀ a ∈ S, ∀ b ∈ S,
      cexp ((zetaZeroFamily q - 1 / 2) ^ 2 / 2) * cexp ((zetaZeroFamily q - 1 / 2) * Real.log ((a : ℝ) / b)) =
        (w q : ℂ) * (e q a * conj (e q b)) := by
    intro q a ha b hb
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (hS a ha).ne'
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (hS b hb).ne'
    rw [hline, Real.log_div ha0 hb0]
    simp only [he, hw, ← Complex.exp_conj, ← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
    push_cast
    linear_combination ((t q : ℂ) ^ 2 / 2) * Complex.I_sq
  have hsum : ∀ a ∈ S, ∀ b ∈ S, Summable fun q : ZIdx => x a * conj (x b) * ((w q : ℂ) * (e q a * conj (e q b))) := by
    intro a _ b _
    refine ((hsw.mul_left ‖x a * conj (x b)‖).of_norm_bounded fun q => ?_)
    have h1 : ‖e q a‖ = 1 := by simp only [he]; rw [Complex.norm_exp]; simp
    have h2 : ‖conj (e q b)‖ = 1 := by
      rw [Complex.norm_conj]; simp only [he]; rw [Complex.norm_exp]; simp
    simp only [norm_mul, h1, h2, mul_one, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, hw, le_refl]
  have hexp : ∑ a ∈ S, ∑ b ∈ S, x a * conj (x b) * kerK ((a : ℝ) / b) =
      ∑' q, (w q : ℂ) * ((∑ a ∈ S, x a * e q a) * conj (∑ b ∈ S, x b * e q b)) := by
    calc ∑ a ∈ S, ∑ b ∈ S, x a * conj (x b) * kerK ((a : ℝ) / b)
        = ∑ a ∈ S, ∑ b ∈ S, ∑' q, x a * conj (x b) * ((w q : ℂ) * (e q a * conj (e q b))) := by
          refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
          unfold kerK
          rw [← tsum_mul_left]
          exact tsum_congr fun q => by rw [hterm q a ha b hb]
      _ = ∑' q, ∑ a ∈ S, ∑ b ∈ S, x a * conj (x b) * ((w q : ℂ) * (e q a * conj (e q b))) := by
          rw [Summable.tsum_finsetSum fun a ha => ?_]
          · refine Finset.sum_congr rfl fun a ha => ?_
            rw [Summable.tsum_finsetSum fun b hb => hsum a ha b hb]
          · exact summable_sum fun b hb => hsum a ha b hb
      _ = ∑' q, (w q : ℂ) * ((∑ a ∈ S, x a * e q a) * conj (∑ b ∈ S, x b * e q b)) := by
          refine tsum_congr fun q => ?_
          rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [map_mul]
          ring
  rw [hexp]
  exact tsum_nonneg fun q => mul_nonneg (by exact_mod_cast (Real.exp_pos _).le) (mul_star_self_nonneg _)

/-- **The Riemann hypothesis is positive-definiteness on the positive rationals**: Mathlib's `RiemannHypothesis` holds
if and only if `K(r) = Σ_ρ e^{(ρ − ½)²/2} r^{ρ − ½}` is positive-definite on `ℚ₊^×`. -/
theorem rh_iff_posDef : RiemannHypothesis ↔ PosDefQ kerK := ⟨posDef_of_rh, rh_of_posDef⟩

/-! ## The kernel is even, and the explicit formula computes it from the primes -/

/-- The terms of the kernel are summable at every `r`. -/
lemma summable_kerK_term (L : ℝ) : Summable fun q : ZIdx =>
    cexp ((zetaZeroFamily q - 1 / 2) ^ 2 / 2) * cexp ((zetaZeroFamily q - 1 / 2) * L) := by
  refine (summable_kerK (L / 2)).congr fun q => ?_
  unfold gw poleP
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- **The kernel is even**: `K(1/r) = K(r)`, as the zeros come in pairs `ρ, 1 − ρ`. -/
theorem kerK_inv (r : ℝ) : kerK r⁻¹ = kerK r := by
  unfold kerK
  rw [Real.log_inv, ← zetaEquiv.symm.tsum_eq, ← zetaEquiv.symm.tsum_eq]
  have hz : ∀ p, zetaZeroFamily (zetaEquiv.symm p) = rhoXi p := fun p => by
    rw [← rhoXi_zetaEquiv, Equiv.apply_symm_apply]
  simp only [hz]
  set fl : Bool × ZeroIdx (sqF Xi) ≃ Bool × ZeroIdx (sqF Xi) := Equiv.prodCongr Equiv.boolNot (Equiv.refl _)
  rw [← fl.tsum_eq]
  refine tsum_congr fun p => ?_
  have h : rhoXi (fl p) - 1 / 2 = -(rhoXi p - 1 / 2) := by
    rcases p with ⟨b, i⟩
    cases b <;> simp [fl, rhoXi, Equiv.boolNot]
  rw [h, neg_sq]
  congr 2
  push_cast
  ring

/-- The test function of the explicit formula for `K(r)`: `h(t) = e^{−t²/2}cos(t log r)`. -/
def hK (r : ℝ) (t : ℂ) : ℂ := cexp (-t ^ 2 / 2) * Complex.cos (t * Real.log r)

/-- Its values on the real line, `e^{−t²/2}cos(t log r)`. -/
def hKR (r t : ℝ) : ℝ := Real.exp (-t ^ 2 / 2) * Real.cos (t * Real.log r)

lemma norm_cos_le (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  have h1 : ‖cexp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  have h2 : ‖cexp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  rw [norm_div, Complex.norm_two]
  have h3 := norm_add_le (cexp (z * I)) (cexp (-z * I))
  rw [h1, h2] at h3
  have h4 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  have h5 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  rw [div_le_iff₀ two_pos]
  linarith

/-- **`h` is a strip test function**: entire, with `|h(t)| ≤ 2e^{1/2 + |log r|}/(1 + (Re t)²)` on `|Im t| ≤ 1`. -/
theorem hK_strip (r : ℝ) : WeilStrip.StripTest (hK r) (2 * Real.exp (1 / 2 + |Real.log r|)) where
  diff := by
    unfold hK
    exact (Differentiable.mul (by fun_prop) (Complex.differentiable_cos.comp (by fun_prop))).differentiableOn
  bound t ht := by
    obtain ⟨h1, h2⟩ := ht
    have hy : t.im ^ 2 ≤ 1 := by nlinarith
    unfold hK
    rw [norm_mul, Complex.norm_exp]
    have hre : (-t ^ 2 / 2).re = -(t.re ^ 2 - t.im ^ 2) / 2 := by simp [sq]
    rw [hre]
    have hc := norm_cos_le (t * Real.log r)
    have him : (t * (Real.log r : ℂ)).im = t.im * Real.log r := by simp
    rw [him] at hc
    have hc' : Real.exp |t.im * Real.log r| ≤ Real.exp |Real.log r| := by
      refine Real.exp_le_exp.2 ?_
      rw [abs_mul]
      have : |t.im| ≤ 1 := abs_le.2 ⟨h1, h2⟩
      nlinarith [abs_nonneg (Real.log r)]
    have hg : Real.exp (-(t.re ^ 2 - t.im ^ 2) / 2) ≤ Real.exp (1 / 2) * Real.exp (-(t.re ^ 2 / 2)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    have hx : Real.exp (-(t.re ^ 2 / 2)) * (1 + t.re ^ 2) ≤ 2 := by
      have h := Real.add_one_le_exp (t.re ^ 2 / 2)
      have hp := Real.exp_pos (t.re ^ 2 / 2)
      rw [Real.exp_neg, inv_mul_le_iff₀ hp]
      nlinarith
    rw [le_div_iff₀ (by positivity), Real.exp_add]
    have hpos1 := Real.exp_pos (-(t.re ^ 2 - t.im ^ 2) / 2)
    have hpos2 := Real.exp_pos (1 / 2 : ℝ)
    have hpos3 := Real.exp_pos (-(t.re ^ 2 / 2))
    have hcn := norm_nonneg (Complex.cos (t * Real.log r))
    calc Real.exp (-(t.re ^ 2 - t.im ^ 2) / 2) * ‖Complex.cos (t * Real.log r)‖ * (1 + t.re ^ 2)
        ≤ Real.exp (1 / 2) * Real.exp (-(t.re ^ 2 / 2)) * Real.exp |Real.log r| * (1 + t.re ^ 2) := by
          gcongr
          exact hc.trans hc'
      _ = Real.exp (1 / 2) * Real.exp |Real.log r| * (Real.exp (-(t.re ^ 2 / 2)) * (1 + t.re ^ 2)) := by ring
      _ ≤ Real.exp (1 / 2) * Real.exp |Real.log r| * 2 := by gcongr
      _ = 2 * (Real.exp (1 / 2) * Real.exp |Real.log r|) := by ring

theorem hK_even (r : ℝ) (t : ℂ) : hK r (-t) = hK r t := by
  unfold hK; rw [neg_sq, neg_mul, Complex.cos_neg]

theorem hK_real (r t : ℝ) : hK r t = hKR r t := by
  unfold hK hKR; push_cast; ring_nf

/-- **The explicit formula computes the kernel from the primes**: for every `r > 0` (indeed every `r`, with Mathlib's
`log`),
`K(r) = 2e^{1/8}cosh((log r)/2) − ĝ(0)log π + (1/2π)∫ g ψ − 2Σ_n Λ(n)n^{−1/2} ĝ(log n)`, where
`g(t) = e^{−t²/2}cos(t log r)`, `ĝ(u) = (1/2π)∫ g(t)cos(tu) dt` (`gh`) and `ψ` is the real part of the digamma term
(`psiRe`). The first term, `e^{1/8}(r^{1/2} + r^{−1/2})`, is the poles of `ζ` at `0` and `1`; the prime sum
weighs each prime power `n` by Gaussians at `log n ∓ log r`. -/
theorem kerK_explicit (r : ℝ) :
    kerK r = ((2 * Real.exp (1 / 8) * Real.cosh (Real.log r / 2) : ℝ) : ℂ) +
      ((-(gh (hKR r) 0 * Real.log π) + 1 / (2 * π) * (∫ t, hKR r t * psiRe t)
        - 2 * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * gh (hKR r) (Real.log n) : ℝ) : ℂ) := by
  have H := weilExplicit_zeta (hK_strip r) (hK_even r) (hK_real r)
  have hsum : HasSum (fun q : ZIdx => hK r ((zetaZeroFamily q - 1 / 2) / I)) (kerK r) := by
    have h1 := (summable_kerK_term (Real.log r)).hasSum
    have h2 := (summable_kerK_term (Real.log r⁻¹)).hasSum
    have h12 := (h1.add h2).div_const 2
    have e : (∑' q : ZIdx, cexp ((zetaZeroFamily q - 1 / 2) ^ 2 / 2) *
        cexp ((zetaZeroFamily q - 1 / 2) * Real.log r) + ∑' q : ZIdx, cexp ((zetaZeroFamily q - 1 / 2) ^ 2 / 2) *
        cexp ((zetaZeroFamily q - 1 / 2) * Real.log r⁻¹)) / 2 = kerK r := by
      have := kerK_inv r
      unfold kerK at this ⊢
      rw [this]; ring
    rw [e] at h12
    refine h12.congr_fun fun q => ?_
    unfold hK
    rw [Complex.cos, Real.log_inv]
    have e1 : -((zetaZeroFamily q - 1 / 2) / I) ^ 2 / 2 = (zetaZeroFamily q - 1 / 2) ^ 2 / 2 := by
      field_simp; rw [Complex.I_sq]; ring
    have e2 : (zetaZeroFamily q - 1 / 2) / I * (Real.log r : ℂ) * I = (zetaZeroFamily q - 1 / 2) * Real.log r := by
      field_simp
    have e3 : -((zetaZeroFamily q - 1 / 2) / I * (Real.log r : ℂ)) * I =
        (zetaZeroFamily q - 1 / 2) * ((-Real.log r : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [e1, e2, e3]
    ring
  have hval : hK r (I / 2) + hK r (-(I / 2)) = ((2 * Real.exp (1 / 8) * Real.cosh (Real.log r / 2) : ℝ) : ℂ) := by
    rw [hK_even]
    unfold hK
    have e1 : -(I / 2) ^ 2 / 2 = ((1 / 8 : ℝ) : ℂ) := by
      rw [div_pow, Complex.I_sq]; push_cast; ring
    have e2 : I / 2 * (Real.log r : ℂ) = ((Real.log r / 2 : ℝ) : ℂ) * I := by push_cast; ring
    rw [e1, e2, Complex.cos_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cosh]
    push_cast
    ring
  rw [hsum.unique H.2, hval]

end BallKernel

#print axioms BallKernel.re_eq_zero_of_dense
#print axioms BallKernel.summable_gw
#print axioms BallKernel.twin_eq_kerK
#print axioms BallKernel.rh_iff_posDef
#print axioms BallKernel.kerK_inv
#print axioms BallKernel.kerK_explicit
