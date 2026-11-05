import Mathlib
import BallWeil
import BallFlat

/-! # The evaporation rate of the orbit form: witness level, approach, rate

Plain statement. For `N ≥ 1` the orbit form is `Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn) K_H(m/n)` (`BallWeil.form`), with
`K_H` computed from the primes, and `λ_N = min{Q_N(x) : Σ x_n² = 1}`. The library has RH ⇔ (`Q_N ≥ 0` for every
`N`) (`BallWeil.rh_iff_form`). This module makes the picture quantitative, in three parts, in the language of
`formalisations/ball-rate.md`:

* **Collapse** (`rh_of_frequently_balanced`, `rh_of_excess_tendsto`): the excess `ε_N = max(0, −λ_N)` is monotone in
  `N` (`excess_mono`), RH is `ε_N = 0` at every level (`rh_iff_balance`), and `ε_N ≤ δ` at infinitely many levels for
  every `δ > 0` is already RH. So no asymptotic balance is weaker than exact balance: a crossing cannot hide in the
  limit. If RH fails, a negative vector appears at some level and persists at every higher one (`neg_persists`).
* **Witness level** (`witness_level`): an explicit level at which a dominant crossing is seen.
* **Rate** (`rate_of_sampling`): under RH and a sampling inequality for Dirichlet polynomials at the zeros,
  `λ_N ≥ c·N^{−1−θ}`.

The collapse part is re-proved from the `positivity-search` branch's `GravastarTower` and `GravastarMargin`.
-/

open Finset Filter WeilForm WeilTest Real ComplexConjugate

noncomputable section

namespace BallRate

open BallWeil

/-! ## The excess and its monotonicity -/

/-- The excess positivity at level `N` is at most `t`: `−Q_N(x) ≤ t·Σ_{n ≤ N} x_n²` for every real `x`. -/
def ExcessLe (N : ℕ) (t : ℝ) : Prop := ∀ x : ℕ → ℝ, -form N x ≤ t * ∑ n ∈ Icc 1 N, x n ^ 2

/-- Truncation of a vector to level `N`. -/
def trunc (N : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun n => if n ≤ N then x n else 0

lemma sum_trunc {N N' : ℕ} (h : N ≤ N') (x : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (hg : ∀ n, g n 0 = 0) :
    ∑ n ∈ Icc 1 N', g n (trunc N x n) = ∑ n ∈ Icc 1 N, g n (x n) := by
  rw [← Finset.sum_subset (Icc_subset_Icc_right h)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp [trunc, (mem_Icc.1 hn).2]
  · intro n _ hn
    have : ¬ n ≤ N := fun h' => hn (mem_Icc.2 ⟨by simp_all, h'⟩)
    simp [trunc, this, hg]

/-- The sections nest: the level-`N` form is the level-`N'` form on truncated vectors. -/
lemma form_trunc {N N' : ℕ} (h : N ≤ N') (x : ℕ → ℝ) : form N' (trunc N x) = form N x := by
  unfold form
  rw [sum_trunc h x (fun m y => ∑ n ∈ Icc 1 N', y * trunc N x n * gram m n) (by simp)]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact sum_trunc h x (fun n y => x m * y * gram m n) (by simp)

/-- **Monotonicity of the excess**: a bound at level `N'` holds at every lower level. -/
theorem excess_mono {N N' : ℕ} (h : N ≤ N') {t : ℝ} (hN' : ExcessLe N' t) : ExcessLe N t := by
  intro x
  have := hN' (trunc N x)
  rwa [form_trunc h, sum_trunc h x (fun _ y => y ^ 2) (by simp)] at this

/-- **RH is exact balance at every level.** -/
theorem rh_iff_balance : RiemannHypothesis ↔ ∀ N, ExcessLe N 0 := by
  constructor
  · intro hRH N x
    simp only [zero_mul, neg_nonpos]
    exact form_nonneg hRH N x
  · intro h
    refine rh_iff_form.2 fun N x => ?_
    have := h N (fun n => x n)
    simp only [zero_mul, neg_nonpos] at this
    exact this

/-- **The collapse lemma**: balance up to every `δ > 0` at infinitely many levels is RH. -/
theorem rh_of_frequently_balanced (h : ∀ δ > 0, ∃ᶠ N in atTop, ExcessLe N δ) : RiemannHypothesis := by
  refine rh_iff_balance.2 fun N x => ?_
  simp only [zero_mul]
  set s := ∑ n ∈ Icc 1 N, x n ^ 2
  have hs : 0 ≤ s := Finset.sum_nonneg fun n _ => sq_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (s + 1) := div_pos hε (by linarith)
  obtain ⟨N', hb, hN'⟩ := ((h _ hδ).and_eventually (eventually_ge_atTop N)).exists
  have := excess_mono hN' hb x
  have hle : ε / (s + 1) * s ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- **Asymptotic balance with any rate collapses**: `ε_N ≤ f(N)` with `f(N) → 0` gives RH. -/
theorem rh_of_excess_tendsto {f : ℕ → ℝ} (hf : Tendsto f atTop (nhds 0)) (h : ∀ N, ExcessLe N (f N)) :
    RiemannHypothesis := by
  refine rh_of_frequently_balanced fun δ hδ => Eventually.frequently ?_
  filter_upwards [(hf.eventually (gt_mem_nhds hδ))] with N hN x
  exact (h N x).trans (mul_le_mul_of_nonneg_right hN.le (Finset.sum_nonneg fun n _ => sq_nonneg _))

/-- **Balance to within `1/N` collapses**: `−Q_N(x) ≤ (1/N)·Σ x_n²` at every level is RH. The rate `1/N` is one
choice; `rh_of_excess_tendsto` takes any rate tending to `0`. -/
theorem rh_of_excess_le_inv (h : ∀ N, ExcessLe N (1 / (N : ℝ))) : RiemannHypothesis :=
  rh_of_excess_tendsto (f := fun N : ℕ => 1 / (N : ℝ)) tendsto_one_div_atTop_nhds_zero_nat h

/-- **If RH fails, some level has a negative vector.** -/
theorem exists_neg_of_not_rh (h : ¬ RiemannHypothesis) : ∃ (N : ℕ) (x : ℕ → ℝ), form N x < 0 := by
  by_contra hc
  push Not at hc
  exact h (rh_iff_balance.2 fun N x => by simp only [zero_mul, neg_nonpos]; exact hc N x)

/-- **Failures persist up the tower**: a negative vector at level `N` gives one at every level `N' ≥ N`. -/
theorem neg_persists {N N' : ℕ} (hNN' : N ≤ N') {x : ℕ → ℝ} (hx : form N x < 0) :
    ∃ y : ℕ → ℝ, form N' y < 0 :=
  ⟨trunc N x, by rwa [form_trunc hNN']⟩

/-! ## The witness level of a dominant crossing

The `2 × 2` minor of the form at `(p², q²)` with coefficients `(q, p)` is `p²q²·Re W(log(p/q))`, where
`W(λ) = Σ_ρ a_ρ(2 + e^{λP_ρ} + e^{−λP_ρ})` is the twin sum of `TwinLandau` over the poles `P_ρ = 2(ρ − ½)` with the
Hadamard weights `a_ρ = 1/(ρ(1 − ρ))` (`BallHadamard.twin_eq_kerH`). Its real part is `2H₀ + Σ_ρ g_ρ(λ)` with
`g_ρ(λ) = Re(a_ρ(e^{λP_ρ} + e^{−λP_ρ}))`: the zeros on the line give `g_ρ ≤ 2Re a_ρ`, and `Σ_ρ Re a_ρ = H₀`
(Hadamard's identity) bounds their total by `2H₀` whatever `λ` is; the four zeros `ρ₀, ρ̄₀, 1 − ρ₀, 1 − ρ̄₀` of a
crossing give `4|a₀|e^{2δλ}cos(2γλ + arg a₀) + O(|a₀|)`; and the other off-line zeros give at most
`(e^{2δλ} + 1)·M` when `ρ₀` is extremal. At the first `λ ≥ Λ` with `cos = −1`, approximated by `log(p/q)` to within
`π/(6γ)`, the sum is negative. -/

section Witness

open BallHadamard BallKernel TwinLandau Complex
open scoped Classical

/-- Hadamard's constant `H₀ = K_H(1) = 2 + γ − log 4π`. -/
def H₀ : ℝ := 2 + eulerMascheroniConstant - Real.log (4 * π)

lemma kψ_one_eq : kψ 1 = H₀ := by unfold H₀; exact kψ_one

lemma H₀_pos : 0 < H₀ := kψ_one_eq ▸ kψ_one_pos

/-- The weight `1/(ρ(1 − ρ))` of a point `ρ`. -/
def aw (ρ : ℂ) : ℂ := 1 / (ρ * (1 - ρ))

/-- The Hadamard weight `a_q = 1/(ρ_q(1 − ρ_q))` of the zero `ρ_q`: the weight `G(P_q)` of the twin sum. -/
def hw (q : ZIdx) : ℂ := aw (zetaZeroFamily q)

lemma hw_eq (q : ZIdx) : hw q = hG (poleP q) := (hG_poleP q).symm

lemma summable_norm_hw : Summable fun q => ‖hw q‖ := BallHadamard.summable_hw

lemma hasSum_hw : HasSum hw ((H₀ : ℝ) : ℂ) := by unfold hw aw H₀; exact hadamard_zeta

lemma aw_conj (ρ : ℂ) : aw (conj ρ) = conj (aw ρ) := by
  unfold aw; rw [map_div₀, map_one, map_mul, map_sub, map_one]

lemma aw_one_sub (ρ : ℂ) : aw (1 - ρ) = aw ρ := by
  unfold aw; ring_nf

/-- `Re a_q > 0`: `Re(ρ(1 − ρ)) = β(1 − β) + γ² > 0` for `0 < β < 1`. -/
lemma re_hw_pos (q : ZIdx) : 0 < (hw q).re := by
  have hb := abs_re_poleP q
  rw [re_poleP] at hb
  set ρ := zetaZeroFamily q
  have hz : (ρ * (1 - ρ)).re = ρ.re * (1 - ρ.re) + ρ.im ^ 2 := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have hpos : 0 < (ρ * (1 - ρ)).re := by
    rw [hz]
    have := abs_lt.1 hb
    nlinarith [sq_nonneg ρ.im]
  have hne : ρ * (1 - ρ) ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
  unfold hw aw
  rw [one_div, Complex.inv_re]
  exact div_pos hpos (Complex.normSq_pos.2 hne)

/-- One zero's term of `Re W(λ) − 2H₀`: `g_q(λ) = Re(a_q(e^{λP_q} + e^{−λP_q}))`. -/
def gq (q : ZIdx) (l : ℝ) : ℝ := (hw q * (cexp (l * poleP q) + cexp (-(l * poleP q)))).re

lemma summable_exp_pair (l : ℝ) :
    Summable fun q => hw q * (cexp (l * poleP q) + cexp (-(l * poleP q))) := by
  have h := (summable_kerH l).add (summable_kerH (-l))
  refine h.congr fun q => ?_
  rw [hw_eq]
  push_cast
  ring_nf

lemma summable_gq (l : ℝ) : Summable fun q => gq q l :=
  (Complex.hasSum_re (summable_exp_pair l).hasSum).summable

/-- **`Re W(λ) = 2H₀ + Σ_q g_q(λ)`.** -/
lemma re_Wsum (l : ℝ) : (Wsum poleP (fun q => hG (poleP q)) l).re = 2 * H₀ + ∑' q, gq q l := by
  unfold Wsum wq
  have e : ∀ q, hG (poleP q) * (2 + cexp (l * poleP q) + cexp (-(l * poleP q))) =
      2 * hw q + hw q * (cexp (l * poleP q) + cexp (-(l * poleP q))) := fun q => by rw [hw_eq]; ring
  simp_rw [e]
  rw [(hasSum_hw.summable.mul_left 2).tsum_add (summable_exp_pair l), Complex.add_re, tsum_mul_left,
    hasSum_hw.tsum_eq, Complex.re_tsum (summable_exp_pair l)]
  simp [gq]

/-! ### The quadruple of a crossing -/

/-- The indices of the four zeros `ρ₀, ρ̄₀, 1 − ρ₀, 1 − ρ̄₀`. -/
def quadSet (ρ₀ : ℂ) : Set ZIdx :=
  {q | zetaZeroFamily q = ρ₀ ∨ zetaZeroFamily q = conj ρ₀ ∨ zetaZeroFamily q = 1 - ρ₀ ∨
    zetaZeroFamily q = 1 - conj ρ₀}

lemma quadSet_finite (ρ₀ : ℂ) : (quadSet ρ₀).Finite := by
  refine (finite_poleP (2 * ‖ρ₀ - 1 / 2‖)).subset fun q hq => ?_
  simp only [quadSet, Set.mem_ofPred_eq] at hq ⊢
  unfold poleP
  rw [norm_mul, Complex.norm_two]
  refine mul_le_mul_of_nonneg_left ?_ two_pos.le
  have hc : ‖conj ρ₀ - 1 / 2‖ = ‖ρ₀ - 1 / 2‖ := by
    rw [show (conj ρ₀ - 1 / 2 : ℂ) = conj (ρ₀ - 1 / 2) by
      rw [map_sub, map_div₀, map_one, map_ofNat], Complex.norm_conj]
  rcases hq with h | h | h | h
  · rw [h]
  · rw [h]; exact hc.le
  · rw [h, show (1 - ρ₀ - 1 / 2 : ℂ) = -(ρ₀ - 1 / 2) by ring, norm_neg]
  · rw [h, show (1 - conj ρ₀ - 1 / 2 : ℂ) = -(conj ρ₀ - 1 / 2) by ring, norm_neg]
    exact hc.le

/-- The quadruple as a finite set. -/
def quad (ρ₀ : ℂ) : Finset ZIdx := (quadSet_finite ρ₀).toFinset

lemma mem_quad {ρ₀ : ℂ} {q : ZIdx} : q ∈ quad ρ₀ ↔ q ∈ quadSet ρ₀ := Set.Finite.mem_toFinset _

/-- The term of a zero of the quadruple is that of `ρ₀`, up to conjugation: all four have the same real part. -/
lemma gq_quad {ρ₀ : ℂ} {q : ZIdx} (hq : q ∈ quad ρ₀) (l : ℝ) :
    gq q l = (aw ρ₀ * (cexp (l * (2 * (ρ₀ - 1 / 2))) + cexp (-(l * (2 * (ρ₀ - 1 / 2)))))).re := by
  rw [mem_quad] at hq
  simp only [quadSet, Set.mem_ofPred_eq] at hq
  unfold gq hw poleP
  set X : ℂ := (l : ℂ) * (2 * (ρ₀ - 1 / 2)) with hX
  have hcX : (l : ℂ) * (2 * (conj ρ₀ - 1 / 2)) = conj X := by
    rw [hX, map_mul, map_mul, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_ofReal]
  have hconj : (conj (aw ρ₀) * (cexp (conj X) + cexp (-(conj X)))).re =
      (aw ρ₀ * (cexp X + cexp (-X))).re := by
    rw [← map_neg, Complex.exp_conj, Complex.exp_conj, ← map_add, ← map_mul, Complex.conj_re]
  rcases hq with h | h | h | h
  · rw [h]
  · rw [h, aw_conj, hcX]; exact hconj
  · rw [h, aw_one_sub]
    have e : (l : ℂ) * (2 * (1 - ρ₀ - 1 / 2)) = -X := by rw [hX]; ring
    rw [e, neg_neg, add_comm]
  · rw [h, show (1 - conj ρ₀ : ℂ) = conj (1 - ρ₀) by rw [map_sub, map_one], aw_conj, aw_one_sub]
    have e : (l : ℂ) * (2 * (conj (1 - ρ₀) - 1 / 2)) = conj (-X) := by
      rw [hX, map_neg, map_mul, map_mul, map_sub, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_ofReal]
      ring
    rw [e, ← map_neg, Complex.exp_conj, Complex.exp_conj, ← map_add, ← map_mul, Complex.conj_re, neg_neg,
      add_comm]

lemma re_hw_quad {ρ₀ : ℂ} {q : ZIdx} (hq : q ∈ quad ρ₀) : (hw q).re = (aw ρ₀).re := by
  rw [mem_quad] at hq
  simp only [quadSet, Set.mem_ofPred_eq] at hq
  unfold hw
  rcases hq with h | h | h | h
  · rw [h]
  · rw [h, aw_conj, Complex.conj_re]
  · rw [h, aw_one_sub]
  · rw [h, show (1 - conj ρ₀ : ℂ) = conj (1 - ρ₀) by rw [map_sub, map_one], aw_conj, aw_one_sub,
      Complex.conj_re]

/-- The four zeros of a crossing are nontrivial zeros: `ζ(ρ̄) = conj ζ(ρ)`, and `ζ(1 − ρ)` vanishes with `ζ(ρ)` by the
functional equation. -/
lemma isNontrivialZero_quad {ρ₀ : ℂ} (hz : IsNontrivialZero ρ₀) (him : ρ₀.im ≠ 0) :
    IsNontrivialZero (conj ρ₀) ∧ IsNontrivialZero (1 - ρ₀) ∧ IsNontrivialZero (1 - conj ρ₀) := by
  have hnot : ∀ z : ℂ, z.im ≠ 0 → ¬ ∃ n : ℕ, z = -2 * (n + 1) := fun z hz ⟨n, hn⟩ => hz (by
    rw [hn]; simp)
  have hne : ∀ n : ℕ, ρ₀ ≠ -n := fun n h => him (by rw [h]; simp)
  have h1 : ρ₀ ≠ 1 := fun h => him (by rw [h]; simp)
  have hone : riemannZeta (1 - ρ₀) = 0 := by
    rw [riemannZeta_one_sub hne h1, hz.1, mul_zero]
  refine ⟨⟨by rw [riemannZeta_conj, hz.1, map_zero], hnot _ (by simpa using him)⟩,
    ⟨hone, hnot _ (by simpa using him)⟩, ⟨?_, hnot _ (by simpa using him)⟩⟩
  rw [show (1 - conj ρ₀ : ℂ) = conj (1 - ρ₀) by simp [map_sub], riemannZeta_conj, hone, map_zero]

/-- **The quadruple has at least four members** when `ρ₀` is off the line: the four values are distinct. -/
lemma four_le_card_quad {ρ₀ : ℂ} (hz : IsNontrivialZero ρ₀) (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0) :
    4 ≤ (quad ρ₀).card := by
  classical
  obtain ⟨hc, ho, hco⟩ := isNontrivialZero_quad hz him
  -- one index for each of the four values
  let ι : ℂ → ZIdx := fun v => if h : IsNontrivialZero v then ⟨⟨v, h⟩, ⟨0, zeroMult_pos _⟩⟩ else
    ⟨⟨ρ₀, hz⟩, ⟨0, zeroMult_pos _⟩⟩
  have hι : ∀ v, IsNontrivialZero v → zetaZeroFamily (ι v) = v := fun v h => by
    simp only [ι, h, ↓reduceDIte]; rfl
  set V : Finset ℂ := {ρ₀, conj ρ₀, 1 - ρ₀, 1 - conj ρ₀} with hV
  have hre' : (conj ρ₀).re = ρ₀.re := Complex.conj_re _
  have him' : (conj ρ₀).im = -ρ₀.im := Complex.conj_im _
  have hVcard : V.card = 4 := by
    rw [hV, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h; apply him; have := congrArg Complex.im h; simp at this; linarith
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := congrArg Complex.re h; simp at this; exact hre (by linarith)
      · have := congrArg Complex.re h; simp at this; exact hre (by linarith)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := congrArg Complex.im h; simp at this; exact him (by linarith)
      · have := congrArg Complex.re h; simp at this; exact hre (by linarith)
      · have := congrArg Complex.re h; simp at this; exact hre (by linarith)
  have hmaps : ∀ v ∈ V, ι v ∈ quad ρ₀ := by
    intro v hv
    rw [mem_quad]
    simp only [hV, Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [quadSet, Set.mem_ofPred_eq]
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inl (hι _ hz)
    · exact Or.inr (Or.inl (hι _ hc))
    · exact Or.inr (Or.inr (Or.inl (hι _ ho)))
    · exact Or.inr (Or.inr (Or.inr (hι _ hco)))
  have hinj : Set.InjOn ι V := by
    intro v hv v' hv' h
    have hnv : IsNontrivialZero v := by
      simp only [hV, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> assumption
    have hnv' : IsNontrivialZero v' := by
      simp only [hV, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
      rcases hv' with rfl | rfl | rfl | rfl <;> assumption
    rw [← hι v hnv, ← hι v' hnv', h]
  rw [← hVcard]
  exact Finset.card_le_card_of_injOn ι hmaps hinj

/-! ### The zeros outside the quadruple -/

/-- A zero on the line contributes at most `2Re a_q`: its term is `2cos(2λγ)/(¼ + γ²)`. -/
lemma gq_le_online {q : ZIdx} (hq : (zetaZeroFamily q).re = 1 / 2) (l : ℝ) : gq q l ≤ 2 * (hw q).re := by
  set t : ℝ := (zetaZeroFamily q).im with ht
  have hline : zetaZeroFamily q = 1 / 2 + I * t := by
    apply Complex.ext <;> simp [ht, hq]
  have hrr : zetaZeroFamily q * (1 - zetaZeroFamily q) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    rw [hline]; push_cast; linear_combination (-(t : ℂ) ^ 2) * Complex.I_sq
  have hP : poleP q = 2 * I * t := by unfold poleP; rw [hline]; ring
  have hpos : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  have hc : cexp ((l : ℂ) * (2 * I * t)) + cexp (-((l : ℂ) * (2 * I * t))) =
      2 * ((Real.cos (2 * l * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    have e1 : (l : ℂ) * (2 * I * t) = ((2 * l * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [e1, neg_mul]
    ring
  unfold gq hw aw
  rw [hrr, hP, hc]
  have e : (1 / ((1 / 4 + t ^ 2 : ℝ) : ℂ)) * (2 * ((Real.cos (2 * l * t) : ℝ) : ℂ)) =
      ((2 * Real.cos (2 * l * t) / (1 / 4 + t ^ 2) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / ((1 / 4 + t ^ 2 : ℝ) : ℂ)).re = 1 / (1 / 4 + t ^ 2) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [e, Complex.ofReal_re, e2]
  calc 2 * Real.cos (2 * l * t) / (1 / 4 + t ^ 2) ≤ 2 / (1 / 4 + t ^ 2) :=
        div_le_div_of_nonneg_right (by linarith [Real.cos_le_one (2 * l * t)]) hpos.le
    _ = 2 * (1 / (1 / 4 + t ^ 2)) := by ring

/-- A zero within `δ` of the line contributes at most `|a_q|(e^{2δλ} + 1)`, for `λ ≥ 0`. -/
lemma gq_le_offline {q : ZIdx} {δ l : ℝ} (hl : 0 ≤ l) (hq : |(zetaZeroFamily q).re - 1 / 2| ≤ δ) :
    gq q l ≤ ‖hw q‖ * (Real.exp (2 * δ * l) + 1) := by
  unfold gq
  calc (hw q * (cexp (l * poleP q) + cexp (-(l * poleP q)))).re
      ≤ ‖hw q * (cexp (l * poleP q) + cexp (-(l * poleP q)))‖ := Complex.re_le_norm _
    _ ≤ ‖hw q‖ * (‖cexp (l * poleP q)‖ + ‖cexp (-(l * poleP q))‖) := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖hw q‖ * (Real.exp (2 * δ * l) + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Complex.norm_exp, Complex.norm_exp]
        have e1 : ((l : ℂ) * poleP q).re = l * (poleP q).re := by simp
        have e2 : (-((l : ℂ) * poleP q)).re = -(l * (poleP q).re) := by simp
        rw [e1, e2]
        have hP : |(poleP q).re| ≤ 2 * δ := by
          rw [re_poleP, show 2 * (zetaZeroFamily q).re - 1 = 2 * ((zetaZeroFamily q).re - 1 / 2) by ring,
            abs_mul, abs_two]
          linarith
        obtain ⟨hlo, hhi⟩ := abs_le.1 hP
        rcases le_or_gt 0 (poleP q).re with h | h
        · have h1 : Real.exp (l * (poleP q).re) ≤ Real.exp (2 * δ * l) :=
            Real.exp_le_exp.2 (by nlinarith)
          have h2 : Real.exp (-(l * (poleP q).re)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
          linarith
        · have h1 : Real.exp (l * (poleP q).re) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
          have h2 : Real.exp (-(l * (poleP q).re)) ≤ Real.exp (2 * δ * l) :=
            Real.exp_le_exp.2 (by nlinarith)
          linarith

/-- The weight of the off-line zeros outside the quadruple of `ρ₀`. -/
def offMass (ρ₀ : ℂ) : ℝ :=
  ∑' q, if q ∉ quad ρ₀ ∧ (zetaZeroFamily q).re ≠ 1 / 2 then ‖hw q‖ else 0

lemma summable_offMass (ρ₀ : ℂ) :
    Summable fun q => if q ∉ quad ρ₀ ∧ (zetaZeroFamily q).re ≠ 1 / 2 then ‖hw q‖ else 0 :=
  summable_norm_hw.of_nonneg_of_le (fun q => by split_ifs <;> positivity) (fun q => by split_ifs <;> simp)

lemma offMass_nonneg (ρ₀ : ℂ) : 0 ≤ offMass ρ₀ := tsum_nonneg fun q => by split_ifs <;> positivity

/-- `ρ₀` is a **dominant** zero: no zero is further from the line, and the other off-line zeros weigh less than
`2|a_{ρ₀}|`. -/
structure Dominant (ρ₀ : ℂ) : Prop where
  extremal : ∀ q : ZIdx, |(zetaZeroFamily q).re - 1 / 2| ≤ ρ₀.re - 1 / 2
  mass : offMass ρ₀ < 2 * ‖aw ρ₀‖

/-- A sum over the zeros splits at a finite set. -/
lemma tsum_split_finset {f : ZIdx → ℝ} (hf : Summable f) (s : Finset ZIdx) :
    ∑' q, f q = ∑ q ∈ s, f q + ∑' q, (if q ∈ s then 0 else f q) := by
  have h1 : Summable fun q => if q ∈ s then f q else 0 :=
    summable_of_ne_finset_zero (s := s) fun q hq => by simp [hq]
  have h2 : Summable fun q => if q ∈ s then 0 else f q := by
    refine (hf.sub h1).congr fun q => ?_
    split_ifs <;> simp
  have e : ∀ q, f q = (if q ∈ s then f q else 0) + (if q ∈ s then 0 else f q) := fun q => by
    split_ifs <;> simp
  conv_lhs => rw [tsum_congr e]
  rw [h1.tsum_add h2, tsum_eq_sum (s := s) fun q hq => by simp [hq]]
  congr 1
  exact Finset.sum_congr rfl fun q hq => by simp [hq]

lemma hw_re_tsum : ∑' q, (hw q).re = H₀ := by
  rw [← Complex.re_tsum hasSum_hw.summable, hasSum_hw.tsum_eq, Complex.ofReal_re]

/-- **The twin sum of an extremal zero**: `Re W(λ) ≤ 4H₀ − 8Re a₀ + 4T(λ) + (e^{2δλ} + 1)M`, where `T(λ)` is the
term of `ρ₀` (nonpositive by hypothesis) and `M` the weight of the other off-line zeros. -/
lemma re_Wsum_le {ρ₀ : ℂ} (hz : IsNontrivialZero ρ₀) (hre : 1 / 2 < ρ₀.re) (him : 0 < ρ₀.im)
    (hext : ∀ q : ZIdx, |(zetaZeroFamily q).re - 1 / 2| ≤ ρ₀.re - 1 / 2) {l : ℝ} (hl : 0 ≤ l)
    (hT : (aw ρ₀ * (cexp (l * (2 * (ρ₀ - 1 / 2))) + cexp (-(l * (2 * (ρ₀ - 1 / 2)))))).re ≤ 0) :
    (Wsum poleP (fun q => hG (poleP q)) l).re ≤ 4 * H₀ - 8 * (aw ρ₀).re +
      4 * (aw ρ₀ * (cexp (l * (2 * (ρ₀ - 1 / 2))) + cexp (-(l * (2 * (ρ₀ - 1 / 2)))))).re +
      (Real.exp (2 * (ρ₀.re - 1 / 2) * l) + 1) * offMass ρ₀ := by
  set T := (aw ρ₀ * (cexp (l * (2 * (ρ₀ - 1 / 2))) + cexp (-(l * (2 * (ρ₀ - 1 / 2)))))).re with hTdef
  set δ := ρ₀.re - 1 / 2 with hδ
  have hcard := four_le_card_quad hz (by linarith) him.ne'
  have hcard' : (4 : ℝ) ≤ (quad ρ₀).card := by exact_mod_cast hcard
  -- `Re a₀ > 0`, through the index of `ρ₀`
  have ha0 : 0 < (aw ρ₀).re := re_hw_pos ⟨⟨ρ₀, hz⟩, ⟨0, zeroMult_pos _⟩⟩
  rw [re_Wsum, tsum_split_finset (summable_gq l) (quad ρ₀)]
  -- the quadruple
  have hquad : ∑ q ∈ quad ρ₀, gq q l ≤ 4 * T := by
    rw [Finset.sum_congr rfl fun q hq => gq_quad hq l, Finset.sum_const, nsmul_eq_mul]
    nlinarith
  -- outside the quadruple
  have hpt : ∀ q, (if q ∈ quad ρ₀ then 0 else gq q l) ≤
      (if q ∈ quad ρ₀ then 0 else 2 * (hw q).re) + (Real.exp (2 * δ * l) + 1) *
        (if q ∉ quad ρ₀ ∧ (zetaZeroFamily q).re ≠ 1 / 2 then ‖hw q‖ else 0) := by
    intro q
    by_cases hq : q ∈ quad ρ₀
    · simp [hq]
    · by_cases hon : (zetaZeroFamily q).re = 1 / 2
      · simp only [hq, hon, ne_eq, not_true_eq_false, and_false, ite_false, mul_zero, add_zero]
        exact gq_le_online hon l
      · simp only [hq, hon, ne_eq, not_false_eq_true, and_self, ite_true, ite_false]
        have h1 := gq_le_offline hl (hext q)
        have h0 := re_hw_pos q
        nlinarith [norm_nonneg (hw q), Real.exp_pos (2 * δ * l)]
  have hs1 : Summable fun q => if q ∈ quad ρ₀ then 0 else gq q l := by
    refine ((summable_gq l).sub (summable_of_ne_finset_zero (s := quad ρ₀) (f := fun q =>
      if q ∈ quad ρ₀ then gq q l else 0) fun q hq => by simp [hq])).congr fun q => ?_
    split_ifs <;> simp
  have hre : Summable fun q => (hw q).re := (Complex.hasSum_re hasSum_hw).summable
  have hs2a : Summable fun q => if q ∈ quad ρ₀ then 0 else 2 * (hw q).re := by
    refine ((hre.mul_left 2).sub (summable_of_ne_finset_zero (s := quad ρ₀) (f := fun q =>
      if q ∈ quad ρ₀ then 2 * (hw q).re else 0) fun q hq => by simp [hq])).congr fun q => ?_
    split_ifs <;> simp
  have hs2b := (summable_offMass ρ₀).mul_left (Real.exp (2 * δ * l) + 1)
  have hout := Summable.tsum_le_tsum hpt hs1 (hs2a.add hs2b)
  rw [hs2a.tsum_add hs2b, tsum_mul_left] at hout
  -- the on-line weight outside the quadruple
  have hsplit : ∑' q, 2 * (hw q).re = ∑ q ∈ quad ρ₀, 2 * (hw q).re +
      ∑' q, (if q ∈ quad ρ₀ then 0 else 2 * (hw q).re) := tsum_split_finset (hre.mul_left 2) (quad ρ₀)
  rw [tsum_mul_left, hw_re_tsum, Finset.sum_congr rfl (fun q hq => by rw [re_hw_quad hq]), Finset.sum_const,
    nsmul_eq_mul] at hsplit
  have hM : ∑' q, (if q ∉ quad ρ₀ ∧ (zetaZeroFamily q).re ≠ 1 / 2 then ‖hw q‖ else 0) = offMass ρ₀ := rfl
  rw [hM] at hout
  nlinarith

/-- The term of `ρ₀`: `Re(a₀(e^{λP₀} + e^{−λP₀})) ≤ |a₀|(e^{2δλ}cos(2γλ + arg a₀) + 1)` for `λ ≥ 0`. -/
lemma quad_term_le {ρ₀ : ℂ} (hre : 1 / 2 ≤ ρ₀.re) {l : ℝ} (hl : 0 ≤ l) :
    (aw ρ₀ * (cexp (l * (2 * (ρ₀ - 1 / 2))) + cexp (-(l * (2 * (ρ₀ - 1 / 2)))))).re ≤
      ‖aw ρ₀‖ * (Real.exp (2 * (ρ₀.re - 1 / 2) * l) * Real.cos (2 * ρ₀.im * l + Complex.arg (aw ρ₀)) + 1) := by
  rw [mul_add, Complex.add_re]
  have h1 : (aw ρ₀ * cexp (l * (2 * (ρ₀ - 1 / 2)))).re =
      ‖aw ρ₀‖ * (Real.exp (2 * (ρ₀.re - 1 / 2) * l) * Real.cos (2 * ρ₀.im * l + Complex.arg (aw ρ₀))) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (aw ρ₀)]
    rw [mul_assoc, ← Complex.exp_add, Complex.re_ofReal_mul, Complex.exp_re]
    congr 2
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.sub_re, Complex.re_ofNat, Complex.im_ofNat, Complex.sub_im,
        Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.sub_re, Complex.re_ofNat, Complex.im_ofNat, Complex.sub_im,
        Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
      ring
  have h2 : (aw ρ₀ * cexp (-(l * (2 * (ρ₀ - 1 / 2))))).re ≤ ‖aw ρ₀‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_exp]
    have e : (-((l : ℂ) * (2 * (ρ₀ - 1 / 2)))).re = -(2 * (ρ₀.re - 1 / 2) * l) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.re_ofNat, Complex.im_ofNat, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [e]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 (by nlinarith))
  rw [h1]
  linarith

/-- `Λ(ρ₀) = log((4H₀ + 4|a₀| + M)/(2|a₀| − M))/(2δ)`: the twin sum is negative at every `λ ≥ Λ` with
`cos(2γλ + arg a₀) ≤ −½`. -/
def lamMin (ρ₀ : ℂ) : ℝ :=
  Real.log ((4 * H₀ + 4 * ‖aw ρ₀‖ + offMass ρ₀) / (2 * ‖aw ρ₀‖ - offMass ρ₀)) / (2 * (ρ₀.re - 1 / 2))

lemma aw_ne_zero {ρ₀ : ℂ} (hz : IsNontrivialZero ρ₀) : aw ρ₀ ≠ 0 := fun h => by
  have := re_hw_pos ⟨⟨ρ₀, hz⟩, ⟨0, zeroMult_pos _⟩⟩
  change 0 < (aw ρ₀).re at this
  rw [h] at this
  simp at this

/-- The ratio inside `Λ` is at least `2`, so `Λ > 0`. -/
lemma two_le_ratio {ρ₀ : ℂ} (hD : Dominant ρ₀) :
    2 ≤ (4 * H₀ + 4 * ‖aw ρ₀‖ + offMass ρ₀) / (2 * ‖aw ρ₀‖ - offMass ρ₀) := by
  have hM := offMass_nonneg ρ₀
  have hden : 0 < 2 * ‖aw ρ₀‖ - offMass ρ₀ := by linarith [hD.mass]
  rw [le_div_iff₀ hden]
  linarith [H₀_pos]

lemma lamMin_pos {ρ₀ : ℂ} (hre : 1 / 2 < ρ₀.re) (hD : Dominant ρ₀) :
    0 < lamMin ρ₀ := by
  unfold lamMin
  have h2 := two_le_ratio hD
  exact div_pos (Real.log_pos (by linarith)) (by linarith)

/-- **The twin sum is negative** at every `λ ≥ Λ` with `cos(2γλ + arg a₀) ≤ −½`, for a dominant zero. -/
theorem re_Wsum_neg {ρ₀ : ℂ} (hz : IsNontrivialZero ρ₀) (hre : 1 / 2 < ρ₀.re) (him : 0 < ρ₀.im)
    (hD : Dominant ρ₀) {l : ℝ} (hl : lamMin ρ₀ ≤ l)
    (hcos : Real.cos (2 * ρ₀.im * l + Complex.arg (aw ρ₀)) ≤ -1 / 2) :
    (Wsum poleP (fun q => hG (poleP q)) l).re < 0 := by
  set a := ‖aw ρ₀‖ with ha
  set M := offMass ρ₀ with hMdef
  set δ := ρ₀.re - 1 / 2 with hδ
  set R := (4 * H₀ + 4 * a + M) / (2 * a - M) with hR
  have hδ0 : 0 < δ := by linarith
  have hM := offMass_nonneg ρ₀
  have hden : 0 < 2 * a - M := by linarith [hD.mass]
  have hR2 : 2 ≤ R := two_le_ratio hD
  have hl0 : 0 ≤ l := (lamMin_pos hre hD).le.trans hl
  have ha0 : 0 < a := norm_pos_iff.2 (aw_ne_zero hz)
  have hare : 0 < (aw ρ₀).re := re_hw_pos ⟨⟨ρ₀, hz⟩, ⟨0, zeroMult_pos _⟩⟩
  -- `e^{2δl} ≥ R`
  have hE : R ≤ Real.exp (2 * δ * l) := by
    have : Real.log R ≤ 2 * δ * l := by
      have h := hl
      unfold lamMin at h
      rw [← ha, ← hMdef, ← hδ, ← hR, div_le_iff₀ (by linarith)] at h
      linarith
    calc R = Real.exp (Real.log R) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (2 * δ * l) := Real.exp_le_exp.2 this
  have hE2 : 2 ≤ Real.exp (2 * δ * l) := hR2.trans hE
  -- the term of `ρ₀`
  have hT := quad_term_le hre.le hl0
  have hT' : (aw ρ₀ * (cexp (l * (2 * (ρ₀ - 1 / 2))) + cexp (-(l * (2 * (ρ₀ - 1 / 2)))))).re ≤
      a * (1 - Real.exp (2 * δ * l) / 2) := by
    refine hT.trans ?_
    have := mul_le_mul_of_nonneg_left hcos (mul_nonneg ha0.le (Real.exp_pos (2 * δ * l)).le)
    linarith
  have hT0 : (aw ρ₀ * (cexp (l * (2 * (ρ₀ - 1 / 2))) + cexp (-(l * (2 * (ρ₀ - 1 / 2)))))).re ≤ 0 :=
    hT'.trans (by linarith [mul_le_mul_of_nonneg_left hE2 ha0.le])
  have hW := re_Wsum_le hz hre him hD.extremal hl0 hT0
  -- `R(2a − M) = 4H₀ + 4a + M`
  have hRM : R * (2 * a - M) = 4 * H₀ + 4 * a + M := by rw [hR, div_mul_cancel₀ _ hden.ne']
  have hEM : R * (2 * a - M) ≤ Real.exp (2 * δ * l) * (2 * a - M) :=
    mul_le_mul_of_nonneg_right hE hden.le
  nlinarith

/-! ### The explicit level -/

/-- The phase `arg a₀` of the weight of `ρ₀`. -/
def phase (ρ₀ : ℂ) : ℝ := Complex.arg (aw ρ₀)

/-- The index of the first `λ ≥ Λ` with `2γλ + arg a₀ ≡ π (mod 2π)`. -/
def kStar (ρ₀ : ℂ) : ℤ := ⌈(2 * ρ₀.im * lamMin ρ₀ + phase ρ₀ - π) / (2 * π)⌉

/-- `λ* = (π − arg a₀ + 2πk)/(2γ)`, the first `λ ≥ Λ` with `cos(2γλ + arg a₀) = −1`. -/
def lamStar (ρ₀ : ℂ) : ℝ := (π - phase ρ₀ + 2 * π * kStar ρ₀) / (2 * ρ₀.im)

lemma lamStar_spec {ρ₀ : ℂ} (him : 0 < ρ₀.im) :
    lamMin ρ₀ ≤ lamStar ρ₀ ∧ lamStar ρ₀ < lamMin ρ₀ + π / ρ₀.im ∧
      2 * ρ₀.im * lamStar ρ₀ + phase ρ₀ = π + kStar ρ₀ * (2 * π) := by
  have hπ := Real.pi_pos
  have hk1 : (2 * ρ₀.im * lamMin ρ₀ + phase ρ₀ - π) / (2 * π) ≤ kStar ρ₀ := Int.le_ceil _
  have hk2 : (kStar ρ₀ : ℝ) < (2 * ρ₀.im * lamMin ρ₀ + phase ρ₀ - π) / (2 * π) + 1 := Int.ceil_lt_add_one _
  rw [div_le_iff₀ (by positivity)] at hk1
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ (by positivity)] at hk2
  refine ⟨?_, ?_, ?_⟩
  · unfold lamStar
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · unfold lamStar
    have e : (lamMin ρ₀ + π / ρ₀.im) * (2 * ρ₀.im) = 2 * ρ₀.im * lamMin ρ₀ + 2 * π := by
      field_simp
    rw [div_lt_iff₀ (by positivity), e]
    linarith
  · unfold lamStar
    field_simp
    ring

/-- `q₀ = ⌈6γ/π⌉`. -/
def qWit (ρ₀ : ℂ) : ℕ := ⌈6 * ρ₀.im / π⌉₊

/-- `p₀ = ⌈q₀ e^{λ*}⌉`. -/
def pWit (ρ₀ : ℂ) : ℕ := ⌈(qWit ρ₀ : ℝ) * Real.exp (lamStar ρ₀)⌉₊

/-- The witness vector: the minor at `(p², q²)` with the coefficients `(q, p)`. -/
def minorVec (p q : ℕ) : ℕ → ℝ := fun i => if i = p ^ 2 then q else if i = q ^ 2 then p else 0

/-- **The explicit level** `N₀ = (⌈6γ/π⌉·⌈e^{Λ + π/γ}⌉ + 1)²`. -/
def witnessLevel (ρ₀ : ℂ) : ℕ := (qWit ρ₀ * ⌈Real.exp (lamMin ρ₀ + π / ρ₀.im)⌉₊ + 1) ^ 2

lemma qWit_pos {ρ₀ : ℂ} (him : 0 < ρ₀.im) : 0 < qWit ρ₀ := Nat.ceil_pos.2 (by positivity)

/-- `log(p₀/q₀)` is within `π/(6γ)` above `λ*`, and `q₀ < p₀`. -/
lemma log_pWit_div {ρ₀ : ℂ} (him : 0 < ρ₀.im) (hls : 0 < lamStar ρ₀) :
    lamStar ρ₀ ≤ Real.log (pWit ρ₀ / qWit ρ₀) ∧
      Real.log (pWit ρ₀ / qWit ρ₀) ≤ lamStar ρ₀ + π / (6 * ρ₀.im) ∧ qWit ρ₀ < pWit ρ₀ := by
  have hπ := Real.pi_pos
  set q : ℝ := (qWit ρ₀ : ℝ) with hq
  set ls := lamStar ρ₀ with hlsdef
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast qWit_pos him
  have hq6 : 6 * ρ₀.im / π ≤ q := Nat.le_ceil _
  have hp1 : q * Real.exp ls ≤ pWit ρ₀ := Nat.le_ceil _
  have hp2 : (pWit ρ₀ : ℝ) < q * Real.exp ls + 1 := Nat.ceil_lt_add_one (by positivity)
  have hexp1 : 1 < Real.exp ls := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 hls
  have hp0 : (0 : ℝ) < pWit ρ₀ := lt_of_lt_of_le (by positivity) hp1
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hq0]
    linarith
  · have hpos : 0 < (pWit ρ₀ : ℝ) / q := by positivity
    have hprod : Real.exp ls * Real.exp (-ls) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hlt : (pWit ρ₀ : ℝ) / q ≤ Real.exp ls * (1 + Real.exp (-ls) / q) := by
      rw [div_le_iff₀ hq0, mul_add, mul_one, add_mul, mul_div_assoc', div_mul_cancel₀ _ hq0.ne', hprod]
      linarith
    have h1 : Real.log ((pWit ρ₀ : ℝ) / q) ≤ ls + Real.log (1 + Real.exp (-ls) / q) := by
      have := Real.log_le_log hpos hlt
      rwa [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp] at this
    have h2 : Real.log (1 + Real.exp (-ls) / q) ≤ Real.exp (-ls) / q := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-ls) / q by positivity)
      linarith
    have h3 : Real.exp (-ls) / q ≤ 1 / q :=
      div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by linarith)) hq0.le
    have h4 : 1 / q ≤ π / (6 * ρ₀.im) := by
      rw [div_le_div_iff₀ hq0 (by positivity)]
      have := mul_le_mul_of_nonneg_right hq6 hπ.le
      rw [div_mul_cancel₀ _ hπ.ne'] at this
      linarith
    linarith
  · have : q < pWit ρ₀ := by nlinarith
    rw [hq] at this
    exact_mod_cast this

/-- The cosine at `log(p₀/q₀)` is at most `−½`. -/
lemma cos_log_pWit {ρ₀ : ℂ} (him : 0 < ρ₀.im) (hls : 0 < lamStar ρ₀) :
    Real.cos (2 * ρ₀.im * Real.log (pWit ρ₀ / qWit ρ₀) + phase ρ₀) ≤ -1 / 2 := by
  obtain ⟨hlo, hhi, -⟩ := log_pWit_div him hls
  obtain ⟨-, -, hk⟩ := lamStar_spec him
  set η := 2 * ρ₀.im * (Real.log (pWit ρ₀ / qWit ρ₀) - lamStar ρ₀) with hη
  have hη0 : 0 ≤ η := by rw [hη]; nlinarith
  have hη1 : η ≤ π / 3 := by
    rw [hη]
    have : Real.log (pWit ρ₀ / qWit ρ₀) - lamStar ρ₀ ≤ π / (6 * ρ₀.im) := by linarith
    calc 2 * ρ₀.im * (Real.log (pWit ρ₀ / qWit ρ₀) - lamStar ρ₀) ≤ 2 * ρ₀.im * (π / (6 * ρ₀.im)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = π / 3 := by field_simp; ring
  have e : 2 * ρ₀.im * Real.log (pWit ρ₀ / qWit ρ₀) + phase ρ₀ = (η + π) + kStar ρ₀ * (2 * π) := by
    rw [hη]; linarith
  rw [e, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  have : Real.cos (π / 3) ≤ Real.cos η :=
    Real.cos_le_cos_of_nonneg_of_le_pi hη0 (by linarith [Real.pi_pos]) hη1
  rw [Real.cos_pi_div_three] at this
  linarith

/-- **The minor is the twin sum**: `Q_{p²}(qδ_{p²} + pδ_{q²}) = p²q²·Re W(log(p/q))` for `0 < q < p`. -/
lemma form_minorVec {p q : ℕ} (hq : 0 < q) (hpq : q < p) :
    form (p ^ 2) (minorVec p q) =
      (p : ℝ) ^ 2 * q ^ 2 * (Wsum poleP (fun q => hG (poleP q)) (Real.log (p / q))).re := by
  have hp : 0 < p := hq.trans hpq
  have hmN : p ^ 2 ∈ Icc 1 (p ^ 2) := Finset.mem_Icc.2 ⟨Nat.one_le_pow _ _ hp, le_rfl⟩
  have hnN : q ^ 2 ∈ Icc 1 (p ^ 2) :=
    Finset.mem_Icc.2 ⟨Nat.one_le_pow _ _ hq, Nat.pow_le_pow_left hpq.le 2⟩
  have hne : p ^ 2 ≠ q ^ 2 := fun e => hpq.ne' (Nat.pow_left_injective (by norm_num) e)
  unfold minorVec
  rw [form_two hmN hnN hne, gram_self, gram_self, gram_sq]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : (0 : ℝ) < ((p : ℝ) / q) ^ 2 := by positivity
  have hk1 : kψ 1 = (kerH 1).re := by rw [kerH_eq_kψ one_pos, Complex.ofReal_re]
  have hkr : kψ (((p : ℝ) / q) ^ 2) = (kerH (((p : ℝ) / q) ^ 2)).re := by
    rw [kerH_eq_kψ hr, Complex.ofReal_re]
  have hW := twin_eq_kerH (((p : ℝ) / q) ^ 2)
  rw [kerH_inv] at hW
  have hlog : Real.log (((p : ℝ) / q) ^ 2) / 2 = Real.log ((p : ℝ) / q) := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlog] at hW
  have hre : (Wsum poleP (fun q => hG (poleP q)) (Real.log ((p : ℝ) / q))).re =
      2 * kψ 1 + 2 * kψ (((p : ℝ) / q) ^ 2) := by
    rw [hW, hk1, hkr]
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    ring
  rw [hre]
  push_cast
  ring

lemma pWit_sq_le {ρ₀ : ℂ} (him : 0 < ρ₀.im) : pWit ρ₀ ^ 2 ≤ witnessLevel ρ₀ := by
  obtain ⟨-, hhi, -⟩ := lamStar_spec him
  have hq0 : (0 : ℝ) ≤ qWit ρ₀ := Nat.cast_nonneg _
  have h1 : (pWit ρ₀ : ℝ) < qWit ρ₀ * Real.exp (lamStar ρ₀) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : Real.exp (lamStar ρ₀) ≤ ⌈Real.exp (lamMin ρ₀ + π / ρ₀.im)⌉₊ :=
    (Real.exp_le_exp.2 hhi.le).trans (Nat.le_ceil _)
  have h3 : (pWit ρ₀ : ℝ) < (qWit ρ₀ * ⌈Real.exp (lamMin ρ₀ + π / ρ₀.im)⌉₊ + 1 : ℕ) + 1 := by
    push_cast
    nlinarith
  have h4 : pWit ρ₀ ≤ qWit ρ₀ * ⌈Real.exp (lamMin ρ₀ + π / ρ₀.im)⌉₊ + 1 := by
    have := (Nat.cast_lt (α := ℝ)).1 (by push_cast at h3 ⊢; linarith : (pWit ρ₀ : ℝ) <
      ((qWit ρ₀ * ⌈Real.exp (lamMin ρ₀ + π / ρ₀.im)⌉₊ + 1 + 1 : ℕ) : ℝ))
    omega
  exact Nat.pow_le_pow_left h4 2

/-- **The witness level.** A dominant crossing at `ρ₀ = β + iγ` (`β > ½`, `γ > 0`) is seen by the orbit form at the
level `p₀²`, on the minor vector `q₀δ_{p₀²} + p₀δ_{q₀²}`, with `p₀² ≤ N₀(ρ₀) = (⌈6γ/π⌉·⌈e^{Λ + π/γ}⌉ + 1)²`. -/
theorem witness_level {ρ₀ : ℂ} (hz : IsNontrivialZero ρ₀) (hre : 1 / 2 < ρ₀.re) (him : 0 < ρ₀.im)
    (hD : Dominant ρ₀) :
    pWit ρ₀ ^ 2 ≤ witnessLevel ρ₀ ∧ form (pWit ρ₀ ^ 2) (minorVec (pWit ρ₀) (qWit ρ₀)) < 0 := by
  refine ⟨pWit_sq_le him, ?_⟩
  obtain ⟨hlo, -, -⟩ := lamStar_spec him
  have hls : 0 < lamStar ρ₀ := (lamMin_pos hre hD).trans_le hlo
  obtain ⟨hlo', -, hqp⟩ := log_pWit_div him hls
  rw [form_minorVec (qWit_pos him) hqp]
  have hq0 : (0 : ℝ) < qWit ρ₀ := by exact_mod_cast qWit_pos him
  have hp0 : (0 : ℝ) < pWit ρ₀ := by exact_mod_cast (qWit_pos him).trans hqp
  apply mul_neg_of_pos_of_neg
  · positivity
  · exact re_Wsum_neg hz hre him hD (hlo.trans hlo') (cos_log_pWit him hls)

/-- **The witness level, as an existence statement**: `∃ N ≤ N₀(ρ₀), ∃ x, Q_N(x) < 0`. -/
theorem witness_level' {ρ₀ : ℂ} (hz : IsNontrivialZero ρ₀) (hre : 1 / 2 < ρ₀.re) (him : 0 < ρ₀.im)
    (hD : Dominant ρ₀) : ∃ N ≤ witnessLevel ρ₀, ∃ x : ℕ → ℝ, form N x < 0 :=
  ⟨_, (witness_level hz hre him hD).1, _, (witness_level hz hre him hD).2⟩

/-- A **single crossing**: every zero outside the quadruple of `ρ₀` lies on the line. -/
def SingleCrossing (ρ₀ : ℂ) : Prop := ∀ q : ZIdx, q ∉ quad ρ₀ → (zetaZeroFamily q).re = 1 / 2

/-- A single crossing is dominant, with `M = 0`. -/
lemma dominant_of_single {ρ₀ : ℂ} (hz : IsNontrivialZero ρ₀) (hre : 1 / 2 < ρ₀.re) (hS : SingleCrossing ρ₀) :
    Dominant ρ₀ where
  extremal q := by
    by_cases hq : q ∈ quad ρ₀
    · rw [mem_quad] at hq
      simp only [quadSet, Set.mem_ofPred_eq] at hq
      rcases hq with h | h | h | h <;> rw [h]
      · rw [abs_of_pos (by linarith)]
      · rw [Complex.conj_re, abs_of_pos (by linarith)]
      · rw [Complex.sub_re, Complex.one_re, show 1 - ρ₀.re - 1 / 2 = -(ρ₀.re - 1 / 2) by ring, abs_neg,
          abs_of_pos (by linarith)]
      · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, show 1 - ρ₀.re - 1 / 2 = -(ρ₀.re - 1 / 2) by ring,
          abs_neg, abs_of_pos (by linarith)]
    · rw [hS q hq]; simp; linarith
  mass := by
    have h0 : offMass ρ₀ = 0 := by
      unfold offMass
      have e : (fun q : ZIdx => if q ∉ quad ρ₀ ∧ (zetaZeroFamily q).re ≠ 1 / 2 then ‖hw q‖ else 0) =
          fun _ => 0 := funext fun q => by
        split_ifs with h
        · exact absurd (hS q h.1) h.2
        · rfl
      rw [e, tsum_zero]
    rw [h0]
    exact mul_pos two_pos (norm_pos_iff.2 (aw_ne_zero hz))

/-- **A single crossing is seen at `N₀(β, γ)`.** -/
theorem witness_level_single {ρ₀ : ℂ} (hz : IsNontrivialZero ρ₀) (hre : 1 / 2 < ρ₀.re) (him : 0 < ρ₀.im)
    (hS : SingleCrossing ρ₀) : ∃ N ≤ witnessLevel ρ₀, ∃ x : ℕ → ℝ, form N x < 0 :=
  witness_level' hz hre him (dominant_of_single hz hre hS)

end Witness

/-! ## The rate under RH and a sampling inequality

Under RH, `Q_N(x) = Σ_ρ |V_x(ρ)|²/(¼ + γ²)` with `V_x(s) = Σ_{n ≤ N} x_n n^s` (`hasSum_form`), from the realization
`BallHadamard.realizationH`. A sampling inequality for these Dirichlet polynomials at the zeros of height at most
`T ≥ C N^{1+θ}` then bounds `λ_N` below by `(c/2C)·N^{−1−θ}` (`rate_of_sampling`). -/

section Rate

open BallHadamard BallLattice
open scoped InnerProductSpace

/-- The Dirichlet polynomial of a real vector at the zero `ρ_q`: `V_x(ρ_q) = Σ_{n ≤ N} x_n n^{ρ_q}`. -/
def dpoly (N : ℕ) (x : ℕ → ℝ) (q : ZIdx) : ℂ := ∑ n ∈ Icc 1 N, (x n : ℂ) * pw q n

lemma coord_eq (N : ℕ) (x : ℕ → ℝ) (q : ZIdx) :
    (∑ n ∈ Icc 1 N, (x n : ℂ) • wvOf cH summable_cH_sq (n : ℚ)) q = cH q * dpoly N x q := by
  rw [lp.coeFn_sum, Finset.sum_apply, dpoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, wvOf_apply, Rat.cast_natCast]
  ring

/-- Under RH, `|c_ρ|² = 1/(¼ + γ²)`. -/
lemma norm_cH_sq (hRH : RiemannHypothesis) (q : ZIdx) :
    ‖cH q‖ ^ 2 = 1 / (1 / 4 + (zetaZeroFamily q).im ^ 2) := by
  set t : ℝ := (zetaZeroFamily q).im with ht
  have hline : zetaZeroFamily q = 1 / 2 + Complex.I * t := by
    have h := line_of_RH hRH q
    apply Complex.ext <;> simp [ht, h]
  have hrr : zetaZeroFamily q * (1 - zetaZeroFamily q) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    rw [hline]; push_cast; linear_combination (-(t : ℂ) ^ 2) * Complex.I_sq
  have hpos : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  unfold cH
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (inv_nonneg.2 (norm_nonneg _)),
    hrr, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  exact (one_div _).symm

/-- **The form under RH as a sum over the zeros**: `Q_N(x) = Σ_ρ |V_x(ρ)|²/(¼ + γ²)`. -/
theorem hasSum_form (hRH : RiemannHypothesis) (N : ℕ) (x : ℕ → ℝ) :
    HasSum (fun q => ‖dpoly N x q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2)) (form N x) := by
  have hform := form_eq_norm_sq (realizationH hRH) N x
  change form N x = ‖(∑ n ∈ Icc 1 N, (x n : ℂ) • wvOf cH summable_cH_sq (n : ℚ) : L2)‖ ^ 2 at hform
  set v : L2 := ∑ n ∈ Icc 1 N, (x n : ℂ) • wvOf cH summable_cH_sq (n : ℚ) with hv
  have key : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (w : E), (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 :=
    fun E _ _ w => by rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
  have hre := Complex.hasSum_re (lp.hasSum_inner v v)
  rw [key, ← hform] at hre
  refine hre.congr_fun fun q => ?_
  rw [key, hv, coord_eq, norm_mul, mul_pow, norm_cH_sq hRH]
  ring

/-- The zeros of height at most `T` are finitely many. -/
lemma heightLe_finite (T : ℝ) : {q : ZIdx | |(zetaZeroFamily q).im| ≤ T}.Finite := by
  refine (finite_poleP (2 * Real.sqrt (1 / 4 + T ^ 2))).subset fun q hq => ?_
  simp only [Set.mem_ofPred_eq] at hq ⊢
  unfold poleP
  rw [norm_mul, Complex.norm_two]
  refine mul_le_mul_of_nonneg_left ?_ two_pos.le
  rw [← Real.sqrt_sq (norm_nonneg (zetaZeroFamily q - 1 / 2))]
  refine Real.sqrt_le_sqrt ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hb := abs_re_poleP q
  rw [re_poleP] at hb
  have h1 : (zetaZeroFamily q - 1 / 2).re = (zetaZeroFamily q).re - 1 / 2 := by simp
  have h2 : (zetaZeroFamily q - 1 / 2).im = (zetaZeroFamily q).im := by simp
  rw [h1, h2]
  have hb' : ((zetaZeroFamily q).re - 1 / 2) ^ 2 ≤ 1 / 4 := by
    have := abs_lt.1 hb
    nlinarith
  have ht : (zetaZeroFamily q).im ^ 2 ≤ T ^ 2 := by
    have := sq_abs (zetaZeroFamily q).im
    nlinarith [abs_nonneg (zetaZeroFamily q).im]
  nlinarith

/-- The zeros of height at most `T`. -/
def zerosUpTo (T : ℝ) : Finset ZIdx := (heightLe_finite T).toFinset

lemma mem_zerosUpTo {T : ℝ} {q : ZIdx} : q ∈ zerosUpTo T ↔ |(zetaZeroFamily q).im| ≤ T := by
  unfold zerosUpTo
  rw [Set.Finite.mem_toFinset]
  rfl

/-- **The sampling hypothesis** `SamplingAtZeros c C θ`: for every `N ≥ 1`, every real vector `x` on `[1, N]` and
every `T ≥ C·N^{1+θ}`, `Σ_{|γ_ρ| ≤ T} |V_x(ρ)|² ≥ c·T·Σ_{n ≤ N} x_n² n`: the zeros up to height `T` sample the
Dirichlet polynomials of length `N`. A hypothesis. -/
def SamplingAtZeros (c C θ : ℝ) : Prop :=
  ∀ (N : ℕ) (x : ℕ → ℝ) (T : ℝ), 1 ≤ N → C * (N : ℝ) ^ (1 + θ) ≤ T →
    c * T * ∑ n ∈ Icc 1 N, x n ^ 2 * n ≤ ∑ q ∈ zerosUpTo T, ‖dpoly N x q‖ ^ 2

/-- **The rate**: under RH and sampling at `(c, C, θ)` with `c > 0`, `C ≥ 1`, `θ ≥ 0`,
`Q_N(x) ≥ (c/2C)·N^{−1−θ}·Σ x_n²` for every `N ≥ 1`: `λ_N ≥ (c/2C)·N^{−1−θ}`. -/
theorem rate_of_sampling (hRH : RiemannHypothesis) {c C θ : ℝ} (hc : 0 < c) (hC : 1 ≤ C) (hθ : 0 ≤ θ)
    (hS : SamplingAtZeros c C θ) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    c / (2 * C) * (N : ℝ) ^ (-(1 + θ)) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ form N x := by
  set T : ℝ := C * (N : ℝ) ^ (1 + θ) with hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : 1 ≤ (N : ℝ) ^ (1 + θ) := Real.one_le_rpow hN1 (by linarith)
  have hNp0 : 0 < (N : ℝ) ^ (1 + θ) := by linarith
  have hT1 : 1 ≤ T := by rw [hT]; nlinarith
  have hT0 : 0 < T := by linarith
  have hC0 : 0 < C := by linarith
  have hsum := hasSum_form hRH N x
  have hpart : ∑ q ∈ zerosUpTo T, ‖dpoly N x q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤ form N x := by
    rw [← hsum.tsum_eq]
    exact Summable.sum_le_tsum (zerosUpTo T) (fun q _ => by positivity) hsum.summable
  have hterm : ∀ q ∈ zerosUpTo T, ‖dpoly N x q‖ ^ 2 / (2 * T ^ 2) ≤
      ‖dpoly N x q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2) := by
    intro q hq
    rw [mem_zerosUpTo] at hq
    have h1 : (zetaZeroFamily q).im ^ 2 ≤ T ^ 2 := by
      have := sq_abs (zetaZeroFamily q).im
      nlinarith [abs_nonneg (zetaZeroFamily q).im]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith
  have hS' := hS N x T hN (le_of_eq hT)
  have hx : ∑ n ∈ Icc 1 N, x n ^ 2 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * n :=
    Finset.sum_le_sum fun n hn => by
      have : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
      nlinarith [sq_nonneg (x n)]
  have hx0 : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  calc c / (2 * C) * (N : ℝ) ^ (-(1 + θ)) * ∑ n ∈ Icc 1 N, x n ^ 2
      = c / (2 * T) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
        rw [hT, Real.rpow_neg (by positivity)]
        field_simp
    _ ≤ c / (2 * T) * ∑ n ∈ Icc 1 N, x n ^ 2 * n := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = (c * T * ∑ n ∈ Icc 1 N, x n ^ 2 * n) / (2 * T ^ 2) := by
        field_simp
    _ ≤ (∑ q ∈ zerosUpTo T, ‖dpoly N x q‖ ^ 2) / (2 * T ^ 2) :=
        div_le_div_of_nonneg_right hS' (by positivity)
    _ = ∑ q ∈ zerosUpTo T, ‖dpoly N x q‖ ^ 2 / (2 * T ^ 2) := by rw [Finset.sum_div]
    _ ≤ ∑ q ∈ zerosUpTo T, ‖dpoly N x q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2) := Finset.sum_le_sum hterm
    _ ≤ form N x := hpart

end Rate

/-! ## The flat model has a uniform margin

With Lebesgue measure for the zeros the kernel is `K₀(x) = e^{−|log x|/2}` and the Gram matrix `√(mn)K₀(m/n)` is
`min(m, n)` (`BallFlat.gram_flat`); scaled by `K_H(1) = H₀` it is `H₀·min(m, n)`, the covariance of Brownian motion.
Its form is `H₀·Σ_k S_k²` for the tail sums `S_k = Σ_{n ≥ k} x_n` (`sum_min_eq`), and `x_n = S_n − S_{n+1}` gives
`Σ x_n² ≤ 4Σ S_k²`: the smallest eigenvalue is at least `H₀/4` at every level (`flat_margin`). -/

section Flat

/-- The flat orbit form `Σ_{m,n ≤ N} x_m x_n·H₀·min(m, n)`. -/
def flatForm (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * (H₀ * ((min m n : ℕ) : ℝ))

/-- The flat form is the orbit form of the flat kernel, scaled by `H₀`. -/
lemma flatForm_eq_kerFlat (N : ℕ) (x : ℕ → ℝ) :
    flatForm N x = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      x m * x n * (H₀ * (Real.sqrt ((m : ℝ) * n) * BallFlat.kerFlat ((m : ℝ) / n))) := by
  unfold flatForm
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
  rw [BallFlat.gram_flat hm0 hn0, Nat.cast_min]

/-- The tail sums `S_k = Σ_{k ≤ n ≤ N} x_n`. -/
def tailSum (N : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ := ∑ n ∈ Icc k N, x n

/-- **Telescoping**: `Σ_{m,n ≤ N} x_m x_n min(m, n) = Σ_{k=1}^N S_k²`. -/
lemma sum_min_eq (N : ℕ) (x : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * ((min m n : ℕ) : ℝ) = ∑ k ∈ Icc 1 N, tailSum N x k ^ 2 := by
  have hmin : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
      ((min m n : ℕ) : ℝ) = ∑ k ∈ Icc 1 N, (if k ≤ m then (1 : ℝ) else 0) * (if k ≤ n then 1 else 0) := by
    intro m hm n hn
    have hm' := Finset.mem_Icc.1 hm
    have hn' := Finset.mem_Icc.1 hn
    have e : ∀ k, (if k ≤ m then (1 : ℝ) else 0) * (if k ≤ n then 1 else 0) =
        if k ≤ m ∧ k ≤ n then 1 else 0 := fun k => by
      by_cases h1 : k ≤ m <;> by_cases h2 : k ≤ n <;> simp [h1, h2]
    simp_rw [e]
    rw [Finset.sum_boole]
    have hf : (Icc 1 N).filter (fun k => k ≤ m ∧ k ≤ n) = Icc 1 (min m n) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
      omega
    rw [hf, Nat.card_Icc, Nat.add_sub_cancel]
  have htail : ∀ k ∈ Icc 1 N, ∑ m ∈ Icc 1 N, x m * (if k ≤ m then (1 : ℝ) else 0) = tailSum N x k := by
    intro k hk
    unfold tailSum
    have h1 : Icc k N = (Icc 1 N).filter (fun m => k ≤ m) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc]
      have := Finset.mem_Icc.1 hk
      omega
    rw [h1, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  calc ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * ((min m n : ℕ) : ℝ)
      = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
          (x m * (if k ≤ m then (1 : ℝ) else 0)) * (x n * (if k ≤ n then 1 else 0)) := by
        refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
        rw [hmin m hm n hn, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ k ∈ Icc 1 N, (∑ m ∈ Icc 1 N, x m * (if k ≤ m then (1 : ℝ) else 0)) *
          (∑ n ∈ Icc 1 N, x n * (if k ≤ n then (1 : ℝ) else 0)) := by
        rw [Finset.sum_congr rfl fun m _ => Finset.sum_comm, Finset.sum_comm]
        simp_rw [Finset.sum_mul_sum]
    _ = ∑ k ∈ Icc 1 N, tailSum N x k ^ 2 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [htail k hk, sq]

lemma tailSum_succ_top (N : ℕ) (x : ℕ → ℝ) : tailSum N x (N + 1) = 0 := by
  unfold tailSum
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]

lemma tailSum_eq {N n : ℕ} (hn : n ≤ N) (x : ℕ → ℝ) : tailSum N x n = x n + tailSum N x (n + 1) := by
  unfold tailSum
  rw [Finset.Icc_eq_cons_Ioc hn, Finset.sum_cons, Finset.Icc_add_one_left_eq_Ioc]

/-- The shifted sum of squares: `Σ_{k=1}^N S_{k+1}² + S_1² = Σ_{k=1}^N S_k² + S_{N+1}²`. -/
lemma sum_shift (N : ℕ) (T : ℕ → ℝ) :
    ∑ k ∈ Icc 1 N, T (k + 1) + T 1 = ∑ k ∈ Icc 1 N, T k + T (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    linarith

/-- `Σ x_n² ≤ 4Σ S_k²`, from `x_n = S_n − S_{n+1}`. -/
lemma sum_sq_le_four_tail (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, x n ^ 2 ≤ 4 * ∑ k ∈ Icc 1 N, tailSum N x k ^ 2 := by
  have h1 : ∑ n ∈ Icc 1 N, x n ^ 2 ≤
      ∑ n ∈ Icc 1 N, (2 * tailSum N x n ^ 2 + 2 * tailSum N x (n + 1) ^ 2) := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [show x n = tailSum N x n - tailSum N x (n + 1) by
      rw [tailSum_eq (Finset.mem_Icc.1 hn).2]; ring]
    nlinarith [sq_nonneg (tailSum N x n + tailSum N x (n + 1))]
  have h2 := sum_shift N (fun k => tailSum N x k ^ 2)
  simp only [tailSum_succ_top] at h2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  nlinarith [sq_nonneg (tailSum N x 1)]

/-- **The flat model's margin**: `Σ_{m,n ≤ N} x_m x_n·H₀·min(m, n) ≥ (H₀/4)·Σ x_n²` for every `N` and every real
`x`: with Lebesgue measure for the zeros, `λ_N ≥ H₀/4` at every level. -/
theorem flat_margin (N : ℕ) (x : ℕ → ℝ) : H₀ / 4 * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ flatForm N x := by
  have e : flatForm N x = H₀ * ∑ k ∈ Icc 1 N, tailSum N x k ^ 2 := by
    unfold flatForm
    rw [← sum_min_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [e]
  have := sum_sq_le_four_tail N x
  have h0 := H₀_pos
  nlinarith

end Flat

/-! ## The approach: `lim sup λ_N ≤ 0`, unconditionally

Under RH the two-point vector `x = δ_n − √n·δ_1` has `Q_N(x) = 2n(H₀ − K_H(n))` and `Σ x² = n + 1`
(`form_twoPt`), with `H₀ − K_H(n) = Σ_ρ (1 − cos(γ log n))/(¼ + γ²)` (`defect_eq`, from
`BallHadamard.kerH_second_diff`). The finitely many zeros that carry all but `ε/8` of the weight `Σ_ρ 1/(¼ + γ²) = H₀`
are brought to within `η` of `2πℤ` at once, at an `n` as large as wanted, by simultaneous Dirichlet approximation on
their ordinates (`exists_simultaneous`): so `λ_N ≤ ε` from some level on (`approach`). If RH fails, a negative
vector appears at some level and persists (`neg_persists`). The test vector is explicit given the first ordinates;
the level is not. -/

section Approach

open BallHadamard

/-- **Simultaneous Dirichlet approximation**, by the pigeonhole principle: for finitely many reals `α_i` and `Q ≥ 1`
there is `1 ≤ m ≤ Q^J` with every `m·α_i` within `1/Q` of an integer. -/
theorem exists_simultaneous {ι : Type*} [Fintype ι] (α : ι → ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ m : ℕ, 0 < m ∧ m ≤ Q ^ Fintype.card ι ∧ ∀ i, ∃ k : ℤ, |m * α i - k| ≤ 1 / Q := by
  classical
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  let g : Fin (Q ^ Fintype.card ι + 1) → (ι → Fin Q) := fun j i =>
    ⟨⌊Int.fract ((j : ℝ) * α i) * Q⌋₊, by
      have h1 := Int.fract_lt_one ((j : ℝ) * α i)
      rw [Nat.floor_lt (by positivity)]
      nlinarith⟩
  have hcard : Fintype.card (ι → Fin Q) < Fintype.card (Fin (Q ^ Fintype.card ι + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨j, j', hne, hjj⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  wlog hlt : j < j' generalizing j j'
  · exact this j' j hne.symm hjj.symm (lt_of_le_of_ne (not_lt.1 hlt) hne.symm)
  have hjlt : (j : ℕ) < j' := hlt
  refine ⟨j' - j, by omega, by omega, fun i => ?_⟩
  have hbox : ⌊Int.fract ((j' : ℝ) * α i) * Q⌋₊ = ⌊Int.fract ((j : ℝ) * α i) * Q⌋₊ := by
    have := congrArg (fun f => (f i : ℕ)) hjj
    simpa [g] using this.symm
  -- the two fractional parts are within `1/Q`
  set a := Int.fract ((j : ℝ) * α i) with ha
  set b := Int.fract ((j' : ℝ) * α i) with hb
  have hfl : ∀ y : ℝ, 0 ≤ y → (⌊y * Q⌋₊ : ℝ) ≤ y * Q ∧ y * Q < ⌊y * Q⌋₊ + 1 := fun y hy =>
    ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  obtain ⟨ha1, ha2⟩ := hfl a (Int.fract_nonneg _)
  obtain ⟨hb1, hb2⟩ := hfl b (Int.fract_nonneg _)
  rw [hbox] at hb1 hb2
  have h1 : b - a < 1 / Q := by rw [lt_div_iff₀ hQ']; linarith
  have h2 : a - b < 1 / Q := by rw [lt_div_iff₀ hQ']; linarith
  have hab : |b - a| ≤ 1 / Q := abs_le.2 ⟨by linarith, h1.le⟩
  refine ⟨⌊(j' : ℝ) * α i⌋ - ⌊(j : ℝ) * α i⌋, ?_⟩
  have e : ((j' - j : ℕ) : ℝ) * α i - ((⌊(j' : ℝ) * α i⌋ - ⌊(j : ℝ) * α i⌋ : ℤ) : ℝ) = b - a := by
    rw [hb, ha, Nat.cast_sub hjlt.le]
    push_cast
    rw [← Int.self_sub_floor, ← Int.self_sub_floor]
    ring
  rw [e]
  exact hab

/-- The approximation with `m ≥ m₀`: `m₀·m` for the `m` of `exists_simultaneous` at `Q·m₀`. -/
theorem exists_simultaneous_ge {ι : Type*} [Fintype ι] (α : ι → ℝ) {Q m₀ : ℕ} (hQ : 0 < Q) (hm₀ : 0 < m₀) :
    ∃ m : ℕ, m₀ ≤ m ∧ ∀ i, ∃ k : ℤ, |m * α i - k| ≤ 1 / Q := by
  obtain ⟨m, hm0, -, hm⟩ := exists_simultaneous α (Q := Q * m₀) (by positivity)
  refine ⟨m₀ * m, Nat.le_mul_of_pos_right _ hm0, fun i => ?_⟩
  obtain ⟨k, hk⟩ := hm i
  refine ⟨m₀ * k, ?_⟩
  have hm₀' : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have e : ((m₀ * m : ℕ) : ℝ) * α i - ((m₀ * k : ℤ) : ℝ) = m₀ * ((m : ℝ) * α i - k) := by
    push_cast
    ring
  rw [e, abs_mul, abs_of_pos hm₀']
  calc (m₀ : ℝ) * |(m : ℝ) * α i - k| ≤ m₀ * (1 / ((Q * m₀ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hk hm₀'.le
    _ = 1 / Q := by
        push_cast
        field_simp

/-- `|sin x| ≤ |x|`. -/
lemma abs_sin_le_abs' (x : ℝ) : |Real.sin x| ≤ |x| := by
  have key : ∀ y : ℝ, 0 ≤ y → |Real.sin y| ≤ y := fun y hy => by
    rw [abs_le]
    refine ⟨?_, Real.sin_le hy⟩
    rcases le_or_gt y π with h | h
    · linarith [Real.sin_nonneg_of_nonneg_of_le_pi hy h]
    · linarith [Real.neg_one_le_sin y, Real.pi_gt_three]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]; exact key x h
  · rw [abs_of_neg h, ← abs_neg, ← Real.sin_neg]; exact key (-x) (by linarith)

/-- `1 − cos θ ≤ θ²/2`. -/
lemma one_sub_cos_le (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  have h2 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul, Real.cos_sq']
    ring_nf
  have hs : Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := by
    rw [← sq_abs (Real.sin _), ← sq_abs (θ / 2)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_sin_le_abs' _) 2
  rw [h2]
  nlinarith

/-- The two-point vector `δ_n − √n·δ_1`. -/
def twoPt (n : ℕ) : ℕ → ℝ := fun i => if i = n then 1 else if i = 1 then -Real.sqrt n else 0

/-- `Q_N(δ_n − √n·δ_1) = 2n(H₀ − K_H(n))` for `2 ≤ n ≤ N`. -/
lemma form_twoPt {n N : ℕ} (hn : 2 ≤ n) (hN : n ≤ N) : form N (twoPt n) = 2 * n * (H₀ - kψ n) := by
  have hmN : n ∈ Icc 1 N := Finset.mem_Icc.2 ⟨by omega, hN⟩
  have h1N : 1 ∈ Icc 1 N := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hne : n ≠ 1 := by omega
  unfold twoPt
  rw [form_two hmN h1N hne, gram_self, gram_self, gram_comm, gram, kψ_one_eq]
  have hsq : Real.sqrt ((1 : ℕ) * (n : ℕ) : ℝ) = Real.sqrt n := by simp
  have hdiv : ((1 : ℕ) : ℝ) / (n : ℕ) = ((n : ℝ))⁻¹ := by simp
  rw [hsq, hdiv, kψ_inv]
  have := Real.mul_self_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  push_cast
  linear_combination (H₀ - 2 * kψ ↑n) * this

lemma sum_sq_twoPt {n N : ℕ} (hn : 2 ≤ n) (hN : n ≤ N) :
    ∑ i ∈ Icc 1 N, twoPt n i ^ 2 = 1 + n := by
  have hne : n ≠ 1 := by omega
  have e : ∀ i, twoPt n i ^ 2 = (if i = n then (1 : ℝ) else 0) + (if i = 1 then (n : ℝ) else 0) := by
    intro i
    unfold twoPt
    by_cases hi : i = n
    · subst hi; simp [hne]
    · by_cases hi1 : i = 1
      · subst hi1; simp [Ne.symm hne, Real.sq_sqrt (Nat.cast_nonneg n)]
      · simp [hi, hi1]
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Finset.mem_Icc.2 ⟨show 1 ≤ n by omega, hN⟩, Finset.mem_Icc.2 ⟨le_rfl, show 1 ≤ N by omega⟩]

/-- Under RH, the weight of the zero `ρ_q` is `1/(¼ + γ_q²)`. -/
lemma hw_re_rh (hRH : RiemannHypothesis) (q : ZIdx) : (hw q).re = 1 / (1 / 4 + (zetaZeroFamily q).im ^ 2) := by
  set t : ℝ := (zetaZeroFamily q).im with ht
  have hline : zetaZeroFamily q = 1 / 2 + Complex.I * t := by
    have h := line_of_RH hRH q
    apply Complex.ext <;> simp [ht, h]
  have hrr : zetaZeroFamily q * (1 - zetaZeroFamily q) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    rw [hline]; push_cast; linear_combination (-(t : ℂ) ^ 2) * Complex.I_sq
  unfold hw aw
  rw [hrr, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]

/-- **The defect under RH**: `H₀ − K_H(n) = Σ_ρ (1 − cos(γ log n))/(¼ + γ²)`. -/
lemma defect_eq (hRH : RiemannHypothesis) {n : ℕ} (hn : 0 < n) :
    H₀ - kψ n = ∑' q, (1 - Real.cos ((zetaZeroFamily q).im * Real.log n)) /
      (1 / 4 + (zetaZeroFamily q).im ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := kerH_second_diff hRH n
  rw [kerH_inv, kerH_eq_kψ hn0, kerH_eq_kψ one_pos, kψ_one_eq] at h
  have h2 : ((2 * kψ n - 2 * H₀ : ℝ) : ℂ) = ((-(∑' q : ZIdx, (2 - 2 * Real.cos ((zetaZeroFamily q).im *
      Real.log n)) / (1 / 4 + (zetaZeroFamily q).im ^ 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
    linear_combination h
  have h3 := Complex.ofReal_injective h2
  have e : ∑' q : ZIdx, (2 - 2 * Real.cos ((zetaZeroFamily q).im * Real.log n)) /
      (1 / 4 + (zetaZeroFamily q).im ^ 2) = 2 * ∑' q : ZIdx, (1 - Real.cos ((zetaZeroFamily q).im * Real.log n)) /
      (1 / 4 + (zetaZeroFamily q).im ^ 2) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun q => by ring
  rw [e] at h3
  linarith

/-- The summable weights `1/(¼ + γ²)` under RH, with sum `H₀`. -/
lemma hasSum_weights (hRH : RiemannHypothesis) :
    HasSum (fun q : ZIdx => 1 / (1 / 4 + (zetaZeroFamily q).im ^ 2)) H₀ := by
  have h := Complex.hasSum_re hasSum_hw
  rw [Complex.ofReal_re] at h
  exact h.congr_fun fun q => (hw_re_rh hRH q).symm

/-- Under RH, a term of the defect is at most twice the weight. -/
lemma defect_term_le (q : ZIdx) (u : ℝ) :
    (1 - Real.cos ((zetaZeroFamily q).im * u)) / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤
      2 * (1 / (1 / 4 + (zetaZeroFamily q).im ^ 2)) := by
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (by linarith [Real.neg_one_le_cos ((zetaZeroFamily q).im * u)]) (by positivity)

lemma defect_term_nonneg (q : ZIdx) (u : ℝ) :
    0 ≤ (1 - Real.cos ((zetaZeroFamily q).im * u)) / (1 / 4 + (zetaZeroFamily q).im ^ 2) :=
  div_nonneg (by linarith [Real.cos_le_one ((zetaZeroFamily q).im * u)]) (by positivity)

/-- For a finite set of zeros and `η > 0`, some `n ≥ n₁` has every `γ_q log n` within `η` of `2πℤ`: simultaneous
Dirichlet approximation on the ratios `γ_q/γ_{q₁}` gives `u = 2πm/γ_{q₁}`, and `n = ⌈e^u⌉` has `log n` within
`e^{−u}` of `u`. -/
lemma exists_near_two_pi (F : Finset ZIdx) {η : ℝ} (hη : 0 < η) (n₁ : ℕ) :
    ∃ n : ℕ, n₁ ≤ n ∧ 2 ≤ n ∧
      ∀ q ∈ F, ∃ k : ℤ, |(zetaZeroFamily q).im * Real.log n - k * (2 * π)| ≤ η := by
  classical
  have hπ := Real.pi_pos
  set Γ : ℝ := ∑ q ∈ F, |(zetaZeroFamily q).im| + 1 with hΓdef
  have hΓ1 : 1 ≤ Γ := by
    have : 0 ≤ ∑ q ∈ F, |(zetaZeroFamily q).im| := Finset.sum_nonneg fun q _ => abs_nonneg _
    linarith
  have hΓ : ∀ q ∈ F, |(zetaZeroFamily q).im| ≤ Γ := fun q hq => by
    have := Finset.single_le_sum (f := fun q => |(zetaZeroFamily q).im|) (fun q _ => abs_nonneg _) hq
    linarith
  rcases F.eq_empty_or_nonempty with hFe | ⟨q₁, hq₁⟩
  · exact ⟨max n₁ 2, le_max_left _ _, le_max_right _ _, fun q hq => by simp [hFe] at hq⟩
  set γ₁ : ℝ := |(zetaZeroFamily q₁).im| with hγ₁
  have hγ₁0 : 0 < γ₁ := by
    rw [hγ₁, abs_pos]
    intro h
    apply im_poleP_ne q₁
    unfold poleP
    simp [h]
  set Q : ℕ := ⌈4 * π / η⌉₊ with hQ
  have hQ0 : 0 < Q := Nat.ceil_pos.2 (by positivity)
  have hQ' : 4 * π / η ≤ Q := Nat.le_ceil _
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  set u₀ : ℝ := Real.log ((2 * Γ / η + 1) * (n₁ + 2)) with hu₀
  have hu₀pos : 0 < (2 * Γ / η + 1) * (n₁ + 2) := by positivity
  have hn₁0 : (0 : ℝ) ≤ n₁ := Nat.cast_nonneg n₁
  have h2Γ : 0 ≤ 2 * Γ / η := by positivity
  set m₀ : ℕ := ⌈γ₁ * u₀ / (2 * π)⌉₊ + 1 with hm₀
  obtain ⟨m, hm, hmk⟩ := exists_simultaneous_ge (fun q : F => (zetaZeroFamily q.1).im / γ₁) hQ0
    (Nat.succ_pos _ : 0 < m₀)
  set u : ℝ := 2 * π * m / γ₁ with hu
  have hmR : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
  have hm₀R : γ₁ * u₀ / (2 * π) < m₀ := by
    rw [hm₀]
    push_cast
    linarith [Nat.le_ceil (γ₁ * u₀ / (2 * π))]
  have hu₀u : u₀ < u := by
    rw [hu, lt_div_iff₀ hγ₁0]
    have := (div_lt_iff₀ (by positivity)).1 (hm₀R.trans_le hmR)
    linarith
  have hexp0 : (n₁ : ℝ) + 2 ≤ Real.exp u₀ := by
    rw [hu₀, Real.exp_log hu₀pos]
    nlinarith
  have hexpΓ : 2 * Γ / η ≤ Real.exp u₀ := by
    rw [hu₀, Real.exp_log hu₀pos]
    nlinarith
  have hu0 : 0 < u := by
    have : 0 < u₀ := Real.log_pos (by nlinarith)
    linarith
  set n : ℕ := ⌈Real.exp u⌉₊ with hn
  have hn1 : Real.exp u ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < Real.exp u + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hexpu : Real.exp u₀ < Real.exp u := Real.exp_lt_exp.2 hu₀u
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn1
  refine ⟨n, ?_, ?_, fun q hq => ?_⟩
  · exact_mod_cast (by linarith : (n₁ : ℝ) ≤ n)
  · exact_mod_cast (by linarith : (2 : ℝ) ≤ n)
  · obtain ⟨k, hk⟩ := hmk ⟨q, hq⟩
    refine ⟨k, ?_⟩
    have hlog1 : u ≤ Real.log n := by rw [Real.le_log_iff_exp_le hnpos]; exact hn1
    have hlog2 : Real.log n ≤ u + Real.exp (-u) := by
      have h1 : Real.log n ≤ Real.log (Real.exp u + 1) := Real.log_le_log hnpos hn2.le
      have h2 : Real.log (Real.exp u + 1) = u + Real.log (1 + Real.exp (-u)) := by
        rw [show Real.exp u + 1 = Real.exp u * (1 + Real.exp (-u)) by
          rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero],
          Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
      have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-u) by positivity)
      linarith
    have hγ := hΓ q hq
    have hpiece1 : |(zetaZeroFamily q).im * u - k * (2 * π)| ≤ η / 2 := by
      have e : (zetaZeroFamily q).im * u - k * (2 * π) =
          2 * π * ((m : ℝ) * ((zetaZeroFamily q).im / γ₁) - k) := by
        rw [hu]
        field_simp
      rw [e, abs_mul, abs_of_pos (by positivity)]
      calc 2 * π * |(m : ℝ) * ((zetaZeroFamily q).im / γ₁) - k| ≤ 2 * π * (1 / Q) :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ ≤ η / 2 := by
            rw [mul_one_div, div_le_div_iff₀ hQR two_pos]
            have := (div_le_iff₀ hη).1 hQ'
            nlinarith
    have hpiece2 : |(zetaZeroFamily q).im * Real.log n - (zetaZeroFamily q).im * u| ≤ η / 2 := by
      rw [← mul_sub, abs_mul]
      have h1 : |Real.log n - u| ≤ Real.exp (-u) := by
        rw [abs_le]
        constructor <;> linarith [Real.exp_pos (-u)]
      have h2 : Real.exp (-u) ≤ η / (2 * Γ) := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
        exact hexpΓ.trans hexpu.le
      calc |(zetaZeroFamily q).im| * |Real.log n - u| ≤ Γ * (η / (2 * Γ)) :=
            mul_le_mul hγ (h1.trans h2) (abs_nonneg _) (by linarith)
        _ = η / 2 := by field_simp
    calc |(zetaZeroFamily q).im * Real.log n - k * (2 * π)|
        = |((zetaZeroFamily q).im * Real.log n - (zetaZeroFamily q).im * u) +
            ((zetaZeroFamily q).im * u - k * (2 * π))| := by ring_nf
      _ ≤ |(zetaZeroFamily q).im * Real.log n - (zetaZeroFamily q).im * u| +
            |(zetaZeroFamily q).im * u - k * (2 * π)| := abs_add_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add hpiece2 hpiece1
      _ = η := by ring

/-- Under RH, for every `ε > 0` and `n₁`, some `n ≥ n₁` has `H₀ − K_H(n) ≤ ε`: the finitely many zeros that carry all
but `ε/8` of the weight are brought near `2πℤ` at once. -/
lemma exists_defect_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (n₁ : ℕ) :
    ∃ n : ℕ, n₁ ≤ n ∧ 2 ≤ n ∧ H₀ - kψ n ≤ ε := by
  classical
  set w : ZIdx → ℝ := fun q => 1 / (1 / 4 + (zetaZeroFamily q).im ^ 2) with hw_def
  have hw0 : ∀ q, 0 ≤ w q := fun q => by positivity
  have hws : HasSum w H₀ := hasSum_weights hRH
  obtain ⟨F, hF⟩ : ∃ F : Finset ZIdx, ∑' q, (if q ∈ F then 0 else w q) ≤ ε / 8 := by
    obtain ⟨F, hF⟩ := Metric.tendsto_atTop.1 hws (ε / 8) (by positivity)
    refine ⟨F, ?_⟩
    have h := hF F le_rfl
    rw [Real.dist_eq, abs_lt] at h
    have hsplit := tsum_split_finset hws.summable F
    rw [hws.tsum_eq] at hsplit
    linarith
  have hH := H₀_pos
  set η : ℝ := Real.sqrt (ε / (2 * H₀)) with hη
  have hη0 : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hη2 : η ^ 2 = ε / (2 * H₀) := Real.sq_sqrt (by positivity)
  obtain ⟨n, hn1, hn2, hnear⟩ := exists_near_two_pi F hη0 n₁
  refine ⟨n, hn1, hn2, ?_⟩
  rw [defect_eq hRH (by omega)]
  set d : ZIdx → ℝ := fun q => (1 - Real.cos ((zetaZeroFamily q).im * Real.log n)) /
    (1 / 4 + (zetaZeroFamily q).im ^ 2) with hd_def
  have hd0 : ∀ q, 0 ≤ d q := fun q => defect_term_nonneg q _
  have hd2 : ∀ q, d q ≤ 2 * w q := fun q => defect_term_le q _
  have hds : Summable d := (hws.summable.mul_left 2).of_nonneg_of_le hd0 hd2
  rw [tsum_split_finset hds F]
  have hhead : ∑ q ∈ F, d q ≤ ε / 4 := by
    have h1 : ∀ q ∈ F, d q ≤ η ^ 2 / 2 * w q := by
      intro q hq
      obtain ⟨k, hk⟩ := hnear q hq
      have hc : 1 - Real.cos ((zetaZeroFamily q).im * Real.log n) ≤ η ^ 2 / 2 := by
        rw [← Real.cos_sub_int_mul_two_pi _ k]
        refine (one_sub_cos_le _).trans ?_
        have : ((zetaZeroFamily q).im * Real.log n - k * (2 * π)) ^ 2 ≤ η ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hk 2
        linarith
      simp only [hd_def, hw_def]
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    calc ∑ q ∈ F, d q ≤ ∑ q ∈ F, η ^ 2 / 2 * w q := Finset.sum_le_sum h1
      _ = η ^ 2 / 2 * ∑ q ∈ F, w q := by rw [Finset.mul_sum]
      _ ≤ η ^ 2 / 2 * H₀ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← hws.tsum_eq]
          exact Summable.sum_le_tsum F (fun q _ => hw0 q) hws.summable
      _ = ε / 4 := by
          rw [hη2]
          field_simp
          ring
  have htail : ∑' q, (if q ∈ F then 0 else d q) ≤ ε / 4 := by
    have hs2 : Summable fun q => if q ∈ F then 0 else 2 * w q :=
      (hws.summable.mul_left 2).of_nonneg_of_le (fun q => by split_ifs <;> positivity)
        (fun q => by split_ifs <;> [positivity; exact le_rfl])
    have hs1 : Summable fun q => if q ∈ F then 0 else d q :=
      hs2.of_nonneg_of_le (fun q => by split_ifs <;> [exact le_rfl; exact hd0 q])
        (fun q => by split_ifs <;> [exact le_rfl; exact hd2 q])
    have h := Summable.tsum_le_tsum (fun q => by split_ifs <;> [exact le_rfl; exact hd2 q]) hs1 hs2
    have e : ∑' q, (if q ∈ F then 0 else 2 * w q) = 2 * ∑' q, (if q ∈ F then 0 else w q) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun q => by split_ifs <;> simp
    linarith
  linarith

/-- **The approach, unconditionally**: `lim sup λ_N ≤ 0`. For every `ε > 0` there is a level `N₀` from which every
level has a nonzero real vector `x` with `Q_N(x) ≤ ε·Σ x_n²`. Under RH the vector is `δ_n − √n·δ_1` for an `n` whose
logarithm brings the heavy ordinates near `2πℤ` (`exists_defect_le`); if RH fails it is a negative vector, truncated
(`neg_persists`). -/
theorem approach {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ x : ℕ → ℝ, (∃ i ∈ Icc 1 N, x i ≠ 0) ∧
      form N x ≤ ε * ∑ i ∈ Icc 1 N, x i ^ 2 := by
  by_cases hRH : RiemannHypothesis
  · obtain ⟨n, -, hn2, hD⟩ := exists_defect_le hRH (half_pos hε) 0
    refine ⟨n, fun N hN => ⟨twoPt n, ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, ?_⟩, ?_⟩⟩
    · have h1n : (1 : ℕ) ≠ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      simp only [twoPt, h1n, ↓reduceIte, ne_eq, neg_eq_zero]
      exact (Real.sqrt_pos.2 hn0).ne'
    · rw [form_twoPt hn2 hN, sum_sq_twoPt hn2 hN]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      nlinarith
  · obtain ⟨N₁, x, hx⟩ := exists_neg_of_not_rh hRH
    refine ⟨N₁, fun N hN => ⟨trunc N₁ x, ?_, ?_⟩⟩
    · by_contra hall
      push Not at hall
      have : form N₁ x = 0 := by
        unfold form
        refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun n _ => ?_
        have hm' : x m = 0 := by
          have := hall m (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hm).1, (Finset.mem_Icc.1 hm).2.trans hN⟩)
          simpa [trunc, (Finset.mem_Icc.1 hm).2] using this
        simp [hm']
      linarith
    · rw [form_trunc hN]
      have : 0 ≤ ε * ∑ i ∈ Icc 1 N, trunc N₁ x i ^ 2 := by positivity
      linarith

end Approach

end BallRate
