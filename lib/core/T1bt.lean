import Mathlib

open Complex Real MeasureTheory intervalIntegral

noncomputable section

namespace WeilTest

/-- The zero-sum lemma of 1bt(ii): for a zero `ρ = β + iγ` in the open strip,
`Re 1/(ρ(1-ρ)) ≥ 1/(γ² + 5/4)`. -/
theorem re_inv_zero_term_ge (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    1 / (ρ.im ^ 2 + 5 / 4) ≤ (1 / (ρ * (1 - ρ))).re := by
  have hre : (ρ * (1 - ρ)).re = ρ.re * (1 - ρ.re) + ρ.im ^ 2 := by
    simp [Complex.mul_re]; ring
  have him : (ρ * (1 - ρ)).im = ρ.im * (1 - 2 * ρ.re) := by
    simp [Complex.mul_im]; ring
  set β := ρ.re
  set γ := ρ.im
  have hx0 : 0 < β * (1 - β) := mul_pos h0 (by linarith)
  have hx1 : β * (1 - β) ≤ 1 / 4 := by nlinarith [sq_nonneg (β - 1 / 2)]
  have hX : 0 < β * (1 - β) + γ ^ 2 := by nlinarith [sq_nonneg γ]
  rw [one_div (ρ * (1 - ρ)), Complex.inv_re, Complex.normSq_apply, hre, him]
  have hden : 0 < (β * (1 - β) + γ ^ 2) * (β * (1 - β) + γ ^ 2)
      + γ * (1 - 2 * β) * (γ * (1 - 2 * β)) :=
    add_pos_of_pos_of_nonneg (mul_pos hX hX) (mul_self_nonneg _)
  rw [div_le_div_iff₀ (by positivity) hden]
  -- (x+γ²)(γ²+5/4) - (x+γ²)² - γ²(1-2β)² = x(5/4-x) + γ²(1/4+3x),  x = β(1-β)
  have key : (β * (1 - β) + γ ^ 2) * (γ ^ 2 + 5 / 4)
      - ((β * (1 - β) + γ ^ 2) * (β * (1 - β) + γ ^ 2)
         + γ * (1 - 2 * β) * (γ * (1 - 2 * β)))
      = β * (1 - β) * (5 / 4 - β * (1 - β)) + γ ^ 2 * (1 / 4 + 3 * (β * (1 - β))) := by ring
  have hA : 0 ≤ β * (1 - β) * (5 / 4 - β * (1 - β)) := by
    apply mul_nonneg hx0.le; linarith
  have hB : 0 ≤ γ ^ 2 * (1 / 4 + 3 * (β * (1 - β))) := by
    apply mul_nonneg (sq_nonneg γ); linarith
  nlinarith

/-- The Hadamard constant `K = 2 + γ_E - log(4π)` (true value 0.046191...) is below 0.0539.
Uses only Mathlib's `γ_E < H_128 - log 128`, `log 2 > 0.6931471803`, `e < 2.7182818286`,
`π > 3.141592` and a four-term Taylor bound for `exp 0.143`. The bound `0.0539`, from `n = 128`,
is what lets 1bt(i) drop the first-zero height. -/
theorem hadamard_const_lt : 2 + eulerMascheroniConstant - Real.log (4 * π) < 0.0539 := by
  have hγ := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  have hseq : eulerMascheroniSeq' 128 = (harmonic 128 : ℝ) - Real.log 128 := by
    simp [eulerMascheroniSeq']
  have hH : (harmonic 128 : ℝ) < 54335 / 10000 := by
    have : harmonic 128 < (54335 / 10000 : ℚ) := by
      simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have h' : ((harmonic 128 : ℚ) : ℝ) < ((54335 / 10000 : ℚ) : ℝ) := Rat.cast_lt.mpr this
    simpa using h'
  have hlog64 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have hlog4pi : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    norm_num
  have hl2 := Real.log_two_gt_d9
  have hlpi : 1.143 < Real.log π := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    have h1 : Real.exp 1.143 = Real.exp 1 * Real.exp 0.143 := by
      rw [← Real.exp_add]; norm_num
    have hb := Real.exp_bound (x := 0.143) (by rw [abs_of_pos (by norm_num)]; norm_num)
      (n := 4) (by norm_num)
    have hb' := (abs_sub_le_iff.1 hb).1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb'
    norm_num at hb'
    have he := Real.exp_one_lt_d9
    have hpi := Real.pi_gt_d6
    have hexp : Real.exp 0.143 < 1.1538 := by linarith
    rw [h1]
    calc Real.exp 1 * Real.exp 0.143 < 2.7182818286 * 1.1538 :=
          mul_lt_mul'' he hexp (Real.exp_pos 1).le (Real.exp_pos _).le
      _ < 3.141592 := by norm_num
      _ < π := hpi
  rw [hlog4pi]
  rw [hseq, hlog64] at hγ
  linarith

/-! ## The strip hypothesis, discharged from Mathlib -/
/-- A nontrivial zero of `ζ`, exactly as in Mathlib's `RiemannHypothesis`: `ζ s = 0` and `s` is not
a trivial zero `-2(n+1)`. (`s ≠ 1` is automatic, since Mathlib's `ζ 1 ≠ 0`.) -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ¬∃ n : ℕ, s = -2 * (n + 1)

/-- Nontrivial zeros have `Re s < 1` (Mathlib: `ζ ≠ 0` on `Re s ≥ 1`). -/
theorem IsNontrivialZero.re_lt_one {s : ℂ} (h : IsNontrivialZero s) : s.re < 1 := by
  by_contra hc
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hc) h.1

/-- Nontrivial zeros have `Re s > 0`: for `Re s ≤ 0` the functional equation
`ζ(s) = 2(2π)^{-(1-s)} Γ(1-s) cos(π(1-s)/2) ζ(1-s)` has every factor but the cosine nonzero, and the
cosine vanishes only at `s = -2k`, which is `ζ(0) = -1/2 ≠ 0` for `k = 0` and a trivial zero for
`k ≥ 1`. -/
theorem IsNontrivialZero.re_pos {s : ℂ} (h : IsNontrivialZero s) : 0 < s.re := by
  by_contra hc'
  have hc : s.re ≤ 0 := not_lt.1 hc'
  obtain ⟨hz, hnt⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  set w := 1 - s with hw
  have hwre : 1 ≤ w.re := by
    rw [hw, Complex.sub_re, Complex.one_re]; linarith
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    have h1 := congrArg Complex.re hn
    rw [Complex.neg_re, Complex.natCast_re] at h1
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by
    intro h1
    apply hs0
    have : s = 1 - w := by rw [hw]; ring
    rw [this, h1]; ring
  have hfe := riemannZeta_one_sub hwn hw1
  have h1w : 1 - w = s := by rw [hw]; ring
  rw [h1w, hz] at hfe
  have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hcos : Complex.cos (Real.pi * w / 2) = 0 := by
    have h0 := hfe.symm
    rcases mul_eq_zero.1 h0 with h0 | h0
    · rcases mul_eq_zero.1 h0 with h0 | h0
      · rcases mul_eq_zero.1 h0 with h0 | h0
        · rcases mul_eq_zero.1 h0 with h0 | h0
          · exact absurd h0 two_ne_zero
          · exact absurd h0 hpow
        · exact absurd h0 hΓ
      · exact h0
    · exact absurd h0 hζw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 hcos
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hwk : w = 2 * k + 1 := by
    have h2 : (Real.pi : ℂ) * w = (2 * k + 1) * Real.pi := by
      linear_combination 2 * hk
    have h3 : (Real.pi : ℂ) * w = (Real.pi : ℂ) * (2 * k + 1) := by rw [h2]; ring
    exact mul_left_cancel₀ hpi h3
  have hsk : s = -2 * (k : ℂ) := by
    have : s = 1 - w := by rw [hw]; ring
    rw [this, hwk]; ring
  -- `Re s = -2k ≤ 0` forces `k ≥ 0`; `s ≠ 0` forces `k ≠ 0`
  have hkre : s.re = -2 * (k : ℝ) := by
    rw [hsk]; simp
  have hk0 : 0 ≤ k := by
    have : -2 * (k : ℝ) ≤ 0 := by rw [← hkre]; exact hc
    have : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hkne : k ≠ 0 := by
    rintro rfl
    apply hs0
    rw [hsk]; simp
  have hk1 : 0 ≤ k - 1 := by omega
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hk1
  apply hnt
  refine ⟨m, ?_⟩
  rw [hsk]
  have : (k : ℂ) = (m : ℂ) + 1 := by
    have : k = (m : ℤ) + 1 := by omega
    rw [this]; push_cast; ring
  rw [this]

/-- **The strip hypothesis, discharged**: every nontrivial zero of Mathlib's `riemannZeta` lies in
the open critical strip. -/
theorem IsNontrivialZero.mem_strip {s : ℂ} (h : IsNontrivialZero s) : 0 < s.re ∧ s.re < 1 :=
  ⟨h.re_pos, h.re_lt_one⟩

/-! ## The canonical zero family: the nontrivial zeros of `ζ` with multiplicity -/

/-- The nontrivial zeros of Mathlib's `riemannZeta`. -/
def NontrivialZero : Type := {s : ℂ // IsNontrivialZero s}

/-- The multiplicity of a nontrivial zero: the analytic order of `ζ` there. -/
def zeroMult (z : NontrivialZero) : ℕ := (analyticOrderAt riemannZeta z.1).toNat

/-- Each nontrivial zero has multiplicity at least one (and finite order), so the family below
lists every nontrivial zero, repeated by multiplicity. -/
theorem zeroMult_pos (z : NontrivialZero) : 0 < zeroMult z := by
  have hz := z.2.1
  have h1 : z.1 ≠ 1 := by
    intro h; rw [h] at hz; exact riemannZeta_one_ne_zero hz
  have han : AnalyticAt ℂ riemannZeta z.1 := analyticOn_riemannZeta z.1 h1
  have hne0 : analyticOrderAt riemannZeta z.1 ≠ 0 := analyticOrderAt_ne_zero.2 ⟨han, hz⟩
  have hne_top : analyticOrderAt riemannZeta z.1 ≠ ⊤ := by
    have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
    have hord2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
      rw [ne_eq, analyticOrderAt_eq_zero.2 (Or.inr (riemannZeta_ne_zero_of_one_le_re
        (by norm_num)))]
      exact ENat.zero_ne_top
    exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected h2 h1 hord2
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne_top
  unfold zeroMult
  rw [← hm, ENat.toNat_natCast]
  rw [← hm] at hne0
  exact Nat.pos_of_ne_zero (by exact_mod_cast hne0)

/-- The nontrivial zeros of `ζ` counted with multiplicity, as an indexed family. -/
def zetaZeroFamily : (Σ z : NontrivialZero, Fin (zeroMult z)) → ℂ := fun p => p.1.1

/-- **The zeros' height from Hadamard's identity.** Every term of `Σ_ρ 1/(ρ(1 − ρ)) = K` has real part
at least `1/(γ² + 5/4) > 0` (`re_inv_zero_term_ge`), so no term exceeds `K`: `1 ≤ K(γ² + 5/4)` for every
zero. With `K < 0.0539` this gives `γ² > 17.3`. -/
theorem one_le_hadamard_height {ι : Type*} (ρ : ι → ℂ)
    (h_strip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (h_hadamard : HasSum (fun i => 1 / (ρ i * (1 - ρ i)))
      ((2 + eulerMascheroniConstant - Real.log (4 * π) : ℝ) : ℂ)) (i : ι) :
    1 ≤ (2 + eulerMascheroniConstant - Real.log (4 * π)) * ((ρ i).im ^ 2 + 5 / 4) := by
  have hre : HasSum (fun j => (1 / (ρ j * (1 - ρ j))).re)
      (2 + eulerMascheroniConstant - Real.log (4 * π)) := by
    simpa using Complex.hasSum_re h_hadamard
  have hlow : ∀ j, 1 / ((ρ j).im ^ 2 + 5 / 4) ≤ (1 / (ρ j * (1 - ρ j))).re := fun j =>
    re_inv_zero_term_ge (ρ j) (h_strip j).1 (h_strip j).2
  have hnn : ∀ j, 0 ≤ (1 / (ρ j * (1 - ρ j))).re := fun j =>
    le_trans (by positivity) (hlow j)
  have hle := le_hasSum hre i fun j _ => hnn j
  have h := (hlow i).trans hle
  rwa [div_le_iff₀ (by positivity)] at h

end WeilTest

#print axioms WeilTest.re_inv_zero_term_ge
#print axioms WeilTest.hadamard_const_lt
#print axioms WeilTest.one_le_hadamard_height
#print axioms WeilTest.IsNontrivialZero.mem_strip
#print axioms WeilTest.zeroMult_pos
