import Zeta23.Final

/-! # The zeros of `ζ` on the critical line: Hardy, Selberg, and Alpöge and Furman's two thirds

zeta23 proves Alpöge and Furman's theorem with no hypothesis (`Zeta23.thmA₀`). For every `ε > 0` and all large `T`, at
least `(2/3 − ε)·N(T, 2T)` distinct zeros of `ζ` with `T < Im ρ ≤ 2T` lie on the critical line, where `N(T, 2T)`
counts all the nontrivial zeros there with multiplicity. zeta23's Riemann–von Mangoldt formula gives
`N(T, 2T) ≥ T log T/(4π)` for large `T` (`Ncount_ge`). Together they give the classical theorems on the zeros on the
line, stated here with Mathlib's `riemannZeta` and `analyticOrderAt` alone:

* **`infinite_zeros`**, **`exists_zero_im_gt`**: infinitely many zeros of `ζ` lie on the critical line, with
  arbitrarily large ordinates (Hardy, 1914).
* **`ncard_zeros_ge`**: for all large `T`, at least `T log T/(12π)` of them have `T < Im ρ ≤ 2T`. This is a positive
  proportion of all the zeros there (Selberg, 1942), and contains Hardy and Littlewood's `N₀(T) ≫ T` (1921).
* **`ncard_simple_zeros_ge`**, **`infinite_simple_zeros`**: the same for the simple zeros on the line, at least
  `T log T/(16π)` of them with `T < Im ρ ≤ 2T`, from `Zeta23.thmB₀`.
* **`two_thirds`**, **`two_thirds_cumulative`**, **`half_simple`**, **`three_quarters_distinct`**: zeta23's Theorems
  A, B and C, in its counting functions `Zeta23.Ncount`, `Zeta23.N0star`, `Zeta23.N0simple` and `Zeta23.Ndist`, which
  are defined from Mathlib's `riemannZeta` and `analyticOrderAt`.

Levinson (1974) had `1/3` and Conrey (1989) `2/5`. The paper is L. Alpöge and R. Furman, "More than two thirds of the
zeta zeros are simple and on the critical line" (2026), arXiv:2608.13637; its journal review is pending.
-/

open Real Filter Set

namespace CriticalLine

open Zeta23

/-- The zeros of `ζ` on the critical line with `T₁ < Im ρ ≤ T₂`, as zeta23 counts them. -/
lemma onLine_inter_window (T₁ T₂ : ℝ) :
    zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} =
      {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂} := by
  ext ρ
  simp only [zerosIn, IsNontrivialZero, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨h0, -, -⟩, h1, h2⟩, h3⟩
    exact ⟨⟨h0, h3⟩, h1, h2⟩
  · rintro ⟨⟨h0, h3⟩, h1, h2⟩
    exact ⟨⟨⟨h0, by rw [h3]; norm_num, by rw [h3]; norm_num⟩, h1, h2⟩, h3⟩

/-- The simple zeros of `ζ` on the critical line with `T₁ < Im ρ ≤ T₂`, as zeta23 counts them. -/
lemma simple_inter_window (T₁ T₂ : ℝ) :
    zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1} =
      {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1} ∩
        {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂} := by
  rw [onLine_inter_window]
  ext ρ
  simp only [zeroMult, mem_inter_iff, mem_ofPred_eq, ENat.toNat_eq_iff one_ne_zero, Nat.cast_one]
  tauto

/-- **Riemann–von Mangoldt, from below**: `N(T, 2T) ≥ T log T/(4π)` for all large `T`. -/
lemma Ncount_ge : ∀ᶠ T : ℝ in atTop, T * Real.log T / (4 * π) ≤ (Ncount T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, hR⟩ := riemannVonMangoldt_zeta.main
  have hπ := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have hl2 := Real.log_two_gt_d9
  -- `log(2π) < 2`
  have hl2π : Real.log (2 * π) < 2 := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]
    have := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (Real.exp 8),
    eventually_ge_atTop (8 * π * |C| + 1)] with T hT₀ hT8 hTC
  have hT1 : 1 ≤ T := le_trans (by linarith [Real.add_one_le_exp (8 : ℝ)]) hT8
  have hT0 : 0 < T := by linarith
  have hR' := hR T hT₀
  rw [zetaZeroConfig_N] at hR'
  have hL8 : 8 ≤ Real.log T := by rw [Real.le_log_iff_exp_le hT0]; exact hT8
  have hell : Real.log T - 2 ≤ ell1 T := by
    unfold Zeta23.ell1 Zeta23.l
    rw [Real.log_div hT0.ne' (by positivity)]
    linarith
  have hClog : C * Real.log T ≤ |C| * Real.log T :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have hN : T / (2 * π) * (Real.log T - 2) - |C| * Real.log T ≤ (Ncount T (2 * T) : ℝ) := by
    have h1 := (abs_le.1 hR').1
    have h2 : T / (2 * π) * (Real.log T - 2) ≤ T / (2 * π) * ell1 T :=
      mul_le_mul_of_nonneg_left hell (by positivity)
    linarith
  have hgoal : T * Real.log T / (4 * π) ≤ T / (2 * π) * (Real.log T - 2) - |C| * Real.log T := by
    rw [div_le_iff₀ (by positivity)]
    have e : (T / (2 * π) * (Real.log T - 2) - |C| * Real.log T) * (4 * π)
        = 2 * T * (Real.log T - 2) - 4 * π * |C| * Real.log T := by field_simp; ring
    rw [e]
    have h8 : T * 8 ≤ T * Real.log T := mul_le_mul_of_nonneg_left hL8 hT0.le
    have hC : 8 * π * |C| * Real.log T ≤ T * Real.log T :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  linarith

/-- If a set `S` meets the strip `T < Im s ≤ 2T` for all large `T`, its ordinates are unbounded. -/
lemma exists_im_gt {S : Set ℂ} (h : ∀ᶠ T : ℝ in atTop, 0 < (S ∩ {ρ | T < ρ.im ∧ ρ.im ≤ 2 * T}).ncard) (T : ℝ) :
    ∃ ρ ∈ S, T < ρ.im := by
  obtain ⟨T', hT', hle⟩ := (h.and (eventually_ge_atTop T)).exists
  obtain ⟨ρ, hρ, h1, -⟩ := nonempty_of_ncard_ne_zero hT'.ne'
  exact ⟨ρ, hρ, hle.trans_lt h1⟩

/-- A set of points with unbounded ordinates is infinite. -/
lemma infinite_of_exists_im_gt {S : Set ℂ} (h : ∀ T : ℝ, ∃ ρ ∈ S, T < ρ.im) : S.Infinite := by
  intro hS
  obtain ⟨B, hB⟩ := (hS.image Complex.im).bddAbove
  obtain ⟨ρ, hρ, hlt⟩ := h B
  exact absurd (hB ⟨ρ, hρ, rfl⟩) (not_le.2 hlt)

/-- **A positive proportion of the zeros of `ζ` lie on the critical line** (Selberg): for all large `T`, at least
`T log T/(12π)` zeros `ρ` of `ζ` with `Re ρ = 1/2` have `T < Im ρ ≤ 2T`. -/
theorem ncard_zeros_ge : ∀ᶠ T : ℝ in atTop, T * Real.log T / (12 * π) ≤
    (({ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2} ∩ {ρ | T < ρ.im ∧ ρ.im ≤ 2 * T}).ncard : ℝ) := by
  obtain ⟨T₀, hA⟩ := thmA₀ (1 / 3) (by norm_num)
  filter_upwards [Ncount_ge, eventually_ge_atTop T₀] with T hN hT
  have h := hA T hT
  rw [N0star, onLine_inter_window] at h
  have e : T * Real.log T / (12 * π) = (2 / 3 - 1 / 3) * (T * Real.log T / (4 * π)) := by ring
  rw [e]
  exact le_trans (mul_le_mul_of_nonneg_left hN (by norm_num)) h

/-- **The zeros of `ζ` on the critical line have unbounded ordinates** (Hardy): for every `T` some zero `ρ` of `ζ`
with `Re ρ = 1/2` has `Im ρ > T`. -/
theorem exists_zero_im_gt (T : ℝ) : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ T < ρ.im := by
  have h : ∀ᶠ T : ℝ in atTop,
      0 < ({ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2} ∩ {ρ | T < ρ.im ∧ ρ.im ≤ 2 * T}).ncard := by
    filter_upwards [ncard_zeros_ge, eventually_ge_atTop 2] with T h hT
    have : 0 < T * Real.log T / (12 * π) :=
      div_pos (mul_pos (by linarith) (Real.log_pos (by linarith))) (by positivity)
    exact_mod_cast this.trans_le h
  obtain ⟨ρ, ⟨h0, h1⟩, h2⟩ := exists_im_gt h T
  exact ⟨ρ, h0, h1, h2⟩

/-- **Hardy's theorem** (1914): infinitely many zeros of `ζ` lie on the critical line. -/
theorem infinite_zeros : {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2}.Infinite :=
  infinite_of_exists_im_gt fun T ↦ by
    obtain ⟨ρ, h0, h1, h2⟩ := exists_zero_im_gt T
    exact ⟨ρ, ⟨h0, h1⟩, h2⟩

/-- **A positive proportion of the zeros of `ζ` are simple and on the critical line**: for all large `T`, at least
`T log T/(16π)` zeros `ρ` of `ζ` of order one with `Re ρ = 1/2` have `T < Im ρ ≤ 2T`. -/
theorem ncard_simple_zeros_ge : ∀ᶠ T : ℝ in atTop, T * Real.log T / (16 * π) ≤
    (({ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1} ∩
      {ρ | T < ρ.im ∧ ρ.im ≤ 2 * T}).ncard : ℝ) := by
  obtain ⟨T₀, hB⟩ := thmB₀ (1 / 4) (by norm_num)
  filter_upwards [Ncount_ge, eventually_ge_atTop T₀] with T hN hT
  have h := hB T hT
  rw [N0simple, simple_inter_window] at h
  have e : T * Real.log T / (16 * π) = (1 / 2 - 1 / 4) * (T * Real.log T / (4 * π)) := by ring
  rw [e]
  exact le_trans (mul_le_mul_of_nonneg_left hN (by norm_num)) h

/-- **Infinitely many zeros of `ζ` on the critical line are simple.** -/
theorem infinite_simple_zeros :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1}.Infinite := by
  refine infinite_of_exists_im_gt (exists_im_gt ?_)
  filter_upwards [ncard_simple_zeros_ge, eventually_ge_atTop 2] with T h hT
  have : 0 < T * Real.log T / (16 * π) :=
    div_pos (mul_pos (by linarith) (Real.log_pos (by linarith))) (by positivity)
  exact_mod_cast this.trans_le h

/-- **Two thirds of the zeros of `ζ` lie on the critical line** (Alpöge and Furman, Theorem A): for every `ε > 0` and
all large `T`, at least `(2/3 − ε)·N(T, 2T)` distinct zeros with `T < Im ρ ≤ 2T` lie on the line, where `N(T, 2T)`
counts all the nontrivial zeros there with multiplicity. -/
theorem two_thirds :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  thmA₀

/-- **Two thirds of the zeros of `ζ` up to height `T` lie on the critical line** (Theorem A, cumulative):
`liminf N₀*(T)/N(T) ≥ 2/3`. -/
theorem two_thirds_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  thmA₀_cumulative

/-- **Half of the zeros of `ζ` are simple and on the critical line** (Alpöge and Furman, Theorem B in its
Cauchy–Schwarz form): `(1/2 − ε)·N(T, 2T) ≤ N₀ˢ(T, 2T)` for all large `T`. -/
theorem half_simple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  thmB₀

/-- **Three quarters of the zeros of `ζ` are distinct** (Alpöge and Furman, Theorem C in its Cauchy–Schwarz form):
`(3/4 − ε)·N(T, 2T) ≤ N_d(T, 2T)` for all large `T`. -/
theorem three_quarters_distinct :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  thmC₀

end CriticalLine

#print axioms CriticalLine.infinite_zeros
#print axioms CriticalLine.ncard_zeros_ge
#print axioms CriticalLine.infinite_simple_zeros
#print axioms CriticalLine.two_thirds
