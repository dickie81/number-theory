/-
# The Type II estimate in two variables, by bins of characters

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveHMBins.sum_typeII_bins_hm` bounds `Σ_{χ≠1} |W(χ)||B(χ)|` for one polynomial `W(χ) = dp S (aχ) h₀` by bins: in a
bin `R` it bounds `Σ_{χ∈R} |W(χ)|`, by `|R|^{1/2}(Σ_χ|W(χ)|²)^{1/2}` and orthogonality or by the Halász–Montgomery
inequality, and either way the number of characters of the bin enters. With two polynomials `W₁` and `W₂`,
Cauchy–Schwarz between them, `Σ_{χ∈R} |W₁(χ)||W₂(χ)| ≤ (Σ_{χ∈R}|W₁(χ)|²)^{1/2}(Σ_{χ∈R}|W₂(χ)|²)^{1/2}`, needs no count
of the bin, and each mean square is at most orthogonality's `(P + q)Σ|a|²` and at most the Halász–Montgomery bound in
its mean-square form, `e·Σ|a|²·(2P + |R|·B)`, in which the bin's count multiplies the kernel bound `B` only.

* `hm_duality_wt`: `LinnikPower.hm_duality` with weights. For `η_χ ∈ ℂ` on a set `R` of characters, one point
  `β_χ + iγ_χ` per character with `β_χ ≥ σ`, `S ⊆ [1, Λ]` and `|K_Λ(χχ′⁻¹, z_{χχ′})| ≤ B` for `χ ≠ χ′`:
  `|Σ_{χ∈R} η_χ D_χ|² ≤ e·G·(Λ·Σ_χ|η_χ|² + B·(Σ_χ|η_χ|)²)`, with `D_χ = pv S a χ (β_χ + iγ_χ)` and
  `G = Σ_{n∈S}|a_n|²n^{−2σ}`. (`hm_duality` is the case `η_χ = phase D_χ`, of modulus at most `1`.)
* `sum_bin_hm_sq`, **Halász–Montgomery in mean square for one bin at one height**: for `S ⊆ (P, 2P]` with `P ≥ 1`, a
  set `R` of characters and `B ≥ 0` with `|K_{2P}(ψ, 0)| ≤ B` for every `ψ ≠ 1`,
  `Σ_{χ∈R} |dp S (aχ) h₀|² ≤ e·Σ_{j∈S}|a_j|²·(2P + |R|·B)`.
* `sqTerm cnt P q V B`, the smaller of `(P + q)V` and `e·V·(2P + cnt·B)`.
* `sum_bin_two`, **one bin in two variables**: for `S_i ⊆ (P_i, 2P_i]` and kernel bounds `B_i`,
  `Σ_{χ∈R} |dp S₁ (aχ) h₁||dp S₂ (bχ) h₂| ≤ (sqTerm |R| P₁ q Σ|a|² B₁)^{1/2}(sqTerm |R| P₂ q Σ|b|² B₂)^{1/2}`.
* `sum_typeII_two_bins`, **the estimate by bins**: for `N > 0` bins and bounds `M_i ≥ 0` with `|B(χ)| ≤ M_i` for
  `χ ≠ 1` in bin `i`, `Σ_{χ≠1} |W₁(χ)||W₂(χ)||B(χ)| ≤ Σ_{i<N} M_i (sqTerm (#bin i) P₁ q Σ|a|² B₁)^{1/2}
  (sqTerm (#bin i) P₂ q Σ|b|² B₂)^{1/2}`. `SieveTypeIIHM.offK_bound` supplies the `B_i`.

The proof:

* `hm_duality_wt`: the proof of `LinnikPower.hm_duality` with `η` in place of the phases: `Σ_χ η_χ D_χ =
  Σ_{n∈S} x_n Φ_n` with `x_n = a_n n^{−σ}` and `Φ_n = Σ_χ η_χ χ(n) n^{−u_χ}`, Cauchy–Schwarz with the weight
  `e^{−n/Λ}`, and `Σ_n e^{−n/Λ}|Φ_n|² = Σ_{χ,χ′} η_χ η̄_{χ′} K_Λ(χχ′⁻¹, z_{χχ′})`, whose diagonal terms are at most
  `Λ|η_χ|²` and the others at most `B|η_χ||η_{χ′}|`.
* `sum_bin_hm_sq`: `hm_duality_wt` at `σ = 0`, `β_χ ≡ 0`, `γ_χ ≡ h₀`, `Λ = 2P` and `η_χ` the conjugate of `W(χ)`.
  Then `Σ_χ η_χ W(χ) = Σ_χ|W(χ)|² = D`, `Σ_χ|η_χ|² = D` and `(Σ_χ|η_χ|)² ≤ |R|D`, so `D² ≤ e·V·(2P + |R|B)·D`.
* `sum_bin_two`: Cauchy–Schwarz over the bin; each mean square by `SieveTypeII.sum_chars_dp_sq_le` (over all the
  characters) and by `sum_bin_hm_sq`.
* `sum_typeII_two_bins`: the split into bins of `sum_typeII_bins_hm`, and `sum_bin_two` in each.

The file imports `SieveHMBins.lean`.
-/
import SieveHMBins

namespace SieveTypeIIHM

open Finset DirMean LinnikPower SieveTypeII Complex

variable {q : ℕ}

/-! ### The duality inequality with weights -/

/-- **The Halász–Montgomery duality inequality over the characters mod `q`, with weights** `η_χ`: one point
`β_χ + iγ_χ` per character, `β_χ ≥ σ`, and `|Σ_χ η_χ D_χ|² ≤ e·G·(Λ·Σ_χ|η_χ|² + B·(Σ_χ|η_χ|)²)`, with
`G = Σ_{n∈S}|a_n|²n^{−2σ}`, for `S ⊆ [1, Λ]` and `|K_Λ(χχ′⁻¹, z_{χχ′})| ≤ B` for `χ ≠ χ′`,
`z_{χχ′} = (β_χ + β_{χ′} − 2σ) + i(γ_χ − γ_{χ′})`. -/
theorem hm_duality_wt {R : Finset (DirichletCharacter ℂ q)} {S : Finset ℕ} (hS0 : 0 ∉ S) {Λ : ℝ} (hΛ : 0 < Λ)
    (hSΛ : ∀ n ∈ S, (n : ℝ) ≤ Λ) (a : ℕ → ℂ) {σ : ℝ} (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ R, σ ≤ β χ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ χ ∈ R, ∀ χ' ∈ R, χ ≠ χ' →
      ‖∑' n : ℕ, kTerm (χ * χ'⁻¹) Λ (((β χ + β χ' - 2 * σ : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I) n‖ ≤ B)
    (η : DirichletCharacter ℂ q → ℂ) :
    ‖∑ χ ∈ R, η χ * pv S a χ ((β χ : ℂ) + γ χ * I)‖ ^ 2 ≤
      Real.exp 1 * (∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) *
        (Λ * ∑ χ ∈ R, ‖η χ‖ ^ 2 + B * (∑ χ ∈ R, ‖η χ‖) ^ 2) := by
  classical
  set u : DirichletCharacter ℂ q → ℂ := fun χ => ((β χ - σ : ℝ) : ℂ) + (γ χ : ℂ) * I with hu
  set D : DirichletCharacter ℂ q → ℂ := fun χ => pv S a χ ((β χ : ℂ) + γ χ * I) with hD
  set Φ : ℕ → ℂ := fun n => ∑ χ ∈ R, η χ * χ n * (n : ℂ) ^ (-u χ) with hΦ
  set x : ℕ → ℂ := fun n => a n * (n : ℂ) ^ (-(σ : ℂ)) with hx
  set Hs : ℝ := ∑ χ ∈ R, ‖η χ‖ with hHs
  have hHs0 : 0 ≤ Hs := sum_nonneg fun _ _ => norm_nonneg _
  -- (1) the weighted sum as a bilinear form
  have h1 : ∑ χ ∈ R, η χ * D χ = ∑ n ∈ S, x n * Φ n := by
    simp only [hD, pv, hΦ, hx, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun n hn => sum_congr rfl fun χ _ => ?_
    have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
    rw [cpow_split hn0 σ (β χ) (γ χ)]
    simp only [hu]
    ring
  -- (2) the moduli of the terms
  have hnx : ∀ n ∈ S, ‖x n‖ = ‖a n‖ * (n : ℝ) ^ (-σ) := by
    intro n hn
    have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
    rw [hx, norm_mul, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0)]
    simp
  -- (3) Cauchy–Schwarz with the weight `e^{−n/Λ}`
  set w : ℕ → ℝ := fun n => Real.exp (-((n : ℝ) / Λ)) with hw
  have hwpos : ∀ n, 0 < w n := fun n => Real.exp_pos _
  have hcs : (∑ n ∈ S, ‖x n‖ * ‖Φ n‖) ^ 2 ≤ (∑ n ∈ S, ‖x n‖ ^ 2 / w n) * (∑ n ∈ S, w n * ‖Φ n‖ ^ 2) := by
    have h := sum_mul_sq_le_sq_mul_sq S (fun n => ‖x n‖ * (Real.sqrt (w n))⁻¹) (fun n => Real.sqrt (w n) * ‖Φ n‖)
    have e1 : ∀ n, ‖x n‖ * (Real.sqrt (w n))⁻¹ * (Real.sqrt (w n) * ‖Φ n‖) = ‖x n‖ * ‖Φ n‖ := fun n => by
      have : Real.sqrt (w n) ≠ 0 := (Real.sqrt_pos.2 (hwpos n)).ne'
      field_simp
    have e2 : ∀ n, (‖x n‖ * (Real.sqrt (w n))⁻¹) ^ 2 = ‖x n‖ ^ 2 / w n := fun n => by
      rw [mul_pow, inv_pow, Real.sq_sqrt (hwpos n).le, div_eq_mul_inv]
    have e3 : ∀ n, (Real.sqrt (w n) * ‖Φ n‖) ^ 2 = w n * ‖Φ n‖ ^ 2 := fun n => by
      rw [mul_pow, Real.sq_sqrt (hwpos n).le]
    simp only [e1, e2, e3] at h
    exact h
  have hG : ∑ n ∈ S, ‖x n‖ ^ 2 / w n ≤ Real.exp 1 * ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [hnx n hn, hw, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    have : Real.exp ((n : ℝ) / Λ) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 ((div_le_one hΛ).2 (hSΛ n hn))
    calc (‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2 * Real.exp ((n : ℝ) / Λ)
        ≤ (‖a n‖ * (n : ℝ) ^ (-σ)) ^ 2 * Real.exp 1 := by gcongr
      _ = Real.exp 1 * (‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) := by ring
  -- (4) the weighted square sum as a double sum of kernels
  set z : DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℂ :=
    fun χ χ' => ((β χ + β χ' - 2 * σ : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I with hz
  have hzre : ∀ χ ∈ R, ∀ χ' ∈ R, 0 ≤ (z χ χ').re := by
    intro χ hχ χ' hχ'
    simp only [hz, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
    linarith [hβ χ hχ, hβ χ' hχ']
  have hzu : ∀ χ χ', z χ χ' = u χ + (starRingEnd ℂ) (u χ') := by
    intro χ χ'
    simp only [hz, hu, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  set F : ℕ → ℂ := fun n => ∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * kTerm (χ * χ'⁻¹) Λ (z χ χ') n
    with hF
  have hFeq : ∀ n, n ≠ 0 → F n = (w n : ℂ) * Φ n * (starRingEnd ℂ) (Φ n) := by
    intro n hn
    have hterm : ∀ χ χ', kTerm (χ * χ'⁻¹) Λ (z χ χ') n
        = (w n : ℂ) * (χ n * (n : ℂ) ^ (-u χ)) * (starRingEnd ℂ) (χ' n * (n : ℂ) ^ (-u χ')) := by
      intro χ χ'
      simp only [kTerm, hn, ite_false, hw]
      rw [MulChar.mul_apply, ← MulChar.star_apply', hzu, ← cpow_mul_conj_cpow hn, map_mul, Complex.star_def]
      ring
    have hΦexp : (w n : ℂ) * Φ n * (starRingEnd ℂ) (Φ n) = ∑ χ ∈ R, ∑ χ' ∈ R,
        (w n : ℂ) * (η χ * χ n * (n : ℂ) ^ (-u χ)) * (starRingEnd ℂ) (η χ' * χ' n * (n : ℂ) ^ (-u χ')) := by
      simp only [hΦ, map_sum]
      rw [mul_assoc, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun χ _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun χ' _ => ?_
      ring
    rw [hΦexp]
    simp only [hF]
    refine sum_congr rfl fun χ _ => sum_congr rfl fun χ' _ => ?_
    rw [hterm, map_mul, map_mul, map_mul]
    ring
  have hFre : ∀ n, (F n).re = (if n = 0 then 0 else w n * ‖Φ n‖ ^ 2) := by
    intro n
    split_ifs with hn
    · simp [hF, kTerm, hn]
    · rw [hFeq n hn, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- (5) summability and the bound on the double sum
  have hsumk : ∀ χ ∈ R, ∀ χ' ∈ R, Summable (kTerm (χ * χ'⁻¹) Λ (z χ χ')) :=
    fun χ hχ χ' hχ' => summable_kTerm _ hΛ (hzre χ hχ χ' hχ')
  have hFsum : Summable F := by
    simp only [hF]
    refine summable_sum fun χ hχ => summable_sum fun χ' hχ' => (hsumk χ hχ χ' hχ').mul_left _
  have hFbd : ∀ n, ‖F n‖ ≤ Hs ^ 2 * wt Λ n := by
    intro n
    simp only [hF]
    calc ‖∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖
        ≤ ∑ χ ∈ R, ∑ χ' ∈ R, ‖η χ * (starRingEnd ℂ) (η χ') * kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun χ _ => norm_sum_le _ _)
      _ ≤ ∑ χ ∈ R, ∑ χ' ∈ R, ‖η χ‖ * ‖η χ'‖ * wt Λ n := by
          refine sum_le_sum fun χ hχ => sum_le_sum fun χ' hχ' => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          exact mul_le_mul_of_nonneg_left (norm_kTerm_le (χ * χ'⁻¹) Λ (hzre χ hχ χ' hχ') n) (by positivity)
      _ = Hs ^ 2 * wt Λ n := by
          rw [hHs, sq, sum_mul_sum, sum_mul]
          refine sum_congr rfl fun χ _ => ?_
          rw [sum_mul]
  have hwt := wt_summable_le hΛ
  have hFresum : Summable fun n => (F n).re :=
    Summable.of_norm_bounded (hwt.1.mul_left (Hs ^ 2))
      (fun n => (Real.norm_eq_abs _).trans_le ((Complex.abs_re_le_norm (F n)).trans (hFbd n)))
  -- (6) the finite weighted sum against the full series
  have hFre0 : ∀ n, 0 ≤ (F n).re := fun n => by
    rw [hFre n]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hwpos n).le (by positivity)
  have h6 : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ ∑' n, (F n).re := by
    have e : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 = ∑ n ∈ S, (F n).re := by
      refine sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := fun h => hS0 (h ▸ hn)
      rw [hFre n, ite_eq_right hn0]
    rw [e]
    exact hFresum.sum_le_tsum S (fun n _ => hFre0 n)
  -- (7)–(8) the series as a double sum of kernels
  have h7 : ∑' n, (F n).re ≤ ‖∑' n, F n‖ := by
    rw [← Complex.re_tsum hFsum]; exact Complex.re_le_norm _
  have h8 : ∑' n, F n = ∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') *
      ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n := by
    simp only [hF]
    rw [Summable.tsum_finsetSum fun χ hχ => summable_sum fun χ' hχ' => (hsumk χ hχ χ' hχ').mul_left _]
    refine sum_congr rfl fun χ hχ => ?_
    rw [Summable.tsum_finsetSum fun χ' hχ' => (hsumk χ hχ χ' hχ').mul_left _]
    exact sum_congr rfl fun χ' _ => tsum_mul_left
  -- (9) the diagonal and the off-diagonal
  have hdiag : ∀ χ ∈ R, ‖∑' n, kTerm (χ * χ⁻¹) Λ (z χ χ) n‖ ≤ Λ := by
    intro χ hχ
    have hn := fun n => norm_kTerm_le (χ * χ⁻¹) Λ (hzre χ hχ χ hχ) n
    have hns : Summable fun n => ‖kTerm (χ * χ⁻¹) Λ (z χ χ) n‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hn hwt.1
    calc ‖∑' n, kTerm (χ * χ⁻¹) Λ (z χ χ) n‖ ≤ ∑' n, ‖kTerm (χ * χ⁻¹) Λ (z χ χ) n‖ :=
          norm_tsum_le_tsum_norm hns
      _ ≤ ∑' n, wt Λ n := hns.tsum_le_tsum hn hwt.1
      _ ≤ Λ := hwt.2
  have h9 : ‖∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖
      ≤ Λ * ∑ χ ∈ R, ‖η χ‖ ^ 2 + B * Hs ^ 2 := by
    have hpt : ∀ χ ∈ R, ∀ χ' ∈ R,
        ‖η χ * (starRingEnd ℂ) (η χ') * ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖
          ≤ (if χ = χ' then Λ * ‖η χ‖ ^ 2 else 0) + B * (‖η χ‖ * ‖η χ'‖) := by
      intro χ hχ χ' hχ'
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have h0 : 0 ≤ ‖η χ‖ * ‖η χ'‖ := by positivity
      by_cases h : χ = χ'
      · subst h
        rw [ite_eq_left rfl]
        have hK := hdiag χ hχ
        have hB' : 0 ≤ B * (‖η χ‖ * ‖η χ‖) := by positivity
        calc ‖η χ‖ * ‖η χ‖ * ‖∑' n, kTerm (χ * χ⁻¹) Λ (z χ χ) n‖ ≤ ‖η χ‖ * ‖η χ‖ * Λ :=
              mul_le_mul_of_nonneg_left hK h0
          _ = Λ * ‖η χ‖ ^ 2 := by ring
          _ ≤ Λ * ‖η χ‖ ^ 2 + B * (‖η χ‖ * ‖η χ‖) := le_add_of_nonneg_right hB'
      · rw [ite_eq_right h, zero_add]
        have hK : ‖∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖ ≤ B := by
          have := hB χ hχ χ' hχ' h
          simpa [hz] using this
        calc ‖η χ‖ * ‖η χ'‖ * ‖∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖ ≤ ‖η χ‖ * ‖η χ'‖ * B :=
              mul_le_mul_of_nonneg_left hK h0
          _ = B * (‖η χ‖ * ‖η χ'‖) := by ring
    calc ‖∑ χ ∈ R, ∑ χ' ∈ R, η χ * (starRingEnd ℂ) (η χ') * ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖
        ≤ ∑ χ ∈ R, ∑ χ' ∈ R, ‖η χ * (starRingEnd ℂ) (η χ') * ∑' n, kTerm (χ * χ'⁻¹) Λ (z χ χ') n‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun χ _ => norm_sum_le _ _)
      _ ≤ ∑ χ ∈ R, ∑ χ' ∈ R, ((if χ = χ' then Λ * ‖η χ‖ ^ 2 else 0) + B * (‖η χ‖ * ‖η χ'‖)) :=
          sum_le_sum fun χ hχ => sum_le_sum fun χ' hχ' => hpt χ hχ χ' hχ'
      _ = Λ * ∑ χ ∈ R, ‖η χ‖ ^ 2 + B * Hs ^ 2 := by
          simp only [sum_add_distrib]
          congr 1
          · rw [mul_sum]
            refine sum_congr rfl fun χ hχ => ?_
            rw [sum_ite_eq, ite_eq_left hχ]
          · rw [hHs, sq, sum_mul_sum, mul_sum]
            refine sum_congr rfl fun χ _ => ?_
            rw [mul_sum]
  -- (10) assemble
  have hmod : ‖∑ χ ∈ R, η χ * D χ‖ ≤ ∑ n ∈ S, ‖x n‖ * ‖Φ n‖ := by
    rw [h1]
    exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => norm_mul _ _))
  have hW : ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ Λ * ∑ χ ∈ R, ‖η χ‖ ^ 2 + B * Hs ^ 2 := by
    calc ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 ≤ ∑' n, (F n).re := h6
      _ ≤ ‖∑' n, F n‖ := h7
      _ = _ := by rw [h8]
      _ ≤ Λ * ∑ χ ∈ R, ‖η χ‖ ^ 2 + B * Hs ^ 2 := h9
  have hWnn : 0 ≤ ∑ n ∈ S, w n * ‖Φ n‖ ^ 2 := sum_nonneg fun n _ => mul_nonneg (hwpos n).le (by positivity)
  have hGnn : 0 ≤ ∑ n ∈ S, ‖x n‖ ^ 2 / w n := sum_nonneg fun n _ => div_nonneg (by positivity) (hwpos n).le
  calc ‖∑ χ ∈ R, η χ * pv S a χ ((β χ : ℂ) + γ χ * I)‖ ^ 2 = ‖∑ χ ∈ R, η χ * D χ‖ ^ 2 := rfl
    _ ≤ (∑ n ∈ S, ‖x n‖ * ‖Φ n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmod 2
    _ ≤ (∑ n ∈ S, ‖x n‖ ^ 2 / w n) * (∑ n ∈ S, w n * ‖Φ n‖ ^ 2) := hcs
    _ ≤ (Real.exp 1 * ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) * (Λ * ∑ χ ∈ R, ‖η χ‖ ^ 2 + B * Hs ^ 2) :=
        mul_le_mul hG hW hWnn (by positivity)

/-! ### The mean square over a bin -/

/-- **Halász–Montgomery in mean square, for one bin at one height.** For `S ⊆ (P, 2P]` with `P ≥ 1`, a set `R` of
characters and a bound `B ≥ 0` on `|K_{2P}(ψ, 0)|` for every `ψ ≠ 1`:
`Σ_{χ∈R} |dp S (aχ) h₀|² ≤ e·(Σ_{j∈S} |a_j|²)·(2P + |R|·B)` (`hP`, `hS`, `hB0`, `hB`). -/
theorem sum_bin_hm_sq {P : ℕ} (hP : 0 < P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ℕ → ℂ) (h₀ : ℝ)
    (R : Finset (DirichletCharacter ℂ q)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P) 0 n‖ ≤ B) :
    ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2 ≤
      Real.exp 1 * (∑ j ∈ S, ‖a j‖ ^ 2) * (2 * P + R.card * B) := by
  have hS0 : 0 ∉ S := fun h => by have := (Finset.mem_Ioc.1 (hS h)).1; omega
  have hSΛ : ∀ n ∈ S, (n : ℝ) ≤ 2 * P := fun n hn => by exact_mod_cast (Finset.mem_Ioc.1 (hS hn)).2
  have hΛ : (0 : ℝ) < 2 * P := by positivity
  have hpv : ∀ χ : DirichletCharacter ℂ q,
      pv S a χ ((((0 : ℝ)) : ℂ) + ((h₀ : ℝ) : ℂ) * I) = dp S (fun j => a j * χ j) h₀ := by
    intro χ
    rw [dp_eq_pv hS0]
    congr 1
    push_cast
    ring
  -- the duality with weights, at the conjugates of the values
  have h := hm_duality_wt (q := q) (R := R) hS0 hΛ hSΛ a (σ := 0) (fun _ => 0) (fun _ => h₀) (fun _ _ => le_rfl) hB0
    (fun χ _ χ' _ hne => by
      have hψ : χ * χ'⁻¹ ≠ 1 := by rwa [Ne, mul_inv_eq_one]
      convert hB (χ * χ'⁻¹) hψ using 3
      simp)
    (fun χ => (starRingEnd ℂ) (dp S (fun j => a j * χ j) h₀))
  have hG : ∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-(0 : ℝ))) ^ 2 = ∑ j ∈ S, ‖a j‖ ^ 2 := by
    simp [Real.rpow_zero]
  have hD0 : 0 ≤ ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2 := sum_nonneg fun _ _ => by positivity
  have hV0 : 0 ≤ ∑ j ∈ S, ‖a j‖ ^ 2 := sum_nonneg fun _ _ => by positivity
  have hsum : ∑ χ ∈ R, (starRingEnd ℂ) (dp S (fun j => a j * χ j) h₀) *
        pv S a χ ((((0 : ℝ)) : ℂ) + ((h₀ : ℝ) : ℂ) * I) =
      ((∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine sum_congr rfl fun χ _ => ?_
    rw [hpv χ, Complex.conj_mul', Complex.ofReal_pow]
  have hcs : (∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖) ^ 2 ≤
      R.card * ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  -- `h` reads `D² ≤ e·V·(2P·D + B·(Σ|W|)²)` with `D = Σ|W|²`
  have h' : (∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2) ^ 2 ≤
      Real.exp 1 * (∑ j ∈ S, ‖a j‖ ^ 2) *
        (2 * (P : ℝ) * ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2 +
          B * (∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖) ^ 2) := by
    have e1 : ‖∑ χ ∈ R, (starRingEnd ℂ) (dp S (fun j => a j * χ j) h₀) *
        pv S a χ ((((0 : ℝ)) : ℂ) + ((h₀ : ℝ) : ℂ) * I)‖ = ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2 := by
      rw [hsum, Complex.norm_real, Real.norm_of_nonneg hD0]
    have e2 : ∀ χ : DirichletCharacter ℂ q,
        ‖(starRingEnd ℂ) (dp S (fun j => a j * χ j) h₀)‖ = ‖dp S (fun j => a j * χ j) h₀‖ :=
      fun χ => Complex.norm_conj _
    simp only [e2] at h
    rw [e1, hG] at h
    exact h
  generalize ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2 = D at h' hD0 hcs ⊢
  generalize ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ = D1 at h' hcs
  generalize ∑ j ∈ S, ‖a j‖ ^ 2 = V at h' hV0 ⊢
  have hEV : 0 ≤ Real.exp 1 * V := mul_nonneg (Real.exp_pos 1).le hV0
  have hle : D * D ≤ Real.exp 1 * V * (2 * P + R.card * B) * D := by
    calc D * D = D ^ 2 := (sq D).symm
      _ ≤ Real.exp 1 * V * (2 * (P : ℝ) * D + B * D1 ^ 2) := h'
      _ ≤ Real.exp 1 * V * (2 * (P : ℝ) * D + B * (R.card * D)) := by
          have : B * D1 ^ 2 ≤ B * (R.card * D) := mul_le_mul_of_nonneg_left hcs hB0
          exact mul_le_mul_of_nonneg_left (by linarith) hEV
      _ = Real.exp 1 * V * (2 * P + R.card * B) * D := by ring
  rcases eq_or_lt_of_le hD0 with h0 | hpos
  · rw [← h0]
    have : (0 : ℝ) ≤ 2 * P + R.card * B := by positivity
    exact mul_nonneg hEV this
  · exact le_of_mul_le_mul_right hle hpos

/-! ### One bin in two variables -/

/-- The better of the two bounds for the mean square of a polynomial over a bin of `cnt` characters: orthogonality's
`(P + q)V` and Halász–Montgomery's `e·V·(2P + cnt·B)`, with `V = Σ|a|²` and `B` a bound on `|K_{2P}(ψ, 0)|` for
`ψ ≠ 1`. -/
noncomputable def sqTerm (cnt P q V B : ℝ) : ℝ :=
  min ((P + q) * V) (Real.exp 1 * V * (2 * P + cnt * B))

/-- The mean square of a polynomial over a bin is at most `sqTerm`. -/
theorem sum_bin_sq_le [NeZero q] {P : ℕ} (hP : 0 < P) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (a : ℕ → ℂ)
    (h₀ : ℝ) (R : Finset (DirichletCharacter ℂ q)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P) 0 n‖ ≤ B) :
    ∑ χ ∈ R, ‖dp S (fun j => a j * χ j) h₀‖ ^ 2 ≤ sqTerm R.card P q (∑ j ∈ S, ‖a j‖ ^ 2) B := by
  refine le_min ?_ (sum_bin_hm_sq hP hS a h₀ R hB0 hB)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) fun _ _ _ => by positivity).trans
    (sum_chars_dp_sq_le hS a q h₀)

/-- **One bin in two variables.** For `S₁ ⊆ (P₁, 2P₁]` and `S₂ ⊆ (P₂, 2P₂]` with `P₁, P₂ ≥ 1`, a set `R` of
characters, and bounds `B₁, B₂ ≥ 0` on `|K_{2P₁}(ψ, 0)|` and `|K_{2P₂}(ψ, 0)|` for `ψ ≠ 1`:
`Σ_{χ∈R} |dp S₁ (aχ) h₁||dp S₂ (bχ) h₂| ≤ (sqTerm |R| P₁ q Σ|a|² B₁)^{1/2}(sqTerm |R| P₂ q Σ|b|² B₂)^{1/2}`.
The number of characters of the bin enters through the kernel bounds only. -/
theorem sum_bin_two [NeZero q] {P₁ P₂ : ℕ} (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) {S₁ S₂ : Finset ℕ}
    (hS₁ : S₁ ⊆ Finset.Ioc P₁ (2 * P₁)) (hS₂ : S₂ ⊆ Finset.Ioc P₂ (2 * P₂)) (a b : ℕ → ℂ) (h₁ h₂ : ℝ)
    (R : Finset (DirichletCharacter ℂ q)) {B₁ B₂ : ℝ} (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂)
    (hK₁ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P₁) 0 n‖ ≤ B₁)
    (hK₂ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P₂) 0 n‖ ≤ B₂) :
    ∑ χ ∈ R, ‖dp S₁ (fun j => a j * χ j) h₁‖ * ‖dp S₂ (fun j => b j * χ j) h₂‖ ≤
      Real.sqrt (sqTerm R.card P₁ q (∑ j ∈ S₁, ‖a j‖ ^ 2) B₁) *
        Real.sqrt (sqTerm R.card P₂ q (∑ j ∈ S₂, ‖b j‖ ^ 2) B₂) := by
  refine (Real.sum_mul_le_sqrt_mul_sqrt R _ _).trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt (sum_bin_sq_le hP₁ hS₁ a h₁ R hB₁0 hK₁))
    (Real.sqrt_le_sqrt (sum_bin_sq_le hP₂ hS₂ b h₂ R hB₂0 hK₂)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ### The estimate by bins -/

/-- **The Type II estimate in two variables, by bins.** For `N > 0` bins (`hN`), `S₁ ⊆ (P₁, 2P₁]` and
`S₂ ⊆ (P₂, 2P₂]` (`hS₁`, `hS₂`) with `P₁, P₂ ≥ 1`, bounds `M_i ≥ 0` (`hM`) with `|B(χ)| ≤ M_i` for `χ ≠ 1` in bin `i`
(`hB`), and `B₁, B₂ ≥ 0` with `|K_{2P₁}(ψ, 0)| ≤ B₁` and `|K_{2P₂}(ψ, 0)| ≤ B₂` for `ψ ≠ 1`:
`Σ_{χ≠1} |W₁(χ)||W₂(χ)||B(χ)| ≤ Σ_{i<N} M_i (sqTerm (#bin i) P₁ q Σ|a|² B₁)^{1/2}(sqTerm (#bin i) P₂ q Σ|b|² B₂)^{1/2}`,
with `W₁(χ) = dp S₁ (aχ) h₁` and `W₂(χ) = dp S₂ (bχ) h₂`. -/
theorem sum_typeII_two_bins [NeZero q] {β : ℕ → ℝ} {N : ℕ} (hN : 0 < N) (T : ℝ) {P₁ P₂ : ℕ} (hP₁ : 0 < P₁)
    (hP₂ : 0 < P₂) {S₁ S₂ : Finset ℕ} (hS₁ : S₁ ⊆ Finset.Ioc P₁ (2 * P₁)) (hS₂ : S₂ ⊆ Finset.Ioc P₂ (2 * P₂))
    (a b : ℕ → ℂ) (h₁ h₂ : ℝ) (Bf : DirichletCharacter ℂ q → ℂ) (M : ℕ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hB : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖Bf χ‖ ≤ M (bin β N T χ))
    {B₁ B₂ : ℝ} (hB₁0 : 0 ≤ B₁) (hB₂0 : 0 ≤ B₂)
    (hK₁ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P₁) 0 n‖ ≤ B₁)
    (hK₂ : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ‖∑' n, kTerm ψ (2 * P₂) 0 n‖ ≤ B₂) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖dp S₁ (fun j => a j * χ j) h₁‖ * ‖dp S₂ (fun j => b j * χ j) h₂‖ * ‖Bf χ‖ ≤
      ∑ i ∈ Finset.range N, M i *
        (Real.sqrt (sqTerm ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card)
            P₁ q (∑ j ∈ S₁, ‖a j‖ ^ 2) B₁) *
          Real.sqrt (sqTerm ((Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i).card)
            P₂ q (∑ j ∈ S₂, ‖b j‖ ^ 2) B₂)) := by
  classical
  set W : DirichletCharacter ℂ q → ℝ :=
    fun χ => ‖dp S₁ (fun j => a j * χ j) h₁‖ * ‖dp S₂ (fun j => b j * χ j) h₂‖ with hW
  have hW0 : ∀ χ, 0 ≤ W χ := fun χ => by rw [hW]; positivity
  -- split the sum over the bins: `Σ_{χ≠1} W·|Bf| ≤ Σ_i M_i Σ_{χ ∈ bin i} W χ`
  have hsplit : ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), W χ * ‖Bf χ‖ ≤
      ∑ i ∈ Finset.range N, M i *
        ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i), W χ := by
    calc ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), W χ * ‖Bf χ‖
        ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), W χ * M (bin β N T χ) := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          exact mul_le_mul_of_nonneg_left (hB χ (Finset.mem_filter.1 hχ).2) (hW0 χ)
      _ = ∑ i ∈ Finset.range N, ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧
            bin β N T χ = i), W χ * M i := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := bin β N T) (t := Finset.range N)
            (fun χ _ => Finset.mem_range.2 (bin_lt hN T χ))]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.filter_filter]
          exact Finset.sum_congr rfl fun χ hχ => by rw [(Finset.mem_filter.1 hχ).2.2]
      _ = ∑ i ∈ Finset.range N, M i *
            ∑ χ ∈ (Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ ≠ 1 ∧ bin β N T χ = i), W χ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  refine hsplit.trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hM i))
  exact sum_bin_two hP₁ hP₂ hS₁ hS₂ a b h₁ h₂ _ hB₁0 hB₂0 hK₁ hK₂

end SieveTypeIIHM

#print axioms SieveTypeIIHM.hm_duality_wt
#print axioms SieveTypeIIHM.sum_bin_hm_sq
#print axioms SieveTypeIIHM.sum_bin_two
#print axioms SieveTypeIIHM.sum_typeII_two_bins
