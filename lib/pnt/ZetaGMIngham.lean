/-
# Ingham's count for `ζ` up to `σ = 7/10 + η`, at the exponent `30/13`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. For `0 < ε ≤ 1` and `0 ≤ η ≤ 1/10` there is `C ≥ 0` with
`N(σ, T) ≤ C T^{(30/13)(1−σ)+η+ε/4}(log T)^{12}` for `17/30 ≤ σ ≤ 7/10 + η` and `T ≥ 2` (`nx_ingham13`). It is
`ZetaIngham`'s window argument at `c = 1/13` in place of `c = 1/10`: the polynomial classes carry
`U^{(2+4c)(1−σ)} = U^{(30/13)(1−σ)}` (`InghamDensity.bound_S1`), and the integral class, at `Y = U^{15/13}`,
`δ = 1/15` and `λ = U^{(5/13)(½−σ)+ε/4}`, carries `U^{(20/13)(½−σ)+1+ε/4}` (`bound_B3_gm`), which is at most
`U^{(30/13)(1−σ)+ε/4}` exactly when `σ ≤ 7/10`, and exceeds it by at most `U^{(10/13)η}` up to `7/10 + η`.

* `bound_B3_gm`: `ZetaIngham.bound_B3_ingham` at `c = 1/13`, `δ = 1/15`.
* `window_count_ingham13`: `ZetaIngham.window_count_ingham` at these parameters, on `17/30 ≤ σ ≤ 7/10 + η`.
* `nx_ingham13`: `ZetaIngham.nx_le_of_windows`.

The file imports `ZetaIngham.lean`.
-/
import ZetaIngham

open Complex Real Filter Topology MeasureTheory

noncomputable section

namespace ZetaGMIngham

open ShortWeil PsiOmega WeilForm WeilTest DirMean Finset InghamDensity ZetaIngham

/-- The window constant at `δ = 1/15`. -/
def Cwg (C₄ : ℝ) : ℝ :=
  2 * Kc * (2 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71) + (216000 * KG + 18225 * KG ^ 2 * C₄))

theorem Cwg_nonneg {C₄ : ℝ} (hC₄ : 0 ≤ C₄) : 0 ≤ Cwg C₄ := by
  unfold Cwg; have := Kc_nonneg; have := KG_pos; positivity

/-- **The integral class at `c = 1/13`**: at `X = ⌊U⌋`, `Y = U^{15/13}`, `δ = 1/15` and
`λ = U^{(5/13)(½−σ)+ε/4}`, with the fourth moment at `3ε/4`, `2AλM₁ + A²M₂/λ² ≤ (216000KG + 18225KG²C₄)(log U)⁵
U^{(20/13)(½−σ)+1+ε/4}` (`ZetaIngham.bound_B3_ingham` at these parameters). -/
theorem bound_B3_gm {ε C₄ σ U : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hC₄ : 0 ≤ C₄) (hU : 8 ≤ U) :
    2 * (3 * KG * (Yw (1 / 13) U) ^ (1 / 2 - σ) / (1 / 15)) * U ^ (5 / 13 * (1 / 2 - σ) + ε / 4) *
        (MV (Xw U) * (U + (Xw U) + 1)) +
      (3 * KG * (Yw (1 / 13) U) ^ (1 / 2 - σ) / (1 / 15)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) /
        (U ^ (5 / 13 * (1 / 2 - σ) + ε / 4)) ^ 2
      ≤ (216000 * KG + 18225 * KG ^ 2 * C₄) * Real.log U ^ 5 * U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hL := log_ge_two hU
  have hKG := KG_pos
  have hMV := bound_MV hU
  have hMV0 : 0 ≤ MV (Xw U) := by
    unfold MV; have := Real.log_nonneg (by exact_mod_cast Xw_one hU : (1 : ℝ) ≤ Xw U); positivity
  have hXU := Xw_le hU
  have hY : (Yw (1 / 13) U) ^ (1 / 2 - σ) = U ^ (15 / 13 * (1 / 2 - σ)) := by
    unfold Yw; rw [← Real.rpow_mul hU0.le]; norm_num
  set a := U ^ (15 / 13 * (1 / 2 - σ)) with ha
  set l := U ^ (5 / 13 * (1 / 2 - σ) + ε / 4) with hl
  have ha0 : 0 < a := by positivity
  have hl0 : 0 < l := by positivity
  rw [hY]
  -- the first term
  have hM₁ : MV (Xw U) * (U + (Xw U) + 1) ≤ 800 * Real.log U ^ 5 * (3 * U) := by
    have h3 : U + (Xw U : ℝ) + 1 ≤ 3 * U := by linarith
    gcongr
  have hal : a * l = U ^ (20 / 13 * (1 / 2 - σ) + ε / 4) := by
    rw [ha, hl, ← Real.rpow_add hU0]; congr 1; ring
  have hE1 : U ^ (20 / 13 * (1 / 2 - σ) + ε / 4) * U = U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by
    rw [← Real.rpow_add_one hU0.ne']; congr 1; ring
  have hT1 : 2 * (3 * KG * a / (1 / 15)) * l * (MV (Xw U) * (U + (Xw U) + 1))
      ≤ 216000 * KG * Real.log U ^ 5 * U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by
    calc 2 * (3 * KG * a / (1 / 15)) * l * (MV (Xw U) * (U + (Xw U) + 1))
        ≤ 2 * (3 * KG * a / (1 / 15)) * l * (800 * Real.log U ^ 5 * (3 * U)) := by gcongr
      _ = 216000 * KG * Real.log U ^ 5 * ((a * l) * U) := by ring
      _ = 216000 * KG * Real.log U ^ 5 * U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by rw [hal, hE1]
  -- the second term
  have hM₂ : (2 * U + 2) ^ (1 + 3 * ε / 4) ≤ 9 * U ^ (1 + 3 * ε / 4) := by
    calc (2 * U + 2) ^ (1 + 3 * ε / 4) ≤ (3 * U) ^ (1 + 3 * ε / 4) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = (3 : ℝ) ^ (1 + 3 * ε / 4) * U ^ (1 + 3 * ε / 4) := Real.mul_rpow (by norm_num) hU0.le
      _ ≤ 9 * U ^ (1 + 3 * ε / 4) := by
          gcongr
          calc (3 : ℝ) ^ (1 + 3 * ε / 4) ≤ 3 ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 9 := by norm_num
  have hE2 : a ^ 2 * U ^ (1 + 3 * ε / 4) / l ^ 2 = U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by
    rw [ha, hl, ← Real.rpow_natCast (U ^ (15 / 13 * (1 / 2 - σ))), ← Real.rpow_natCast
      (U ^ (5 / 13 * (1 / 2 - σ) + ε / 4)), ← Real.rpow_mul hU0.le, ← Real.rpow_mul hU0.le,
      ← Real.rpow_add hU0, ← Real.rpow_sub hU0]
    congr 1; push_cast; ring
  have hT2 : (3 * KG * a / (1 / 15)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) / l ^ 2
      ≤ 18225 * KG ^ 2 * C₄ * U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by
    have hl2 : 0 < l ^ 2 := by positivity
    calc (3 * KG * a / (1 / 15)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) / l ^ 2
        ≤ (3 * KG * a / (1 / 15)) ^ 2 * (C₄ * (9 * U ^ (1 + 3 * ε / 4))) / l ^ 2 := by gcongr
      _ = 18225 * KG ^ 2 * C₄ * (a ^ 2 * U ^ (1 + 3 * ε / 4) / l ^ 2) := by ring
      _ = 18225 * KG ^ 2 * C₄ * U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by rw [hE2]
  have hL5 : 1 ≤ Real.log U ^ 5 := one_le_pow₀ (by linarith)
  have hP : 0 ≤ U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by positivity
  have hT2' : 18225 * KG ^ 2 * C₄ * U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4)
      ≤ 18225 * KG ^ 2 * C₄ * Real.log U ^ 5 * U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by
    have : 0 ≤ 18225 * KG ^ 2 * C₄ * U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) := by positivity
    nlinarith
  nlinarith

/-- **One window at `c = 1/13`**: for `0 ≤ η ≤ 1/10`, `17/30 ≤ σ ≤ 7/10 + η` and `U ≥ 8`, at most
`Cwg(C₄)(log U)^{11}U^{(30/13)(1−σ)+η+ε/4}` zeros with `U ≤ |γ| ≤ 2U` and `β ≥ σ`, given the fourth moment of `ζ` at
`3ε/4` with constant `C₄`: `ZetaIngham.window_count_ingham` at `Y = U^{15/13}`, `δ = 1/15` and
`λ = U^{(5/13)(½−σ)+ε/4}`, where `(20/13)(½ − σ) + 1 ≤ (30/13)(1 − σ) + η` for `σ ≤ 7/10 + η`. -/
theorem window_count_ingham13 {ε η : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1 / 10) {C₄ : ℝ}
    (hC₄ : 0 ≤ C₄)
    (h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄ * (T + 2) ^ (1 + 3 * ε / 4))
    {σ U : ℝ} (hσ : 17 / 30 ≤ σ) (hσ1 : σ ≤ 7 / 10 + η) (hU : 8 ≤ U) (Z : Finset (ZeroIdx (sqF Xi)))
    (hZ : ∀ i ∈ Z, U ≤ |(tau i).re| ∧ |(tau i).re| ≤ 2 * U ∧ σ ≤ βs i) :
    (Z.card : ℝ) ≤ Cwg C₄ * Real.log U ^ 11 * U ^ (30 / 13 * (1 - σ) + η + ε / 4) := by
  have hc0 : (0 : ℝ) ≤ 1 / 13 := by norm_num
  have hc1 : (1 / 13 : ℝ) ≤ 1 := by norm_num
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hY := Yw_ge hc0 hU
  have hwc := window_classes_ingham (ε := 3 * ε / 4) (by linarith) (by linarith) hC₄ h4 (δ := 1 / 15)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith) hY
    (lam := U ^ (5 / 13 * (1 / 2 - σ) + ε / 4)) (by positivity) (Xw_one hU) Nw_one (XN_ge hU) Z hZ
  refine hwc.trans ?_
  set L := Real.log U with hLdef
  set E := 30 / 13 * (1 - σ) with hE
  have hL := log_ge_two hU
  have hL1 : 1 ≤ L := by linarith
  have hE' : (2 + 4 * (1 / 13 : ℝ)) * (1 - σ) = E := by rw [hE]; ring
  have hUE : 0 ≤ U ^ E := by positivity
  have hK := bound_K hc0 hc1 hU
  have hl := bound_ell hc0 hc1 hU
  have hS := bound_S1 hc0 hc1 (σ := σ) (by linarith) (by linarith) hU
  rw [hE'] at hS
  have hB3 := bound_B3_gm (σ := σ) hε0 hε1 hC₄ hU
  have hKl := Kloc_le (U := U) (by linarith)
  have hKl0 : 0 ≤ Kloc (2 * U + 1) := Kloc_nonneg (by linarith)
  have he : 32 * Real.exp 1 ≤ 96 := by have := Real.exp_one_lt_d9; linarith
  have hK0 : (0 : ℝ) ≤ ((Nat.log 2 (Nw (1 / 13) U) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX1 : (1 : ℝ) ≤ Xw U := by exact_mod_cast Xw_one hU
  have hN1 : (1 : ℝ) ≤ Nw (1 / 13) U := by exact_mod_cast (Nw_one (c := 1 / 13) (U := U))
  have hl0 : 0 ≤ 1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 13) U)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (Xw U : ℝ) * (Nw (1 / 13) U) by nlinarith)
    linarith
  have hS0 : 0 ≤ U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 13) U)) ^ (2 - 2 * σ) := by positivity
  have e16 : ∀ x : ℝ, x / (1 / 4) ^ 2 = 16 * x := fun x => by norm_num [div_eq_mul_inv]; ring
  have hEe : U ^ E ≤ U ^ (E + η + ε / 4) := Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
  have hT1 : ((Nat.log 2 (Nw (1 / 13) U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 13) U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 13) U)) ^ (2 - 2 * σ)))
      ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ (E + η + ε / 4) := by
    rw [e16]
    calc 16 * ((Nat.log 2 (Nw (1 / 13) U) + 1 : ℕ) : ℝ) ^ 3
          * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 13) U))) ^ 6
            * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 13) U)) ^ (2 - 2 * σ)))
        ≤ 16 * (13 * L) ^ 3 * (96 * (9 * L) ^ 6 * (71 * L * U ^ E)) := by gcongr
      _ = 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ E := by ring
      _ ≤ 16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ (E + η + ε / 4) := by gcongr
  have hexp : 20 / 13 * (1 / 2 - σ) + 1 + ε / 4 ≤ E + η + ε / 4 := by rw [hE]; linarith
  have hB3' : 2 * (3 * KG * (Yw (1 / 13) U) ^ (1 / 2 - σ) / (1 / 15)) * U ^ (5 / 13 * (1 / 2 - σ) + ε / 4) *
        (MV (Xw U) * (U + (Xw U) + 1)) +
      (3 * KG * (Yw (1 / 13) U) ^ (1 / 2 - σ) / (1 / 15)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) /
        (U ^ (5 / 13 * (1 / 2 - σ) + ε / 4)) ^ 2
      ≤ (216000 * KG + 18225 * KG ^ 2 * C₄) * L ^ 10 * U ^ (E + η + ε / 4) := by
    refine hB3.trans ?_
    have h510 : L ^ 5 ≤ L ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
    have := KG_pos
    have hU' : U ^ (20 / 13 * (1 / 2 - σ) + 1 + ε / 4) ≤ U ^ (E + η + ε / 4) :=
      Real.rpow_le_rpow_of_exponent_le hU1 hexp
    gcongr
  have hKlL : Kloc (2 * U + 1) ≤ Kc * L := hKl
  have hsum0 : 0 ≤ 2 * (((Nat.log 2 (Nw (1 / 13) U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 13) U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 13) U)) ^ (2 - 2 * σ))))
      + (2 * (3 * KG * (Yw (1 / 13) U) ^ (1 / 2 - σ) / (1 / 15)) * U ^ (5 / 13 * (1 / 2 - σ) + ε / 4) *
        (MV (Xw U) * (U + (Xw U) + 1)) +
      (3 * KG * (Yw (1 / 13) U) ^ (1 / 2 - σ) / (1 / 15)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) /
        (U ^ (5 / 13 * (1 / 2 - σ) + ε / 4)) ^ 2) := by
    have : 0 ≤ MV (Xw U) := by unfold MV; have := Real.log_nonneg hX1; positivity
    have := KG_pos
    have : 0 < Yw (1 / 13) U := by unfold Yw; positivity
    positivity
  have hKcL : 0 ≤ 2 * (Kc * L) := by have := Kc_nonneg; positivity
  calc 2 * Kloc (2 * U + 1) * (2 * (((Nat.log 2 (Nw (1 / 13) U) + 1 : ℕ) : ℝ) ^ 3 / (1 / 4) ^ 2
      * (32 * Real.exp 1 * (1 + Real.log (2 * (Xw U : ℝ) * (Nw (1 / 13) U))) ^ 6
        * (U * ((Xw U : ℝ)) ^ (1 - 2 * σ) + ((Xw U : ℝ) * (Nw (1 / 13) U)) ^ (2 - 2 * σ))))
      + (2 * (3 * KG * (Yw (1 / 13) U) ^ (1 / 2 - σ) / (1 / 15)) * U ^ (5 / 13 * (1 / 2 - σ) + ε / 4) *
        (MV (Xw U) * (U + (Xw U) + 1)) +
      (3 * KG * (Yw (1 / 13) U) ^ (1 / 2 - σ) / (1 / 15)) ^ 2 * (C₄ * (2 * U + 2) ^ (1 + 3 * ε / 4)) /
        (U ^ (5 / 13 * (1 / 2 - σ) + ε / 4)) ^ 2))
      ≤ 2 * (Kc * L) * (2 * (16 * 13 ^ 3 * 96 * 9 ^ 6 * 71 * L ^ 10 * U ^ (E + η + ε / 4))
          + (216000 * KG + 18225 * KG ^ 2 * C₄) * L ^ 10 * U ^ (E + η + ε / 4)) := by
        gcongr
    _ = Cwg C₄ * L ^ 11 * U ^ (E + η + ε / 4) := by unfold Cwg; ring

/-- **The count at the exponent `30/13` on `17/30 ≤ σ ≤ 7/10 + η`**: for `0 < ε ≤ 1` and `0 ≤ η ≤ 1/10` there is
`C ≥ 0` with `N(σ, T) ≤ C T^{(30/13)(1−σ)+η+ε/4}(log T)^{12}` for `T ≥ 2` (`ZetaIngham.nx_le_of_windows` with
`window_count_ingham13`). -/
theorem nx_ingham13 {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1 / 10) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 17 / 30 ≤ σ → σ ≤ 7 / 10 + η →
      (NX (σ - 1 / 2) T : ℝ) ≤ C * T ^ (30 / 13 * (1 - σ) + η + ε / 4) * Real.log T ^ 12 := by
  obtain ⟨C₄, hC₄⟩ := ZetaFourth.zeta_fourth_moment (ε := 3 * ε / 4) (by positivity) (by linarith)
  set C₄' := max C₄ 0 with hC₄'
  have hC₄'0 : 0 ≤ C₄' := le_max_right _ _
  have h4 : ∀ (C' : Finset ℕ) (t : ℕ → ℝ), (∀ r ∈ C', ∀ s ∈ C', r ≠ s → 1 ≤ |t r - t s|) → ∀ T : ℝ, 0 ≤ T →
      (∀ r ∈ C', |t r| ≤ T) → ∑ r ∈ C', ‖riemannZeta (1 / 2 + t r * I)‖ ^ 4 ≤ C₄' * (T + 2) ^ (1 + 3 * ε / 4) := by
    intro C' t hsep T hT ht
    refine (hC₄ C' t hsep T hT ht).trans ?_
    gcongr
    exact le_max_left _ _
  refine ⟨((finite_re_le 8).toFinset.card : ℝ) * 2 ^ 12 + 4 * Cwg C₄', by
    have := Cwg_nonneg hC₄'0; positivity, fun T hT σ hσ hσ1 => ?_⟩
  have he0 : 0 ≤ 30 / 13 * (1 - σ) + η + ε / 4 := by nlinarith
  exact nx_le_of_windows he0 (Cwg_nonneg hC₄'0)
    (fun U hU Z hZ => window_count_ingham13 hε.le hε1 hη hη1 hC₄'0 h4 hσ hσ1 hU Z hZ) hT

end ZetaGMIngham

#print axioms ZetaGMIngham.bound_B3_gm
#print axioms ZetaGMIngham.window_count_ingham13
#print axioms ZetaGMIngham.nx_ingham13
