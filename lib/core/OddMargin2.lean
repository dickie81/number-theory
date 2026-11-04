import Mathlib
import WeilCoer
import CmEncOdd6

/-! # Odd-sector margin `4·10⁻⁵` at `L = 1/2`

With the odd `C^ψ` enclosure tightened to `6·10⁻⁹` (`CmEncOdd6`), the existing odd head certificate
(`δ = 42·10⁻⁶`) leaves the margin `δ − 28ρ ≥ 4·10⁻⁵` with `ρ = 10⁻⁸`. -/

namespace OddMargin2

open Finset Real WeilTail WeilTailB WeilHead

theorem odd_chk2 : chk L05Odd2.Mq L05Odd2.Dq (42/1000000) (-1) OddQ.bq OddQ.pq OddQ.cq
    (1/10^8 - (1/10^12 + 10 * (1/10^12) + 6/10^9)) = true := by decide +kernel

theorem oddHead2 : ∀ i < 28, ∀ j < 28,
    |Rm 1 (-1) wψ βs i j - certMat 28 L05Odd2.Mn L05Odd2.Dn L05Odd2.δ i j| ≤ 1 / 10 ^ 8 := by
  intro i hi j hj
  have E : HeadEnc 1 OddQ.bq OddQ.pq OddQ.cq (1/10^12) (1/10^12) (6/10^9) :=
    ⟨WeilConst.beta_enc_odd, fun i hi => WeilConst.pole_enc_odd i hi, CmFin.cmEnc_odd6⟩
  have h1 := Rm_near (σ := -1) (by norm_num) E (by norm_num) odd_pchk hi hj
  have h2 := chk_spec odd_chk2 hi hj
  have h3 := certMat_eq L05Odd2.Mq L05Odd2.Dq (42/1000000) hi hj
  have hM : L05Odd2.Mn = fun k i => if h : k < 28 ∧ i < 28 then ((getq L05Odd2.Mq k i : ℚ) : ℝ) else 0 := rfl
  have hD : L05Odd2.Dn = fun k => if k < 28 then ((L05Odd2.Dq.getD k 0 : ℚ) : ℝ) else 0 := by
    funext k; unfold L05Odd2.Dn L05Odd2.D; split_ifs <;> rfl
  have hδ : L05Odd2.δ = (((42/1000000) : ℚ) : ℝ) := by unfold L05Odd2.δ; norm_num
  rw [hM, hD, hδ, h3]
  push_cast at h1 h2
  calc _ ≤ |Rm 1 (-1) wψ βs i j - ((Aq (-1) OddQ.bq OddQ.pq OddQ.cq i j : ℚ) : ℝ)|
        + |((Aq (-1) OddQ.bq OddQ.pq OddQ.cq i j : ℚ) : ℝ) - ((certq L05Odd2.Mq L05Odd2.Dq (42/1000000) i j : ℚ) : ℝ)| :=
          abs_sub_le _ _ _
    _ ≤ ((1/10^12:ℝ) + 10 * (1/10^12:ℝ) + (6/10^9:ℝ)) + ((1/10^8:ℝ) - ((1/10^12:ℝ) + 10 * (1/10^12:ℝ) + (6/10^9:ℝ))) :=
          add_le_add (by simpa using h1) (by linarith)
    _ = _ := by ring

theorem odd_margin2 (N : ℕ) (hN : 28 ≤ N) (y : ℕ → ℝ) :
    (4 / 100000 : ℝ) * ∑ i ∈ range N, y i ^ 2 ≤ WeilZhuRed.QF 1 (-1) N y := by
  have hm := sector_margin 1 le_rfl (by norm_num) _ _ _ _ (4 / 100000) (5 / 10 ^ 25) L05Odd2.hDn (by norm_num)
    oddHead2 b57_le (by simp only [L05Odd2.δ]; norm_num) (by norm_num) (by simp only [L05Odd2.δ]; norm_num) N hN y
  exact hm.trans (WeilZhuRed.QF_ge_R 1 (-1) (WeilPlanch.modePlancherel_of WeilModes.modeDecay 1
    (WeilFourier.modeOrth (by norm_num))) N y)

end OddMargin2
