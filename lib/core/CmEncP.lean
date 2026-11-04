import Mathlib
import CmFinA
import CmFinRe0
import CmFinRe1
import CmFinRe2
import CmFinRe3
import CmFinRo0
import CmFinRo1
import CmFinRo2
import CmFinRo3

/-! # `CmEnc` discharged for both sectors: unconditional positivity of the Weil form at `L = 1/2` -/

namespace CmFin

open Finset Real WeilTailB

lemma rows_even (i : ℕ) (hi : i < 28) : rowOK 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) i = true := by
  interval_cases i
  exacts [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27]

lemma rows_odd (i : ℕ) (hi : i < 28) : rowOK 1 WeilHead.OddQ.cq (13 / 10 ^ 7) i = true := by
  interval_cases i
  exacts [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25, o26, o27]

theorem cmEnc_even : WeilConst.CmEnc 0 WeilHead.EvenQ.cq (6 / 10 ^ 9) := by
  intro i hi j hj
  have h := List.all_eq_true.1 (rows_even i hi) j (List.mem_range.2 hj)
  have := entry 0 i j (by norm_num) hi hj _ _ (of_decide_eq_true h)
  push_cast at this; exact this

theorem cmEnc_odd : WeilConst.CmEnc 1 WeilHead.OddQ.cq (13 / 10 ^ 7) := by
  intro i hi j hj
  have h := List.all_eq_true.1 (rows_odd i hi) j (List.mem_range.2 hj)
  have := entry 1 i j (by norm_num) hi hj _ _ (of_decide_eq_true h)
  push_cast at this; exact this

/-- **Unconditional even-sector positivity at `L = 1/2`.** -/
theorem L05_even_uncond (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) :
    0 < WeilForm.weilQ (1 / 2) (WeilPlanch.fx N x) :=
  WeilConst.L05_even cmEnc_even N hN x hx

/-- **Unconditional odd-sector positivity at `L = 1/2`.** -/
theorem L05_odd_uncond (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) :
    0 < WeilZhuRed.QF 1 (-1) N x :=
  WeilConst.L05_odd cmEnc_odd N hN x hx

end CmFin
