import Mathlib
import V3FinA
import V3FinRe0
import V3FinRe1
import V3FinRo0
import V3FinRo1

/-! # The entries `C3` enclosed at `λ = log 3`: every `|C3(2i+par, 2j+par) − ĉᵢⱼ| ≤ 3·10⁻⁹`, `i, j < 28`

The kernel checks of `V3FinR*` cover the upper triangle row by row; `entry3_sym` turns them into enclosures of every
entry. -/

namespace V3Fin

lemma rows_even (i : ℕ) (hi : i < 28) : rowOK3 0 cqE (3 / 10 ^ 9) i = true := by
  interval_cases i
  exacts [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22,
    e23, e24, e25, e26, e27]

lemma rows_odd (i : ℕ) (hi : i < 28) : rowOK3 1 cqO (3 / 10 ^ 9) i = true := by
  interval_cases i
  exacts [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22,
    o23, o24, o25, o26, o27]

lemma row_spec {par : ℕ} {cq : List (List ℚ)} {εc : ℚ} {i : ℕ} (h : rowOK3 par cq εc i = true) {j : ℕ}
    (hij : i ≤ j) (hj : j < 28) : R3e (2 * i + par) (2 * j + par) (cs cq i j) ≤ εc := by
  unfold rowOK3 at h
  exact of_decide_eq_true (List.all_eq_true.1 h j (List.mem_range'_1.2 ⟨hij, by omega⟩))

theorem c3Enc_even : ∀ i < 28, ∀ j < 28,
    |V3Zhu.C3 (2 * i + 0) (2 * j + 0) - ((cs cqE i j : ℚ) : ℝ)| ≤ 3 / 10 ^ 9 := by
  intro i hi j hj
  have := entry3_sym 0 i j (by norm_num) hi hj cqE (3 / 10 ^ 9)
    (fun i' hi' j' hj' hij => row_spec (rows_even i' hi') hij hj')
  push_cast at this; exact this

theorem c3Enc_odd : ∀ i < 28, ∀ j < 28,
    |V3Zhu.C3 (2 * i + 1) (2 * j + 1) - ((cs cqO i j : ℚ) : ℝ)| ≤ 3 / 10 ^ 9 := by
  intro i hi j hj
  have := entry3_sym 1 i j (by norm_num) hi hj cqO (3 / 10 ^ 9)
    (fun i' hi' j' hj' hij => row_spec (rows_odd i' hi') hij hj')
  push_cast at this; exact this

end V3Fin
