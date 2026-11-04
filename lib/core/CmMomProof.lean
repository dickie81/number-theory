import Mathlib
import CmMomChk

/-! # The rounded moments `ν̂` are within `128·2^-128` of the exact model moments -/

namespace CmMom

open Finset CmPoly CmW CmNu CmLhD

lemma lsumZ (n : ℕ) (f : ℕ → ℤ) : ((List.range n).map f).sum = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

lemma sum_blocks (f : ℕ → ℤ) : ∀ c : ℕ, ∑ p ∈ range (16 * c), f p = ∑ c' ∈ range c, ∑ i ∈ range 16, f (16 * c' + i)
  | 0 => by simp
  | c + 1 => by
    rw [show 16 * (c + 1) = 16 * c + 16 by ring, sum_range_add, sum_blocks f c,
      Finset.sum_range_succ (fun c' => ∑ i ∈ range 16, f (16 * c' + i)) c]

lemma cs_getD (c j : ℕ) (hj : j < 134) : (cs c).getD j 0 = ∑ i ∈ range 16, fl (mP (16 * c + i) j) := by
  unfold cs; rw [List.getD_eq_getElem?_getD]; simp [hj, lsumZ]

lemma gs_getD (j : ℕ) (hj : j < 134) : gs.getD j 0 = fl (mG j) := by
  unfold gs; rw [List.getD_eq_getElem?_getD]; simp [hj]

lemma CSL_getD (c : ℕ) (hc : c < 8) : CSL.getD c [] = cs c := by
  interval_cases c
  · exact (of_decide_eq_true cs0_chk).symm
  · exact (of_decide_eq_true cs1_chk).symm
  · exact (of_decide_eq_true cs2_chk).symm
  · exact (of_decide_eq_true cs3_chk).symm
  · exact (of_decide_eq_true cs4_chk).symm
  · exact (of_decide_eq_true cs5_chk).symm
  · exact (of_decide_eq_true cs6_chk).symm
  · exact (of_decide_eq_true cs7_chk).symm

theorem nuN_eq (j : ℕ) (hj : j < 134) : nuN.getD j 0 = fl (mG j) - ∑ p ∈ range 128, fl (mP p j) := by
  have h := of_decide_eq_true nu_chk
  rw [List.all_eq_true] at h
  have h2 := of_decide_eq_true (h j (List.mem_range.2 hj))
  rw [h2, ← (of_decide_eq_true gs_chk), gs_getD j hj, lsumZ, show (128:ℕ) = 16 * 8 by norm_num, sum_blocks]
  congr 1
  refine sum_congr rfl (fun c hc => ?_)
  rw [CSL_getD c (mem_range.1 hc), cs_getD c j hj]

lemma fl_bd (q : ℚ) : ((fl q : ℤ) : ℝ) / 2 ^ 128 ≤ (q : ℝ) ∧ (q : ℝ) - 1 / 2 ^ 128 < ((fl q : ℤ) : ℝ) / 2 ^ 128 := by
  have h1 := Int.floor_le (q * 2 ^ 128)
  have h2 := Int.lt_floor_add_one (q * 2 ^ 128)
  have a1 : ((fl q : ℤ) : ℝ) ≤ (q : ℝ) * 2 ^ 128 := by unfold fl; exact_mod_cast h1
  have a2 : (q : ℝ) * 2 ^ 128 < ((fl q : ℤ) : ℝ) + 1 := by unfold fl; exact_mod_cast h2
  have hp : (0:ℝ) < 2 ^ 128 := by positivity
  constructor
  · rw [div_le_iff₀ hp]; exact a1
  · rw [lt_div_iff₀ hp, sub_mul, one_div, inv_mul_cancel₀ hp.ne']; linarith

/-- rounded moment value -/
def nuQ (j : ℕ) : ℚ := (nuN.getD j 0 : ℚ) / 2 ^ 128

theorem nu_err (j : ℕ) (hj : j < 134) :
    |((mG j : ℚ) : ℝ) - ∑ p ∈ range 128, ((mP p j : ℚ) : ℝ) - ((nuQ j : ℚ) : ℝ)| ≤ 128 / 2 ^ 128 := by
  have e : ((nuQ j : ℚ) : ℝ) = ((fl (mG j) : ℤ) : ℝ) / 2 ^ 128 - ∑ p ∈ range 128, ((fl (mP p j) : ℤ) : ℝ) / 2 ^ 128 := by
    unfold nuQ; push_cast; rw [nuN_eq j hj]; push_cast; rw [← sum_div, sub_div]
  have g := fl_bd (mG j)
  have s1 : ∑ p ∈ range 128, ((fl (mP p j) : ℤ) : ℝ) / 2 ^ 128 ≤ ∑ p ∈ range 128, ((mP p j : ℚ) : ℝ) :=
    sum_le_sum fun p _ => (fl_bd (mP p j)).1
  have s2 : ∑ p ∈ range 128, (((mP p j : ℚ) : ℝ) - 1 / 2 ^ 128) ≤ ∑ p ∈ range 128, ((fl (mP p j) : ℤ) : ℝ) / 2 ^ 128 :=
    sum_le_sum fun p _ => (fl_bd (mP p j)).2.le
  rw [sum_sub_distrib, sum_const, card_range] at s2
  rw [e, abs_le]; constructor <;> norm_num at s2 ⊢ <;> linarith [g.1, g.2]

end CmMom
