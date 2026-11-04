import Mathlib
import CmAsm
import CmMomProof
import CmFinD
import WeilFourier

/-! # Assembly: from the rational entry bound `R` to `|Cm wψ n m − c| ≤ R` -/

namespace CmFin

open Finset Real CmPoly CmW CmNu CmLhD CmBessel CmWD CmMom CmAsm CmData WeilTailB MeasureTheory

theorem qh_chk : ((List.range 56).all fun n =>
    decide (qh 128 40 96 n = (qN.getD n []).map (fun z : ℤ => ((z : ℚ) / 2 ^ 128)))) = true := by decide +kernel

theorem eT_chk : ((List.range 56).all fun n => decide (eTq n ≤ eU n)) = true := by decide +kernel

theorem sq_chk : ((List.range 56).all fun n => decide (0 ≤ (sqb.getD n (0, 0)).1 ∧ 0 ≤ (sqb.getD n (0, 0)).2 ∧
    (sqb.getD n (0, 0)).1 ^ 2 ≤ 2 * n + 1 ∧ 2 * (n : ℚ) + 1 ≤ (sqb.getD n (0, 0)).2 ^ 2)) = true := by decide +kernel

lemma q_eq (n k : ℕ) (hn : n < 56) : q n k = qQ n k := by
  have h := qh_chk; rw [List.all_eq_true] at h
  have e := of_decide_eq_true (h n (List.mem_range.2 hn))
  unfold q qQ; rw [e, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  simp only [List.getD_eq_getElem?_getD]
  cases (qN[n]?.getD [])[k]? <;> simp

lemma eT_le (n : ℕ) (hn : n < 56) : (eTq n : ℝ) ≤ eU n := by
  have h := eT_chk; rw [List.all_eq_true] at h
  exact_mod_cast of_decide_eq_true (h n (List.mem_range.2 hn))

lemma sq_b (n : ℕ) (hn : n < 56) :
    ((sqb.getD n (0, 0)).1 : ℝ) ≤ √(2 * n + 1) ∧ √(2 * n + 1) ≤ ((sqb.getD n (0, 0)).2 : ℝ) ∧
    (0:ℝ) ≤ (sqb.getD n (0, 0)).1 := by
  have h := sq_chk; rw [List.all_eq_true] at h
  obtain ⟨h0, h3, h1, h2⟩ := of_decide_eq_true (h n (List.mem_range.2 hn))
  have r0 : (0:ℝ) ≤ (sqb.getD n (0, 0)).1 := by exact_mod_cast h0
  have r1 : ((sqb.getD n (0, 0)).1 : ℝ) ^ 2 ≤ 2 * n + 1 := by exact_mod_cast h1
  have r2 : 2 * (n : ℝ) + 1 ≤ ((sqb.getD n (0, 0)).2 : ℝ) ^ 2 := by exact_mod_cast h2
  have r3 : (0:ℝ) ≤ (sqb.getD n (0, 0)).2 := by exact_mod_cast h3
  refine ⟨Real.le_sqrt_of_sq_le r1, ?_, r0⟩
  rw [Real.sqrt_le_left r3]; exact r2

lemma cn_eq (n : ℕ) : 2 * √((1 / 2) * ((n : ℝ) + 1 / 2)) = √(2 * n + 1) := by
  rw [show (2:ℝ) * √((1 / 2) * ((n : ℝ) + 1 / 2)) = √(2 ^ 2) * √((1 / 2) * ((n : ℝ) + 1 / 2)) by
    rw [Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by norm_num)]
  congr 1; ring

lemma sg_eq (n : ℕ) : ((-1 : ℝ) ^ (n / 2)) = (sg n : ℝ) := by
  unfold sg; split_ifs with h
  · rw [Even.neg_one_pow (Nat.even_iff.2 h)]; simp
  · rw [Odd.neg_one_pow (Nat.odd_iff.2 (by omega))]; simp

lemma That30 (n : ℕ) (s : ℝ) : That n (30 * s) = (sg n : ℝ) * (√(2 * n + 1) * jP n (15 * s)) := by
  unfold That; rw [sg_eq, cn_eq, show 30 * s / 2 = 15 * s by ring]

lemma cov (g : ℝ → ℝ) : ∫ t in (0:ℝ)..30, g t = 30 * ∫ s in (0:ℝ)..1, g (30 * s) := by
  rw [intervalIntegral.integral_comp_mul_left g (by norm_num : (30:ℝ) ≠ 0)]
  simp

lemma Cm_eq (n m : ℕ) : Cm wψ n m = (30 / π) * ((sg n : ℝ) * sg m) * (√(2 * n + 1) * √(2 * m + 1)) *
    ∫ s in (0:ℝ)..1, wψ (30 * s) * (jP n (15 * s) * jP m (15 * s)) := by
  unfold Cm; rw [cov, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  simp_rw [That30]
  congr 1; funext s; ring

lemma abs_eq30 (n m : ℕ) : ∫ t in (0:ℝ)..30, |That n t * That m t| =
    30 * (√(2 * n + 1) * √(2 * m + 1)) * ∫ s in (0:ℝ)..1, |jP n (15 * s) * jP m (15 * s)| := by
  rw [cov, mul_assoc]
  simp_rw [That30]
  congr 1; rw [← intervalIntegral.integral_const_mul]; congr 1; funext s
  have a := Real.sqrt_nonneg (2 * (n:ℝ) + 1); have b := Real.sqrt_nonneg (2 * (m:ℝ) + 1)
  rw [show (sg n : ℝ) * (√(2 * n + 1) * jP n (15 * s)) * ((sg m : ℝ) * (√(2 * m + 1) * jP m (15 * s)))
      = ((sg n : ℝ) * sg m) * ((√(2 * n + 1) * √(2 * m + 1)) * (jP n (15 * s) * jP m (15 * s))) by ring,
    abs_mul, abs_mul (√(2 * (n:ℝ) + 1) * √(2 * (m:ℝ) + 1)), abs_of_nonneg (mul_nonneg a b)]
  have : |(sg n : ℝ) * (sg m : ℝ)| = 1 := by unfold sg; split_ifs <;> norm_num
  rw [this]; ring

lemma L2 (par i : ℕ) (hp : par < 2) : ∫ t in (0:ℝ)..30, That (2 * i + par) t ^ 2 ≤ π := by
  have h := WeilFourier.modeOrth hp i i
  rw [ite_eq_left rfl] at h
  have hπ := Real.pi_pos
  have hI : ∫ t in Set.Ioi 0, WeilZhuRed.G par i i t = π := by
    field_simp at h; linarith
  have hint : IntegrableOn (WeilZhuRed.G par i i) (Set.Ioi 0) := by
    by_contra hc; rw [integral_undef hc] at hI; linarith
  have e : ∀ t, WeilZhuRed.G par i i t = That (2 * i + par) t ^ 2 := fun t => by unfold WeilZhuRed.G; ring
  rw [intervalIntegral.integral_of_le (by norm_num), ← hI]
  simp_rw [← e]
  refine setIntegral_mono_set hint (ae_of_all _ fun t => ?_) (ae_of_all _ fun t ht => ?_)
  · rw [e]; positivity
  · exact ht.1

lemma absTT (par i j : ℕ) (hp : par < 2) :
    (1 / π) * ∫ t in (0:ℝ)..30, |That (2 * i + par) t * That (2 * j + par) t| ≤ 1 := by
  have a := L2 par i hp; have b := L2 par j hp
  have hπ := Real.pi_pos
  have c1 := (WeilPlanch.That_cont (2 * i + par)); have c2 := (WeilPlanch.That_cont (2 * j + par))
  have hm : ∫ t in (0:ℝ)..30, |That (2 * i + par) t * That (2 * j + par) t|
      ≤ ∫ t in (0:ℝ)..30, (That (2 * i + par) t ^ 2 + That (2 * j + par) t ^ 2) / 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) ((c1.mul c2).abs.intervalIntegrable _ _)
      (((c1.pow 2).add (c2.pow 2)).div_const 2 |>.intervalIntegrable _ _) fun t _ => ?_
    rw [abs_mul]; nlinarith [sq_abs (That (2 * i + par) t), sq_abs (That (2 * j + par) t),
      sq_nonneg (|That (2 * i + par) t| - |That (2 * j + par) t|)]
  have i1 : IntervalIntegrable (fun x => That (2 * i + par) x ^ 2) volume 0 30 := (c1.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => That (2 * j + par) x ^ 2) volume 0 30 := (c2.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add i1 i2] at hm
  rw [div_mul_eq_mul_div, one_mul, div_le_one hπ]; linarith

end CmFin
