import Mathlib
import CmFinA
import V3Asm
import V3FinD
import V3Zhu

/-! # Assembly at `λ = log 3`: the data checks and the change of variables `t = 30 λ s`

`qh3_chk` and `eT3_chk` identify the generated Bessel data of `V3FinD` with the exact definitions of `V3Asm`;
`C3_eq` writes `C3 n m = (30λ/π) σₙσₘ √(2n+1)√(2m+1) ∫₀¹ wψ(30s) jₙ(15λs) jₘ(15λs) ds`; `absTT3` bounds the
absolute integral on `[0, 30λ]` by Cauchy–Schwarz and Plancherel. -/

namespace V3Fin

open Finset Real CmBessel CmMom WeilTailB MeasureTheory V3Asm V3Bessel

theorem qh3_chk : ((List.range 56).all fun n =>
    decide (qhX 128 Xh 40 96 n = (q3N.getD n []).map (fun z : ℤ => ((z : ℚ) / 2 ^ 128)))) = true := by decide +kernel

theorem eT3_chk : ((List.range 56).all fun n => decide (eTq3 n ≤ eU3 n)) = true := by decide +kernel

lemma q3_eq (n k : ℕ) (hn : n < 56) : q3 n k = qQ3 n k := by
  have h := qh3_chk; rw [List.all_eq_true] at h
  have e := of_decide_eq_true (h n (List.mem_range.2 hn))
  unfold q3 qQ3; rw [e, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  simp only [List.getD_eq_getElem?_getD]
  cases (q3N[n]?.getD [])[k]? <;> simp

lemma eT3_le (n : ℕ) (hn : n < 56) : (eTq3 n : ℝ) ≤ eU3 n := by
  have h := eT3_chk; rw [List.all_eq_true] at h
  exact_mod_cast of_decide_eq_true (h n (List.mem_range.2 hn))

lemma That3 (n : ℕ) (s : ℝ) :
    That n (30 * V3Scale.lam * s) = (CmFin.sg n : ℝ) * (√(2 * n + 1) * jP n (15 * V3Scale.lam * s)) := by
  unfold That; rw [CmFin.sg_eq, CmFin.cn_eq, show 30 * V3Scale.lam * s / 2 = 15 * V3Scale.lam * s by ring]

lemma cov3 (g : ℝ → ℝ) :
    ∫ t in (0:ℝ)..(30 * V3Scale.lam), g t = 30 * V3Scale.lam * ∫ s in (0:ℝ)..1, g (30 * V3Scale.lam * s) := by
  have hl := V3Scale.lam_pos
  rw [intervalIntegral.integral_comp_mul_left g (by positivity : (30 * V3Scale.lam : ℝ) ≠ 0), smul_eq_mul,
    mul_zero, mul_one, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

lemma Psi3_30 (s : ℝ) : V3Scale.Psi3 (30 * V3Scale.lam * s) - βs = wψ (30 * s) := by
  unfold V3Scale.Psi3 wψ
  rw [show 30 * V3Scale.lam * s / V3Scale.lam = 30 * s by field_simp [V3Scale.lam_pos.ne']]

lemma C3_eq (n m : ℕ) : V3Zhu.C3 n m = (30 * V3Scale.lam / π) * ((CmFin.sg n : ℝ) * CmFin.sg m) *
    (√(2 * n + 1) * √(2 * m + 1)) *
    ∫ s in (0:ℝ)..1, wψ (30 * s) * (jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)) := by
  unfold V3Zhu.C3
  rw [cov3, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  simp_rw [That3, Psi3_30]
  congr 1; funext s; ring

lemma abs_eq3 (n m : ℕ) : ∫ t in (0:ℝ)..(30 * V3Scale.lam), |That n t * That m t| =
    30 * V3Scale.lam * (√(2 * n + 1) * √(2 * m + 1)) *
      ∫ s in (0:ℝ)..1, |jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s)| := by
  rw [cov3, mul_assoc (30 * V3Scale.lam)]
  simp_rw [That3]
  congr 1; rw [← intervalIntegral.integral_const_mul]; congr 1; funext s
  have a := Real.sqrt_nonneg (2 * (n:ℝ) + 1); have b := Real.sqrt_nonneg (2 * (m:ℝ) + 1)
  rw [show (CmFin.sg n : ℝ) * (√(2 * n + 1) * jP n (15 * V3Scale.lam * s)) *
        ((CmFin.sg m : ℝ) * (√(2 * m + 1) * jP m (15 * V3Scale.lam * s)))
      = ((CmFin.sg n : ℝ) * CmFin.sg m) * ((√(2 * n + 1) * √(2 * m + 1)) *
        (jP n (15 * V3Scale.lam * s) * jP m (15 * V3Scale.lam * s))) by ring,
    abs_mul, abs_mul (√(2 * (n:ℝ) + 1) * √(2 * (m:ℝ) + 1)), abs_of_nonneg (mul_nonneg a b)]
  have : |(CmFin.sg n : ℝ) * (CmFin.sg m : ℝ)| = 1 := by unfold CmFin.sg; split_ifs <;> norm_num
  rw [this]; ring

lemma L2_3 (par i : ℕ) (hp : par < 2) : ∫ t in (0:ℝ)..(30 * V3Scale.lam), That (2 * i + par) t ^ 2 ≤ π := by
  have h := WeilFourier.modeOrth hp i i
  rw [ite_eq_left rfl] at h
  have hπ := Real.pi_pos
  have hI : ∫ t in Set.Ioi 0, WeilZhuRed.G par i i t = π := by
    field_simp at h; linarith
  have hint : IntegrableOn (WeilZhuRed.G par i i) (Set.Ioi 0) := by
    by_contra hc; rw [integral_undef hc] at hI; linarith
  have e : ∀ t, WeilZhuRed.G par i i t = That (2 * i + par) t ^ 2 := fun t => by unfold WeilZhuRed.G; ring
  rw [intervalIntegral.integral_of_le V3Zhu.lam30_pos.le, ← hI]
  simp_rw [← e]
  refine setIntegral_mono_set hint (ae_of_all _ fun t => ?_) (ae_of_all _ fun t ht => ?_)
  · rw [e]; positivity
  · exact ht.1

lemma absTT3 (par i j : ℕ) (hp : par < 2) :
    (1 / π) * ∫ t in (0:ℝ)..(30 * V3Scale.lam), |That (2 * i + par) t * That (2 * j + par) t| ≤ 1 := by
  have a := L2_3 par i hp; have b := L2_3 par j hp
  have hπ := Real.pi_pos
  have hl := V3Zhu.lam30_pos
  have c1 := (WeilPlanch.That_cont (2 * i + par)); have c2 := (WeilPlanch.That_cont (2 * j + par))
  have hm : ∫ t in (0:ℝ)..(30 * V3Scale.lam), |That (2 * i + par) t * That (2 * j + par) t|
      ≤ ∫ t in (0:ℝ)..(30 * V3Scale.lam), (That (2 * i + par) t ^ 2 + That (2 * j + par) t ^ 2) / 2 := by
    refine intervalIntegral.integral_mono_on hl.le ((c1.mul c2).abs.intervalIntegrable _ _)
      (((c1.pow 2).add (c2.pow 2)).div_const 2 |>.intervalIntegrable _ _) fun t _ => ?_
    rw [abs_mul]; nlinarith [sq_abs (That (2 * i + par) t), sq_abs (That (2 * j + par) t),
      sq_nonneg (|That (2 * i + par) t| - |That (2 * j + par) t|)]
  have i1 : IntervalIntegrable (fun x => That (2 * i + par) x ^ 2) volume 0 (30 * V3Scale.lam) :=
    (c1.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => That (2 * j + par) x ^ 2) volume 0 (30 * V3Scale.lam) :=
    (c2.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add i1 i2] at hm
  rw [div_mul_eq_mul_div, one_mul, div_le_one hπ]; linarith

end V3Fin
