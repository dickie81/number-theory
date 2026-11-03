import Mathlib
import CmFinP

/-! # The entry theorem: a passing rational row check gives `|Cm wψ n m − c| ≤ εc` -/

namespace CmFin

open Finset Real CmPoly CmW CmNu CmLhD CmBessel CmWD CmMom CmAsm CmData WeilTailB MeasureTheory

set_option maxRecDepth 100000 in
lemma X_eq (n m : ℕ) : (((XN n m : ℚ) / 2 ^ 384 : ℚ) : ℝ) = ∑ k ∈ range 40, ∑ l ∈ range 40,
    ((qQ n k : ℚ) : ℝ) * ((qQ m l : ℚ) : ℝ) * ((nuQ ((n + m) / 2 + k + l) : ℚ) : ℝ) := by
  unfold XN qQ nuQ
  simp_rw [lsumZ]
  push_cast
  rw [Finset.sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_div]
  refine sum_congr rfl fun l _ => ?_
  rw [div_mul_div_comm, div_mul_div_comm]; congr 1
  exact_mod_cast (show (2:ℕ) ^ 384 = 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 by rfl)

lemma Ih_X (n m : ℕ) (hn : n < 56) (hm : m < 56) :
    |Ih n m - (((XN n m : ℚ) / 2 ^ 384 : ℚ) : ℝ)| ≤ ((aq n * aq m * 128 / 2 ^ 128 : ℚ) : ℝ) := by
  rw [X_eq]
  have hA : ∀ n, ((aq n : ℚ) : ℝ) = ∑ k ∈ range 40, |((qQ n k : ℚ) : ℝ)| := by
    intro n; unfold aq; rw [WeilHead.cast_lsum]; push_cast; rfl
  rw [show ((aq n * aq m * 128 / 2 ^ 128 : ℚ) : ℝ) = (aq n : ℝ) * (aq m : ℝ) * 128 / 2 ^ 128 by push_cast; ring,
    hA, hA]
  have hq : ∀ k, q n k = qQ n k := fun k => q_eq n k hn
  have hq' : ∀ k, q m k = qQ m k := fun k => q_eq m k hm
  unfold Ih
  simp only [hq, hq']
  rw [← sum_sub_distrib, Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  rw [← sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l hl => ?_)
  have hk' := mem_range.1 hk; have hl' := mem_range.1 hl
  have hj : (n + m) / 2 + k + l < 134 := by omega
  have e := nu_err _ hj
  rw [show ((qQ n k : ℚ) : ℝ) * ((qQ m l : ℚ) : ℝ) * ((((mG ((n + m) / 2 + k + l)) : ℚ) : ℝ) -
      ∑ p ∈ range 128, ((mP p ((n + m) / 2 + k + l) : ℚ) : ℝ)) -
      ((qQ n k : ℚ) : ℝ) * ((qQ m l : ℚ) : ℝ) * ((nuQ ((n + m) / 2 + k + l) : ℚ) : ℝ)
      = ((qQ n k : ℚ) : ℝ) * ((qQ m l : ℚ) : ℝ) * ((((mG ((n + m) / 2 + k + l)) : ℚ) : ℝ) -
      ∑ p ∈ range 128, ((mP p ((n + m) / 2 + k + l) : ℚ) : ℝ) - ((nuQ ((n + m) / 2 + k + l) : ℚ) : ℝ)) by ring,
    abs_mul, abs_mul]
  have : |((qQ n k : ℚ) : ℝ)| * |((qQ m l : ℚ) : ℝ)| * 128 / 2 ^ 128
      = |((qQ n k : ℚ) : ℝ)| * |((qQ m l : ℚ) : ℝ)| * (128 / 2 ^ 128) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left e (by positivity)

lemma between (K Kl Kh x d : ℝ) (h1 : Kl ≤ K) (h2 : K ≤ Kh) :
    |K * x - d| ≤ max |Kl * x - d| |Kh * x - d| := by
  rcases le_total 0 x with hx | hx
  · have a : Kl * x ≤ K * x := mul_le_mul_of_nonneg_right h1 hx
    have b : K * x ≤ Kh * x := mul_le_mul_of_nonneg_right h2 hx
    rw [abs_le]; constructor
    · have := le_max_left |Kl * x - d| |Kh * x - d|; have := neg_abs_le (Kl * x - d); linarith
    · have := le_max_right |Kl * x - d| |Kh * x - d|; have := le_abs_self (Kh * x - d); linarith
  · have a : K * x ≤ Kl * x := mul_le_mul_of_nonpos_right h1 hx
    have b : Kh * x ≤ K * x := mul_le_mul_of_nonpos_right h2 hx
    rw [abs_le]; constructor
    · have := le_max_right |Kl * x - d| |Kh * x - d|; have := neg_abs_le (Kh * x - d); linarith
    · have := le_max_left |Kl * x - d| |Kh * x - d|; have := le_abs_self (Kl * x - d); linarith

def Zq (n m : ℕ) : ℚ := (XN n m : ℚ) / 2 ^ 384
def Klq (n m : ℕ) : ℚ := 30 * (1 / WeilConst.phi) * (sqb.getD n (0, 0)).1 * (sqb.getD m (0, 0)).1
def Khq (n m : ℕ) : ℚ := 30 * (1 / WeilConst.plo) * (sqb.getD n (0, 0)).2 * (sqb.getD m (0, 0)).2
def csq (n m : ℕ) (c : ℚ) : ℚ := sg n * sg m * c
def Eaq (n m : ℕ) : ℚ := aq n * aq m * 128 / 2 ^ 128

lemma R_eq (n m : ℕ) (c : ℚ) : R n m c = max |Klq n m * Zq n m - csq n m c| |Khq n m * Zq n m - csq n m c|
    + Khq n m * (56 * eJU n m + Eaq n m) + εwq := rfl

theorem entry (par i j : ℕ) (hp : par < 2) (hi : i < 28) (hj : j < 28) (c εc : ℚ)
    (h : R (2 * i + par) (2 * j + par) c ≤ εc) : |Cm wψ (2 * i + par) (2 * j + par) - c| ≤ εc := by
  have hn : 2 * i + par < 56 := by omega
  have hm : 2 * j + par < 56 := by omega
  have hpar : (2 * i + par + (2 * j + par)) % 2 = 0 := by omega
  have hπ := Real.pi_pos
  have hpb := CmGlob.pi_b
  have hplo : (0:ℝ) < WeilConst.plo := by unfold WeilConst.plo; norm_num
  have hphi : (0:ℝ) < WeilConst.phi := by unfold WeilConst.phi; norm_num
  -- notation
  have hCm := Cm_eq (2 * i + par) (2 * j + par)
  have hKJ := absTT par i j hp
  rw [abs_eq30] at hKJ
  have hJA0 : 0 ≤ ∫ s in (0:ℝ)..1, |jP (2 * i + par) (15 * s) * jP (2 * j + par) (15 * s)| :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => abs_nonneg _
  obtain ⟨bn1, bn2, bn0⟩ := sq_b _ hn
  obtain ⟨bm1, bm2, bm0⟩ := sq_b _ hm
  have e1 := I_err _ _ hn hm hpar
  have e2 : |Ih (2 * i + par) (2 * j + par) - ((Zq (2 * i + par) (2 * j + par) : ℚ) : ℝ)|
      ≤ ((Eaq (2 * i + par) (2 * j + par) : ℚ) : ℝ) := Ih_X _ _ hn hm
  generalize hI : (∫ s in (0:ℝ)..1, wψ (30 * s) * (jP (2 * i + par) (15 * s) * jP (2 * j + par) (15 * s))) = I at hCm e1
  generalize hJ : (∫ s in (0:ℝ)..1, |jP (2 * i + par) (15 * s) * jP (2 * j + par) (15 * s)|) = JA at hKJ hJA0 e1
  have t0n := eT_nonneg _ hn; have t0m := eT_nonneg _ hm
  have tn := eT_le _ hn; have tm := eT_le _ hm
  generalize 2 * i + par = n at *
  generalize 2 * j + par = m at *
  generalize hcn : √(2 * (n:ℝ) + 1) = cn at *
  generalize hcm : √(2 * (m:ℝ) + 1) = cm at *
  have cn0 : 0 ≤ cn := hcn ▸ Real.sqrt_nonneg _
  have cm0 : 0 ≤ cm := hcm ▸ Real.sqrt_nonneg _
  set K : ℝ := 30 / π * (cn * cm) with hK
  have hK0 : 0 ≤ K := by positivity
  have hKJ' : K * JA ≤ 1 := by
    calc K * JA = 1 / π * (30 * (cn * cm) * JA) := by rw [hK]; ring
      _ ≤ 1 := hKJ
  have u1 : (1 / (WeilConst.phi : ℝ)) ≤ 1 / π := one_div_le_one_div_of_le hπ hpb.2.le
  have u2 : 1 / π ≤ 1 / (WeilConst.plo : ℝ) := one_div_le_one_div_of_le hplo hpb.1.le
  have Kl : ((Klq n m : ℚ) : ℝ) ≤ K := by
    unfold Klq; push_cast
    rw [hK, div_eq_mul_one_div 30 π]
    have := mul_le_mul u1 (mul_le_mul bn1 bm1 bm0 cn0) (mul_nonneg bn0 bm0) (by positivity)
    nlinarith
  have Kh : K ≤ ((Khq n m : ℚ) : ℝ) := by
    unfold Khq; push_cast
    rw [hK, div_eq_mul_one_div 30 π]
    have := mul_le_mul u2 (mul_le_mul bn2 bm2 cm0 (cn0.trans bn2)) (mul_nonneg cn0 cm0) (by positivity)
    nlinarith
  have hB0 : ∀ k, (0:ℝ) ≤ BU k := fun k => by unfold BU; positivity
  have hB : ∀ k, ((Bq k : ℚ) : ℝ) = ((BU k : ℚ) : ℝ) := fun k => rfl
  have heJ : (eJ n m : ℝ) ≤ eJU n m := by
    unfold eJ eJU; push_cast; rw [hB, hB]
    have := hB0 n; have := hB0 m
    have a1 : ((BU n : ℚ) : ℝ) * eTq m ≤ (BU n : ℝ) * eU m := mul_le_mul_of_nonneg_left tm (hB0 n)
    have a2 : (((BU m : ℚ) : ℝ) + eTq m) * eTq n ≤ ((BU m : ℝ) + eU m) * eU n :=
      mul_le_mul (by linarith) tn t0n (by linarith)
    linarith
  have heJ0 : (0:ℝ) ≤ eJ n m := by
    unfold eJ; push_cast; rw [hB]; have := hB0 n; have := hB0 m; positivity
  have hSS : (sg n : ℝ) * sg m * ((sg n : ℝ) * sg m) = 1 := by unfold sg; split_ifs <;> norm_num
  have hS1 : |(sg n : ℝ) * sg m| = 1 := by unfold sg; split_ifs <;> norm_num
  have hcs : ((csq n m c : ℚ) : ℝ) = (sg n : ℝ) * sg m * c := by unfold csq; push_cast; ring
  have main : |Cm wψ n m - c| ≤ |K * I - ((csq n m c : ℚ) : ℝ)| := by
    rw [hCm, hcs, show 30 / π * ((sg n : ℝ) * sg m) * (cn * cm) * I - (c:ℝ)
        = ((sg n : ℝ) * sg m) * (K * I - (sg n : ℝ) * sg m * c) by
          rw [hK]; linear_combination (c:ℝ) * hSS,
      abs_mul, hS1, one_mul]
  have b1 : K * |I - Ih n m| ≤ (εw : ℝ) + K * (56 * eJ n m) := by
    calc K * |I - Ih n m| ≤ K * ((εw : ℝ) * JA + 56 * eJ n m) := mul_le_mul_of_nonneg_left e1 hK0
      _ = (εw : ℝ) * (K * JA) + K * (56 * eJ n m) := by ring
      _ ≤ (εw : ℝ) * 1 + K * (56 * eJ n m) := by
        have : (0:ℝ) ≤ εw := by norm_num [εw]
        exact add_le_add (mul_le_mul_of_nonneg_left hKJ' this) le_rfl
      _ = _ := by ring
  have b2 : K * |Ih n m - (Zq n m : ℝ)| ≤ K * ((Eaq n m : ℚ) : ℝ) := mul_le_mul_of_nonneg_left e2 hK0
  have b3 := between K _ _ ((Zq n m : ℚ) : ℝ) ((csq n m c : ℚ) : ℝ) Kl Kh
  have hE0 : (0:ℝ) ≤ ((Eaq n m : ℚ) : ℝ) := (abs_nonneg _).trans e2
  have hKe : K * (56 * (eJ n m : ℝ) + ((Eaq n m : ℚ) : ℝ))
      ≤ ((Khq n m : ℚ) : ℝ) * (56 * ((eJU n m : ℚ) : ℝ) + ((Eaq n m : ℚ) : ℝ)) := by
    calc _ ≤ K * (56 * ((eJU n m : ℚ) : ℝ) + ((Eaq n m : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_right Kh (by linarith)
  have hR : ((R n m c : ℚ) : ℝ) ≤ εc := by exact_mod_cast h
  rw [R_eq] at hR
  simp only [Rat.cast_add, Rat.cast_max, Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] at hR
  have hεw : (εw : ℝ) = εwq := by norm_num [εw, εwq]
  refine main.trans ?_
  rw [show K * I - ((csq n m c : ℚ) : ℝ) = K * (I - Ih n m) + K * (Ih n m - (Zq n m : ℝ))
      + (K * (Zq n m : ℝ) - ((csq n m c : ℚ) : ℝ)) by ring]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  rw [abs_mul K, abs_mul K, abs_of_nonneg hK0]
  have hsplit : K * (56 * (eJ n m : ℝ)) + K * ((Eaq n m : ℚ) : ℝ) = K * (56 * (eJ n m : ℝ) + ((Eaq n m : ℚ) : ℝ)) := by ring
  linarith

end CmFin
