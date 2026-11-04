import Mathlib
import V3FinP

/-! # The entry theorem at `λ = log 3`: a passing rational check gives `|C3 n m − c| ≤ εc` -/

namespace V3Fin

open Finset Real CmBessel CmMom CmData WeilTailB MeasureTheory V3Asm V3Bessel

set_option maxRecDepth 100000 in
lemma X3_eq (n m : ℕ) : (((XN3 n m : ℚ) / 2 ^ 384 : ℚ) : ℝ) = ∑ k ∈ range 40, ∑ l ∈ range 40,
    ((qQ3 n k : ℚ) : ℝ) * ((qQ3 m l : ℚ) : ℝ) * ((nuQ ((n + m) / 2 + k + l) : ℚ) : ℝ) := by
  unfold XN3 qQ3 nuQ
  simp_rw [lsumZ]
  push_cast
  rw [Finset.sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_div]
  refine sum_congr rfl fun l _ => ?_
  rw [div_mul_div_comm, div_mul_div_comm]; congr 1
  exact_mod_cast (show (2:ℕ) ^ 384 = 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 by rfl)

lemma Ih3_X (n m : ℕ) (hn : n < 56) (hm : m < 56) :
    |Ih3 n m - (((XN3 n m : ℚ) / 2 ^ 384 : ℚ) : ℝ)| ≤ ((aq3 n * aq3 m * 128 / 2 ^ 128 : ℚ) : ℝ) := by
  rw [X3_eq]
  have hA : ∀ n, ((aq3 n : ℚ) : ℝ) = ∑ k ∈ range 40, |((qQ3 n k : ℚ) : ℝ)| := by
    intro n; unfold aq3; rw [WeilHead.cast_lsum]; push_cast; rfl
  rw [show ((aq3 n * aq3 m * 128 / 2 ^ 128 : ℚ) : ℝ) = (aq3 n : ℝ) * (aq3 m : ℝ) * 128 / 2 ^ 128 by push_cast; ring,
    hA, hA]
  have hq : ∀ k, q3 n k = qQ3 n k := fun k => q3_eq n k hn
  have hq' : ∀ k, q3 m k = qQ3 m k := fun k => q3_eq m k hm
  unfold Ih3
  simp only [hq, hq']
  rw [← sum_sub_distrib, Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  rw [← sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l hl => ?_)
  have hk' := mem_range.1 hk; have hl' := mem_range.1 hl
  have hj : (n + m) / 2 + k + l < 134 := by omega
  have e := nu_err _ hj
  rw [show ((qQ3 n k : ℚ) : ℝ) * ((qQ3 m l : ℚ) : ℝ) * ((((mG ((n + m) / 2 + k + l)) : ℚ) : ℝ) -
      ∑ p ∈ range 128, ((mP p ((n + m) / 2 + k + l) : ℚ) : ℝ)) -
      ((qQ3 n k : ℚ) : ℝ) * ((qQ3 m l : ℚ) : ℝ) * ((nuQ ((n + m) / 2 + k + l) : ℚ) : ℝ)
      = ((qQ3 n k : ℚ) : ℝ) * ((qQ3 m l : ℚ) : ℝ) * ((((mG ((n + m) / 2 + k + l)) : ℚ) : ℝ) -
      ∑ p ∈ range 128, ((mP p ((n + m) / 2 + k + l) : ℚ) : ℝ) - ((nuQ ((n + m) / 2 + k + l) : ℚ) : ℝ)) by ring,
    abs_mul, abs_mul]
  have : |((qQ3 n k : ℚ) : ℝ)| * |((qQ3 m l : ℚ) : ℝ)| * 128 / 2 ^ 128
      = |((qQ3 n k : ℚ) : ℝ)| * |((qQ3 m l : ℚ) : ℝ)| * (128 / 2 ^ 128) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left e (by positivity)

def Zq3 (n m : ℕ) : ℚ := (XN3 n m : ℚ) / 2 ^ 384
def Klq3 (n m : ℕ) : ℚ :=
  30 * V3Log.l3lo * (1 / WeilConst.phi) * (sqb.getD n (0, 0)).1 * (sqb.getD m (0, 0)).1
def Khq3 (n m : ℕ) : ℚ :=
  30 * V3Log.l3hi * (1 / WeilConst.plo) * (sqb.getD n (0, 0)).2 * (sqb.getD m (0, 0)).2
def Eaq3 (n m : ℕ) : ℚ := aq3 n * aq3 m * 128 / 2 ^ 128

lemma R3e_eq (n m : ℕ) (c : ℚ) : R3e n m c =
    max |Klq3 n m * Zq3 n m - CmFin.csq n m c| |Khq3 n m * Zq3 n m - CmFin.csq n m c|
      + Khq3 n m * (56 * eJU3 n m + Eaq3 n m) + CmFin.εwq := rfl

theorem entry3 (par i j : ℕ) (hp : par < 2) (hi : i < 28) (hj : j < 28) (c εc : ℚ)
    (h : R3e (2 * i + par) (2 * j + par) c ≤ εc) : |V3Zhu.C3 (2 * i + par) (2 * j + par) - c| ≤ εc := by
  have hn : 2 * i + par < 56 := by omega
  have hm : 2 * j + par < 56 := by omega
  have hpar : (2 * i + par + (2 * j + par)) % 2 = 0 := by omega
  have hπ := Real.pi_pos
  have hpb := CmGlob.pi_b
  have hplo : (0:ℝ) < WeilConst.plo := by unfold WeilConst.plo; norm_num
  have hphi : (0:ℝ) < WeilConst.phi := by unfold WeilConst.phi; norm_num
  obtain ⟨hl1, hl2⟩ := V3Scale.lam_bounds
  have hlam := V3Scale.lam_pos
  have hl0 : (0:ℝ) ≤ (V3Log.l3lo : ℝ) := by unfold V3Log.l3lo; norm_num
  have hCm := C3_eq (2 * i + par) (2 * j + par)
  have hKJ := absTT3 par i j hp
  rw [abs_eq3] at hKJ
  have hJA0 : 0 ≤ ∫ s in (0:ℝ)..1, |jP (2 * i + par) (15 * V3Scale.lam * s) * jP (2 * j + par) (15 * V3Scale.lam * s)| :=
    intervalIntegral.integral_nonneg (by norm_num) fun s _ => abs_nonneg _
  obtain ⟨bn1, bn2, bn0⟩ := CmFin.sq_b _ hn
  obtain ⟨bm1, bm2, bm0⟩ := CmFin.sq_b _ hm
  have e1 := I3_err _ _ hn hm hpar
  have e2 : |Ih3 (2 * i + par) (2 * j + par) - ((Zq3 (2 * i + par) (2 * j + par) : ℚ) : ℝ)|
      ≤ ((Eaq3 (2 * i + par) (2 * j + par) : ℚ) : ℝ) := Ih3_X _ _ hn hm
  generalize hI : (∫ s in (0:ℝ)..1, wψ (30 * s) *
    (jP (2 * i + par) (15 * V3Scale.lam * s) * jP (2 * j + par) (15 * V3Scale.lam * s))) = I at hCm e1
  generalize hJ : (∫ s in (0:ℝ)..1,
    |jP (2 * i + par) (15 * V3Scale.lam * s) * jP (2 * j + par) (15 * V3Scale.lam * s)|) = JA at hKJ hJA0 e1
  have t0n := eT3_nonneg _ hn; have t0m := eT3_nonneg _ hm
  have tn := eT3_le _ hn; have tm := eT3_le _ hm
  generalize 2 * i + par = n at *
  generalize 2 * j + par = m at *
  generalize hcn : √(2 * (n:ℝ) + 1) = cn at *
  generalize hcm : √(2 * (m:ℝ) + 1) = cm at *
  have cn0 : 0 ≤ cn := hcn ▸ Real.sqrt_nonneg _
  have cm0 : 0 ≤ cm := hcm ▸ Real.sqrt_nonneg _
  set K : ℝ := 30 * V3Scale.lam / π * (cn * cm) with hK
  have hK0 : 0 ≤ K := by positivity
  have hKJ' : K * JA ≤ 1 := by
    calc K * JA = 1 / π * (30 * V3Scale.lam * (cn * cm) * JA) := by rw [hK]; ring
      _ ≤ 1 := hKJ
  have u1 : (1 / (WeilConst.phi : ℝ)) ≤ 1 / π := one_div_le_one_div_of_le hπ hpb.2.le
  have u2 : 1 / π ≤ 1 / (WeilConst.plo : ℝ) := one_div_le_one_div_of_le hplo hpb.1.le
  have Kl : ((Klq3 n m : ℚ) : ℝ) ≤ K := by
    unfold Klq3; push_cast
    rw [hK, div_eq_mul_one_div (30 * V3Scale.lam) π]
    have a1 := mul_le_mul hl1 u1 (by positivity) hlam.le
    have a2 := mul_le_mul a1 (mul_le_mul bn1 bm1 bm0 cn0) (mul_nonneg bn0 bm0) (by positivity)
    nlinarith
  have Kh : K ≤ ((Khq3 n m : ℚ) : ℝ) := by
    unfold Khq3; push_cast
    rw [hK, div_eq_mul_one_div (30 * V3Scale.lam) π]
    have a1 := mul_le_mul hl2 u2 (by positivity) (hlam.le.trans hl2)
    have a2 := mul_le_mul a1 (mul_le_mul bn2 bm2 cm0 (cn0.trans bn2)) (mul_nonneg cn0 cm0)
      (mul_nonneg (hlam.le.trans hl2) (one_div_pos.2 hplo).le)
    nlinarith
  have hB0 : ∀ k, (0:ℝ) ≤ BU3 k := fun k => by unfold BU3; positivity
  have hB : ∀ k, ((Bq3 k : ℚ) : ℝ) = ((BU3 k : ℚ) : ℝ) := fun k => rfl
  have heJ : (eJ3 n m : ℝ) ≤ eJU3 n m := by
    unfold eJ3 eJU3; push_cast; rw [hB, hB]
    have := hB0 n; have := hB0 m
    have a1 : ((BU3 n : ℚ) : ℝ) * eTq3 m ≤ (BU3 n : ℝ) * eU3 m := mul_le_mul_of_nonneg_left tm (hB0 n)
    have a2 : (((BU3 m : ℚ) : ℝ) + eTq3 m) * eTq3 n ≤ ((BU3 m : ℝ) + eU3 m) * eU3 n :=
      mul_le_mul (by linarith) tn t0n (by linarith)
    linarith
  have heJ0 : (0:ℝ) ≤ eJ3 n m := by
    unfold eJ3; push_cast; rw [hB]; have := hB0 n; have := hB0 m; positivity
  have hSS : (CmFin.sg n : ℝ) * CmFin.sg m * ((CmFin.sg n : ℝ) * CmFin.sg m) = 1 := by
    unfold CmFin.sg; split_ifs <;> norm_num
  have hS1 : |(CmFin.sg n : ℝ) * CmFin.sg m| = 1 := by unfold CmFin.sg; split_ifs <;> norm_num
  have hcs : ((CmFin.csq n m c : ℚ) : ℝ) = (CmFin.sg n : ℝ) * CmFin.sg m * c := by
    unfold CmFin.csq; push_cast; ring
  have main : |V3Zhu.C3 n m - c| ≤ |K * I - ((CmFin.csq n m c : ℚ) : ℝ)| := by
    rw [hCm, hcs, show 30 * V3Scale.lam / π * ((CmFin.sg n : ℝ) * CmFin.sg m) * (cn * cm) * I - (c:ℝ)
        = ((CmFin.sg n : ℝ) * CmFin.sg m) * (K * I - (CmFin.sg n : ℝ) * CmFin.sg m * c) by
          rw [hK]; linear_combination (c:ℝ) * hSS,
      abs_mul, hS1, one_mul]
  have b1 : K * |I - Ih3 n m| ≤ (CmWD.εw : ℝ) + K * (56 * eJ3 n m) := by
    calc K * |I - Ih3 n m| ≤ K * ((CmWD.εw : ℝ) * JA + 56 * eJ3 n m) := mul_le_mul_of_nonneg_left e1 hK0
      _ = (CmWD.εw : ℝ) * (K * JA) + K * (56 * eJ3 n m) := by ring
      _ ≤ (CmWD.εw : ℝ) * 1 + K * (56 * eJ3 n m) := by
        have : (0:ℝ) ≤ CmWD.εw := by norm_num [CmWD.εw]
        exact add_le_add (mul_le_mul_of_nonneg_left hKJ' this) le_rfl
      _ = _ := by ring
  have b2 : K * |Ih3 n m - (Zq3 n m : ℝ)| ≤ K * ((Eaq3 n m : ℚ) : ℝ) := mul_le_mul_of_nonneg_left e2 hK0
  have b3 := CmFin.between K _ _ ((Zq3 n m : ℚ) : ℝ) ((CmFin.csq n m c : ℚ) : ℝ) Kl Kh
  have hE0 : (0:ℝ) ≤ ((Eaq3 n m : ℚ) : ℝ) := (abs_nonneg _).trans e2
  have hKe : K * (56 * (eJ3 n m : ℝ) + ((Eaq3 n m : ℚ) : ℝ))
      ≤ ((Khq3 n m : ℚ) : ℝ) * (56 * ((eJU3 n m : ℚ) : ℝ) + ((Eaq3 n m : ℚ) : ℝ)) := by
    calc _ ≤ K * (56 * ((eJU3 n m : ℚ) : ℝ) + ((Eaq3 n m : ℚ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_right Kh (by linarith)
  have hR : ((R3e n m c : ℚ) : ℝ) ≤ εc := by exact_mod_cast h
  rw [R3e_eq] at hR
  simp only [Rat.cast_add, Rat.cast_max, Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] at hR
  have hεw : (CmWD.εw : ℝ) = CmFin.εwq := by norm_num [CmWD.εw, CmFin.εwq]
  refine main.trans ?_
  rw [show K * I - ((CmFin.csq n m c : ℚ) : ℝ) = K * (I - Ih3 n m) + K * (Ih3 n m - (Zq3 n m : ℝ))
      + (K * (Zq3 n m : ℝ) - ((CmFin.csq n m c : ℚ) : ℝ)) by ring]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  rw [abs_mul K, abs_mul K, abs_of_nonneg hK0]
  have hsplit : K * (56 * (eJ3 n m : ℝ)) + K * ((Eaq3 n m : ℚ) : ℝ) =
      K * (56 * (eJ3 n m : ℝ) + ((Eaq3 n m : ℚ) : ℝ)) := by ring
  linarith

/-- Entries below the diagonal follow by symmetry: a passing upper-triangle row check bounds every entry. -/
theorem entry3_sym (par i j : ℕ) (hp : par < 2) (hi : i < 28) (hj : j < 28) (cq : List (List ℚ)) (εc : ℚ)
    (h : ∀ i' < 28, ∀ j' < 28, i' ≤ j' → R3e (2 * i' + par) (2 * j' + par) (cs cq i' j') ≤ εc) :
    |V3Zhu.C3 (2 * i + par) (2 * j + par) - cs cq i j| ≤ εc := by
  rcases le_total i j with hij | hij
  · exact entry3 par i j hp hi hj _ _ (h i hi j hj hij)
  · have hc : cs cq i j = cs cq j i := by unfold cs; rw [min_comm, max_comm]
    rw [V3Zhu.C3_symm, hc]
    exact entry3 par j i hp hj hi _ _ (h j hj i hi hij)

end V3Fin
