import Mathlib
import GsFourier

/-! # The tail of the frequency form above `T# = 30`

* `QF_eq`: `QF = R(x) + (1/π)∫_{30}^∞ (Ψ − β*) F²` (Zhu's reduction with the tail kept);
* `psi_upper`: `Ψ(t) − β* ≤ 202/100 − 1 + t/30` for `t ≥ 30` (vendored Stirling);
* `tail_bound`: the tail of a probe whose transform decays like `t⁻³` after six integrations by parts. -/

namespace GsTail

open Real Finset MeasureTheory WeilTail WeilZhuRed WeilTailB

theorem QF_eq (par : ℕ) (σ : ℝ) (P : ModePlancherel par) (N : ℕ) (x : ℕ → ℝ) :
    IntegrableOn (fun t => (Psi t - βs) * Fx par N x t ^ 2) (Set.Ioi 30) ∧
    QF par σ N x = qf (Rm par σ wψ βs) x (range N) (range N)
      + (1 / π) * ∫ t in Set.Ioi 30, (Psi t - βs) * Fx par N x t ^ 2 := by
  have hIoc : ∀ i j, IntegrableOn (G par i j) (Set.Ioc 0 30) := fun i j => (P.int1 i j).mono_set Set.Ioc_subset_Ioi_self
  have hIoi : ∀ i j, IntegrableOn (G par i j) (Set.Ioi 30) :=
    fun i j => (P.int1 i j).mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have one_G : ∀ (A : Set ℝ), (∀ i j, IntegrableOn (G par i j) A) → ∀ i j, IntegrableOn (fun t => (fun _ => (1:ℝ)) t * G par i j t) A :=
    fun A h i j => by simpa using h i j
  -- Ψ on the pieces
  have hP0 := expand_int par N x Psi (Set.Ioi 0) P.int2
  have hPa := expand_int par N x Psi (Set.Ioc 0 30) (fun i j => (P.int2 i j).mono_set Set.Ioc_subset_Ioi_self)
  have hPb := expand_int par N x Psi (Set.Ioi 30) (fun i j => (P.int2 i j).mono_set (Set.Ioi_subset_Ioi (by norm_num)))
  have h10 := expand_int par N x (fun _ => 1) (Set.Ioi 0) (one_G _ P.int1)
  have h1a := expand_int par N x (fun _ => 1) (Set.Ioc 0 30) (one_G _ hIoc)
  have h1b := expand_int par N x (fun _ => 1) (Set.Ioi 30) (one_G _ hIoi)
  have hwa := expand_int par N x wψ (Set.Ioc 0 30) (fun i j => by
    have e : (fun t => wψ t * G par i j t) = fun t => Psi t * G par i j t - βs * G par i j t := by
      funext t; unfold wψ; ring
    rw [e]; exact ((P.int2 i j).mono_set Set.Ioc_subset_Ioi_self).sub ((hIoc i j).const_mul βs))
  have hdisj : Disjoint (Set.Ioc (0:ℝ) 30) (Set.Ioi 30) := by
    rw [Set.disjoint_left]; intro a ha hb; simp only [Set.mem_Ioc, Set.mem_Ioi] at ha hb; linarith
  have hU : Set.Ioc (0:ℝ) 30 ∪ Set.Ioi 30 = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  have splitP : ∫ t in Set.Ioi 0, Psi t * Fx par N x t ^ 2
      = (∫ t in Set.Ioc 0 30, Psi t * Fx par N x t ^ 2) + ∫ t in Set.Ioi 30, Psi t * Fx par N x t ^ 2 := by
    rw [← hU, setIntegral_union hdisj measurableSet_Ioi hPa.1 hPb.1]
  have split1 : ∫ t in Set.Ioi 0, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2
      = (∫ t in Set.Ioc 0 30, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2) + ∫ t in Set.Ioi 30, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 := by
    rw [← hU, setIntegral_union hdisj measurableSet_Ioi h1a.1 h1b.1]
  -- Plancherel: ∫₀^∞ F² = π Σ x²
  have hπ : 0 < π := Real.pi_pos
  have hpl : ∫ t in Set.Ioi 0, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 = π * ∑ i ∈ range N, x i ^ 2 := by
    rw [h10.2]
    have : ∀ i j, ∫ t in Set.Ioi 0, (fun _ => (1:ℝ)) t * G par i j t = π * (if i = j then 1 else 0) := by
      intro i j; rw [← P.orth i j]; simp only [one_mul]; field_simp
    simp only [this]
    rw [mul_sum]; refine sum_congr rfl (fun i hi => ?_)
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [ite_eq_right (Ne.symm hj)]; ring) (fun h => absurd hi h)]
    rw [ite_eq_left rfl]; ring
  -- the [0,30] piece is π Σ xᵢxⱼ Cmᵢⱼ
  have hC : ∫ t in Set.Ioc 0 30, wψ t * Fx par N x t ^ 2
      = π * ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * Cm wψ (2 * i + par) (2 * j + par) := by
    rw [hwa.2, mul_sum]; refine sum_congr rfl (fun i _ => ?_); rw [mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    unfold Cm G
    rw [intervalIntegral.integral_of_le (by norm_num)]
    have : ∫ t in Set.Ioc 0 30, wψ t * That (2 * i + par) t * That (2 * j + par) t
        = ∫ t in Set.Ioc 0 30, wψ t * (That (2 * i + par) t * That (2 * j + par) t) := by
      congr 1; funext t; ring
    rw [this]; field_simp
  have hwsplit : ∫ t in Set.Ioc 0 30, wψ t * Fx par N x t ^ 2
      = (∫ t in Set.Ioc 0 30, Psi t * Fx par N x t ^ 2) - βs * ∫ t in Set.Ioc 0 30, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 := by
    rw [← integral_const_mul, ← integral_sub hPa.1 (h1a.1.const_mul βs)]
    congr 1; funext t; unfold wψ; ring
  have hPb' : IntegrableOn (fun t => (Psi t - βs) * Fx par N x t ^ 2) (Set.Ioi 30) := by
    have e : (fun t => (Psi t - βs) * Fx par N x t ^ 2)
        = fun t => Psi t * Fx par N x t ^ 2 - βs * ((fun _ => (1:ℝ)) t * Fx par N x t ^ 2) := by
      funext t; ring
    rw [e]; exact hPb.1.sub (h1b.1.const_mul βs)
  have hb : ∫ t in Set.Ioi 30, Psi t * Fx par N x t ^ 2
      = (∫ t in Set.Ioi 30, (Psi t - βs) * Fx par N x t ^ 2) + βs * ∫ t in Set.Ioi 30, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 := by
    rw [← integral_const_mul, ← integral_add hPb' (h1b.1.const_mul βs)]
    congr 1; funext t; ring
  refine ⟨hPb', ?_⟩
  rw [qf_Rm]
  unfold QF
  rw [splitP, hb]
  have e : π * (βs * ∑ i ∈ range N, x i ^ 2)
      = βs * (∫ t in Set.Ioc 0 30, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2)
        + βs * ∫ t in Set.Ioi 30, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 := by
    rw [show π * (βs * ∑ i ∈ range N, x i ^ 2) = βs * (π * ∑ i ∈ range N, x i ^ 2) by ring, ← hpl, split1, mul_add]
  have hC' := hC
  rw [hwsplit] at hC'
  have k : (∫ t in Set.Ioc 0 30, Psi t * Fx par N x t ^ 2) + βs * ∫ t in Set.Ioi 30, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2
      = π * (βs * ∑ i ∈ range N, x i ^ 2
        + ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * Cm wψ (2 * i + par) (2 * j + par)) := by
    rw [mul_add]; linarith
  rw [show ∀ a b c : ℝ, (1/π) * (a + (b + c)) = (1/π) * (a + c) + (1/π) * b from fun a b c => by ring, k]
  field_simp; ring

theorem psi_upper {t : ℝ} (ht : 30 ≤ t) : Psi t - βs ≤ 202 / 100 - 1 + t / 30 := by
  have h := Zeta23.StirlingVert.re_digamma_stirling' (a := 1 / 4) (by norm_num) (by norm_num)
    (t := t / 2) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hz : ((1 / 4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) = 1 / 4 + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hz, abs_of_nonneg (by linarith : (0:ℝ) ≤ t / 2), abs_le] at h
  have hpos : 0 < t / 2 := by linarith
  have hsq : 5 / (t / 2) ^ 2 ≤ 1 / 45 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hπ := Real.pi_pos
  have hlog : Real.log (t / 2) - Real.log π - Real.log (30 / (2 * π)) = Real.log (t / 30) := by
    rw [Real.log_div (by linarith) (by norm_num), Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne', Real.log_div (by linarith) (by norm_num)]
    ring
  have hl := Real.log_le_sub_one_of_pos (show 0 < t / 30 by linarith)
  have hc := Real.neg_one_le_cos (t * Real.log 2)
  have hl2 := Real.log_two_lt_d9
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs := sqrt2_le
  have hs0 := Real.sqrt_nonneg 2
  have hk : Real.sqrt 2 * Real.log 2 ≤ 1.4143 * 0.6931471808 := by
    apply mul_le_mul hs hl2.le hl0 (by norm_num)
  have hcos : -(Real.sqrt 2 * Real.log 2 * Real.cos (t * Real.log 2)) ≤ Real.sqrt 2 * Real.log 2 := by
    have := mul_nonneg hs0 hl0
    nlinarith
  unfold Psi βs
  nlinarith [h.2]

/-- `(a+b+c)² ≤ (3/2)a² + 6b² + 6c²` -/
lemma cs3 (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 / 2 * a ^ 2 + 6 * b ^ 2 + 6 * c ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b - 2 * c), sq_nonneg (b - c)]

lemma rpow_nat_neg {t : ℝ} (ht : 0 < t) (k : ℕ) : t ^ (-(k:ℝ)) = 1 / t ^ k := by
  rw [Real.rpow_neg ht.le, Real.rpow_natCast, one_div]

/-- `∫_{30}^∞ t^{-k} = 30^{1-k}/(k-1)` -/
lemma int_pow (k : ℕ) (hk : 2 ≤ k) :
    IntegrableOn (fun t : ℝ => t ^ (-(k:ℝ))) (Set.Ioi 30) ∧
    ∫ t in Set.Ioi (30:ℝ), t ^ (-(k:ℝ)) = 1 / ((k - 1) * 30 ^ (k - 1)) := by
  have h2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk' : -(k:ℝ) < -1 := by linarith
  refine ⟨integrableOn_Ioi_rpow_of_lt hk' (by norm_num), ?_⟩
  rw [integral_Ioi_rpow_of_lt hk' (by norm_num)]
  have e : -(k:ℝ) + 1 = -((k - 1 : ℕ) : ℝ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring
  rw [e, rpow_nat_neg (by norm_num)]
  push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
  have : (0:ℝ) < k - 1 := by linarith
  field_simp

/-- `I_k = (κ−1)·30^{1−k}/(k−1) + 30^{2−k}/(30(k−2))` -/
noncomputable def Ik (k : ℕ) : ℝ := (202 / 100 - 1) * (1 / ((k - 1) * 30 ^ (k - 1))) + 1 / 30 * (1 / ((k - 2) * 30 ^ (k - 2)))

lemma int_e (k : ℕ) (hk : 3 ≤ k) :
    IntegrableOn (fun t : ℝ => (202 / 100 - 1 + t / 30) * t ^ (-(k:ℝ))) (Set.Ioi 30) ∧
    ∫ t in Set.Ioi (30:ℝ), (202 / 100 - 1 + t / 30) * t ^ (-(k:ℝ)) = Ik k := by
  obtain ⟨i1, e1⟩ := int_pow k (by omega)
  obtain ⟨i2, e2⟩ := int_pow (k - 1) (by omega)
  have eq : (fun t : ℝ => (202 / 100 - 1 + t / 30) * t ^ (-(k:ℝ)))
      =ᵐ[volume.restrict (Set.Ioi 30)] fun t => (202 / 100 - 1) * t ^ (-(k:ℝ)) + 1 / 30 * t ^ (-((k - 1 : ℕ):ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := by have := Set.mem_Ioi.mp ht; linarith
    rw [rpow_nat_neg ht0, rpow_nat_neg ht0]
    have : t ^ k = t * t ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]; field_simp
  have iS := (i1.const_mul (202 / 100 - 1)).add (i2.const_mul (1 / 30))
  refine ⟨iS.congr eq.symm, ?_⟩
  rw [integral_congr_ae eq, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    e1, e2]
  unfold Ik
  have : (k - 1 - 1 : ℕ) = k - 2 := by omega
  rw [this]
  push_cast [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k)]
  ring

/-- **Tail bound.** If `|F(t)| ≤ A₂/t³ + A₃/t⁴ + g(t)/t⁶` on `t > 0` with `∫₀^∞ g² ≤ π·n₆`, then
`(1/π)∫_{30}^∞ (Ψ−β*)F² ≤ (1/π)(3/2·A₂²I₆ + 6A₃²I₈) + 6κ·30⁻¹²·n₆`. -/
theorem tail_bound (N : ℕ) (x : ℕ → ℝ) (A2 A3 n6 : ℝ) (g : ℝ → ℝ)
    (hg : IntegrableOn (fun t => g t ^ 2) (Set.Ioi 0)) (hgn : ∫ t in Set.Ioi 0, g t ^ 2 ≤ π * n6)
    (hF : ∀ t, 0 < t → |Fx 0 N x t| ≤ A2 / t ^ 3 + A3 / t ^ 4 + |g t| / t ^ 6) :
    (1 / π) * ∫ t in Set.Ioi 30, (Psi t - βs) * Fx 0 N x t ^ 2
      ≤ (1 / π) * (3 / 2 * A2 ^ 2 * Ik 6 + 6 * A3 ^ 2 * Ik 8) + 6 * (202 / 100) / 30 ^ 12 * n6 := by
  have P := WeilPlanch.modePlancherel_of WeilModes.modeDecay 0 (WeilFourier.modeOrth (by norm_num))
  obtain ⟨hI, -⟩ := QF_eq 0 1 P N x
  obtain ⟨i6, e6⟩ := int_e 6 (by norm_num)
  obtain ⟨i8, e8⟩ := int_e 8 (by norm_num)
  have hg30 : IntegrableOn (fun t => g t ^ 2) (Set.Ioi 30) := hg.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have iR := ((i6.const_mul (3 / 2 * A2 ^ 2)).add (i8.const_mul (6 * A3 ^ 2))).add
    (hg30.const_mul (6 * (202 / 100) / 30 ^ 12))
  have hπ := Real.pi_pos
  have hmono : ∫ t in Set.Ioi 30, (Psi t - βs) * Fx 0 N x t ^ 2
      ≤ ∫ t in Set.Ioi 30, (3 / 2 * A2 ^ 2 * ((202 / 100 - 1 + t / 30) * t ^ (-((6:ℕ):ℝ)))
          + 6 * A3 ^ 2 * ((202 / 100 - 1 + t / 30) * t ^ (-((8:ℕ):ℝ))))
          + 6 * (202 / 100) / 30 ^ 12 * g t ^ 2 := by
    refine setIntegral_mono_on hI iR measurableSet_Ioi (fun t ht => ?_)
    have ht30 : 30 < t := ht
    have ht0 : 0 < t := by linarith
    have hpe := WeilZhuRed.envelope ht30.le
    have hpu := psi_upper ht30.le
    have hFb := hF t ht0
    set a := A2 / t ^ 3
    set b := A3 / t ^ 4
    set c := |g t| / t ^ 6
    have hF2 : Fx 0 N x t ^ 2 ≤ 3 / 2 * a ^ 2 + 6 * b ^ 2 + 6 * c ^ 2 := by
      refine le_trans ?_ (cs3 a b c)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hFb 2
    rw [rpow_nat_neg ht0, rpow_nat_neg ht0]
    have ea : a ^ 2 = A2 ^ 2 * (1 / t ^ 6) := by simp only [a]; field_simp
    have eb : b ^ 2 = A3 ^ 2 * (1 / t ^ 8) := by simp only [b]; field_simp
    have ec : c ^ 2 = g t ^ 2 * (1 / t ^ 12) := by simp only [c]; rw [div_pow, sq_abs]; field_simp
    have hc12 : (202 / 100 - 1 + t / 30) * (1 / t ^ 12) ≤ 202 / 100 / 30 ^ 12 := by
      have h1 : 202 / 100 - 1 + t / 30 ≤ 202 / 100 * (t / 30) := by nlinarith
      have h2 : t / 30 * (1 / t ^ 12) ≤ 1 / 30 ^ 12 := by
        rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (30:ℝ) ^ 11 ≤ t ^ 11 := pow_le_pow_left₀ (by norm_num) ht30.le 11
        nlinarith [pow_pos ht0 11]
      calc _ ≤ 202 / 100 * (t / 30) * (1 / t ^ 12) := by gcongr
        _ = 202 / 100 * (t / 30 * (1 / t ^ 12)) := by ring
        _ ≤ 202 / 100 * (1 / 30 ^ 12) := by gcongr
        _ = _ := by ring
    have hw0 : 0 ≤ Psi t - βs := by linarith
    have hgs : 0 ≤ g t ^ 2 := sq_nonneg _
    calc (Psi t - βs) * Fx 0 N x t ^ 2 ≤ (202 / 100 - 1 + t / 30) * (3 / 2 * a ^ 2 + 6 * b ^ 2 + 6 * c ^ 2) := by
          apply mul_le_mul hpu hF2 (sq_nonneg _) (by linarith)
      _ = 3 / 2 * A2 ^ 2 * ((202 / 100 - 1 + t / 30) * (1 / t ^ 6)) + 6 * A3 ^ 2 * ((202 / 100 - 1 + t / 30) * (1 / t ^ 8))
          + 6 * g t ^ 2 * ((202 / 100 - 1 + t / 30) * (1 / t ^ 12)) := by rw [ea, eb, ec]; ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hc12 (by positivity : (0:ℝ) ≤ 6 * g t ^ 2)
          nlinarith
  have hR : ∫ t in Set.Ioi 30, (3 / 2 * A2 ^ 2 * ((202 / 100 - 1 + t / 30) * t ^ (-((6:ℕ):ℝ)))
          + 6 * A3 ^ 2 * ((202 / 100 - 1 + t / 30) * t ^ (-((8:ℕ):ℝ))))
          + 6 * (202 / 100) / 30 ^ 12 * g t ^ 2
      = 3 / 2 * A2 ^ 2 * Ik 6 + 6 * A3 ^ 2 * Ik 8 + 6 * (202 / 100) / 30 ^ 12 * ∫ t in Set.Ioi 30, g t ^ 2 := by
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul, e6, e8]
    all_goals first | exact (i6.const_mul _) | exact (i8.const_mul _) | exact (hg30.const_mul _) | exact ((i6.const_mul _).add (i8.const_mul _))
  rw [hR] at hmono
  have hg' : ∫ t in Set.Ioi 30, g t ^ 2 ≤ π * n6 := by
    refine le_trans (setIntegral_mono_set hg (Filter.Eventually.of_forall (fun t => sq_nonneg (g t)))
      (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi (by norm_num)))) hgn
  have : (1 / π) * ∫ t in Set.Ioi 30, (Psi t - βs) * Fx 0 N x t ^ 2
      ≤ (1 / π) * ((3 / 2 * A2 ^ 2 * Ik 6 + 6 * A3 ^ 2 * Ik 8) + 6 * (202 / 100) / 30 ^ 12 * (π * n6)) := by
    gcongr
    refine hmono.trans ?_
    gcongr
  refine this.trans (le_of_eq ?_)
  field_simp

end GsTail
