import Mathlib
import WeilTailB
import Zeta23.GammaFacts.StirlingVert

/-! # Zhu's reduction `Q_N ≥ R_N` at `L = 1/2`, split into proved steps and named inputs

Frequency form of the Weil functional on `f = Σ xᵢ T_{2i+par}`:
`QF(x) = σ·2(Σ xᵢ pᵢ)² + (1/π)∫₀^∞ Ψ_L(t) F(t)² dt`, `F = Σ xᵢ T̂_{2i+par}`.

Proved here:
* `prime_coeff_L05`: `2Λ(2)/√2 = √2 log 2`, the coefficient of the single cosine term in `WeilTailB.Psi` (the
  only prime power `n` with `log n < 2L = 1` is `n = 2`; the prime sum itself is `WeilPlanch.prime_sum_L05`).
* `envelope`: Zhu's Lemma 3.1 at `T# = 30`: `Ψ_L(t) ≥ β*` for all `t ≥ 30`, from the vendored Stirling bound
  `|Re ψ(a+it) − log|t|| ≤ 5/t²` (`Zeta23.StirlingVert.re_digamma_stirling'`).
* `QF_ge_R`: Zhu's Thm 1.1 reduction `R_N(x) ≤ QF_N(x)` for every `N` and `x`, given `ModePlancherel`.

Named input: `ModePlancherel` (orthonormality and integrability of the mode transforms on `(0,∞)`, functional
analysis), proved in `WeilPlanch` (`modePlancherel_of`).
-/

namespace WeilZhuRed

open Finset Real WeilTail WeilTailB MeasureTheory

/-! ## The prime part at L = 1/2 -/

theorem prime_coeff_L05 : 2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 = Real.sqrt 2 * Real.log 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := by positivity
  rw [div_eq_iff hp.ne']
  have := Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [Nat.cast_ofNat]
  nlinarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]

/-! ## Envelope (Zhu, Lemma 3.1) at T# = 30 -/

theorem envelope {t : ℝ} (ht : 30 ≤ t) : βs ≤ Psi t := by
  have h := Zeta23.StirlingVert.re_digamma_stirling' (a := 1 / 4) (by norm_num) (by norm_num)
    (t := t / 2) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hz : ((1 / 4 : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) = 1 / 4 + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hz, abs_of_nonneg (by linarith : (0:ℝ) ≤ t / 2), abs_le] at h
  have hpos : 0 < t / 2 := by linarith
  have hsq : 5 / (t / 2) ^ 2 ≤ 1 / 30 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hπ := Real.pi_gt_three
  have hlog : Real.log (30 / (2 * π)) ≤ Real.log (t / 2) - Real.log π := by
    rw [← Real.log_div hpos.ne' (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hc := Real.cos_le_one (t * Real.log 2)
  have hk : 0 ≤ Real.sqrt 2 * Real.log 2 := mul_nonneg (Real.sqrt_nonneg 2) (Real.log_nonneg (by norm_num))
  unfold Psi βs
  nlinarith [h.1]

/-! ## Frequency form and the reduction -/

noncomputable def G (par i j : ℕ) (t : ℝ) : ℝ := That (2 * i + par) t * That (2 * j + par) t

noncomputable def Fx (par N : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℝ := ∑ i ∈ range N, x i * That (2 * i + par) t

/-- Frequency form of the Weil functional on the span of the first `N` sector modes. -/
noncomputable def QF (par : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  σ * 2 * (∑ i ∈ range N, x i * pole (2 * i + par)) ^ 2 + (1 / π) * ∫ t in Set.Ioi 0, Psi t * Fx par N x t ^ 2

/-- **Named input (functional analysis)**: Plancherel orthonormality of the sector modes,
`(1/π)∫₀^∞ T̂ₙT̂ₘ = δₙₘ` (Legendre orthonormality on `[−L, L]` + Plancherel), and integrability on `(0,∞)`
of `T̂ₙT̂ₘ` and `Ψ_L T̂ₙT̂ₘ`. -/
structure ModePlancherel (par : ℕ) : Prop where
  orth : ∀ i j, (1 / π) * ∫ t in Set.Ioi 0, G par i j t = if i = j then 1 else 0
  int1 : ∀ i j, IntegrableOn (G par i j) (Set.Ioi 0)
  int2 : ∀ i j, IntegrableOn (fun t => Psi t * G par i j t) (Set.Ioi 0)

lemma Fsq (par N : ℕ) (x : ℕ → ℝ) (h : ℝ → ℝ) (t : ℝ) :
    h t * Fx par N x t ^ 2 = ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * (h t * G par i j t) := by
  unfold Fx G; rw [sq, sum_mul_sum, mul_sum]
  refine sum_congr rfl (fun i _ => ?_); rw [mul_sum]
  refine sum_congr rfl (fun j _ => ?_); ring

lemma expand_int (par N : ℕ) (x : ℕ → ℝ) (h : ℝ → ℝ) (A : Set ℝ)
    (hi : ∀ i j, IntegrableOn (fun t => h t * G par i j t) A) :
    IntegrableOn (fun t => h t * Fx par N x t ^ 2) A ∧
    ∫ t in A, h t * Fx par N x t ^ 2 = ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * ∫ t in A, h t * G par i j t := by
  have e : (fun t => h t * Fx par N x t ^ 2) = fun t => ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * (h t * G par i j t) :=
    funext (Fsq par N x h)
  have hI : ∀ i ∈ range N, Integrable (fun t => ∑ j ∈ range N, x i * x j * (h t * G par i j t)) (volume.restrict A) :=
    fun i _ => integrable_finsetSum _ (fun j _ => (hi i j).const_mul _)
  refine ⟨?_, ?_⟩
  · rw [e]; exact integrable_finsetSum _ hI
  · rw [e, integral_finsetSum _ hI]
    refine sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => (hi i j).const_mul _)]
    refine sum_congr rfl (fun j _ => ?_)
    exact integral_const_mul _ _

lemma qf_Rm (par : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    qf (Rm par σ wψ βs) x (range N) (range N) = βs * ∑ i ∈ range N, x i ^ 2
      + σ * 2 * (∑ i ∈ range N, x i * pole (2 * i + par)) ^ 2
      + ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * Cm wψ (2 * i + par) (2 * j + par) := by
  unfold qf Rm
  have e1 : ∀ i ∈ range N, ∑ j ∈ range N, x i * (if i = j then βs else 0) * x j = βs * x i ^ 2 := by
    intro i hi
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [ite_eq_right (Ne.symm hj)]; ring) (fun h => absurd hi h)]
    rw [ite_eq_left rfl]; ring
  have e2 : (∑ i ∈ range N, x i * pole (2 * i + par)) ^ 2
      = ∑ i ∈ range N, ∑ j ∈ range N, (x i * pole (2 * i + par)) * (x j * pole (2 * j + par)) := by
    rw [sq, sum_mul_sum]
  rw [e2, mul_sum, mul_sum]
  simp only [mul_sum]
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun i hi => ?_)
  rw [← e1 i hi, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun j _ => ?_)
  ring

/-- **Zhu's reduction (Thm 1.1) at L = 1/2, T# = 30**: `R_N(x) ≤ QF_N(x)` for every truncation and every `x`,
given only `ModePlancherel`. The envelope (Lemma 3.1) is proved above. -/
theorem QF_ge_R (par : ℕ) (σ : ℝ) (P : ModePlancherel par) (N : ℕ) (x : ℕ → ℝ) :
    qf (Rm par σ wψ βs) x (range N) (range N) ≤ QF par σ N x := by
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
  -- envelope on (30, ∞)
  have henv : ∫ t in Set.Ioi 30, βs * ((fun _ => (1:ℝ)) t * Fx par N x t ^ 2) ≤ ∫ t in Set.Ioi 30, Psi t * Fx par N x t ^ 2 := by
    refine setIntegral_mono_on (h1b.1.const_mul βs) hPb.1 measurableSet_Ioi (fun t ht => ?_)
    have := envelope (le_of_lt (Set.mem_Ioi.mp ht))
    have := sq_nonneg (Fx par N x t)
    simp only [one_mul]; nlinarith
  rw [integral_const_mul] at henv
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
  rw [qf_Rm]
  unfold QF
  rw [splitP]
  have key : π * (βs * ∑ i ∈ range N, x i ^ 2
      + ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * Cm wψ (2 * i + par) (2 * j + par))
      ≤ (∫ t in Set.Ioc 0 30, Psi t * Fx par N x t ^ 2) + ∫ t in Set.Ioi 30, Psi t * Fx par N x t ^ 2 := by
    rw [mul_add, ← hC, hwsplit]
    have e : π * (βs * ∑ i ∈ range N, x i ^ 2)
        = βs * (∫ t in Set.Ioc 0 30, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2)
          + βs * ∫ t in Set.Ioi 30, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 := by
      rw [show π * (βs * ∑ i ∈ range N, x i ^ 2) = βs * (π * ∑ i ∈ range N, x i ^ 2) by ring, ← hpl, split1, mul_add]
    linarith
  have : βs * ∑ i ∈ range N, x i ^ 2
      + ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * Cm wψ (2 * i + par) (2 * j + par)
      ≤ (1 / π) * ((∫ t in Set.Ioc 0 30, Psi t * Fx par N x t ^ 2) + ∫ t in Set.Ioi 30, Psi t * Fx par N x t ^ 2) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hπ]; linarith
  linarith

/-- Directly on the frequency form: positivity of `QF` needs only `ModePlancherel` and the arb head. -/
theorem QF_pos_of (par : ℕ) (σ m : ℝ) (hm : 0 < m) (P : ModePlancherel par) (N : ℕ)
    (hR : ∀ x : ℕ → ℝ, m * ∑ i ∈ range N, x i ^ 2 ≤ qf (Rm par σ wψ βs) x (range N) (range N))
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < QF par σ N x := by
  obtain ⟨i, hi, hxi⟩ := hx
  have hs : 0 < ∑ i ∈ range N, x i ^ 2 := lt_of_lt_of_le (by positivity) (sq_le_sum (x := x) hi)
  have := hR x; have := QF_ge_R par σ P N x
  nlinarith [mul_pos hm hs]

theorem QF_even_pos (P : ModePlancherel 0) (H : EvenHead) (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ)
    (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < QF 0 1 N x :=
  QF_pos_of 0 1 _ (by norm_num) P N (even_margin H N hN) x hx

theorem QF_odd_pos (P : ModePlancherel 1) (H : OddHead) (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ)
    (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < QF 1 (-1) N x :=
  QF_pos_of 1 (-1) _ (by norm_num) P N (odd_margin H N hN) x hx

end WeilZhuRed
