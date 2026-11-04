import Mathlib
import V3Scale

/-! # Zhu's reduction at support `log 3 / 2`, and the sector theorem on Connes–Consani's subspace

In the rescaled picture of `V3Scale` the frequency weight is `Ψ̃(t) = Ψ(t/λ)`, `λ = log 3`, and the modes are the
`L = 1/2` transforms `T̂ₙ`. Since `Ψ ≥ β*` on `[30, ∞)` (`WeilZhuRed.envelope`), `Ψ̃ ≥ β*` on `[30λ, ∞)`, and splitting
there gives Zhu's reduced form

  `QF3_par(x) ≥ β*‖x‖² + Σᵢⱼ xᵢxⱼ C3(2i+par, 2j+par)`,  `C3 n m = (1/π)∫₀^{30λ} (Ψ̃ − β*) T̂ₙT̂ₘ`  (`QF3_ge`).

On the subspace `V'` the even coefficients satisfy two linear constraints (`x₀ = 0` and `Σ xᵢ p̃_{2i} = 0`, with
`p̃ₙ = 2√(νₙ/2)·iₙ(λ/4)` the rescaled pole vector), so the even reduced matrix may be augmented by
`μ_p p̃p̃ᵀ + μ₀ e₀e₀ᵀ` without changing the form there. `sector_margin3` is the head/tail theorem for that augmented
matrix: a head certificate on 28 modes gives `m‖x‖² ≤ xᵀR x` for every truncation, with the tail and coupling
controlled by `|T̂ₙ| ≤ b3 n = (1 + (2n+1)/4)(33/4)ⁿ/n!` on `[0, 30λ]`. -/

namespace V3Zhu

open Real Finset MeasureTheory Set WeilTail WeilTailB WeilZhuRed V3Scale
open scoped Nat

/-! ## Envelope and the reduction -/

theorem envelope3 {t : ℝ} (ht : 30 * lam ≤ t) : βs ≤ Psi3 t :=
  envelope (by rw [le_div_iff₀ lam_pos]; linarith)

/-- `C3 n m = (1/π)∫₀^{30λ} (Ψ̃(t) − β*) T̂ₙ(t) T̂ₘ(t) dt`. -/
noncomputable def C3 (n m : ℕ) : ℝ := (1 / π) * ∫ t in (0:ℝ)..(30 * lam), (Psi3 t - βs) * That n t * That m t

lemma lam30_pos : 0 < 30 * lam := by have := lam_pos; positivity

/-- **Zhu's reduction at support `log 3 / 2`.** -/
theorem QF3_ge (par : ℕ) (P : ModePlancherel par) (N : ℕ) (x : ℕ → ℝ) :
    βs * ∑ i ∈ range N, x i ^ 2 + ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * C3 (2 * i + par) (2 * j + par)
      ≤ QF3 par N x := by
  set T := 30 * lam with hT
  have hT0 : 0 < T := lam30_pos
  have hIoc : ∀ i j, IntegrableOn (G par i j) (Set.Ioc 0 T) := fun i j => (P.int1 i j).mono_set Set.Ioc_subset_Ioi_self
  have hIoi : ∀ i j, IntegrableOn (G par i j) (Set.Ioi T) :=
    fun i j => (P.int1 i j).mono_set (Set.Ioi_subset_Ioi hT0.le)
  have one_G : ∀ (A : Set ℝ), (∀ i j, IntegrableOn (G par i j) A) →
      ∀ i j, IntegrableOn (fun t => (fun _ => (1:ℝ)) t * G par i j t) A :=
    fun A h i j => by simpa using h i j
  have hW := int_Psi3 par
  have hPa := expand_int par N x Psi3 (Set.Ioc 0 T) (fun i j => (hW i j).mono_set Set.Ioc_subset_Ioi_self)
  have hPb := expand_int par N x Psi3 (Set.Ioi T) (fun i j => (hW i j).mono_set (Set.Ioi_subset_Ioi hT0.le))
  have h10 := expand_int par N x (fun _ => 1) (Set.Ioi 0) (one_G _ P.int1)
  have h1a := expand_int par N x (fun _ => 1) (Set.Ioc 0 T) (one_G _ hIoc)
  have h1b := expand_int par N x (fun _ => 1) (Set.Ioi T) (one_G _ hIoi)
  have hwa := expand_int par N x (fun t => Psi3 t - βs) (Set.Ioc 0 T) (fun i j => by
    have e : (fun t => (fun t => Psi3 t - βs) t * G par i j t) = fun t => Psi3 t * G par i j t - βs * G par i j t := by
      funext t; ring
    rw [e]; exact ((hW i j).mono_set Set.Ioc_subset_Ioi_self).sub ((hIoc i j).const_mul βs))
  have hdisj : Disjoint (Set.Ioc (0:ℝ) T) (Set.Ioi T) := by
    rw [Set.disjoint_left]; intro a ha hb; simp only [Set.mem_Ioc, Set.mem_Ioi] at ha hb; linarith
  have hU : Set.Ioc (0:ℝ) T ∪ Set.Ioi T = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi hT0.le
  have splitP : ∫ t in Set.Ioi 0, Psi3 t * Fx par N x t ^ 2
      = (∫ t in Set.Ioc 0 T, Psi3 t * Fx par N x t ^ 2) + ∫ t in Set.Ioi T, Psi3 t * Fx par N x t ^ 2 := by
    rw [← hU, setIntegral_union hdisj measurableSet_Ioi hPa.1 hPb.1]
  have split1 : ∫ t in Set.Ioi 0, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2
      = (∫ t in Set.Ioc 0 T, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2)
        + ∫ t in Set.Ioi T, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 := by
    rw [← hU, setIntegral_union hdisj measurableSet_Ioi h1a.1 h1b.1]
  have henv : ∫ t in Set.Ioi T, βs * ((fun _ => (1:ℝ)) t * Fx par N x t ^ 2)
      ≤ ∫ t in Set.Ioi T, Psi3 t * Fx par N x t ^ 2 := by
    refine setIntegral_mono_on (h1b.1.const_mul βs) hPb.1 measurableSet_Ioi (fun t ht => ?_)
    have := envelope3 (le_of_lt (Set.mem_Ioi.mp ht))
    have := sq_nonneg (Fx par N x t)
    simp only [one_mul]; nlinarith
  rw [integral_const_mul] at henv
  have hπ : 0 < π := Real.pi_pos
  have hpl : ∫ t in Set.Ioi 0, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 = π * ∑ i ∈ range N, x i ^ 2 := by
    rw [h10.2]
    have : ∀ i j, ∫ t in Set.Ioi 0, (fun _ => (1:ℝ)) t * G par i j t = π * (if i = j then 1 else 0) := by
      intro i j; rw [← P.orth i j]; simp only [one_mul]; field_simp
    simp only [this]
    rw [mul_sum]; refine sum_congr rfl (fun i hi => ?_)
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj)]; ring) (fun h => absurd hi h)]
    rw [if_pos rfl]; ring
  have hC : ∫ t in Set.Ioc 0 T, (fun t => Psi3 t - βs) t * Fx par N x t ^ 2
      = π * ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * C3 (2 * i + par) (2 * j + par) := by
    rw [hwa.2, mul_sum]; refine sum_congr rfl (fun i _ => ?_); rw [mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    unfold C3 G
    rw [intervalIntegral.integral_of_le hT0.le]
    have : ∫ t in Set.Ioc 0 T, (Psi3 t - βs) * That (2 * i + par) t * That (2 * j + par) t
        = ∫ t in Set.Ioc 0 T, (fun t => Psi3 t - βs) t * (That (2 * i + par) t * That (2 * j + par) t) := by
      congr 1; funext t; ring
    rw [this]; field_simp
  have hwsplit : ∫ t in Set.Ioc 0 T, (fun t => Psi3 t - βs) t * Fx par N x t ^ 2
      = (∫ t in Set.Ioc 0 T, Psi3 t * Fx par N x t ^ 2)
        - βs * ∫ t in Set.Ioc 0 T, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 := by
    rw [← integral_const_mul, ← integral_sub hPa.1 (h1a.1.const_mul βs)]
    congr 1; funext t; ring
  unfold QF3
  rw [splitP]
  have key : π * (βs * ∑ i ∈ range N, x i ^ 2
      + ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * C3 (2 * i + par) (2 * j + par))
      ≤ (∫ t in Set.Ioc 0 T, Psi3 t * Fx par N x t ^ 2) + ∫ t in Set.Ioi T, Psi3 t * Fx par N x t ^ 2 := by
    rw [mul_add, ← hC, hwsplit]
    have e : π * (βs * ∑ i ∈ range N, x i ^ 2)
        = βs * (∫ t in Set.Ioc 0 T, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2)
          + βs * ∫ t in Set.Ioi T, (fun _ => (1:ℝ)) t * Fx par N x t ^ 2 := by
      rw [show π * (βs * ∑ i ∈ range N, x i ^ 2) = βs * (π * ∑ i ∈ range N, x i ^ 2) by ring, ← hpl, split1, mul_add]
    linarith
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hπ]; linarith

/-! ## Mode, pole and entry bounds on `[0, 30λ]` -/

lemma lam_le : lam ≤ 11 / 10 := lam_lt.le

/-- `b3 n = (1 + (2n+1)/4)(33/4)ⁿ/n!`, since `15λ/2 ≤ 33/4`. -/
noncomputable def b3 (n : ℕ) : ℝ := (1 + (2 * n + 1) / 4) * (33 / 4) ^ n / n !

lemma b3_nonneg (n : ℕ) : 0 ≤ b3 n := by unfold b3; positivity

theorem That_bound3 (n : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 30 * lam) : |That n t| ≤ b3 n := by
  unfold That b3
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hy : (0:ℝ) ≤ (1 / 2) * (n + 1 / 2) := by positivity
  have hs := two_sqrt_le hy
  rw [y_eq] at hs hy
  rw [y_eq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt ((2 * n + 1) / 4))]
  have hj := jP_bound n (by linarith : (0:ℝ) ≤ t / 2)
  have hl := lam_le
  have ht : t / 2 / 2 ≤ 33 / 4 := by nlinarith
  have hp : (t / 2 / 2) ^ n / n ! ≤ (33 / 4 : ℝ) ^ n / n ! :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht n) (by positivity)
  calc 2 * Real.sqrt ((2 * n + 1) / 4) * |jP n (t / 2)| ≤ (1 + (2 * n + 1) / 4) * ((33 / 4 : ℝ) ^ n / n !) :=
        mul_le_mul hs (hj.trans hp) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The rescaled pole vector `p̃ₙ = 2√(νₙ/2)·iₙ(λ/4)` (the value of `∫ T_n(u) e^{−λu/2} du`, `V3Pole`). -/
noncomputable def pole3 (n : ℕ) : ℝ := 2 * Real.sqrt ((1 / 2) * (n + 1 / 2)) * iP n (lam / 4)

theorem pole3_bound (n : ℕ) : |pole3 n| ≤ 2 * b3 n := by
  unfold pole3 b3
  have hy : (0:ℝ) ≤ (1 / 2) * (n + 1 / 2) := by positivity
  have hs := two_sqrt_le hy
  rw [y_eq] at hs hy
  rw [y_eq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt ((2 * n + 1) / 4))]
  have hl := lam_le; have hl0 := lam_pos
  have hi := iP_bound n (by positivity : (0:ℝ) ≤ lam / 4) (by linarith)
  have hz : lam / 4 / 2 ≤ 33 / 4 := by linarith
  have hp : 2 * ((lam / 4 / 2 : ℝ) ^ n / n !) ≤ 2 * ((33 / 4 : ℝ) ^ n / n !) := by
    gcongr
  calc 2 * Real.sqrt ((2 * n + 1) / 4) * |iP n (lam / 4)| ≤ (1 + (2 * n + 1) / 4) * (2 * ((33 / 4 : ℝ) ^ n / n !)) :=
        mul_le_mul hs (hi.trans hp) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem w3_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 30 * lam) : |Psi3 t - βs| ≤ 55 := by
  have := wψ_bound (t := t / lam) (div_nonneg h0 lam_pos.le) (by rw [div_le_iff₀ lam_pos]; linarith)
  unfold wψ at this; unfold Psi3; exact this

theorem C3_bound (n m : ℕ) : |C3 n m| ≤ 605 * b3 n * b3 m := by
  have hl := lam_le; have hl0 := lam_pos
  have hT0 : (0:ℝ) ≤ 30 * lam := by positivity
  have hI : ‖∫ t in (0:ℝ)..(30 * lam), (Psi3 t - βs) * That n t * That m t‖ ≤ (55 * b3 n * b3 m) * |30 * lam - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hT0] at ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have a := w3_bound ht.1.le ht.2
    have bn := That_bound3 n ht.1.le ht.2
    have bm := That_bound3 m ht.1.le ht.2
    exact mul_le_mul (mul_le_mul a bn (abs_nonneg _) (by norm_num)) bm (abs_nonneg _)
      (mul_nonneg (by norm_num) (b3_nonneg n))
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT0] at hI
  unfold C3
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / π)]
  have hπ := Real.pi_gt_three
  have : 1 / π ≤ 1 / 3 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h0 : 0 ≤ 55 * b3 n * b3 m := mul_nonneg (mul_nonneg (by norm_num) (b3_nonneg n)) (b3_nonneg m)
  calc 1 / π * |∫ t in (0:ℝ)..(30 * lam), (Psi3 t - βs) * That n t * That m t|
      ≤ 1 / 3 * (55 * b3 n * b3 m * (30 * lam)) := mul_le_mul this hI (abs_nonneg _) (by norm_num)
    _ ≤ 1 / 3 * (55 * b3 n * b3 m * 33) := by gcongr; linarith
    _ = 605 * b3 n * b3 m := by ring

lemma C3_symm (n m : ℕ) : C3 n m = C3 m n := by
  unfold C3; congr 1; refine intervalIntegral.integral_congr (fun t _ => ?_); ring

/-! ## The (augmented) reduced matrix -/

/-- Sector `par` reduced matrix, augmented by `μp p̃p̃ᵀ + μ0 e₀e₀ᵀ` (both vanish on `V'` in the even sector; the odd
sector uses `μp = μ0 = 0`). -/
noncomputable def R3 (par : ℕ) (μp μ0 : ℝ) (i j : ℕ) : ℝ :=
  (if i = j then βs else 0) + μp * pole3 (2 * i + par) * pole3 (2 * j + par)
    + (if i = 0 ∧ j = 0 then μ0 else 0) + C3 (2 * i + par) (2 * j + par)

theorem R3_symm (par : ℕ) (μp μ0 : ℝ) (i j : ℕ) : R3 par μp μ0 i j = R3 par μp μ0 j i := by
  unfold R3; rw [C3_symm (2 * i + par)]
  have e1 : (if i = j then βs else 0) = (if j = i then βs else 0) := by
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  have e2 : (if i = 0 ∧ j = 0 then μ0 else 0) = (if j = 0 ∧ i = 0 then μ0 else 0) := by
    by_cases h : i = 0 ∧ j = 0
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]
  rw [e1, e2]; ring

theorem R3_entry (par : ℕ) {μp : ℝ} (hμ : 0 ≤ μp) (μ0 : ℝ) (i j : ℕ) :
    |R3 par μp μ0 i j - (if i = j then βs else 0) - (if i = 0 ∧ j = 0 then μ0 else 0)|
      ≤ (605 + 4 * μp) * b3 (2 * i + par) * b3 (2 * j + par) := by
  have hc := C3_bound (2 * i + par) (2 * j + par)
  have hpi := pole3_bound (2 * i + par)
  have hpj := pole3_bound (2 * j + par)
  have bi := b3_nonneg (2 * i + par)
  have bj := b3_nonneg (2 * j + par)
  have hp : |μp * pole3 (2 * i + par) * pole3 (2 * j + par)| ≤ 4 * μp * b3 (2 * i + par) * b3 (2 * j + par) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hμ]
    have := mul_le_mul hpi hpj (abs_nonneg _) (by linarith)
    calc μp * |pole3 (2 * i + par)| * |pole3 (2 * j + par)| = μp * (|pole3 (2 * i + par)| * |pole3 (2 * j + par)|) := by
          ring
      _ ≤ μp * (2 * b3 (2 * i + par) * (2 * b3 (2 * j + par))) := mul_le_mul_of_nonneg_left this hμ
      _ = _ := by ring
  unfold R3
  have : (if i = j then βs else 0) + μp * pole3 (2 * i + par) * pole3 (2 * j + par)
      + (if i = 0 ∧ j = 0 then μ0 else 0) + C3 (2 * i + par) (2 * j + par)
      - (if i = j then βs else 0) - (if i = 0 ∧ j = 0 then μ0 else 0)
      = μp * pole3 (2 * i + par) * pole3 (2 * j + par) + C3 (2 * i + par) (2 * j + par) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  nlinarith

/-- `xᵀ R3 x` for the augmented matrix: `β*‖x‖² + μp (Σ xᵢ p̃ᵢ)² + μ0 x₀² + Σ xᵢxⱼ C3`. -/
theorem qf_R3 (par : ℕ) (μp μ0 : ℝ) (N : ℕ) (hN : 1 ≤ N) (x : ℕ → ℝ) :
    qf (R3 par μp μ0) x (range N) (range N) = βs * ∑ i ∈ range N, x i ^ 2
      + μp * (∑ i ∈ range N, x i * pole3 (2 * i + par)) ^ 2 + μ0 * x 0 ^ 2
      + ∑ i ∈ range N, ∑ j ∈ range N, x i * x j * C3 (2 * i + par) (2 * j + par) := by
  unfold qf R3
  have e1 : ∀ i ∈ range N, ∑ j ∈ range N, x i * (if i = j then βs else 0) * x j = βs * x i ^ 2 := by
    intro i hi
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj)]; ring) (fun h => absurd hi h)]
    rw [if_pos rfl]; ring
  have e2 : (∑ i ∈ range N, x i * pole3 (2 * i + par)) ^ 2
      = ∑ i ∈ range N, ∑ j ∈ range N, (x i * pole3 (2 * i + par)) * (x j * pole3 (2 * j + par)) := by
    rw [sq, sum_mul_sum]
  have h0 : 0 ∈ range N := mem_range.mpr (by omega)
  have e3 : ∑ i ∈ range N, ∑ j ∈ range N, x i * (if i = 0 ∧ j = 0 then μ0 else 0) * x j = μ0 * x 0 ^ 2 := by
    rw [Finset.sum_eq_single 0 (fun i _ hi => sum_eq_zero (fun j _ => by rw [if_neg (fun h => hi h.1)]; ring))
      (fun h => absurd h0 h)]
    rw [Finset.sum_eq_single 0 (fun j _ hj => by rw [if_neg (fun h => hj h.2)]; ring) (fun h => absurd h0 h)]
    rw [if_pos ⟨rfl, rfl⟩]; ring
  have expand : ∀ i j, x i * ((if i = j then βs else 0) + μp * pole3 (2 * i + par) * pole3 (2 * j + par)
      + (if i = 0 ∧ j = 0 then μ0 else 0) + C3 (2 * i + par) (2 * j + par)) * x j
      = x i * (if i = j then βs else 0) * x j + μp * ((x i * pole3 (2 * i + par)) * (x j * pole3 (2 * j + par)))
        + x i * (if i = 0 ∧ j = 0 then μ0 else 0) * x j + x i * x j * C3 (2 * i + par) (2 * j + par) := by
    intro i j; ring
  simp only [expand, sum_add_distrib]
  rw [sum_congr rfl e1, e3, e2, mul_sum]
  simp only [mul_sum]

/-! ## Geometric tail majorants for `b3` -/

lemma b3_step {n : ℕ} (hn : 20 ≤ n) : b3 (n + 2) ≤ b3 n / 2 := by
  have hF : 0 ≤ (33 / 4 : ℝ) ^ n / n ! := by positivity
  have e1 : b3 (n + 2) = (1 + (2 * ((n:ℝ) + 2) + 1) / 4) * (1089 / 16) / (((n:ℝ) + 2) * ((n:ℝ) + 1))
      * ((33 / 4) ^ n / n !) := by
    unfold b3; rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; field_simp; ring
  have e2 : b3 n = (1 + (2 * (n:ℝ) + 1) / 4) * ((33 / 4) ^ n / n !) := by unfold b3; ring
  have hn' : (20:ℝ) ≤ n := by exact_mod_cast hn
  have key : (1 + (2 * ((n:ℝ) + 2) + 1) / 4) * (1089 / 16) / (((n:ℝ) + 2) * ((n:ℝ) + 1))
      ≤ (1 + (2 * (n:ℝ) + 1) / 4) / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have A : 0 < (1 + (2 * (n:ℝ) + 1) / 4) := by positivity
    have B : (1089 / 4 : ℝ) < ((n:ℝ) + 2) * ((n:ℝ) + 1) := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left B A]
  rw [e1, e2]
  calc _ ≤ (1 + (2 * (n:ℝ) + 1) / 4) / 2 * ((33 / 4) ^ n / n !) := mul_le_mul_of_nonneg_right key hF
    _ = _ := by ring

lemma bs3_step (par : ℕ) : ∀ i, 28 ≤ i → b3 (2 * (i + 1) + par) ≤ b3 (2 * i + par) / 2 := by
  intro i hi
  rw [show 2 * (i + 1) + par = (2 * i + par) + 2 by ring]; exact b3_step (by omega)

lemma bsq3_step (par : ℕ) : ∀ i, 28 ≤ i → b3 (2 * (i + 1) + par) ^ 2 ≤ b3 (2 * i + par) ^ 2 / 2 := by
  intro i hi
  have h := bs3_step par i hi
  have h0 := b3_nonneg (2 * (i + 1) + par)
  have h1 := b3_nonneg (2 * i + par)
  nlinarith

lemma tail_sum3 (par N : ℕ) (hN : 28 ≤ N) : ∑ j ∈ Ico 28 N, b3 (2 * j + par) ≤ 2 * b3 (56 + par) := by
  have := geom_sum (fun i => b3 (2 * i + par)) 28 (bs3_step par) N hN
  have := b3_nonneg (2 * N + par)
  linarith

lemma tail_sumsq3 (par N : ℕ) (hN : 28 ≤ N) : ∑ j ∈ Ico 28 N, b3 (2 * j + par) ^ 2 ≤ 2 * b3 (56 + par) ^ 2 := by
  have := geom_sum (fun i => b3 (2 * i + par) ^ 2) 28 (bsq3_step par) N hN
  have := sq_nonneg (b3 (2 * N + par))
  linarith

lemma b3_le_head (n : ℕ) (hn : n ≤ 55) : b3 n ≤ 128383 := by
  have e : b3 n = (1 + (2 * (n:ℝ) + 1) / 4) * ((33 / 4) ^ n / n !) := by unfold b3; ring
  have h1 : (33 / 4 : ℝ) ^ n / n ! ≤ 4427 := by
    refine (Real.pow_div_factorial_le_exp (33 / 4) (by norm_num) n).trans ?_
    have h9 : Real.exp (33 / 4) = Real.exp 1 ^ 8 * Real.exp (1 / 4) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have he := Real.exp_one_lt_d9
    have hq : Real.exp (1 / 4) ≤ 1.3 := by
      have := Real.exp_bound (x := 1 / 4) (by rw [abs_of_pos (by norm_num)]; norm_num) (n := 3) (by norm_num)
      simp [Finset.sum_range_succ, Nat.factorial] at this
      have := (abs_le.mp this).2; norm_num at this ⊢; linarith
    have h8 : Real.exp 1 ^ 8 ≤ (2.7182818286:ℝ) ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 8
    rw [h9]
    calc Real.exp 1 ^ 8 * Real.exp (1 / 4) ≤ (2.7182818286:ℝ) ^ 8 * 1.3 :=
          mul_le_mul h8 hq (Real.exp_pos _).le (by positivity)
      _ ≤ 4427 := by norm_num
  have hn' : (n:ℝ) ≤ 55 := by exact_mod_cast hn
  rw [e]
  have : (1 + (2 * (n:ℝ) + 1) / 4) ≤ 29 := by linarith
  calc _ ≤ 29 * 4427 := mul_le_mul this h1 (by positivity) (by norm_num)
    _ = 128383 := by norm_num

lemma b3_56_le : b3 56 ≤ 1 / 10 ^ 22 := by
  unfold b3; rw [div_le_iff₀ (by positivity)]; norm_num [Nat.factorial]

lemma b3_57_le : b3 57 ≤ 1 / 10 ^ 22 := by
  unfold b3; rw [div_le_iff₀ (by positivity)]; norm_num [Nat.factorial]

/-! ## The sector theorem -/

/-- **Sector theorem at support `log 3 / 2`.** A head certificate `(Mh, Dh, δ, ρ)` for the augmented reduced matrix
on the first 28 modes gives `m‖x‖² ≤ xᵀR3 x` for every `N ≥ 28`. Here `K = 605 + 4μp` bounds the entries off the
diagonal through `|T̂ₙ| ≤ b3 n`, and `B0 ≥ b3(56+par)` the tail. -/
theorem sector_margin3 (par : ℕ) (hpar : par ≤ 1) {μp : ℝ} (hμ : 0 ≤ μp) (μ0 : ℝ)
    (Mh : ℕ → ℕ → ℝ) (Dh : ℕ → ℝ) (δ ρ m B0 K : ℝ) (hK : K = 605 + 4 * μp) (hD : ∀ k, 0 ≤ Dh k) (hρ0 : 0 ≤ ρ)
    (hhead : ∀ i < 28, ∀ j < 28, |R3 par μp μ0 i j - certMat 28 Mh Dh δ i j| ≤ ρ)
    (hB0 : b3 (56 + par) ≤ B0)
    (hm1 : m ≤ δ - ((28:ℕ):ℝ) * ρ) (hm2 : m ≤ 0.37 - K * B0 ^ 2 - K * B0 * (2 * B0))
    (hb : K ^ 2 * (28 * 128383 ^ 2) * (2 * B0 ^ 2)
      ≤ (δ - ((28:ℕ):ℝ) * ρ - m) * (0.37 - K * B0 ^ 2 - K * B0 * (2 * B0) - m))
    (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) :
    m * ∑ i ∈ range N, x i ^ 2 ≤ qf (R3 par μp μ0) x (range N) (range N) := by
  have hE := R3_entry par hμ μ0
  rw [← hK] at hE
  set R := R3 par μp μ0
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  have B0nn : 0 ≤ B0 := (b3_nonneg _).trans hB0
  have hbt : ∀ i, 28 ≤ i → b3 (2 * i + par) ≤ B0 := by
    intro i hi
    have := tail_mono (fun i => b3 (2 * i + par)) 28 (fun i => b3_nonneg _) (bs3_step par) i hi
    rw [show 2 * 28 + par = 56 + par by ring] at this; linarith
  -- off the head, the `μ0` term is absent
  have hE' : ∀ i j, (28 ≤ i ∨ 28 ≤ j) → |R i j - (if i = j then βs else 0)| ≤ K * b3 (2 * i + par) * b3 (2 * j + par) := by
    intro i j hij
    have e := hE i j
    have hz : ¬(i = 0 ∧ j = 0) := by rintro ⟨rfl, rfl⟩; omega
    rw [if_neg hz, sub_zero] at e; exact e
  have hH := head_margin 28 R Mh Dh δ ρ hD hρ0 hhead x
  refine block_margin R (R3_symm par μp μ0) 28 N hN _ (0.37 - K * B0 ^ 2) (K * B0 * (2 * B0))
    (K ^ 2 * (28 * 128383 ^ 2) * (2 * B0 ^ 2)) m x hH ?_ ?_ ?_ (by positivity) hm1 hm2 hb
  · intro i hi
    have hi' := (mem_Ico.mp hi).1
    have e := hE' i i (Or.inl hi')
    rw [if_pos rfl, abs_le] at e
    have hb := hbt i hi'
    have := b3_nonneg (2 * i + par)
    have := βs_ge
    have : K * b3 (2 * i + par) * b3 (2 * i + par) ≤ K * B0 ^ 2 := by
      rw [mul_assoc, sq]; exact mul_le_mul_of_nonneg_left (mul_le_mul hb hb (b3_nonneg _) B0nn) hK0
    linarith [e.1]
  · intro i hi
    have hi' := (mem_Ico.mp hi).1
    have hb := hbt i hi'
    have bi := b3_nonneg (2 * i + par)
    calc ∑ j ∈ Ico 28 N, |if i = j then 0 else R i j|
        ≤ ∑ j ∈ Ico 28 N, K * b3 (2 * i + par) * b3 (2 * j + par) := by
          refine sum_le_sum (fun j _ => ?_)
          by_cases h : i = j
          · rw [if_pos h, abs_zero]; have := b3_nonneg (2 * j + par); positivity
          · rw [if_neg h]; have := hE' i j (Or.inl hi'); rw [if_neg h, sub_zero] at this; exact this
      _ = K * b3 (2 * i + par) * ∑ j ∈ Ico 28 N, b3 (2 * j + par) := by rw [mul_sum]
      _ ≤ K * B0 * (2 * B0) := by
          have ts := tail_sum3 par N hN
          have s0 : 0 ≤ ∑ j ∈ Ico 28 N, b3 (2 * j + par) := sum_nonneg (fun j _ => b3_nonneg _)
          have : ∑ j ∈ Ico 28 N, b3 (2 * j + par) ≤ 2 * B0 := by linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb hK0) this s0 (by positivity)
  · calc ∑ i ∈ range 28, ∑ j ∈ Ico 28 N, R i j ^ 2
        ≤ ∑ i ∈ range 28, ∑ j ∈ Ico 28 N, K ^ 2 * b3 (2 * i + par) ^ 2 * b3 (2 * j + par) ^ 2 := by
          refine sum_le_sum (fun i hi => sum_le_sum (fun j hj => ?_))
          have hij : i ≠ j := by
            have := mem_range.mp hi; have := (mem_Ico.mp hj).1; omega
          have e := hE' i j (Or.inr (mem_Ico.mp hj).1)
          rw [if_neg hij, sub_zero] at e
          have : R i j ^ 2 ≤ (K * b3 (2 * i + par) * b3 (2 * j + par)) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e 2
          nlinarith
      _ = K ^ 2 * (∑ i ∈ range 28, b3 (2 * i + par) ^ 2) * (∑ j ∈ Ico 28 N, b3 (2 * j + par) ^ 2) := by
          rw [mul_assoc, sum_mul_sum, mul_sum]
          refine sum_congr rfl (fun i _ => ?_); rw [mul_sum]
          refine sum_congr rfl (fun j _ => ?_); ring
      _ ≤ K ^ 2 * (28 * 128383 ^ 2) * (2 * B0 ^ 2) := by
          have h1 : ∑ i ∈ range 28, b3 (2 * i + par) ^ 2 ≤ 28 * 128383 ^ 2 := by
            calc ∑ i ∈ range 28, b3 (2 * i + par) ^ 2 ≤ ∑ i ∈ range 28, (128383:ℝ) ^ 2 := by
                  refine sum_le_sum (fun i hi => ?_)
                  have := b3_le_head (2 * i + par) (by have := mem_range.mp hi; omega)
                  exact pow_le_pow_left₀ (b3_nonneg _) this 2
              _ = 28 * 128383 ^ 2 := by simp
          have h2 : ∑ j ∈ Ico 28 N, b3 (2 * j + par) ^ 2 ≤ 2 * B0 ^ 2 := by
            have := tail_sumsq3 par N hN
            have : b3 (56 + par) ^ 2 ≤ B0 ^ 2 := pow_le_pow_left₀ (b3_nonneg _) hB0 2
            linarith
          have s0 : 0 ≤ ∑ i ∈ range 28, b3 (2 * i + par) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
          have s1 : 0 ≤ ∑ j ∈ Ico 28 N, b3 (2 * j + par) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
          have := mul_le_mul h1 h2 s1 (by positivity)
          nlinarith

end V3Zhu
