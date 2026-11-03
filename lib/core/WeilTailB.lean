import Mathlib
import WeilTail
import WeilAssemble

/-! # Unconditional tail for the L = 1/2 Legendre certificate

Spherical Bessel functions are *defined* by Poisson's integral, so the bounds
`|j_n(x)| ≤ (x/2)ⁿ/n!` and `|i_n(z)| ≤ 2 (z/2)ⁿ/n!` (`0 ≤ z ≤ 1`) are proved here. The weight bound
`|Ψ_L − β*| ≤ 55` on `[0, 30]` comes from the stack's `WeilForm.norm_digamma_le`, and `β* ≥ 0.37` from
Mathlib's `log 2`, `π` and `√2` bounds. Geometric majorants then bound all tail row sums and the head–tail
coupling for every truncation size. The only inputs left are the arb head enclosure and Zhu's reduction.
-/

namespace WeilTailB

open Finset Real WeilTail Nat

noncomputable def jP (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (2 ^ (n + 1) * n !) * ∫ t in (-1:ℝ)..1, Real.cos (x * t) * (1 - t ^ 2) ^ n

noncomputable def iP (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (2 ^ (n + 1) * n !) * ∫ t in (-1:ℝ)..1, Real.cosh (x * t) * (1 - t ^ 2) ^ n

lemma wt_bound {t : ℝ} (ht : t ∈ Set.uIoc (-1:ℝ) 1) (n : ℕ) : 0 ≤ (1 - t ^ 2) ^ n ∧ (1 - t ^ 2) ^ n ≤ 1 := by
  rw [Set.uIoc_of_le (by norm_num)] at ht
  obtain ⟨h1, h2⟩ := ht
  have a : 0 ≤ 1 - t ^ 2 := by nlinarith
  have b : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  exact ⟨pow_nonneg a n, pow_le_one₀ a b⟩

lemma poisson_bound (n : ℕ) {x C : ℝ} (hx : 0 ≤ x) (g : ℝ → ℝ)
    (hg : ∀ t ∈ Set.uIoc (-1:ℝ) 1, |g t| ≤ C) (hC : 0 ≤ C) :
    |x ^ n / (2 ^ (n + 1) * n !) * ∫ t in (-1:ℝ)..1, g t * (1 - t ^ 2) ^ n| ≤ C * ((x / 2) ^ n / n !) := by
  have hI : ‖∫ t in (-1:ℝ)..1, g t * (1 - t ^ 2) ^ n‖ ≤ C * |1 - (-1:ℝ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    obtain ⟨a, b⟩ := wt_bound ht n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg a]
    calc |g t| * (1 - t ^ 2) ^ n ≤ C * 1 := mul_le_mul (hg t ht) b a hC
      _ = C := by ring
  have h2 : |1 - (-1:ℝ)| = 2 := by norm_num
  rw [h2, Real.norm_eq_abs] at hI
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ n / (2 ^ (n + 1) * n !))]
  calc x ^ n / (2 ^ (n + 1) * n !) * |∫ t in (-1:ℝ)..1, g t * (1 - t ^ 2) ^ n|
      ≤ x ^ n / (2 ^ (n + 1) * n !) * (C * 2) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = C * ((x / 2) ^ n / n !) := by rw [div_pow, pow_succ]; field_simp

/-- `|j_n(x)| ≤ (x/2)ⁿ/n!` for `x ≥ 0`. -/
theorem jP_bound (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : |jP n x| ≤ (x / 2) ^ n / n ! := by
  have := poisson_bound n hx (fun t => Real.cos (x * t)) (fun t _ => abs_cos_le_one _) zero_le_one
  simpa [jP] using this

lemma cosh_one_le : Real.cosh 1 ≤ 2 := by
  rw [Real.cosh_eq]
  have := Real.exp_one_lt_d9
  have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith

/-- `|i_n(x)| ≤ 2 (x/2)ⁿ/n!` for `0 ≤ x ≤ 1`. -/
theorem iP_bound (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : |iP n x| ≤ 2 * ((x / 2) ^ n / n !) := by
  have hg : ∀ t ∈ Set.uIoc (-1:ℝ) 1, |Real.cosh (x * t)| ≤ 2 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    rw [abs_of_pos (Real.cosh_pos _)]
    refine le_trans (Real.cosh_le_cosh.mpr ?_) cosh_one_le
    rw [abs_mul, abs_of_nonneg hx, abs_one]
    have : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    nlinarith [abs_nonneg t]
  have := poisson_bound n hx (fun t => Real.cosh (x * t)) hg (by norm_num)
  simpa [iP] using this

/-! ## Transforms, pole vector and the reduced matrix (L = 1/2, T# = 30) -/

/-- `T̂ₙ(t) = (−1)^{⌊n/2⌋} 2√(Lνₙ) jₙ(tL)`, `L = 1/2` (the sign `iⁿ` of the Legendre–Fourier identity, real part). -/
noncomputable def That (n : ℕ) (t : ℝ) : ℝ := (-1) ^ (n / 2) * (2 * Real.sqrt ((1 / 2) * (n + 1 / 2)) * jP n (t / 2))
noncomputable def pole (n : ℕ) : ℝ := 2 * Real.sqrt ((1 / 2) * (n + 1 / 2)) * iP n (1 / 4)
noncomputable def b (n : ℕ) : ℝ := (1 + (2 * n + 1) / 4) * (15 / 2) ^ n / n !

lemma b_nonneg (n : ℕ) : 0 ≤ b n := by unfold b; positivity

lemma two_sqrt_le {y : ℝ} (hy : 0 ≤ y) : 2 * Real.sqrt y ≤ 1 + y := by
  nlinarith [Real.sq_sqrt hy, sq_nonneg (Real.sqrt y - 1)]

lemma y_eq (n : ℕ) : (1 / 2 : ℝ) * (n + 1 / 2) = (2 * n + 1) / 4 := by ring

theorem That_bound (n : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 30) : |That n t| ≤ b n := by
  unfold That b
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hy : (0:ℝ) ≤ (1 / 2) * (n + 1 / 2) := by positivity
  have hs := two_sqrt_le hy
  rw [y_eq] at hs hy
  rw [y_eq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt ((2 * n + 1) / 4))]
  have hj := jP_bound n (by linarith : (0:ℝ) ≤ t / 2)
  have hp : (t / 2 / 2) ^ n / n ! ≤ (15 / 2 : ℝ) ^ n / n ! := by
    gcongr; linarith
  calc 2 * Real.sqrt ((2 * n + 1) / 4) * |jP n (t / 2)| ≤ (1 + (2 * n + 1) / 4) * ((15 / 2 : ℝ) ^ n / n !) :=
        mul_le_mul hs (hj.trans hp) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem pole_bound (n : ℕ) : |pole n| ≤ 2 * b n := by
  unfold pole b
  have hy : (0:ℝ) ≤ (1 / 2) * (n + 1 / 2) := by positivity
  have hs := two_sqrt_le hy
  rw [y_eq] at hs hy
  rw [y_eq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt ((2 * n + 1) / 4))]
  have hi := iP_bound n (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num)
  have hp : 2 * ((1 / 4 / 2 : ℝ) ^ n / n !) ≤ 2 * ((15 / 2 : ℝ) ^ n / n !) := by
    gcongr; norm_num
  calc 2 * Real.sqrt ((2 * n + 1) / 4) * |iP n (1 / 4)| ≤ (1 + (2 * n + 1) / 4) * (2 * ((15 / 2 : ℝ) ^ n / n !)) :=
        mul_le_mul hs (hi.trans hp) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Archimedean-plus-prime weight at `L = 1/2` (only `n = 2` has `log n < 2L`). -/
noncomputable def Psi (t : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + (t / 2 : ℝ) * Complex.I)).re - Real.log π - Real.sqrt 2 * Real.log 2 * Real.cos (t * Real.log 2)

/-- `β* = log(T#/2π) − 1/T# − A_L` with `T# = 30`, `A_L = √2 log 2`. -/
noncomputable def βs : ℝ := Real.log (30 / (2 * π)) - 1 / 30 - Real.sqrt 2 * Real.log 2

lemma sqrt2_le : Real.sqrt 2 ≤ 1.4143 := by
  rw [show (1.4143:ℝ) = Real.sqrt (1.4143 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem βs_ge : (0.37 : ℝ) ≤ βs := by
  unfold βs
  have hπ := Real.pi_lt_d2
  have h4 : Real.log 4 ≤ Real.log (30 / (2 * π)) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ (by positivity)]; linarith
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have s := sqrt2_le
  have s0 := Real.sqrt_nonneg 2
  nlinarith

theorem βs_le : βs ≤ 4 := by
  unfold βs
  have hπ := Real.pi_gt_three
  have : Real.log (30 / (2 * π)) ≤ 30 / (2 * π) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have : 30 / (2 * π) ≤ 5 := by rw [div_le_iff₀ (by positivity)]; linarith
  have : 0 ≤ Real.sqrt 2 * Real.log 2 := mul_nonneg (Real.sqrt_nonneg 2) (Real.log_nonneg (by norm_num))
  linarith

noncomputable def wψ (t : ℝ) : ℝ := Psi t - βs

/-- **`|Ψ_L − β*| ≤ 55` on `[0, 30]`**, from the stack's `‖ψ(z)‖ ≤ 12√(1 + ‖z‖)`. -/
theorem wψ_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 30) : |wψ t| ≤ 55 := by
  set z : ℂ := 1 / 4 + (t / 2 : ℝ) * Complex.I
  have hzre : z.re = 1 / 4 := by simp [z]
  have hz : 1 / 4 ≤ z.re := by rw [hzre]
  have hnz : ‖z‖ ≤ 1 / 4 + t / 2 := by
    refine (norm_add_le _ _).trans ?_
    have : ‖((1:ℂ) / 4)‖ = 1 / 4 := by norm_num
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hψ := WeilForm.norm_digamma_le hz
  have hsq : Real.sqrt (1 + ‖z‖) ≤ 4.04 := by
    rw [show (4.04:ℝ) = Real.sqrt (4.04 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hre : |(Complex.digamma z).re| ≤ 48.48 := by
    refine (Complex.abs_re_le_norm _).trans (hψ.trans ?_); nlinarith
  have hlogπ : |Real.log π| ≤ 1.39 := by
    have hπ := Real.pi_lt_d2; have hπ3 := Real.pi_gt_three
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    have : Real.log π ≤ Real.log 4 := Real.log_le_log (by positivity) (by linarith)
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  have hc : |Real.sqrt 2 * Real.log 2 * Real.cos (t * Real.log 2)| ≤ 0.99 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.log_nonneg (by norm_num)))]
    have := abs_cos_le_one (t * Real.log 2)
    have := Real.log_two_lt_d9; have := sqrt2_le
    have : Real.sqrt 2 * Real.log 2 ≤ 0.99 := by
      nlinarith [Real.sqrt_nonneg 2, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
    nlinarith [abs_nonneg (Real.cos (t * Real.log 2)), mul_nonneg (Real.sqrt_nonneg 2) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
  have hb1 := βs_ge; have hb2 := βs_le
  unfold wψ Psi
  rw [abs_le] at hre hlogπ hc ⊢
  constructor <;> linarith [hre.1, hre.2, hlogπ.1, hlogπ.2, hc.1, hc.2]

noncomputable def Cm (w : ℝ → ℝ) (n m : ℕ) : ℝ := (1 / π) * ∫ t in (0:ℝ)..30, w t * That n t * That m t

theorem Cm_bound (w : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ t, 0 ≤ t → t ≤ 30 → |w t| ≤ M) (n m : ℕ) :
    |Cm w n m| ≤ 10 * M * b n * b m := by
  have hI : ‖∫ t in (0:ℝ)..30, w t * That n t * That m t‖ ≤ (M * b n * b m) * |30 - (0:ℝ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have a := hw t ht.1.le ht.2
    have bn := That_bound n ht.1.le ht.2
    have bm := That_bound m ht.1.le ht.2
    exact mul_le_mul (mul_le_mul a bn (abs_nonneg _) hM) bm (abs_nonneg _) (mul_nonneg hM (b_nonneg n))
  rw [Real.norm_eq_abs, show |30 - (0:ℝ)| = 30 by norm_num] at hI
  unfold Cm
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / π)]
  have hπ := Real.pi_gt_three
  have : 1 / π ≤ 1 / 3 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h0 : 0 ≤ M * b n * b m := mul_nonneg (mul_nonneg hM (b_nonneg n)) (b_nonneg m)
  calc 1 / π * |∫ t in (0:ℝ)..30, w t * That n t * That m t| ≤ 1 / 3 * (M * b n * b m * 30) :=
        mul_le_mul this hI (abs_nonneg _) (by norm_num)
    _ = 10 * M * b n * b m := by ring

/-- Reduced Zhu matrix in sector `par` (`0` even, `1` odd), pole sign `σ` (`+1` even, `−1` odd). -/
noncomputable def Rm (par : ℕ) (σ : ℝ) (w : ℝ → ℝ) (β : ℝ) (i j : ℕ) : ℝ :=
  (if i = j then β else 0) + σ * 2 * pole (2 * i + par) * pole (2 * j + par) + Cm w (2 * i + par) (2 * j + par)

lemma Cm_symm (w : ℝ → ℝ) (n m : ℕ) : Cm w n m = Cm w m n := by
  unfold Cm; congr 1; refine intervalIntegral.integral_congr (fun t _ => ?_); ring

theorem Rm_symm (par : ℕ) (σ : ℝ) (w : ℝ → ℝ) (β : ℝ) (i j : ℕ) : Rm par σ w β i j = Rm par σ w β j i := by
  unfold Rm; rw [Cm_symm w (2 * i + par)]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

theorem Rm_entry (par : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1) (w : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ t, 0 ≤ t → t ≤ 30 → |w t| ≤ M) (β : ℝ) (i j : ℕ) :
    |Rm par σ w β i j - (if i = j then β else 0)| ≤ (10 * M + 8) * b (2 * i + par) * b (2 * j + par) := by
  have hc := Cm_bound w hM hw (2 * i + par) (2 * j + par)
  have hpi := pole_bound (2 * i + par)
  have hpj := pole_bound (2 * j + par)
  have bi := b_nonneg (2 * i + par)
  have bj := b_nonneg (2 * j + par)
  have hp : |σ * 2 * pole (2 * i + par) * pole (2 * j + par)| ≤ 8 * b (2 * i + par) * b (2 * j + par) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    have := mul_le_mul hpi hpj (abs_nonneg _) (by linarith)
    have h1 : |σ| * 2 * |pole (2 * i + par)| * |pole (2 * j + par)| ≤ 1 * 2 * |pole (2 * i + par)| * |pole (2 * j + par)| := by
      have := mul_nonneg (abs_nonneg (pole (2 * i + par))) (abs_nonneg (pole (2 * j + par)))
      nlinarith
    nlinarith
  unfold Rm
  have : (if i = j then β else 0) + σ * 2 * pole (2 * i + par) * pole (2 * j + par) + Cm w (2 * i + par) (2 * j + par)
      - (if i = j then β else 0) = σ * 2 * pole (2 * i + par) * pole (2 * j + par) + Cm w (2 * i + par) (2 * j + par) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  nlinarith

/-! ## Geometric majorants, valid for every truncation size -/

lemma b_step {n : ℕ} (hn : 20 ≤ n) : b (n + 2) ≤ b n / 2 := by
  have hF : 0 ≤ (15 / 2 : ℝ) ^ n / n ! := by positivity
  have e1 : b (n + 2) = (1 + (2 * ((n:ℝ) + 2) + 1) / 4) * (225 / 4) / (((n:ℝ) + 2) * ((n:ℝ) + 1)) * ((15 / 2) ^ n / n !) := by
    unfold b; rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; field_simp; ring
  have e2 : b n = (1 + (2 * (n:ℝ) + 1) / 4) * ((15 / 2) ^ n / n !) := by unfold b; ring
  have hn' : (20:ℝ) ≤ n := by exact_mod_cast hn
  have key : (1 + (2 * ((n:ℝ) + 2) + 1) / 4) * (225 / 4) / (((n:ℝ) + 2) * ((n:ℝ) + 1)) ≤ (1 + (2 * (n:ℝ) + 1) / 4) / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have A : 0 < (1 + (2 * (n:ℝ) + 1) / 4) := by positivity
    have B : (225:ℝ) < ((n:ℝ) + 2) * ((n:ℝ) + 1) := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left B A]
  rw [e1, e2]
  calc _ ≤ (1 + (2 * (n:ℝ) + 1) / 4) / 2 * ((15 / 2) ^ n / n !) := mul_le_mul_of_nonneg_right key hF
    _ = _ := by ring

lemma geom_sum (f : ℕ → ℝ) (h : ℕ) (hf : ∀ i, h ≤ i → f (i + 1) ≤ f i / 2) :
    ∀ N, h ≤ N → (∑ i ∈ Ico h N, f i) + 2 * f N ≤ 2 * f h := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih => rw [Finset.sum_Ico_succ_top hN]; have := hf N hN; linarith

lemma tail_mono (f : ℕ → ℝ) (h : ℕ) (hf0 : ∀ i, 0 ≤ f i) (hf : ∀ i, h ≤ i → f (i + 1) ≤ f i / 2) :
    ∀ i, h ≤ i → f i ≤ f h := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact le_rfl
  | succ i hi ih => have := hf i hi; have := hf0 i; linarith

lemma bs_step (par : ℕ) : ∀ i, 28 ≤ i → b (2 * (i + 1) + par) ≤ b (2 * i + par) / 2 := by
  intro i hi
  rw [show 2 * (i + 1) + par = (2 * i + par) + 2 by ring]; exact b_step (by omega)

lemma bsq_step (par : ℕ) : ∀ i, 28 ≤ i → b (2 * (i + 1) + par) ^ 2 ≤ b (2 * i + par) ^ 2 / 2 := by
  intro i hi
  have h := bs_step par i hi
  have h0 := b_nonneg (2 * (i + 1) + par)
  have h1 := b_nonneg (2 * i + par)
  nlinarith

lemma tail_sum (par N : ℕ) (hN : 28 ≤ N) : ∑ j ∈ Ico 28 N, b (2 * j + par) ≤ 2 * b (56 + par) := by
  have := geom_sum (fun i => b (2 * i + par)) 28 (bs_step par) N hN
  have := b_nonneg (2 * N + par)
  linarith

lemma tail_sumsq (par N : ℕ) (hN : 28 ≤ N) : ∑ j ∈ Ico 28 N, b (2 * j + par) ^ 2 ≤ 2 * b (56 + par) ^ 2 := by
  have := geom_sum (fun i => b (2 * i + par) ^ 2) 28 (bsq_step par) N hN
  have := sq_nonneg (b (2 * N + par))
  linarith

lemma b_le_head (n : ℕ) (hn : n ≤ 55) : b n ≤ 190269 := by
  have e : b n = (1 + (2 * (n:ℝ) + 1) / 4) * ((15 / 2) ^ n / n !) := by unfold b; ring
  have h1 : (15 / 2 : ℝ) ^ n / n ! ≤ 6561 := by
    refine (Real.pow_div_factorial_le_exp (15 / 2) (by norm_num) n).trans ?_
    have : Real.exp (15 / 2) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by norm_num)
    have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have he := Real.exp_one_lt_d9
    have : Real.exp 1 ^ 8 ≤ (3:ℝ) ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 8
    norm_num at this; linarith
  have hn' : (n:ℝ) ≤ 55 := by exact_mod_cast hn
  rw [e]
  have : (1 + (2 * (n:ℝ) + 1) / 4) ≤ 29 := by linarith
  calc _ ≤ 29 * 6561 := mul_le_mul this h1 (by positivity) (by norm_num)
    _ = 190269 := by norm_num

lemma b56_le : b 56 ≤ 5 / 10 ^ 25 := by
  unfold b; rw [div_le_iff₀ (by positivity)]; norm_num [Nat.factorial]

lemma b57_le : b 57 ≤ 5 / 10 ^ 25 := by
  unfold b; rw [div_le_iff₀ (by positivity)]; norm_num [Nat.factorial]

/-- **Sector theorem (unconditional except the head enclosure).** For the reduced matrix with the true
weight `wψ = Ψ_L − β*`, a head certificate `(Mh, Dh, δ, ρ)` on the first 28 modes whose entrywise enclosure
holds gives `m‖x‖² ≤ xᵀ R_N x` for every `N ≥ 28`. -/
theorem sector_margin (par : ℕ) (hpar : par ≤ 1) {σ : ℝ} (hσ : |σ| ≤ 1)
    (Mh : ℕ → ℕ → ℝ) (Dh : ℕ → ℝ) (δ ρ m B0 : ℝ) (hD : ∀ k, 0 ≤ Dh k) (hρ0 : 0 ≤ ρ)
    (hhead : ∀ i < 28, ∀ j < 28, |Rm par σ wψ βs i j - certMat 28 Mh Dh δ i j| ≤ ρ)
    (hB0 : b (56 + par) ≤ B0)
    (hm1 : m ≤ δ - ((28:ℕ):ℝ) ^ 2 * ρ) (hm2 : m ≤ 0.37 - 558 * B0 ^ 2 - 558 * B0 * (2 * B0))
    (hb : 558 ^ 2 * (28 * 190269 ^ 2) * (2 * B0 ^ 2) ≤ (δ - ((28:ℕ):ℝ) ^ 2 * ρ - m) * (0.37 - 558 * B0 ^ 2 - 558 * B0 * (2 * B0) - m))
    (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) :
    m * ∑ i ∈ range N, x i ^ 2 ≤ qf (Rm par σ wψ βs) x (range N) (range N) := by
  have hw : ∀ t, 0 ≤ t → t ≤ 30 → |wψ t| ≤ 55 := fun t h0 h1 => wψ_bound h0 h1
  have hE := Rm_entry par hσ wψ (by norm_num) hw βs
  have hK : (10 * (55:ℝ) + 8) = 558 := by norm_num
  rw [hK] at hE
  set R := Rm par σ wψ βs
  have B0nn : 0 ≤ B0 := (b_nonneg _).trans hB0
  have hbt : ∀ i, 28 ≤ i → b (2 * i + par) ≤ B0 := by
    intro i hi
    have := tail_mono (fun i => b (2 * i + par)) 28 (fun i => b_nonneg _) (bs_step par) i hi
    rw [show 2 * 28 + par = 56 + par by ring] at this; linarith
  have hH := head_margin 28 R Mh Dh δ ρ hD hρ0 hhead x
  refine block_margin R (Rm_symm par σ wψ βs) 28 N hN _ (0.37 - 558 * B0 ^ 2) (558 * B0 * (2 * B0))
    (558 ^ 2 * (28 * 190269 ^ 2) * (2 * B0 ^ 2)) m x hH ?_ ?_ ?_ (by positivity) hm1 hm2 hb
  · intro i hi
    have hi' := (mem_Ico.mp hi).1
    have e := hE i i
    rw [if_pos rfl, abs_le] at e
    have hb := hbt i hi'
    have := b_nonneg (2 * i + par)
    have := βs_ge
    nlinarith
  · intro i hi
    have hi' := (mem_Ico.mp hi).1
    have hb := hbt i hi'
    have bi := b_nonneg (2 * i + par)
    calc ∑ j ∈ Ico 28 N, |if i = j then 0 else R i j|
        ≤ ∑ j ∈ Ico 28 N, 558 * b (2 * i + par) * b (2 * j + par) := by
          refine sum_le_sum (fun j _ => ?_)
          by_cases h : i = j
          · rw [if_pos h, abs_zero]; have := b_nonneg (2 * j + par); positivity
          · rw [if_neg h]; have := hE i j; rw [if_neg h, sub_zero] at this; exact this
      _ = 558 * b (2 * i + par) * ∑ j ∈ Ico 28 N, b (2 * j + par) := by rw [mul_sum]
      _ ≤ 558 * B0 * (2 * B0) := by
          have ts := tail_sum par N hN
          have : b (56 + par) ≤ B0 := hB0
          have s0 : 0 ≤ ∑ j ∈ Ico 28 N, b (2 * j + par) := sum_nonneg (fun j _ => b_nonneg _)
          have : ∑ j ∈ Ico 28 N, b (2 * j + par) ≤ 2 * B0 := by linarith
          exact mul_le_mul (by nlinarith) this s0 (by positivity)
  · calc ∑ i ∈ range 28, ∑ j ∈ Ico 28 N, R i j ^ 2
        ≤ ∑ i ∈ range 28, ∑ j ∈ Ico 28 N, 558 ^ 2 * b (2 * i + par) ^ 2 * b (2 * j + par) ^ 2 := by
          refine sum_le_sum (fun i hi => sum_le_sum (fun j hj => ?_))
          have hij : i ≠ j := by
            have := mem_range.mp hi; have := (mem_Ico.mp hj).1; omega
          have e := hE i j
          rw [if_neg hij, sub_zero] at e
          have : R i j ^ 2 ≤ (558 * b (2 * i + par) * b (2 * j + par)) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e 2
          nlinarith
      _ = 558 ^ 2 * (∑ i ∈ range 28, b (2 * i + par) ^ 2) * (∑ j ∈ Ico 28 N, b (2 * j + par) ^ 2) := by
          rw [mul_assoc, sum_mul_sum, mul_sum]
          refine sum_congr rfl (fun i _ => ?_); rw [mul_sum]
          refine sum_congr rfl (fun j _ => ?_); ring
      _ ≤ 558 ^ 2 * (28 * 190269 ^ 2) * (2 * B0 ^ 2) := by
          have h1 : ∑ i ∈ range 28, b (2 * i + par) ^ 2 ≤ 28 * 190269 ^ 2 := by
            calc ∑ i ∈ range 28, b (2 * i + par) ^ 2 ≤ ∑ i ∈ range 28, (190269:ℝ) ^ 2 := by
                  refine sum_le_sum (fun i hi => ?_)
                  have := b_le_head (2 * i + par) (by have := mem_range.mp hi; omega)
                  exact pow_le_pow_left₀ (b_nonneg _) this 2
              _ = 28 * 190269 ^ 2 := by simp
          have h2 : ∑ j ∈ Ico 28 N, b (2 * j + par) ^ 2 ≤ 2 * B0 ^ 2 := by
            have := tail_sumsq par N hN
            have : b (56 + par) ^ 2 ≤ B0 ^ 2 := pow_le_pow_left₀ (b_nonneg _) hB0 2
            linarith
          have s0 : 0 ≤ ∑ i ∈ range 28, b (2 * i + par) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
          have s1 : 0 ≤ ∑ j ∈ Ico 28 N, b (2 * j + par) ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
          have := mul_le_mul h1 h2 s1 (by positivity)
          nlinarith


namespace L05Odd
/-- Upper-triangular factor (row `k` = column `k` of the unit lower LDLᵀ factor), exact rationals. -/
noncomputable def M : Fin 28 → Fin 28 → ℝ := ![![(1:ℝ), (129319610482684604510831/151115727451828646838272:ℝ), (-761941265239446535728289/1208925819614629174706176:ℝ), (125948594903727744031387/302231454903657293676544:ℝ), (-710643767760871209186913/1208925819614629174706176:ℝ), (433071716801584182208267/1208925819614629174706176:ℝ), (-52126162957805774665469/604462909807314587353088:ℝ), (-3189253965994395411823/1208925819614629174706176:ℝ), (9290011676435942471127/1208925819614629174706176:ℝ), (-3118361895773303947073/1208925819614629174706176:ℝ), (318060499839053943383/604462909807314587353088:ℝ), (-94434872094013308613/1208925819614629174706176:ℝ), (10962683072632880591/1208925819614629174706176:ℝ), (-1035896145054184279/1208925819614629174706176:ℝ), (40903768286056825/604462909807314587353088:ℝ), (-2751758625454053/604462909807314587353088:ℝ), (320059639258423/1208925819614629174706176:ℝ), (-16280682350363/1208925819614629174706176:ℝ), (45715554777/75557863725914323419136:ℝ), (-7315933787/302231454903657293676544:ℝ), (1049968147/1208925819614629174706176:ℝ), (-16996835/604462909807314587353088:ℝ), (998519/1208925819614629174706176:ℝ), (-6685/302231454903657293676544:ℝ), (41/75557863725914323419136:ℝ), (-15/1208925819614629174706176:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (1:ℝ), (3732230836935415505350239/1208925819614629174706176:ℝ), (-52435384099288869610079/151115727451828646838272:ℝ), (-1321921657789267491293589/1208925819614629174706176:ℝ), (796145186332140771271099/1208925819614629174706176:ℝ), (-18387215859964543917841/151115727451828646838272:ℝ), (-1652977109813978932059/75557863725914323419136:ℝ), (21838178481293710465395/1208925819614629174706176:ℝ), (-6417768361314349931367/1208925819614629174706176:ℝ), (307900784646055376239/302231454903657293676544:ℝ), (-44034852480589091695/302231454903657293676544:ℝ), (19927121087319974773/1208925819614629174706176:ℝ), (-1847290285939018415/1208925819614629174706176:ℝ), (71861636543776819/604462909807314587353088:ℝ), (-298508864031887/37778931862957161709568:ℝ), (549892342839407/1208925819614629174706176:ℝ), (-27727261191459/1208925819614629174706176:ℝ), (1236103284501/1208925819614629174706176:ℝ), (-24555430653/604462909807314587353088:ℝ), (1750920427/1208925819614629174706176:ℝ), (-28178201/604462909807314587353088:ℝ), (823191/604462909807314587353088:ℝ), (-5483/151115727451828646838272:ℝ), (535/604462909807314587353088:ℝ), (-3/151115727451828646838272:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (1:ℝ), (511057441664651531283127/75557863725914323419136:ℝ), (7198797333629793772212237/1208925819614629174706176:ℝ), (-664814292688747876682147/151115727451828646838272:ℝ), (1916645824717271681525255/1208925819614629174706176:ℝ), (-217094277779767720241647/604462909807314587353088:ℝ), (66475266041846112630977/1208925819614629174706176:ℝ), (-6878853462488201103883/1208925819614629174706176:ℝ), (51478728642662537283/151115727451828646838272:ℝ), (4282406100128674961/1208925819614629174706176:ℝ), (-4424632477397157359/1208925819614629174706176:ℝ), (313394850391376163/604462909807314587353088:ℝ), (-14815770403639717/302231454903657293676544:ℝ), (274361891092187/75557863725914323419136:ℝ), (-135008402961559/604462909807314587353088:ℝ), (14213955637853/1208925819614629174706176:ℝ), (-40781484237/75557863725914323419136:ℝ), (6616810501/302231454903657293676544:ℝ), (-119760529/151115727451828646838272:ℝ), (15597933/604462909807314587353088:ℝ), (-459823/604462909807314587353088:ℝ), (12341/604462909807314587353088:ℝ), (-303/604462909807314587353088:ℝ), (7/604462909807314587353088:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-318193528868738248902181/302231454903657293676544:ℝ), (658458213760966834901323/1208925819614629174706176:ℝ), (-120486713695578215476295/1208925819614629174706176:ℝ), (-3397777202408359819487/302231454903657293676544:ℝ), (6643595606660527820649/604462909807314587353088:ℝ), (-243251309420995507401/75557863725914323419136:ℝ), (368003587366475822619/604462909807314587353088:ℝ), (-51814809248923145621/604462909807314587353088:ℝ), (722099834378294367/75557863725914323419136:ℝ), (-528437387885346365/604462909807314587353088:ℝ), (81239812729371019/1208925819614629174706176:ℝ), (-5340299859458739/1208925819614629174706176:ℝ), (76081549345767/302231454903657293676544:ℝ), (-3800421216053/302231454903657293676544:ℝ), (335890630101/604462909807314587353088:ℝ), (-26470436371/1208925819614629174706176:ℝ), (936372597/1208925819614629174706176:ℝ), (-14957411/604462909807314587353088:ℝ), (433857/604462909807314587353088:ℝ), (-1435/75557863725914323419136:ℝ), (557/1208925819614629174706176:ℝ), (-3/302231454903657293676544:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (992338742120372554764409/1208925819614629174706176:ℝ), (-48470688885119411514045/302231454903657293676544:ℝ), (-3224654063740305558549/302231454903657293676544:ℝ), (8812864907008854280673/604462909807314587353088:ℝ), (-2674436271243631467873/604462909807314587353088:ℝ), (1024205943064507437203/1208925819614629174706176:ℝ), (-72438975669172540995/604462909807314587353088:ℝ), (8081621760075499495/604462909807314587353088:ℝ), (-738052503592047861/604462909807314587353088:ℝ), (113113952648384111/1208925819614629174706176:ℝ), (-3702868746528799/604462909807314587353088:ℝ), (210047089789187/604462909807314587353088:ℝ), (-20880913000421/1208925819614629174706176:ℝ), (114750824663/151115727451828646838272:ℝ), (-35982512211/1208925819614629174706176:ℝ), (316528095/302231454903657293676544:ℝ), (-10058723/302231454903657293676544:ℝ), (1160909/1208925819614629174706176:ℝ), (-15279/604462909807314587353088:ℝ), (737/1208925819614629174706176:ℝ), (-1/75557863725914323419136:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-174583205698781768483471/1208925819614629174706176:ℝ), (158658839016294397766069/1208925819614629174706176:ℝ), (-29349737397084806338353/604462909807314587353088:ℝ), (876441000551660785065/75557863725914323419136:ℝ), (-2449453724053917338559/1208925819614629174706176:ℝ), (166222619372597463279/604462909807314587353088:ℝ), (-18199126018862282073/604462909807314587353088:ℝ), (1649899236780086499/604462909807314587353088:ℝ), (-252598341432036635/1208925819614629174706176:ℝ), (16579885775399051/1208925819614629174706176:ℝ), (-944855223606423/1208925819614629174706176:ℝ), (47239478229993/1208925819614629174706176:ℝ), (-1045241260729/604462909807314587353088:ℝ), (41255253731/604462909807314587353088:ℝ), (-1462058025/604462909807314587353088:ℝ), (93597537/1208925819614629174706176:ℝ), (-2720197/1208925819614629174706176:ℝ), (72119/1208925819614629174706176:ℝ), (-219/151115727451828646838272:ℝ), (39/1208925819614629174706176:ℝ), (-1/1208925819614629174706176:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-84359817113623205170277/1208925819614629174706176:ℝ), (837259574457453111095/37778931862957161709568:ℝ), (-6032711479311360729763/1208925819614629174706176:ℝ), (513758502069271716661/604462909807314587353088:ℝ), (-138051542262718921499/1208925819614629174706176:ℝ), (1884210845532615055/151115727451828646838272:ℝ), (-1368072446025426293/1208925819614629174706176:ℝ), (105054915262447259/1208925819614629174706176:ℝ), (-6924625418083175/1208925819614629174706176:ℝ), (198250422625245/604462909807314587353088:ℝ), (-9961488324613/604462909807314587353088:ℝ), (886132588861/1208925819614629174706176:ℝ), (-8788106527/302231454903657293676544:ℝ), (1251992283/1208925819614629174706176:ℝ), (-20135225/604462909807314587353088:ℝ), (587969/604462909807314587353088:ℝ), (-31321/1208925819614629174706176:ℝ), (191/302231454903657293676544:ℝ), (-17/1208925819614629174706176:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-9367974418393544239267/1208925819614629174706176:ℝ), (2018863891188506991971/1208925819614629174706176:ℝ), (-337825862837401903613/1208925819614629174706176:ℝ), (45158384020355924189/1208925819614629174706176:ℝ), (-1234168450645337127/302231454903657293676544:ℝ), (112496996836333031/302231454903657293676544:ℝ), (-34757167222145711/1208925819614629174706176:ℝ), (2305966217519241/1208925819614629174706176:ℝ), (-132931355225195/1208925819614629174706176:ℝ), (6724487093973/1208925819614629174706176:ℝ), (-301069375309/1208925819614629174706176:ℝ), (12019896421/1208925819614629174706176:ℝ), (-215376003/604462909807314587353088:ℝ), (13937703/1208925819614629174706176:ℝ), (-102331/302231454903657293676544:ℝ), (5481/604462909807314587353088:ℝ), (-269/1208925819614629174706176:ℝ), (3/604462909807314587353088:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-267842289852787589077/604462909807314587353088:ℝ), (88933989359140134467/1208925819614629174706176:ℝ), (-11887365282973440395/1208925819614629174706176:ℝ), (1304352490000714531/1208925819614629174706176:ℝ), (-119542402103326319/1208925819614629174706176:ℝ), (9290133734079463/1208925819614629174706176:ℝ), (-620236178377165/1208925819614629174706176:ℝ), (17988179980525/604462909807314587353088:ℝ), (-1830803514283/1208925819614629174706176:ℝ), (20609501367/302231454903657293676544:ℝ), (-3309171465/1208925819614629174706176:ℝ), (14900275/151115727451828646838272:ℝ), (-1937949/604462909807314587353088:ℝ), (57179/604462909807314587353088:ℝ), (-769/302231454903657293676544:ℝ), (19/302231454903657293676544:ℝ), (-1/604462909807314587353088:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-18529568005888425297/1208925819614629174706176:ℝ), (2483493640941019369/1208925819614629174706176:ℝ), (-17106221216674687/75557863725914323419136:ℝ), (25209167690098435/1208925819614629174706176:ℝ), (-1969023324599227/1208925819614629174706176:ℝ), (132103313896079/1208925819614629174706176:ℝ), (-3849162484939/604462909807314587353088:ℝ), (196741181201/604462909807314587353088:ℝ), (-8895452761/604462909807314587353088:ℝ), (716911355/1208925819614629174706176:ℝ), (-25918073/1208925819614629174706176:ℝ), (422803/604462909807314587353088:ℝ), (-25029/1208925819614629174706176:ℝ), (675/1208925819614629174706176:ℝ), (-17/1208925819614629174706176:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-414334631706515793/1208925819614629174706176:ℝ), (11462770216882169/302231454903657293676544:ℝ), (-4240382638905347/1208925819614629174706176:ℝ), (20780518269833/75557863725914323419136:ℝ), (-22387346438629/1208925819614629174706176:ℝ), (1308976520411/1208925819614629174706176:ℝ), (-16777932215/302231454903657293676544:ℝ), (3043054907/1208925819614629174706176:ℝ), (-122949609/1208925819614629174706176:ℝ), (2227949/604462909807314587353088:ℝ), (-72857/604462909807314587353088:ℝ), (2161/604462909807314587353088:ℝ), (-117/1208925819614629174706176:ℝ), (3/1208925819614629174706176:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-3107057200581927/604462909807314587353088:ℝ), (576574102234059/1208925819614629174706176:ℝ), (-22671389101843/604462909807314587353088:ℝ), (3061200769551/1208925819614629174706176:ℝ), (-179420098015/1208925819614629174706176:ℝ), (4609627345/604462909807314587353088:ℝ), (-104719267/302231454903657293676544:ℝ), (16955689/1208925819614629174706176:ℝ), (-38473/75557863725914323419136:ℝ), (10081/604462909807314587353088:ℝ), (-599/1208925819614629174706176:ℝ), (1/75557863725914323419136:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-64402713282345/1208925819614629174706176:ℝ), (1269116676117/302231454903657293676544:ℝ), (-343425545293/1208925819614629174706176:ℝ), (5041338377/302231454903657293676544:ℝ), (-259470971/302231454903657293676544:ℝ), (23613761/604462909807314587353088:ℝ), (-1914375/1208925819614629174706176:ℝ), (34795/604462909807314587353088:ℝ), (-1141/604462909807314587353088:ℝ), (17/302231454903657293676544:ℝ), (-1/604462909807314587353088:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-474200019679/1208925819614629174706176:ℝ), (8033078295/302231454903657293676544:ℝ), (-944744359/604462909807314587353088:ℝ), (97376317/1208925819614629174706176:ℝ), (-4436241/1208925819614629174706176:ℝ), (45005/302231454903657293676544:ℝ), (-6551/1208925819614629174706176:ℝ), (215/1208925819614629174706176:ℝ), (-3/604462909807314587353088:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-2544995823/1208925819614629174706176:ℝ), (149833705/1208925819614629174706176:ℝ), (-3865053/604462909807314587353088:ℝ), (176255/604462909807314587353088:ℝ), (-7159/604462909807314587353088:ℝ), (521/1208925819614629174706176:ℝ), (-17/1208925819614629174706176:ℝ), (1/1208925819614629174706176:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-5094491/604462909807314587353088:ℝ), (263073/604462909807314587353088:ℝ), (-12007/604462909807314587353088:ℝ), (61/75557863725914323419136:ℝ), (-9/302231454903657293676544:ℝ), (1/1208925819614629174706176:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-31061/1208925819614629174706176:ℝ), (1419/1208925819614629174706176:ℝ), (-29/604462909807314587353088:ℝ), (1/604462909807314587353088:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (-73/1208925819614629174706176:ℝ), (3/1208925819614629174706176:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ)]]
/-- LDLᵀ pivots of `mid − δ I`, exact rationals. -/
noncomputable def D : Fin 28 → ℝ := ![(166419892615310035624477/1208925819614629174706176:ℝ), (119975223907169552366965/1208925819614629174706176:ℝ), (8324603375381749714133/1208925819614629174706176:ℝ), (429599668573198208217379/1208925819614629174706176:ℝ), (66167718906891979460633/302231454903657293676544:ℝ), (126488313380567634713799/302231454903657293676544:ℝ), (96398964116823008465477/151115727451828646838272:ℝ), (682987538696657644568861/1208925819614629174706176:ℝ), (665955086459785958392057/1208925819614629174706176:ℝ), (664614645844127097788679/1208925819614629174706176:ℝ), (332277455840263387644339/604462909807314587353088:ℝ), (332276624687985247308953/604462909807314587353088:ℝ), (664553218999035855164539/1208925819614629174706176:ℝ), (664553218621791639719473/1208925819614629174706176:ℝ), (664553218618511455538693/1208925819614629174706176:ℝ), (664553218618490932542899/1208925819614629174706176:ℝ), (332276609309245418918097/604462909807314587353088:ℝ), (166138304654622709376673/302231454903657293676544:ℝ), (332276609309245418752905/604462909807314587353088:ℝ), (664553218618490837505809/1208925819614629174706176:ℝ), (664553218618490837505809/1208925819614629174706176:ℝ), (664553218618490837505809/1208925819614629174706176:ℝ), (664553218618490837505809/1208925819614629174706176:ℝ), (664553218618490837505809/1208925819614629174706176:ℝ), (664553218618490837505809/1208925819614629174706176:ℝ), (664553218618490837505809/1208925819614629174706176:ℝ), (664553218618490837505809/1208925819614629174706176:ℝ), (664553218618490837505809/1208925819614629174706176:ℝ)]
noncomputable def δ : ℝ := (233/10000000:ℝ)
noncomputable def ρ : ℝ := (189/10000000000000000000000000:ℝ)
lemma hD : ∀ k, 0 ≤ D k := by intro k; fin_cases k <;> simp [D] <;> norm_num
lemma hρ : (((28:ℕ)):ℝ) ^ 2 * ρ < δ := by simp only [ρ, δ]; norm_num


noncomputable def Mn (k i : ℕ) : ℝ := if h : k < 28 ∧ i < 28 then M ⟨k, h.1⟩ ⟨i, h.2⟩ else 0
noncomputable def Dn (k : ℕ) : ℝ := if h : k < 28 then D ⟨k, h⟩ else 0
lemma hDn : ∀ k, 0 ≤ Dn k := by
  intro k; unfold Dn; split_ifs with h
  · exact hD _
  · exact le_rfl
end L05Odd

/-- **Named hypothesis (arb numerics), even sector**: entrywise enclosure of the 28×28 head of the reduced matrix. -/
def EvenHead : Prop := ∀ i < 28, ∀ j < 28,
  |Rm 0 1 wψ βs i j - certMat 28 WeilTail.L05Tail.Mn WeilTail.L05Tail.Dn WeilTail.L05Tail.δ i j| ≤ WeilTail.L05Tail.ρ

/-- **Named hypothesis (arb numerics), odd sector**. -/
def OddHead : Prop := ∀ i < 28, ∀ j < 28,
  |Rm 1 (-1) wψ βs i j - certMat 28 L05Odd.Mn L05Odd.Dn L05Odd.δ i j| ≤ L05Odd.ρ

theorem even_margin (H : EvenHead) (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) :
    (1 / 20000000 : ℝ) * ∑ i ∈ range N, x i ^ 2 ≤ qf (Rm 0 1 wψ βs) x (range N) (range N) := by
  have hρ0 : (0:ℝ) ≤ WeilTail.L05Tail.ρ := by simp only [WeilTail.L05Tail.ρ]; norm_num
  refine sector_margin 0 (by norm_num) (by norm_num) _ _ _ _ _ (5 / 10 ^ 25) WeilTail.L05Tail.hDn hρ0 H
    b56_le ?_ ?_ ?_ N hN x
  · simp only [WeilTail.L05Tail.δ, WeilTail.L05Tail.ρ]; norm_num
  · norm_num
  · simp only [WeilTail.L05Tail.δ, WeilTail.L05Tail.ρ]; norm_num

theorem odd_margin (H : OddHead) (N : ℕ) (hN : 28 ≤ N) (x : ℕ → ℝ) :
    (1 / 100000 : ℝ) * ∑ i ∈ range N, x i ^ 2 ≤ qf (Rm 1 (-1) wψ βs) x (range N) (range N) := by
  have hρ0 : (0:ℝ) ≤ L05Odd.ρ := by simp only [L05Odd.ρ]; norm_num
  refine sector_margin 1 le_rfl (by norm_num) _ _ _ _ _ (5 / 10 ^ 25) L05Odd.hDn hρ0 H
    b57_le ?_ ?_ ?_ N hN x
  · simp only [L05Odd.δ, L05Odd.ρ]; norm_num
  · norm_num
  · simp only [L05Odd.δ, L05Odd.ρ]; norm_num

/-- **Named hypothesis (Zhu analytic)**: in sector coordinates (index `i` ↔ Legendre order `2i + par`),
the Weil form `Q` dominates the reduced form on every truncation (Zhu Thm 1.1 / Lemma 3.1). -/
structure ZhuRed (Q : ℕ → ℕ → ℝ) (par : ℕ) (σ : ℝ) : Prop where
  red : ∀ N x, qf (Rm par σ wψ βs) x (range N) (range N) ≤ qf Q x (range N) (range N)

theorem pos_of_margin {Q R : ℕ → ℕ → ℝ} {m : ℝ} (hm : 0 < m) (N : ℕ)
    (hR : ∀ x : ℕ → ℝ, m * ∑ i ∈ range N, x i ^ 2 ≤ qf R x (range N) (range N))
    (hQ : ∀ x, qf R x (range N) (range N) ≤ qf Q x (range N) (range N))
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < qf Q x (range N) (range N) := by
  obtain ⟨i, hi, hxi⟩ := hx
  have hs : 0 < ∑ i ∈ range N, x i ^ 2 := lt_of_lt_of_le (by positivity) (sq_le_sum (x := x) hi)
  have := hR x; have := hQ x
  nlinarith [mul_pos hm hs]

/-- **L = 1/2, even sector.** -/
theorem L05_even_full (Q : ℕ → ℕ → ℝ) (Z : ZhuRed Q 0 1) (H : EvenHead) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < qf Q x (range N) (range N) :=
  pos_of_margin (by norm_num) N (even_margin H N hN) (Z.red N) x hx

/-- **L = 1/2, odd sector.** -/
theorem L05_odd_full (Q : ℕ → ℕ → ℝ) (Z : ZhuRed Q 1 (-1)) (H : OddHead) (N : ℕ) (hN : 28 ≤ N)
    (x : ℕ → ℝ) (hx : ∃ i ∈ range N, x i ≠ 0) : 0 < qf Q x (range N) (range N) :=
  pos_of_margin (by norm_num) N (odd_margin H N hN) (Z.red N) x hx

end WeilTailB
