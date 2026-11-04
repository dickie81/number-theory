import Mathlib

/-!
# Lamzouri's random model for `L'/L(1, χ_D)` (milestone B2, unconditional)

Independent `X(n)` (`RandModel.law`): at a prime `p`, `0` with probability `1/(p+1)` and each of `±1` with
probability `p/(2(p+1))`; `0` at other `n`. The model `X = -Σ_p (log p) X(p)/(p - X(p))` (`RandModel.X`):

* `RandModel.ae_tendsto_X`: the partial sums converge almost surely (the centred sums are an `L¹`-bounded
  martingale, `RandModel.martingale`, bounded through Hoeffding's lemma);
* `RandModel.integrable_exp_X`, `RandModel.integrable_exp_abs_X`: `e^{tX}` and `e^{s|X|}` are integrable for every `t`, `s`;
* `RandModel.ν`, its law, with `RandModel.integrable_exp_abs_ν` and `RandModel.integrable_pow_ν`.
-/

namespace RandModel
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

/-- The weight of each of `±1` at `n`: `n/(2(n+1))` at a prime, `0` otherwise. -/
noncomputable def r (n : ℕ) : ℝ := if n.Prime then n / (2 * (n + 1)) else 0

theorem r_nonneg (n : ℕ) : 0 ≤ r n := by unfold r; split_ifs <;> positivity

theorem r_le (n : ℕ) : r n ≤ 1 / 2 := by
  unfold r; split_ifs
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · norm_num

/-- The law of `X(n)`: `0` with probability `1 - 2r(n)`, each of `±1` with probability `r(n)`. -/
noncomputable def law (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - 2 * r n) • Measure.dirac 0 + ENNReal.ofReal (r n) • (Measure.dirac 1 + Measure.dirac (-1))

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  constructor
  have h1 : 0 ≤ 1 - 2 * r n := by linarith [r_le n]
  simp only [law, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [one_add_one_eq_two, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (r_nonneg n), ← ENNReal.ofReal_add h1 (by linarith [r_nonneg n])]
  convert ENNReal.ofReal_one using 2; ring

theorem ae_law (n : ℕ) : ∀ᵐ y ∂law n, y = -1 ∨ y = 0 ∨ y = 1 := by
  rw [ae_iff]
  simp [law, Measure.dirac_apply]

/-- The `n`-th term of the model, `-(log n) y/(n - y)`. -/
noncomputable def g (n : ℕ) (y : ℝ) : ℝ := -Real.log n * y / (n - y)

theorem measurable_g (n : ℕ) : Measurable (g n) := by unfold g; fun_prop

theorem integral_law (n : ℕ) (f : ℝ → ℝ) :
    ∫ y, f y ∂law n = (1 - 2 * r n) * f 0 + r n * (f 1 + f (-1)) := by
  have h1 : 0 ≤ 1 - 2 * r n := by linarith [r_le n]
  have i0 : Integrable f (Measure.dirac (0:ℝ)) := integrable_dirac enorm_lt_top
  have i1 : Integrable f (Measure.dirac (1:ℝ)) := integrable_dirac enorm_lt_top
  have i2 : Integrable f (Measure.dirac (-1:ℝ)) := integrable_dirac enorm_lt_top
  rw [law, integral_add_measure (i0.smul_measure ENNReal.ofReal_ne_top)
    ((i1.add_measure i2).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_add_measure i1 i2, integral_dirac, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal (r_nonneg n)]
  simp only [smul_eq_mul]

theorem g_zero (n : ℕ) : g n 0 = 0 := by simp [g]

theorem g_small {n : ℕ} (hn : n < 2) (y : ℝ) : g n y = 0 := by
  interval_cases n <;> simp [g]

/-- The bound on `|g(n, ·)|` on `{-1, 0, 1}`. -/
noncomputable def β (n : ℕ) : ℝ := |g n 1| + |g n (-1)|

/-- The mean of the `n`-th term. -/
noncomputable def m (n : ℕ) : ℝ := r n * (g n 1 + g n (-1))

theorem integral_g (n : ℕ) : ∫ y, g n y ∂law n = m n := by
  rw [integral_law, g_zero, m]; ring

theorem log_div_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log n / (n - 1) ≤ 8 * ((n : ℝ) ^ (3 / 4 : ℝ))⁻¹ := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set a := (n : ℝ) ^ (1 / 4 : ℝ)
  set b := (n : ℝ) ^ (3 / 4 : ℝ)
  have hb : 0 < b := Real.rpow_pos_of_pos hn0 _
  have hab : a * b = n := by
    rw [← Real.rpow_add hn0]; norm_num
  have hlog : Real.log n ≤ 4 * a := by
    have := Real.log_le_rpow_div hn0.le (show (0:ℝ) < 1 / 4 by norm_num)
    rw [div_div_eq_mul_div, div_one] at this; linarith
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by linarith) hb]
  nlinarith

theorem β_le (n : ℕ) : β n ≤ 16 * ((n : ℝ) ^ (3 / 4 : ℝ))⁻¹ := by
  rcases lt_or_ge n 2 with hn | hn
  · rw [β, g_small hn, g_small hn]; simp; positivity
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have e1 : |g n 1| = Real.log n / (n - 1) := by
    rw [g, abs_div, abs_of_pos (by linarith : (0:ℝ) < n - 1)]; simp [abs_of_nonneg hl]
  have e2 : |g n (-1)| ≤ Real.log n / (n - 1) := by
    rw [g, abs_div, abs_of_pos (by linarith : (0:ℝ) < n - -1)]; simp only [mul_neg, mul_one, neg_neg, abs_of_nonneg hl]
    exact div_le_div_of_nonneg_left hl (by linarith) (by linarith)
  have := log_div_le hn
  rw [β, e1]; linarith

theorem summable_β_sq : Summable fun n => β n ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    ((Real.summable_nat_rpow_inv.2 (show (1:ℝ) < 3 / 2 by norm_num)).mul_left 256)
  have h0 : 0 ≤ β n := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h := pow_le_pow_left₀ h0 (β_le n) 2
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, inv_pow, ← Real.rpow_natCast ((n : ℝ) ^ (3 / 4 : ℝ)), ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

theorem abs_m_le (n : ℕ) : |m n| ≤ 16 * ((n : ℝ) ^ (7 / 4 : ℝ))⁻¹ := by
  rcases lt_or_ge n 2 with hn | hn
  · rw [m, g_small hn, g_small hn]; simp; positivity
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have e : g n 1 + g n (-1) = -(Real.log n / (n - 1)) * (2 / (n + 1)) := by
    have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (n : ℝ) - -1 ≠ 0 := by linarith
    have h3 : (n : ℝ) + 1 ≠ 0 := by linarith
    rw [g, g]; field_simp; ring
  have hL := log_div_le hn
  have hq : 0 ≤ Real.log n / (n - 1) := div_nonneg hl (by linarith)
  have h7 : (n : ℝ) ^ (7 / 4 : ℝ) = (n : ℝ) ^ (3 / 4 : ℝ) * n := by
    rw [← Real.rpow_add_one hn0.ne']; norm_num
  have hb : 0 < (n : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hn0 _
  rw [m, e, abs_mul, abs_mul, abs_neg, abs_of_nonneg hq, abs_of_nonneg (r_nonneg n),
    abs_of_pos (by positivity : (0:ℝ) < 2 / (n + 1)), h7, mul_inv]
  have hr := r_le n
  have h2 : 2 / ((n : ℝ) + 1) ≤ 2 * (n : ℝ)⁻¹ := by
    rw [div_le_iff₀ (by positivity)]; field_simp; linarith
  calc r n * (Real.log n / (n - 1) * (2 / (n + 1))) ≤ 1 * (8 * ((n : ℝ) ^ (3 / 4 : ℝ))⁻¹ * (2 * (n : ℝ)⁻¹)) := by
        gcongr; linarith
    _ = _ := by ring

theorem summable_m : Summable fun n => |m n| :=
  Summable.of_nonneg_of_le (fun n => abs_nonneg _) abs_m_le
    ((Real.summable_nat_rpow_inv.2 (show (1:ℝ) < 7 / 4 by norm_num)).mul_left 16)


/-! ### The probability space -/

/-- The sample space: one coordinate per `n`. -/
abbrev Ω := ℕ → ℝ

/-- The product of the laws `law n`. -/
noncomputable def P : Measure Ω := Measure.infinitePi law

instance : IsProbabilityMeasure P := by unfold P; infer_instance

theorem map_eval (n : ℕ) : P.map (fun ω => ω n) = law n := Measure.infinitePi_map_eval law n

theorem ae_coord (n : ℕ) : ∀ᵐ ω ∂P, ω n = -1 ∨ ω n = 0 ∨ ω n = 1 := by
  have := ae_law n
  rw [← map_eval] at this
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable this

theorem integral_coord (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) : ∫ ω, f (ω n) ∂P = ∫ y, f y ∂law n := by
  rw [← map_eval, integral_map (measurable_pi_apply n).aemeasurable hf.aestronglyMeasurable]

/-- The centred `n`-th term. -/
noncomputable def h (n : ℕ) (y : ℝ) : ℝ := g n y - m n

theorem measurable_h (n : ℕ) : Measurable (h n) := (measurable_g n).sub_const _

theorem indep : iIndepFun (fun n (ω : Ω) => h n (ω n)) P := iIndepFun_infinitePi (P := law) measurable_h

theorem abs_g_le (n : ℕ) {y : ℝ} (hy : y = -1 ∨ y = 0 ∨ y = 1) : |g n y| ≤ β n := by
  have h1 := abs_nonneg (g n 1); have h2 := abs_nonneg (g n (-1))
  rcases hy with rfl | rfl | rfl
  · simp only [β]; linarith
  · rw [g_zero, abs_zero]; exact add_nonneg h1 h2
  · simp only [β]; linarith

/-- The variance proxy `β(n)²`. -/
noncomputable def c (n : ℕ) : ℝ≥0 := ⟨β n ^ 2, sq_nonneg _⟩

theorem subG (n : ℕ) : HasSubgaussianMGF (fun ω : Ω => h n (ω n)) (c n) P := by
  have hb : ∀ᵐ ω ∂P, g n (ω n) ∈ Set.Icc (-β n) (β n) := by
    filter_upwards [ae_coord n] with ω hω
    exact abs_le.1 (abs_g_le n hω)
  have H : HasSubgaussianMGF (fun ω : Ω => g n (ω n) - P[fun ω : Ω => g n (ω n)]) _ P :=
    hasSubgaussianMGF_of_mem_Icc ((measurable_g n).comp (measurable_pi_apply n)).aemeasurable hb
  have e : P[fun ω : Ω => g n (ω n)] = m n := by
    rw [integral_coord n (measurable_g n), integral_g]
  have hβ : 0 ≤ β n := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have ec : ((‖β n - -β n‖₊ / 2) ^ 2 : ℝ≥0) = c n := by
    ext; change _ = β n ^ 2
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
    rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]; norm_num
  rw [e, ec] at H
  exact H

/-- The centred partial sums `S N = Σ_{n ≤ N} (g n (ω n) - m n)`. -/
noncomputable def S (N : ℕ) (ω : Ω) : ℝ := ∑ n ∈ range (N + 1), h n (ω n)

/-- The total variance proxy. -/
noncomputable def V : ℝ := ∑' n, β n ^ 2

theorem subG_S (N : ℕ) : HasSubgaussianMGF (S N) (∑ n ∈ range (N + 1), c n) P :=
  HasSubgaussianMGF.sum_of_iIndepFun indep (fun n _ => subG n)

theorem mgf_S_le (N : ℕ) (t : ℝ) : mgf (S N) P t ≤ Real.exp (V * t ^ 2 / 2) := by
  refine ((subG_S N).mgf_le t).trans (Real.exp_le_exp.2 ?_)
  have : ((∑ n ∈ range (N + 1), c n : ℝ≥0) : ℝ) ≤ V := by
    rw [NNReal.coe_sum]
    exact Summable.sum_le_tsum _ (fun n _ => sq_nonneg _) summable_β_sq
  have := mul_le_mul_of_nonneg_right this (sq_nonneg t)
  linarith

theorem abs_le_exp_add (x : ℝ) : |x| ≤ Real.exp (1 * x) + Real.exp ((-1) * x) := by
  have h1 := Real.add_one_le_exp |x|
  have h2 := Real.exp_pos x; have h3 := Real.exp_pos (-x)
  rcases abs_cases x with ⟨hx, -⟩ | ⟨hx, -⟩ <;> rw [hx] at h1 <;> simp <;> linarith

theorem eLpNorm_S_le (N : ℕ) : eLpNorm (S N) 1 P ≤ ENNReal.ofReal (2 * Real.exp (V / 2)) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hi : Integrable (fun ω => Real.exp (1 * S N ω) + Real.exp ((-1) * S N ω)) P :=
    ((subG_S N).integrable_exp_mul 1).add ((subG_S N).integrable_exp_mul (-1))
  calc ∫⁻ ω, ‖S N ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (1 * S N ω) + Real.exp ((-1) * S N ω)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (abs_le_exp_add _)
    _ = ENNReal.ofReal (mgf (S N) P 1 + mgf (S N) P (-1)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => by positivity),
          integral_add ((subG_S N).integrable_exp_mul 1) ((subG_S N).integrable_exp_mul (-1))]
        rfl
    _ ≤ ENNReal.ofReal (2 * Real.exp (V / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := mgf_S_le N 1; have := mgf_S_le N (-1)
        norm_num at *; linarith
  exact (subG_S N).aemeasurable.aestronglyMeasurable


/-! ### Almost sure convergence -/

/-- The filtration of the first coordinates. -/
noncomputable abbrev F : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace Ω) := Filtration.piLE (X := fun _ : ℕ => ℝ)

theorem adapted : StronglyAdapted F S := by
  intro N
  refine (Finset.measurable_sum _ fun n hn => (measurable_h n).comp ?_).stronglyMeasurable
  have hn' : n ∈ Set.Iic N := by
    rw [Finset.mem_range] at hn; exact Set.mem_Iic.2 (Nat.lt_succ_iff.1 hn)
  exact (measurable_pi_apply (⟨n, hn'⟩ : Set.Iic N)).comp (comap_measurable (Preorder.restrictLe N))

theorem indep_step (N : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : Ω => ω (N + 1)) inferInstance) (F N) P := by
  have hc : iIndepFun (fun n (ω : Ω) => ω n) P :=
    iIndepFun_infinitePi (P := law) (X := fun _ => id) (fun _ => measurable_id)
  have H := hc.indepFun_finset {N + 1} (Finset.Iic N) (by simp) (fun i => measurable_pi_apply i)
  have H' : Indep (MeasurableSpace.comap (fun ω : Ω => fun (i : ({N + 1} : Finset ℕ)) => ω i)
        (MeasurableSpace.pi : MeasurableSpace (({N + 1} : Finset ℕ) → ℝ)))
      (MeasurableSpace.comap (fun ω : Ω => fun (i : Finset.Iic N) => ω i)
        (MeasurableSpace.pi : MeasurableSpace (Finset.Iic N → ℝ))) P := H
  rw [F, Filtration.piLE_eq_comap_frestrictLe]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left H' ?_) le_rfl
  exact ((show Measurable fun z : ({N + 1} : Finset ℕ) → ℝ => z ⟨N + 1, by simp⟩ from
    measurable_pi_apply _).comp (comap_measurable (fun ω : Ω => fun (i : ({N + 1} : Finset ℕ)) => ω i))).comap_le

theorem integral_h (n : ℕ) : ∫ ω, h n (ω n) ∂P = 0 := by
  rw [integral_coord n (measurable_h n), integral_law]
  simp only [h, g_zero, m]; ring

theorem martingale : Martingale S F P := by
  refine martingale_of_condExp_sub_eq_zero_nat adapted (fun N => (subG_S N).integrable) fun N => ?_
  have e : S (N + 1) - S N = fun ω => h (N + 1) (ω (N + 1)) := by
    funext ω; simp [S, Finset.sum_range_succ _ (N + 1)]
  rw [e]
  refine (condExp_indep_eq (m₁ := MeasurableSpace.comap (fun ω : Ω => ω (N + 1)) inferInstance)
    (measurable_pi_apply (N + 1)).comap_le (F.le N)
    ((measurable_h _).comp (comap_measurable _)).stronglyMeasurable (indep_step N)).trans ?_
  exact Eventually.of_forall fun ω => by simp [integral_h]

theorem ae_S : ∀ᵐ ω ∂P, ∃ c, Tendsto (fun N => S N ω) atTop (𝓝 c) :=
  martingale.submartingale.exists_ae_tendsto_of_bdd (R := (2 * Real.exp (V / 2)).toNNReal) eLpNorm_S_le

/-- The partial sums of the model, `T N = Σ_{n < N} g n (ω n)`. -/
noncomputable def T (N : ℕ) (ω : Ω) : ℝ := ∑ n ∈ range N, g n (ω n)

theorem measurable_T (N : ℕ) : Measurable (T N) :=
  Finset.measurable_sum _ fun n _ => (measurable_g n).comp (measurable_pi_apply n)

theorem T_succ (N : ℕ) (ω : Ω) : T (N + 1) ω = S N ω + ∑ n ∈ range (N + 1), m n := by
  simp [T, S, h, Finset.sum_sub_distrib]

theorem ae_T : ∀ᵐ ω ∂P, ∃ c, Tendsto (fun N => T N ω) atTop (𝓝 c) := by
  filter_upwards [ae_S] with ω ⟨c, hc⟩
  refine ⟨c + ∑' n, m n, ?_⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  have hm := (summable_m.of_abs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  convert hc.add hm using 1
  funext N; simp [T_succ]

/-- **The random model** `X = Σ_n g n (X n) = -Σ_p (log p) X(p)/(p - X(p))` (Lamzouri), as an a.s. limit. -/
noncomputable def X (ω : Ω) : ℝ := limUnder atTop fun N => T N ω

theorem ae_tendsto_X : ∀ᵐ ω ∂P, Tendsto (fun N => T N ω) atTop (𝓝 (X ω)) := by
  filter_upwards [ae_T] with ω hω
  exact tendsto_nhds_limUnder hω

theorem aemeasurable_X : AEMeasurable X P :=
  aemeasurable_of_tendsto_metrizable_ae' (fun N => (measurable_T N).aemeasurable) ae_tendsto_X


/-! ### A finite moment generating function -/

/-- `Σ |m n|`. -/
noncomputable def M : ℝ := ∑' n, |m n|

theorem exp_T_le (t : ℝ) (N : ℕ) (ω : Ω) :
    Real.exp (t * T (N + 1) ω) ≤ Real.exp (|t| * M) * Real.exp (t * S N ω) := by
  rw [← Real.exp_add, Real.exp_le_exp, T_succ, mul_add, add_comm]
  have h1 : |∑ n ∈ range (N + 1), m n| ≤ M :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Summable.sum_le_tsum _ (fun n _ => abs_nonneg _) summable_m)
  have h2 : t * ∑ n ∈ range (N + 1), m n ≤ |t| * M := by
    calc t * ∑ n ∈ range (N + 1), m n ≤ |t * ∑ n ∈ range (N + 1), m n| := le_abs_self _
      _ = |t| * |∑ n ∈ range (N + 1), m n| := abs_mul _ _
      _ ≤ |t| * M := mul_le_mul_of_nonneg_left h1 (abs_nonneg t)
  linarith

/-- **Finite mgf.** `e^{tX}` is integrable for every real `t`. -/
theorem integrable_exp_X (t : ℝ) : Integrable (fun ω => Real.exp (t * X ω)) P := by
  set K := Real.exp (|t| * M) * Real.exp (V * t ^ 2 / 2)
  have hN : ∀ N, ∫⁻ ω, ENNReal.ofReal (Real.exp (t * T (N + 1) ω)) ∂P ≤ ENNReal.ofReal K := by
    intro N
    have hi := ((subG_S N).integrable_exp_mul t).const_mul (Real.exp (|t| * M))
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (t * T (N + 1) ω)) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (|t| * M) * Real.exp (t * S N ω)) ∂P :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (exp_T_le t N ω)
      _ = ENNReal.ofReal (Real.exp (|t| * M) * mgf (S N) P t) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => by positivity),
            integral_const_mul]; rfl
      _ ≤ ENNReal.ofReal K :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (mgf_S_le N t) (Real.exp_pos _).le)
  have hmeas : ∀ N, AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (t * T (N + 1) ω))) P := fun N =>
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_T _).const_mul t))).aemeasurable
  have hlim : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (t * X ω)) =
      liminf (fun N => ENNReal.ofReal (Real.exp (t * T (N + 1) ω))) atTop := by
    filter_upwards [ae_tendsto_X] with ω hω
    refine ((ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp
      ((hω.comp (tendsto_add_atTop_nat 1)).const_mul t))).liminf_eq.symm
  have hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P ≤ ENNReal.ofReal K := by
    rw [lintegral_congr_ae hlim]
    exact (lintegral_liminf_le' hmeas).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall hN))
  refine ⟨(Real.measurable_exp.comp_aemeasurable (aemeasurable_X.const_mul t)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  exact hfin.trans_lt ENNReal.ofReal_lt_top

/-- `e^{s|X|}` is integrable for every real `s`. -/
theorem integrable_exp_abs_X (s : ℝ) : Integrable (fun ω => Real.exp (s * |X ω|)) P := by
  refine ((integrable_exp_X s).add (integrable_exp_X (-s))).mono'
    (Real.measurable_exp.comp_aemeasurable (aemeasurable_X.abs.const_mul s)).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
  have h1 := Real.exp_pos (s * X ω); have h2 := Real.exp_pos (-s * X ω)
  rcases abs_cases (X ω) with ⟨hx, -⟩ | ⟨hx, -⟩ <;> rw [hx]
  · linarith
  · rw [show s * -X ω = -s * X ω by ring]; linarith


/-! ### The law of the model -/

/-- The law of `X`. -/
noncomputable def ν : ProbabilityMeasure ℝ := ⟨P.map X, (Measure.isProbabilityMeasure_map_iff aemeasurable_X).2 inferInstance⟩

theorem integrable_exp_abs_ν (s : ℝ) : Integrable (fun x => Real.exp (s * |x|)) (ν : Measure ℝ) :=
  (integrable_map_measure (by fun_prop) aemeasurable_X).2 (integrable_exp_abs_X s)

/-- Every moment of `ν` is finite. -/
theorem integrable_pow_ν (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) := by
  refine ((integrable_exp_abs_ν 1).const_mul (k.factorial : ℝ)).mono' (by fun_prop)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow, one_mul]
  have := Real.pow_div_factorial_le_exp _ (abs_nonneg x) k
  rwa [div_le_iff₀ (by positivity), mul_comm] at this

end RandModel
