import D2GS
import RandModel

/-!
# The main-term moments are the random model's (milestone B3, unconditional)

With `X(n) = ∏_p X(p)^{v_p(n)}` (`ModelMoments.Xm`) built from `RandModel`, `E[X(m)]` is `∏_{p ∣ m} p/(p+1)` for a
square `m` and `0` otherwise (`ModelMoments.integral_Xm`), so `E[(Σ_{n ∈ P} a_n X(n))^k]` is the square-term sum
(`ModelMoments.model_moment`). The density in the Granville–Soundararajan moment theorems is `(3/π²) ∏_{p ∣ r} p/(p+1)`
(`ModelMoments.dens_pos_eq`), so the moments over fundamental discriminants of each sign tend to `(3/π²)` times the
model's (`ModelMoments.moment_pos_model`, `ModelMoments.moment_neg_model`).
-/

namespace ModelMoments
open MeasureTheory ProbabilityTheory Filter Topology Finset
open GSFund GSEven GSDens GSUncond GSDelta GSNu RandModel

/-- The completely multiplicative extension `X(n) = ∏_p X(p)^{v_p(n)}`. -/
noncomputable def Xm (n : ℕ) (ω : Ω) : ℝ := n.factorization.prod fun p e => ω p ^ e

theorem Xm_one (ω : Ω) : Xm 1 ω = 1 := by simp [Xm]

theorem Xm_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (ω : Ω) : Xm (a * b) ω = Xm a ω * Xm b ω := by
  unfold Xm
  rw [Nat.factorization_mul ha hb, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

theorem Xm_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) (ω : Ω) :
    Xm (∏ i ∈ s, f i) ω = ∏ i ∈ s, Xm (f i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Xm_one]
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, Xm_mul (hf j (mem_insert_self _ _))
      (prod_ne_zero_iff.2 fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

theorem Xm_eq (n : ℕ) (ω : Ω) : Xm n ω = ∏ p ∈ n.primeFactors, ω p ^ n.factorization p := by
  rw [Xm, Finsupp.prod, Nat.support_factorization]

theorem measurable_Xm (n : ℕ) : Measurable (Xm n) := by
  have : Xm n = fun ω : Ω => ∏ p ∈ n.primeFactors, ω p ^ n.factorization p := funext (Xm_eq n)
  rw [this]; fun_prop

theorem ae_abs_le : ∀ᵐ ω ∂(RandModel.P), ∀ p, |ω p| ≤ 1 := by
  rw [ae_all_iff]; intro p
  filter_upwards [ae_coord p] with ω h
  rcases h with h | h | h <;> rw [h] <;> norm_num

theorem ae_abs_Xm_le (n : ℕ) : ∀ᵐ ω ∂(RandModel.P), |Xm n ω| ≤ 1 := by
  filter_upwards [ae_abs_le] with ω h
  rw [Xm_eq, abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun p _ => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (h p)

theorem integrable_Xm (n : ℕ) : Integrable (Xm n) RandModel.P :=
  Integrable.of_bound (measurable_Xm n).aestronglyMeasurable 1
    ((ae_abs_Xm_le n).mono fun ω h => by rwa [Real.norm_eq_abs])

theorem integral_pow_coord (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    ∫ ω, ω p ^ e ∂(RandModel.P) = if Even e then (p : ℝ) / (p + 1) else 0 := by
  rw [integral_coord p (by fun_prop : Measurable fun y : ℝ => y ^ e), integral_law, zero_pow he.ne']
  have hr : r p = p / (2 * (p + 1)) := by simp [r, hp]
  split_ifs with h
  · rw [h.neg_one_pow, hr]; field_simp; ring
  · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow]; ring

/-- **Expectation of `X(m)`**: `∏_{p ∣ m} p/(p+1)` if `m` is a square, `0` otherwise. -/
theorem integral_Xm (m : ℕ) (hm : m ≠ 0) :
    ∫ ω, Xm m ω ∂(RandModel.P) = if IsSquare m then gfac m else 0 := by
  have hX : (fun ω => Xm m ω) = fun ω : Ω => ∏ p : m.primeFactors, ω p ^ m.factorization p := by
    funext ω; rw [Xm_eq, ← prod_coe_sort]
  have hc : iIndepFun (fun (p : m.primeFactors) (ω : Ω) => ω p) RandModel.P :=
    (iIndepFun_infinitePi (P := law) (X := fun _ => id) (fun _ => measurable_id)).precomp
      Subtype.val_injective
  rw [hX, hc.integral_fun_prod_comp (f := fun (p : m.primeFactors) (y : ℝ) => y ^ m.factorization p)
    (fun _ => (measurable_pi_apply _).aemeasurable) (fun _ => by fun_prop)]
  have hi : ∀ p : m.primeFactors, ∫ ω, ω p ^ m.factorization p ∂(RandModel.P) =
      if Even (m.factorization p) then (p : ℝ) / (p + 1) else 0 := fun p =>
    integral_pow_coord p _ (Nat.prime_of_mem_primeFactors p.2)
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors p.2) hm
        (Nat.dvd_of_mem_primeFactors p.2))
  simp only [hi]
  split_ifs with hs
  · rw [Nat.isSquare_iff_even_factorization] at hs
    rw [gfac, ← Finset.prod_coe_sort m.primeFactors (fun p => (p : ℝ) / (p + 1))]
    exact prod_congr rfl fun p _ => by rw [ite_eq_left (hs p (Nat.prime_of_mem_primeFactors p.2))]
  · rw [Nat.isSquare_iff_even_factorization] at hs
    push Not at hs
    obtain ⟨p, hp, hodd⟩ := hs
    have hpm : p ∈ m.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, hm⟩
      by_contra h
      exact hodd (by rw [Nat.factorization_eq_zero_of_not_dvd h]; exact ⟨0, rfl⟩)
    exact prod_eq_zero (i := ⟨p, hpm⟩) (mem_univ _) (by rw [ite_eq_right hodd])


/-- **Moments of the model**: `E[(Σ_{n ∈ P} a_n X(n))^k] = Σ_{f, ∏ f square} ∏ a(f i) · ∏_{p ∣ ∏ f} p/(p+1)`. -/
theorem model_moment (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℝ) (k : ℕ) :
    ∫ ω, (∑ n ∈ P, a n * Xm n ω) ^ k ∂(RandModel.P) =
      ∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
        (∏ i, a (f i)) * gfac (∏ i, f i) := by
  classical
  have hne : ∀ f ∈ Fintype.piFinset (fun _ : Fin k => P), ∏ i, f i ≠ 0 := fun f hf =>
    prod_ne_zero_iff.2 fun i _ => (hP _ (Fintype.mem_piFinset.1 hf i)).ne'
  have e : ∀ ω, (∑ n ∈ P, a n * Xm n ω) ^ k =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => P), (∏ i, a (f i)) * Xm (∏ i, f i) ω := by
    intro ω
    rw [← Fin.prod_const, Finset.prod_univ_sum]
    refine sum_congr rfl fun f hf => ?_
    rw [Xm_prod univ f (fun i _ => (hP _ (Fintype.mem_piFinset.1 hf i)).ne'), ← prod_mul_distrib]
  simp_rw [e]
  rw [integral_finsetSum _ (fun f _ => (integrable_Xm _).const_mul _), sum_filter]
  refine sum_congr rfl fun f hf => ?_
  rw [integral_const_mul, integral_Xm _ (hne f hf)]
  split_ifs <;> simp

theorem gfac_sqrt {m : ℕ} (hm : IsSquare m) : gfac (Nat.sqrt m) = gfac m := by
  obtain ⟨s, rfl⟩ := hm
  rw [Nat.sqrt_eq]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · unfold gfac; rw [Nat.primeFactors_mul hs.ne' hs.ne', union_self]

theorem dens_pos_eq {r : ℕ} (hr : 0 < r) : GSUncond.dens GSLink.CpPos CpPos0 r = 3 / Real.pi ^ 2 * gfac r := by
  unfold GSUncond.dens; rw [dite_eq_left hr]
  exact tendsto_nhds_unique (Classical.choose_spec (Q_density GSLink.CpPos CpPos0 r hr)) (delta_pos_closed r hr)

theorem dens_neg_eq {r : ℕ} (hr : 0 < r) : GSUncond.dens GSLink.CpNeg CpNeg0 r = 3 / Real.pi ^ 2 * gfac r := by
  unfold GSUncond.dens; rw [dite_eq_left hr]
  exact tendsto_nhds_unique (Classical.choose_spec (Q_density GSLink.CpNeg CpNeg0 r hr)) (delta_neg_closed r hr)

open Classical in
theorem main_eq (Cp : ℕ → Prop) (hC0 : ¬ Cp 0)
    (hd : ∀ {r : ℕ}, 0 < r → GSUncond.dens Cp hC0 r = 3 / Real.pi ^ 2 * gfac r)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℝ) (k : ℕ) :
    (∑ f ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun f => IsSquare (∏ i, f i)),
        (∏ i, (a (f i) : ℂ)) * (GSUncond.dens Cp hC0 (Nat.sqrt (∏ i, f i)) : ℂ)) =
      ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ P, a n * Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ) := by
  rw [model_moment P hP a k, mul_sum]
  push_cast
  refine sum_congr rfl fun f hf => ?_
  have hsq := (mem_filter.1 hf).2
  have hpos : 0 < Nat.sqrt (∏ i, f i) := Nat.sqrt_pos.2 (Nat.pos_of_ne_zero
    (prod_ne_zero_iff.2 fun i _ => (hP _ (Fintype.mem_piFinset.1 (mem_filter.1 hf).1 i)).ne'))
  rw [hd hpos, gfac_sqrt hsq]
  push_cast; ring

/-- **B3, positive discriminants.** The `k`-th moment of `Σ_{n ∈ P} a_n χ_D(n)` over fundamental `D ∈ (0, x]`,
divided by `x`, tends to `(3/π²) E[(Σ_{n ∈ P} a_n X(n))^k]`. Unconditional. -/
theorem moment_pos_model (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun x : ℕ => ((x : ℂ))⁻¹ *
        ∑ d ∈ Ioc 0 x, (if fundPos d then (∑ p ∈ P, (a p : ℂ) * kron d p) ^ k else 0)) atTop
      (𝓝 ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ P, a n * Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ)) := by
  rw [← main_eq GSLink.CpPos CpPos0 dens_pos_eq P hP a k]
  convert moment_pos_unconditional P hP (fun n => (a n : ℂ)) k

/-- **B3, negative discriminants** (`D = -d`). Unconditional. -/
theorem moment_neg_model (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun x : ℕ => ((x : ℂ))⁻¹ *
        ∑ d ∈ Ioc 0 x, (if fundNeg d then (∑ p ∈ P, (a p : ℂ) * kron (-(d : ℤ)) p) ^ k else 0)) atTop
      (𝓝 ((3 / Real.pi ^ 2 * ∫ ω, (∑ n ∈ P, a n * Xm n ω) ^ k ∂(RandModel.P) : ℝ) : ℂ)) := by
  rw [← main_eq GSLink.CpNeg CpNeg0 dens_neg_eq P hP a k]
  convert moment_neg_unconditional P hP (fun n => (a n : ℂ)) k

end ModelMoments
