import Mathlib
import BallRate
import DirMean

/-! # The rate of the orbit form from a gap hypothesis on the zeros

Plain statement. Under RH the orbit form is `Q_N(x) = Σ_ρ |V_x(ρ)|²/(¼ + γ²)` with `V_x(ρ) = Σ_{n ≤ N} x_n n^ρ`
(`BallRate.hasSum_form`), so a lower bound for `λ_N = min{Q_N(x) : Σ x_n² = 1}` is a lower bound for the Dirichlet
polynomial `V_x` sampled at the zeros. This module proves one from a hypothesis on the gaps between the zeros:

* `meanValue`: for `D(t) = Σ_{j ≤ N} c_j j^{−it}`, `|∫_a^b |D|² − (b − a)Σ|c_j|²| ≤ 2N²Σ|c_j|²`, both ways;
* `cells_bound`: for `F` with a continuous derivative and one point `γ_j` in each cell of length `h`,
  `∫|F|² ≤ 2hΣ_j|F(γ_j)|² + 2h²∫|F'|²`;
* `exists_sampling`: under RH, if every interval `[u, u + 1/(1 + log N))` with `T₁ ≤ u ≤ T₁ + L` contains the
  ordinate of a zero (`GapsOn N T₁ L`) and `L ≥ 12N² + 1`, the zeros in `[T₁, T₁ + L]` have
  `Σ|V_x(ρ)|² ≥ (L − 1)(1 + log N)/8·Σ x_n² n`. The polynomial is centred in frequency first, so that its derivative's
  coefficients carry `|log n − ½ log N| ≤ ½ log N`;
* `rate_of_gaps`: then `λ_N ≥ (1 + log N)/(80T₁)` when `GapsOn N T₁ T₁` and `T₁ ≥ 12N² + 2`;
* from a gap hypothesis at every height, `ZeroGaps g u₀` (from `u₀` on, every `[u, u + g(u))` contains an ordinate),
  three rates: `g(u) = K/log u` gives `λ_N ≥ (1 + log N)/(80·max(u₀, (eN)^K, 14N²))`, polynomial
  (`rate_of_gapsLog`, and `samplingAtZeros_of_gapsLog` derives `BallRate.SamplingAtZeros`);
  `g(u) = K/√(log u)` gives `exp(−K²(1 + log N)²)` up to the factor `(1 + log N)/80` (`rate_of_gapsSqrt`);
  `g(u) = K/log log u` gives `exp(−exp(K(1 + log N)))` up to that factor (`rate_of_gapsLogLog`).

The three gap hypotheses are statements about the zeros, not proved here. The last one holds under RH for suitable
`K` and `u₀` (Littlewood), so its rate is the one with RH as its only deep input; the second is what the random-matrix
model predicts for `K > √32`; the first is believed false for every fixed `K`. See `formalisations/ball-rate.md`.
-/

open Real Complex Finset MeasureTheory WeilForm WeilTest
open scoped ComplexConjugate

noncomputable section

namespace BallSampling

open DirMean

/-! ## The mean value theorem on `[1, N]`, both ways -/

/-- For `1 ≤ m < m' ≤ N`, `log m' − log m ≥ 1/N`. -/
lemma inv_le_log_sub {N m m' : ℕ} (hm : 1 ≤ m) (hmm : m < m') (hm' : m' ≤ N) :
    1 / (N : ℝ) ≤ Real.log m' - Real.log m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm'0 : (0 : ℝ) < m' := by exact_mod_cast (lt_of_lt_of_le hm hmm.le)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hm'0 hm0)
  rw [Real.log_div hm'0.ne' hm0.ne', inv_div] at h
  have hlt : (m : ℝ) + 1 ≤ m' := by exact_mod_cast hmm
  have hm'N : (m' : ℝ) ≤ N := by exact_mod_cast hm'
  have h2 : 1 / (N : ℝ) ≤ 1 - m / m' := by
    rw [one_sub_div hm'0.ne', div_le_div_iff₀ hN0 hm'0]
    nlinarith
  linarith

/-- For distinct `j, j' ∈ [1, N]`, `|log j' − log j| ≥ 1/N`. -/
lemma inv_le_abs_log_sub {N j j' : ℕ} (hj : j ∈ Icc 1 N) (hj' : j' ∈ Icc 1 N) (hne : j ≠ j') :
    1 / (N : ℝ) ≤ |Real.log j' - Real.log j| := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨hj'1, hj'2⟩ := Finset.mem_Icc.1 hj'
  have hN0 : (0 : ℝ) < 1 / N := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  rcases lt_or_gt_of_ne hne with h | h
  · have hk := inv_le_log_sub hj1 h hj'2
    rw [abs_of_pos (lt_of_lt_of_le hN0 hk)]
    exact hk
  · have hk := inv_le_log_sub hj'1 h hj2
    rw [abs_sub_comm, abs_of_pos (lt_of_lt_of_le hN0 hk)]
    exact hk

/-- **The mean value theorem on `[1, N]`, both ways**: for `D(t) = Σ_{j ≤ N} c_j j^{−it}`,
`|∫_a^b |D|² − (b − a)Σ|c_j|²| ≤ 2N²Σ|c_j|²`. Each off-diagonal integral is at most `2/|log j' − log j| ≤ 2N`, and
`(Σ|c_j|)² ≤ NΣ|c_j|²`. -/
theorem meanValue (N : ℕ) (c : ℕ → ℂ) (a b : ℝ) :
    |(∫ t in a..b, ‖dp (Icc 1 N) c t‖ ^ 2) - (b - a) * ∑ j ∈ Icc 1 N, ‖c j‖ ^ 2| ≤
      2 * (N : ℝ) ^ 2 * ∑ j ∈ Icc 1 N, ‖c j‖ ^ 2 := by
  set E : ℕ → ℕ → ℝ → ℂ := fun j j' t => c j * (starRingEnd ℂ) (c j')
      * Complex.exp (I * (((Real.log j' - Real.log j) * t : ℝ) : ℂ)) with hE
  have hcont : ∀ j j', Continuous (E j j') := fun j j' => by simp only [hE]; fun_prop
  have hc : Continuous fun t => ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, E j j' t := by fun_prop
  have hint : ∫ t in a..b, ‖dp (Icc 1 N) c t‖ ^ 2 = (∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, ∫ t in a..b, E j j' t).re := by
    simp_rw [sq_norm_dp]
    show ∫ t in a..b, (∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, E j j' t).re = _
    have key := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM
      (hc.intervalIntegrable (μ := volume) a b)
    simp only [Complex.reCLM_apply] at key
    rw [key]
    congr 1
    rw [intervalIntegral.integral_finsetSum fun j hj =>
      (continuous_finsetSum _ fun j' _ => hcont j j').intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [intervalIntegral.integral_finsetSum fun j' _ => (hcont j j').intervalIntegrable _ _]
  have hdiag : ∀ j, ∫ t in a..b, E j j t = (((b - a) * ‖c j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    simp only [hE, sub_self, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      intervalIntegral.integral_const, Complex.real_smul]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  set off : ℂ := ∑ j ∈ Icc 1 N, ∑ j' ∈ (Icc 1 N).erase j, ∫ t in a..b, E j j' t with hoff
  have hsplit : ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, ∫ t in a..b, E j j' t =
      ((∑ j ∈ Icc 1 N, (b - a) * ‖c j‖ ^ 2 : ℝ) : ℂ) + off := by
    rw [hoff, Complex.ofReal_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.add_sum_erase (Icc 1 N) _ hj, hdiag]
  have hbound : ∀ j ∈ Icc 1 N, ∀ j' ∈ (Icc 1 N).erase j, ‖∫ t in a..b, E j j' t‖ ≤ ‖c j‖ * ‖c j'‖ * (2 * N) := by
    intro j hj j' hj'
    obtain ⟨hne, hj'S⟩ := Finset.mem_erase.1 hj'
    simp only [hE]
    rw [intervalIntegral.integral_const_mul, norm_mul, norm_mul, Complex.norm_conj]
    have hlog := inv_le_abs_log_sub hj hj'S (Ne.symm hne)
    have hN0 : (0 : ℝ) < N := by
      have := (Finset.mem_Icc.1 hj).1
      exact_mod_cast (show 0 < N by have := (Finset.mem_Icc.1 hj).2; omega)
    have hl0 : 0 < |Real.log j' - Real.log j| := lt_of_lt_of_le (by positivity) hlog
    have hlne : Real.log j' - Real.log j ≠ 0 := fun h0 => by rw [h0, abs_zero] at hl0; exact lt_irrefl _ hl0
    have h1 := norm_integral_exp_le hlne a b
    have h2 : 2 / |Real.log j' - Real.log j| ≤ 2 * N := by
      rw [div_le_iff₀ hl0]
      have := (div_le_iff₀ hN0).1 hlog
      nlinarith
    calc ‖c j‖ * ‖c j'‖ * ‖∫ t in a..b, Complex.exp (I * (((Real.log j' - Real.log j) * t : ℝ) : ℂ))‖
        ≤ ‖c j‖ * ‖c j'‖ * (2 / |Real.log j' - Real.log j|) := by gcongr
      _ ≤ ‖c j‖ * ‖c j'‖ * (2 * N) := by gcongr
  have hcard : ((Icc 1 N).card : ℝ) = N := by rw [Nat.card_Icc]; push_cast; ring
  have hoffle : ‖off‖ ≤ 2 * (N : ℝ) ^ 2 * ∑ j ∈ Icc 1 N, ‖c j‖ ^ 2 := by
    have h1 : ‖off‖ ≤ ∑ j ∈ Icc 1 N, ∑ j' ∈ (Icc 1 N).erase j, ‖c j‖ * ‖c j'‖ * (2 * N) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j' hj' => hbound j hj j' hj'))
    have h2 : ∑ j ∈ Icc 1 N, ∑ j' ∈ (Icc 1 N).erase j, ‖c j‖ * ‖c j'‖ * (2 * N) ≤
        ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, ‖c j‖ * ‖c j'‖ * (2 * N) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun _ _ _ => by positivity
    have h3 : ∑ j ∈ Icc 1 N, ∑ j' ∈ Icc 1 N, ‖c j‖ * ‖c j'‖ * (2 * N) = 2 * N * (∑ j ∈ Icc 1 N, ‖c j‖) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j' _ => by ring
    have h4 : (∑ j ∈ Icc 1 N, ‖c j‖) ^ 2 ≤ (Icc 1 N).card * ∑ j ∈ Icc 1 N, ‖c j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    rw [hcard] at h4
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ‖off‖ ≤ 2 * N * (∑ j ∈ Icc 1 N, ‖c j‖) ^ 2 := by linarith
      _ ≤ 2 * N * (N * ∑ j ∈ Icc 1 N, ‖c j‖ ^ 2) := by gcongr
      _ = 2 * (N : ℝ) ^ 2 * ∑ j ∈ Icc 1 N, ‖c j‖ ^ 2 := by ring
  have key : (∫ t in a..b, ‖dp (Icc 1 N) c t‖ ^ 2) - (b - a) * ∑ j ∈ Icc 1 N, ‖c j‖ ^ 2 = off.re := by
    rw [hint]
    rw [hsplit, Complex.add_re, Complex.ofReal_re, Finset.mul_sum]
    ring
  rw [key]
  exact (Complex.abs_re_le_norm off).trans hoffle

/-! ## Discretisation on cells -/

/-- **Cauchy–Schwarz on an interval**: `(∫_u^v φ)² ≤ (v − u)∫_u^v φ²` for a continuous `φ ≥ 0`, from
`φ ≤ φ²/(2κ) + κ/2` at `κ = (∫φ)/(v − u)`. -/
lemma sq_integral_le {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : ∀ t, 0 ≤ φ t) {u v : ℝ} (huv : u ≤ v) :
    (∫ t in u..v, φ t) ^ 2 ≤ (v - u) * ∫ t in u..v, φ t ^ 2 := by
  set I1 := ∫ t in u..v, φ t with hI1def
  set I2 := ∫ t in u..v, φ t ^ 2 with hI2def
  have hI1 : 0 ≤ I1 := intervalIntegral.integral_nonneg huv fun t _ => h0 t
  have hI2 : 0 ≤ I2 := intervalIntegral.integral_nonneg huv fun t _ => sq_nonneg _
  have amgm : ∀ κ : ℝ, 0 < κ → I1 ≤ I2 / (2 * κ) + (v - u) * (κ / 2) := by
    intro κ hκ
    have hpt : ∀ t ∈ Set.Icc u v, φ t ≤ φ t ^ 2 / (2 * κ) + κ / 2 := fun t _ => by
      have : 0 ≤ (φ t - κ) ^ 2 := sq_nonneg _
      rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
      nlinarith
    have hc2 : Continuous fun t => φ t ^ 2 / (2 * κ) := (hφ.pow 2).div_const _
    have h := intervalIntegral.integral_mono_on (μ := volume) huv (hφ.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => φ t ^ 2 / (2 * κ) + κ / 2).intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_add (hc2.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume)),
      intervalIntegral.integral_div, intervalIntegral.integral_const, smul_eq_mul] at h
    exact h
  rcases hI1.eq_or_lt with h | h
  · rw [← h]
    have : 0 ≤ (v - u) * I2 := mul_nonneg (sub_nonneg.2 huv) hI2
    nlinarith
  · have hvu : 0 < v - u := by
      rcases (sub_nonneg.2 huv).eq_or_lt with h' | h'
      · exfalso
        have hv : v = u := by linarith
        have : I1 = 0 := by rw [hI1def, hv, intervalIntegral.integral_same]
        linarith
      · exact h'
    have hk := amgm (I1 / (v - u)) (div_pos h hvu)
    have e : (v - u) * (I1 / (v - u) / 2) = I1 / 2 := by field_simp
    rw [e] at hk
    have hk2 : I1 / 2 ≤ I2 / (2 * (I1 / (v - u))) := by linarith
    rw [le_div_iff₀ (by positivity)] at hk2
    have e2 : I1 / 2 * (2 * (I1 / (v - u))) = I1 ^ 2 / (v - u) := by field_simp
    rw [e2, div_le_iff₀ hvu] at hk2
    linarith

/-- **One cell**: for `F` with a continuous derivative and `γ ∈ [u, u + h]`,
`∫_u^{u+h} |F|² ≤ 2h|F(γ)|² + 2h²∫_u^{u+h} |F'|²`. -/
lemma cell_bound {F F' : ℝ → ℂ} (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F') {u h γ : ℝ}
    (hh : 0 ≤ h) (hγ1 : u ≤ γ) (hγ2 : γ ≤ u + h) :
    ∫ t in u..u + h, ‖F t‖ ^ 2 ≤ 2 * h * ‖F γ‖ ^ 2 + 2 * h ^ 2 * ∫ t in u..u + h, ‖F' t‖ ^ 2 := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  have huv : u ≤ u + h := by linarith
  set M := ∫ t in u..u + h, ‖F' t‖ with hM
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc u (u + h))] fun s => ‖F' s‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  have hni : IntervalIntegrable (fun s => ‖F' s‖) volume u (u + h) := hF'.norm.intervalIntegrable _ _
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg huv fun s _ => norm_nonneg _
  have hpt : ∀ t ∈ Set.Icc u (u + h), ‖F t‖ ^ 2 ≤ 2 * ‖F γ‖ ^ 2 + 2 * M ^ 2 := by
    intro t ht
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := γ) (b := t) (fun s _ => hF s)
      (hF'.intervalIntegrable _ _)
    have hdiff : ‖F t - F γ‖ ≤ M := by
      rw [← hftc]
      rcases le_total γ t with hγt | hγt
      · refine (intervalIntegral.norm_integral_le_integral_norm hγt).trans ?_
        exact intervalIntegral.integral_mono_interval hγ1 hγt ht.2 hnn hni
      · rw [intervalIntegral.integral_symm, norm_neg]
        refine (intervalIntegral.norm_integral_le_integral_norm hγt).trans ?_
        exact intervalIntegral.integral_mono_interval ht.1 hγt hγ2 hnn hni
    have h1 : ‖F t‖ ≤ ‖F γ‖ + M := by
      have := norm_le_insert' (F t) (F γ)
      linarith
    have h2 : ‖F t‖ ^ 2 ≤ (‖F γ‖ + M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖F γ‖ - M)]
  have hCS : M ^ 2 ≤ h * ∫ t in u..u + h, ‖F' t‖ ^ 2 := by
    have := sq_integral_le hF'.norm (fun t => norm_nonneg _) huv
    rwa [add_sub_cancel_left] at this
  have hI := intervalIntegral.integral_mono_on huv
    ((by fun_prop : Continuous fun t => ‖F t‖ ^ 2).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume)) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hI
  nlinarith

/-- **The cells**: with a point `γ_j` in each cell `[T₁ + jh, T₁ + jh + h]`, `j < J`,
`∫_{T₁}^{T₁+Jh} |F|² ≤ 2hΣ_j |F(γ_j)|² + 2h²∫_{T₁}^{T₁+Jh} |F'|²`. -/
theorem cells_bound {F F' : ℝ → ℂ} (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F') {T₁ h : ℝ}
    (hh : 0 ≤ h) (J : ℕ) (γ : ℕ → ℝ) (hγ : ∀ j < J, T₁ + j * h ≤ γ j ∧ γ j ≤ T₁ + j * h + h) :
    ∫ t in T₁..T₁ + J * h, ‖F t‖ ^ 2 ≤
      2 * h * ∑ j ∈ range J, ‖F (γ j)‖ ^ 2 + 2 * h ^ 2 * ∫ t in T₁..T₁ + J * h, ‖F' t‖ ^ 2 := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  have hsplit : ∀ g : ℝ → ℝ, Continuous g →
      ∫ t in T₁..T₁ + J * h, g t = ∑ j ∈ range J, ∫ t in T₁ + j * h..T₁ + j * h + h, g t := by
    intro g hg
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
      (a := fun j : ℕ => T₁ + j * h) (n := J) fun k _ => hg.intervalIntegrable _ _
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_succ] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  rw [hsplit _ (by fun_prop : Continuous fun t => ‖F t‖ ^ 2),
    hsplit _ (by fun_prop : Continuous fun t => ‖F' t‖ ^ 2), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j hj =>
    cell_bound hF hF' hh (hγ j (Finset.mem_range.1 hj)).1 (hγ j (Finset.mem_range.1 hj)).2

/-! ## The centred polynomial and the zeros -/

/-- The Dirichlet polynomial centred in frequency, `e^{iκt}·D(t)` with `κ = ½ log N`: its frequencies `κ − log j`
lie in `[−κ, κ]` for `1 ≤ j ≤ N`, and `|e^{iκt}D(t)| = |D(t)|`. -/
def dcen (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp (I * ((Real.log N / 2 * t : ℝ) : ℂ)) * dp (Icc 1 N) a t

/-- The coefficients `a_j·i(κ − log j)` of the derivative of the centred polynomial. -/
def dcoef (N : ℕ) (a : ℕ → ℂ) (j : ℕ) : ℂ := a j * (I * ((Real.log N / 2 - Real.log j : ℝ) : ℂ))

lemma dp_add_mul (S : Finset ℕ) (a a' : ℕ → ℂ) (w : ℂ) (t : ℝ) :
    w * dp S a t + dp S a' t = dp S (fun j => w * a j + a' j) t := by
  unfold dp
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma hasDerivAt_dcen (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (dcen N a)
      (Complex.exp (I * ((Real.log N / 2 * t : ℝ) : ℂ)) * dp (Icc 1 N) (dcoef N a) t) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((Real.log N / 2 * s : ℝ) : ℂ)) ((Real.log N / 2 : ℝ) : ℂ) t := by
    have := ((hasDerivAt_id' t).const_mul (Real.log N / 2)).ofReal_comp
    rwa [mul_one] at this
  have he := (h1.const_mul I).cexp
  have h := he.mul (hasDerivAt_dp (Icc 1 N) a t)
  unfold dcen
  convert h using 1
  have e : dp (Icc 1 N) (dcoef N a) t = (I * ((Real.log N / 2 : ℝ) : ℂ)) * dp (Icc 1 N) a t +
      dp (Icc 1 N) (fun j => a j * (-(I * (Real.log j : ℂ)))) t := by
    rw [dp_add_mul]
    congr 1
    funext j
    unfold dcoef
    push_cast
    ring
  rw [e]
  ring

lemma norm_dcen (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ‖dcen N a t‖ = ‖dp (Icc 1 N) a t‖ := by
  unfold dcen
  rw [norm_mul, norm_exp_I_mul, one_mul]

lemma norm_dcoef_sq_le (N : ℕ) (a : ℕ → ℂ) {j : ℕ} (hj : j ∈ Icc 1 N) :
    ‖dcoef N a j‖ ^ 2 ≤ (Real.log N / 2) ^ 2 * ‖a j‖ ^ 2 := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  unfold dcoef
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have h1 : 0 ≤ Real.log j := Real.log_natCast_nonneg j
  have h2 : Real.log j ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < j by omega)) (by exact_mod_cast hj2)
  have h3 : (Real.log N / 2 - Real.log j) ^ 2 ≤ (Real.log N / 2) ^ 2 := by nlinarith
  nlinarith [sq_nonneg ‖a j‖]

/-- Under RH, `n^ρ = √n·n^{iγ}`. -/
lemma pw_eq_of_rh (hRH : RiemannHypothesis) (q : ZIdx) {n : ℕ} (hn : 1 ≤ n) :
    BallLattice.pw q n =
      ((Real.sqrt n : ℝ) : ℂ) * Complex.exp (I * (((zetaZeroFamily q).im * Real.log n : ℝ) : ℂ)) := by
  have h := BallHadamard.zZF_sub_half hRH q
  unfold BallLattice.pw
  set L : ℝ := Real.log (n : ℝ) with hL
  have e : zetaZeroFamily q * (L : ℂ) = ((L / 2 : ℝ) : ℂ) + I * (((zetaZeroFamily q).im * L : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    linear_combination (L : ℂ) * h
  rw [e, Complex.exp_add, ← Complex.ofReal_exp, hL, BallPsi.exp_log_half (by exact_mod_cast hn)]

/-- Under RH, `V_x(ρ)` is the conjugate of `D(γ)` with the coefficients `x_n √n`. -/
lemma dpoly_eq_conj (hRH : RiemannHypothesis) (N : ℕ) (x : ℕ → ℝ) (q : ZIdx) :
    BallRate.dpoly N x q =
      conj (dp (Icc 1 N) (fun n => ((x n * Real.sqrt n : ℝ) : ℂ)) (zetaZeroFamily q).im) := by
  unfold BallRate.dpoly dp
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [pw_eq_of_rh hRH q (Finset.mem_Icc.1 hn).1, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have e : conj (-(I * (((zetaZeroFamily q).im * Real.log n : ℝ) : ℂ))) =
      I * (((zetaZeroFamily q).im * Real.log n : ℝ) : ℂ) := by
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [e]
  push_cast
  ring

/-- **Under RH, `|V_x(ρ)|` is the centred polynomial at `γ`.** -/
lemma norm_dpoly_eq (hRH : RiemannHypothesis) (N : ℕ) (x : ℕ → ℝ) (q : ZIdx) :
    ‖BallRate.dpoly N x q‖ = ‖dcen N (fun n => ((x n * Real.sqrt n : ℝ) : ℂ)) (zetaZeroFamily q).im‖ := by
  rw [dpoly_eq_conj hRH, Complex.norm_conj, norm_dcen]

lemma sum_norm_sq_coef (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ‖((x n * Real.sqrt n : ℝ) : ℂ)‖ ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 * n := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-! ## Sampling from the gaps -/

/-- **The gap hypothesis on a window** `[T₁, T₁ + L]` at the scale `1/(1 + log N)`: every interval
`[u, u + 1/(1 + log N))` with `T₁ ≤ u ≤ T₁ + L` contains the ordinate of a zero. A hypothesis. -/
def GapsOn (N : ℕ) (T₁ L : ℝ) : Prop :=
  ∀ u : ℝ, T₁ ≤ u → u ≤ T₁ + L →
    ∃ q : ZIdx, u ≤ (zetaZeroFamily q).im ∧ (zetaZeroFamily q).im < u + 1 / (1 + Real.log N)

/-- **Sampling from the gaps.** Under RH, if `GapsOn N T₁ L` with `L ≥ 12N² + 1`, a finite set `Z` of
zeros with ordinates in `[T₁, T₁ + L]` has `Σ_{ρ ∈ Z} |V_x(ρ)|² ≥ (L − 1)(1 + log N)/8·Σ x_n² n` for every real `x`.
One zero is taken in each cell of length `h = 1/(1 + log N)`; on the cells, `∫|D|² ≤ 2hΣ|D(γ)|² + 2h²∫|D'|²`
(`cells_bound`) for the polynomial centred in frequency, and the mean value theorem (`meanValue`) gives
`∫|D|² ≥ (Jh − 2N²)Σ|a|²` and `∫|D'|² ≤ (Jh + 2N²)(½ log N)²Σ|a|²`, where `2h²(½ log N)² ≤ ½`. -/
theorem exists_sampling (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {T₁ L : ℝ}
    (hL : 12 * (N : ℝ) ^ 2 + 1 ≤ L) (hG : GapsOn N T₁ L) :
    ∃ Z : Finset ZIdx, (∀ q ∈ Z, T₁ ≤ (zetaZeroFamily q).im ∧ (zetaZeroFamily q).im ≤ T₁ + L) ∧
      ∀ x : ℕ → ℝ, (L - 1) * (1 + Real.log N) / 8 * ∑ n ∈ Icc 1 N, x n ^ 2 * n ≤
        ∑ q ∈ Z, ‖BallRate.dpoly N x q‖ ^ 2 := by
  classical
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set h : ℝ := 1 / (1 + Real.log N) with hh
  have hh0 : 0 < h := by rw [hh]; positivity
  have hh1 : h ≤ 1 := by rw [hh, div_le_one (by positivity)]; linarith
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
  have hL0 : 0 < L := by linarith
  set J : ℕ := ⌊L / h⌋₊ with hJ
  have hJ1 : (J : ℝ) ≤ L / h := Nat.floor_le (by positivity)
  have hJ2 : L / h < J + 1 := Nat.lt_floor_add_one _
  have hJh : (J : ℝ) * h ≤ L := by rwa [le_div_iff₀ hh0] at hJ1
  have hJh' : L - h < (J : ℝ) * h := by
    rw [div_lt_iff₀ hh0] at hJ2
    linarith
  obtain ⟨q₀, -⟩ := hG T₁ le_rfl (by linarith)
  have hsel : ∀ j : ℕ, ∃ q : ZIdx, j < J →
      T₁ + j * h ≤ (zetaZeroFamily q).im ∧ (zetaZeroFamily q).im < T₁ + j * h + h := by
    intro j
    by_cases hj : j < J
    · have hjR : (j : ℝ) + 1 ≤ J := by exact_mod_cast hj
      have hj0 : (0 : ℝ) ≤ j * h := mul_nonneg (Nat.cast_nonneg j) hh0.le
      have hjJ : (j : ℝ) * h ≤ J * h := mul_le_mul_of_nonneg_right (by linarith) hh0.le
      obtain ⟨q, hq1, hq2⟩ := hG (T₁ + j * h) (by linarith) (by linarith)
      exact ⟨q, fun _ => ⟨hq1, hq2⟩⟩
    · exact ⟨q₀, fun h' => absurd h' hj⟩
  choose qs hqs using hsel
  have hinj : Set.InjOn qs (range J) := by
    intro j hj k hk hjk
    by_contra hne
    have hj' := hqs j (Finset.mem_range.1 hj)
    have hk' := hqs k (Finset.mem_range.1 hk)
    rw [hjk] at hj'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hlt
      have := mul_le_mul_of_nonneg_right this hh0.le
      linarith [hj'.2, hk'.1]
    · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      have := mul_le_mul_of_nonneg_right this hh0.le
      linarith [hj'.1, hk'.2]
  refine ⟨(range J).image qs, ?_, fun x => ?_⟩
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
    have hj' := hqs j (Finset.mem_range.1 hj)
    have hjR : (j : ℝ) + 1 ≤ J := by exact_mod_cast Finset.mem_range.1 hj
    have hj0 : (0 : ℝ) ≤ j * h := mul_nonneg (Nat.cast_nonneg j) hh0.le
    have hjJ : ((j : ℝ) + 1) * h ≤ J * h := mul_le_mul_of_nonneg_right hjR hh0.le
    exact ⟨by linarith [hj'.1], by linarith [hj'.2]⟩
  set a : ℕ → ℂ := fun n => ((x n * Real.sqrt n : ℝ) : ℂ) with ha
  set A := ∑ n ∈ Icc 1 N, ‖a n‖ ^ 2 with hA
  have hAx : A = ∑ n ∈ Icc 1 N, x n ^ 2 * n := sum_norm_sq_coef N x
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => by positivity
  set F' : ℝ → ℂ := fun t =>
    Complex.exp (I * ((Real.log N / 2 * t : ℝ) : ℂ)) * dp (Icc 1 N) (dcoef N a) t with hF'
  have hFd : ∀ t, HasDerivAt (dcen N a) (F' t) t := fun t => hasDerivAt_dcen N a t
  have hF'c : Continuous F' := by
    simp only [hF']
    exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (I * ((Real.log N / 2 * t : ℝ) : ℂ))).mul
      (continuous_dp _ _)
  have hcells := cells_bound hFd hF'c hh0.le J (fun j => (zetaZeroFamily (qs j)).im)
    fun j hj => ⟨(hqs j hj).1, (hqs j hj).2.le⟩
  have hI1 : ∫ t in T₁..T₁ + J * h, ‖dcen N a t‖ ^ 2 = ∫ t in T₁..T₁ + J * h, ‖dp (Icc 1 N) a t‖ ^ 2 := by
    simp only [norm_dcen]
  have hI2 : ∫ t in T₁..T₁ + J * h, ‖F' t‖ ^ 2 =
      ∫ t in T₁..T₁ + J * h, ‖dp (Icc 1 N) (dcoef N a) t‖ ^ 2 := by
    simp only [hF', norm_mul, norm_exp_I_mul, one_mul]
  have hmv1 := meanValue N a T₁ (T₁ + J * h)
  have hmv2 := meanValue N (dcoef N a) T₁ (T₁ + J * h)
  rw [add_sub_cancel_left] at hmv1 hmv2
  have hB : ∑ n ∈ Icc 1 N, ‖dcoef N a n‖ ^ 2 ≤ (Real.log N / 2) ^ 2 * A := by
    rw [hA, Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn => norm_dcoef_sq_le N a hn
  have hS : ∑ j ∈ range J, ‖dcen N a (zetaZeroFamily (qs j)).im‖ ^ 2 =
      ∑ q ∈ (range J).image qs, ‖BallRate.dpoly N x q‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun j _ => by rw [norm_dpoly_eq hRH]
  rw [hI1, hI2, hS] at hcells
  set S0 := ∑ q ∈ (range J).image qs, ‖BallRate.dpoly N x q‖ ^ 2 with hS0
  set IF := ∫ t in T₁..T₁ + J * h, ‖dp (Icc 1 N) a t‖ ^ 2 with hIF
  set ID := ∫ t in T₁..T₁ + J * h, ‖dp (Icc 1 N) (dcoef N a) t‖ ^ 2 with hID
  set B := ∑ n ∈ Icc 1 N, ‖dcoef N a n‖ ^ 2 with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hS0 : 0 ≤ S0 := Finset.sum_nonneg fun _ _ => by positivity
  have hJh0 : 0 ≤ (J : ℝ) * h := by positivity
  have s1 : (J : ℝ) * h * A - 2 * (N : ℝ) ^ 2 * A ≤ IF := by linarith [(abs_le.1 hmv1).1]
  have s2 : ID ≤ (J : ℝ) * h * B + 2 * (N : ℝ) ^ 2 * B := by linarith [(abs_le.1 hmv2).2]
  have s3 : ID ≤ ((J : ℝ) * h + 2 * (N : ℝ) ^ 2) * ((Real.log N / 2) ^ 2 * A) := by
    have := mul_le_mul_of_nonneg_left hB (show 0 ≤ (J : ℝ) * h + 2 * (N : ℝ) ^ 2 by positivity)
    linarith
  have hhl : (h * Real.log N) ^ 2 ≤ 1 := by
    have e : h * Real.log N = Real.log N / (1 + Real.log N) := by rw [hh]; ring
    rw [e, div_pow, div_le_one (by positivity)]
    nlinarith
  have s4 : 2 * h ^ 2 * ID ≤ ((J : ℝ) * h + 2 * (N : ℝ) ^ 2) * A / 2 := by
    have e : 2 * h ^ 2 * (((J : ℝ) * h + 2 * (N : ℝ) ^ 2) * ((Real.log N / 2) ^ 2 * A)) =
        ((J : ℝ) * h + 2 * (N : ℝ) ^ 2) * A / 2 * (h * Real.log N) ^ 2 := by ring
    have hpos : 0 ≤ ((J : ℝ) * h + 2 * (N : ℝ) ^ 2) * A / 2 := by positivity
    calc 2 * h ^ 2 * ID ≤ 2 * h ^ 2 * (((J : ℝ) * h + 2 * (N : ℝ) ^ 2) * ((Real.log N / 2) ^ 2 * A)) :=
          mul_le_mul_of_nonneg_left s3 (by positivity)
      _ = ((J : ℝ) * h + 2 * (N : ℝ) ^ 2) * A / 2 * (h * Real.log N) ^ 2 := e
      _ ≤ ((J : ℝ) * h + 2 * (N : ℝ) ^ 2) * A / 2 * 1 := mul_le_mul_of_nonneg_left hhl hpos
      _ = ((J : ℝ) * h + 2 * (N : ℝ) ^ 2) * A / 2 := mul_one _
  have s5 : (J : ℝ) * h * A / 4 ≤ 2 * h * S0 := by
    have hJ12 : 12 * (N : ℝ) ^ 2 ≤ (J : ℝ) * h := by linarith
    have hp := mul_nonneg (sub_nonneg.2 hJ12) hA0
    linarith
  have s6 : (J : ℝ) * A / 8 ≤ S0 := by
    have e : (J : ℝ) * h * A / 4 = 2 * h * ((J : ℝ) * A / 8) := by ring
    rw [e] at s5
    exact le_of_mul_le_mul_left s5 (by positivity)
  have hJ3 : L * (1 + Real.log N) - 1 < J := by
    have e : L / h = L * (1 + Real.log N) := by rw [hh]; field_simp
    rw [e] at hJ2
    linarith
  rw [← hAx]
  have s7 : (L - 1) * (1 + Real.log N) / 8 * A ≤ (J : ℝ) * A / 8 := by
    have : (L - 1) * (1 + Real.log N) ≤ J := by linarith
    have := mul_le_mul_of_nonneg_right this hA0
    linarith
  linarith

/-- **The rate from the gaps.** Under RH, if `GapsOn N T₁ T₁` with `T₁ ≥ 12N² + 2`, then
`Q_N(x) ≥ (1 + log N)/(80T₁)·Σ x_n²` for every real `x`: `λ_N ≥ (1 + log N)/(80T₁)`. The zeros of `exists_sampling`
lie in `[T₁, 2T₁]`, where `¼ + γ² ≤ 5T₁²`. -/
theorem rate_of_gaps (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) {T₁ : ℝ}
    (hT₁ : 12 * (N : ℝ) ^ 2 + 2 ≤ T₁) (hG : GapsOn N T₁ T₁) (x : ℕ → ℝ) :
    (1 + Real.log N) / (80 * T₁) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x := by
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
  have hT0 : 2 ≤ T₁ := by linarith
  obtain ⟨Z, hZ, hS⟩ := exists_sampling hRH hN (by linarith) hG
  have hsum := BallRate.hasSum_form hRH N x
  have h1 : ∑ q ∈ Z, ‖BallRate.dpoly N x q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2) ≤
      BallWeil.form N x := by
    rw [← hsum.tsum_eq]
    exact Summable.sum_le_tsum Z (fun q _ => by positivity) hsum.summable
  have h2 : ∑ q ∈ Z, ‖BallRate.dpoly N x q‖ ^ 2 / (5 * T₁ ^ 2) ≤
      ∑ q ∈ Z, ‖BallRate.dpoly N x q‖ ^ 2 / (1 / 4 + (zetaZeroFamily q).im ^ 2) := by
    refine Finset.sum_le_sum fun q hq => div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    obtain ⟨hq1, hq2⟩ := hZ q hq
    have hg0 : 0 ≤ (zetaZeroFamily q).im := by linarith
    have hsq : (zetaZeroFamily q).im ^ 2 ≤ (2 * T₁) ^ 2 := pow_le_pow_left₀ hg0 (by linarith) 2
    nlinarith
  rw [← Finset.sum_div] at h2
  have h3 := hS x
  have hA : ∑ n ∈ Icc 1 N, x n ^ 2 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * n := Finset.sum_le_sum fun n hn => by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    nlinarith [sq_nonneg (x n)]
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set A := ∑ n ∈ Icc 1 N, x n ^ 2 * n with hAdef
  set A₀ := ∑ n ∈ Icc 1 N, x n ^ 2 with hA₀def
  set S0 := ∑ q ∈ Z, ‖BallRate.dpoly N x q‖ ^ 2 with hS0
  have hA₀ : 0 ≤ A₀ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT2 : 0 < 5 * T₁ ^ 2 := by positivity
  have k1 : (T₁ - 1) * (1 + Real.log N) / 8 * A / (5 * T₁ ^ 2) ≤ BallWeil.form N x :=
    (div_le_div_of_nonneg_right h3 hT2.le).trans (h2.trans h1)
  have k2 : (1 + Real.log N) / (80 * T₁) * A₀ ≤ (T₁ - 1) * (1 + Real.log N) / 8 * A / (5 * T₁ ^ 2) := by
    have hT1 : T₁ / 2 ≤ T₁ - 1 := by linarith
    have hm : T₁ / 2 * A₀ ≤ (T₁ - 1) * A := mul_le_mul hT1 hA hA₀ (by linarith)
    have hm2 := mul_le_mul_of_nonneg_left hm (show 0 ≤ (1 + Real.log N) * T₁ by positivity)
    have hT3 : (0 : ℝ) < 40 * T₁ ^ 3 := by positivity
    have e1 : (1 + Real.log N) / (80 * T₁) * A₀ = (1 + Real.log N) * T₁ * (T₁ / 2 * A₀) / (40 * T₁ ^ 3) := by
      field_simp
      ring
    have e2 : (T₁ - 1) * (1 + Real.log N) / 8 * A / (5 * T₁ ^ 2) =
        (1 + Real.log N) * T₁ * ((T₁ - 1) * A) / (40 * T₁ ^ 3) := by
      field_simp
      ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hm2 hT3.le
  exact k2.trans k1

/-! ## Gap hypotheses at every height -/

/-- **A gap hypothesis on the zeros**: from height `u₀` on, every interval `[u, u + g(u))` contains the ordinate of a
zero. A hypothesis. -/
def ZeroGaps (g : ℝ → ℝ) (u₀ : ℝ) : Prop :=
  ∀ u : ℝ, u₀ ≤ u → ∃ q : ZIdx, u ≤ (zetaZeroFamily q).im ∧ (zetaZeroFamily q).im < u + g u

lemma gapsOn_of_zeroGaps {g : ℝ → ℝ} {u₀ : ℝ} (hG : ZeroGaps g u₀) {N : ℕ} {T₁ L : ℝ} (hu₀ : u₀ ≤ T₁)
    (hg : ∀ u, T₁ ≤ u → g u ≤ 1 / (1 + Real.log N)) : GapsOn N T₁ L := by
  intro u hu1 _
  obtain ⟨q, hq1, hq2⟩ := hG u (hu₀.trans hu1)
  exact ⟨q, hq1, lt_of_lt_of_le hq2 (by linarith [hg u hu1])⟩

/-- **The rate from a gap hypothesis at every height**: under RH and `ZeroGaps g u₀`, for every `T₁ ≥ max(u₀, 14N²)`
from which on `g ≤ 1/(1 + log N)`, `Q_N(x) ≥ (1 + log N)/(80T₁)·Σ x_n²`. -/
theorem rate_of_zeroGaps (hRH : RiemannHypothesis) {g : ℝ → ℝ} {u₀ : ℝ} (hG : ZeroGaps g u₀) {N : ℕ}
    (hN : 1 ≤ N) {T₁ : ℝ} (hu₀ : u₀ ≤ T₁) (hT₁ : 14 * (N : ℝ) ^ 2 ≤ T₁)
    (hg : ∀ u, T₁ ≤ u → g u ≤ 1 / (1 + Real.log N)) (x : ℕ → ℝ) :
    (1 + Real.log N) / (80 * T₁) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
  exact rate_of_gaps hRH hN (by linarith) (gapsOn_of_zeroGaps hG hu₀ hg) x

/-- `K/log u ≤ 1/(1 + log N)` once `u ≥ e^{K(1 + log N)}`. -/
lemma log_gap_le {K : ℝ} (hK : 0 < K) {N : ℕ} {u : ℝ} (hu : Real.exp (K * (1 + Real.log N)) ≤ u) :
    K / Real.log u ≤ 1 / (1 + Real.log N) := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlog : K * (1 + Real.log N) ≤ Real.log u := by
    rw [← Real.log_exp (K * (1 + Real.log N))]
    exact Real.log_le_log (Real.exp_pos _) hu
  have hpos : 0 < K * (1 + Real.log N) := by positivity
  rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hlog) (by positivity), one_mul]
  exact hlog

/-- **Bounded normalised gaps give a polynomial rate**: under RH and `ZeroGaps (K/log u) u₀` with `K > 0`,
`λ_N ≥ (1 + log N)/(80·max(u₀, e^{K(1 + log N)}, 14N²))`; here `e^{K(1 + log N)} = (eN)^K`, so for `K > 2` and `N`
large `λ_N ≥ (1 + log N)/(80e^K N^K)`. The hypothesis says the gaps are at most `K/(2π)` times the mean spacing
`2π/log(u/2π)`; the random-matrix model predicts that the largest normalised gaps grow, so it is believed false for
every fixed `K`. -/
theorem rate_of_gapsLog (hRH : RiemannHypothesis) {K u₀ : ℝ} (hK : 0 < K)
    (hG : ZeroGaps (fun u => K / Real.log u) u₀) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (1 + Real.log N) / (80 * max u₀ (max (Real.exp (K * (1 + Real.log N))) (14 * (N : ℝ) ^ 2))) *
      ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x :=
  rate_of_zeroGaps hRH hG hN (le_max_left _ _)
    ((le_max_right (Real.exp (K * (1 + Real.log N))) _).trans (le_max_right u₀ _))
    (fun _ hu => log_gap_le hK ((le_max_left _ _).trans ((le_max_right u₀ _).trans hu))) x

/-- **Gaps `K/√(log u)` give a quasi-polynomial rate**: under RH and `ZeroGaps (K/√(log u)) u₀` with `K > 0`,
`λ_N ≥ (1 + log N)/(80·max(u₀, e^{K²(1 + log N)²}, 14N²))`. The random-matrix model predicts the largest gaps near
height `u` to be about `√(32 log u)/log u`, so this hypothesis is expected for every `K > √32` from some height on. -/
theorem rate_of_gapsSqrt (hRH : RiemannHypothesis) {K u₀ : ℝ} (hK : 0 < K)
    (hG : ZeroGaps (fun u => K / Real.sqrt (Real.log u)) u₀) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (1 + Real.log N) / (80 * max u₀ (max (Real.exp (K ^ 2 * (1 + Real.log N) ^ 2)) (14 * (N : ℝ) ^ 2))) *
      ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x := by
  refine rate_of_zeroGaps hRH hG hN (le_max_left _ _)
    ((le_max_right (Real.exp (K ^ 2 * (1 + Real.log N) ^ 2)) _).trans (le_max_right u₀ _)) (fun u hu => ?_) x
  have hu1 : Real.exp (K ^ 2 * (1 + Real.log N) ^ 2) ≤ u := (le_max_left _ _).trans ((le_max_right u₀ _).trans hu)
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlog : (K * (1 + Real.log N)) ^ 2 ≤ Real.log u := by
    rw [mul_pow, ← Real.log_exp (K ^ 2 * (1 + Real.log N) ^ 2)]
    exact Real.log_le_log (Real.exp_pos _) hu1
  have hpos : 0 < K * (1 + Real.log N) := by positivity
  have hsq : K * (1 + Real.log N) ≤ Real.sqrt (Real.log u) := by
    have := Real.sqrt_le_sqrt hlog
    rwa [Real.sqrt_sq hpos.le] at this
  show K / Real.sqrt (Real.log u) ≤ 1 / (1 + Real.log N)
  rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hsq) (by positivity), one_mul]
  exact hsq

/-- **Gaps `K/log log u` give a rate with RH as the only deep input**: under RH and `ZeroGaps (K/log log u) u₀` with
`K > 0`, `λ_N ≥ (1 + log N)/(80·max(u₀, e^{e^{K(1 + log N)}}, 14N²))`. Under RH the gaps near height `u` are
`O(1/log log u)` (Littlewood), so this hypothesis holds for suitable `K` and `u₀`; it is not proved here. -/
theorem rate_of_gapsLogLog (hRH : RiemannHypothesis) {K u₀ : ℝ} (hK : 0 < K)
    (hG : ZeroGaps (fun u => K / Real.log (Real.log u)) u₀) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (1 + Real.log N) / (80 * max u₀ (max (Real.exp (Real.exp (K * (1 + Real.log N)))) (14 * (N : ℝ) ^ 2))) *
      ∑ n ∈ Icc 1 N, x n ^ 2 ≤ BallWeil.form N x := by
  refine rate_of_zeroGaps hRH hG hN (le_max_left _ _)
    ((le_max_right (Real.exp (Real.exp (K * (1 + Real.log N)))) _).trans (le_max_right u₀ _))
    (fun u hu => ?_) x
  have hu1 : Real.exp (Real.exp (K * (1 + Real.log N))) ≤ u :=
    (le_max_left _ _).trans ((le_max_right u₀ _).trans hu)
  have hlog1 : Real.exp (K * (1 + Real.log N)) ≤ Real.log u := by
    rw [← Real.log_exp (Real.exp (K * (1 + Real.log N)))]
    exact Real.log_le_log (Real.exp_pos _) hu1
  exact log_gap_le hK hlog1

/-- **The sampling hypothesis of `BallRate` from bounded normalised gaps**: under RH, `ZeroGaps (K/log u) u₀` with
`K ≥ 2` gives `BallRate.SamplingAtZeros (1/32) (2e^K·max(u₀, 13)) (K − 1)`, so `BallRate.rate_of_sampling` applies.
For `T ≥ 2e^K·max(u₀, 13)·N^K` the window `[T/2, T]` satisfies `GapsOn`. -/
theorem samplingAtZeros_of_gapsLog (hRH : RiemannHypothesis) {K u₀ : ℝ} (hK : 2 ≤ K)
    (hG : ZeroGaps (fun u => K / Real.log u) u₀) :
    BallRate.SamplingAtZeros (1 / 32) (2 * Real.exp K * max u₀ 13) (K - 1) := by
  intro N x T hN hT
  rw [show (1 : ℝ) + (K - 1) = K by ring] at hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNK : 1 ≤ (N : ℝ) ^ K := Real.one_le_rpow hN1 (by linarith)
  have hNK2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ K := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)
  have heK : 1 ≤ Real.exp K := Real.one_le_exp (by linarith)
  have hM : (13 : ℝ) ≤ max u₀ 13 := le_max_right _ _
  have hMu : u₀ ≤ max u₀ 13 := le_max_left _ _
  have hexp : Real.exp (K * (1 + Real.log N)) = Real.exp K * (N : ℝ) ^ K := by
    rw [mul_add, mul_one, Real.exp_add, Real.rpow_def_of_pos (by linarith), mul_comm (Real.log N) K]
  have hP : max u₀ 13 ≤ Real.exp K * max u₀ 13 * (N : ℝ) ^ K := by
    have h1 : max u₀ 13 ≤ Real.exp K * max u₀ 13 := le_mul_of_one_le_left (by linarith) heK
    have h2 : 0 ≤ Real.exp K * max u₀ 13 := by positivity
    exact h1.trans (le_mul_of_one_le_right h2 hNK)
  have hT2 : Real.exp K * max u₀ 13 * (N : ℝ) ^ K ≤ T / 2 := by linarith
  have hu₀ : u₀ ≤ T / 2 := by linarith
  have hexpT : Real.exp (K * (1 + Real.log N)) ≤ T / 2 := by
    rw [hexp]
    have : Real.exp K * (N : ℝ) ^ K * 1 ≤ Real.exp K * (N : ℝ) ^ K * max u₀ 13 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hL : 12 * (N : ℝ) ^ 2 + 1 ≤ T / 2 := by
    have h13 : 13 * (N : ℝ) ^ K ≤ Real.exp K * max u₀ 13 * (N : ℝ) ^ K := by
      have : 13 ≤ Real.exp K * max u₀ 13 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
    linarith
  have hg : ∀ u, T / 2 ≤ u → K / Real.log u ≤ 1 / (1 + Real.log N) := fun u hu =>
    log_gap_le (by linarith) (hexpT.trans hu)
  obtain ⟨Z, hZ, hS⟩ := exists_sampling hRH hN hL (gapsOn_of_zeroGaps hG hu₀ hg)
  have hsub : Z ⊆ BallRate.zerosUpTo T := fun q hq => by
    rw [BallRate.mem_zerosUpTo]
    obtain ⟨h1, h2⟩ := hZ q hq
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h1 := hS x
  have h2 : ∑ q ∈ Z, ‖BallRate.dpoly N x q‖ ^ 2 ≤ ∑ q ∈ BallRate.zerosUpTo T, ‖BallRate.dpoly N x q‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hA0 : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * n := Finset.sum_nonneg fun n _ => by positivity
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hT4 : 4 ≤ T := by nlinarith
  have h3 : 1 / 32 * T * ∑ n ∈ Icc 1 N, x n ^ 2 * n ≤
      (T / 2 - 1) * (1 + Real.log N) / 8 * ∑ n ∈ Icc 1 N, x n ^ 2 * n := by
    have hk : 1 / 32 * T ≤ (T / 2 - 1) * (1 + Real.log N) / 8 := by nlinarith
    exact mul_le_mul_of_nonneg_right hk hA0
  linarith

end BallSampling
