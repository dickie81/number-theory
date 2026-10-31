import ShortSieveMoment
import ShortSieveTwist
import ShortSieveHolder
import ShortSieveInterval

/-!
# The pieces of the Type II estimates for products of primes in boxes

For a box `(N, M]`, `M ≤ 2N`, let `P(t) = Σ_{N<p≤M} (N/p)^{1/2} p^{−it}`, the Dirichlet polynomial `DirMean.dp` of the
primes of the box (`box`) with the weights of the line `Re s = 1/2`, normalised to modulus at most `1` (`boxWt`). For
boxes `(Nⱼ, Mⱼ]`, `j ∈ ι`, the tuples `(pⱼ)ⱼ` with `pⱼ` prime in `(Nⱼ, Mⱼ]` (`tuples`) have the products `prods`;
`cnt n` counts the tuples with product `n` (the Dirichlet convolution of the indicators of the boxes' primes). This
module proves, with no hypothesis (the analytic input beyond the large values estimates of `ShortSieveMoment` is the
zero-free half-plane `Re s > 11/12` behind `ShortSieveTwist`), the pieces of the Type II estimate that
`ShortSieveGroup` assembles:

* `norm_dp_boxWt_le_of`: `|P(t)| ≤ C N^{1−κ}` for `κ < 1/50` and `N^κ ≤ |t| ≤ N^A`: Abel summation
  (`ShortSieveTwist.norm_sum_mul_le`) with the nonincreasing weights over `ShortSieveTwist.norm_dp_primes_Ioc_le_of`,
  which is uniform in the endpoint;
* `pointwise_boxWt_of`: the same in the form of the hypothesis of `ShortSieveMoment`'s lemmas, `|P| ≤ N^{1−κ/2}` on
  the heights `N^κ ≤ |t| ≤ N^D` for `N` large; it depends on `|t|` only, so the negative heights need no reflection.
  `MomentOK D δ` says that `δ` is an admissible moment for those lemmas: `m < D ≤ m + 1/2` and `δ > 4D − 2m`, or
  `D ≤ k` and `δ > 2k`;
* `integral_prod_le`: Hölder's inequality `∫_a^b ∏ fⱼ ≤ ∏ Kⱼ` from `∫_a^b fⱼ^{δⱼ} ≤ Kⱼ^{δⱼ}`, `Σ 1/δⱼ = 1`
  (`ShortSieveHolder.lintegral_prod_le_of_moments` on `(a, b]`);
* `dp_prods`: the product formula `Σ_n cnt(n) n^{−1/2−it} = ∏ⱼ Nⱼ^{−1/2} Pⱼ(t)`, that is
  `A(s) = ∏ⱼ Σ_{Nⱼ<p≤Mⱼ} p^{−s}` on `Re s = 1/2` for `A(s) = Σ_n cnt(n) n^{−s}`; `sum_cnt_filter` counts the tuples
  by their products;
* the four terms of `ShortSieveInterval.norm_sum_Ioc_sub_le` for the coefficients `cnt` on `prods`: the middle range
  (`mid_term_le`), the low range (`sum_norm_coef_le`, `low_term_le_of`), the tail (`tail_term_le`) and the
  transitions (`trans_term_le`).
-/

open Finset Real MeasureTheory DirMean

noncomputable section

namespace ShortSieveTypeII

/-! ### The weighted prime polynomials -/

/-- The primes of `(N, M]`. -/
def box (N M : ℕ) : Finset ℕ := (Ioc N M).filter Nat.Prime

/-- The weights `(N/p)^{1/2}` of the line `Re s = 1/2`, normalised to modulus at most `1` on `(N, ∞)`. -/
def boxWt (N p : ℕ) : ℂ := ((((N : ℝ) / p) ^ (1 / 2 : ℝ) : ℝ) : ℂ)

/-- The primes of a box are positive. -/
lemma pos_of_mem_box {N M n : ℕ} (hn : n ∈ box N M) : 0 < n := (mem_filter.1 hn).2.pos

/-- **The weighted prime polynomial, pointwise, for a general exponent.** For `κ < 1/50` and `A > 0` there is `C`
with `|Σ_{N<p≤M} (N/p)^{1/2} p^{−it}| ≤ C N^{1−κ}` for all `N ≥ 2`, `N ≤ M ≤ 2N` and `N^κ ≤ |t| ≤ N^A`: Abel
summation (`ShortSieveTwist.norm_sum_mul_le`) with the nonincreasing weights `(N/n)^{1/2} ≤ 1` over the partial sums
`Σ_{N<p≤m} p^{−it}`, `N ≤ m ≤ M`, which `ShortSieveTwist.norm_dp_primes_Ioc_le_of` bounds uniformly in `m`. -/
theorem norm_dp_boxWt_le_of {κ A : ℝ} (hκ : κ < 1 / 50) (hA : 0 < A) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ M : ℕ, N ≤ M → M ≤ 2 * N → ∀ t : ℝ, (N : ℝ) ^ κ ≤ |t| → |t| ≤ (N : ℝ) ^ A →
      ‖dp (box N M) (boxWt N) t‖ ≤ C * (N : ℝ) ^ (1 - κ) := by
  obtain ⟨C, hC0, hC⟩ := ShortSieveTwist.norm_dp_primes_Ioc_le_of hκ hA
  refine ⟨C, hC0, fun N hN M hNM hM t ht1 ht2 => ?_⟩
  set a : ℕ → ℂ := fun n => if n.Prime then Complex.exp (-(Complex.I * ((t * Real.log n : ℝ) : ℂ))) else 0
    with ha
  set w : ℕ → ℝ := fun n => ((N : ℝ) / n) ^ (1 / 2 : ℝ) with hw
  have hdp : dp (box N M) (boxWt N) t = ∑ n ∈ Ioc N M, (w n : ℂ) * a n := by
    rw [dp, box, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    simp only [ha, hw, boxWt]
    split_ifs <;> simp
  have hpart : ∀ m, N ≤ m → m ≤ M → ‖∑ n ∈ Ioc N m, a n‖ ≤ C * (N : ℝ) ^ (1 - κ) := by
    intro m hNm hmM
    have e : ∑ n ∈ Ioc N m, a n = dp ((Ioc N m).filter Nat.Prime) (fun _ => 1) t := by
      rw [dp, sum_filter]
      refine sum_congr rfl fun n _ => ?_
      simp only [ha]
      split_ifs <;> simp
    rw [e]
    exact hC N hN m hNm (by omega) t ht1 ht2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hwmono : ∀ n, N < n → n ≤ M → w (n + 1) ≤ w n := by
    intro n hn _
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simp only [hw]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    exact div_le_div_of_nonneg_left hN0.le hn0 (by push_cast; linarith)
  have hw0 : 0 ≤ w (M + 1) := by simp only [hw]; positivity
  have hw1 : w (N + 1) ≤ 1 := by
    simp only [hw]
    refine Real.rpow_le_one (by positivity) ?_ (by norm_num)
    rw [div_le_one (by positivity)]
    push_cast
    linarith
  rw [hdp]
  calc ‖∑ n ∈ Ioc N M, (w n : ℂ) * a n‖ ≤ C * (N : ℝ) ^ (1 - κ) * w (N + 1) :=
        ShortSieveTwist.norm_sum_mul_le hNM hwmono hw0 hpart
    _ ≤ C * (N : ℝ) ^ (1 - κ) * 1 := by gcongr
    _ = C * (N : ℝ) ^ (1 - κ) := mul_one _

/-- The pointwise bound in the form of `ShortSieveMoment`'s hypothesis, with `η₁ = κ/2`, for both signs of `t`, on
the heights `N^κ ≤ |t| ≤ N^D`, `0 < κ < 1/50`, for `N` large: `norm_dp_boxWt_le_of`, with `C ≤ N^{κ/2}`. -/
lemma pointwise_boxWt_of {κ Dx : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 50) (hDx : 0 < Dx) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N → ∀ t : ℝ, (N : ℝ) ^ κ ≤ |t| →
      |t| ≤ (N : ℝ) ^ Dx → ‖dp (box N M) (boxWt N) t‖ ≤ (N : ℝ) ^ (1 - κ / 2) := by
  obtain ⟨C, hC0, hC⟩ := norm_dp_boxWt_le_of hκ hDx
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → C ≤ (N : ℝ) ^ (κ / 2) := by
    refine ⟨⌈C ^ (2 / κ)⌉₊, fun N hN => ?_⟩
    have hN' : C ^ (2 / κ) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    calc C = (C ^ (2 / κ)) ^ (κ / 2) := by
          rw [← Real.rpow_mul hC0, show 2 / κ * (κ / 2) = 1 by field_simp, Real.rpow_one]
      _ ≤ (N : ℝ) ^ (κ / 2) := Real.rpow_le_rpow (by positivity) hN' (by positivity)
  refine ⟨max N₁ 2, fun N hN M hNM hM t ht1 ht2 => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by positivity
  calc ‖dp (box N M) (boxWt N) t‖ ≤ C * (N : ℝ) ^ (1 - κ) := hC N hN2 M hNM hM t ht1 ht2
    _ ≤ (N : ℝ) ^ (κ / 2) * (N : ℝ) ^ (1 - κ) := by
        gcongr
        exact hN₁ N (le_trans (le_max_left _ _) hN)
    _ = (N : ℝ) ^ (1 - κ / 2) := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring

/-- `δ` is an admissible moment for heights up to `N^D`: `ShortSieveMoment.moment_le_hux` (`m < D ≤ m + 1/2`,
`δ > 4D − 2m`) or `ShortSieveMoment.moment_le_mv` (`D ≤ k`, `δ > 2k`) applies. -/
def MomentOK (D δ : ℝ) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) < D ∧ D ≤ m + 1 / 2 ∧ 4 * D - 2 * m < δ) ∨ (∃ k : ℕ, 1 ≤ k ∧ D ≤ k ∧ 2 * k < δ)

/-! ### Hölder's inequality on an interval -/

/-- **Hölder's inequality on an interval.** For continuous `fⱼ ≥ 0`, `δⱼ > 0` with `Σ 1/δⱼ = 1` and `Kⱼ ≥ 0`, if
`∫_a^b fⱼ^{δⱼ} ≤ Kⱼ^{δⱼ}` for every `j` then `∫_a^b ∏ fⱼ ≤ ∏ Kⱼ` (`ShortSieveHolder.lintegral_prod_le_of_moments`
on `(a, b]`). -/
theorem integral_prod_le {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, Continuous (f i))
    (hf0 : ∀ i ∈ s, ∀ t, 0 ≤ f i t) {a b : ℝ} (hab : a ≤ b) {δ : ι → ℝ} (hδ : ∀ i ∈ s, 0 < δ i)
    (hsum : ∑ i ∈ s, 1 / δ i = 1) {K : ι → ℝ} (hK : ∀ i ∈ s, 0 ≤ K i)
    (hmom : ∀ i ∈ s, ∫ t in a..b, f i t ^ δ i ≤ K i ^ δ i) :
    ∫ t in a..b, ∏ i ∈ s, f i t ≤ ∏ i ∈ s, K i := by
  rw [intervalIntegral.integral_of_le hab]
  have hint : Integrable (fun t => ∏ i ∈ s, f i t) (volume.restrict (Set.Ioc a b)) :=
    (continuous_finsetProd s fun i hi => hf i hi).integrableOn_Ioc
  have h0 : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] fun t => ∏ i ∈ s, f i t :=
    Filter.Eventually.of_forall fun t => prod_nonneg fun i hi => hf0 i hi t
  rw [← ENNReal.ofReal_le_ofReal_iff (prod_nonneg hK), ofReal_integral_eq_lintegral_ofReal hint h0,
    ENNReal.ofReal_prod_of_nonneg hK]
  have e1 : ∀ t, ENNReal.ofReal (∏ i ∈ s, f i t) = ∏ i ∈ s, ENNReal.ofReal (f i t) := fun t =>
    ENNReal.ofReal_prod_of_nonneg fun i hi => hf0 i hi t
  simp_rw [e1]
  refine ShortSieveHolder.lintegral_prod_le_of_moments s (fun i hi => ?_) hδ hsum fun i hi => ?_
  · exact (hf i hi).measurable.ennreal_ofReal.aemeasurable
  · have e2 : ∀ t, ENNReal.ofReal (f i t) ^ δ i = ENNReal.ofReal (f i t ^ δ i) := fun t =>
      ENNReal.ofReal_rpow_of_nonneg (hf0 i hi t) (hδ i hi).le
    simp_rw [e2]
    have hci : Continuous fun t => f i t ^ δ i := (hf i hi).rpow_const fun _ => Or.inr (hδ i hi).le
    rw [← ofReal_integral_eq_lintegral_ofReal hci.integrableOn_Ioc
      (Filter.Eventually.of_forall fun t => Real.rpow_nonneg (hf0 i hi t) _),
      ENNReal.ofReal_rpow_of_nonneg (hK i hi) (hδ i hi).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← intervalIntegral.integral_of_le hab]
    exact hmom i hi

/-! ### Products of primes in boxes -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tuples `(pⱼ)ⱼ` with `pⱼ` prime in `(Nⱼ, Mⱼ]`. -/
def tuples (N M : ι → ℕ) : Finset (ι → ℕ) := Fintype.piFinset fun j => box (N j) (M j)

/-- The products `∏ⱼ pⱼ` of the tuples. -/
def prods (N M : ι → ℕ) : Finset ℕ := (tuples N M).image fun g => ∏ j, g j

/-- The number of tuples with product `n`: the Dirichlet convolution of the indicators of the primes of the
boxes. -/
def cnt (N M : ι → ℕ) (n : ℕ) : ℂ := (#{g ∈ tuples N M | ∏ j, g j = n} : ℂ)

/-- The entries of a tuple are positive. -/
lemma pos_of_mem_tuples {N M : ι → ℕ} {g : ι → ℕ} (hg : g ∈ tuples N M) (j : ι) : 0 < g j :=
  pos_of_mem_box (Fintype.mem_piFinset.1 hg j)

/-- The products of the tuples are positive. -/
lemma pos_of_mem_prods {N M : ι → ℕ} {n : ℕ} (hn : n ∈ prods N M) : 0 < n := by
  obtain ⟨g, hg, rfl⟩ := mem_image.1 hn
  exact prod_pos fun j _ => pos_of_mem_tuples hg j

/-- Sums over the products, weighted by `cnt`, are sums over the tuples. -/
lemma sum_prods (N M : ι → ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ prods N M, cnt N M n * f n = ∑ g ∈ tuples N M, f (∏ j, g j) := by
  rw [prods, sum_comp f (fun g : ι → ℕ => ∏ j, g j)]
  refine sum_congr rfl fun n _ => ?_
  rw [cnt, nsmul_eq_mul]

/-- `(∏ⱼ gⱼ)^s = ∏ⱼ gⱼ^s` for natural numbers `gⱼ`. -/
lemma natCast_prod_cpow (g : ι → ℕ) (s : ℂ) : (((∏ j, g j : ℕ) : ℂ)) ^ s = ∏ j, ((g j : ℕ) : ℂ) ^ s := by
  suffices h : ∀ u : Finset ι, (((∏ j ∈ u, g j : ℕ) : ℂ)) ^ s = ∏ j ∈ u, ((g j : ℕ) : ℂ) ^ s from h univ
  intro u
  induction u using Finset.induction_on with
  | empty => simp [Complex.one_cpow]
  | insert j u hj ih =>
    rw [prod_insert hj, prod_insert hj, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih]

/-- `Σ_{N<p≤M} p^{−1/2−it} = N^{−1/2} Σ_{N<p≤M} (N/p)^{1/2} p^{−it}` for `N > 0`. -/
lemma sum_box_cpow {N M : ℕ} (hN : 0 < N) (t : ℝ) :
    ∑ p ∈ box N M, ((p : ℕ) : ℂ) ^ (-ShortSieveInterval.cl t) =
      (((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * dp (box N M) (boxWt N) t := by
  rw [dp, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [ShortSieveInterval.natCast_cpow_neg_cl (pos_of_mem_box hp), boxWt, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hN1 : (N : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  rw [Real.div_rpow hN0.le hp0, Real.rpow_neg hN0.le, Real.rpow_neg hp0]
  field_simp

/-- **The product formula.** For `Nⱼ > 0`, the Dirichlet polynomial of the products with the coefficients `cnt`
is the product of the weighted prime polynomials of the boxes on the line `Re s = 1/2`:
`Σ_n cnt(n) n^{−1/2−it} = ∏ⱼ Nⱼ^{−1/2} Σ_{Nⱼ<p≤Mⱼ} (Nⱼ/p)^{1/2} p^{−it}`, that is `A(s) = ∏ⱼ Σ_{Nⱼ<p≤Mⱼ} p^{−s}`
at `s = 1/2 + it` for `A(s) = Σ_n cnt(n) n^{−s}`. -/
theorem dp_prods (N M : ι → ℕ) (hN : ∀ j, 0 < N j) (t : ℝ) :
    dp (prods N M) (ShortSieveInterval.coef (cnt N M)) t =
      ∏ j, ((((N j : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * dp (box (N j) (M j)) (boxWt (N j)) t) := by
  rw [ShortSieveInterval.dp_coef (fun n hn => pos_of_mem_prods hn), sum_prods]
  simp_rw [natCast_prod_cpow]
  have h := prod_univ_sum (fun j => box (N j) (M j)) (fun _ p => ((p : ℕ) : ℂ) ^ (-ShortSieveInterval.cl t))
  rw [tuples, ← h]
  exact prod_congr rfl fun j _ => sum_box_cpow (hN j) t

/-- Counting the tuples by their products. -/
lemma sum_cnt_filter (N M : ι → ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ n ∈ (prods N M).filter P, cnt N M n = ((#{g ∈ tuples N M | P (∏ j, g j)} : ℕ) : ℂ) := by
  rw [card_eq_sum_card_fiberwise (f := fun g : ι → ℕ => ∏ j, g j) (t := (prods N M).filter P)]
  · push_cast
    refine sum_congr rfl fun n hn => ?_
    rw [cnt, filter_filter]
    congr 2
    refine filter_congr fun g _ => ?_
    constructor
    · intro h
      exact ⟨h ▸ (mem_filter.1 hn).2, h⟩
    · exact fun h => h.2
  · intro g hg
    have hg' := mem_filter.1 hg
    exact mem_filter.2 ⟨mem_image_of_mem _ hg'.1, hg'.2⟩

/-- `Σ_n |cnt(n)| n^{−1/2} ≤ (∏ⱼ Nⱼ)^{1/2}` for `Nⱼ > 0` and `Mⱼ ≤ 2Nⱼ`: at most `∏ⱼ Nⱼ` tuples, each product
exceeding `∏ⱼ Nⱼ`. -/
lemma sum_norm_coef_le (N M : ι → ℕ) (hN : ∀ j, 0 < N j) (hM : ∀ j, M j ≤ 2 * N j) :
    ∑ n ∈ prods N M, ‖ShortSieveInterval.coef (cnt N M) n‖ ≤ (∏ j, (N j : ℝ)) ^ (1 / 2 : ℝ) := by
  set P : ℝ := ∏ j, (N j : ℝ) with hP
  have hP0 : 0 < P := prod_pos fun j _ => by exact_mod_cast hN j
  have e : ∀ n, ‖ShortSieveInterval.coef (cnt N M) n‖ =
      (#{g ∈ tuples N M | ∏ j, g j = n} : ℕ) • ((n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    intro n
    rw [ShortSieveInterval.coef, norm_mul, cnt, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), nsmul_eq_mul]
  simp_rw [e]
  rw [prods, ← sum_comp (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) (fun g : ι → ℕ => ∏ j, g j)]
  have hterm : ∀ g ∈ tuples N M, ((∏ j, g j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ P ^ (-(1 / 2 : ℝ)) := by
    intro g hg
    refine Real.rpow_le_rpow_of_nonpos hP0 ?_ (by norm_num)
    rw [hP, Nat.cast_prod]
    refine prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => ?_
    exact_mod_cast (mem_Ioc.1 (mem_filter.1 (Fintype.mem_piFinset.1 hg j)).1).1.le
  have hcard : ((tuples N M).card : ℝ) ≤ P := by
    rw [tuples, Fintype.card_piFinset, hP, Nat.cast_prod]
    refine prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => ?_
    have h1 : (box (N j) (M j)).card ≤ N j := by
      refine (card_filter_le _ _).trans ?_
      rw [Nat.card_Ioc]
      have := hM j
      omega
    exact_mod_cast h1
  calc ∑ g ∈ tuples N M, ((∏ j, g j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ∑ _g ∈ tuples N M, P ^ (-(1 / 2 : ℝ)) :=
        sum_le_sum hterm
    _ = (tuples N M).card * P ^ (-(1 / 2 : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ P * P ^ (-(1 / 2 : ℝ)) := by gcongr
    _ = P ^ (1 / 2 : ℝ) := by
        have h := Real.rpow_add hP0 1 (-(1 / 2))
        rw [Real.rpow_one] at h
        rw [← h]
        norm_num

/-! ### The ranges of heights -/

/-! ### The four terms -/

/-- The middle range: `C₀(y/√x)(I₁ + I₂) ≤ 2C₀K y x^{−η}` when `I₁, I₂ ≤ K x^{1/2} x^{−η}`. -/
lemma mid_term_le {C₀ x y K η I₁ I₂ : ℝ} (hC₀ : 0 ≤ C₀) (hx : 0 < x) (hy : 0 ≤ y)
    (h₁ : I₁ ≤ K * x ^ (1 / 2 : ℝ) * x ^ (-η)) (h₂ : I₂ ≤ K * x ^ (1 / 2 : ℝ) * x ^ (-η)) :
    C₀ * (y / √x) * (I₁ + I₂) ≤ 2 * C₀ * K * y * x ^ (-η) := by
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  have hc : 0 ≤ C₀ * (y / √x) := by positivity
  calc C₀ * (y / √x) * (I₁ + I₂) ≤ C₀ * (y / √x) * (2 * (K * x ^ (1 / 2 : ℝ) * x ^ (-η))) := by
        gcongr
        linarith
    _ = 2 * C₀ * K * y * x ^ (-η) * (x ^ (1 / 2 : ℝ) / √x) := by ring
    _ = 2 * C₀ * K * y * x ^ (-η) := by rw [← Real.sqrt_eq_rpow, div_self hs.ne', mul_one]

/-- The low range for a general height: `C₀(1 + T₀)(y/√x)(y₁/x) I ≤ 4C₀ y x^{2κ₀−ρ}` for `T₀ = x^{κ₀}`, `κ₀ ≥ 0`,
`y₁ ≤ x^{1−ρ}` and `I ≤ 2T₀ x^{1/2}`. -/
lemma low_term_le_of {C₀ x y y₁ ρ κ₀ I : ℝ} (hC₀ : 0 ≤ C₀) (hx : 1 ≤ x) (hκ₀ : 0 ≤ κ₀) (hy : 0 ≤ y)
    (hy₁ : 0 ≤ y₁) (hy₁x : y₁ ≤ x ^ (1 - ρ)) (hI : I ≤ 2 * x ^ κ₀ * x ^ (1 / 2 : ℝ)) :
    C₀ * (1 + x ^ κ₀) * (y / √x) * (y₁ / x) * I ≤ 4 * C₀ * y * x ^ (2 * κ₀ - ρ) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.2 hx0
  have hT₀ : 1 ≤ x ^ κ₀ := Real.one_le_rpow hx hκ₀
  have hc : 0 ≤ C₀ * (1 + x ^ κ₀) * (y / √x) * (y₁ / x) := by positivity
  have hy₁' : y₁ / x ≤ x ^ (-ρ) := by
    rw [div_le_iff₀ hx0]
    calc y₁ ≤ x ^ (1 - ρ) := hy₁x
      _ = x ^ (-ρ) * x := by
          rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
  calc C₀ * (1 + x ^ κ₀) * (y / √x) * (y₁ / x) * I
      ≤ C₀ * (1 + x ^ κ₀) * (y / √x) * (y₁ / x) * (2 * x ^ κ₀ * x ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hI hc
    _ ≤ C₀ * (2 * x ^ κ₀) * (y / √x) * x ^ (-ρ) * (2 * x ^ κ₀ * x ^ (1 / 2 : ℝ)) := by
        gcongr
        linarith
    _ = 4 * C₀ * y * (x ^ κ₀ * x ^ κ₀ * x ^ (-ρ)) * (x ^ (1 / 2 : ℝ) / √x) := by ring
    _ = 4 * C₀ * y * x ^ (2 * κ₀ - ρ) := by
        have e : x ^ κ₀ * x ^ κ₀ * x ^ (-ρ) = x ^ (2 * κ₀ - ρ) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
          congr 1
          ring
        rw [← Real.sqrt_eq_rpow, div_self hs.ne', mul_one, e]

/-- The tail: with `ε = y x^{−1−κ/2}`, `T = x^{1−θ+κ}`, `x^θ ≤ y`, `1 ≤ y`, `L ≤ x^{1/2}` and `kκ ≥ 6 + κ`,
`C₀√x L ε^{−1}(2/(εT))^k ≤ C₀2^k y x^{−1}`. -/
lemma tail_term_le {C₀ x y θ κ L : ℝ} (hC₀ : 0 ≤ C₀) (hx : 1 ≤ x) (hy : x ^ θ ≤ y) (hy1 : 1 ≤ y)
    (hL : L ≤ x ^ (1 / 2 : ℝ)) {k : ℕ} (hk : 6 + κ ≤ k * κ) :
    C₀ * √x * L / (y * x ^ (-1 - κ / 2)) * (2 / (y * x ^ (-1 - κ / 2) * x ^ (1 - θ + κ))) ^ k ≤
      C₀ * 2 ^ k * y * x ^ (-1 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  set ε := y * x ^ (-1 - κ / 2) with hε
  have hε0 : 0 < ε := by positivity
  have hεT : x ^ (κ / 2) ≤ ε * x ^ (1 - θ + κ) := by
    calc x ^ (κ / 2) = x ^ θ * (x ^ (-1 - κ / 2) * x ^ (1 - θ + κ)) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
          ring_nf
      _ ≤ y * (x ^ (-1 - κ / 2) * x ^ (1 - θ + κ)) := by gcongr
      _ = ε * x ^ (1 - θ + κ) := by rw [hε]; ring
  have h2 : 2 / (ε * x ^ (1 - θ + κ)) ≤ 2 * x ^ (-(κ / 2)) := by
    rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hεT
  have h3 : (2 / (ε * x ^ (1 - θ + κ))) ^ k ≤ 2 ^ k * x ^ (-(k * κ / 2)) := by
    calc (2 / (ε * x ^ (1 - θ + κ))) ^ k ≤ (2 * x ^ (-(κ / 2))) ^ k := pow_le_pow_left₀ (by positivity) h2 k
      _ = 2 ^ k * x ^ (-(k * κ / 2)) := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ (-(κ / 2))), ← Real.rpow_mul hx0.le]
          ring_nf
  have h4 : C₀ * √x * L / ε ≤ C₀ * x ^ (2 + κ / 2) / y := by
    rw [Real.sqrt_eq_rpow, hε, div_le_div_iff₀ (by positivity) hy0]
    have e : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (2 + κ / 2) * x ^ (-1 - κ / 2) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      ring_nf
    calc C₀ * x ^ (1 / 2 : ℝ) * L * y ≤ C₀ * x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * y := by gcongr
      _ = C₀ * x ^ (2 + κ / 2) * (y * x ^ (-1 - κ / 2)) := by
          rw [mul_assoc C₀, e]
          ring
  have h5 : x ^ (2 + κ / 2) * x ^ (-(k * κ / 2)) ≤ x ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h6 : x ^ (-1 : ℝ) / y ≤ x ^ (-1 : ℝ) * y := by
    rw [div_le_iff₀ hy0, mul_assoc]
    have hyy : 1 ≤ y * y := by nlinarith
    calc x ^ (-1 : ℝ) = x ^ (-1 : ℝ) * 1 := (mul_one _).symm
      _ ≤ x ^ (-1 : ℝ) * (y * y) := mul_le_mul_of_nonneg_left hyy (by positivity)
  calc C₀ * √x * L / ε * (2 / (ε * x ^ (1 - θ + κ))) ^ k
      ≤ C₀ * x ^ (2 + κ / 2) / y * (2 ^ k * x ^ (-(k * κ / 2))) := by
        gcongr
    _ = C₀ * 2 ^ k * (x ^ (2 + κ / 2) * x ^ (-(k * κ / 2))) / y := by ring
    _ ≤ C₀ * 2 ^ k * x ^ (-1 : ℝ) / y := by gcongr
    _ = C₀ * 2 ^ k * (x ^ (-1 : ℝ) / y) := by ring
    _ ≤ C₀ * 2 ^ k * (x ^ (-1 : ℝ) * y) := by gcongr
    _ = C₀ * 2 ^ k * y * x ^ (-1 : ℝ) := by ring

/-- The transitions: with `B = C_B x^β`, `ε = y x^{−1−κ/2}`, `β ≤ κ/4` and `x^{2β} ≤ y`,
`8B(xε(k + 3) + 1) ≤ 8C_B(k + 4) y x^{−β}`. -/
lemma trans_term_le {CB x y κ β : ℝ} (k : ℕ) (hCB : 0 ≤ CB) (hx : 1 ≤ x) (hβ : β ≤ κ / 4)
    (hy : x ^ (2 * β) ≤ y) :
    8 * (CB * x ^ β) * (x * (y * x ^ (-1 - κ / 2)) * (k + 3) + 1) ≤ 8 * CB * (k + 4) * y * x ^ (-β) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have e1 : x * (y * x ^ (-1 - κ / 2)) * x ^ β = y * x ^ (β - κ / 2) := by
    have : x * x ^ (-1 - κ / 2) * x ^ β = x ^ (β - κ / 2) := by
      calc x * x ^ (-1 - κ / 2) * x ^ β = x ^ (1 : ℝ) * x ^ (-1 - κ / 2) * x ^ β := by rw [Real.rpow_one]
        _ = x ^ (β - κ / 2) := by
            rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
            ring_nf
    linear_combination y * this
  have h1 : x ^ (β - κ / 2) ≤ x ^ (-β) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h2 : x ^ β ≤ y * x ^ (-β) := by
    calc x ^ β = x ^ (2 * β) * x ^ (-β) := by rw [← Real.rpow_add hx0]; ring_nf
      _ ≤ y * x ^ (-β) := by gcongr
  have hk : (0 : ℝ) ≤ k + 3 := by positivity
  calc 8 * (CB * x ^ β) * (x * (y * x ^ (-1 - κ / 2)) * (k + 3) + 1)
      = 8 * CB * ((k + 3) * (x * (y * x ^ (-1 - κ / 2)) * x ^ β) + x ^ β) := by ring
    _ = 8 * CB * ((k + 3) * (y * x ^ (β - κ / 2)) + x ^ β) := by rw [e1]
    _ ≤ 8 * CB * ((k + 3) * (y * x ^ (-β)) + y * x ^ (-β)) := by
        have h3 : (k + 3 : ℝ) * (y * x ^ (β - κ / 2)) ≤ (k + 3) * (y * x ^ (-β)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hy0.le) hk
        exact mul_le_mul_of_nonneg_left (add_le_add h3 h2) (by positivity)
    _ = 8 * CB * (k + 4) * y * x ^ (-β) := by ring

/-! ### The Type II estimate -/

end ShortSieveTypeII

#print axioms ShortSieveTypeII.norm_dp_boxWt_le_of
#print axioms ShortSieveTypeII.integral_prod_le
#print axioms ShortSieveTypeII.dp_prods
#print axioms ShortSieveTypeII.sum_cnt_filter
