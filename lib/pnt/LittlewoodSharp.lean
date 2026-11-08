/-
# Littlewood's bounds for `L(1, χ)` with explicit constants, for every Dirichlet character

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`) and the port of its Mertens file
(`PNTMertens`).

Plain statement. For every Dirichlet character `χ ≠ 1` mod `N`, real or complex, with `ℓ = log log(N + 2)` and `γ`
Euler's constant, `e^{−γ−3/100}/(13(52 + ℓ)) ≤ |L(1, χ)| ≤ 13e^{γ+3/100}(52 + ℓ)` (`norm_LFunction_one_bounds_sharp`).
As `N → ∞` the upper bound is `13e^{γ+3/100}(1 + o(1)) log log N`, where Littlewood's bound under GRH is
`2e^γ log log N`: the zero-free half-plane `Re s > 11/12` (through `ExplicitConstants.psiChi_le_explicit`), used in
place of GRH, costs the factor `13 = 1/(1 − 12/13)`. It replaces the constants `e^{±2·10²¹}` of `ExplicitConstants`, and holds for complex `χ` as well as quadratic.
No hypothesis.

The argument. For `σ > 1`, `log |L(σ, χ)| = Re Σ χ(n)Λ(n)/(n^σ log n)` (Mathlib's
`DirichletCharacter.LSeries_eq_exp_LSeries`). The terms `n ≤ x` have absolute value at most
`Σ_{n ≤ x} Λ(n)/(n log n) = log log x + γ + E₂(x)`, `|E₂(x)| ≤ (log 4 + 6)/log x` (Mertens' second theorem,
`PNTMertens`). The terms `n > x` have partial sums that vanish below `x` and, by Abel summation against
`|ψ(t, χ)| ≤ B t^θ`, are at most `B t^θ(2/log x + 1/(θ log² x))` beyond; so they sum to at most
`σ K x^{θ−σ}/(σ − θ) ≤ K x^{θ−1}/(1 − θ)`. The bound passes to `σ = 1` by continuity. At `θ = 12/13` (the half-plane
with `η = 1/156`) and `x = (e⁵² log(N + 2))¹³`, `log x = 13(52 + ℓ)`, the tail is below `0.019` and `E₂(x)` below
`0.011`.

* `norm_LFunction_eq`: `|L(s, χ)| = exp Re L(χΛ/log, s)` for `Re s > 1`.
* `norm_head_le`: the terms `n ≤ Y` are at most `Σ_{n ≤ Y} Λ(n)/(n log n)` for `σ ≥ 1`.
* `norm_LSeries_le_of_vanish`: partial summation for an L-series whose partial sums vanish up to `x` and are at most
  `K t^α` beyond: `|L(f, σ)| ≤ σ K x^{α−σ}/(σ − α)`.
* `norm_sum_Ioc_lc_le`: Abel summation for `Σ_{x < k ≤ t} χ(k)Λ(k)/log k`.
* `re_LSeries_lc_le`, `norm_LFunction_one_bounds_of`: the bound for `σ > 1`, then at `σ = 1`, from any
  `|ψ(t, χ)| ≤ B t^θ` and any `x ≥ 2`.
* `norm_LFunction_one_bounds_sharp`: the constants.
-/
import PNTMertens
import ExplicitConstants

set_option lang.lemmaCmd true

open Complex Set Filter Topology MeasureTheory Asymptotics
open ArithmeticFunction (vonMangoldt vonMangoldt_nonneg vonMangoldt_le_log)

namespace LittlewoodSharp

open ChiPNT

section General

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-! ### The coefficients of `log L(s, χ)` -/

/-- The coefficients `χ(n)Λ(n)/log n` of `log L(s, χ)`. -/
noncomputable def lc (n : ℕ) : ℂ := χ n * (vonMangoldt n : ℂ) / (Real.log n : ℂ)

lemma vm_div_log_nonneg (n : ℕ) : 0 ≤ vonMangoldt n / Real.log n :=
  div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)

/-- `Λ(n)/log n ≤ 1`. -/
lemma vm_div_log_le_one (n : ℕ) : vonMangoldt n / Real.log n ≤ 1 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast h)
    rw [div_le_one hlog]
    exact vonMangoldt_le_log

lemma norm_lc (n : ℕ) : ‖lc χ n‖ ≤ vonMangoldt n / Real.log n := by
  unfold lc
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
    Real.norm_of_nonneg (Real.log_natCast_nonneg n), mul_div_assoc]
  exact mul_le_of_le_one_left (vm_div_log_nonneg n) (DirichletCharacter.norm_le_one χ n)

lemma norm_lc_le_one (n : ℕ) : ‖lc χ n‖ ≤ 1 := (norm_lc χ n).trans (vm_div_log_le_one n)

/-- **`|L(s, χ)| = exp Re Σ χ(n)Λ(n)/(n^s log n)`** for `Re s > 1`, from the Euler product
(Mathlib's `DirichletCharacter.LSeries_eq_exp_LSeries`). -/
lemma norm_LFunction_eq [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ = Real.exp (LSeries (lc χ) s).re := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, ← DirichletCharacter.LSeries_eq_exp_LSeries χ hs,
    Complex.norm_exp]
  rfl

/-! ### Head and tail -/

/-- The terms `n > Y`. -/
noncomputable def tl (Y n : ℕ) : ℂ := if Y < n then lc χ n else 0

/-- The terms `n ≤ Y`. -/
noncomputable def hd (Y n : ℕ) : ℂ := if n ≤ Y then lc χ n else 0

lemma LSeries_lc_split {s : ℂ} (hs : 1 < s.re) (Y : ℕ) :
    LSeries (lc χ) s = (∑ n ∈ Finset.Icc 1 Y, lc χ n / (n : ℂ) ^ s) + LSeries (tl χ Y) s := by
  have hsT : LSeriesSummable (tl χ Y) s := LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (fun n _ ↦ by unfold tl; split_ifs; exacts [norm_lc_le_one χ n, by simp]) hs
  have hsH : LSeriesSummable (hd χ Y) s := LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (fun n _ ↦ by unfold hd; split_ifs; exacts [norm_lc_le_one χ n, by simp]) hs
  have hadd : lc χ = hd χ Y + tl χ Y := by
    funext n
    simp only [Pi.add_apply, hd, tl]
    split_ifs <;> first | omega | simp
  have hH : LSeries (hd χ Y) s = ∑ n ∈ Finset.Icc 1 Y, lc χ n / (n : ℂ) ^ s := by
    rw [LSeries, tsum_eq_sum (s := Finset.Icc 1 Y)]
    · refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hn1 : n ≠ 0 := by simp at hn; omega
      have hnY : n ≤ Y := by simp at hn; omega
      rw [LSeries.term_def, ite_eq_right hn1, hd, ite_eq_left hnY]
    · intro n hn
      rw [LSeries.term_def]
      split_ifs with h0
      · rfl
      · simp only [Finset.mem_Icc, not_and, not_le] at hn
        rw [hd, ite_eq_right (by omega), zero_div]
  conv_lhs => rw [hadd]
  rw [LSeries_add hsH hsT, hH]

/-- The terms `n ≤ Y` are at most `Σ_{n ≤ Y} Λ(n)/(n log n)` for `σ ≥ 1`. -/
lemma norm_head_le {σ : ℝ} (hσ : 1 ≤ σ) (Y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 Y, lc χ n / (n : ℂ) ^ (σ : ℂ)‖ ≤
      ∑ n ∈ Finset.Icc 1 Y, vonMangoldt n / (n * Real.log n) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega), Complex.ofReal_re]
  calc ‖lc χ n‖ / (n : ℝ) ^ σ ≤ (vonMangoldt n / Real.log n) / n := by
        apply div_le_div₀ (vm_div_log_nonneg n) (norm_lc χ n) hn0
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hσ
    _ = vonMangoldt n / (n * Real.log n) := by rw [div_div, mul_comm (Real.log n)]

end General

/-! ### Partial summation for an L-series whose partial sums vanish up to `x` -/

/-- **Partial summation with vanishing partial sums.** If the partial sums of `f` vanish for `t ≤ x` and are at most
`K t^α` for `t > x`, with `0 ≤ α < σ`, `x ≥ 1`, and `L(f, σ)` converges absolutely, then
`|L(f, σ)| ≤ σ K x^{α−σ}/(σ − α)`. -/
theorem norm_LSeries_le_of_vanish {f : ℕ → ℂ} {α σ K x : ℝ} (hα : 0 ≤ α) (hασ : α < σ) (hx : 1 ≤ x)
    (hK : 0 ≤ K) (hS : LSeriesSummable f σ)
    (hb : ∀ t : ℝ, 1 ≤ t → ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤ (Ioi x).indicator (fun t ↦ K * t ^ α) t) :
    ‖LSeries f σ‖ ≤ σ * K * x ^ (α - σ) / (σ - α) := by
  have hσ : 0 < σ := by linarith
  have hx0 : 0 < x := by linarith
  have hb' : ∀ t : ℝ, 1 ≤ t → ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤ K * t ^ α := fun t ht ↦ by
    refine (hb t ht).trans ?_
    by_cases h : t ∈ Ioi x
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      exact mul_nonneg hK (Real.rpow_nonneg (by linarith) _)
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ α := by
    refine IsBigO.of_bound K ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := hb' n (by exact_mod_cast hn)
    rw [Nat.floor_natCast] at h
    rwa [Real.norm_of_nonneg (by positivity)]
  rw [LSeries_eq_mul_integral f hα (by simpa using hασ) hS hO, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hσ.le, mul_assoc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hσ.le
  set g : ℝ → ℝ := (Ioi x).indicator (fun t ↦ K * t ^ (α - σ - 1)) with hgdef
  have hg : IntegrableOn (fun t : ℝ ↦ K * t ^ (α - σ - 1)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx0).const_mul K
  have hint : IntegrableOn g (Ioi 1) := (hg.integrable_indicator measurableSet_Ioi).integrableOn
  calc ‖∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-((σ : ℂ) + 1))‖
      ≤ ∫ t in Ioi (1 : ℝ), g t := by
        refine norm_integral_le_of_norm_le hint ?_
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht ↦ ?_)
        have ht1 : 1 < t := ht
        have ht0 : 0 < t := by linarith
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-((σ : ℂ) + 1)).re = -(σ + 1) := by simp
        rw [hre]
        by_cases hxt : x < t
        · have h := hb t ht1.le
          rw [Set.indicator_of_mem (show t ∈ Ioi x from hxt)] at h
          rw [hgdef, Set.indicator_of_mem (show t ∈ Ioi x from hxt)]
          calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ * t ^ (-(σ + 1)) ≤ K * t ^ α * t ^ (-(σ + 1)) :=
                mul_le_mul_of_nonneg_right h (by positivity)
            _ = K * t ^ (α - σ - 1) := by
                rw [mul_assoc, ← Real.rpow_add ht0]
                congr 2
                ring
        · have h := hb t ht1.le
          rw [Set.indicator_of_notMem (show t ∉ Ioi x from hxt)] at h
          have h0 : ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ = 0 := le_antisymm h (norm_nonneg _)
          rw [h0, zero_mul, hgdef, Set.indicator_of_notMem (show t ∉ Ioi x from hxt)]
    _ = K * x ^ (α - σ) / (σ - α) := by
        rw [hgdef, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          Set.Ioi_inter_Ioi, max_eq_left hx, integral_const_mul,
          integral_Ioi_rpow_of_lt (by linarith) hx0]
        have h1 : α - σ - 1 + 1 = α - σ := by ring
        have h2 : σ - α ≠ 0 := (by linarith : (0 : ℝ) < σ - α).ne'
        have h3 : α - σ ≠ 0 := (by linarith : α - σ < 0).ne
        rw [h1]
        field_simp
        ring

/-! ### Abel summation for the partial sums of the tail -/

section Abel

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- `χ(k)Λ(k)`. -/
noncomputable def cv (k : ℕ) : ℂ := χ k * (vonMangoldt k : ℂ)

lemma sum_Icc_zero_cv (u : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, cv χ k = psiChi χ u := by
  have h : Finset.Icc 0 ⌊u⌋₊ = insert 0 (Finset.Icc 1 ⌊u⌋₊) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [h, Finset.sum_insert (by simp), psiChi]
  simp [cv]

/-- `1/log u`, as a complex-valued function of `u`. -/
noncomputable def ilog (u : ℝ) : ℂ := ((Real.log u)⁻¹ : ℝ)

lemma hasDerivAt_ilog {u : ℝ} (hu : 1 < u) :
    HasDerivAt ilog ((-(u⁻¹ / Real.log u ^ 2) : ℝ) : ℂ) u := by
  have hlog : Real.log u ≠ 0 := (Real.log_pos hu).ne'
  have h1 : HasDerivAt (fun u : ℝ ↦ (Real.log u)⁻¹) (-(u⁻¹) / Real.log u ^ 2) u :=
    (Real.hasDerivAt_log (by linarith)).inv hlog
  have h2 := h1.ofReal_comp
  unfold ilog
  convert h2 using 2
  ring

lemma deriv_ilog {u : ℝ} (hu : 1 < u) : deriv ilog u = ((-(u⁻¹ / Real.log u ^ 2) : ℝ) : ℂ) :=
  (hasDerivAt_ilog hu).deriv

/-- **Abel summation for `Σ_{x < k ≤ t} χ(k)Λ(k)/log k`.** If `|ψ(u, χ)| ≤ B u^θ` for `u > 1`, then for
`1 < x ≤ t` the sum is at most `B t^θ(2/log x + 1/(θ log² x))`. -/
theorem norm_sum_Ioc_lc_le {B θ x t : ℝ} (hθ : 0 < θ) (hx : 1 < x) (hxt : x ≤ t) (hB : 0 ≤ B)
    (hψ : ∀ u : ℝ, 1 < u → ‖psiChi χ u‖ ≤ B * u ^ θ) :
    ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊t⌋₊, lc χ k‖ ≤
      B * t ^ θ * (2 / Real.log x + 1 / (θ * Real.log x ^ 2)) := by
  have hx0 : 0 ≤ x := by linarith
  have ht1 : 1 < t := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlxt : Real.log x ≤ Real.log t := Real.log_le_log (by linarith) hxt
  have hdiff : ∀ u ∈ Icc x t, DifferentiableAt ℝ ilog u := fun u hu ↦
    (hasDerivAt_ilog (by linarith [hu.1])).differentiableAt
  have hcont : ContinuousOn (deriv ilog) (Icc x t) := by
    have hc : ContinuousOn (fun u : ℝ ↦ ((-(u⁻¹ / Real.log u ^ 2) : ℝ) : ℂ)) (Icc x t) := by
      refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.neg ?_)
      refine ContinuousOn.div (continuousOn_inv₀.mono fun u hu ↦ ?_)
        ((Real.continuousOn_log.mono fun u hu ↦ ?_).pow 2) fun u hu ↦ ?_
      · exact (show (0 : ℝ) < u by linarith [hu.1]).ne'
      · exact (show (0 : ℝ) < u by linarith [hu.1]).ne'
      · exact pow_ne_zero 2 (Real.log_pos (by linarith [hu.1])).ne'
    exact hc.congr fun u hu ↦ deriv_ilog (by linarith [hu.1])
  have hint : IntegrableOn (deriv ilog) (Icc x t) := hcont.integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul (cv χ) hx0 hxt hdiff hint
  have hL : ∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊t⌋₊, ilog k * cv χ k = ∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊t⌋₊, lc χ k := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [ilog, lc, cv, Complex.ofReal_inv]
    ring
  simp only [sum_Icc_zero_cv] at habel
  rw [hL] at habel
  rw [habel]
  have hxθ : x ^ θ ≤ t ^ θ := Real.rpow_le_rpow hx0 hxt hθ.le
  have h1 : ‖ilog t * psiChi χ t‖ ≤ B * t ^ θ / Real.log x := by
    rw [norm_mul, ilog, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.log_nonneg ht1.le)),
      inv_mul_eq_div]
    calc ‖psiChi χ t‖ / Real.log t ≤ B * t ^ θ / Real.log t :=
          div_le_div_of_nonneg_right (hψ t ht1) (by linarith)
      _ ≤ B * t ^ θ / Real.log x := div_le_div_of_nonneg_left (by positivity) hlx hlxt
  have h2 : ‖ilog x * psiChi χ x‖ ≤ B * t ^ θ / Real.log x := by
    rw [norm_mul, ilog, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hlx.le), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right ((hψ x hx).trans (mul_le_mul_of_nonneg_left hxθ hB)) hlx.le
  have h3 : ‖∫ u in Ioc x t, deriv ilog u * psiChi χ u‖ ≤ B * t ^ θ / (θ * Real.log x ^ 2) := by
    have hG : IntegrableOn (fun u : ℝ ↦ B / Real.log x ^ 2 * u ^ (θ - 1)) (Ioc x t) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
      exact continuousOn_const.mul (continuousOn_id.rpow_const fun u hu ↦ Or.inl (by
        simp only [id]; linarith [hu.1]))
    calc ‖∫ u in Ioc x t, deriv ilog u * psiChi χ u‖
        ≤ ∫ u in Ioc x t, B / Real.log x ^ 2 * u ^ (θ - 1) := by
          refine norm_integral_le_of_norm_le hG ?_
          refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu ↦ ?_)
          have hu1 : 1 < u := by linarith [hu.1]
          have hu0 : 0 < u := by linarith
          have hlu : Real.log x ≤ Real.log u := Real.log_le_log (by linarith) hu.1.le
          rw [deriv_ilog hu1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
            abs_of_nonneg (by positivity)]
          calc u⁻¹ / Real.log u ^ 2 * ‖psiChi χ u‖ ≤ u⁻¹ / Real.log x ^ 2 * (B * u ^ θ) := by
                refine mul_le_mul ?_ (hψ u hu1) (norm_nonneg _) (by positivity)
                exact div_le_div_of_nonneg_left (by positivity) (by positivity)
                  (pow_le_pow_left₀ hlx.le hlu 2)
            _ = B / Real.log x ^ 2 * u ^ (θ - 1) := by
                rw [Real.rpow_sub hu0, Real.rpow_one]
                field_simp
      _ = B / Real.log x ^ 2 * ((t ^ θ - x ^ θ) / θ) := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hxt,
            integral_rpow (Or.inl (by linarith)), sub_add_cancel]
      _ ≤ B / Real.log x ^ 2 * (t ^ θ / θ) := by
          have : 0 ≤ x ^ θ := Real.rpow_nonneg hx0 θ
          gcongr
          linarith
      _ = B * t ^ θ / (θ * Real.log x ^ 2) := by
          field_simp
  calc ‖ilog t * psiChi χ t - ilog x * psiChi χ x - ∫ u in Ioc x t, deriv ilog u * psiChi χ u‖
      ≤ ‖ilog t * psiChi χ t‖ + ‖ilog x * psiChi χ x‖ +
          ‖∫ u in Ioc x t, deriv ilog u * psiChi χ u‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _) |>.trans (by linarith)
    _ ≤ B * t ^ θ / Real.log x + B * t ^ θ / Real.log x + B * t ^ θ / (θ * Real.log x ^ 2) := by
        linarith
    _ = B * t ^ θ * (2 / Real.log x + 1 / (θ * Real.log x ^ 2)) := by ring

end Abel

/-! ### The bound for `1 < σ ≤ 2`, and at `σ = 1` -/

section Assembly

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- The bound's right side: `log log x + γ + (log 4 + 6)/log x + B x^{θ−1}(2/log x + 1/(θ log² x))/(1 − θ)`. -/
noncomputable def bd (B θ x : ℝ) : ℝ :=
  Real.log (Real.log x) + Real.eulerMascheroniConstant + (Real.log 4 + 6) / Real.log x +
    B * x ^ (θ - 1) * (2 / Real.log x + 1 / (θ * Real.log x ^ 2)) / (1 - θ)

/-- **`|log |L(σ, χ)|| ≤ bd`** for every `σ > 1`, from `|ψ(u, χ)| ≤ B u^θ`, for every `x ≥ 2`. -/
theorem re_LSeries_lc_le {B θ x : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hx : 2 ≤ x) (hB : 0 ≤ B)
    (hψ : ∀ u : ℝ, 1 < u → ‖psiChi χ u‖ ≤ B * u ^ θ) {σ : ℝ} (hσ1 : 1 < σ) :
    |(LSeries (lc χ) σ).re| ≤ bd B θ x := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ1
  have hx1 : 1 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  set Y := ⌊x⌋₊ with hY
  rw [LSeries_lc_split χ hs Y, Complex.add_re]
  set K := B * (2 / Real.log x + 1 / (θ * Real.log x ^ 2)) with hK
  have hK0 : 0 ≤ K := by positivity
  -- the terms `n ≤ x`: Mertens' second theorem
  have hhead : |(∑ n ∈ Finset.Icc 1 Y, lc χ n / (n : ℂ) ^ (σ : ℂ)).re| ≤
      Real.log (Real.log x) + Real.eulerMascheroniConstant + (Real.log 4 + 6) / Real.log x := by
    refine (Complex.abs_re_le_norm _).trans ((norm_head_le χ hσ1.le Y).trans ?_)
    have e1 : Finset.Icc 1 Y = Finset.Ioc 0 Y := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hm := PNTMertens.sum_mangoldt_div_log_eq x
    have hE := PNTMertens.E₂Λ.abs_le hx
    rw [e1, hm]
    linarith [(abs_le.1 hE).2]
  -- the terms `n > x`: partial summation
  have hsT : LSeriesSummable (tl χ Y) σ := LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (fun n _ ↦ by unfold tl; split_ifs; exacts [norm_lc_le_one χ n, by simp]) hs
  have hb : ∀ t : ℝ, 1 ≤ t →
      ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, tl χ Y k‖ ≤ (Ioi x).indicator (fun t ↦ K * t ^ θ) t := by
    intro t _
    have hsum : ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, tl χ Y k = ∑ k ∈ Finset.Ioc Y ⌊t⌋₊, lc χ k := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊t⌋₊) (fun k ↦ Y < k)]
      have h0 : ∑ k ∈ (Finset.Icc 1 ⌊t⌋₊).filter (fun k ↦ ¬ Y < k), tl χ Y k = 0 :=
        Finset.sum_eq_zero fun k hk ↦ by
          rw [Finset.mem_filter] at hk
          simp only [tl, ite_eq_right hk.2]
      rw [h0, add_zero]
      have e : (Finset.Icc 1 ⌊t⌋₊).filter (fun k ↦ Y < k) = Finset.Ioc Y ⌊t⌋₊ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [e]
      exact Finset.sum_congr rfl fun k hk ↦ by
        rw [Finset.mem_Ioc] at hk
        simp only [tl, ite_eq_left hk.1]
    rw [hsum]
    by_cases hxt : x < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi x from hxt)]
      refine (norm_sum_Ioc_lc_le χ hθ hx1 hxt.le hB hψ).trans (le_of_eq ?_)
      rw [hK]
      ring
    · rw [Set.indicator_of_notMem (show t ∉ Ioi x from hxt)]
      have hYt : ⌊t⌋₊ ≤ Y := Nat.floor_le_floor (not_lt.1 hxt)
      rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
  have htail := norm_LSeries_le_of_vanish (α := θ) hθ.le (by linarith) (by linarith : (1 : ℝ) ≤ x)
    hK0 hsT hb
  have hσθ : σ * x ^ (θ - σ) / (σ - θ) ≤ x ^ (θ - 1) / (1 - θ) := by
    have h1 : x ^ (θ - σ) ≤ x ^ (θ - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : σ / (σ - θ) ≤ 1 / (1 - θ) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    calc σ * x ^ (θ - σ) / (σ - θ) = σ / (σ - θ) * x ^ (θ - σ) := by ring
      _ ≤ 1 / (1 - θ) * x ^ (θ - 1) :=
          mul_le_mul h2 h1 (by positivity) (div_nonneg zero_le_one (by linarith))
      _ = x ^ (θ - 1) / (1 - θ) := by ring
  have htail' : ‖LSeries (tl χ Y) σ‖ ≤
      B * x ^ (θ - 1) * (2 / Real.log x + 1 / (θ * Real.log x ^ 2)) / (1 - θ) := by
    calc ‖LSeries (tl χ Y) σ‖ ≤ σ * K * x ^ (θ - σ) / (σ - θ) := htail
      _ = K * (σ * x ^ (θ - σ) / (σ - θ)) := by ring
      _ ≤ K * (x ^ (θ - 1) / (1 - θ)) := mul_le_mul_of_nonneg_left hσθ hK0
      _ = B * x ^ (θ - 1) * (2 / Real.log x + 1 / (θ * Real.log x ^ 2)) / (1 - θ) := by
          rw [hK]
          ring
  calc |(∑ n ∈ Finset.Icc 1 Y, lc χ n / (n : ℂ) ^ (σ : ℂ)).re + (LSeries (tl χ Y) σ).re|
      ≤ |(∑ n ∈ Finset.Icc 1 Y, lc χ n / (n : ℂ) ^ (σ : ℂ)).re| + |(LSeries (tl χ Y) σ).re| :=
        abs_add_le _ _
    _ ≤ bd B θ x := by
        rw [bd]
        linarith [(Complex.abs_re_le_norm (LSeries (tl χ Y) σ)).trans htail']

/-- **`e^{−bd} ≤ |L(1, χ)| ≤ e^{bd}`** for every `χ ≠ 1` with `|ψ(u, χ)| ≤ B u^θ`, for every `x ≥ 2`: the bound of
`re_LSeries_lc_le` passes to `σ = 1` by continuity. -/
theorem norm_LFunction_one_bounds_of [NeZero N] (hχ : χ ≠ 1) {B θ x : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hx : 2 ≤ x) (hB : 0 ≤ B) (hψ : ∀ u : ℝ, 1 < u → ‖psiChi χ u‖ ≤ B * u ^ θ) :
    Real.exp (-bd B θ x) ≤ ‖DirichletCharacter.LFunction χ 1‖ ∧
      ‖DirichletCharacter.LFunction χ 1‖ ≤ Real.exp (bd B θ x) := by
  have hσ : ∀ σ : ℝ, 1 < σ →
      Real.exp (-bd B θ x) ≤ ‖DirichletCharacter.LFunction χ σ‖ ∧
        ‖DirichletCharacter.LFunction χ σ‖ ≤ Real.exp (bd B θ x) := by
    intro σ h1
    have hs : 1 < ((σ : ℂ)).re := by simpa using h1
    have h := re_LSeries_lc_le χ hθ hθ1 hx hB hψ h1
    rw [norm_LFunction_eq χ hs]
    obtain ⟨ha, hb⟩ := abs_le.1 h
    exact ⟨Real.exp_le_exp.2 ha, Real.exp_le_exp.2 hb⟩
  have hF := DirichletCharacter.differentiable_LFunction hχ
  have hcont : Continuous fun σ : ℝ ↦ ‖DirichletCharacter.LFunction χ σ‖ :=
    (hF.continuous.comp Complex.continuous_ofReal).norm
  have ht : Tendsto (fun σ : ℝ ↦ ‖DirichletCharacter.LFunction χ σ‖) (𝓝[>] 1)
      (𝓝 ‖DirichletCharacter.LFunction χ 1‖) := by
    have h := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    simpa using h
  have hev : ∀ᶠ σ in 𝓝[>] (1 : ℝ), σ ∈ Ioi (1 : ℝ) := self_mem_nhdsWithin
  exact ⟨ge_of_tendsto ht (hev.mono fun σ hσ' ↦ (hσ σ hσ').1),
    le_of_tendsto ht (hev.mono fun σ hσ' ↦ (hσ σ hσ').2)⟩

end Assembly

/-! ### The constants: `θ = 12/13`, `x = (e⁵² log(N + 2))¹³` -/

lemma min_156 : min (1 / 156 : ℝ) (1 / 24) = 1 / 156 := by norm_num

lemma theta_eq : (11 / 12 + 1 / 156 : ℝ) = 12 / 13 := by norm_num

/-- `2·10¹¹·156⁵ ≤ 0.483·e⁵²`. -/
lemma A_le : (2 * 10 ^ 11 / (1 / 156 : ℝ) ^ 5) ≤ 483 / 1000 * Real.exp 52 := by
  have he := Real.exp_one_gt_d9
  have h52 : Real.exp 1 ^ 52 = Real.exp 52 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (2.7182818283 : ℝ) ^ 52 ≤ Real.exp 1 ^ 52 := pow_le_pow_left₀ (by norm_num) he.le 52
  rw [← h52]
  have h : (2 * 10 ^ 11 / (1 / 156 : ℝ) ^ 5) ≤ 483 / 1000 * 2.7182818283 ^ 52 := by norm_num
  linarith

/-- The numbers: with `D = 13(52 + log log(N + 2)) ≥ 676` and `B x^{θ−1} ≤ 0.483`, the error terms are below `3/100`. -/
lemma err_le {D a : ℝ} (hD : 676 ≤ D) (ha : a ≤ 483 / 1000) :
    (Real.log 4 + 6) / D + a * (2 / D + 1 / (12 / 13 * D ^ 2)) / (1 - 12 / 13) ≤ 3 / 100 := by
  have h4 := ExplicitConstants.log_four_lt
  have hD0 : 0 < D := by linarith
  have hu : 1 / D ≤ 1 / 676 := one_div_le_one_div_of_le (by norm_num) hD
  have hu0 : 0 ≤ 1 / D := by positivity
  have e1 : (Real.log 4 + 6) / D = (Real.log 4 + 6) * (1 / D) := by ring
  have e2 : a * (2 / D + 1 / (12 / 13 * D ^ 2)) / (1 - 12 / 13) =
      13 * a * (2 * (1 / D) + 13 / 12 * (1 / D) ^ 2) := by
    field_simp
    ring
  rw [e1, e2]
  have h1 : (Real.log 4 + 6) * (1 / D) ≤ 7.3863 * (1 / 676) :=
    mul_le_mul (by linarith) hu hu0 (by norm_num)
  have h2 : 2 * (1 / D) + 13 / 12 * (1 / D) ^ 2 ≤ 2 * (1 / 676) + 13 / 12 * (1 / 676) ^ 2 := by
    gcongr
  have h3 : 13 * a * (2 * (1 / D) + 13 / 12 * (1 / D) ^ 2) ≤
      13 * (483 / 1000) * (2 * (1 / 676) + 13 / 12 * (1 / 676) ^ 2) :=
    mul_le_mul (by linarith) h2 (by positivity) (by norm_num)
  linarith [show 7.3863 * (1 / 676 : ℝ) + 13 * (483 / 1000) * (2 * (1 / 676) + 13 / 12 * (1 / 676) ^ 2)
    ≤ 3 / 100 by norm_num]

/-- **Littlewood's bounds with explicit constants, for every Dirichlet character**: for every `χ ≠ 1` mod `N`, with
`ℓ = log log(N + 2)`, `e^{−γ−3/100}/(13(52 + ℓ)) ≤ |L(1, χ)| ≤ 13e^{γ+3/100}(52 + ℓ)`. -/
theorem norm_LFunction_one_bounds_sharp :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      Real.exp (-(Real.eulerMascheroniConstant + 3 / 100)) /
          (13 * (52 + Real.log (Real.log (N + 2)))) ≤ ‖DirichletCharacter.LFunction χ 1‖ ∧
        ‖DirichletCharacter.LFunction χ 1‖ ≤
          13 * Real.exp (Real.eulerMascheroniConstant + 3 / 100) * (52 + Real.log (Real.log (N + 2))) := by
  intro N _ χ hχ
  have hψ0 := ExplicitConstants.psiChi_le_explicit (η := 1 / 156) (by norm_num) N χ hχ
  rw [min_156, theta_eq] at hψ0
  set A : ℝ := 2 * 10 ^ 11 / (1 / 156 : ℝ) ^ 5 with hA
  set L : ℝ := Real.log (N + 2) with hL
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hL1 : 1 < L := by
    rw [hL, Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hlL : 0 < Real.log L := Real.log_pos hL1
  set y : ℝ := Real.exp 52 * L with hy
  have hy0 : 0 < y := by positivity
  have hy1 : 2 ≤ y := by
    have h52 : (2 : ℝ) ≤ Real.exp 52 := by
      have := Real.add_one_le_exp (52 : ℝ)
      linarith
    nlinarith
  set x : ℝ := y ^ 13 with hx
  have hx2 : 2 ≤ x := by
    have : y ≤ y ^ 13 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hψ : ∀ u : ℝ, 1 < u → ‖psiChi χ u‖ ≤ (A * L) * u ^ (12 / 13 : ℝ) := fun u hu ↦ by
    have h := hψ0 u hu
    rw [hA, hL]
    linarith
  have hB : 0 ≤ A * L := by positivity
  obtain ⟨hlo, hup⟩ := norm_LFunction_one_bounds_of χ hχ (B := A * L) (θ := 12 / 13) (x := x)
    (by norm_num) (by norm_num) hx2 hB hψ
  -- `bd ≤ log(13(52 + ℓ)) + γ + 3/100`
  have hlogx : Real.log x = 13 * (52 + Real.log L) := by
    rw [hx, Real.log_pow, hy, Real.log_mul (Real.exp_pos 52).ne' (by positivity), Real.log_exp]
    push_cast
    ring
  have hxθ : x ^ ((12 / 13 : ℝ) - 1) = y⁻¹ := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    norm_num
    exact Real.rpow_neg_one y
  have hAy : A * L * y⁻¹ ≤ 483 / 1000 := by
    have e : A * L * y⁻¹ = A / Real.exp 52 := by
      rw [hy]
      field_simp
    rw [e, div_le_iff₀ (Real.exp_pos 52), hA]
    exact A_le
  have hbd : bd (A * L) (12 / 13) x ≤
      Real.log (13 * (52 + Real.log L)) + Real.eulerMascheroniConstant + 3 / 100 := by
    rw [bd, hlogx, hxθ]
    have hD : (676 : ℝ) ≤ 13 * (52 + Real.log L) := by linarith
    have h := err_le hD hAy
    linarith
  have hD0 : 0 < 13 * (52 + Real.log L) := by positivity
  constructor
  · refine le_trans ?_ hlo
    calc Real.exp (-(Real.eulerMascheroniConstant + 3 / 100)) / (13 * (52 + Real.log L))
        = Real.exp (-(Real.log (13 * (52 + Real.log L)) + Real.eulerMascheroniConstant + 3 / 100)) := by
          rw [show -(Real.log (13 * (52 + Real.log L)) + Real.eulerMascheroniConstant + 3 / 100) =
              -(Real.eulerMascheroniConstant + 3 / 100) + -Real.log (13 * (52 + Real.log L)) by ring,
            Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hD0, div_eq_mul_inv]
      _ ≤ Real.exp (-bd (A * L) (12 / 13) x) := Real.exp_le_exp.2 (by linarith)
  · refine hup.trans ?_
    calc Real.exp (bd (A * L) (12 / 13) x)
        ≤ Real.exp (Real.log (13 * (52 + Real.log L)) + Real.eulerMascheroniConstant + 3 / 100) :=
          Real.exp_le_exp.2 hbd
      _ = 13 * Real.exp (Real.eulerMascheroniConstant + 3 / 100) * (52 + Real.log L) := by
          rw [add_assoc, Real.exp_add, Real.exp_log hD0]
          ring

end LittlewoodSharp
