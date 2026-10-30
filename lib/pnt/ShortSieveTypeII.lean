import ShortSieveHarman
import ShortSieveHolder
import ShortSieveInterval

/-!
# Type II estimates for products of primes in boxes

For a box `(N, M]`, `M ≤ 2N`, let `P(t) = Σ_{N<p≤M} (N/p)^{1/2} p^{−it}`, the Dirichlet polynomial `DirMean.dp` of the
primes of the box (`box`) with the weights of the line `Re s = 1/2`, normalised to modulus at most `1` (`boxWt`). For
boxes `(Nⱼ, Mⱼ]`, `j ∈ ι`, the tuples `(pⱼ)ⱼ` with `pⱼ` prime in `(Nⱼ, Mⱼ]` (`tuples`) have the products `prods`;
`cnt n` counts the tuples with product `n` (the Dirichlet convolution of the indicators of the boxes' primes). This
module proves, with no hypothesis (the analytic input beyond the large values estimates of `ShortSieveMoment` is the
zero-free half-plane `Re s > 11/12` behind `ShortSieveTwist`):

* `norm_dp_boxWt_le_of`: `|P(t)| ≤ C N^{1−κ}` for `κ < 1/50` and `N^κ ≤ |t| ≤ N^A`: Abel summation
  (`ShortSieveTwist.norm_sum_mul_le`) with the nonincreasing weights over `ShortSieveTwist.norm_dp_primes_Ioc_le_of`,
  which is uniform in the endpoint; `norm_dp_boxWt_le` is the case `κ = 1/100`;
* `moment_boxWt_hux_from`, `moment_boxWt_mv_from`, `moment_boxWt_from`: Harman's moment lemma for `P` on the heights
  from `N^κ`, `0 < κ < 1/50`: `∫ |P|^δ ≤ C N^{δ−η}` over `[a, b]` and over `[−b, −a]` for `N^κ ≤ a ≤ b ≤ N^D`, with
  `η > 0` depending on `κ`, when `δ` is admissible for `D` (`MomentOK`: `m < D ≤ m + 1/2` and `δ > 4D − 2m`, or
  `D ≤ k` and `δ > 2k`). The lemmas of `ShortSieveMoment` hold on any interval of length at most `N^D` on which
  `|P| ≤ N^{1−κ/2}` (`pointwise_boxWt_of`), and the pointwise bound depends on `|t|` only, so the negative heights
  need no reflection. `moment_boxWt_hux`, `moment_boxWt_mv` and `moment_boxWt` are the case `κ = 1/100`;
* `integral_prod_le`: Hölder's inequality `∫_a^b ∏ fⱼ ≤ ∏ Kⱼ` from `∫_a^b fⱼ^{δⱼ} ≤ Kⱼ^{δⱼ}`, `Σ 1/δⱼ = 1`
  (`ShortSieveHolder.lintegral_prod_le_of_moments` on `(a, b]`);
* `dp_prods`: the product formula `Σ_n cnt(n) n^{−1/2−it} = ∏ⱼ Nⱼ^{−1/2} Pⱼ(t)`, that is
  `A(s) = ∏ⱼ Σ_{Nⱼ<p≤Mⱼ} p^{−s}` on `Re s = 1/2` for `A(s) = Σ_n cnt(n) n^{−s}`; `sum_cnt_filter` counts the tuples
  by their products;
* `abs_card_tuples_sub_le_of`, the Type II estimate: for `αⱼ > κ > 0` with `Σ αⱼ ≤ 1`, `θ > 0`, `κ₀ > 0` and
  `ρ > 2κ₀` with `θ + ρ ≤ 1`, and `δⱼ > 0` with `Σ 1/δⱼ = 1`, each admissible for `Dⱼ = (1 − θ + κ)/(αⱼ − κ)`, there
  are `η > 0`, `C` and `x₀` with `|#{∏ pⱼ ∈ (x − y, x]} − (y/y₁)·#{∏ pⱼ ∈ (x − y₁, x]}| ≤ C y x^{−η}` for `x ≥ x₀`,
  `x^θ ≤ y ≤ y₁ ≤ x^{1−ρ}` and all boxes with `x^{αⱼ}/2 ≤ Nⱼ ≤ x^{αⱼ}`, `Nⱼ ≤ Mⱼ ≤ 2Nⱼ`. The conclusion does not
  involve `κ₀`, so every `ρ > 0` will do (`abs_card_tuples_sub_le_of_pos`, `κ₀ = ρ/4`); `abs_card_tuples_sub_le` is
  the case `κ₀ = 1/100`, `ρ > 1/50`. For three primes near `x^{1/3}` and `θ = 3/5`: `abs_card_tuples_sub_le_three`
  (`ρ = 1/25`) and `abs_card_tuples_sub_le_three_long` (`κ₀ = 1/2000`, `ρ = 1/400`).

The route of the Type II estimate: `ShortSieveInterval.norm_sum_Ioc_sub_le` for the coefficients `cnt` on `prods`, with
`T₀ = x^{κ₀}`, `T = x^{1−θ+κ}`, `ε = y x^{−1−κ/2}` and `k = ⌈(6 + κ)/κ⌉` averages, and its four terms.
* The middle range `T₀ ≤ |t| ≤ T`. For large `x`, `Nⱼ ≥ x^{αⱼ−κ}`, so `T ≤ Nⱼ^{Dⱼ}`, and `Nⱼ ≤ x`, so
  `T₀ ≥ Nⱼ^{κ'}` for `κ' = min(κ₀, 1/100)`: the moments of the boxes from the heights `Nⱼ^{κ'}` apply on `[T₀, T]`
  and `[−T, −T₀]`. Hölder gives `∫|A| ≤ ∏ⱼ Cⱼ^{1/δⱼ} Nⱼ^{1/2−ηⱼ/δⱼ}` (`integral_norm_dp_prods_le`), at most
  `C x^{1/2} x^{−η}` since `∏ Nⱼ ≤ x` (`prod_le_rpow`); the term is `C(y/√x)∫|A| ≤ C y x^{−η}` (`mid_term_le`).
* The low range `|t| ≤ T₀`: `|A| ≤ Σ_n cnt(n) n^{−1/2} ≤ (∏ Nⱼ)^{1/2} ≤ x^{1/2}` (`sum_norm_coef_le`), and the factor
  `(1 + T₀)(y₁/x) ≤ 2T₀ x^{−ρ}` leaves `4C y x^{2κ₀−ρ}` (`low_term_le_of`): this is where `ρ > 2κ₀` is needed.
* The tail: `εT ≥ x^{κ/2}`, so the term is at most `C 2^k x^{2+κ/2−kκ/2}/y ≤ C 2^k y x^{−1}` (`tail_term_le`).
* The transitions: `cnt(n) ≤ d(n)^r ≤ C x^β` for the `r` boxes and `β = min(κ, θ)/4` (`norm_cnt_le`,
  `norm_cnt_le_rpow`, `LinnikPower.card_divisors_le`), so `8B(xε(k + 3) + 1) ≤ C y x^{−β}` (`trans_term_le`).
-/

open Finset Real MeasureTheory DirMean

noncomputable section

namespace ShortSieveTypeII

/-! ### The weighted prime polynomials -/

/-- The primes of `(N, M]`. -/
def box (N M : ℕ) : Finset ℕ := (Ioc N M).filter Nat.Prime

/-- The weights `(N/p)^{1/2}` of the line `Re s = 1/2`, normalised to modulus at most `1` on `(N, ∞)`. -/
def boxWt (N p : ℕ) : ℂ := ((((N : ℝ) / p) ^ (1 / 2 : ℝ) : ℝ) : ℂ)

/-- The primes of `(N, M]`, `M ≤ 2N`, lie in `(N, 2N]`. -/
lemma box_subset {N M : ℕ} (hM : M ≤ 2 * N) : box N M ⊆ Ioc N (2 * N) := fun n hn => by
  have h := (mem_filter.1 hn).1
  rw [mem_Ioc] at h ⊢
  omega

/-- The primes of a box are positive. -/
lemma pos_of_mem_box {N M n : ℕ} (hn : n ∈ box N M) : 0 < n := (mem_filter.1 hn).2.pos

/-- `|(N/p)^{1/2}| ≤ 1` for `p > N`. -/
lemma norm_boxWt_le {N p : ℕ} (hp : N < p) : ‖boxWt N p‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hle : (N : ℝ) / p ≤ 1 := (div_le_one hp0).2 (by exact_mod_cast hp.le)
  rw [boxWt, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_one (by positivity) hle (by norm_num)

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

/-- **The weighted prime polynomial, pointwise.** For every `A > 0` there is `C` with
`|Σ_{N<p≤M} (N/p)^{1/2} p^{−it}| ≤ C N^{99/100}` for all `N ≥ 2`, `N ≤ M ≤ 2N` and `N^{1/100} ≤ |t| ≤ N^A`:
`norm_dp_boxWt_le_of` at `κ = 1/100`. -/
theorem norm_dp_boxWt_le {A : ℝ} (hA : 0 < A) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ M : ℕ, N ≤ M →
    M ≤ 2 * N → ∀ t : ℝ, (N : ℝ) ^ (1 / 100 : ℝ) ≤ |t| → |t| ≤ (N : ℝ) ^ A →
      ‖dp (box N M) (boxWt N) t‖ ≤ C * (N : ℝ) ^ (99 / 100 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := norm_dp_boxWt_le_of (κ := 1 / 100) (by norm_num) hA
  refine ⟨C, hC0, fun N hN M hNM hM t ht1 ht2 => ?_⟩
  have h := hC N hN M hNM hM t ht1 ht2
  rwa [show (1 : ℝ) - 1 / 100 = 99 / 100 by norm_num] at h

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

/-- The pointwise bound in the form of `ShortSieveMoment`'s hypothesis, with `η₁ = 1/200`, for both signs of `t`. -/
lemma pointwise_boxWt {Dx : ℝ} (hDx : 0 < Dx) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N →
    ∀ t : ℝ, (N : ℝ) ^ (1 / 100 : ℝ) ≤ |t| → |t| ≤ (N : ℝ) ^ Dx →
      ‖dp (box N M) (boxWt N) t‖ ≤ (N : ℝ) ^ (1 - 1 / 200 : ℝ) := by
  obtain ⟨N₀, h⟩ := pointwise_boxWt_of (κ := 1 / 100) (by norm_num) (by norm_num) hDx
  refine ⟨N₀, fun N hN M hNM hM t ht1 ht2 => ?_⟩
  have h' := h N hN M hNM hM t ht1 ht2
  rwa [show (1 : ℝ) - 1 / 100 / 2 = 1 - 1 / 200 by norm_num] at h'

/-- The two-sided moment of the weighted prime polynomial on the heights from `N^κ`, `0 < κ < 1/50`, from one of
the moment lemmas of `ShortSieveMoment` with `η₁ = κ/2` (`pointwise_boxWt_of`). -/
lemma moment_boxWt_from_of {κ Dx δ : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 50) (hDx : 0 < Dx)
    (h : ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Ioc N (2 * N) →
      ∀ c : ℕ → ℂ, (∀ j ∈ S, ‖c j‖ ≤ 1) → ∀ a b : ℝ, a ≤ b → b - a ≤ (N : ℝ) ^ Dx →
      (∀ t ∈ Set.Icc a b, ‖dp S c t‖ ≤ (N : ℝ) ^ (1 - κ / 2)) →
      ∫ t in a..b, ‖dp S c t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η₂)) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N →
      ∀ a b : ℝ, (N : ℝ) ^ κ ≤ a → a ≤ b → b ≤ (N : ℝ) ^ Dx →
        (∫ t in a..b, ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η)) ∧
          ∫ t in (-b)..(-a), ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) := by
  obtain ⟨η, hη, C, N₀, hmom⟩ := h
  obtain ⟨N₁, hpt⟩ := pointwise_boxWt_of hκ0 hκ hDx
  refine ⟨η, hη, max C 0, le_max_right _ _, max N₀ N₁, fun N hN M hNM hM a b ha hab hb => ?_⟩
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  have hc : ∀ j ∈ box N M, ‖boxWt N j‖ ≤ 1 := fun j hj =>
    norm_boxWt_le (mem_Ioc.1 (mem_filter.1 hj).1).1
  have hmax : C * (N : ℝ) ^ (δ - η) ≤ max C 0 * (N : ℝ) ^ (δ - η) := by
    gcongr
    exact le_max_left _ _
  have hpt' := hpt N (le_trans (le_max_right _ _) hN) M hNM hM
  refine ⟨le_trans ?_ hmax, le_trans ?_ hmax⟩
  · refine hmom N (le_trans (le_max_left _ _) hN) _ (box_subset hM) _ hc a b hab (by linarith) fun t ht => ?_
    have ht0 : 0 ≤ t := le_trans ha0 ht.1
    exact hpt' t (by rw [abs_of_nonneg ht0]; exact le_trans ha ht.1)
      (by rw [abs_of_nonneg ht0]; exact le_trans ht.2 hb)
  · refine hmom N (le_trans (le_max_left _ _) hN) _ (box_subset hM) _ hc (-b) (-a) (by linarith)
      (by linarith) fun t ht => ?_
    have ht0 : t ≤ 0 := le_trans ht.2 (by linarith)
    exact hpt' t (by rw [abs_of_nonpos ht0]; linarith [ht.2]) (by rw [abs_of_nonpos ht0]; linarith [ht.1])

/-- The two-sided moment of the weighted prime polynomial from a moment lemma of `ShortSieveMoment` with
`η₁ = 1/200`: `moment_boxWt_from_of` at `κ = 1/100`. -/
lemma moment_boxWt_of {Dx δ : ℝ} (hDx : 0 < Dx)
    (h : ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ, S ⊆ Ioc N (2 * N) →
      ∀ c : ℕ → ℂ, (∀ j ∈ S, ‖c j‖ ≤ 1) → ∀ a b : ℝ, a ≤ b → b - a ≤ (N : ℝ) ^ Dx →
      (∀ t ∈ Set.Icc a b, ‖dp S c t‖ ≤ (N : ℝ) ^ (1 - 1 / 200 : ℝ)) →
      ∫ t in a..b, ‖dp S c t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η₂)) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N →
      ∀ a b : ℝ, (N : ℝ) ^ (1 / 100 : ℝ) ≤ a → a ≤ b → b ≤ (N : ℝ) ^ Dx →
        (∫ t in a..b, ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η)) ∧
          ∫ t in (-b)..(-a), ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) := by
  refine moment_boxWt_from_of (κ := 1 / 100) (by norm_num) (by norm_num) hDx ?_
  rwa [show (1 : ℝ) - 1 / 100 / 2 = 1 - 1 / 200 by norm_num]

/-- **Harman's moment lemma for the weighted primes on the heights from `N^κ`, from the Halász–Montgomery
count.** For `0 < κ < 1/50`, `m ≥ 1`, `m < D ≤ m + 1/2` and `δ > 4D − 2m` there are `η > 0`, `C ≥ 0` and `N₀` such
that for `N ≥ N₀`, `N ≤ M ≤ 2N` and `N^κ ≤ a ≤ b ≤ N^D` both `∫_a^b |P|^δ` and `∫_{−b}^{−a} |P|^δ` are at most
`C N^{δ−η}`, where `P(t) = Σ_{N<p≤M} (N/p)^{1/2} p^{−it}`: `ShortSieveMoment.moment_le_hux` with `η₁ = κ/2`. -/
theorem moment_boxWt_hux_from {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 50) {m : ℕ} (hm : 1 ≤ m) {Dx δ : ℝ}
    (hD : (m : ℝ) < Dx) (hD' : Dx ≤ m + 1 / 2) (hδ : 4 * Dx - 2 * m < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N →
      ∀ a b : ℝ, (N : ℝ) ^ κ ≤ a → a ≤ b → b ≤ (N : ℝ) ^ Dx →
        (∫ t in a..b, ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η)) ∧
          ∫ t in (-b)..(-a), ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) :=
  moment_boxWt_from_of hκ0 hκ (lt_of_le_of_lt (Nat.cast_nonneg m) hD)
    (ShortSieveMoment.moment_le_hux hm hD hD' hδ (by positivity))

/-- **Harman's moment lemma for the weighted primes on the heights from `N^κ`, from the mean value theorem.** For
`0 < κ < 1/50`, `k ≥ 1`, `0 < D ≤ k` and `δ > 2k`, the conclusion of `moment_boxWt_hux_from`. -/
theorem moment_boxWt_mv_from {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 50) {k : ℕ} (hk : 1 ≤ k) {Dx δ : ℝ}
    (hDx : 0 < Dx) (hD : Dx ≤ k) (hδ : 2 * k < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N →
      ∀ a b : ℝ, (N : ℝ) ^ κ ≤ a → a ≤ b → b ≤ (N : ℝ) ^ Dx →
        (∫ t in a..b, ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η)) ∧
          ∫ t in (-b)..(-a), ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) :=
  moment_boxWt_from_of hκ0 hκ hDx (ShortSieveMoment.moment_le_mv hk hD hδ (by positivity))

/-- **Harman's moment lemma for the weighted primes, from the Halász–Montgomery count.** For `m ≥ 1`,
`m < D ≤ m + 1/2` and `δ > 4D − 2m` there are `η > 0`, `C ≥ 0` and `N₀` such that for `N ≥ N₀`, `N ≤ M ≤ 2N` and
`N^{1/100} ≤ a ≤ b ≤ N^D` both `∫_a^b |P|^δ` and `∫_{−b}^{−a} |P|^δ` are at most `C N^{δ−η}`, where
`P(t) = Σ_{N<p≤M} (N/p)^{1/2} p^{−it}`: `moment_boxWt_hux_from` at `κ = 1/100`. -/
theorem moment_boxWt_hux {m : ℕ} (hm : 1 ≤ m) {Dx δ : ℝ} (hD : (m : ℝ) < Dx) (hD' : Dx ≤ m + 1 / 2)
    (hδ : 4 * Dx - 2 * m < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N →
      ∀ a b : ℝ, (N : ℝ) ^ (1 / 100 : ℝ) ≤ a → a ≤ b → b ≤ (N : ℝ) ^ Dx →
        (∫ t in a..b, ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η)) ∧
          ∫ t in (-b)..(-a), ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) :=
  moment_boxWt_hux_from (κ := 1 / 100) (by norm_num) (by norm_num) hm hD hD' hδ

/-- **Harman's moment lemma for the weighted primes, from the mean value theorem.** For `k ≥ 1`, `0 < D ≤ k` and
`δ > 2k`, the conclusion of `moment_boxWt_hux`. -/
theorem moment_boxWt_mv {k : ℕ} (hk : 1 ≤ k) {Dx δ : ℝ} (hDx : 0 < Dx) (hD : Dx ≤ k) (hδ : 2 * k < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N →
      ∀ a b : ℝ, (N : ℝ) ^ (1 / 100 : ℝ) ≤ a → a ≤ b → b ≤ (N : ℝ) ^ Dx →
        (∫ t in a..b, ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η)) ∧
          ∫ t in (-b)..(-a), ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) :=
  moment_boxWt_mv_from (κ := 1 / 100) (by norm_num) (by norm_num) hk hDx hD hδ

/-- `δ` is an admissible moment for heights up to `N^D`: `moment_boxWt_hux` (`m < D ≤ m + 1/2`, `δ > 4D − 2m`) or
`moment_boxWt_mv` (`D ≤ k`, `δ > 2k`) applies. -/
def MomentOK (D δ : ℝ) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) < D ∧ D ≤ m + 1 / 2 ∧ 4 * D - 2 * m < δ) ∨ (∃ k : ℕ, 1 ≤ k ∧ D ≤ k ∧ 2 * k < δ)

/-- **The weighted moment lemma on the heights from `N^κ` for an admissible moment.** For `0 < κ < 1/50`, `D > 0`
and `MomentOK D δ`, the conclusion of `moment_boxWt_hux_from`. -/
theorem moment_boxWt_from {κ Dx δ : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 50) (hDx : 0 < Dx) (hok : MomentOK Dx δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N →
      ∀ a b : ℝ, (N : ℝ) ^ κ ≤ a → a ≤ b → b ≤ (N : ℝ) ^ Dx →
        (∫ t in a..b, ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η)) ∧
          ∫ t in (-b)..(-a), ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) := by
  rcases hok with ⟨m, hm, hD, hD', hδ⟩ | ⟨k, hk, hD, hδ⟩
  · exact moment_boxWt_hux_from hκ0 hκ hm hD hD' hδ
  · exact moment_boxWt_mv_from hκ0 hκ hk hDx hD hδ

/-- **The weighted moment lemma for an admissible moment.** For `D > 0` and `MomentOK D δ`, the conclusion of
`moment_boxWt_hux`: `moment_boxWt_from` at `κ = 1/100`. -/
theorem moment_boxWt {Dx δ : ℝ} (hDx : 0 < Dx) (hok : MomentOK Dx δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N ≤ M → M ≤ 2 * N →
      ∀ a b : ℝ, (N : ℝ) ^ (1 / 100 : ℝ) ≤ a → a ≤ b → b ≤ (N : ℝ) ^ Dx →
        (∫ t in a..b, ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η)) ∧
          ∫ t in (-b)..(-a), ‖dp (box N M) (boxWt N) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) :=
  moment_boxWt_from (κ := 1 / 100) (by norm_num) (by norm_num) hDx hok

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

/-- A product `n` has at most `d(n)^r` representations, `r` the number of boxes. -/
lemma norm_cnt_le (N M : ι → ℕ) {n : ℕ} (hn : 0 < n) :
    ‖cnt N M n‖ ≤ ((n.divisors.card : ℝ)) ^ Fintype.card ι := by
  rw [cnt, Complex.norm_natCast]
  have hsub : (tuples N M).filter (fun g => ∏ j, g j = n) ⊆ Fintype.piFinset fun _ : ι => n.divisors := by
    intro g hg
    rw [mem_filter] at hg
    refine Fintype.mem_piFinset.2 fun j => Nat.mem_divisors.2 ⟨?_, hn.ne'⟩
    rw [← hg.2]
    exact dvd_prod_of_mem _ (mem_univ j)
  have := card_le_card hsub
  rw [Fintype.card_piFinset, prod_const, card_univ] at this
  exact_mod_cast this

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

/-- **The middle range by Hölder.** If `∫_a^b |Pⱼ|^{δⱼ} ≤ Cⱼ Nⱼ^{δⱼ−ηⱼ}` for every box, `Pⱼ` the weighted prime
polynomial of the box, with `δⱼ > 0`, `Σ 1/δⱼ = 1` and `Cⱼ ≥ 0`, then
`∫_a^b |A(1/2 + it)| dt ≤ ∏ⱼ Cⱼ^{1/δⱼ} Nⱼ^{1/2} Nⱼ^{−ηⱼ/δⱼ}` (`dp_prods`, `integral_prod_le`). -/
theorem integral_norm_dp_prods_le (N M : ι → ℕ) (hN : ∀ j, 0 < N j) {a b : ℝ} (hab : a ≤ b) {δ : ι → ℝ}
    (hδ : ∀ j, 0 < δ j) (hδs : ∑ j, 1 / δ j = 1) {η C : ι → ℝ} (hC : ∀ j, 0 ≤ C j)
    (hmom : ∀ j, ∫ t in a..b, ‖dp (box (N j) (M j)) (boxWt (N j)) t‖ ^ δ j ≤ C j * (N j : ℝ) ^ (δ j - η j)) :
    ∫ t in a..b, ‖dp (prods N M) (ShortSieveInterval.coef (cnt N M)) t‖ ≤
      ∏ j, (C j ^ (1 / δ j) * ((N j : ℝ) ^ (1 / 2 : ℝ) * (N j : ℝ) ^ (-(η j / δ j)))) := by
  have hN0 : ∀ j, (0 : ℝ) < N j := fun j => by exact_mod_cast hN j
  set c : ι → ℝ := fun j => (N j : ℝ) ^ (-(1 / 2 : ℝ)) with hc
  have hnorm : ∀ t, ‖dp (prods N M) (ShortSieveInterval.coef (cnt N M)) t‖ =
      (∏ j, c j) * ∏ j, ‖dp (box (N j) (M j)) (boxWt (N j)) t‖ := by
    intro t
    rw [dp_prods N M hN t, norm_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp_rw [hnorm]
  rw [intervalIntegral.integral_const_mul]
  set K : ι → ℝ := fun j => (C j * (N j : ℝ) ^ (δ j - η j)) ^ (1 / δ j) with hK
  have hK0 : ∀ j, 0 ≤ K j := fun j => Real.rpow_nonneg (mul_nonneg (hC j) (by positivity)) _
  have hhol := integral_prod_le univ (f := fun j t => ‖dp (box (N j) (M j)) (boxWt (N j)) t‖)
    (fun j _ => (continuous_dp _ _).norm) (fun j _ t => norm_nonneg _) hab (fun j _ => hδ j) hδs
    (fun j _ => hK0 j) fun j _ => by
      rw [hK, ← Real.rpow_mul (mul_nonneg (hC j) (by positivity)), one_div_mul_cancel (hδ j).ne',
        Real.rpow_one]
      exact hmom j
  have hc0 : 0 ≤ ∏ j, c j := prod_nonneg fun j _ => by positivity
  calc (∏ j, c j) * ∫ t in a..b, ∏ j, ‖dp (box (N j) (M j)) (boxWt (N j)) t‖ ≤ (∏ j, c j) * ∏ j, K j :=
        mul_le_mul_of_nonneg_left hhol hc0
    _ = ∏ j, (c j * K j) := prod_mul_distrib.symm
    _ = _ := by
        refine prod_congr rfl fun j _ => ?_
        simp only [hc, hK]
        rw [Real.mul_rpow (hC j) (by positivity), ← Real.rpow_mul (hN0 j).le]
        have e : (δ j - η j) * (1 / δ j) = 1 - η j / δ j := by
          rw [mul_one_div, sub_div, div_self (hδ j).ne']
        rw [e]
        calc (N j : ℝ) ^ (-(1 / 2 : ℝ)) * (C j ^ (1 / δ j) * (N j : ℝ) ^ (1 - η j / δ j))
            = C j ^ (1 / δ j) * ((N j : ℝ) ^ (-(1 / 2 : ℝ)) * (N j : ℝ) ^ (1 - η j / δ j)) := by ring
          _ = _ := by
              rw [← Real.rpow_add (hN0 j), ← Real.rpow_add (hN0 j)]
              congr 2
              ring

/-- The middle range in terms of `x`: for `1 ≤ Nⱼ ≤ x^{αⱼ}`, `Σ αⱼ ≤ 1`, `eⱼ ≥ 0` and `x^γ ≤ N_{j₀}`,
`∏ⱼ cⱼ Nⱼ^{1/2} Nⱼ^{−eⱼ} ≤ (∏ⱼ cⱼ) x^{1/2} x^{−γ e_{j₀}}`. -/
lemma prod_le_rpow {N : ι → ℕ} {x : ℝ} (hx : 1 ≤ x) {α : ι → ℝ} (hαs : ∑ j, α j ≤ 1)
    (hN : ∀ j, (N j : ℝ) ≤ x ^ α j) (hN1 : ∀ j, 1 ≤ N j) {c e : ι → ℝ} (hc : ∀ j, 0 ≤ c j)
    (he : ∀ j, 0 ≤ e j) (j₀ : ι) {γ : ℝ} (hγ : x ^ γ ≤ N j₀) :
    ∏ j, (c j * ((N j : ℝ) ^ (1 / 2 : ℝ) * (N j : ℝ) ^ (-e j))) ≤
      (∏ j, c j) * x ^ (1 / 2 : ℝ) * x ^ (-(γ * e j₀)) := by
  have hx0 : 0 < x := by linarith
  have hN0 : ∀ j, (1 : ℝ) ≤ N j := fun j => by exact_mod_cast hN1 j
  rw [prod_mul_distrib, prod_mul_distrib, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun j _ => hc j)
  refine mul_le_mul ?_ ?_ (prod_nonneg fun j _ => by positivity) (by positivity)
  · rw [Real.finsetProd_rpow _ _ (fun j _ => by positivity)]
    refine Real.rpow_le_rpow (prod_nonneg fun j _ => by positivity) ?_ (by norm_num)
    calc ∏ j, (N j : ℝ) ≤ ∏ j, x ^ α j := prod_le_prod₀ (fun j _ => by positivity) fun j _ => hN j
      _ = x ^ ∑ j, α j := (Real.rpow_sum_of_pos hx0 _ _).symm
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hαs
      _ = x := Real.rpow_one x
  · rw [← mul_prod_erase univ _ (mem_univ j₀)]
    have h1 : ∏ j ∈ univ.erase j₀, (N j : ℝ) ^ (-e j) ≤ 1 :=
      prod_le_one₀ (fun j _ => by positivity) fun j _ =>
        Real.rpow_le_one_of_one_le_of_nonpos (hN0 j) (by linarith [he j])
    have h2 : (N j₀ : ℝ) ^ (-e j₀) ≤ x ^ (-(γ * e j₀)) := by
      calc (N j₀ : ℝ) ^ (-e j₀) ≤ (x ^ γ) ^ (-e j₀) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hγ (by linarith [he j₀])
        _ = x ^ (-(γ * e j₀)) := by rw [← Real.rpow_mul hx0.le]; ring_nf
    calc (N j₀ : ℝ) ^ (-e j₀) * ∏ j ∈ univ.erase j₀, (N j : ℝ) ^ (-e j) ≤ (N j₀ : ℝ) ^ (-e j₀) * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ x ^ (-(γ * e j₀)) := by rw [mul_one]; exact h2

/-- The coefficients in terms of `x`: for `2^r ≤ x`, `Nⱼ ≤ x^{αⱼ}`, `Σ αⱼ ≤ 1` and `Mⱼ ≤ 2Nⱼ`, every product
`n ≤ 2^r x ≤ x²` has `cnt(n) ≤ d(n)^r ≤ C_β x^β`, `r` the number of boxes, for `0 < β ≤ 1`. -/
lemma norm_cnt_le_rpow (N M : ι → ℕ) {x : ℝ} (hx : (2 : ℝ) ^ Fintype.card ι ≤ x) (hx1 : 1 ≤ x) {α : ι → ℝ}
    (hαs : ∑ j, α j ≤ 1) (hN : ∀ j, (N j : ℝ) ≤ x ^ α j) (hM : ∀ j, M j ≤ 2 * N j) {β : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hι : 0 < Fintype.card ι) {n : ℕ} (hn : n ∈ prods N M) :
    ‖cnt N M n‖ ≤ LinnikPower.Cdiv (β / (2 * Fintype.card ι)) ^ Fintype.card ι * x ^ β := by
  set r := Fintype.card ι with hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hι
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hι
  set β' := β / (2 * r) with hβ'
  have hβ'0 : 0 < β' := by positivity
  have hβ'1 : β' ≤ 1 := by
    rw [hβ', div_le_one (by positivity)]
    linarith
  have hx0 : 0 < x := by linarith
  have hn0 := pos_of_mem_prods hn
  obtain ⟨g, hg, rfl⟩ := mem_image.1 hn
  -- the size of the product
  have hsize : ((∏ j, g j : ℕ) : ℝ) ≤ x ^ (2 : ℝ) := by
    have hgM : ∀ j, (g j : ℝ) ≤ 2 * x ^ α j := fun j => by
      have h1 : g j ≤ M j := (mem_Ioc.1 (mem_filter.1 (Fintype.mem_piFinset.1 hg j)).1).2
      have h2 : (g j : ℝ) ≤ 2 * N j := by exact_mod_cast h1.trans (hM j)
      linarith [hN j]
    calc ((∏ j, g j : ℕ) : ℝ) = ∏ j, (g j : ℝ) := Nat.cast_prod _ _
      _ ≤ ∏ j, (2 * x ^ α j) := prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => hgM j
      _ = 2 ^ r * x ^ ∑ j, α j := by
          rw [prod_mul_distrib, prod_const, card_univ, Real.rpow_sum_of_pos hx0]
      _ ≤ x * x ^ (1 : ℝ) := by
          gcongr
      _ = x ^ (2 : ℝ) := by
          rw [Real.rpow_one, show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have hd := LinnikPower.card_divisors_le hβ'0 hβ'1 (∏ j, g j)
  have hd' : ((∏ j, g j).divisors.card : ℝ) ≤ LinnikPower.Cdiv β' * x ^ (2 * β') := by
    calc ((∏ j, g j).divisors.card : ℝ) ≤ LinnikPower.Cdiv β' * ((∏ j, g j : ℕ) : ℝ) ^ β' := hd
      _ ≤ LinnikPower.Cdiv β' * (x ^ (2 : ℝ)) ^ β' := by
          gcongr
          exact (zero_lt_one.trans_le (LinnikPower.one_le_Cdiv hβ'0 hβ'1)).le
      _ = LinnikPower.Cdiv β' * x ^ (2 * β') := by rw [← Real.rpow_mul hx0.le]
  calc ‖cnt N M (∏ j, g j)‖ ≤ (((∏ j, g j).divisors.card : ℕ) : ℝ) ^ r := norm_cnt_le N M hn0
    _ ≤ (LinnikPower.Cdiv β' * x ^ (2 * β')) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _) hd' r
    _ = LinnikPower.Cdiv β' ^ r * x ^ β := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ (2 * β')), ← Real.rpow_mul hx0.le]
        congr 2
        rw [hβ']
        field_simp

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

/-- The low range: `C₀(1 + T₀)(y/√x)(y₁/x) I ≤ 4C₀ y x^{1/50−ρ}` for `T₀ = x^{1/100}`, `y₁ ≤ x^{1−ρ}` and
`I ≤ 2T₀ x^{1/2}`: `low_term_le_of` at `κ₀ = 1/100`. -/
lemma low_term_le {C₀ x y y₁ ρ I : ℝ} (hC₀ : 0 ≤ C₀) (hx : 1 ≤ x) (hy : 0 ≤ y) (hy₁ : 0 ≤ y₁)
    (hy₁x : y₁ ≤ x ^ (1 - ρ)) (hI : I ≤ 2 * x ^ (1 / 100 : ℝ) * x ^ (1 / 2 : ℝ)) :
    C₀ * (1 + x ^ (1 / 100 : ℝ)) * (y / √x) * (y₁ / x) * I ≤ 4 * C₀ * y * x ^ (1 / 50 - ρ) := by
  have h := low_term_le_of hC₀ hx (by norm_num : (0 : ℝ) ≤ 1 / 100) hy hy₁ hy₁x hI
  rwa [show (2 : ℝ) * (1 / 100) - ρ = 1 / 50 - ρ by ring] at h

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

/-- **Type II estimates for products of primes in boxes, with the low range up to `x^{κ₀}`.** Let `αⱼ > κ > 0`
with `Σⱼ αⱼ ≤ 1`, `θ > 0`, `κ₀ > 0` and `ρ > 2κ₀` with `θ + ρ ≤ 1`, and `δⱼ > 0` with `Σⱼ 1/δⱼ = 1`, each `δⱼ`
admissible (`MomentOK`) for `Dⱼ = (1 − θ + κ)/(αⱼ − κ)`. There are `η > 0`, `C` and `x₀` such that for `x ≥ x₀`,
`x^θ ≤ y ≤ y₁ ≤ x^{1−ρ}` and boxes `x^{αⱼ}/2 ≤ Nⱼ ≤ x^{αⱼ}`, `Nⱼ ≤ Mⱼ ≤ 2Nⱼ`, the numbers of tuples `(pⱼ)ⱼ`, `pⱼ`
prime in `(Nⱼ, Mⱼ]`, with `∏ⱼ pⱼ ∈ (x − y, x]` and with `∏ⱼ pⱼ ∈ (x − y₁, x]` satisfy
`|#{∏ⱼ pⱼ ∈ (x − y, x]} − (y/y₁)·#{∏ⱼ pⱼ ∈ (x − y₁, x]}| ≤ C y x^{−η}`. The proof is
`ShortSieveInterval.norm_sum_Ioc_sub_le` with `T₀ = x^{κ₀}` and the four terms bounded as in the module docstring:
the low range costs `4C₀ y x^{2κ₀−ρ}` (`low_term_le_of`), which is where `ρ > 2κ₀` is needed, and the middle range
takes the moments of the boxes from the heights `Nⱼ^{κ'} ≤ x^{κ'} ≤ T₀`, `κ' = min(κ₀, 1/100)`
(`moment_boxWt_from`). -/
theorem abs_card_tuples_sub_le_of {α δ : ι → ℝ} {θ κ κ₀ ρ : ℝ} (hκ : 0 < κ) (hα : ∀ j, κ < α j)
    (hαs : ∑ j, α j ≤ 1) (hθ : 0 < θ) (hκ₀ : 0 < κ₀) (hρ : 2 * κ₀ < ρ) (hθρ : θ + ρ ≤ 1) (hδ : ∀ j, 0 < δ j)
    (hδs : ∑ j, 1 / δ j = 1) (hok : ∀ j, MomentOK ((1 - θ + κ) / (α j - κ)) (δ j)) :
    ∃ η : ℝ, 0 < η ∧ ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y y₁ : ℝ, x ^ θ ≤ y → y ≤ y₁ → y₁ ≤ x ^ (1 - ρ) →
      ∀ N M : ι → ℕ, (∀ j, x ^ α j / 2 ≤ N j ∧ (N j : ℝ) ≤ x ^ α j) → (∀ j, N j ≤ M j ∧ M j ≤ 2 * N j) →
        |(#{g ∈ tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
          y / y₁ * #{g ∈ tuples N M | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
          C * y * x ^ (-η) := by
  -- a box
  obtain ⟨j₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hδs
  have hι : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨j₀⟩
  -- the exponents
  have hακ : ∀ j, 0 < α j - κ := fun j => sub_pos.2 (hα j)
  have hα1 : ∀ j, α j ≤ 1 := fun j =>
    (single_le_sum (fun i _ => (hκ.trans (hα i)).le) (mem_univ j)).trans hαs
  have hκ1 : κ < 1 := (hα j₀).trans_le (hα1 j₀)
  have hD0 : ∀ j, 0 < (1 - θ + κ) / (α j - κ) := fun j => div_pos (by linarith) (hακ j)
  -- the start `κ' = min(κ₀, 1/100)` of the moments
  set κ' : ℝ := min κ₀ (1 / 100) with hκ'
  have hκ'0 : 0 < κ' := lt_min hκ₀ (by norm_num)
  have hκ'1 : κ' < 1 / 50 := (min_le_right _ _).trans_lt (by norm_num)
  have hκ'κ₀ : κ' ≤ κ₀ := min_le_left _ _
  -- the moments of the boxes and the comparison
  choose η₁ hη₁ C₁ hC₁ N₁ hmom using fun j => moment_boxWt_from hκ'0 hκ'1 (hD0 j) (hok j)
  obtain ⟨C₀, hC₀, hcmp⟩ := ShortSieveInterval.norm_sum_Ioc_sub_le
  -- the parameters
  set ηm : ℝ := (α j₀ - κ) * (η₁ j₀ / δ j₀) with hηm
  have hηm0 : 0 < ηm := mul_pos (hακ j₀) (div_pos (hη₁ j₀) (hδ j₀))
  set k : ℕ := ⌈(6 + κ) / κ⌉₊ with hk
  have hkκ : 6 + κ ≤ k * κ := by
    have := Nat.le_ceil ((6 + κ) / κ)
    rwa [div_le_iff₀ hκ] at this
  set β : ℝ := min κ θ / 4 with hβ
  have hβ0 : 0 < β := div_pos (lt_min hκ hθ) (by norm_num)
  have hβκ : β ≤ κ / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hβθ : β ≤ θ / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hβ1 : β ≤ 1 := by linarith
  have hKm0 : 0 ≤ ∏ j, C₁ j ^ (1 / δ j) := prod_nonneg fun j _ => Real.rpow_nonneg (hC₁ j) _
  set CB : ℝ := LinnikPower.Cdiv (β / (2 * Fintype.card ι)) ^ Fintype.card ι with hCB
  have hCB0 : 0 ≤ CB := by
    have hr1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hι
    refine pow_nonneg (le_trans zero_le_one (LinnikPower.one_le_Cdiv (by positivity) ?_)) _
    rw [div_le_one (by positivity)]
    linarith
  set η : ℝ := min (min ηm (ρ - 2 * κ₀)) β with hη
  have hη0 : 0 < η := lt_min (lt_min hηm0 (by linarith)) hβ0
  have hηm' : η ≤ ηm := (min_le_left _ _).trans (min_le_left _ _)
  have hηρ : η ≤ ρ - 2 * κ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hηβ : η ≤ β := min_le_right _ _
  -- the threshold
  set N₀ : ℕ := ∑ j, N₁ j + 1 with hN₀
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ 2 ≤ x ^ κ ∧ 2 ≤ x ^ ρ ∧ 2 * (N₀ : ℝ) ≤ x ^ κ ∧
      (2 : ℝ) ^ Fintype.card ι ≤ x := by
    have h1 := tendsto_rpow_atTop hκ
    have h2 := tendsto_rpow_atTop (show 0 < ρ by linarith)
    exact (Filter.eventually_ge_atTop 1).and ((h1.eventually_ge_atTop 2).and ((h2.eventually_ge_atTop 2).and
      ((h1.eventually_ge_atTop _).and (Filter.eventually_ge_atTop _))))
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨η, hη0, 2 * C₀ * (∏ j, C₁ j ^ (1 / δ j)) + 4 * C₀ + C₀ * 2 ^ k + 8 * CB * (k + 4), x₀,
    fun x hx y y₁ hy hyy₁ hy₁ N M hNb hMb => ?_⟩
  obtain ⟨hx1, hxκ, hxρ, hxN, hxr⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ y := le_trans (Real.one_le_rpow hx1 hθ.le) hy
  have hy0 : 0 < y := by linarith
  have hy₁0 : 0 < y₁ := by linarith
  -- the boxes
  have hxα : ∀ j, x ^ κ ≤ x ^ α j := fun j => Real.rpow_le_rpow_of_exponent_le hx1 (hα j).le
  have hNα : ∀ j, x ^ (α j - κ) ≤ N j := by
    intro j
    have e : x ^ α j = x ^ (α j - κ) * x ^ κ := by rw [← Real.rpow_add hx0]; ring_nf
    have h0 : 0 ≤ x ^ (α j - κ) := by positivity
    have h1 := (hNb j).1
    rw [e] at h1
    nlinarith
  have hN₀N : ∀ j, N₀ ≤ N j := fun j => by
    have h1 := (hNb j).1
    have h2 := hxα j
    have h3 : (N₀ : ℝ) ≤ N j := by linarith
    exact_mod_cast h3
  have hN₁ : ∀ j, N₁ j ≤ N j := fun j => by
    have h1 : N₁ j ≤ ∑ i, N₁ i := single_le_sum (fun i _ => Nat.zero_le _) (mem_univ j)
    have h2 := hN₀N j
    omega
  have hNpos : ∀ j, 0 < N j := fun j => by
    have h2 := hN₀N j
    omega
  -- the heights `T₀ = x^{κ₀}` and `T = x^{1−θ+κ}`
  have hT₀1 : 1 ≤ x ^ κ₀ := Real.one_le_rpow hx1 hκ₀.le
  have hT₀T : x ^ κ₀ ≤ x ^ (1 - θ + κ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hTN : ∀ j, x ^ (1 - θ + κ) ≤ (N j : ℝ) ^ ((1 - θ + κ) / (α j - κ)) := by
    intro j
    calc x ^ (1 - θ + κ) = (x ^ (α j - κ)) ^ ((1 - θ + κ) / (α j - κ)) := by
          rw [← Real.rpow_mul hx0.le, mul_div_cancel₀ _ (hακ j).ne']
      _ ≤ (N j : ℝ) ^ ((1 - θ + κ) / (α j - κ)) :=
          Real.rpow_le_rpow (by positivity) (hNα j) (hD0 j).le
  have hT₀N : ∀ j, (N j : ℝ) ^ κ' ≤ x ^ κ₀ := by
    intro j
    calc (N j : ℝ) ^ κ' ≤ x ^ κ' := by
          refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hκ'0.le
          calc (N j : ℝ) ≤ x ^ α j := (hNb j).2
            _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (hα1 j)
            _ = x := Real.rpow_one x
      _ ≤ x ^ κ₀ := Real.rpow_le_rpow_of_exponent_le hx1 hκ'κ₀
  -- the middle range
  have hm := fun j => hmom j (N j) (hN₁ j) (M j) (hMb j).1 (hMb j).2 _ _ (hT₀N j) hT₀T (hTN j)
  have hprod := prod_le_rpow (N := N) hx1 hαs (fun j => (hNb j).2) (fun j => hNpos j)
    (c := fun j => C₁ j ^ (1 / δ j)) (e := fun j => η₁ j / δ j) (fun j => Real.rpow_nonneg (hC₁ j) _)
    (fun j => (div_pos (hη₁ j) (hδ j)).le) j₀ (hNα j₀)
  have hI₁ := (integral_norm_dp_prods_le N M hNpos hT₀T hδ hδs hC₁ fun j => (hm j).1).trans hprod
  have hI₂ := (integral_norm_dp_prods_le N M hNpos (neg_le_neg hT₀T) hδ hδs hC₁ fun j => (hm j).2).trans hprod
  -- the low range
  have hL₁ : ∑ n ∈ prods N M, ‖ShortSieveInterval.coef (cnt N M) n‖ ≤ x ^ (1 / 2 : ℝ) := by
    refine (sum_norm_coef_le N M hNpos fun j => (hMb j).2).trans ?_
    refine Real.rpow_le_rpow (prod_nonneg fun j _ => Nat.cast_nonneg _) ?_ (by norm_num)
    calc ∏ j, (N j : ℝ) ≤ ∏ j, x ^ α j := prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => (hNb j).2
      _ = x ^ ∑ j, α j := (Real.rpow_sum_of_pos hx0 _ _).symm
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hαs
      _ = x := Real.rpow_one x
  have hI₀ : ∫ t in (-x ^ κ₀)..x ^ κ₀,
      ‖dp (prods N M) (ShortSieveInterval.coef (cnt N M)) t‖ ≤ 2 * x ^ κ₀ * x ^ (1 / 2 : ℝ) := by
    refine (ShortSieveInterval.integral_norm_dp_le _ _ (by linarith)).trans ?_
    rw [show x ^ κ₀ - -x ^ κ₀ = 2 * x ^ κ₀ by ring]
    exact mul_le_mul_of_nonneg_left hL₁ (by positivity)
  -- the comparison
  have hx1' : 1 < x := by
    by_contra hc
    have hx' : x = 1 := le_antisymm (not_lt.1 hc) hx1
    rw [hx', Real.one_rpow] at hxκ
    norm_num at hxκ
  have hε0 : 0 < y * x ^ (-1 - κ / 2) := by positivity
  have hε1 : y * x ^ (-1 - κ / 2) < 1 := by
    calc y * x ^ (-1 - κ / 2) ≤ x ^ (1 - ρ) * x ^ (-1 - κ / 2) := by gcongr; linarith
      _ = x ^ (-ρ - κ / 2) := by rw [← Real.rpow_add hx0]; ring_nf
      _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx1' (by linarith)
  have hy₁x : y₁ ≤ x / 2 := by
    calc y₁ ≤ x ^ (1 - ρ) := hy₁
      _ = x / x ^ ρ := by rw [Real.rpow_sub hx0, Real.rpow_one]
      _ ≤ x / 2 := div_le_div_of_nonneg_left hx0.le (by norm_num) hxρ
  have hB : ∀ n ∈ prods N M, ‖cnt N M n‖ ≤ CB * x ^ β := fun n hn =>
    norm_cnt_le_rpow N M hxr hx1 hαs (fun j => (hNb j).2) (fun j => (hMb j).2) hβ0 hβ1 hι hn
  have h := hcmp (y * x ^ (-1 - κ / 2)) hε0 hε1 k x y y₁ (x ^ κ₀) (x ^ (1 - θ + κ)) hx0 hy0 hyy₁
    hy₁x (by positivity) hT₀T (prods N M) (fun n hn => pos_of_mem_prods hn) (cnt N M) (CB * x ^ β)
    (by positivity) hB
  rw [sum_cnt_filter, sum_cnt_filter] at h
  have hnorm : ∀ u v : ℕ, ‖((u : ℕ) : ℂ) - ((y / y₁ : ℝ) : ℂ) * ((v : ℕ) : ℂ)‖ = |(u : ℝ) - y / y₁ * v| := by
    intro u v
    rw [show ((u : ℕ) : ℂ) - ((y / y₁ : ℝ) : ℂ) * ((v : ℕ) : ℂ) = (((u : ℝ) - y / y₁ * v : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at h
  -- the four terms
  have hy2β : x ^ (2 * β) ≤ y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) hy
  have t1 := mid_term_le hC₀.le hx0 hy0.le hI₁ hI₂
  have t2 := low_term_le_of hC₀.le hx1 hκ₀.le hy0.le hy₁0.le hy₁ hI₀
  have t3 := tail_term_le hC₀.le hx1 hy hy1 hL₁ hkκ
  have t4 := trans_term_le k hCB0 hx1 hβκ hy2β
  have hX : ∀ e : ℝ, η ≤ e → ∀ c : ℝ, 0 ≤ c → c * x ^ (-e) ≤ c * x ^ (-η) := fun e he c hc =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) hc
  have u1 := hX ((α j₀ - κ) * (η₁ j₀ / δ j₀)) hηm' (2 * C₀ * (∏ j, C₁ j ^ (1 / δ j)) * y) (by positivity)
  have u2 := hX (ρ - 2 * κ₀) hηρ (4 * C₀ * y) (by positivity)
  rw [neg_sub] at u2
  have u3 := hX 1 (by linarith) (C₀ * 2 ^ k * y) (by positivity)
  have u4 := hX β hηβ (8 * CB * (k + 4) * y) (by positivity)
  refine h.trans (le_of_le_of_eq (add_le_add (add_le_add (add_le_add (t1.trans u1) (t2.trans u2))
    (t3.trans u3)) (t4.trans u4)) ?_)
  ring

/-- **Type II estimates for products of primes in boxes.** Let `αⱼ > κ > 0` with `Σⱼ αⱼ ≤ 1`, `θ > 0`,
`ρ > 1/50` with `θ + ρ ≤ 1`, and `δⱼ > 0` with `Σⱼ 1/δⱼ = 1`, each `δⱼ` admissible (`MomentOK`) for
`Dⱼ = (1 − θ + κ)/(αⱼ − κ)`. There are `η > 0`, `C` and `x₀` such that for `x ≥ x₀`, `x^θ ≤ y ≤ y₁ ≤ x^{1−ρ}` and
boxes `x^{αⱼ}/2 ≤ Nⱼ ≤ x^{αⱼ}`, `Nⱼ ≤ Mⱼ ≤ 2Nⱼ`, the numbers of tuples `(pⱼ)ⱼ`, `pⱼ` prime in `(Nⱼ, Mⱼ]`, with
`∏ⱼ pⱼ ∈ (x − y, x]` and with `∏ⱼ pⱼ ∈ (x − y₁, x]` satisfy
`|#{∏ⱼ pⱼ ∈ (x − y, x]} − (y/y₁)·#{∏ⱼ pⱼ ∈ (x − y₁, x]}| ≤ C y x^{−η}`; in particular for `y = x^θ` and
`y₁ = x^{1−ρ}`. This is `abs_card_tuples_sub_le_of` at `κ₀ = 1/100`, that is with `T₀ = x^{1/100}`. -/
theorem abs_card_tuples_sub_le {α δ : ι → ℝ} {θ κ ρ : ℝ} (hκ : 0 < κ) (hα : ∀ j, κ < α j)
    (hαs : ∑ j, α j ≤ 1) (hθ : 0 < θ) (hρ : 1 / 50 < ρ) (hθρ : θ + ρ ≤ 1) (hδ : ∀ j, 0 < δ j) (hδs : ∑ j, 1 / δ j = 1)
    (hok : ∀ j, MomentOK ((1 - θ + κ) / (α j - κ)) (δ j)) :
    ∃ η : ℝ, 0 < η ∧ ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y y₁ : ℝ, x ^ θ ≤ y → y ≤ y₁ → y₁ ≤ x ^ (1 - ρ) →
      ∀ N M : ι → ℕ, (∀ j, x ^ α j / 2 ≤ N j ∧ (N j : ℝ) ≤ x ^ α j) → (∀ j, N j ≤ M j ∧ M j ≤ 2 * N j) →
        |(#{g ∈ tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
          y / y₁ * #{g ∈ tuples N M | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
          C * y * x ^ (-η) :=
  abs_card_tuples_sub_le_of (κ₀ := 1 / 100) hκ hα hαs hθ (by norm_num) (by linarith) hθρ hδ hδs hok

/-- **Type II estimates for products of primes in boxes, for every `ρ > 0`.** The conclusion of
`abs_card_tuples_sub_le` under its hypotheses with `ρ > 0` in place of `ρ > 1/50`: `abs_card_tuples_sub_le_of` with
`κ₀ = ρ/4`. -/
theorem abs_card_tuples_sub_le_of_pos {α δ : ι → ℝ} {θ κ ρ : ℝ} (hκ : 0 < κ) (hα : ∀ j, κ < α j)
    (hαs : ∑ j, α j ≤ 1) (hθ : 0 < θ) (hρ : 0 < ρ) (hθρ : θ + ρ ≤ 1) (hδ : ∀ j, 0 < δ j) (hδs : ∑ j, 1 / δ j = 1)
    (hok : ∀ j, MomentOK ((1 - θ + κ) / (α j - κ)) (δ j)) :
    ∃ η : ℝ, 0 < η ∧ ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y y₁ : ℝ, x ^ θ ≤ y → y ≤ y₁ → y₁ ≤ x ^ (1 - ρ) →
      ∀ N M : ι → ℕ, (∀ j, x ^ α j / 2 ≤ N j ∧ (N j : ℝ) ≤ x ^ α j) → (∀ j, N j ≤ M j ∧ M j ≤ 2 * N j) →
        |(#{g ∈ tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
          y / y₁ * #{g ∈ tuples N M | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
          C * y * x ^ (-η) :=
  abs_card_tuples_sub_le_of (κ₀ := ρ / 4) hκ hα hαs hθ (by positivity) (by linarith) hθρ hδ hδs hok

/-- **Three primes near `x^{1/3}` in intervals of length `x^{3/5}`.** `abs_card_tuples_sub_le` for three boxes
`x^{1/3}/2 ≤ Nⱼ ≤ x^{1/3}` with `δⱼ = 3`, `κ = 1/1000`, `θ = 3/5` and `ρ = 1/25`: there
`Dⱼ = (2/5 + 1/1000)/(1/3 − 1/1000) = 1203/997` and `4Dⱼ − 2 < 3` (Harman's moment lemma with `m = 1`). For three
equal boxes the method needs `D ≤ 1` or `4D − 2 < 3`, with `D ≈ 3(1 − θ)`: `θ > 7/12`. -/
theorem abs_card_tuples_sub_le_three : ∃ η : ℝ, 0 < η ∧ ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y y₁ : ℝ,
    x ^ (3 / 5 : ℝ) ≤ y → y ≤ y₁ → y₁ ≤ x ^ (24 / 25 : ℝ) → ∀ N M : Fin 3 → ℕ,
      (∀ j, x ^ (1 / 3 : ℝ) / 2 ≤ N j ∧ (N j : ℝ) ≤ x ^ (1 / 3 : ℝ)) → (∀ j, N j ≤ M j ∧ M j ≤ 2 * N j) →
        |(#{g ∈ tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
          y / y₁ * #{g ∈ tuples N M | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
          C * y * x ^ (-η) := by
  obtain ⟨η, hη, C, x₀, h⟩ := abs_card_tuples_sub_le (ι := Fin 3) (α := fun _ => 1 / 3) (δ := fun _ => 3)
    (θ := 3 / 5) (κ := 1 / 1000) (ρ := 1 / 25) (by norm_num) (fun _ => by norm_num) (by simp)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num) (by simp)
    (fun _ => Or.inl ⟨1, le_rfl, by norm_num, by norm_num, by norm_num⟩)
  refine ⟨η, hη, C, x₀, fun x hx y y₁ hy hyy₁ hy₁ N M hN hM => h x hx y y₁ hy hyy₁ ?_ N M hN hM⟩
  norm_num
  exact hy₁

/-- **Three primes near `x^{1/3}` in intervals of length `x^{3/5}`, against intervals of length `x^{399/400}`.**
`abs_card_tuples_sub_le_of` for three boxes `x^{1/3}/2 ≤ Nⱼ ≤ x^{1/3}` with `δⱼ = 3`, `κ = 1/1000`, `θ = 3/5`,
`T₀ = x^{1/2000}` and `ρ = 1/400 > 2/2000`: the exponents `Dⱼ = 1203/997` are those of
`abs_card_tuples_sub_le_three`, and the comparison interval `(x − y₁, x]` may be as long as `x^{1−1/400}`. -/
theorem abs_card_tuples_sub_le_three_long : ∃ η : ℝ, 0 < η ∧ ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y y₁ : ℝ,
    x ^ (3 / 5 : ℝ) ≤ y → y ≤ y₁ → y₁ ≤ x ^ (399 / 400 : ℝ) → ∀ N M : Fin 3 → ℕ,
      (∀ j, x ^ (1 / 3 : ℝ) / 2 ≤ N j ∧ (N j : ℝ) ≤ x ^ (1 / 3 : ℝ)) → (∀ j, N j ≤ M j ∧ M j ≤ 2 * N j) →
        |(#{g ∈ tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
          y / y₁ * #{g ∈ tuples N M | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
          C * y * x ^ (-η) := by
  obtain ⟨η, hη, C, x₀, h⟩ := abs_card_tuples_sub_le_of (ι := Fin 3) (α := fun _ => 1 / 3) (δ := fun _ => 3)
    (θ := 3 / 5) (κ := 1 / 1000) (κ₀ := 1 / 2000) (ρ := 1 / 400) (by norm_num) (fun _ => by norm_num) (by simp)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num) (by simp)
    (fun _ => Or.inl ⟨1, le_rfl, by norm_num, by norm_num, by norm_num⟩)
  refine ⟨η, hη, C, x₀, fun x hx y y₁ hy hyy₁ hy₁ N M hN hM => h x hx y y₁ hy hyy₁ ?_ N M hN hM⟩
  norm_num
  exact hy₁

end ShortSieveTypeII

#print axioms ShortSieveTypeII.norm_dp_boxWt_le_of
#print axioms ShortSieveTypeII.norm_dp_boxWt_le
#print axioms ShortSieveTypeII.moment_boxWt_hux_from
#print axioms ShortSieveTypeII.moment_boxWt_mv_from
#print axioms ShortSieveTypeII.moment_boxWt_from
#print axioms ShortSieveTypeII.moment_boxWt_hux
#print axioms ShortSieveTypeII.moment_boxWt_mv
#print axioms ShortSieveTypeII.moment_boxWt
#print axioms ShortSieveTypeII.integral_prod_le
#print axioms ShortSieveTypeII.dp_prods
#print axioms ShortSieveTypeII.sum_cnt_filter
#print axioms ShortSieveTypeII.abs_card_tuples_sub_le_of
#print axioms ShortSieveTypeII.abs_card_tuples_sub_le
#print axioms ShortSieveTypeII.abs_card_tuples_sub_le_of_pos
#print axioms ShortSieveTypeII.abs_card_tuples_sub_le_three
#print axioms ShortSieveTypeII.abs_card_tuples_sub_le_three_long
