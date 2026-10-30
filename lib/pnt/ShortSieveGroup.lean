import ShortSieveTypeII

/-!
# Type II estimates for groups of prime boxes

`ShortSieveTypeII` proves the Type II estimate with one Hölder factor per prime, each prime in a box `(Nⱼ, Mⱼ]` with
`x^{αⱼ}/2 ≤ Nⱼ ≤ x^{αⱼ}`. Harman's sieve, as in R. Li's proof that `(x − x^{0.52}, x]` contains primes
(arXiv:2308.04458), needs more: its asymptotic tests group several primes into one Hölder factor, and the rough
cofactor of a sieve term (a number with no prime factor below `x^c`), expanded into its prime factors, goes into one
group. This module proves the Type II estimate with one Hölder factor per group of boxes and with the sizes of the
boxes ranging over intervals: for boxes `(Nⱼ, Mⱼ]`, `j ∈ ι`, sorted into groups by `grp : ι → G`, it asks only for
`Nⱼ ≥ x^c`, for `N_i ≥ x^{a_i}` and for `∏_{grp j = i} Mⱼ ≤ 2N_i`, where `N_i = ∏_{grp j = i} Nⱼ` is the product of the
group. It proves, with no hypothesis (the analytic input is that of `ShortSieveTypeII`):

* `norm_cnt_le_pow`: a number has at most `r^r` representations as an ordered product of primes from `r` boxes, since
  each entry of a representation is one of the `r` entries of a fixed one;
* `moment_group_from`: Harman's moment lemma for a group, `∫ |F|^δ ≤ C N^{δ−η}` over `[a, b]` and over `[−b, −a]` for
  the product `F = ∏ⱼ Pⱼ` of the weighted prime polynomials `Pⱼ` of the boxes of the group, `N = ∏ Nⱼ`, on the
  heights `Nⱼ^κ ≤ a ≤ b ≤ Nⱼ^A` with `b ≤ N^D`, `0 < κ < 1/50`, when `δ` is admissible for `D` (`MomentOK`). The
  product `F = (∏ Nⱼ)^{1/2} Σ_n cnt(n) n^{−1/2−it}` (`prod_dp_boxWt_eq`) is one Dirichlet polynomial on `(N, 2N]`
  (`prods_subset`) with coefficients `cnt(n) (N/n)^{1/2} ≤ r^r`, and `|F| ≤ ∏ⱼ Nⱼ^{1−κ/2} = N^{1−κ/2}`
  (`pointwise_boxWt_of`): `F/r^r` satisfies the hypotheses of `ShortSieveMoment.moment_le_hux` or
  `ShortSieveMoment.moment_le_mv` with `η₁ = κ/2`, whose constants do not depend on the polynomial;
* `integral_norm_dp_prods_le_group`: Hölder's inequality with one factor per group,
  `∫_a^b |A(1/2 + it)| dt ≤ ∏_i C_i^{1/δ_i} N_i^{1/2} N_i^{−η_i/δ_i}`, from `|A(1/2 + it)| = ∏_i N_i^{−1/2} |F_i(t)|`;
* `abs_card_tuples_sub_le_group`, the Type II estimate: for `c > 0`, `a_i > κ > 0`, `θ > 0`, `κ₀ > 0` and `ρ > 2κ₀`
  with `θ + ρ ≤ 1`, and `δ_i > 0` with `Σ 1/δ_i = 1`, each admissible for `D_i = (1 − θ + κ)/(a_i − κ)`, there are
  `η > 0`, `C` and `x₀` with `|#{∏ pⱼ ∈ (x − y, x]} − (y/y₁)·#{∏ pⱼ ∈ (x − y₁, x]}| ≤ C y x^{−η}` for `x ≥ x₀`,
  `x^θ ≤ y ≤ y₁ ≤ x^{1−ρ}` and all boxes with `x^c ≤ Nⱼ ≤ Mⱼ`, `∏_{grp j = i} Mⱼ ≤ 2N_i` and `N_i ≥ x^{a_i}`. The
  conclusion does not involve `κ₀`, so every `ρ > 0` will do (`abs_card_tuples_sub_le_group_of_pos`, `κ₀ = ρ/4`).
  `abs_card_tuples_sub_le_four` is an instance: four primes in the groups `{0, 1}`, `{2}`, `{3}`, with `θ = 13/20`.

The route of the Type II estimate is that of `ShortSieveTypeII.abs_card_tuples_sub_le_of`:
`ShortSieveInterval.norm_sum_Ioc_sub_le` for the coefficients `cnt` on `prods`, with `T₀ = x^{κ₀}`, `T = x^{1−θ+κ}`,
`ε = y x^{−1−κ/2}` and `k = ⌈(6 + κ)/κ⌉` averages, and its four terms.
* No upper bounds. Every product of a tuple exceeds `∏ Nⱼ`, so if `∏ Nⱼ ≥ x` both counts vanish. Otherwise
  `Nⱼ ≤ ∏ Nⱼ < x` for every `j`, and `Mⱼ ≤ 2Nⱼ`, since the other factors of the ratio of its group are at least `1`
  (`le_two_mul_of_prod_le`). A group with no box has `N_i = 1 < x^{a_i}`, so for `x > 1` every group has a box.
* The middle range `T₀ ≤ |t| ≤ T`. `Nⱼ < x` gives `Nⱼ^{κ'} ≤ T₀` for `κ' = min(κ₀, 1/100)`, `Nⱼ ≥ x^c` gives
  `T ≤ Nⱼ^A` for `A = (1 − θ + κ)/c`, and `N_i ≥ x^{a_i}` gives `T ≤ N_i^{D_i}`: the moments of the groups apply on
  `[T₀, T]` and on `[−T, −T₀]`. Hölder gives `∫|A| ≤ ∏_i C_i^{1/δ_i} N_i^{1/2−η_i/δ_i}`, at most `C x^{1/2} x^{−η}`
  since `∏_i N_i = ∏ Nⱼ ≤ x` and `N_i ≥ 1` (`prod_le_rpow_of_prod_le`).
* The low range and the tail, as in `ShortSieveTypeII`, with `Σ_n cnt(n) n^{−1/2} ≤ (∏ Nⱼ)^{1/2} ≤ x^{1/2}`.
* The transitions, with `cnt(n) ≤ r^r` (`norm_cnt_le_pow`) for the `r` boxes in place of the divisor bound.
-/

open Finset Real MeasureTheory DirMean ShortSieveTypeII

noncomputable section

namespace ShortSieveGroup

/-! ### One group of boxes -/

section group

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A number has at most `r^r` representations as an ordered product of primes from the `r` boxes: every entry of a
representation divides the product of a fixed one, so it is one of the `r` entries of that one. -/
lemma norm_cnt_le_pow (N M : ι → ℕ) (n : ℕ) : ‖cnt N M n‖ ≤ (Fintype.card ι : ℝ) ^ Fintype.card ι := by
  rw [cnt, Complex.norm_natCast]
  rcases (filter (fun g => ∏ j, g j = n) (tuples N M)).eq_empty_or_nonempty with h | ⟨g₀, hg₀⟩
  · rw [h, card_empty, Nat.cast_zero]
    positivity
  have hprime : ∀ g ∈ tuples N M, ∀ j, (g j).Prime := fun g hg j =>
    (mem_filter.1 (Fintype.mem_piFinset.1 hg j)).2
  have hg₀' := mem_filter.1 hg₀
  have hsub : filter (fun g => ∏ j, g j = n) (tuples N M) ⊆ Fintype.piFinset fun _ : ι => univ.image g₀ := by
    intro g hg
    have hg' := mem_filter.1 hg
    refine Fintype.mem_piFinset.2 fun j => ?_
    have hdvd : g j ∣ ∏ j', g₀ j' := by
      rw [hg₀'.2, ← hg'.2]
      exact dvd_prod_of_mem _ (mem_univ j)
    obtain ⟨j', -, hj'⟩ := ((hprime g hg'.1 j).prime.dvd_finsetProd_iff _).1 hdvd
    rw [(Nat.prime_dvd_prime_iff_eq (hprime g hg'.1 j) (hprime g₀ hg₀'.1 j')).1 hj']
    exact mem_image_of_mem _ (mem_univ j')
  have h1 := card_le_card hsub
  rw [Fintype.card_piFinset, prod_const, card_univ] at h1
  have h2 : (univ.image g₀).card ≤ Fintype.card ι := card_image_le.trans card_univ.le
  calc ((filter (fun g => ∏ j, g j = n) (tuples N M)).card : ℝ)
      ≤ (((univ.image g₀).card ^ Fintype.card ι : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (Fintype.card ι : ℝ) ^ Fintype.card ι := by push_cast; gcongr

omit [Fintype ι] in
/-- The box ratios from the ratio of a product: `Mⱼ ≤ 2Nⱼ` for `j ∈ s` when `∏_s Mⱼ ≤ 2 ∏_s Nⱼ`, `0 < Nⱼ ≤ Mⱼ`. -/
lemma le_two_mul_of_prod_le {s : Finset ι} {N M : ι → ℕ} (hN : ∀ j ∈ s, 0 < N j) (hNM : ∀ j ∈ s, N j ≤ M j)
    (h : ∏ j ∈ s, M j ≤ 2 * ∏ j ∈ s, N j) {j : ι} (hj : j ∈ s) : M j ≤ 2 * N j := by
  rw [← mul_prod_erase s M hj, ← mul_prod_erase s N hj] at h
  have h1 : ∏ i ∈ s.erase j, N i ≤ ∏ i ∈ s.erase j, M i := prod_le_prod fun i hi => hNM i (mem_of_mem_erase hi)
  have h0 : 0 < ∏ i ∈ s.erase j, N i := prod_pos fun i hi => hN i (mem_of_mem_erase hi)
  refine Nat.le_of_mul_le_mul_right ?_ h0
  calc M j * ∏ i ∈ s.erase j, N i ≤ M j * ∏ i ∈ s.erase j, M i := Nat.mul_le_mul_left _ h1
    _ ≤ 2 * (N j * ∏ i ∈ s.erase j, N i) := h
    _ = 2 * N j * ∏ i ∈ s.erase j, N i := by ring

/-- The products of the tuples lie in `(∏ Nⱼ, 2 ∏ Nⱼ]` when `∏ Mⱼ ≤ 2 ∏ Nⱼ` and there is a box. -/
lemma prods_subset [Nonempty ι] {N M : ι → ℕ} (hN : ∀ j, 0 < N j) (hM : ∏ j, M j ≤ 2 * ∏ j, N j) :
    prods N M ⊆ Ioc (∏ j, N j) (2 * ∏ j, N j) := by
  intro n hn
  obtain ⟨g, hg, rfl⟩ := mem_image.1 hn
  have hb : ∀ j, N j < g j ∧ g j ≤ M j := fun j => mem_Ioc.1 (mem_filter.1 (Fintype.mem_piFinset.1 hg j)).1
  exact mem_Ioc.2 ⟨prod_lt_prod_of_nonempty₀ (fun j _ => hN j) (fun j _ => (hb j).1) univ_nonempty,
    (prod_le_prod fun j _ => (hb j).2).trans hM⟩

/-- `Σ_n k c_n n^{−it} = k Σ_n c_n n^{−it}`. -/
lemma dp_const_mul (S : Finset ℕ) (c : ℕ → ℂ) (k : ℂ) (t : ℝ) : dp S (fun n => k * c n) t = k * dp S c t := by
  simp only [dp, mul_sum, mul_assoc]

/-- The product of the weighted prime polynomials of the boxes: `∏ⱼ Pⱼ(t) = (∏ⱼ Nⱼ)^{1/2} Σ_n cnt(n) n^{−1/2−it}`
(`dp_prods`). -/
lemma prod_dp_boxWt_eq (N M : ι → ℕ) (hN : ∀ j, 0 < N j) (t : ℝ) :
    ∏ j, dp (box (N j) (M j)) (boxWt (N j)) t =
      (((∏ j, (N j : ℝ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * dp (prods N M) (ShortSieveInterval.coef (cnt N M)) t := by
  have hN0 : ∀ j, (0 : ℝ) < N j := fun j => by exact_mod_cast hN j
  have hP : 0 < ∏ j, (N j : ℝ) := prod_pos fun j _ => hN0 j
  rw [dp_prods N M hN t, prod_mul_distrib, ← mul_assoc, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
    Real.finsetProd_rpow _ _ (fun j _ => (hN0 j).le), ← Real.rpow_add hP]
  norm_num

/-- **Harman's moment lemma for a group of boxes.** For `0 < κ < 1/50`, `A > 0` and `δ` admissible for `D`
(`MomentOK D δ`) there are `η > 0`, `C ≥ 0` and `N₀` such that for boxes `(Nⱼ, Mⱼ]` with `Nⱼ ≥ N₀` and `Nⱼ ≤ Mⱼ`
whose product `N = ∏ Nⱼ` has `∏ Mⱼ ≤ 2N` and `N > 1` (there is a box), and for `Nⱼ^κ ≤ a ≤ b ≤ Nⱼ^A` (every `j`)
with `b ≤ N^D`, both `∫_a^b |F|^δ` and `∫_{−b}^{−a} |F|^δ` are at most `C N^{δ−η}`, where
`F(t) = ∏ⱼ Σ_{Nⱼ<p≤Mⱼ} (Nⱼ/p)^{1/2} p^{−it}`. `F` is the Dirichlet polynomial `Σ_n cnt(n) (N/n)^{1/2} n^{−it}` on
`(N, 2N]` (`prod_dp_boxWt_eq`, `prods_subset`) with `cnt(n) ≤ r^r`, `r` the number of boxes (`norm_cnt_le_pow`), and
`|F| ≤ ∏ⱼ Nⱼ^{1−κ/2} = N^{1−κ/2}` on these heights (`pointwise_boxWt_of`): `F/r^r` satisfies the hypotheses of
`ShortSieveMoment.moment_le_hux` or `ShortSieveMoment.moment_le_mv` with `η₁ = κ/2`, and `C` takes the factor
`r^{rδ}`. -/
theorem moment_group_from {κ A Dx δ : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 50) (hA : 0 < A) (hok : MomentOK Dx δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N M : ι → ℕ, (∀ j, N₀ ≤ N j) → (∀ j, N j ≤ M j) →
      ∏ j, M j ≤ 2 * ∏ j, N j → 1 < ∏ j, N j → ∀ a b : ℝ, (∀ j, (N j : ℝ) ^ κ ≤ a) → a ≤ b →
      (∀ j, b ≤ (N j : ℝ) ^ A) → b ≤ (∏ j, (N j : ℝ)) ^ Dx →
        (∫ t in a..b, ‖∏ j, dp (box (N j) (M j)) (boxWt (N j)) t‖ ^ δ ≤ C * (∏ j, (N j : ℝ)) ^ (δ - η)) ∧
          ∫ t in (-b)..(-a), ‖∏ j, dp (box (N j) (M j)) (boxWt (N j)) t‖ ^ δ ≤
            C * (∏ j, (N j : ℝ)) ^ (δ - η) := by
  -- the moment lemma of `ShortSieveMoment` with `η₁ = κ/2`
  obtain ⟨η, hη, C, N₂, hmom⟩ : ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ,
      S ⊆ Ioc N (2 * N) → ∀ c : ℕ → ℂ, (∀ j ∈ S, ‖c j‖ ≤ 1) → ∀ a b : ℝ, a ≤ b → b - a ≤ (N : ℝ) ^ Dx →
      (∀ t ∈ Set.Icc a b, ‖dp S c t‖ ≤ (N : ℝ) ^ (1 - κ / 2)) →
      ∫ t in a..b, ‖dp S c t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η₂) := by
    rcases hok with ⟨m, hm, hD, hD', hδ⟩ | ⟨k, hk, hD, hδ⟩
    · exact ShortSieveMoment.moment_le_hux hm hD hD' hδ (by positivity)
    · exact ShortSieveMoment.moment_le_mv hk hD hδ (by positivity)
  -- the pointwise bound for one box
  obtain ⟨N₁, hpt⟩ := pointwise_boxWt_of hκ0 hκ hA
  -- the bound `r^r` for the number of representations
  set B : ℝ := (Fintype.card ι : ℝ) ^ Fintype.card ι
  refine ⟨η, hη, B ^ δ * max C 0, by positivity, max (max N₁ N₂) 1,
    fun N M hN hNM hMN hN1 a b ha hab hbA hbD => ?_⟩
  -- a box
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hN1
  obtain ⟨j₀⟩ := id hne
  have hB1 : 1 ≤ B := one_le_pow₀ (by exact_mod_cast Fintype.card_pos)
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hNpos : ∀ j, 0 < N j := fun j => lt_of_lt_of_le (by omega) ((le_max_right _ _).trans (hN j))
  have hN0 : ∀ j, (0 : ℝ) < N j := fun j => by exact_mod_cast hNpos j
  have hM2 : ∀ j, M j ≤ 2 * N j := fun j =>
    le_two_mul_of_prod_le (fun j _ => hNpos j) (fun j _ => hNM j) hMN (mem_univ j)
  -- the product `N`
  set Nn : ℕ := ∏ j, N j
  set P : ℝ := ∏ j, (N j : ℝ) with hP
  have hNnP : (Nn : ℝ) = P := Nat.cast_prod _ _
  have hP0 : 0 < P := prod_pos fun j _ => hN0 j
  have hNn₂ : N₂ ≤ Nn :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans ((hN j₀).trans
      (Nat.le_of_dvd (prod_pos fun j _ => hNpos j) (dvd_prod_of_mem _ (mem_univ j₀))))
  have ha0 : 0 ≤ a := le_trans (by positivity) (ha j₀)
  -- `F/r^r` as one Dirichlet polynomial with coefficients at most `1`
  set S : Finset ℕ := prods N M with hS
  have hSsub : S ⊆ Ioc Nn (2 * Nn) := prods_subset hNpos hMN
  set c : ℕ → ℂ := fun n => (((P ^ (1 / 2 : ℝ) / B : ℝ)) : ℂ) * ShortSieveInterval.coef (cnt N M) n with hc
  have hc1 : ∀ n ∈ S, ‖c n‖ ≤ 1 := by
    intro n hn
    have hPn : P ≤ n := by
      rw [← hNnP]
      exact_mod_cast (mem_Ioc.1 (hSsub hn)).1.le
    have hn1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ P ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hP0 hPn (by norm_num)
    rw [hc, norm_mul, ShortSieveInterval.coef, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    calc P ^ (1 / 2 : ℝ) / B * (‖cnt N M n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)))
        ≤ P ^ (1 / 2 : ℝ) / B * (B * P ^ (-(1 / 2 : ℝ))) := by
          gcongr
          exact norm_cnt_le_pow N M n
      _ = P ^ (1 / 2 : ℝ) * P ^ (-(1 / 2 : ℝ)) := by field_simp
      _ = 1 := by rw [← Real.rpow_add hP0]; norm_num
  have hdp : ∀ t, ‖∏ j, dp (box (N j) (M j)) (boxWt (N j)) t‖ = B * ‖dp S c t‖ := by
    intro t
    rw [prod_dp_boxWt_eq N M hNpos t, ← hP, ← hS, hc, dp_const_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    field_simp
  -- the pointwise bound for `F`
  have hpt' : ∀ t : ℝ, a ≤ |t| → |t| ≤ b → ‖dp S c t‖ ≤ (Nn : ℝ) ^ (1 - κ / 2) := by
    intro t ht1 ht2
    have h1 : ‖dp S c t‖ ≤ ‖∏ j, dp (box (N j) (M j)) (boxWt (N j)) t‖ := by
      rw [hdp]
      exact le_mul_of_one_le_left (norm_nonneg _) hB1
    refine h1.trans ?_
    rw [norm_prod, hNnP, hP, ← Real.finsetProd_rpow _ _ (fun j _ => (hN0 j).le)]
    exact prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ =>
      hpt (N j) ((le_max_left _ _).trans ((le_max_left _ _).trans (hN j))) (M j) (hNM j) (hM2 j) t
        ((ha j).trans ht1) (ht2.trans (hbA j))
  -- the moment over an interval of heights in `[a, b]`
  have key : ∀ a' b' : ℝ, a' ≤ b' → b' - a' ≤ P ^ Dx → (∀ t ∈ Set.Icc a' b', a ≤ |t| ∧ |t| ≤ b) →
      ∫ t in a'..b', ‖∏ j, dp (box (N j) (M j)) (boxWt (N j)) t‖ ^ δ ≤ B ^ δ * max C 0 * P ^ (δ - η) := by
    intro a' b' hab' hba' ht
    have h := hmom Nn hNn₂ S hSsub c hc1 a' b' hab' (by rwa [hNnP]) fun t ht' =>
      hpt' t (ht t ht').1 (ht t ht').2
    rw [hNnP] at h
    simp_rw [hdp, Real.mul_rpow hB0 (norm_nonneg _)]
    rw [intervalIntegral.integral_const_mul]
    calc B ^ δ * ∫ t in a'..b', ‖dp S c t‖ ^ δ ≤ B ^ δ * (C * P ^ (δ - η)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ B ^ δ * (max C 0 * P ^ (δ - η)) := by
          gcongr
          exact le_max_left _ _
      _ = B ^ δ * max C 0 * P ^ (δ - η) := by ring
  refine ⟨key a b hab (by linarith) fun t ht => ?_, key (-b) (-a) (by linarith) (by linarith) fun t ht => ?_⟩
  · rw [abs_of_nonneg (ha0.trans ht.1)]
    exact ht
  · rw [abs_of_nonpos (by linarith [ht.2])]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

end group

/-! ### Hölder over the groups -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [Fintype G] [DecidableEq G]

/-- **The middle range by Hölder over the groups.** For boxes sorted into groups by `grp : ι → G`, if
`∫_a^b |F_i|^{δ_i} ≤ C_i N_i^{δ_i−η_i}` for every group `i`, where `F_i = ∏_{grp j = i} Pⱼ` is the product of the
weighted prime polynomials of the boxes of the group and `N_i = ∏_{grp j = i} Nⱼ`, with `δ_i > 0`, `Σ 1/δ_i = 1` and
`C_i ≥ 0`, then `∫_a^b |A(1/2 + it)| dt ≤ ∏_i C_i^{1/δ_i} N_i^{1/2} N_i^{−η_i/δ_i}`, from
`|A(1/2 + it)| = ∏_i N_i^{−1/2} |F_i(t)|` (`dp_prods`, `Fintype.prod_fiberwise`) and `integral_prod_le`. -/
theorem integral_norm_dp_prods_le_group (grp : ι → G) (N M : ι → ℕ) (hN : ∀ j, 0 < N j) {a b : ℝ} (hab : a ≤ b)
    {δ : G → ℝ} (hδ : ∀ i, 0 < δ i) (hδs : ∑ i, 1 / δ i = 1) {η C : G → ℝ} (hC : ∀ i, 0 ≤ C i)
    (hmom : ∀ i, ∫ t in a..b, ‖∏ j : {j // grp j = i}, dp (box (N j) (M j)) (boxWt (N j)) t‖ ^ δ i ≤
      C i * (∏ j : {j // grp j = i}, (N j : ℝ)) ^ (δ i - η i)) :
    ∫ t in a..b, ‖dp (prods N M) (ShortSieveInterval.coef (cnt N M)) t‖ ≤
      ∏ i, (C i ^ (1 / δ i) * ((∏ j : {j // grp j = i}, (N j : ℝ)) ^ (1 / 2 : ℝ) *
        (∏ j : {j // grp j = i}, (N j : ℝ)) ^ (-(η i / δ i)))) := by
  have hN0 : ∀ j, (0 : ℝ) < N j := fun j => by exact_mod_cast hN j
  set u : G → ℝ := fun i => ∏ j : {j // grp j = i}, (N j : ℝ)
  have hu0 : ∀ i, 0 < u i := fun i => prod_pos fun j _ => hN0 j
  set F : G → ℝ → ℝ := fun i t => ‖∏ j : {j // grp j = i}, dp (box (N j) (M j)) (boxWt (N j)) t‖
  have hnorm : ∀ t, ‖dp (prods N M) (ShortSieveInterval.coef (cnt N M)) t‖ =
      (∏ i, u i ^ (-(1 / 2 : ℝ))) * ∏ i, F i t := by
    intro t
    rw [← prod_mul_distrib, dp_prods N M hN t, ← Fintype.prod_fiberwise grp, norm_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [prod_mul_distrib, norm_mul, ← Complex.ofReal_prod, Complex.norm_real,
      Real.norm_of_nonneg (prod_nonneg fun j _ => by positivity),
      Real.finsetProd_rpow _ (fun j : {j // grp j = i} => (N j : ℝ)) (fun j _ => (hN0 j).le)]
  simp_rw [hnorm]
  rw [intervalIntegral.integral_const_mul]
  set K : G → ℝ := fun i => (C i * u i ^ (δ i - η i)) ^ (1 / δ i) with hK
  have hK0 : ∀ i, 0 ≤ K i := fun i => Real.rpow_nonneg (mul_nonneg (hC i) (Real.rpow_nonneg (hu0 i).le _)) _
  have hhol := integral_prod_le univ (f := F)
    (fun i _ => (continuous_finsetProd univ fun j _ => continuous_dp _ _).norm) (fun i _ t => norm_nonneg _) hab
    (fun i _ => hδ i) hδs (fun i _ => hK0 i) fun i _ => by
      rw [hK, ← Real.rpow_mul (mul_nonneg (hC i) (Real.rpow_nonneg (hu0 i).le _)), one_div_mul_cancel (hδ i).ne',
        Real.rpow_one]
      exact hmom i
  have hc0 : 0 ≤ ∏ i, u i ^ (-(1 / 2 : ℝ)) := prod_nonneg fun i _ => Real.rpow_nonneg (hu0 i).le _
  calc (∏ i, u i ^ (-(1 / 2 : ℝ))) * ∫ t in a..b, ∏ i, F i t ≤ (∏ i, u i ^ (-(1 / 2 : ℝ))) * ∏ i, K i :=
        mul_le_mul_of_nonneg_left hhol hc0
    _ = ∏ i, (u i ^ (-(1 / 2 : ℝ)) * K i) := prod_mul_distrib.symm
    _ = _ := by
        refine prod_congr rfl fun i _ => ?_
        simp only [hK]
        rw [Real.mul_rpow (hC i) (Real.rpow_nonneg (hu0 i).le _), ← Real.rpow_mul (hu0 i).le]
        have e : (δ i - η i) * (1 / δ i) = 1 - η i / δ i := by
          rw [mul_one_div, sub_div, div_self (hδ i).ne']
        rw [e]
        calc u i ^ (-(1 / 2 : ℝ)) * (C i ^ (1 / δ i) * u i ^ (1 - η i / δ i))
            = C i ^ (1 / δ i) * (u i ^ (-(1 / 2 : ℝ)) * u i ^ (1 - η i / δ i)) := by ring
          _ = _ := by
              rw [← Real.rpow_add (hu0 i), ← Real.rpow_add (hu0 i)]
              congr 2
              ring

/-- The middle range in terms of `x`: for `u_i ≥ 1` with `∏ u_i ≤ x`, `e_i ≥ 0` and `x^γ ≤ u_{i₀}`,
`∏_i c_i u_i^{1/2} u_i^{−e_i} ≤ (∏_i c_i) x^{1/2} x^{−γ e_{i₀}}`. -/
lemma prod_le_rpow_of_prod_le {u : G → ℝ} {x : ℝ} (hx : 1 ≤ x) (hu1 : ∀ i, 1 ≤ u i) (hux : ∏ i, u i ≤ x)
    {c e : G → ℝ} (hc : ∀ i, 0 ≤ c i) (he : ∀ i, 0 ≤ e i) (i₀ : G) {γ : ℝ} (hγ : x ^ γ ≤ u i₀) :
    ∏ i, (c i * (u i ^ (1 / 2 : ℝ) * u i ^ (-e i))) ≤ (∏ i, c i) * x ^ (1 / 2 : ℝ) * x ^ (-(γ * e i₀)) := by
  have hx0 : 0 < x := by linarith
  have hu0 : ∀ i, 0 ≤ u i := fun i => zero_le_one.trans (hu1 i)
  rw [prod_mul_distrib, prod_mul_distrib, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun i _ => hc i)
  refine mul_le_mul ?_ ?_ (prod_nonneg fun i _ => Real.rpow_nonneg (hu0 i) _) (by positivity)
  · rw [Real.finsetProd_rpow _ _ (fun i _ => hu0 i)]
    exact Real.rpow_le_rpow (prod_nonneg fun i _ => hu0 i) hux (by norm_num)
  · rw [← mul_prod_erase univ _ (mem_univ i₀)]
    have h1 : ∏ i ∈ univ.erase i₀, u i ^ (-e i) ≤ 1 :=
      prod_le_one₀ (fun i _ => Real.rpow_nonneg (hu0 i) _) fun i _ =>
        Real.rpow_le_one_of_one_le_of_nonpos (hu1 i) (by linarith [he i])
    have h2 : u i₀ ^ (-e i₀) ≤ x ^ (-(γ * e i₀)) := by
      calc u i₀ ^ (-e i₀) ≤ (x ^ γ) ^ (-e i₀) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hγ (by linarith [he i₀])
        _ = x ^ (-(γ * e i₀)) := by rw [← Real.rpow_mul hx0.le]; ring_nf
    calc u i₀ ^ (-e i₀) * ∏ i ∈ univ.erase i₀, u i ^ (-e i) ≤ u i₀ ^ (-e i₀) * 1 :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (hu0 i₀) _)
      _ ≤ x ^ (-(γ * e i₀)) := by rw [mul_one]; exact h2

/-! ### The Type II estimate -/

/-- **Type II estimates for groups of prime boxes, with the low range up to `x^{κ₀}`.** Let `grp : ι → G` sort the
boxes into groups, let `c > 0`, `a_i > κ > 0`, `θ > 0`, `κ₀ > 0` and `ρ > 2κ₀` with `θ + ρ ≤ 1`, and let `δ_i > 0`
with `Σ_i 1/δ_i = 1`, each `δ_i` admissible (`MomentOK`) for `D_i = (1 − θ + κ)/(a_i − κ)`. There are `η > 0`, `C`
and `x₀` such that for `x ≥ x₀`, `x^θ ≤ y ≤ y₁ ≤ x^{1−ρ}` and boxes `(Nⱼ, Mⱼ]` with `x^c ≤ Nⱼ ≤ Mⱼ` whose groups have
products `N_i = ∏_{grp j = i} Nⱼ ≥ x^{a_i}` and ratios `∏_{grp j = i} Mⱼ ≤ 2N_i`, the numbers of tuples `(pⱼ)ⱼ`, `pⱼ`
prime in `(Nⱼ, Mⱼ]`, with `∏ⱼ pⱼ ∈ (x − y, x]` and with `∏ⱼ pⱼ ∈ (x − y₁, x]` satisfy
`|#{∏ⱼ pⱼ ∈ (x − y, x]} − (y/y₁)·#{∏ⱼ pⱼ ∈ (x − y₁, x]}| ≤ C y x^{−η}`. The boxes have no upper bounds: if
`∏ Nⱼ ≥ x` both counts vanish, and otherwise `Nⱼ < x` and `Mⱼ ≤ 2Nⱼ` (`le_two_mul_of_prod_le`). The proof is that of
`ShortSieveTypeII.abs_card_tuples_sub_le_of` with one Hölder factor per group (`integral_norm_dp_prods_le_group`),
each with the moment lemma of its group (`moment_group_from`) on the heights from `Nⱼ^{κ'} ≤ x^{κ'} ≤ T₀`,
`κ' = min(κ₀, 1/100)`, up to `T = x^{1−θ+κ}`, which is at most `Nⱼ^{(1−θ+κ)/c}` and `N_i^{D_i}`; the transitions take
`cnt(n) ≤ r^r` (`norm_cnt_le_pow`). -/
theorem abs_card_tuples_sub_le_group (grp : ι → G) {a δ : G → ℝ} {c θ κ κ₀ ρ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (ha : ∀ i, κ < a i) (hθ : 0 < θ) (hκ₀ : 0 < κ₀) (hρ : 2 * κ₀ < ρ) (hθρ : θ + ρ ≤ 1) (hδ : ∀ i, 0 < δ i)
    (hδs : ∑ i, 1 / δ i = 1) (hok : ∀ i, MomentOK ((1 - θ + κ) / (a i - κ)) (δ i)) :
    ∃ η : ℝ, 0 < η ∧ ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y y₁ : ℝ, x ^ θ ≤ y → y ≤ y₁ → y₁ ≤ x ^ (1 - ρ) →
      ∀ N M : ι → ℕ, (∀ j, x ^ c ≤ N j) → (∀ j, N j ≤ M j) →
        (∀ i, ∏ j ∈ univ.filter (grp · = i), M j ≤ 2 * ∏ j ∈ univ.filter (grp · = i), N j) →
        (∀ i, x ^ a i ≤ ∏ j ∈ univ.filter (grp · = i), (N j : ℝ)) →
        |(#{g ∈ tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
          y / y₁ * #{g ∈ tuples N M | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
          C * y * x ^ (-η) := by
  -- a group
  obtain ⟨i₀⟩ : Nonempty G := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hδs
  -- the exponents
  have haκ : ∀ i, 0 < a i - κ := fun i => sub_pos.2 (ha i)
  have ha0 : ∀ i, 0 < a i := fun i => hκ.trans (ha i)
  have hD0 : ∀ i, 0 < (1 - θ + κ) / (a i - κ) := fun i => div_pos (by linarith) (haκ i)
  -- the start `κ' = min(κ₀, 1/100)` of the moments and the end `A = (1 − θ + κ)/c` of the pointwise bounds
  set κ' : ℝ := min κ₀ (1 / 100) with hκ'
  have hκ'0 : 0 < κ' := lt_min hκ₀ (by norm_num)
  have hκ'1 : κ' < 1 / 50 := (min_le_right _ _).trans_lt (by norm_num)
  have hκ'κ₀ : κ' ≤ κ₀ := min_le_left _ _
  set A : ℝ := (1 - θ + κ) / c with hA
  have hA0 : 0 < A := div_pos (by linarith) hc
  -- the moments of the groups and the comparison
  choose η₁ hη₁ C₁ hC₁ N₁ hmom using fun i =>
    moment_group_from (ι := {j // grp j = i}) hκ'0 hκ'1 hA0 (hok i)
  obtain ⟨C₀, hC₀, hcmp⟩ := ShortSieveInterval.norm_sum_Ioc_sub_le
  -- the parameters
  set ηm : ℝ := a i₀ * (η₁ i₀ / δ i₀) with hηm
  have hηm0 : 0 < ηm := mul_pos (ha0 i₀) (div_pos (hη₁ i₀) (hδ i₀))
  set k : ℕ := ⌈(6 + κ) / κ⌉₊ with hk
  have hkκ : 6 + κ ≤ k * κ := by
    have := Nat.le_ceil ((6 + κ) / κ)
    rwa [div_le_iff₀ hκ] at this
  set β : ℝ := min κ θ / 4 with hβ
  have hβ0 : 0 < β := div_pos (lt_min hκ hθ) (by norm_num)
  have hβκ : β ≤ κ / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hβθ : β ≤ θ / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hKm0 : 0 ≤ ∏ i, C₁ i ^ (1 / δ i) := prod_nonneg fun i _ => Real.rpow_nonneg (hC₁ i) _
  set CB : ℝ := (Fintype.card ι : ℝ) ^ Fintype.card ι with hCB
  have hCB0 : 0 ≤ CB := by positivity
  set η : ℝ := min (min ηm (ρ - 2 * κ₀)) β with hη
  have hη0 : 0 < η := lt_min (lt_min hηm0 (by linarith)) hβ0
  have hηm' : η ≤ ηm := (min_le_left _ _).trans (min_le_left _ _)
  have hηρ : η ≤ ρ - 2 * κ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hηβ : η ≤ β := min_le_right _ _
  set Ctot : ℝ := 2 * C₀ * (∏ i, C₁ i ^ (1 / δ i)) + 4 * C₀ + C₀ * 2 ^ k + 8 * CB * (k + 4)
  have hCtot0 : 0 ≤ Ctot := by
    have := hC₀.le
    positivity
  -- the threshold
  set N₀ : ℕ := ∑ i, N₁ i with hN₀
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ 2 ≤ x ^ κ ∧ 2 ≤ x ^ ρ ∧ (N₀ : ℝ) ≤ x ^ c := by
    have h1 := tendsto_rpow_atTop hκ
    have h2 := tendsto_rpow_atTop (show 0 < ρ by linarith)
    have h3 := tendsto_rpow_atTop hc
    exact (Filter.eventually_ge_atTop 1).and ((h1.eventually_ge_atTop 2).and ((h2.eventually_ge_atTop 2).and
      (h3.eventually_ge_atTop _)))
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨η, hη0, Ctot, x₀, fun x hx y y₁ hy hyy₁ hy₁ N M hNc hNM hMN hNa => ?_⟩
  obtain ⟨hx1, hxκ, hxρ, hxN⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hx1' : 1 < x := by
    by_contra hc'
    have hx' : x = 1 := le_antisymm (not_lt.1 hc') hx1
    rw [hx', Real.one_rpow] at hxκ
    norm_num at hxκ
  have hy1 : 1 ≤ y := le_trans (Real.one_le_rpow hx1 hθ.le) hy
  have hy0 : 0 < y := by linarith
  have hy₁0 : 0 < y₁ := by linarith
  -- the boxes
  have hNpos : ∀ j, 0 < N j := fun j => by
    have h : (0 : ℝ) < N j := lt_of_lt_of_le (by positivity) (hNc j)
    exact_mod_cast h
  have hN0 : ∀ j, (0 : ℝ) < N j := fun j => by exact_mod_cast hNpos j
  have hM2 : ∀ j, M j ≤ 2 * N j := fun j =>
    le_two_mul_of_prod_le (fun j _ => hNpos j) (fun j _ => hNM j) (hMN (grp j)) (mem_filter.2 ⟨mem_univ j, rfl⟩)
  -- the groups
  have hsub : ∀ i (f : ι → ℕ), ∏ j ∈ univ.filter (grp · = i), f j = ∏ j : {j // grp j = i}, f j := fun i f =>
    prod_subtype _ (fun j => by simp) _
  set u : G → ℝ := fun i => ∏ j : {j // grp j = i}, (N j : ℝ) with hu
  have hua : ∀ i, x ^ a i ≤ u i := fun i => (hNa i).trans_eq (prod_subtype _ (fun j => by simp) _)
  have hu1 : ∀ i, 1 < u i := fun i => lt_of_lt_of_le (Real.one_lt_rpow hx1' (ha0 i)) (hua i)
  have hprod_u : ∏ i, u i = ∏ j, (N j : ℝ) := Fintype.prod_fiberwise grp fun j => (N j : ℝ)
  obtain ⟨⟨j₀, -⟩⟩ : Nonempty {j // grp j = i₀} := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hu1 i₀
    simp [hu] at this
  -- if `∏ Nⱼ ≥ x` both counts vanish
  rcases le_or_gt x (∏ j, (N j : ℝ)) with hbig | hsmall
  · have hzero : ∀ y' : ℝ, #{g ∈ tuples N M | x - y' < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} = 0 := by
      intro y'
      rw [card_eq_zero, filter_eq_empty_iff]
      intro g hg hgx
      have hlt : ∏ j, (N j : ℝ) < ((∏ j, g j : ℕ) : ℝ) := by
        rw [Nat.cast_prod]
        exact prod_lt_prod_of_nonempty₀ (fun j _ => hN0 j)
          (fun j _ => by exact_mod_cast (mem_Ioc.1 (mem_filter.1 (Fintype.mem_piFinset.1 hg j)).1).1)
          ⟨j₀, mem_univ _⟩
      linarith [hgx.2]
    rw [hzero, hzero]
    simp only [Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hCtot0 hy0.le) (by positivity)
  -- otherwise every box is below `x`
  have hNx : ∀ j, (N j : ℝ) ≤ x := fun j => by
    refine le_trans ?_ hsmall.le
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (prod_pos fun j _ => hNpos j) (dvd_prod_of_mem _ (mem_univ j))
  -- the heights `T₀ = x^{κ₀}` and `T = x^{1−θ+κ}`
  have hT₀1 : 1 ≤ x ^ κ₀ := Real.one_le_rpow hx1 hκ₀.le
  have hT₀T : x ^ κ₀ ≤ x ^ (1 - θ + κ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hT₀N : ∀ j, (N j : ℝ) ^ κ' ≤ x ^ κ₀ := fun j => by
    calc (N j : ℝ) ^ κ' ≤ x ^ κ' := Real.rpow_le_rpow (Nat.cast_nonneg _) (hNx j) hκ'0.le
      _ ≤ x ^ κ₀ := Real.rpow_le_rpow_of_exponent_le hx1 hκ'κ₀
  have hTA : ∀ j, x ^ (1 - θ + κ) ≤ (N j : ℝ) ^ A := fun j => by
    calc x ^ (1 - θ + κ) = (x ^ c) ^ A := by rw [← Real.rpow_mul hx0.le, hA, mul_div_cancel₀ _ hc.ne']
      _ ≤ (N j : ℝ) ^ A := Real.rpow_le_rpow (by positivity) (hNc j) hA0.le
  have hTD : ∀ i, x ^ (1 - θ + κ) ≤ u i ^ ((1 - θ + κ) / (a i - κ)) := fun i => by
    calc x ^ (1 - θ + κ) = (x ^ (a i - κ)) ^ ((1 - θ + κ) / (a i - κ)) := by
          rw [← Real.rpow_mul hx0.le, mul_div_cancel₀ _ (haκ i).ne']
      _ ≤ u i ^ ((1 - θ + κ) / (a i - κ)) := Real.rpow_le_rpow (by positivity)
          ((Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans (hua i)) (hD0 i).le
  -- the middle range
  have hN₁ : ∀ i (j : {j // grp j = i}), N₁ i ≤ N j := fun i j => by
    have h1 : N₁ i ≤ N₀ := single_le_sum (fun i _ => Nat.zero_le (N₁ i)) (mem_univ i)
    have h2 : (N₀ : ℝ) ≤ N j := hxN.trans (hNc j)
    have h3 : N₀ ≤ N j := by exact_mod_cast h2
    omega
  have hMNs : ∀ i, ∏ j : {j // grp j = i}, M j ≤ 2 * ∏ j : {j // grp j = i}, N j := fun i => by
    rw [← hsub i M, ← hsub i N]
    exact hMN i
  have hNs1 : ∀ i, 1 < ∏ j : {j // grp j = i}, N j := fun i => by
    have h : (1 : ℝ) < ∏ j : {j // grp j = i}, (N j : ℝ) := hu1 i
    exact_mod_cast h
  have hm := fun i => hmom i (fun j => N j) (fun j => M j) (hN₁ i) (fun j => hNM j) (hMNs i) (hNs1 i)
    (x ^ κ₀) (x ^ (1 - θ + κ)) (fun j => hT₀N j) hT₀T (fun j => hTA j) (hTD i)
  have hprod := prod_le_rpow_of_prod_le hx1 (fun i => (hu1 i).le) (hprod_u.trans_le hsmall.le)
    (c := fun i => C₁ i ^ (1 / δ i)) (e := fun i => η₁ i / δ i) (fun i => Real.rpow_nonneg (hC₁ i) _)
    (fun i => (div_pos (hη₁ i) (hδ i)).le) i₀ (hua i₀)
  have hI₁ := (integral_norm_dp_prods_le_group grp N M hNpos hT₀T hδ hδs hC₁ fun i => (hm i).1).trans hprod
  have hI₂ := (integral_norm_dp_prods_le_group grp N M hNpos (neg_le_neg hT₀T) hδ hδs hC₁
    fun i => (hm i).2).trans hprod
  -- the low range
  have hL₁ : ∑ n ∈ prods N M, ‖ShortSieveInterval.coef (cnt N M) n‖ ≤ x ^ (1 / 2 : ℝ) :=
    (sum_norm_coef_le N M hNpos hM2).trans
      (Real.rpow_le_rpow (prod_nonneg fun j _ => Nat.cast_nonneg _) hsmall.le (by norm_num))
  have hI₀ : ∫ t in (-x ^ κ₀)..x ^ κ₀,
      ‖dp (prods N M) (ShortSieveInterval.coef (cnt N M)) t‖ ≤ 2 * x ^ κ₀ * x ^ (1 / 2 : ℝ) := by
    refine (ShortSieveInterval.integral_norm_dp_le _ _ (by linarith)).trans ?_
    rw [show x ^ κ₀ - -x ^ κ₀ = 2 * x ^ κ₀ by ring]
    exact mul_le_mul_of_nonneg_left hL₁ (by positivity)
  -- the comparison
  have hε0 : 0 < y * x ^ (-1 - κ / 2) := by positivity
  have hε1 : y * x ^ (-1 - κ / 2) < 1 := by
    calc y * x ^ (-1 - κ / 2) ≤ x ^ (1 - ρ) * x ^ (-1 - κ / 2) := by gcongr; linarith
      _ = x ^ (-ρ - κ / 2) := by rw [← Real.rpow_add hx0]; ring_nf
      _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx1' (by linarith)
  have hy₁x : y₁ ≤ x / 2 := by
    calc y₁ ≤ x ^ (1 - ρ) := hy₁
      _ = x / x ^ ρ := by rw [Real.rpow_sub hx0, Real.rpow_one]
      _ ≤ x / 2 := div_le_div_of_nonneg_left hx0.le (by norm_num) hxρ
  have hB : ∀ n ∈ prods N M, ‖cnt N M n‖ ≤ CB * x ^ β := fun n _ =>
    (norm_cnt_le_pow N M n).trans (le_mul_of_one_le_right hCB0 (Real.one_le_rpow hx1 hβ0.le))
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
  have u1 := hX (a i₀ * (η₁ i₀ / δ i₀)) hηm' (2 * C₀ * (∏ i, C₁ i ^ (1 / δ i)) * y) (by positivity)
  have u2 := hX (ρ - 2 * κ₀) hηρ (4 * C₀ * y) (by positivity)
  rw [neg_sub] at u2
  have u3 := hX 1 (by linarith) (C₀ * 2 ^ k * y) (by positivity)
  have u4 := hX β hηβ (8 * CB * (k + 4) * y) (by positivity)
  refine h.trans (le_of_le_of_eq (add_le_add (add_le_add (add_le_add (t1.trans u1) (t2.trans u2))
    (t3.trans u3)) (t4.trans u4)) ?_)
  ring

/-- **Type II estimates for groups of prime boxes, for every `ρ > 0`.** The conclusion of
`abs_card_tuples_sub_le_group` under its hypotheses with `ρ > 0` in place of `κ₀ > 0` and `ρ > 2κ₀`:
`abs_card_tuples_sub_le_group` with `κ₀ = ρ/4`. -/
theorem abs_card_tuples_sub_le_group_of_pos (grp : ι → G) {a δ : G → ℝ} {c θ κ ρ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (ha : ∀ i, κ < a i) (hθ : 0 < θ) (hρ : 0 < ρ) (hθρ : θ + ρ ≤ 1) (hδ : ∀ i, 0 < δ i) (hδs : ∑ i, 1 / δ i = 1)
    (hok : ∀ i, MomentOK ((1 - θ + κ) / (a i - κ)) (δ i)) :
    ∃ η : ℝ, 0 < η ∧ ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y y₁ : ℝ, x ^ θ ≤ y → y ≤ y₁ → y₁ ≤ x ^ (1 - ρ) →
      ∀ N M : ι → ℕ, (∀ j, x ^ c ≤ N j) → (∀ j, N j ≤ M j) →
        (∀ i, ∏ j ∈ univ.filter (grp · = i), M j ≤ 2 * ∏ j ∈ univ.filter (grp · = i), N j) →
        (∀ i, x ^ a i ≤ ∏ j ∈ univ.filter (grp · = i), (N j : ℝ)) →
        |(#{g ∈ tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
          y / y₁ * #{g ∈ tuples N M | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
          C * y * x ^ (-η) :=
  abs_card_tuples_sub_le_group grp (κ₀ := ρ / 4) hc hκ ha hθ (by positivity) (by linarith) hθρ hδ hδs hok

/-- **Four primes in three groups.** `abs_card_tuples_sub_le_group_of_pos` for four boxes in the groups `{0, 1}`,
`{2}` and `{3}`, with `Nⱼ ≥ x^{1/5}`, `N₀N₁ ≥ x^{49/100}`, `N₂, N₃ ≥ x^{49/200}`, `θ = 13/20`, `κ = 1/1000`,
`ρ = 1/100` and `δ = (19/9, 19/5, 19/5)`, `Σ 1/δ_i = 1`. For the pair `D = (7/20 + 1/1000)/(49/100 − 1/1000)` is
`351/489 ≤ 1` and `19/9 > 2` (the mean value theorem, `k = 1`); for each single prime `D = 351/244 ∈ (1, 3/2]` and
`4D − 2 = 229/61 < 19/5` (Harman's moment lemma, `m = 1`). The exponents `49/100`, `49/200`, `49/200` sum to
`49/50 < 1`, so boxes with `∏ Nⱼ < x < ∏ Mⱼ` meet the hypotheses for large `x`, for example with the products of the
groups near `x^{1/2}`, `x^{1/4}` and `x^{1/4}`; with exponents summing to `1` the hypotheses would force `∏ Nⱼ ≥ x`,
and both counts would vanish. -/
theorem abs_card_tuples_sub_le_four : ∃ η : ℝ, 0 < η ∧ ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y y₁ : ℝ,
    x ^ (13 / 20 : ℝ) ≤ y → y ≤ y₁ → y₁ ≤ x ^ (99 / 100 : ℝ) → ∀ N M : Fin 4 → ℕ,
      (∀ j, x ^ (1 / 5 : ℝ) ≤ N j) → (∀ j, N j ≤ M j) → M 0 * M 1 ≤ 2 * (N 0 * N 1) → M 2 ≤ 2 * N 2 →
      M 3 ≤ 2 * N 3 → x ^ (49 / 100 : ℝ) ≤ (N 0 : ℝ) * N 1 → x ^ (49 / 200 : ℝ) ≤ N 2 →
      x ^ (49 / 200 : ℝ) ≤ N 3 →
        |(#{g ∈ tuples N M | x - y < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x} : ℝ) -
          y / y₁ * #{g ∈ tuples N M | x - y₁ < ((∏ j, g j : ℕ) : ℝ) ∧ ((∏ j, g j : ℕ) : ℝ) ≤ x}| ≤
          C * y * x ^ (-η) := by
  obtain ⟨η, hη, C, x₀, h⟩ := abs_card_tuples_sub_le_group_of_pos (ι := Fin 4) (G := Fin 3) ![0, 0, 1, 2]
    (a := ![49 / 100, 49 / 200, 49 / 200]) (δ := ![19 / 9, 19 / 5, 19 / 5]) (c := 1 / 5) (θ := 13 / 20)
    (κ := 1 / 1000) (ρ := 1 / 100) (by norm_num) (by norm_num) (fun i => by fin_cases i <;> norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun i => by fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)
    (fun i => by
      fin_cases i
      · exact Or.inr ⟨1, le_rfl, by norm_num, by norm_num⟩
      · exact Or.inl ⟨1, le_rfl, by norm_num, by norm_num, by norm_num⟩
      · exact Or.inl ⟨1, le_rfl, by norm_num, by norm_num, by norm_num⟩)
  refine ⟨η, hη, C, x₀, fun x hx y y₁ hy hyy₁ hy₁ N M hN hNM h01 h2 h3 hN01 hN2 hN3 =>
    h x hx y y₁ hy hyy₁ ?_ N M hN hNM (fun i => ?_) (fun i => ?_)⟩
  · norm_num
    exact hy₁
  · fin_cases i <;> simp [prod_filter, Fin.prod_univ_four] <;> assumption
  · fin_cases i <;> simp [prod_filter, Fin.prod_univ_four] <;> assumption

end ShortSieveGroup

#print axioms ShortSieveGroup.moment_group_from
#print axioms ShortSieveGroup.integral_norm_dp_prods_le_group
#print axioms ShortSieveGroup.abs_card_tuples_sub_le_group
#print axioms ShortSieveGroup.abs_card_tuples_sub_le_group_of_pos
#print axioms ShortSieveGroup.abs_card_tuples_sub_le_four
