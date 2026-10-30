import HalfPlaneFinal
import SieveRough

/-!
# Primes and rough numbers in intervals of relative length `X^{−σ}`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Harman's sieve for primes in `A = (x − y, x]`, `y = x^θ`, compares `A` with `B = (x − y₁, x]`, `y₁ = x^{1−ρ}`, and the
sieve's main terms live in `B`: they need a lower bound for the primes of `B` and upper bounds, with the constant of
Buchstab's function, for the numbers of `B/d = ((x − y₁)/d, x/d]` with no prime factor below `z`. This module proves
both with no hypothesis. The only analytic input is the library's prime number theorem `ψ(t) − t = O(t^{11/12+ε})`
(`HalfPlanePNT.psi_isBigO_eleven_twelfths`, from the zero-free half-plane `Re s > 11/12`), whose error is smaller than
the length `X^{1−σ}` of an interval at `X` when `σ < 1/12`.

Plain statements.

* `abs_theta_sub_theta_le`: for `ε > 0` there is `C` with `|θ(X) − θ(X − H) − H| ≤ C X^{11/12+ε}` for all `X ≥ 1` and
  `0 ≤ H ≤ X`.
* `card_primes_short`: for `σ < 1/12` and `ε > 0`, for all large `X` and every `H` with `X^{1−σ} ≤ H ≤ X/2`,
  `(1 − ε)H/log X ≤ #{p : X − H < p ≤ X} ≤ (1 + ε)H/log X`. `primeCounting_short` is its case `H = X^{1−ρ}`,
  `0 < ρ < 1/12`, for `π(X) − π(X − X^{1−ρ})` (`card_primes_Ioc`).
* `psi_le`: rough numbers from above. Let `0 ≤ σ < 1/12`. For every `U` and `ε > 0` there is `z₀` such that
  `Ψ(X, H; z) ≤ (ω*(u) + ε)H/log z`, `u = log X/log z`, for `z ≥ z₀`, `X ≥ 2`, `z^{−σ}X ≤ H ≤ X/2` and `u ≤ U`.
  Here `Ψ(X, H; z) = #{m ∈ (X − H, X] : p | m ⇒ p ≥ z}` (`Psi`), and `ω*` is the bound for Buchstab's `ω` of
  `SieveCert.omegaC`, as in `SieveRough.psi_le`, the case of the dyadic ranges `(y, 2y]`. The condition `z^{−σ}X ≤ H`
  says that the relative length `H/X` is at least `z^{−σ}`, hence at least `p^{−σ}` at every prime `p ≥ z`, so the
  prime counts of `card_primes_short` apply at every prime the induction reaches. It is uniform in the cofactors:
  for `m ∈ ((x − y₁)/d, x/d]` (`X = x/d`, `H = y₁/d`) it reads `z^{−σ} ≤ y₁/x`. For `y₁ = x^{1−ρ}` and `z ≥ x^c` it
  holds with `σ = ρ/c`, and `σ < 1/12` is `ρ < c/12` (`ρ < 1/300` for `c = 2θ − 1 = 1/25` at `θ = 0.52`).
  `psi_le_rpow` is the case `H = X^{1−ρ}`, `z ≤ X`, with `ρU < 1/12`.
* `card_dvd_rough`, `card_dvd_rough_of_le`: the `n ∈ (X − H, X]` with `d | n` and `n/d` rough for `z` number
  `Ψ(X/d, H/d; z)`, and so do those with `d | n` and `n` rough for `z` when `d`'s prime factors are at least `z`.

The proof:

* `abs_theta_sub_le`: `|θ(t) − t| ≤ C t^{11/12+ε}` for every `t ≥ 1`, from the `O` bound for `ψ`, Mathlib's
  `ψ − θ ≤ 2√t log t` (`Chebyshev.psi_sub_theta_le`) and `log t ≤ 4t^{1/4}`, and `θ(t) ≤ t log 4` below the range of
  the `O` bound. `abs_theta_sub_theta_le` is the difference of the bounds at `X` and `X − H`.
* `card_primes_short`: `Σ_{X−H<p≤X} log p = θ(X) − θ(X − H)` (`sum_log_primes`), and every `log p` lies in
  `(log(X/2), log X]`, so no partial summation is needed. With `η = (1/12 − σ)/2`,
  `C X^{11/12+η} ≤ (ε/2)X^{1−σ} ≤ (ε/2)H` for large `X`, and `(1 + ε/2) log 2 ≤ (ε/2) log(X/2)` turns the division by
  `log(X/2)` into one by `log X`.
* `Psi_eq_zero`, `Psi_le_buchstab`: `Ψ(X, H; z) = 0` when `X < z` and `X − H ≥ 1`, and for `X − H ≥ 1` Buchstab's
  inequality by the least prime factor, `Ψ(X, H; z) ≤ #{p : X − H < p ≤ X} + Σ_{z ≤ p ≤ √X} Ψ(X/p, H/p; p)`. The
  cofactor's interval `((X − H)/p, X/p]` has the same relative length as `(X − H, X]`.
* `Claim`, `claim_step`, `claim_nat`, `psi_le`: the induction on the level `K` in `log X ≤ K log z`, as in
  `SieveRough.claim_step`, with `card_primes_short` in place of `SieveRough.card_primes_dyadic`. At the primes
  `p ∈ [z, √X]` the induction hypothesis leaves `H` times the sum of the dyadic case,
  `Σ_p (ω*((L − log p)/log p) + ε/4)/(p log p)` with `L = log X`, which `SieveRough` bounds (`sumW_le_three`,
  `sumW_gt_three`, `super_M`, `bracket_le`).
-/

open Real Filter Finset
open scoped Chebyshev

namespace ShortSieveLong

/-! ### `θ` on short intervals -/

/-- From the library's prime number theorem, for `ε > 0` there is `C ≥ 0` with `|θ(t) − t| ≤ C t^{11/12+ε}` for every
`t ≥ 1`. -/
theorem abs_theta_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → |θ t - t| ≤ C * t ^ ((11 : ℝ) / 12 + ε) := by
  obtain ⟨C₁, hC₁⟩ := (HalfPlanePNT.psi_isBigO_eleven_twelfths hε).bound
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hC₁
  set a : ℝ := (11 : ℝ) / 12 + ε with ha
  set T' : ℝ := max T 1 with hT'
  have hT'1 : 1 ≤ T' := le_max_right _ _
  refine ⟨max C₁ 0 + 8 + 2 * T', by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hta : 1 ≤ t ^ a := Real.one_le_rpow ht (by positivity)
  have e : (max C₁ 0 + 8 + 2 * T') * t ^ a = max C₁ 0 * t ^ a + 8 * t ^ a + 2 * T' * t ^ a := by ring
  rw [e]
  have hC0 : 0 ≤ max C₁ 0 * t ^ a := mul_nonneg (le_max_right _ _) (by positivity)
  have hT0 : 0 ≤ 2 * T' * t ^ a := by positivity
  by_cases htT : T ≤ t
  · -- the range of the `O` bound
    have h1 : |ψ t - t| ≤ max C₁ 0 * t ^ a := by
      have := hT t htT
      simp only [Pi.sub_apply, id, Real.norm_eq_abs] at this
      rw [abs_of_pos (Real.rpow_pos_of_pos ht0 _)] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have h2 : 0 ≤ ψ t - θ t := sub_nonneg.2 (Chebyshev.theta_le_psi t)
    have h3 : ψ t - θ t ≤ 2 * √t * Real.log t := Chebyshev.psi_sub_theta_le ht
    -- `2√t log t ≤ 8t^{3/4} ≤ 8t^a`
    have hlog : Real.log t ≤ t ^ ((1 : ℝ) / 4) / (1 / 4) := Real.log_le_rpow_div ht0.le (by norm_num)
    have hsq : √t = t ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow t
    have h34 : t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 4) = t ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_add ht0]; norm_num
    have h3a : t ^ ((3 : ℝ) / 4) ≤ t ^ a := Real.rpow_le_rpow_of_exponent_le ht (by rw [ha]; linarith)
    have h4 : 2 * √t * Real.log t ≤ 8 * t ^ a := by
      calc 2 * √t * Real.log t ≤ 2 * √t * (t ^ ((1 : ℝ) / 4) / (1 / 4)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = 8 * (t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 4)) := by rw [hsq]; ring
        _ = 8 * t ^ ((3 : ℝ) / 4) := by rw [h34]
        _ ≤ 8 * t ^ a := by linarith
    have h5 : |θ t - t| ≤ |ψ t - t| + (ψ t - θ t) := by
      have e' : θ t - t = (ψ t - t) - (ψ t - θ t) := by ring
      rw [e']
      calc |(ψ t - t) - (ψ t - θ t)| ≤ |ψ t - t| + |ψ t - θ t| := abs_sub _ _
        _ = |ψ t - t| + (ψ t - θ t) := by rw [abs_of_nonneg h2]
    linarith
  · -- below it, `|θ(t) − t| ≤ 2t ≤ 2T'`
    have htT' : t ≤ T' := (not_le.1 htT).le.trans (le_max_left _ _)
    have hθ0 := Chebyshev.theta_nonneg t
    have hθ4 : θ t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x ht0.le
    have hl4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [h4]; norm_num at this; linarith
    have h1 : |θ t - t| ≤ 2 * T' := by
      rw [abs_le]; constructor <;> nlinarith
    have h2 : 2 * T' ≤ 2 * T' * t ^ a := le_mul_of_one_le_right (by positivity) hta
    have h3 : 0 ≤ 8 * t ^ a := by positivity
    linarith

/-- **`θ` on short intervals.** For `ε > 0` there is `C ≥ 0` with `|θ(X) − θ(X − H) − H| ≤ C X^{11/12+ε}` for all
`X ≥ 1` and `0 ≤ H ≤ X`. -/
theorem abs_theta_sub_theta_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X H : ℝ, 1 ≤ X → 0 ≤ H → H ≤ X →
      |θ X - θ (X - H) - H| ≤ C * X ^ ((11 : ℝ) / 12 + ε) := by
  obtain ⟨C, hC0, hC⟩ := abs_theta_sub_le hε
  refine ⟨2 * C + 1, by positivity, fun X H hX hH hHX => ?_⟩
  set a : ℝ := (11 : ℝ) / 12 + ε with ha
  have hXa : 1 ≤ X ^ a := Real.one_le_rpow hX (by positivity)
  have h1 := hC X hX
  have h2 : |θ (X - H) - (X - H)| ≤ C * X ^ a + 1 := by
    by_cases hXH : 1 ≤ X - H
    · have h := hC (X - H) hXH
      have hle : (X - H) ^ a ≤ X ^ a := Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
      have := mul_le_mul_of_nonneg_left hle hC0
      linarith
    · have hθ : θ (X - H) = 0 := Chebyshev.theta_eq_zero_of_lt_two (by linarith)
      rw [hθ, zero_sub, abs_neg, abs_of_nonneg (by linarith)]
      have : 0 ≤ C * X ^ a := by positivity
      linarith
  have e : θ X - θ (X - H) - H = (θ X - X) - (θ (X - H) - (X - H)) := by ring
  rw [e]
  calc |(θ X - X) - (θ (X - H) - (X - H))| ≤ |θ X - X| + |θ (X - H) - (X - H)| := abs_sub _ _
    _ ≤ C * X ^ a + (C * X ^ a + 1) := add_le_add h1 h2
    _ ≤ (2 * C + 1) * X ^ a := by linarith

/-- `Σ_{X−H<p≤X} log p = θ(X) − θ(X − H)`. -/
theorem sum_log_primes {X H : ℝ} (hH : 0 ≤ H) :
    ∑ p ∈ (Ioc ⌊X - H⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p = θ X - θ (X - H) := by
  have hle : ⌊X - H⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor (by linarith)
  unfold Chebyshev.theta
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle]
  ring

/-- Membership in `(X − H, X]` through the floors, for `0 ≤ H ≤ X`. -/
theorem mem_Ioc_floor {X H : ℝ} (hXH : 0 ≤ X - H) (hH : 0 ≤ H) {m : ℕ} :
    m ∈ Ioc ⌊X - H⌋₊ ⌊X⌋₊ ↔ X - H < m ∧ (m : ℝ) ≤ X := by
  rw [Finset.mem_Ioc, Nat.floor_lt hXH, Nat.le_floor_iff (by linarith)]

/-- **Primes in intervals of relative length `X^{−σ}`**, `σ < 1/12`. For `ε > 0`, for all large `X` and every `H`
with `X^{1−σ} ≤ H ≤ X/2`: `(1 − ε)H/log X ≤ #{p : X − H < p ≤ X} ≤ (1 + ε)H/log X`. -/
theorem card_primes_short {σ : ℝ} (hσ : σ < 1 / 12) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ H : ℝ, X ^ (1 - σ) ≤ H → H ≤ X / 2 →
      (1 - ε) * H / Real.log X ≤ (((Ioc ⌊X - H⌋₊ ⌊X⌋₊).filter Nat.Prime).card : ℝ) ∧
        (((Ioc ⌊X - H⌋₊ ⌊X⌋₊).filter Nat.Prime).card : ℝ) ≤ (1 + ε) * H / Real.log X := by
  set η : ℝ := (1 / 12 - σ) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨C, hC0, hC⟩ := abs_theta_sub_theta_le hη0
  have hev1 : ∀ᶠ X : ℝ in atTop, 2 * C / ε ≤ X ^ η := (tendsto_rpow_atTop hη0).eventually_ge_atTop _
  have hev2 : ∀ᶠ X : ℝ in atTop, 2 * (1 + ε) * Real.log 2 / ε ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  filter_upwards [hev1, hev2, eventually_ge_atTop (4 : ℝ)] with X hX1 hX2 hX4 H hH1 hH2
  have hX0 : 0 < X := by linarith
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `CX^{11/12+η} ≤ (ε/2)H`
  have hsplit : X ^ (1 - σ) = X ^ ((11 : ℝ) / 12 + η) * X ^ η := by
    rw [← Real.rpow_add hX0]; congr 1; rw [hη]; ring
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) hH1
  have hCX : C * X ^ ((11 : ℝ) / 12 + η) ≤ ε / 2 * H := by
    have hXa : 0 < X ^ ((11 : ℝ) / 12 + η) := Real.rpow_pos_of_pos hX0 _
    have hCε : C ≤ ε / 2 * X ^ η := by
      rw [div_le_iff₀ hε] at hX1; linarith
    have : C * X ^ ((11 : ℝ) / 12 + η) ≤ ε / 2 * X ^ (1 - σ) := by
      rw [hsplit]
      calc C * X ^ ((11 : ℝ) / 12 + η) ≤ (ε / 2 * X ^ η) * X ^ ((11 : ℝ) / 12 + η) :=
            mul_le_mul_of_nonneg_right hCε hXa.le
        _ = ε / 2 * (X ^ ((11 : ℝ) / 12 + η) * X ^ η) := by ring
    exact this.trans (mul_le_mul_of_nonneg_left hH1 (by positivity))
  have hθ := abs_le.1 (hC X H (by linarith) hHpos.le (by linarith))
  have hsum := sum_log_primes (X := X) hHpos.le
  set P := (Ioc ⌊X - H⌋₊ ⌊X⌋₊).filter Nat.Prime with hP
  have hXH : 0 ≤ X - H := by linarith
  -- each `log p` lies in `(log(X/2), log X]`
  have hlo : (P.card : ℝ) * Real.log (X / 2) ≤ θ X - θ (X - H) := by
    rw [← hsum, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := (Finset.mem_filter.1 hp).1
    rw [mem_Ioc_floor hXH hHpos.le] at hp'
    simp only [Nat.cast_one, one_mul]
    exact Real.log_le_log (by positivity) (by linarith [hp'.1])
  have hhi : θ X - θ (X - H) ≤ (P.card : ℝ) * Real.log X := by
    rw [← hsum, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := (Finset.mem_filter.1 hp).1
    rw [mem_Ioc_floor hXH hHpos.le] at hp'
    have hp0 : (0 : ℝ) < p := by linarith [hp'.1]
    simp only [Nat.cast_one, one_mul]
    exact Real.log_le_log hp0 hp'.2
  constructor
  · rw [div_le_iff₀ hlX]
    have : (1 - ε) * H ≤ H - ε / 2 * H := by nlinarith
    linarith [hθ.1]
  · have hlX2 : Real.log (X / 2) = Real.log X - Real.log 2 := Real.log_div hX0.ne' (by norm_num)
    rw [le_div_iff₀ hlX]
    have hP0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
    -- `P log(X/2) ≤ (1 + ε/2)H` and `(1 + ε/2) log 2 ≤ (ε/2) log(X/2)`
    have h1 : (P.card : ℝ) * Real.log (X / 2) ≤ (1 + ε / 2) * H := by linarith [hθ.2]
    have h2 : (1 + ε / 2) * Real.log 2 ≤ ε / 2 * Real.log (X / 2) := by
      rw [div_le_iff₀ hε] at hX2
      rw [hlX2]; nlinarith
    have h3 : (1 + ε / 2) * ((P.card : ℝ) * Real.log 2) ≤ (1 + ε / 2) * (ε / 2 * H) := by
      have := mul_le_mul_of_nonneg_left h2 hP0
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ ε / 2)
      nlinarith
    have h4 : (P.card : ℝ) * Real.log 2 ≤ ε / 2 * H := le_of_mul_le_mul_left h3 (by positivity)
    have e : (P.card : ℝ) * Real.log X = (P.card : ℝ) * Real.log (X / 2) + (P.card : ℝ) * Real.log 2 := by
      rw [hlX2]; ring
    rw [e]
    nlinarith

/-- The primes of `(a, b]` number `π(b) − π(a)`. -/
theorem card_primes_Ioc {a b : ℕ} (hab : a ≤ b) :
    (((Ioc a b).filter Nat.Prime).card : ℝ) = Nat.primeCounting b - Nat.primeCounting a := by
  have h : ((Ioc 0 a).filter Nat.Prime).card + ((Ioc a b).filter Nat.Prime).card =
      ((Ioc 0 b).filter Nat.Prime).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  rw [← Nat.primesLE_eq_filter_Ioc_zero, ← Nat.primesLE_eq_filter_Ioc_zero,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at h
  rw [eq_sub_iff_add_eq, ← h]
  push_cast
  ring

/-- **Primes in `(X − X^{1−ρ}, X]`**, `0 < ρ < 1/12`: for `ε > 0` and all large `X`,
`(1 − ε)X^{1−ρ}/log X ≤ π(X) − π(X − X^{1−ρ}) ≤ (1 + ε)X^{1−ρ}/log X` (`card_primes_short` at `H = X^{1−ρ}`). -/
theorem primeCounting_short {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1 / 12) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      (1 - ε) * X ^ (1 - ρ) / Real.log X ≤
          (Nat.primeCounting ⌊X⌋₊ : ℝ) - Nat.primeCounting ⌊X - X ^ (1 - ρ)⌋₊ ∧
        (Nat.primeCounting ⌊X⌋₊ : ℝ) - Nat.primeCounting ⌊X - X ^ (1 - ρ)⌋₊ ≤
          (1 + ε) * X ^ (1 - ρ) / Real.log X := by
  have hev : ∀ᶠ X : ℝ in atTop, 2 ≤ X ^ ρ := (tendsto_rpow_atTop hρ0).eventually_ge_atTop _
  filter_upwards [card_primes_short hρ hε, hev, eventually_gt_atTop (0 : ℝ)] with X hX hX2 hX0
  have hH : X ^ (1 - ρ) ≤ X / 2 := by
    have e : X ^ (1 - ρ) = X / X ^ ρ := by
      rw [Real.rpow_sub hX0, Real.rpow_one]
    rw [e]
    exact div_le_div_of_nonneg_left hX0.le (by norm_num) hX2
  have hle : ⌊X - X ^ (1 - ρ)⌋₊ ≤ ⌊X⌋₊ :=
    Nat.floor_le_floor (by linarith [Real.rpow_nonneg hX0.le (1 - ρ)])
  rw [← card_primes_Ioc hle]
  exact hX (X ^ (1 - ρ)) le_rfl hH

/-! ### Rough numbers of a short interval and Buchstab's inequality -/

/-- The rough numbers of `(X − H, X]`: the `m` all of whose prime factors are at least `z`. -/
noncomputable def roughSet (X H : ℝ) (z : ℕ) : Finset ℕ :=
  (Ioc ⌊X - H⌋₊ ⌊X⌋₊).filter fun m => ∀ p ∈ m.primeFactors, z ≤ p

/-- `Ψ(X, H; z) = #{m ∈ (X − H, X] : p | m ⇒ p ≥ z}`. -/
noncomputable def Psi (X H : ℝ) (z : ℕ) : ℕ := (roughSet X H z).card

/-- Below `u = 1` (`X < z`, `X − H ≥ 1`) there are no rough numbers. -/
theorem Psi_eq_zero {X H : ℝ} {z : ℕ} (hXH : 1 ≤ X - H) (hH : 0 ≤ H) (h : X < z) : Psi X H z = 0 := by
  unfold Psi roughSet
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m hm hr
  rw [mem_Ioc_floor (by linarith) hH] at hm
  have hm1 : m ≠ 1 := by rintro rfl; norm_num at hm; linarith [hm.1]
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm; linarith [hm.1]
  have hp := Nat.minFac_prime hm1
  have hz := hr _ (Nat.mem_primeFactors.2 ⟨hp, Nat.minFac_dvd m, hm0⟩)
  have hle : (m.minFac : ℝ) ≤ m := by exact_mod_cast Nat.minFac_le (Nat.pos_of_ne_zero hm0)
  have : (z : ℝ) ≤ m.minFac := by exact_mod_cast hz
  linarith [hm.2]

/-- **Buchstab's inequality** on `(X − H, X]`, `X − H ≥ 1`: a rough number of the interval is a prime, or `p·m′`
with `p ≥ z` its least prime factor, `p² ≤ X` and `m′` rough for `p` in `((X − H)/p, X/p]`. -/
theorem Psi_le_buchstab {X H : ℝ} {z : ℕ} (hXH : 1 ≤ X - H) (hH : 0 ≤ H) :
    (Psi X H z : ℝ) ≤ ((Ioc ⌊X - H⌋₊ ⌊X⌋₊).filter Nat.Prime).card +
      ∑ p ∈ (Icc z ⌊√X⌋₊).filter Nat.Prime, (Psi (X / p) (H / p) p : ℝ) := by
  have hX0 : 0 ≤ X := by linarith
  set S := Ioc ⌊X - H⌋₊ ⌊X⌋₊ with hS
  set C := (roughSet X H z).filter fun m => ¬ m.Prime with hC
  have hsplit : roughSet X H z ⊆ S.filter Nat.Prime ∪ C := by
    intro m hm
    by_cases hp : m.Prime
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hm).1, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hm, hp⟩)
  have hCsub : C ⊆ ((Icc z ⌊√X⌋₊).filter Nat.Prime).biUnion
      (fun p => (roughSet (X / p) (H / p) p).image (fun m' => p * m')) := by
    intro m hm
    obtain ⟨hmR, hmp⟩ := Finset.mem_filter.1 hm
    obtain ⟨hmS, hr⟩ := Finset.mem_filter.1 hmR
    rw [mem_Ioc_floor (by linarith) hH] at hmS
    have hm0 : m ≠ 0 := by rintro rfl; norm_num at hmS; linarith [hmS.1]
    have hm1 : m ≠ 1 := by rintro rfl; norm_num at hmS; linarith [hmS.1]
    set p := m.minFac with hpdef
    have hpp : p.Prime := Nat.minFac_prime hm1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hpz : z ≤ p := hr _ (Nat.mem_primeFactors.2 ⟨hpp, Nat.minFac_dvd m, hm0⟩)
    have hsq : p ^ 2 ≤ m := Nat.minFac_sq_le_self (Nat.pos_of_ne_zero hm0) hmp
    have hpsqrt : p ≤ ⌊√X⌋₊ := by
      rw [Nat.le_floor_iff (Real.sqrt_nonneg _)]
      rw [Real.le_sqrt (by positivity) hX0]
      have : ((p ^ 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hsq
      push_cast at this
      linarith [hmS.2]
    rw [Finset.mem_biUnion]
    refine ⟨p, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpz, hpsqrt⟩, hpp⟩, ?_⟩
    rw [Finset.mem_image]
    refine ⟨m / p, ?_, Nat.mul_div_cancel' (Nat.minFac_dvd m)⟩
    have hmeq : ((m / p : ℕ) : ℝ) = m / p := by
      rw [Nat.cast_div (Nat.minFac_dvd m) hp0.ne']
    have hXHp : X / p - H / p = (X - H) / p := (sub_div _ _ _).symm
    unfold roughSet
    rw [Finset.mem_filter, mem_Ioc_floor (by rw [hXHp]; exact div_nonneg (by linarith) hp0.le)
      (div_nonneg hH hp0.le), hmeq, hXHp]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact div_lt_div_of_pos_right hmS.1 hp0
    · exact div_le_div_of_nonneg_right hmS.2 hp0.le
    · intro q hq
      obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.1 hq
      exact Nat.minFac_le_of_dvd hqp.two_le (hqd.trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd m)))
  have h1 : (roughSet X H z).card ≤ (S.filter Nat.Prime).card + C.card :=
    (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have h2 : C.card ≤ ∑ p ∈ (Icc z ⌊√X⌋₊).filter Nat.Prime, (roughSet (X / p) (H / p) p).card :=
    (Finset.card_le_card hCsub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun p _ => Finset.card_image_le))
  unfold Psi
  have h3 : ((roughSet X H z).card : ℝ) ≤ (S.filter Nat.Prime).card +
      ((∑ p ∈ (Icc z ⌊√X⌋₊).filter Nat.Prime, (roughSet (X / p) (H / p) p).card : ℕ) : ℝ) := by
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  push_cast at h3
  exact h3

/-! ### The induction on `u` -/

/-- The bound at level `K`, for relative lengths at least `z^{−σ}`: `Ψ(X, H; z) ≤ (ω*(log X/log z) + ε)H/log z`
whenever `X ≥ 2`, `z^{−σ}X ≤ H ≤ X/2` and `log X ≤ K log z`, for every `ε > 0` and all large `z`. -/
def Claim (σ K : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ X H : ℝ, 2 ≤ X →
  (z : ℝ) ^ (-σ) * X ≤ H → H ≤ X / 2 → Real.log X ≤ K * Real.log z →
    (Psi X H z : ℝ) ≤ (SieveCert.omegaC (Real.log X / Real.log z) + ε) * H / Real.log z

/-- It suffices to prove the bound for `ε ≤ 1`. -/
theorem claim_of_small {σ K : ℝ} (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ X H : ℝ,
    2 ≤ X → (z : ℝ) ^ (-σ) * X ≤ H → H ≤ X / 2 → Real.log X ≤ K * Real.log z →
      (Psi X H z : ℝ) ≤ (SieveCert.omegaC (Real.log X / Real.log z) + ε) * H / Real.log z) :
    Claim σ K := by
  intro ε hε
  obtain ⟨z₀, hz₀⟩ := h (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨max z₀ 3, fun z hz X H hX hH1 hH2 hlog => ?_⟩
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast le_trans (le_max_right _ _) hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hH0 : 0 ≤ H := le_trans (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by linarith)) hH1
  refine (hz₀ z (le_trans (le_max_left _ _) hz) X H hX hH1 hH2 hlog).trans ?_
  apply div_le_div_of_nonneg_right _ hlz.le
  apply mul_le_mul_of_nonneg_right _ hH0
  linarith [min_le_left ε 1]

set_option maxHeartbeats 1000000 in
/-- **The induction step**: the bound at level `K` gives it at level `K + 1`. -/
theorem claim_step {σ K : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 12) (hK : 0 ≤ K) (IH : Claim σ K) :
    Claim σ (K + 1) := by
  apply claim_of_small
  intro ε hε hε1
  obtain ⟨ε₃, hε₃⟩ : ∃ ε₃ : ℝ, ε₃ = ε / 100 := ⟨_, rfl⟩
  have hε₃0 : 0 < ε₃ := by rw [hε₃]; positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 (card_primes_short hσ (ε := ε / 4) (by positivity))
  obtain ⟨z₁, hz₁⟩ := IH (ε / 4) (by positivity)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (SieveRough.theta_near (ε := ε₃) hε₃0)
  refine ⟨max (max z₁ (⌈X₀⌉₊ + 4)) (max (⌈T⌉₊ + 4) (⌈8 / ε⌉₊ + 4)), ?_⟩
  intro z hz X H hX hH1 hH2 hlog
  -- facts about `z`
  have hzz₁ : z₁ ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hzA : ⌈X₀⌉₊ + 4 ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hzB : ⌈T⌉₊ + 4 ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hz
  have hzC : ⌈8 / ε⌉₊ + 4 ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hz
  have hzX₀ : X₀ ≤ z := by
    have : ((⌈X₀⌉₊ + 4 : ℕ) : ℝ) ≤ z := by exact_mod_cast hzA
    push_cast at this
    linarith [Nat.le_ceil X₀]
  have hzT : T ≤ z := by
    have : ((⌈T⌉₊ + 4 : ℕ) : ℝ) ≤ z := by exact_mod_cast hzB
    push_cast at this
    linarith [Nat.le_ceil T]
  have hz8 : 8 / ε ≤ z := by
    have : ((⌈8 / ε⌉₊ + 4 : ℕ) : ℝ) ≤ z := by exact_mod_cast hzC
    push_cast at this
    linarith [Nat.le_ceil (8 / ε)]
  have hz4 : (4 : ℝ) ≤ z := by
    have : ((⌈T⌉₊ + 4 : ℕ) : ℝ) ≤ z := by exact_mod_cast hzB
    push_cast at this
    linarith [Nat.cast_nonneg (α := ℝ) ⌈T⌉₊]
  have hez : Real.exp 1 ≤ z := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have hlz : 1 ≤ Real.log z := by rw [Real.le_log_iff_exp_le (by linarith)]; exact hez
  have hlz0 : 0 < Real.log z := by linarith
  have hθ : ∀ a b : ℝ, (z : ℝ) ≤ a → ∀ t ∈ Set.Icc a b, |θ t - t| ≤ ε₃ * t / Real.log t :=
    fun a b hza t ht => hT t (by linarith [ht.1])
  have hX0 : 0 < X := by linarith
  have hzσ0 : 0 < (z : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
  have hH0 : 0 < H := lt_of_lt_of_le (mul_pos hzσ0 hX0) hH1
  have hXH : 1 ≤ X - H := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log X := ⟨_, rfl⟩
  rw [← hLdef] at hlog
  rw [← hLdef]
  -- below `u = 1`
  by_cases hsmall : X < z
  · rw [Psi_eq_zero hXH hH0.le hsmall, Nat.cast_zero]
    have := SieveRough.omegaC_nonneg (L / Real.log z)
    positivity
  have hzX : (z : ℝ) ≤ X := not_lt.1 hsmall
  have hXX₀ : X₀ ≤ X := by linarith
  have hLz : Real.log z ≤ L := by rw [hLdef]; exact Real.log_le_log (by linarith) hzX
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = L / Real.log z := ⟨_, rfl⟩
  rw [← hu]
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hlz0]; linarith
  have hLu : L = u * Real.log z := by rw [hu]; field_simp
  have hL0 : 0 < L := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = H / Real.log z := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hHL : H / L = Q / u := by rw [hLu, hQ]; field_simp
  -- Buchstab and the primes
  have hbuch := Psi_le_buchstab (z := z) hXH hH0.le
  have hXσ : X ^ (1 - σ) ≤ H := by
    have h1 : X ^ (1 - σ) = X ^ (-σ) * X := by
      rw [sub_eq_add_neg, add_comm, Real.rpow_add hX0, Real.rpow_one]
    have h2 : X ^ (-σ) ≤ (z : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by linarith) hzX (by linarith)
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_right h2 hX0.le) hH1
  have hN := (hX₀ X hXX₀ H hXσ hH2).2
  -- the induction hypothesis at each prime
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℝ, F = fun p : ℕ => SieveCert.omegaC ((L - Real.log p) / Real.log p) /
      ((p : ℝ) * Real.log p) + ε / 4 / ((p : ℝ) * Real.log p) := ⟨_, rfl⟩
  have hIH : ∀ p ∈ (Icc z ⌊√X⌋₊).filter Nat.Prime, (Psi (X / p) (H / p) p : ℝ) ≤ H * F p := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.1 hp
    obtain ⟨hzp, hpn⟩ := Finset.mem_Icc.1 hpI
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpz : (z : ℝ) ≤ p := by exact_mod_cast hzp
    have hpsq : (p : ℝ) ≤ √X := le_trans (by exact_mod_cast hpn) (Nat.floor_le (Real.sqrt_nonneg _))
    have hpp2 : (p : ℝ) * p ≤ X := by
      calc (p : ℝ) * p ≤ √X * √X := mul_le_mul hpsq hpsq hp0.le (Real.sqrt_nonneg _)
        _ = X := Real.mul_self_sqrt hX0.le
    have hXp2 : 2 ≤ X / p := by rw [le_div_iff₀ hp0]; nlinarith
    have hlp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlzp : Real.log z ≤ Real.log p := Real.log_le_log (by linarith) hpz
    have hlXp : Real.log (X / p) = L - Real.log p := by
      rw [Real.log_div hX0.ne' hp0.ne', hLdef]
    have hlogp : Real.log (X / p) ≤ K * Real.log p := by
      rw [hlXp]
      have : L ≤ (K + 1) * Real.log p := le_trans hlog (mul_le_mul_of_nonneg_left hlzp (by linarith))
      linarith
    have hpσ : (p : ℝ) ^ (-σ) ≤ (z : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hpz (by linarith)
    have hH1p : (p : ℝ) ^ (-σ) * (X / p) ≤ H / p := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hp0]
      exact le_trans (mul_le_mul_of_nonneg_right hpσ hX0.le) hH1
    have hH2p : H / p ≤ X / p / 2 := by
      rw [div_right_comm]
      exact div_le_div_of_nonneg_right hH2 hp0.le
    have h := hz₁ p (le_trans hzz₁ hzp) (X / p) (H / p) hXp2 hH1p hH2p hlogp
    rw [hlXp] at h
    refine h.trans (le_of_eq ?_)
    simp only [hFdef]
    field_simp
  have hF0 : ∀ p, 0 ≤ F p := by
    intro p
    simp only [hFdef]
    have := SieveRough.omegaC_nonneg ((L - Real.log p) / Real.log p)
    rcases Nat.lt_or_ge p 2 with hp | hp
    · interval_cases p <;> simp
    · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
      have : 0 < Real.log p := Real.log_pos hp1
      positivity
  have hsumP : ∑ p ∈ (Icc z ⌊√X⌋₊).filter Nat.Prime, (Psi (X / p) (H / p) p : ℝ) ≤
      H * ∑ p ∈ (Icc z ⌊√X⌋₊).filter Nat.Prime, F p := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hIH
  by_cases hu2 : u < 2
  · -- `1 ≤ u < 2`: no prime of the sum
    have hn : ⌊√X⌋₊ < z := by
      have hXz : X < (z : ℝ) * z := by
        have : L < 2 * Real.log z := by rw [hLu]; nlinarith
        have : Real.log X < Real.log ((z : ℝ) * z) := by
          have hzz : Real.log ((z : ℝ) * z) = 2 * Real.log z := by
            rw [Real.log_mul (by positivity) (by positivity)]; ring
          rw [hzz, ← hLdef]; exact this
        exact (Real.log_lt_log_iff (by linarith) (by positivity)).1 this
      have : √X < z := by
        rw [Real.sqrt_lt' (by linarith)]; nlinarith
      exact (Nat.floor_lt (Real.sqrt_nonneg _)).2 this
    have hempty : (Icc z ⌊√X⌋₊).filter Nat.Prime = ∅ := by
      rw [Finset.Icc_eq_empty (by omega), Finset.filter_empty]
    rw [hempty, Finset.sum_empty, add_zero] at hbuch
    rw [SieveRough.omegaC_of_lt_two hu1 hu2]
    have h1 : (Psi X H z : ℝ) ≤ (1 + ε / 4) * (Q / u) := by
      calc (Psi X H z : ℝ) ≤ _ := hbuch
        _ ≤ (1 + ε / 4) * H / L := by rw [hLdef]; exact hN
        _ = (1 + ε / 4) * (H / L) := by ring
        _ = (1 + ε / 4) * (Q / u) := by rw [hHL]
    have h2 : (1 + ε / 4) * (Q / u) ≤ (1 / u + ε) * Q := by
      have hu0 : 0 < u := by linarith
      have : ε / 4 / u ≤ ε := by rw [div_le_iff₀ hu0]; nlinarith
      have e : (1 + ε / 4) * (Q / u) = (1 / u + ε / 4 / u) * Q := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (by linarith) hQ0.le
    calc (Psi X H z : ℝ) ≤ (1 / u + ε) * Q := h1.trans h2
      _ = (1 / u + ε) * H / Real.log z := by rw [hQ]; ring
  · -- `u ≥ 2`
    have hu2' : 2 ≤ u := not_lt.1 hu2
    obtain ⟨b2, hb2⟩ : ∃ b2 : ℝ, b2 = √X := ⟨_, rfl⟩
    have hlb2 : 2 * Real.log b2 = L := by rw [hb2, Real.log_sqrt hX0.le, hLdef]; ring
    have hzb2 : (z : ℝ) ≤ b2 := by
      have : 2 * Real.log z ≤ 2 * Real.log b2 := by
        rw [hlb2]
        calc 2 * Real.log z ≤ u * Real.log z := mul_le_mul_of_nonneg_right hu2' hlz0.le
          _ = L := hLu.symm
      have hb20 : 0 < b2 := by rw [hb2]; positivity
      exact (Real.log_le_log_iff (by linarith) hb20).1 (by linarith)
    have hzn : z ≤ ⌊b2⌋₊ := Nat.le_floor hzb2
    have hfloorz : ⌊(z : ℝ)⌋₊ = z := Nat.floor_natCast z
    -- the term at `z`
    have hFz : F z ≤ 2 / ((z : ℝ) * Real.log z) := by
      simp only [hFdef]
      have := SieveRough.omegaC_le_one ((L - Real.log z) / Real.log z)
      have hd : 0 < (z : ℝ) * Real.log z := by positivity
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hd.le
    -- the `ε/4` part
    have hE : ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, ε / 4 / ((p : ℝ) * Real.log p) ≤
        ε / 4 * (1 / Real.log z + 4 * ε₃ / Real.log z ^ 2) := by
      have h := SieveRough.sum_inv_mul_log_le hez hzb2 hε₃0.le (hθ z b2 le_rfl)
      rw [hfloorz] at h
      have hb21 : 0 ≤ 1 / Real.log b2 := by
        have : 0 < Real.log b2 := by linarith only [hlb2, hL0]
        positivity
      have e : ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, ε / 4 / ((p : ℝ) * Real.log p) =
          ε / 4 * ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, 1 / ((p : ℝ) * Real.log p) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith only [h, hb21]) (by positivity)
    -- the sum of `ω*` over `(z, √X]`
    have hW : ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime,
        SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) ≤
        (1 / L) * (if u ≤ 3 then Real.log (u - 1) else
          Real.log 2 + 5671433 / 10000000 * min (u - 3) 1 + 565073 / 1000000 * max (u - 4) 0) +
          12 * ε₃ / L + 8 * ε₃ / Real.log z := by
      by_cases hu3 : u ≤ 3
      · simp only [hu3, ite_true]
        have h := SieveRough.sumW_le_three hez hzb2 hlb2 hLu hu2' hu3 hε₃0 (hθ z b2 le_rfl)
        have h48 : 4 * ε₃ / Real.log z ≤ 8 * ε₃ / Real.log z :=
          div_le_div_of_nonneg_right (by linarith) hlz0.le
        linarith
      · have hu3' : 3 < u := not_le.1 hu3
        obtain ⟨b3, hb3⟩ : ∃ b3 : ℝ, b3 = X ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
        have hb30 : 0 < b3 := by rw [hb3]; positivity
        have hlb3 : 3 * Real.log b3 = L := by
          rw [hb3, Real.log_rpow hX0, hLdef]; ring
        obtain ⟨b4, hb4⟩ : ∃ b4 : ℝ, b4 = X ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
        have hb40 : 0 < b4 := by rw [hb4]; positivity
        have hlb4 : 4 * Real.log b4 = L := by
          rw [hb4, Real.log_rpow hX0, hLdef]; ring
        simp only [hu3, ite_false]
        have hb20 : 0 < b2 := by rw [hb2]; positivity
        exact SieveRough.sumW_gt_three hez hlb2 hlb3 hlb4 hb20 hb30 hb40 hLu hu3' hε₃0 (hθ z b2 le_rfl)
    -- the final count
    have hPsum := SieveRough.sum_Icc_filter_le hF0 hzn
    have hIocF : ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, F p =
        ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime,
          SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) +
        ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, ε / 4 / ((p : ℝ) * Real.log p) := by
      simp only [hFdef, Finset.sum_add_distrib]
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = if u ≤ 3 then Real.log (u - 1) else
        Real.log 2 + 5671433 / 10000000 * min (u - 3) 1 + 565073 / 1000000 * max (u - 4) 0 := ⟨_, rfl⟩
    rw [← hM] at hW
    have hsuper : 1 + M ≤ SieveCert.omegaC u * u := SieveRough.super_M hu2' hM
    -- everything in units of `Q = H/log z`, with `H/L = Q/u`
    have hN' : (1 + ε / 4) * H / Real.log X = (1 + ε / 4) * (Q / u) := by
      rw [← hLdef, ← hHL]; ring
    have h1 := hN.trans hN'.le
    have h2 : ∑ p ∈ (Icc z ⌊√X⌋₊).filter Nat.Prime, F p ≤ 2 / ((z : ℝ) * Real.log z) +
        ((1 / L) * M + 12 * ε₃ / L + 8 * ε₃ / Real.log z) +
        ε / 4 * (1 / Real.log z + 4 * ε₃ / Real.log z ^ 2) := by
      rw [← hb2]
      calc ∑ p ∈ (Icc z ⌊b2⌋₊).filter Nat.Prime, F p
          ≤ F z + ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, F p := hPsum
        _ = F z + (∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime,
              SieveCert.omegaC ((L - Real.log p) / Real.log p) / ((p : ℝ) * Real.log p) +
            ∑ p ∈ (Ioc z ⌊b2⌋₊).filter Nat.Prime, ε / 4 / ((p : ℝ) * Real.log p)) := by rw [hIocF]
        _ ≤ 2 / ((z : ℝ) * Real.log z) + (((1 / L) * M + 12 * ε₃ / L + 8 * ε₃ / Real.log z) +
            ε / 4 * (1 / Real.log z + 4 * ε₃ / Real.log z ^ 2)) := add_le_add hFz (add_le_add hW hE)
        _ = _ := by ring
    have hbound : (Psi X H z : ℝ) ≤ (1 + ε / 4) * (Q / u) + H * (2 / ((z : ℝ) * Real.log z) +
        ((1 / L) * M + 12 * ε₃ / L + 8 * ε₃ / Real.log z) +
          ε / 4 * (1 / Real.log z + 4 * ε₃ / Real.log z ^ 2)) :=
      hbuch.trans (add_le_add h1 (hsumP.trans (mul_le_mul_of_nonneg_left h2 hH0.le)))
    -- the bracket
    have hu0 : 0 < u := by linarith
    have hz2 : 2 / (z : ℝ) ≤ ε / 4 := by
      rw [div_le_iff₀ (by linarith)]
      have : 8 / ε * ε = 8 := by field_simp
      nlinarith
    calc (Psi X H z : ℝ) ≤ _ := hbound
      _ = _ := SieveRough.units_eq hlz0 hLu hu0 hQ (by linarith)
      _ ≤ Q * (SieveCert.omegaC u + ε) :=
          mul_le_mul_of_nonneg_left (SieveRough.bracket_le hu1 hlz hz2 hε hε1 hε₃ hsuper) hQ0.le
      _ = (SieveCert.omegaC u + ε) * H / Real.log z := by rw [hQ]; ring

/-- The bound at level `0` is vacuous, since `log X > 0` for `X ≥ 2`. -/
theorem claim_zero (σ : ℝ) : Claim σ 0 := by
  intro ε hε
  refine ⟨0, fun z _ X H hX _ _ hlog => ?_⟩
  have : 0 < Real.log X := Real.log_pos (by linarith)
  linarith [show (0 : ℝ) * Real.log z = 0 by ring]

/-- The bound at every natural level. -/
theorem claim_nat {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 12) (k : ℕ) : Claim σ k := by
  induction k with
  | zero => simpa using claim_zero σ
  | succ k ih =>
    have h := claim_step hσ0 hσ (Nat.cast_nonneg k) ih
    simpa using h

/-- **Rough numbers of a short interval from above.** Let `0 ≤ σ < 1/12`. For every `U` and `ε > 0` there is `z₀`
such that for `z ≥ z₀`, `X ≥ 2`, `z^{−σ}X ≤ H ≤ X/2` and `log X ≤ U log z`:
`Ψ(X, H; z) ≤ (ω*(log X/log z) + ε)H/log z`. -/
theorem psi_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 12) (U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ X H : ℝ, 2 ≤ X → (z : ℝ) ^ (-σ) * X ≤ H → H ≤ X / 2 →
      Real.log X ≤ U * Real.log z →
        (Psi X H z : ℝ) ≤ (SieveCert.omegaC (Real.log X / Real.log z) + ε) * H / Real.log z := by
  obtain ⟨z₀, hz₀⟩ := claim_nat hσ0 hσ ⌈U⌉₊ ε hε
  refine ⟨max z₀ 2, fun z hz X H hX hH1 hH2 hlog =>
    hz₀ z (le_trans (le_max_left _ _) hz) X H hX hH1 hH2 (hlog.trans ?_)⟩
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast le_trans (le_max_right _ _) hz
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil U) hlz

/-- **Rough numbers of `(X − X^{1−ρ}, X]` from above.** Let `ρ > 0` and `ρU < 1/12`. For every `ε > 0` there is `z₀`
such that for `z ≥ z₀` and `X ≥ z` with `log X ≤ U log z`:
`#{m ∈ (X − X^{1−ρ}, X] : p | m ⇒ p ≥ z} ≤ (ω*(log X/log z) + ε)X^{1−ρ}/log z` (`psi_le` at `σ = max(ρU, 0)`). -/
theorem psi_le_rpow {ρ U : ℝ} (hρ : 0 < ρ) (hρU : ρ * U < 1 / 12) {ε : ℝ} (hε : 0 < ε) :
    ∃ z₀ : ℕ, ∀ z : ℕ, z₀ ≤ z → ∀ X : ℝ, (z : ℝ) ≤ X → Real.log X ≤ U * Real.log z →
      (Psi X (X ^ (1 - ρ)) z : ℝ) ≤
        (SieveCert.omegaC (Real.log X / Real.log z) + ε) * X ^ (1 - ρ) / Real.log z := by
  set σ : ℝ := max (ρ * U) 0 with hσ
  obtain ⟨z₀, hz₀⟩ := psi_le (σ := σ) (le_max_right _ _) (max_lt hρU (by norm_num)) U hε
  refine ⟨max z₀ (⌈(2 : ℝ) ^ (1 / ρ)⌉₊ + 2), fun z hz X hzX hlog => ?_⟩
  have hz₀z : z₀ ≤ z := le_trans (le_max_left _ _) hz
  have hpos : 0 < (2 : ℝ) ^ (1 / ρ) := by positivity
  have hz2 : (2 : ℝ) ^ (1 / ρ) + 2 ≤ z := by
    have : ((⌈(2 : ℝ) ^ (1 / ρ)⌉₊ + 2 : ℕ) : ℝ) ≤ z := by exact_mod_cast le_trans (le_max_right _ _) hz
    push_cast at this
    linarith [Nat.le_ceil ((2 : ℝ) ^ (1 / ρ))]
  have hX2 : 2 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hz0 : (0 : ℝ) < z := by linarith
  -- `X^ρ ≥ 2`
  have hXρ : 2 ≤ X ^ ρ := by
    have h : ((2 : ℝ) ^ (1 / ρ)) ^ ρ = 2 := by
      rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hρ.ne', Real.rpow_one]
    rw [← h]
    exact Real.rpow_le_rpow hpos.le (by linarith) hρ.le
  refine hz₀ z hz₀z X (X ^ (1 - ρ)) hX2 ?_ ?_ hlog
  · -- `z^{−σ} ≤ X^{−ρ}`, from `ρ log X ≤ ρU log z ≤ σ log z`
    have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
    have hexp : Real.log z * (-σ) ≤ Real.log X * (-ρ) := by
      have h1 : ρ * Real.log X ≤ ρ * U * Real.log z := by
        have := mul_le_mul_of_nonneg_left hlog hρ.le; linarith
      have h2 : ρ * U * Real.log z ≤ σ * Real.log z := mul_le_mul_of_nonneg_right (le_max_left _ _) hlz
      linarith
    have h : (z : ℝ) ^ (-σ) ≤ X ^ (-ρ) := by
      rw [Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos hX0]
      exact Real.exp_le_exp.2 hexp
    have hsplit : X ^ (1 - ρ) = X ^ (-ρ) * X := by
      rw [sub_eq_add_neg, add_comm, Real.rpow_add hX0, Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right h hX0.le
  · -- `X^{1−ρ} = X/X^ρ ≤ X/2`
    have e : X ^ (1 - ρ) = X / X ^ ρ := by rw [Real.rpow_sub hX0, Real.rpow_one]
    rw [e]
    exact div_le_div_of_nonneg_left hX0.le (by norm_num) hXρ

/-! ### Rough cofactors -/

/-- **Rough cofactors in a short interval.** For `d ≥ 1` and `0 ≤ H ≤ X`, the `n ∈ (X − H, X]` with `d | n` and `n/d`
free of prime factors below `z` number `Ψ(X/d, H/d; z)`: `n = dm` with `m ∈ ((X − H)/d, X/d]`. -/
theorem card_dvd_rough {d : ℕ} (hd : 0 < d) {X H : ℝ} (hH : 0 ≤ H) (hHX : H ≤ X) (z : ℕ) :
    ((Ioc ⌊X - H⌋₊ ⌊X⌋₊).filter fun n => d ∣ n ∧ ∀ p ∈ (n / d).primeFactors, z ≤ p).card =
      Psi (X / d) (H / d) z := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hXH : 0 ≤ X - H := by linarith
  have hXHd : X / d - H / d = (X - H) / d := (sub_div _ _ _).symm
  have hXHd0 : 0 ≤ X / d - H / d := by rw [hXHd]; exact div_nonneg hXH hd0.le
  unfold Psi
  rw [← Finset.card_image_of_injective (roughSet (X / d) (H / d) z) (mul_right_injective₀ hd.ne')]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_image, roughSet]
  constructor
  · rintro ⟨hn, ⟨m, rfl⟩, hr⟩
    rw [Nat.mul_div_cancel_left m hd] at hr
    rw [mem_Ioc_floor hXH hH] at hn
    push_cast at hn
    refine ⟨m, ⟨?_, hr⟩, rfl⟩
    rw [mem_Ioc_floor hXHd0 (div_nonneg hH hd0.le), hXHd]
    constructor
    · rw [div_lt_iff₀ hd0]; linarith [hn.1]
    · rw [le_div_iff₀ hd0]; linarith [hn.2]
  · rintro ⟨m, ⟨hm, hr⟩, rfl⟩
    rw [mem_Ioc_floor hXHd0 (div_nonneg hH hd0.le), hXHd, div_lt_iff₀ hd0, le_div_iff₀ hd0] at hm
    refine ⟨?_, ⟨m, rfl⟩, by rwa [Nat.mul_div_cancel_left m hd]⟩
    rw [mem_Ioc_floor hXH hH]
    push_cast
    constructor
    · linarith [hm.1]
    · linarith [hm.2]

/-- **Rough multiples in a short interval.** When the prime factors of `d ≥ 1` are at least `z`, the `n ∈ (X − H, X]`
with `d | n` and no prime factor below `z` number `Ψ(X/d, H/d; z)`, for `0 ≤ H ≤ X`. -/
theorem card_dvd_rough_of_le {d z : ℕ} (hd : 0 < d) (hdz : ∀ p ∈ d.primeFactors, z ≤ p) {X H : ℝ} (hH : 0 ≤ H)
    (hHX : H ≤ X) :
    ((Ioc ⌊X - H⌋₊ ⌊X⌋₊).filter fun n => d ∣ n ∧ ∀ p ∈ n.primeFactors, z ≤ p).card = Psi (X / d) (H / d) z := by
  rw [← card_dvd_rough hd hH hHX z]
  congr 1
  refine Finset.filter_congr fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.1 hn).1; omega
  constructor
  · rintro ⟨⟨m, rfl⟩, hr⟩
    refine ⟨⟨m, rfl⟩, ?_⟩
    rw [Nat.mul_div_cancel_left m hd]
    exact fun p hp => hr p (Nat.primeFactors_mono (Dvd.intro_left d rfl) hn0 hp)
  · rintro ⟨⟨m, rfl⟩, hr⟩
    refine ⟨⟨m, rfl⟩, ?_⟩
    rw [Nat.mul_div_cancel_left m hd] at hr
    have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (mul_zero d)
    intro p hp
    rw [Nat.primeFactors_mul hd.ne' hm0, Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact hdz p hp
    · exact hr p hp

end ShortSieveLong

#print axioms ShortSieveLong.abs_theta_sub_theta_le
#print axioms ShortSieveLong.card_primes_short
#print axioms ShortSieveLong.primeCounting_short
#print axioms ShortSieveLong.Psi_le_buchstab
#print axioms ShortSieveLong.claim_step
#print axioms ShortSieveLong.psi_le
#print axioms ShortSieveLong.psi_le_rpow
#print axioms ShortSieveLong.card_dvd_rough
#print axioms ShortSieveLong.card_dvd_rough_of_le
