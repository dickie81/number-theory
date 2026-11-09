import Mathlib
import BallGap

/-! # Under RH the pivots of the orbit form grow like `log N`: the orbit-lattice inequality for all large `N`

Plain statement. `Q_N(x) = Σ_{m,n ≤ N} x_m x_n √(mn)·K_H(m/n)` is the form of the Gram matrix of the orbit
(`BallWeil.form`), computed from the primes, and `d_N = min{Q_N(x) : x_N = 1}` is its `N`-th Gram–Schmidt pivot: in a
realization, the squared distance of `w_N` from the span of `w_1, …, w_{N−1}`. The orbit-lattice conjecture of
`docs/ball-conjecture.md` is `d_N ≥ d_1 = K_H(1)` for every `N`; it implies RH (`BallWeil.rh_of_pivots`).

* `slack_top`: for `N ≥ 1` and every real `c`, `Σ_{n ≤ N}c_n² + G(c) ≥ (log N/2 + log 4 + 2)·c_N²`, where `G` is
  Landau's slack (`BallSharp.landauSlack`). No hypothesis.
* `pivot_ge` (RH): `Q_N(x) ≥ (log N/2 + log 4 + 2)/(22e⁸)·x_N²` for every `N ≥ 1` and every real `x`. So
  `d_N ≥ (log N/2 + log 4 + 2)/(22e⁸)`: under RH the pivots tend to infinity (`pivot_tendsto`), at the rate `log N`
  of the bound `d_N ≤ ‖w_N − w_{N−1}‖² = log(N/2π) + 1 − γ + o(1)` of `docs/ball-conjecture.md`.
* `orbitLattice_of_log_ge` (RH): the pivot inequality `d_k ≥ d_1` holds for every `k` with `log k ≥ 7100`.
* `orbitLattice_iff`: the orbit-lattice conjecture holds if and only if RH holds and the pivot inequality holds for the
  `k` with `log k < 7100`. So under RH the conjecture is a statement about finitely many pivots.

The proofs.

- **The top vertex.** Let `c′` be `c` with `c_N` set to `0`. The terms of Landau's form `L(c) = 2Σ_n Λ(n)n^{−1/2}
  Σ_{jn ≤ N}c_j c_{jn}` that contain `c_N` are those with `jn = N`, `n ≥ 2` (`ex_cut`): the term `j = N`, `n = 1` has
  `Λ(1) = 0`. So `G(c) = G(c′) + (log N + log 4 + 1)c_N² − 2c_N Σ_{n ∣ N}Λ(n)n^{−1/2}c_{N/n}` (`landau_cut`).
- **Each parent pays once.** `2c_N·Λ(n)n^{−1/2}c_{N/n} ≤ c_{N/n}² + c_N²Λ(n)²/n`. The parents `N/n`, `n ≥ 2`, are
  distinct and below `N`, so the first terms total at most `Σ_n c′_n²` (`sum_parents_le`); and `Λ(n)/n ≤ 1/2` with
  `Σ_{n ∣ N}Λ(n) = log N` bounds the second by `c_N² log N/2` (`sum_vonMangoldt_sq_le`). With `G(c′) ≥ 0`
  (`BallSharp.landauSlack_nonneg`) this is `slack_top`.
- **The pivot.** `BallSharp.rate_slack` is `Q_N(x) ≥ (Σx_n² n + G(c))/(22e⁸N)` with `c_n = x_n√n`, and `c_N² = N x_N²`.
- **The threshold.** `K_H(1) < 0.0539` (`WeilTest.hadamard_const_lt`) and `e⁸ < 2981`.

`slack_top` is the inequality behind it: in the divisibility graph of Landau's form the vertex `N` has no children,
and its parents are the `N/q`, `q` a prime power dividing `N`, with `Σ_q Λ(q) = log N`. A vector cannot cancel the
edge `(N/q, N)` without placing `√q·c_N` at the parent, where the spread `Σc_n²` charges it.
-/

open Real Finset BallDensity BallSharp
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace BallPivot

/-! ## Removing the top coefficient -/

/-- `c` with its coefficient at `N` set to `0`. -/
def cut (N : ℕ) (c : ℕ → ℝ) : ℕ → ℝ := fun n => if n = N then 0 else c n

lemma cut_self (N : ℕ) (c : ℕ → ℝ) : cut N c N = 0 := by simp [cut]

lemma cut_of_ne {N n : ℕ} (c : ℕ → ℝ) (h : n ≠ N) : cut N c n = c n := by simp [cut, h]

/-- `Σ_{j ≤ N}c_j² = Σ_{j ≤ N}c′_j² + c_N²`. -/
lemma S2_cut {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) : S2 N c = S2 N (cut N c) + c N ^ 2 := by
  unfold S2
  have hmem : N ∈ Icc 1 N := Finset.mem_Icc.2 ⟨hN, le_rfl⟩
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase (Icc 1 N) (fun j => cut N c j ^ 2) hmem,
    cut_self]
  have h : ∑ j ∈ (Icc 1 N).erase N, cut N c j ^ 2 = ∑ j ∈ (Icc 1 N).erase N, c j ^ 2 :=
    Finset.sum_congr rfl fun j hj => by rw [cut_of_ne c (Finset.mem_erase.1 hj).1]
  rw [h]
  ring

/-- For `n ≥ 2`, the inner sum of Landau's form at `n` is that of `c′` plus the edge `(N/n, N)`. -/
lemma ex_cut {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ex N c n = ex N (cut N c) n + (if n ∣ N then c (N / n) * c N else 0) := by
  unfold ex
  have hterm : ∀ j ∈ (Icc 1 N).filter (fun j => j * n ≤ N),
      c j * c (j * n) = cut N c j * cut N c (j * n) + (if j * n = N then c j * c N else 0) := by
    intro j hj
    have hjn := (Finset.mem_filter.1 hj).2
    have hjN : j ≠ N := by
      rintro rfl
      nlinarith
    by_cases h : j * n = N
    · simp only [h, ↓reduceIte, cut_self, mul_zero, zero_add]
    · simp only [h, ↓reduceIte, cut_of_ne c hjN, cut_of_ne c h, add_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  have hn0 : 0 < n := by omega
  by_cases hd : n ∣ N
  · have hmul : N / n * n = N := Nat.div_mul_cancel hd
    simp only [hd, ↓reduceIte]
    rw [Finset.sum_eq_single (N / n)]
    · simp only [hmul, ↓reduceIte]
    · intro j _ hne
      have hjn : j * n ≠ N := by
        intro h
        apply hne
        rw [← h, Nat.mul_div_cancel _ hn0]
      simp only [hjn, ↓reduceIte]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.div_pos (Nat.le_of_dvd (by omega) hd) hn0, Nat.div_le_self _ _⟩, hmul.le⟩
  · simp only [hd, ↓reduceIte]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hjn : j * n ≠ N := fun h => hd ⟨j, by rw [← h, mul_comm]⟩
    simp only [hjn, ↓reduceIte]

/-- **Landau's form with the top coefficient split off**:
`Σ_n Λ(n)n^{−1/2}Σ_{jn ≤ N}c_j c_{jn} = (the same for c′) + c_N Σ_{n ∣ N}Λ(n)n^{−1/2}c_{N/n}`. -/
lemma landau_cut {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N c n =
      ∑ n ∈ Icc 1 N, Λ n / Real.sqrt n * ex N (cut N c) n +
        c N * ∑ n ∈ Icc 1 N, (if n ∣ N then Λ n / Real.sqrt n * c (N / n) else 0) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 := (Finset.mem_Icc.1 hn).1
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have h1 : n = 1 := by omega
    subst h1
    simp [ArithmeticFunction.vonMangoldt_apply_one]
  · rw [ex_cut hN c h2]
    split_ifs <;> ring

/-! ## The parents of the top vertex -/

/-- **The parents are distinct and below `N`**: `Σ_{n ∣ N, 2 ≤ n ≤ N}c_{N/n}² ≤ Σ_{j ≤ N}c′_j²`. -/
lemma sum_parents_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    ∑ n ∈ (Icc 2 N).filter (· ∣ N), c (N / n) ^ 2 ≤ S2 N (cut N c) := by
  unfold S2
  have hN0 : 0 < N := hN
  have hinj : Set.InjOn (fun n => N / n) ((Icc 2 N).filter (· ∣ N) : Finset ℕ) := by
    intro a ha b hb hab
    have had : a ∣ N := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
    have hbd : b ∣ N := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
    have h1 : N / (N / a) = a := Nat.div_div_self had hN0.ne'
    have h2 : N / (N / b) = b := Nat.div_div_self hbd hN0.ne'
    have hab' : N / a = N / b := hab
    rw [← h1, ← h2, hab']
  have hsub : ((Icc 2 N).filter (· ∣ N)).image (fun n => N / n) ⊆ Icc 1 N := by
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hj
    have hnd : n ∣ N := (Finset.mem_filter.1 hn).2
    have hn2 : 2 ≤ n := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    exact Finset.mem_Icc.2 ⟨Nat.div_pos (Nat.le_of_dvd hN0 hnd) (by omega), Nat.div_le_self _ _⟩
  have hcongr : ∑ n ∈ (Icc 2 N).filter (· ∣ N), c (N / n) ^ 2 =
      ∑ n ∈ (Icc 2 N).filter (· ∣ N), cut N c (N / n) ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    have hne : N / n ≠ N := (Nat.div_lt_self hN0 (by omega)).ne
    rw [cut_of_ne c hne]
  rw [hcongr, ← Finset.sum_image (f := fun j => cut N c j ^ 2) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

/-- `log n ≤ n/2` for every natural `n`. -/
lemma log_le_half (n : ℕ) : Real.log n ≤ (n : ℝ) / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log ((n : ℝ) / 2) ≤ (n : ℝ) / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hn0.ne' (by norm_num)] at h1
  have h2 := Real.log_two_lt_d9
  linarith

/-- `Λ(n)²/n ≤ Λ(n)/2`. -/
lemma vonMangoldt_sq_div_le (n : ℕ) : Λ n ^ 2 / n ≤ Λ n / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : Λ n ≤ (n : ℝ) / 2 := ArithmeticFunction.vonMangoldt_le_log.trans (log_le_half n)
  rw [div_le_iff₀ hn0]
  nlinarith

/-- **`Σ_{n ∣ N}Λ(n)²/n ≤ log N/2`**, from `Σ_{n ∣ N}Λ(n) = log N`. -/
lemma sum_vonMangoldt_sq_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ (Icc 1 N).filter (· ∣ N), Λ n ^ 2 / n ≤ Real.log N / 2 := by
  have hdiv : (Icc 1 N).filter (· ∣ N) = N.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
    · rintro ⟨hd, hN0⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), Nat.le_of_dvd (by omega) hd⟩, hd⟩
  rw [hdiv]
  calc ∑ n ∈ N.divisors, Λ n ^ 2 / n ≤ ∑ n ∈ N.divisors, Λ n / 2 :=
        Finset.sum_le_sum fun n _ => vonMangoldt_sq_div_le n
    _ = Real.log N / 2 := by rw [← Finset.sum_div, ArithmeticFunction.vonMangoldt_sum]

/-- **The cross term**: `2c_N Σ_{n ∣ N}Λ(n)n^{−1/2}c_{N/n} ≤ Σ_{j ≤ N}c′_j² + c_N² log N/2`. -/
lemma cross_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    2 * (c N * ∑ n ∈ Icc 1 N, (if n ∣ N then Λ n / Real.sqrt n * c (N / n) else 0)) ≤
      S2 N (cut N c) + c N ^ 2 * (Real.log N / 2) := by
  have hterm : ∀ n ∈ Icc 1 N, 2 * (c N * (if n ∣ N then Λ n / Real.sqrt n * c (N / n) else 0)) ≤
      (if n ∣ N ∧ 2 ≤ n then c (N / n) ^ 2 else 0) + c N ^ 2 * (if n ∣ N then Λ n ^ 2 / n else 0) := by
    intro n hn
    have hn1 := (Finset.mem_Icc.1 hn).1
    by_cases hd : n ∣ N
    · rcases Nat.lt_or_ge n 2 with h2 | h2
      · have h1 : n = 1 := by omega
        subst h1
        simp [ArithmeticFunction.vonMangoldt_apply_one]
      · simp only [hd, h2, and_self, ↓reduceIte]
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
        have hsq : Λ n ^ 2 / n = (Λ n / Real.sqrt n) ^ 2 := by
          rw [div_pow, Real.sq_sqrt hn0.le]
        rw [hsq]
        nlinarith [sq_nonneg (c (N / n) - c N * (Λ n / Real.sqrt n))]
    · simp [hd]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have h1 : ∑ n ∈ Icc 1 N, (if n ∣ N ∧ 2 ≤ n then c (N / n) ^ 2 else 0) =
      ∑ n ∈ (Icc 2 N).filter (· ∣ N), c (N / n) ^ 2 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, hnN⟩, hd, h2⟩
      exact ⟨⟨h2, hnN⟩, hd⟩
    · rintro ⟨⟨h2, hnN⟩, hd⟩
      exact ⟨⟨by omega, hnN⟩, hd, h2⟩
  have h2 : ∑ n ∈ Icc 1 N, (if n ∣ N then Λ n ^ 2 / n else 0) =
      ∑ n ∈ (Icc 1 N).filter (· ∣ N), Λ n ^ 2 / n := by
    rw [← Finset.sum_filter]
  rw [h1, h2] at hsum
  have hp := sum_parents_le hN c
  have hv := sum_vonMangoldt_sq_le hN
  have hc : 0 ≤ c N ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hv hc]

/-! ## The top vertex of Landau's slack -/

/-- **The top vertex**: for `N ≥ 1` and every real `c`,
`Σ_{n ≤ N}c_n² + G(c) ≥ (log N/2 + log 4 + 2)·c_N²`, `G` Landau's slack. -/
theorem slack_top {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    c N ^ 2 * (Real.log N / 2 + (Real.log 4 + 2)) ≤ S2 N c + landauSlack N c := by
  have hG : 0 ≤ landauSlack N (cut N c) := landauSlack_nonneg N (cut N c)
  have hS := S2_cut hN c
  have hL := landau_cut hN c
  have hX := cross_le hN c
  unfold landauSlack at hG ⊢
  rw [hL, hS]
  nlinarith

/-! ## The pivot -/

/-- **The pivots grow like `log N`** (RH): for `N ≥ 1` and every real `x`,
`Q_N(x) ≥ (log N/2 + log 4 + 2)/(22e⁸)·x_N²`. -/
theorem pivot_ge (hRH : RiemannHypothesis) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (Real.log N / 2 + (Real.log 4 + 2)) / (22 * Real.exp 8) * x N ^ 2 ≤ BallWeil.form N x := by
  have h := rate_slack hRH hN x
  have ht := slack_top hN (fun n => x n * Real.sqrt n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hS2 : S2 N (fun n => x n * Real.sqrt n) = ∑ n ∈ Icc 1 N, x n ^ 2 * n := by
    unfold S2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hcN : (x N * Real.sqrt N) ^ 2 = x N ^ 2 * N := by
    rw [mul_pow, Real.sq_sqrt hN0.le]
  rw [hS2] at ht
  simp only [hcN] at ht
  have hc : 0 < 1 / (22 * Real.exp 8 * N) := by positivity
  have hm := mul_le_mul_of_nonneg_left ht hc.le
  have e : (Real.log N / 2 + (Real.log 4 + 2)) / (22 * Real.exp 8) * x N ^ 2 =
      1 / (22 * Real.exp 8 * N) * (x N ^ 2 * N * (Real.log N / 2 + (Real.log 4 + 2))) := by
    field_simp
  rw [e]
  linarith

/-- `e⁸ < 2981`. -/
lemma exp_eight_lt : Real.exp 8 < 2981 := by
  have h1 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  have h2 := Real.exp_one_lt_d9
  calc Real.exp 1 ^ 8 < 2.7182818286 ^ 8 := pow_lt_pow_left₀ h2 (Real.exp_pos 1).le (by norm_num)
    _ < 2981 := by norm_num

/-- **The orbit-lattice inequality for large `k`** (RH): if `log k ≥ 7100`, then
`Q_k(δ_k − Σ_{n < k}c_n δ_n) ≥ Q_1(δ_1) = K_H(1)` for all real `c`: the pivot inequality `d_k ≥ d_1`. -/
theorem orbitLattice_of_log_ge (hRH : RiemannHypothesis) {k : ℕ} (hk : 7100 ≤ Real.log k) (c : ℕ → ℝ) :
    BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n) := by
  have hk1 : 1 ≤ k := by
    by_contra h
    have h0 : k = 0 := by omega
    rw [h0] at hk
    norm_num at hk
  have h := pivot_ge hRH hk1 (fun n => if n = k then 1 else -c n)
  simp only [↓reduceIte, one_pow, mul_one] at h
  have hg : BallWeil.gram 1 1 < 0.0539 := by
    rw [BallWeil.gram_self, BallWeil.kψ_one]
    simpa using WeilTest.hadamard_const_lt
  have he := exp_eight_lt
  have he0 := Real.exp_pos 8
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlow : (0.0539 : ℝ) ≤ (Real.log k / 2 + (Real.log 4 + 2)) / (22 * Real.exp 8) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Under RH the pivots tend to infinity**: for every `B` there is `K` such that `Q_k(x) ≥ B` for every `k ≥ K`
and every real `x` with `x_k = 1`. -/
theorem pivot_tendsto (hRH : RiemannHypothesis) (B : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ x : ℕ → ℝ, x k = 1 → B ≤ BallWeil.form k x := by
  obtain ⟨K, hK⟩ := exists_nat_ge (Real.exp (2 * (22 * Real.exp 8) * |B|))
  refine ⟨K + 1, fun k hk x hx => ?_⟩
  have hk1 : 1 ≤ k := by omega
  have h := pivot_ge hRH hk1 x
  rw [hx, one_pow, mul_one] at h
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hKk : (K : ℝ) ≤ k := by exact_mod_cast (show K ≤ k by omega)
  have hlog : 2 * (22 * Real.exp 8) * |B| ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hk0]
    exact hK.trans hKk
  have he0 := Real.exp_pos 8
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB : |B| ≤ (Real.log k / 2 + (Real.log 4 + 2)) / (22 * Real.exp 8) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg B]
  exact (le_abs_self B).trans (hB.trans h)

/-- **The orbit-lattice conjecture is RH together with finitely many pivot inequalities**: the pivot inequality
`Q_k(δ_k − Σ_{n < k}c_n δ_n) ≥ Q_1(δ_1)` holds for every `k ≥ 1` and all real `c` if and only if RH holds and the
inequality holds for the `k` with `log k < 7100`. -/
theorem orbitLattice_iff :
    (∀ (k : ℕ) (c : ℕ → ℝ), 1 ≤ k →
        BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n)) ↔
      RiemannHypothesis ∧ ∀ (k : ℕ) (c : ℕ → ℝ), 1 ≤ k → Real.log k < 7100 →
        BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n) := by
  constructor
  · intro h
    exact ⟨BallWeil.rh_of_pivots h, fun k c hk _ => h k c hk⟩
  · rintro ⟨hRH, hfin⟩ k c hk
    rcases lt_or_ge (Real.log k) 7100 with hlt | hge
    · exact hfin k c hk hlt
    · exact orbitLattice_of_log_ge hRH hge c

end BallPivot
