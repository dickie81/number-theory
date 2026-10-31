import SieveBox

/-!
# Sums over chains of decreasing primes

The primes of a dropped node are ordered, `p₀ > p₁ > ⋯`, and the certificate bounds their weighted sums by cutting the
primes' range at breakpoints: the primes in one interval form a run, strictly decreasing inside it, whose sum is at
most `(Σ 1/p)^r/r!`. This file has the sums over chains and runs and their bounds, without asymptotics but for the
last section.

* `chainSum L U`: the sum over strictly decreasing tuples `U > p₀ > p₁ > ⋯` with `p_i ∈ S_i` of `∏ φ_i(p_i)`, for the
  members `(S_i, φ_i)` of `L`; `runSum r L a U`: the same over the first `r` members, all at least `a`.
* `chainSum_split`: **a chain split at `a`**, exactly: the tuples with `r` primes at least `a` and the others below it.
* `runSum_le_prod`: a run is at most the product of its members' sums; `runSum_sfx_le_dec` and `decSum_le`: a run
  of primes with weights at most `c_i f` is at most `∏ c_i (Σ f)^r/r!`.
* `sum_filter_strictAnti`: the sum over the strictly decreasing tuples of a product of sets is a chain sum.
* `evLe_add`, `evLe_sum`, `evLe_const_mul`, `evLe_pow`, `evLe_min`: `SieveRough.EvLe` for sums, multiples, powers and
  minima.
-/

open Finset Filter

namespace ShortSieveChain

/-! ### Chains and runs -/

/-- The sum over the strictly decreasing tuples `U > p₀ > p₁ > ⋯` with `p_i ∈ S_i` of `∏ φ_i(p_i)`, for the members
`(S_i, φ_i)` of the list. -/
noncomputable def chainSum : List (Finset ℕ × (ℕ → ℝ)) → ℕ → ℝ
  | [], _ => 1
  | M :: L, U => ∑ p ∈ M.1.filter (· < U), M.2 p * chainSum L p

/-- The sum over the strictly decreasing tuples `U > p₀ > ⋯ > p_{r−1} ≥ a` of the first `r` members (`0` if there
are fewer). -/
noncomputable def runSum : ℕ → List (Finset ℕ × (ℕ → ℝ)) → ℕ → ℕ → ℝ
  | 0, _, _, _ => 1
  | _ + 1, [], _, _ => 0
  | r + 1, M :: L, a, U => ∑ p ∈ M.1.filter (fun p => a ≤ p ∧ p < U), M.2 p * runSum r L a p

/-- **A chain split at `a ≤ U`**: by the number `r` of its primes at least `a`. -/
theorem chainSum_split : ∀ (L : List (Finset ℕ × (ℕ → ℝ))) {a U : ℕ}, a ≤ U →
    chainSum L U = ∑ r ∈ range (L.length + 1), runSum r L a U * chainSum (L.drop r) a
  | [], a, U, _ => by simp [chainSum, runSum]
  | M :: L, a, U, h => by
    have ih : ∀ p, a ≤ p →
        chainSum L p = ∑ r ∈ range (L.length + 1), runSum r L a p * chainSum (L.drop r) a :=
      fun p hp => chainSum_split L hp
    rw [List.length_cons, sum_range_succ', chainSum, ← sum_filter_add_sum_filter_not (M.1.filter (· < U)) (· < a)]
    have e1 : (M.1.filter (· < U)).filter (· < a) = M.1.filter (· < a) := by
      ext p
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, by omega⟩, h3⟩
    have e2 : (M.1.filter (· < U)).filter (fun p => ¬p < a) = M.1.filter (fun p => a ≤ p ∧ p < U) := by
      ext p
      simp only [mem_filter, not_lt]
      tauto
    rw [e1, e2, add_comm]
    congr 1
    · rw [sum_congr rfl fun p hp => by rw [ih p (mem_filter.1 hp).2.1]]
      simp only [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun r _ => ?_
      simp only [runSum, List.drop_succ_cons, sum_mul]
      exact sum_congr rfl fun p _ => by ring
    · simp [runSum, chainSum]

theorem chainSum_nonneg : ∀ (L : List (Finset ℕ × (ℕ → ℝ))), (∀ M ∈ L, ∀ p, 0 ≤ M.2 p) → ∀ U, 0 ≤ chainSum L U
  | [], _, _ => by simp [chainSum]
  | M :: L, h, U => by
    rw [chainSum]
    exact sum_nonneg fun p _ => mul_nonneg (h M (by simp) p)
      (chainSum_nonneg L (fun M' hM' => h M' (by simp [hM'])) p)

theorem runSum_nonneg : ∀ (r : ℕ) (L : List (Finset ℕ × (ℕ → ℝ))), (∀ M ∈ L, ∀ p, 0 ≤ M.2 p) → ∀ a U,
    0 ≤ runSum r L a U
  | 0, _, _, _, _ => by simp [runSum]
  | _ + 1, [], _, _, _ => by simp [runSum]
  | r + 1, M :: L, h, a, U => by
    rw [runSum]
    exact sum_nonneg fun p _ => mul_nonneg (h M (by simp) p)
      (runSum_nonneg r L (fun M' hM' => h M' (by simp [hM'])) a p)

/-- A chain whose first member has no element below `U` has sum `0`. -/
theorem chainSum_eq_zero {M : Finset ℕ × (ℕ → ℝ)} {L : List (Finset ℕ × (ℕ → ℝ))} {U : ℕ}
    (h : ∀ p ∈ M.1, U ≤ p) : chainSum (M :: L) U = 0 := by
  rw [chainSum]
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
  exact absurd (h p hp1) (by omega)

/-! ### The bounds of a run -/

/-- **A run is at most the product of its members' sums** over `[a, V)`, for `V ≥ U`. -/
theorem runSum_le_prod : ∀ (r : ℕ) (L : List (Finset ℕ × (ℕ → ℝ))) (a U V : ℕ), U ≤ V →
    (∀ M ∈ L, ∀ p, 0 ≤ M.2 p) →
    runSum r L a U ≤ ((L.take r).map fun M => ∑ p ∈ M.1.filter (fun p => a ≤ p ∧ p < V), M.2 p).prod
  | 0, _, _, _, _, _, _ => by simp [runSum]
  | _ + 1, [], _, _, _, _, _ => by simp [runSum]
  | r + 1, M :: L, a, U, V, hUV, h0 => by
    have h0' : ∀ M' ∈ L, ∀ p, 0 ≤ M'.2 p := fun M' hM' => h0 M' (by simp [hM'])
    set Q := ((L.take r).map fun M => ∑ p ∈ M.1.filter (fun p => a ≤ p ∧ p < V), M.2 p).prod with hQ
    have hQ0 : 0 ≤ Q := List.prod_nonneg fun y hy => by
      obtain ⟨M', hM', rfl⟩ := List.mem_map.1 hy
      exact sum_nonneg fun p _ => h0' M' (List.mem_of_mem_take hM') p
    simp only [runSum, List.take_succ_cons, List.map_cons, List.prod_cons, ← hQ, sum_mul]
    calc ∑ p ∈ M.1.filter (fun p => a ≤ p ∧ p < U), M.2 p * runSum r L a p
        ≤ ∑ p ∈ M.1.filter (fun p => a ≤ p ∧ p < U), M.2 p * Q := sum_le_sum fun p hp =>
          mul_le_mul_of_nonneg_left (runSum_le_prod r L a p V (by have := (mem_filter.1 hp).2.2; omega) h0')
            (h0 M (by simp) p)
      _ ≤ ∑ p ∈ M.1.filter (fun p => a ≤ p ∧ p < V), M.2 p * Q := by
          refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => mul_nonneg (h0 M (by simp) p) hQ0
          obtain ⟨h1, h2, h3⟩ := mem_filter.1 hp
          exact mem_filter.2 ⟨h1, h2, by omega⟩

/-- The sum over the strictly decreasing tuples `U > p₁ > ⋯ > p_r ≥ a` of `S` of `∏ f(p_i)`. -/
noncomputable def decSum (S : Finset ℕ) (f : ℕ → ℝ) (a : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | r + 1, U => ∑ p ∈ S.filter (fun p => a ≤ p ∧ p < U), f p * decSum S f a r p

theorem decSum_nonneg (S : Finset ℕ) {f : ℕ → ℝ} (hf : ∀ p, 0 ≤ f p) (a : ℕ) :
    ∀ r U, 0 ≤ decSum S f a r U
  | 0, _ => by simp [decSum]
  | r + 1, U => by
    rw [decSum]
    exact sum_nonneg fun p _ => mul_nonneg (hf p) (decSum_nonneg S hf a r p)

/-- `a^{n+1} + (n + 1) b a^n ≤ (a + b)^{n+1}` for `a, b ≥ 0`. -/
theorem pow_add_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : ∀ n : ℕ,
    a ^ (n + 1) + (n + 1) * b * a ^ n ≤ (a + b) ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    have ih := pow_add_mul_le ha hb n
    have h1 : 0 ≤ a ^ n := pow_nonneg ha n
    have e : (a + b) ^ (n + 1 + 1) = (a + b) * (a + b) ^ (n + 1) := by ring
    rw [e]
    have h2 : (a + b) * (a ^ (n + 1) + (n + 1) * b * a ^ n) ≤ (a + b) * (a + b) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h3 : a ^ (n + 1 + 1) + (↑(n + 1) + 1) * b * a ^ (n + 1) ≤ (a + b) * (a ^ (n + 1) + (n + 1) * b * a ^ n) := by
      have e2 : (a + b) * (a ^ (n + 1) + (n + 1) * b * a ^ n) =
          a ^ (n + 1 + 1) + (↑(n + 1) + 1) * b * a ^ (n + 1) + (n + 1) * b ^ 2 * a ^ n := by
        push_cast
        ring
      rw [e2]
      have : 0 ≤ (n + 1 : ℝ) * b ^ 2 * a ^ n := by positivity
      linarith
    linarith

/-- **The ordered sum**: the sum over the strictly decreasing `r`-tuples of `S ∩ [a, U)` of `∏ f` is at most
`(Σ_{S ∩ [a, U)} f)^r/r!`. -/
theorem decSum_le (S : Finset ℕ) {f : ℕ → ℝ} (hf : ∀ p, 0 ≤ f p) (a : ℕ) : ∀ r U,
    decSum S f a r U ≤ (∑ p ∈ S.filter (fun p => a ≤ p ∧ p < U), f p) ^ r / r.factorial
  | 0, _ => by simp [decSum]
  | r + 1, U => by
    have ih := decSum_le S hf a r
    -- the filter at `U + 1`
    have hstep : ∀ U : ℕ, ∀ g : ℕ → ℝ, ∑ p ∈ S.filter (fun p => a ≤ p ∧ p < U + 1), g p =
        ∑ p ∈ S.filter (fun p => a ≤ p ∧ p < U), g p + if U ∈ S ∧ a ≤ U then g U else 0 := by
      intro U g
      by_cases hU : U ∈ S ∧ a ≤ U
      · rw [ite_eq_left hU]
        have e : S.filter (fun p => a ≤ p ∧ p < U + 1) = insert U (S.filter (fun p => a ≤ p ∧ p < U)) := by
          ext p
          simp only [mem_filter, mem_insert]
          constructor
          · rintro ⟨h1, h2, h3⟩
            by_cases hpU : p = U
            · exact Or.inl hpU
            · exact Or.inr ⟨h1, h2, by omega⟩
          · rintro (rfl | ⟨h1, h2, h3⟩)
            · exact ⟨hU.1, hU.2, by omega⟩
            · exact ⟨h1, h2, by omega⟩
        rw [e, sum_insert (by simp), add_comm]
      · rw [ite_eq_right hU, add_zero]
        congr 1
        ext p
        simp only [mem_filter]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, lt_of_le_of_ne (by omega) fun hpU => hU ⟨hpU ▸ h1, hpU ▸ h2⟩⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, by omega⟩
    have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    have e : ((r + 1).factorial : ℝ) = (r + 1) * r.factorial := by rw [Nat.factorial_succ]; push_cast; ring
    rw [e]
    induction U with
    | zero => simp [decSum]
    | succ U ihU =>
      have hd : decSum S f a (r + 1) (U + 1) =
          decSum S f a (r + 1) U + if U ∈ S ∧ a ≤ U then f U * decSum S f a r U else 0 := by
        simp only [decSum]
        exact hstep U _
      rw [hd, hstep U f]
      set G := ∑ p ∈ S.filter (fun p => a ≤ p ∧ p < U), f p with hG
      have hG0 : 0 ≤ G := sum_nonneg fun p _ => hf p
      by_cases hU : U ∈ S ∧ a ≤ U
      · rw [ite_eq_left hU, ite_eq_left hU, le_div_iff₀ (by positivity)]
        have hiU := (le_div_iff₀ (by positivity)).1 ihU
        have h1 : decSum S f a r U * r.factorial ≤ G ^ r := (le_div_iff₀ hfac).1 (ih U)
        have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (hf U) (by positivity) : (0 : ℝ) ≤ f U * (r + 1))
        have hB := pow_add_mul_le hG0 (hf U) r
        calc (decSum S f a (r + 1) U + f U * decSum S f a r U) * ((r + 1) * r.factorial)
            = decSum S f a (r + 1) U * ((r + 1) * r.factorial) +
                f U * (r + 1) * (decSum S f a r U * r.factorial) := by ring
          _ ≤ G ^ (r + 1) + f U * (r + 1) * G ^ r := add_le_add hiU h2
          _ ≤ (G + f U) ^ (r + 1) := by linarith
      · rw [ite_eq_right hU, ite_eq_right hU, add_zero, add_zero]
        exact ihU

/-! ### Chains given by their members' function -/

/-- The members `j, j + 1, …, m − 1` of the chain whose member `i` is `M i`. -/
noncomputable def sfx (M : ℕ → Finset ℕ × (ℕ → ℝ)) (m j : ℕ) : List (Finset ℕ × (ℕ → ℝ)) :=
  (List.range (m - j)).map fun i => M (j + i)

theorem length_sfx (M : ℕ → Finset ℕ × (ℕ → ℝ)) (m j : ℕ) : (sfx M m j).length = m - j := by
  simp [sfx]

theorem sfx_of_lt (M : ℕ → Finset ℕ × (ℕ → ℝ)) {m j : ℕ} (h : j < m) : sfx M m j = M j :: sfx M m (j + 1) := by
  unfold sfx
  obtain ⟨n, hn⟩ : ∃ n, m - j = n + 1 := ⟨m - j - 1, by omega⟩
  have hn' : m - (j + 1) = n := by omega
  rw [hn, hn', List.range_succ_eq_map, List.map_cons, List.map_map]
  have e : ∀ i, M (j + (i + 1)) = M (j + 1 + i) := fun i => by congr 1; omega
  simp only [Function.comp_def, Nat.succ_eq_add_one, Nat.add_zero, e]

theorem sfx_of_le (M : ℕ → Finset ℕ × (ℕ → ℝ)) {m j : ℕ} (h : m ≤ j) : sfx M m j = [] := by
  simp [sfx, Nat.sub_eq_zero_of_le h]

theorem drop_sfx (M : ℕ → Finset ℕ × (ℕ → ℝ)) (m : ℕ) : ∀ (r j : ℕ), (sfx M m j).drop r = sfx M m (j + r)
  | 0, j => by simp
  | r + 1, j => by
    by_cases h : j < m
    · rw [sfx_of_lt M h, List.drop_succ_cons, drop_sfx M m r (j + 1)]
      congr 1
      omega
    · rw [sfx_of_le M (by omega), sfx_of_le M (by omega)]
      simp

theorem mem_sfx {M : ℕ → Finset ℕ × (ℕ → ℝ)} {m j : ℕ} {M' : Finset ℕ × (ℕ → ℝ)} (h : M' ∈ sfx M m j) :
    ∃ i, j ≤ i ∧ i < m ∧ M' = M i := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  exact ⟨j + i, by omega, by have := List.mem_range.1 hi; omega, rfl⟩

theorem prod_take_sfx (M : ℕ → Finset ℕ × (ℕ → ℝ)) (m j r : ℕ) (g : Finset ℕ × (ℕ → ℝ) → ℝ) :
    (((sfx M m j).take r).map g).prod = ∏ i ∈ range (min r (m - j)), g (M (j + i)) := by
  rw [sfx, ← List.map_take, List.take_range, List.map_map]
  induction min r (m - j) with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, prod_range_succ]; simp

/-- **A run of weights at most `c_i f`**: the run of the members `j, …, j + r − 1` is at most `∏ c_i` times the sum
over the strictly decreasing `r`-tuples of `S` of `∏ f`, if the members' elements in `[a, U)` lie in `S`. -/
theorem runSum_sfx_le_dec (M : ℕ → Finset ℕ × (ℕ → ℝ)) (m : ℕ) (S : Finset ℕ) {f : ℕ → ℝ} (hf : ∀ p, 0 ≤ f p)
    (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i) (hM0 : ∀ i p, 0 ≤ (M i).2 p) : ∀ (r j a U : ℕ),
    (∀ i, j ≤ i → i < m → ∀ p ∈ (M i).1, a ≤ p → p < U → p ∈ S ∧ (M i).2 p ≤ c i * f p) →
    runSum r (sfx M m j) a U ≤ (∏ i ∈ range (min r (m - j)), c (j + i)) * decSum S f a r U
  | 0, j, a, U, _ => by simp [runSum, decSum]
  | r + 1, j, a, U, hM => by
    have hP0 : ∀ n, 0 ≤ ∏ i ∈ range n, c (j + 1 + i) := fun n => prod_nonneg fun i _ => hc _
    by_cases hj : j < m
    · rw [sfx_of_lt M hj, runSum, decSum, mul_sum]
      have hmin : min (r + 1) (m - j) = min r (m - (j + 1)) + 1 := by omega
      rw [hmin, prod_range_succ']
      have e : ∀ i, c (j + (i + 1)) = c (j + 1 + i) := fun i => by congr 1; omega
      simp only [e, Nat.add_zero]
      calc ∑ p ∈ (M j).1.filter (fun p => a ≤ p ∧ p < U), (M j).2 p * runSum r (sfx M m (j + 1)) a p
          ≤ ∑ p ∈ (M j).1.filter (fun p => a ≤ p ∧ p < U),
              c j * f p * ((∏ i ∈ range (min r (m - (j + 1))), c (j + 1 + i)) * decSum S f a r p) := by
            refine sum_le_sum fun p hp => ?_
            obtain ⟨hp1, hp2, hp3⟩ := mem_filter.1 hp
            have ih := runSum_sfx_le_dec M m S hf c hc hM0 r (j + 1) a p fun i hi1 hi2 q hq hq1 hq2 =>
              hM i (by omega) hi2 q hq hq1 (by omega)
            exact mul_le_mul (hM j le_rfl hj p hp1 hp2 hp3).2 ih
              (runSum_nonneg r _ (fun M' hM' q => by obtain ⟨i', -, -, rfl⟩ := mem_sfx hM'; exact hM0 i' q) a p)
              (mul_nonneg (hc j) (hf p))
        _ = ∑ p ∈ (M j).1.filter (fun p => a ≤ p ∧ p < U),
              (∏ i ∈ range (min r (m - (j + 1))), c (j + 1 + i)) * c j * (f p * decSum S f a r p) :=
            sum_congr rfl fun p _ => by ring
        _ ≤ ∑ p ∈ S.filter (fun p => a ≤ p ∧ p < U),
              (∏ i ∈ range (min r (m - (j + 1))), c (j + 1 + i)) * c j * (f p * decSum S f a r p) := by
            refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ =>
              mul_nonneg (mul_nonneg (hP0 _) (hc j)) (mul_nonneg (hf p) (decSum_nonneg S hf a r p))
            obtain ⟨hp1, hp2, hp3⟩ := mem_filter.1 hp
            exact mem_filter.2 ⟨(hM j le_rfl hj p hp1 hp2 hp3).1, hp2, hp3⟩
    · rw [sfx_of_le M (by omega), runSum]
      exact mul_nonneg (prod_nonneg fun i _ => hc _) (decSum_nonneg S hf a _ _)

/-- `Fin.cons a t` is strictly decreasing iff `t` is, below `a`. -/
theorem strictAnti_cons {n : ℕ} {a : ℕ} {t : Fin n → ℕ} :
    StrictAnti (Fin.cons a t : Fin (n + 1) → ℕ) ↔ (∀ i, t i < a) ∧ StrictAnti t := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · simpa using h (Fin.succ_pos i)
    · simpa using h (Fin.succ_lt_succ_iff.2 hij)
  · rintro ⟨h1, h2⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd hij (lt_irrefl _)
      | succ j => simpa using h1 j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ j => simpa using h2 (Fin.succ_lt_succ_iff.1 hij)

/-- A sum over the tuples of `∏ S_i` by the first coordinate and the rest. -/
theorem sum_piFinset_succ {n : ℕ} (S : Fin (n + 1) → Finset ℕ) (g : (Fin (n + 1) → ℕ) → ℝ) :
    ∑ p ∈ Fintype.piFinset S, g p =
      ∑ a ∈ S 0, ∑ t ∈ Fintype.piFinset (fun i : Fin n => S i.succ), g (Fin.cons a t) := by
  have hmap := Finset.filter_piFinset_eq_map_consEquiv S (fun _ => True)
  simp only [filter_true] at hmap
  rw [hmap, sum_map, sum_product]
  rfl

open Classical in
/-- **The tuples of a box as a chain**: the sum over the strictly decreasing tuples `U > p₀ > ⋯ > p_{n−1}` with
`p_i ∈ S_i` of `∏ φ_i(p_i)` is the chain sum of the members `(S_i, φ_i) = M i`. -/
theorem sum_filter_strictAnti : ∀ (n : ℕ) (M : ℕ → Finset ℕ × (ℕ → ℝ)) (U : ℕ),
    ∑ p ∈ (Fintype.piFinset fun i : Fin n => (M i).1).filter (fun p => StrictAnti p ∧ ∀ i, p i < U),
      ∏ i : Fin n, (M i).2 (p i) = chainSum (sfx M n 0) U
  | 0, M, U => by
    rw [sfx_of_le M le_rfl, chainSum]
    have e : (Fintype.piFinset fun i : Fin 0 => (M i).1).filter (fun p => StrictAnti p ∧ ∀ i, p i < U) =
        {Fin.elim0} := by
      ext p
      simp only [mem_filter, Fintype.mem_piFinset, mem_singleton, IsEmpty.forall_iff, true_and]
      constructor
      · intro _
        funext i
        exact Fin.elim0 i
      · rintro rfl
        exact ⟨fun a => Fin.elim0 a, trivial⟩
    rw [e, sum_singleton]
    simp
  | n + 1, M, U => by
    rw [sfx_of_lt M (Nat.succ_pos n), chainSum, sum_filter, sum_piFinset_succ]
    have hsfx : sfx M (n + 1) (0 + 1) = sfx (fun i => M (i + 1)) n 0 := by
      unfold sfx
      rw [show n + 1 - (0 + 1) = n - 0 by omega]
      exact List.map_congr_left fun i _ => by congr 1; omega
    rw [hsfx, sum_filter]
    have ih := sum_filter_strictAnti n (fun i => M (i + 1))
    refine sum_congr (by simp) fun a _ => ?_
    by_cases haU : a < U
    · rw [ite_eq_left haU, ← ih a, sum_filter, mul_sum]
      refine sum_congr rfl fun t _ => ?_
      have hc : (StrictAnti (Fin.cons a t : Fin (n + 1) → ℕ) ∧ ∀ i, (Fin.cons a t : Fin (n + 1) → ℕ) i < U) ↔
          StrictAnti t ∧ ∀ i, t i < a := by
        rw [strictAnti_cons, Fin.forall_fin_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        constructor
        · rintro ⟨⟨h1, h2⟩, -, -⟩
          exact ⟨h2, h1⟩
        · rintro ⟨h2, h1⟩
          exact ⟨⟨h1, h2⟩, haU, fun i => (h1 i).trans haU⟩
      by_cases h : StrictAnti t ∧ ∀ i, t i < a
      · rw [ite_eq_left (hc.2 h), ite_eq_left h, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
      · rw [ite_eq_right fun h' => h (hc.1 h'), ite_eq_right h, mul_zero]
    · rw [ite_eq_right haU]
      exact sum_eq_zero fun t _ => ite_eq_right fun h => haU (by simpa using h.2 0)

/-- The primes of a chain of positions `c`: `p_{c_i}`, and `0` outside `p`'s positions. -/
def chT {K : ℕ} (p : Fin K → ℕ) (c : List ℕ) : Fin c.length → ℕ :=
  fun i => if h : c.getD i 0 < K then p ⟨c.getD i 0, h⟩ else 0

open Classical in
/-- **Two chains**: if the positions of the tuples split into two chains `c` and `d`, the sum over the tuples whose
chains decrease below `U` and `V` is at most the product of the two chain sums. -/
theorem sum_le_two_chains {K : ℕ} (M : ℕ → Finset ℕ × (ℕ → ℝ)) (hM : ∀ a q, 0 ≤ (M a).2 q) (c d : List ℕ)
    (hnd : (c ++ d).Nodup) (hcov : ∀ a, a ∈ c ++ d ↔ a < K) (U V : ℕ) :
    ∑ p ∈ (Fintype.piFinset fun j : Fin K => (M j).1).filter (fun p =>
        (StrictAnti (chT p c) ∧ ∀ i, chT p c i < U) ∧ StrictAnti (chT p d) ∧ ∀ i, chT p d i < V),
      ∏ j : Fin K, (M j).2 (p j) ≤
    chainSum (sfx (fun i => M (c.getD i 0)) c.length 0) U * chainSum (sfx (fun i => M (d.getD i 0)) d.length 0) V := by
  rw [← sum_filter_strictAnti c.length (fun i => M (c.getD i 0)) U,
    ← sum_filter_strictAnti d.length (fun i => M (d.getD i 0)) V, sum_mul_sum, ← sum_product']
  have hcK : ∀ i : Fin c.length, c.getD i 0 < K := fun i => by
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact (hcov _).1 (List.mem_append_left _ (List.getElem_mem _))
  have hdK : ∀ i : Fin d.length, d.getD i 0 < K := fun i => by
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact (hcov _).1 (List.mem_append_right _ (List.getElem_mem _))
  -- the product over the positions splits over the two chains
  have hsplit : ∀ p : Fin K → ℕ, ∏ j : Fin K, (M j).2 (p j) =
      (∏ i : Fin c.length, (M (c.getD i 0)).2 (chT p c i)) * ∏ i : Fin d.length, (M (d.getD i 0)).2 (chT p d i) := by
    intro p
    set f : ℕ → ℝ := fun a => if h : a < K then (M a).2 (p ⟨a, h⟩) else 1 with hf
    have e1 : ∏ j : Fin K, (M j).2 (p j) = ∏ a ∈ range K, f a := by
      rw [← Fin.prod_univ_eq_prod_range]
      exact prod_congr rfl fun j _ => by simp [hf, j.isLt]
    have e2 : (c ++ d).toFinset = range K := by
      ext a
      simp only [List.mem_toFinset, mem_range]
      exact hcov a
    rw [e1, ← e2, List.prod_toFinset f hnd, List.map_append, List.prod_append, ← Fin.prod_univ_fun_getElem,
      ← Fin.prod_univ_fun_getElem]
    congr 1
    · refine prod_congr rfl fun i _ => ?_
      have hi := List.getD_eq_getElem c 0 i.isLt
      simp only [hf, chT, dite_eq_left (hcK i)]
      rw [dite_eq_left (hi ▸ hcK i)]
      simp only [hi]
    · refine prod_congr rfl fun i _ => ?_
      have hi := List.getD_eq_getElem d 0 i.isLt
      simp only [hf, chT, dite_eq_left (hdK i)]
      rw [dite_eq_left (hi ▸ hdK i)]
      simp only [hi]
  -- the chains determine the tuple
  have hinj : Set.InjOn (fun p : Fin K → ℕ => (chT p c, chT p d))
      ((Fintype.piFinset fun j : Fin K => (M j).1).filter (fun p =>
        (StrictAnti (chT p c) ∧ ∀ i, chT p c i < U) ∧ StrictAnti (chT p d) ∧ ∀ i, chT p d i < V) : Set _) := by
    intro p _ p' _ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    funext j
    rcases List.mem_append.1 ((hcov j).2 j.isLt) with hj | hj
    · obtain ⟨i, hi, hij⟩ := List.getElem_of_mem hj
      have := congrFun h1 ⟨i, hi⟩
      simp only [chT, dite_eq_left (hcK ⟨i, hi⟩)] at this
      have e : (⟨c.getD i 0, hcK ⟨i, hi⟩⟩ : Fin K) = j :=
        Fin.ext (show c.getD i 0 = j by rw [List.getD_eq_getElem _ _ hi, hij])
      rwa [e] at this
    · obtain ⟨i, hi, hij⟩ := List.getElem_of_mem hj
      have := congrFun h2 ⟨i, hi⟩
      simp only [chT, dite_eq_left (hdK ⟨i, hi⟩)] at this
      have e : (⟨d.getD i 0, hdK ⟨i, hi⟩⟩ : Fin K) = j :=
        Fin.ext (show d.getD i 0 = j by rw [List.getD_eq_getElem _ _ hi, hij])
      rwa [e] at this
  rw [sum_congr rfl fun p _ => hsplit p, ← sum_image (g := fun p : Fin K → ℕ => (chT p c, chT p d))
    (f := fun q => (∏ i : Fin c.length, (M (c.getD i 0)).2 (q.1 i)) *
      ∏ i : Fin d.length, (M (d.getD i 0)).2 (q.2 i)) hinj]
  refine sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun q _ _ =>
    mul_nonneg (prod_nonneg fun i _ => hM _ _) (prod_nonneg fun i _ => hM _ _)
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
  obtain ⟨hp1, ⟨hc1, hc2⟩, hd1, hd2⟩ := mem_filter.1 hp
  have hpm := Fintype.mem_piFinset.1 hp1
  refine mem_product.2 ⟨mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, hc1, hc2⟩,
    mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, hd1, hd2⟩⟩
  · simp only [chT, dite_eq_left (hcK i)]
    exact hpm _
  · simp only [chT, dite_eq_left (hdK i)]
    exact hpm _

/-! ### Limits superior -/

open SieveRough

theorem evLe_add {S T : ℝ → ℝ} {P Q : ℝ} (hS : EvLe S P) (hT : EvLe T Q) : EvLe (fun x => S x + T x) (P + Q) := by
  intro δ hδ
  filter_upwards [hS (δ / 2) (by linarith), hT (δ / 2) (by linarith)] with x h1 h2
  linarith

theorem evLe_mono {S : ℝ → ℝ} {P Q : ℝ} (hS : EvLe S P) (hPQ : P ≤ Q) : EvLe S Q := fun δ hδ => by
  filter_upwards [hS δ hδ] with x hx
  linarith

theorem evLe_of_le {S T : ℝ → ℝ} {P : ℝ} (hS : EvLe S P) (hTS : ∀ᶠ x : ℝ in atTop, T x ≤ S x) : EvLe T P :=
  fun δ hδ => by
  filter_upwards [hS δ hδ, hTS] with x h1 h2
  linarith

theorem evLe_sum {ι : Type*} (s : Finset ι) (S : ι → ℝ → ℝ) (P : ι → ℝ) (h : ∀ i ∈ s, EvLe (S i) (P i)) :
    EvLe (fun x => ∑ i ∈ s, S i x) (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun δ hδ => Eventually.of_forall fun x => by simp only [sum_empty]; linarith
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact evLe_add (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem evLe_min {S : ℝ → ℝ} {P Q : ℝ} (hP : EvLe S P) (hQ : EvLe S Q) : EvLe S (min P Q) := fun δ hδ => by
  filter_upwards [hP δ hδ, hQ δ hδ] with x h1 h2
  rcases min_choice P Q with h | h <;> rw [h] <;> assumption

theorem evLe_const_mul {S : ℝ → ℝ} {P c : ℝ} (hc : 0 ≤ c) (hS : EvLe S P) : EvLe (fun x => c * S x) (c * P) := by
  intro δ hδ
  filter_upwards [hS (δ / (c + 1)) (by positivity)] with x hx
  have h1 : c * S x ≤ c * (P + δ / (c + 1)) := mul_le_mul_of_nonneg_left hx hc
  have h2 : c * (δ / (c + 1)) ≤ δ := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

theorem evLe_pow {S : ℝ → ℝ} {P : ℝ} (hP : 0 ≤ P) (hS0 : ∀ᶠ x : ℝ in atTop, 0 ≤ S x) (hS : EvLe S P) :
    ∀ n : ℕ, EvLe (fun x => S x ^ n) (P ^ n)
  | 0 => fun δ hδ => Eventually.of_forall fun x => by simp only [pow_zero]; linarith
  | n + 1 => by
    have h := EvLe.mul (pow_nonneg hP n) hP (hS0.mono fun x hx => pow_nonneg hx n) hS0 (evLe_pow hP hS0 hS n) hS
    simpa [pow_succ] using h

end ShortSieveChain
