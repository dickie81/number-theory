/-
# The prime sums of the ranges are at most 3

Plain statements. `SieveRanges.rng A` is the set of primes in `[A, A²)`. `SieveRanges.rng_sum_le` bounds
`Σ_{p ∈ rng A} 1/p` by a constant that comes from the prime number theorem and has no value. Here the bound is `3`,
by Mertens' first theorem in its elementary form:

* `sum_log_div_le`: for `n ≥ 1`, `Σ_{p ≤ n} (log p)/p ≤ log n + log 4`. Legendre's formula gives
  `Σ_{p ≤ n} ⌊n/p⌋ log p ≤ log n! ≤ n log n`, and `Σ_{p ≤ n} log p ≤ n log 4` is Chebyshev's bound.
* `rng_sum_le_three`: for `A ≥ 1`, `Σ_{p ∈ rng A} 1/p ≤ 3`. For `A ≥ 4` the sum is at most
  `(log A)⁻¹ Σ_{p < A²} (log p)/p ≤ 2 + log 4/log A`; for `A < 4` its primes are below `16`.

With an explicit bound for these sums, Brun's sieve at a fixed level has an explicit gap (`SieveProp6.zeta`).

The file imports `SieveRanges.lean`.
-/
import SieveRanges

open Real Finset

namespace SieveRanges

open scoped Chebyshev in
/-- **Mertens' first theorem, the upper bound, in its elementary form**: for `n ≥ 1`,
`Σ_{p ≤ n} (log p)/p ≤ log n + log 4`. -/
theorem sum_log_div_le {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- Legendre: `⌊n/p⌋ ≤ v_p(n!)`
  have hleg : ∀ p ∈ (Ioc 0 n).filter Nat.Prime, n / p ≤ (n.factorial).factorization p := by
    intro p hp
    obtain ⟨hpn, hpp⟩ := Finset.mem_filter.1 hp
    have hle : p ≤ n := (Finset.mem_Ioc.1 hpn).2
    rw [Nat.factorization_factorial hpp (Nat.lt_succ_self _)]
    have h1 : 1 ∈ Ico 1 (Nat.log p n + 1) := by
      rw [Finset.mem_Ico]
      exact ⟨le_refl 1, Nat.succ_lt_succ (Nat.log_pos hpp.one_lt hle)⟩
    calc n / p = n / p ^ 1 := by rw [pow_one]
      _ ≤ ∑ i ∈ Ico 1 (Nat.log p n + 1), n / p ^ i :=
        Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1
  -- `Σ_{p ≤ n} ⌊n/p⌋ log p ≤ log n!`
  have hfac : ∑ p ∈ (Ioc 0 n).filter Nat.Prime, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℝ) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
    have hsub : (Ioc 0 n).filter Nat.Prime ⊆ (n.factorial).factorization.support := by
      intro p hp
      obtain ⟨hpn, hpp⟩ := Finset.mem_filter.1 hp
      rw [Nat.support_factorization, Nat.mem_primeFactors]
      exact ⟨hpp, (hpp.dvd_factorial).2 (Finset.mem_Ioc.1 hpn).2, Nat.factorial_ne_zero n⟩
    refine le_trans (Finset.sum_le_sum fun p hp => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_)
    · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hleg p hp) (Real.log_nonneg hp1)
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hp1)
  -- `log n! ≤ n log n`
  have hpow : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h2 h1
      _ = n * Real.log n := Real.log_pow n n
  -- Chebyshev: `Σ_{p ≤ n} log p ≤ n log 4`
  have hth : ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p ≤ Real.log 4 * n := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (Nat.cast_nonneg n)
    rwa [Chebyshev.theta, Nat.floor_natCast] at h
  -- each term
  have hterm : ∀ p ∈ (Ioc 0 n).filter Nat.Prime,
      (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    obtain ⟨hpn, hpp⟩ := Finset.mem_filter.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hdiv : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]
      have h := Nat.lt_div_mul_add hpp.pos (a := n)
      have h' : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
      linarith
    calc (n : ℝ) * (Real.log p / p) = (n : ℝ) / p * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right hdiv hlog
      _ = ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hsum : (n : ℝ) * ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / p ≤
      n * Real.log n + Real.log 4 * n := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ (Ioc 0 n).filter Nat.Prime, (n : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ (Ioc 0 n).filter Nat.Prime, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) :=
          Finset.sum_le_sum hterm
      _ = ∑ p ∈ (Ioc 0 n).filter Nat.Prime, ((n / p : ℕ) : ℝ) * Real.log p +
            ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p := Finset.sum_add_distrib
      _ ≤ n * Real.log n + Real.log 4 * n := add_le_add (hfac.trans hpow) hth
  have h : (n : ℝ) * ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left h hn0

/-- **The prime sums of the ranges are at most `3`**: `Σ_{A ≤ p < A²} 1/p ≤ 3` for `A ≥ 1`. -/
theorem rng_sum_le_three {A : ℝ} (hA : 1 ≤ A) : ∑ p ∈ rng A, 1 / (p : ℝ) ≤ 3 := by
  by_cases h4 : A < 4
  · -- the primes of the range are below `16`
    have hsub : rng A ⊆ ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by
      intro p hp
      obtain ⟨hpp, -, hpA⟩ := mem_rng.1 hp
      have h16 : (p : ℝ) < 16 := by nlinarith
      have hp16 : p < 16 := by exact_mod_cast h16
      have hmem : p ∈ (Finset.range 16).filter Nat.Prime := Finset.mem_filter.2 ⟨Finset.mem_range.2 hp16, hpp⟩
      have he : (Finset.range 16).filter Nat.Prime = ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by decide
      rwa [he] at hmem
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity) ?_
    norm_num
  · rw [not_lt] at h4
    have hA0 : (0 : ℝ) < A := by linarith
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hlogA : Real.log 4 ≤ Real.log A := Real.log_le_log (by norm_num) h4
    have hlogA0 : 0 < Real.log A := lt_of_lt_of_le hlog4 hlogA
    set n := ⌈A ^ 2⌉₊ - 1 with hn
    have hc1 : 1 ≤ ⌈A ^ 2⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
    have hnlt : (n : ℝ) < A ^ 2 := by
      have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ A ^ 2)
      have hcast : (n : ℝ) = (⌈A ^ 2⌉₊ : ℝ) - 1 := by
        rw [hn, Nat.cast_sub hc1, Nat.cast_one]
      rw [hcast]
      linarith
    have hn1 : 1 ≤ n := by
      have h16 : (15 : ℝ) < ⌈A ^ 2⌉₊ := by
        have h1 : A ^ 2 ≤ ⌈A ^ 2⌉₊ := Nat.le_ceil _
        nlinarith
      have h16' : 15 < ⌈A ^ 2⌉₊ := by exact_mod_cast h16
      omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlogn : Real.log n ≤ 2 * Real.log A := by
      calc Real.log n ≤ Real.log (A ^ 2) := Real.log_le_log hn0 hnlt.le
        _ = 2 * Real.log A := by rw [Real.log_pow]; norm_num
    have hsub : rng A ⊆ (Ioc 0 n).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpp, -, hpA⟩ := mem_rng.1 hp
      refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hpp.pos, ?_⟩, hpp⟩
      have h1 : p < ⌈A ^ 2⌉₊ := Nat.lt_ceil.2 hpA
      omega
    have hterm : ∀ p ∈ rng A, 1 / (p : ℝ) ≤ (Real.log A)⁻¹ * (Real.log p / p) := by
      intro p hp
      obtain ⟨hpp, hAp, -⟩ := mem_rng.1 hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlp : Real.log A ≤ Real.log p := Real.log_le_log hA0 hAp
      rw [inv_mul_eq_div, le_div_iff₀ hlogA0, div_mul_eq_mul_div, one_mul]
      exact div_le_div_of_nonneg_right hlp hp0.le
    calc ∑ p ∈ rng A, 1 / (p : ℝ) ≤ ∑ p ∈ rng A, (Real.log A)⁻¹ * (Real.log p / p) := Finset.sum_le_sum hterm
      _ = (Real.log A)⁻¹ * ∑ p ∈ rng A, Real.log p / p := by rw [Finset.mul_sum]
      _ ≤ (Real.log A)⁻¹ * ∑ p ∈ (Ioc 0 n).filter Nat.Prime, Real.log p / p := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_)
          (inv_nonneg.2 hlogA0.le)
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le
        exact div_nonneg (Real.log_nonneg hp1) (by linarith)
      _ ≤ (Real.log A)⁻¹ * (Real.log n + Real.log 4) :=
        mul_le_mul_of_nonneg_left (sum_log_div_le hn1) (inv_nonneg.2 hlogA0.le)
      _ ≤ (Real.log A)⁻¹ * (3 * Real.log A) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hlogA0.le)
      _ = 3 := by field_simp

end SieveRanges

#print axioms SieveRanges.sum_log_div_le
#print axioms SieveRanges.rng_sum_le_three
