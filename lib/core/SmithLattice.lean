/-
# The gcd lattice of Smith, and Mertens' function inside the divisibility basis

Plain statement. For `N ≥ 1` and real `x_1, …, x_N`:
* **Smith's factorisation**: `gcd(i, j) = Σ_{d ∣ i, d ∣ j} φ(d)` (`gcd_eq_sum_totient`), so
  `Σ_{i,j ≤ N} x_i x_j gcd(i, j) = Σ_{d ≤ N} φ(d)·(Σ_{d ∣ i} x_i)²` (`smith_form`): the gcd matrix is `E·diag(φ)·Eᵀ`
  with `E` the divisibility matrix, an integral Gram matrix that is positive, unconditionally (`smith_nonneg`), and
  definite: the form vanishes only at `x = 0` (`smith_pos`).
* **Mertens' function in the same basis**: `Σ_{d ≤ N} μ(d)⌊N/d⌋ = 1` (`mertens_identity`), the identity
  `Σ_{n ≤ N} M(N/n) = 1` read in the divisibility basis: `μ` gives the coordinates of `δ_1` in the basis of
  divisibility vectors. RH is equivalent to `M(N) = O(N^{1/2+ε})` (`MertensExponent.rh_iff_mertens`), so in this
  integral lattice RH is a bound on the coordinates of one fixed vector, not a positivity statement.
-/
import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

namespace SmithLattice

/-- Swapping a divisor sum: `Σ_{n ≤ N} Σ_{d ∣ n} f(d) = Σ_{d ≤ N} ⌊N/d⌋·f(d)`. -/
lemma sum_divisors_swap {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, f d = ∑ d ∈ Ioc 0 N, (N / d) • f d := by
  have h : ∀ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, f d = ∑ d ∈ Ioc 0 N, if d ∣ n then f d else 0 := by
    intro n hn
    obtain ⟨h0, hk⟩ := mem_Ioc.1 hn
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd h0, (Nat.le_of_dvd h0 hd).trans hk⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, h0.ne'⟩
  rw [sum_congr rfl h, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div]

/-- **Smith's factorisation of the gcd**: `gcd(i, j) = Σ_{d ≤ N, d ∣ i, d ∣ j} φ(d)` for `i, j ≤ N`, `i ≥ 1`. -/
theorem gcd_eq_sum_totient {N i j : ℕ} (hi : i ∈ Ioc 0 N) :
    (Nat.gcd i j : ℝ) = ∑ d ∈ Ioc 0 N, if d ∣ i ∧ d ∣ j then (Nat.totient d : ℝ) else 0 := by
  obtain ⟨h0, hN⟩ := mem_Ioc.1 hi
  have hg : 0 < Nat.gcd i j := Nat.gcd_pos_of_pos_left _ h0
  rw [← Finset.sum_filter, ← Nat.sum_totient (Nat.gcd i j), Nat.cast_sum]
  congr 1
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Ioc, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨hd, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 h0, (Nat.le_of_dvd h0 hd.1).trans hN⟩, hd⟩
  · rintro ⟨-, hd⟩
    exact ⟨hd, hg.ne'⟩

/-- The divisibility sums `S_d(x) = Σ_{i ≤ N, d ∣ i} x_i`. -/
def S (N : ℕ) (x : ℕ → ℝ) (d : ℕ) : ℝ := ∑ i ∈ (Ioc 0 N).filter (d ∣ ·), x i

/-- **Smith's form**: `Σ_{i,j} x_i x_j gcd(i, j) = Σ_d φ(d)·S_d(x)²`. -/
theorem smith_form (N : ℕ) (x : ℕ → ℝ) :
    ∑ i ∈ Ioc 0 N, ∑ j ∈ Ioc 0 N, x i * x j * (Nat.gcd i j : ℝ) =
      ∑ d ∈ Ioc 0 N, (Nat.totient d : ℝ) * S N x d ^ 2 := by
  have e : ∀ i ∈ Ioc 0 N, ∀ j ∈ Ioc 0 N, x i * x j * (Nat.gcd i j : ℝ) =
      ∑ d ∈ Ioc 0 N, (Nat.totient d : ℝ) * ((if d ∣ i then x i else 0) * (if d ∣ j then x j else 0)) := by
    intro i hi j _
    rw [gcd_eq_sum_totient hi, mul_sum]
    refine sum_congr rfl fun d _ => ?_
    by_cases h1 : d ∣ i <;> by_cases h2 : d ∣ j <;> (simp [h1, h2]; try ring)
  rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => e i hi j hj]
  calc _ = ∑ i ∈ Ioc 0 N, ∑ d ∈ Ioc 0 N, ∑ j ∈ Ioc 0 N,
        (Nat.totient d : ℝ) * ((if d ∣ i then x i else 0) * (if d ∣ j then x j else 0)) :=
        sum_congr rfl fun i _ => sum_comm
    _ = ∑ d ∈ Ioc 0 N, ∑ i ∈ Ioc 0 N, ∑ j ∈ Ioc 0 N,
        (Nat.totient d : ℝ) * ((if d ∣ i then x i else 0) * (if d ∣ j then x j else 0)) := sum_comm
    _ = _ := by
        refine sum_congr rfl fun d _ => ?_
        unfold S
        rw [sq, sum_filter, sum_mul_sum, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]

/-- **The gcd lattice is positive**, unconditionally. -/
theorem smith_nonneg (N : ℕ) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Ioc 0 N, ∑ j ∈ Ioc 0 N, x i * x j * (Nat.gcd i j : ℝ) := by
  rw [smith_form]
  exact sum_nonneg fun d _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- **And definite**: the form vanishes only when every `x_i`, `i ≤ N`, is `0`. -/
theorem smith_pos (N : ℕ) (x : ℕ → ℝ)
    (h0 : ∑ i ∈ Ioc 0 N, ∑ j ∈ Ioc 0 N, x i * x j * (Nat.gcd i j : ℝ) = 0) : ∀ i ∈ Ioc 0 N, x i = 0 := by
  rw [smith_form] at h0
  have hS : ∀ d ∈ Ioc 0 N, S N x d = 0 := by
    intro d hd
    have hφ : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.2 (mem_Ioc.1 hd).1
    have := (sum_eq_zero_iff_of_nonneg fun d _ => mul_nonneg (Nat.cast_nonneg (Nat.totient d)) (sq_nonneg
      (S N x d))).1 h0 d hd
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 this).resolve_left hφ.ne')
  -- descending induction on `N − i`
  intro i hi
  obtain ⟨hi0, hiN⟩ := mem_Ioc.1 hi
  induction h : N - i using Nat.strong_induction_on generalizing i with
  | _ m ih =>
    have hSi := hS i hi
    unfold S at hSi
    have hsplit : ∑ j ∈ (Ioc 0 N).filter (i ∣ ·), x j = x i + ∑ j ∈ ((Ioc 0 N).filter (i ∣ ·)).erase i, x j :=
      (add_sum_erase _ _ (by simp [hi0, hiN])).symm
    have hrest : ∑ j ∈ ((Ioc 0 N).filter (i ∣ ·)).erase i, x j = 0 := by
      refine sum_eq_zero fun j hj => ?_
      obtain ⟨hji, hj'⟩ := mem_erase.1 hj
      obtain ⟨hjN, hdj⟩ := mem_filter.1 hj'
      obtain ⟨hj0, hjN'⟩ := mem_Ioc.1 hjN
      have hlt : i < j := lt_of_le_of_ne (Nat.le_of_dvd hj0 hdj) (Ne.symm hji)
      exact ih (N - j) (by omega) j hjN hj0 hjN' rfl
    linarith

/-- `Σ_{d ∣ n} μ(d) = [n = 1]`. -/
lemma sum_moebius_divisors (n : ℕ) : ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  exact h

/-- **Mertens' identity in the divisibility basis**: `Σ_{d ≤ N} μ(d)⌊N/d⌋ = 1` for `N ≥ 1`. -/
theorem mertens_identity {N : ℕ} (hN : 1 ≤ N) : ∑ d ∈ Ioc 0 N, ((N / d : ℕ) : ℤ) * μ d = 1 := by
  have h := sum_divisors_swap (fun d => (μ d : ℤ)) N
  simp only [sum_moebius_divisors, nsmul_eq_mul] at h
  rw [← h, sum_ite_eq' (Ioc 0 N) 1 (fun _ => (1 : ℤ))]
  simp [mem_Ioc, hN]

end SmithLattice

#print axioms SmithLattice.smith_form
#print axioms SmithLattice.smith_nonneg
#print axioms SmithLattice.smith_pos
#print axioms SmithLattice.mertens_identity
