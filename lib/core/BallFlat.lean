/-
# The flat model: with Lebesgue measure for the zeros, the orbit spans the cubic lattice

Plain statement. Replace the zeros in `K_H(x) = Σ_γ cos(γ log x)/(¼ + γ²)` by Lebesgue measure. The flat kernel
`K₀(x) = (1/2π)∫ cos(r log x)/(r² + ¼) dr` is `e^{−|log x|/2}` (`kerFlat_eq_integral`), and its orbit Gram matrix is
`√(ab)·K₀(a/b) = min(a, b)` (`gram_flat`), the covariance of Brownian motion. For vectors `v_0, v_1, …` with Gram
matrix `c·min(m, n)`:
* the increments `v_{n+1} − v_n` are orthogonal, each of squared norm `c` (`inner_increments`). So `v_n` is their sum
  (`telescope`), and an integer combination `Σ a_i(v_{i+1} − v_i)` has squared norm `c·Σ|a_i|²` (`norm_sq_lattice`).
  The orbit spans a copy of the cubic lattice `ℤ^∞`, scaled by `√c`;
* `v_{k+1}` has squared distance exactly `c = ‖v_1‖²` from the span of `v_0, …, v_k` (`flat_pivot`, attained at
  `v_k`). This is the bound of the orbit-lattice conjecture of `docs/ball-conjecture.md`, with equality.
In `ℓ²`, `v_n = e_0 + ⋯ + e_{n−1}` is one such family, with `c = 1` (`inner_flatOrbit`).

The conjecture asks that the zeros of `ζ`, in place of Lebesgue measure, never do worse than this model. Numerically
they do much better: replacing Lebesgue measure by the density `(1/2π)log(|γ|/2π)` of the zeros makes the pivots
grow, and the primes take back part of the gain.
-/
import Mathlib
import BallPsi

open Real Complex Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace BallFlat

/-! ## The flat kernel -/

/-- **The flat kernel** `K₀(x) = e^{−|log x|/2}`, which is `min(√x, 1/√x)` for `x > 0`. -/
def kerFlat (x : ℝ) : ℝ := Real.exp (-|Real.log x| / 2)

/-- **`K₀` is `K_H` with Lebesgue measure for the zeros**: `K₀(x) = (1/2π)∫ cos(r log x)/(r² + ¼) dr`. -/
theorem kerFlat_eq_integral (x : ℝ) :
    kerFlat x = 1 / (2 * π) * ∫ r : ℝ, Real.cos (r * Real.log x) / (r ^ 2 + 1 / 4) := by
  rw [BallPsi.integral_cos_div, kerFlat]
  have : (0 : ℝ) < π := Real.pi_pos
  field_simp

lemma kerFlat_of_le {x : ℝ} (hx : 1 ≤ x) : kerFlat x = (Real.sqrt x)⁻¹ := by
  have hx0 : 0 < x := by linarith
  rw [kerFlat, abs_of_nonneg (Real.log_nonneg hx), show -Real.log x / 2 = -(Real.log x / 2) by ring, Real.exp_neg,
    BallPsi.exp_log_half hx0]

lemma kerFlat_inv (x : ℝ) : kerFlat x⁻¹ = kerFlat x := by
  rw [kerFlat, kerFlat, Real.log_inv, abs_neg]

/-- **The orbit Gram matrix of the flat kernel is `min(a, b)`**: `√(ab)·K₀(a/b) = min(a, b)` for `a, b > 0`. -/
theorem gram_flat {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.sqrt (a * b) * kerFlat (a / b) = min a b := by
  have hsa := Real.sqrt_pos.2 ha
  have hsb := Real.sqrt_pos.2 hb
  rw [Real.sqrt_mul ha.le]
  rcases le_total b a with h | h
  · rw [kerFlat_of_le ((one_le_div hb).2 h), Real.sqrt_div' _ hb.le, min_eq_right h, inv_div]
    field_simp
    exact Real.sq_sqrt hb.le
  · rw [← kerFlat_inv, inv_div, kerFlat_of_le ((one_le_div ha).2 h), Real.sqrt_div' _ ha.le, min_eq_left h, inv_div]
    field_simp
    exact Real.sq_sqrt ha.le

/-! ## Vectors with Gram matrix `c·min(m, n)` -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

section Gram

variable {v : ℕ → E} {c : ℝ} (hv : ∀ m n : ℕ, ⟪v m, v n⟫_ℂ = ((c * (min m n : ℕ) : ℝ) : ℂ))
include hv

lemma v_zero : v 0 = 0 := by
  have h := hv 0 0
  simp only [min_self, Nat.cast_zero, mul_zero, Complex.ofReal_zero] at h
  exact inner_self_eq_zero.1 h

/-- The increment `v_{n+1} − v_n` is orthogonal to `v_j` for `j ≤ n`. -/
lemma inner_increment {j n : ℕ} (hj : j ≤ n) : ⟪v j, v (n + 1) - v n⟫_ℂ = 0 := by
  rw [inner_sub_right, hv, hv, min_eq_left (by omega), min_eq_left hj, sub_self]

/-- **The increments are orthogonal, each of squared norm `c`**. -/
theorem inner_increments (i j : ℕ) :
    ⟪v (i + 1) - v i, v (j + 1) - v j⟫_ℂ = if i = j then (c : ℂ) else 0 := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hv, hv, hv, hv]
  split_ifs with h
  · subst h
    simp only [min_self, min_eq_right (Nat.le_succ i), min_eq_left (Nat.le_succ i)]
    push_cast
    ring
  · rcases lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left (by omega : i + 1 ≤ j + 1), min_eq_left (by omega : i + 1 ≤ j),
        min_eq_left (by omega : i ≤ j + 1), min_eq_left h'.le]
      push_cast
      ring
    · rw [min_eq_right (by omega : j + 1 ≤ i + 1), min_eq_right (by omega : j + 1 ≤ i),
        min_eq_right (by omega : j ≤ i + 1), min_eq_right h'.le]
      push_cast
      ring

/-- `v_n` is the sum of the increments below it. -/
theorem telescope (n : ℕ) : v n = ∑ i ∈ Finset.range n, (v (i + 1) - v i) := by
  rw [Finset.sum_range_sub, v_zero hv, sub_zero]

/-- **The orbit spans the cubic lattice**: `‖Σ a_i(v_{i+1} − v_i)‖² = c·Σ|a_i|²`. -/
theorem norm_sq_lattice (N : ℕ) (a : ℕ → ℂ) :
    ‖∑ i ∈ Finset.range N, a i • (v (i + 1) - v i)‖ ^ 2 = c * ∑ i ∈ Finset.range N, ‖a i‖ ^ 2 := by
  have key : ⟪∑ i ∈ Finset.range N, a i • (v (i + 1) - v i), ∑ i ∈ Finset.range N, a i • (v (i + 1) - v i)⟫_ℂ =
      ∑ i ∈ Finset.range N, (starRingEnd ℂ) (a i) * a i * c := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inner_sum]
    simp_rw [inner_smul_left, inner_smul_right, inner_increments hv]
    rw [Finset.sum_eq_single i (fun j _ hji => by simp only [Ne.symm hji, ↓reduceIte, mul_zero])
      (fun h => absurd hi h)]
    simp only [↓reduceIte]
    ring
  have e : ∑ i ∈ Finset.range N, (starRingEnd ℂ) (a i) * a i * (c : ℂ) =
      ((c * ∑ i ∈ Finset.range N, ‖a i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (starRingEnd ℂ (a i)), Complex.mul_conj', mul_comm]
  rw [@norm_sq_eq_re_inner ℂ, key, e]
  exact Complex.ofReal_re _

/-- **The pivots of the flat model are all `c = ‖v_1‖²`**: `v_{k+1}` keeps squared distance at least `c` from the span
of `v_0, …, v_k`, with equality at `v_k` (`inner_increments`). -/
theorem flat_pivot (k : ℕ) (a : ℕ → ℂ) : c ≤ ‖v (k + 1) - ∑ j ∈ Finset.range (k + 1), a j • v j‖ ^ 2 := by
  have hsplit : v (k + 1) - ∑ j ∈ Finset.range (k + 1), a j • v j =
      (v (k + 1) - v k) + (v k - ∑ j ∈ Finset.range (k + 1), a j • v j) := by abel
  have horth : ⟪v (k + 1) - v k, v k - ∑ j ∈ Finset.range (k + 1), a j • v j⟫_ℂ = 0 := by
    rw [← inner_conj_symm, inner_sub_left, sum_inner, inner_increment hv le_rfl]
    simp_rw [inner_smul_left]
    rw [Finset.sum_eq_zero fun j hj => by
      rw [inner_increment hv (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), mul_zero]]
    simp
  have hc : ‖v (k + 1) - v k‖ ^ 2 = c := by
    rw [@norm_sq_eq_re_inner ℂ, inner_increments hv]
    simp
  rw [hsplit, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth, ← sq, ← sq, hc]
  linarith [sq_nonneg ‖v k - ∑ j ∈ Finset.range (k + 1), a j • v j‖]

end Gram

/-! ## A family in `ℓ²` -/

/-- `v_n = e_0 + ⋯ + e_{n−1}` in `ℓ²`. -/
def flatOrbit (n : ℕ) : lp (fun _ : ℕ => ℂ) 2 := ∑ i ∈ Finset.range n, lp.single 2 i 1

lemma flatOrbit_apply (n i : ℕ) : flatOrbit n i = if i < n then 1 else 0 := by
  classical
  rw [flatOrbit, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_range]

/-- **The family `e_0 + ⋯ + e_{n−1}` has Gram matrix `min(m, n)`**. -/
theorem inner_flatOrbit (m n : ℕ) : ⟪flatOrbit m, flatOrbit n⟫_ℂ = ((min m n : ℕ) : ℂ) := by
  classical
  rw [flatOrbit, sum_inner]
  simp_rw [lp.inner_single_left, flatOrbit_apply, RCLike.inner_apply', map_one, one_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Finset.range m).filter (fun i => i < n) = Finset.range (min m n) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  rw [this, Finset.card_range]

/-- **In `ℓ²` the flat orbit attains the bound of the orbit-lattice conjecture**: `e_0 + ⋯ + e_k` keeps squared
distance at least `1 = ‖e_0‖²` from the span of the earlier partial sums, with equality at `e_0 + ⋯ + e_{k−1}`. -/
theorem flatOrbit_pivot (k : ℕ) (a : ℕ → ℂ) :
    1 ≤ ‖flatOrbit (k + 1) - ∑ j ∈ Finset.range (k + 1), a j • flatOrbit j‖ ^ 2 :=
  flat_pivot (c := 1) (fun m n => by rw [inner_flatOrbit, one_mul, Complex.ofReal_natCast]) k a

end BallFlat

#print axioms BallFlat.kerFlat_eq_integral
#print axioms BallFlat.gram_flat
#print axioms BallFlat.telescope
#print axioms BallFlat.norm_sq_lattice
#print axioms BallFlat.flat_pivot
#print axioms BallFlat.flatOrbit_pivot
