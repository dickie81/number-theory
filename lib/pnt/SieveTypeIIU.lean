/-
# Sharp prime ranges: the primes up to `Y`, dyadic blocks and `Dsum`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Lemmas for the Type II families with sharp prime ranges: the primes up to `Y`, the dyadic block of an integer, sums
`Dsum`, and a power of a logarithm below a power.

* `primesLe Y`: the primes up to `Y`, with `mem_primesLe`; `mem_primesTo`: for `Q ≥ 0`, `p ∈ primesTo Q` if and only
  if `p ≤ 2Q` and `p` is prime.
* `blk_spec`: for `P₁ ≥ 1`, `m ∈ (P₁, P₂]` lies in the dyadic block `(P₁2^b, 2P₁2^b]` with `b = log₂((m − 1)/P₁)`.
* `Dsum_sum`, `Dsum_subset`, `Dsum_congr`: `Dsum` (`SieveFamily.Dsum`) is additive in the weight, may be taken over a
  smaller set when the weight vanishes off it, and depends only on the weight's values on the set.
* `ev_log_pow_le`: for `r > 0`, eventually `(3 + 4 log x)^K ≤ x^r`; it puts a count of pieces such as
  `(3 + 4 log q)^{K₀+1}` below `q^{δ/2}`.

The file imports `SieveFamily.lean` and `SieveDyadic.lean`.
-/
import SieveFamily
import SieveDyadic

open Real Finset Filter Asymptotics SieveFamily SieveRoute

namespace SieveTypeIIU

/-- The primes up to `Y`. -/
def primesLe (Y : ℕ) : Finset ℕ := (Finset.range (Y + 1)).filter Nat.Prime

theorem mem_primesLe {Y p : ℕ} : p ∈ primesLe Y ↔ p ≤ Y ∧ p.Prime := by
  rw [primesLe, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The dyadic block of `m > P₁ ≥ 1`: `b = log₂((m − 1)/P₁)` has `P₁2^b < m ≤ 2P₁2^b`. -/
theorem blk_spec {P₁ m : ℕ} (hP : 1 ≤ P₁) (hm : P₁ < m) :
    P₁ * 2 ^ Nat.log 2 ((m - 1) / P₁) < m ∧ m ≤ 2 * (P₁ * 2 ^ Nat.log 2 ((m - 1) / P₁)) := by
  set t := (m - 1) / P₁ with ht
  have ht1 : 1 ≤ t := by
    rw [ht, Nat.le_div_iff_mul_le (by omega)]; omega
  have h1 : 2 ^ Nat.log 2 t ≤ t := Nat.pow_log_le_self 2 (by omega)
  have h2 : t < 2 ^ (Nat.log 2 t).succ := Nat.lt_pow_succ_log_self (by norm_num) t
  have h3 : P₁ * t ≤ m - 1 := Nat.mul_div_le (m - 1) P₁
  have h4 : m - 1 < P₁ * (t + 1) := by
    rw [ht]; exact Nat.lt_mul_div_succ (m - 1) (by omega)
  constructor
  · exact lt_of_le_of_lt (le_trans (Nat.mul_le_mul_left _ h1) h3) (by omega)
  · have h5 : P₁ * (t + 1) ≤ 2 * (P₁ * 2 ^ Nat.log 2 t) := by
      have := Nat.mul_le_mul_left P₁ (show t + 1 ≤ 2 ^ (Nat.log 2 t).succ by omega)
      rw [pow_succ] at this
      linarith
    generalize P₁ * (t + 1) = B at h4 h5
    generalize P₁ * 2 ^ Nat.log 2 t = A at h5 ⊢
    omega

/-- `Dsum` is additive in the weight. -/
theorem Dsum_sum {X ι : Type*} {q : ℕ} (a : ZMod q) (T : Finset X) (n : X → ℕ) (s : Finset ι)
    (w : ι → X → ℂ) : Dsum q a T n (fun x => ∑ i ∈ s, w i x) = ∑ i ∈ s, Dsum q a T n (w i) := by
  unfold Dsum
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]

/-- `Dsum` over a smaller set, when the weight vanishes off it. -/
theorem Dsum_subset {X : Type*} {q : ℕ} (a : ZMod q) {T T' : Finset X} (h : T' ⊆ T) (n : X → ℕ) (w : X → ℂ)
    (hw : ∀ x ∈ T, x ∉ T' → w x = 0) : Dsum q a T n w = Dsum q a T' n w := by
  unfold Dsum
  exact (Finset.sum_subset h fun x hx hx' => by rw [hw x hx hx', zero_mul]).symm

theorem Dsum_congr {X : Type*} {q : ℕ} (a : ZMod q) (T : Finset X) (n : X → ℕ) {w w' : X → ℂ}
    (h : ∀ x ∈ T, w x = w' x) : Dsum q a T n w = Dsum q a T n w' := by
  unfold Dsum
  exact Finset.sum_congr rfl fun x hx => by rw [h x hx]

/-- Eventually `(3 + 4 log x)^K ≤ x^r`, for `r > 0`. -/
theorem ev_log_pow_le (K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, (3 + 4 * Real.log x) ^ K ≤ x ^ r := by
  have hrK : 0 < r / (K + 1) := by positivity
  have h1 := (isLittleO_log_rpow_atTop hrK).def (show (0 : ℝ) < 1 / 7 by norm_num)
  filter_upwards [h1, eventually_ge_atTop (Real.exp 1)] with x hx1 hx2
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx2
  have hl : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx2
  have hxr : 0 ≤ x ^ (r / (K + 1)) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg hxr] at hx1
  have h2 : 3 + 4 * Real.log x ≤ x ^ (r / (K + 1)) := by linarith
  calc (3 + 4 * Real.log x) ^ K ≤ (x ^ (r / (K + 1))) ^ K := pow_le_pow_left₀ (by linarith) h2 K
    _ = x ^ (r / (K + 1) * K) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    _ ≤ x ^ r := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.add_one_le_exp (1 : ℝ)])
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

theorem mem_primesTo {Q : ℝ} (hQ : 0 ≤ Q) {p : ℕ} : p ∈ primesTo Q ↔ (p : ℝ) ≤ 2 * Q ∧ p.Prime := by
  rw [primesTo, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by positivity)]

end SieveTypeIIU
