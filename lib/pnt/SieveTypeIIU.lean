/-
# Type II families with sharp prime ranges

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement (`typeII_unw`). Let `L`, `w₁` and `w₂` be a route's parameters (`SieveRoute.Route`) with `RouteOK`, and
assume its Type II estimate (`hII : SieveRoute.TypeIIAt`). Fix `K₀`, `J₀`, `e₁ > 0`, `E₀ ≥ 0` and `Λ₁ ≥ 0`. There are
`δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `m` run over `S ⊆ (P₁, P₂]` with `q^{w₁L} ≤ P₁` and
`P₂ ≤ q^{w₂L}`, with coefficients `|a_m| ≤ 1`, and let `n + 1 ≤ K₀` primes `x_i` run over all the primes up to `⌊2q^L⌋`.
Let `J ≤ J₀` sharp comparisons `P_j` hold when `ℓ_j = φ_j(m) + Σ_i e_{ji} log x_i > 0` and imply `ℓ_j ≥ 0`, with
`|e_{ji}| ≤ E₀`, `φ_j(m) ≤ Λ₁ log q` on `S`, and for each `j` a pivot `i` with `e_{ji} = ±1`. If wherever all the
comparisons hold each `x_i ≥ 2q^{e₁}` and `m∏_i x_i ≤ 2q^L`, then the family's `|A − B/φ(q)|` (`SieveFamily.Dsum`) is at
most `q^{L−δ}/φ(q)`.

This removes the dyadic weights from `SieveFamily.typeII_sharp`, whose primes carry `f0(x_i/Q_i)` at fixed scales
and whose `m` lies in a dyadic block, so that families with sharp ranges can be used.

The proof:

* `blk_spec`: for `P₁ ≥ 1`, `m ∈ (P₁, P₂]` lies in the dyadic block `(P₁2^b, 2P₁2^b]` with `b = log₂((m − 1)/P₁)`.
* `SieveDyadic.sum_bump`: each prime's range is covered by `Σ_k bump(x/2^k) = 1`, so the family is a sum of families
  with weights `bump(x_i/Q_i)` at the scales `Q_i = 2^{k_i}`, and `box_change` puts each one in `Sp`'s ranges.
* `SieveFamily.typeII_sharp` bounds each piece by `q^{L−δ}/φ(q)` (with `f0 = bump`, `F₀ = 1`, `A₀ = 1`). The pieces
  number at most `(3 + 4 log q)^{K₀+1}`, which `ev_log_pow_le` puts below `q^{δ/2}`.

`L`, `w₁` and `w₂` are a route's parameters and the Type II estimate is a hypothesis (`hII`).

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

section Main

open Classical
open scoped ContDiff

end Main

end SieveTypeIIU
