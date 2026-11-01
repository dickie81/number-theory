/-
# Two primes carry the Riemann hypothesis: positivity on the slice of `p` and `q`

Plain statement. Let `p ≠ q` be primes. Call the positive rationals `p^a q^b`, `a, b ∈ ℤ`, the slice of `p` and `q`
(`pair`), and the numbers `p^i q^j`, `i, j ∈ ℕ`, its integers (`InSlice`). Let `K_H` be the Hadamard kernel, computed
from the primes (`BallWeil.kψ`). Then Mathlib's `RiemannHypothesis` holds if and only if:
* `K_H` is positive-definite on the slice (`rh_iff_posDefOn_pair`);
* `K_H(p^a q^b) ≥ −K_H(1)` for all integers `a, b` (`rh_iff_bound_pair`), and for `p = 2`, `q = 3`
  (`rh_iff_two_three`). This is the lower half of the Weil bound, on the slice only;
* in the terms of `BallWeil`, `D_m·D_n ≤ m + n + (2 − D_1²)·√(mn)` for all integers `m, n` of the slice
  (`rh_iff_weil_bound_pair`);
* every divisor `a·e₁ + b·e₂ + Σ_n c_n D_n` with integer coefficients and `c_n = 0` off the integers of the slice
  satisfies the Castelnuovo–Severi inequality `D² ≤ 2(D·e₁)(D·e₂)` (`rh_iff_castelnuovo_severi_pair`).

So the slice of any two primes already carries all of RH, and so does each statement about it in the orbit-lattice
conjecture of `docs/ball-conjecture.md`. A single prime would not do: the logarithms of the `p^a` form the discrete
set `ℤ·log p`.

* `log p/log q` is irrational (`irrational_log_div`). A rational value `a/b` would give `p^b = q^a` in `ℚ`, and the
  `p`-adic valuation of the two sides is `b` and `0`.
* So `ℤ·log p + ℤ·log q` is dense in `ℝ` (`dense_log_pair`, by Mathlib's `dense_addSubgroupClosure_pair_iff`).
* The Landau argument of `BallKernel.re_eq_zero_of_dense` needs the twin sum to be nonnegative on a dense set only,
  since the sum is continuous (`re_eq_zero_of_dense_set`). At `λ = log(p^a q^b)` the twin sum is
  `2K_H(1) + 2K_H((p^a q^b)²)` (`BallHadamard.twin_eq_kerH`). So the bound at the squares of the slice gives RH
  (`rh_of_sq_bound`).
* For divisors, `v·D_{u²} + u·D_{v²}` with `u/v = p^a q^b` gives that bound with integer coefficients, as in
  `BallWeil.minor_of_form` (`minor_of_form_on`).
-/
import Mathlib
import BallWeil

open Real Complex Finset ComplexConjugate WeilForm WeilTest
open scoped ComplexOrder

noncomputable section

namespace BallSlice

open BallKernel BallLattice BallHadamard BallPsi BallWeil

/-- **The slice of the primes `p` and `q`**: the positive rationals `p^a q^b`, `a, b ∈ ℤ`. -/
def pair (p q : ℕ) : Set ℚ := {r | ∃ a b : ℤ, r = (p : ℚ) ^ a * (q : ℚ) ^ b}

/-- **The integers of the slice**: `n = p^i q^j` with `i, j ∈ ℕ`. -/
def InSlice (p q n : ℕ) : Prop := ∃ i j : ℕ, n = p ^ i * q ^ j

/-- A kernel is **positive-definite on a set `Γ` of positive rationals** when `Σ_{a,b ∈ S} x_a x̄_b k(a/b) ≥ 0` for
every finite `S ⊆ Γ` and all complex `x`. -/
def PosDefOn (Γ : Set ℚ) (k : ℝ → ℂ) : Prop :=
  ∀ (S : Finset ℚ) (x : ℚ → ℂ), (∀ a ∈ S, 0 < a ∧ a ∈ Γ) →
    0 ≤ ∑ a ∈ S, ∑ b ∈ S, x a * conj (x b) * k ((a : ℝ) / b)

/-! ## The logarithms of the slice are dense -/

/-- **`log p/log q` is irrational** for distinct primes `p` and `q`: `p^b = q^a` has no solution with `b ≠ 0`, by the
`p`-adic valuation. -/
theorem irrational_log_div {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational (Real.log p / Real.log q) := by
  have := Fact.mk hp
  have := Fact.mk hq
  rw [irrational_iff_ne_rational]
  intro a b hb h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlq : Real.log q ≠ 0 := (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have e : (b : ℝ) * Real.log p = a * Real.log q := by
    field_simp at h
    linarith
  have e2 : Real.log ((p : ℝ) ^ b) = Real.log ((q : ℝ) ^ a) := by rw [Real.log_zpow, Real.log_zpow, e]
  have e3 : (p : ℝ) ^ b = (q : ℝ) ^ a :=
    Real.log_injOn_pos (Set.mem_Ioi.2 (zpow_pos hp0 b)) (Set.mem_Ioi.2 (zpow_pos hq0 a)) e2
  have e4 : (p : ℚ) ^ b = (q : ℚ) ^ a := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact e3
  have h5 := congrArg (padicValRat p) e4
  rw [padicValRat.zpow, padicValRat.zpow, padicValRat.self hp.one_lt, padicValRat.of_nat, padicValNat_primes hpq]
    at h5
  simp only [mul_one, Nat.cast_zero, mul_zero] at h5
  exact hb h5

/-- **`ℤ·log p + ℤ·log q` is dense in `ℝ`** for distinct primes `p` and `q`. -/
theorem dense_log_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Dense (AddSubgroup.closure {Real.log p, Real.log q} : Set ℝ) :=
  dense_addSubgroupClosure_pair_iff.2 (irrational_log_div hp hq hpq)

/-! ## The Landau argument on a dense set -/

open TwinLandau in
/-- **Twin positivity on a dense set puts every pole on the imaginary axis**: as `BallKernel.re_eq_zero_of_dense`,
with the twin sum nonnegative on any dense set of `λ`. The sum is continuous, so it is then nonnegative everywhere. -/
theorem re_eq_zero_of_dense_set {ι : Type*} [Countable ι] {P c : ι → ℂ} {G : ℂ → ℂ} (D : TwinPoles P c)
    (hc : ∀ q, c q = G (P q)) (hGe : ∀ p, G (-p) = G p) (hGn : ∀ p, 0 < p.re → G p ≠ 0) {A : Set ℝ}
    (hA : Dense A) (hW : ∀ l ∈ A, 0 ≤ Wsum P c l) (q : ι) : (P q).re = 0 := by
  have hcl : IsClosed {l : ℝ | 0 ≤ Wsum P c l} := isClosed_le continuous_const (continuous_Wsum D)
  have hall : ∀ l : ℝ, 0 ≤ Wsum P c l := fun l => (hcl.closure_subset_iff.2 hW) (hA l)
  exact re_eq_zero_of_dense D hc hGe hGn one_ne_zero (fun r _ => hall _) q

/-- **The bound at the squares of the slice gives the Riemann hypothesis**: if `K_H((p^a q^b)²) ≥ −K_H(1)` for all
integers `a, b`, then RH. At `λ = a·log p + b·log q` the twin sum is `2K_H(1) + 2K_H((p^a q^b)²)`, and these `λ` are
dense. -/
theorem rh_of_sq_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : ∀ a b : ℤ, -kψ 1 ≤ kψ (((p : ℝ) ^ a * (q : ℝ) ^ b) ^ 2)) : RiemannHypothesis := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hW : ∀ l ∈ (AddSubgroup.closure {Real.log p, Real.log q} : Set ℝ),
      0 ≤ TwinLandau.Wsum poleP (fun i => hG (poleP i)) l := by
    intro l hl
    obtain ⟨a, b, rfl⟩ := AddSubgroup.mem_closure_pair.1 hl
    have hs : 0 < (p : ℝ) ^ a * (q : ℝ) ^ b := mul_pos (zpow_pos hp0 a) (zpow_pos hq0 b)
    have e : a • Real.log p + b • Real.log q = Real.log (((p : ℝ) ^ a * (q : ℝ) ^ b) ^ 2) / 2 := by
      rw [Real.log_pow, Real.log_mul (zpow_pos hp0 a).ne' (zpow_pos hq0 b).ne', Real.log_zpow, Real.log_zpow,
        zsmul_eq_mul, zsmul_eq_mul]
      push_cast
      ring
    rw [e, twin_eq_kerH, kerH_inv, kerH_eq_kψ one_pos, kerH_eq_kψ (by positivity)]
    have hb := h a b
    have e2 : 2 * (kψ 1 : ℂ) + kψ (((p : ℝ) ^ a * (q : ℝ) ^ b) ^ 2) + kψ (((p : ℝ) ^ a * (q : ℝ) ^ b) ^ 2) =
        ((2 * kψ 1 + 2 * kψ (((p : ℝ) ^ a * (q : ℝ) ^ b) ^ 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e2]
    exact Complex.zero_le_real.2 (by linarith)
  have hline : ∀ i : ZIdx, (zetaZeroFamily i).re = 1 / 2 := fun i => by
    have h' := re_eq_zero_of_dense_set twinPoles_hG (G := hG) (fun _ => rfl) hG_neg (fun p _ => hG_ne p)
      (dense_log_pair hp hq hpq) hW i
    rw [re_poleP] at h'
    linarith
  intro s hs htriv _
  exact hline ⟨⟨s, hs, htriv⟩, ⟨0, zeroMult_pos _⟩⟩

/-! ## The slice as a ratio of its integers -/

lemma pos_of_inSlice {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (h : InSlice p q n) : 0 < n := by
  obtain ⟨i, j, rfl⟩ := h
  exact Nat.mul_pos (pow_pos hp.pos i) (pow_pos hq.pos j)

/-- `p^a q^b = u/v` with `u = p^{a⁺} q^{b⁺}` and `v = p^{a⁻} q^{b⁻}`, two integers of the slice. -/
lemma zpow_eq_div {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a b : ℤ) :
    (p : ℝ) ^ a * (q : ℝ) ^ b =
      ((p ^ a.toNat * q ^ b.toNat : ℕ) : ℝ) / ((p ^ (-a).toNat * q ^ (-b).toNat : ℕ) : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.pos.ne'
  conv_lhs => rw [← Int.toNat_sub_toNat_neg a, ← Int.toNat_sub_toNat_neg b]
  rw [zpow_sub₀ hp0, zpow_sub₀ hq0, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
  push_cast
  field_simp

lemma inSlice_num (p q : ℕ) (a b : ℤ) : InSlice p q (p ^ a.toNat * q ^ b.toNat) := ⟨_, _, rfl⟩

lemma inSlice_den (p q : ℕ) (a b : ℤ) : InSlice p q (p ^ (-a).toNat * q ^ (-b).toNat) := ⟨_, _, rfl⟩

lemma inSlice_sq {p q n : ℕ} (h : InSlice p q n) : InSlice p q (n ^ 2) := by
  obtain ⟨i, j, rfl⟩ := h
  exact ⟨2 * i, 2 * j, by ring⟩

/-! ## The equivalences -/

/-- **The Riemann hypothesis is the lower Weil bound on the slice of two primes**: for distinct primes `p` and `q`,
RH holds if and only if `K_H(p^a q^b) ≥ −K_H(1)` for all integers `a, b`, with `K_H` computed from the primes. -/
theorem rh_iff_bound_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∀ a b : ℤ, -kψ 1 ≤ kψ ((p : ℝ) ^ a * (q : ℝ) ^ b) := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  refine ⟨fun hRH a b => ?_, fun h => rh_of_sq_bound hp hq hpq fun a b => ?_⟩
  · have hr : (0 : ℚ) < (p : ℚ) ^ a * (q : ℚ) ^ b := mul_pos (zpow_pos hp0 a) (zpow_pos hq0 b)
    have hm := minor_nonneg (rh_iff_posDefH.1 hRH) hr
    have hr' : (0 : ℝ) < (p : ℝ) ^ a * (q : ℝ) ^ b :=
      mul_pos (zpow_pos (by exact_mod_cast hp.pos) a) (zpow_pos (by exact_mod_cast hq.pos) b)
    push_cast at hm
    rw [kerH_inv, kerH_eq_kψ one_pos, kerH_eq_kψ hr'] at hm
    have e : 2 * (kψ 1 : ℂ) + kψ ((p : ℝ) ^ a * (q : ℝ) ^ b) + kψ ((p : ℝ) ^ a * (q : ℝ) ^ b) =
        ((2 * kψ 1 + 2 * kψ ((p : ℝ) ^ a * (q : ℝ) ^ b) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e] at hm
    linarith [Complex.zero_le_real.1 hm]
  · have e : ((p : ℝ) ^ a * (q : ℝ) ^ b) ^ 2 = (p : ℝ) ^ (2 * a) * (q : ℝ) ^ (2 * b) := by
      rw [mul_pow, mul_comm 2 a, mul_comm 2 b, zpow_mul, zpow_mul]
      norm_cast
    rw [e]
    exact h (2 * a) (2 * b)

/-- **For `2` and `3`**: RH holds if and only if `K_H(2^a 3^b) ≥ −K_H(1)` for all integers `a, b`. -/
theorem rh_iff_two_three : RiemannHypothesis ↔ ∀ a b : ℤ, -kψ 1 ≤ kψ ((2 : ℝ) ^ a * (3 : ℝ) ^ b) := by
  have h := rh_iff_bound_pair Nat.prime_two Nat.prime_three (by norm_num)
  simpa using h

lemma minor_nonneg_on {Γ : Set ℚ} {k : ℝ → ℂ} (hk : PosDefOn Γ k) (h1 : (1 : ℚ) ∈ Γ) {r : ℚ} (hr : 0 < r)
    (hrΓ : r ∈ Γ) : 0 ≤ 2 * k 1 + k r + k (r : ℝ)⁻¹ := by
  by_cases hr1 : r = 1
  · subst hr1
    have h := hk {1} (fun _ => 2) (by simpa using h1)
    simp only [Finset.sum_singleton, Rat.cast_one, div_one, map_ofNat] at h
    simp only [Rat.cast_one, inv_one]
    calc (0 : ℂ) ≤ 2 * 2 * k 1 := h
      _ = 2 * k 1 + k 1 + k 1 := by ring
  · have h := hk {1, r} (fun _ => 1) (by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact ⟨one_pos, h1⟩
      · rw [Finset.mem_singleton.1 ha]
        exact ⟨hr, hrΓ⟩)
    simp only [Finset.sum_pair (Ne.symm hr1), map_one, one_mul, Rat.cast_one, div_one] at h
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [div_self hr0, one_div] at h
    calc (0 : ℂ) ≤ k 1 + k (↑r)⁻¹ + (k ↑r + k 1) := h
      _ = 2 * k 1 + k r + k (↑r)⁻¹ := by ring

/-- **The Riemann hypothesis is positive-definiteness on the slice of two primes**: for distinct primes `p` and `q`,
RH holds if and only if `K_H` is positive-definite on the positive rationals `p^a q^b`. -/
theorem rh_iff_posDefOn_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    RiemannHypothesis ↔ PosDefOn (pair p q) kerH := by
  refine ⟨fun hRH S x hS => rh_iff_posDefH.1 hRH S x fun a ha => (hS a ha).1,
    fun h => (rh_iff_bound_pair hp hq hpq).2 fun a b => ?_⟩
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hr : (0 : ℚ) < (p : ℚ) ^ a * (q : ℚ) ^ b := mul_pos (zpow_pos hp0 a) (zpow_pos hq0 b)
  have hm := minor_nonneg_on h ⟨0, 0, by simp⟩ hr ⟨a, b, rfl⟩
  have hr' : (0 : ℝ) < (p : ℝ) ^ a * (q : ℝ) ^ b :=
    mul_pos (zpow_pos (by exact_mod_cast hp.pos) a) (zpow_pos (by exact_mod_cast hq.pos) b)
  push_cast at hm
  rw [kerH_inv, kerH_eq_kψ one_pos, kerH_eq_kψ hr'] at hm
  have e : 2 * (kψ 1 : ℂ) + kψ ((p : ℝ) ^ a * (q : ℝ) ^ b) + kψ ((p : ℝ) ^ a * (q : ℝ) ^ b) =
      ((2 * kψ 1 + 2 * kψ ((p : ℝ) ^ a * (q : ℝ) ^ b) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e] at hm
  linarith [Complex.zero_le_real.1 hm]

/-- **The Riemann hypothesis is the upper Weil bound for the divisors of the slice**: for distinct primes `p` and `q`,
RH holds if and only if `D_m·D_n ≤ m + n + (2 − D_1²)·√(mn)` for all integers `m, n` of the slice. -/
theorem rh_iff_weil_bound_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∀ m n : ℕ, InSlice p q m → InSlice p q n →
      inter m n ≤ m + n + (2 - inter 1 1) * Real.sqrt ((m : ℝ) * n) := by
  refine ⟨fun hRH m n hm hn => (rh_iff_weil_bound.1 hRH) m n (pos_of_inSlice hp hq hm) (pos_of_inSlice hp hq hn),
    fun h => (rh_iff_bound_pair hp hq hpq).2 fun a b => ?_⟩
  set u := p ^ a.toNat * q ^ b.toNat
  set v := p ^ (-a).toNat * q ^ (-b).toNat
  have hu := pos_of_inSlice hp hq (inSlice_num p q a b)
  have hv := pos_of_inSlice hp hq (inSlice_den p q a b)
  have hb := h u v (inSlice_num p q a b) (inSlice_den p q a b)
  have hk : 2 - inter 1 1 = kψ 1 := by rw [inter_one, kψ_one]; ring
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hs : 0 < Real.sqrt ((u : ℝ) * v) := Real.sqrt_pos.2 (mul_pos hu0 hv0)
  rw [hk] at hb
  unfold inter gram at hb
  rw [zpow_eq_div hp hq a b]
  nlinarith

/-- With `u/v = s`, the divisor `v·D_{u²} + u·D_{v²}` gives the bound at `s²`, when the coefficients may be nonzero
only where `P` holds and `P` holds at `u²` and `v²`. -/
lemma minor_of_form_on {P : ℕ → Prop} (h : ∀ (N : ℕ) (x : ℕ → ℤ), (∀ n, x n ≠ 0 → P n) → 0 ≤ form N (fun n => x n))
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (hPu : P (u ^ 2)) (hPv : P (v ^ 2)) :
    -kψ 1 ≤ kψ (((u : ℝ) / v) ^ 2) := by
  rcases eq_or_ne u v with rfl | huv
  · rw [div_self (by exact_mod_cast hu.ne'), one_pow]
    linarith [kψ_one_pos]
  · have hu2 : 0 < u ^ 2 := pow_pos hu 2
    have hv2 : 0 < v ^ 2 := pow_pos hv 2
    have hne : u ^ 2 ≠ v ^ 2 := fun e => huv (Nat.pow_left_injective (by norm_num) e)
    have hmN : u ^ 2 ∈ Icc 1 (max (u ^ 2) (v ^ 2)) := Finset.mem_Icc.2 ⟨hu2, le_max_left _ _⟩
    have hnN : v ^ 2 ∈ Icc 1 (max (u ^ 2) (v ^ 2)) := Finset.mem_Icc.2 ⟨hv2, le_max_right _ _⟩
    have hx := h (max (u ^ 2) (v ^ 2)) (fun i => if i = u ^ 2 then (v : ℤ) else if i = v ^ 2 then (u : ℤ) else 0)
      (fun n hn => by
        by_cases h1 : n = u ^ 2
        · rw [h1]; exact hPu
        · by_cases h2 : n = v ^ 2
          · rw [h2]; exact hPv
          · simp [h1, h2] at hn)
    have e : (fun i => (((if i = u ^ 2 then (v : ℤ) else if i = v ^ 2 then (u : ℤ) else 0 : ℤ)) : ℝ)) =
        fun i => if i = u ^ 2 then (v : ℝ) else if i = v ^ 2 then (u : ℝ) else 0 := by
      funext i
      split_ifs <;> simp
    rw [e, form_two hmN hnN hne, gram_self, gram_self, gram_sq] at hx
    have huv0 : (0 : ℝ) < (u : ℝ) ^ 2 * v ^ 2 := by positivity
    push_cast at hx
    nlinarith

/-- **The Riemann hypothesis is Castelnuovo–Severi for the divisors of the slice**: for distinct primes `p` and `q`,
RH holds if and only if every `D = a·e₁ + b·e₂ + Σ_{n ≤ N} c_n D_n` with integer coefficients, and `c_n = 0` unless
`n = p^i q^j`, satisfies `D² ≤ 2(D·e₁)(D·e₂)`. -/
theorem rh_iff_castelnuovo_severi_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∀ (a b : ℤ) (N : ℕ) (c : ℕ → ℤ), (∀ n, c n ≠ 0 → InSlice p q n) →
      selfInt a b N (fun n => c n) ≤ 2 * deg₁ b N (fun n => c n) * deg₂ a N (fun n => c n) := by
  refine ⟨fun hRH a b N c _ => rh_iff_castelnuovo_severi.1 hRH a b N c, fun h => rh_of_sq_bound hp hq hpq fun a b => ?_⟩
  have hform : ∀ (N : ℕ) (x : ℕ → ℤ), (∀ n, x n ≠ 0 → InSlice p q n) → 0 ≤ form N (fun n => x n) := by
    intro N x hx
    have h0 := h 0 0 N x hx
    have e := two_deg_sub_selfInt 0 0 N (fun n => x n)
    simp only [Int.cast_zero] at h0
    linarith
  have hu := pos_of_inSlice hp hq (inSlice_num p q a b)
  have hv := pos_of_inSlice hp hq (inSlice_den p q a b)
  rw [zpow_eq_div hp hq a b]
  exact minor_of_form_on hform hu hv (inSlice_sq (inSlice_num p q a b)) (inSlice_sq (inSlice_den p q a b))

end BallSlice

#print axioms BallSlice.irrational_log_div
#print axioms BallSlice.dense_log_pair
#print axioms BallSlice.re_eq_zero_of_dense_set
#print axioms BallSlice.rh_iff_bound_pair
#print axioms BallSlice.rh_iff_two_three
#print axioms BallSlice.rh_iff_posDefOn_pair
#print axioms BallSlice.rh_iff_weil_bound_pair
#print axioms BallSlice.rh_iff_castelnuovo_severi_pair
