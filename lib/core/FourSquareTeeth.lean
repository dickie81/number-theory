/-
# The global step in 4D, and the alternating lattice sum of `ℤ⁴`

Plain statement. Jacobi's four-square theorem (`JacobiFourSquares.r4_eq`) makes the number `r₄(n)` of points of `ℤ⁴`
on the sphere `x₁² + x₂² + x₃² + x₄² = n` a product of one factor per prime, as `GlobalTeeth` does for `ℤ²`:
* at `2`: for odd `m`, `r₄(2^k m) = 8σ(m)` if `k = 0` and `24σ(m)` if `k ≥ 1`, with `σ` the sum of divisors
  (`r4_two_pow_mul`);
* at an odd prime `p ∤ m`, `m ≠ 0`: `r₄(p^j m) = r₄(m)·(1 + p + ⋯ + p^j)` (`r4_pow_mul`).
The proof: `σ₄(n) = Σ_{d ∣ n, 4 ∤ d} d` is the convolution of the multiplicative function `d ↦ d·[4 ∤ d]` with `1`,
so it is multiplicative, with `σ₄(2^k) = 3` for `k ≥ 1` and `σ₄(m) = σ(m)` for odd `m`.

The Dirichlet series follow (`lseries_r4`): `Σ_{n ≥ 1} r₄(n)n^{−s} = 8(1 − 4^{1−s})ζ(s)ζ(s − 1)` on `Re s > 2`. Put the
charge `(−1)^{x₁+x₂+x₃+x₄}` at each point `x ≠ 0` of `ℤ⁴`, as `Madelung` does for the square lattice; on the shell
`n` it is `(−1)^n`. Since `r₄(2n) = 3r₄(n)` for odd `n` and `r₄(2n) = r₄(n)` for even `n ≥ 2`, the even shells are
`2^{−s}` times the odd ones three times over plus the even ones, and the alternating lattice sum of `ℤ⁴` is
  `Σ_{n ≥ 1} (−1)^n r₄(n) n^{−s} = −8(1 − 2^{1−s})(1 − 2^{2−s}) ζ(s) ζ(s − 1)`   (`lseries_alt`)
on `Re s > 2`, whose right side is holomorphic off `s = 1, 2` (`differentiableOn_rhs`). With Dirichlet's
`η(s) = (1 − 2^{1−s})ζ(s)` it reads `−8η(s)η(s − 1)`. At `s = 1/2`, `−8η(1/2)η(−1/2) ≈ −1.8394` is the continuation's
value of the four-dimensional Madelung constant; the numerical value is a remark, not a theorem.
-/
import Mathlib
import JacobiFourSquares
import TwoVariableZeta

open Complex Finset JacobiFourSquares

noncomputable section

namespace FourSquareTeeth

/-! ## `σ₄` is multiplicative -/

/-- `d ↦ d·[4 ∤ d]`, as an arithmetic function. -/
def dNot4 : ArithmeticFunction ℕ := ⟨fun d => if 4 ∣ d then 0 else d, by simp⟩

lemma dNot4_apply (d : ℕ) : dNot4 d = if 4 ∣ d then 0 else d := rfl

/-- For coprime `m`, `n`, `4 ∣ mn` forces `4 ∣ m` or `4 ∣ n`: only one of them can be even. -/
lemma four_dvd_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (h4 : 4 ∣ m * n) : 4 ∣ m ∨ 4 ∣ n := by
  rcases Nat.even_or_odd m with hm | hm
  · have h2 : Nat.Coprime 2 n := Nat.Coprime.coprime_dvd_left hm.two_dvd h
    exact Or.inl ((show Nat.Coprime 4 n by simpa using h2.pow_left 2).dvd_of_dvd_mul_right h4)
  · have h2 : Nat.Coprime 2 m := Nat.coprime_two_left.2 hm
    exact Or.inr ((show Nat.Coprime 4 m by simpa using h2.pow_left 2).dvd_of_dvd_mul_left h4)

lemma isMultiplicative_dNot4 : dNot4.IsMultiplicative := by
  refine ⟨by simp [dNot4_apply], fun {m n} h => ?_⟩
  simp only [dNot4_apply]
  by_cases hmn : 4 ∣ m * n
  · rcases four_dvd_of_coprime h hmn with h' | h' <;> simp [hmn, h']
  · have hm : ¬ 4 ∣ m := fun h' => hmn (dvd_mul_of_dvd_left h' n)
    have hn : ¬ 4 ∣ n := fun h' => hmn (dvd_mul_of_dvd_right h' m)
    simp [hmn, hm, hn]

lemma sigma4_eq (n : ℕ) : sigma4 n = (dNot4 * ArithmeticFunction.zeta) n := by
  rw [ArithmeticFunction.mul_zeta_apply, sigma4, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : 4 ∣ d <;> simp [dNot4_apply, h]

lemma sigma4_mul {m n : ℕ} (h : Nat.Coprime m n) : sigma4 (m * n) = sigma4 m * sigma4 n := by
  simp only [sigma4_eq]
  exact (isMultiplicative_dNot4.mul ArithmeticFunction.isMultiplicative_zeta).map_mul_of_coprime h

lemma sum_dNot4_two_pow (k : ℕ) : ∑ i ∈ range (k + 1), dNot4 (2 ^ i) = if k = 0 then 1 else 3 := by
  induction k with
  | zero => simp [dNot4_apply]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases k with _ | k
    · simp [dNot4_apply]
    · have h4 : 4 ∣ 2 ^ (k + 1 + 1) := ⟨2 ^ k, by ring⟩
      simp [dNot4_apply, h4]

lemma sigma4_two_pow (k : ℕ) : sigma4 (2 ^ k) = if k = 0 then 1 else 3 := by
  rw [sigma4_eq, ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow Nat.prime_two,
    sum_dNot4_two_pow]

lemma sigma4_odd {m : ℕ} (hm : Odd m) : sigma4 m = ArithmeticFunction.sigma 1 m := by
  rw [sigma4, ArithmeticFunction.sigma_one_apply]
  refine Finset.sum_congr (Finset.filter_true_of_mem fun d hd h4 => ?_) fun _ _ => rfl
  have hd' : Odd d := hm.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
  exact (Nat.not_even_iff_odd.2 hd') (even_iff_two_dvd.2 (dvd_trans ⟨2, rfl⟩ h4))

/-! ## The prime-by-prime count -/

/-- **The count at `2`** (the 4D analogue of `GlobalTeeth`'s prime factors): for odd `m`,
`r₄(2^k m) = 8σ(m)` if `k = 0` and `24σ(m)` if `k ≥ 1`. -/
theorem r4_two_pow_mul {k m : ℕ} (hm : Odd m) :
    r4 (2 ^ k * m) = (if k = 0 then 8 else 24) * ArithmeticFunction.sigma 1 m := by
  have hm0 : m ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hm) ⟨0, rfl⟩
  rw [r4_eq (mul_ne_zero (pow_ne_zero _ two_ne_zero) hm0),
    sigma4_mul ((Nat.coprime_two_left.2 hm).pow_left k), sigma4_two_pow, sigma4_odd hm]
  split_ifs <;> ring

/-- **The count at an odd prime**: for `p ∤ m`, `m ≠ 0`, `r₄(p^j m) = r₄(m)·(1 + p + ⋯ + p^j)`. -/
theorem r4_pow_mul {p j m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : m ≠ 0) (hpm : ¬ p ∣ m) :
    r4 (p ^ j * m) = r4 m * ∑ i ∈ range (j + 1), p ^ i := by
  rw [r4_eq (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hm), r4_eq hm,
    sigma4_mul (((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).pow_left j), sigma4_eq (p ^ j),
    ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  have h : ∀ i, dNot4 (p ^ i) = p ^ i := fun i => by
    rw [dNot4_apply]
    have : ¬ 4 ∣ p ^ i := fun h4 =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
        (Nat.prime_two.dvd_of_dvd_pow (dvd_trans ⟨2, rfl⟩ h4))).symm
    simp [this]
  simp only [h]
  ring

lemma r4_two_mul_odd {n : ℕ} (hn : Odd n) : r4 (2 * n) = 3 * r4 n := by
  have h1 : r4 (2 * n) = 24 * ArithmeticFunction.sigma 1 n := by simpa using r4_two_pow_mul (k := 1) hn
  have h0 : r4 n = 8 * ArithmeticFunction.sigma 1 n := by simpa using r4_two_pow_mul (k := 0) hn
  rw [h1, h0]
  ring

lemma r4_two_mul_even {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) : r4 (2 * n) = r4 n := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hn
    exact (Nat.not_even_iff_odd.2 hm) hn
  rw [← mul_assoc, ← pow_succ', r4_two_pow_mul hm, r4_two_pow_mul hm]
  simp [hk]

/-! ## The Dirichlet series -/

lemma summable_r4 {s : ℂ} (hs : 2 < s.re) : LSeriesSummable (fun n ↦ (r4 n : ℂ)) s :=
  (LSeriesSummable_congr s fun {n} hn => by simp [r4_eq hn]).2 ((TwoVariableZeta.LSeries_sigma4 hs).1.smul 8)

/-- **`Σ r₄(n)n^{−s} = 8(1 − 4^{1−s})ζ(s)ζ(s − 1)`** on `Re s > 2`. -/
theorem lseries_r4 {s : ℂ} (hs : 2 < s.re) :
    LSeries (fun n ↦ (r4 n : ℂ)) s = 8 * (1 - 4 ^ (1 - s)) * riemannZeta s * riemannZeta (s - 1) := by
  have h : LSeries (fun n ↦ (r4 n : ℂ)) s = LSeries ((8 : ℂ) • fun n ↦ (sigma4 n : ℂ)) s :=
    LSeries_congr (fun {n} hn => by simp [r4_eq hn]) s
  rw [h, LSeries_smul, (TwoVariableZeta.LSeries_sigma4 hs).2]
  ring

/-- **The alternating lattice sum of `ℤ⁴`** on `Re s > 2`:
`Σ_{n ≥ 1} (−1)^n r₄(n) n^{−s} = −8(1 − 2^{1−s})(1 − 2^{2−s}) ζ(s) ζ(s − 1)`. -/
theorem lseries_alt {s : ℂ} (hs : 2 < s.re) :
    LSeries (fun n ↦ (-1) ^ n * (r4 n : ℂ)) s =
      -8 * (1 - 2 ^ (1 - s)) * (1 - 2 ^ (2 - s)) * riemannZeta s * riemannZeta (s - 1) := by
  set t : ℕ → ℂ := LSeries.term (fun n ↦ (r4 n : ℂ)) s with ht
  set x : ℂ := 2 ^ (-s) with hx
  have hR : Summable t := summable_r4 hs
  have h2s : (2 : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
  have hterm2 : ∀ n : ℕ, n ≠ 0 → t (2 * n) = x * ((r4 (2 * n) : ℂ) / (n : ℂ) ^ s) := by
    intro n hn
    have hn' : (n : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hn))
    rw [ht, LSeries.term_of_ne_zero (by omega), Nat.cast_mul, natCast_mul_natCast_cpow, hx, cpow_neg]
    push_cast
    field_simp
  have heven : ∀ k : ℕ, t (2 * (2 * k)) = x * t (2 * k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [ht]
    · rw [hterm2 _ (by omega), r4_two_mul_even (even_two_mul k) (by omega), ht,
        LSeries.term_of_ne_zero (by omega)]
  have hodd : ∀ k : ℕ, t (2 * (2 * k + 1)) = 3 * x * t (2 * k + 1) := by
    intro k
    rw [hterm2 _ (by omega), r4_two_mul_odd (odd_two_mul_add_one k), ht, LSeries.term_of_ne_zero (by omega)]
    push_cast
    ring
  have hse : Summable fun k ↦ t (2 * k) := hR.comp_injective fun a b h ↦ by omega
  have hso : Summable fun k ↦ t (2 * k + 1) := hR.comp_injective fun a b h ↦ by omega
  have hsee : Summable fun k ↦ t (2 * (2 * k)) := hR.comp_injective fun a b h ↦ by omega
  have hseo : Summable fun k ↦ t (2 * (2 * k + 1)) := hR.comp_injective fun a b h ↦ by omega
  -- the whole sum, and the even part through the doubling relation
  have hL : ∑' k, t (2 * k) + ∑' k, t (2 * k + 1) = LSeries (fun n ↦ (r4 n : ℂ)) s := tsum_even_add_odd hse hso
  have hE : ∑' k, t (2 * (2 * k)) + ∑' k, t (2 * (2 * k + 1)) = ∑' k, t (2 * k) :=
    tsum_even_add_odd (f := fun k ↦ t (2 * k)) hsee hseo
  rw [tsum_congr heven, tsum_congr hodd, tsum_mul_left, tsum_mul_left] at hE
  -- the alternating sum is the even part minus the odd part
  have hceven : ∀ k : ℕ, LSeries.term (fun n ↦ (-1) ^ n * (r4 n : ℂ)) s (2 * k) = t (2 * k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [ht]
    · rw [ht, LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero (by omega), pow_mul]
      simp
  have hcodd : ∀ k : ℕ, LSeries.term (fun n ↦ (-1) ^ n * (r4 n : ℂ)) s (2 * k + 1) = -t (2 * k + 1) := by
    intro k
    rw [ht, LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero (by omega), pow_succ, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul, neg_mul, neg_div]
  have hA : ∑' k, LSeries.term (fun n ↦ (-1) ^ n * (r4 n : ℂ)) s (2 * k) +
      ∑' k, LSeries.term (fun n ↦ (-1) ^ n * (r4 n : ℂ)) s (2 * k + 1) =
      LSeries (fun n ↦ (-1) ^ n * (r4 n : ℂ)) s :=
    tsum_even_add_odd (hse.congr fun k ↦ (hceven k).symm) (hso.neg.congr fun k ↦ (hcodd k).symm)
  rw [tsum_congr hceven, tsum_congr hcodd, tsum_neg] at hA
  -- the powers of `2`
  have h21 : (2 : ℂ) ^ (1 - s) = 2 * x := by
    rw [hx, cpow_sub _ _ two_ne_zero, cpow_one, cpow_neg, div_eq_mul_inv]
  have h22 : (2 : ℂ) ^ (2 - s) = 4 * x := by
    rw [hx, cpow_sub _ _ two_ne_zero, cpow_two, cpow_neg, div_eq_mul_inv]
    norm_num
  have h41 : (4 : ℂ) ^ (1 - s) = 4 * x ^ 2 := by
    have e : (4 : ℂ) ^ (1 - s) = 2 ^ (1 - s) * 2 ^ (1 - s) := by
      rw [show (4 : ℂ) = ((2 : ℕ) : ℂ) * ((2 : ℕ) : ℂ) by norm_num, natCast_mul_natCast_cpow]
      norm_num
    rw [e, h21]
    ring
  -- `1 + 2x ≠ 0`, since `|x| = 2^{−Re s} < 1/2`
  have hx1 : 1 + 2 * x ≠ 0 := by
    intro h0
    have hxn : ‖x‖ < 1 / 2 := by
      have e : x = ((2 : ℝ) : ℂ) ^ (-s) := by rw [hx]; norm_num
      rw [e, norm_cpow_eq_rpow_re_of_pos two_pos, neg_re]
      calc (2 : ℝ) ^ (-s.re) < 2 ^ (-1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
        _ = 1 / 2 := by norm_num [Real.rpow_neg_one]
    have : x = -(1 / 2) := by linear_combination h0 / 2
    rw [this, norm_neg] at hxn
    norm_num at hxn
  have hLval := lseries_r4 hs
  rw [h41] at hLval
  rw [h21, h22, ← hA]
  apply mul_left_cancel₀ hx1
  linear_combination (4 * x - 1) * hL - 2 * hE + (4 * x - 1) * hLval

/-- **The continuation**: the right side of `lseries_alt` is holomorphic off `s = 1, 2`. -/
theorem differentiableOn_rhs : DifferentiableOn ℂ
    (fun s ↦ -8 * (1 - 2 ^ (1 - s)) * (1 - 2 ^ (2 - s)) * riemannZeta s * riemannZeta (s - 1)) {1, 2}ᶜ := by
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  have hz : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs.1
  have hz1 : DifferentiableAt ℂ (fun s ↦ riemannZeta (s - 1)) s :=
    (differentiableAt_riemannZeta fun h => hs.2 (by linear_combination h)).comp s
      (differentiableAt_id.sub_const 1)
  have hc1 : DifferentiableAt ℂ (fun s : ℂ ↦ (2 : ℂ) ^ (1 - s)) s :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero)
  have hc2 : DifferentiableAt ℂ (fun s : ℂ ↦ (2 : ℂ) ^ (2 - s)) s :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero)
  exact (((((differentiableAt_const _).mul ((differentiableAt_const _).sub hc1)).mul
    ((differentiableAt_const _).sub hc2)).mul hz).mul hz1).differentiableWithinAt

end FourSquareTeeth

#print axioms FourSquareTeeth.r4_two_pow_mul
#print axioms FourSquareTeeth.r4_pow_mul
#print axioms FourSquareTeeth.lseries_r4
#print axioms FourSquareTeeth.lseries_alt
#print axioms FourSquareTeeth.differentiableOn_rhs
