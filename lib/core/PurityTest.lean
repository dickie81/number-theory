/-
# The purity test: an Euler product and a functional equation, without positivity

Plain statement. Let `Y = 𝔾_m × (𝔸² ∖ 0)` over `𝔽_3`, so that `N_d = #Y(𝔽_{3^d}) = (3^d − 1)(9^d − 1)` (`card_Y`).
* `N_d = 27^d + 1 − (9^d + 3^d)` (`countY_eq`). So the zeta function `exp(Σ_d N_dT^d/d)` of `Y` is
  `Z(T) = (1 − 9T)(1 − 3T)/((1 − T)(1 − 27T))`, which has the shape of an elliptic curve's over `𝔽_27` and its
  functional equation: `Z(1/(27T)) = Z(T)` (`zeta_functional_equation`).
* It has an Euler product: there are integers `b_n ≥ 0` with `Σ_{d∣n} d·b_d = N_n` for every `n ≥ 1`
  (`euler_product`). That is `Z(T) = Π_n (1 − T^n)^{−b_n}`, and `b_n` is the number of closed points of `Y` of degree
  `n`.
* But the kernel of its counts, `c(d) = (27^{|d|} + 1 − N_{|d|})/27^{|d|/2}` and `c(0) = 2`, the kernel of
  `WeilFF.countKernel_posDef_iff` for an elliptic curve over `𝔽_27`, is not positive-definite on `ℤ` (`not_posDef`).
  Its inverse zeros `9` and `3` are off the circle `|α| = √27`, and already `c(1) = 12/√27 > 2 = c(0)`.
* Every elliptic curve over `𝔽_q` of odd characteristic has a positive-definite kernel (`posDef_elliptic`, from the
  lattice of `ManinLattice`). So no elliptic curve over a field with 27 elements has the counts of `Y`; already none
  has `N_1 = 16` points (`card_ne_countY`, from Hasse's bound `ManinHasse.abs_trace_le`).

So the positivity in Weil's criterion does not follow from an Euler product and a functional equation. For a curve it
is purity: all the inverse zeros have the one absolute value `√q`. In the lattice of `ManinLattice` that is the
Frobenius multiplying the definite form by `q`; the inverse zeros of `Y` have the two absolute values `9` and `3`.
* The `b_n` are integers by the necklace congruence `n ∣ Σ_{u∣n} μ(u)a^{n/u}` (`dvd_necklace`). At a prime power
  `p^j ∥ n` the sum is `Σ_{w∣m} μ(w)(y^{p^j} − y^{p^{j−1}})` with `y = a^{m/w}` (`necklace_prime_pow_mul`), and
  `p^j ∣ y^{p^j} − y^{p^{j−1}}` (`prime_pow_dvd_pow_sub`).
* They are nonnegative because `N_n > Σ_{d<n} 27^d ≥ Σ_{d<n} N_d` (`placesY_nonneg`).

This is the second part of the fourth of the first steps in `docs/ball-conjecture.md`.
-/
import WeilFF
import ManinLattice

open Finset ArithmeticFunction ComplexConjugate
open scoped ArithmeticFunction.Moebius

namespace PurityTest

/-! ## The necklace congruence -/

/-- `Σ_{u ∣ n} μ(u) a^{n/u}`, the number of words of length `n` in `a` letters that are not periodic. -/
def necklace (a : ℤ) (n : ℕ) : ℤ := ∑ u ∈ n.divisors, μ u * a ^ (n / u)

/-- `p^{k+1} ∣ x^{p^{k+1}} − x^{p^k}`, from Fermat's `p ∣ x^p − x`. -/
lemma prime_pow_dvd_pow_sub {p : ℕ} (hp : p.Prime) (k : ℕ) (x : ℤ) :
    (p : ℤ) ^ (k + 1) ∣ x ^ p ^ (k + 1) - x ^ p ^ k := by
  have := Fact.mk hp
  have h1 : (p : ℤ) ∣ x ^ p - x := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  have h := dvd_sub_pow_of_dvd_sub h1 k
  rwa [← pow_mul, ← pow_succ'] at h

/-- Sums over the divisors of a product of coprime numbers. -/
lemma sum_divisors_coprime_mul {M : Type*} [AddCommMonoid M] {m n : ℕ} (h : m.Coprime n) (f : ℕ → M) :
    ∑ e ∈ (m * n).divisors, f e = ∑ u ∈ m.divisors, ∑ w ∈ n.divisors, f (u * w) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image h.mul_injOn_divisors, Finset.sum_product]

/-- **The necklace sum at a prime power**: for `p^{k+1}` coprime to `m`,
`Σ_{u ∣ p^{k+1}m} μ(u)a^{p^{k+1}m/u} = Σ_{w ∣ m} μ(w)(y^{p^{k+1}} − y^{p^k})` with `y = a^{m/w}`. -/
lemma necklace_prime_pow_mul (a : ℤ) {p : ℕ} (hp : p.Prime) (k : ℕ) {m : ℕ} (hm : (p ^ (k + 1)).Coprime m) :
    necklace a (p ^ (k + 1) * m) =
      ∑ w ∈ m.divisors, μ w * ((a ^ (m / w)) ^ p ^ (k + 1) - (a ^ (m / w)) ^ p ^ k) := by
  unfold necklace
  rw [sum_divisors_coprime_mul hm, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : ∀ i ∈ Finset.range (k + 1 + 1), ∀ w ∈ m.divisors,
      μ (p ^ i * w) * a ^ (p ^ (k + 1) * m / (p ^ i * w)) =
        μ (p ^ i) * (μ w * (a ^ (m / w)) ^ p ^ (k + 1 - i)) := by
    intro i hi w hw
    have hi' : i ≤ k + 1 := by simp only [Finset.mem_range] at hi; omega
    have hpi : p ^ i ∣ p ^ (k + 1) := pow_dvd_pow p hi'
    have hwm : w ∣ m := Nat.dvd_of_mem_divisors hw
    have hcop : (p ^ i).Coprime w := (hm.coprime_dvd_left hpi).coprime_dvd_right hwm
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop, ← Nat.div_mul_div_comm hpi hwm,
      Nat.pow_div hi' hp.pos, ← pow_mul, mul_comm (p ^ (k + 1 - i)) (m / w), pow_mul]
    ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (hterm i hi), Finset.sum_range_succ',
    Finset.sum_range_succ']
  have hz : ∀ i ∈ Finset.range k,
      ∑ w ∈ m.divisors, μ (p ^ (i + 1 + 1)) * (μ w * (a ^ (m / w)) ^ p ^ (k + 1 - (i + 1 + 1))) = 0 := by
    intro i _
    rw [moebius_apply_prime_pow hp (by omega)]
    simp
  rw [Finset.sum_eq_zero hz, zero_add, zero_add, pow_zero, pow_one, moebius_apply_one, moebius_apply_prime hp,
    Nat.sub_zero, Nat.add_sub_cancel, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

/-- **The necklace congruence**: `n ∣ Σ_{u ∣ n} μ(u)a^{n/u}` for every integer `a`. -/
theorem dvd_necklace (a : ℤ) {n : ℕ} (hn : 0 < n) : (n : ℤ) ∣ necklace a n := by
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hj : k + 1 ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn.ne').1 hpk
  obtain ⟨j, hjdef⟩ : ∃ j, n.factorization p = j + 1 := ⟨n.factorization p - 1, by omega⟩
  have hn' : n = p ^ (j + 1) * (n / p ^ (j + 1)) := by
    rw [← hjdef]; exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hcop : (p ^ (j + 1)).Coprime (n / p ^ (j + 1)) := by
    rw [← hjdef]; exact (Nat.coprime_ordCompl hp hn.ne').pow_left _
  have hdvd : (p : ℤ) ^ (k + 1) ∣ necklace a n := by
    rw [hn', necklace_prime_pow_mul a hp j hcop]
    refine Finset.dvd_sum fun w _ => dvd_mul_of_dvd_right ?_ _
    exact (pow_dvd_pow _ (by omega)).trans (prime_pow_dvd_pow_sub hp j _)
  rw [← Int.natCast_dvd]
  exact_mod_cast hdvd

/-! ## The variety `Y = 𝔾_m × (𝔸² ∖ 0)` over `𝔽_3` -/

/-- `N_d = (3^d − 1)(9^d − 1)`, the number of points of `Y` over `𝔽_{3^d}`. -/
def countY (d : ℕ) : ℤ := (3 ^ d - 1) * (9 ^ d - 1)

/-- **The points of `Y`**: `#(𝔽_{3^d}^× × (𝔽_{3^d}² ∖ 0)) = (3^d − 1)(9^d − 1)`. -/
theorem card_Y (d : ℕ) (hd : d ≠ 0) :
    (Nat.card ((GaloisField 3 d)ˣ × {v : Fin 2 → GaloisField 3 d // v ≠ 0}) : ℤ) = countY d := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 d) = 3 ^ d := GaloisField.card 3 d hd
  have hV : Nat.card {v : Fin 2 → GaloisField 3 d // v ≠ 0} + 1 = 9 ^ d := by
    have h := Nat.card_congr (Equiv.sumCompl (· = (0 : Fin 2 → GaloisField 3 d)))
    rw [Nat.card_sum, Nat.card_unique, Nat.card_fun, hK, Nat.card_fin] at h
    rw [show (9 : ℕ) ^ d = (3 ^ d) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num, ← h, add_comm]
  have h3 : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.card_prod, Nat.card_units, hK, countY, Nat.cast_mul, Nat.cast_sub h3]
  rw [show Nat.card {v : Fin 2 → GaloisField 3 d // v ≠ 0} = 9 ^ d - 1 by omega,
    Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
  push_cast
  ring

/-- `N_d = 27^d + 1 − (9^d + 3^d)`: the counts of an elliptic curve over `𝔽_27` with inverse zeros `9` and `3`. -/
lemma countY_eq (d : ℕ) : countY d = 27 ^ d + 1 - (9 ^ d + 3 ^ d) := by
  have h27 : (27 : ℤ) ^ d = 3 ^ d * 9 ^ d := by rw [← mul_pow]; norm_num
  rw [countY, h27]
  ring

/-- The zeta function of `Y`, `(1 − 9T)(1 − 3T)/((1 − T)(1 − 27T))`. -/
noncomputable def zetaY (T : ℂ) : ℂ := (1 - 9 * T) * (1 - 3 * T) / ((1 - T) * (1 - 27 * T))

/-- **The functional equation of an elliptic curve over `𝔽_27`**: `Z(1/(27T)) = Z(T)`. -/
theorem zeta_functional_equation (T : ℂ) (h0 : T ≠ 0) (h1 : T ≠ 1) (h27 : 27 * T ≠ 1) :
    zetaY (1 / (27 * T)) = zetaY T := by
  have e1 : (1 : ℂ) - T ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have e2 : (1 : ℂ) - 27 * T ≠ 0 := sub_ne_zero.2 (Ne.symm h27)
  have e3 : (27 : ℂ) * T - 1 ≠ 0 := sub_ne_zero.2 h27
  have e4 : T - 1 ≠ 0 := sub_ne_zero.2 h1
  have e5 : (1 : ℂ) - 1 / (27 * T) ≠ 0 := by
    rw [show (1 : ℂ) - 1 / (27 * T) = (27 * T - 1) / (27 * T) by field_simp]
    exact div_ne_zero e3 (mul_ne_zero (by norm_num) h0)
  have e6 : (1 : ℂ) - 27 * (1 / (27 * T)) ≠ 0 := by
    rw [show (1 : ℂ) - 27 * (1 / (27 * T)) = (T - 1) / T by field_simp]
    exact div_ne_zero e4 h0
  unfold zetaY
  rw [div_eq_div_iff (mul_ne_zero e5 e6) (mul_ne_zero e1 e2)]
  field_simp
  ring

/-- The Möbius transform `Σ_{u∣n} μ(u)N_{n/u}`, which is `n·b_n`. -/
def placesY (n : ℕ) : ℤ := ∑ x ∈ n.divisorsAntidiagonal, μ x.1 * countY x.2

lemma placesY_eq (n : ℕ) : placesY n = necklace 27 n - necklace 9 n - necklace 3 n + necklace 1 n := by
  unfold placesY necklace
  rw [Nat.sum_divisorsAntidiagonal (fun a b => μ a * countY b)]
  simp only [countY_eq, one_pow, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => by ring

lemma dvd_placesY {n : ℕ} (hn : 0 < n) : (n : ℤ) ∣ placesY n := by
  rw [placesY_eq]
  exact dvd_add (dvd_sub (dvd_sub (dvd_necklace 27 hn) (dvd_necklace 9 hn)) (dvd_necklace 3 hn))
    (dvd_necklace 1 hn)

/-- **The `b_n` are nonnegative**: `N_n > Σ_{d<n} 27^d ≥ Σ_{d<n} N_d`. -/
lemma placesY_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ placesY n := by
  have hpos : ∀ d : ℕ, (1 : ℤ) ≤ 3 ^ d ∧ (1 : ℤ) ≤ 9 ^ d := fun d =>
    ⟨one_le_pow₀ (by norm_num), one_le_pow₀ (by norm_num)⟩
  have h0 : ∀ d, 0 ≤ countY d := fun d =>
    mul_nonneg (by linarith [(hpos d).1]) (by linarith [(hpos d).2])
  have hle : ∀ d, countY d ≤ 27 ^ d := fun d => by
    have h27 : (27 : ℤ) ^ d = 3 ^ d * 9 ^ d := by rw [← mul_pow]; norm_num
    rw [countY, h27]
    exact mul_le_mul (by linarith) (by linarith) (by linarith [(hpos d).2]) (by positivity)
  -- `placesY n = N_n + Σ_{d ∈ properDivisors n} μ(n/d)N_d`
  have hsplit : placesY n = countY n + ∑ d ∈ n.properDivisors, μ (n / d) * countY d := by
    unfold placesY
    rw [Nat.sum_divisorsAntidiagonal' (fun a b => μ a * countY b), ← Nat.cons_self_properDivisors hn.ne',
      Finset.sum_cons, Nat.div_self hn, moebius_apply_one, one_mul]
  have hlow : -∑ d ∈ Finset.range n, (27 : ℤ) ^ d ≤ ∑ d ∈ n.properDivisors, μ (n / d) * countY d := by
    calc -∑ d ∈ Finset.range n, (27 : ℤ) ^ d ≤ -∑ d ∈ Finset.range n, countY d :=
          neg_le_neg (Finset.sum_le_sum fun d _ => hle d)
      _ ≤ -∑ d ∈ n.properDivisors, countY d := by
          refine neg_le_neg (Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) fun d _ _ => h0 d)
          exact Finset.mem_range.2 (Nat.mem_properDivisors.1 hd).2
      _ = ∑ d ∈ n.properDivisors, -countY d := by rw [Finset.sum_neg_distrib]
      _ ≤ ∑ d ∈ n.properDivisors, μ (n / d) * countY d := Finset.sum_le_sum fun d _ => by
          have := abs_moebius_le_one (n := n / d)
          nlinarith [abs_le.1 this, h0 d]
  have hgeom : (∑ d ∈ Finset.range n, (27 : ℤ) ^ d) * 26 = 27 ^ n - 1 := by
    have := geom_sum_mul (27 : ℤ) n
    norm_num at this ⊢
    linarith
  have hY : 16 * 27 ^ n ≤ 27 * countY n := by
    have h27 : (27 : ℤ) ^ n = 3 ^ n * 9 ^ n := by rw [← mul_pow]; norm_num
    have h3 : (3 : ℤ) ≤ 3 ^ n := by simpa using pow_le_pow_right₀ (show (1 : ℤ) ≤ 3 by norm_num) hn
    have h9 : (9 : ℤ) ≤ 9 ^ n := by simpa using pow_le_pow_right₀ (show (1 : ℤ) ≤ 9 by norm_num) hn
    rw [countY, h27]
    nlinarith [mul_le_mul (show (2 : ℤ) * 3 ^ n ≤ 3 * (3 ^ n - 1) by linarith)
      (show (8 : ℤ) * 9 ^ n ≤ 9 * (9 ^ n - 1) by linarith) (by positivity) (by linarith)]
  have h27pos : (0 : ℤ) < 27 ^ n := by positivity
  rw [hsplit]
  nlinarith

/-- **The Euler product of `Y`**: there are `b_n ≥ 0` with `Σ_{d∣n} d·b_d = N_n` for every `n ≥ 1`, so that
`Z(T) = Π_n (1 − T^n)^{−b_n}`. -/
theorem euler_product :
    ∃ b : ℕ → ℕ, ∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, ((d * b d : ℕ) : ℤ) = countY n := by
  refine ⟨fun n => (placesY n / n).toNat, ?_⟩
  have hb : ∀ n : ℕ, 0 < n → ((n * (placesY n / n).toNat : ℕ) : ℤ) = placesY n := fun n hn => by
    push_cast
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg (placesY_nonneg hn) (by positivity)),
      Int.mul_ediv_cancel' (dvd_placesY hn)]
  exact (sum_eq_iff_sum_smul_moebius_eq (f := fun n => ((n * (placesY n / n).toNat : ℕ) : ℤ))
    (g := countY)).2 fun n hn => by rw [hb n hn]; rfl

/-- **The kernel of `Y`'s counts is not positive-definite.** Its inverse zeros `9` and `3`, closed under
`α ↦ 27/ᾱ`, are not on the circle `|α| = √27`. -/
theorem not_posDef : ¬ WeilFF.PosDef (WeilFF.countKernel 27 2 fun d => (countY d : ℝ)) := by
  have hα : ∀ i, ![(9 : ℂ), 3] i ≠ 0 := by intro i; fin_cases i <;> norm_num
  have hσ : ∀ i, ![(9 : ℂ), 3] (Equiv.swap 0 1 i) = ((27 : ℝ) : ℂ) / conj (![(9 : ℂ), 3] i) := by
    intro i
    fin_cases i <;> norm_num [Equiv.swap_apply_left, Equiv.swap_apply_right, map_ofNat]
  have hN : ∀ d, 0 < d → (((countY d : ℝ)) : ℂ) = ((27 : ℝ) : ℂ) ^ d + 1 - ∑ i, ![(9 : ℂ), 3] i ^ d := by
    intro d _
    rw [countY_eq, Fin.sum_univ_two]
    push_cast
    simp
  have h := WeilFF.countKernel_posDef_iff (σ := Equiv.swap 0 1) (by norm_num : (0 : ℝ) < 27) hα hσ hN
  rw [Fintype.card_fin] at h
  rw [h]
  intro hall
  have h9 : (9 : ℝ) = Real.sqrt 27 := by simpa using hall 0
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 27 by norm_num)
  rw [← h9] at hsq
  norm_num at hsq

/-- **Every elliptic curve's kernel is positive-definite.** For `E` over `𝔽_q` of odd characteristic and extensions
`L_d` with `q^d` elements, the kernel of the counts `#E(L_d)` is positive-definite on `ℤ`: it is twice the normalised
traces of `ManinHasse.toeplitz_nonneg`, the Gram matrix of the Frobenius points of Manin's twist. -/
theorem posDef_elliptic {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]
    (hF : ringChar F ≠ 2) (L : ℕ → Type*) [∀ d, Field (L d)] [∀ d, Fintype (L d)] [∀ d, Algebra F (L d)]
    (hL : ∀ d, 0 < d → Fintype.card (L d) = Fintype.card F ^ d) :
    WeilFF.PosDef (WeilFF.countKernel (Fintype.card F) 2
      fun d => (Nat.card (W.baseChange (L d)).toAffine.Point : ℝ)) := by
  set c : ℤ → ℝ := fun d => 2 * ManinHasse.ctrace W L d.natAbs with hc
  have hk : WeilFF.countKernel (Fintype.card F) 2
      (fun d => (Nat.card (W.baseChange (L d)).toAffine.Point : ℝ)) = fun d => (c d : ℂ) := by
    funext d
    have hs : 0 < Real.sqrt (Fintype.card F) := Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
    have hs' : Real.sqrt (Fintype.card F) ^ d.natAbs ≠ 0 := pow_ne_zero _ hs.ne'
    simp only [WeilFF.countKernel, hc, ManinHasse.ctrace, Int.natAbs_eq_zero]
    split_ifs with h
    · norm_num
    · congr 1
      field_simp
  have hdist : ∀ i j : ℕ, ((i : ℤ) - j).natAbs = Nat.dist i j := fun i j => by
    rcases le_total i j with h | h
    · rw [Int.natAbs_natCast_sub_natCast_of_le h, Nat.dist_eq_sub_of_le h]
    · rw [Int.natAbs_natCast_sub_natCast_of_ge h, Nat.dist_eq_sub_of_le_right h]
  rw [hk]
  refine WeilFF.posDef_of_real (fun d => by simp only [hc, Int.natAbs_neg]) fun K y => ?_
  have h := ManinHasse.toeplitz_nonneg W hF L hL K y
  calc (0 : ℝ) ≤ 2 * ∑ i, ∑ j, y i * y j * ManinHasse.ctrace W L (Nat.dist i j) := by linarith
    _ = ∑ i, ∑ j, y i * y j * c (((i : ℕ) : ℤ) - (j : ℕ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc]
      simp only [hdist]
      ring

/-- **No elliptic curve over `𝔽_27` has `Y`'s counts**: none has `N_1 = 16` points, by Hasse's bound. -/
theorem card_ne_countY {F : Type*} [Field F] [Fintype F] (hF : Fintype.card F = 27) (W : WeierstrassCurve F)
    [W.IsElliptic] : (Nat.card W.toAffine.Point : ℤ) ≠ countY 1 := by
  have hchar : ringChar F ≠ 2 := by
    intro h2
    have h27 : ((27 : ℕ) : F) = 0 := by rw [← hF]; exact FiniteField.cast_card_eq_zero F
    rw [ringChar.spec, h2] at h27
    norm_num at h27
  intro hN
  have h := ManinHasse.abs_trace_le W hchar
  have h16 : (Nat.card W.toAffine.Point : ℝ) = 16 := by
    have : (Nat.card W.toAffine.Point : ℤ) = 16 := by rw [hN]; norm_num [countY]
    exact_mod_cast this
  rw [hF, h16] at h
  have hs : Real.sqrt 27 < 6 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  norm_num at h
  linarith

end PurityTest

#print axioms PurityTest.dvd_necklace
#print axioms PurityTest.card_Y
#print axioms PurityTest.zeta_functional_equation
#print axioms PurityTest.euler_product
#print axioms PurityTest.not_posDef
#print axioms PurityTest.posDef_elliptic
#print axioms PurityTest.card_ne_countY
