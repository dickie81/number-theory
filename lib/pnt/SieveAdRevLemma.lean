/-
# Role reversal: the term of three primes and the terms of its atoms' boxes

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. A box `[c3, c2, c1]` of three primes `p₁ > p₂ > p₃` that passes `SieveAd.revOK`
(`SieveAdRevDefs.lean`) has its numbers `n = p₁p₂p₃m` with `m` a prime `Q` or a product `q₂Q` of two primes, all at
least `p₃`. Write `r' = n/p₁`, the product of the atoms `p₂`, `p₃` and the primes of `m`.

* `Xe q e`: `x^{e/DEN}`, with its rules.
* `cofactor_cases`: a number `m ≥ 2` below `p³` with no prime factor below the prime `p` is a prime, or a product of
  two primes at least `p`.
* `famI_eq_sum_card`, `famJ_eq_sum_card`, `famPr_eq_sum_card`: the terms of a family as sums over `n` of the number
  of its tuples that count `n`.
* `rev_cover_pt`: **every tuple is reached.** For `n ∈ (N₁, N₂]` that no square of a prime at least
  `z = ⌈x^{l₃/DEN}⌉` divides, and a tuple of the box that counts `n`: the atoms, in order, are a tuple of one of
  five atoms' boxes under the condition, `r' | n`, `n` has no prime factor below `z`, and the tuple is
  `(n/r', p₂, p₃)` read off the atoms.
* `rev_cover`: so the term of the box, with weights `g ≥ 0`, is at most the sum of the terms at the level `z` of the
  five atoms' boxes under the condition, plus `(DEN + 1)³` times the weight of the `n` that such a square divides.

The file imports `SieveAdRevFam.lean`.
-/
import SieveAdRevFam

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

/-! ### A number with no small prime factor, below a cube -/

/-- A number `m ≥ 2` below `p³` with no prime factor below the prime `p` is a prime, or a product of two primes at
least `p`, the smaller first. -/
theorem cofactor_cases {p m : ℕ} (hm : 2 ≤ m) (hr : SieveTree.rough p m) (hlt : m < p ^ 3) :
    m.Prime ∨ ∃ q₂ Q : ℕ, q₂.Prime ∧ Q.Prime ∧ m = q₂ * Q ∧ p ≤ q₂ ∧ q₂ ≤ Q := by
  by_cases hmp : m.Prime
  · exact Or.inl hmp
  right
  have hq₂ := Nat.minFac_prime (show m ≠ 1 by omega)
  have hpq : p ≤ m.minFac := (SieveStops2.rough_iff_le_minFac hm).1 hr
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < m) hmp
  obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
  have hq0 : 0 < m.minFac := hq₂.pos
  have hm'ge : m.minFac ≤ m' := by
    have h1 : m.minFac * m.minFac ≤ m.minFac * m' := by
      rw [← hm', ← sq]
      exact hsq
    exact Nat.le_of_mul_le_mul_left h1 hq0
  have hm'2 : 2 ≤ m' := le_trans hq₂.two_le hm'ge
  have hmin' : m.minFac ≤ m'.minFac :=
    Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega)).two_le
      ((Nat.minFac_dvd m').trans (Dvd.intro_left m.minFac hm'.symm))
  have hm'p : m'.Prime := by
    by_contra hnp
    have h1 := Nat.minFac_sq_le_self (by omega : 0 < m') hnp
    have h2 : m.minFac ^ 2 ≤ m' := le_trans (Nat.pow_le_pow_left hmin' 2) h1
    have h3 : m.minFac ^ 3 ≤ m := by
      calc m.minFac ^ 3 = m.minFac * m.minFac ^ 2 := by ring
        _ ≤ m.minFac * m' := Nat.mul_le_mul_left _ h2
        _ = m := hm'.symm
    have h4 : p ^ 3 ≤ m.minFac ^ 3 := Nat.pow_le_pow_left hpq 3
    omega
  exact ⟨m.minFac, m', hq₂, hm'p, hm', hpq, hm'ge⟩

/-! ### Boxes of three and of four cells -/

theorem boxFn3 (a b c : Cell) : boxFn [a, b, c] 3 rfl = ![c, b, a] := by
  funext i
  fin_cases i <;> rfl

theorem boxFn4 (a b c d : Cell) : boxFn [a, b, c, d] 4 rfl = ![d, c, b, a] := by
  funext i
  fin_cases i <;> rfl

/-! ### The terms of a family, by the numbers -/

/-- The terms of a family: the sum over `n` of the weight of `n` times the number of the tuples that count it. -/
theorem famI_eq_sum_card (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) :
    famI g N₁ N₂ F = ∑ n ∈ Ioc N₁ N₂, g n *
      ((F.filter fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n).card : ℝ) := by
  unfold famI
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.mul_sum, Finset.sum_boole]

/-- The terms of a family at a floor: the sum over `n` of the weight of `n` times the number of the tuples that
count it. -/
theorem famJ_eq_sum_card (g : ℕ → ℝ) (N₁ N₂ z : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) :
    famJ g N₁ N₂ z F = ∑ n ∈ Ioc N₁ N₂, g n *
      ((F.filter fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n).card : ℝ) := by
  unfold famJ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.mul_sum, Finset.sum_boole]

/-- The numbers `K·∏rt` with `K` prime over a family: the sum over `n` of the weight of `n` times the number of the
tuples that count it. -/
theorem famPr_eq_sum_card (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) :
    famPr g N₁ N₂ F = ∑ n ∈ Ioc N₁ N₂, g n *
      ((F.filter fun rt => (∏ i, rt i) ∣ n ∧ (n / ∏ i, rt i).Prime).card : ℝ) := by
  unfold famPr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.mul_sum, Finset.sum_boole]

variable [Route]

/-! ### Powers of `x` by their exponents -/

/-- `x^{e/DEN}`. -/
noncomputable def Xe (q e : ℕ) : ℝ := xq q ^ ((e : ℝ) / DEN)

theorem Xe_pos {q : ℕ} (hx0 : 0 < xq q) (e : ℕ) : 0 < Xe q e := Real.rpow_pos_of_pos hx0 _

theorem Xe_add {q : ℕ} (hx0 : 0 < xq q) (a b : ℕ) : Xe q (a + b) = Xe q a * Xe q b := by
  unfold Xe
  rw [← Real.rpow_add hx0]
  congr 1
  push_cast
  ring

theorem Xe_mono {q : ℕ} (hx1 : 1 ≤ xq q) {a b : ℕ} (h : a ≤ b) : Xe q a ≤ Xe q b := pow_mono hx1 h

theorem Xe_DEN (q : ℕ) : Xe q DEN = xq q := by
  unfold Xe
  rw [div_self DEN_pos'.ne', Real.rpow_one]

theorem Xe_zero (q : ℕ) : Xe q 0 = 1 := by simp [Xe]

theorem one_le_Xe {q : ℕ} (hx1 : 1 ≤ xq q) (e : ℕ) : 1 ≤ Xe q e := by
  rw [← Xe_zero q]
  exact Xe_mono hx1 (Nat.zero_le e)

/-- At a large modulus: `x ≥ 3`, `x^{1/DEN} ≥ 3`, and for `n ∈ (N₁, N₂]`: `x < n < x^{(DEN+1)/DEN}`. -/
theorem big_n [RouteOK] {q : ℕ} (hq : Big q) :
    3 ≤ xq q ∧ 3 ≤ Xe q 1 ∧ ∀ n ∈ Ioc (N1 q) (N2 q), xq q < (n : ℝ) ∧ (n : ℝ) < Xe q (DEN + 1) := by
  obtain ⟨-, hx3, -, hN2, hy3⟩ := big_facts hq
  refine ⟨hx3, ?_, fun n hn => ?_⟩
  · unfold Xe
    rw [Nat.cast_one]
    exact hy3
  · rw [Finset.mem_Ioc] at hn
    refine ⟨Nat.lt_of_floor_lt hn.1, ?_⟩
    have h1 : (n : ℝ) ≤ N2 q := by exact_mod_cast hn.2
    have h2 : Xe q (DEN + 1) = xq q ^ (((DEN : ℝ) + 1) / DEN) := by
      unfold Xe
      push_cast
      rfl
    rw [h2]
    linarith

/-- The other factor of a number with a factor in a cell lies in the range of the condition: for `n ∈ (N₁, N₂]`
with `n = p·r` and `x^{l/DEN} ≤ p < x^{h/DEN}`, `0 < l ≤ h ≤ DEN`: `x^{(DEN−h)/DEN} < r ≤ x^{(DEN−l+1)/DEN}`. -/
theorem slab_of_mul [RouteOK] {q : ℕ} (hq : Big q) {c : Cell} (hc : 0 < c.1 ∧ c.1 ≤ c.2 ∧ c.2 ≤ DEN) {n p r : ℕ}
    (hn : n ∈ Ioc (N1 q) (N2 q)) (hnr : n = p * r) (hp : Xe q c.1 ≤ p ∧ (p : ℝ) < Xe q c.2) :
    Xe q (e1 c) < (r : ℝ) ∧ (r : ℝ) ≤ Xe q (e2 c) := by
  obtain ⟨hx3, -, hn'⟩ := big_n hq
  obtain ⟨hn1, hn2⟩ := hn' n hn
  have hx0 : 0 < xq q := by linarith
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (Xe_pos hx0 _) hp.1
  have hcast : (n : ℝ) = p * r := by exact_mod_cast hnr
  constructor
  · have h1 : Xe q (e1 c) * Xe q c.2 = xq q := by
      rw [← Xe_add hx0, ← Xe_DEN q]
      congr 1
      unfold e1
      omega
    have h2 : Xe q (e1 c) * p ≤ Xe q (e1 c) * Xe q c.2 := mul_le_mul_of_nonneg_left hp.2.le (Xe_pos hx0 _).le
    have h3 : Xe q (e1 c) * p < r * p := by rw [mul_comm (r : ℝ)]; linarith
    exact lt_of_mul_lt_mul_right h3 hp0.le
  · have h1 : Xe q (e2 c) * Xe q c.1 = Xe q (DEN + 1) := by
      rw [← Xe_add hx0]
      congr 1
      unfold e2
      omega
    have h2 : (r : ℝ) * Xe q c.1 ≤ r * p := mul_le_mul_of_nonneg_left hp.1 (Nat.cast_nonneg r)
    have h3 : (r : ℝ) * Xe q c.1 ≤ Xe q (e2 c) * Xe q c.1 := by rw [h1]; rw [mul_comm (r : ℝ)] at h2; linarith
    exact le_of_mul_le_mul_right h3 (Xe_pos hx0 _)

/-! ### Tuples of three and of four primes in a box under the condition -/

omit [Route] in
theorem maxN_cases (a b : ℕ) : maxN a b = a ∨ maxN a b = b := by
  unfold maxN
  cases Nat.ble a b <;> simp

theorem Xe_maxN_le {q : ℕ} {a b : ℕ} {v : ℝ} (ha : Xe q a ≤ v) (hb : Xe q b ≤ v) : Xe q (maxN a b) ≤ v := by
  rcases maxN_cases a b with h | h <;> rw [h] <;> assumption

/-- The facts of a tuple of a box of three cells. -/
theorem famB3_facts {q : ℕ} {k0 k1 k2 : Cell} {rt : Fin 3 → ℕ} (h : rt ∈ famB q (boxFn [k2, k1, k0] 3 rfl)) :
    (∀ i, rt i ≤ N2 q ∧ (rt i).Prime) ∧ rt 1 < rt 0 ∧ rt 2 < rt 1 ∧
      (Xe q k0.1 ≤ rt 0 ∧ (rt 0 : ℝ) < Xe q k0.2) ∧ (Xe q k1.1 ≤ rt 1 ∧ (rt 1 : ℝ) < Xe q k1.2) ∧
        (Xe q k2.1 ≤ rt 2 ∧ (rt 2 : ℝ) < Xe q k2.2) := by
  rw [boxFn3, mem_famB] at h
  obtain ⟨hp, hsa, hc⟩ := h
  exact ⟨hp, hsa (by decide), hsa (by decide), hc 0, hc 1, hc 2⟩

/-- A strictly decreasing triple of primes in three cells is a tuple of the box. -/
theorem mem_famB3 {q : ℕ} {k0 k1 k2 : Cell} {a0 a1 a2 : ℕ} (hp0 : a0 ≤ N2 q ∧ a0.Prime)
    (hp1 : a1 ≤ N2 q ∧ a1.Prime) (hp2 : a2 ≤ N2 q ∧ a2.Prime) (h01 : a1 < a0) (h12 : a2 < a1)
    (hc0 : Xe q k0.1 ≤ a0 ∧ (a0 : ℝ) < Xe q k0.2) (hc1 : Xe q k1.1 ≤ a1 ∧ (a1 : ℝ) < Xe q k1.2)
    (hc2 : Xe q k2.1 ≤ a2 ∧ (a2 : ℝ) < Xe q k2.2) :
    (![a0, a1, a2] : Fin 3 → ℕ) ∈ famB q (boxFn [k2, k1, k0] 3 rfl) := by
  rw [boxFn3, mem_famB]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hp0
    · exact hp1
    · exact hp2
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    fin_cases i
    · exact h01
    · exact h12
  · intro i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2

/-- A strictly decreasing triple of primes in three cells, with its product in the range, is a tuple of the box
under the condition. -/
theorem mem_famK3 {q e₁ e₂ : ℕ} {k0 k1 k2 : Cell} {a0 a1 a2 : ℕ} (hp0 : a0 ≤ N2 q ∧ a0.Prime)
    (hp1 : a1 ≤ N2 q ∧ a1.Prime) (hp2 : a2 ≤ N2 q ∧ a2.Prime) (h01 : a1 < a0) (h12 : a2 < a1)
    (hc0 : Xe q k0.1 ≤ a0 ∧ (a0 : ℝ) < Xe q k0.2) (hc1 : Xe q k1.1 ≤ a1 ∧ (a1 : ℝ) < Xe q k1.2)
    (hc2 : Xe q k2.1 ≤ a2 ∧ (a2 : ℝ) < Xe q k2.2)
    (hs : Xe q e₁ < ((a0 * a1 * a2 : ℕ) : ℝ) ∧ ((a0 * a1 * a2 : ℕ) : ℝ) ≤ Xe q e₂) :
    (![a0, a1, a2] : Fin 3 → ℕ) ∈ famK q e₁ e₂ 3 (boxFn [k2, k1, k0] 3 rfl) := by
  rw [famK, Finset.mem_filter, boxFn3, mem_famB]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · exact hp0
    · exact hp1
    · exact hp2
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    fin_cases i
    · exact h01
    · exact h12
  · intro i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  · unfold slabP
    rw [aprodR_full (le_refl _), Fin.prod_univ_three]
    push_cast at hs
    exact hs

/-- A strictly decreasing quadruple of primes in four cells, with its product in the range, is a tuple of the box
under the condition. -/
theorem mem_famK4 {q e₁ e₂ : ℕ} {k0 k1 k2 k3 : Cell} {a0 a1 a2 a3 : ℕ} (hp0 : a0 ≤ N2 q ∧ a0.Prime)
    (hp1 : a1 ≤ N2 q ∧ a1.Prime) (hp2 : a2 ≤ N2 q ∧ a2.Prime) (hp3 : a3 ≤ N2 q ∧ a3.Prime) (h01 : a1 < a0)
    (h12 : a2 < a1) (h23 : a3 < a2) (hc0 : Xe q k0.1 ≤ a0 ∧ (a0 : ℝ) < Xe q k0.2)
    (hc1 : Xe q k1.1 ≤ a1 ∧ (a1 : ℝ) < Xe q k1.2) (hc2 : Xe q k2.1 ≤ a2 ∧ (a2 : ℝ) < Xe q k2.2)
    (hc3 : Xe q k3.1 ≤ a3 ∧ (a3 : ℝ) < Xe q k3.2)
    (hs : Xe q e₁ < ((a0 * a1 * a2 * a3 : ℕ) : ℝ) ∧ ((a0 * a1 * a2 * a3 : ℕ) : ℝ) ≤ Xe q e₂) :
    (![a0, a1, a2, a3] : Fin 4 → ℕ) ∈ famK q e₁ e₂ 4 (boxFn [k3, k2, k1, k0] 4 rfl) := by
  rw [famK, Finset.mem_filter, boxFn4, mem_famB]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · exact hp0
    · exact hp1
    · exact hp2
    · exact hp3
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    fin_cases i
    · exact h01
    · exact h12
    · exact h23
  · intro i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
  · unfold slabP
    rw [aprodR_full (le_refl _), Fin.prod_univ_four]
    push_cast at hs
    exact hs

/-! ### The atoms' boxes of a reversal -/

/-- The least exponent of the cofactor: `DEN − (h₁ + h₂ + h₃)`. -/
def mlo (c1 c2 c3 : Cell) : ℕ := DEN - (c1.2 + c2.2 + c3.2)

/-- The cofactor's exponent is below `DEN + 1 − (l₁ + l₂ + l₃)`. -/
def mhi (c1 c2 c3 : Cell) : ℕ := DEN + 1 - (c1.1 + c2.1 + c3.1)

/-- The cell of a prime cofactor. -/
def iq1 (c1 c2 c3 : Cell) : Cell := (maxN (mlo c1 c2 c3) c3.1, mhi c1 c2 c3)

/-- The cell of the larger prime of a cofactor of two primes, the smaller in the cell `d`. -/
def iq2 (c1 c2 c3 d : Cell) : Cell := (maxN (mlo c1 c2 c3 - d.2) d.1, mhi c1 c2 c3 - d.1 + 1)

/-- The smaller prime of a cofactor of two primes has its exponent below `topQ`. -/
def topQ (c1 c2 c3 : Cell) : ℕ := (mhi c1 c2 c3 + 1) / 2

/-- **Every tuple is reached.** For a box `[c3, c2, c1]` that passes `revOK`, at a large modulus, `n ∈ (N₁, N₂]`
that no square of a prime at least `z = ⌈x^{l₃/DEN}⌉` divides, and a tuple `(p₁, p₂, p₃)` of the box that counts
`n`: `n` has no prime factor below `z`, and the atoms in order are a tuple `u` of one of the five atoms' boxes
under the condition, with `∏u | n` and `(n/∏u, p₂, p₃)` read off `u` the tuple. -/
theorem rev_cover_pt [RouteOK] {q : ℕ} (hq : Big q) {c1 c2 c3 : Cell} (hrev : revOK [c3, c2, c1] = true) {n : ℕ}
    (hn : n ∈ Ioc (N1 q) (N2 q)) (hgood : ∀ s : ℕ, s.Prime → ⌈Xe q c3.1⌉₊ ≤ s → ¬ s ^ 2 ∣ n) {rt : Fin 3 → ℕ}
    (hrt : rt ∈ famB q (boxFn [c3, c2, c1] 3 rfl)) (hd : (∏ i, rt i) ∣ n) (hr : SieveTree.rough (rt 2) n) :
    SieveTree.rough ⌈Xe q c3.1⌉₊ n ∧
    ((∃ u ∈ famK q (e1 c1) (e2 c1) 3 (boxFn [c3, c2, iq1 c1 c2 c3] 3 rfl),
        (∏ i, u i) ∣ n ∧ ![n / ∏ i, u i, u 1, u 2] = rt) ∨
      (∃ u ∈ famK q (e1 c1) (e2 c1) 3 (boxFn [c3, iq1 c1 c2 c3, c2] 3 rfl),
        (∏ i, u i) ∣ n ∧ ![n / ∏ i, u i, u 0, u 2] = rt) ∨
      (∃ u ∈ famK q (e1 c1) (e2 c1) 4
          (boxFn [c3, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3), c2] 4 rfl),
        (∏ i, u i) ∣ n ∧ ![n / ∏ i, u i, u 0, u 3] = rt) ∨
      (∃ u ∈ famK q (e1 c1) (e2 c1) 4
          (boxFn [c3, (c3.1, topQ c1 c2 c3), c2, iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl),
        (∏ i, u i) ∣ n ∧ ![n / ∏ i, u i, u 1, u 3] = rt) ∨
      (∃ u ∈ famK q (e1 c1) (e2 c1) 4
          (boxFn [c3, c2, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl),
        (∏ i, u i) ∣ n ∧ ![n / ∏ i, u i, u 2, u 3] = rt)) := by
  obtain ⟨hx3, hX1, hn'⟩ := big_n hq
  obtain ⟨hn1, hn2⟩ := hn' n hn
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  obtain ⟨hp, h10, h21, hc0, hc1, hc2⟩ := famB3_facts hrt
  simp only [revOK, Bool.and_eq_true, Nat.ble_eq] at hrev
  obtain ⟨⟨⟨⟨hcells, hb⟩, hsum⟩, hcube⟩, h31⟩ := hrev
  have hcl := (cellsOK_iff _).1 hcells
  have hk3 := hcl c3 (by simp)
  have hk2 := hcl c2 (by simp)
  have hk1 := hcl c1 (by simp)
  obtain ⟨p₁, hp₁⟩ : ∃ p₁, rt 0 = p₁ := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂⟩ : ∃ p₂, rt 1 = p₂ := ⟨_, rfl⟩
  obtain ⟨p₃, hp₃⟩ : ∃ p₃, rt 2 = p₃ := ⟨_, rfl⟩
  have hP1 := hp 0
  have hP2 := hp 1
  have hP3 := hp 2
  rw [hp₁] at hP1 hc0 h10
  rw [hp₂] at hP2 hc1 h10 h21
  rw [hp₃] at hP3 hc2 h21 hr
  have hrt_eq : rt = ![p₁, p₂, p₃] := by
    funext i
    fin_cases i
    · exact hp₁
    · exact hp₂
    · exact hp₃
  have hprod : ∏ i, rt i = p₁ * p₂ * p₃ := by rw [Fin.prod_univ_three, hp₁, hp₂, hp₃]
  have hn0 : 0 < n := by have := (Finset.mem_Ioc.1 hn).1; omega
  have hnN : n ≤ N2 q := (Finset.mem_Ioc.1 hn).2
  have hp1pos : (0 : ℝ) < p₁ := by exact_mod_cast hP1.2.pos
  have hp2pos : (0 : ℝ) < p₂ := by exact_mod_cast hP2.2.pos
  have hp3pos : (0 : ℝ) < p₃ := by exact_mod_cast hP3.2.pos
  -- the floor
  obtain ⟨z, hz⟩ : ∃ z, z = ⌈Xe q c3.1⌉₊ := ⟨_, rfl⟩
  rw [← hz] at hgood ⊢
  have hzp3 : z ≤ p₃ := by rw [hz]; exact Nat.ceil_le.2 hc2.1
  refine ⟨SieveTree.rough_mono hzp3 hr, ?_⟩
  have hsq : ∀ s : ℕ, s.Prime → p₃ ≤ s → ¬ s ^ 2 ∣ n := fun s hs h => hgood s hs (hzp3.trans h)
  -- the cofactor
  rw [hprod] at hd
  obtain ⟨m, hm⟩ := hd
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; omega
    · exact h
  have hPhi : ((p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ Xe q c1.2 * Xe q c2.2 * Xe q c3.2 := by
    push_cast
    exact mul_le_mul (mul_le_mul hc0.2.le hc1.2.le hp2pos.le (Xe_pos hx0 _).le) hc2.2.le hp3pos.le
      (mul_nonneg (Xe_pos hx0 _).le (Xe_pos hx0 _).le)
  have hPlo : Xe q c1.1 * Xe q c2.1 * Xe q c3.1 ≤ ((p₁ * p₂ * p₃ : ℕ) : ℝ) := by
    push_cast
    exact mul_le_mul (mul_le_mul hc0.1 hc1.1 (Xe_pos hx0 _).le hp1pos.le) hc2.1 (Xe_pos hx0 _).le
      (mul_nonneg hp1pos.le hp2pos.le)
  have hP0 : (0 : ℝ) < ((p₁ * p₂ * p₃ : ℕ) : ℝ) := by push_cast; positivity
  have hncast : (n : ℝ) = ((p₁ * p₂ * p₃ : ℕ) : ℝ) * m := by exact_mod_cast hm
  have hmlo : Xe q (mlo c1 c2 c3) < m := by
    have e : Xe q (mlo c1 c2 c3) * (Xe q c1.2 * Xe q c2.2 * Xe q c3.2) = xq q := by
      rw [← Xe_add hx0, ← Xe_add hx0, ← Xe_add hx0, ← Xe_DEN q]
      congr 1
      unfold mlo
      omega
    have h1 : Xe q (mlo c1 c2 c3) * ((p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ xq q := by
      rw [← e]; exact mul_le_mul_of_nonneg_left hPhi (Xe_pos hx0 _).le
    have h2 : Xe q (mlo c1 c2 c3) * ((p₁ * p₂ * p₃ : ℕ) : ℝ) < (m : ℝ) * ((p₁ * p₂ * p₃ : ℕ) : ℝ) := by
      rw [mul_comm (m : ℝ)]; linarith
    exact lt_of_mul_lt_mul_right h2 hP0.le
  have hmhi : (m : ℝ) < Xe q (mhi c1 c2 c3) := by
    have e : Xe q (mhi c1 c2 c3) * (Xe q c1.1 * Xe q c2.1 * Xe q c3.1) = Xe q (DEN + 1) := by
      rw [← Xe_add hx0, ← Xe_add hx0, ← Xe_add hx0]
      congr 1
      unfold mhi
      omega
    have h1 : (m : ℝ) * (Xe q c1.1 * Xe q c2.1 * Xe q c3.1) ≤ m * ((p₁ * p₂ * p₃ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hPlo (Nat.cast_nonneg m)
    have h2 : (m : ℝ) * (Xe q c1.1 * Xe q c2.1 * Xe q c3.1) <
        Xe q (mhi c1 c2 c3) * (Xe q c1.1 * Xe q c2.1 * Xe q c3.1) := by
      rw [e]; rw [mul_comm (m : ℝ) ((p₁ * p₂ * p₃ : ℕ) : ℝ)] at h1; linarith
    exact lt_of_mul_lt_mul_right h2
      (mul_nonneg (mul_nonneg (Xe_pos hx0 _).le (Xe_pos hx0 _).le) (Xe_pos hx0 _).le)
  have hm2 : 2 ≤ m := by
    have h1 : (1 : ℝ) < m := lt_of_le_of_lt (one_le_Xe hx1 _) hmlo
    have h2 : 1 < m := by exact_mod_cast h1
    omega
  have hmn : m ∣ n := Dvd.intro_left _ hm.symm
  have hroughm : SieveTree.rough p₃ m := fun p hpl hpp hpd => hr p hpl hpp (hpd.trans hmn)
  have hcubeN : m < p₃ ^ 3 := by
    have h1 : Xe q (mhi c1 c2 c3) ≤ Xe q (c3.1 + c3.1 + c3.1) := Xe_mono hx1 (by unfold mhi; omega)
    have h2 : Xe q (c3.1 + c3.1 + c3.1) = Xe q c3.1 ^ 3 := by rw [Xe_add hx0, Xe_add hx0]; ring
    have h3 : Xe q c3.1 ^ 3 ≤ (p₃ : ℝ) ^ 3 := pow_le_pow_left₀ (Xe_pos hx0 _).le hc2.1 3
    have h4 : (m : ℝ) < ((p₃ ^ 3 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h4
  -- the atoms' product lies in the range
  have hnr : n = p₁ * (p₂ * p₃ * m) := by rw [hm]; ring
  have hslab := slab_of_mul hq ⟨hk1.1, hk1.2.le, by omega⟩ hn hnr hc0
  have hle : ∀ p : ℕ, p ∣ n → p ≤ N2 q := fun p hpd => (Nat.le_of_dvd hn0 hpd).trans hnN
  have hp1n : 0 < p₁ := hP1.2.pos
  have hp2n : 0 < p₂ := hP2.2.pos
  have hp3n : 0 < p₃ := hP3.2.pos
  rcases cofactor_cases hm2 hroughm hcubeN with hmp | ⟨q₂, Q, hq₂, hQ, hmq, hpq, hqQ⟩
  · -- a prime cofactor
    have hp3m : p₃ ≤ m := by
      have := (SieveStops2.rough_iff_le_minFac hm2).1 hroughm
      rwa [Nat.Prime.minFac_eq hmp] at this
    have hne3 : m ≠ p₃ := fun h => hsq p₃ hP3.2 le_rfl ⟨p₁ * p₂, by rw [hm, h]; ring⟩
    have hne2 : m ≠ p₂ := fun h => hsq p₂ hP2.2 h21.le ⟨p₁ * p₃, by rw [hm, h]; ring⟩
    have hp3m' : p₃ < m := lt_of_le_of_ne hp3m (Ne.symm hne3)
    have hmN : m ≤ N2 q ∧ m.Prime := ⟨hle m hmn, hmp⟩
    have hcQ : Xe q (iq1 c1 c2 c3).1 ≤ m ∧ (m : ℝ) < Xe q (iq1 c1 c2 c3).2 := by
      refine ⟨Xe_maxN_le hmlo.le (hc2.1.trans ?_), hmhi⟩
      exact_mod_cast hp3m
    rcases lt_or_gt_of_ne hne2 with hlt | hgt
    · -- `p₃ < m < p₂`
      right; left
      refine ⟨![p₂, m, p₃], mem_famK3 hP2 hmN hP3 hlt hp3m' hc1 hcQ hc2 ?_, ?_, ?_⟩
      · rw [show p₂ * m * p₃ = p₂ * p₃ * m by ring]; exact hslab
      · rw [Fin.prod_univ_three]
        exact ⟨p₁, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]; rw [hm]; ring⟩
      · rw [hrt_eq, Fin.prod_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons]
        rw [Nat.div_eq_of_eq_mul_left (by positivity) (show n = p₁ * (p₂ * m * p₃) by rw [hm]; ring)]
    · -- `p₂ < m`
      left
      refine ⟨![m, p₂, p₃], mem_famK3 hmN hP2 hP3 hgt h21 hcQ hc1 hc2 ?_, ?_, ?_⟩
      · rw [show m * p₂ * p₃ = p₂ * p₃ * m by ring]; exact hslab
      · rw [Fin.prod_univ_three]
        exact ⟨p₁, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]; rw [hm]; ring⟩
      · rw [hrt_eq, Fin.prod_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons]
        rw [Nat.div_eq_of_eq_mul_left (by positivity) (show n = p₁ * (m * p₂ * p₃) by rw [hm]; ring)]
  · -- a cofactor of two primes
    have hq2n : q₂ ∣ n := (Dvd.intro _ hmq.symm).trans hmn
    have hQn : Q ∣ n := (Dvd.intro_left _ hmq.symm).trans hmn
    have hne3 : q₂ ≠ p₃ := fun h => hsq p₃ hP3.2 le_rfl ⟨p₁ * p₂ * Q, by rw [hm, hmq, h]; ring⟩
    have hp3q : p₃ < q₂ := lt_of_le_of_ne hpq (Ne.symm hne3)
    have hneQ : q₂ ≠ Q := fun h => hsq q₂ hq₂ hpq ⟨p₁ * p₂ * p₃, by rw [hm, hmq, ← h]; ring⟩
    have hqQ' : q₂ < Q := lt_of_le_of_ne hqQ hneQ
    have hne2 : q₂ ≠ p₂ := fun h => hsq p₂ hP2.2 h21.le ⟨p₁ * p₃ * Q, by rw [hm, hmq, h]; ring⟩
    have hneQ2 : Q ≠ p₂ := fun h => hsq p₂ hP2.2 h21.le ⟨p₁ * p₃ * q₂, by rw [hm, hmq, h]; ring⟩
    have hq2N : q₂ ≤ N2 q ∧ q₂.Prime := ⟨hle q₂ hq2n, hq₂⟩
    have hQN : Q ≤ N2 q ∧ Q.Prime := ⟨hle Q hQn, hQ⟩
    have hq2n : 0 < q₂ := hq₂.pos
    have hQn0 : 0 < Q := hQ.pos
    have hq2pos : (0 : ℝ) < q₂ := by exact_mod_cast hq₂.pos
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ.pos
    have hmcast : (m : ℝ) = q₂ * Q := by exact_mod_cast hmq
    have hq2lo : Xe q c3.1 ≤ q₂ := hc2.1.trans (by exact_mod_cast hp3q.le)
    have hq2top : (q₂ : ℝ) < Xe q (topQ c1 c2 c3) := by
      have h1 : (q₂ : ℝ) ^ 2 ≤ q₂ * Q := by
        rw [sq]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqQ) hq2pos.le
      have h2 : Xe q (mhi c1 c2 c3) ≤ Xe q (topQ c1 c2 c3 + topQ c1 c2 c3) :=
        Xe_mono hx1 (by unfold topQ; omega)
      have h3 : Xe q (topQ c1 c2 c3 + topQ c1 c2 c3) = Xe q (topQ c1 c2 c3) ^ 2 := by rw [Xe_add hx0, sq]
      have h4 : (q₂ : ℝ) ^ 2 < Xe q (topQ c1 c2 c3) ^ 2 := by linarith
      exact lt_of_pow_lt_pow_left₀ 2 (Xe_pos hx0 _).le h4
    have hcq2 : Xe q ((c3.1, topQ c1 c2 c3) : Cell).1 ≤ q₂ ∧ (q₂ : ℝ) < Xe q ((c3.1, topQ c1 c2 c3) : Cell).2 :=
      ⟨hq2lo, hq2top⟩
    have hQlo1 : Xe q c3.1 ≤ Q := hq2lo.trans (by exact_mod_cast hqQ)
    have hQlo2 : Xe q (mlo c1 c2 c3 - topQ c1 c2 c3) ≤ Q := by
      by_cases ht : topQ c1 c2 c3 ≤ mlo c1 c2 c3
      · have e : Xe q (mlo c1 c2 c3 - topQ c1 c2 c3) * Xe q (topQ c1 c2 c3) = Xe q (mlo c1 c2 c3) := by
          rw [← Xe_add hx0, Nat.sub_add_cancel ht]
        have h1 : Xe q (mlo c1 c2 c3 - topQ c1 c2 c3) * Xe q (topQ c1 c2 c3) < Q * Xe q (topQ c1 c2 c3) := by
          rw [e]
          have : (q₂ : ℝ) * Q ≤ Q * Xe q (topQ c1 c2 c3) := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left hq2top.le hQpos.le
          linarith
        exact (lt_of_mul_lt_mul_right h1 (Xe_pos hx0 _).le).le
      · rw [show mlo c1 c2 c3 - topQ c1 c2 c3 = 0 by omega, Xe_zero]
        exact_mod_cast hQ.one_lt.le
    have hQhi : (Q : ℝ) < Xe q (mhi c1 c2 c3 - c3.1 + 1) := by
      have h1 : (Q : ℝ) * Xe q c3.1 ≤ m := by
        rw [hmcast, mul_comm (q₂ : ℝ)]; exact mul_le_mul_of_nonneg_left hq2lo hQpos.le
      by_cases ht : c3.1 ≤ mhi c1 c2 c3
      · have e : Xe q (mhi c1 c2 c3 - c3.1) * Xe q c3.1 = Xe q (mhi c1 c2 c3) := by
          rw [← Xe_add hx0, Nat.sub_add_cancel ht]
        have h2 : (Q : ℝ) * Xe q c3.1 < Xe q (mhi c1 c2 c3 - c3.1) * Xe q c3.1 := by rw [e]; linarith
        exact (lt_of_mul_lt_mul_right h2 (Xe_pos hx0 _).le).trans_le (Xe_mono hx1 (Nat.le_succ _))
      · exfalso
        have h2 : Xe q (mhi c1 c2 c3) ≤ Xe q c3.1 := Xe_mono hx1 (by omega)
        have h3 : (Q : ℝ) * Xe q c3.1 < 1 * Xe q c3.1 := by linarith
        have h4 : (Q : ℝ) < 1 := lt_of_mul_lt_mul_right h3 (Xe_pos hx0 _).le
        have h5 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ.one_lt.le
        linarith
    have hcQ : Xe q (iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)).1 ≤ Q ∧
        (Q : ℝ) < Xe q (iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)).2 := ⟨Xe_maxN_le hQlo2 hQlo1, hQhi⟩
    have hslab' : Xe q (e1 c1) < ((p₂ * p₃ * (q₂ * Q) : ℕ) : ℝ) ∧ ((p₂ * p₃ * (q₂ * Q) : ℕ) : ℝ) ≤ Xe q (e2 c1) := by
      rw [← hmq]; exact hslab
    rcases lt_or_gt_of_ne hneQ2 with hlt | hgt
    · -- `p₃ < q₂ < Q < p₂`
      right; right; left
      refine ⟨![p₂, Q, q₂, p₃], mem_famK4 hP2 hQN hq2N hP3 hlt hqQ' hp3q hc1 hcQ hcq2 hc2 ?_, ?_, ?_⟩
      · rw [show p₂ * Q * q₂ * p₃ = p₂ * p₃ * (q₂ * Q) by ring]; exact hslab'
      · rw [Fin.prod_univ_four]
        exact ⟨p₁, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]; rw [hm, hmq]; ring⟩
      · rw [hrt_eq, Fin.prod_univ_four]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
          Matrix.head_cons, Matrix.tail_cons]
        rw [Nat.div_eq_of_eq_mul_left (by positivity) (show n = p₁ * (p₂ * Q * q₂ * p₃) by rw [hm, hmq]; ring)]
    · rcases lt_or_gt_of_ne hne2 with hlt2 | hgt2
      · -- `p₃ < q₂ < p₂ < Q`
        right; right; right; left
        refine ⟨![Q, p₂, q₂, p₃], mem_famK4 hQN hP2 hq2N hP3 hgt hlt2 hp3q hcQ hc1 hcq2 hc2 ?_, ?_, ?_⟩
        · rw [show Q * p₂ * q₂ * p₃ = p₂ * p₃ * (q₂ * Q) by ring]; exact hslab'
        · rw [Fin.prod_univ_four]
          exact ⟨p₁, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]; rw [hm, hmq]; ring⟩
        · rw [hrt_eq, Fin.prod_univ_four]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
            Matrix.head_cons, Matrix.tail_cons]
          rw [Nat.div_eq_of_eq_mul_left (by positivity) (show n = p₁ * (Q * p₂ * q₂ * p₃) by rw [hm, hmq]; ring)]
      · -- `p₃ < p₂ < q₂ < Q`
        right; right; right; right
        refine ⟨![Q, q₂, p₂, p₃], mem_famK4 hQN hq2N hP2 hP3 hqQ' hgt2 h21 hcQ hcq2 hc1 hc2 ?_, ?_, ?_⟩
        · rw [show Q * q₂ * p₂ * p₃ = p₂ * p₃ * (q₂ * Q) by ring]; exact hslab'
        · rw [Fin.prod_univ_four]
          exact ⟨p₁, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]; rw [hm, hmq]; ring⟩
        · rw [hrt_eq, Fin.prod_univ_four]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
            Matrix.head_cons, Matrix.tail_cons]
          rw [Nat.div_eq_of_eq_mul_left (by positivity) (show n = p₁ * (Q * q₂ * p₂ * p₃) by rw [hm, hmq]; ring)]

theorem Xe_pow {q : ℕ} (hx0 : 0 < xq q) (k : ℕ) : Xe q 1 ^ k = Xe q k := by
  induction k with
  | zero => rw [pow_zero, Xe_zero]
  | succ k ih => rw [pow_succ, ih, ← Xe_add hx0]

/-- **The term of the box is at most the terms of its atoms' boxes.** For a box `[c3, c2, c1]` that passes `revOK`,
at a large modulus, and weights `g ≥ 0`: the term of the box is at most the sum of the terms at the level
`z = ⌈x^{l₃/DEN}⌉` of the five atoms' boxes under the condition, plus `(DEN + 1)³` times the weight of the `n` that
the square of a prime at least `z` divides. -/
theorem rev_cover [RouteOK] {q : ℕ} (hq : Big q) {c1 c2 c3 : Cell} (hrev : revOK [c3, c2, c1] = true) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) :
    famI g (N1 q) (N2 q) (famB q (boxFn [c3, c2, c1] 3 rfl)) ≤
      famJ g (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 3 (boxFn [c3, c2, iq1 c1 c2 c3] 3 rfl)) +
      famJ g (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 3 (boxFn [c3, iq1 c1 c2 c3, c2] 3 rfl)) +
      famJ g (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 4
        (boxFn [c3, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3), c2] 4 rfl)) +
      famJ g (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 4
        (boxFn [c3, (c3.1, topQ c1 c2 c3), c2, iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl)) +
      famJ g (N1 q) (N2 q) ⌈Xe q c3.1⌉₊ (famK q (e1 c1) (e2 c1) 4
        (boxFn [c3, c2, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl)) +
      ((DEN + 1 : ℕ) : ℝ) ^ 3 * ∑ n ∈ (Ioc (N1 q) (N2 q)).filter
        (fun n => ∃ s : ℕ, s.Prime ∧ ⌈Xe q c3.1⌉₊ ≤ s ∧ s ^ 2 ∣ n), g n := by
  obtain ⟨hx3, hX1, hn'⟩ := big_n hq
  have hx0 : 0 < xq q := by linarith
  have hx1 : 1 ≤ xq q := by linarith
  have hcl : ∀ c ∈ [c3, c2, c1], 0 < c.1 ∧ c.1 < c.2 := by
    simp only [revOK, Bool.and_eq_true, Nat.ble_eq] at hrev
    exact (cellsOK_iff _).1 hrev.1.1.1.1
  rw [famI_eq_sum_card, famJ_eq_sum_card, famJ_eq_sum_card, famJ_eq_sum_card, famJ_eq_sum_card, famJ_eq_sum_card,
    Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n hn => ?_
  have hgn := hg n
  have hn0 : 0 < n := by have := (Finset.mem_Ioc.1 hn).1; omega
  obtain ⟨z, hz⟩ : ∃ z, z = ⌈Xe q c3.1⌉₊ := ⟨_, rfl⟩
  rw [← hz]
  obtain ⟨C, hC⟩ : ∃ C, C = (famB q (boxFn [c3, c2, c1] 3 rfl)).filter
      (fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last 2)) n) := ⟨_, rfl⟩
  rw [← hC]
  by_cases hbad : ∃ s : ℕ, s.Prime ∧ z ≤ s ∧ s ^ 2 ∣ n
  · -- a number with a square factor: few tuples
    simp only [hbad, ↓reduceIte]
    have hcard : C.card ≤ (DEN + 1) ^ 3 := by
      refine card_tuples_dvd_le C (P := Xe q 1) hn0 (by linarith) ?_ ?_
      · rw [Xe_pow hx0]
        exact (hn' n hn).2
      · intro rt hrt i
        rw [hC, Finset.mem_filter] at hrt
        obtain ⟨hp, -, hc⟩ := mem_famB.1 hrt.1
        refine ⟨(hp i).2, ?_, (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hrt.2.1⟩
        have h1 : 1 ≤ (boxFn [c3, c2, c1] 3 rfl i).1 := (hcl _ (boxFn_mem [c3, c2, c1] 3 rfl i)).1
        exact (Xe_mono hx1 h1).trans (hc i).1
    have h1 : g n * (C.card : ℝ) ≤ ((DEN + 1 : ℕ) : ℝ) ^ 3 * g n := by
      have : (C.card : ℝ) ≤ ((DEN + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast hcard
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right this hgn
    have h2 : ∀ c : ℕ, 0 ≤ g n * (c : ℝ) := fun c => mul_nonneg hgn (Nat.cast_nonneg c)
    linarith [h2 ((famK q (e1 c1) (e2 c1) 3 (boxFn [c3, c2, iq1 c1 c2 c3] 3 rfl)).filter
        fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n).card,
      h2 ((famK q (e1 c1) (e2 c1) 3 (boxFn [c3, iq1 c1 c2 c3, c2] 3 rfl)).filter
        fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n).card,
      h2 ((famK q (e1 c1) (e2 c1) 4 (boxFn [c3, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3), c2] 4
        rfl)).filter fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n).card,
      h2 ((famK q (e1 c1) (e2 c1) 4 (boxFn [c3, (c3.1, topQ c1 c2 c3), c2, iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4
        rfl)).filter fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n).card,
      h2 ((famK q (e1 c1) (e2 c1) 4 (boxFn [c3, c2, (c3.1, topQ c1 c2 c3), iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4
        rfl)).filter fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n).card]
  · -- no square factor: every tuple is reached
    simp only [hbad, ↓reduceIte, mul_zero, add_zero]
    rw [← mul_add, ← mul_add, ← mul_add, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hgn
    have hgood : ∀ s : ℕ, s.Prime → ⌈Xe q c3.1⌉₊ ≤ s → ¬ s ^ 2 ∣ n := fun s hs hzs hd =>
      hbad ⟨s, hs, by rw [hz]; exact hzs, hd⟩
    obtain ⟨D1, hD1⟩ : ∃ D1, D1 = ((famK q (e1 c1) (e2 c1) 3 (boxFn [c3, c2, iq1 c1 c2 c3] 3 rfl)).filter
        fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n) := ⟨_, rfl⟩
    obtain ⟨D2, hD2⟩ : ∃ D2, D2 = ((famK q (e1 c1) (e2 c1) 3 (boxFn [c3, iq1 c1 c2 c3, c2] 3 rfl)).filter
        fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n) := ⟨_, rfl⟩
    obtain ⟨D3, hD3⟩ : ∃ D3, D3 = ((famK q (e1 c1) (e2 c1) 4 (boxFn [c3, (c3.1, topQ c1 c2 c3),
        iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3), c2] 4 rfl)).filter
          fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n) := ⟨_, rfl⟩
    obtain ⟨D4, hD4⟩ : ∃ D4, D4 = ((famK q (e1 c1) (e2 c1) 4 (boxFn [c3, (c3.1, topQ c1 c2 c3), c2,
        iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl)).filter
          fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n) := ⟨_, rfl⟩
    obtain ⟨D5, hD5⟩ : ∃ D5, D5 = ((famK q (e1 c1) (e2 c1) 4 (boxFn [c3, c2, (c3.1, topQ c1 c2 c3),
        iq2 c1 c2 c3 (c3.1, topQ c1 c2 c3)] 4 rfl)).filter
          fun rt => (∏ i, rt i) ∣ n ∧ SieveTree.rough z n) := ⟨_, rfl⟩
    rw [← hD1, ← hD2, ← hD3, ← hD4, ← hD5]
    have hsub : C ⊆ D1.image (fun u => ![n / ∏ i, u i, u 1, u 2]) ∪ D2.image (fun u => ![n / ∏ i, u i, u 0, u 2]) ∪
        D3.image (fun u => ![n / ∏ i, u i, u 0, u 3]) ∪ D4.image (fun u => ![n / ∏ i, u i, u 1, u 3]) ∪
          D5.image (fun u => ![n / ∏ i, u i, u 2, u 3]) := by
      intro rt hrt
      rw [hC, Finset.mem_filter] at hrt
      obtain ⟨hrz, hcases⟩ := rev_cover_pt hq hrev hn hgood hrt.1 hrt.2.1 hrt.2.2
      rw [← hz] at hrz
      simp only [Finset.mem_union, Finset.mem_image]
      rcases hcases with ⟨u, hu, hd, he⟩ | ⟨u, hu, hd, he⟩ | ⟨u, hu, hd, he⟩ | ⟨u, hu, hd, he⟩ | ⟨u, hu, hd, he⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨u, by rw [hD1]; exact Finset.mem_filter.2 ⟨hu, hd, hrz⟩, he⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨u, by rw [hD2]; exact Finset.mem_filter.2 ⟨hu, hd, hrz⟩, he⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨u, by rw [hD3]; exact Finset.mem_filter.2 ⟨hu, hd, hrz⟩, he⟩))
      · exact Or.inl (Or.inr ⟨u, by rw [hD4]; exact Finset.mem_filter.2 ⟨hu, hd, hrz⟩, he⟩)
      · exact Or.inr ⟨u, by rw [hD5]; exact Finset.mem_filter.2 ⟨hu, hd, hrz⟩, he⟩
    have hcard : C.card ≤ D1.card + D2.card + D3.card + D4.card + D5.card := by
      refine (Finset.card_le_card hsub).trans ?_
      refine (Finset.card_union_le _ _).trans (add_le_add ?_ Finset.card_image_le)
      refine (Finset.card_union_le _ _).trans (add_le_add ?_ Finset.card_image_le)
      refine (Finset.card_union_le _ _).trans (add_le_add ?_ Finset.card_image_le)
      exact (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
    exact_mod_cast hcard

end SieveAd

#print axioms SieveAd.rev_cover
