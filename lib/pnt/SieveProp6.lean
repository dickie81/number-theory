/-
# Proposition 6, Harman's fundamental theorem in the form used

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement (`prop6`). Let `L`, `w₁` and `w₂` be a route's parameters (`SieveRoute.Route`) with `RouteOK`, and
assume its Type II estimate (`hII : SieveRoute.TypeIIAt`). Fix `j`, `J₀`, `Λ₁ ≥ 0`, exponents `a₀ > 0` and `b₀` with
`a₀ + b₀ < (1 − w₁)L` and `(1 − w₂)L < b₀ < L − 1`, and `η > 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a
unit `a` mod `q`: let `rt` run over the `j`-tuples of primes up to `⌊2q^L⌋` that satisfy at most `J₀` comparisons `Ω`
(taken at `m = 0`, with `m`-parts `c(0)` at most `Λ₁ log q`) forcing every `rt_i ≥ z₀ = ⌈q^{a₀}⌉` and
`∏rt ≤ X' = ⌊q^{b₀}⌋`. Then `Σ_{rt}(S(A_r, z₀) − S(B_r, z₀)/φ(q))`, `r = ∏rt`, is at most
`ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)` in absolute value, where `A` is the `n ∈ (⌊q^L⌋, ⌊2q^L⌋]` with `n ≡ a` and `B` those
prime to `q`.

It is built with one tree at the threshold `X'` for every `r ≤ X'`. The conditions on `a₀` and `b₀` say that the
stops' cofactors fall in the lower window (`a₀ + b₀ < (1 − w₁)L`, `(1 − w₂)L < b₀`: a stop lies in `(X', X'z₀)`) and
that the leaves' remainder is small (`b₀ < L − 1`).

The proof:

* The tree (`SieveDiff.tree_weighted`) runs from `z₀` down to `w = ⌈q^{ε_w}⌉`, `ε_w = c/(2k + 4)`,
  `c = (L − 1 − b₀)/4`, at the threshold `X'`. `SieveStops2.stops2_bound` bounds its stops (`window_lo`,
  `window_hi`).
* `leaf_bound`: at a leaf `d = r∏P ≤ X'`, `SieveLeaf.leaf_A` and `leaf_B` with the ranges' levels `k + 2j`
  (`Jw_spec`, `SieveLeaf.leaf_gap`) give `2ζ(k)·YV + 2·rem`, `Y = (N₂ − N₁)/(dq)`, and `V ≤ q/(φ(q) log w)`
  (`SieveLeaf.prod_T_le`, Mertens' product bound in its elementary form).
* `leaves_sum_le`: with `N₂ − N₁ ≤ X + 1`, `X = q^L`, the leaves total at most
  `(2ζ(k)(X + 1)/(φ(q) log w) + 2·rem·X')·Σ_{rt} Σ_P 1/(r∏P)`, and the double sum is `Σ_{rt} 1/r ∏_{w ≤ p < z₀} (1 + 1/p)`
  (`sum_leaves_inv`), bounded by `sum_RT_inv_le` and `SieveRough.evLe_sum_inv`.
* `exists_k`, `main_coef`, `main_term`: an even `k` with `(2k + 4)²ζ(k)` small puts the main terms below
  `ηq^L/(φ(q) log q)`; `rem_le`, `rem_term`: the remainders total at most `q^{L−c}/φ(q)`.

`L`, `w₁` and `w₂` are a route's parameters and the Type II estimate is a hypothesis (`hII`).

The file imports `SieveStops2.lean`.
-/
import SieveStops2

open Real Finset SieveFamily SieveTree SieveCmp SieveBrun SieveLeaf SieveRanges SieveRoute

namespace SieveProp6

/-! ### The fundamental lemma's remainder -/

theorem geom_nat_le {n : ℕ} (hn : 2 ≤ n) (m : ℕ) : ∑ i ∈ Finset.range (m + 1), n ^ i ≤ 2 * n ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have : 2 * n ^ m ≤ n ^ (m + 1) := by rw [pow_succ']; exact Nat.mul_le_mul_right _ hn
    calc ∑ i ∈ Finset.range (m + 1), n ^ i + n ^ (m + 1) ≤ 2 * n ^ m + n ^ (m + 1) := by omega
      _ ≤ 2 * n ^ (m + 1) := by omega

theorem sum_choose_le_two_pow (n m : ℕ) : ∑ i ∈ Finset.range (m + 1), n.choose i ≤ 2 ^ n := by
  calc ∑ i ∈ Finset.range (m + 1), n.choose i ≤ ∑ i ∈ Finset.range (m + n + 1), n.choose i :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    _ = ∑ i ∈ Finset.range (n + 1), n.choose i := by
        refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i hi hi' => ?_).symm
        rw [Finset.mem_range] at hi'
        exact Nat.choose_eq_zero_of_lt (by omega)
    _ = 2 ^ n := Nat.sum_range_choose n

/-- `Σ_{i ≤ m} C(n, i) ≤ 2 max(1, n)^m`. -/
theorem sum_choose_le (n m : ℕ) : ∑ i ∈ Finset.range (m + 1), n.choose i ≤ 2 * (max 1 n) ^ m := by
  rcases le_or_gt n 1 with hn | hn
  · rw [max_eq_left hn, one_pow, mul_one]
    calc ∑ i ∈ Finset.range (m + 1), n.choose i ≤ 2 ^ n := sum_choose_le_two_pow n m
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 2 := by norm_num
  · rw [max_eq_right hn.le]
    calc ∑ i ∈ Finset.range (m + 1), n.choose i ≤ ∑ i ∈ Finset.range (m + 1), n ^ i :=
          Finset.sum_le_sum fun i _ => Nat.choose_le_pow n i
      _ ≤ 2 * n ^ m := geom_nat_le (by omega) m

/-- For `w ≥ 1`, a range has at most `w^{2^{−j}}` primes. -/
theorem card_T_le {w : ℝ} (hw : 1 ≤ w) (J : ℕ) (j : Fin J) :
    ((max 1 (T w J j).card : ℕ) : ℝ) ≤ w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) := by
  set A := w ^ ((1 / 2 : ℝ) ^ ((j : ℕ) + 1)) with hA
  have hA2 : A ^ 2 = w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    rw [pow_succ]
    push_cast
    ring
  have h1 : (1 : ℝ) ≤ w ^ ((1 / 2 : ℝ) ^ (j : ℕ)) := Real.one_le_rpow hw (by positivity)
  rw [Nat.cast_max, Nat.cast_one]
  refine max_le h1 ?_
  rcases Nat.eq_zero_or_pos (T w J j).card with h0 | hpos
  · rw [h0, Nat.cast_zero]
    linarith
  · have hsub : T w J j ⊆ Finset.Ico 2 ⌈A ^ 2⌉₊ := by
      intro p hp
      obtain ⟨hpp, -, hpA⟩ := mem_rng.1 hp
      exact Finset.mem_Ico.2 ⟨hpp.two_le, Nat.lt_ceil.2 hpA⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    have hc2 : (T w J j).card + 2 ≤ ⌈A ^ 2⌉₊ := by omega
    have hc3 : ((T w J j).card : ℝ) + 2 ≤ ⌈A ^ 2⌉₊ := by exact_mod_cast hc2
    have hc4 : (⌈A ^ 2⌉₊ : ℝ) < A ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [← hA2]
    linarith

theorem sum_half_pow (J : ℕ) : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j = 2 - 2 * (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem sum_mul_half_pow (J : ℕ) :
    ∑ j ∈ Finset.range J, (j : ℝ) * (1 / 2 : ℝ) ^ j = 2 - 2 * ((J : ℝ) + 1) * (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

/-- `Σ_{j<J} 2^{−j}(k + 2j) ≤ 2k + 4`. -/
theorem sum_levels_exp_le (J k : ℕ) :
    ∑ j : Fin J, (1 / 2 : ℝ) ^ (j : ℕ) * ((k : ℝ) + 2 * (j : ℕ)) ≤ 2 * k + 4 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (1 / 2 : ℝ) ^ j * ((k : ℝ) + 2 * j)) J]
  have h1 := sum_half_pow J
  have h2 := sum_mul_half_pow J
  have e : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j * ((k : ℝ) + 2 * j) =
      k * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j + 2 * ∑ j ∈ Finset.range J, (j : ℝ) * (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, h1, h2]
  have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ J := by positivity
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  nlinarith

/-- The fundamental lemma's remainder at the levels `k + 2j`. -/
noncomputable def rem (w : ℝ) (J k : ℕ) : ℝ :=
  (J + 1) * 1 * ∏ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ)

theorem rem_nonneg (w : ℝ) (J k : ℕ) : 0 ≤ rem w J k := by
  unfold rem
  positivity

/-- For `w ≥ 1`, the remainder is at most `(J + 1)2^J w^{2k+4}`. -/
theorem rem_le {w : ℝ} (hw : 1 ≤ w) (J k : ℕ) :
    rem w J k ≤ (J + 1) * 2 ^ J * w ^ ((2 * k + 4 : ℕ) : ℝ) := by
  unfold rem
  have hw0 : 0 < w := by linarith
  have h1 : ∀ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ) ≤
      2 * (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ (k + 2 * (j : ℕ)) := by
    intro j
    have h := sum_choose_le (T w J j).card (k + 2 * (j : ℕ))
    have h' : ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ) ≤
        2 * ((max 1 (T w J j).card : ℕ) : ℝ) ^ (k + 2 * (j : ℕ)) := by exact_mod_cast h
    refine h'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (card_T_le hw J j) _)
      (by norm_num))
  have h2 : ∏ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ) ≤
      ∏ j : Fin J, 2 * (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ (k + 2 * (j : ℕ)) :=
    Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun i _ => by positivity) fun j _ => h1 j
  have h3 : ∏ j : Fin J, 2 * (w ^ ((1 / 2 : ℝ) ^ (j : ℕ))) ^ (k + 2 * (j : ℕ)) =
      2 ^ J * w ^ (∑ j : Fin J, (1 / 2 : ℝ) ^ (j : ℕ) * ((k : ℝ) + 2 * (j : ℕ))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Real.rpow_sum_of_pos hw0]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
    push_cast
    ring_nf
  have h4 : w ^ (∑ j : Fin J, (1 / 2 : ℝ) ^ (j : ℕ) * ((k : ℝ) + 2 * (j : ℕ))) ≤ w ^ ((2 * k + 4 : ℕ) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hw
    push_cast
    exact sum_levels_exp_le J k
  calc ((J : ℝ) + 1) * 1 * ∏ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1), ((T w J j).card.choose i : ℝ)
      ≤ ((J : ℝ) + 1) * 1 * (2 ^ J * w ^ ((2 * k + 4 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (h2.trans (h3.le.trans (mul_le_mul_of_nonneg_left h4 (by positivity))))
          (by positivity)
    _ = (J + 1) * 2 ^ J * w ^ ((2 * k + 4 : ℕ) : ℝ) := by ring

/-- The number of ranges, `J = 2⌊log₂ w⌋ + 2`. -/
def Jw (w : ℕ) : ℕ := 2 * Nat.log 2 w + 2

/-- For `w ≥ 2`, `J = Jw w` covers the primes below `w` (`w^{2^{−J}} ≤ 2`), with `2^J ≤ 4w²` and `J + 1 ≤ 3w`. -/
theorem Jw_spec {w : ℕ} (hw : 2 ≤ w) :
    (w : ℝ) ^ ((1 / 2 : ℝ) ^ Jw w) ≤ 2 ∧ (2 : ℝ) ^ Jw w ≤ 4 * (w : ℝ) ^ 2 ∧ (Jw w : ℝ) + 1 ≤ 3 * w := by
  have hl1 : w < 2 ^ (Nat.log 2 w + 1) := Nat.lt_pow_succ_log_self (by norm_num) w
  have hl2 : 2 ^ Nat.log 2 w ≤ w := Nat.pow_log_le_self 2 (by omega)
  have hl3 : Nat.log 2 w < w := Nat.log_lt_self 2 (by omega)
  have hw0 : (0 : ℝ) < w := by positivity
  have hw2 : (2 : ℝ) ≤ w := by exact_mod_cast hw
  refine ⟨?_, ?_, ?_⟩
  · have hpow : (w : ℝ) ^ 2 < (2 : ℝ) ^ Jw w := by
      have h : (w : ℝ) < 2 ^ (Nat.log 2 w + 1) := by exact_mod_cast hl1
      have e : (2 : ℝ) ^ Jw w = (2 ^ (Nat.log 2 w + 1)) ^ 2 := by unfold Jw; ring
      rw [e]
      exact pow_lt_pow_left₀ h hw0.le (by norm_num)
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlogw : Real.log w ≤ (w : ℝ) ^ 2 * Real.log 2 := by
      have h1 := Real.log_le_sub_one_of_pos hw0
      nlinarith
    have hexp : (1 / 2 : ℝ) ^ Jw w * Real.log w ≤ Real.log 2 := by
      rw [one_div_pow, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      have hl2pos : 0 < Real.log 2 := by linarith
      nlinarith
    calc (w : ℝ) ^ ((1 / 2 : ℝ) ^ Jw w) = Real.exp ((1 / 2 : ℝ) ^ Jw w * Real.log w) := by
          rw [Real.rpow_def_of_pos hw0, mul_comm]
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hexp
      _ = 2 := Real.exp_log (by norm_num)
  · have e : (2 : ℝ) ^ Jw w = 4 * ((2 : ℝ) ^ Nat.log 2 w) ^ 2 := by unfold Jw; ring
    rw [e]
    have : ((2 : ℝ) ^ Nat.log 2 w) ≤ w := by exact_mod_cast hl2
    have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ Nat.log 2 w := by positivity
    nlinarith
  · unfold Jw
    have : (Nat.log 2 w : ℝ) + 1 ≤ w := by exact_mod_cast hl3
    push_cast
    linarith

/-! ### A leaf -/

/-- `ζ(k) = e^{2C₀}·(2C₀^k/k!)·exp(e^{2C₀}·2C₀^{k+1}/(k+1)!)`, the fundamental lemma's relative error at the
levels `k + 2j` (`SieveLeaf.leaf_gap`). -/
noncomputable def zeta (C₀ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (2 * C₀) * (2 * (C₀ ^ k / k.factorial)) *
    Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (k + 1) / (k + 1).factorial)))

theorem zeta_nonneg {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (k : ℕ) : 0 ≤ zeta C₀ k := by
  unfold zeta
  positivity

/-- **A leaf.** For `a` a unit, `d > 0` with every prime factor at least `w ≥ 2`, `N₁ ≤ N₂`, the ranges with
`w^{2^{−J}} ≤ 2`, `C₀ ≥ 0` bounding the sums `Σ 1/p` over the ranges `rng A` (`A ≥ 1`), and levels `k + 2j` with
`k ≥ 1` even and `2C₀² ≤ (k + 1)(k + 2)`: the `n ∈ (N₁, N₂]` with `d ∣ n` and no prime factor below `w` have
`|A − B/φ(q)| ≤ 2ζ(k)(N₂ − N₁)/(dφ(q) log w) + 2·rem`. Here
`ζ(k) = e^{2C₀}(2C₀^k/k!)·exp(e^{2C₀}·2C₀^{k+1}/(k + 1)!)`, as in `SieveLeaf.leaf_gap`. -/
theorem leaf_bound {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {d N₁ N₂ w : ℕ} (hd : 0 < d) (hw : 2 ≤ w)
    (hdw : ∀ p : ℕ, p.Prime → p ∣ d → w ≤ p) {J : ℕ} (hJ : (w : ℝ) ^ ((1 / 2 : ℝ) ^ J) ≤ 2) (hN : N₁ ≤ N₂)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hC : ∀ A : ℝ, 1 ≤ A → ∑ p ∈ rng A, 1 / (p : ℝ) ≤ C₀) {k : ℕ} (hk : Even k)
    (hk1 : 1 ≤ k) (hkC : 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2)) :
    ‖∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if d ∣ n ∧ rough w n then 1 else 0)‖ ≤
      2 * zeta C₀ k * (((N₂ : ℝ) - N₁) / (d * (q.totient * Real.log w))) + 2 * rem w J k := by
  have hq : 0 < q := NeZero.pos q
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogw : 0 < Real.log w := Real.log_pos (by exact_mod_cast hw)
  have hζ0 := zeta_nonneg hC₀ k
  have hR0 := rem_nonneg (w : ℝ) J k
  have hNN : (0 : ℝ) ≤ (N₂ : ℝ) - N₁ := by
    have : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN
    linarith
  have hRHS : 0 ≤ 2 * zeta C₀ k * (((N₂ : ℝ) - N₁) / (d * (q.totient * Real.log w))) + 2 * rem w J k := by
    positivity
  by_cases hcop : Nat.Coprime d q
  · rw [SieveDiff.sum_dw_eq]
    have ha' : Nat.Coprime a.val q := (ZMod.isUnit_iff_coprime a.val q).1 (by rw [ZMod.natCast_zmod_val]; exact ha)
    have hw' : (1 : ℝ) ≤ w := by exact_mod_cast (by omega : 1 ≤ w)
    have hdw' : ∀ p : ℕ, p.Prime → p ∣ d → (w : ℝ) ≤ p := fun p hp hpd => by exact_mod_cast hdw p hp hpd
    have hkk : ∀ j : Fin J, Even (k + 2 * (j : ℕ)) := fun j => by
      rcases hk with ⟨r, hr⟩; exact ⟨r + j, by omega⟩
    have hkk1 : ∀ j : Fin J, 1 ≤ k + 2 * (j : ℕ) := fun j => by omega
    have hA := leaf_A hq ha' hd hcop hw' hdw' hJ hN (fun j => k + 2 * (j : ℕ)) hkk hkk1
    have hB := leaf_B hq hd hcop hw' hdw' hJ hN (fun j => k + 2 * (j : ℕ)) hkk hkk1
    have hG := leaf_gap hw' J q hC₀ hC hk hkC
    rw [Nat.ceil_natCast] at hA hB
    beta_reduce at hA hB
    set A := (#{n ∈ Ioc N₁ N₂ | n ≡ a.val [MOD q] ∧ d ∣ n ∧ ∀ p < w, p.Prime → ¬ p ∣ n} : ℕ) with hAdef
    set B := (#{n ∈ Ioc N₁ N₂ | Nat.Coprime n q ∧ d ∣ n ∧ ∀ p < w, p.Prime → ¬ p ∣ n} : ℕ) with hBdef
    have hAeq : ((Ioc N₁ N₂).filter (fun n => n ≡ a.val [MOD q] ∧ (d ∣ n ∧ rough w n))).card = A := rfl
    have hBeq : ((Ioc N₁ N₂).filter (fun n => Nat.Coprime n q ∧ (d ∣ n ∧ rough w n))).card = B := rfl
    rw [hAeq, hBeq]
    have hreal : ((A : ℂ) - (B : ℂ) / q.totient) = (((A : ℝ) - (B : ℝ) / q.totient : ℝ) : ℂ) := by push_cast; ring
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    set Y := ((N₂ : ℝ) - N₁) / (d * q) with hY
    have hY0 : 0 ≤ Y := by rw [hY]; positivity
    set V := ∏ j : Fin J, ∏ p ∈ T w J j, (1 - g q p) with hV
    set G := ∑ j : Fin J, esym (T w J j) (g q) (k + 2 * (j : ℕ)) *
      ∏ i ∈ Finset.univ.erase j, trunc (T w J i) (g q) (k + 2 * (i : ℕ)) with hGdef
    set R := rem w J k with hRdef
    have hR : R = (J + 1) * 1 * ∏ j : Fin J, ∑ i ∈ Finset.range (k + 2 * (j : ℕ) + 1),
        ((T w J j).card.choose i : ℝ) := rfl
    rw [← hR] at hA hB
    set ζ := zeta C₀ k with hζdef
    have hYG : Y * G ≤ ζ * (Y * V) := by
      have h : Y * G ≤ Y * (V * ζ) := mul_le_mul_of_nonneg_left hG hY0
      linarith [show Y * (V * ζ) = ζ * (Y * V) by ring]
    -- the main term `YV`, by Mertens' product bound
    have hYV : Y * V ≤ ((N₂ : ℝ) - N₁) / (d * (q.totient * Real.log w)) := by
      calc Y * V ≤ Y * (q / (q.totient * Real.log w)) := mul_le_mul_of_nonneg_left (prod_T_le hw hJ hq) hY0
        _ = ((N₂ : ℝ) - N₁) / (d * (q.totient * Real.log w)) := by
          rw [hY]; field_simp
    have htri : |(A : ℝ) - (B : ℝ) / q.totient| ≤ |(A : ℝ) - Y * V| + |(B : ℝ) / q.totient - Y * V| := by
      have e : (A : ℝ) - (B : ℝ) / q.totient = ((A : ℝ) - Y * V) - ((B : ℝ) / q.totient - Y * V) := by ring
      rw [e]
      exact abs_sub _ _
    have hζYV : ζ * (Y * V) ≤ ζ * (((N₂ : ℝ) - N₁) / (d * (q.totient * Real.log w))) :=
      mul_le_mul_of_nonneg_left hYV hζ0
    linarith
  · have hzero : ∀ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if d ∣ n ∧ rough w n then 1 else 0) = 0 := by
      intro n _
      by_cases hn : d ∣ n ∧ rough w n
      · have hnc : ¬ Nat.Coprime n q := fun h => hcop (Nat.Coprime.coprime_dvd_left hn.1 h)
        have hnu : ¬ IsUnit (n : ZMod q) := fun h => hnc ((ZMod.isUnit_iff_coprime n q).1 h)
        have hna : (n : ZMod q) ≠ a := fun h => hnu (h ▸ ha)
        simp [dw, hn, hnu, hna]
      · simp [hn]
    rw [Finset.sum_eq_zero hzero, norm_zero]
    exact hRHS

/-! ### The sums of `1/d` over the leaves -/

/-- `Σ_{rt} Σ_{P ⊆ T} 1/(r∏P) = (Σ_{rt} 1/r)·∏_{p∈T}(1 + 1/p)`. -/
theorem sum_leaves_inv {j : ℕ} (RT : Finset (Fin j → ℕ)) (T : Finset ℕ) :
    ∑ rt ∈ RT, ∑ P ∈ T.powerset, 1 / (((∏ i, rt i) * ∏ p ∈ P, p : ℕ) : ℝ) =
      (∑ rt ∈ RT, 1 / ((∏ i, rt i : ℕ) : ℝ)) * ∏ p ∈ T, (1 + 1 / (p : ℝ)) := by
  rw [Finset.prod_one_add, Finset.sum_mul]
  refine Finset.sum_congr rfl fun rt _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one, one_div_mul_one_div]

/-- `Σ_{rt} 1/∏rt ≤ (Σ_{p∈s} 1/p)^j` over tuples with entries in `s`. -/
theorem sum_RT_inv_le {j : ℕ} {RT : Finset (Fin j → ℕ)} {s : Finset ℕ}
    (hRT : RT ⊆ Fintype.piFinset (fun _ : Fin j => s)) :
    ∑ rt ∈ RT, 1 / ((∏ i, rt i : ℕ) : ℝ) ≤ (∑ p ∈ s, 1 / (p : ℝ)) ^ j := by
  have h : ∀ rt : Fin j → ℕ, 1 / ((∏ i, rt i : ℕ) : ℝ) = ∏ i, 1 / (rt i : ℝ) := fun rt => by
    push_cast
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
  calc ∑ rt ∈ RT, 1 / ((∏ i, rt i : ℕ) : ℝ) ≤ ∑ rt ∈ Fintype.piFinset (fun _ : Fin j => s),
        1 / ((∏ i, rt i : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hRT fun rt _ _ => by positivity
    _ = ∑ rt ∈ Fintype.piFinset (fun _ : Fin j => s), ∏ i, 1 / (rt i : ℝ) :=
        Finset.sum_congr rfl fun rt _ => h rt
    _ = ∏ _i : Fin j, ∑ p ∈ s, 1 / (p : ℝ) := (Finset.prod_univ_sum (fun _ => s) (fun _ p => 1 / (p : ℝ))).symm
    _ = (∑ p ∈ s, 1 / (p : ℝ)) ^ j := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The leaves of the tree -/

/-! ### The level `k` -/

theorem sq_le_four_pow (k : ℕ) : (((2 * k + 4 : ℕ) : ℝ)) ^ 2 ≤ 16 * 4 ^ k := by
  have h1 : k + 2 ≤ 2 ^ (k + 1) := by
    have := Nat.lt_two_pow_self (n := k + 1)
    omega
  have h2 : ((k : ℝ) + 2) ≤ 2 ^ (k + 1) := by exact_mod_cast h1
  have h3 : (((2 * k + 4 : ℕ) : ℝ)) = 2 * ((k : ℝ) + 2) := by push_cast; ring
  rw [h3, mul_pow, show (16 : ℝ) * 4 ^ k = 2 ^ 2 * (2 ^ (k + 1)) ^ 2 by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 2) (by norm_num)

/-- For `C₀ ≥ 0`, `ε > 0` and `a₀ > 0` there is an even `k ≥ 2` with `2C₀² ≤ (k + 1)(k + 2)`,
`(2k + 4)²ζ(k) ≤ ε` and `c < (2k + 4)a₀`. -/
theorem exists_k {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {ε c a₀ : ℝ} (hε : 0 < ε) (ha₀ : 0 < a₀) :
    ∃ k : ℕ, Even k ∧ 2 ≤ k ∧ 2 * C₀ ^ 2 ≤ ((k : ℝ) + 1) * (k + 2) ∧
      (((2 * k + 4 : ℕ) : ℝ)) ^ 2 * zeta C₀ k ≤ ε ∧ c < ((2 * k + 4 : ℕ) : ℝ) * a₀ := by
  set M : ℝ := 32 * Real.exp (2 * C₀ + 1) with hM
  have hM0 : 0 < M := by positivity
  set ε' : ℝ := ε / M with hε'
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hF := FloorSemiring.tendsto_pow_div_factorial_atTop (4 * C₀)
  have hG := (FloorSemiring.tendsto_pow_div_factorial_atTop C₀).comp (Filter.tendsto_add_atTop_nat 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hF.eventually (ge_mem_nhds hε'0))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (hG.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / (2 * Real.exp (2 * C₀)) by positivity)))
  set m : ℕ := max (max N₁ N₂) (max (⌈2 * C₀ ^ 2⌉₊ + 1) (⌈c / a₀⌉₊ + 1)) with hm
  have hN1m : N₁ ≤ m := le_trans (le_max_left N₁ N₂) (le_max_left _ _)
  have hN2m : N₂ ≤ m := le_trans (le_max_right N₁ N₂) (le_max_left _ _)
  have hCm : ⌈2 * C₀ ^ 2⌉₊ + 1 ≤ m := le_trans (le_max_left _ (⌈c / a₀⌉₊ + 1)) (le_max_right _ _)
  have hcm : ⌈c / a₀⌉₊ + 1 ≤ m := le_trans (le_max_right (⌈2 * C₀ ^ 2⌉₊ + 1) _) (le_max_right _ _)
  refine ⟨2 * m, ⟨m, by ring⟩, by omega, ?_, ?_⟩
  · have h1 : (⌈2 * C₀ ^ 2⌉₊ : ℝ) + 1 ≤ m := by exact_mod_cast hCm
    have h2 := Nat.le_ceil (2 * C₀ ^ 2)
    push_cast
    nlinarith
  have hk1 : N₁ ≤ 2 * m := by omega
  have hk2 : N₂ ≤ 2 * m := by omega
  have hF' : (4 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ) ≤ ε' := hN₁ _ hk1
  have hG' : C₀ ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) ≤ 1 / (2 * Real.exp (2 * C₀)) := hN₂ _ hk2
  -- the bound `(2k + 4)²ζ(k) ≤ M·(4C₀)^k/k!`
  have hexp : Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)))) ≤
      Real.exp 1 := by
    apply Real.exp_le_exp.2
    have he : 0 < Real.exp (2 * C₀) := Real.exp_pos _
    have := mul_le_mul_of_nonneg_left hG' (show (0 : ℝ) ≤ 2 * Real.exp (2 * C₀) by positivity)
    rw [mul_one_div_cancel (by positivity)] at this
    linarith
  have hfac : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hz : (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 2 * zeta C₀ (2 * m) ≤
      M * ((4 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ)) := by
    unfold zeta
    have h1 := sq_le_four_pow (2 * m)
    have h2 : (0 : ℝ) ≤ Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m) / ((2 * m).factorial : ℝ))) := by positivity
    calc (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 2 * (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m) / ((2 * m).factorial : ℝ))) *
          Real.exp (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)))))
        ≤ (16 * 4 ^ (2 * m)) * (Real.exp (2 * C₀) * (2 * (C₀ ^ (2 * m) / ((2 * m).factorial : ℝ))) *
          Real.exp 1) := by
          apply mul_le_mul h1 (mul_le_mul_of_nonneg_left hexp h2) (by positivity) (by positivity)
      _ = M * ((4 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ)) := by
          rw [hM, mul_pow, Real.exp_add]
          ring
  have hzM : (((2 * (2 * m) + 4 : ℕ) : ℝ)) ^ 2 * zeta C₀ (2 * m) ≤ ε := by
    calc _ ≤ M * ((4 * C₀) ^ (2 * m) / ((2 * m).factorial : ℝ)) := hz
      _ ≤ M * ε' := mul_le_mul_of_nonneg_left hF' hM0.le
      _ = ε := by rw [hε']; field_simp
  refine ⟨hzM, ?_⟩
  · have h1 : (⌈c / a₀⌉₊ : ℝ) + 1 ≤ m := by exact_mod_cast hcm
    have h2 := Nat.le_ceil (c / a₀)
    have h3 : c / a₀ < ((2 * (2 * m) + 4 : ℕ) : ℝ) := by push_cast; linarith
    rwa [div_lt_iff₀ ha₀] at h3

/-! ### The windows of the stops -/

/-! ### Arithmetic of the error terms -/

/-- The main term's coefficient: for `E > 0`, `K₁ ≥ 0`, `a₀ > 0`, `c > 0` and `η > 0`, with `ε_w = c/(2k + 4)` and
`(2k + 4)²Z ≤ ηc²/(4E(K₁ + 1)a₀)`, the coefficient `4EK₁a₀Z/ε_w²` is at most `η`. -/
theorem main_coef {E K₁ a₀ Z εw c η : ℝ} {k : ℕ} (hE : 0 < E) (hK₁ : 0 ≤ K₁) (ha₀ : 0 < a₀) (hc : 0 < c)
    (hη : 0 < η) (hεw : εw = c / ((2 * k + 4 : ℕ) : ℝ))
    (hζε : ((2 * k + 4 : ℕ) : ℝ) ^ 2 * Z ≤ η * c ^ 2 / (4 * E * (K₁ + 1) * a₀)) :
    4 * E * K₁ * a₀ * Z / εw ^ 2 ≤ η := by
  have hk4 : (0 : ℝ) < ((2 * k + 4 : ℕ) : ℝ) := by positivity
  have hA : 4 * E * K₁ * a₀ * Z / εw ^ 2 = 4 * E * K₁ * a₀ * (((2 * k + 4 : ℕ) : ℝ) ^ 2 * Z) / c ^ 2 := by
    rw [hεw]; field_simp
  have hB : 4 * E * K₁ * a₀ * (((2 * k + 4 : ℕ) : ℝ) ^ 2 * Z) / c ^ 2 ≤
      4 * E * K₁ * a₀ * (η * c ^ 2 / (4 * E * (K₁ + 1) * a₀)) / c ^ 2 := by
    gcongr
  have hC : 4 * E * K₁ * a₀ * (η * c ^ 2 / (4 * E * (K₁ + 1) * a₀)) / c ^ 2 = η * (K₁ / (K₁ + 1)) := by
    field_simp
  have hD : η * (K₁ / (K₁ + 1)) ≤ η := by
    have : K₁ / (K₁ + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  linarith

/-- The leaves' main term: for `Z ≥ 0`, `X ≥ 1`, `φ > 0`, `K₁ ≥ 0`, `E > 0`, `a₀ > 0`, `ε_w > 0`, `L_Q > 0` and
`L_w ≥ ε_w L_Q` (in use `L_w = log w`, `L_Q = log q`), with the coefficient `4EK₁a₀Z/ε_w²` at most `η`:
`2Z(X + 1)/(φL_w) · K₁(Ea₀/ε_w) ≤ ηX/(φL_Q)`. -/
theorem main_term {Z X Lw LQ φ K₁ E a₀ εw η : ℝ} (hZ : 0 ≤ Z) (hX : 1 ≤ X) (hφ : 0 < φ) (hK₁ : 0 ≤ K₁)
    (hE : 0 < E) (ha₀ : 0 < a₀) (hεw : 0 < εw) (hLQ : 0 < LQ) (hlw : εw * LQ ≤ Lw)
    (hcoef : 4 * E * K₁ * a₀ * Z / εw ^ 2 ≤ η) :
    2 * Z * ((X + 1) / (φ * Lw)) * (K₁ * (E * a₀ / εw)) ≤ η * X / (φ * LQ) := by
  have hLw : 0 < Lw := lt_of_lt_of_le (mul_pos hεw hLQ) hlw
  have hXw : (X + 1) / (φ * Lw) ≤ 2 * X / (φ * (εw * LQ)) :=
    calc (X + 1) / (φ * Lw) ≤ 2 * X / (φ * Lw) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 2 * X / (φ * (εw * LQ)) := by
          apply div_le_div_of_nonneg_left (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_left hlw hφ.le
  have e : 2 * Z * (K₁ * (E * a₀ / εw)) * (2 * X / (φ * (εw * LQ))) =
      (4 * E * K₁ * a₀ * Z / εw ^ 2) * (X / (φ * LQ)) := by
    field_simp
    ring
  have hpos : 0 ≤ 2 * Z * (K₁ * (E * a₀ / εw)) := by positivity
  have hpos2 : 0 ≤ X / (φ * LQ) := div_nonneg (by linarith) (by positivity)
  calc 2 * Z * ((X + 1) / (φ * Lw)) * (K₁ * (E * a₀ / εw))
      = 2 * Z * (K₁ * (E * a₀ / εw)) * ((X + 1) / (φ * Lw)) := by ring
    _ ≤ 2 * Z * (K₁ * (E * a₀ / εw)) * (2 * X / (φ * (εw * LQ))) := mul_le_mul_of_nonneg_left hXw hpos
    _ = (4 * E * K₁ * a₀ * Z / εw ^ 2) * (X / (φ * LQ)) := e
    _ ≤ η * (X / (φ * LQ)) := mul_le_mul_of_nonneg_right hcoef hpos2
    _ = η * X / (φ * LQ) := by ring

/-- The leaves' remainder: for a route with `RouteOK`, `Q ≥ 1`, `K ≥ 0`, `1 ≤ w ≤ 2Q^{ε_w}`, `ε_w(2k + 7) ≤ 2c`,
`0 ≤ X' ≤ Q^{b₀}`, `2^J ≤ 4w²`, `J + 1 ≤ 3w`, `24·2^{2k+7}K ≤ Q^c`, `0 < φ ≤ Q`, `L − 1 − c = c + (b₀ + 2c)` and
`R ≤ (J + 1)2^J w^{2k+4}`: `2RX'K ≤ φ⁻¹Q^{L−c}`. -/
theorem rem_term [Route] [RouteOK] {Q w X' φ K εw c b₀ Mrem R : ℝ} {k J : ℕ} (hQ1 : 1 ≤ Q) (hw1 : 1 ≤ w)
    (hwle : w ≤ 2 * Q ^ εw) (hεw7 : εw * ((2 * k + 7 : ℕ) : ℝ) ≤ 2 * c) (hX' : X' ≤ Q ^ b₀) (hX'0 : 0 ≤ X')
    (hK : 0 ≤ K) (hJ2 : (2 : ℝ) ^ J ≤ 4 * w ^ 2) (hJ3 : (J : ℝ) + 1 ≤ 3 * w)
    (hMrem : Mrem = 24 * 2 ^ (2 * k + 7) * K) (hM : Mrem ≤ Q ^ c) (hφ : 0 < φ) (hφq : φ ≤ Q)
    (hc : (L - 1 - c : ℝ) = c + (b₀ + 2 * c))
    (hR : R ≤ (J + 1) * 2 ^ J * w ^ ((2 * k + 4 : ℕ) : ℝ)) : 2 * R * X' * K ≤ φ⁻¹ * Q ^ (L - c : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have hw7 : R ≤ 12 * w ^ (2 * k + 7) := by
    refine hR.trans ?_
    rw [Real.rpow_natCast]
    have h0 : (0 : ℝ) ≤ w ^ (2 * k + 4) := by positivity
    calc ((J : ℝ) + 1) * 2 ^ J * w ^ (2 * k + 4) ≤ (3 * w) * (4 * w ^ 2) * w ^ (2 * k + 4) := by
          apply mul_le_mul (mul_le_mul hJ3 hJ2 (by positivity) (by positivity)) le_rfl h0 (by positivity)
      _ = 12 * w ^ (2 * k + 7) := by ring
  have hwpow : w ^ (2 * k + 7) ≤ 2 ^ (2 * k + 7) * Q ^ (2 * c) := by
    calc w ^ (2 * k + 7) ≤ (2 * Q ^ εw) ^ (2 * k + 7) := pow_le_pow_left₀ (by positivity) hwle _
      _ = 2 ^ (2 * k + 7) * Q ^ (εw * ((2 * k + 7 : ℕ) : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast (Q ^ εw), ← Real.rpow_mul hQ0.le]
      _ ≤ 2 ^ (2 * k + 7) * Q ^ (2 * c) := by
          gcongr
  have hstep : 2 * R * X' * K ≤ Mrem * Q ^ (b₀ + 2 * c) := by
    calc 2 * R * X' * K ≤ 2 * (12 * (2 ^ (2 * k + 7) * Q ^ (2 * c))) * Q ^ b₀ * K := by
          gcongr
          exact hw7.trans (by gcongr)
      _ = Mrem * Q ^ (b₀ + 2 * c) := by
          rw [hMrem, Real.rpow_add hQ0]
          ring
  have hfin : Mrem * Q ^ (b₀ + 2 * c) ≤ Q ^ (L - 1 - c) := by
    rw [hc, Real.rpow_add hQ0 c (b₀ + 2 * c)]
    exact mul_le_mul_of_nonneg_right hM (by positivity)
  have hφinv : Q ^ (L - 1 - c) ≤ φ⁻¹ * Q ^ (L - c : ℝ) := by
    have e : Q ^ (L - c : ℝ) = Q ^ (L - 1 - c) * Q := by
      rw [← Real.rpow_add_one hQ0.ne']; ring_nf
    rw [e, inv_mul_eq_div, le_div_iff₀ hφ]
    exact mul_le_mul_of_nonneg_left hφq (by positivity)
  linarith

/-! ### Proposition 6 -/

section Prop6

open Classical

end Prop6

end SieveProp6
