/-
# The leaves by the bilinear estimate without `2HDm < q`: the asymptotic form

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTypeIBAsym.leaves_ib` (the paper's Lemma 4.3) bounds the leaves `d = d₁d₂` with `d₁f_max ≤ q^{L−1−a}`,
`d₁f_maxd₂² ≤ q^{L−b}` and `d₁d₂ ≥ q^{L−1−δ'}`, `b > 0`: the second condition, `d₁d₂² ≤ x^{1−b/L}`, is what the cut
`2HD_m < q` of its bilinear estimate needs. This file is the same with `SieveTypeIBSumWide.leaves_family_wide`,
whose cut is `H = ⌈qY/ℓ⌉`, for leaves with `d₁f_maxd₂² ≤ q^{L+c}`, `c` of either sign.

* `bdUW_le_pow`: **the uniform bound as powers of `q`.** With `x = q`, `η = x^{−s}`, `ρ = 1 + η`, `N₁ = ⌊x^L⌋`,
  `N₂ = ⌊2x^L⌋`, `X₁ = x^{L−1−a}`, `X₂ = x^{L+c}`, `X₃ = x^{L−1−δ'}`, `Y = x^y`, `r ≥ 2/y`, `F, d(q) ≤ C_dx^s`, and a
  margin `κ ≥ 0` with `max(c, 0) ≤ a − δ' − κ`:
  `bdUW ≤ √(816(64r + 1)C_d)x^{L−1−(κ−y−2s)/2} + 16x^{L−2} + 4(64r + 1)C_dx^{L−1/2+s}/φ(q)`.
* `sIBW`, `sIBW_spec`: the exponent `s = min(κ/(4(J₀ + 6)), e₀, 1/(4(J₀ + 6)))` of `η = θ = q^{−s}`.
* `leaves_ib_wide`: **the leaves by the bilinear estimate on the wider region, asymptotically.** Fix `L > 2`,
  `a ≤ L − 2`, `c ≥ −L`, a margin `κ > 0` and `0 ≤ δ' ≤ min(κ/4, 1/8)` with `max(c, 0) ≤ a − δ' − κ`, and the sizes
  of `leaves_ib`. For large `q`, families of leaves as in `leaves_ib` with every leaf in the region
  `∏y₁·f_max ≤ q^{L−1−a}`, `∏y₁·f_max(∏y₂)² ≤ q^{L+c}`, `∏y₁∏y₂ ≥ q^{L−1−δ'}` have
  `|Σ_y c Σ_m rng(d, m)R(m)dw(dm)| ≤ (N₂ − N₁)/q·|Γ|·Σ_y c/d + q^{L−s/4}/φ(q)`.

In exponents of `x = q^L`, with `d₁ = x^{a₁}`, `d₂ = x^{a₂}` and `τ = 1/L`: the paper's lemma asks `a₁ + 2a₂ < 1`
besides `a₁ < 1 − τ`; this one asks `a₁ + 2a₂ < 1 + c/L` with `c < a − δ'`, where `q^{−a}` is the room of `d₁` below
`x/q` (at most `q^{L−2}`, the room of `q` itself) and `q^{δ'}` that of the cofactor above `q`. For a cofactor of
length at most about `q` (`δ'` small) that is, up to the margins, `2a₁ + 2a₂ < 2 − τ` for `a₁ ≥ τ` (take
`d₁ = x^{1−τ−a/L}`) and `a₁ + 2a₂ < 2 − 2τ` for `a₁ ≤ τ` (take `a = L − 2`): the rule
`max(a₁, τ) + a₁ + 2a₂ < 2 − τ` of `tools/linnik/two_factor.py --bil`.

The proof of `leaves_ib_wide` is that of `leaves_ib`, with `Y = q^y`, `y = min(κ/4, 1/8)`, `r = ⌈2/y⌉`, the divisor
bound `d(n) ≤ F` for `n ≤ ⌊q^{L+2}⌋`, and the three conditions on `Y` of `SieveTypeIBSumWide.bdPW_le` for large `q`
(the step of the splines is at most `q^{1+δ'−s} + 1 ≤ qY`, which is where `δ' ≤ y` enters).

The file imports `SieveTypeIBAsym.lean` and `SieveTypeIBSumWide.lean`.
-/
import SieveTypeIBAsym
import SieveTypeIBSumWide

open Finset MeasureTheory
open scoped FourierTransform

namespace SieveTypeIBAsymWide

open SieveTypeIB SieveSpline SieveTypeIBLeaf SieveTypeIBEv SieveTypeIBSum SieveSmooth SieveTypeIBAsym
  SieveTypeIBSumWide

set_option maxHeartbeats 1000000 in
/-- **The uniform bound with the cut `⌈qY/ℓ⌉`, as powers of `q`.** Let `x = q ≥ 3`, `L > 2`, `0 ≤ δ'`, `a ≤ L − 2`,
`0 < s`, `0 < y`, `r ≥ 2/y`, `F ≤ C_dx^s`, `d(q) ≤ C_dx^s`, and `κ ≥ 0` with `c` and `0` at most `a − δ' − κ`. With `η = x^{−s}`, `ρ = 1 + η`, `N₁ = ⌊x^L⌋`, `N₂ = ⌊2x^L⌋`, `X₁ = x^{L−1−a}`, `X₂ = x^{L+c}`,
`X₃ = x^{L−1−δ'}` and `Y = x^y`:
`bdUW ≤ √(816(64r + 1)C_d)x^{L−1−(κ−y−2s)/2} + 16x^{L−2} + 4(64r + 1)C_dx^{L−1/2+s}/φ(q)`. -/
theorem bdUW_le_pow (q : ℕ) [NeZero q] {L s a c δ' κ y Cd : ℝ} (hq3 : (3 : ℝ) ≤ q) (hL : 2 < L) (hδ' : 0 ≤ δ')
    (haL : a ≤ L - 2) (hκ : 0 ≤ κ) (hκ1 : c ≤ a - δ' - κ)
    (hκ3 : 0 ≤ a - δ' - κ) (hs : 0 < s) (hy : 0 < y) {r : ℕ} (hr : 2 / y ≤ r) {F : ℕ}
    (hF : (F : ℝ) ≤ Cd * (q : ℝ) ^ s) (hdq : (q.divisors.card : ℝ) ≤ Cd * (q : ℝ) ^ s) :
    bdUW q (1 + (q : ℝ) ^ (-s)) ((q : ℝ) ^ (-s)) ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊ r F ((q : ℝ) ^ (L - 1 - a))
        ((q : ℝ) ^ (L + c)) ((q : ℝ) ^ (L - 1 - δ')) ((q : ℝ) ^ y) ≤
      √(816 * ((64 * r + 1) * Cd)) * (q : ℝ) ^ (L - 1 - (κ - y - 2 * s) / 2) + 16 * (q : ℝ) ^ (L - 2) +
        4 * ((64 * r + 1) * Cd) * (q : ℝ) ^ (L - 1 / 2 + s) / q.totient := by
  set x : ℝ := (q : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set η : ℝ := x ^ (-s) with hηdef
  have hη0 : 0 < η := Real.rpow_pos_of_pos hx0 _
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hρ1 : 1 + η ≤ 2 := by linarith
  have hxL : 2 ≤ x ^ L := by
    calc (2 : ℝ) ≤ x ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
      _ ≤ x ^ L := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  set N₁ := ⌊x ^ L⌋₊ with hN₁
  set N₂ := ⌊2 * x ^ L⌋₊ with hN₂
  have hN₂le : (N₂ : ℝ) ≤ 2 * x ^ L := Nat.floor_le (by positivity)
  have hN₁ge : x ^ L / 2 ≤ (N₁ : ℝ) := by
    have := Nat.sub_one_lt_floor (x ^ L)
    linarith
  have hN₁0 : 0 < (N₁ : ℝ) := lt_of_lt_of_le (by positivity) hN₁ge
  have hN₂0 : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
  have hdq0 : 0 ≤ Cd * x ^ s := le_trans (Nat.cast_nonneg _) hdq
  have hxs1 : 1 ≤ x ^ s := Real.one_le_rpow hx1 hs.le
  have hCd : 0 ≤ Cd := (mul_nonneg_iff_of_pos_right (by positivity)).1 hdq0
  clear_value N₁ N₂
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hr
  have hxy0 : 0 < x ^ y := Real.rpow_pos_of_pos hx0 _
  have hg1 : (1 : ℝ) ≤ x ^ (a - δ' - κ + y + s) := Real.one_le_rpow hx1 (by linarith)
  rw [bdUW]
  -- the factor of the diagonal
  have hbase : r * (1 + η) ^ 3 * x ^ (L + c) / (η * N₁) ≤ 16 * r * x ^ (s + c) := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : (1 + η) ^ 3 ≤ 8 := by
      calc (1 + η) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) hρ1 3
        _ = 8 := by norm_num
    have hsb' : x ^ (s + c) * η * x ^ L = x ^ (L + c) := by
      rw [hηdef, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
    calc r * (1 + η) ^ 3 * x ^ (L + c) ≤ r * 8 * x ^ (L + c) := by gcongr
      _ = 16 * r * x ^ (s + c) * (η * (x ^ L / 2)) := by rw [← hsb']; ring
      _ ≤ 16 * r * x ^ (s + c) * (η * N₁) := by gcongr
  have hΦ : 4 * x ^ y * (r * (1 + η) ^ 3 * x ^ (L + c) / (η * N₁)) + 1 ≤
      (64 * r + 1) * x ^ (a - δ' - κ + y + s) := by
    have h1 : 4 * x ^ y * (r * (1 + η) ^ 3 * x ^ (L + c) / (η * N₁)) ≤ 64 * r * x ^ (a - δ' - κ + y + s) := by
      calc 4 * x ^ y * (r * (1 + η) ^ 3 * x ^ (L + c) / (η * N₁)) ≤ 4 * x ^ y * (16 * r * x ^ (s + c)) :=
            mul_le_mul_of_nonneg_left hbase (by positivity)
        _ = 64 * r * x ^ (y + (s + c)) := by rw [Real.rpow_add hx0 y (s + c)]; ring
        _ ≤ 64 * r * x ^ (a - δ' - κ + y + s) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) (by positivity)
    linarith
  have hΦ0 : 0 ≤ 4 * x ^ y * (r * (1 + η) ^ 3 * x ^ (L + c) / (η * N₁)) + 1 := by positivity
  have e1 : (1 + η) ^ 2 * (1 + η) * N₂ ≤ 16 * x ^ L := by
    have : (1 + η) ^ 2 * (1 + η) ≤ 8 := by
      have h0 : 0 ≤ 1 + η := by linarith
      calc (1 + η) ^ 2 * (1 + η) ≤ 2 ^ 2 * 2 := by gcongr
        _ = 8 := by norm_num
    nlinarith
  -- the first term
  have hA : √((1 + η) ^ 2 * (1 + η) * N₂ * ((1 + η) * x ^ (L - 1 - a) / q + 1) *
        (F * (4 * x ^ y * (r * (1 + η) ^ 3 * x ^ (L + c) / (η * N₁)) + 1)) *
        ((1 + η) * (1 + η) ^ 2 * N₂ / (x ^ (L - 1 - δ') * q) + 1)) ≤
      √(816 * ((64 * r + 1) * Cd)) * x ^ (L - 1 - (κ - y - 2 * s) / 2) := by
    have hxa : 1 ≤ x ^ (L - 2 - a) := Real.one_le_rpow hx1 (by linarith)
    have e2 : (1 + η) * x ^ (L - 1 - a) / q + 1 ≤ 3 * x ^ (L - 2 - a) := by
      have : x ^ (L - 1 - a) / x = x ^ (L - 2 - a) := by
        rw [div_eq_iff hx0.ne', ← Real.rpow_add_one hx0.ne']; ring_nf
      have h2 : (1 + η) * x ^ (L - 1 - a) / q = (1 + η) * x ^ (L - 2 - a) := by
        rw [mul_div_assoc, ← hxdef, this]
      rw [h2]
      nlinarith
    have hxδ : 1 ≤ x ^ δ' := Real.one_le_rpow hx1 hδ'
    have e3 : (1 + η) * (1 + η) ^ 2 * N₂ / (x ^ (L - 1 - δ') * q) + 1 ≤ 17 * x ^ δ' := by
      have hden : x ^ (L - 1 - δ') * q = x ^ L / x ^ δ' := by
        rw [← hxdef, eq_div_iff (by positivity)]
        calc x ^ (L - 1 - δ') * x * x ^ δ' = x ^ (L - 1 - δ') * x ^ (1 : ℝ) * x ^ δ' := by rw [Real.rpow_one]
          _ = x ^ (L - 1 - δ' + 1 + δ') := by rw [Real.rpow_add hx0, Real.rpow_add hx0]
          _ = x ^ L := by ring_nf
      rw [hden]
      have h8 : (1 + η) * (1 + η) ^ 2 * N₂ ≤ 16 * x ^ L := by nlinarith
      have hpos : 0 < x ^ L / x ^ δ' := by positivity
      have : (1 + η) * (1 + η) ^ 2 * N₂ / (x ^ L / x ^ δ') ≤ 16 * x ^ δ' := by
        rw [div_le_iff₀ hpos]
        rw [show 16 * x ^ δ' * (x ^ L / x ^ δ') = 16 * x ^ L by field_simp]
        exact h8
      linarith
    have e4 : (F : ℝ) * (4 * x ^ y * (r * (1 + η) ^ 3 * x ^ (L + c) / (η * N₁)) + 1) ≤
        (Cd * x ^ s) * ((64 * r + 1) * x ^ (a - δ' - κ + y + s)) :=
      mul_le_mul hF hΦ hΦ0 hdq0
    have hprod : (1 + η) ^ 2 * (1 + η) * N₂ * ((1 + η) * x ^ (L - 1 - a) / q + 1) *
        (F * (4 * x ^ y * (r * (1 + η) ^ 3 * x ^ (L + c) / (η * N₁)) + 1)) *
        ((1 + η) * (1 + η) ^ 2 * N₂ / (x ^ (L - 1 - δ') * q) + 1) ≤
        (16 * x ^ L) * (3 * x ^ (L - 2 - a)) * ((Cd * x ^ s) * ((64 * r + 1) * x ^ (a - δ' - κ + y + s))) *
          (17 * x ^ δ') := by
      have h0a : 0 ≤ (1 + η) ^ 2 * (1 + η) * N₂ := by positivity
      have h0b : 0 ≤ (1 + η) * x ^ (L - 1 - a) / q + 1 := by positivity
      have h0c : (0 : ℝ) ≤ F * (4 * x ^ y * (r * (1 + η) ^ 3 * x ^ (L + c) / (η * N₁)) + 1) :=
        mul_nonneg (Nat.cast_nonneg _) hΦ0
      have h0d : 0 ≤ (1 + η) * (1 + η) ^ 2 * N₂ / (x ^ (L - 1 - δ') * q) + 1 := by positivity
      exact mul_le_mul (mul_le_mul (mul_le_mul e1 e2 h0b (by positivity)) e4 h0c (by positivity)) e3 h0d
        (by positivity)
    have hsq : (16 * x ^ L) * (3 * x ^ (L - 2 - a)) * ((Cd * x ^ s) * ((64 * r + 1) * x ^ (a - δ' - κ + y + s))) *
        (17 * x ^ δ') = 816 * ((64 * r + 1) * Cd) * (x ^ (L - 1 - (κ - y - 2 * s) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      have : x ^ L * x ^ (L - 2 - a) * x ^ s * x ^ (a - δ' - κ + y + s) * x ^ δ' =
          x ^ ((L - 1 - (κ - y - 2 * s) / 2) * ((2 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
        congr 1; push_cast; ring
      rw [← this]; ring
    have hc0 : (0 : ℝ) ≤ 816 * ((64 * r + 1) * Cd) := by positivity
    calc _ ≤ √(816 * ((64 * r + 1) * Cd) * (x ^ (L - 1 - (κ - y - 2 * s) / 2)) ^ 2) :=
          Real.sqrt_le_sqrt (hprod.trans (le_of_eq hsq))
      _ = √(816 * ((64 * r + 1) * Cd)) * x ^ (L - 1 - (κ - y - 2 * s) / 2) := by
          rw [Real.sqrt_mul hc0, Real.sqrt_sq (by positivity)]
  -- the tail
  have hB : (1 + η) ^ 2 * (1 + η) * N₂ * (1 / (2 * x ^ y)) ^ r ≤ 16 * x ^ (L - 2) := by
    have hpow : (1 / (2 * x ^ y)) ^ r ≤ x ^ (-2 : ℝ) := by
      have h1 : 1 / (2 * x ^ y) ≤ x ^ (-y) := by
        rw [Real.rpow_neg hx0.le, ← one_div]
        exact one_div_le_one_div_of_le hxy0 (by linarith)
      have hyr : 2 ≤ y * r := by
        have := (div_le_iff₀ hy).1 hr
        linarith
      calc (1 / (2 * x ^ y)) ^ r ≤ (x ^ (-y)) ^ r := pow_le_pow_left₀ (by positivity) h1 r
        _ = x ^ (-y * r) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        _ ≤ x ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc (1 + η) ^ 2 * (1 + η) * N₂ * (1 / (2 * x ^ y)) ^ r ≤ (16 * x ^ L) * x ^ (-2 : ℝ) :=
          mul_le_mul e1 hpow (by positivity) (by positivity)
      _ = 16 * (x ^ L * x ^ (-2 : ℝ)) := by ring
      _ = 16 * x ^ (L - 2) := by rw [← Real.rpow_add hx0]; ring_nf
  -- the last term
  have hC : (1 + η) ^ 2 * √(x ^ (L - 1 - a) * x ^ (L + c)) * ((q.divisors.card : ℝ) / q.totient) ≤
      4 * ((64 * r + 1) * Cd) * x ^ (L - 1 / 2 + s) / q.totient := by
    have hsq : √(x ^ (L - 1 - a) * x ^ (L + c)) ≤ x ^ (L - 1 / 2) := by
      rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h4 : (1 + η) ^ 2 ≤ 4 := by nlinarith
    have hCd2 : Cd ≤ (64 * r + 1) * Cd := by nlinarith
    calc (1 + η) ^ 2 * √(x ^ (L - 1 - a) * x ^ (L + c)) * ((q.divisors.card : ℝ) / q.totient)
        ≤ 4 * x ^ (L - 1 / 2) * (Cd * x ^ s / q.totient) := by
          gcongr
      _ = 4 * Cd * x ^ (L - 1 / 2 + s) / q.totient := by
          rw [Real.rpow_add hx0]; ring
      _ ≤ 4 * ((64 * r + 1) * Cd) * x ^ (L - 1 / 2 + s) / q.totient := by
          gcongr
  exact add_le_add (add_le_add hA hB) hC

/-- The exponent `s` of the parameters `η = θ = q^{−s}` for the wider region:
`s = min(κ/(4(J₀ + 6)), e₀, 1/(4(J₀ + 6)))`. -/
noncomputable def sIBW (κ e₀ : ℝ) (J₀ : ℕ) : ℝ :=
  min (min (κ / (4 * (J₀ + 6))) e₀) (1 / (4 * (J₀ + 6)))

theorem sIBW_spec {κ e₀ : ℝ} (hκ : 0 < κ) (he₀ : 0 < e₀) (J₀ : ℕ) :
    0 < sIBW κ e₀ J₀ ∧ sIBW κ e₀ J₀ ≤ κ / (4 * (J₀ + 6)) ∧ sIBW κ e₀ J₀ ≤ e₀ ∧
      sIBW κ e₀ J₀ ≤ 1 / (4 * (J₀ + 6)) := by
  unfold sIBW
  have h1 : 0 < κ / (4 * (J₀ + 6)) := by positivity
  refine ⟨lt_min (lt_min h1 he₀) (by positivity), ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact min_le_right _ _

set_option maxHeartbeats 8000000 in
open Classical Filter in
/-- **The leaves by the bilinear estimate on the wider region, asymptotically.** Fix `L > 2`, `a ≤ L − 2`, `c ≥ −L`,
a margin `κ > 0` and `0 ≤ δ' ≤ min(κ/4, 1/8)` with `c` and `0` at most `a − δ' − κ`; `e₀ > 0`, `Λ₀ ≥ 0`, `B ≥ 1`,
sizes `K₁`, `K₂`, `J₀`, and `0 ≤ c₁ < s/4` with `s = sIBW κ e₀ J₀`. There are `δ > 0` and `q₀` such that for `q ≥ q₀`
and a unit `a'`: let families `Y₁`, `Y₂` of tuples lie in boxes of integers at least `q^{e₀}` with `Σ 1/p ≤ B` on each
coordinate, with fibres of `∏y₂` at most `q^{c₁}`; let `J ≤ J₀` sharp comparisons `Pr_j` of forms
`c_j + Σ e₁ log y₁ + Σ e₂ log y₂ ≤ Λ₀ log q`, each with a coefficient `±1`; let sieve weights `S₁` above and `S₂`
below sandwich `R`, with divisors in `[1, f_max]`, fibres and `Σ|λ|/f` at most `q^{c₁}` and `Σ|λ|` at most `q^{1/4}`;
and let every leaf have `∏y₁·f_max ≤ q^{L−1−a}`, `∏y₁·f_max(∏y₂)² ≤ q^{L+c}` and `∏y₁∏y₂ ≥ q^{L−1−δ'}`. Then the
leaves' sum `Σ_{y₁,y₂} c Σ_m rng(d, m)R(m)dw(dm)`, `c = ∏_j 1[Pr_j]`, `d = ∏y₁∏y₂`, `N₁ = ⌊q^L⌋`, `N₂ = ⌊2q^L⌋`, is at
most `(N₂ − N₁)/q·|Γ|·Σ_y c/d + q^{L−δ}/φ(q)` in absolute value, `Γ` the sieve's gap. `SieveTypeIBAsym.leaves_ib` is
the region `∏y₁·f_max(∏y₂)² ≤ q^{L−b}`, `b > 0`. -/
theorem leaves_ib_wide {L : ℝ} (hL : 2 < L) {a c δ' κ e₀ c₁ Λ₀ B : ℝ} (hδ' : 0 ≤ δ') (haL : a ≤ L - 2)
    (hκ : 0 < κ) (hκ1 : c ≤ a - δ' - κ) (hκ3 : 0 ≤ a - δ' - κ) (hδ1 : δ' ≤ κ / 4) (hδ2 : δ' ≤ 1 / 8)
    (hcL : -L ≤ c) (he₀ : 0 < e₀) (hΛ₀ : 0 ≤ Λ₀) (hB : 1 ≤ B) (K₁ K₂ J₀ : ℕ) (hc₁0 : 0 ≤ c₁)
    (hc₁ : c₁ < sIBW κ e₀ J₀ / 4) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a' : ZMod q), IsUnit a' →
    ∀ (t₁ : Fin K₁ → Finset ℕ) (t₂ : Fin K₂ → Finset ℕ),
      (∀ i, ∀ p ∈ t₁ i, (q : ℝ) ^ e₀ ≤ p) → (∀ i, ∀ p ∈ t₂ i, (q : ℝ) ^ e₀ ≤ p) →
      (∀ i, ∑ p ∈ t₁ i, 1 / (p : ℝ) ≤ B) → (∀ i, ∑ p ∈ t₂ i, 1 / (p : ℝ) ≤ B) →
    ∀ (Y₁ : Finset (Fin K₁ → ℕ)) (Y₂ : Finset (Fin K₂ → ℕ)), Y₁ ⊆ Fintype.piFinset t₁ →
      Y₂ ⊆ Fintype.piFinset t₂ → (∀ d, (#(Y₂.filter (fun y => ∏ i, y i = d)) : ℝ) ≤ (q : ℝ) ^ c₁) →
    ∀ {J : ℕ}, J ≤ J₀ → ∀ (cc : Fin J → ℝ) (e₁ : Fin J → Fin K₁ → ℝ) (e₂ : Fin J → Fin K₂ → ℝ)
      (Pr : Fin J → (Fin K₁ → ℕ) → (Fin K₂ → ℕ) → Prop),
      (∀ j y₁ y₂, (0 < cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) → Pr j y₁ y₂) ∧
        (Pr j y₁ y₂ → 0 ≤ cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) →
      (∀ j, ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂,
        cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) ≤ Λ₀ * Real.log q) →
      (∀ j, (∃ i, e₁ j i = 1 ∨ e₁ j i = -1) ∨ ∃ i, e₂ j i = 1 ∨ e₂ j i = -1) →
    ∀ (R : ℕ → ℝ) {κ₁ κ₂ : Type} (S₁ : Finset κ₁) (f₁ : κ₁ → ℕ) (l₁ : κ₁ → ℝ) (S₂ : Finset κ₂)
      (f₂ : κ₂ → ℕ) (l₂ : κ₂ → ℝ), (∀ σ ∈ S₁, 1 ≤ f₁ σ) → (∀ τ ∈ S₂, 1 ≤ f₂ τ) →
      (∀ m, R m ≤ ∑ σ ∈ S₁, l₁ σ * dv (f₁ σ) m) → (∀ m, ∑ τ ∈ S₂, l₂ τ * dv (f₂ τ) m ≤ R m) →
    ∀ fmax : ℝ, 1 ≤ fmax → (∀ σ ∈ S₁, (f₁ σ : ℝ) ≤ fmax) → (∀ τ ∈ S₂, (f₂ τ : ℝ) ≤ fmax) →
      (∀ d, ∑ x ∈ (Y₁ ×ˢ S₁).filter (fun x => (∏ i, x.1 i) * f₁ x.2 = d), |l₁ x.2| ≤ (q : ℝ) ^ c₁) →
      (∀ d, ∑ x ∈ (Y₁ ×ˢ S₂).filter (fun x => (∏ i, x.1 i) * f₂ x.2 = d), |l₂ x.2| ≤ (q : ℝ) ^ c₁) →
      ∑ σ ∈ S₁, |l₁ σ| + ∑ τ ∈ S₂, |l₂ τ| ≤ (q : ℝ) ^ (1 / 4 : ℝ) →
      ∑ σ ∈ S₁, |l₁ σ| / f₁ σ + ∑ τ ∈ S₂, |l₂ τ| / f₂ τ ≤ (q : ℝ) ^ c₁ →
      (∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∀ j, Pr j y₁ y₂) →
        ((∏ i, y₁ i : ℕ) : ℝ) * fmax ≤ (q : ℝ) ^ (L - 1 - a) ∧
        ((∏ i, y₁ i : ℕ) : ℝ) * fmax * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ (L + c) ∧
        (q : ℝ) ^ (L - 1 - δ') ≤ ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ)) →
      |∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) *
          ∑ m ∈ range (⌊2 * (q : ℝ) ^ L⌋₊ + 1),
            rng ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊ ((∏ i, y₁ i) * ∏ i, y₂ i) m * R m *
              dwR q a' ((∏ i, y₁ i) * (∏ i, y₂ i) * m)| ≤
        ((⌊2 * (q : ℝ) ^ L⌋₊ : ℝ) - ⌊(q : ℝ) ^ L⌋₊) / q *
            |∑ σ ∈ S₁, l₁ σ * gU q (f₁ σ) / f₁ σ - ∑ τ ∈ S₂, l₂ τ * gU q (f₂ τ) / f₂ τ| *
            ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, if Pr j y₁ y₂ then (1 : ℝ) else 0) /
              (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) +
          (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  obtain ⟨hs0, hsκ, hse, hs1⟩ := sIBW_spec hκ he₀ J₀
  set s := sIBW κ e₀ J₀ with hsdef
  have hL2 : L + 2 ≠ 0 := by linarith
  have hs1' : s ≤ 1 := hs1.trans (by rw [div_le_one (by positivity)]; linarith)
  have hs₀0 : 0 < s / (L + 2) := div_pos hs0 (by linarith)
  have hs₀1 : s / (L + 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = min (κ / 4) (1 / 8) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hydef]; exact lt_min (by linarith) (by norm_num)
  have hyκ : y ≤ κ / 4 := by rw [hydef]; exact min_le_left _ _
  have hy8 : y ≤ 1 / 8 := by rw [hydef]; exact min_le_right _ _
  have hδy : δ' ≤ y := by rw [hydef]; exact le_min hδ1 hδ2
  set r : ℕ := ⌈2 / y⌉₊ with hrdef
  have hr4 : 2 / y ≤ r := Nat.le_ceil _
  have hr1 : 1 ≤ r := by
    have h4 : (0 : ℝ) < 2 / y := by positivity
    have : (0 : ℝ) < r := lt_of_lt_of_le h4 hr4
    have : 0 < r := by exact_mod_cast this
    omega
  set Cd := LinnikPower.Cdiv (s / (L + 2)) with hCddef
  have hCd1 : 1 ≤ Cd := LinnikPower.one_le_Cdiv hs₀0 hs₀1
  obtain ⟨Cd2, hCd2⟩ : ∃ C : ℝ, C = (64 * r + 1) * Cd := ⟨_, rfl⟩
  have hCd20 : 0 ≤ Cd2 := by rw [hCd2]; positivity
  have hc₂ : 0 ≤ ∫ v, ‖iteratedDeriv 2 SieveSmooth.gc v‖ := integral_nonneg fun _ => norm_nonneg _
  set Cm := 1 + (∫ v, ‖iteratedDeriv 2 SieveSmooth.gc v‖) / (2 * Real.pi) with hCmdef
  have hCm1 : 1 ≤ Cm := by
    have : 0 ≤ (∫ v, ‖iteratedDeriv 2 SieveSmooth.gc v‖) / (2 * Real.pi) := by positivity
    linarith
  set Ctot : ℝ := (15 + 2 * Cd) * B ^ (K₁ + K₂) +
    36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * (√(816 * Cd2) + 16 + 4 * Cd2) + 416 * J₀ * B ^ (K₁ + K₂) with hCtot
  refine ⟨s / 4, by positivity, ?_⟩
  have hev : ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ Real.pi * (2 * Λ₀ * Real.log x + 3) ≤ x ^ s ∧
      Ctot * Real.log x ^ 2 * x ^ (L - 3 * s / 4) ≤ x ^ (L - s / 4) ∧ 16 * (r : ℝ) + 3 ≤ x ^ (1 / 3 : ℝ) :=
    (eventually_ge_atTop 3).and ((SieveFamily.ev_pi_log_le hs0 hΛ₀).and ((ev_log_sq_le Ctot (by linarith)).and
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop _)))
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨q₀, ?_⟩
  intro q _ hq a' ha' t₁ t₂ ht₁ ht₂ hB₁ hB₂ Y₁ Y₂ hY₁ hY₂ hM₂ J hJ cc e₁ e₂ Pr hPr hΛ hpiv R κ₁ κ₂ S₁ f₁ l₁ S₂ f₂
    l₂ hf₁ hf₂ hR₁ hR₂ fmax hfmax hfm₁ hfm₂ hMf₁ hMf₂ hW hV hreg
  obtain ⟨hx3, hmassc, hfin, hx13⟩ := hq₀ q hq
  set x : ℝ := (q : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have hφx : (q.totient : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast Nat.totient_le q
  -- the parameters
  have hxs9 : 9 ≤ x ^ s := by
    have := Real.pi_gt_three
    have : 0 ≤ Real.pi * (2 * Λ₀ * Real.log x) := by positivity
    nlinarith
  set θ : ℝ := x ^ (-s) with hθdef
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos hx0 _
  have hθxs : θ * x ^ s = 1 := by rw [hθdef, ← Real.rpow_add hx0]; simp
  have hθ9 : θ ≤ 1 / 9 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  set Λ : ℝ := Λ₀ * Real.log x + 1 with hΛdef
  have hΛ1 : 1 ≤ Λ := by rw [hΛdef]; nlinarith [mul_nonneg hΛ₀ hlx]
  have hθΛ : θ ≤ 2 * Λ := by linarith
  obtain ⟨hGc, hGi, hGf, hGm, hMc, hMi, hMfr, hMm⟩ := cutoffs hθ0 hθΛ
  obtain ⟨hmB1, hmB2⟩ := SieveFamily.massB_le hx1 hΛ₀ hmassc
  set N₁ : ℕ := ⌊x ^ L⌋₊ with hN₁def
  set N₂ : ℕ := ⌊2 * x ^ L⌋₊ with hN₂def
  have hxL1 : 1 ≤ x ^ L := Real.one_le_rpow hx1 (by linarith)
  have hN : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₁ : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hxL1)
  have hN₁le : (N₁ : ℝ) ≤ x ^ L := Nat.floor_le (by positivity)
  have hN₂le : (N₂ : ℝ) ≤ 2 * x ^ L := Nat.floor_le (by positivity)
  -- the divisor bound, for `n ≤ ⌊x^{L+2}⌋`
  set NF : ℕ := ⌊x ^ (L + 2)⌋₊ with hNFdef
  have hNFle : (NF : ℝ) ≤ x ^ (L + 2) := Nat.floor_le (by positivity)
  have hpow₀ : ∀ n : ℕ, (n : ℝ) ≤ x ^ (L + 2) → (n : ℝ) ^ (s / (L + 2)) ≤ x ^ s := by
    intro n hn
    calc (n : ℝ) ^ (s / (L + 2)) ≤ (x ^ (L + 2)) ^ (s / (L + 2)) := Real.rpow_le_rpow (by positivity) hn hs₀0.le
      _ = x ^ s := by
          rw [← Real.rpow_mul hx0.le]
          congr 1
          field_simp
  set F : ℕ := ⌊Cd * x ^ s⌋₊ with hFdef
  have hF : ∀ n, 0 < n → n ≤ NF → n.divisors.card ≤ F := by
    intro n hn hnF
    apply Nat.le_floor
    refine (LinnikPower.card_divisors_le hs₀0 hs₀1 n).trans ?_
    have hnR : (n : ℝ) ≤ x ^ (L + 2) := le_trans (by exact_mod_cast hnF) hNFle
    exact mul_le_mul_of_nonneg_left (hpow₀ n hnR) (by linarith)
  have hFR : (F : ℝ) ≤ Cd * x ^ s := Nat.floor_le (by positivity)
  have hdq : (q.divisors.card : ℝ) ≤ Cd * x ^ s := by
    refine (LinnikPower.card_divisors_le hs₀0 hs₀1 q).trans ?_
    have hqR : (q : ℝ) ≤ x ^ (L + 2) := by
      rw [← hxdef]
      calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ (L + 2) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    exact mul_le_mul_of_nonneg_left (hpow₀ q hqR) (by linarith)
  -- the two conditions on the cut, with `Y = x^y`
  have hy1 : 0 < x ^ y := Real.rpow_pos_of_pos hx0 _
  have hs1'' : s * (4 * (J₀ + 6)) ≤ 1 := (le_div_iff₀ (by positivity)).1 hs1
  have hJs : 0 ≤ (J₀ : ℝ) * s := by positivity
  have hs24 : s ≤ 1 / 24 := by linarith
  have hθ1' : θ ≤ 1 := by linarith
  have hxL2 : 2 ≤ x ^ L := by
    calc (2 : ℝ) ≤ x ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
      _ ≤ x ^ L := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hN₁ge : x ^ L / 2 ≤ (N₁ : ℝ) := by
    have := Nat.sub_one_lt_floor (x ^ L)
    linarith
  have hθL : θ * x ^ L = x ^ (L - s) := by
    rw [hθdef, ← Real.rpow_add hx0]; congr 1; ring
  have hθN₁ : x ^ (L - s) / 2 ≤ θ * N₁ := by
    have := mul_le_mul_of_nonneg_left hN₁ge hθ0.le
    linarith
  have hx23 : 1 ≤ x ^ (2 / 3 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hx13x : x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hsqX : √(x ^ (L - 1 - a) * x ^ (L + c)) ≤ x ^ (L - 1 / 2) := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hcut : 2 * (x * x ^ y * ((r : ℝ) * (1 + θ) ^ 2 * √(x ^ (L - 1 - a) * x ^ (L + c))) / (θ * N₁) + 1) < x := by
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hρ2 : (1 + θ) ^ 2 ≤ 4 := by nlinarith
    have h1 : x * x ^ y * ((r : ℝ) * (1 + θ) ^ 2 * √(x ^ (L - 1 - a) * x ^ (L + c))) / (θ * N₁) ≤
        8 * r * x ^ (2 / 3 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have hexp : x * x ^ y * x ^ (L - 1 / 2) ≤ x ^ (2 / 3 : ℝ) * x ^ (L - s) := by
        have : x * x ^ y * x ^ (L - 1 / 2) = x ^ (1 + y + (L - 1 / 2)) := by
          rw [Real.rpow_add hx0 (1 + y) (L - 1 / 2), Real.rpow_add hx0 1 y, Real.rpow_one]
        rw [this, ← Real.rpow_add hx0]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      calc x * x ^ y * ((r : ℝ) * (1 + θ) ^ 2 * √(x ^ (L - 1 - a) * x ^ (L + c)))
          ≤ x * x ^ y * ((r : ℝ) * 4 * x ^ (L - 1 / 2)) := by gcongr
        _ = 4 * r * (x * x ^ y * x ^ (L - 1 / 2)) := by ring
        _ ≤ 4 * r * (x ^ (2 / 3 : ℝ) * x ^ (L - s)) := by gcongr
        _ = 8 * r * x ^ (2 / 3 : ℝ) * (x ^ (L - s) / 2) := by ring
        _ ≤ 8 * r * x ^ (2 / 3 : ℝ) * (θ * N₁) := by gcongr
    have h2 : 16 * (r : ℝ) * x ^ (2 / 3 : ℝ) + 2 < x := by
      have := mul_le_mul_of_nonneg_right hx13 (by positivity : (0 : ℝ) ≤ x ^ (2 / 3 : ℝ))
      rw [hx13x] at this
      linarith
    linarith
  have hstep : θ * N₁ / ((r : ℝ) * x ^ (L - 1 - δ')) + 1 ≤ x * x ^ y := by
    have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hX0 : 0 < x ^ (L - 1 - δ') := Real.rpow_pos_of_pos hx0 _
    have h1 : θ * N₁ / ((r : ℝ) * x ^ (L - 1 - δ')) ≤ x ^ (1 + δ' - s) := by
      rw [div_le_iff₀ (by positivity)]
      have e : x ^ (1 + δ' - s) * x ^ (L - 1 - δ') = x ^ (L - s) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      have hθN : θ * N₁ ≤ x ^ (L - s) := by
        rw [← hθL]; exact mul_le_mul_of_nonneg_left hN₁le hθ0.le
      have hpos : 0 ≤ x ^ (1 + δ' - s) := by positivity
      calc θ * N₁ ≤ x ^ (L - s) := hθN
        _ = x ^ (1 + δ' - s) * x ^ (L - 1 - δ') := e.symm
        _ ≤ x ^ (1 + δ' - s) * ((r : ℝ) * x ^ (L - 1 - δ')) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX0.le hr1R) hpos
    have hxy : x * x ^ y = x ^ (1 + y) := by rw [Real.rpow_add hx0, Real.rpow_one]
    have h2 : x ^ (1 + δ' - s) ≤ x ^ (1 + y) * θ := by
      rw [hθdef, ← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h3 : 3 ≤ x ^ (1 + y) := by
      calc (3 : ℝ) ≤ x ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hx3
        _ ≤ x ^ (1 + y) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h4 : x ^ (1 + y) * θ ≤ x ^ (1 + y) * (1 / 9) := mul_le_mul_of_nonneg_left hθ9 (by positivity)
    rw [hxy]
    linarith
  have hNF : 2 * (x * x ^ y * ((r : ℝ) * (1 + θ) ^ 3 * x ^ (L + c) / (θ * N₁))) ≤ NF := by
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hρ3 : (1 + θ) ^ 3 ≤ 8 := by
      calc (1 + θ) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
        _ = 8 := by norm_num
    have hbase : (r : ℝ) * (1 + θ) ^ 3 * x ^ (L + c) / (θ * N₁) ≤ 16 * r * x ^ (s + c) := by
      rw [div_le_iff₀ (by positivity)]
      have hsc' : x ^ (s + c) * x ^ (L - s) = x ^ (L + c) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      calc (r : ℝ) * (1 + θ) ^ 3 * x ^ (L + c) ≤ r * 8 * x ^ (L + c) := by gcongr
        _ = 16 * r * x ^ (s + c) * (x ^ (L - s) / 2) := by rw [← hsc']; ring
        _ ≤ 16 * r * x ^ (s + c) * (θ * N₁) := by gcongr
    have h1 : x * x ^ y * ((r : ℝ) * (1 + θ) ^ 3 * x ^ (L + c) / (θ * N₁)) ≤ 16 * r * x ^ L := by
      have hexp : x * x ^ y * x ^ (s + c) ≤ x ^ L := by
        have : x * x ^ y * x ^ (s + c) = x ^ (1 + y + (s + c)) := by
          rw [Real.rpow_add hx0 (1 + y) (s + c), Real.rpow_add hx0 1 y, Real.rpow_one]
        rw [this]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      calc x * x ^ y * ((r : ℝ) * (1 + θ) ^ 3 * x ^ (L + c) / (θ * N₁)) ≤ x * x ^ y * (16 * r * x ^ (s + c)) :=
            mul_le_mul_of_nonneg_left hbase (by positivity)
        _ = 16 * r * (x * x ^ y * x ^ (s + c)) := by ring
        _ ≤ 16 * r * x ^ L := by gcongr
    have hxL10 : 0 < x ^ (L + 1) := Real.rpow_pos_of_pos hx0 _
    have h3 : (16 * (r : ℝ) + 3) * x ^ L ≤ x ^ (L + 1) := by
      calc (16 * (r : ℝ) + 3) * x ^ L ≤ x ^ (1 / 3 : ℝ) * x ^ L := by gcongr
        _ = x ^ (1 / 3 + L) := by rw [← Real.rpow_add hx0]
        _ ≤ x ^ (L + 1) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h3' : 3 * x ^ (L + 1) ≤ x ^ (L + 2) := by
      have : x ^ (L + 2) = x ^ (L + 1) * x := by
        rw [← Real.rpow_add_one hx0.ne']; congr 1; ring
      rw [this]
      nlinarith
    have h4 : x ^ (L + 2) - 1 ≤ (NF : ℝ) := by
      have := Nat.sub_one_lt_floor (x ^ (L + 2))
      linarith
    linarith
  -- the products
  have hY₀ : 0 < x ^ e₀ := Real.rpow_pos_of_pos hx0 _
  have hpos₁ : ∀ y ∈ Y₁, 1 ≤ ∏ i, y i := by
    intro y hy
    refine Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    have h := ht₁ i (y i) (Fintype.mem_piFinset.1 (hY₁ hy) i)
    intro h0; rw [h0, Nat.cast_zero] at h; linarith
  have hpos₂ : ∀ y ∈ Y₂, 1 ≤ ∏ i, y i := by
    intro y hy
    refine Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    have h := ht₂ i (y i) (Fintype.mem_piFinset.1 (hY₂ hy) i)
    intro h0; rw [h0, Nat.cast_zero] at h; linarith
  -- the comparisons, with the cut-off itself off the family
  have hIb : ∀ j y₁ y₂, 0 ≤ (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) ∧
      (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) ≤ 1 := by
    intro j y₁ y₂
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨G_nonneg hθ0 hθΛ _, G_le_one _⟩
  have hIGb : ∀ j y₁ y₂, |(if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))) -
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i))| ≤
      G θ θ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ) := by
    intro j y₁ y₂
    by_cases hy : y₁ ∈ Y₁ ∧ y₂ ∈ Y₂
    · rw [ite_eq_left hy]
      have hu : cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) ≤ Λ :=
        (hΛ j y₁ hy.1 y₂ hy.2).trans (by rw [hΛdef]; linarith)
      exact SieveFamily.abs_ind_sub_G_le hθ0 (by linarith) hu (Pr j y₁ y₂) (hPr j y₁ y₂)
    · rw [ite_eq_right hy, sub_self, abs_zero]
      exact G_nonneg hθ0 (by linarith) _
  have hreg' : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∏ j, (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i)))) ≠ 0 →
      ((∏ i, y₁ i : ℕ) : ℝ) * fmax ≤ x ^ (L - 1 - a) ∧
        ((∏ i, y₁ i : ℕ) : ℝ) * fmax * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤ x ^ (L + c) ∧
        x ^ (L - 1 - δ') ≤ ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ) := by
    intro y₁ hy₁ y₂ hy₂ hne
    refine hreg y₁ hy₁ y₂ hy₂ fun j => ?_
    by_contra hj
    apply hne
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [ite_eq_left ⟨hy₁, hy₂⟩, ite_eq_right hj]
  have hη1 : θ ≤ 1 := by linarith
  have hfam := leaves_family_wide (q := q) a' ha' (N₁ := N₁) (N₂ := N₂) hN hN₁ Y₁ Y₂ (fun y => ∏ i, y i)
    (fun y => ∏ i, y i) hpos₁ hpos₂
    (fun j y₁ y₂ => if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i)))
    (fun _ => G θ Λ) (fun _ u => G θ θ (u + θ)) (fun _ => hGc) (fun _ => hGi) (fun _ => hGf) (fun _ => hMc)
    (fun _ => hMi) (fun _ => hMfr) (fun j y₁ => cc j + ∑ i, e₁ j i * Real.log (y₁ i))
    (fun j y₂ => ∑ i, e₂ j i * Real.log (y₂ i)) hIb (fun _ u => ⟨G_nonneg hθ0 hθΛ u, G_le_one u⟩) hIGb
    R S₁ f₁ l₁ hf₁ hR₁ S₂ f₂ l₂ hf₂ hR₂ hfm₁ hfm₂ (Mf := x ^ c₁) (M₂ := x ^ c₁) (by positivity) hMf₁ hMf₂ hM₂
    hF (ρ := 1 + θ) (η := θ) (by linarith) hθ0 hη1 hr1 (X₁ := x ^ (L - 1 - a)) (X₂ := x ^ (L + c))
    (X₃ := x ^ (L - 1 - δ')) (Y := x ^ y) (by positivity) hy1 hcut hstep hNF hreg'
  beta_reduce at hfam
  rw [← hxdef] at hfam
  -- on the family, the weights are the comparisons'
  have hcI : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, (∏ j, (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
      G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i)))) =
      ∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0) :=
    fun y₁ hy₁ y₂ hy₂ => Finset.prod_congr rfl fun j _ => ite_eq_left ⟨hy₁, hy₂⟩
  have hc0 : ∀ y₁ y₂, 0 ≤ ∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0) := fun y₁ y₂ =>
    Finset.prod_nonneg fun j _ => by split_ifs <;> norm_num
  have hc1 : ∀ y₁ y₂, ∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0) ≤ 1 := fun y₁ y₂ =>
    Finset.prod_le_one₀ (fun j _ => by split_ifs <;> norm_num) fun j _ => by split_ifs <;> norm_num
  set K := K₁ + K₂ with hKdef
  have hB0 : 0 ≤ B := by linarith
  have hBK : 1 ≤ B ^ K := one_le_pow₀ hB
  have hCd0 : 0 ≤ Cd := by linarith
  -- the exponents
  have hsκ' : s * (4 * (J₀ + 6)) ≤ κ := (le_div_iff₀ (by positivity)).1 hsκ
  -- the leaves' weights: `Σ c/d ≤ B^K` and `Σ c ≤ x^{L−1/2}B^K`
  have hSd : ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) /
      (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) ≤ B ^ K :=
    box_weight_le t₁ t₂ Y₁ Y₂ hY₁ hY₂ hB0 hB₁ hB₂ _ hc1
  have hSc : ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) ≤ x ^ (L - 1 / 2) * B ^ K := by
    calc ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0))
        ≤ ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, x ^ (L - 1 / 2) * ((∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) /
            (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun y₁ hy₁ => Finset.sum_le_sum fun y₂ hy₂ => ?_
          have hd0 : (0 : ℝ) < (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) := by
            have := hpos₁ y₁ hy₁; have := hpos₂ y₂ hy₂; positivity
          by_cases hall : ∀ j, Pr j y₁ y₂
          · obtain ⟨h1, h2, -⟩ := hreg y₁ hy₁ y₂ hy₂ hall
            have hd : (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) ≤ x ^ (L - 1 / 2) := by
              have hp₁ : (1 : ℝ) ≤ ((∏ i, y₁ i : ℕ) : ℝ) := by exact_mod_cast hpos₁ y₁ hy₁
              have h1' : ((∏ i, y₁ i : ℕ) : ℝ) ≤ x ^ (L - 1 - a) :=
                le_trans (le_mul_of_one_le_right (by positivity) hfmax) h1
              have h2' : ((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2 ≤ x ^ (L + c) :=
                le_trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hfmax)
                  (by positivity)) h2
              have hsq : ((((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ)) ^ 2 ≤ (x ^ (L - 1 / 2)) ^ 2 := by
                rw [Nat.cast_mul]
                calc (((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ)) ^ 2 =
                    ((∏ i, y₁ i : ℕ) : ℝ) * (((∏ i, y₁ i : ℕ) : ℝ) * ((∏ i, y₂ i : ℕ) : ℝ) ^ 2) := by ring
                  _ ≤ x ^ (L - 1 - a) * x ^ (L + c) := mul_le_mul h1' h2' (by positivity) (by positivity)
                  _ ≤ (x ^ (L - 1 / 2)) ^ 2 := by
                      rw [← Real.rpow_add hx0, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
                      exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
              exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
            rw [mul_div_assoc', le_div_iff₀ hd0]
            exact (mul_le_mul_of_nonneg_left hd (hc0 y₁ y₂)).trans_eq (mul_comm _ _)
          · have : (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) = 0 := by
              obtain ⟨j, hj⟩ := not_forall.1 hall
              exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
            rw [this, zero_div, mul_zero]
      _ = x ^ (L - 1 / 2) * ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) /
            (((∏ i, y₁ i) * ∏ i, y₂ i : ℕ) : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y₁ _ => (Finset.mul_sum _ _ _).symm
      _ ≤ x ^ (L - 1 / 2) * B ^ K := mul_le_mul_of_nonneg_left hSd (by positivity)
  -- the target power `P = x^{L−3s/4}/φ(q)`
  set P : ℝ := x ^ (L - 3 * s / 4) / (q.totient : ℝ) with hP
  have hP0 : 0 < P := by rw [hP]; positivity
  have hPa : ∀ α β : ℝ, α + β ≤ L - 3 * s / 4 → x ^ α * x ^ β / (q.totient : ℝ) ≤ P := by
    intro α β h
    rw [hP, ← Real.rpow_add hx0]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1 h) hφ0.le
  have hPb : ∀ α β : ℝ, α + β ≤ L - 3 * s / 4 → x ^ α * x ^ β / x ≤ P := fun α β h =>
    (div_le_div_of_nonneg_left (by positivity) hφ0 hφx).trans (hPa α β h)
  have hlg : 1 ≤ Real.log x ^ 2 := by
    have : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    exact one_le_pow₀ this
  -- the three parts against `x^{L−s/4}/φ(q)`
  have key : ∀ A₀ Bb Cc M₀ : ℝ, A₀ ≤ M₀ + (15 + 2 * Cd) * B ^ K * P →
      Bb ≤ 36 * L ^ 2 * (J₀ + 1) * Cm ^ J₀ * (√(816 * Cd2) + 16 + 4 * Cd2) * Real.log x ^ 2 * P →
      Cc ≤ 416 * J₀ * B ^ K * P → A₀ + Bb + Cc ≤ M₀ + (q.totient : ℝ)⁻¹ * x ^ (L - s / 4) := by
    intro A₀ Bb Cc M₀ hA hBb hCc
    have hfin' : Ctot * Real.log x ^ 2 * P ≤ (q.totient : ℝ)⁻¹ * x ^ (L - s / 4) := by
      calc Ctot * Real.log x ^ 2 * P = Ctot * Real.log x ^ 2 * x ^ (L - 3 * s / 4) / q.totient := by
            rw [hP]; ring
        _ ≤ x ^ (L - s / 4) / q.totient := div_le_div_of_nonneg_right hfin hφ0.le
        _ = (q.totient : ℝ)⁻¹ * x ^ (L - s / 4) := by ring
    rw [hCtot] at hfin'
    have h1 := mul_le_mul_of_nonneg_left hlg (by positivity : (0 : ℝ) ≤ (15 + 2 * Cd) * B ^ K * P)
    have h3 := mul_le_mul_of_nonneg_left hlg (by positivity : (0 : ℝ) ≤ 416 * J₀ * B ^ K * P)
    linarith only [hA, hBb, hCc, hfin', h1, h3]
  -- the near-boundary pieces, per comparison
  have hj₁ : ∀ j : Fin J, ∑ z ∈ Y₁ ×ˢ S₁, ∑ y₂ ∈ Y₂, (1 + θ) * (1 + θ) ^ 2 * (N₂ : ℝ) * |l₁ z.2| *
      G θ θ (cc j + ∑ i, e₁ j i * Real.log (z.1 i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ) /
      (((∏ i, z.1 i) * f₁ z.2 * ∏ i, y₂ i : ℕ) : ℝ) ≤
      (1 + θ) * (1 + θ) ^ 2 * N₂ * (∑ σ ∈ S₁, |l₁ σ| / f₁ σ) * ((12 * θ + 1 / x ^ e₀) * B ^ (K - 1)) := by
    intro j
    refine (le_of_eq (nb_regroup Y₁ Y₂ S₁ (fun y => ∏ i, y i) (fun y => ∏ i, y i) f₁ l₁
      ((1 + θ) * (1 + θ) ^ 2 * N₂)
      (fun y₁ y₂ => G θ θ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ)))).trans ?_
    exact mul_le_mul_of_nonneg_left (pivot_two_le t₁ t₂ Y₁ Y₂ hY₁ hY₂ hY₀ ht₁ ht₂ hB0 hB₁ hB₂ hθ0 hθ9 (cc j)
      (e₁ j) (e₂ j) (hpiv j)) (by positivity)
  have hj₂ : ∀ j : Fin J, ∑ z ∈ Y₁ ×ˢ S₂, ∑ y₂ ∈ Y₂, (1 + θ) * (1 + θ) ^ 2 * (N₂ : ℝ) * |l₂ z.2| *
      G θ θ (cc j + ∑ i, e₁ j i * Real.log (z.1 i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ) /
      (((∏ i, z.1 i) * f₂ z.2 * ∏ i, y₂ i : ℕ) : ℝ) ≤
      (1 + θ) * (1 + θ) ^ 2 * N₂ * (∑ τ ∈ S₂, |l₂ τ| / f₂ τ) * ((12 * θ + 1 / x ^ e₀) * B ^ (K - 1)) := by
    intro j
    refine (le_of_eq (nb_regroup Y₁ Y₂ S₂ (fun y => ∏ i, y i) (fun y => ∏ i, y i) f₂ l₂
      ((1 + θ) * (1 + θ) ^ 2 * N₂)
      (fun y₁ y₂ => G θ θ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i) + θ)))).trans ?_
    exact mul_le_mul_of_nonneg_left (pivot_two_le t₁ t₂ Y₁ Y₂ hY₁ hY₂ hY₀ ht₁ ht₂ hB0 hB₁ hB₂ hθ0 hθ9 (cc j)
      (e₁ j) (e₂ j) (hpiv j)) (by positivity)
  have hCθ : (1 + θ) * (1 + θ) ^ 2 * (N₂ : ℝ) ≤ 16 * x ^ L := by
    calc (1 + θ) * (1 + θ) ^ 2 * (N₂ : ℝ) ≤ 2 * 2 ^ 2 * (2 * x ^ L) := by gcongr <;> linarith
      _ = 16 * x ^ L := by ring
  have hPv : (12 * θ + 1 / x ^ e₀) * B ^ (K - 1) ≤ 13 * θ * B ^ K := by
    have h1 : 1 / x ^ e₀ ≤ θ := by
      calc 1 / x ^ e₀ ≤ 1 / x ^ s := one_div_le_one_div_of_le (by positivity)
            (Real.rpow_le_rpow_of_exponent_le hx1 hse)
        _ = θ := by rw [hθdef, Real.rpow_neg hx0.le, one_div]
    exact mul_le_mul (by linarith) (pow_le_pow_right₀ hB (Nat.sub_le K 1)) (by positivity) (by positivity)
  have hLcθ : x ^ L * x ^ c₁ * θ / (q.totient : ℝ) ≤ P := by
    rw [← Real.rpow_add hx0]
    exact hPa (L + c₁) (-s) (by linarith)
  have hJ' : (J : ℝ) ≤ J₀ := by exact_mod_cast hJ
  -- the transition term `Θ`
  have h30 : 0 ≤ (1 + θ) ^ 2 - 1 := by nlinarith
  have hΘ0 : 0 ≤ ((N₁ : ℝ) + N₂) * ((1 + θ) ^ 2 - 1) + 2 * θ * N₁ :=
    add_nonneg (mul_nonneg (by positivity) h30) (by positivity)
  have hΘ : ((N₁ : ℝ) + N₂) * ((1 + θ) ^ 2 - 1) + 2 * θ * N₁ ≤ 11 * x ^ (L - s) := by
    have h3 : (1 + θ) ^ 2 - 1 ≤ 3 * θ := by nlinarith
    have h4 : ((N₁ : ℝ) + N₂) * ((1 + θ) ^ 2 - 1) ≤ 3 * x ^ L * (3 * θ) :=
      mul_le_mul (by linarith) h3 h30 (by positivity)
    have h5 : 2 * θ * (N₁ : ℝ) ≤ 2 * θ * x ^ L := by gcongr
    have hθL : θ * x ^ L = x ^ (L - s) := by
      rw [hθdef, ← Real.rpow_add hx0]; congr 1; ring
    linarith
  -- the bilinear part's ingredients
  have hk₁ : ((blk (1 + θ) ⌊x ^ (L - 1 - a)⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L * x ^ s * Real.log x := by
    push_cast
    exact blk_floor_le hx3 hs0 hL.le (Real.one_le_rpow hx1 (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have hk₂ : ((blk (1 + θ) ⌊√(x ^ (L + c))⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L * x ^ s * Real.log x := by
    push_cast
    have h1 : 1 ≤ x ^ (L + c) := Real.one_le_rpow hx1 (by linarith)
    have hsq : √(x ^ (L + c)) = x ^ ((L + c) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; congr 1; ring
    exact blk_floor_le hx3 hs0 hL.le (Real.one_le_sqrt.2 h1)
      (hsq.le.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)))
  have hMx1 : 1 ≤ Cm * x ^ s := by nlinarith
  have hFN : (∏ j : Fin J, ∫ t, ‖𝓕 (fun u => ((G θ Λ u : ℝ) : ℂ)) t‖) +
      ∑ j : Fin J, ∫ t, ‖𝓕 (fun u => ((G θ θ (u + θ) : ℝ) : ℂ)) t‖ ≤ (J₀ + 1) * (Cm * x ^ s) ^ J₀ :=
    masses_le hJ _ _ hMx1 (fun j => integral_nonneg fun _ => norm_nonneg _) (fun j => hGm.trans hmB1)
      (fun j => hMm.trans hmB2)
  have hFN0 : 0 ≤ (∏ j : Fin J, ∫ t, ‖𝓕 (fun u => ((G θ Λ u : ℝ) : ℂ)) t‖) +
      ∑ j : Fin J, ∫ t, ‖𝓕 (fun u => ((G θ θ (u + θ) : ℝ) : ℂ)) t‖ :=
    add_nonneg (Finset.prod_nonneg fun j _ => integral_nonneg fun _ => norm_nonneg _)
      (Finset.sum_nonneg fun j _ => integral_nonneg fun _ => norm_nonneg _)
  have hU : bdUW q (1 + θ) θ N₁ N₂ r F (x ^ (L - 1 - a)) (x ^ (L + c)) (x ^ (L - 1 - δ')) (x ^ y) ≤
      √(816 * Cd2) * x ^ (L - 1 - ((κ - y - s) - 0 - s) / 2) + 16 * x ^ (L - 2) +
        4 * Cd2 * x ^ (L - 1 / 2 + s) / (q.totient : ℝ) := by
    have h := bdUW_le_pow q hx3 hL hδ' haL hκ.le hκ1 hκ3 hs0 hy0 hr4 hFR hdq
    have he : L - 1 - ((κ - y - s) - 0 - s) / 2 = L - 1 - (κ - y - 2 * s) / 2 := by ring
    rw [hCd2, he]
    exact h
  have hU0 : 0 ≤ bdUW q (1 + θ) θ N₁ N₂ r F (x ^ (L - 1 - a)) (x ^ (L + c)) (x ^ (L - 1 - δ')) (x ^ y) :=
    bdUW_nonneg q hθ0 N₁ N₂ r F hy1.le
  have e1 : (J₀ + 2) * s + 2 * c₁ + (L - 1 - ((κ - y - s) - 0 - s) / 2) ≤ L - 3 * s / 4 - 1 := by linarith
  have e2 : (J₀ + 2) * s + 2 * c₁ + (L - 2) ≤ L - 3 * s / 4 - 1 := by linarith
  have e3 : (J₀ + 2) * s + 2 * c₁ + (L - 1 / 2 + s) ≤ L - 3 * s / 4 := by linarith
  -- assemble
  have hcI' : ∀ g : (Fin K₁ → ℕ) → (Fin K₂ → ℕ) → ℝ,
      ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if y₁ ∈ Y₁ ∧ y₂ ∈ Y₂ then (if Pr j y₁ y₂ then (1 : ℝ) else 0) else
        G θ Λ (cc j + ∑ i, e₁ j i * Real.log (y₁ i) + ∑ i, e₂ j i * Real.log (y₂ i)))) * g y₁ y₂ =
      ∑ y₁ ∈ Y₁, ∑ y₂ ∈ Y₂, (∏ j, (if Pr j y₁ y₂ then (1 : ℝ) else 0)) * g y₁ y₂ :=
    fun g => Finset.sum_congr rfl fun y₁ hy₁ => Finset.sum_congr rfl fun y₂ hy₂ => by rw [hcI y₁ hy₁ y₂ hy₂]
  rw [hcI', hcI'] at hfam
  refine hfam.trans (key _ _ _ _ ?_ ?_ ?_)
  · -- the main term and the transition
    rw [split_main, add_assoc]
    refine add_le_add le_rfl ((add_le_add ?_ ?_).trans (le_of_eq (by ring :
      11 * B ^ K * P + (4 + 2 * Cd) * B ^ K * P = (15 + 2 * Cd) * B ^ K * P)))
    · calc _ ≤ x ^ c₁ * (11 * x ^ (L - s)) / x * B ^ K := by gcongr
        _ = 11 * B ^ K * (x ^ c₁ * x ^ (L - s) / x) := by ring
        _ ≤ 11 * B ^ K * P := mul_le_mul_of_nonneg_left (hPb _ _ (by linarith)) (by positivity)
    · calc _ ≤ (4 * x ^ (1 / 4 : ℝ) / x + 2 * x ^ (1 / 4 : ℝ) * (Cd * x ^ s / q.totient)) *
              (x ^ (L - 1 / 2) * B ^ K) := by
            gcongr
        _ = 4 * B ^ K * (x ^ (1 / 4 : ℝ) * x ^ (L - 1 / 2) / x) +
            2 * Cd * B ^ K * (x ^ ((1 / 4 : ℝ) + s) * x ^ (L - 1 / 2) / q.totient) := by
            rw [Real.rpow_add hx0]; ring
        _ ≤ 4 * B ^ K * P + 2 * Cd * B ^ K * P :=
            add_le_add (mul_le_mul_of_nonneg_left (hPb _ _ (by linarith)) (by positivity))
              (mul_le_mul_of_nonneg_left (hPa _ _ (by linarith)) (by positivity))
        _ = (4 + 2 * Cd) * B ^ K * P := by ring
  · -- the bilinear part
    rw [Nat.cast_mul]
    refine (bil_le hx3 hφ0 hφx (by linarith) (by positivity) hk₁ (by positivity) hk₂ hFN0 hFN (by positivity)
      le_rfl (by positivity) le_rfl hU0 hU hCd20 (by norm_num) (by linarith) e1 e2 e3).trans (le_of_eq ?_)
    rw [hP]; ring
  · -- the near-boundary masses
    refine le_trans (add_le_add
      (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj₁ j) (by positivity))
      (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj₂ j) (by positivity))) ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hprod : (J : ℝ) * ((1 + θ) * (1 + θ) ^ 2 * N₂ * ((∑ σ ∈ S₁, |l₁ σ| / f₁ σ + ∑ τ ∈ S₂, |l₂ τ| / f₂ τ) *
        ((12 * θ + 1 / x ^ e₀) * B ^ (K - 1)))) ≤ J₀ * (16 * x ^ L * (x ^ c₁ * (13 * θ * B ^ K))) :=
      mul_le_mul hJ' (mul_le_mul hCθ (mul_le_mul hV hPv (by positivity) (by positivity)) (by positivity)
        (by positivity)) (by positivity) (by positivity)
    calc _ = 2 * (q.totient : ℝ)⁻¹ * ((J : ℝ) * ((1 + θ) * (1 + θ) ^ 2 * N₂ *
          ((∑ σ ∈ S₁, |l₁ σ| / f₁ σ + ∑ τ ∈ S₂, |l₂ τ| / f₂ τ) * ((12 * θ + 1 / x ^ e₀) * B ^ (K - 1))))) := by
          ring
      _ ≤ 2 * (q.totient : ℝ)⁻¹ * (J₀ * (16 * x ^ L * (x ^ c₁ * (13 * θ * B ^ K)))) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 416 * J₀ * B ^ K * (x ^ L * x ^ c₁ * θ / q.totient) := by ring
      _ ≤ 416 * J₀ * B ^ K * P := mul_le_mul_of_nonneg_left hLcθ (by positivity)

end SieveTypeIBAsymWide

#print axioms SieveTypeIBAsymWide.bdUW_le_pow
#print axioms SieveTypeIBAsymWide.leaves_ib_wide
