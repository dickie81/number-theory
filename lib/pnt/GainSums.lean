import DesignOrbits

/-!
# The gain's sums

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain`; module M-G7s of the gain's numbers): the
closed-form constant and the Stage-2 clause that the gain's numbers are stated against, the growth package that
absorbs the tile parameters' constants `10^{O(1/ε)}`, and the elementary sums over primes that the losses and the
errors read.

**Definitions.** The constant `c_G = x^{1+2ε}·|A|·e^{x^ε}` (`Setting.cGform`); the clause G1,
`Σ_{p ∈ PR} (log p/p)·|badTops p| ≤ |TT|·x^{−2+ε}` (`SharpDesign.FewBadTops`), as M-G4 will add it to `Adm`; and the
growth package `GainBig ε x` (with `k = designK x ε`): `(G′ + 2)·x^{ε/3} + 1000 log x ≤ x^ε/8`,
`N₁ + r ≤ x^{1/8}` and `10⁹ ≤ x^{ε/8}`.

**The growth package holds eventually** (`gainBig_eventually`): for every `ε > 0` some `x₀` has `GainBig ε x` at
every `x ≥ x₀`. The parameters `G′`, `N₁`, `r` of `tilePar` do not read `k`, and `r = ⌈8(h* + 2)/ε⌉ + 1` does not
read `x` (`tilePar_r`). With `u ≤ x^{ε/8} + 1` (`tilePar_u_le`) and `M₀ ≤ A₀·log x + 1` (`tilePar_M₀_le`,
`A₀ = (h* + 3)·10^{6r+1}`), `G′ = (M₀ + 5)(6r + 1)u ≤ C₁·log x·x^{ε/8}` once `log x ≥ 1`, and `G′δ₁ ≤ C₁·log x` as
`uδ₁ ≤ 2`; so `(G′ + 2)x^{ε/3} ≤ (C₁ + 2)·log x·x^{11ε/24}` and `N₁ + r ≤ C₂·log x`, and `log x = o(x^s)` for every
`s > 0` (`eventually_log_le_rpow`, from `isLittleO_log_rpow_atTop`) gives the three clauses.

**Elementary sums** (crude, which is all the losses need: their budget has `x^{1/2}` to spare).
* `card_le_of_mem_Icc`: a set of integers in `[α, β]` has at most `β − α + 1` elements;
* `sum_log_le_of_mem`: `Σ log n ≤ Y log Y` over integers in `[1, Y]`;
* `sum_log_div_le_of_mem`: `Σ log n/n ≤ log Y·(1 + log Y)` over integers in `[1, Y]` (`sum_Icc_one_div_le`);
* `sum_log_div_sq_le_of_mem`: `Σ log n/n² ≤ 2 log Y/P₀` over integers in `[P₀, Y]` (`sum_Ioo_inv_sq_le`).

**The band** (`sum_band_le`, `Setting.sum_inBand_le`). For `Y ≥ 1`, `0 ≤ ρ ≤ 1/2` and `P₀ ≥ e`, the integers
`n ≥ P₀` with some power `n^i ∈ [Y(1 − ρ), Y(1 + ρ)]`, `i ≥ 1`, have `Σ log n/n ≤ (8ρ + 1/P₀)·log 2Y`. The exponent is
at most `I = ⌊log 2Y/log P₀⌋`, as `P₀^i ≤ 2Y`; for each `i` the integers lie in `[α, β]`,
`α = (Y(1 − ρ))^{1/i}`, `β = (Y(1 + ρ))^{1/i}`, so there are at most `β − α + 1` of them, each with
`log n/n ≤ min(log β/α, log P₀/P₀)` (`log t/t` decreases on `[e, ∞)`); and `β/α ≤ (1 + 4ρ)^{1/i} ≤ 1 + 4ρ/i`
(Bernoulli), `log β ≤ log 2Y/i`. So the `i`-th part is at most `4ρ·log 2Y/i² + log P₀/P₀`, and
`Σ_i 1/i² ≤ 2`, `I·log P₀/P₀ ≤ log 2Y/P₀`. At the design's parameters (`Y = X′`, `ρ = ρ_B`, `P₀ = p₀`) this is the
band of the candidates (`InBand`).

**Odd orders are large** (`Setting.TwoAdic.le_of_odd`): at a non-split prime `p` with `ord(c·[p]_A)` odd,
`c = twA κ`, `4|A|/ord κ ≤ p + 1`. The image of `c·[p]_A` in `H_e = (ℤ/2^{e+2})ˣ/±1` (which kills `c`) has odd order
dividing `|H_e| = 2^e`, so it is trivial: `p ≡ ±1 (mod 2^{e+2})`, `p + 1 ≥ 2^{e+2}`, and
`2^{e+2} ≥ 4|A₀| = 4|A|/ord κ` (`TwoAdic.card_A₀_le`, `card_A_eq`), as in `Setting.TwoAdic.sum_log_div_le`.

**Against the spec.**
* `GainBig` relaxes `N₁ ≤ x^{ε/1000}` to `N₁ + r ≤ x^{1/8}`, as the study does (`N₁ ≈ 10^{6r}·log x`).
* The elementary sums are stated for any set of integers in a range (the primes are a case), with the crude constants
  above: `Y log Y` for `(Y + 1)log(Y + 1)`, `2 log Y/P₀` for `log Y/(P₀ − 1)`, `β − α + 1` for `θY + 1` (the count of
  `(Y, Y(1 + θ)]` is the case `α = Y`, `β = Y(1 + θ)`), and the band bound `(8ρ + 1/P₀)·log 2Y` for
  `3ρ log 2Y·(1 + log I) + I·log P₀/P₀`.
-/

open Finset Filter

namespace ZetaBalance

noncomputable section

/-! ## The constant, the clause G1, the growth package -/

/-- **The closed-form constant** `c_G = x^{1+2ε}·|A|·e^{x^ε}` (the gain spec's C4). -/
def Setting.cGform (S : Setting) (x ε : ℝ) : ℝ := x ^ (1 + 2 * ε) * Fintype.card S.A * scB x ε

/-- **(G1)**, the Stage-2 clause as M-G4 will add it to `Adm`: `Σ_{p ∈ PR} (log p/p)·|badTops p| ≤ |TT|·x^{−2+ε}`. -/
def SharpDesign.FewBadTops {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X) : Prop :=
  ∑ p ∈ S.PR κ x ε, (Real.log p / p) * ((Dg.badTops p).card : ℝ) ≤ Dg.TT.card * x ^ (-2 + ε)

/-- **The growth conditions of the gain's numbers**, eventually true in `x` at a fixed `ε` (`gainBig_eventually`): the
tile parameters `G′`, `N₁`, `r` of `tilePar` (at `k = designK x ε`, which they do not read) against powers of `x`. -/
structure GainBig (ε x : ℝ) : Prop where
  /-- `(G′ + 2)·x^{ε/3} + 1000 log x ≤ x^ε/8`: the factors `Q_p = p^{G′}` of the depth, for `p < X′`. -/
  G'_le : (((tilePar x ε (designK x ε)).G' : ℝ) + 2) * x ^ (ε / 3) + 1000 * Real.log x ≤ x ^ ε / 8
  /-- `N₁ + r ≤ x^{1/8}`: the polynomial factors of the allowances. -/
  N₁r_le : ((tilePar x ε (designK x ε)).N₁ : ℝ) + (tilePar x ε (designK x ε)).r ≤ x ^ (1 / 8 : ℝ)
  /-- `10⁹ ≤ x^{ε/8}`: the absolute constants of the losses and the errors. -/
  C_le : (10 : ℝ) ^ 9 ≤ x ^ (ε / 8)

/-- **The cell length** `u = ⌈1/δ₁⌉ ≤ x^{ε/8} + 1`. -/
theorem tilePar_u_le {x ε : ℝ} (k : ℕ) (hx : 0 < x) : ((tilePar x ε k).u : ℝ) ≤ x ^ (ε / 8) + 1 := by
  have h : (scδ₁ x ε)⁻¹ = x ^ (ε / 8) := by rw [scδ₁, Real.rpow_neg hx.le, inv_inv]
  show ((⌈(scδ₁ x ε)⁻¹⌉₊ : ℕ) : ℝ) ≤ _
  rw [h]
  exact (Nat.ceil_lt_add_one (Real.rpow_nonneg hx.le _)).le

/-- **The run length** `M₀ ≤ (h* + 3)·10^{6r+1}·log x + 1`. -/
theorem tilePar_M₀_le {x ε : ℝ} (k : ℕ) (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    ((tilePar x ε k).M₀ : ℝ) ≤ ((2 + 8 * ε) + 3) * 10 ^ (6 * (tilePar x ε k).r + 1) * Real.log x + 1 :=
  (Nat.ceil_lt_add_one (by have := Real.log_nonneg hx; positivity)).le

/-- **The spacing window** `G′ = (M₀ + 5)(6r + 1)u`. -/
theorem tilePar_G' (x ε : ℝ) (k : ℕ) :
    (tilePar x ε k).G' = ((tilePar x ε k).M₀ + 5) * ((6 * (tilePar x ε k).r + 1) * (tilePar x ε k).u) := rfl

/-- **The window count** `N₁ = ⌈max(6e·G′δ₁, (h* + 3)·log₂ x)⌉ + 1`. -/
theorem tilePar_N₁ (x ε : ℝ) (k : ℕ) :
    (tilePar x ε k).N₁ =
      ⌈max (6 * Real.exp 1 * (tilePar x ε k).G' * scδ₁ x ε) (((2 + 8 * ε) + 3) * Real.logb 2 x)⌉₊ + 1 := rfl

/-- **The rank `r = ⌈8(h* + 2)/ε⌉ + 1`** does not read `x` (nor `k`). -/
theorem tilePar_r (x ε : ℝ) (k : ℕ) : (tilePar x ε k).r = ⌈8 * ((2 + 8 * ε) + 2) / ε⌉₊ + 1 := rfl

/-- **`log x ≤ c·x^s` eventually**, for `c, s > 0` (`isLittleO_log_rpow_atTop`). -/
theorem eventually_log_le_rpow {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∀ᶠ x in atTop, Real.log x ≤ c * x ^ s := by
  filter_upwards [(isLittleO_log_rpow_atTop hs).bound hc, eventually_gt_atTop 0] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hx
  exact (le_abs_self _).trans hx

/-- **The growth package holds eventually**: for `ε > 0`, `GainBig ε x` at every large `x`. With
`r₀ = ⌈8(h* + 2)/ε⌉ + 1`, `A₀ = (h* + 3)·10^{6r₀+1}`, `B₀ = 6r₀ + 1` and `C₁ = 2B₀(A₀ + 6)`: `G′ ≤ C₁·log x·x^{ε/8}`
and `G′δ₁ ≤ C₁·log x` for `x ≥ e`, so `(G′ + 2)x^{ε/3} ≤ (C₁ + 2)·log x·x^{11ε/24} ≤ x^ε/16` once
`log x ≤ x^{13ε/24}/(16(C₁ + 2))`, `1000 log x ≤ x^ε/16` once `log x ≤ x^ε/16000`, and
`N₁ + r ≤ (18C₁ + 2(h* + 3) + 2 + r₀)·log x ≤ x^{1/8}` eventually. -/
theorem gainBig_eventually {ε : ℝ} (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → GainBig ε x := by
  set r₀ : ℕ := ⌈8 * ((2 + 8 * ε) + 2) / ε⌉₊ + 1
  set A₀ : ℝ := ((2 + 8 * ε) + 3) * 10 ^ (6 * r₀ + 1)
  set B₀ : ℝ := 6 * r₀ + 1
  set C₁ : ℝ := 2 * B₀ * (A₀ + 6)
  set C₂ : ℝ := 18 * C₁ + 2 * ((2 + 8 * ε) + 3) + 2 + r₀ with hC₂
  have hA₀ : 0 < A₀ := by positivity
  have hB₀ : 0 < B₀ := by positivity
  have hC₁ : 0 < C₁ := by positivity
  have hC₂0 : 0 < C₂ := by positivity
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 ((eventually_ge_atTop (Real.exp 1)).and
    ((eventually_log_le_rpow (c := 1 / (16 * (C₁ + 2))) (s := 13 * ε / 24) (by positivity) (by positivity)).and
    ((eventually_log_le_rpow (c := 1 / 16000) (s := ε) (by positivity) hε).and
    ((eventually_log_le_rpow (c := 1 / C₂) (s := 1 / 8) (by positivity) (by norm_num)).and
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 8)).eventually_ge_atTop ((10 : ℝ) ^ 9))))))
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx₀ x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp zero_le_one) h1
  have hlog : 1 ≤ Real.log x := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) h1
  have hxe : 1 ≤ x ^ (ε / 8) := Real.one_le_rpow hx1 (by positivity)
  have hr : (tilePar x ε (designK x ε)).r = r₀ := rfl
  have hu := tilePar_u_le (ε := ε) (designK x ε) hx0
  have hM := tilePar_M₀_le (designK x ε) hx1 hε.le
  rw [hr] at hM
  have hM' : ((tilePar x ε (designK x ε)).M₀ : ℝ) ≤ A₀ * Real.log x + 1 := hM
  have hG : ((tilePar x ε (designK x ε)).G' : ℝ) =
      ((tilePar x ε (designK x ε)).M₀ + 5) * (B₀ * (tilePar x ε (designK x ε)).u) := by
    rw [tilePar_G', hr]; push_cast; rfl
  have hM0 : (0 : ℝ) ≤ (tilePar x ε (designK x ε)).M₀ := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ (tilePar x ε (designK x ε)).u := Nat.cast_nonneg _
  -- `G′ ≤ C₁·log x·x^{ε/8}`
  have hG1 : ((tilePar x ε (designK x ε)).G' : ℝ) ≤ C₁ * Real.log x * x ^ (ε / 8) := by
    rw [hG]
    calc ((tilePar x ε (designK x ε)).M₀ + 5) * (B₀ * (tilePar x ε (designK x ε)).u : ℝ) ≤
        (A₀ * Real.log x + 6) * (B₀ * (2 * x ^ (ε / 8))) :=
          mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hB₀.le) (by positivity)
            (by positivity)
      _ ≤ ((A₀ + 6) * Real.log x) * (B₀ * (2 * x ^ (ε / 8))) := by gcongr; nlinarith
      _ = C₁ * Real.log x * x ^ (ε / 8) := by ring
  have hxx : x ^ (ε / 8) * x ^ (ε / 3) * x ^ (13 * ε / 24) = x ^ ε := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  refine ⟨?_, ?_, h5⟩
  · have hl0 : 0 ≤ Real.log x := by linarith
    have hx3 : 0 ≤ x ^ (ε / 3) := Real.rpow_nonneg hx0.le _
    have hG2 : ((tilePar x ε (designK x ε)).G' : ℝ) + 2 ≤ (C₁ + 2) * Real.log x * x ^ (ε / 8) := by
      nlinarith
    have hlx : (C₁ + 2) * Real.log x ≤ x ^ (13 * ε / 24) / 16 := by
      rw [show 1 / (16 * (C₁ + 2)) * x ^ (13 * ε / 24) = x ^ (13 * ε / 24) / 16 / (C₁ + 2) by
        field_simp] at h2
      rwa [le_div_iff₀ (by positivity), mul_comm] at h2
    calc (((tilePar x ε (designK x ε)).G' : ℝ) + 2) * x ^ (ε / 3) + 1000 * Real.log x ≤
        ((C₁ + 2) * Real.log x * x ^ (ε / 8)) * x ^ (ε / 3) + x ^ ε / 16 := by
          gcongr
          linarith
      _ ≤ (x ^ (13 * ε / 24) / 16 * x ^ (ε / 8)) * x ^ (ε / 3) + x ^ ε / 16 := by gcongr
      _ = x ^ ε / 8 := by rw [← hxx]; ring
  · -- `N₁ + r ≤ C₂·log x ≤ x^{1/8}`
    have hδ : 0 < scδ₁ x ε := Real.rpow_pos_of_pos hx0 _
    have huδ : ((tilePar x ε (designK x ε)).u : ℝ) * scδ₁ x ε ≤ 2 := by
      have h1' : x ^ (ε / 8) * scδ₁ x ε = 1 := by
        rw [scδ₁, ← Real.rpow_add hx0]; simp
      have h2' : scδ₁ x ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
      nlinarith
    have hGδ : ((tilePar x ε (designK x ε)).G' : ℝ) * scδ₁ x ε ≤ C₁ * Real.log x := by
      rw [hG]
      calc ((tilePar x ε (designK x ε)).M₀ + 5) * (B₀ * (tilePar x ε (designK x ε)).u) * scδ₁ x ε =
          ((tilePar x ε (designK x ε)).M₀ + 5) * B₀ * ((tilePar x ε (designK x ε)).u * scδ₁ x ε) := by ring
        _ ≤ (A₀ * Real.log x + 6) * B₀ * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hB₀.le) huδ (by positivity) (by positivity)
        _ ≤ ((A₀ + 6) * Real.log x) * B₀ * 2 := by gcongr; nlinarith
        _ = C₁ * Real.log x := by ring
    have hlog2 : Real.logb 2 x ≤ 2 * Real.log x := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      have := Real.log_two_gt_d9
      nlinarith
    have hlb : 0 ≤ Real.logb 2 x := Real.logb_nonneg one_lt_two hx1
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hmax : max (6 * Real.exp 1 * (tilePar x ε (designK x ε)).G' * scδ₁ x ε)
        (((2 + 8 * ε) + 3) * Real.logb 2 x) ≤ (18 * C₁ + 2 * ((2 + 8 * ε) + 3)) * Real.log x := by
      have hG0 : (0 : ℝ) ≤ ((tilePar x ε (designK x ε)).G' : ℝ) * scδ₁ x ε := by positivity
      refine max_le ?_ ?_
      · calc 6 * Real.exp 1 * (tilePar x ε (designK x ε)).G' * scδ₁ x ε =
            6 * Real.exp 1 * ((tilePar x ε (designK x ε)).G' * scδ₁ x ε) := by ring
          _ ≤ 6 * 3 * (C₁ * Real.log x) := by gcongr
          _ ≤ _ := by
            have h1' : 0 ≤ Real.log x := by linarith
            have h2' : 0 ≤ ε * Real.log x := by positivity
            linarith
      · have h1' := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ (2 + 8 * ε) + 3)
        have h2' : 0 ≤ C₁ * Real.log x := by positivity
        linarith
    have hmax0 : 0 ≤ max (6 * Real.exp 1 * (tilePar x ε (designK x ε)).G' * scδ₁ x ε)
        (((2 + 8 * ε) + 3) * Real.logb 2 x) := le_max_of_le_right (by positivity)
    have hN₁ : ((tilePar x ε (designK x ε)).N₁ : ℝ) ≤ (18 * C₁ + 2 * ((2 + 8 * ε) + 3)) * Real.log x + 2 := by
      rw [tilePar_N₁]
      push_cast
      linarith [Nat.ceil_lt_add_one hmax0]
    have h4' : C₂ * Real.log x ≤ x ^ (1 / 8 : ℝ) := by
      rw [show 1 / C₂ * x ^ (1 / 8 : ℝ) = x ^ (1 / 8 : ℝ) / C₂ by ring, le_div_iff₀ hC₂0] at h4
      linarith
    rw [hr]
    have h5' : (2 + (r₀ : ℝ)) * 1 ≤ (2 + r₀) * Real.log x := mul_le_mul_of_nonneg_left hlog (by positivity)
    rw [hC₂] at h4'
    linarith

/-! ## Elementary sums -/

/-- **Counting integers in an interval**: a set of integers in `[α, β]`, `α ≤ β`, has at most `β − α + 1`
elements. -/
theorem card_le_of_mem_Icc {P : Finset ℕ} {α β : ℝ} (hαβ : α ≤ β) (hP : ∀ n ∈ P, α ≤ n ∧ (n : ℝ) ≤ β) :
    (P.card : ℝ) ≤ β - α + 1 := by
  rcases lt_or_ge β 0 with hβ | hβ
  · have : P = ∅ := eq_empty_of_forall_notMem fun n hn => by
      have := (hP n hn).2
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [this, card_empty, Nat.cast_zero]
    linarith
  have hsub : P ⊆ Icc ⌈α⌉₊ ⌊β⌋₊ := fun n hn =>
    mem_Icc.2 ⟨Nat.ceil_le.2 (hP n hn).1, Nat.le_floor (hP n hn).2⟩
  have h1 := card_le_card hsub
  rw [Nat.card_Icc] at h1
  have h2 : (⌊β⌋₊ : ℝ) ≤ β := Nat.floor_le hβ
  have h3 : α ≤ ⌈α⌉₊ := Nat.le_ceil α
  by_cases h : ⌈α⌉₊ ≤ ⌊β⌋₊ + 1
  · have h4 : (P.card : ℝ) ≤ ((⌊β⌋₊ + 1 - ⌈α⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub h] at h4
    push_cast at h4
    linarith
  · have h4 : P.card ≤ 0 := by omega
    have h5 : (P.card : ℝ) ≤ 0 := by exact_mod_cast h4
    linarith

/-- **`Σ log n ≤ Y log Y`** over a set of integers in `[1, Y]`. -/
theorem sum_log_le_of_mem {P : Finset ℕ} {Y : ℝ} (hY : 1 ≤ Y) (hP : ∀ n ∈ P, 1 ≤ n ∧ (n : ℝ) ≤ Y) :
    ∑ n ∈ P, Real.log n ≤ Y * Real.log Y := by
  have hc := card_le_of_mem_Icc (α := 1) hY fun n hn => ⟨by exact_mod_cast (hP n hn).1, (hP n hn).2⟩
  calc ∑ n ∈ P, Real.log n ≤ ∑ _n ∈ P, Real.log Y := sum_le_sum fun n hn =>
        Real.log_le_log (by exact_mod_cast (hP n hn).1) (hP n hn).2
    _ = P.card * Real.log Y := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Y * Real.log Y := mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg hY)

/-- **`Σ log n/n ≤ log Y·(1 + log Y)`** over a set of integers in `[1, Y]`, by the harmonic bound. -/
theorem sum_log_div_le_of_mem {P : Finset ℕ} {Y : ℝ} (hY : 1 ≤ Y) (hP : ∀ n ∈ P, 1 ≤ n ∧ (n : ℝ) ≤ Y) :
    ∑ n ∈ P, Real.log n / n ≤ Real.log Y * (1 + Real.log Y) := by
  have hL : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hH : ∑ k ∈ Icc 1 ⌊Y⌋₊, (1 : ℝ) / k ≤ 1 + Real.log Y := by
    have h1 : (0 : ℝ) < ⌊Y⌋₊ := by exact_mod_cast Nat.floor_pos.2 hY
    exact (sum_Icc_one_div_le _).trans (by gcongr; exact Nat.floor_le (by linarith))
  calc ∑ n ∈ P, Real.log n / n ≤ ∑ n ∈ P, Real.log Y * ((1 : ℝ) / n) := sum_le_sum fun n hn => by
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (hP n hn).1
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (Real.log_le_log hn0 (hP n hn).2) hn0.le
    _ = Real.log Y * ∑ n ∈ P, (1 : ℝ) / n := by rw [mul_sum]
    _ ≤ Real.log Y * ∑ k ∈ Icc 1 ⌊Y⌋₊, (1 : ℝ) / k := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (fun n hn => mem_Icc.2 ⟨(hP n hn).1, Nat.le_floor (hP n hn).2⟩)
          fun _ _ _ => by positivity) hL
    _ ≤ Real.log Y * (1 + Real.log Y) := mul_le_mul_of_nonneg_left hH hL

/-- **`Σ log n/n² ≤ 2 log Y/P₀`** over a set of integers in `[P₀, Y]`, `P₀ > 0`: the integers lie in
`(⌈P₀⌉ − 1, ⌊Y⌋ + 1)`, where `Σ 1/n² ≤ 2/⌈P₀⌉` (`sum_Ioo_inv_sq_le`). -/
theorem sum_log_div_sq_le_of_mem {P : Finset ℕ} {P₀ Y : ℝ} (hP₀ : 0 < P₀) (hY : 1 ≤ Y)
    (hP : ∀ n ∈ P, P₀ ≤ n ∧ (n : ℝ) ≤ Y) : ∑ n ∈ P, Real.log n / (n : ℝ) ^ 2 ≤ 2 * Real.log Y / P₀ := by
  have hL : 0 ≤ Real.log Y := Real.log_nonneg hY
  set N := ⌈P₀⌉₊
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hP₀))
  have hNP : P₀ ≤ N := Nat.le_ceil P₀
  have hS : ∑ n ∈ P, ((n : ℝ) ^ 2)⁻¹ ≤ 2 / N := by
    calc ∑ n ∈ P, ((n : ℝ) ^ 2)⁻¹ ≤ ∑ n ∈ Ioo (N - 1) (⌊Y⌋₊ + 1), ((n : ℝ) ^ 2)⁻¹ :=
          sum_le_sum_of_subset_of_nonneg (fun n hn => mem_Ioo.2
            ⟨by have := Nat.ceil_le.2 (hP n hn).1; omega, by have := Nat.le_floor (hP n hn).2; omega⟩)
            fun _ _ _ => by positivity
      _ ≤ 2 / (((N - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
      _ = 2 / N := by rw [Nat.cast_sub hN]; ring_nf
  calc ∑ n ∈ P, Real.log n / (n : ℝ) ^ 2 ≤ ∑ n ∈ P, Real.log Y * ((n : ℝ) ^ 2)⁻¹ := sum_le_sum fun n hn => by
        have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hP₀ (hP n hn).1
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Real.log_le_log hn0 (hP n hn).2) (by positivity)
    _ = Real.log Y * ∑ n ∈ P, ((n : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
    _ ≤ Real.log Y * (2 / N) := mul_le_mul_of_nonneg_left hS hL
    _ ≤ Real.log Y * (2 / P₀) := by gcongr
    _ = 2 * Real.log Y / P₀ := by ring

/-! ## The band -/

/-- **The band sum**: for `Y ≥ 1`, `0 ≤ ρ ≤ 1/2` and `P₀ ≥ e`, the integers `n ≥ P₀` with some power
`n^i ∈ [Y(1 − ρ), Y(1 + ρ)]`, `i ≥ 1`, have `Σ log n/n ≤ (8ρ + 1/P₀)·log 2Y`. The exponents are at most
`⌊log 2Y/log P₀⌋`; at the exponent `i` the integers lie in `[(Y(1 − ρ))^{1/i}, (Y(1 + ρ))^{1/i}] = [α, β]`, and
contribute at most `(β − α)·log β/α + log P₀/P₀ ≤ 4ρ·log 2Y/i² + log P₀/P₀`. -/
theorem sum_band_le {Y ρ P₀ : ℝ} (hY : 1 ≤ Y) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) (hP₀ : Real.exp 1 ≤ P₀)
    {P : Finset ℕ}
    (hP : ∀ n ∈ P, P₀ ≤ n ∧ ∃ i, 1 ≤ i ∧ Y * (1 - ρ) ≤ (n : ℝ) ^ i ∧ (n : ℝ) ^ i ≤ Y * (1 + ρ)) :
    ∑ n ∈ P, Real.log n / n ≤ (8 * ρ + 1 / P₀) * Real.log (2 * Y) := by
  classical
  have hP₀1 : 1 < P₀ := lt_of_lt_of_le (Real.one_lt_exp_iff.2 one_pos) hP₀
  have hlP₀ : 1 ≤ Real.log P₀ := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hP₀
  have hL2 : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  set I := ⌊Real.log (2 * Y) / Real.log P₀⌋₊
  set C : ℕ → ℕ → Prop := fun i n => Y * (1 - ρ) ≤ (n : ℝ) ^ i ∧ (n : ℝ) ^ i ≤ Y * (1 + ρ) with hC
  have hf0 : ∀ n : ℕ, 0 ≤ Real.log n / n := fun n => div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
  -- each exponent `i` of the band is at most `I`
  have hI : ∀ n ∈ P, ∀ i, C i n → i ≤ I := by
    intro n hn i hCi
    have hn : P₀ ≤ n := (hP n hn).1
    have h1 : P₀ ^ i ≤ (n : ℝ) ^ i := pow_le_pow_left₀ (by linarith) hn i
    have h2 : (n : ℝ) ^ i ≤ 2 * Y := hCi.2.trans (by nlinarith)
    have h3 : (i : ℝ) * Real.log P₀ ≤ Real.log (2 * Y) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (h1.trans h2)
    exact Nat.le_floor ((le_div_iff₀ (by linarith)).2 h3)
  -- the union bound over the exponents
  have hU : ∑ n ∈ P, Real.log n / n ≤ ∑ i ∈ Icc 1 I, ∑ n ∈ P.filter (C i), Real.log n / n := by
    simp only [sum_filter]
    rw [sum_comm]
    refine sum_le_sum fun n hn => ?_
    obtain ⟨i, hi, hCi⟩ := (hP n hn).2
    have := single_le_sum (s := Icc 1 I) (f := fun j => if C j n then Real.log n / n else 0)
      (fun j _ => by split_ifs; exacts [hf0 n, le_rfl]) (mem_Icc.2 ⟨hi, hI n hn i hCi⟩)
    exact (ite_eq_left hCi).symm.trans_le this
  -- one exponent: the integers of `[α, β]`, `α = (Y(1 − ρ))^{1/i}`, `β = (Y(1 + ρ))^{1/i}`
  have hiB : ∀ i ∈ Icc 1 I, ∑ n ∈ P.filter (C i), Real.log n / n ≤
      4 * ρ * Real.log (2 * Y) / (i : ℝ) ^ 2 + Real.log P₀ / P₀ := by
    intro i hi
    have hi1 : 1 ≤ i := (mem_Icc.1 hi).1
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi1
    have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have hYm : 0 < Y * (1 - ρ) := by nlinarith
    have hYp : 0 < Y * (1 + ρ) := by nlinarith
    set α := (Y * (1 - ρ)) ^ ((1 : ℝ) / i)
    set β := (Y * (1 + ρ)) ^ ((1 : ℝ) / i)
    have hα0 : 0 < α := Real.rpow_pos_of_pos hYm _
    have hαβ : α ≤ β := Real.rpow_le_rpow hYm.le (by nlinarith) (by positivity)
    have hmem : ∀ n ∈ P.filter (C i), α ≤ n ∧ (n : ℝ) ≤ β := by
      intro n hn
      obtain ⟨-, hCi⟩ := mem_filter.1 hn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have e : ((n : ℝ) ^ i) ^ ((1 : ℝ) / i) = n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0, mul_one_div_cancel hi0.ne', Real.rpow_one]
      constructor
      · rw [← e]; exact Real.rpow_le_rpow hYm.le hCi.1 (by positivity)
      · rw [← e]; exact Real.rpow_le_rpow (by positivity) hCi.2 (by positivity)
    have hcard := card_le_of_mem_Icc hαβ hmem
    have hR : 0 ≤ 4 * ρ * Real.log (2 * Y) / (i : ℝ) ^ 2 + Real.log P₀ / P₀ := by
      have : 0 ≤ Real.log P₀ := by linarith
      positivity
    rcases (P.filter (C i)).eq_empty_or_nonempty with hne | ⟨n₁, hn₁⟩
    · rw [hne, sum_empty]
      exact hR
    have hβ1 : 1 ≤ β := by
      have h1 := (hmem n₁ hn₁).2
      have h2 : P₀ ≤ n₁ := (hP n₁ (mem_filter.1 hn₁).1).1
      linarith
    have hlβ : 0 ≤ Real.log β := Real.log_nonneg hβ1
    set m := min (Real.log β / α) (Real.log P₀ / P₀)
    have hterm : ∀ n ∈ P.filter (C i), Real.log n / n ≤ m := by
      intro n hn
      obtain ⟨h1, h2⟩ := hmem n hn
      have hP₀n : P₀ ≤ n := (hP n (mem_filter.1 hn).1).1
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hα0 h1
      refine le_min ?_ ?_
      · calc Real.log n / n ≤ Real.log β / n := div_le_div_of_nonneg_right (Real.log_le_log hn0 h2) hn0.le
          _ ≤ Real.log β / α := div_le_div_of_nonneg_left hlβ hα0 h1
      · exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 hP₀) (Set.mem_Ici.2 (hP₀.trans hP₀n)) hP₀n
    have hm0 : 0 ≤ m := (hf0 n₁).trans (hterm n₁ hn₁)
    -- `β/α ≤ (1 + 4ρ)^{1/i} ≤ 1 + 4ρ/i` and `log β ≤ log(2Y)/i`
    have hratio : β / α ≤ 1 + 4 * ρ / i := by
      rw [← Real.div_rpow hYp.le hYm.le]
      have hq : Y * (1 + ρ) / (Y * (1 - ρ)) ≤ 1 + 4 * ρ := by
        rw [div_le_iff₀ hYm]
        have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ Y) hρ0) (by linarith : (0 : ℝ) ≤ 1 - 2 * ρ)
        nlinarith
      calc (Y * (1 + ρ) / (Y * (1 - ρ))) ^ ((1 : ℝ) / i) ≤ (1 + 4 * ρ) ^ ((1 : ℝ) / i) :=
            Real.rpow_le_rpow (by positivity) hq (by positivity)
        _ ≤ 1 + (1 / i) * (4 * ρ) := rpow_one_add_le_one_add_mul_self (by linarith) (by positivity)
            (by rw [div_le_one hi0]; exact hi1')
        _ = 1 + 4 * ρ / i := by ring
    have hlogβ : Real.log β ≤ Real.log (2 * Y) / i := by
      rw [Real.log_rpow hYp, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (Real.log_le_log hYp (by nlinarith)) hi0.le
    calc ∑ n ∈ P.filter (C i), Real.log n / n ≤ ∑ _n ∈ P.filter (C i), m := sum_le_sum hterm
      _ = (P.filter (C i)).card * m := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (β - α + 1) * m := mul_le_mul_of_nonneg_right hcard hm0
      _ = (β - α) * m + m := by ring
      _ ≤ (β - α) * (Real.log β / α) + Real.log P₀ / P₀ :=
          add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)) (min_le_right _ _)
      _ = (β / α - 1) * Real.log β + Real.log P₀ / P₀ := by field_simp
      _ ≤ (4 * ρ / i) * (Real.log (2 * Y) / i) + Real.log P₀ / P₀ :=
          add_le_add_left (mul_le_mul (by linarith) hlogβ hlβ (by positivity)) _
      _ = 4 * ρ * Real.log (2 * Y) / (i : ℝ) ^ 2 + Real.log P₀ / P₀ := by ring
  have hsq : ∑ i ∈ Icc 1 I, ((i : ℝ) ^ 2)⁻¹ ≤ 2 := by
    have e : Icc 1 I = Ioo 0 (I + 1) := by ext n; simp only [mem_Icc, mem_Ioo]; omega
    rw [e]
    simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (I + 1)
  have hIle : (I : ℝ) ≤ Real.log (2 * Y) / Real.log P₀ := Nat.floor_le (div_nonneg hL2 (by linarith))
  have hlP : 0 ≤ Real.log P₀ / P₀ := div_nonneg (by linarith) (by linarith)
  calc ∑ n ∈ P, Real.log n / n ≤ ∑ i ∈ Icc 1 I, ∑ n ∈ P.filter (C i), Real.log n / n := hU
    _ ≤ ∑ i ∈ Icc 1 I, (4 * ρ * Real.log (2 * Y) / (i : ℝ) ^ 2 + Real.log P₀ / P₀) := sum_le_sum hiB
    _ = 4 * ρ * Real.log (2 * Y) * ∑ i ∈ Icc 1 I, ((i : ℝ) ^ 2)⁻¹ + I * (Real.log P₀ / P₀) := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, mul_sum, nsmul_eq_mul]
        simp only [div_eq_mul_inv, add_tsub_cancel_right]
    _ ≤ 4 * ρ * Real.log (2 * Y) * 2 + (Real.log (2 * Y) / Real.log P₀) * (Real.log P₀ / P₀) := by
        gcongr
    _ = (8 * ρ + 1 / P₀) * Real.log (2 * Y) := by field_simp; ring

/-- **The band sum at the design's parameters**: the primes `p ≥ p₀` in the band (`InBand`: some power `p^i`,
`i ≥ 1`, in `[X′(1 − ρ_B), X′(1 + ρ_B)]`) have `Σ log p/p ≤ (8ρ_B + 1/p₀)·log 2X′`, when `0 ≤ ρ_B ≤ 1/2` and
`p₀ ≥ e` (`sum_band_le`). -/
theorem Setting.sum_inBand_le (S : Setting) {x ε : ℝ} {k : ℕ} (hx : 0 ≤ x) (hρ0 : 0 ≤ scRhoB S x ε k)
    (hρ : scRhoB S x ε k ≤ 1 / 2) (hp₀ : Real.exp 1 ≤ scP0 x k) {P : Finset ℕ}
    (hP : ∀ p ∈ P, scP0 x k ≤ p ∧ InBand S x ε k p) :
    ∑ p ∈ P, Real.log p / p ≤ (8 * scRhoB S x ε k + 1 / scP0 x k) * Real.log (2 * scX' x ε) :=
  sum_band_le (Real.one_le_exp (Real.rpow_nonneg hx _)) hρ0 hρ hp₀ hP

/-! ## Odd orders -/

/-- **A prime of odd order is large**: for a 2-adic setting and a non-split prime `p` with `ord(c·[p]_A)` odd,
`c = twA κ`, `4|A|/ord κ ≤ p + 1`. The image of `c·[p]_A` in `H_e` has odd order dividing `2^e`, so `p ≡ ±1
(mod 2^{e+2})` and `p + 1 ≥ 2^{e+2} ≥ 4|A₀| = 4|A|/ord κ`. -/
theorem Setting.TwoAdic.le_of_odd {S : Setting} {κ : S.A →* ℂˣ} {e : ℕ} (h : S.TwoAdic κ e) {p : ℕ}
    (hp : p.Prime) (hcls : S.cls p ≠ .split) (hodd : Odd (orderOf (S.hPtw (S.twA κ) p))) :
    4 * (Fintype.card S.A : ℝ) / orderOf κ ≤ p + 1 := by
  let ψ : S.A →* He e := QuotientGroup.lift S.K _ h.K_le
  have hψ (u : (ZMod S.QS)ˣ) : ψ (S.mkA u) = (QuotientGroup.mk (ZMod.unitsMap h.dvd u) : He e) := rfl
  have hψc : ψ (S.twA κ) = 1 := by
    unfold twA
    split_ifs
    · exact map_one ψ
    · have hneg : ZMod.unitsMap h.dvd (-1) = -1 := Units.ext (by
        rw [ZMod.unitsMap_val, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one, ZMod.cast_neg h.dvd,
          ZMod.cast_one h.dvd])
      rw [hψ, hneg, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_zpowers _
  have hpQS : ¬ p ∣ S.QS := fun hd => S.not_dvd_N_of_cls hp hcls (hd.trans S.QS_dvd_N)
  have hunit : IsUnit (p : ZMod S.QS) :=
    (ZMod.isUnit_iff_coprime p S.QS).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpQS)
  set v := ZMod.unitsMap h.dvd hunit.unit with hv_def
  have hv : (v : ZMod (2 ^ (e + 2))) = p := by
    rw [hv_def, ZMod.unitsMap_val, IsUnit.unit_spec, ZMod.cast_natCast h.dvd]
  have himg : ψ (S.hPtw (S.twA κ) p) = (QuotientGroup.mk v : He e) := by
    have h1 : ψ (S.hP p) = (QuotientGroup.mk v : He e) := by rw [hP, frob, clsA, dite_eq_left hunit, hψ]
    rw [hPtw, map_mul, hψc, h1]
    exact one_mul (QuotientGroup.mk v : He e)
  -- the image of `c·[p]_A` in `H_e` has odd order dividing `2^e`: it is trivial
  have hdvd1 : orderOf (QuotientGroup.mk v : He e) ∣ orderOf (S.hPtw (S.twA κ) p) :=
    himg ▸ orderOf_map_dvd ψ _
  have hdvd2 : orderOf (QuotientGroup.mk v : He e) ∣ 2 ^ e := card_He e ▸ orderOf_dvd_natCard _
  have h1 : (QuotientGroup.mk v : He e) = 1 := by
    obtain ⟨s, -, hos⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
    rcases s with _ | s
    · exact orderOf_eq_one_iff.1 (by simpa using hos)
    · exfalso
      have h2 : 2 ∣ orderOf (S.hPtw (S.twA κ) p) := (hos ▸ dvd_pow_self 2 (by omega)).trans hdvd1
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at h1
  obtain ⟨m, hm⟩ := h1
  -- so `p ≡ ±1 (mod 2^{e+2})`, and `2^{e+2} ≤ p + 1`
  have hpm : (p : ZMod (2 ^ (e + 2))) = 1 ∨ (p : ZMod (2 ^ (e + 2))) = -1 := by
    have hm' := congrArg (fun w : (ZMod (2 ^ (e + 2)))ˣ => (w : ZMod (2 ^ (e + 2)))) hm
    simp only [hv] at hm'
    rw [← hm']
    rcases Int.even_or_odd m with hm2 | hm2
    · left
      rw [hm2.neg_one_zpow, Units.val_one]
    · right
      rw [hm2.neg_one_zpow, Units.val_neg, Units.val_one]
  have hc (z : ℤ) (hz : (z : ZMod (2 ^ (e + 2))) = 0) : (2 : ℤ) ^ (e + 2) ∣ z := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd z (2 ^ (e + 2))).1 hz
    exact_mod_cast this
  have hp2 := hp.two_le
  have hle : (2 : ℤ) ^ (e + 2) ≤ p + 1 := by
    rcases hpm with h1 | h1
    · have := Int.le_of_dvd (by omega) (hc ((p : ℤ) - 1) (by push_cast; rw [h1, sub_self]))
      linarith
    · exact Int.le_of_dvd (by omega) (hc ((p : ℤ) + 1) (by push_cast; rw [h1, neg_add_cancel]))
  have hA : 4 * Fintype.card S.A ≤ orderOf κ * 2 ^ (e + 2) := by
    calc 4 * Fintype.card S.A = orderOf κ * (4 * (A₀ κ).card) := by rw [card_A_eq κ]; ring
      _ ≤ orderOf κ * 2 ^ (e + 2) := Nat.mul_le_mul_left _ (by rw [pow_add]; nlinarith [h.card_A₀_le])
  have hle' : (2 : ℝ) ^ (e + 2) ≤ p + 1 := by exact_mod_cast hle
  have hA' : (4 * Fintype.card S.A : ℝ) ≤ orderOf κ * 2 ^ (e + 2) := by exact_mod_cast hA
  have ho : (0 : ℝ) < orderOf κ := by exact_mod_cast orderOf_pos κ
  rw [div_le_iff₀ ho]
  nlinarith

end

end ZetaBalance
