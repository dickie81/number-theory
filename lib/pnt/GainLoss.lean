import GainAsk
import GainSums

/-!
# The losses, prime by prime

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain`; module M-G7c of the gain's numbers, first
half): the sizes the losses read, the asks at one prime against the gain (`loss_at_le`), the uncovered tops
(`uncov_le`, `sum_uncov_le`), and the slacks at one prime, split into a polynomial part and the parts of size `a`
(`base_le`, `cpart_ge_le`, `cpart_lt_le`). `GainLoss2` sums them and proves `losses_le`.

**The sizes** (`LossSizes`, `lossSizes`), at an admissible design under the growth package, with `y = x^{1/8}`:
`y ≥ 10⁹` (`GainBig.C_le`), `y^{16} ≤ |A| ≤ x³`, `|TT| ≤ |A|`, `1 ≤ m ≤ 2y⁴`, `y^{36} ≤ k ≤ 2x⁵`, `c₀ ≤ 64x⁶`,
`η + 1 ≤ x^{410}`, `N_m ≤ x^{403}`, `f ≤ 2x⁵`, `N₁ + r ≤ y`, `x^ε, x^{ε/3}, x^{ε/4}, log x, ord κ ≤ y`,
`x^{−2+ε}y^{16} ≤ y`, `x^{410} ≤ X′`, `x^{1000}·X′^{G′+2} ≤ b` (`GainBig.G'_le`, exponentiated), `|A|·a ≤ c_G` and
`d > 2^{12}x^{406}`.

**The ask, crudely.** At a top, `ask ≤ γ_p·a_t ≤ 4a/p` (`askE_le`); beyond the cut-off, `p > X″`, only `e = 1`
asks, and `ask ≤ a(1 + 1/x)/X″ − w″ = w″/x` (`askE_le_of_gt`); at `d`, `log d·askAtD ≤ (log⌈2a⌉ + log d)·2a/d`
(`log_mul_askAtD_le`, from `⌊log_d n⌋·log d ≤ log n`, `natLog_mul_log_le`).

**One prime** (`loss_at_le`, from `gains_ge_ask`): `Σ_j Σ_{t ∈ TT} ask − (Σ_j G_j − τ_p) ≤ m·(|TT|·slack₁ +
slack₂) + m·|TT ∖ coveredTops|·4a/p`, as `slack₁ ≥ 0` (`slack1_nonneg`). The left side of `losses_le` splits
(`losses_eq`, Step A) into these over the inert and signal `p ≤ X″`, the asks at the primes of the ask beyond `X″`
(`Setting.inertPrimes_subset_askSupp`), and the ask at `d`.

**The uncovered tops** (`uncov_le`, Step C): at an inert or signal `p ≤ X″`, the tops off `coveredTops` are all the
tops when `ord h_p` is odd, or when `p` is inert below `X′` with `ord h_p < x^{ε/4}` (`p ∉ PR`), or when `p ≥ p₀` is
in the band; there are none at a signal `p` or at `p ≥ X′`; and at a candidate they are bad tops (the served orbits
are the good ones, and `IsGoodAt` reads only the base point). Summed (`sum_uncov_le`): `|TT|` times the sum of
`log p/p` over the small or odd orders below `X″ + 1`, plus `|TT|·(8ρ_B + 1/p₀)·log 2X′` (`Setting.sum_inBand_le`),
plus `Σ_{p ∈ PR} (log p/p)·|badTops p|`.

**The slacks at one prime.** `|TT|·slack₁ + slack₂` is `|TT|·2c₀·|gainExps| + c_{dl,1}·2|A|·N_m²·log_p 2a +
c_{dl,2}·|TT|·log_p(2a)²`, plus `|TT|·topAllow + 2|A|·orbAllow + e_p` at a candidate (`slack_eq`). Times
`2 log p·m`, the first part is at most `x^{900}` (`base_le`; `2 log p·log_p z = 2 log z`). The second, at a
candidate (so `p < X′` and `p^{G′} ≤ X′^{G′}`), is at most `x^{900}·X′^{G′}` (every polynomial term, with
`D_p ≤ x^{47}` and `c_dep ≤ x^{49}` at `p ≥ p₀`) plus the terms of size `a`: at `p ≥ p₀` (`cpart_ge_le`)
`m|TT|·(2(b′/x)·log p + 2c_{κ,1}N₁a·log p/p² + 2c_{κ,1}N₁·La·a/k·log p/p) + 4m|A|·c_Pr·w″·log p`, and at `p < p₀`
(`cpart_lt_le`) `m|TT|·(4r(1 + c_t)b′·log p + 2c_t r·La·a/k·log p/p + 2c_t r·a/(kx^{26})⁴·log p) +
4m|A|·(r·w″ + 80rδ₁b′)·log p` (`p^{L₁(p)} ≥ (kx^{26})⁴`, `pow_scL1_ge`).
-/

open Finset

namespace ZetaBalance

noncomputable section

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-! ## The sizes -/

/-- **The sizes the losses read**, with `y = x^{1/8}`: `y ≥ 10⁹`, `y^{16} ≤ |A| ≤ x³`, `|TT| ≤ |A|`,
`1 ≤ m ≤ 2y⁴`, `y^{36} ≤ k ≤ 2x⁵`, the polynomial sizes `c₀ ≤ 64x⁶`, `η + 1 ≤ x^{410}`, `N_m ≤ x^{403}`, `f ≤ 2x⁵`,
the tile parameters `N₁ + r ≤ y`, the powers `x^ε, x^{ε/3}, x^{ε/4}, log x, ord κ ≤ y`, the scales
`x^{410} ≤ X′`, `x^{1000}·X′^{G′+2} ≤ b` (the growth package), `|A|·a ≤ c_G`, and `d > 2^{12}x^{406}`. -/
structure LossSizes : Prop where
  /-- `x ≥ 4096`. -/
  x_ge : 4096 ≤ x
  /-- `y = x^{1/8} ≥ 10⁹`. -/
  y_ge : 10 ^ 9 ≤ x ^ (1 / 8 : ℝ)
  /-- `y⁸ = x`. -/
  y_pow : (x ^ (1 / 8 : ℝ)) ^ 8 = x
  /-- `|A| ≥ x² = y^{16}`. -/
  A_ge : (x ^ (1 / 8 : ℝ)) ^ 16 ≤ Fintype.card S.A
  /-- `|A| ≤ x³`. -/
  A_le : (Fintype.card S.A : ℝ) ≤ x ^ 3
  /-- `|TT| ≤ |A|`. -/
  TT_le : (Dg.TT.card : ℝ) ≤ Fintype.card S.A
  /-- `m ≤ 2x^{1/2} = 2y⁴`. -/
  m_le : (Dg.R.m : ℝ) ≤ 2 * (x ^ (1 / 8 : ℝ)) ^ 4
  /-- `m ≥ 1`. -/
  m_ge : 1 ≤ (Dg.R.m : ℝ)
  /-- `k ≥ x^{9/2} = y^{36}`. -/
  k_ge : (x ^ (1 / 8 : ℝ)) ^ 36 ≤ Dg.R.k
  /-- `k ≤ 2x⁵`. -/
  k_le : (Dg.R.k : ℝ) ≤ 2 * x ^ 5
  /-- `c₀ ≤ 64x⁶`. -/
  c0_le : Dg.c0 ≤ 64 * x ^ 6
  /-- `η + 1 ≤ x^{410}`. -/
  eta_le : Dg.eta + 1 ≤ x ^ 410
  /-- `N_m ≤ x^{403}`. -/
  N_le : (Dg.R.N Dg.R.m : ℝ) ≤ x ^ 403
  /-- `f ≤ 2x⁵`. -/
  f_le : (S.f : ℝ) ≤ 2 * x ^ 5
  /-- `N₁ + r ≤ y`. -/
  N₁r_le : ((tilePar x ε Dg.R.k).N₁ : ℝ) + (tilePar x ε Dg.R.k).r ≤ x ^ (1 / 8 : ℝ)
  /-- `δ₁ ≤ 1`. -/
  δ_le : scδ₁ x ε ≤ 1
  /-- `x^{ε/3} ≤ y`. -/
  L_le : x ^ (ε / 3) ≤ x ^ (1 / 8 : ℝ)
  /-- `x^ε ≤ y`. -/
  xε_le : x ^ ε ≤ x ^ (1 / 8 : ℝ)
  /-- `x^{ε/4} ≤ y`. -/
  quarter_le : x ^ (ε / 4) ≤ x ^ (1 / 8 : ℝ)
  /-- `log x ≤ y`. -/
  log_le : Real.log x ≤ x ^ (1 / 8 : ℝ)
  /-- `ord κ ≤ y`. -/
  ord_le : (orderOf κ : ℝ) ≤ x ^ (1 / 8 : ℝ)
  /-- `x^{−2+ε}·y^{16} ≤ y`. -/
  rpow_neg_le : x ^ (-2 + ε) * (x ^ (1 / 8 : ℝ)) ^ 16 ≤ x ^ (1 / 8 : ℝ)
  /-- `X′ ≥ x^{410}`. -/
  X'_ge : x ^ 410 ≤ scX' x ε
  /-- `x^{1000}·X′^{G′+2} ≤ b`. -/
  b_ge : x ^ 1000 * scX' x ε ^ ((tilePar x ε Dg.R.k).G' + 2) ≤ scB x ε
  /-- `|A|·a ≤ c_G`. -/
  cG_ge : Fintype.card S.A * scA x ε ≤ S.cGform x ε
  /-- `d > 2^{12}x^{406}`. -/
  d_gt : 2 ^ 12 * x ^ 406 < (S.d : ℝ)

variable {Dg}

/-- **The sizes hold** at an admissible design under the growth package. -/
theorem lossSizes (hA : Dg.Adm) (hB : GainBig ε x) : Dg.LossSizes := by
  have hbig := hA.big
  have hx := hbig.x_ge
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hε := hbig.ε_pos
  have hε' := hbig.ε_lt
  have hyle : ∀ c : ℝ, c ≤ 1 / 8 → x ^ c ≤ x ^ (1 / 8 : ℝ) := fun c hc =>
    Real.rpow_le_rpow_of_exponent_le hx1 hc
  have hypow : ∀ n : ℕ, (x ^ (1 / 8 : ℝ)) ^ n = x ^ ((n : ℝ) / 8) := fun n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    ring_nf
  have hk := hA.k_eq
  have hkd := hbig.designK_le
  rw [← hk] at hkd
  have hm2 : (Dg.R.m : ℝ) ≤ 2 * x := by rw [hA.m_eq]; exact hbig.designM_le
  refine ⟨hx, hB.C_le.trans (hyle _ (by linarith)), ?_, ?_, hA.toDesignAdm.card_le_cube,
    by exact_mod_cast card_le_univ _, ?_, hA.one_le_m, ?_, hkd.2, ?_, ?_, ?_, ?_, ?_, ?_,
    hyle _ (by linarith), hyle _ (by linarith), hyle _ (by linarith), ?_, ?_, ?_, hbig.X'_ge, ?_, ?_,
    hA.toDesignAdm.lt_of_log hA.d_large⟩
  · rw [hypow]; norm_num
  · rw [hypow]
    refine le_trans ?_ hA.card_ge
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith)
  · rw [hypow]
    refine hA.m_mem.2.trans ?_
    have := Real.rpow_le_rpow_of_exponent_le hx1 (show 1 / 2 - ε / 16 ≤ ((4 : ℕ) : ℝ) / 8 by norm_num; linarith)
    linarith
  · rw [hypow, hk]
    refine le_trans ?_ (designK_mem hbig).1
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith)
  · have hΔ := hbig.designΔ_mem.2
    unfold c0
    calc 16 * (Dg.R.k : ℝ) * designΔ x ≤ 16 * (2 * x ^ 5) * (2 * x) := by gcongr; exact hkd.2
      _ = 64 * x ^ 6 := by ring
  · have := hA.toDesignAdm.eta_le hm2
    unfold eta
    linarith
  · have ht : (Dg.R.t : ℝ) ≤ x ^ 401 := by rw [hA.t_eq]; exact designT_le S hbig hA.card_le
    have h1 : (Dg.R.N Dg.R.m : ℝ) = Dg.R.k + Dg.R.m * (Dg.R.t + 1) := by
      simp [Setting.Ranks.N]
    rw [h1]
    have h5 : x ^ 5 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
    have h401 : 1 ≤ x ^ 401 := one_le_pow₀ hx1
    have e : x ^ 403 = x * x * x ^ 401 := by ring
    calc (Dg.R.k : ℝ) + Dg.R.m * (Dg.R.t + 1) ≤ 2 * x ^ 5 + (2 * x) * (x ^ 401 + x ^ 401) := by
          gcongr
          · linarith
      _ ≤ x ^ 403 := by
          have hxx : 4 * x + 2 ≤ x * x := by nlinarith
          have := mul_le_mul_of_nonneg_right hxx (by linarith : (0 : ℝ) ≤ x ^ 401)
          rw [e]; nlinarith
  · have := f_le_designK S hbig hA.card_le
    have h2 : (S.f : ℝ) ≤ designK x ε := by exact_mod_cast this
    rw [← hk] at h2
    linarith [hkd.2]
  · rw [hk]; exact hB.N₁r_le
  · exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  · exact hbig.log_le.trans (by linarith [Real.rpow_nonneg hx0.le ε, hyle ε (by linarith)])
  · exact hA.orderOf_le.trans (hyle _ (by linarith))
  · rw [hypow, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith)
  · -- `exp((G′ + 2)x^{ε/3} + 1000 log x) ≤ exp(x^ε/8) ≤ b`
    have hG := hB.G'_le
    rw [← hk] at hG
    set G := (tilePar x ε Dg.R.k).G'
    have hxe : 0 ≤ x ^ ε := Real.rpow_nonneg hx0.le ε
    have e1 : Real.exp (((G + 2 : ℕ) : ℝ) * x ^ (ε / 3)) = scX' x ε ^ (G + 2) := by
      rw [Real.exp_nat_mul]; rfl
    have e2 : Real.exp (((1000 : ℕ) : ℝ) * Real.log x) = x ^ 1000 := by
      rw [Real.exp_nat_mul, Real.exp_log hx0]
    have h3 : (((G + 2 : ℕ) : ℝ) * x ^ (ε / 3)) + ((1000 : ℕ) : ℝ) * Real.log x ≤ x ^ ε := by
      push_cast
      linarith
    calc x ^ 1000 * scX' x ε ^ (G + 2) = Real.exp ((((G + 2 : ℕ) : ℝ) * x ^ (ε / 3)) +
          ((1000 : ℕ) : ℝ) * Real.log x) := by rw [Real.exp_add, e1, e2, mul_comm]
      _ ≤ Real.exp (x ^ ε) := Real.exp_le_exp.2 h3
      _ = scB x ε := rfl
  · unfold Setting.cGform scA
    have hb := Real.exp_pos (scL x ε)
    have h1 : x ≤ x ^ (1 + 2 * ε) := by
      conv_lhs => rw [← Real.rpow_one x]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hA0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ Fintype.card S.A * scB x ε := mul_nonneg hA0 (Real.exp_pos _).le
    calc (Fintype.card S.A : ℝ) * (x * scB x ε) = x * (Fintype.card S.A * scB x ε) := by ring
      _ ≤ x ^ (1 + 2 * ε) * (Fintype.card S.A * scB x ε) := by gcongr
      _ = _ := by ring

namespace LossSizes

variable (hs : Dg.LossSizes)
include hs

/-- `x > 0`. -/
theorem x_pos : 0 < x := by linarith [hs.x_ge]

/-- `y ≥ 1`. -/
theorem one_le_y : 1 ≤ x ^ (1 / 8 : ℝ) := by linarith [hs.y_ge]

/-- `y ≤ x`. -/
theorem y_le_x : x ^ (1 / 8 : ℝ) ≤ x := by
  conv_rhs => rw [← hs.y_pow]
  exact le_self_pow₀ hs.one_le_y (by norm_num)

/-- `m ≤ 2x`. -/
theorem m_le_x : (Dg.R.m : ℝ) ≤ 2 * x := by
  have h := hs.m_le
  have h4 : (x ^ (1 / 8 : ℝ)) ^ 4 ≤ (x ^ (1 / 8 : ℝ)) ^ 8 := pow_le_pow_right₀ hs.one_le_y (by norm_num)
  rw [hs.y_pow] at h4
  linarith

/-- `log a = log x + x^ε`. -/
theorem log_scA : Real.log (scA x ε) = Real.log x + x ^ ε := by
  unfold scA scB scL
  rw [Real.log_mul hs.x_pos.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- `log a ≤ 2y`. -/
theorem log_scA_le : Real.log (scA x ε) ≤ 2 * x ^ (1 / 8 : ℝ) := by
  rw [hs.log_scA]; linarith [hs.log_le, hs.xε_le]

/-- `log 2a ≤ 3y`. -/
theorem log_two_scA_le : Real.log (2 * scA x ε) ≤ 3 * x ^ (1 / 8 : ℝ) := by
  rw [Real.log_mul two_ne_zero (scA_pos ε hs.x_pos).ne']
  linarith [hs.log_scA_le, Real.log_two_lt_d9, hs.one_le_y]

/-- `log⌈2a⌉ ≤ 3y`, as `⌈2a⌉ ≤ 3a`. -/
theorem log_ceil_le : Real.log ⌈2 * scA x ε⌉₊ ≤ 3 * x ^ (1 / 8 : ℝ) := by
  have ha := one_le_scA ε (by linarith [hs.x_ge] : (1 : ℝ) ≤ x)
  have h1 : (⌈2 * scA x ε⌉₊ : ℝ) ≤ 3 * scA x ε := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * scA x ε)
    linarith
  have h0 : (0 : ℝ) < ⌈2 * scA x ε⌉₊ := by exact_mod_cast Nat.ceil_pos.2 (by linarith)
  calc Real.log ⌈2 * scA x ε⌉₊ ≤ Real.log (3 * scA x ε) := Real.log_le_log h0 h1
    _ = Real.log 3 + Real.log (scA x ε) := Real.log_mul (by norm_num) (by linarith)
    _ ≤ 3 * x ^ (1 / 8 : ℝ) := by
        have : Real.log 3 ≤ 2 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
        linarith [hs.log_scA_le, hs.y_ge]

/-- `log 2X″ ≤ 6y`: `log 2X″ = log 2 + log x + log|A| + x^{ε/3}` and `|A| ≤ x³`. -/
theorem log_two_cutX_le : Real.log (2 * S.cutX x ε) ≤ 6 * x ^ (1 / 8 : ℝ) := by
  have hx0 := hs.x_pos
  have hA1 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have hlA : Real.log (Fintype.card S.A) ≤ 3 * Real.log x := by
    have e : Real.log (x ^ 3) = 3 * Real.log x := by rw [Real.log_pow]; norm_num
    rw [← e]
    exact Real.log_le_log (by linarith) hs.A_le
  have e2 : 2 * S.cutX x ε = 2 * x * Fintype.card S.A * Real.exp (x ^ (ε / 3)) := by unfold Setting.cutX; ring
  rw [e2, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul two_ne_zero hx0.ne', Real.log_exp]
  linarith [hs.log_le, hs.L_le, Real.log_two_lt_d9, hs.y_ge]

/-- `log p ≤ 6y` for `1 ≤ p ≤ 2X″`. -/
theorem log_le_of_le {p : ℕ} (hp : 1 ≤ p) (hpX : (p : ℝ) ≤ 2 * S.cutX x ε) : Real.log p ≤ 6 * x ^ (1 / 8 : ℝ) :=
  (Real.log_le_log (by exact_mod_cast hp) hpX).trans hs.log_two_cutX_le

/-- `X″ ≥ 1`. -/
theorem one_le_cutX : 1 ≤ S.cutX x ε := by
  have hA1 : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
  have h1 : (1 : ℝ) ≤ Real.exp (x ^ (ε / 3)) := Real.one_le_exp (Real.rpow_nonneg hs.x_pos.le _)
  unfold Setting.cutX
  have : (1 : ℝ) ≤ x * Fintype.card S.A := by nlinarith [hs.x_ge]
  nlinarith

end LossSizes

/-- **`log_p z ≤ 2 log z`** for `p ≥ 2` and `z ≥ 1`, as `log p ≥ log 2 > 1/2`. -/
theorem logb_le_two_mul {p : ℕ} (hp : 2 ≤ p) {z : ℝ} (hz : 1 ≤ z) : Real.logb p z ≤ 2 * Real.log z := by
  have h2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  have hl : 1 / 2 < Real.log p := by linarith [Real.log_two_gt_d9]
  have hz0 := Real.log_nonneg hz
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

/-! ## Elementary bounds -/

/-- **`⌊log_b n⌋·log b ≤ log n`** for `b > 1`, `n ≥ 1`, as `b^{⌊log_b n⌋} ≤ n`. -/
theorem natLog_mul_log_le {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : (Nat.log b n : ℝ) * Real.log b ≤ Real.log n := by
  have h := Nat.pow_log_le_self b hn
  have hpos : (0 : ℝ) < ((b ^ Nat.log b n : ℕ) : ℝ) := by exact_mod_cast pow_pos (by omega) _
  calc (Nat.log b n : ℝ) * Real.log b = Real.log ((b ^ Nat.log b n : ℕ) : ℝ) := by
        push_cast; rw [Real.log_pow]
    _ ≤ Real.log n := Real.log_le_log hpos (by exact_mod_cast h)

/-- **The number of exponents**: `|gainExps| = ⌊log_p⌈2a⌉⌋ + 1`. -/
theorem card_gainExps (x ε : ℝ) (p : ℕ) : (gainExps x ε p).card = Nat.log p ⌈2 * scA x ε⌉₊ + 1 := by
  simp [gainExps]

/-- **`log p·|gainExps| ≤ log⌈2a⌉ + log p`** for `p ≥ 2` and `x > 0`. -/
theorem log_mul_card_gainExps_le {x ε : ℝ} (hx : 0 < x) {p : ℕ} (hp : 2 ≤ p) :
    Real.log p * (gainExps x ε p).card ≤ Real.log ⌈2 * scA x ε⌉₊ + Real.log p := by
  have hn : ⌈2 * scA x ε⌉₊ ≠ 0 := (Nat.ceil_pos.2 (by have := scA_pos ε hx; linarith)).ne'
  have h := natLog_mul_log_le (b := p) (by omega) hn
  rw [card_gainExps]
  push_cast
  linarith

/-- **`p^{L₁(p)} ≥ (kx^{26})⁴`** for `p ≥ 2`, `k ≥ 1`, `x > 0`. -/
theorem pow_scL1_ge {x : ℝ} (hx : 0 < x) {k p : ℕ} (hk : 1 ≤ k) (hp : 2 ≤ p) :
    ((k : ℝ) * x ^ 26) ^ 4 ≤ (p : ℝ) ^ scL1 x k p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hY : 0 < ((k : ℝ) * x ^ 26) ^ 4 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  calc ((k : ℝ) * x ^ 26) ^ 4 = (p : ℝ) ^ Real.logb p (((k : ℝ) * x ^ 26) ^ 4) :=
        (Real.rpow_logb (by linarith) hp1.ne' hY).symm
    _ ≤ (p : ℝ) ^ ((scL1 x k p : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1.le (Nat.le_ceil _)
    _ = (p : ℝ) ^ scL1 x k p := Real.rpow_natCast _ _

/-- **`2 log p·log_p y = 2 log y`** for `p ≥ 2`. -/
theorem two_log_mul_logb {p : ℕ} (hp : 2 ≤ p) (y : ℝ) : 2 * Real.log p * Real.logb p y = 2 * Real.log y := by
  have : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  rw [Real.logb]
  field_simp

/-- **`X″·w″ = a`**: the cut-off is `a/w″`. -/
theorem cutX_mul_scW'' (S : Setting) {x : ℝ} (ε : ℝ) (hx : 0 < x) : S.cutX x ε * scW'' S x ε = scA x ε := by
  have h := scA_div_scW'' S ε hx
  rw [div_eq_iff (scW''_pos S ε hx).ne'] at h
  rw [h]
  rfl

/-- **`X′·b′ = a`.** -/
theorem scX'_mul_scB' (x ε : ℝ) : scX' x ε * scB' x ε = scA x ε := by
  have h : scX' x ε ≠ 0 := (Real.exp_pos _).ne'
  unfold scB'
  field_simp [h]

/-! ## The ask, crudely -/

/-- **The ask is at most `4a/p`** at a top, for `p ≥ 2`: `ask ≤ Σ_e a_t/p^e ≤ γ_p·a_t ≤ (4/(3p))·2a`. -/
theorem askE_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (hp : 2 ≤ p) {t : S.A} (ht : t ∈ Dg.TT) : Dg.askE u J p t ≤ 4 * scA x ε / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have ha0 : 0 ≤ Dg.a t := by linarith [hA.two_c0_le_a hF ht, Dg.c0_nonneg]
  have ha2 := hA.a_le_two hF ht
  have hg := gamP_le hp
  have hg0 : 0 ≤ gamP p := by
    unfold gamP
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_nonneg hp0.le (by nlinarith)
  calc Dg.askE u J p t ≤ ∑ e ∈ gainExps x ε p, Dg.a t / (p : ℝ) ^ e := by
        refine sum_le_sum fun e _ => max_le ?_ (by positivity)
        linarith [Dg.wt_pos u J (S.pos (S.twA κ) p (1, t) e)]
    _ ≤ gamP p * Dg.a t := sum_gainExps_le hp ha0
    _ ≤ 4 / (3 * p) * (2 * scA x ε) := mul_le_mul hg ha2 ha0 (by positivity)
    _ ≤ 4 * scA x ε / p := by
        have := scA_pos ε hA.big.pos
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hp0]
        nlinarith

/-- **Beyond the cut-off the ask is at most `w″/x`**: for `p > X″`, the term `e = 1` is
`a_t/p − w ≤ a(1 + 1/x)/X″ − w″ = w″/x`, and the terms `e ≥ 3` vanish (`a_t/p^e ≤ a_t/(2p) < w″`). -/
theorem askE_le_of_gt (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (hp : 2 ≤ p) (hpX : S.cutX x ε < p) {t : S.A} (ht : t ∈ Dg.TT) :
    Dg.askE u J p t ≤ scW'' S x ε / x := by
  have hx := hA.big.x_ge
  have hx0 : 0 < x := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hw := scW''_pos S ε hx0
  have hXw := cutX_mul_scW'' S ε hx0
  have hX0 : 0 < S.cutX x ε := by unfold Setting.cutX; have := Real.exp_pos (x ^ (ε / 3)); positivity
  have ha0 : 0 ≤ Dg.a t := by linarith [hA.two_c0_le_a hF ht, Dg.c0_nonneg]
  have hal := hA.a_le hF ht
  -- `a_t/p ≤ w″ + w″/x`
  have h1 : Dg.a t / p ≤ scW'' S x ε + scW'' S x ε / x := by
    have e : scW'' S x ε + scW'' S x ε / x = (scA x ε + scA x ε / x) / S.cutX x ε := by
      rw [← hXw]; field_simp
    rw [e]
    calc Dg.a t / p ≤ Dg.a t / S.cutX x ε := div_le_div_of_nonneg_left ha0 hX0 hpX.le
      _ ≤ (scA x ε + scA x ε / x) / S.cutX x ε := div_le_div_of_nonneg_right hal hX0.le
  have hwx : scW'' S x ε / x ≤ scW'' S x ε := div_le_self hw.le (by linarith)
  have hterm : ∀ e ∈ gainExps x ε p, max (Dg.a t / (p : ℝ) ^ e - Dg.wt u J (S.pos (S.twA κ) p (1, t) e)) 0 ≤
      if e = 1 then scW'' S x ε / x else 0 := by
    intro e he
    have hwe := (hA.e_mem u (S.pos (S.twA κ) p (1, t) e) J).1
    have hwe' : scW'' S x ε ≤ Dg.wt u J (S.pos (S.twA κ) p (1, t) e) := hwe
    split_ifs with h1e
    · subst h1e
      rw [pow_one]
      exact max_le (by linarith) (by positivity)
    · have h3 : 3 ≤ e := by
        obtain ⟨i, rfl⟩ := odd_of_mem_gainExps he
        omega
      have hpe : 2 * (p : ℝ) ≤ (p : ℝ) ^ e := by
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
        calc 2 * (p : ℝ) ≤ p * p := by nlinarith
          _ = (p : ℝ) ^ 2 := by ring
          _ ≤ (p : ℝ) ^ e := pow_le_pow_right₀ (by linarith) (by omega)
      have h4 : Dg.a t / (p : ℝ) ^ e ≤ Dg.a t / p / 2 := by
        rw [div_div, mul_comm]
        exact div_le_div_of_nonneg_left ha0 (by positivity) hpe
      exact max_le (by linarith) le_rfl
  calc Dg.askE u J p t ≤ ∑ e ∈ gainExps x ε p, if e = 1 then scW'' S x ε / x else 0 := sum_le_sum hterm
    _ = scW'' S x ε / x := by
        have : 1 ∈ gainExps x ε p := mem_map.2 ⟨0, mem_range.2 (by omega), rfl⟩
        simp [this]

/-- **The ask at `d`**: `log d·askAtD ≤ (log⌈2a⌉ + log d)·2a/d`, as each of its `⌊log_d⌈2a⌉⌋ + 1` terms is at most
`a_t/d ≤ 2a/d`. -/
theorem log_mul_askAtD_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {t : S.A}
    (ht : t ∈ Dg.TT) :
    Real.log S.d * Dg.askAtD u J t ≤ (Real.log ⌈2 * scA x ε⌉₊ + Real.log S.d) * (2 * scA x ε / S.d) := by
  have hd : S.d.Prime := Fact.out
  have hd2 := hd.two_le
  have hd0 : (0 : ℝ) < S.d := by exact_mod_cast hd.pos
  have hd1 : (1 : ℝ) ≤ S.d := by exact_mod_cast hd.one_lt.le
  have ha0 : 0 ≤ Dg.a t := by linarith [hA.two_c0_le_a hF ht, Dg.c0_nonneg]
  have ha2 := hA.a_le_two hF ht
  have hA0 := scA_pos ε hA.big.pos
  have hl : 0 ≤ Real.log S.d := Real.log_nonneg hd1
  have hn : ⌈2 * scA x ε⌉₊ ≠ 0 := (Nat.ceil_pos.2 (by linarith)).ne'
  have hL := natLog_mul_log_le (b := S.d) hd.one_lt hn
  have h1 : Dg.askAtD u J t ≤ (Nat.log S.d ⌈2 * scA x ε⌉₊ + 1 : ℕ) * (2 * scA x ε / S.d) := by
    unfold askAtD
    calc ∑ e ∈ Icc 1 (Nat.log S.d ⌈2 * scA x ε⌉₊ + 1),
          max (Dg.a t / (S.d : ℝ) ^ e - Dg.wt u J (S.partner t (S.d ^ e))) 0 ≤
        ∑ _e ∈ Icc 1 (Nat.log S.d ⌈2 * scA x ε⌉₊ + 1), 2 * scA x ε / S.d := by
          refine sum_le_sum fun e he => max_le ?_ (by positivity)
          have he1 := (mem_Icc.1 he).1
          have hde : (S.d : ℝ) ≤ (S.d : ℝ) ^ e := le_self_pow₀ hd1 (by omega)
          have : Dg.a t / (S.d : ℝ) ^ e ≤ 2 * scA x ε / S.d :=
            div_le_div₀ (by linarith) ha2 hd0 hde
          linarith [Dg.wt_pos u J (S.partner t (S.d ^ e))]
      _ = _ := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  calc Real.log S.d * Dg.askAtD u J t ≤
      Real.log S.d * ((Nat.log S.d ⌈2 * scA x ε⌉₊ + 1 : ℕ) * (2 * scA x ε / S.d)) :=
        mul_le_mul_of_nonneg_left h1 hl
    _ = ((Nat.log S.d ⌈2 * scA x ε⌉₊ : ℝ) * Real.log S.d + Real.log S.d) * (2 * scA x ε / S.d) := by
        push_cast; ring
    _ ≤ _ := by gcongr

/-- **`topAllow ≥ 0`** for `x ≥ 1`. -/
theorem topAllow_nonneg (hx : 1 ≤ x) (p : ℕ) : 0 ≤ Dg.topAllow p := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlg : 0 ≤ Real.logb p (scA x ε) := logb_nat_nonneg p (one_le_scA ε hx)
  have hla : 0 ≤ Real.log (scA x ε) := Real.log_nonneg (one_le_scA ε hx)
  have hLa : 0 ≤ scLa x ε Dg.R.k := by unfold scLa; positivity
  have hδ : 0 ≤ scδ₁ x ε := Real.rpow_nonneg hx0 _
  have hb' : 0 ≤ scB' x ε := (scB'_pos ε (by linarith)).le
  have ha : 0 ≤ scA x ε := (scA_pos ε (by linarith)).le
  have hc0 := Dg.c0_nonneg
  have heta := Dg.eta_nonneg
  have hcD : 0 ≤ Dg.cDep p := by unfold cDep; positivity
  unfold topAllow
  split_ifs <;> positivity

/-- **`slack₁ ≥ 0`** for `x ≥ 1`. -/
theorem slack1_nonneg (hx : 1 ≤ x) (p : ℕ) : 0 ≤ Dg.slack1 p := by
  have := Dg.topAllow_nonneg hx p
  have hc0 := Dg.c0_nonneg
  unfold slack1
  split_ifs <;> positivity

/-! ## The losses at one prime -/

/-- **The covered tops are tops.** -/
theorem coveredTops_subset (p : ℕ) : Dg.coveredTops p ⊆ Dg.TT := by
  classical
  unfold coveredTops
  split_ifs
  · exact Subset.rfl
  · exact filter_subset _ _
  · exact empty_subset _

/-- **The loss at a prime `p ≥ 2`** (`gains_ge_ask`): the asks of all tops, less the gain, are at most
`m·(|TT|·slack₁ + slack₂)` plus `4a/p` for each lift and each uncovered top. -/
theorem loss_at_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) {p : ℕ} (hp : 2 ≤ p) :
    ∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t - (∑ J, Dg.gainG pr u J p - Dg.tau pr p) ≤
      Dg.R.m * (Dg.TT.card * Dg.slack1 p + Dg.slack2 p) +
        Dg.R.m * ((Dg.TT \ Dg.coveredTops p).card * (4 * scA x ε / p)) := by
  have hsub := Dg.coveredTops_subset p
  have h1 := gains_ge_ask hA hF u p
  have hs1 := Dg.slack1_nonneg hA.one_le_x p
  have hm0 : (0 : ℝ) ≤ Dg.R.m := Nat.cast_nonneg _
  have hsplit : ∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t =
      ∑ J, ∑ t ∈ Dg.TT \ Dg.coveredTops p, Dg.askE u J p t + ∑ J, ∑ t ∈ Dg.coveredTops p, Dg.askE u J p t := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun J _ => (sum_sdiff hsub).symm
  have hunc : ∑ J, ∑ t ∈ Dg.TT \ Dg.coveredTops p, Dg.askE u J p t ≤
      Dg.R.m * ((Dg.TT \ Dg.coveredTops p).card * (4 * scA x ε / p)) := by
    calc ∑ J, ∑ t ∈ Dg.TT \ Dg.coveredTops p, Dg.askE u J p t ≤
        ∑ _J : Fin Dg.R.m, ((Dg.TT \ Dg.coveredTops p).card * (4 * scA x ε / p)) := by
          refine sum_le_sum fun J _ => ?_
          rw [← nsmul_eq_mul]
          exact sum_le_card_nsmul _ _ _ fun t ht => askE_le hA hF u J hp (mem_sdiff.1 ht).1
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcov : (Dg.coveredTops p).card * Dg.slack1 p ≤ Dg.TT.card * Dg.slack1 p :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hsub) hs1
  have hcov' := mul_le_mul_of_nonneg_left hcov hm0
  rw [hsplit]
  nlinarith

/-- **The losses, split** (Step A): the left side of `losses_le` is the sum over the inert and signal `p ≤ X″` of
`2 log p·(asks − gain)`, plus the asks at the primes of the ask beyond `X″`, plus the ask at `d`. -/
theorem losses_eq (hA : Dg.Adm) (pr : DesignPar S) (u : S.A) :
    (∑ t ∈ Dg.TT, ∑ J, ((∑ p ∈ S.askSupp x ε, 2 * Real.log p * Dg.askE u J p t) +
        Real.log S.d * Dg.askAtD u J t)) -
      ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
        2 * Real.log p * (∑ J, Dg.gainG pr u J p - Dg.tau pr p) =
      ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), 2 * Real.log p *
          (∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t - (∑ J, Dg.gainG pr u J p - Dg.tau pr p)) +
        ∑ p ∈ S.askSupp x ε \ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε),
          2 * Real.log p * ∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t +
        ∑ t ∈ Dg.TT, ∑ J, Real.log S.d * Dg.askAtD u J t := by
  have hsub := S.inertPrimes_subset_askSupp (x := x) (ε := ε) (by linarith [hA.big.x_ge])
  have e1 : ∑ t ∈ Dg.TT, ∑ J, ∑ p ∈ S.askSupp x ε, 2 * Real.log p * Dg.askE u J p t =
      ∑ p ∈ S.askSupp x ε, 2 * Real.log p * ∑ J, ∑ t ∈ Dg.TT, Dg.askE u J p t := by
    simp only [mul_sum]
    calc ∑ t ∈ Dg.TT, ∑ J, ∑ p ∈ S.askSupp x ε, 2 * Real.log p * Dg.askE u J p t =
        ∑ J, ∑ t ∈ Dg.TT, ∑ p ∈ S.askSupp x ε, 2 * Real.log p * Dg.askE u J p t := sum_comm
      _ = ∑ J, ∑ p ∈ S.askSupp x ε, ∑ t ∈ Dg.TT, 2 * Real.log p * Dg.askE u J p t :=
          sum_congr rfl fun J _ => sum_comm
      _ = _ := sum_comm
  simp only [sum_add_distrib]
  rw [e1, ← sum_sdiff hsub]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-! ## The uncovered tops -/

open scoped Classical in
/-- **The uncovered tops at one prime** (Step C): at an inert or signal `p ≤ X″`, the tops off `coveredTops` are all
the tops if `ord h_p` is odd, or if `p` is inert, `p < X′` and `ord h_p < x^{ε/4}` (`p ∉ PR`), or if `p ≥ p₀` is in
the band; none at a signal `p` or `p ≥ X′`; and bad tops at a candidate. -/
theorem uncov_le {p : ℕ} (hp : p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε)) :
    Real.log p / p * ((Dg.TT \ Dg.coveredTops p).card : ℝ) ≤
      Dg.TT.card * (if p.Prime ∧ S.cls p ≠ .split ∧ (orderOf (S.hPtw (S.twA κ) p) ≤ ⌈x ^ (ε / 4)⌉₊ ∨
          Odd (orderOf (S.hPtw (S.twA κ) p))) then Real.log p / p else 0) +
        Dg.TT.card * (if scP0 x Dg.R.k ≤ p ∧ InBand S x ε Dg.R.k p then Real.log p / p else 0) +
        (if p ∈ S.PR κ x ε then Real.log p / p * (Dg.badTops p).card else 0) := by
  obtain ⟨-, hp', -, hcls⟩ := mem_filter.1 hp
  have w0 : 0 ≤ Real.log p / p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hT0 : (0 : ℝ) ≤ Dg.TT.card := Nat.cast_nonneg _
  have i1 : 0 ≤ Dg.TT.card * (if p.Prime ∧ S.cls p ≠ .split ∧ (orderOf (S.hPtw (S.twA κ) p) ≤ ⌈x ^ (ε / 4)⌉₊ ∨
      Odd (orderOf (S.hPtw (S.twA κ) p))) then Real.log p / p else 0) := by
    split_ifs <;> positivity
  have i2 : 0 ≤ Dg.TT.card * (if scP0 x Dg.R.k ≤ p ∧ InBand S x ε Dg.R.k p then Real.log p / p else 0) := by
    split_ifs <;> positivity
  have i3 : 0 ≤ (if p ∈ S.PR κ x ε then Real.log p / p * (Dg.badTops p).card else 0) := by
    split_ifs <;> positivity
  by_cases hev : Even (orderOf (S.hPtw (S.twA κ) p))
  swap
  · have hc : Dg.coveredTops p = ∅ := by
      unfold coveredTops
      rw [ite_eq_right fun h => hev h.2]
    rw [hc, sdiff_empty, ite_eq_left ⟨hp', hcls, Or.inr (Nat.not_even_iff_odd.1 hev)⟩]
    nlinarith
  by_cases hsig : S.cls p = .signal ∨ scX' x ε ≤ p
  · have hc : Dg.coveredTops p = Dg.TT := by
      unfold coveredTops
      rw [ite_eq_left ⟨hp, hev⟩, ite_eq_left hsig]
    rw [hc, Finset.sdiff_self, card_empty, Nat.cast_zero, mul_zero]
    linarith
  have hin : S.cls p = .inert := by
    rcases h : S.cls p with _ | _ | _
    · exact absurd h hcls
    · exact absurd (Or.inl h) hsig
    · rfl
  have hpX' : (p : ℝ) < scX' x ε := lt_of_not_ge fun h => hsig (Or.inr h)
  by_cases hc : p ∈ S.cand κ x ε Dg.R.k
  · have hPR : p ∈ S.PR κ x ε := (mem_filter.1 hc).1
    rw [ite_eq_left hPR]
    have hsubset : Dg.TT \ Dg.coveredTops p ⊆ Dg.badTops p := by
      intro t ht
      obtain ⟨htT, htc⟩ := mem_sdiff.1 ht
      unfold coveredTops at htc
      rw [ite_eq_left ⟨hp, hev⟩, ite_eq_right hsig, mem_filter, not_and] at htc
      have hns := htc htT
      rw [Dg.mem_served_iff] at hns
      refine mem_filter.2 ⟨htT, fun hgood => hns ⟨⟨hc, hp⟩, mem_image_of_mem _ htT, ?_⟩⟩
      unfold IsGoodAt at hgood ⊢
      rwa [basePoint_basePoint]
    have h1 : ((Dg.TT \ Dg.coveredTops p).card : ℝ) ≤ (Dg.badTops p).card := by
      exact_mod_cast card_le_card hsubset
    have := mul_le_mul_of_nonneg_left h1 w0
    linarith
  · have hcov : Dg.coveredTops p = ∅ := by
      unfold coveredTops
      rw [ite_eq_left ⟨hp, hev⟩, ite_eq_right hsig, Dg.served_eq_empty_of_not_cand hc]
      simp
    rw [hcov, sdiff_empty]
    by_cases hPR : p ∈ S.PR κ x ε
    · have hband : scP0 x Dg.R.k ≤ p ∧ InBand S x ε Dg.R.k p := by
        by_contra hb
        exact hc (mem_filter.2 ⟨hPR, hev, fun h1 h2 => hb ⟨h1, h2⟩⟩)
      rw [ite_eq_left hband]
      nlinarith
    · have hord : orderOf (S.hPtw (S.twA κ) p) ≤ ⌈x ^ (ε / 4)⌉₊ := by
        by_contra ho
        replace ho := not_le.1 ho
        apply hPR
        refine mem_filter.2 ⟨mem_range.2 (Nat.lt_ceil.2 hpX'), hp', hin, ?_⟩
        exact (Nat.le_ceil _).trans (by exact_mod_cast ho.le)
      rw [ite_eq_left ⟨hp', hcls, Or.inl hord⟩]
      nlinarith

/-- **The uncovered tops, summed** over the inert and signal `p ≤ X″`: at most `|TT|` times the sum of `log p/p`
over the small or odd orders below `X″ + 1`, plus `|TT|` times the sum over the band, plus
`Σ_{p ∈ PR} (log p/p)·|badTops p|`. -/
theorem sum_uncov_le (hx : 0 ≤ x) (hρ0 : 0 ≤ scRhoB S x ε Dg.R.k) (hρ : scRhoB S x ε Dg.R.k ≤ 1 / 2)
    (hp₀ : Real.exp 1 ≤ scP0 x Dg.R.k) :
    ∑ p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε), Real.log p / p * ((Dg.TT \ Dg.coveredTops p).card : ℝ) ≤
      Dg.TT.card * ∑ p ∈ (range ⌈S.cutX x ε + 1⌉₊).filter (fun p => p.Prime ∧ S.cls p ≠ .split ∧
          (orderOf (S.hPtw (S.twA κ) p) ≤ ⌈x ^ (ε / 4)⌉₊ ∨ Odd (orderOf (S.hPtw (S.twA κ) p)))),
          Real.log p / p +
        Dg.TT.card * (8 * scRhoB S x ε Dg.R.k + 1 / scP0 x Dg.R.k) * Real.log (2 * scX' x ε) +
        ∑ p ∈ S.PR κ x ε, (Real.log p / p) * ((Dg.badTops p).card : ℝ) := by
  classical
  have hX0 : 0 ≤ S.cutX x ε := by unfold Setting.cutX; positivity
  have hw : ∀ p : ℕ, 0 ≤ Real.log p / p := fun p => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have h1 := sum_le_sum fun p hp => Dg.uncov_le (p := p) hp
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_filter, ← sum_filter, ← sum_filter] at h1
  refine h1.trans (add_le_add_three ?_ ?_ ?_)
  · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ fun p hp => ?_) fun p _ _ => hw p
    have h2 := mem_range.1 (mem_filter.1 hp).1
    have h3 : (p : ℝ) ≤ S.cutX x ε := (Nat.cast_le.2 (by omega : p ≤ ⌊S.cutX x ε⌋₊)).trans (Nat.floor_le hX0)
    exact mem_range.2 (Nat.lt_ceil.2 (by linarith))
  · rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact S.sum_inBand_le hx hρ0 hρ hp₀ fun p hp => (mem_filter.1 hp).2
  · exact sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_filter.1 hp).2) fun p _ _ =>
      mul_nonneg (hw p) (Nat.cast_nonneg _)

/-! ## The slacks: the polynomial part -/

/-- `c·x^m ≤ x^n` for `c ≤ x^k`, `m + k ≤ n`, `x ≥ 1`. -/
theorem mul_pow_le_pow {x c : ℝ} (hx : 1 ≤ x) {k m n : ℕ} (hc : c ≤ x ^ k) (hmn : m + k ≤ n) :
    c * x ^ m ≤ x ^ n :=
  calc c * x ^ m ≤ x ^ k * x ^ m := mul_le_mul_of_nonneg_right hc (pow_nonneg (by linarith) _)
    _ = x ^ (m + k) := by ring
    _ ≤ x ^ n := pow_le_pow_right₀ hx hmn

/-- `c ≤ x²` for `c ≤ 4096²` and `x ≥ 4096`. -/
theorem const_le_sq {x c : ℝ} (hx : 4096 ≤ x) (hc : c ≤ 16777216) : c ≤ x ^ 2 := by nlinarith

/-- **The slack decomposed**: `|TT|·slack₁ + slack₂` is `|TT|·2c₀·|gainExps| + c_{dl,1}·2|A|·N_m²·log_p(2a) +
c_{dl,2}·|TT|·log_p(2a)²`, plus `|TT|·topAllow + 2|A|·orbAllow + e_p` at a candidate. -/
theorem slack_eq (p : ℕ) :
    Dg.TT.card * Dg.slack1 p + Dg.slack2 p =
      (Dg.TT.card * (2 * Dg.c0 * (gainExps x ε p).card) +
        (Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
          Kg.cdl₂ * Dg.TT.card * Real.logb p (2 * scA x ε) ^ 2)) +
      if p ∈ S.cand κ x ε Dg.R.k then
        Dg.TT.card * Dg.topAllow p + (2 * Fintype.card S.A * Dg.orbAllow p + Dg.eSand p) else 0 := by
  unfold slack1 slack2
  split_ifs <;> ring

/-- **The slacks off the candidates, at one prime**: `2 log p·m·(|TT|·2c₀·|gainExps| + c_{dl,1}·2|A|·N_m²·log_p(2a)
+ c_{dl,2}·|TT|·log_p(2a)²) ≤ x^{900}` for `2 ≤ p ≤ 2X″` (`N_m ≤ x^{403}` dominates). -/
theorem base_le (hs : Dg.LossSizes) {p : ℕ} (hp : 2 ≤ p) (hpX : (p : ℝ) ≤ 2 * S.cutX x ε) :
    2 * Real.log p * (Dg.R.m * (Dg.TT.card * (2 * Dg.c0 * (gainExps x ε p).card) +
      (Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
        Kg.cdl₂ * Dg.TT.card * Real.logb p (2 * scA x ε) ^ 2))) ≤ x ^ 900 := by
  have hx := hs.x_ge
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hyx := hs.y_le_x
  have hm := hs.m_le_x
  have hTT : (Dg.TT.card : ℝ) ≤ x ^ 3 := hs.TT_le.trans hs.A_le
  have hc0 := hs.c0_le
  have hc00 := Dg.c0_nonneg
  have hN := hs.N_le
  have hlp : Real.log p ≤ 6 * x ^ (1 / 8 : ℝ) := hs.log_le_of_le (by omega) hpX
  have hlp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have ha1 := one_le_scA ε hx1
  have hE := log_mul_card_gainExps_le (ε := ε) hx0 hp
  have hla := hs.log_two_scA_le
  have hla0 : 0 ≤ Real.log (2 * scA x ε) := Real.log_nonneg (by linarith)
  have hlb : Real.logb p (2 * scA x ε) ≤ 6 * x ^ (1 / 8 : ℝ) := by
    have := logb_le_two_mul hp (by linarith : (1 : ℝ) ≤ 2 * scA x ε); linarith
  have hlb0 : 0 ≤ Real.logb p (2 * scA x ε) := logb_nat_nonneg p (by linarith)
  have h2l := two_log_mul_logb hp (2 * scA x ε)
  have hc1 : (Kg.cdl₁ : ℝ) = 5 := by norm_num [Kg]
  have hc2 : (Kg.cdl₂ : ℝ) = 4 := by norm_num [Kg]
  have hlc := hs.log_ceil_le
  have t1 : 2 * Real.log p * (Dg.R.m * (Dg.TT.card * (2 * Dg.c0 * (gainExps x ε p).card))) ≤ x ^ 13 := by
    calc 2 * Real.log p * (Dg.R.m * (Dg.TT.card * (2 * Dg.c0 * (gainExps x ε p).card))) =
        4 * Dg.R.m * Dg.TT.card * Dg.c0 * (Real.log p * (gainExps x ε p).card) := by ring
      _ ≤ 4 * (2 * x) * x ^ 3 * (64 * x ^ 6) * (9 * x) := by
          gcongr 4 * ?_ * ?_ * ?_ * ?_
          linarith
      _ = 4608 * x ^ 11 := by ring
      _ ≤ x ^ 13 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
  have t2 : 2 * Real.log p * (Dg.R.m * (Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 *
      Real.logb p (2 * scA x ε))) ≤ x ^ 813 := by
    calc 2 * Real.log p * (Dg.R.m * (Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 *
        Real.logb p (2 * scA x ε))) = 10 * Dg.R.m * Fintype.card S.A * (Dg.R.N Dg.R.m : ℝ) ^ 2 *
          (2 * Real.log p * Real.logb p (2 * scA x ε)) := by rw [hc1]; ring
      _ ≤ 10 * (2 * x) * x ^ 3 * (x ^ 403) ^ 2 * (6 * x) := by
          rw [h2l]
          gcongr 10 * ?_ * ?_ * ?_ ^ 2 * ?_ <;> linarith [hs.A_le]
      _ = 120 * x ^ 811 := by ring
      _ ≤ x ^ 813 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
  have t3 : 2 * Real.log p * (Dg.R.m * (Kg.cdl₂ * Dg.TT.card * Real.logb p (2 * scA x ε) ^ 2)) ≤ x ^ 8 := by
    calc 2 * Real.log p * (Dg.R.m * (Kg.cdl₂ * Dg.TT.card * Real.logb p (2 * scA x ε) ^ 2)) =
        4 * Dg.R.m * Dg.TT.card * Real.logb p (2 * scA x ε) *
          (2 * Real.log p * Real.logb p (2 * scA x ε)) := by rw [hc2]; ring
      _ ≤ 4 * (2 * x) * x ^ 3 * (6 * x) * (6 * x) := by
          rw [h2l]
          gcongr 4 * ?_ * ?_ * ?_ * ?_ <;> linarith
      _ = 288 * x ^ 6 := by ring
      _ ≤ x ^ 8 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
  have e8 : x ^ 8 ≤ x ^ 13 := pow_le_pow_right₀ hx1 (by norm_num)
  have e13 : 3 * x ^ 813 ≤ x ^ 900 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
  have e813 : x ^ 13 ≤ x ^ 813 := pow_le_pow_right₀ hx1 (by norm_num)
  linear_combination t1 + t2 + t3 + e8 + 2 * e813 + e13

/-- **`n_p ≤ 2|A|`.** -/
theorem nP_le (c : S.A) (p : ℕ) : (S.nP c p : ℝ) ≤ 2 * Fintype.card S.A := by
  have h1 : orderOf (S.hPtw c p ^ 2) ≤ Fintype.card S.A := orderOf_le_card_univ
  have h2 : orderOf (S.hPtw c p) ≤ Fintype.card S.A := orderOf_le_card_univ
  have h3 : S.nP c p ≤ 2 * Fintype.card S.A := by
    unfold Setting.nP
    split_ifs <;> omega
  exact_mod_cast h3

/-- **`log_p a ≤ 4y`** for `p ≥ 2`. -/
theorem LossSizes.logb_scA_le (hs : Dg.LossSizes) {p : ℕ} (hp : 2 ≤ p) :
    Real.logb p (scA x ε) ≤ 4 * x ^ (1 / 8 : ℝ) := by
  have := logb_le_two_mul hp (one_le_scA ε (by linarith [hs.x_ge] : (1 : ℝ) ≤ x))
  linarith [hs.log_scA_le]

/-- **`D_p ≤ x^{47}`** for `p ≥ p₀`. -/
theorem Dexp_le (hs : Dg.LossSizes) {p : ℕ} (hp : 2 ≤ p) (hp₀ : scP0 x Dg.R.k ≤ p) :
    (Dg.Dexp p : ℝ) ≤ x ^ 47 := by
  have hx := hs.x_ge
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hyx := hs.y_le_x
  have hn := nP_le (S.twA κ) p
  have hδ := hs.δ_le
  have hδ0 : 0 ≤ scδ₁ x ε := Real.rpow_nonneg hx0.le _
  have hN1 : ((tilePar x ε Dg.R.k).N₁ : ℝ) ≤ x := by linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤
    (tilePar x ε Dg.R.k).r)]
  have hk := hs.k_le
  have hla := hs.logb_scA_le hp
  have hla0 : 0 ≤ Real.logb p (scA x ε) := logb_nat_nonneg p (one_le_scA ε hx1)
  have hc : (Kg.cD₁ : ℝ) = 100 := by norm_num [Kg]
  have hA := hs.A_le
  have harg : (Kg.cD₁ : ℝ) * 40 * S.nP (S.twA κ) p * scδ₁ x ε * x ^ 26 *
      (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 3) * Real.logb p (scA x ε) ≤ 288000 * x ^ 45 := by
    have h15 : x ^ 5 ≤ x ^ 15 := pow_le_pow_right₀ hx1 (by norm_num)
    calc (Kg.cD₁ : ℝ) * 40 * S.nP (S.twA κ) p * scδ₁ x ε * x ^ 26 *
        (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 3) * Real.logb p (scA x ε) ≤
        100 * 40 * (2 * x ^ 3) * 1 * x ^ 26 * (x ^ 5 + (2 * x ^ 5) ^ 3) * (4 * x) := by
          rw [hc]
          gcongr 100 * 40 * ?_ * ?_ * x ^ 26 * (?_ ^ 5 + ?_ ^ 3) * ?_ <;> linarith
      _ ≤ 100 * 40 * (2 * x ^ 3) * 1 * x ^ 26 * (9 * x ^ 15) * (4 * x) := by gcongr; linarith
      _ = 288000 * x ^ 45 := by ring
  unfold Dexp
  rw [ite_eq_left hp₀]
  have h0 : 0 ≤ (Kg.cD₁ : ℝ) * 40 * S.nP (S.twA κ) p * scδ₁ x ε * x ^ 26 *
      (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 3) * Real.logb p (scA x ε) := by positivity
  have := natCeil_le_add_one harg (by positivity)
  have h2 : 288000 * x ^ 45 + 1 ≤ x ^ 47 := by
    have : 288001 * x ^ 45 ≤ x ^ 47 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
    have : 1 ≤ x ^ 45 := one_le_pow₀ hx1
    linarith
  linarith

/-- **`c_dep ≤ x^{49}`** for `p ≥ p₀`. -/
theorem cDep_le (hs : Dg.LossSizes) {p : ℕ} (hp : 2 ≤ p) (hp₀ : scP0 x Dg.R.k ≤ p) : Dg.cDep p ≤ x ^ 49 := by
  have hx := hs.x_ge
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hyx := hs.y_le_x
  have hn := nP_le (S.twA κ) p
  have hn0 : (0 : ℝ) ≤ S.nP (S.twA κ) p := Nat.cast_nonneg _
  have hδ := hs.δ_le
  have hδ0 : 0 ≤ scδ₁ x ε := Real.rpow_nonneg hx0.le _
  have hk := hs.k_le
  have hla := hs.logb_scA_le hp
  have hla0 : 0 ≤ Real.logb p (scA x ε) := logb_nat_nonneg p (one_le_scA ε hx1)
  have hc : (Kg.cκ₂ : ℝ) = 100 := by norm_num [Kg]
  have hA := hs.A_le
  have hD := Dg.Dexp_le hs hp hp₀
  have hc0 := hs.c0_le
  have hc00 := Dg.c0_nonneg
  have hnA : (S.nP (S.twA κ) p : ℝ) ≤ 2 * x ^ 3 := by linarith
  have t1 : (Kg.cκ₂ : ℝ) * 40 * S.nP (S.twA κ) p * scδ₁ x ε * Dg.R.k * Real.logb p (scA x ε) ≤
      100 * 40 * (2 * x ^ 3) * 1 * (2 * x ^ 5) * (4 * x) := by
    rw [hc]
    gcongr 100 * 40 * ?_ * ?_ * ?_ * ?_
    linarith
  have t2 : 160 * (S.nP (S.twA κ) p : ℝ) * scδ₁ x ε * Dg.c0 ≤ 160 * (2 * x ^ 3) * 1 * (64 * x ^ 6) := by
    gcongr
  have t3 : 2 * (S.nP (S.twA κ) p : ℝ) * Dg.c0 ≤ 2 * (2 * x ^ 3) * (64 * x ^ 6) := by gcongr
  have e1 : (1 : ℝ) ≤ x ^ 9 := one_le_pow₀ hx1
  have e2 : x ^ 9 ≤ x ^ 47 := pow_le_pow_right₀ hx1 (by norm_num)
  have e3 : 10 * x ^ 47 ≤ x ^ 49 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
  have e4 : 64000 * x ^ 9 + 20480 * x ^ 9 + 256 * x ^ 9 + 8 ≤ x ^ 47 := by
    have : 84744 * x ^ 9 ≤ x ^ 47 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
    linarith
  unfold cDep
  linarith

/-- **`log p ≤ y`, `p^{G′} ≤ X′^{G′}`** for `1 ≤ p < X′`. -/
theorem LossSizes.log_pow_le (hs : Dg.LossSizes) {p : ℕ} (hp : 1 ≤ p) (hpX' : (p : ℝ) < scX' x ε) (G : ℕ) :
    Real.log p ≤ x ^ (1 / 8 : ℝ) ∧ (p : ℝ) ^ G ≤ scX' x ε ^ G := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨?_, pow_le_pow_left₀ hp0.le hpX'.le G⟩
  calc Real.log p ≤ Real.log (scX' x ε) := Real.log_le_log hp0 hpX'.le
    _ = x ^ (ε / 3) := Real.log_exp _
    _ ≤ _ := hs.L_le

/-- **`e_p·2 log p ≤ c_S·f·k²·2 log a + 2 log p`.** -/
theorem two_log_mul_eSand_le {p : ℕ} (hp : 2 ≤ p) (hx : 1 ≤ x) :
    2 * Real.log p * Dg.eSand p ≤ Kg.cS * S.f * (Dg.R.k : ℝ) ^ 2 * (2 * Real.log (scA x ε)) + 2 * Real.log p := by
  have hla0 : 0 ≤ Real.logb p (scA x ε) := logb_nat_nonneg p (one_le_scA ε hx)
  have h := natCeil_le_add_one (le_refl ((Kg.cS : ℝ) * S.f * (Dg.R.k : ℝ) ^ 2 * Real.logb p (scA x ε)))
    (by positivity)
  have hl : 0 ≤ 2 * Real.log p := by have := Real.log_natCast_nonneg p; linarith
  have h2 := mul_le_mul_of_nonneg_left h hl
  have e := two_log_mul_logb hp (scA x ε)
  unfold eSand
  calc 2 * Real.log p * (⌈(Kg.cS : ℝ) * S.f * (Dg.R.k : ℝ) ^ 2 * Real.logb p (scA x ε)⌉₊ : ℝ) ≤
      2 * Real.log p * ((Kg.cS : ℝ) * S.f * (Dg.R.k : ℝ) ^ 2 * Real.logb p (scA x ε) + 1) := h2
    _ = Kg.cS * S.f * (Dg.R.k : ℝ) ^ 2 * (2 * Real.log p * Real.logb p (scA x ε)) + 2 * Real.log p := by ring
    _ = _ := by rw [e]

/-- **The candidates' allowances at one prime `p ≥ p₀`**: `2 log p·m·(|TT|·topAllow + 2|A|·orbAllow + e_p)` is at
most `x^{900}·X′^{G′}` (the polynomial terms and `Q_p = p^{G′}`) plus the terms of size `a`:
`m|TT|·(2(b′/x)·log p + 2c_{κ,1}N₁·a·log p/p² + 2c_{κ,1}N₁·La·a/k·log p/p) + 4m|A|·c_Pr·w″·log p`. -/
theorem cpart_ge_le (hs : Dg.LossSizes) {p : ℕ} (hp : 2 ≤ p) (hpX' : (p : ℝ) < scX' x ε)
    (hp₀ : scP0 x Dg.R.k ≤ p) :
    2 * Real.log p * (Dg.R.m * (Dg.TT.card * Dg.topAllow p +
        (2 * Fintype.card S.A * Dg.orbAllow p + Dg.eSand p))) ≤
      x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G' +
        Dg.R.m * Dg.TT.card * (2 * (scB' x ε / x) * Real.log p +
          2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scA x ε * (Real.log p / (p : ℝ) ^ 2) +
          2 * Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * scLa x ε Dg.R.k * scA x ε / Dg.R.k * (Real.log p / p)) +
        4 * Dg.R.m * Fintype.card S.A * Kg.cPr * scW'' S x ε * Real.log p := by
  have hx := hs.x_ge
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hyx := hs.y_le_x
  have hm := hs.m_le_x
  have hTT : (Dg.TT.card : ℝ) ≤ x ^ 3 := hs.TT_le.trans hs.A_le
  have hA := hs.A_le
  have hc0 := hs.c0_le
  have hc00 := Dg.c0_nonneg
  have heta := hs.eta_le
  have heta0 := Dg.eta_nonneg
  have hN := hs.N_le
  have hk := hs.k_le
  have hf := hs.f_le
  have hδ := hs.δ_le
  have hδ0 : 0 ≤ scδ₁ x ε := Real.rpow_nonneg hx0.le _
  have hN1 : ((tilePar x ε Dg.R.k).N₁ : ℝ) ≤ x := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).r)]
  obtain ⟨hL, hQ⟩ := hs.log_pow_le (by omega) hpX' (tilePar x ε Dg.R.k).G'
  have hL0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hla2 : 2 * Real.log p * Real.logb p (scA x ε) ≤ 4 * x := by
    rw [two_log_mul_logb hp]; linarith [hs.log_scA_le]
  have hla0 : 0 ≤ Real.logb p (scA x ε) := logb_nat_nonneg p (one_le_scA ε hx1)
  have hcD := Dg.cDep_le hs hp hp₀
  have hcD0 : 0 ≤ Dg.cDep p := by
    unfold cDep
    have : 0 ≤ Real.logb p (scA x ε) := hla0
    positivity
  have hE := Dg.two_log_mul_eSand_le hp hx1
  have hla := hs.log_scA_le
  have hla' : 0 ≤ Real.log (scA x ε) := Real.log_nonneg (one_le_scA ε hx1)
  have hP1 : (1 : ℝ) ≤ scX' x ε ^ (tilePar x ε Dg.R.k).G' :=
    one_le_pow₀ (Real.one_le_exp (Real.rpow_nonneg hx0.le _))
  have hQ0 : (0 : ℝ) ≤ (p : ℝ) ^ (tilePar x ε Dg.R.k).G' := by positivity
  unfold topAllow orbAllow
  rw [ite_eq_left hp₀, ite_eq_left hp₀]
  have k1 : (Kg.cκ₂ : ℝ) = 100 := by norm_num [Kg]
  have k2 : (Kg.cPr : ℝ) = 1 := by norm_num [Kg]
  have k3 : (Kg.cD₁ : ℝ) = 100 := by norm_num [Kg]
  have k4 : (Kg.cS : ℝ) = 100 := by norm_num [Kg]
  generalize scX' x ε ^ (tilePar x ε Dg.R.k).G' = P at hP1 hQ ⊢
  generalize (p : ℝ) ^ (tilePar x ε Dg.R.k).G' = Q at hQ0 hQ ⊢
  have hLx : Real.log p ≤ x := hL.trans hyx
  have e6 : 64 * x ^ 6 ≤ x ^ 410 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
  have e403 : x ^ 403 ≤ x ^ 410 := pow_le_pow_right₀ hx1 (by norm_num)
  -- the polynomial terms
  have hA1 : Dg.R.m * Dg.TT.card * (2 * Real.log p * (Dg.c0 + 1 + Dg.eta)) ≤ x ^ 417 * P := by
    have h1 : Dg.c0 + 1 + Dg.eta ≤ 2 * x ^ 410 := by linarith
    calc Dg.R.m * Dg.TT.card * (2 * Real.log p * (Dg.c0 + 1 + Dg.eta)) ≤ (2 * x) * x ^ 3 * (2 * x * (2 * x ^ 410)) := by
          gcongr ?_ * ?_ * (2 * ?_ * ?_)
      _ = 8 * x ^ 415 := by ring
      _ ≤ x ^ 417 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
      _ ≤ x ^ 417 * P := le_mul_of_one_le_right (by positivity) hP1
  have hA5 : Dg.R.m * Dg.TT.card * (Kg.cκ₂ * (2 * Real.log p * (Q * Dg.cDep p + Dg.R.k * Q))) ≤ x ^ 56 * P := by
    have h1 : Q * Dg.cDep p + Dg.R.k * Q ≤ 2 * x ^ 49 * P := by
      have h5 : (Dg.R.k : ℝ) ≤ x ^ 49 := hk.trans (mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num))
      have : Q * (Dg.cDep p + Dg.R.k) ≤ P * (x ^ 49 + x ^ 49) := by gcongr
      linarith
    calc Dg.R.m * Dg.TT.card * (Kg.cκ₂ * (2 * Real.log p * (Q * Dg.cDep p + Dg.R.k * Q))) ≤
        (2 * x) * x ^ 3 * (100 * (2 * x * (2 * x ^ 49 * P))) := by
          rw [k1]; gcongr ?_ * ?_ * (100 * (2 * ?_ * ?_))
      _ = 800 * x ^ 54 * P := by ring
      _ ≤ x ^ 56 * P := by
          gcongr; exact mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
  have hA6 : Dg.R.m * Dg.TT.card * (Kg.cκ₂ * Dg.R.k * (2 * Real.log p * Real.logb p (scA x ε))) ≤ x ^ 11 * P := by
    calc Dg.R.m * Dg.TT.card * (Kg.cκ₂ * Dg.R.k * (2 * Real.log p * Real.logb p (scA x ε))) ≤
        (2 * x) * x ^ 3 * (100 * (2 * x ^ 5) * (4 * x)) := by
          rw [k1]; gcongr ?_ * ?_ * (100 * ?_ * ?_)
      _ = 1600 * x ^ 10 := by ring
      _ ≤ x ^ 11 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
      _ ≤ x ^ 11 * P := le_mul_of_one_le_right (by positivity) hP1
  have hA7 : Dg.R.m * Dg.TT.card * (Kg.cκ₂ * (2 * Real.log p * Dg.c0)) ≤ x ^ 13 * P := by
    calc Dg.R.m * Dg.TT.card * (Kg.cκ₂ * (2 * Real.log p * Dg.c0)) ≤
        (2 * x) * x ^ 3 * (100 * (2 * x * (64 * x ^ 6))) := by
          rw [k1]; gcongr ?_ * ?_ * (100 * (2 * ?_ * ?_))
      _ = 25600 * x ^ 11 := by ring
      _ ≤ x ^ 13 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
      _ ≤ x ^ 13 * P := le_mul_of_one_le_right (by positivity) hP1
  have hB2 : Dg.R.m * (2 * Fintype.card S.A) * (2 * Real.log p * (Kg.cPr * (Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) +
      2 * Dg.c0 + 3)) ≤ x ^ 417 * P := by
    have h1 : (Kg.cPr : ℝ) * (Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) + 2 * Dg.c0 + 3 ≤ 6 * x ^ 410 := by
      have : (2 : ℝ) ≤ x ^ 410 := by have := le_self_pow₀ hx1 (show 410 ≠ 0 by norm_num); linarith
      rw [k2]; linarith
    calc Dg.R.m * (2 * Fintype.card S.A) * (2 * Real.log p * (Kg.cPr * (Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) +
        2 * Dg.c0 + 3)) ≤ (2 * x) * (2 * x ^ 3) * (2 * x * (6 * x ^ 410)) := by
          gcongr ?_ * (2 * ?_) * (2 * ?_ * ?_)
      _ = 48 * x ^ 415 := by ring
      _ ≤ x ^ 417 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
      _ ≤ x ^ 417 * P := le_mul_of_one_le_right (by positivity) hP1
  have hB3 : Dg.R.m * (2 * Fintype.card S.A) * (Kg.cD₁ * 40 * scδ₁ x ε * x ^ 26 *
      (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 3) * (2 * Real.log p * Real.logb p (scA x ε))) ≤
      x ^ 48 * P := by
    have h15 : x ^ 5 ≤ x ^ 15 := pow_le_pow_right₀ hx1 (by norm_num)
    calc Dg.R.m * (2 * Fintype.card S.A) * (Kg.cD₁ * 40 * scδ₁ x ε * x ^ 26 *
        (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 3) * (2 * Real.log p * Real.logb p (scA x ε))) ≤
        (2 * x) * (2 * x ^ 3) * (100 * 40 * 1 * x ^ 26 * (x ^ 5 + (2 * x ^ 5) ^ 3) * (4 * x)) := by
          rw [k3]; gcongr ?_ * (2 * ?_) * (100 * 40 * ?_ * x ^ 26 * (?_ ^ 5 + ?_ ^ 3) * ?_)
      _ ≤ (2 * x) * (2 * x ^ 3) * (100 * 40 * 1 * x ^ 26 * (9 * x ^ 15) * (4 * x)) := by gcongr; linarith
      _ = 576000 * x ^ 46 := by ring
      _ ≤ x ^ 48 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
      _ ≤ x ^ 48 * P := le_mul_of_one_le_right (by positivity) hP1
  have hEs : Dg.R.m * (2 * Real.log p * Dg.eSand p) ≤ x ^ 19 * P := by
    have h1 : (Kg.cS : ℝ) * S.f * (Dg.R.k : ℝ) ^ 2 * (2 * Real.log (scA x ε)) + 2 * Real.log p ≤ 3202 * x ^ 16 := by
      have : (Kg.cS : ℝ) * S.f * (Dg.R.k : ℝ) ^ 2 * (2 * Real.log (scA x ε)) ≤
          100 * (2 * x ^ 5) * (2 * x ^ 5) ^ 2 * (2 * (2 * x)) := by
        rw [k4]; gcongr 100 * ?_ * ?_ ^ 2 * (2 * ?_); linarith
      have h16 : x ≤ x ^ 16 := le_self_pow₀ hx1 (by norm_num)
      have e : 100 * (2 * x ^ 5) * (2 * x ^ 5) ^ 2 * (2 * (2 * x)) = 3200 * x ^ 16 := by ring
      linarith
    calc Dg.R.m * (2 * Real.log p * Dg.eSand p) ≤ (2 * x) * (3202 * x ^ 16) :=
          mul_le_mul hm (hE.trans h1) (by positivity) (by positivity)
      _ = 6404 * x ^ 17 := by ring
      _ ≤ x ^ 19 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
      _ ≤ x ^ 19 * P := le_mul_of_one_le_right (by positivity) hP1
  have hfin : x ^ 417 * P + x ^ 56 * P + x ^ 11 * P + x ^ 13 * P + x ^ 417 * P + x ^ 48 * P + x ^ 19 * P ≤
      x ^ 900 * P := by
    have h1 : x ^ 56 ≤ x ^ 417 := pow_le_pow_right₀ hx1 (by norm_num)
    have h2 : x ^ 11 ≤ x ^ 417 := pow_le_pow_right₀ hx1 (by norm_num)
    have h3 : x ^ 13 ≤ x ^ 417 := pow_le_pow_right₀ hx1 (by norm_num)
    have h4 : x ^ 48 ≤ x ^ 417 := pow_le_pow_right₀ hx1 (by norm_num)
    have h5 : x ^ 19 ≤ x ^ 417 := pow_le_pow_right₀ hx1 (by norm_num)
    have h6 : 7 * x ^ 417 ≤ x ^ 900 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
    have : x ^ 417 + x ^ 56 + x ^ 11 + x ^ 13 + x ^ 417 + x ^ 48 + x ^ 19 ≤ x ^ 900 := by linarith
    calc x ^ 417 * P + x ^ 56 * P + x ^ 11 * P + x ^ 13 * P + x ^ 417 * P + x ^ 48 * P + x ^ 19 * P =
        (x ^ 417 + x ^ 56 + x ^ 11 + x ^ 13 + x ^ 417 + x ^ 48 + x ^ 19) * P := by ring
      _ ≤ x ^ 900 * P := mul_le_mul_of_nonneg_right this (by linarith)
  linear_combination hA1 + hA5 + hA6 + hA7 + hB2 + hB3 + hEs + hfin

/-- **The candidates' allowances at one prime `p < p₀`**: `2 log p·m·(|TT|·topAllow + 2|A|·orbAllow + e_p)` is at
most `x^{900}·X′^{G′}` plus the terms of size `a`: `m|TT|·(4r(1 + c_t)·b′·log p + 2c_t·r·La·a/k·log p/p +
2c_t·r·(a/(kx^{26})⁴)·log p) + 4m|A|·(r·w″ + 80rδ₁·b′)·log p` (`p^{L₁(p)} ≥ (kx^{26})⁴`). -/
theorem cpart_lt_le (hs : Dg.LossSizes) {p : ℕ} (hp : 2 ≤ p) (hpX' : (p : ℝ) < scX' x ε)
    (hp₀ : ¬ scP0 x Dg.R.k ≤ p) :
    2 * Real.log p * (Dg.R.m * (Dg.TT.card * Dg.topAllow p +
        (2 * Fintype.card S.A * Dg.orbAllow p + Dg.eSand p))) ≤
      x ^ 900 * scX' x ε ^ (tilePar x ε Dg.R.k).G' +
        Dg.R.m * Dg.TT.card * (4 * (tilePar x ε Dg.R.k).r * (1 + Kg.ct) * scB' x ε * Real.log p +
          2 * Kg.ct * (tilePar x ε Dg.R.k).r * scLa x ε Dg.R.k * scA x ε / Dg.R.k * (Real.log p / p) +
          2 * Kg.ct * (tilePar x ε Dg.R.k).r * (scA x ε / ((Dg.R.k : ℝ) * x ^ 26) ^ 4) * Real.log p) +
        4 * Dg.R.m * Fintype.card S.A * ((tilePar x ε Dg.R.k).r * scW'' S x ε +
          80 * (tilePar x ε Dg.R.k).r * scδ₁ x ε * scB' x ε) * Real.log p := by
  have hx := hs.x_ge
  have hx0 := hs.x_pos
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hyx := hs.y_le_x
  have hm := hs.m_le_x
  have hTT : (Dg.TT.card : ℝ) ≤ x ^ 3 := hs.TT_le.trans hs.A_le
  have hA := hs.A_le
  have hc0 := hs.c0_le
  have hc00 := Dg.c0_nonneg
  have heta := hs.eta_le
  have heta0 := Dg.eta_nonneg
  have hN := hs.N_le
  have hk := hs.k_le
  have hk1 : (1 : ℝ) ≤ Dg.R.k := Dg.one_le_k
  have hf := hs.f_le
  have hδ := hs.δ_le
  have hδ0 : 0 ≤ scδ₁ x ε := Real.rpow_nonneg hx0.le _
  have hN1 : ((tilePar x ε Dg.R.k).N₁ : ℝ) ≤ x := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).r)]
  have hr : ((tilePar x ε Dg.R.k).r : ℝ) ≤ x := by
    linarith [hs.N₁r_le, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).N₁)]
  have hr0 : (0 : ℝ) ≤ (tilePar x ε Dg.R.k).r := Nat.cast_nonneg _
  obtain ⟨hL, hQ⟩ := hs.log_pow_le (by omega) hpX' (tilePar x ε Dg.R.k).G'
  have hL0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hLx : Real.log p ≤ x := hL.trans hyx
  have hla2 : 2 * Real.log p * Real.logb p (scA x ε) ≤ 4 * x := by
    rw [two_log_mul_logb hp]; linarith [hs.log_scA_le]
  have hla0 : 0 ≤ Real.logb p (scA x ε) := logb_nat_nonneg p (one_le_scA ε hx1)
  have hE := Dg.two_log_mul_eSand_le hp hx1
  have hla := hs.log_scA_le
  have hla' : 0 ≤ Real.log (scA x ε) := Real.log_nonneg (one_le_scA ε hx1)
  have ha0 : 0 ≤ scA x ε := (scA_pos ε hx0).le
  have hP1 : (1 : ℝ) ≤ scX' x ε ^ (tilePar x ε Dg.R.k).G' :=
    one_le_pow₀ (Real.one_le_exp (Real.rpow_nonneg hx0.le _))
  have hQ0 : (0 : ℝ) ≤ (p : ℝ) ^ (tilePar x ε Dg.R.k).G' := by positivity
  have k1 : (Kg.ct : ℝ) = 100 := by norm_num [Kg]
  have k3 : (Kg.cD₂ : ℝ) = 100 := by norm_num [Kg]
  have k4 : (Kg.cS : ℝ) = 100 := by norm_num [Kg]
  -- `a/p^{L₁} ≤ a/(kx^{26})⁴`
  have hY := pow_scL1_ge hx0 (k := Dg.R.k) (by exact_mod_cast hk1) hp
  have hY0 : 0 < ((Dg.R.k : ℝ) * x ^ 26) ^ 4 := by positivity
  have hC4 : Dg.R.m * Dg.TT.card * (2 * Real.log p * (Kg.ct * (tilePar x ε Dg.R.k).r *
      (scA x ε / (p : ℝ) ^ scL1 x Dg.R.k p))) ≤
      Dg.R.m * Dg.TT.card * (2 * Kg.ct * (tilePar x ε Dg.R.k).r * (scA x ε / ((Dg.R.k : ℝ) * x ^ 26) ^ 4) *
        Real.log p) := by
    have h1 : scA x ε / (p : ℝ) ^ scL1 x Dg.R.k p ≤ scA x ε / ((Dg.R.k : ℝ) * x ^ 26) ^ 4 :=
      div_le_div_of_nonneg_left ha0 hY0 hY
    have h2 : (0 : ℝ) ≤ Dg.R.m * Dg.TT.card * (2 * Real.log p * (Kg.ct * (tilePar x ε Dg.R.k).r)) := by
      positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    linarith
  unfold topAllow orbAllow
  rw [ite_eq_right hp₀, ite_eq_right hp₀]
  generalize scX' x ε ^ (tilePar x ε Dg.R.k).G' = P at hP1 hQ ⊢
  generalize (p : ℝ) ^ (tilePar x ε Dg.R.k).G' = Q at hQ0 hQ ⊢
  have e6 : 64 * x ^ 6 ≤ x ^ 410 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
  have e403 : x ^ 403 ≤ x ^ 410 := pow_le_pow_right₀ hx1 (by norm_num)
  have hC1 : Dg.R.m * Dg.TT.card * (2 * Real.log p * (1 + (tilePar x ε Dg.R.k).r * Dg.c0 +
      Kg.ct * (tilePar x ε Dg.R.k).r * (2 * Dg.c0))) ≤ x ^ 15 * P := by
    have h1 : 1 + (tilePar x ε Dg.R.k).r * Dg.c0 + Kg.ct * (tilePar x ε Dg.R.k).r * (2 * Dg.c0) ≤ x ^ 9 := by
      have a1 : ((tilePar x ε Dg.R.k).r : ℝ) * Dg.c0 ≤ 64 * x ^ 7 :=
        calc ((tilePar x ε Dg.R.k).r : ℝ) * Dg.c0 ≤ x * (64 * x ^ 6) := by gcongr
          _ = 64 * x ^ 7 := by ring
      have a2 : (1 : ℝ) ≤ x ^ 7 := one_le_pow₀ hx1
      have a3 : 12865 * x ^ 7 ≤ x ^ 9 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
      rw [k1]
      linarith
    calc Dg.R.m * Dg.TT.card * (2 * Real.log p * (1 + (tilePar x ε Dg.R.k).r * Dg.c0 +
        Kg.ct * (tilePar x ε Dg.R.k).r * (2 * Dg.c0))) ≤ (2 * x) * x ^ 3 * (2 * x * x ^ 9) := by
          gcongr ?_ * ?_ * (2 * ?_ * ?_)
      _ = 4 * x ^ 14 := by ring
      _ ≤ x ^ 15 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
      _ ≤ x ^ 15 * P := le_mul_of_one_le_right (by positivity) hP1
  have hC5 : Dg.R.m * Dg.TT.card * (2 * Real.log p * (Kg.ct * (tilePar x ε Dg.R.k).r * (Dg.R.k * Q))) ≤
      x ^ 13 * P := by
    calc Dg.R.m * Dg.TT.card * (2 * Real.log p * (Kg.ct * (tilePar x ε Dg.R.k).r * (Dg.R.k * Q))) ≤
        (2 * x) * x ^ 3 * (2 * x * (100 * x * ((2 * x ^ 5) * P))) := by
          rw [k1]; gcongr ?_ * ?_ * (2 * ?_ * (100 * ?_ * (?_ * ?_)))
      _ = 800 * x ^ 11 * P := by ring
      _ ≤ x ^ 13 * P := by
          gcongr; exact mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
  have hD2 : Dg.R.m * (2 * Fintype.card S.A) * (2 * Real.log p * ((tilePar x ε Dg.R.k).r *
      (Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) + 4 * (tilePar x ε Dg.R.k).r * Dg.c0 +
      (tilePar x ε Dg.R.k).r * 40 * scδ₁ x ε * (2 * Dg.c0) + 3)) ≤ x ^ 418 * P := by
    have h1 : ((tilePar x ε Dg.R.k).r : ℝ) * (Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) +
        4 * (tilePar x ε Dg.R.k).r * Dg.c0 + (tilePar x ε Dg.R.k).r * 40 * scδ₁ x ε * (2 * Dg.c0) + 3 ≤
        100 * x ^ 411 := by
      have a1 : ((tilePar x ε Dg.R.k).r : ℝ) * (Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) ≤ 3 * x ^ 411 :=
        calc ((tilePar x ε Dg.R.k).r : ℝ) * (Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) ≤ x * (3 * x ^ 410) := by
              gcongr; linarith
          _ = 3 * x ^ 411 := by ring
      have a2 : 4 * ((tilePar x ε Dg.R.k).r : ℝ) * Dg.c0 ≤ 4 * x ^ 411 :=
        calc 4 * ((tilePar x ε Dg.R.k).r : ℝ) * Dg.c0 ≤ 4 * x * x ^ 410 := by gcongr; linarith
          _ = 4 * x ^ 411 := by ring
      have a3 : ((tilePar x ε Dg.R.k).r : ℝ) * 40 * scδ₁ x ε * (2 * Dg.c0) ≤ 80 * x ^ 411 :=
        calc ((tilePar x ε Dg.R.k).r : ℝ) * 40 * scδ₁ x ε * (2 * Dg.c0) ≤ x * 40 * 1 * (2 * x ^ 410) := by
              gcongr; linarith
          _ = 80 * x ^ 411 := by ring
      have a4 : (3 : ℝ) ≤ x ^ 411 := by have := le_self_pow₀ hx1 (show 411 ≠ 0 by norm_num); linarith
      linarith
    calc Dg.R.m * (2 * Fintype.card S.A) * (2 * Real.log p * ((tilePar x ε Dg.R.k).r *
        (Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) + 4 * (tilePar x ε Dg.R.k).r * Dg.c0 +
        (tilePar x ε Dg.R.k).r * 40 * scδ₁ x ε * (2 * Dg.c0) + 3)) ≤
        (2 * x) * (2 * x ^ 3) * (2 * x * (100 * x ^ 411)) := by
          gcongr ?_ * (2 * ?_) * (2 * ?_ * ?_)
      _ = 800 * x ^ 416 := by ring
      _ ≤ x ^ 418 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
      _ ≤ x ^ 418 * P := le_mul_of_one_le_right (by positivity) hP1
  have hD3 : Dg.R.m * (2 * Fintype.card S.A) * (Kg.cD₂ * 40 * scδ₁ x ε * (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 3 +
      ((tilePar x ε Dg.R.k).r : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 2) * (2 * Real.log p * Real.logb p (scA x ε))) ≤
      x ^ 17 * P := by
    have h3 : x ^ 3 ≤ x ^ 10 := pow_le_pow_right₀ hx1 (by norm_num)
    have h5 : x ^ 5 ≤ x ^ 10 := pow_le_pow_right₀ hx1 (by norm_num)
    calc Dg.R.m * (2 * Fintype.card S.A) * (Kg.cD₂ * 40 * scδ₁ x ε * (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 3 +
        ((tilePar x ε Dg.R.k).r : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 2) * (2 * Real.log p * Real.logb p (scA x ε))) ≤
        (2 * x) * (2 * x ^ 3) * (100 * 40 * 1 * (x ^ 3 + x ^ 5 + (2 * x ^ 5) ^ 2) * (4 * x)) := by
          rw [k3]; gcongr ?_ * (2 * ?_) * (100 * 40 * ?_ * (?_ ^ 3 + ?_ ^ 5 + ?_ ^ 2) * ?_)
      _ ≤ (2 * x) * (2 * x ^ 3) * (100 * 40 * 1 * (6 * x ^ 10) * (4 * x)) := by
          have e : (2 * x ^ 5) ^ 2 = 4 * x ^ 10 := by ring
          gcongr; linarith
      _ = 384000 * x ^ 15 := by ring
      _ ≤ x ^ 17 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
      _ ≤ x ^ 17 * P := le_mul_of_one_le_right (by positivity) hP1
  have hEs : Dg.R.m * (2 * Real.log p * Dg.eSand p) ≤ x ^ 19 * P := by
    have h1 : (Kg.cS : ℝ) * S.f * (Dg.R.k : ℝ) ^ 2 * (2 * Real.log (scA x ε)) + 2 * Real.log p ≤
        3202 * x ^ 16 := by
      have : (Kg.cS : ℝ) * S.f * (Dg.R.k : ℝ) ^ 2 * (2 * Real.log (scA x ε)) ≤
          100 * (2 * x ^ 5) * (2 * x ^ 5) ^ 2 * (2 * (2 * x)) := by
        rw [k4]; gcongr 100 * ?_ * ?_ ^ 2 * (2 * ?_); linarith
      have h16 : x ≤ x ^ 16 := le_self_pow₀ hx1 (by norm_num)
      have e : 100 * (2 * x ^ 5) * (2 * x ^ 5) ^ 2 * (2 * (2 * x)) = 3200 * x ^ 16 := by ring
      linarith
    calc Dg.R.m * (2 * Real.log p * Dg.eSand p) ≤ (2 * x) * (3202 * x ^ 16) :=
          mul_le_mul hm (hE.trans h1) (by positivity) (by positivity)
      _ = 6404 * x ^ 17 := by ring
      _ ≤ x ^ 19 := mul_pow_le_pow hx1 (k := 2) (const_le_sq hx (by norm_num)) (by norm_num)
      _ ≤ x ^ 19 * P := le_mul_of_one_le_right (by positivity) hP1
  have hfin : x ^ 15 * P + x ^ 13 * P + x ^ 418 * P + x ^ 17 * P + x ^ 19 * P ≤ x ^ 900 * P := by
    have h1 : x ^ 15 ≤ x ^ 418 := pow_le_pow_right₀ hx1 (by norm_num)
    have h2 : x ^ 13 ≤ x ^ 418 := pow_le_pow_right₀ hx1 (by norm_num)
    have h3 : x ^ 17 ≤ x ^ 418 := pow_le_pow_right₀ hx1 (by norm_num)
    have h4 : x ^ 19 ≤ x ^ 418 := pow_le_pow_right₀ hx1 (by norm_num)
    have h6 : 5 * x ^ 418 ≤ x ^ 900 := mul_pow_le_pow hx1 (k := 1) (by linarith) (by norm_num)
    have : x ^ 15 + x ^ 13 + x ^ 418 + x ^ 17 + x ^ 19 ≤ x ^ 900 := by linarith
    calc x ^ 15 * P + x ^ 13 * P + x ^ 418 * P + x ^ 17 * P + x ^ 19 * P =
        (x ^ 15 + x ^ 13 + x ^ 418 + x ^ 17 + x ^ 19) * P := by ring
      _ ≤ x ^ 900 * P := mul_le_mul_of_nonneg_right this (by linarith)
  linear_combination hC1 + hC4 + hC5 + hD2 + hD3 + hEs + hfin

end SharpDesign

end

end ZetaBalance
