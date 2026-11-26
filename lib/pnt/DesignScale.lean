import CMHost

/-!
# The scale, the growth package and the ranks of the design

A step of the proof of the sharp frontier (`SharpInputs`, the field `SharpPieces.params`): the functions of `x` and
`ε` that fix the sizes of a design at `x` (`SharpDesign`), the explicit inequalities between them that hold for large
`x`, and the ranks `(k, m, t)` (`Setting.Ranks`).

**The scale.** `L = x^ε` (`scL`), `b = e^L` (`scB`), `a = x·b` (`scA`, the scale of the `a_t`),
`X′ = exp(x^{ε/3})` (`scX'`), `b′ = a/X′` (`scB'`, the size of the top weights), `w″ = b′/(x·|A|)` (`scW''`, the
size of the thin weights), `δ₁ = x^{−ε/8}` (`scδ₁`, the density of the tops), `L_w = 10⌈405 log x⌉ + 2⌈30/ε⌉ + 22`
(`scLw`, the length of the orbit windows of the thick set), `TO = ⌈x^{377}⌉` (`scTO`) and
`nW = 8⌈10r(f + f²(k − 1)³L²/m)/8⌉` (`scNW`). The cut-off of the inert places is `a/w″ = x·|A|·X′`, the repo's
`Setting.cutX` (`scA_div_scW''`).

**The growth package** (`DesignBig ε x`): `0 < ε < 1/52`, `x > 1`, and seven inequalities between powers of `x`,
`exp(x^{cε})` and powers of `log x`, each with a strict margin in the exponent; the structure's docstring says which
size fact of the design each one serves. All of them hold for large `x` (`eventually_designBig`). Each clause follows
at one `x` from a bound `C ≤ x^a`, `a > 0`, which holds for large `x` (`tendsto_rpow_atTop`), and from
`log x ≤ x^δ/δ` (`Real.log_le_rpow_div`) at a suitable `δ`; an exponential clause is compared through its logarithm.

**The ranks** (`designRanks`), for `x^{2+8ε} ≤ |A| ≤ 2x^{2+8ε+ε/100}`: `k = 2⌈x^{9/2+10ε}/2⌉`,
`m = 2⌈x^{1/2−ε/16}/2⌉` (`x^{1/2−ε/16} = √(xδ₁)`) and `t = 8fr + 4 + TO·nW − r`, with `r = k + m − 1` and `f = 2|A|`.
They have `k ∈ [x^{9/2+10ε}, 2x^{9/2+10ε}]`, `m ∈ [x^{1/2−ε/16}, 2x^{1/2−ε/16}]`, `r + t = 8fr + 4 + TO·nW`,
`r ≤ 3x^{9/2+10ε}` (`designRanks_r_le`) and `t ≤ x^{401}`. The obligations of `Setting.Ranks`: `t` is odd since `r` is odd and `nW` is a
multiple of `8`; `t ≥ 7r + 4` gives `k + m + 4 ≤ t`, `3m < t` and `m² ≤ m(t + 1)`; and `m + 3 ≤ k`, `m ≤ f ≤ k`
and `t ≤ x^{401}` are comparisons of powers of `y = x^{1/100} ≥ 4096`, as `ε < 1/52` puts every exponent between two
hundredths: `y^{450} ≤ k ≤ 2y^{470}`, `y^{49} ≤ m ≤ 2y^{50}`, `y^{200} ≤ |A| ≤ 2y^{216}`, `L² ≤ y⁴` and
`TO ≤ 2y^{37700}`, so `nW ≤ 3968y^{2267}` and `t ≤ 8036y^{39967} ≤ y^{40100}`.

**The Behrend density** (`eventually_behrend`): `8L_w·exp(C√(3 log x·log(2L_w + 1))) ≤ x^{ε/2}` for large `x`, at
every `C ≥ 0`. In `ℓ = log x`: `L_w ≤ 4051ℓ`, so `log(2L_w + 1)` and `log(8L_w)` are at most `2 log ℓ`, and
`log ℓ ≤ cℓ` for large `ℓ` (`Real.isLittleO_log_id_atTop`). At `C = 6`, the constant of the relation-free sets
(`RelFree.exists_six`), it makes the design's thick set dense enough.

**Choices.**
* `DesignBig` carries `0 < ε < 1/52` and `x > 1`, so that it alone is the size clause of the design.
* One clause, `big` (`x^{ε/100} ≥ 4096`), replaces the absolute comparisons (`t ≤ x^{401}` among them): every
  comparison of a constant `≤ 4096` with a power of `x` of exponent `≥ ε/100` follows from it (`DesignBig.le_rpow`).
* The Behrend density is not a clause of `DesignBig`: only the construction of the design needs it, not the
  pieces.
* `m` is defined through `x^{1/2−ε/16}`, which equals `√(xδ₁)` for `x > 0`.
-/

open Filter

namespace ZetaBalance

/-! ## The scale -/

/-- `L = x^ε`, the logarithmic scale of the design. -/
noncomputable def scL (x ε : ℝ) : ℝ := x ^ ε

/-- `b = e^L = exp(x^ε)`. -/
noncomputable def scB (x ε : ℝ) : ℝ := Real.exp (scL x ε)

/-- `a = x·b`, the scale of the `a_t`. -/
noncomputable def scA (x ε : ℝ) : ℝ := x * scB x ε

/-- `X′ = exp(x^{ε/3})`. -/
noncomputable def scX' (x ε : ℝ) : ℝ := Real.exp (x ^ (ε / 3))

/-- `b′ = a/X′`, the size of the top weights. -/
noncomputable def scB' (x ε : ℝ) : ℝ := scA x ε / scX' x ε

/-- `w″ = b′/(x·|A|)`, the size of the thin weights. -/
noncomputable def scW'' (S : Setting) (x ε : ℝ) : ℝ := scB' x ε / (x * Fintype.card S.A)

/-- `δ₁ = x^{−ε/8}`, the density of the tops. -/
noncomputable def scδ₁ (x ε : ℝ) : ℝ := x ^ (-(ε / 8))

/-- `L_w = 10⌈405 log x⌉ + 2⌈30/ε⌉ + 22`, the length of the orbit windows of the thick set. -/
noncomputable def scLw (x ε : ℝ) : ℕ := 10 * ⌈405 * Real.log x⌉₊ + 2 * ⌈30 / ε⌉₊ + 22

/-- `TO = ⌈x^{377}⌉`, the factor of `nW` in `r + t`. -/
noncomputable def scTO (x : ℝ) : ℕ := ⌈x ^ 377⌉₊

/-- `nW = 8⌈10r(f + f²(k − 1)³L²/m)/8⌉`, a multiple of `8`. -/
noncomputable def scNW (f k m r : ℕ) (L : ℝ) : ℕ :=
  8 * ⌈10 * r * (f + f ^ 2 * ((k : ℝ) - 1) ^ 3 * L ^ 2 / m) / 8⌉₊

/-- `a > 0`. -/
theorem scA_pos {x : ℝ} (ε : ℝ) (hx : 0 < x) : 0 < scA x ε := mul_pos hx (Real.exp_pos _)

/-- `b′ > 0`. -/
theorem scB'_pos {x : ℝ} (ε : ℝ) (hx : 0 < x) : 0 < scB' x ε := div_pos (scA_pos ε hx) (Real.exp_pos _)

/-- `w″ > 0`. -/
theorem scW''_pos (S : Setting) {x : ℝ} (ε : ℝ) (hx : 0 < x) : 0 < scW'' S x ε :=
  div_pos (scB'_pos ε hx) (mul_pos hx (Nat.cast_pos.2 Fintype.card_pos))

/-- `a/w″ = x·|A|·X′`, the cut-off `Setting.cutX` of the inert places. -/
theorem scA_div_scW'' (S : Setting) {x : ℝ} (ε : ℝ) (hx : 0 < x) :
    scA x ε / scW'' S x ε = x * Fintype.card S.A * scX' x ε := by
  have h1 := scA_pos ε hx
  have h2 : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
  have h3 := Real.exp_pos (x ^ (ε / 3))
  unfold scW'' scB' scX'
  field_simp

/-! ## The growth package -/

/-- **The growth package** at `(ε, x)`: the explicit inequalities that the design and the pieces need for large `x`
(`eventually_designBig`). What each clause serves:
* `ε_pos`, `ε_lt`, `one_lt`: the range of the frontier's `ε`, and `x > 1`.
* `big`: every comparison of a constant `≤ 4096` with a power of `x` of exponent `≥ ε/100` (`DesignBig.le_rpow`):
  the ranks (`designRanks`), `|A| ≤ x³`, `log k ≤ 6 log x`, the windows of `|TT|`, `H ≥ t + 3`.
* `log_le`: `log x ≤ x^ε/1000` (the slope budget), and the terms `log k`, `log |A|` of `Λ_u`.
* `thin`: `log X = log x·(log N + log x) < x^{ε/3} − log 3` for `X = (Nx)^{log x}` and `log N ≤ 3x^{ε/5}log² x`
  (`Weights.thin_far`, with `a_t/w ≥ X′/3`), and `log N ≤ x^ε` in `Λ_u`.
* `gap`: `x^ε − x^{ε/3} ≥ x^{ε/3} + 30 log x`, so `b′/x ≥ X′x^{30}` and `w″ ≥ X′x^{27}`: the gaps and the cloud of
  the Harish-Chandra families, the windows of `a_t` and `b_t`, `η + 2 ≤ w″` (`thin_far`), and
  `log w″ ≥ x^ε − x^{ε/3} − 3 log x` (the lower bound of `Λ_u`).
* `poly`: `x^{410} ≤ X′`: `8k ≤ X′` (the bound `Σ natW ≤ 2Σa_t`), and with `gap` every polynomial size below `b′/x`,
  `w″` and `b` (`Weights.thick_small`, `[E:ℚ] ≤ Σa_t/x`).
* `cube`: `(log 4dM²)³ ≤ 10⁶x^{3ε} ≤ mx^ε/2 ≤ Λ_u` and `24mx^ε + log 2 ≤ x` (the auxiliary primes (T)).
* `tq`: `4tr + 1 < q` and `< d`, as `log q, log d > x^{ε/10}/2` and `4tr + 1 ≤ 2^{12}x^{406}`. -/
structure DesignBig (ε x : ℝ) : Prop where
  /-- `ε > 0`. -/
  ε_pos : 0 < ε
  /-- `ε < 1/52`. -/
  ε_lt : ε < 1 / 52
  /-- `x > 1`. -/
  one_lt : 1 < x
  /-- `x^{ε/100} ≥ 4096`. -/
  big : 4096 ≤ x ^ (ε / 100)
  /-- `log x ≤ x^ε/1000`. -/
  log_le : Real.log x ≤ x ^ ε / 1000
  /-- `3x^{ε/5} log³ x + log² x + 2 ≤ x^{ε/3}`. -/
  thin : 3 * x ^ (ε / 5) * Real.log x ^ 3 + Real.log x ^ 2 + 2 ≤ x ^ (ε / 3)
  /-- `2x^{ε/3} + 30 log x ≤ x^ε`. -/
  gap : 2 * x ^ (ε / 3) + 30 * Real.log x ≤ x ^ ε
  /-- `x^{410} ≤ exp(x^{ε/3})`. -/
  poly : x ^ 410 ≤ Real.exp (x ^ (ε / 3))
  /-- `10⁶x^{3ε} ≤ x^{1/2}`. -/
  cube : 10 ^ 6 * x ^ (3 * ε) ≤ x ^ (1 / 2 : ℝ)
  /-- `2^{12}x^{406} ≤ exp(x^{ε/10}/2)`. -/
  tq : 2 ^ 12 * x ^ 406 ≤ Real.exp (x ^ (ε / 10) / 2)

namespace DesignBig

variable {ε x : ℝ}

/-- `x^a = x^b·x^{a−b}`. -/
theorem rpow_split (hx : 0 < x) (a b : ℝ) : x ^ a = x ^ b * x ^ (a - b) := by
  rw [← Real.rpow_add hx]; ring_nf

/-- `c·log x ≤ x^{2δ}` once `c/δ ≤ x^δ`, for `c ≥ 0`. -/
theorem mul_log_le_of (hx : 0 < x) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (h : c / δ ≤ x ^ δ) :
    c * Real.log x ≤ x ^ (2 * δ) := by
  have hl := Real.log_le_rpow_div hx.le hδ
  have hp : 0 < x ^ δ := Real.rpow_pos_of_pos hx _
  rw [rpow_split hx (2 * δ) δ, show 2 * δ - δ = δ by ring]
  calc c * Real.log x ≤ c * (x ^ δ / δ) := by gcongr
    _ = c / δ * x ^ δ := by ring
    _ ≤ x ^ δ * x ^ δ := by gcongr

/-- The clause `log_le` once `2000/ε ≤ x^{ε/2}`. -/
theorem log_le_of (hx : 0 < x) (hε : 0 < ε) (h : 2000 / ε ≤ x ^ (ε / 2)) : Real.log x ≤ x ^ ε / 1000 := by
  have key := mul_log_le_of hx (half_pos hε) (show (0 : ℝ) ≤ 1000 by norm_num)
    (by rw [show (1000 : ℝ) / (ε / 2) = 2000 / ε by field_simp; ring]; exact h)
  rw [show 2 * (ε / 2) = ε by ring] at key
  linarith

/-- The clause `thin` once `3K³ + K² + 2 ≤ x^{ε/30}`, `K = 30/ε`: with `u = x^{ε/30}`, `log x ≤ Ku`, so the left
side is at most `(3K³ + K² + 2)u⁹ ≤ u^{10}`. -/
theorem thin_of (hx : 1 ≤ x) (hε : 0 < ε) (h : 3 * (30 / ε) ^ 3 + (30 / ε) ^ 2 + 2 ≤ x ^ (ε / 30)) :
    3 * x ^ (ε / 5) * Real.log x ^ 3 + Real.log x ^ 2 + 2 ≤ x ^ (ε / 3) := by
  have hx0 : 0 < x := by linarith
  set u := x ^ (ε / 30) with hu
  set K := 30 / ε with hK
  have hu1 : 1 ≤ u := Real.one_le_rpow hx (by positivity)
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl : Real.log x ≤ K * u := by
    calc Real.log x ≤ u / (ε / 30) := Real.log_le_rpow_div hx0.le (by positivity)
      _ = K * u := by rw [hK]; field_simp
  have h5 : x ^ (ε / 5) = u ^ 6 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num; ring_nf
  have h3 : x ^ (ε / 3) = u ^ 10 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num; ring_nf
  rw [h5, h3]
  have e3 : Real.log x ^ 3 ≤ (K * u) ^ 3 := pow_le_pow_left₀ hl0 hl 3
  have e2 : Real.log x ^ 2 ≤ (K * u) ^ 2 := pow_le_pow_left₀ hl0 hl 2
  have u29 : u ^ 2 ≤ u ^ 9 := pow_le_pow_right₀ hu1 (by norm_num)
  have u09 : 1 ≤ u ^ 9 := one_le_pow₀ hu1
  calc 3 * u ^ 6 * Real.log x ^ 3 + Real.log x ^ 2 + 2
      ≤ 3 * u ^ 6 * (K * u) ^ 3 + (K * u) ^ 2 + 2 := by gcongr
    _ = 3 * K ^ 3 * u ^ 9 + K ^ 2 * u ^ 2 + 2 := by ring
    _ ≤ 3 * K ^ 3 * u ^ 9 + K ^ 2 * u ^ 9 + 2 * u ^ 9 := by gcongr; linarith
    _ = (3 * K ^ 3 + K ^ 2 + 2) * u ^ 9 := by ring
    _ ≤ u * u ^ 9 := by gcongr
    _ = u ^ 10 := by ring

/-- The clause `gap` once `2 + 90/ε ≤ x^{2ε/3}`. -/
theorem gap_of (hx : 0 < x) (hε : 0 < ε) (h : 2 + 90 / ε ≤ x ^ (2 * ε / 3)) :
    2 * x ^ (ε / 3) + 30 * Real.log x ≤ x ^ ε := by
  have hl := Real.log_le_rpow_div hx.le (show 0 < ε / 3 by positivity)
  have hp : 0 < x ^ (ε / 3) := Real.rpow_pos_of_pos hx _
  rw [rpow_split hx ε (ε / 3), show ε - ε / 3 = 2 * ε / 3 by ring]
  calc 2 * x ^ (ε / 3) + 30 * Real.log x ≤ 2 * x ^ (ε / 3) + 30 * (x ^ (ε / 3) / (ε / 3)) := by gcongr
    _ = (2 + 90 / ε) * x ^ (ε / 3) := by field_simp; ring
    _ ≤ x ^ (2 * ε / 3) * x ^ (ε / 3) := by gcongr
    _ = x ^ (ε / 3) * x ^ (2 * ε / 3) := by ring

/-- The clause `poly` once `2460/ε ≤ x^{ε/6}`, through `410 log x ≤ x^{ε/3}`. -/
theorem poly_of (hx : 0 < x) (hε : 0 < ε) (h : 2460 / ε ≤ x ^ (ε / 6)) : x ^ 410 ≤ Real.exp (x ^ (ε / 3)) := by
  have key := mul_log_le_of hx (show 0 < ε / 6 by positivity) (show (0 : ℝ) ≤ 410 by norm_num)
    (by rw [show (410 : ℝ) / (ε / 6) = 2460 / ε by field_simp; ring]; exact h)
  rw [show 2 * (ε / 6) = ε / 3 by ring] at key
  calc x ^ 410 = Real.exp (410 * Real.log x) := by
        rw [← Real.exp_log (pow_pos hx 410), Real.log_pow]; norm_num
    _ ≤ Real.exp (x ^ (ε / 3)) := Real.exp_le_exp.2 key

/-- The clause `cube` once `10⁶ ≤ x^{1/2−3ε}`. -/
theorem cube_of (hx : 0 < x) (h : 10 ^ 6 ≤ x ^ (1 / 2 - 3 * ε)) : 10 ^ 6 * x ^ (3 * ε) ≤ x ^ (1 / 2 : ℝ) := by
  rw [rpow_split hx (1 / 2) (3 * ε), mul_comm (x ^ (3 * ε))]
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx.le _)

/-- The clause `tq` once `24 + 16240/ε ≤ x^{ε/20}`: with `v = x^{ε/20}`,
`12 log 2 + 406 log x ≤ 12 + 8120v/ε ≤ v²/2`. -/
theorem tq_of (hx : 1 ≤ x) (hε : 0 < ε) (h : 24 + 16240 / ε ≤ x ^ (ε / 20)) :
    2 ^ 12 * x ^ 406 ≤ Real.exp (x ^ (ε / 10) / 2) := by
  have hx0 : 0 < x := by linarith
  set v := x ^ (ε / 20) with hv
  have hv1 : 1 ≤ v := Real.one_le_rpow hx (by positivity)
  have hl : Real.log x ≤ v / (ε / 20) := Real.log_le_rpow_div hx0.le (by positivity)
  have h10 : x ^ (ε / 10) = v ^ 2 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num; ring_nf
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have key : 12 * Real.log 2 + 406 * Real.log x ≤ v ^ 2 / 2 := by
    have e1 : 406 * Real.log x ≤ 16240 / ε * v / 2 := by
      calc 406 * Real.log x ≤ 406 * (v / (ε / 20)) := by gcongr
        _ = 16240 / ε * v / 2 := by field_simp; ring
    have e2 : (24 + 16240 / ε) * v ≤ v * v := by gcongr
    nlinarith
  calc 2 ^ 12 * x ^ 406 = Real.exp (12 * Real.log 2 + 406 * Real.log x) := by
        rw [← Real.exp_log (show (0 : ℝ) < 2 ^ 12 * x ^ 406 by positivity), Real.log_mul (by positivity)
          (by positivity), Real.log_pow, Real.log_pow]; norm_num
    _ ≤ Real.exp (x ^ (ε / 10) / 2) := by rw [h10]; exact Real.exp_le_exp.2 key

end DesignBig

/-- **The growth package holds for large `x`**, at every `ε ∈ (0, 1/52)`. -/
theorem eventually_designBig (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 52) : ∀ᶠ x in atTop, DesignBig ε x := by
  have ev : ∀ {a : ℝ}, 0 < a → ∀ C : ℝ, ∀ᶠ x in atTop, C ≤ x ^ a :=
    fun ha C => (tendsto_rpow_atTop ha).eventually_ge_atTop C
  filter_upwards [eventually_gt_atTop 1, ev (show 0 < ε / 100 by positivity) 4096,
    ev (show 0 < ε / 2 by positivity) (2000 / ε),
    ev (show 0 < ε / 30 by positivity) (3 * (30 / ε) ^ 3 + (30 / ε) ^ 2 + 2),
    ev (show 0 < 2 * ε / 3 by positivity) (2 + 90 / ε), ev (show 0 < ε / 6 by positivity) (2460 / ε),
    ev (show 0 < 1 / 2 - 3 * ε by linarith) (10 ^ 6), ev (show 0 < ε / 20 by positivity) (24 + 16240 / ε)]
    with x h1 h2 h3 h4 h5 h6 h7 h8
  have hx0 : 0 < x := by linarith
  exact ⟨hε, hε', h1, h2, DesignBig.log_le_of hx0 hε h3, DesignBig.thin_of h1.le hε h4,
    DesignBig.gap_of hx0 hε h5, DesignBig.poly_of hx0 hε h6, DesignBig.cube_of hx0 h7,
    DesignBig.tq_of h1.le hε h8⟩

/-! ## Powers of `x^{1/100}` -/

namespace DesignBig

/-- `x^{a/100} = (x^{1/100})^a`. -/
theorem rpow_div_hundred {x : ℝ} (hx : 0 ≤ x) (a : ℕ) : x ^ ((a : ℝ) / 100) = (x ^ (1 / 100 : ℝ)) ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; ring_nf

/-- `x^n = (x^{1/100})^{100n}`. -/
theorem pow_eq_hundredth {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : x ^ n = (x ^ (1 / 100 : ℝ)) ^ (100 * n) := by
  rw [pow_mul, ← Real.rpow_natCast (x ^ (1 / 100 : ℝ)) 100, ← Real.rpow_mul hx]; norm_num

/-- `4096·y^a ≤ y^b` for `a < b` and `y ≥ 4096`. -/
theorem mul_pow_le_pow {y : ℝ} (hy : 4096 ≤ y) {a b : ℕ} (hab : a < b) : 4096 * y ^ a ≤ y ^ b := by
  have h1 : y ^ (a + 1) ≤ y ^ b := pow_le_pow_right₀ (by linarith) hab
  rw [pow_succ] at h1
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ y by linarith) a]

/-- `y ≤ 2⌈y/2⌉ ≤ 2y` for `y ≥ 2`. -/
theorem two_mul_ceil_half_mem {y : ℝ} (hy : 2 ≤ y) :
    y ≤ ((2 * ⌈y / 2⌉₊ : ℕ) : ℝ) ∧ ((2 * ⌈y / 2⌉₊ : ℕ) : ℝ) ≤ 2 * y := by
  push_cast
  have h1 := Nat.le_ceil (y / 2)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ y / 2 by linarith)
  constructor <;> linarith

section

variable {ε x : ℝ} (h : DesignBig ε x)
include h

/-- `x > 0`. -/
theorem pos : 0 < x := zero_lt_one.trans h.one_lt

/-- `4096 ≤ x^c` for `c ≥ ε/100`: the clause `big` at every exponent above `ε/100`. -/
theorem le_rpow {c : ℝ} (hc : ε / 100 ≤ c) : 4096 ≤ x ^ c :=
  h.big.trans (Real.rpow_le_rpow_of_exponent_le h.one_lt.le hc)

/-- `x^c ≤ y^a` for `c ≤ a/100`, with `y = x^{1/100}`. -/
theorem rpow_le_pow {c : ℝ} (a : ℕ) (hc : c ≤ a / 100) : x ^ c ≤ (x ^ (1 / 100 : ℝ)) ^ a := by
  rw [← rpow_div_hundred h.pos.le]; exact Real.rpow_le_rpow_of_exponent_le h.one_lt.le hc

/-- `y^a ≤ x^c` for `a/100 ≤ c`, with `y = x^{1/100}`. -/
theorem pow_le_rpow {c : ℝ} (a : ℕ) (hc : a / 100 ≤ c) : (x ^ (1 / 100 : ℝ)) ^ a ≤ x ^ c := by
  rw [← rpow_div_hundred h.pos.le]; exact Real.rpow_le_rpow_of_exponent_le h.one_lt.le hc

end

end DesignBig

/-! ## The ranks -/

/-- The rank `k = 2⌈x^{9/2+10ε}/2⌉`. -/
noncomputable def designK (x ε : ℝ) : ℕ := 2 * ⌈x ^ (9 / 2 + 10 * ε) / 2⌉₊

/-- The rank `m = 2⌈√(xδ₁)/2⌉`, with `√(xδ₁) = x^{1/2−ε/16}`. -/
noncomputable def designM (x ε : ℝ) : ℕ := 2 * ⌈x ^ (1 / 2 - ε / 16) / 2⌉₊

/-- The rank `t = 8fr + 4 + TO·nW − r`, with `r = k + m − 1`. -/
noncomputable def designT (S : Setting) (x ε : ℝ) : ℕ :=
  8 * S.f * (designK x ε + designM x ε - 1) + 4 +
    scTO x * scNW S.f (designK x ε) (designM x ε) (designK x ε + designM x ε - 1) (scL x ε) -
      (designK x ε + designM x ε - 1)

variable {ε x : ℝ}

/-- `x^{9/2+10ε} ≤ k ≤ 2x^{9/2+10ε}`. -/
theorem designK_mem (h : DesignBig ε x) :
    x ^ (9 / 2 + 10 * ε) ≤ designK x ε ∧ (designK x ε : ℝ) ≤ 2 * x ^ (9 / 2 + 10 * ε) :=
  DesignBig.two_mul_ceil_half_mem ((by norm_num : (2 : ℝ) ≤ 4096).trans (h.le_rpow (by linarith [h.ε_pos])))

/-- `x^{1/2−ε/16} ≤ m ≤ 2x^{1/2−ε/16}`. -/
theorem designM_mem (h : DesignBig ε x) :
    x ^ (1 / 2 - ε / 16) ≤ designM x ε ∧ (designM x ε : ℝ) ≤ 2 * x ^ (1 / 2 - ε / 16) :=
  DesignBig.two_mul_ceil_half_mem ((by norm_num : (2 : ℝ) ≤ 4096).trans (h.le_rpow (by linarith [h.ε_lt])))

/-- `k` and `m` in powers of `y = x^{1/100}`: `y^{450} ≤ k ≤ 2y^{470}` and `y^{49} ≤ m ≤ 2y^{50}`. -/
theorem designKM_hundredth (h : DesignBig ε x) :
    (x ^ (1 / 100 : ℝ)) ^ 450 ≤ designK x ε ∧ (designK x ε : ℝ) ≤ 2 * (x ^ (1 / 100 : ℝ)) ^ 470 ∧
      (x ^ (1 / 100 : ℝ)) ^ 49 ≤ designM x ε ∧ (designM x ε : ℝ) ≤ 2 * (x ^ (1 / 100 : ℝ)) ^ 50 := by
  have hε := h.ε_pos
  have hε' := h.ε_lt
  obtain ⟨hk1, hk2⟩ := designK_mem h
  obtain ⟨hm1, hm2⟩ := designM_mem h
  have e1 := h.pow_le_rpow 450 (c := 9 / 2 + 10 * ε) (by norm_num; linarith)
  have e2 := h.rpow_le_pow 470 (c := 9 / 2 + 10 * ε) (by norm_num; linarith)
  have e3 := h.pow_le_rpow 49 (c := 1 / 2 - ε / 16) (by norm_num; linarith)
  have e4 := h.rpow_le_pow 50 (c := 1 / 2 - ε / 16) (by norm_num; linarith)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `f ≥ 1`. -/
theorem Setting.one_le_f (S : Setting) : 1 ≤ S.f := by
  rw [S.f_eq]; have := Fintype.card_pos (α := S.A); omega

/-- `m ≥ 2`. -/
theorem two_le_designM (h : DesignBig ε x) : 2 ≤ designM x ε := by
  have : (2 : ℝ) ≤ designM x ε :=
    ((by norm_num : (2 : ℝ) ≤ 4096).trans (h.le_rpow (by linarith [h.ε_lt]))).trans (designM_mem h).1
  exact_mod_cast this

/-- `m + 3 ≤ k`. -/
theorem designM_add_three_le (h : DesignBig ε x) : designM x ε + 3 ≤ designK x ε := by
  have hy := h.le_rpow (c := 1 / 100) (by linarith [h.ε_lt])
  obtain ⟨hk, -, -, hm⟩ := designKM_hundredth h
  have e1 := DesignBig.mul_pow_le_pow hy (show 50 < 450 by norm_num)
  have e2 : 1 ≤ (x ^ (1 / 100 : ℝ)) ^ 50 := one_le_pow₀ (by linarith)
  have : (designM x ε : ℝ) + 3 ≤ designK x ε := by linarith
  exact_mod_cast this

/-- `m ≤ f`, for `|A| ≥ x^{2+8ε}`. -/
theorem designM_le_f (S : Setting) (h : DesignBig ε x) (hn₀ : x ^ (2 + 8 * ε) ≤ Fintype.card S.A) :
    designM x ε ≤ S.f := by
  have hy := h.le_rpow (c := 1 / 100) (by linarith [h.ε_lt])
  obtain ⟨-, -, -, hm⟩ := designKM_hundredth h
  have e1 := (h.pow_le_rpow 200 (by norm_num; linarith [h.ε_pos])).trans hn₀
  have e2 : (x ^ (1 / 100 : ℝ)) ^ 50 ≤ (x ^ (1 / 100 : ℝ)) ^ 200 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have : (designM x ε : ℝ) ≤ S.f := by rw [S.f_eq]; push_cast; linarith
  exact_mod_cast this

/-- `f ≤ k`, for `|A| ≤ 2x^{2+8ε+ε/100}`. -/
theorem f_le_designK (S : Setting) (h : DesignBig ε x)
    (hn₁ : (Fintype.card S.A : ℝ) ≤ 2 * x ^ (2 + 8 * ε + ε / 100)) : S.f ≤ designK x ε := by
  have hy := h.le_rpow (c := 1 / 100) (by linarith [h.ε_lt])
  obtain ⟨hk, -, -, -⟩ := designKM_hundredth h
  have e1 := h.rpow_le_pow 216 (c := 2 + 8 * ε + ε / 100) (by norm_num; linarith [h.ε_lt])
  have e2 := DesignBig.mul_pow_le_pow hy (show 216 < 450 by norm_num)
  have e3 : 0 ≤ (x ^ (1 / 100 : ℝ)) ^ 216 := by positivity
  have : (S.f : ℝ) ≤ designK x ε := by rw [S.f_eq]; push_cast; linarith
  exact_mod_cast this

/-- `r + t = 8fr + 4 + TO·nW`. -/
theorem designT_add (S : Setting) (x ε : ℝ) :
    designK x ε + designM x ε - 1 + designT S x ε = 8 * S.f * (designK x ε + designM x ε - 1) + 4 +
      scTO x * scNW S.f (designK x ε) (designM x ε) (designK x ε + designM x ε - 1) (scL x ε) := by
  unfold designT
  generalize scTO x * scNW S.f (designK x ε) (designM x ε) (designK x ε + designM x ε - 1) (scL x ε) = c
  generalize designK x ε + designM x ε - 1 = r
  have : 8 * r ≤ 8 * S.f * r := Nat.mul_le_mul_right _ (by have := S.one_le_f; omega)
  omega

/-- `t ≥ 7r + 4`. -/
theorem designT_ge (S : Setting) (x ε : ℝ) : 7 * (designK x ε + designM x ε - 1) + 4 ≤ designT S x ε := by
  have := designT_add S x ε
  have : 8 * (designK x ε + designM x ε - 1) ≤ 8 * S.f * (designK x ε + designM x ε - 1) :=
    Nat.mul_le_mul_right _ (by have := S.one_le_f; omega)
  omega

/-- `t` is odd, as `r` is odd and `8fr + 4 + TO·nW` is even. -/
theorem designT_odd (S : Setting) (x ε : ℝ) (hk : 2 ≤ designK x ε) : Odd (designT S x ε) := by
  have hr : Odd (designK x ε + designM x ε - 1) := by
    unfold designK designM at *
    exact ⟨⌈x ^ (9 / 2 + 10 * ε) / 2⌉₊ + ⌈x ^ (1 / 2 - ε / 16) / 2⌉₊ - 1, by omega⟩
  have he : Even (8 * S.f * (designK x ε + designM x ε - 1) + 4 +
      scTO x * scNW S.f (designK x ε) (designM x ε) (designK x ε + designM x ε - 1) (scL x ε)) := by
    have h8 : Even 8 := ⟨4, rfl⟩
    exact (((h8.mul_right _).mul_right _).add ⟨2, rfl⟩).add ((h8.mul_right _).mul_left _)
  have := designT_add S x ε
  exact Nat.Even.sub_odd (by omega) he hr

/-- **`t ≤ x^{401}`**, for `|A| ≤ 2x^{2+8ε+ε/100}`: in powers of `y = x^{1/100}`, `nW ≤ 3968y^{2267}`,
`TO ≤ 2y^{37700}`, so `t ≤ 8036y^{39967} ≤ y^{40100}`. -/
theorem designT_le (S : Setting) (h : DesignBig ε x)
    (hn₁ : (Fintype.card S.A : ℝ) ≤ 2 * x ^ (2 + 8 * ε + ε / 100)) : (designT S x ε : ℝ) ≤ x ^ 401 := by
  have hε := h.ε_pos
  have hε' := h.ε_lt
  set y := x ^ (1 / 100 : ℝ) with hy
  have hy4 : 4096 ≤ y := h.le_rpow (by linarith)
  have hy1 : 1 ≤ y := by linarith
  obtain ⟨hk1, hk, hm, hm2⟩ := designKM_hundredth h
  have hF : x ^ (2 + 8 * ε + ε / 100) ≤ y ^ 216 := h.rpow_le_pow 216 (by norm_num; linarith)
  have hL : scL x ε ^ 2 ≤ y ^ 4 := by
    rw [scL, ← Real.rpow_natCast, ← Real.rpow_mul h.pos.le]
    exact h.rpow_le_pow 4 (by norm_num; linarith)
  set k := designK x ε
  set m := designM x ε
  set r := k + m - 1
  have hf : (S.f : ℝ) ≤ 4 * y ^ 216 := by rw [S.f_eq]; push_cast; linarith
  have hk0 : 1 ≤ (k : ℝ) := le_trans (one_le_pow₀ hy1) hk1
  have hr : (r : ℝ) ≤ 3 * y ^ 470 := by
    have e1 : (r : ℝ) ≤ k + m := by exact_mod_cast Nat.sub_le _ _
    have e2 := DesignBig.mul_pow_le_pow hy4 (show 50 < 470 by norm_num)
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ y by linarith) 50]
  have hTO : (scTO x : ℝ) ≤ 2 * y ^ 37700 := by
    have h1 := Nat.ceil_lt_add_one (pow_nonneg h.pos.le 377)
    have h2 : 1 ≤ x ^ 377 := one_le_pow₀ h.one_lt.le
    have h3 : x ^ 377 = y ^ 37700 := DesignBig.pow_eq_hundredth h.pos.le 377
    rw [scTO]
    linarith
  -- `nW ≤ 3968·y^{2267}`
  have hfrac : (S.f : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * scL x ε ^ 2 / m ≤ 128 * y ^ 1797 := by
    have h1 : (S.f : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * scL x ε ^ 2 ≤
        (4 * y ^ 216) ^ 2 * (2 * y ^ 470) ^ 3 * y ^ 4 := by
      gcongr; linarith
    calc (S.f : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * scL x ε ^ 2 / m
        ≤ (4 * y ^ 216) ^ 2 * (2 * y ^ 470) ^ 3 * y ^ 4 / y ^ 49 :=
          div_le_div₀ (by positivity) h1 (by positivity) hm
      _ = 128 * y ^ 1797 := by rw [div_eq_iff (by positivity)]; ring
  have hQ : 10 * (r : ℝ) * (S.f + S.f ^ 2 * ((k : ℝ) - 1) ^ 3 * scL x ε ^ 2 / m) ≤ 3960 * y ^ 2267 := by
    have h1 : y ^ 216 ≤ y ^ 1797 := pow_le_pow_right₀ hy1 (by norm_num)
    calc 10 * (r : ℝ) * (S.f + S.f ^ 2 * ((k : ℝ) - 1) ^ 3 * scL x ε ^ 2 / m)
        ≤ 10 * (3 * y ^ 470) * (4 * y ^ 1797 + 128 * y ^ 1797) := by gcongr; linarith
      _ = 3960 * y ^ 2267 := by ring
  have hnW : (scNW S.f k m r (scL x ε) : ℝ) ≤ 3968 * y ^ 2267 := by
    have h0 : 0 ≤ 10 * (r : ℝ) * (S.f + S.f ^ 2 * ((k : ℝ) - 1) ^ 3 * scL x ε ^ 2 / m) := by
      have : 0 ≤ (k : ℝ) - 1 := by linarith
      positivity
    have h1 := Nat.ceil_lt_add_one (div_nonneg h0 (show (0 : ℝ) ≤ 8 by norm_num))
    have h2 : 1 ≤ y ^ 2267 := one_le_pow₀ hy1
    rw [scNW]; push_cast
    linarith
  -- the total
  have hE : (designT S x ε : ℝ) ≤ 8 * S.f * r + 4 + scTO x * scNW S.f k m r (scL x ε) := by
    have : designT S x ε ≤ 8 * S.f * r + 4 + scTO x * scNW S.f k m r (scL x ε) := Nat.sub_le _ _
    exact_mod_cast this
  have hTOn : (scTO x : ℝ) * scNW S.f k m r (scL x ε) ≤ 7936 * y ^ 39967 := by
    calc (scTO x : ℝ) * scNW S.f k m r (scL x ε) ≤ (2 * y ^ 37700) * (3968 * y ^ 2267) := by gcongr
      _ = 7936 * y ^ 39967 := by ring
  have hfr : 8 * (S.f : ℝ) * r + 4 ≤ 100 * y ^ 39967 := by
    have h1 : y ^ 686 ≤ y ^ 39967 := pow_le_pow_right₀ hy1 (by norm_num)
    have h2 : 1 ≤ y ^ 686 := one_le_pow₀ hy1
    calc 8 * (S.f : ℝ) * r + 4 ≤ 8 * (4 * y ^ 216) * (3 * y ^ 470) + 4 := by gcongr
      _ = 96 * y ^ 686 + 4 := by ring
      _ ≤ 100 * y ^ 39967 := by linarith
  have h133 : 8036 ≤ y ^ 133 := by
    have := DesignBig.mul_pow_le_pow hy4 (show 1 < 133 by norm_num)
    rw [pow_one] at this
    nlinarith
  rw [DesignBig.pow_eq_hundredth h.pos.le]
  calc (designT S x ε : ℝ) ≤ 8036 * y ^ 39967 := by linarith
    _ ≤ y ^ 133 * y ^ 39967 := by gcongr
    _ = y ^ (100 * 401) := by ring

/-- **The ranks of the design** at `x`, for `x^{2+8ε} ≤ |A| ≤ 2x^{2+8ε+ε/100}`: `k = 2⌈x^{9/2+10ε}/2⌉`,
`m = 2⌈x^{1/2−ε/16}/2⌉` and `t = 8fr + 4 + TO·nW − r`, with `r = k + m − 1`. -/
noncomputable def designRanks (S : Setting) (x ε : ℝ) (hbig : DesignBig ε x)
    (hn₀ : x ^ (2 + 8 * ε) ≤ Fintype.card S.A)
    (hn₁ : (Fintype.card S.A : ℝ) ≤ 2 * x ^ (2 + 8 * ε + ε / 100)) : S.Ranks where
  k := designK x ε
  m := designM x ε
  t := designT S x ε
  k_even := even_two_mul _
  m_even := even_two_mul _
  t_odd := designT_odd S x ε (by have := designM_add_three_le hbig; omega)
  two_le_m := two_le_designM hbig
  m_add_three_le := designM_add_three_le hbig
  k_add_m_add_four_le := by have := designT_ge S x ε; have := designM_add_three_le hbig; omega
  three_m_lt := by have := designT_ge S x ε; have := designM_add_three_le hbig; omega
  m_le_f := designM_le_f S hbig hn₀
  f_le_k := f_le_designK S hbig hn₁
  m_sq_le := by
    have : designM x ε ≤ designT S x ε + 1 := by
      have := designT_ge S x ε; have := designM_add_three_le hbig; omega
    calc designM x ε ^ 2 = designM x ε * designM x ε := sq _
      _ ≤ designM x ε * (designT S x ε + 1) := Nat.mul_le_mul_left _ this
      _ ≤ _ := Nat.le_add_left _ _

section designRanks

variable (S : Setting) (hbig : DesignBig ε x) (hn₀ : x ^ (2 + 8 * ε) ≤ Fintype.card S.A)
  (hn₁ : (Fintype.card S.A : ℝ) ≤ 2 * x ^ (2 + 8 * ε + ε / 100))

/-- **`r ≤ 3x^{9/2+10ε}`**, as `m ≤ 2y^{50} ≤ x^{9/2+10ε}` for `y = x^{1/100}`. -/
theorem designRanks_r_le : ((designRanks S x ε hbig hn₀ hn₁).r : ℝ) ≤ 3 * x ^ (9 / 2 + 10 * ε) := by
  have hy := hbig.le_rpow (c := 1 / 100) (by linarith [hbig.ε_lt])
  obtain ⟨hk1, hk2⟩ := designK_mem hbig
  obtain ⟨-, -, -, hm⟩ := designKM_hundredth hbig
  have e1 := hbig.pow_le_rpow 450 (c := 9 / 2 + 10 * ε) (by norm_num; linarith [hbig.ε_pos])
  have e2 := DesignBig.mul_pow_le_pow hy (show 50 < 450 by norm_num)
  have e3 : 0 ≤ (x ^ (1 / 100 : ℝ)) ^ 50 := by positivity
  have hr : ((designRanks S x ε hbig hn₀ hn₁).r : ℝ) ≤ designK x ε + designM x ε := by
    exact_mod_cast Nat.sub_le (designK x ε + designM x ε) 1
  linarith

end designRanks

/-! ## The Behrend density -/

/-- The Behrend comparison at one `x`, in `ℓ = log x`: for `ℓ ≥ 60/ε + 34`, `ℓ ≥ 32408` and `log ℓ ≤ cℓ` with
`c = ε²/(96(C² + 1))`, `8L_w·exp(C√(3ℓ·log(2L_w + 1))) ≤ x^{ε/2}`. -/
theorem behrend_of {C ε x : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hε' : ε ≤ 1) (hx : 0 < x)
    (h1 : 60 / ε + 34 ≤ Real.log x) (h2 : 32408 ≤ Real.log x)
    (h3 : Real.log (Real.log x) ≤ ε ^ 2 / (96 * (C ^ 2 + 1)) * Real.log x) :
    8 * scLw x ε * Real.exp (C * √(3 * Real.log x * Real.log (2 * scLw x ε + 1))) ≤ x ^ (ε / 2) := by
  set ℓ := Real.log x with hℓ
  set c := ε ^ 2 / (96 * (C ^ 2 + 1)) with hc
  have hC1 : 0 < C ^ 2 + 1 := by positivity
  -- `22 ≤ L_w ≤ 4051ℓ`
  have hL : (scLw x ε : ℝ) ≤ 4051 * ℓ := by
    have e1 := Nat.ceil_lt_add_one (show 0 ≤ 405 * ℓ by positivity)
    have e2 := Nat.ceil_lt_add_one (show 0 ≤ 30 / ε by positivity)
    have e3 : 60 / ε = 2 * (30 / ε) := by ring
    rw [scLw, ← hℓ]; push_cast
    linarith
  have hL0 : (22 : ℝ) ≤ scLw x ε := by
    have : 22 ≤ scLw x ε := Nat.le_add_left _ _
    exact_mod_cast this
  -- `log(2L_w + 1) ≤ 2 log ℓ` and `log(8L_w) ≤ 2 log ℓ`
  have hsq : Real.log (ℓ ^ 2) = 2 * Real.log ℓ := by rw [Real.log_pow]; norm_num
  have hl1 : Real.log (2 * scLw x ε + 1) ≤ 2 * Real.log ℓ := by
    rw [← hsq]; exact Real.log_le_log (by positivity) (by nlinarith)
  have hl2 : Real.log (8 * scLw x ε) ≤ 2 * Real.log ℓ := by
    rw [← hsq]; exact Real.log_le_log (by positivity) (by nlinarith)
  have hc16 : c ≤ ε / 16 := by
    rw [hc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg C]
  -- the square root: `C√(3ℓ·log(2L_w + 1)) ≤ εℓ/4`
  have hA : C ^ 2 * (3 * ℓ * Real.log (2 * scLw x ε + 1)) ≤ (ε / 4 * ℓ) ^ 2 := by
    have e1 : 3 * ℓ * Real.log (2 * scLw x ε + 1) ≤ 6 * c * ℓ ^ 2 := by nlinarith
    have e2 : C ^ 2 * (6 * c) ≤ ε ^ 2 / 16 := by
      rw [hc, show C ^ 2 * (6 * (ε ^ 2 / (96 * (C ^ 2 + 1)))) = ε ^ 2 / 16 * (C ^ 2 / (C ^ 2 + 1)) by
        field_simp; ring]
      have : C ^ 2 / (C ^ 2 + 1) ≤ 1 := (div_le_one hC1).2 (by linarith)
      nlinarith [sq_nonneg ε]
    calc C ^ 2 * (3 * ℓ * Real.log (2 * scLw x ε + 1)) ≤ C ^ 2 * (6 * c * ℓ ^ 2) := by gcongr
      _ = C ^ 2 * (6 * c) * ℓ ^ 2 := by ring
      _ ≤ ε ^ 2 / 16 * ℓ ^ 2 := by gcongr
      _ = (ε / 4 * ℓ) ^ 2 := by ring
  have hroot : C * √(3 * ℓ * Real.log (2 * scLw x ε + 1)) ≤ ε / 4 * ℓ := by
    calc C * √(3 * ℓ * Real.log (2 * scLw x ε + 1))
        = √(C ^ 2 * (3 * ℓ * Real.log (2 * scLw x ε + 1))) := by
          rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
      _ ≤ √((ε / 4 * ℓ) ^ 2) := Real.sqrt_le_sqrt hA
      _ = ε / 4 * ℓ := Real.sqrt_sq (by positivity)
  rw [Real.rpow_def_of_pos hx, ← Real.exp_log (show 0 < 8 * (scLw x ε : ℝ) by positivity), ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [← hℓ]
  nlinarith

/-- **The Behrend density beats `x^{−ε/2}`** for large `x`: `8L_w·exp(C√(3 log x·log(2L_w + 1))) ≤ x^{ε/2}`, at
every `C ≥ 0` and `ε ∈ (0, 1]`. With `C = 6` (`RelFree.exists_six`), `N = ⌊|A₀|/(4L_w)⌋` and `log N ≤ 3 log x`, it
turns `|T| ≥ N·exp(−C√(log N·log(2L_w + 1)))` into `|T| ≥ x^{−ε}|A|`. -/
theorem eventually_behrend {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hε' : ε ≤ 1) : ∀ᶠ x in atTop,
    8 * scLw x ε * Real.exp (C * √(3 * Real.log x * Real.log (2 * scLw x ε + 1))) ≤ x ^ (ε / 2) := by
  have hc : 0 < ε ^ 2 / (96 * (C ^ 2 + 1)) := by positivity
  have h2 := (eventually_ge_atTop (max (60 / ε + 34) 32408)).and (Real.isLittleO_log_id_atTop.bound hc)
  filter_upwards [Real.tendsto_log_atTop.eventually h2, eventually_gt_atTop 0] with x ⟨hl1, hl2⟩ hx
  have hm1 := le_of_max_le_left hl1
  have hm2 := le_of_max_le_right hl1
  have hpos : 0 < Real.log x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hpos,
    abs_of_nonneg (Real.log_nonneg (by linarith))] at hl2
  exact behrend_of hC hε hε' hx hm1 hm2 hl2

end ZetaBalance

#print axioms ZetaBalance.eventually_designBig
#print axioms ZetaBalance.designRanks
#print axioms ZetaBalance.designRanks_r_le
#print axioms ZetaBalance.eventually_behrend
