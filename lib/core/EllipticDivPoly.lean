import EllipticAdd

/-!
# The division values of `σ` and Mathlib's division polynomials

For the curve `curve Λ : Y² = X³ − (g₂/4)X − g₃/4` of a period pair (`X = ℘`, `Y = −℘′/2`), the torsion values of `℘`
are roots of Mathlib's division polynomials: `ΨSq_N(℘(q)) = 0` for `q ∉ Λ`, `Nq ∈ Λ` (`eval_ΨSq_eq_zero`). With the
leading coefficient `N²` of `ΨSq_N` in degree `N² − 1` and the integrality of its coefficients this makes `℘(q)`
integral away from `N` (`TorsionInt`).

**Duplication.** As `w → z`, the chord slope `(℘′(z) − ℘′(w))/(℘(z) − ℘(w))` tends to `m = ℘″(z)/℘′(z)`
(`tendsto_slope_ratio`), so the addition theorems of `℘` and `ζ` (`EllipticAdd.weierstrassP_add`, `zetaW_add`) give
`℘(2z) = m²/4 − 2℘(z)` (`weierstrassP_two_mul`) and `ζ(2z) = 2ζ(z) + m/2` (`zetaW_two_mul`) for `z, 2z ∉ Λ`.
Differentiating the first, with `m′ = 12℘ − m²`, gives `℘′(2z) = m(12℘ − m²)/4 − ℘′` (`derivWeierstrassP_two_mul`).

**The division values** `F(z, n) = σ(nz)/σ(z)^{n²}` (`sigRat`). The `σ` addition formula at `(az, bz)` gives
`F(a + b)F(a − b) = F(a)²F(b)²(℘(bz) − ℘(az))` (`sigRat_add_mul_sub`), hence the three-term relation
`F(a + b)F(a − b) = F(a + 1)F(a − 1)F(b)² − F(b + 1)F(b − 1)F(a)²` (`sigRat_rel`), which is the recursion of Mathlib's
normalised elliptic divisibility sequence. With `F(2) = −℘′`, `F(3) = Ψ₃(℘)` and `F(4) = −℘′(2z)℘′⁴ = −℘′·preΨ₄(℘)`
(the duplication formulas and `℘′² = 4℘³ − g₂℘ − g₃`), `F(z, n) = normEDS(−℘′, Ψ₃(℘), preΨ₄(℘))(n)` at generic `z`,
no multiple of which is a period (`sigRat_eq_normEDS`), so `F(z, n)² = ΨSq_n(℘(z))` there (`sigRat_sq_of_generic`).

**Density.** The non-generic points `⋃_k k⁻¹Λ` are countable, so the generic points are dense in `ℂ ∖ Λ`
(`subset_closure_generic`), and `F(z, n)² = ΨSq_n(℘(z))` on all of `ℂ ∖ Λ` by continuity (`sigRat_sq`). At a torsion
point, `σ(Nq) = 0`.

**Main declarations:** `weierstrassP_two_mul`, `zetaW_two_mul`, `derivWeierstrassP_two_mul`, `sigRat_eq_normEDS`,
`sigRat_sq`, `eval_ΨSq_eq_zero`; the definitions `curve`, `sigRat`, `Generic`.
-/

namespace EllipticDivPoly

noncomputable section

open Polynomial PeriodPair ThetaNorm CMThetaOne EllipticAdd Filter Topology

variable (Λ : PeriodPair)

/-! ## The curve of `Λ` -/

/-- **The Weierstrass curve of `Λ`**: `Y² = X³ − (g₂/4)X − g₃/4` (`X = ℘`, `Y = −℘′/2`). -/
def curve : WeierstrassCurve ℂ := ⟨0, 0, 0, -Λ.g₂ / 4, -Λ.g₃ / 4⟩

/-- **`Ψ₂Sq` of the curve**: `Ψ₂Sq(x) = 4x³ − g₂x − g₃`, so `Ψ₂Sq(℘) = ℘′²`. -/
theorem eval_Ψ₂Sq (x : ℂ) : (curve Λ).Ψ₂Sq.eval x = 4 * x ^ 3 - Λ.g₂ * x - Λ.g₃ := by
  simp [WeierstrassCurve.Ψ₂Sq, curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ring

/-- **`Ψ₃` of the curve.** -/
theorem eval_Ψ₃ (x : ℂ) :
    (curve Λ).Ψ₃.eval x = 3 * x ^ 4 - 3 / 2 * Λ.g₂ * x ^ 2 - 3 * Λ.g₃ * x - Λ.g₂ ^ 2 / 16 := by
  simp [WeierstrassCurve.Ψ₃, curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- **`preΨ₄` of the curve.** -/
theorem eval_preΨ₄ (x : ℂ) :
    (curve Λ).preΨ₄.eval x = 2 * x ^ 6 - 5 / 2 * Λ.g₂ * x ^ 4 - 10 * Λ.g₃ * x ^ 3 - 5 / 8 * Λ.g₂ ^ 2 * x ^ 2 -
      Λ.g₂ * Λ.g₃ / 2 * x + Λ.g₂ ^ 3 / 32 - Λ.g₃ ^ 2 := by
  simp [WeierstrassCurve.preΨ₄, curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-! ## Duplication -/

/-- **`℘′(z) ≠ 0`** when `2z` is not a period (`sigmaW_two_mul`). -/
theorem derivWeierstrassP_ne_zero {z : ℂ} (hz : z ∉ Λ.lattice) (h2 : 2 * z ∉ Λ.lattice) : ℘'[Λ] z ≠ 0 := by
  intro h0
  have := sigmaW_two_mul Λ hz
  rw [h0, neg_zero, zero_mul] at this
  exact h2 ((sigmaW_eq_zero_iff Λ _).1 this)

/-- **The chord slope tends to the tangent slope**: `(℘′(z) − ℘′(w))/(℘(z) − ℘(w)) → ℘″(z)/℘′(z)` as `w → z`. -/
theorem tendsto_slope_ratio {z : ℂ} (hz : z ∉ Λ.lattice) (hz' : ℘'[Λ] z ≠ 0) :
    Tendsto (fun w => (℘'[Λ] z - ℘'[Λ] w) / (℘[Λ] z - ℘[Λ] w)) (𝓝[≠] z)
      (𝓝 ((6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) / ℘'[Λ] z)) := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_derivWeierstrassP Λ hz)
  have h2 := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_weierstrassP Λ hz)
  refine (h1.div h2 hz').congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : w - z ≠ 0 := sub_ne_zero.mpr hw
  change slope ℘'[Λ] z w / slope ℘[Λ] z w = _
  rw [slope_def_field, slope_def_field, div_div_div_cancel_right₀ hw', ← neg_div_neg_eq, neg_sub, neg_sub]

/-- **Near `z`, the points `w ≠ z` have `w`, `z ± w` off the lattice** (when `z`, `2z` are). -/
theorem eventually_add_sub {z : ℂ} (hz : z ∉ Λ.lattice) (h2 : 2 * z ∉ Λ.lattice) :
    ∀ᶠ w in 𝓝[≠] z, w ∉ Λ.lattice ∧ z + w ∉ Λ.lattice ∧ z - w ∉ Λ.lattice := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  have h1 : ∀ᶠ w in 𝓝 z, w ∉ Λ.lattice := hU.mem_nhds hz
  have h2' : ∀ᶠ w in 𝓝 z, z + w ∉ Λ.lattice :=
    ((continuous_const.add continuous_id : Continuous fun w : ℂ => z + w).tendsto' z (z + z) rfl).eventually
      (hU.mem_nhds (by rwa [← two_mul]))
  have h3 : ∀ᶠ w in 𝓝 z, z - w ∈ ((Λ.lattice : Set ℂ) \ {0})ᶜ :=
    ((continuous_const.sub continuous_id : Continuous fun w : ℂ => z - w).tendsto' z 0 (sub_self z)).eventually
      (Λ.compl_lattice_sdiff_singleton_mem_nhds 0)
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2', nhdsWithin_le_nhds h3, self_mem_nhdsWithin]
    with w hw1 hw2 hw3 hw4
  exact ⟨hw1, hw2, fun h => hw3 ⟨h, fun h0 => hw4 (sub_eq_zero.mp h0).symm⟩⟩

/-- **Duplication of `℘`**: `℘(2z) = m²/4 − 2℘(z)`, `m = ℘″(z)/℘′(z)` (the limit `w → z` of `weierstrassP_add`). -/
theorem weierstrassP_two_mul {z : ℂ} (hz : z ∉ Λ.lattice) (h2 : 2 * z ∉ Λ.lattice) :
    ℘[Λ] (2 * z) = ((6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) / ℘'[Λ] z) ^ 2 / 4 - 2 * ℘[Λ] z := by
  have hp := derivWeierstrassP_ne_zero Λ hz h2
  have hzz : z + z ∉ Λ.lattice := by rwa [← two_mul]
  have hL : Tendsto (fun w => ℘[Λ] (z + w)) (𝓝[≠] z) (𝓝 (℘[Λ] (2 * z))) := by
    rw [two_mul]
    exact ((hasDerivAt_weierstrassP Λ hzz).comp_const_add z z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hR := ((((tendsto_slope_ratio Λ hz hp).pow 2).div_const 4).sub_const (℘[Λ] z)).sub
    ((hasDerivAt_weierstrassP Λ hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  refine (tendsto_nhds_unique hL (hR.congr' ?_)).trans (by ring)
  filter_upwards [eventually_add_sub Λ hz h2] with w ⟨hw, hp', hm⟩
  exact (weierstrassP_add Λ hz hw hp' hm).symm

/-- **Duplication of `ζ`**: `ζ(2z) = 2ζ(z) + ℘″(z)/(2℘′(z))` (the limit `w → z` of `zetaW_add`). -/
theorem zetaW_two_mul {z : ℂ} (hz : z ∉ Λ.lattice) (h2 : 2 * z ∉ Λ.lattice) :
    zetaW Λ (2 * z) = 2 * zetaW Λ z + (6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) / (2 * ℘'[Λ] z) := by
  have hp := derivWeierstrassP_ne_zero Λ hz h2
  have hzz : z + z ∉ Λ.lattice := by rwa [← two_mul]
  have hL : Tendsto (fun w => zetaW Λ (z + w)) (𝓝[≠] z) (𝓝 (zetaW Λ (2 * z))) := by
    rw [two_mul]
    exact ((hasDerivAt_zetaW Λ hzz).comp_const_add z z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hR := (((hasDerivAt_zetaW Λ hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).const_add
    (zetaW Λ z)).add ((tendsto_slope_ratio Λ hz hp).div_const 2)
  refine (tendsto_nhds_unique hL (hR.congr' ?_)).trans (by ring)
  filter_upwards [eventually_add_sub Λ hz h2] with w ⟨hw, hp', hm⟩
  rw [zetaW_add Λ hz hw hp' hm, mul_comm (2 : ℂ), ← div_div]

/-- **Duplication of `℘′`**: `℘′(2z) = m(12℘(z) − m²)/4 − ℘′(z)`, `m = ℘″(z)/℘′(z)` (differentiate
`weierstrassP_two_mul` on the open set `{z, 2z ∉ Λ}`; `m′ = 12℘ − m²`). -/
theorem derivWeierstrassP_two_mul {z : ℂ} (hz : z ∉ Λ.lattice) (h2 : 2 * z ∉ Λ.lattice) :
    ℘'[Λ] (2 * z) = (6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) / ℘'[Λ] z *
      (12 * ℘[Λ] z - ((6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) / ℘'[Λ] z) ^ 2) / 4 - ℘'[Λ] z := by
  have hU : IsOpen (Λ.latticeᶜ : Set ℂ) := Λ.isClosed_lattice.isOpen_compl
  have hV : {y : ℂ | y ∉ Λ.lattice ∧ 2 * y ∉ Λ.lattice} ∈ 𝓝 z :=
    (hU.inter (hU.preimage (continuous_const.mul continuous_id))).mem_nhds ⟨hz, h2⟩
  have hp := derivWeierstrassP_ne_zero Λ hz h2
  have hL : HasDerivAt (fun y => ℘[Λ] (2 * y)) (℘'[Λ] (2 * z) * 2) z := by
    have h := (hasDerivAt_weierstrassP Λ h2).comp z ((hasDerivAt_id' z).const_mul (2 : ℂ))
    rw [mul_one] at h
    exact h
  have hm := ((((hasDerivAt_weierstrassP Λ hz).pow 2).const_mul 6).sub_const (Λ.g₂ / 2)).div
    (hasDerivAt_derivWeierstrassP Λ hz) hp
  have hR := ((hm.pow 2).div_const 4).sub ((hasDerivAt_weierstrassP Λ hz).const_mul 2)
  have heq : (fun y => ℘[Λ] (2 * y)) =ᶠ[𝓝 z]
      fun y => ((6 * ℘[Λ] y ^ 2 - Λ.g₂ / 2) / ℘'[Λ] y) ^ 2 / 4 - 2 * ℘[Λ] y := by
    filter_upwards [hV] with y hy using weierstrassP_two_mul Λ hy.1 hy.2
  have hd := hL.unique (hR.congr_of_eventuallyEq heq)
  simp only [Pi.div_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hd
  rw [show ℘'[Λ] (2 * z) = ℘'[Λ] (2 * z) * 2 / 2 by ring, hd]
  field_simp
  ring

/-! ## The division values of `σ` -/

/-- **The analytic division values** `F(z, n) = σ(nz)/σ(z)^{n²}`. -/
def sigRat (z : ℂ) (n : ℕ) : ℂ := sigmaW Λ (n * z) / sigmaW Λ z ^ (n ^ 2)

/-- **`F(z, 0) = 0`.** -/
theorem sigRat_zero (z : ℂ) : sigRat Λ z 0 = 0 := by simp [sigRat, sigmaW_zero]

/-- **`F(z, 1) = 1`.** -/
theorem sigRat_one {z : ℂ} (hz : z ∉ Λ.lattice) : sigRat Λ z 1 = 1 := by
  simp [sigRat, sigmaW_ne_zero Λ hz]

/-- **`F(z, 2) = −℘′(z)`** (`sigmaW_two_mul`). -/
theorem sigRat_two {z : ℂ} (hz : z ∉ Λ.lattice) : sigRat Λ z 2 = -℘'[Λ] z := by
  have hs := sigmaW_ne_zero Λ hz
  rw [sigRat, Nat.cast_ofNat, sigmaW_two_mul Λ hz, show (2 : ℕ) ^ 2 = 4 by norm_num]
  field_simp

/-- **`F(a + b)F(a − b) = F(a)²F(b)²(℘(bz) − ℘(az))`** (`sigmaW_add_mul_sub` at `az`, `bz`). -/
theorem sigRat_add_mul_sub {z : ℂ} (hz : z ∉ Λ.lattice) {a b : ℕ} (hba : b ≤ a) (ha : (a : ℂ) * z ∉ Λ.lattice)
    (hb : (b : ℂ) * z ∉ Λ.lattice) :
    sigRat Λ z (a + b) * sigRat Λ z (a - b) =
      sigRat Λ z a ^ 2 * sigRat Λ z b ^ 2 * (℘[Λ] (b * z) - ℘[Λ] (a * z)) := by
  have h := sigmaW_add_mul_sub Λ ha hb
  have hs := sigmaW_ne_zero Λ hz
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hba
  simp only [sigRat]
  rw [show (((b + c + b : ℕ) : ℂ) * z) = (b + c : ℕ) * z + b * z by push_cast; ring,
    show (((b + c - b : ℕ) : ℂ) * z) = (b + c : ℕ) * z - b * z by rw [Nat.add_sub_cancel_left]; push_cast; ring,
    div_mul_div_comm, h, ← pow_add, show (b + c + b) ^ 2 + (b + c - b) ^ 2 = 2 * (b + c) ^ 2 + 2 * b ^ 2 by
      rw [Nat.add_sub_cancel_left]; ring]
  field_simp
  ring

/-- **Generic points**: no nonzero multiple is a period. -/
def Generic (z : ℂ) : Prop := ∀ k : ℕ, 0 < k → (k : ℂ) * z ∉ Λ.lattice

/-- **A generic point is not a period.** -/
theorem Generic.not_mem {z : ℂ} (hz : Generic Λ z) : z ∉ Λ.lattice := by simpa using hz 1 one_pos

/-- **The three-term relation** `F(a + b)F(a − b) = F(a + 1)F(a − 1)F(b)² − F(b + 1)F(b − 1)F(a)²` at generic
points, `1 ≤ b ≤ a` (`sigRat_add_mul_sub` three times). -/
theorem sigRat_rel {z : ℂ} (hz : Generic Λ z) {a b : ℕ} (hb : 1 ≤ b) (hba : b ≤ a) :
    sigRat Λ z (a + b) * sigRat Λ z (a - b) = sigRat Λ z (a + 1) * sigRat Λ z (a - 1) * sigRat Λ z b ^ 2 -
      sigRat Λ z (b + 1) * sigRat Λ z (b - 1) * sigRat Λ z a ^ 2 := by
  have hz1 := hz.not_mem
  have h1 : ((1 : ℕ) : ℂ) * z ∉ Λ.lattice := by simpa using hz1
  have ha := hz a (by omega)
  have hb' := hz b (by omega)
  rw [sigRat_add_mul_sub Λ hz1 hba ha hb', sigRat_add_mul_sub Λ hz1 (hb.trans hba) ha h1,
    sigRat_add_mul_sub Λ hz1 hb hb' h1, sigRat_one Λ hz1, Nat.cast_one, one_mul]
  ring

/-- **`F(z, 3) = Ψ₃(℘(z))`** (`sigRat_add_mul_sub` at `(2, 1)`, `weierstrassP_two_mul`). -/
theorem sigRat_three {z : ℂ} (hz : z ∉ Λ.lattice) (h2 : 2 * z ∉ Λ.lattice) :
    sigRat Λ z 3 = (curve Λ).Ψ₃.eval (℘[Λ] z) := by
  have h := sigRat_add_mul_sub Λ hz (a := 2) (b := 1) (by norm_num) (by simpa using h2) (by simpa using hz)
  have hp := derivWeierstrassP_ne_zero Λ hz h2
  have hrel := Λ.derivWeierstrassP_sq z hz
  rw [show 2 + 1 = 3 by rfl, show 2 - 1 = 1 by rfl, sigRat_one Λ hz, sigRat_two Λ hz] at h
  push_cast at h
  rw [one_mul, weierstrassP_two_mul Λ hz h2, mul_one] at h
  have e : (-℘'[Λ] z) ^ 2 * 1 ^ 2 * (℘[Λ] z - (((6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) / ℘'[Λ] z) ^ 2 / 4 - 2 * ℘[Λ] z)) =
      3 * ℘[Λ] z * ℘'[Λ] z ^ 2 - (6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) ^ 2 / 4 := by
    field_simp
    ring
  rw [h, e, eval_Ψ₃]
  linear_combination 3 * ℘[Λ] z * hrel

/-- **`F(z, 4) = −℘′(z)·preΨ₄(℘(z))`** (`sigmaW_two_mul` at `2z`, `derivWeierstrassP_two_mul`). -/
theorem sigRat_four {z : ℂ} (hz : z ∉ Λ.lattice) (h2 : 2 * z ∉ Λ.lattice) :
    sigRat Λ z 4 = (curve Λ).preΨ₄.eval (℘[Λ] z) * -℘'[Λ] z := by
  have hs := sigmaW_ne_zero Λ hz
  have hp := derivWeierstrassP_ne_zero Λ hz h2
  have hrel := Λ.derivWeierstrassP_sq z hz
  have h4 : ℘'[Λ] (2 * z) * ℘'[Λ] z ^ 3 = (6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) *
      (12 * ℘[Λ] z * ℘'[Λ] z ^ 2 - (6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) ^ 2) / 4 - ℘'[Λ] z ^ 4 := by
    rw [derivWeierstrassP_two_mul Λ hz h2]
    field_simp
  have hP : (6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) * (12 * ℘[Λ] z * ℘'[Λ] z ^ 2 - (6 * ℘[Λ] z ^ 2 - Λ.g₂ / 2) ^ 2) / 4 -
      ℘'[Λ] z ^ 4 = (curve Λ).preΨ₄.eval (℘[Λ] z) := by
    rw [eval_preΨ₄]
    linear_combination (-(2 * ℘'[Λ] z ^ 2 - 28 * ℘[Λ] z ^ 3 + Λ.g₂ * ℘[Λ] z - 2 * Λ.g₃) / 2) * hrel
  rw [sigRat, show ((4 : ℕ) : ℂ) * z = 2 * (2 * z) by push_cast; ring, sigmaW_two_mul Λ h2, sigmaW_two_mul Λ hz,
    ← hP, ← h4, show (4 : ℕ) ^ 2 = 16 by norm_num]
  field_simp

/-- **The analytic division values form Mathlib's normalised elliptic divisibility sequence** at generic points:
`F(z, n) = normEDS(−℘′, Ψ₃(℘), preΨ₄(℘))(n)` (`normEDSRec`: the even and odd steps are `sigRat_rel` at
`(m + 4, m + 2)` and `(m + 3, m + 2)`, against `normEDS_even`, `normEDS_odd`). -/
theorem sigRat_eq_normEDS {z : ℂ} (hz : Generic Λ z) (n : ℕ) :
    sigRat Λ z n = normEDS (-℘'[Λ] z) ((curve Λ).Ψ₃.eval (℘[Λ] z)) ((curve Λ).preΨ₄.eval (℘[Λ] z)) n := by
  have hz1 := hz.not_mem
  have h2 : 2 * z ∉ Λ.lattice := by simpa using hz 2 two_pos
  have hb : -℘'[Λ] z ≠ 0 := neg_ne_zero.mpr (derivWeierstrassP_ne_zero Λ hz1 h2)
  set b := -℘'[Λ] z
  set c := (curve Λ).Ψ₃.eval (℘[Λ] z)
  set d := (curve Λ).preΨ₄.eval (℘[Λ] z)
  induction n using normEDSRec with
  | zero => simp [sigRat_zero]
  | one => simp [sigRat_one Λ hz1]
  | two => simp [sigRat_two Λ hz1, b]
  | three => simp [sigRat_three Λ hz1 h2, c]
  | four => simp [sigRat_four Λ hz1 h2, b, d]
  | even m h1 h2 h3 h4 h5 =>
    have hr := sigRat_rel Λ hz (a := m + 4) (b := m + 2) (by omega) (by omega)
    rw [show m + 4 + (m + 2) = 2 * (m + 3) by ring, show m + 4 - (m + 2) = 2 by omega, show m + 4 + 1 = m + 5 by rfl,
      show m + 4 - 1 = m + 3 by rfl, show m + 2 + 1 = m + 3 by rfl, show m + 2 - 1 = m + 1 by rfl,
      sigRat_two Λ hz1, h1, h2, h3, h4, h5] at hr
    have he := normEDS_even b c d ((m : ℤ) + 3)
    rw [show 2 * ((m : ℤ) + 3) = ((2 * (m + 3) : ℕ) : ℤ) by push_cast; ring,
      show (m : ℤ) + 3 - 1 = ((m + 2 : ℕ) : ℤ) by push_cast; ring,
      show (m : ℤ) + 3 + 2 = ((m + 5 : ℕ) : ℤ) by push_cast; ring,
      show (m : ℤ) + 3 - 2 = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      show (m : ℤ) + 3 + 1 = ((m + 4 : ℕ) : ℤ) by push_cast; ring,
      show (m : ℤ) + 3 = ((m + 3 : ℕ) : ℤ) by push_cast; ring] at he
    exact mul_right_cancel₀ hb (by linear_combination hr - he)
  | odd m h1 h2 h3 h4 =>
    have hr := sigRat_rel Λ hz (a := m + 3) (b := m + 2) (by omega) (by omega)
    rw [show m + 3 + (m + 2) = 2 * (m + 2) + 1 by ring, show m + 3 - (m + 2) = 1 by omega,
      show m + 3 + 1 = m + 4 by rfl, show m + 3 - 1 = m + 2 by rfl, show m + 2 + 1 = m + 3 by rfl,
      show m + 2 - 1 = m + 1 by rfl, sigRat_one Λ hz1, h1, h2, h3, h4] at hr
    have he := normEDS_odd b c d ((m : ℤ) + 2)
    rw [show 2 * ((m : ℤ) + 2) + 1 = ((2 * (m + 2) + 1 : ℕ) : ℤ) by push_cast; ring,
      show (m : ℤ) + 2 + 2 = ((m + 4 : ℕ) : ℤ) by push_cast; ring,
      show (m : ℤ) + 2 - 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      show (m : ℤ) + 2 + 1 = ((m + 3 : ℕ) : ℤ) by push_cast; ring,
      show (m : ℤ) + 2 = ((m + 2 : ℕ) : ℤ) by push_cast; ring] at he
    linear_combination hr - he

/-- **`F(z, n)² = ΨSq_n(℘(z))` at generic points** (`normEDS` and `ΨSq` are `preNormEDS` with the parameter
`b⁴ = ℘′⁴ = Ψ₂Sq(℘)²`, carried along `evalRingHom (℘ z)` by `map_preNormEDS'`). -/
theorem sigRat_sq_of_generic {z : ℂ} (hz : Generic Λ z) (n : ℕ) :
    sigRat Λ z n ^ 2 = ((curve Λ).ΨSq n).eval (℘[Λ] z) := by
  have hrel := Λ.derivWeierstrassP_sq z hz.not_mem
  have hm := map_preNormEDS' (evalRingHom (℘[Λ] z)) ((curve Λ).Ψ₂Sq ^ 2) (curve Λ).Ψ₃ (curve Λ).preΨ₄ n
  simp only [coe_evalRingHom, eval_pow, eval_Ψ₂Sq] at hm
  have hb : (-℘'[Λ] z) ^ 4 = (4 * ℘[Λ] z ^ 3 - Λ.g₂ * ℘[Λ] z - Λ.g₃) ^ 2 := by rw [← hrel]; ring
  rw [sigRat_eq_normEDS Λ hz, normEDS_ofNat, WeierstrassCurve.ΨSq_ofNat, eval_mul, eval_pow,
    show (curve Λ).preΨ' n = preNormEDS' ((curve Λ).Ψ₂Sq ^ 2) (curve Λ).Ψ₃ (curve Λ).preΨ₄ n from rfl, hm, hb]
  split_ifs
  · rw [eval_Ψ₂Sq, ← hrel]; ring
  · simp

/-! ## All points off the lattice -/

/-- **The non-generic points are countable**: they lie in `⋃_k (k + 1)⁻¹Λ`. -/
theorem countable_not_generic : {z : ℂ | ¬ Generic Λ z}.Countable := by
  refine (Set.countable_iUnion fun k : ℕ => (countable_lattice Λ).image fun l => l / ((k : ℂ) + 1)).mono ?_
  intro z hz
  simp only [Generic, Set.mem_ofPred_eq] at hz
  push Not at hz
  obtain ⟨k, hk, hkz⟩ := hz
  refine Set.mem_iUnion.mpr ⟨k - 1, _, hkz, ?_⟩
  have hk' : ((k - 1 : ℕ) : ℂ) + 1 = k := by rw [Nat.cast_sub hk]; push_cast; ring
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [hk']
  field_simp

/-- **The generic points are dense in `ℂ ∖ Λ`** (`Set.Countable.dense_compl`). -/
theorem subset_closure_generic :
    (Λ.lattice : Set ℂ)ᶜ ⊆ closure ((Λ.lattice : Set ℂ)ᶜ ∩ {z | Generic Λ z}) := by
  have hd : Dense {z : ℂ | Generic Λ z} := by
    simpa [Set.compl_ofPred] using (countable_not_generic Λ).dense_compl ℂ
  exact hd.open_subset_closure_inter Λ.isClosed_lattice.isOpen_compl

/-- **`F(·, n)` is continuous off the lattice.** -/
theorem continuousOn_sigRat (n : ℕ) : ContinuousOn (fun z => sigRat Λ z n) (Λ.lattice : Set ℂ)ᶜ := by
  have hσ := (differentiable_sigmaW Λ).continuous
  exact ((hσ.comp (continuous_const.mul continuous_id)).continuousOn).div (hσ.pow _).continuousOn
    fun z hz => pow_ne_zero _ (sigmaW_ne_zero Λ hz)

/-- **`F(z, n)² = ΨSq_n(℘(z))` off the lattice** (`sigRat_sq_of_generic`, by density and continuity). -/
theorem sigRat_sq {z : ℂ} (hz : z ∉ Λ.lattice) (n : ℕ) : sigRat Λ z n ^ 2 = ((curve Λ).ΨSq n).eval (℘[Λ] z) :=
  Set.EqOn.of_subset_closure (f := fun z => sigRat Λ z n ^ 2) (g := fun z => ((curve Λ).ΨSq n).eval (℘[Λ] z))
    (fun _ hw => sigRat_sq_of_generic Λ hw.2 n) ((continuousOn_sigRat Λ n).pow 2)
    ((Polynomial.continuous _).comp_continuousOn Λ.differentiableOn_weierstrassP.continuousOn)
    Set.inter_subset_left (subset_closure_generic Λ) hz

/-- **`℘(q)` is a root of `ΨSq_N`** for `q ∉ Λ` with `Nq ∈ Λ` (`sigRat_sq`, `σ(Nq) = 0`). -/
theorem eval_ΨSq_eq_zero {q : ℂ} (hq : q ∉ Λ.lattice) {N : ℕ} (hN : (N : ℂ) * q ∈ Λ.lattice) :
    ((curve Λ).ΨSq N).eval (℘[Λ] q) = 0 := by
  have h := sigRat_sq Λ hq N
  rw [sigRat, (sigmaW_eq_zero_iff Λ _).2 hN, zero_div, zero_pow two_ne_zero] at h
  exact h.symm

end

end EllipticDivPoly
