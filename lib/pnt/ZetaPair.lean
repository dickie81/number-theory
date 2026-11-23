import ZetaThin
import ZetaTwist

/-!
# The pair-first frontiers — CONDITIONAL on the half-plane

A step of the library's proof of the Riemann hypothesis for `ζ` and every Dirichlet `L`-function
(`docs/rh-rebuild.md`, "The analytic inputs"): the twists (`ZetaTwist.exists_winPair_twists`) and the thin scales
(`ZetaBalance.thin_of_large`) joined to the frontiers after step 4. What is left, `PairBound` for every primitive
character and `ZetaPairBound` for `ζ`, is the construction alone.

**CONDITIONAL.** `rhAndGRH_of_pairBound` and `riemannHypothesis_of_zetaPairBound` use the half-plane `Re s > 11/12` for
`ζ` and every Dirichlet `L`-function (`Eis.LFunction_ne_zero_of_re_gt`), an input formalised in the library that no
referee has read (see `formalisations/openai-half-plane.md`), through `ZetaTwist.exists_winPair_twists` and
`ZetaBalance.thin_of_large`. Lean checks them with the standard axioms only, but they are only as good as that input,
and must be cited as conditional on it.

* **The twists of a setting as concrete characters** (`Setting.Lifts.g_twist`). For `κ` lifting `χ` mod `f`
  (`Setting.Lifts`), `κ̃^k` is `χ^k` at the level `QS` (`Setting.lift_pow`), so `D_{(α,β,κ^k)}` is the twist
  `χ_d^α χ_q^β χ^k` (`ZetaTwist.twist`) changed from the level `f·q·d` to `N`. Its primitive character has the conductor
  and the values of the twist's (`prim_changeLevel`), so the same ramp error. So bounds on the `3o` twists at `x` give
  `Setting.Twists` (`Setting.Lifts.twists_of_le`). For `ζ`, `κ = 1` lifts the character mod `1` (`Setting.lifts_one`).
* **The frontiers**, `PairBound` and `ZetaPairBound`, have the shape of the archive's window input: the pair first, then
  a sub-window, at arbitrarily small `ε`. For every large `Y`, every pair `(q, d)` with the arithmetic of
  `ZetaTwist.WinPair` has a sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, on which every `x` has lattice data in a
  setting with that pair; for `PairBound`, with a character `κ` of `A` lifting `χ`. Such settings exist once `Y` is
  large: a pair of `ZetaTwist.WinPair` has `d ≡ 7 (mod 16)` and `d ≡ −1` modulo every odd prime `p ≤ Y^{ε/5}`, so
  `(p/d) = 1` for every prime `p ≤ Y^{ε/5}`, and a modulus `QS` built from `f` and a power of `2` meets `Setting.split`.
* **The theorems.** Given `θ > 1/2`, take `ε < (θ − 1/2)/3`. A large `Y` has a pair whose twists are small on
  `[Y, Y^A]`, and the frontier gives `Y′`. On `[Y′, Y′²] ⊆ [Y, Y^A]` the setting is thin and its twists are small, so
  Theorem Z bounds the weighted error of the cyclic family of `χ` by `(9o − 2)x^{1/2+3ε} ≤ (9o − 2)x^θ`, the kept errors
  by the crude bound `eventually_norm_rampErr_le`. That is `WindowGRH.WindowBound` with `λ = 2`
  (`rhAndGRH_of_pairBound`); for `ζ` it is `WindowGRH.ZetaWindowBound` with `λ = 2` and `C = 7`
  (`riemannHypothesis_of_zetaPairBound`).
-/

open DirichletCharacter

namespace ZetaBalance

namespace Setting

variable {S : Setting} {κ : S.A →* ℂˣ} {f : ℕ} [NeZero f] {χ : DirichletCharacter ℂ f}

/-- **The twists of a setting as concrete characters**: for `κ` lifting `χ`, `g_{(α,β,κ^k)}` is the ramp error of the
primitive character of the twist `χ_d^α χ_q^β χ^k` (`ZetaTwist.twist`). `D_{(α,β,κ^k)}` is that twist, changed from the
level `f·q·d` to `N`. -/
theorem Lifts.g_twist (hL : S.Lifts κ χ) (α β : Bool) (k : ℕ) (y : ℝ) :
    S.g (α, β, κ ^ k) y = WindowGRH.rampErr (ZetaTwist.twist (χ ^ k) S.q S.d α β).primitiveCharacter y := by
  obtain ⟨h, hl⟩ := hL
  have hN : f * S.q * S.d ∣ S.N := mul_dvd_mul_right (mul_dvd_mul_right h _) _
  have hD : S.D (α, β, κ ^ k) = changeLevel hN (ZetaTwist.twist (χ ^ k) S.q S.d α β) := by
    simp only [D, ZetaTwist.twist, map_mul, map_pow, ← changeLevel_trans, S.lift_pow, hl]
  rw [g]
  exact rampErr_congr (by rw [hD, conductor_changeLevel]) (fun n => by rw [hD, prim_changeLevel]) y

/-- **The twists of a setting are small** at `x` when the `3o` twists `χ_d^α χ_q^β χ^k` of `χ`, `(α, β) ≠ (0, 0)` and
`k < o`, are. -/
theorem Lifts.twists_of_le (hL : S.Lifts κ χ) {x ε : ℝ}
    (h : ∀ α β : Bool, (α || β) = true → ∀ k < orderOf χ,
      ‖WindowGRH.rampErr (ZetaTwist.twist (χ ^ k) S.q S.d α β).primitiveCharacter x‖ ≤ x ^ (1 / 2 + ε)) :
    S.Twists κ x ε := fun α β hαβ k hk => by
  rw [hL.g_twist]
  exact h α β hαβ k (hL.orderOf_eq ▸ hk)

/-- `κ = 1` lifts the character mod `1`. -/
theorem lifts_one (S : Setting) : S.Lifts 1 (1 : DirichletCharacter ℂ 1) :=
  ⟨one_dvd _, by rw [S.lift_one, map_one]⟩

end Setting

/-- **The pair-first frontier for every primitive character**, the construction alone: every analytic input is proved,
conditionally on the half-plane (`rhAndGRH_of_pairBound`). For every primitive `χ`, at arbitrarily small `ε` there is
`A ≥ 1` such that, for every large `Y`, every pair `(q, d)` meeting `ZetaTwist.WinPair ε Y` has a sub-window
`[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, at each `x` of which a setting with that pair and a character `κ` of `A` lifting
`χ` has lattice data whose thin classes lie beyond `(Nx)^{log x}`. -/
def PairBound : Prop :=
  ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → ∀ ε₀ > 0, ∃ ε, 0 < ε ∧ ε < ε₀ ∧
    ∃ A ≥ (1 : ℝ), ∀ᶠ Y in Filter.atTop, ∀ q d, ZetaTwist.WinPair ε Y q d →
      ∃ Y' ∈ Set.Icc Y (Y ^ (A / 2)), ∀ x ∈ Set.Icc Y' (Y' ^ 2), ∃ (S : Setting) (κ : S.A →* ℂˣ), S.q = q ∧
        S.d = d ∧ S.Lifts κ χ ∧ Nonempty (LatticeData S κ x ε (((S.N : ℝ) * x) ^ Real.log x))

/-- **CONDITIONAL. The Riemann hypothesis for `ζ` and every Dirichlet `L`-function from the pair-first frontier**
(conditional on the half-plane `Re s > 11/12`, through `ZetaTwist.exists_winPair_twists` and `thin_of_large`). -/
theorem rhAndGRH_of_pairBound (h : PairBound) : HalfPlaneGRH.RHandGRH := by
  obtain ⟨x₀, hx₀⟩ := thin_of_large
  refine WindowGRH.rhAndGRH_of_windowBound fun f _ χ hχ θ hθ => ?_
  obtain ⟨ε, hε, hεθ, A, hA, hfr⟩ := h f χ hχ (min ((θ - 1 / 2) / 3) (1 / 2)) (lt_min (by linarith) (by norm_num))
  obtain ⟨hεθ, hε2⟩ := lt_min_iff.1 hεθ
  -- the kept errors are eventually at most `x^{3/2+ε}`
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 fun k : Fin (orderOf χ) =>
    eventually_norm_rampErr_le (χ ^ (k : ℕ)).primitiveCharacter hε)
  have ho : (0 : ℝ) ≤ 9 * orderOf χ - 2 := by
    have : (1 : ℝ) ≤ orderOf χ := by exact_mod_cast orderOf_pos χ
    linarith
  refine ⟨2, one_lt_two, 9 * orderOf χ - 2, fun Y₀ => ?_⟩
  -- a large `Y`, a pair whose twists are small on `[Y, Y^A]`, and the sub-window `[Y′, Y′²]` of that pair
  obtain ⟨Y, ⟨hfrY, q, d, hp, htw⟩, hY⟩ := ((hfr.and (ZetaTwist.exists_winPair_twists χ hε hε2.le hA)).and
    (Filter.eventually_ge_atTop (max Y₀ (max x₀ (max x₁ 1))))).exists
  obtain ⟨hY₀, hx₀Y, hx₁Y, hY1⟩ : Y₀ ≤ Y ∧ x₀ ≤ Y ∧ x₁ ≤ Y ∧ 1 ≤ Y := by simpa using hY
  obtain ⟨Y', ⟨hYY', hY'⟩, hx⟩ := hfrY q d hp
  refine ⟨Y', hY₀.trans hYY', fun x hx' => ?_⟩
  rw [Real.rpow_two] at hx'
  obtain ⟨S, κ, rfl, rfl, hL, ⟨L⟩⟩ := hx x hx'
  -- `x ∈ [Y′, Y′²] ⊆ [Y, Y^A]`, so the setting is thin and its twists are small: Theorem Z
  have hYx : Y ≤ x := hYY'.trans hx'.1
  have hxA : x ≤ Y ^ A :=
    calc x ≤ Y' ^ 2 := hx'.2
      _ ≤ (Y ^ (A / 2)) ^ 2 := pow_le_pow_left₀ (by linarith) hY' 2
      _ = Y ^ A := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hZ := L.toBalanceData.cyclicG_le (hx₀ x (hx₀Y.trans hYx) S) (hL.twists_of_le (htw x ⟨hYx, hxA⟩))
    (fun k _ hk => by
      rw [hL.g_pow]
      exact hx₁ x (hx₁Y.trans hYx) ⟨k, hL.orderOf_eq ▸ hk⟩) (hY1.trans hYx) hε.le
  rw [hL.cyclicG_eq, hL.orderOf_eq] at hZ
  exact hZ.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hY1.trans hYx) (by linarith)) ho)

/-- **The pair-first frontier for `ζ`**, the construction alone: every analytic input is proved, conditionally on the
half-plane (`riemannHypothesis_of_zetaPairBound`). At arbitrarily small `ε` there is `A ≥ 1` such that, for every large
`Y`, every pair `(q, d)` meeting `ZetaTwist.WinPair ε Y` has a sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, at each
`x` of which a setting with that pair has lattice data whose thin classes lie beyond `(Nx)^{log x}`. -/
def ZetaPairBound : Prop :=
  ∀ ε₀ > 0, ∃ ε, 0 < ε ∧ ε < ε₀ ∧ ∃ A ≥ (1 : ℝ), ∀ᶠ Y in Filter.atTop, ∀ q d, ZetaTwist.WinPair ε Y q d →
    ∃ Y' ∈ Set.Icc Y (Y ^ (A / 2)), ∀ x ∈ Set.Icc Y' (Y' ^ 2), ∃ S : Setting, S.q = q ∧ S.d = d ∧
      Nonempty (LatticeData S 1 x ε (((S.N : ℝ) * x) ^ Real.log x))

/-- **CONDITIONAL. The Riemann hypothesis from the pair-first frontier** (conditional on the half-plane
`Re s > 11/12`, through `ZetaTwist.exists_winPair_twists` and `thin_of_large`). -/
theorem riemannHypothesis_of_zetaPairBound (h : ZetaPairBound) : RiemannHypothesis := by
  obtain ⟨x₀, hx₀⟩ := thin_of_large
  refine WindowGRH.riemannHypothesis_of_zetaWindowBound fun θ hθ => ?_
  obtain ⟨ε, hε, hεθ, A, hA, hfr⟩ := h (min ((θ - 1 / 2) / 3) (1 / 2)) (lt_min (by linarith) (by norm_num))
  obtain ⟨hεθ, hε2⟩ := lt_min_iff.1 hεθ
  refine ⟨2, one_lt_two, 7, fun Y₀ => ?_⟩
  -- a large `Y`, a pair whose twists are small on `[Y, Y^A]`, and the sub-window `[Y′, Y′²]` of that pair
  obtain ⟨Y, ⟨hfrY, q, d, hp, htw⟩, hY⟩ := ((hfr.and
    (ZetaTwist.exists_winPair_twists (1 : DirichletCharacter ℂ 1) hε hε2.le hA)).and
    (Filter.eventually_ge_atTop (max Y₀ (max x₀ 1)))).exists
  obtain ⟨hY₀, hx₀Y, hY1⟩ : Y₀ ≤ Y ∧ x₀ ≤ Y ∧ 1 ≤ Y := by simpa using hY
  obtain ⟨Y', ⟨hYY', hY'⟩, hx⟩ := hfrY q d hp
  refine ⟨Y', hY₀.trans hYY', fun x hx' => ?_⟩
  rw [Real.rpow_two] at hx'
  obtain ⟨S, rfl, rfl, ⟨L⟩⟩ := hx x hx'
  -- `x ∈ [Y′, Y′²] ⊆ [Y, Y^A]`, so the setting is thin and its twists are small: Theorem Z
  have hYx : Y ≤ x := hYY'.trans hx'.1
  have hxA : x ≤ Y ^ A :=
    calc x ≤ Y' ^ 2 := hx'.2
      _ ≤ (Y ^ (A / 2)) ^ 2 := pow_le_pow_left₀ (by linarith) hY' 2
      _ = Y ^ A := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  calc _ ≤ 7 * x ^ (1 / 2 + 3 * ε) := L.toBalanceData.zeta_le (hx₀ x (hx₀Y.trans hYx) S)
        (S.lifts_one.twists_of_le (htw x ⟨hYx, hxA⟩)) (hY1.trans hYx) hε.le
    _ ≤ 7 * x ^ θ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hY1.trans hYx) (by linarith)) (by norm_num)

end ZetaBalance

#print axioms ZetaBalance.rhAndGRH_of_pairBound
#print axioms ZetaBalance.riemannHypothesis_of_zetaPairBound
