import ZetaThin
import ZetaTwist

/-!
# The pair-first frontier for `ζ` — CONDITIONAL on the half-plane

A step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`, "The analytic inputs"): the twists
(`ZetaTwist.exists_winPair_twists`) and the thin scales (`ZetaBalance.thin_of_large`) joined to the frontier after
step 4. What is left, `ZetaPairBound`, is the construction alone.

**CONDITIONAL.** `riemannHypothesis_of_zetaPairBound` uses the half-plane `Re s > 11/12` for `ζ` and every Dirichlet
`L`-function (`Eis.LFunction_ne_zero_of_re_gt`), an input formalised in the library that no referee has read (see
`formalisations/openai-half-plane.md`), through `ZetaTwist.exists_winPair_twists` and `ZetaBalance.thin_of_large`. Lean
checks it with the standard axioms only, but it is only as good as that input, and must be cited as conditional on it.

* **The twists as concrete characters.** The three twists of a setting are the ramp errors `E_χ` of `χ_d`, `χ_q` and
  `χ_qχ_d` (`Setting.g_d`, `Setting.g_q`, `Setting.g_qd`). Each `D_χ` is a primitive character `ψ` changed to the
  level `N`, and the primitive character of `ψ` at a higher level has the conductor and the values of `ψ`, so the same
  ramp error (`rampErr_prim_changeLevel`). `χ_qχ_d` is primitive (`ZetaTwist.chiQD_isPrimitive`): its primitive
  character vanishes at `d`, as `χ_d` does, and at `q` (`ZetaBalance.prim_mul_apply`). So bounds on the three at `x`
  give `Setting.Twists` (`Setting.twists_of_le`).
* **The frontier**, `ZetaPairBound`, has the shape of the archive's window input: the pair first, then a sub-window, at
  arbitrarily small `ε`. For every large `Y`, every pair `(q, d)` with the arithmetic of `ZetaTwist.WinPair` has a
  sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, on which every `x` has lattice data in a setting with that pair.
* **The Riemann hypothesis** (`riemannHypothesis_of_zetaPairBound`). Given `θ > 1/2`, take `ε < (θ − 1/2)/3`. A large
  `Y` has a pair whose twists are small on `[Y, Y^A]`, and the frontier gives `Y′`. On `[Y′, Y′²] ⊆ [Y, Y^A]` the
  setting is thin and its twists are small, so Theorem Z gives `Gz(x) ≤ 7x^{1/2+3ε} ≤ 7x^θ`. That is
  `WindowGRH.ZetaWindowBound` with `λ = 2` and `C = 7`.
-/

open DirichletCharacter ZetaBalance

namespace ZetaTwist

/-- **`χ_qχ_d` is primitive**, for distinct odd primes `q` and `d`. Its primitive character vanishes at `d`, as `χ_d`
does (`ZetaBalance.prim_mul_apply`), and likewise at `q`, so `qd` divides its conductor. -/
theorem chiQD_isPrimitive {q d : ℕ} [hq : Fact q.Prime] [hd : Fact d.Prime] (hq2 : q ≠ 2) (hd2 : d ≠ 2)
    (hqd : q ≠ d) : (chiQD q d).IsPrimitive := by
  have hcop := (Nat.coprime_primes hq.out hd.out).2 hqd
  have hzero {p : ℕ} (hp : p.Prime) (h : (chiQD q d).primitiveCharacter p = 0) : p ∣ (chiQD q d).conductor := by
    rwa [← Int.cast_natCast, apply_eq_zero_iff, Nat.isCoprime_iff_coprime, hp.coprime_iff_not_dvd, not_not] at h
  have h1 : (chiQD q d).primitiveCharacter d = 0 := by
    rw [chiQD, prim_mul_apply _ _ _ hd.out (hd.out.coprime_iff_not_dvd.1 hcop.symm), prim_changeLevel,
      prim_apply_of_isPrimitive (legChar_isPrimitive hd2), ZMod.natCast_self, legChar_zero, mul_zero]
  have h2 : (chiQD q d).primitiveCharacter q = 0 := by
    rw [chiQD, mul_comm (changeLevel _ (legChar q)), prim_mul_apply _ _ _ hq.out (hq.out.coprime_iff_not_dvd.1 hcop),
      prim_changeLevel, prim_apply_of_isPrimitive (legChar_isPrimitive hq2), ZMod.natCast_self, legChar_zero,
      mul_zero]
  exact Nat.dvd_antisymm (conductor_dvd_level _) (hcop.mul_dvd_of_dvd_of_dvd (hzero hq.out h2) (hzero hd.out h1))

end ZetaTwist

namespace ZetaBalance

/-- Two characters with the same values, at levels that are equal only propositionally, have the same ramp error. -/
theorem rampErr_congr {M M' : ℕ} [NeZero M] [NeZero M'] (h : M = M') {ψ : DirichletCharacter ℂ M}
    {ψ' : DirichletCharacter ℂ M'} (hv : ∀ n : ℕ, ψ n = ψ' n) (y : ℝ) :
    WindowGRH.rampErr ψ y = WindowGRH.rampErr ψ' y := by
  subst h
  obtain rfl : ψ = ψ' := MulChar.ext' fun x => by rw [← ZMod.natCast_zmod_val x]; exact hv x.val
  rfl

/-- The ramp error of the primitive character of `D`, a primitive `ψ` changed to a higher level, is that of `ψ`. -/
theorem rampErr_prim_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (h : M ∣ N) {ψ : DirichletCharacter ℂ M}
    (hψ : ψ.IsPrimitive) {D : DirichletCharacter ℂ N} (hD : D = changeLevel h ψ) (y : ℝ) :
    WindowGRH.rampErr D.primitiveCharacter y = WindowGRH.rampErr ψ y := by
  subst hD
  exact rampErr_congr (by rw [conductor_changeLevel, (isPrimitive_def _).1 hψ])
    (fun n => by rw [prim_changeLevel, prim_apply_of_isPrimitive hψ]) y

namespace Setting

variable (S : Setting)

/-- **The twist by `χ_d`**: `g_χ = E_{χ_d}` at `χ = (1, 0, 1)`, where `D_χ` is `χ_d` at the level `N`. -/
theorem g_d (y : ℝ) : S.g (true, false, 1) y = WindowGRH.rampErr (legChar S.d) y :=
  rampErr_prim_changeLevel S.d_dvd_N (legChar_isPrimitive S.d_ne_two) (by simp [D, legPow, lift_one]) y

/-- **The twist by `χ_q`**: `g_χ = E_{χ_q}` at `χ = (0, 1, 1)`, where `D_χ` is `χ_q` at the level `N`. -/
theorem g_q (y : ℝ) : S.g (false, true, 1) y = WindowGRH.rampErr (legChar S.q) y :=
  rampErr_prim_changeLevel S.q_dvd_N (legChar_isPrimitive S.q_ne_two) (by simp [D, legPow, lift_one]) y

/-- **The twist by `χ_qχ_d`**: `g_χ = E_{χ_qχ_d}` at `χ = (1, 1, 1)`, where `D_χ` is `χ_qχ_d` (`ZetaTwist.chiQD`) at
the level `N`. -/
theorem g_qd (y : ℝ) : S.g (true, true, 1) y = WindowGRH.rampErr (ZetaTwist.chiQD S.q S.d) y :=
  rampErr_prim_changeLevel (⟨2 ^ (S.e + 2), by rw [N]; ring⟩ : S.q * S.d ∣ S.N)
    (ZetaTwist.chiQD_isPrimitive S.q_ne_two S.d_ne_two S.q_ne_d) (by
      rw [ZetaTwist.chiQD, map_mul, ← changeLevel_trans, ← changeLevel_trans,
        mul_comm (changeLevel _ (legChar S.q))]
      simp [D, legPow, lift_one]) y

/-- **The twists of a setting are small** at `x` when the ramp errors of `χ_q`, `χ_d` and `χ_qχ_d` are at most
`x^{1/2+ε}` there. -/
theorem twists_of_le {x ε : ℝ} (h : ‖WindowGRH.rampErr (legChar S.q) x‖ ≤ x ^ (1 / 2 + ε) ∧
    ‖WindowGRH.rampErr (legChar S.d) x‖ ≤ x ^ (1 / 2 + ε) ∧
    ‖WindowGRH.rampErr (ZetaTwist.chiQD S.q S.d) x‖ ≤ x ^ (1 / 2 + ε)) : S.Twists x ε := by
  rintro (_ | _) (_ | _) hαβ
  · simp at hαβ
  · rw [S.g_q]
    exact h.1
  · rw [S.g_d]
    exact h.2.1
  · rw [S.g_qd]
    exact h.2.2

end Setting

/-- **The pair-first frontier for `ζ`**, the construction alone: every analytic input is proved, conditionally on the
half-plane (`riemannHypothesis_of_zetaPairBound`). At arbitrarily small `ε` there is `A ≥ 1` such that, for every large
`Y`, every pair `(q, d)` meeting `ZetaTwist.WinPair ε Y` has a sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, at each
`x` of which a setting with that pair has lattice data whose thin classes lie beyond `(Nx)^{log x}`. -/
def ZetaPairBound : Prop :=
  ∀ ε₀ > 0, ∃ ε, 0 < ε ∧ ε < ε₀ ∧ ∃ A ≥ (1 : ℝ), ∀ᶠ Y in Filter.atTop, ∀ q d, ZetaTwist.WinPair ε Y q d →
    ∃ Y' ∈ Set.Icc Y (Y ^ (A / 2)), ∀ x ∈ Set.Icc Y' (Y' ^ 2), ∃ S : Setting, S.q = q ∧ S.d = d ∧
      Nonempty (LatticeData S x ε (((S.N : ℝ) * x) ^ Real.log x))

/-- **CONDITIONAL. The Riemann hypothesis from the pair-first frontier** (conditional on the half-plane
`Re s > 11/12`, through `ZetaTwist.exists_winPair_twists` and `thin_of_large`). -/
theorem riemannHypothesis_of_zetaPairBound (h : ZetaPairBound) : RiemannHypothesis := by
  obtain ⟨x₀, hx₀⟩ := thin_of_large
  refine WindowGRH.riemannHypothesis_of_zetaWindowBound fun θ hθ => ?_
  obtain ⟨ε, hε, hεθ, A, hA, hfr⟩ := h (min ((θ - 1 / 2) / 3) (1 / 2)) (lt_min (by linarith) (by norm_num))
  obtain ⟨hεθ, hε2⟩ := lt_min_iff.1 hεθ
  refine ⟨2, one_lt_two, 7, fun Y₀ => ?_⟩
  -- a large `Y`, a pair whose twists are small on `[Y, Y^A]`, and the sub-window `[Y′, Y′²]` of that pair
  obtain ⟨Y, ⟨hfrY, q, d, hp, htw⟩, hY⟩ := ((hfr.and (ZetaTwist.exists_winPair_twists hε hε2.le hA)).and
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
        (S.twists_of_le (htw x ⟨hYx, hxA⟩)) (hY1.trans hYx) hε.le
    _ ≤ 7 * x ^ θ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hY1.trans hYx) (by linarith)) (by norm_num)

end ZetaBalance

#print axioms ZetaBalance.riemannHypothesis_of_zetaPairBound
