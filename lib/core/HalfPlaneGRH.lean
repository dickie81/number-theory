import Mathlib
import T1bt

/-!
# The Riemann hypothesis for `ζ` and every Dirichlet `L`-function, from a zero-free half-plane

The top step of the library's proof of the Riemann hypothesis (`docs/rh-rebuild.md`). The steps below it prove
that no primitive Dirichlet `L`-function vanishes right of the critical line; this file turns that into the
Riemann hypothesis for `ζ` and for the `L`-function of every Dirichlet character.

* `ZeroFreeRightOf θ`: no `L(s, χ)` with `χ` primitive vanishes on `Re s > θ`, the pole of `ζ` at `s = 1` aside.
* `LFunction_ne_zero_of_zeroFreeRightOf`: for `θ ≥ 0`, the same for every character. `L(s, χ)` is `L(s, χ*)`,
  for the primitive character `χ*` that induces `χ`, times the Euler factors `1 − χ*(p) p^{−s}` at the primes
  dividing the modulus (Mathlib's `LFunction_changeLevel`), and these have no zero on `Re s > 0`
  (`eulerFactor_ne_zero`).
* `LFunction_inv_one_sub_eq_zero`: a zero `s` of `L(s, χ)`, `χ` primitive, in the open strip makes `1 − s` a
  zero of `L(s, χ⁻¹)`. The gamma factor has no zero on `Re s > 0`, so `s` is a zero of the completed
  `L`-function of `χ`, and the functional equation of `χ⁻¹`, which is primitive too, carries it to `1 − s`.
* `re_eq_half_of_zeroFreeRightOf`: at `θ = 1/2`, every zero of every `L(s, χ)` in the critical strip lies on
  the line `Re s = 1/2`.
* `riemannHypothesis_of_zeta_ne_zero`: Mathlib's `RiemannHypothesis` from `ζ` alone. A nontrivial zero lies in the
  open strip (the library's `WeilTest.IsNontrivialZero.mem_strip`), and the functional equation of `ζ` reflects
  one left of the line to the right. `riemannHypothesis_of_zeroFreeRightOf` is the case of the character mod `1`.
* `zeroFreeRightOf_half_iff`: the half-plane at `1/2` is equivalent to those two conclusions together, so this
  step neither adds to nor takes from what the steps below must prove.
-/

open Complex DirichletCharacter

namespace HalfPlaneGRH

/-- No `L(s, χ)` with `χ` primitive vanishes on `Re s > θ`, the pole of `ζ` at `s = 1` aside. -/
def ZeroFreeRightOf (θ : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, θ < s.re → (χ ≠ 1 ∨ s ≠ 1) → LFunction χ s ≠ 0

/-- The Riemann hypothesis for `ζ`, and for the `L`-function of every Dirichlet character: every zero in the
open critical strip lies on the line (the library's `PsiOmega.GRH` for each character). -/
def RHandGRH : Prop :=
  RiemannHypothesis ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-! ## Every character from the primitive ones -/

/-- An Euler factor `1 − a p^{−s}` with `‖a‖ ≤ 1` has no zero on `Re s > 0`. -/
theorem eulerFactor_ne_zero {p : ℕ} (hp : p.Prime) {a : ℂ} (ha : ‖a‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    1 - a * (p : ℂ) ^ (-s) ≠ 0 := by
  have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_lt_zero.2 hs)
  intro h
  have h1 : a * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have h2 : ‖a * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) hlt
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- On `Re s > 0` the `L`-function of a character induced from level `M` vanishes exactly where the
`L`-function at level `M` does. -/
theorem LFunction_changeLevel_eq_zero_iff {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    LFunction (changeLevel hMN χ) s = 0 ↔ LFunction χ s = 0 := by
  rw [LFunction_changeLevel hMN χ hχs, mul_eq_zero, or_iff_left]
  exact Finset.prod_ne_zero_iff.2 fun p hp =>
    eulerFactor_ne_zero (Nat.prime_of_mem_primeFactors hp) (χ.norm_le_one _) hs

/-- The primitive character that induces `χ` is trivial only when `χ` is. -/
theorem primitiveCharacter_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := fun h =>
  hχ (by rw [← changeLevel_primitiveCharacter χ, h, map_one])

/-- On `Re s > 0`, `L(s, χ)` vanishes exactly where `L(s, χ*)` does, `χ*` the primitive character that
induces `χ`. -/
theorem LFunction_eq_zero_iff_primitive {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have key := LFunction_changeLevel_eq_zero_iff χ.conductor_dvd_level χ.primitiveCharacter hs
    (hχs.imp_left primitiveCharacter_ne_one)
  rwa [changeLevel_primitiveCharacter] at key

/-- For `θ ≥ 0`, a zero-free half-plane for the primitive characters is one for every character. -/
theorem LFunction_ne_zero_of_zeroFreeRightOf {θ : ℝ} (h : ZeroFreeRightOf θ) (hθ : 0 ≤ θ) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : θ < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) : LFunction χ s ≠ 0 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [ne_eq, LFunction_eq_zero_iff_primitive χ (lt_of_le_of_lt hθ hs) hχs]
  exact h _ _ χ.primitiveCharacter_isPrimitive s hs (hχs.imp_left primitiveCharacter_ne_one)

/-! ## The functional equation -/

/-- The inverse of a primitive character is primitive. -/
theorem isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [isPrimitive_def, conductor_inv]
  exact (isPrimitive_def _).1 hχ

/-- The gamma factor of a Dirichlet character has no zero on `Re s > 0`. -/
theorem gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    gammaFactor χ s ≠ 0 := by
  unfold gammaFactor
  split_ifs
  · exact Gammaℝ_ne_zero_of_re_pos hs
  · exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

/-- A zero `s` of `L(s, χ)`, `χ` primitive, with `0 < Re s < 1` makes `1 − s` a zero of `L(s, χ⁻¹)`. -/
theorem LFunction_inv_one_sub_eq_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : LFunction χ s = 0) : LFunction χ⁻¹ (1 - s) = 0 := by
  have hs : s ≠ 0 := fun e => by rw [e, zero_re] at hs0; exact lt_irrefl _ hs0
  have h1s : 1 - s ≠ 0 := fun e => by
    have := congrArg re e
    rw [sub_re, one_re, zero_re] at this
    linarith
  have hc : completedLFunction χ s = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs), div_eq_zero_iff] at hz
    exact hz.resolve_right (gammaFactor_ne_zero χ hs0)
  have hfe := (isPrimitive_inv hχ).completedLFunction_one_sub s
  rw [inv_inv, hc, mul_zero] at hfe
  rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h1s), hfe, zero_div]

/-! ## The critical line -/

/-- **The Riemann hypothesis for every Dirichlet `L`-function**, from the half-plane at `1/2`. -/
theorem re_eq_half_of_zeroFreeRightOf (h : ZeroFreeRightOf (1 / 2)) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hz : LFunction χ s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
    s.re = 1 / 2 := by
  have hs1 : s ≠ 1 := fun e => by rw [e, one_re] at h1; exact lt_irrefl _ h1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hz' := (LFunction_eq_zero_iff_primitive χ h0 (Or.inr hs1)).1 hz
    have h' := LFunction_inv_one_sub_eq_zero χ.primitiveCharacter_isPrimitive h0 h1 hz'
    refine h _ _ (isPrimitive_inv χ.primitiveCharacter_isPrimitive) (1 - s)
      (by rw [sub_re, one_re]; linarith) (Or.inr fun e => ?_) h'
    have := congrArg re e
    rw [sub_re, one_re] at this
    linarith
  · exact heq
  · exact absurd hz (LFunction_ne_zero_of_zeroFreeRightOf h (by norm_num) χ hgt (Or.inr hs1))

/-- **The Riemann hypothesis from `ζ` alone**: if `ζ` has no zero on `Re s > 1/2`, Mathlib's `RiemannHypothesis`
holds. A nontrivial zero lies in the open strip (`WeilTest.IsNontrivialZero.mem_strip`). One left of the line would
give, by the functional equation, the zero `1 − s` right of it. -/
theorem riemannHypothesis_of_zeta_ne_zero (h : ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  obtain ⟨h0, h1⟩ := WeilTest.IsNontrivialZero.mem_strip ⟨hz, htriv⟩
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · have hn : ∀ n : ℕ, s ≠ -n := fun n e => by
      have := congrArg re e
      rw [neg_re, natCast_re] at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hfe := riemannZeta_one_sub hn hs1
    rw [hz, mul_zero] at hfe
    exact absurd hfe (h (1 - s) (by rw [sub_re, one_re]; linarith))
  · exact heq
  · exact absurd hz (h s hgt)

/-- **The Riemann hypothesis** (Mathlib's `RiemannHypothesis`), from the half-plane at `1/2`. -/
theorem riemannHypothesis_of_zeroFreeRightOf (h : ZeroFreeRightOf (1 / 2)) : RiemannHypothesis := by
  refine riemannHypothesis_of_zeta_ne_zero fun s hs => ?_
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero
  · have := h 1 (1 : DirichletCharacter ℂ 1) isPrimitive_one_level_one s hs (Or.inr hs1)
    rwa [LFunction_modOne_eq] at this

/-- **The Riemann hypothesis for `ζ` and every Dirichlet `L`-function**, from the half-plane at `1/2`. -/
theorem rhAndGRH_of_zeroFreeRightOf (h : ZeroFreeRightOf (1 / 2)) : RHandGRH :=
  ⟨riemannHypothesis_of_zeroFreeRightOf h, fun _ _ χ _ hz h0 h1 => re_eq_half_of_zeroFreeRightOf h χ hz h0 h1⟩

/-- The half-plane at `1/2` is equivalent to the Riemann hypothesis for `ζ` and every Dirichlet `L`-function:
the step from it loses nothing. -/
theorem zeroFreeRightOf_half_iff : ZeroFreeRightOf (1 / 2) ↔ RHandGRH := by
  refine ⟨rhAndGRH_of_zeroFreeRightOf, fun h N _ χ _ s hs hχs hz => ?_⟩
  rcases lt_or_ge s.re 1 with h1 | h1
  · have := h.2 N χ s hz (by linarith) h1
    linarith
  · exact LFunction_ne_zero_of_one_le_re χ hχs h1 hz

end HalfPlaneGRH

#print axioms HalfPlaneGRH.rhAndGRH_of_zeroFreeRightOf
#print axioms HalfPlaneGRH.zeroFreeRightOf_half_iff
