import Mathlib

/-!
# The constant package of the gain

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain` and the design's Stage 2): the absolute
numerals that the gain's local exponents and the design's band and windows read, gathered in one package `Kg`
(`GainConsts`), so that the design (`DesignOrbits`, and the Stage 2 clauses of `SharpAdm`) and the gain (its
exponents and its local theorems) read the same values. Nothing here depends on `x`, `ε` or the setting.

**The constants**, by where they enter (the gain spec, §2.5 and §2.6):
* the slack `sl = c_{dl,1}·n_p·N_m²·log_p(2a) + c_{dl,2}·#tops·log_p(2a)²` and the penalty term `c_Pr·n_p·(…)` at
  `p ≥ p₀`: `cdl₁ = 5`, `cdl₂ = 4`, `cPr = 1`, the archive's values;
* the band `ρ_B = 4N_⋆x^ε·La/k + c_ρ·c_N·log x·La/k` and the loss factor `La = c_La·N₁²·log a`, which also sets the
  window `W_b` of the top shifts: `cLa`, `cρ`, `cN`;
* the depth (`c_{κ,1}`, `c_{κ,2}` at `p ≥ p₀`, `c_t` below), the denominator exponents (`c_{D,1}`, `c_{D,2}`), the
  sandwich exponent `e_p = ⌈c_S·f·k²·log_p a⌉` and the exceptional fraction of the second local theorem
  (`κ = min(1, c_κ·#tops·r²·k·x^{−26})`): `cκ₁`, `cκ₂`, `ct`, `cD₁`, `cD₂`, `cS`, `cκ`;
* the error exponents of the divisibility theorem: `cE = 10`, `cE' = 3`, `cE'' = 12`, the least values it allows
  (`c_E ≥ 10`, `c_E′ ≥ 3`, `c_E″ ≥ 12`).

**Provisional values.** The values of `cLa`, `cρ`, `cN`, `cκ₁`, `cκ₂`, `ct`, `cD₁`, `cD₂`, `cS` and `cκ` are fixed by
the local theory, which is not written yet; they are set to `100` here, and the local theorems will replace them.
Outside the served gain every constant may be any absolute number (the budget is about `x^{3/2}` larger than the
per-term allowance), and the band and `W_b` depend on `cLa`, `cρ`, `cN` only through a factor that the losses absorb.

**Choices.** The numerals are natural numbers, cast where they are used; the package is a structure, so that a
statement can be made for any package meeting the lower bounds its proof needs.
-/

namespace ZetaBalance

/-- **The constant package of the gain**: the absolute numerals of its local exponents (module docstring). -/
structure GainConsts where
  /-- `c_Pr`, the penalty's constant at `p ≥ p₀`. -/
  cPr : ℕ
  /-- `c_{dl,1}`, the slack's constant at `n_p·N_m²·log_p(2a)`. -/
  cdl₁ : ℕ
  /-- `c_{dl,2}`, the slack's constant at `#tops·log_p(2a)²`. -/
  cdl₂ : ℕ
  /-- `c_La`, the constant of the loss factor `La = c_La·N₁²·log a`. -/
  cLa : ℕ
  /-- `c_ρ`, a constant of the band `ρ_B`. -/
  cρ : ℕ
  /-- `c_N`, a constant of the band `ρ_B`. -/
  cN : ℕ
  /-- `c_{κ,1}`, the depth's constant at `#tops·N₁·(a/p² + La·a/(pk))`. -/
  cκ₁ : ℕ
  /-- `c_{κ,2}`, the depth's constant at `#tops·(Q_p·c_dep + k·Q_p + k·log_p a + c₀)`. -/
  cκ₂ : ℕ
  /-- `c_t`, the depth's constant at `p < p₀`. -/
  ct : ℕ
  /-- `c_{D,1}`, the denominator exponent's constant at `p ≥ p₀`. -/
  cD₁ : ℕ
  /-- `c_{D,2}`, the denominator exponent's constant at `p < p₀`. -/
  cD₂ : ℕ
  /-- `c_S`, the sandwich exponent's constant. -/
  cS : ℕ
  /-- `c_κ`, the exceptional fraction's constant in the second local theorem. -/
  cκ : ℕ
  /-- `c_E`, the error constant at `g₀, g₁`. -/
  cE : ℕ
  /-- `c_E′`, the error constant at the inert primes with `h_p = 1`. -/
  cE' : ℕ
  /-- `c_E″`, the error constant at the other inert and signal primes. -/
  cE'' : ℕ

/-- **The package `Kg`** that the design and the gain read: the archive's `cPr = 1`, `cdl₁ = 5`, `cdl₂ = 4`, the least
error constants `cE = 10`, `cE' = 3`, `cE'' = 12`, and the provisional value `100` for the constants of the local
theory (module docstring). -/
def Kg : GainConsts where
  cPr := 1
  cdl₁ := 5
  cdl₂ := 4
  cLa := 100
  cρ := 100
  cN := 100
  cκ₁ := 100
  cκ₂ := 100
  ct := 100
  cD₁ := 100
  cD₂ := 100
  cS := 100
  cκ := 100
  cE := 10
  cE' := 3
  cE'' := 12

end ZetaBalance
