import Zeta23.Final

/-! # The Riemann–von Mangoldt formula, in Mathlib's terms

zeta23 proves the Riemann–von Mangoldt formula for the nontrivial zeros of Mathlib's `riemannZeta`
(`Zeta23.riemannVonMangoldt_zeta`), for its zero configuration `Zeta23.zetaZeroConfig` and in its dyadic form. Here it
is restated with `Zeta23.Ncount`, which is defined from `riemannZeta` and `analyticOrderAt` alone: the nontrivial zeros
with `T < Im ρ ≤ 2T`, counted with multiplicity, number `(T/2π)(log(T/2π) + 2 log 2 − 1) + O(log T)`. The main term is
`N(2T) − N(T)` for the classical `N(T) = (T/2π) log(T/2πe)`.

* `riemann_von_mangoldt`: the formula.
-/

open Real

namespace ZeroCount

open Zeta23

/-- **The Riemann–von Mangoldt formula** (zeta23, in its dyadic form): the nontrivial zeros of `ζ` with
`T < Im ρ ≤ 2T`, counted with multiplicity, number `(T/2π)(log(T/2π) + 2 log 2 − 1) + O(log T)`. -/
theorem riemann_von_mangoldt : ∃ C T₀ : ℝ, ∀ T ≥ T₀,
    |(Ncount T (2 * T) : ℝ) - T / (2 * π) * (Real.log (T / (2 * π)) + 2 * Real.log 2 - 1)| ≤ C * Real.log T := by
  obtain ⟨C, T₀, hR⟩ := riemannVonMangoldt_zeta.main
  refine ⟨C, T₀, fun T hT => ?_⟩
  have h := hR T hT
  rw [zetaZeroConfig_N] at h
  exact h

end ZeroCount

#print axioms ZeroCount.riemann_von_mangoldt
