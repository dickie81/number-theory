# The hybrid fourth moment of Dirichlet `L`-functions

**Lean:** `LinnikFourth.fourth_moment` (`lib/pnt/LinnikFourth.lean`):

```lean
theorem fourth_moment {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (Rs : Finset (DirichletCharacter ℂ q)), (∀ χ ∈ Rs, χ ≠ 1) →
      ∀ T : ℝ, 0 ≤ T → ∀ t : DirichletCharacter ℂ q → ℝ, (∀ χ ∈ Rs, |t χ| ≤ T) →
        ∑ χ ∈ Rs, ‖LFunction χ (1 / 2 + t χ * I)‖ ^ 4 ≤ C * ((q : ℝ) * (T + 2)) ^ (1 + ε)
```

In words: for every `ε` in `(0, 1]` there is `C` such that, for every modulus `q ≥ 1`, every set `R` of non-principal
characters mod `q` and every choice of one point `|t_χ| ≤ T` for each `χ ∈ R`,
`Σ_{χ∈R} |L(1/2 + it_χ, χ)|⁴ ≤ C(q(T + 2))^{1+ε}`. `LFunction` is Mathlib's `DirichletCharacter.LFunction`. The theorem
is in the proof of `Linnik22240R.linnik_22240r`, whose axioms are `propext`, `Classical.choice` and `Quot.sound`
(`lib/check/Check.lean`), so it depends on those only.

## Source

The hybrid fourth moment is H. L. Montgomery's (*Topics in Multiplicative Number Theory*, Lecture Notes in Math. 227,
Springer, 1971). H. M. Bui and D. R. Heath-Brown state it so in the introduction of "A note on the fourth moment of
Dirichlet `L`-functions" (arXiv:0903.4008): "a result of Montgomery [2] states that Σ*_{χ (mod q)} ∫_0^T
|L(1/2+it,χ)|⁴ dt ≪ φ(q)T(log qT)⁴ for q, T ≥ 2, where Σ* indicates that the sum is restricted to the primitive
characters modulo q". Their [2] is Montgomery's book.

Montgomery's book was not read for the formalisation; Bui and Heath-Brown's statement was read in their paper's text.
The library's proof was written from the standard argument, an approximate functional equation for `L(s, χ)²` and the
hybrid large values estimate. Nothing in this library claims the estimate as its own.

## What the formalisation here is

- **An approximate functional equation for `L(s, χ)²`** (`LinnikGamma.afe`, in `lib/pnt/LinnikAFE.lean`). For a
  primitive `χ ≠ 1` mod `N` and `0 ≤ Re s ≤ 1`, `Λ(s, χ)² = J(s, χ) + ε(χ)²N^{1−2s}J(1 − s, χ⁻¹)`, where `Λ` is the
  completed `L`-function and `J(s, χ) = (1/2πi)∫_{(2)} Λ(s + w, χ)²N^w e^{w²} dw/w`. With `D = J/γ_χ²`, `γ_χ` the
  gamma factor, `|ε(χ)| = 1` and `|γ_χ(1/2 − it)| = |γ_χ(1/2 + it)|`, it gives
  `|L(1/2 + it, χ)|⁴ ≤ 2|D(1/2 + it, χ)|² + 2|D(1/2 − it, χ⁻¹)|²` (`LinnikFourth.norm_LFunction_four_le`).
- **The terms of `J`** (`LinnikFourth.afeJ_split`). `L(z, χ)² = P(z) + T(z)` with `P(z) = Σ_{n≤N₀} d(n)χ(n)n^{−z}`
  and `|T(z)| ≤ 2N₀^{3−Re z}` on `Re z ≥ 3`. The part with `P` is integrated on `Re w = ε/8` and the part with `T` on
  `Re w = 40/ε`, with no pole crossed.
- **The mean square of `P` at one point per character** (`LinnikFourth.sum_norm_Pd_sq_le`), by its dyadic blocks
  and the hybrid large values estimate `LinnikHybrid.large_values_chars_off` (see [mean-values.md](mean-values.md)).
  Cauchy–Schwarz in the line's variable against the weight then bounds `Σ_χ |D(1/2 + it_χ, χ)|²` by
  `C(N(T + 2))^{1+ε}` (`LinnikFourth.sum_norm_afeD_sq_le`), at `N₀ = ⌈(N(T + 2))^{1+ε/8}⌉`. The fourth power of
  `|L|` over the primitive characters mod `N` follows (`LinnikFourth.fourth_moment_primitive`).
- **From primitive characters to all characters** (`LinnikFourth.fourth_moment`). Each `χ ≠ 1` mod `q` is compared
  with the primitive character that induces it, modulo the conductor `N | q` (Mathlib's `LFunction_changeLevel`).
  The characters are grouped by conductor, and `Σ_{N | q} N^{1+ε} ≤ ζ(1 + ε)q^{1+ε}`.

## Differences from the source

- **Points, not an integral.** The source integrates over `0 ≤ t ≤ T`. The library takes one point `t_χ` for each
  character and sums over the characters. That is the form the zero-density arguments use: one zero for each counted
  character.
- **A power of `qT` for a power of `log qT`.** The bound is `C(q(T + 2))^{1+ε}` for every `ε > 0`, in place of
  `φ(q)T(log qT)⁴`. The loss `(qT)^ε` is absorbed wherever the estimate is used.
- **All non-principal characters.** The sum runs over any set of non-principal characters mod `q`, imprimitive ones
  included, not over the primitive characters only.

## Where the Linnik paper uses it

Through the density estimates of [ingham-density.md](ingham-density.md) and [huxley-density.md](huxley-density.md).
Both bound their integral class, the characters for which the detector's integral along `Re s = 1/2` is large, with
this estimate.
