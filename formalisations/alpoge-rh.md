# The Riemann hypothesis: L. Alpöge's proof, rebuilt

## Source

- L. Alpöge, with Claude: a statement of 20 November 2026, <https://alpo.ge/remark.pdf>.
- The Lean archive it links, in 14 parts at `https://alpo.ge/lean.tar.gz.part01` to `part14`, with SHA-256
  `9631b4f0…49c7fc` once joined (`tools/rh/README.md`).

The archive proves the Riemann hypothesis for `ζ` and for every Dirichlet `L`-function. On its own pins, Lean's
kernel accepts it, and its main theorems use only `propext`, `Classical.choice` and `Quot.sound`. It carries no
licence, so nothing of it is in this repository.

## The library's proof, so far

The library is rebuilding the proof from the top, written fresh from the mathematics, in its own style and on its own
Lean and Mathlib (`docs/rh-rebuild.md`). Two steps are done.

- **The top.** `HalfPlaneGRH.rhAndGRH_of_zeroFreeRightOf`: if no primitive Dirichlet `L`-function vanishes on
  `Re s > 1/2`, the Riemann hypothesis holds for `ζ` (Mathlib's `RiemannHypothesis`) and every zero of every
  `L(s, χ)` in the critical strip lies on the line. `HalfPlaneGRH.zeroFreeRightOf_half_iff` is the converse, so this
  step loses nothing.
- **Landau's theorem on windows.** `LandauWindow.re_le_of_windows`: let a real function `g` of exponential growth have
  a Laplace transform that continues to `Re s > 0` with simple poles, at an isolated set left of `Re s = 1`, of
  positive residue at the real ones. If `g ≤ C e^{θu}` on windows `[U, λU]` for arbitrarily large `U`, no pole lies
  right of `θ`. The proof compares Taylor coefficients at a point of the line `Re s = σ` whose nearest pole is
  unique.
- **For Dirichlet characters.** `WindowGRH.Family.zeroFree_of_windows`: for a finite family of characters with
  positive weights, a bound `G(x) ≤ C x^θ` on windows `[Y, Y^λ]` keeps every member's `L`-function free of zeros right
  of `θ`. Here `G` is the weighted sum of the real parts of the errors of the ramp sums
  `Σ_{n ≤ x} Λ(n)χ(n)(x/n − 1)`.
- **The theorem.** `WindowGRH.rhAndGRH_of_windowBound`: the Riemann hypothesis for `ζ` and every Dirichlet
  `L`-function, from `WindowGRH.WindowBound`.

## How the statements differ from the archive's

- **The frontier is weaker.** `WindowBound` is the bound for the cyclic family of each primitive character, the
  archive's `Level.cyc` with its `Gm`. It allows any window ratio `λ > 1` and any constant `C`, where the archive's
  argument delivers `λ = 3/2` and `C = 1`.
- **More general.** Landau's theorem on windows is proved for any family with positive weights, and abstractly for
  Laplace transforms with simple poles.
- **Less input.** No symmetry of `L(s, χ)` under conjugation is used: real parts are taken in the transform.

## How it was formalised

The steps were written from the mathematics. Parts were written by helpers given only the statements and Mathlib.

- `WindowKernel`: the kernel `uᵏe^{−bu}/k!`, Chernoff's bound and the choice of `k` for a window.
- `WindowPole`: Taylor coefficients of Laplace transforms as moments (from `LandauLaplace`), Cauchy's estimate, and
  the coefficients near a simple pole.
- `WindowNearest`: the geometry of the nearest pole.
- `RampLaplace`: the transforms of the ramp sums.

`WindowGRH` treats `(s − 1)ζ(s)` and `L(s, χ)` alike, through `−F'/F(s) + s·F'/F(1)` over `s(s − 1)`. Mathlib's
`dslope` continues this across `s = 1`, and Mathlib's limit `ζ(s) − 1/(s − 1) → γ` gives the constant.

## Conditional results

| Result | Hypothesis | Lean |
|---|---|---|
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function | `WindowGRH.WindowBound`: for every primitive `χ` and `θ > 1/2`, the weighted error of the ramp sums of the cyclic family of `χ` is at most `C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large | `WindowGRH.rhAndGRH_of_windowBound` |
