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
- **For `ζ` alone.** `WindowGRH.riemannHypothesis_of_zetaWindowBound`: Mathlib's `RiemannHypothesis` follows from a
  statement about `Λ` alone, `WindowGRH.ZetaWindowBound`. For every `θ > 1/2`, on windows `[Y, Y^λ]` with `Y`
  arbitrarily large, `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ C x^θ`.

- **The balance for `ζ`** (step 3). `ZetaBalance.riemannHypothesis_of_zetaBalanceBound`: the Riemann hypothesis
  follows from `ZetaBalance.ZetaBalanceBound`, a bound on sums over prime powers inert in an imaginary quadratic
  field. Two pieces make it up.
  - **The balance identity** (Lemma B), `ZetaBalance.Setting.balance`. Take primes `q ≡ 3 (mod 4)` and `d` with
    `(2/d) = (q/d) = 1`, and let `A = (ℤ/2^{e+2})ˣ/{±1}` and `Φ = {±1} × A`. Weights `W : Φ → (0, ∞)` give a ramp sum
    over the prime powers inert in `ℚ(√−d)`, in the classes `ρ_t(n) = ((−n/q), [n]_A·t)`. That sum, less its main term,
    is an exact combination of the ramp errors `g_χ` of the characters `χ_d^α χ_q^β ξ`, with `ξ` a character of `A`.
  - **Theorem Z**, `ZetaBalance.BalanceData.zeta_le`. Average the identity over the translates `u ∈ A`, keeping only
    the classes where the weights are near `a_t/x`. Only the characters trivial on `A` survive. So a bound on the
    averaged gap gives `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ 7x^{1/2+3ε}`. The analytic inputs are bounds on
    the errors `g_χ`, at large arguments and for three quadratic twists at `x`.

- **Lattices** (step 4). `ZetaBalance.riemannHypothesis_of_zetaLatticeBound`: the Riemann hypothesis follows from
  `ZetaBalance.ZetaLatticeBound`. At each translate there is a frame of lattices meeting the hypotheses of the frame
  inequality. Its gain over the target covers the gap (G), with small losses (Z). That frontier is satisfied by frames
  of rank one whenever the averaged gap bound holds. What is new is how the gap is paid for: by slopes of lattices,
  through the two results below.

- **The frame inequality**, `SlopeFrame.frame_inequality`. Sources `N_i` map to one target `C`. Suppose Bost's slope
  inequality holds on the images, and the images spread their ranks. Then the mean slope of the `N_i`, less the heights
  of the maps, bounds the slope of `C` from below, up to `α·HH + β·u·log(1 + HH/u)`. It is proved for abstract
  lattices of sublattices with a rank and a degree. Under it, `GramVolume` gives volumes of parallelotopes, including
  Hadamard's inequality for maps (`GramVolume.vol_comp_le`).
- **Euclidean lattices satisfy its axioms.** The saturated sublattices of a discrete subgroup of a Euclidean space
  form such a lattice, with `deg = −log covol`. Bost's slope inequality holds on images (`EuclidLattice.bost`): a map
  of norm at most `e^h` lowers minimal slopes by at most `h`. Closure under sums holds (`EuclidLattice.supClosed`),
  because the covolume is supermodular. So Euclidean lattices and maps between them form frames
  (`EuclidLattice.frame`).

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
`dslope` continues this across `s = 1`. For `ζ`, the function is Mathlib's `riemannZeta₁`, whose
`deriv_riemannZeta₁_one` gives the constant `γ`. That a nontrivial zero lies in the strip is the library's
`WeilTest.IsNontrivialZero.mem_strip`.

## Conditional results

| Result | Hypothesis | Lean |
|---|---|---|
| The Riemann hypothesis for `ζ` and for every Dirichlet `L`-function | `WindowGRH.WindowBound`: for every primitive `χ` and `θ > 1/2`, the weighted error of the ramp sums of the cyclic family of `χ` is at most `C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large | `WindowGRH.rhAndGRH_of_windowBound` |
| The Riemann hypothesis | `WindowGRH.ZetaWindowBound`: for every `θ > 1/2`, `Σ_{n≤x} Λ(n)(x/n − 1) − x log x + (1 + γ)x ≤ C x^θ` on windows `[Y, Y^λ]` with `Y` arbitrarily large | `WindowGRH.riemannHypothesis_of_zetaWindowBound` |
| The Riemann hypothesis | `ZetaBalance.ZetaLatticeBound`: for every `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has lattice data (`ZetaBalance.LatticeData x ε`): balance inputs and, at each translate, a frame meeting the hypotheses of the frame inequality, whose gain covers the inert-prime gap (G) with small losses (Z) | `ZetaBalance.riemannHypothesis_of_zetaLatticeBound` |
| The Riemann hypothesis | `ZetaBalance.ZetaBalanceBound`: for every `ε > 0`, on windows `[Y, Y^λ]` with `Y` arbitrarily large, every `x` has balance data (`ZetaBalance.BalanceData x ε`). That is: weights whose inert-prime gap, averaged over translates, is at most `x^ε Σ_t a_t`, with `m ≥ x^{1/2−ε}` words, thick classes of density at least `x^{−ε}`, the errors at most `θy` beyond the thin scales, and three quadratic twists at most `x^{1/2+ε}` at `x` | `ZetaBalance.riemannHypothesis_of_zetaBalanceBound` |
