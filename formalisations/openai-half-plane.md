# The zero-free half-plane for Dirichlet L-functions (OpenAI, 2026)

**Lean:** `Eis.LFunction_ne_zero_of_re_gt` (`lib/core/DirichletCharHalfPlane.lean`). For every modulus `q ≥ 1`,
every Dirichlet character `χ` mod `q` and every `s` with `Re s > 11/12`, `L(s, χ) ≠ 0`, except that the trivial
character's L-function has its pole at `s = 1`:

```lean
theorem LFunction_ne_zero_of_re_gt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 11 / 12 < s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) : LFunction χ s ≠ 0
```

`LFunction` is Mathlib's `DirichletCharacter.LFunction`. The theorem depends on `propext`, `Classical.choice` and
`Quot.sound` only (`lib/check/Check.lean`).

## Attribution

The result and the route to it are OpenAI's. Their release, `github.com/openai/math`, entry 003 (read at commit
`adc7f12` on 2026-10-07), contains:

- the preprint "The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8", dated 30 September 2026. It states
  that every Dirichlet L-function, ζ included, and every finite-order Hecke L-function over `ℚ(√−3)`, has no zero in
  `Re s > 7/8`, the principal pole excepted;
- a companion preprint dated 5 October 2026 and written with human assistance
  (`preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex`). It proves `Re s > 11/12` by a different
  route;
- a Lean formalisation, including the theorems
  `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` and `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`,
  stated against Mathlib's objects. Its import closure was rebuilt independently on Lean v4.34.1 with the release's
  Mathlib (`d13f23b`): both theorems depend on `[propext, Classical.choice, Quot.sound]` only.

That check, made on 2026-10-07, covered the release's statements, a static scan of its Lean, and the rebuild. It did
not read the release's proofs in full.

Nothing in this library claims the half-plane, or the route to it, as its own.

## What the formalisation here is

The library derives the half-plane on its own toolchain (Lean v4.35.0-rc3, Mathlib `0f64d30a`), following the
companion preprint's route. No file of the release is imported or vendored. The route has five steps:

1. Power savings for the smoothed Möbius sums of `ζ_{ℚ(√−3)}` give the half-plane.
2. The target is embedded in a sextic-twisted family `A_u`, with `A_{p⁶} ≈ A_1` for `≍ Y/log Y` primes `p`, so a mean
   square over the family bounds it.
3. Poisson summation in `u` and the Gauss–Jacobi identities turn `μ` times sextic Gauss sums into cubic Gauss sums.
4. Kubota's cubic theta function supplies the transformation. Its tools are Patterson's coefficient formula, the
   Dunn–Radziwiłł cusp expansions, and the quadratic large sieve over `ℤ[ω]`, which bounds the dual mean square.
5. Möbius inversion removes the cube factors, and the exponent is `11/12`.

The library proves the results from the literature that the route uses. Two have notes of their own:
[cubic-theta.md](cubic-theta.md), on Kubota's cubic theta function and Patterson's coefficients in Dunn and
Radziwiłł's form, and [quadratic-large-sieve.md](quadratic-large-sieve.md), on Heath-Brown's and Goldmakher and
Louvel's quadratic large sieve. The classical tools, among them cubic and sextic reciprocity in `ℤ[ω]`, are listed in
[README.md](README.md) under its standard results.

## Differences from the release

- **The exponent.** The library proves `Re s > 11/12`, the companion preprint's exponent. The main preprint's
  `Re s > 7/8`, which the release's Lean proves for every Dirichlet character, is not formalised here. Every result of
  this library that uses the half-plane uses it at `11/12`.
- **The route.** It is the companion preprint's (above), not the main preprint's.
- **A derivation, not an import.** The library's proof is a new formalisation of that route, on a different Lean and
  Mathlib from the release's.
- **The characters, in order.** The chain first gives `ζ(s)` and `L(s, χ₋₃)`
  (`Eis.ne_zero_of_re_gt_eleven_twelfths`). It then covers:
  - the real characters, through the family's own members (`Eis.RealChar.LFunction_ne_zero_of_isQuadratic`);
  - the characters of order dividing `6` (`Eis.LFunction_ne_zero_of_pow_six`);
  - every other Dirichlet character (`Eis.LFunction_ne_zero_of_sq_ne_one`), through the family twisted by `ν_χ`
    modulo `4q`, where `ν_χ(pgen 𝔞 mod 4q) = χ(N𝔞)` for every ideal `𝔞` of norm prime to `6` (`nuChi_pgen`). For
    this step the library generalises the chain to every modulus `m` with `4 ∣ m` and the theta step to every
    modulus, and twists the family by a character modulo `m`. The twisted family's member `1` gives
    `L(s, χ)L(s, χχ₋₃) ≠ 0` at level `3q`, and Mathlib's `LFunction_changeLevel` returns to `L(s, χ)`.
- **The exceptional pole.** The library's hypothesis `χ ≠ 1 ∨ s ≠ 1` is the release's `¬ (χ = 1 ∧ s = 1)`, by De
  Morgan's law.
- **Not covered.** The release's Hecke L-functions over `ℚ(√−3)` at `7/8` are not formalised here, and neither are
  its preprints' later applications.

## Where the Linnik paper uses it

The Type II estimate of the sieve route (`SieveRoute.TypeIIAt`) holds over all non-principal characters mod `q`. It
needs every character's prime sums to be small, not only most of them. Its proof sorts the characters into bins by the
real parts of their zeros. At the top bin, `SieveTypeII.bin_rect` uses the half-plane: no zero of `L(·, χ)` lies in
`Re s > 11/12`. The paper's exponent `899/400` therefore depends on this result. The paper states the dependence, and
compares what its method gives with what the half-plane and the density estimate give without it.
