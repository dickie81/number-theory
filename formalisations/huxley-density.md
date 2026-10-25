# Huxley's zero-density estimate over the characters mod `q`

**Lean:** `LinnikHuxStep.charDensity_gen` (`lib/pnt/LinnikHuxStep.lean`), the estimate for a step of parameters
`Pa : Par` that satisfy `Par.Good`:

```lean
theorem charDensity_gen (Pa : Par) (G : Pa.Good) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), Pa.lo ≤ σ → σ ≤ Pa.hi → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ (Pa.A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ)
```

In words: for every `q ≥ 1`, `σ` in the step's range `[lo, hi]` and `T ≥ 2`, at most `C(qT)^{A(1−σ)}(log qT)^{10}`
characters mod `q` have an `L`-function with a zero in `Re s ≥ σ`, `|Im s| ≤ T`. `Par.Good` lists what the argument
needs of the parameters. Among them are `3/4 ≤ lo`, `hi ≤ 11/12`, and four inequalities between the exponents that
bound `A` below on `[lo, hi]`. `LFunction` is Mathlib's `DirichletCharacter.LFunction`.

The Linnik proof uses two kinds of instance:

- `LinnikStairs7.charDensity_hx7_5` to `charDensity_hx7_19`, the last fifteen of twenty equal steps `[σ₁, σ₂]` of
  `[16/21, 5/6]` (`LinnikStairs7` has `charDensity_hx7_0` … `charDensity_hx7_19`; the first five are replaced in the
  proof of `Linnik22325R.linnik_22325r` by the steps of `LinnikCGLSteps`, see
  [chen-gupta-li-density.md](chen-gupta-li-density.md)). Each has the exponent `3/(3σ₁ − 1) + 1/2000`: Huxley's
  exponent at the step's left end, plus `1/2000`. The first step is `[16/21, 643/840]` with the exponent `14003/6000`,
  which is `7/3 + 1/2000`.
- `LinnikStep.charDensity_step`, the exponent `101/50` on `5/6 ≤ σ ≤ 1`, by the same argument at fixed parameters.
  (`LinnikHuxStep.charDensity_step'` derives it again on `[5/6, 11/12]` from `charDensity_gen`.) Above `11/12` it uses
  the zero-free half-plane ([openai-half-plane.md](openai-half-plane.md)): no non-principal character is counted
  there.

These theorems are in the proof of `Linnik22325R.linnik_22325r`, whose axioms are `propext`, `Classical.choice` and
`Quot.sound` (`lib/check/Check.lean`), so they depend on those only. `charDensity_gen` and the twenty steps do not use
the half-plane: `Eis.LFunction_ne_zero_of_re_gt` is not among the declarations their proofs depend on.

## Source

M. N. Huxley proved the large-values estimate for Dirichlet polynomials that gives the density exponent `12/5` for the
zeros of `ζ` ("On the difference between consecutive primes", Invent. Math. 15 (1972), 164–170). That paper was not
read for the formalisation.

The form over Dirichlet characters is in his "Large values of Dirichlet polynomials, III" (Acta Arith. 26 (1975),
435–444), which was read (pp. 435–439 and 444). Its (1.1) is
`Σ_{q≤Q, q≡0 (mod q₀)} Σ*_{χ mod q} N(σ, T, χ) ≪ (Q²T/q₀)^{12(1−σ)/5+ε}`, and p. 435 adds: "(Jutila actually treats
all characters to a fixed modulus, which is essentially the special case Q = q₀, where q₀ is a divisor of the given
modulus.)"

- For `σ > 3/4` the estimate comes from his Theorem 1 (p. 438): "R ≪ GV^{−2}N log²l + G³V^{−6}NDΔ₂^{1/2}Δ₃l^{11}
  provided that (2.21) V > c₁G^{1/2}N^{1/4}l², where c₁ is an absolute constant", with `D = Q²T/q₀` (2.2).
- His (2.23) reads `Σ_{q≤Q} Σ*_{χ mod q} N(σ,T,χ) ≪ max{D^{3(1−σ)/(3σ−1)+ε}, D^{2(1−σ)+ε}}` (read on the page
  image). The exponent is `3/(3σ − 1)`, capped below at `2`.
- He builds on "Large values of Dirichlet polynomials" (Acta Arith. 24 (1973), 329–346; its contents page and
  pp. 329–331 were read), whose p. 329 says: "The technique used is to feed the Halász inequality (Montgomery's basic
  tool) back into itself by means of an approximate functional equation for L-functions."

Nothing in this library claims the estimate, or the large-values estimate behind it, as its own.

## What the formalisation here is

The library's proof was written from the method as these pages describe it. It does not follow Huxley's text step by
step: his Theorem 1 and his Lemma 2 are not formalised as stated.

- **The Halász–Montgomery inequality with a smooth weight** (`LinnikReflect.hm_duality_W`, in
  `lib/pnt/LinnikWeighted.lean`; see [halasz-montgomery.md](halasz-montgomery.md)). Its off-diagonal terms are sums
  `H_U(ψ, z) = Σ_n ψ(n)n^{−z}(e^{−n/U} − e^{−2n/U})`.
- **The reflection** (`LinnikReflect.reflect_aux`, in `lib/pnt/LinnikReflect.lean`, applied in
  `LinnikReflect.norm_hTerm_le_reflect`). Each `H_U(ψ, z)` is an integral of `L(·, ψ)` along a vertical line, which
  the functional equation of the primitive character inducing `ψ` turns into a short dual sum and a tail. This step
  plays the part of the approximate functional equation in Huxley's description.
- **The large-values estimate** (`LinnikReflect.huxley_large_values`, in `lib/pnt/LinnikLargeValues.lean`). At one
  point per character, the number of characters at which a Dirichlet polynomial of length `N` and mean square `G` is
  at least `V` has the shape `(GN/V² + G³NqT/V⁶)(qNT)^ε`, Huxley's in the `q`-aspect.
- **The density estimate** (`LinnikTwelve`, `LinnikHuxStep`). Zero detection as in
  [ingham-density.md](ingham-density.md), at other parameters. The mollified polynomial of each character is raised to
  a power `m` so that its length reaches a target `Q^a` (`LinnikPower.pv_pow`), the characters are sorted into bins by
  the real parts of their zeros, and the large-values estimate counts each bin. The integral class is counted with
  the hybrid fourth moment ([hybrid-fourth-moment.md](hybrid-fourth-moment.md)).

## Differences from the source

- **Characters, not zeros.** As in [ingham-density.md](ingham-density.md).
- **One modulus.** Huxley's (1.1) sums over the moduli `q ≤ Q` divisible by `q₀`, and over their primitive characters.
  The Lean statements count all the characters to one modulus `q`, which by his remark on Jutila is the case `Q = q₀`.
- **A staircase above Huxley's curve.** On `[16/21, 5/6]` the exponent is constant on each of twenty steps, at
  Huxley's value at the step's left end plus `1/2000`. Huxley's exponent `3/(3σ − 1)` decreases with `σ`, so each
  step's exponent is at least Huxley's on the whole step.
- **Above `5/6`.** Huxley's (2.23) gives the exponent `2` there. The library's step gives `101/50`, which is weaker by
  `1/50`. On `σ > 11/12` it uses the zero-free half-plane, which Huxley's estimate does not need.
- **The power of the logarithm** is `(log qT)^{10}`.

## Where the Linnik paper uses it

The density curve `g7c` of the Linnik paper's Type II estimate (`SieveTypeIIU226C.counts_7c`) takes the twenty steps
`LinnikStairs7.charDensity_hx7_0` to `charDensity_hx7_19` on `[16/21, 5/6]`, and `LinnikStep.charDensity_step` from
`5/6` on.
