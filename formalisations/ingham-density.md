# Ingham's zero-density estimate over the characters mod `q`

**Lean:** `LinnikInghamC.charDensity_ingham_c` (`lib/pnt/LinnikInghamC.lean`):

```lean
theorem charDensity_ingham_c {ε c δ₀ σ₂ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hδ₀ : 0 < δ₀)
    (hσ₂ : σ₂ ≤ 11 / 12) (hexp : 4 / 3 * (1 + 2 * c) * (1 / 2 - σ₂) + 1 ≤ (2 + 4 * c) * (1 - σ₂)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 1 / 2 + δ₀ ≤ σ → σ ≤ σ₂ → 2 ≤ T →
      ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
        ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤
          C * ((q : ℝ) * T) ^ ((2 + 4 * c + 4 * ε) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ (10 : ℝ)
```

The condition `hexp` says `2 + 4c ≥ 3/(2 − σ₂)`: the exponent `2 + 4c` is at least Ingham's `3/(2 − σ)` at the right
end `σ₂ ≤ 11/12` of the range. In words: for such `c` and for `0 < ε ≤ 1` and `δ₀ > 0` there is `C` such that, for
every `q ≥ 1`, `1/2 + δ₀ ≤ σ ≤ σ₂` and `T ≥ 2`, at most `C(qT)^{(2+4c+4ε)(1−σ)}(log qT)^{10}` characters mod `q` have
an `L`-function with a zero in `Re s ≥ σ`, `|Im s| ≤ T`. `LFunction` is Mathlib's `DirichletCharacter.LFunction`.

The theorem is in the proof of `Linnik22322R.linnik_22322r`, whose axioms are `propext`, `Classical.choice` and
`Quot.sound` (`lib/check/Check.lean`), so it depends on those only. It does not use the zero-free half-plane:
`Eis.LFunction_ne_zero_of_re_gt` is not among the declarations its proof depends on.

## Source

A. E. Ingham proved `N(σ, T) ≪ T^{3(1−σ)/(2−σ)}(log T)⁵` for the zeros of `ζ` ("On the estimation of N(σ, T)", Quart.
J. Math. Oxford Ser. 11 (1940), 291–292). Chourasiya and Simonič state his result in that form in the abstract of
arXiv:2507.15184: "Ingham (1940) proved that N(σ,T) ≪ T^{3(1−σ)/(2−σ)} log^5 T".

The form over the characters mod `q` is in H. L. Montgomery's *Topics in Multiplicative Number Theory* (Lecture Notes
in Math. 227, Springer, 1971), as its Theorem 12.1. M. N. Huxley cites it so in "Large values of Dirichlet
polynomials, III" (Acta Arith. 26 (1975), 435–444), whose (1.1) is
`Σ_{q≤Q, q≡0 (mod q₀)} Σ*_{χ mod q} N(σ, T, χ) ≪ (Q²T/q₀)^{12(1−σ)/5+ε}`:

- "Theorem 12.1 of [6] contains (1.1) with 5/2 in place of 12/5 in the exponent" (p. 435);
- the range `1/2 ≤ σ ≤ 3/4` of (1.1) "follows from Theorem 12.1 of [6]" (p. 438).

His [6] is Montgomery's book. Huxley's paper was read (pp. 435–439 and 444); Ingham's paper and Montgomery's book
were not. Nothing in this library claims the estimate as its own.

## What the formalisation here is

The library's proof was written from the standard argument, not transcribed from a source. It has three parts.

- **Zero detection** (`LinnikDetect.dichotomy`). Let `χ ≠ 1` and let `ρ = β + iγ` be a zero of `L(·, χ)` with
  `1/2 < β < 1`. With the mollifier `M_X(s, χ) = Σ_{m≤X} μ(m)χ(m)m^{−s}`, either the Dirichlet polynomial
  `P_χ(ρ) = Σ_{X<j≤XN} b_jχ(j)j^{−ρ}` is at least `1/4` in absolute value, or so is an integral of
  `M_X(ρ + w, χ)L(ρ + w, χ)Γ(w + 1)Y^w/w` along `Re(ρ + w) = 1/2`. Here `b_j = e^{−j/Y}Σ_{d | j, d ≤ X} μ(d)`.
  Detecting zeros with a mollified Dirichlet polynomial is H. L. Montgomery's method ("Zeros of L-functions", Invent.
  Math. 8 (1969), 346–354), which was not read either.
- **The two classes.** The characters whose polynomial is large, at one zero each, are counted by the hybrid large
  values estimate (`LinnikDensity.class1_count`, from `LinnikHybrid.large_values_chars_off`;
  [mean-values.md](mean-values.md)). The characters whose integral is large are counted with the hybrid fourth moment
  at one point per character and the mean value of the mollifier (`LinnikIngham.class2_count_ingham`, from
  `LinnikFourth.fourth_moment`; [hybrid-fourth-moment.md](hybrid-fourth-moment.md)).
- **The parameters** (`LinnikInghamC.count_middle_c`). At `Q = q(T + 6)`, `X = ⌊Q⌋` and `Y = Q^{1+2c}`, the first
  class has at most a constant times `(log Q)^{10}Q^{(2+4c)(1−σ)}` members (`LinnikDensity.bound_class1`). The
  second has, up to a constant and a power of `log Q`, at most `Q^{(4/3)(1+2c)(1/2−σ)+1+ε/3}` members, which `hexp`
  puts below `Q^{(2+4c+4ε)(1−σ)}` (`LinnikInghamC.bound_class2_c`).

`LinnikStairs7` applies the theorem on twenty equal steps `[σ₁, σ₂]` of `[4/7, 5/7]` at `ε = 1/8000`, with
`2 + 4c = 3/(2 − σ₂)`. The exponent on each step is `3/(2 − σ₂) + 1/2000`. The first step is
`LinnikStairs7.charDensity_in7_0`, with the exponent `840199/398000` on `[4/7, 81/140]`, and the last is
`LinnikStairs7.charDensity_in7_19`.

## Differences from the source

- **Characters, not zeros.** Ingham's and Montgomery's estimates count zeros. The Lean statement counts the
  characters with a zero, which is at most that number. Counting characters lets the detector work at one zero for
  each character, which is the form the hybrid estimates of the proof take.
- **A staircase above Ingham's curve.** The exponent is constant on each step, at its largest value
  `3/(2 − σ₂)` there, plus `4ε`. Ingham's exponent `3/(2 − σ)` increases with `σ`, so each step's exponent is at least
  Ingham's on the whole step. On `[4/7, 5/7]` the Lean exponents exceed Ingham's curve by at most the step's rise in
  `3/(2 − σ)` plus `1/2000`.
- **The losses.** The bound carries `(log qT)^{10}` and, beyond the exponent `2 + 4c`, a factor `(qT)^{4ε(1−σ)}` for
  a fixed `ε > 0`. Ingham's bound for `ζ` has `(log T)⁵` and no power loss. The uses absorb both.
- **The range.** The theorem holds for `1/2 + δ₀ ≤ σ ≤ σ₂ ≤ 11/12`, and the Linnik proof uses it on `[4/7, 5/7]` only.
  Ingham's estimate holds on `1/2 ≤ σ ≤ 1`.

## Where the Linnik paper uses it

The density curve `g7c` of the Linnik paper's Type II estimate (`SieveTypeIIU226C.counts_7c`) takes the twenty steps
`LinnikStairs7.charDensity_in7_0` to `charDensity_in7_19` on `[4/7, 5/7]`.
