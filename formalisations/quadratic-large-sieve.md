# The quadratic large sieve over `ℤ[ω]`

**Lean:** `Eis.quadLargeSieve` (`lib/core/EisensteinQuadSieveFinal.lean`) proves the display `Eis.QuadLargeSieve`
(`lib/core/EisensteinPrepared.lean`):

```lean
def QuadLargeSieve : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ H U : ℝ, 1 ≤ H → 1 ≤ U → ∀ (Ks Ns : Finset (𝓞 K)) (β : 𝓞 K → ℂ),
    (∀ k ∈ Ks, Primary k ∧ Squarefree (span {k}) ∧ (absNorm (span {k})).Coprime 6 ∧
      (absNorm (span {k}) : ℝ) ≤ H) →
    (∀ n ∈ Ns, Primary n ∧ Squarefree (span {n}) ∧ U / 2 ≤ (absNorm (span {n}) : ℝ) ∧
      (absNorm (span {n}) : ℝ) ≤ 2 * U) →
    ∑ k ∈ Ks, ‖∑ n ∈ Ns, β n * sym6 n (span {k}) ^ 3‖ ^ 2 ≤
      C * (H * U) ^ ε * (H + U) * ∑ n ∈ Ns, ‖β n‖ ^ 2
```

Here `K = ℚ(ω)`, `𝓞 K = ℤ[ω]`, an element is primary when it is `≡ 1 (mod 3)`, and `sym6 n (k)³ = (n/k)₂` is the
quadratic residue symbol, the cube of the sextic one. In words: for every `ε > 0` there is `C` such that, for
`H, U ≥ 1`, every finite set of primary squarefree moduli `k` with `N(k) ≤ H` prime to `6`, every finite set of
primary squarefree `n` with `U/2 ≤ N(n) ≤ 2U`, and all coefficients `β_n`,

`Σ_k |Σ_n β_n(n/k)₂|² ≤ C(HU)^ε(H + U)Σ_n |β_n|²`.

The theorem is in the proof of `Linnik22240R.linnik_22240r`, whose axioms are `propext`, `Classical.choice` and
`Quot.sound` (`lib/check/Check.lean`), so it depends on those only.

## Source

- D. R. Heath-Brown, "A mean value estimate for real character sums", Acta Arith. 72 (1995), 235–275: the quadratic
  large sieve over `ℤ`, for real characters to squarefree moduli. Sections 2–8 (pp. 240–265) were read: the plan of
  attack, the preliminary lemmas and the proof.
- L. Goldmakher and B. Louvel, "A quadratic large sieve inequality over number fields", Math. Proc. Cambridge
  Philos. Soc. 154 (2013), 193–212 (arXiv:1112.1642): its extension to number fields, their Theorem 1.1. Version 2
  of the arXiv paper was read in full, from its LaTeX source.

The OpenAI companion preprint ([openai-half-plane.md](openai-half-plane.md)) uses the estimate as its Lemma 6.5, and
says of it: "This is Goldmakher and Louvel's quadratic large sieve [GL, Theorem 1.1], after fixing the product of the
prime factors of n lying in S, and finitely many ray classes." The display above is that lemma.

Goldmakher and Louvel's argument, in their words as read: their `(E_α)` is "B_1(M,N)≪(MN)^ε(M+N^α), for all M,N≥1 and
ε>0"; their Lemma 4.2, "The bound (E_2) holds"; and their Theorem 4.1, "For every α≥1, the upper bound (E_α) implies
the upper bound (E_{2−1/α})". From `α = 2` the exponents `(j + 1)/j` tend to `1`. They defer three steps to
Heath-Brown: their Lemma 4.4 to his Lemma 9, their Lemma 7.1 to his Lemma 10, and their Lemma 3.3 to his Lemma 13.

Nothing in this library claims the estimate, or its proof, as its own.

## What the formalisation here is

The library's proof follows Goldmakher and Louvel's argument over `ℤ[ω]`, with Heath-Brown's lemmas where they defer
to them, except his Lemma 9 (see the differences below).

- **The norm** (`EisensteinQuadSieveNorm`). `Eis.QBound M N Δ` says `Σ_k |Σ_n a(n)(n/k)₂|² ≤ ΔΣ_n |a(n)|²` over
  admissible rows `N(k) ≤ M` and columns `N(n) ≤ N`. Its symmetry (Heath-Brown's Lemma 1, `Eis.QBound.symm`) comes
  from quadratic reciprocity for admissible elements (`Eis.sym2_recip_adm`) and the duality principle (`Eis.duality`).
  `Eis.QExp α` is `(E_α)`, and `Eis.quadLargeSieve_of_exp` derives the display from `(E_1)`.
- **The base case `(E_2)`** (`Eis.qExp_two`, `EisensteinQuadSieveBase`).
- **The recursive estimate** (`EisensteinQuadSieveSep`, `EisensteinQuadSieveLemma14`, `EisensteinQuadSieveLattice`,
  `EisensteinQuadSieveSquares`, `EisensteinQuadSieveSigma3`, `EisensteinQuadSieveSigma4`, `EisensteinQuadSieveErrors`,
  `EisensteinQuadSieveGamma`, `EisensteinQuadSieveMain`, `EisensteinQuadSieveMainBound`, `EisensteinQuadSieveGcdPart`,
  `EisensteinQuadSieveRecursion`, `EisensteinQuadSieveCor`). Heath-Brown's Lemmas 2 and 10, his sums `Σ_3` and `Σ_4`
  by Poisson summation over `ℤ[ω]`, a planar form of his Lemma 14, the cancellation of the two main terms, and the
  bounds of the errors at smaller scales.
- **The iteration** (`Eis.qExp_improve`, `Eis.qExp_one`): `(E_α)` gives `(E_{2−1/α})`, and from `(E_2)` the library
  reaches `(E_1)`.

The tools over `ℤ[ω]` are the library's: Poisson summation with twists and with excluded primes
(`EisensteinPoisson`, `EisensteinPoissonExcl`), quadratic Gauss sums and quadratic reciprocity
(`EisensteinQuadGauss`, `EisensteinQuadRecip`, `EisensteinQuadSupplement`), the separation of variables by Mellin
transforms (`MellinSep`), and a radial majorant with compactly supported Fourier transform (`PlaneMajorant`).

## Differences from the source

- **One field.** The estimate is proved over `ℚ(ω)` only, not over a general number field, in the form of the
  companion preprint's Lemma 6.5: primary squarefree moduli prime to `6`, and primary squarefree arguments in a shell
  `U/2 ≤ N(n) ≤ 2U`.
- **Balls, not dyadic ranges.** The norm runs over all rows of norm at most `M` and columns of norm at most `N`, so it
  is monotone by inclusion (`Eis.QBound.mono`). This replaces Heath-Brown's Lemma 9, which averages over the primes
  `p` with `2K/3 < p < 4K/3` and needs their number, of exact order `K/log K`. Over `ℤ[ω]` that would need a count of
  prime ideals in such a range.

## Where the Linnik paper uses it

Through the zero-free half-plane ([openai-half-plane.md](openai-half-plane.md)). The companion preprint's Lemma 6.6
bounds the prepared sums in mean square with it (`EisensteinPrepared`, `EisensteinThetaAssembly`), and the dual mean
square of its route follows. With the theta transformation ([cubic-theta.md](cubic-theta.md)) it gives the
half-plane for `ζ` and `L(s, χ₋₃)` (`Eis.ne_zero_of_thetaRows`).
