# Mean values of Dirichlet polynomials over the characters mod `q`

**Lean:** `LinnikHybrid.mean_value_chars` and `LinnikHybrid.large_values_chars` (`lib/pnt/LinnikHybrid.lean`), with
Gallagher's lemma `DirMean.gallagher_one` (`lib/core/DirMean.lean`):

```lean
theorem mean_value_chars {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    (q : ℕ) [NeZero q] {a b : ℝ} (hab : a ≤ b) :
    ∑ χ : DirichletCharacter ℂ q, ∫ t in a..b, ‖dp S (fun j => c j * χ j) t‖ ^ 2
      ≤ (q * (b - a) + 8 * P * (1 + Real.log P)) * ∑ j ∈ S, ‖c j‖ ^ 2

theorem large_values_chars {P : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Ioc P (2 * P)) (c : ℕ → ℂ)
    (q : ℕ) [NeZero q] {lo hi : ℝ} (hab : lo ≤ hi) (Rs : Finset (DirichletCharacter ℂ q))
    (x : DirichletCharacter ℂ q → ℝ) (hR : ∀ χ ∈ Rs, lo + 1 / 2 ≤ x χ ∧ x χ ≤ hi - 1 / 2) :
    ∑ χ ∈ Rs, ‖dp S (fun j => c j * χ j) (x χ)‖ ^ 2
      ≤ (q * (hi - lo) + 8 * P * (1 + Real.log P)) * (2 + Real.log (2 * P) ^ 2) * ∑ j ∈ S, ‖c j‖ ^ 2
```

Here `dp S c t = Σ_{j∈S} c_j j^{−it}` (`DirMean.dp`). In words, let `D_χ(t) = Σ_{j∈S} c_jχ(j)j^{−it}` with
`S ⊆ (P, 2P]`.

- Summed over all the characters mod `q`, `Σ_χ ∫_a^b |D_χ(t)|² dt ≤ (q(b − a) + 8P(1 + log P))Σ|c_j|²`.
- At one point `x_χ` for each character of a set `R`, all in `[lo + 1/2, hi − 1/2]` and with nothing relating the
  points of different characters,
  `Σ_{χ∈R} |D_χ(x_χ)|² ≤ (q(hi − lo) + 8P(1 + log P))(2 + log²(2P))Σ|c_j|²`.

`LinnikHybrid.large_values_chars_off` is the second with the weights `j^{−β_χ}`, `σ ≤ β_χ ≤ σ + 1/2`, at the cost of a
factor `e`, and with `Σ|c_j|²j^{−2σ}` on the right. These theorems are in the proof of `Linnik22000E.linnik_22000e`,
whose axioms are `propext`, `Classical.choice` and `Quot.sound` (`lib/check/Check.lean`), so they depend on those
only.

## Source

Both estimates are classical. Nothing in this library claims them as its own.

- **The mean value theorem for Dirichlet polynomials.** For one polynomial, `∫_a^b |Σ_n c_n n^{−it}|² dt` is
  `(b − a)Σ|c_n|²` up to an error controlled by the spacing of the frequencies `log n`. H. L. Montgomery and
  R. C. Vaughan proved the sharp form, with an error `O(Σ n|c_n|²)` ("Hilbert's inequality", J. London Math. Soc.
  (2) 8 (1974), 73–82). Over the characters to one modulus, their orthogonality turns it into the first estimate
  above.
- **Gallagher's lemma.** `DirMean.gallagher_one` bounds a value of a function by its mean square and that of its
  derivative on an interval about the point: `|f(x)|² ≤ ∫_{x−1/2}^{x+1/2}(|f|² + 2|f||f′|)`. P. X. Gallagher proved
  the large sieve with an inequality of this kind ("The large sieve", Mathematika 14 (1967), 14–20). With the mean
  value theorem it gives the second estimate. Gallagher's "A large sieve density estimate near σ = 1" (Invent. Math.
  11 (1970), 329–339) contains the hybrid large sieve over the moduli, the characters and the height.

None of these papers was read for the formalisation. The library's proofs were written from the standard arguments.

## What the formalisation here is

- `LinnikHybrid.mean_value_row`: for one polynomial with `S ⊆ (P, 2P]`,
  `∫_a^b |Σ_{j∈S} c_j j^{−it}|² dt ≤ (b − a + 4PK)Σ|c_j|²` when every row sum `Σ_{j′∈S, j′≠j} 1/|j − j′|` is at most
  `K`. The diagonal gives `(b − a)Σ|c_j|²`. Off the diagonal, `|∫_a^b e^{iλt} dt| ≤ 2/|λ|` and
  `|log j − log j′| ≥ |j − j′|/(2P)`.
- `LinnikHybrid.mean_value_chars`: `D_χ` splits over the residue classes mod `q`, the orthogonality of the characters
  (Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`) leaves `φ(q)` times one class at a time, and in one class
  the row sums are at most `(2/q)(1 + log P)`.
- `DirMean.gallagher_one`, then `LinnikHybrid.large_values_chars`: Gallagher's lemma for `D_χ` on the unit interval
  about its point, then the mean value over `[lo, hi]`. The derivative of `D_χ` is a Dirichlet polynomial of the same
  kind, with the coefficients `−ic_j log j`.

## Differences from the source

- **The constant.** The library proves the weak form, with `8P(1 + log P)` where Montgomery and Vaughan have `O(P)`.
  The loss is a power of `log P`, which every use here absorbs.
- **One modulus.** The sums run over the characters to one modulus `q`, not over the primitive characters to all
  moduli up to `Q`.
- **Points per character.** The point form takes one point for each character, with no spacing condition between the
  points of different characters. Distinct characters are already orthogonal.

## Where the Linnik paper uses it

Through the density estimates of [ingham-density.md](ingham-density.md) and [huxley-density.md](huxley-density.md).
Both count the characters whose mollified Dirichlet polynomial is large at a zero, their polynomial class, with
`large_values_chars_off`. The Type II estimate itself uses only the orthogonality of the characters at one height,
`Σ_χ |Σ_{j∈S} c_jχ(j)j^{−it}|² ≤ (P + q)Σ|c_j|²` for `S ⊆ (P, 2P]` (`SieveTypeII.sum_chars_dp_sq_le`, from
`LinnikHybrid.sum_chars_norm_sq_le`), which is elementary.
