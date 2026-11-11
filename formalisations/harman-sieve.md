# Harman's sieve in the form used, with Brun's fundamental lemma and Buchstab's identity

**Lean:** `SieveProp6.prop6` (`lib/pnt/SieveProp6.lean`), the comparison theorem of Harman's sieve for the Linnik
problem:

```lean
theorem prop6 [Route] [RouteOK] (hII : TypeIIAt) (j J₀ : ℕ) {Λ₁ a₀ b₀ : ℝ} (hΛ₁ : 0 ≤ Λ₁) (ha₀ : 0 < a₀)
    (hab : a₀ + b₀ < (1 - w₁) * (L)) (hb₁ : (1 - w₂) * (L) < b₀)
    (hb₂ : b₀ < L - 1) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ Ω : List (Cmp j), Ω.length ≤ J₀ → (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin j → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        (∀ i, ⌈(q : ℝ) ^ a₀⌉₊ ≤ rt i) ∧ ∏ i, rt i ≤ ⌊(q : ℝ) ^ b₀⌋₊) →
      ‖∑ rt ∈ SieveStops2.RT j ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough ⌈(q : ℝ) ^ a₀⌉₊ n then 1 else 0)‖ ≤
        η * (q : ℝ) ^ L / (q.totient * Real.log q) +
          (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)
```

In words: let `L`, `w₁` and `w₂` be the parameters of a route of the Linnik paper's sieve that satisfy `RouteOK`, and
assume the route's Type II estimate (`hII`). Fix `j`, `J₀`, `Λ₁ ≥ 0`, `η > 0`, and exponents `a₀ > 0` and `b₀` with
`a₀ + b₀ < (1 − w₁)L` and `(1 − w₂)L < b₀ < L − 1`. Then there are `δ > 0` and `q₀` such that for `q ≥ q₀` and every
unit `a` mod `q` the following holds. Let the tuple `rt` run over the `j`-tuples of primes up to `2q^L` that satisfy
at most `J₀` comparisons `Ω`, where `Ω` forces every prime to be at least `z₀ = ⌈q^{a₀}⌉` and the product `r` to be at
most `q^{b₀}`. Then

`|Σ_{rt} (S(A_r, z₀) − S(B_r, z₀)/φ(q))| ≤ ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)`,

where `A` is the set of `n ∈ (q^L, 2q^L]` with `n ≡ a (mod q)`, `B` the set of those prime to `q`, and `S(C_r, z₀)`
counts the `n ∈ C` divisible by `r` with no other prime factor below `z₀`. In the Lean, `dw q a n` is
`1[n ≡ a] − 1[(n, q) = 1]/φ(q)`.

Its main tools:

- `SieveBrun.fundamental` (`lib/pnt/SieveBrun.lean`), the fundamental lemma of the sieve in product form. Sift a
  finite set `C` by finite families `T_j` of moduli, truncating the inclusion–exclusion of `T_j` at an even level for
  the upper sieve and one level lower for the lower sieve. If every count `#{n ∈ C : p ∣ n for p ∈ s_j}`, `s_j ⊆ T_j`,
  is `X∏_j∏_{p∈s_j} g(p)` within `R`, then the sifted count is `X∏_j∏_{p∈T_j}(1 − g(p))` within an explicit error.
  The error has two parts: `X` times a sum of truncated products, and `R` times a count of the terms kept.
  `SieveBrun.gap_le` bounds the first.
- `SieveRanges.rng_sum_le_three` (`lib/pnt/SieveRangeSum.lean`), the sums that the gap is made of, with a value:
  `Σ_{A ≤ p < A²} 1/p ≤ 3` for every `A ≥ 1`. It is Mertens' first theorem in its elementary form,
  `Σ_{p ≤ n} (log p)/p ≤ log n + log 4` (`SieveRanges.sum_log_div_le`, from Legendre's formula for `n!` and
  Chebyshev's `θ(n) ≤ n log 4`). The comparison takes these sums bounded by a constant that the prime number theorem
  gives and that has no value (`SieveRanges.rng_sum_le`), since its levels grow as the error shrinks. No result uses
  the explicit bound yet: it is for Brun's sieve at a fixed level, where the gap `SieveProp6.zeta` is a number
  (`docs/research-opportunities.md`, §3.1, on a sieve without the window).
- `SieveGap.family_leaves_le` (`lib/pnt/SieveGap.lean`), Brun's sieve at a fixed level on a family of chains: for
  strictly decreasing chains `x` of primes at least `w = ⌈q^{εw}⌉`, cut out by comparisons, whose chains with
  `∏x > q^{L−1−δ'}` split into two blocks within the bilinear Type I estimate's reach,
  `|Σ_x (S(A_x, w) − S(B_x, w)/φ(q))|` is at most
  `(2ζ(k)(N₂ − N₁)/(φ(q) log w) + 2·rem·q^{L−1−δ'})·Σ_x 1/∏x + q^{L−δ}/φ(q)`. It is the leaves' bound of the
  comparison (`SieveP6TreeLeaves.tree_leaves_le`) with no tree above the level, which is then fixed.
- `SieveGap.gap_at`, the same at large `q` with every constant explicit. Take a level `εw`, an even `k ≥ 4`, a
  `δ'` with `(2k + 7)εw < δ' ≤ 1/16`, an `s ≥ 0` with `5δ' + s ≤ L − 2`, and bounds `hi_i` for the exponents of a
  family's primes that split into two blocks with `D₁ + (2k + 4)εw + 5δ' + s < L − 1` and
  `D₁ + 2D₂ + (2k + 4)εw < L + s`. Then for large `q` the family's terms at the level `w = ⌈q^{εw}⌉` satisfy
  `|Σ_x (S(A_x, w) − S(B_x, w)/φ(q))| ≤ 2ζ(k)·(N₂ − N₁)/(φ(q) log w)·Σ_x 1/∏x + q^{L−δ}/φ(q)` with
  `ζ(k) = SieveProp6.zeta 3 k`, a number. The block conditions are the bilinear Type I estimate's
  (`SieveP6LeavesWide.leavesOK_wide`) with the level's `(2k + 4)εw` added; the remainder of the sieve,
  `12·(2q^{εw})^{2k+7}` per chain, is why `δ'` exceeds `(2k + 7)εw`. No result uses it: the comparison below does
  without a fixed level.
- `SieveFillTree.tree_last` (`lib/pnt/SieveFillTree.lean`), Buchstab's tree below a chain's last entry: for a
  family of strictly decreasing chains `rt` and the rule that a branch `P` stops when `∏P ≥ E`, the terms
  `S(A_{rt}, rt_last)` are the leaves, the chains `(rt, P)` with `P` below `rt`'s last entry and `∏P < E`, sifted
  at a level `w`, plus the stops, sifted at their last entry, with signs. `SieveP6Tree.tree_chains` is the same
  for a family sifted at one level below all its entries.
- `SieveFill.prop6_fill_core` (`lib/pnt/SieveFill.lean`) and `SieveFillComp.prop6_fill`, `SieveFillComp.prop6_fill_at`
  (`lib/pnt/SieveFillComp.lean`), **the comparison in two variables with the rest among the tree's primes.**
  `SieveTwoComp.prop6_two` evaluates `Σ_r S(A_r, z₀)` over a family in boxes when the rest of the estimate in two
  variables is a product of the family's own primes, and a family with no prime of the rest's size has none. Here
  the primes of the tree below `z₀ = q^{a₀}` are used twice: the first of them, the largest, join the first
  variable until its product enters the window `(q^u, q^v]`, as before; a stop of that tree is then sifted
  further, by the tree below its last prime, and the primes of that second tree are the rest, until their product
  reaches `q^τ`. The rest then lies in `[q^τ, q^{τ+a₀})`, and the hypotheses are those of `prop6_two` with that
  range for the rest (`τ + a₀ < ρ₂`, `v + ρ₂ < L`, and the zone for `u ≤ m₁ ≤ v` and
  `L − ρ₂ − ε ≤ m₁ + m₂ ≤ L − τ + ε`) and with the leaves' growth `t + ρ₂` in place of `t`. The level of the
  sieve still falls with the error, so there is no gap: the conclusion is `prop6_two`'s,
  `|Σ_r (S(A_r, z₀) − S(B_r, z₀)/φ(q))| ≤ ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)` for every `η > 0` and large `q`. The
  leaves pass through two trees, so the level `k` is chosen with `(2k + 4)³ζ(k)` small
  (`SieveFillComp.exists_k3`).
- `SieveAd.fillTests_sound`, `SieveAd.fillTests_soundX` (`lib/pnt/SieveAdFill.lean`; the tests are
  `lib/pnt/SieveAdFillDefs.lean`'s, without Mathlib), **the tests of a decomposition with no Type II window**, for
  the trees of Buchstab steps on boxes of cells (`SieveAd.sound`). A box is evaluated by the estimate in two
  variables (`okI2`); its terms at a floor by the comparison with the rest among the box's primes (`okJ2`) or,
  for a box that has none of that size, among the tree's (`okJ3`, by `SieveFillComp.prop6_fill_at`): the rest is
  then of exponent between `r₁`, the least that the region takes, and `r₁ + f` for the floor `x^{f/DEN}`, the
  window is the one the region allows for all such rests, and the leaves grow by `t + r₁ + f`. The second
  statement is the same under two more atoms, for the trees of a reversed term. They are the tests of the
  theorem at `2165/1000`, `Linnik21650.linnik_21650` (`formalisations/README.md`; `docs/research-opportunities.md`,
  §3.1).
- `SieveAd.frozSolve_sound_at`, `SieveAd.dJF_level_at`, `SieveAd.famIR_eq`, `SieveAd.famJR_eq`
  (`lib/pnt/SieveAdFroz.lean`, `lib/pnt/SieveAdFrozTree.lean`), **the tree of a reversed term over a frozen
  part.** A reversed term is a sum over numbers `R` (the product `r'` of the term's other primes and its cofactor)
  of the `n = R·N` whose quotient `N` is sifted, and Buchstab's identity brings out a chain `c₁ > ⋯ > c_t` of
  primes of `N`: the term of the chain's box is the sum, over `R` and the chain, of the `n` with `R·c₁⋯c_t | n`
  and `n/R` free of primes below `c_t` (`famIR_eq`; `famJR_eq` for the terms at a level). The tree of
  `SieveAd.solveK_sound` has the case where the chain lies below every prime of `R`, which is one family of
  tuples. Here `R` runs over any finite family, the frozen part, in the range of `r'` for the cell of the prime
  that is reversed, and the chain's primes may lie above primes of `R`: the cut of a cell, Buchstab's identity on
  the chain, the test of a box with no term and the cost of a dropped box (in units of `Σ 1/R`) use `R` only
  through `x/R`, and the same search is sound, given tests that are sound for the frozen part
  (`SieveAd.SoundF`). `dJF_level_at` is the top of such a tree: the terms at a level `x^{t/DEN}` of the chain
  with no prime are the terms at a floor minus the term of the chain of one prime between the two. Nothing uses
  them yet: they are the first part of role reversal as an identity, for either sign and with the cofactor kept
  as one number (`docs/research-opportunities.md`, §3.1).
- `SieveDecomp.buchstab_fam`, Buchstab's identity on families of tuples of primes:
  `S(C_m, z) = S(C_m, w) − Σ_{w≤p<z} S(C_{mp}, p)`, in the form that extends a tuple by one smaller prime.
- `SieveLeaf.prod_T_le`, the main term at a leaf: `∏_{p < w, p ∤ q} (1 − 1/p) ≤ q/(φ(q) log w)` for an integer
  `w ≥ 2`, from `∏_{p < w} (1 − 1/p) ≤ 1/log w` (`SieveLeaf.prod_primesBelow_le`). That bound is elementary: the
  reciprocal of the product is `Σ 1/m` over the `m` whose prime factors are all below `w` (Mathlib's Euler product over
  the primes below `w`), and that sum is at least the harmonic sum `Σ_{m < w} 1/m ≥ log w`.

The note also covers the bound for rough numbers that the certificate's cells use (below):

- `SieveRough.psi_le`, rough numbers from above. For every `U` and `ε > 0`, eventually in `z`,
  `Ψ(y, z) ≤ (ω*(u) + ε)y/log z` for `u = log 2y/log z ≤ U`. Here `Ψ(y, z)` counts the `m ∈ (y, 2y]` with no prime
  factor below `z`, and `ω*` is the bound of `SieveCert.omegaC`: `0` below `1`, Buchstab's function `ω` itself on
  `[1, 3]` (`1/u` on `[1, 2)`, `(1 + log(u − 1))/u` on `[2, 3]`), and `0.565073` above `3`, the least constant, to six
  decimals, for which the induction of the proof closes with `0.5671433 ≥ max ω` on `[2, 3]` (`SieveOmegaB`).

These theorems are in the proof of `Linnik22000E.linnik_22000e`, whose axioms are `propext`, `Classical.choice` and
`Quot.sound` (`lib/check/Check.lean`), so they depend on those only.

## Source

- **Harman's sieve.** The method is G. Harman's: "On the distribution of αp modulo one", J. London Math. Soc. (2) 27
  (1983), 9–18, and the book *Prime-Detecting Sieves* (London Math. Soc. Monographs 33, Princeton University Press,
  2007), whose Chapter 3 is "The Alternative Sieve". It compares sifted sums over a set `A` with those over a
  comparison set `B`, using Type I information (counts in `A` of the multiples of `d`) and Type II information
  (bilinear sums over `A`). The library calls Proposition 6 Harman's fundamental theorem in the form used: it is the
  method's comparison step for the sets `A` and `B` above, with the Type II information of the Linnik paper's route.
- **The fundamental lemma.** V. Brun, "Le crible d'Eratosthène et le théorème de Goldbach", Videnskapsselskapets
  Skrifter I, Mat.-naturv. Klasse, Kristiania, 1920, no. 3. `SieveBrun.fundamental` is the fundamental lemma by Brun's
  sieve in its product form, built on the Bonferroni inequalities.
- **Buchstab's identity and Buchstab's function.** A. A. Buchstab, "Asymptotische Abschätzung einer allgemeinen
  zahlentheoretischen Funktion", Mat. Sb. 2(44) (1937), no. 6, 1239–1246.

None of these was read for the formalisation. Proposition 6, its proof and the three tools were written from the
methods as recalled, and state only what the route needs. Nothing in this library claims the methods as its own.

## What the formalisation here is

Proposition 6 is proved with one Buchstab tree for every product `r ≤ q^{b₀}`.

- **The tree** (`SieveDiff.tree_weighted`) iterates Buchstab's identity from `z₀` down to `w = ⌈q^{ε_w}⌉`, with
  `ε_w = c/(2k + 4)` and `c = (L − 1 − b₀)/4`. A branch stops when its partial product exceeds `X' = ⌊q^{b₀}⌋`: the
  stop then lies in the reflection `(X', z₀X']` of the route's window, and its cofactor in the window. `SieveStops2.stops2_bound` bounds the stopped terms by the route's Type II estimate (`hII`).
- **The leaves** (`SieveProp6.leaf_bound`). At a leaf `d = r∏P ≤ q^{b₀}`, `SieveLeaf.leaf_A` and `SieveLeaf.leaf_B`
  apply the fundamental lemma to `A` and `B`, with the ranges of primes below `w` cut into dyadic-exponent ranges and
  the levels `k + 2j`. Both main terms are `YV`, with `Y = (N₂ − N₁)/(dq)` and `V = ∏_{p < w, p ∤ q} (1 − 1/p)`, so the
  gap is at most `2ζ(k)·YV` plus a remainder, and `YV ≤ (N₂ − N₁)/(dφ(q) log w)` by `SieveLeaf.prod_T_le`. No lower
  bound for `B` and no count of rough numbers is needed.
- **Summing the leaves** (`SieveProp6.leaves_sum_le`). With `N₂ − N₁ ≤ X + 1`, `X = q^L`, the leaves total at most
  `(2ζ(k)(X + 1)/(φ(q) log w) + 2·rem·q^{b₀})·Σ_{rt} 1/r ∏_{w≤p<z₀}(1 + 1/p)`.
- **The parameters** (`SieveProp6.exists_k`, `SieveProp6.main_term`, `SieveProp6.rem_term`). An even `k` with
  `(2k + 4)²ζ(k)` small puts the main terms below `ηq^L/(φ(q) log q)`, and the remainders total at most
  `q^{L−c}/φ(q)`.

`SieveRough.psi_le` is proved from Buchstab's inequality for `Ψ`, Abel summation over the primes, and the prime number
theorem in the form `|θ(t) − t| ≤ εt/log t` for all large `t` (`SieveRough.theta_near`).

## Differences from the source

- **One problem, not a general theorem.** Proposition 6 compares `A`, the integers of `(q^L, 2q^L]` in one class mod
  `q`, with `B/φ(q)`, `B` those prime to `q`. The tuples `rt` are cut out by finitely many comparisons between their
  primes and products, and the Type II information is the route's hypothesis `TypeIIAt`. A general statement of
  Harman's fundamental theorem is not formalised.
- **The fundamental lemma** is proved by Brun's sieve, with each range of primes truncated at its own level, not by
  Selberg's or Rosser's sieve. Its constants are explicit: the gap is at most `V·ζ(k)` with
  `ζ(k) = e^{2C₀}(2C₀^k/k!)·exp(e^{2C₀}·2C₀^{k+1}/(k + 1)!)` (`SieveLeaf.leaf_gap`).
- **Rough numbers** are bounded above by `ω*`, which is Buchstab's `ω` on `[1, 3]` but above `3` the constant
  `0.565073`, slightly more than `ω(3) = 0.56438…`, the largest value of `ω` there. The certificate of the Linnik
  paper is computed with `ω*`.
- **The prime number theorem** used by `SieveRough.psi_le` is the library's `ψ(t) − t = O(t^{11/12+ε})`
  (`HalfPlanePNT.psi_isBigO_eleven_twelfths`), which comes from the zero-free half-plane for `ζ`
  ([openai-half-plane.md](openai-half-plane.md)). Any error term `o(t/log t)` would do, as in the classical prime
  number theorem.

## Where the Linnik paper uses it

In the leaves of its decomposition: `SieveLeaves.P6_spec` applies `prop6` to each family of at most `40` comparisons,
and `SieveLeaves.P6IB_spec` applies the form of Proposition 6 with the bilinear Type I estimate (`SieveP6ib.prop6ib`,
the paper's Proposition 4.8) to the families of the boxes that the rule's bilinear test (R2) takes whole, with the
witnesses of the test (`SieveCert.ibOK_sound`) turned into its hypotheses by `SieveQ.P6IB_boxes`. The rough-number bound also gives the shares of the certificate's cells (`SieveRough.share2_of_cand`), with which
`SieveDrop` bounds the terms the decomposition drops.
