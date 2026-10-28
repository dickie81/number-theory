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
- `SieveDecomp.buchstab_fam`, Buchstab's identity on families of tuples of primes:
  `S(C_m, z) = S(C_m, w) − Σ_{w≤p<z} S(C_{mp}, p)`, in the form that extends a tuple by one smaller prime.
- `SieveRough.psi_le`, rough numbers from above. For every `U` and `ε > 0`, eventually in `z`,
  `Ψ(y, z) ≤ (ω*(u) + ε)y/log z` for `u = log 2y/log z ≤ U`. Here `Ψ(y, z)` counts the `m ∈ (y, 2y]` with no prime
  factor below `z`, and `ω*` is the bound of `SieveCert.omegaC`: `0` below `1`, Buchstab's function `ω` itself on
  `[1, 3]` (`1/u` on `[1, 2)`, `(1 + log(u − 1))/u` on `[2, 3]`), and `0.565073` above `3`, the least constant, to six
  decimals, for which the induction of the proof closes with `0.5671433 ≥ max ω` on `[2, 3]` (`SieveOmegaB`).

These theorems are in the proof of `Linnik22240R.linnik_22240r`, whose axioms are `propext`, `Classical.choice` and
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
  the levels `k + 2j`. The gap is at most `4ζ(k)·#{n : d ∣ n, n w-rough}/φ(q)` plus a remainder, and the count of
  `w`-rough multiples is at most `Ψ(X/d, w)`.
- **Summing the leaves** (`SieveProp6.leaves_sum_le`). With `Ψ(X/d, w) ≤ 2X/(d log w)` from `SieveRough.psi_le`, the
  leaves total at most `(4ζ(k)·2X/(φ(q) log w) + 4·rem·q^{b₀})·Σ_{rt} 1/r ∏_{w≤p<z₀}(1 + 1/p)`.
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
- **The fundamental lemma** is proved by Brun's pure sieve with explicit truncations, not by Selberg's or Rosser's
  sieve. Its constants are explicit: the gap is at most `V·ζ(k)` with
  `ζ(k) = e^{2C₀}(2C₀^k/k!)·exp(e^{2C₀}·2C₀^{k+1}/(k + 1)!)` (`SieveLeaf.leaf_gap`).
- **Rough numbers** are bounded above by the crude `ω*`, not by Buchstab's `ω`. The bound is weaker, and the
  certificate of the Linnik paper is computed with it.
- **The prime number theorem** used by `SieveRough.psi_le` is the library's `ψ(t) − t = O(t^{11/12+ε})`
  (`HalfPlanePNT.psi_isBigO_eleven_twelfths`), which comes from the zero-free half-plane for `ζ`
  ([openai-half-plane.md](openai-half-plane.md)). Any error term `o(t/log t)` would do, as in the classical prime
  number theorem.

## Where the Linnik paper uses it

In the leaves of its decomposition: `SieveLeaves.P6_spec` applies `prop6` to each family of at most `18` comparisons.
The rough-number bound also gives the shares of the certificate's cells (`SieveRough.share2_of_cand`,
`SieveRough.share4_of_counted4`), with which `SieveDrop` bounds the terms the decomposition drops.
