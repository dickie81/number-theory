# The Halász–Montgomery inequality over the characters mod `q`

**Lean:** `LinnikPower.hm_duality` (`lib/pnt/LinnikPower.lean`):

```lean
theorem hm_duality {R : Finset (DirichletCharacter ℂ q)} {S : Finset ℕ} (hS0 : 0 ∉ S) {Λ : ℝ} (hΛ : 0 < Λ)
    (hSΛ : ∀ n ∈ S, (n : ℝ) ≤ Λ) (a : ℕ → ℂ) {σ : ℝ} (β γ : DirichletCharacter ℂ q → ℝ)
    (hβ : ∀ χ ∈ R, σ ≤ β χ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ χ ∈ R, ∀ χ' ∈ R, χ ≠ χ' →
      ‖∑' n : ℕ, kTerm (χ * χ'⁻¹) Λ (((β χ + β χ' - 2 * σ : ℝ) : ℂ) + ((γ χ - γ χ' : ℝ) : ℂ) * I) n‖ ≤ B) :
    (∑ χ ∈ R, ‖pv S a χ ((β χ : ℂ) + γ χ * I)‖) ^ 2 ≤
      Real.exp 1 * (∑ n ∈ S, ‖a n‖ ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) * (R.card * Λ + R.card ^ 2 * B)
```

In words, let `F(χ, s) = Σ_{n∈S} a_nχ(n)n^{−s}` with `S ⊆ [1, Λ]`, and take one point `β_χ + iγ_χ` with `β_χ ≥ σ`
for each character `χ` of a set `R` of characters mod `q`. Let `B` bound the off-diagonal kernels
`|K_Λ(χχ′⁻¹, z_{χχ′})|` for `χ ≠ χ′` in `R`, where `K_Λ(ψ, z) = Σ_{n≥1} ψ(n)n^{−z}e^{−n/Λ}` (`kTerm`) and
`z_{χχ′} = β_χ + β_χ′ − 2σ + i(γ_χ − γ_χ′)`. Then

`(Σ_{χ∈R} |F(χ, β_χ + iγ_χ)|)² ≤ e·Σ_n |a_n|²n^{−2σ}·(|R|Λ + |R|²B)`.

Two forms of it are used.

- `LinnikReflect.hm_duality_W` (`lib/pnt/LinnikWeighted.lean`) takes the weight `e^{−n/U} − e^{−2n/U}` in place of
  `e^{−n/Λ}`. Huxley's large-values estimate is built on it ([huxley-density.md](huxley-density.md)).
- `SieveTypeIIHM.sum_bin_hm` (`lib/pnt/SieveHMBin.lean`) is the case `σ = 0`, `β_χ = 0` and `γ_χ = h₀`, one height
  for the whole bin, at `Λ = 2P` for `S ⊆ (P, 2P]`.

`hm_duality_W` is in the proof of `Linnik21500.linnik_21500`, the Linnik paper's theorem, through Huxley's estimate,
and `hm_duality` and `sum_bin_hm` in that of `Linnik22000E.linnik_22000e`, the library's theorem at `11/5`. The
axioms of both theorems are `propext`, `Classical.choice` and `Quot.sound` (`lib/check/Check.lean`), so these depend
on those only. `hm_duality` does not use the zero-free half-plane.

## With weights, in mean square, and for two polynomials

`SieveTypeIIHM.hm_duality_wt` (`lib/pnt/SieveTwoBins.lean`) is the same inequality with a weight `η_χ ∈ ℂ` on each
character, under the same hypotheses:

`|Σ_{χ∈R} η_χ F(χ, β_χ + iγ_χ)|² ≤ e·Σ_n |a_n|²n^{−2σ}·(Λ·Σ_χ |η_χ|² + B·(Σ_χ |η_χ|)²)`.

`hm_duality` is the case in which `η_χ` is the phase of the conjugate of `F`, of modulus at most `1`. With `η_χ` the
conjugate of `F` itself, at `σ = 0`, `β_χ = 0`, `γ_χ = h₀` and `Λ = 2P` for `S ⊆ (P, 2P]`, the left side is the square
of `D = Σ_χ |W(χ)|²`, `W(χ) = dp S (aχ) h₀`, and the right side is at most `e·Σ|a|²·(2P + |R|B)·D`. So

`Σ_{χ∈R} |W(χ)|² ≤ e·Σ_{j∈S} |a_j|²·(2P + |R|·B)` (`SieveTypeIIHM.sum_bin_hm_sq`),

the mean-square form: against orthogonality's `(P + q)Σ|a|²`, the number of characters of the set multiplies the
kernel bound only. It does not follow from `hm_duality` on the subsets of `R` without a factor `log |R|`.

For two polynomials `W₁` and `W₂`, Cauchy–Schwarz over a bin needs no count of the bin:

- `SieveTypeIIHM.sum_bin_two`: `Σ_{χ∈R} |W₁(χ)||W₂(χ)|` is at most the product of the square roots of the two mean
  squares, each the smaller of orthogonality's bound and the one above (`sqTerm`);
- `SieveTypeIIHM.sum_typeII_two_bins`: the sum over `χ ≠ 1` of `|W₁(χ)||W₂(χ)||B(χ)|`, by bins, as
  `SieveTypeIIHM.sum_typeII_bins_hm` does for one polynomial;
- `SieveTypeIIHM.bin_bound_two` (`lib/pnt/SieveTwoZone.lean`): a bin's contribution as a power of `q`. For
  `P_i = q^{m_i}` it is at most a constant times `(1 + log qT)^{10} q^{L − 1/25000 + η}(Σ|a|²/P₁)^{1/2}(Σ|b|²/P₂)^{1/2}`
  when there are exponents `M_i` for the two mean squares (`M_i ≥ max(m_i, 1)`, or `M_i ≥ max(m_i, g + b(m_i))` with
  `b` the exponent of the kernel bound) with `(L − m₁ − m₂)(β + w) + (m₁ + M₁)/2 + (m₂ + M₂)/2 ≤ L − 1/25000`
  (`twoBound`). The window's exponents have a term `g/2` that these do not;
- `SieveTypeIIHM.twoBound_of_long`: that inequality holds, for every value of the curve, when `m₁, m₂ ≥ 1` and
  `m₁ + m₂ + 1/2000 ≤ L`: two variables of length at least `q` and a third factor of length at least `q^{1/2000}`.

Summed over the bins these give the paper's Proposition 3′ for two polynomials:

- `SieveTypeIIHM.typeII_two_gen` (`lib/pnt/SieveTwoTypeII.lean`): for a curve `g ≤ 1` with `g(1/2) = 1` and the
  counts `CurveCounts g`, and a region `R` of pairs `(m₁, m₂)` on which `twoBound` holds for `β ∈ [1/2, 11/12]` and
  `w ≤ 4·10⁻⁶` (`ZoneOK g L d e R`), there is `q₀` such that for `q ≥ q₀`, `S_i ⊆ (P_i, 2P_i]` with
  `(log_q P₁, log_q P₂)` in `R`, and at most `K₀` prime sums at scales `Q_j ≥ q^{e₁}` with
  `∏ Q_j ≤ 2^{K₀}q^L/(P₁P₂)`:
  `Σ_{χ≠1} |W₁(χ)||W₂(χ)||∏_j Sp(χ, Q_j, h_j)| ≤ q^{L − 1/50000}(Σ|a|²/P₁)^{1/2}(Σ|b|²/P₂)^{1/2}`.
  It is `SieveTypeIIHM.typeII_gen_hm` with two polynomials in place of one and a region in place of the window;
- `SieveTypeIIHM.typeII_two_long`: the same bound for `P₁ ≥ q`, `P₂ ≥ q` and `P₁P₂ ≤ q^{L − 1/2000}`, for every
  `L`, at the curve `g = 1`: no density estimate enters, only the half-plane through the prime sums;
- `SieveTypeIIHM.typeII_two_gen4` (`lib/pnt/SieveTwoTypeII4.lean`): `typeII_two_gen` with a third bound for each
  mean square, the fourth moment (`lib/pnt/SieveTwoFourth.lean`). `W(χ)²` is the polynomial of the products of two
  elements of `S`, so orthogonality gives `Σ_χ |W(χ)|⁴ ≤ (3P² + q)·F·(Σ|a|²)²` (`sum_chars_dp_four_le`, with `F` the
  divisor bound for the pairs, `card_fiber_le_pow`), and Cauchy–Schwarz over a bin of `|R|` characters gives
  `Σ_{χ∈R}|W(χ)|² ≤ |R|^{1/2}((3P² + q)F)^{1/2}Σ|a|²` (`sum_bin_four_le`): the exponent `M ≥ g/2 + max(m, 1/2) + 2e`
  (`SqExp4`, `lib/pnt/SieveTwoZone4.lean`). It is the case `r = 2` of the moments of Burgess's method; for a variable
  shorter than `√q` it beats orthogonality in every bin with fewer than `q` characters. Nothing uses it yet: it is
  for the leaves of Buchstab's tree with a cofactor shorter than `√q`, taken as the second variable with the
  primes of `d₂` as the rest (`docs/research-opportunities.md`, §3.1);
- `SieveTypeIIHM.zone_leaf` (`lib/pnt/SieveLeafZone.lean`, written by `tools/linnik/gen_leafzone.py`): `ZoneOK4` for
  the curve `g7d` (Ingham's, Chen, Gupta and Li's and Huxley's steps) on the region `LeafZone L` of the leaves,
  for every `L`: the first variable `d₁` of length `q^{m₁}`, `9/10 ≤ m₁ ≤ 6/5`, the second the cofactor, of length
  `q^{m₂}` with `2/5 ≤ m₂ ≤ 1/2`, and the rest `ρ = L − m₁ − m₂` in `[3/10, 1]`, cut by the seven cases of the proof
  that bind. Below `4/7` both variables are by orthogonality; above, the cofactor is by the fourth moment and `d₁`
  by orthogonality while the curve is at least `1/2 − 2/1000`, by the Halász–Montgomery inequality after
  (`SieveTwoPieces4`); each of the 536 cases at the ends of the 67 pieces is `linarith` from the region's 13
  inequalities. At `L = 2.135` it holds the leaves with `d₂` from `x^{0.28}` to `x^{0.32}` and the cofactor down to
  `q^{0.47}`;
- `SieveCurveHx.counts_hx` (`lib/pnt/SieveCurveHx.lean`, written by `tools/linnik/gen_zone.py`): the counts of the
  curve `ghx`, the trivial count `1` below `7789/10000` and Huxley's density estimate from there on (a step
  `SieveCurveHx.charDensity_hxT` on `[7789/10000, 131/168]` with the exponent `(7014/3125)(1 − σ)`, Huxley's
  `3/(3σ − 1)` being `2.24433` at `7789/10000`; then `LinnikStairs7`'s steps and `(101/50)(1 − σ)` from `5/6`), with
  no hypothesis and neither Ingham's estimate nor Chen, Gupta and Li's;
- `SieveTwoZone7D.zone_hx` (`lib/pnt/SieveTwoZone7D.lean`, written by `tools/linnik/gen_zone.py`): `twoBound` for
  the curve `ghx`, for every `L`, on the region `Zone7d L`. With `s_i = 1 − m_i` and `ρ = L − m₁ − m₂`
  it is `ρ ≥ 1/2000`, `m_i ≥ 2/3`, and `s₁ + 1/12500`, `s₂ + 1/12500`, `s₁ + s₂ + 1/12500` at most `λρ`,
  `λ = 27637/62500 = 0.442192`: a variable may be shorter than `q` by `λ` times the exponent of the rest. Both mean
  squares are bounded by orthogonality for `β ≤ 7789/10000` and by the Halász–Montgomery inequality from there on,
  where the curve is at most `1/2 − 2/1000`; `λ = 2(1 − 7789/10000 − 4·10⁻⁶)`. So the estimate needs a density
  estimate only from `7789/10000` on, where Huxley's is below `1/2 − 2/1000`. The proof glues the curve's 18 pieces
  (`SieveTwoPieces`: on a piece the exponent is affine in `β` for each choice of the two maxima, so its two ends
  suffice, and at an end `linarith` proves the inequality from the region's six). Below `7789/10000` the curve `1`
  leaves only orthogonality, so for one short variable the region is the exact zone of `ghx` (`gen_zone.py
  --exact`). The region was first proved for the curve `g7d` of `SieveCurve7D` (Chen, Gupta and Li's steps on
  `[5/7, 131/168]`), whose zone is in the git history; its name stays, as the certificate's tests are written for it;
- `SieveTwoZone7D.typeII_two_hx`: `typeII_two_gen` for `ghx` on `Zone7d L`, with no hypothesis.

The sieve meets the estimate through families of sums (in one variable `SieveFamily.typeII_sharp`): a
polynomial variable with coefficients, primes with smooth weights at fixed scales, and sharp comparisons between
them, each with a prime as a pivot. For two polynomial variables:

- `SieveFamilyGen` (`lib/pnt/SieveFamilyGen.lean`) is `SieveFamily`'s argument with the polynomial part abstract. It
  uses the variable `m` only through its value, its coefficient, its parts `φ_j(m)` of the comparisons' forms, the
  sum of `|a_m|`, and one bound, the Type II estimate at each frequency of the separated sum; there these are data
  (`m` in a finite set of any type) and a hypothesis. `SieveFamilyGen.family_bound_gen`,
  `SieveFamilyGen.sharp_explicit_gen` and `SieveFamilyGen.sharp_gen` are `family_bound`, `typeII_sharp_explicit` and
  `typeII_sharp` in that form; the lemmas on the cut-off and the pivots are `SieveFamily`'s, unchanged;
- `SieveFamilyTwo.box_two` (`lib/pnt/SieveFamilyTwo.lean`) is the hypothesis for pairs `(m₁, m₂)`: a phase
  `κ + Σ_j ξ_j(φ_j(m₁) + ψ_j(m₂))` is a twist of `a` times a twist of `b`, and `χ(m₁m₂) = χ(m₁)χ(m₂)`, so the sum
  over the pairs is a product of two polynomials, which Proposition 3′ in two variables bounds
  (`SieveFamilyTwo.TypeIITwoAt L R`: for the curve `ghx` on `Zone7d L`, `SieveFamilyTwo.typeIITwoAt_hx`; for two
  variables of length at least `q`, `SieveFamilyTwo.typeIITwoAt_long`);
- `SieveFamilyTwo.typeII_sharp_two`, **Lemma 4.4 in two variables**: given `TypeIITwoAt L R`, for `m_i ∈ S_i ⊆
  (P_i, 2P_i]` with `(log_q P₁, log_q P₂)` in `R` and `|a_m| ≤ A₀`, `|b_m| ≤ B₀`, at most `K₀` primes at scales
  `Q_i ≥ q^{e₁}` with `∏ Q_i ≤ 2^{K₀}q^L/(P₁P₂)`, and at most `J₀` sharp comparisons with forms
  `φ_j(m₁) + ψ_j(m₂) + Σ_i e_{ji} log x_i`, bounded by `Λ₀ log q` on the family and each with a pivot prime, the
  family's sum over `𝒜 − ℬ/φ(q)` at `n = m₁m₂∏x_i` is at most `A₀B₀q^{L−δ}/φ(q)`, for some `δ > 0` and large `q`.

- `SieveUnwTwo.typeII_unw_two`, **Lemma 4.5 in two variables** (`lib/pnt/SieveUnwTwo.lean`): the same without the
  dyadic weights. For `0 < L ≤ 5/2`, `m_i ∈ S_i ⊆ (P_i, P_i′]` with `P_i ≥ 1`, `P_i′ ≤ 2q^L` and `R` on the rectangle
  `[log_q P₁, log_q P₁′] × [log_q P₂, log_q P₂′]`, the primes over all the primes up to `⌊2q^L⌋`, and comparisons
  as above that force each prime to be at least `2q^{e₁}` and `m₁m₂∏x_i ≤ 2q^L`: the family's sum over
  `𝒜 − ℬ/φ(q)` is at most `A₀B₀q^{L−δ}/φ(q)`. It is `SieveUnwGen.unw_gen` (`SieveTypeIIU.typeII_unw`'s argument
  with the polynomial part abstract and cut into blocks by a map) for the pairs of dyadic blocks, at most
  `(3 + 4 log q)²` of them.

- `SieveTwoCross.BilBd.cmp_list`, **conditions between the two variables** (`lib/pnt/SieveTwoCross.lean`): a
  comparison between `m₁` and `m₂` with no prime in it has no pivot, and its cut-off does not separate into a twist
  of each variable. It costs a logarithm instead. If `Σ_χ |Σ_i f_iF_i(χ)||Σ_j g_jG_j(χ)|W(χ) ≤ C|f|₂|g|₂` for all
  coefficients `f` and `g`, then with a condition `u(i) ≤ v(j)` (or `<`) inside the double sum the bound is
  `(N + 1)C|f|₂|g|₂`, for `v` with fewer than `2^N` values, and `(N + 1)^k C|f|₂|g|₂` with `k` conditions. The proof
  replaces `u` and `v` by their ranks among the values of `v` and splits on a binary digit: with `d = 2^{N−1}`,
  `1[u ≤ v] = 1[u < d ≤ v] + (1[u, v < d] + 1[u, v ≥ d])·1[u mod d ≤ v mod d]`; the first term is a product, and
  the two others have disjoint supports in `i` and in `j`, so the Cauchy–Schwarz inequality keeps the constant of
  the induction.
- `SieveTwoChain.chain_two`, **Lemma 4.6 in two variables** (`lib/pnt/SieveTwoChain.lean`): given `TypeIITwoAt L R`
  and `0 < L ≤ 5/2`, let `z` run over the `K`-tuples of primes up to `⌊2q^L⌋` that satisfy at most `J₀` comparisons
  `0 ≤ c + Σ_i e_i log z_i` (or `0 <`) with `e_i ∈ {−1, 0, 1}` and `c ≤ Λ₁ log q`, of any kind, and let `S₁` and
  `S₂` be disjoint sets of indices that leave an index out. If every such tuple has its entries at least `q^{e₀}`,
  `P₁ < ∏_{S₁} z ≤ P₁′`, `P₂ < ∏_{S₂} z ≤ P₂′`, `M < ∏_{S₁} z·∏_{S₂} z ≤ M′` and `∏z ≤ 2q^L`, and `R` holds at
  the points `(u, v)` of the rectangle `[log_q P₁, log_q P₁′] × [log_q P₂, log_q P₂′]` with `M ≤ 4q^{u+v}` and
  `q^{u+v} ≤ M′`, then
  `|Σ_z (1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q))| ≤ q^{L−δ}/φ(q)`, for some `δ > 0` and large `q`. The two variables are
  the tuples on `S₁` and on `S₂` (`lib/pnt/SieveTwoTuples.lean`): a tuple of primes is recovered from its product up
  to `(K + 1)^K` choices, so a polynomial of tuples is one of integers whose mean square is at most `(K + 1)^K`
  times as large. A comparison with a prime outside `S₁ ∪ S₂` has it as a pivot and goes into
  `SieveUnwGen.unw_gen`; the others are conditions between the two variables, and cost a power of `log q`. The
  band `M < ∏_{S₁} z·∏_{S₂} z ≤ M′` is two of them, so the region is asked where the two variables can be together
  and not on the whole rectangle of their ranges. A term `Σ_r S(A_r, z)` of a sieve is a sum of such families, one
  for each number of prime factors of the cofactor: with the cofactor in the second variable
  (`SieveTwoTerm.chain2_bound`, the band being `n` over the rest) or in the rest (`SieveTwoTerm.chain2R_bound`,
  the two variables being sets of the chain's primes; `SieveTwoTerm.chain2R_at` is the statement for an exponent
  `2 < L ≤ 5/2`, with no route).

- `SieveTwoComp.prop6_two`, **Harman's comparison with stops in two variables** (`lib/pnt/SieveTwoComp.lean`): the
  paper's Proposition 4.8 (`SieveP6ib.prop6ib`) with this estimate in place of the window, and with its Lemma 4.3 on
  the wider region. For a family of strictly decreasing chains `rt` in boxes `q^{lo_i} ≤ rt_i ≤ q^{hi_i}`, all at
  least `z₀ = ⌈q^{a₀}⌉`, a set `S₀` of indices whose product `c` enters a window `(u, v)` with `u + a₀ < v`,
  `u − Σ_{S₀} lo ≤ t` and `Σ_{S₀} hi < v`, a disjoint set `Sr ≠ ∅` whose product, the rest, has its exponent in
  `[ρ₁, ρ₂]`, the region at the `(m₁, m₂)` with `u ≤ m₁ ≤ v` and `L − ρ₂ − ε ≤ m₁ + m₂ ≤ L − ρ₁ + ε`, and a split
  `(S₁, eIn₁)` of the leaves
  with `D₁ < L − 1` and `max(D₁, 1) + D₁ + 2D₂ < 2L − 1`:
  `|Σ_{rt}(S(A_r, z₀) − S(B_r, z₀)/φ(q))| ≤ ηq^L/(φ(q) log q) + q^{L−δ}/φ(q)` for every `η > 0` and large `q`. The
  tree over the primes below `z₀` stops when `c∏P` passes `⌈q^u⌉`; a stop's first variable is `c∏P·p`, in the
  window because the steps are below `z₀`, its rest is the chain's, and its second variable is all the rest of `n`
  (`SieveTwoTerm.chain2_bound`, from `chain_two` on the chain and the primes of its cofactor). The tree and its
  leaves are the paper's (`SieveTwoP6.prop6_two_core` is `SieveP6ib.prop6ib_core` with the rest carried along the
  extensions of a chain), and the leaves' sizes are those of `SieveTypeIBAsymWide.leaves_ib_wide`
  (`SieveP6LeavesWide.leavesOK_wide`). `SieveTwoComp.prop6_two_at` is the statement for an exponent `2 < L ≤ 5/2`,
  with no route: these lemmas use a route only for its exponent.

The region enters through a rectangle cut by a band of the sum of the two exponents: the estimate holds for a
family whose two variables have their exponents in such a set inside the region. A set of tuples cut by another
slanted side of the region is a union of such sets and a remainder that these lemmas do not evaluate.

Two theorems of the library use them, both in no paper. Linnik's theorem with exponent `219/100`
(`Linnik21900.linnik_21900`) has for its decomposition a tree of Buchstab steps with the window's tests
and two tests by this estimate, a box evaluated outright (`SieveAd.evI_two`, from `chain2_bound`) and the
comparison at a floor (`SieveAd.evJ_two`, from `prop6_two_at`); the term with its cofactor in the rest
(`chain2R_bound`) is not used there. Linnik's theorem with exponent `218/100` (`Linnik21800.linnik_21800`) adds
role reversal for a term of three primes to that tree, and uses the two tests under two more conditions on the
tuples (`SieveAd.evI_twoE`, `SieveAd.evJ_twoE`), for the trees of the reversed terms.
`lib/check/CheckAll.lean` prints their axioms, which are `propext`,
`Classical.choice` and `Quot.sound`. They are the estimate in two variables of
[`docs/research-opportunities.md`](../docs/research-opportunities.md) (§3.1). What that section's computations
below `2.18` use and these do not give: role reversal for terms of more primes and at more than one level, and the
comparison with its rest among the small primes.

## Source

The inequality is named after G. Halász and H. L. Montgomery, who used it for large values of Dirichlet polynomials
and zero density:

- G. Halász, "Über die Mittelwerte multiplikativer zahlentheoretischer Funktionen", Acta Math. Acad. Sci. Hungar. 19
  (1968), 365–403;
- H. L. Montgomery, "Mean and large values of Dirichlet polynomials", Invent. Math. 8 (1969), 334–345, and his
  *Topics in Multiplicative Number Theory*, Lecture Notes in Math. 227 (Springer, 1971).

None of these was read for the formalisation. Huxley's "Large values of Dirichlet polynomials" (Acta Arith. 24 (1973),
329–346), whose p. 329 was read, calls it "the Halász inequality (Montgomery's basic tool)". The library's proof was
written from the standard argument by duality. Nothing in this library claims the inequality as its own.

## What the formalisation here is

`hm_duality` is proved by duality. With the phases `η_χ = conj F_χ/|F_χ|`, the left side is `|Σ_n a_n n^{−σ}·w_n|²`
with `w_n = Σ_χ η_χχ(n)n^{−(β_χ−σ)−iγ_χ}`. Cauchy–Schwarz with the weight `e^{−n/Λ}`, which is at least `e^{−1}` on
`S`, bounds it by `e·Σ_n |a_n|²n^{−2σ}` times `Σ_{n≥1} e^{−n/Λ}|w_n|²`. That full series expands into the kernels:
`Σ_{χ,χ′} η_χη̄_χ′K_Λ(χχ′⁻¹, z_{χχ′})`. The diagonal kernels are at most `Σ_n e^{−n/Λ} ≤ Λ` (`wt_summable_le`), and
the others at most `B`.

## Differences from the source

- **The first-power form.** The bound is on `(Σ_χ |F|)²`, the square of the sum of the absolute values, which is the
  form a count of large values uses.
- **The kernel bound is a hypothesis.** `B` is any bound on the off-diagonal kernels. Each use supplies its own:
  - Huxley's estimate bounds the kernels through the functional equation
    (`LinnikReflect.norm_hTerm_le_reflect`; [huxley-density.md](huxley-density.md)).
  - The Type II estimate's top piece takes `B` from `LinnikOffDiag.norm_offK_le`:
    `C(2P)^{1/12−δ}(2q)^{5/12+δ+2ε′}`. That bound moves the kernel's integral to `Re w = 1/12 − δ`. There it uses the
    functional equation and the bound on `Re s = 11/12 + δ` that the zero-free half-plane gives
    (`LinnikLindelof.lindelof`; [openai-half-plane.md](openai-half-plane.md)).
- **One point per character.** The points of different characters are unrelated; no spacing is needed, since
  `χχ′⁻¹ ≠ 1` for `χ ≠ χ′`.

## Where the Linnik paper uses it

- Through Huxley's estimate, on the steps of the density curve from `7789/10000` on
  ([huxley-density.md](huxley-density.md)).
- Directly, in mean square, in the Type II estimate in two variables: each bin of characters from `7789/10000` on
  bounds the mean square of a polynomial by `SieveTypeIIHM.sum_bin_hm_sq`, from the weighted form
  `SieveTypeIIHM.hm_duality_wt` at the weights `conj W(χ)`, with the kernel bound above.

The library's theorem at `11/5` used it directly on the top piece `[5/6, 11/12]` of its Type II estimate in one
variable: there `SieveHMBins` and `SieveTypeIIHM` bound each bin of characters at one height by
`SieveTypeIIHM.sum_bin_hm`, with the kernel bound above, and the window of that theorem,
`[43457/100000, 46959/100000]·L` at `L = 11/5`, is the window of this branch (`SieveTypeIIU22000D`). (The earlier windows, `[41556/100000, 47531/100000]·L` at `L = 278/125`,
  `[41479/100000, 47555/100000]·L` at `L = 89/40` and `[41335/100000, 48069/100000]·L` at `L = 899/400`, are in the git
  history.)
