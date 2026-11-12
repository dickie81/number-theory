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
  theorems at `2165/1000` and `2150/1000`, `Linnik21650.linnik_21650` and `Linnik21500.linnik_21500`
  (`formalisations/README.md`; `docs/research-opportunities.md`, §3.1).
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
  with no prime are the terms at a floor minus the term of the chain of one prime between the two. They are the
  first part of role reversal as an identity, for either sign and with the cofactor kept as one number, which the
  theorem at `2150/1000` uses (`SieveAd.pr_of_kidsF_at`, below; `docs/research-opportunities.md`, §3.1).
- `SieveAd.bd_flip_neg_at`, `SieveAd.bd_flip_pos_at`, `SieveAd.froz_weight_le_at`, `SieveAd.shareLe_of_box_at`,
  `SieveAd.inSlab_frozS_at`, `SieveAd.inSlab_frozS_inner_at` (`lib/pnt/SieveAdFlip.lean`,
  `lib/pnt/SieveAdFlipSum.lean`), **role reversal through the largest prime, as an identity.** A box of primes
  `p₁ > a₁ > ⋯ > a_{s+1}`, the cell of `p₁` being `(l₁, h₁)`, counts the `n = p₁·a₁⋯a_{s+1}·m` with `m` free of
  primes below `a_{s+1}`. The frozen part is the set of the pairs `(a, m)` with `R = a₁⋯a_{s+1}·m` in a range,
  `m` kept as one number whatever its prime factors (`SieveAd.frozS`), and `n/R` is sifted at a level
  `Z = ⌈x^{t/DEN}⌉` with `l₁ ≥ t ≥ h₁/2`, where a number of the size of `p₁` with no prime factor below `Z` is
  prime. So the term of the box is at most the terms at the level over the frozen part with `R` in
  `(x^{(DEN−h₁)/DEN}, x^{(DEN−l₁+1)/DEN}]` (`SieveAd.flip_cover`) and at least those over the part with `R` in
  `(x^{(DEN−h₁+1)/DEN}, x^{(DEN−l₁)/DEN}]` (`SieveAd.flip_inject`), for any weights `g ≥ 0`: the reversal serves a
  term that needs a lower bound as well as one that needs an upper bound, at the price of the `R` within
  `x^{1/DEN}` of the two ends. The weight `Σ 1/R` of the narrower part is at most `h₁/DEN` times the share of the
  box, the bound of its own dropped term (`froz_weight_le_at`, `shareLe_of_box_at`): each `R` carries the primes
  of `(x/R, 2x/R]`, at least `(1 − ε)(DEN/h₁)(x/R)/log x` of them, and the `n = RP` are numbers of the box. With
  weights `w₀`, `w₁`, `w₂` of the narrower part and of the two ends, `bd` the bound for the rough numbers of
  `(x/R, 2x/R]` at the level, and a tree of cost `C` over the frozen part (the terms at a floor evaluated, the
  chain of one prime between the floor and the level bounded), the term of the box has
  `Bd false (C(w₀ + w₁ + w₂) + bd(w₁ + w₂))` (`bd_flip_neg_at`) or `Bd true (C·w₀ + bd(w₁ + w₂))`
  (`bd_flip_pos_at`). The tests that are sound for this frozen part and the search with this reversal are below;
  the theorem at `2150/1000` uses the reversal for the sign `−` only (`docs/research-opportunities.md`, §3.1).
- `SieveAd.sum_famU_eq_at` (`lib/pnt/SieveAdSort.lean`), **tuples of distinct primes in cells, sorted.** The
  tuples of a reversed term are not in order: the primes of `r'` and those of the chain each decrease, with
  nothing between the two, where the comparisons are proved for strictly decreasing tuples. A tuple of distinct
  numbers strictly decreases in exactly one order of its entries (`SieveAd.existsUnique_sort`, from Mathlib's
  `Tuple.sort`), so a sum over the tuples of distinct primes in the cells `bx` (`SieveAd.famU`) under a condition
  is the sum, over the permutations `σ`, of the sums over the boxes `bx ∘ σ` under the condition carried by `σ`.
  `SieveAd.evJ_famSet_at` uses it.
- `SieveAd.evJ_fill_core_at`, `SieveAd.evJ_two_core_at` (`lib/pnt/SieveAdFillCore.lean`; the checks are
  `lib/pnt/SieveAdCoreDefs.lean`'s, without Mathlib), **the two comparisons at a floor, on the sums of a box.**
  `SieveAd.evJ_fillE` and `SieveAd.evJ_twoE` evaluate the terms at a floor of a box that passes a test which reads
  the box through sums over sets of its primes, the sets given by the bits of their positions in the search's
  list. Here the box is a function, the sets are sets of its indices, and the checks (`SieveAd.coreJ3`,
  `SieveAd.coreJ2`) are on numbers that bound the sums: `c0lo ≤ Σ_{S₀} lo`, `c0hi ≥ Σ_{S₀} hi`, `h1s ≥ Σ_{S₁} hi`,
  `h2s ≥ Σ_{S₁ᶜ} hi`, and for a rest among the box's primes `ρ₁ ≤ Σ_{Sr} lo`, `ρ₂ ≥ Σ_{Sr} hi`. The box may have
  any number of primes, the comparisons of its family being at most `J₀`. They are for the boxes that the tuples
  of a reversed term fall into once the primes of its cofactor are written out and the tuple is sorted, which are
  not boxes of the search's lists (`SieveAd.evJ_fam_fill_at`, `SieveAd.evJ_fam_two_at`).
- `SieveAd.evJ_famSet_at` (`lib/pnt/SieveAdFamSet.lean`), **the terms at a floor of a family of tuples of
  distinct primes, in any order.** A family cut out by atoms (`SieveDecomp.famSet`), with no order between its
  primes and no cell for some of them, is still a union of boxes: each of its tuples of distinct primes lies in
  the box of the cells of side `1/DEN` that hold its primes (`SieveAd.ucell`, `SieveAd.ubox`), in the one order in
  which it decreases, and the atoms pass to that order (`SieveDecomp.Atom.perm`, a case of the atom carried along
  an embedding of the indices, `SieveDecomp.Atom.emb`). So the terms at a floor of the injective tuples of the
  family are the sum over those boxes and the orders of the boxes' terms under the atoms
  (`SieveAd.famJ_famSet_inj`), and they are evaluated as soon as every box that holds a tuple is, by a finite
  union.
- `SieveAd.evJ_fam_fill_at`, `SieveAd.evJ_fam_two_at` (`lib/pnt/SieveAdFamCore.lean`), **the two comparisons at a
  floor for a family of tuples of distinct primes, on bounds for its products.** If at a large modulus every
  injective tuple of a family of at most `m` atoms on `K` indices has its entries in `[x^{f/DEN}, x)`, its
  product over a set `S₀` of indices in `[x^{lo₀/DEN}, x^{hi₀/DEN}]`, and its products over `S₁` and over the
  other indices at most `x^{hi₁/DEN}` and `x^{hi₂/DEN}` (for the second comparison also its product over a set
  `Sr`, disjoint from `S₀`, in `[x^{ρlo/DEN}, x^{ρhi/DEN}]` with `ρlo > 0`), and the exponents pass `coreJ3`
  (`coreJ2`) with `Kb ≥ K` cells of room, as `lo₀ − Kb`, `hi₀ + Kb`, `hi₁ + Kb`, `hi₂ + Kb`, then the terms at
  the floor of the injective tuples of the family are evaluated. The room is what the cells of side `1/DEN` lose:
  a product in `[x^{lo/DEN}, x^{hi/DEN}]` over a set puts the sum of the lower ends of its primes' cells in
  `[lo − K, hi]` and of the upper ends in `[lo, hi + K]` (`SieveAd.sumsOK_ucell`), and the bounds pass to the
  sorted box with the sets carried by the order (`SieveAd.sumsOK_perm`).
- `SieveAd.evIF_frozS_at`, `SieveAd.evJF_frozS_at` (`lib/pnt/SieveAdFrozP.lean`), **the frozen part of a
  reversal as tuples of primes.** The frozen part `SieveAd.frozS` is the pairs of a tuple `a` of the box `βx` and
  a cofactor `m`, rough at the last prime of `a`, with `∏a·m` in a slab. For `e₂ ≤ DEN` and
  `(T + 1)·lo_s ≥ DEN + 1`, a sum over it of a function of `∏a·m` is the sum over `t ≤ T` of the sums over
  `SieveAd.frozP … t`, the tuples of `s + 1 + t` primes whose first `s + 1` are a tuple of `βx`, whose last `t`
  do not increase and are at least the last of the first, and whose product is in the slab
  (`SieveAd.sum_frozS_eq`, from `SieveChain.sum_rough_tuples`). So the terms of a chain's box over the frozen
  part, and its terms at a floor, are evaluated when those over each `frozP … t` are.
- `SieveAd.evJF_frozP_at` (`lib/pnt/SieveAdFrozJ.lean`), **the terms at a floor over the frozen part, as a
  family of tuples of distinct primes.** For a floor `f` at most the lower ends of the last cell of `βx` and of
  the chain's cells, the frozen number `R` is rough at the floor, so `n/R` is rough there exactly when `n` is
  (`SieveAd.rough_div_iff`), and the terms at the floor over `frozP … t` are a sum over tuples `w = (a, y, c)` of
  primes of the `n` that `∏w` divides and that are rough at the floor (`SieveAd.dJF_frozP_eq`). The tuples of
  distinct primes are the injective tuples of a family of atoms (`SieveAd.frozE`, `SieveAd.frozW_inj_eq`): `a`
  and `c` in their cells and decreasing, `y` decreasing and above the last prime of `a`, the product of `a` and
  `y` in the slab. The others have a repeated prime, whose square divides `n`: they number at most
  `(DEN + 1)^K` for each `n` (`SieveAd.card_tuples_dvd_le`), and the `n` that the square of a prime above the
  floor divides weigh little in `𝒜` (`SieveAd.sq_small`) and in the comparison set (`SieveAd.sq_small_B`). So the
  terms are evaluated when the family's are.
- `SieveAd.evJF_froz_fill_at`, `SieveAd.evJF_froz_two_at` (`lib/pnt/SieveAdFrozRole.lean`), **the two comparisons
  at a floor over the frozen part, on the cells and the slab.** A set of the indices of a tuple `(a, y, c)` made of
  a set `A` of `a`, all of `y` or none, and a set `C` of `c` (`SieveAd.roleSet`) has its product in
  `[x^{loRole/DEN}, x^{hiRole/DEN}]` (`SieveAd.role_bounds`): without the cofactor the sums of the lower and upper
  ends over `A` and `C`; with it `e₁ − Σ_{a ∉ A} hi + Σ_C lo` and `e₂ − Σ_{a ∉ A} lo + Σ_C hi`, the cofactor's
  primes together being the slab over the rest of `a`. So, for cells with `f ≤ lo` and ends at most `DEN`,
  `0 < f ≤ DEN`, `e₁, e₂ ≤ DEN` and `(T + 1)·lo_s ≥ DEN + 1`: if the exponents of the role sets (the set that
  enters the window, the first side of the leaves and the other side; for the second comparison also the rest's
  set, disjoint from the first, with a positive lower bound) pass `coreJ3` (`coreJ2`) at the floor with
  `Kb ≥ s + 1 + T + k` cells of room, the terms at the floor `x^{f/DEN}` of the chain's box over the frozen part
  are evaluated (`SieveAd.EvJF` for `SieveAd.frozS`). This is the second of the two evaluations that the tree
  over the frozen part asks for (`SieveAd.SoundF`), on finite sets of indices.
- `SieveAd.full2_core_at` (`lib/pnt/SieveAdFull.lean`; the checks are `lib/pnt/SieveAdFullDefs.lean`'s, without
  Mathlib), **the estimate in two variables on tuples of primes with a given product, in no order.**
  `SieveTwoTerm.chain2_bound` bounds the term of a family of strictly decreasing chains by writing each
  multiple's cofactor out as its primes and applying `SieveTwoChain.chain_two` to the full tuples; `chain_two`
  asks for no order, so the bound holds for any family of `K`-tuples of primes cut out by comparisons whose
  product lies in `(N₁, N₂]`, with a first variable `∏_S z` and a rest `∏_{Sr} z` in ranges, `S` and `Sr ≠ ∅`
  disjoint (`SieveAd.full2_bound`, `SieveAd.full2_exp`). For the region `Zone7d`, entries at least `x^{1/DEN}`
  and exponents `u ≤ v`, `ρ₁ ≤ ρ₂` in units of `1/DEN` that pass the six inequalities of `SieveAd.coreI2` (those
  of `chkI2`, on numbers): the sum over the family of `1[∏z ≡ a] − 1[(∏z, q) = 1]/φ(q)` is at most
  `q^{L−δ}/φ(q)` in absolute value.
- `SieveAd.evIF_froz_two_at` (`lib/pnt/SieveAdFrozI.lean`), **the term of a chain's box over the frozen part,
  by the estimate in two variables.** The term is a sum over a frozen number `R`, a chain `c` of primes of `n/R`
  and the `n` with `R·∏c ∣ n` and `n/R` rough at the last prime of the chain. The multiples are `R·∏c·k` with `k`
  rough at that prime (`SieveAd.sum_mult_froz`), and `k` is written out as its primes: so the term over
  `frozP … t` is a sum over the tuples (primes of `r'`, of its cofactor, of the chain, of the chain's cofactor)
  with product in `(N₁, N₂]` (`SieveAd.dIF_frozP_eq`), which are the family of the comparisons
  `SieveChain.fullTL` of those of `frozW` (`SieveAd.frozΩ`, `SieveAd.frozW_eq_RTg`: the atoms `SieveAd.frozA`
  and the non-strict order of the cofactor's primes): the chain is last, so the chain's cofactor lies above the
  tuple's last entry, as `fullTL` has it. For cells with `1 ≤ lo ≤ hi ≤ DEN` and `e₁ ≤ e₂ ≤ DEN`: if the
  exponents (`SieveAd.loRole`, `SieveAd.hiRole`) of two disjoint role sets, the first variable's and the rest's,
  the rest's with a positive lower bound, pass `coreI2`, the term of the chain's box over the frozen part is
  evaluated (`SieveAd.EvIF` for `SieveAd.frozS`). This is the first of the two evaluations of `SieveAd.SoundF`.
- `SieveAd.frozTests_sound_at` (`lib/pnt/SieveAdFrozTests.lean`; the tests are `lib/pnt/SieveAdFrozDefs.lean`'s,
  without Mathlib), **the tests of the tree over the frozen part are sound.** The tree over the frozen part reads
  a box `ch ++ β`, the chain's cells and then those of `r'`. A configuration gives its sets by the bits of
  numbers: the low bits for the cells of `ch`, the next for those of `β`, and the bit after them for the
  cofactor. `SieveAd.frozTests e₁ e₂ Kb β` tests the term of the chain's box by `coreI2` on the exponents of the
  first variable's set and the rest's (`okIF`), and its terms at a floor by `coreJ3` (`okJF3`, the rest among the
  tree's primes) or `coreJ2` (`okJF2`, among the tuple's), on the exponents with `Kb` cells of room
  (`SieveAd.loR`, `SieveAd.hiR`, `SieveAd.hiRc`: sums of the ends of the cells over the bits, and for a set with
  the cofactor the slab less the cells of `β` outside it). For `e₁ ≤ e₂ ≤ DEN`, `(T + 1)·lo_s ≥ DEN + 1` and
  `Kb ≥ 12 + T`, a test that passes a box of at most twelve cells evaluates the term of the chain over
  `SieveAd.frozS`, or its terms at the floor: `SieveAd.SoundF`, the hypothesis of `SieveAd.frozSolve_sound_at`.
  So the search of `SieveAdRevDefs.lean` with these tests bounds the term of a chain of one prime over the frozen
  part, which is what `SieveAd.bd_flip_neg_at` and `SieveAd.bd_flip_pos_at` ask for.
- `SieveAd.pr_of_kidsF_at` (`lib/pnt/SieveAdFlipSearch.lean`; the definitions are `lib/pnt/SieveAdFlipDefs.lean`'s,
  without Mathlib), **the search with the reversal of a box through its largest prime is sound.**
  `SieveAd.opsF` is the nodes of `SieveAd.opsR` with one more bound for a box of the sign `−` that passes
  `SieveAd.flipOK`: two to `maxlen ≤ 11` cells with `0 < lo < hi` and upper ends of sum at most `DEN − 2`, the
  largest prime's cell `(l₁, h₁)` above the others (`h₂ + 1 ≤ l₁`) with `l₁ ≥ 3`, and the level `t = ⌈h₁/2⌉` with `t ≤ l₁` and
  `h₁ + t + 1 ≤ DEN`. The bound is `SieveAd.flipCost`, `⌈(c(h₁D₀ + E) + bdK·E)/(DEN·K)⌉`: `c` is the cost of the
  tree over the frozen part (`SieveAd.flipTree`: the first floor `f ≤ min(lo_s, t)` at which
  `SieveAd.frozTests` evaluates the terms of the frozen part, then the search of `SieveAdRevDefs.lean` on the
  chain's prime from `f` to `t` with those tests, by a strategy given for the box), `D₀` is the box's
  `dropCost`, `E = (h₁ + 1)D₁ + (l₁ + 1)D₂` with `D₁`, `D₂` the `dropCost` of the box with the largest prime's
  cell replaced by `(h₁ − 1, h₁ + 1)` and by `(l₁ − 1, l₁ + 1)`, and `bdK` is Buchstab's bound at the level `t`.
  The tree is searched with the limit past which the bound is not below the box's other bound, so a reversal
  that loses stops early.
  A cost below the limit bounds the term of the box (`SieveAd.bd_flipCost`, by `SieveAd.bd_flip_core`): it is
  `SieveAd.bd_flip_neg_at` with the tree's bound (the frozen part's rules `SieveAd.frozRules` and
  `SieveAd.frozTests_sound_at`), the terms at the root's floor from the test that passed, and the weights of
  the frozen part and of its two ends from the shares of the three boxes (`SieveAd.froz_weight_le_at`). So the search with these nodes is sound for any strategies
  (`SieveAd.solveF2_sound`), and a part of it as the kernel checks it gives the bound for its range, in the form
  of `SieveAd.pr_of_kids`.
- `Linnik21650.flip_box_21650` (`lib/pnt/SieveFlipBox21650.lean`; the part is `lib/pnt/SieveFlipPart21650.lean`'s
  and the strategies `lib/pnt/SieveAdFlipStratDefs.lean`'s, both without Mathlib), **a bound by the search with
  the reversal through the largest prime**, at `L = 2165/1000`: for `p₁` between `x^{0.4237}` and `x^{0.4287}`
  and `p₂` between `x^{0.2687}` and `x^{0.2737}`, the term of the box `(p₁, p₂)`, of the sign `+`, is at least
  its count in the comparison set less `(c/K + o(1))x/(φ(q) log x)` with `c = 0.000501·K`, where the search of
  the theorem at `2165/1000` drops the box, at `0.000734·K`. The strategies: `SieveAd.stratFF` for a tree over a
  frozen part proposes the sets of the tests on the box with the cofactor as one more cell (`SieveAd.vboxF`),
  widened by the tests' room for the floors (`SieveAd.propIF`, `SieveAd.propJFF`), and cuts the chain's first
  prime from the level down; `SieveAd.stratGFF` is the theorem's strategy with one more cut of a new prime's
  range, one unit below the largest prime's cell, so that the box below the cut passes `flipOK`. The kernel
  runs the search on the box (`SieveAd.flipPart21650`, by `decide +kernel`, nineteen seconds): it takes seven
  reversals through the largest prime, of boxes of three primes, of the nineteen it tries. This is one part,
  not a certificate of the sieve: it checks the rule, its strategies and `tools/linnik/flip_cert.py`, the
  search in Python, against the kernel.
- `SieveAd.pr_of_kidsH_at` (`lib/pnt/SieveAdHint.lean`; the search is `lib/pnt/SieveAdHintDefs.lean`'s and the
  guides `lib/pnt/SieveAdHintStratDefs.lean`'s, both without Mathlib), **the search led by hints is sound.** The
  search of `SieveAdRevDefs.lean` tries at each box what its strategy proposes and keeps the cheapest; the
  kernel, running it, spends most of its time on what is not kept, and on searching every proposal of a floor
  where one is used. `SieveAd.solveH` is told what to do at each box by a number, the hints, read from its low
  end in the order of the search: a run of ones closed by a zero for the action (the box is evaluated or has no
  term; Buchstab's identity at the floor and with the configuration that a guide computes for four more bits;
  the box dropped; the bound `Ops.alt`; a bound that reads hints itself; the cell cut in two), and at each
  proposed cut of a new prime's range one bit, whether the range is cut there, so that consecutive cells that
  one test evaluates are one cell. Each step is one of the rules among which the search chooses
  (`SieveAd.Rules`), and is checked before it is used: a step whose test fails returns the limit, which says
  nothing. So for nodes that prove a statement and a hinted bound that does, a cost that `solveH` returns below
  its limit has the statement, whatever the hints and the guide (`SieveAd.solveH_sound`, from
  `SieveAd.kidsH_sound` and `SieveAd.stepH_sound`). The reversal of a box through its largest prime is such a
  hinted bound (`SieveAd.altFH`, `SieveAd.flipCostH`: the tree over the frozen part is searched by hints;
  `SieveAd.bd_flipCostH`, from `SieveAd.bd_flip_core`, the reversal's bound from the bound of any tree, which
  `SieveAd.bd_flipCost` shares), so the main search led by hints is sound (`SieveAd.solveFH_sound`), and a part
  of it as the kernel checks it gives the bound for its range. The guides (`SieveAd.guideG`, and
  `SieveAd.guideF` over a frozen part) compute one proposal of the strategy, the one that the four bits name:
  the comparison with the rest at one cell (`SieveAd.tryJ2`), or with the rest among the tree's primes at one
  of eight floors.
- `Linnik21500.linnik_21500` (`lib/pnt/Linnik21500.lean`; the parts are `lib/pnt/SieveHint21500P1.lean` and the
  files after it, without Mathlib), **Linnik's theorem with exponent `2150/1000`**: for every `q ≥ 1` and every
  `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{2150/1000}`, with no hypothesis. The route
  and the tests are those of the theorem at `2165/1000`; the search is led by hints (`SieveAd.solve21500`:
  `SieveAd.solveH` with the guides `SieveAd.guideG` and `SieveAd.guideF`), with the reversal through the
  largest prime of boxes of the sign `−` of at most six primes, that is of three and of five, as its hinted
  bound, on cells of side at most `0.004` and chains' cells of side at most `0.006` over the frozen parts. The
  bound of the first term costs `0.94847·K` (`Linnik21500.tree21500`). The hints are the plan that
  `tools/linnik/hint_cert.py` kept of its search: `3.4·10^6` steps, of which `1.6·10^5` reversals, in `1510`
  parts, where the search visited `3.4·10^7` boxes, `2.8·10^7` of them over frozen parts; the plan does not use
  the reversal of three primes of the theorem at `218/100`, which the kernel would search without hints.
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

The paper's theorem at `43/20` (`Linnik21500.linnik_21500`) uses Harman's comparison in two variables through the
tests of its trees: `SieveTwoComp.prop6_two_at` (the rest among the box's primes) for the test `okJ2`
(`SieveAd.evJ_two`), `SieveFillComp.prop6_fill_at` (the rest among the primes of the comparison's own tree) for
`okJ3` (`SieveAd.evJ_fill`), and the chains of `SieveTwoTerm.chain2_bound` for `okI2` (`SieveAd.evI_two`); the leaves
of both comparisons are evaluated on the wider region of the bilinear Type I estimate (`SieveP6LeavesWide.leavesOK_wide`).
Its earlier version, at `11/5` (`Linnik22000E.linnik_22000e`, still in the library), used it in the leaves of its
decomposition: `SieveLeaves.P6_spec` applies `prop6` to each family of at most `40` comparisons,
and `SieveLeaves.P6IB_spec` applies the form of Proposition 6 with the bilinear Type I estimate (`SieveP6ib.prop6ib`)
to the families of the boxes that the rule's bilinear test (R2) takes whole, with the
witnesses of the test (`SieveCert.ibOK_sound`) turned into its hypotheses by `SieveQ.P6IB_boxes`. The rough-number bound also gives the shares of the certificate's cells (`SieveRough.share2_of_cand`), with which
`SieveDrop` bounds the terms the decomposition drops.
