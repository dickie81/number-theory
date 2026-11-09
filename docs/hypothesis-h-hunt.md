# Hypothesis (H) hunt — short character sums at `x = q^{7/18}`

Status labels: **Dead**, **Partial**, **Promising**, **Numerical**. Prepared with AI assistance; never fabricate.
Seed: `20261109` (`scripts/hypothesis_h/seed.txt`). Shuffled openings below.
Branch: `density-exponent-hunt` / PR #98.

## Exact statement of (H)

From `docs/cgl-s3-prime-moduli.md` §8 (verbatim structure):

By orthogonality, `Σ_{χ≠χ₀} |S_I|⁶ = (q−1)J₆(I) − |I|⁶`, where
`J₆(I) = #{a₁a₂a₃ ≡ b₁b₂b₃ (mod q) : aᵢ,bᵢ ∈ I}` and `S_I(χ) = Σ_{n∈I} χ(n)`.

**(H).** There exist `η, c > 0` such that, uniformly in prime `q`, in
`x ∈ [q^{7/18−c}, q^{7/18+c}]` and in intervals `I ⊂ (x, 2x]`,

```
J₆(I) = |I|⁶/(q−1) + O(x⁶ q^{−1−η}).
```

Equivalently (exponent level): a power saving in
`#{χ ≠ χ₀ : max_{I⊂(x,2x]} |S_I(χ)| ≥ x^{5/7}}`
below `q^{2/3}` near the critical threshold.

**Payoff** (same §8): sixth-moment end → `q^{12θ/7−η}`; ends meet at
`θ = 7(1+η)/18`; near `σ=5/7` the `T=1` exponent is `≤ 7/3 − 7η/6`; against
CGL’s `4/(1+σ)` the uniform exponent at `T=1` for prime `q` is
`≤ 7/3 − η/2 + O(η²)`. Sieve floor `1+A/2` moves by `η/4`.

## Exclusion list — already tried (do not repeat)

From `docs/cgl-s3-prime-moduli.md` §§8–11 and hunt docs:

| # | What | Where | Outcome |
|---|---|---|---|
| E1 | Fourth + sixth moment meeting → `θ=7/18`, `|W|≪q^{2/3}` | §8 | Exact critical point; no saving |
| E2 | Orthogonality rewrite via `J₆` | §8 | Restates (H) |
| E3 | Lit: Ayyad–Cochrane–Zheng (4 vars); Garaev 2-interval products; 6th moment of `L(1/2,χ)` averaged over moduli | §8 | No asymptotic of form (H) at `|I|≈q^{7/18}` |
| E4 | Perron ⇒ (H) from `Σ_χ ∫_{|t|≤q^ε} |L(1/2+it,χ)|⁶ ≪ q^{7/6−η}`; Weyl×4th ⇒ only `q^{4/3}` | §8–9 | Short by `q^{1/6}` |
| E5 | `blocks.py` numerics: `[1,x]` saturates `~q^{2/3}`; dyadic milder, falling | §8 | Finite-`q`; log powers swamp savings |
| E6 | Pretentious / smooth-number heuristic for `[1,x]` vs `(x,2x]` | §8 | Heuristic only |
| E7 | Shifted ternary-divisor convolution `N(h)`, split `D+S+F` | §9 | `F` is the problem; known `d₃` averages miss sparse shifts |
| E8 | Multilinear Kloosterman / lattice lines; coeffs too big for DFI | §9 | Stall |
| E9 | Weyl+4th ⇒ (H) only for `x≥q^{4/9+ε}` | §9 | Wrong range (`4/9>7/18`) |
| E10 | Equivalent L-targets: 6th moment; twisted 2nd (len `q^{7/9}`); twisted 4th (len `q^{7/18}`) | §9 | Same obstacle |
| E11 | Bettin–Chandee trilinear: saving `x^{1/4}=q^{0.097}` vs needed `q^{0.389}` | §10 | Far short |
| E12 | Conjectural large-sieve-type for the form ⇒ (H) for `θ>1/3` | §10 | Conjecture, not proved |
| E13 | Kuznetsov / Deshouillers–Iwaniec over moduli `b₂b₃` | §11 | Worse than trivial; needs Linnik–Selberg beyond Kim–Sarnak |
| E14 | Direct `S₃` / Schatten / Bohr / weighted energy (§§2–7) | cgl-s3 | **Other end** of critical point (4th-moment / length `q^{7/9}`) |
| E15 | ADV-realisability / restricted LV at `N=q^{7/9}` | ingredient-hunt | Retracted for Thm 1.3; residual is exactly (H) |
| E16 | Completing at `N=q^{7/9}` / PV toy | loophole_verify | Wrong length for the `T=1` detector |

## Shuffled openings (seed `20261109`)

Order produced by `random.seed(20261109)` over the 18 names in
`scripts/hypothesis_h/` setup.

### 01 `montgomery_vaughan_moments` — Dead (for beating 2/3)

**Idea.** Use classical MV mean values / high even moments of short character sums.
**Bookkeeping.** `Σ_χ |S_I|^{2k} ≪ (q+x^k) x^k (log)^C` ⇒
`|W| ≪ q^{1−k/6} + q^{2k/9}` at `θ=7/18`, `σ=5/7`
(`scripts/hypothesis_h/moments_bookkeeping.py`).
**Verdict: Dead.** `k=2` and `k=3` both give exactly `q^{2/3}`; for `k≥4` the `x^k` term
dominates and is **worse**. No moment order beats `2/3` without a saving in `J_{2k}`.

### 02 `smoothing_vs_sharp_cutoff` — Dead as a new route

**Idea.** Replace sharp `1_I` by a smooth weight of width `x` to gain Poisson / completion.
**Bookkeeping.** CGL’s detector already has smooth weights after partial summation (§8
reduction); the library’s `LinnikCGLStep` likewise. Smoothing is already built into the
route that produces (H).
**Verdict: Dead** for a new saving. Does not change the congruence-count obstacle.

### 03 `paley_obstruction_test` — Partial (no obstruction to (H))

**Idea.** Paley-type quadratic constructions that force many large short sums.
**Bookkeeping / numerics.** Random model: `E[|S|²]=x`, Gaussian tail
`P(|S|≥V)≈exp(−V²/x)` with `V²/x = x^{3/7} = q^{1/6}` → expected count
`≪ q^{2/3}` **exponentially** for large `q` (at `q=10^6` already ratio `~10^{-3}`; at
`q=10^9` negligible). Paley / GS large sums of size `√q log log q` are for **long**
sums (`x∼q`), not `x=q^{7/18}`. At short length the typical size is `√x = q^{7/36}≈q^{0.194} ≪ V=q^{5/18}`.
**Verdict: Partial / no obstruction.** Paley does **not** force `|W|≫q^{2/3}` at this
length. Consistent with (H) being plausible; does not prove it.

### 04 `polya_vinogradov_dual_short` — Dead

**Idea.** Complete the sum; dual length `q/x = q^{11/18} > √q`; apply PV / Weil on the dual.
**Bookkeeping.** Completing always gives `|S_I| ≪ √q log q` (PV), exponent `1/2 > 5/18`,
so does **not** forbid `|S|≥V`. Dual short-sum technology at length `q^{11/18}` is still
in the complete-sum regime; no gain on the count below `q^{2/3}` beyond the fourth-moment
bound already used.
**Verdict: Dead** for beating `2/3` at `θ=7/18`.

### 05 `heath_brown_chang_energy` — Dead (wrong target / wrong range)

**Idea.** Heath-Brown–Chang multiplicative energy bounds inside Burgess amplification.
**Bookkeeping.** Those methods improve **individual** short sums (or sums over forms /
boxes) toward the Burgess threshold `q^{1/4+ε}`, or give mean values over **spaced
starting points for one χ** (HB arXiv:1203.5219). They do not produce a power saving in
`#{χ mod q : |S_I(χ)|≥x^{5/7}}` at fixed `I` of length `q^{7/18}`.
**Verdict: Dead** as a plug-in to (H). Energy estimates are ingredients for pointwise
bounds already weaker than the moment count at this length (see Burgess opening).

### 06 `dyadic_vs_initial_segment` — Numerical / already recorded

**Idea.** Exploit that the detector uses `(x,2x]`, not `[1,x]`.
**Numerics** (`short_sum_counts.py`, primes to `10^5`):

| `q` | `[1,x]/q^{2/3}` | `(x,2x]/q^{2/3}` | `M6/L^6` dyadic |
|---|---|---|---|
| 503 | 0.78 | 0.44 | 1.72 |
| 10007 | 0.92 | 0.35 | 1.60 |
| 100003 | 1.04 | 0.32 | 1.64 |

Log-log fit `count ∼ q^α`: `[1,x]` α=`0.725±0.006` **above** `2/3`; dyadic
α=`0.630±0.025` **mildly below** `2/3`, pairwise locals `0.19–0.77` (unstable at small `q`).
Matches `cgl-s3` §8 table (dyadic falling, local ~`0.59` out to `3·10^7`).
**Verdict: Numerical only.** Weak evidence for (H) on dyadic blocks; finite-`q` / log
powers (E5) still apply. **Not a proof.** Already in exclusion E5–E6; no new theorem.

### 07 `cilleruelo_garaev_products` — Dead / short of range

**Idea.** Cilleruelo–Garaev bounds on products from short intervals / congruence
`a₁⋯a_k ≡ b₁⋯b_k (mod q)`.
**Bookkeeping.** Garaev-type results control products of **two** short intervals, or need
longer intervals than `q^{7/18}` for a power-saving equidistribution of **triple** products.
§8 already cites Garaev as nearest but insufficient (E3). At `x³ = q^{7/6}` the trivial
diagonal dominates; saving in `J₆` is exactly (H).
**Verdict: Dead** for a proved η at `θ=7/18`.

### 08 `moment_k4_eightfold` — Dead

**Idea.** Eighth moment `Σ |S|⁸` / eightfold congruence count.
**Bookkeeping.** `k=4`: `|W| ≪ q^{1/3} + q^{8/9} = q^{8/9} > q^{2/3}` (MVT family).
**Verdict: Dead.** Strictly worse than sixth moment at this `θ`.

### 09 `burgess_counting_LV` — Dead (individual bound misses V)

**Idea.** Burgess pointwise + convert to a large-values count.
**Bookkeeping.** Classical Burgess (Form B):
`|S| ≪ N^{1−1/r} q^{(r+1)/(4r²)+ε}`. At `N=q^{7/18}`, for all `r=2..8` the exponent is
`≥ 0.37 > Vexp=5/18≈0.278` (`moments_bookkeeping.py`). So Burgess does **not** put
every `|S|<V`. A markov/counting upgrade of Burgess moments over χ is not available as a
theorem beating the plain 4th/6th moment meeting (HB’s Burgess LV is over starting points,
not over χ).
**Verdict: Dead** for `|W|≪q^{2/3−η}`.

### 10 `granville_sound_pretentious_LD` — Partial (heuristic / reformulation)

**Idea.** GS: unusually large character sums come from χ pretending to a small-conductor
character; at prime `q` the only small-conductor target is `χ₀`, and few χ are pretentious
to 1 on `p≤y`.
**Bookkeeping.** Matches §8 pretentious heuristic (E6): the `[1,x]` excess is smooth /
pretentious; dyadic has far fewer smooth integers. To turn this into `|W|≪q^{2/3−η}` one
must still bound the **non-pretentious** contribution — essentially (H) or the missing
sixth moment of `L(1/2,χ)` on one modulus (E4, E10).
**Verdict: Partial.** Best structural description of the excess; **not** a proof of (H).

### 11 `lattice_point_triple_products` — Dead (restates §9–10)

**Idea.** Geometry of numbers on `a₁a₂a₃ − b₁b₂b₃ = kq`, `|k|≤K≍q^{1/6}`.
**Bookkeeping.** Exactly the §9–10 reduction (E7–E8, E11–E13). Lattice-point counting
without new cancellation returns the trivial / Bettin–Chandee range.
**Verdict: Dead** as a fresh opening; already exhausted in cgl-s3.

### 12 `moment_k3_J6_geometry` — Partial = (H) itself

**Idea.** Prove the geometric count `J₆` with power saving by lattice / energy methods.
**Bookkeeping.** This **is** (H). Known tools give (H) for `x≥q^{4/9+ε}` (E9) or saving
`q^{0.097}` via Bettin–Chandee (E11), not `η>0` at `q^{7/18}`.
**Verdict: Partial** — the problem statement, not a solution.

### 13 `chang_multiplicative_energy` — Dead (range)

**Idea.** Chang energy `E_×(B,B) ≪ |B|^{11/4}` etc. inside Burgess.
**Bookkeeping.** Yields nontrivial individual bounds for boxes / short sums near
`q^{2/5}` or Burgess `q^{1/4}`; at length `q^{7/18}` individual bounds still sit above `V`
(opening 09). Does not count many χ.
**Verdict: Dead** for (H).

### 14 `bourgain_konyagin_shparlinski` — Dead / short

**Idea.** BKS sum-product / exponential sum estimates over F_q for short interval structure.
**Bookkeeping.** Strong for very short sets or for `|Σ χ(n) e(an)|` hybrids; for plain
`Σ_{n∈I} χ(n)` at `|I|=q^{7/18}` they do not beat the sixth-moment MVT count.
**Verdict: Dead** for a proved η here.

### 15 `bourgain_garaev_energy` — Dead / short

**Idea.** Bourgain–Garaev multiplicative energy of intervals in F_p.
**Bookkeeping.** Improves energy of intervals beyond trivial in some ranges; feeding into
a χ-large-values inequality at `V=x^{5/7}` still fails to beat `q^{2/3}` with published
exponents at `θ=7/18` (same barrier as E3, E11).
**Verdict: Dead** for (H) as stated.

### 16 `high_moment_k5_plus` — Dead

**Idea.** Moments `2k≥10`.
**Bookkeeping.** `k≥5`: `|W| ≪ q^{2k/9}` with `2k/9 ≥ 10/9 > 1`. Useless.
**Verdict: Dead.**

### 17 `heath_brown_burgess_LV` — Dead (different average)

**Idea.** Heath-Brown’s large-values theorem for character sums (moments of
`max_h |S(N_j; h)|` over spaced `N_j`).
**Bookkeeping.** Controls many **intervals** for one (or few) χ, not many χ for one
interval. Dual to what (H) needs.
**Verdict: Dead** as a transfer into (H).

### 18 `moment_k2_congruence_count` — Dead (already sharp)

**Idea.** Exact fourth-moment congruence `ab≡cd (mod q)` at `x²=q^{7/9}<q`.
**Bookkeeping.** Gives `|W|≪ q^{1−6θ/7} = q^{2/3}` exactly at `θ=7/18` (E1). Geometry of
numbers on 4-fold products is classical (`E₄≍x² log x`); no further power saving available
without changing `θ`.
**Verdict: Dead** for η>0; this is the fourth-moment end of the meeting.

## Numerics summary

Script: `scripts/hypothesis_h/short_sum_counts.py` (FFT via discrete log; E₄ exact).

- Primes `q ≤ 10^5`: dyadic count ratio falls slowly (`0.44 → 0.32`); fitted α≈`0.63±0.03`.
- `[1,x]` ratio rises (`0.78 → 1.04`); α≈`0.73`.
- `M₄/((q−1)E₄) → 1` as expected (orthogonality).
- `M₆/L⁶` dyadic stays `~1.6` (above 1); no asymptotic visible at these `q`.
- Larger-`q` table already in `cgl-s3` §8 (`blocks.py` to `3·10^7`): dyadic ratio
  `0.32 → 0.20`, local exponent ~`0.59` — still not a proof, log powers dominate
  any `δ≤1/26` saving at these sizes.

**No rigorous η>0 extracted from numerics.**

## Rigorous partials?

**None that beat `2/3` and transfer into the `T=1` density exponent.**

Closest rigorous facts (already in cgl-s3, reconfirmed):
1. Moment family optimal at `k=2,3` with exponent exactly `2/3` at `θ=7/18`.
2. Burgess individual misses `V`.
3. (H) known for `x≥q^{4/9+ε}` (Weyl×4th) — wrong range.
4. Bettin–Chandee saving `q^{0.097}` on the trilinear form — short of `q^{0.389}`.

No call to `price.py` / `density_payoff.py` for a new `A` or `L`: there is no proved η.

## Live status of (H)

| Claim | Status |
|---|---|
| (H) as stated | **Open** (Partial) |
| Any opening here proves η>0 at `θ=7/18` | **No** |
| Numerics suggest dyadic mildness | **Yes**, weak / finite-`q` |
| Obstruction to (H) from Paley/ADV/moments | **No obstruction found** |
| Next genuine targets (unchanged) | Prove power saving in `J₆` / single-modulus 6th moment of `L` / twisted moments (E4, E10, E12) |

**No improvement of `A` or Linnik `L`.**
