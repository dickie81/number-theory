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


---

## Deep dive: anatomy of `J₆`, LoD/`Kl₃`, pretentious dyadic gap (2026-11-09)

Continues past the exclusion list and the 18 openings. Does **not** repeat Bettin–Chandee,
Kuznetsov, or the §9 `D+S+F` shifted-`d₃` average over sparse `kq` as a claimed solution.
New framing: level of distribution for the **restricted** ternary divisor `r₃^I`, plus
exact `k`-decomposition numerics, plus the range of pretentious theorems for the dyadic gap.

Scripts: `j6_anatomy_bookkeeping.py`, `j6_k_decompose.py`.

### A. Anatomy of `J₆(I)`

Let `I ⊂ (x,2x]` (or `[1,x]`), `x = q^{7/18}`, `X = x³ = q^{7/6}`, and
`r₃(n) = #{(a,b,c) ∈ I³ : abc = n}`. Then

```
J₆(I) = Σ_{|k|≤K} N(kq),     N(h) = Σ_m r₃(m) r₃(m+h),
K = ⌊(max I³ − min I³)/q⌋ ≍ q^{1/6}.
```

| Piece | What | Size vs main `|I|⁶/q = q^{4/3}` |
|---|---|---|
| `k = 0` | Integer equality `abc = def` (diagonal `E₆`) | `N(0) ≍ x³ (log x)^{c}` with `c = (3−1)² = 4` (Conrey–Gamburd); ratio to main `≍ q^{−1/6}(log)^{c}` — **power below** main asymptotically |
| `0 < \|k\| ≤ K` | `abc − def = kq` (small multiples) | Carry the singular series + error; their average manufactures the main term |
| Main term | Equidistribution: `|I|³` products among `q` classes ⇒ `J₆ ∼ \|I|⁶/q` | Equivalent: `J₆ = \|I|⁶/(q−1) + error` is (H) |

**(H) needs** error `O(x⁶ q^{−1−η}) = O(q^{4/3−η})`. Asymptotically the diagonal alone is
`O(q^{7/6}(log)^{c}) = O(q^{4/3−1/6}(log)^{c})`, so it is **not** the asymptotic obstacle —
the obstacle is the average of `N(kq) − (singular series)` over the `K ≍ q^{1/6}` nonzero shifts
(the `F` of `cgl-s3` §9). At reachable `q` the opposite is visible (next subsection).

### B. Level-of-distribution angle (genuinely different framing)

**Need.** Equidistribution of `{abc : a,b,c ∈ I}` among residue classes mod `q`, with
`X = q^{7/6}` products. That is LoD for `r₃^I` at level

```
θ_LoD = log q / log X = 6/7 ≈ 0.857.
```

**What was excluded in §9.** Sparse shifted-convolution averages of unrestricted / box-`d₃`
over shifts `h = kq` spaced `q` apart (no dense interval of `h`); then Bettin–Chandee /
Kuznetsov after Poisson. Those do not claim an LoD theorem for `r₃^I`.

**What the LoD literature gives for unrestricted `d₃`.**

| Source | Level (prime moduli where noted) |
|---|---|
| Friedlander–Iwaniec | `1/2 + 1/230` |
| Heath-Brown | `1/2 + 1/82` |
| Fouvry–Kowalski–Michel | `1/2 + 1/46` (primes); `1/2 + 1/34` avg residue |

All `≪ 6/7` (shortfall `≳ 0.33`). These use Deligne on auxiliary Friedlander–Iwaniec /
hyper-Kloosterman correlation sums to break the large-sieve `1/2` barrier — they do **not**
reach level `2/3`, let alone `6/7`.

**Short-interval structure + incomplete geometric sums.**
`S(r) = Σ_{n₁,n₂,n₃ ∈ I} e(r n₁n₂n₃/q)`. Summing `n₃` first:

```
|S(r)| ≪_ε x³/q + x² = q^{1/6} + q^{7/9}   (dominant q^{7/9}).
```

Parseval: `Σ_a E_a² = q^{−1} Σ_{r≠0} |S(r)|² ≪ q^{14/9}`, against need `q^{4/3}` — short by
`q^{2/9}`. Level reachable with `|S| ≪ Y²` alone: `Q ≤ Y² = X^{2/3}`, i.e. **level `≤ 2/3 < 6/7`**.
Gap: `6/7 − 2/3 = 4/21`. To hit level `6/7` one needs RMS `|S| ≪ q^{2/3}`, i.e. an extra
saving `q^{1/9}` beyond the geometric bound.

**Deligne / `Kl₃` after three Poisson summations.** Dual length `M = q/x = q^{11/18}`.
Normalized `|Kl₃(a;q)| ≤ 2` (Deligne). Crude insertion over all `M³` dual frequencies gives
`|S| ≪ q`, **worse** than the geometric `q^{7/9}`. Random-model dual cancellation would give
`|S| ≪ x^{3/2}/q^{1/2} = q^{1/12}` and prove (H) amply — **unproved**. Published FI/HB/FKM
savings that use Deligne stop near level `1/2+`. Short dyadic factors are already fully used
in the geometric bound; they do not upgrade LoD from `2/3` to `6/7`.

**Averaging over the `q^{1/6}` shifts `k`.** This average **is** `J₆` itself (equidistribution
variance). It is not the dense-interval average supplied by Matomäki–Radziwiłł–Tao /
Baier–Browning–Marasingha–Zhao. Spacing `q = X^{6/7}` is too large for those theorems
(already in §9). LoD framing does not remove the sparsity.

**Verdict on the LoD/`Kl₃` angle: Dead** as a proof of (H). Precise obstruction: need level
`6/7`; short-interval technology reaches `≤ 2/3`; Deligne does not close `4/21` without
unproved dual square-root cancellation.

### C. Numerics: which `k` carries the excess?

`j6_k_decompose.py` (FFT autocorrelation of `r₃` on `I = (x,2x]`):

| `q` | `(J₆−main)/main` | `N(0)/main` | diagonal share of excess | small-`|k|` mean `2N/main` |
|---|---|---|---|---|
| 503 | +1.72 | 2.35 | ~79% | 0.048 |
| 10007 | +1.60 | 2.03 | ~64% | 0.041 |
| 30011 | +1.65 | 2.02 | ~62% | 0.039 |
| 100003 | +1.64 | 2.00 | ~61% | (same pattern) |

- **At all reachable `q`, the `k=0` diagonal dominates the visible excess** (`N(0) ≈ 2 · main`).
  Asymptotically `N(0)/main ≍ q^{−1/6}(log x)^4 → 0` only near `q ≈ 10^{27}` (`cgl-s3` §8).
- Nonzero-`k` mass concentrates on **small** `|k|` (first third of `1..K`); large `|k|` are
  negligible. After signature-matching (`shifts.py`, §9) most of that mass is singular series,
  leaving `F ≈ −0.08 · main` — small, slowly drifting.
- For `[1,x]`: `N(0)/main ≈ 4–7.6` (much larger diagonal from smooth / highly composite
  products); matches the larger character-count ratios.

**Obstacle localization.**
- *Numerically (finite `q`):* `k=0` diagonal log-powers — not a disproof of (H).
- *Asymptotically (for a proof of (H)):* still the nonzero-`k` error `F` / LoD failure at level
  `6/7` (same wall as §9–11 and subsection B).

### D. Dyadic vs `[1,x]` gap and pretentious theorems

**Empirical gap** (`short_sum_counts.py` / `cgl-s3` §8): count `/ q^{2/3}` is `~1.0–1.4` on
`[1,x]` vs `~0.2–0.3` on `(x,2x]`; fitted α `≈ 0.73` vs `≈ 0.63`.

**Rigorous explanation of the mechanism (not yet a power saving).**
Characters pretentious to `χ₀` on small primes (`χ(p) ≈ 1` for `p ≤ y`) satisfy
`S_I(χ) ≈ Σ_{n∈I, y-smooth} 1`. The smooth mass in `[1,x]` includes all of `Ψ(x,y)`, while
`(x,2x]` only sees the thin top slice; small `n` with `χ(n) = 1` exactly feed `[1,x]` and not
the dyadic block. This is the `cgl-s3` §8 pretentious heuristic, confirmed by the diagonal
gap in subsection C (`N(0)/main` several times larger on `[1,x]`).

**Can pretentious theorems make the dyadic case rigorous?**

| Tool | Range | Applies at `x=q^{7/18}`? |
|---|---|---|
| Granville–Soundararajan pretentious structure | Large `M(χ) = max_{N≤q} |Σ_{n≤N} χ(n)|` near `√q` scale | **No** — long sums, not length `q^{7/18}` |
| Bober–Goldmakher–Granville–Koukoulopoulos | Distribution of `M(χ)/√q` | **No** — same long-sum maximum |
| Short-sum Gaussian (e.g. arXiv:1106.6072) | `Σ_{x<n≤x+H} χ(n)` as `x` varies, needs `log H = o(log q)` | **No** — `H = q^{7/18}` has `log H ≍ log q` |
| Halász-type mean values for pretentious distance | Typically averages of `|Σ_{n≤x} f(n)|` for multiplicative `f` | Gives structure, not a proved `#{χ : |S_{(x,2x]}| ≥ x^{5/7}} ≪ q^{2/3−η}` |

**Verdict.** The dyadic restriction **does** kill the main pretentious contribution
heuristically (and numerically), but **no published pretentious / Halász theorem applies at
length `q^{7/18}`** to turn that into a power saving. Making it rigorous remains open and is
essentially a form of (H) for dyadic intervals (the detector's case).

### E. Rigorous partials from this dive?

| Claim | Status |
|---|---|
| Diagonal `N(0)` is `o(main)` by a power `q^{−1/6}` (up to logs) | **Yes** (standard `E₆ ≍ x³(log)^4`) — not new; does not give (H) |
| LoD for `r₃^I` at level `6/7` via geometric + Deligne | **No** — reaches at most level `2/3` |
| Dyadic pretentious saving with η>0 | **No** — out of range of GS/BGGK/short-Gaussian |
| Full (H) | **Still open** |

No η>0 proved. No call to price/`density_payoff` for a new `A` or `L`.

### Updated live status

| Angle | Status after deep dive |
|---|---|
| LoD / `Kl₃` / short-factor `d₃` in APs | **Dead** (need `6/7`, have `≤2/3` or `~1/2+`) |
| `k`-decomposition obstacle | Finite-`q`: diagonal; asymptotic: still `F` / LoD |
| Pretentious dyadic rigorization | **Partial** heuristic; theorems miss the range |
| (H) itself | **Open** |
| Trilinear `S(r)` / BGK / PS for `q^{1/9}` | **Dead** (see next section): average circular; explicit bounds miss; BGK non-explicit |


---

## Attack on the `q^{1/9}` gap in `S(r)` (2026-11-09)

Target: beat the incomplete-geometric bound `|S(r)| ≪ x³/q + x²` by an extra `q^{1/9}`
(pointwise or on an exceptional-set of `r`) so that LoD for `r₃^I` reaches level `6/7`.
Does **not** repeat LoD literature survey, Bettin–Chandee, Kuznetsov, or `D+S+F`.

Script: `scripts/hypothesis_h/trilinear_S.py`.

### (a) Explicit `S(r)` and circularity of averaging

**Definition.** For `I = (x, 2x]`, `x = q^{7/18}`, and `r ∈ F_q`,

```
S(r) = Σ_{n₁,n₂,n₃ ∈ I} e(r n₁ n₂ n₃ / q).
```

(`r = 0` gives `|I|³`. The LoD error uses `r ≠ 0`.) Equivalently, writing `m = n₁n₂` and
`r₂(m) = #{(n₁,n₂)∈I² : n₁n₂ = m}`,

```
S(r) = Σ_m r₂(m) · Σ_{n₃∈I} e(r m n₃ / q),
```

so the inner sum is an incomplete geometric sum of length `|I|` — whence the bound
`|S(r)| ≪_ε x³/q + x²`.

**Average over `r` is circular.** By orthogonality,

```
Σ_{r mod q} |S(r)|² = q · J₆(I).
```

Hence

```
Σ_a E_a² = q^{−1} Σ_{r≠0} |S(r)|² = J₆(I) − |I|⁶/q
```

(up to the `q` vs `q−1` normalisation). **Bounding the average of `|S|²` is literally (H).**
Any argument that only controls `Σ_r |S(r)|²` cannot prove (H); it restates it. The needed
extra saving must be **pointwise** in `r` (or for all `r` outside a sparse exceptional set
whose contribution can be estimated separately without re-encoding `J₆`).

**Propagation.** If `|S(r)| ≪ q^{7/9 − δ}` for every `r ≠ 0`, then
`Σ_a E_a² ≪ q^{14/9 − 2δ}`. Comparing to need `q^{4/3 − η}`:

```
η ≤ 2δ − 2/9.
```

So `η > 0` requires **`δ > 1/9`**. Geometric has `δ = 0` in this normalisation.

### (b) Multilinear exponential-sum bounds — explicit check

Sizes: `|I| = x = q^{7/18}`, `|I|³ = q^{7/6}`, trivial `|S| ≤ q^{7/6}`, geometric `q^{7/9}`,
need `q^{2/3}`.

| Bound | Formula (equal sizes) | Exponent at `θ=7/18` | vs geo `q^{7/9}` | Range |
|---|---|---|---|---|
| Trivial | `x³` | `7/6 ≈ 1.167` | worse | — |
| Incomplete geometric | `x³/q + x²` | `7/9 ≈ 0.778` | = geo | always |
| Bilinear after 1 var (PS (1.6)) | `p^{1/2} x^{1/2}x^{1/2}x` | `1/2+2θ ≈ 1.278` | worse | — |
| Bourgain–Garaev 2009 | `(x³)^{13/16} q^{5/18}` | `≈ 1.226` | worse | — |
| Petridis–Shparlinski 2016 (Thm 1.1, arXiv:1604.08469) | `q^{1/4} x^{19/8}` | `169/144 ≈ 1.174` | worse | nontrivial for `x ≥ q^{2/5}`; we have `7/18 < 2/5` — **out of range** |
| Bourgain multilinear (BGK / Bourgain GAFA 2009) | `q^{−η(δ)} x³` under `|A_i|>q^δ` and `∏\|A_i\| > q^{1+δ}` | some `7/6 − η` | ? | see below |

**BGK applicability (verified against Bourgain’s condition).**
- With `δ = 7/18`: need `|I|³ > q^{1+7/18} = q^{25/18}`, but `|I|³ = q^{21/18}` — **fails**.
- With `δ < 1/6`: `|I| = q^{7/18} > q^{1/6}` and `|I|³ = q^{7/6} > q^{1+δ}` — **applies**, giving
  `|S(r)| < q^{−η} |I|³` for some `η = η(δ) > 0` and all `r ≠ 0`.

**Does BGK reach `δ_save > 1/9` over geometric?** To beat geometric need saving
`η ≥ 7/18` over trivial (so `7/6 − η ≤ 7/9`). To reach the (H) threshold need `η ≥ 1/2`
over trivial. Bourgain’s papers prove **existence** of some `η(δ) > 0`; the dependence is of
tower / iterated-exponential type in `1/δ` (not an explicit `η ≥ 1/9`). **No explicit η ≥ 1/9
is claimed or verified here.** Qualitative BGK therefore does **not** give a usable `δ > 1/9`
beyond geometric for pricing `A`.

**Kerr–Shparlinski / Macourt–Shkredov–Shparlinski.** These treat bilinear forms with
Kloosterman sums, or trilinear sums over subgroups / general sets; they do not supply a
verified explicit bound that beats `x²` for three **intervals** of length `q^{7/18}`.
(Kerr–Shparlinski arXiv:2204.05038 is about Kloosterman bilinear forms — different object.)

**Verdict on (b): no proved power `δ > 1/9`.** Explicit trilinear bounds are weaker than
geometric at our size; BGK gives a non-explicit ε over trivial, not over geometric.

### (c) Additive structure of intervals / sum-product

Intervals have `|I−I| ≪ |I|` (additively structured) and `|I·I| ≍ |I|²` (multiplicatively
expanding). Sum-product exponential-sum technology (Bourgain, Garaev, Shkredov) is designed
for sets that are **additively unstructured**; for intervals the **geometric bound already
exploits additive structure** (one-variable completion). Further cancellation must come from
the sum `Σ_{n₁,n₂} min(x, ‖r n₁ n₂/q‖^{−1})` beyond the standard min-bound — i.e. from
correlation of the lattice `{n₁n₂}` with the Farey dissection of `r/q`. No theorem checked
here upgrades that min-sum by a power `q^{1/9}` uniformly in `r ≠ 0`.

Hegyvári-type bounds for sets with small difference sets exist (cited in PS §1) but, as PS
notes, do not improve with a third interval factor in a way that beats geometric at
`|I|=q^{7/18}` (not re-derived; no explicit competing exponent recorded).

**Verdict on (c): no proved upgrade.** Additive structure of `I` is already spent in the
geometric bound.

### (d) Numerics (`trilinear_S.py`)

Exact `S(r)` via `r₂`-expansion + closed geometric sum in the third variable; Parseval
identity spot-checked (`Σ|S|²/q = J₆`).

| `q` | `max\|S\|/geo` | `RMS/geo` | `RMS/need` | `max ~ q^α` | `RMS ~ q^β` |
|---|---|---|---|---|---|
| 503 | 1.72 | 0.65 | 1.23 | 0.86 | 0.70 |
| 10007 | 3.35 | 0.46 | 1.27 | 0.91 | 0.69 |
| 30011 | 4.80 | 0.41 | 1.28 | 0.93 | 0.69 |
| 100003 | 6.19 | 0.36 | 1.28 | 0.94 | 0.69 |

- **Pointwise max is worse than `L²` by a growing factor** (consistent with log-factors in the
  min-sum); exponent climbing toward ~1, not toward `2/3`.
- **RMS sits at `~q^{0.69}`**, about `1.28 · need`, flat in `q` at these sizes — matching
  that `Σ|S|²` encodes the diagonal-dominated `J₆` excess (circularity).
- No numerical evidence of a pointwise power below geometric.

### (e) Does anything prove (H)?

**No.** No line-by-line proof; no `η > 0`; no call to `price.py` / `density_payoff` for a new
`A` or `L`.

| Claim | Status |
|---|---|
| Average `|S|²` saving ⇒ (H) | **Circular** (identity) |
| PS / BG / bilinear beat geo at `θ=7/18` | **No** (worse or out of range) |
| BGK with `δ<1/6` gives explicit `δ_save>1/9` over geo | **Not verified / not claimed** |
| Interval sum-product upgrades geo by `q^{1/9}` | **No proof found** |
| Numerics support pointwise `q^{2/3}` | **No** (max worse; RMS stuck by Parseval) |

**(H) remains open. The `q^{1/9}` wall stands.**
