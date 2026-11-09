# Hunting a better zero-density exponent than `7/3`

Status labels: **Written proof** (argued here; not machine-checked, not refereed), **Heuristic**,
**Numerical**, **Dead** (with reason). Prepared with AI assistance; needs expert review. Scripts live in
`scripts/density_hunt/`.

## The target

Chen, Gupta and Li (arXiv:2507.08296v2) prove
`Σ_{χ mod q} N(σ, T, χ) ≪_ε (qT)^{7(1−σ)/3+ε}` uniformly in `q` and `T`. The library formalises a weaker
one-point-per-character form on `[5/7, 16/21]` as `LinnikCGLDensity.cglDensity` (see
[`formalisations/chen-gupta-li-density.md`](../formalisations/chen-gupta-li-density.md)). The uniform exponent
`A = 7/3` is attained at `σ = 5/7`, where their term `4/(1+σ)` meets Ingham's `3/(2−σ)`.

The Linnik paper (`papers/linnik-exponent/`) takes this as Input and proves every reduced class mod `q` has a
prime `p ≤ K q^{11/5}` (`Linnik22000E.linnik_22000e`), by Harman's sieve. The sieve's theoretical floor is
`1 + A/2 = 13/6 ≈ 2.167`; the paper proves the round value `11/5 = 2.2`. Any genuine saving on `A` near
`σ = 5/7` widens the Type II window and lowers that floor
(`scripts/density_hunt/price.py`).

This note tries openings that the repository has **not** already recorded as tried. It does not claim an
improvement.

## Bookkeeping (Numerical)

Suppose the critical `S₃` term in CGL §12 gains a factor `q^{−δ}` (their Remark 12.3). Then, as in
`docs/cgl-s3-prime-moduli.md` §1, `4/(1+σ)` becomes `(4 − 2δ)/(1+σ)`, meets Ingham at
`σ* = (5 − 4δ)/(7 − 2δ)`, and the uniform exponent is `A = 7/3 − 2δ/3` for `δ ≤ 1/26`. At `δ = 1/26` one hits
Guth–Maynard's `30/13` and further `δ` does not help the uniform `A` under that model.

| `δ` | `A` | sieve floor `1+A/2` | classical floor `A` |
|---|---|---|---|
| `0` | `7/3 ≈ 2.3333` | `13/6 ≈ 2.1667` | `2.3333` |
| `0.01` | `2.3267` | `2.1633` | `2.3267` |
| `0.02` | `2.3200` | `2.1600` | `2.3200` |
| `1/26 ≈ 0.0385` | `30/13 ≈ 2.3077` | `≈ 2.1538` | `2.3077` |

So even a clean `δ = 0.02` only moves the sieve floor by about `0.007`. The paper's formalised `11/5 = 2.2` has
room down to about `2.198` by recomputing the window (§S6), which is a different, smaller gain that does not
need a new `A`.

## Exclusion list (do not redo)

Recorded in `docs/cgl-s3-prime-moduli.md`, `scripts/cgl_s3/`, `papers/linnik-exponent/` (limits section and
supplement §S6), and `formalisations/chen-gupta-li-density.md`:

1. **Direct attack on CGL's `S₃` at prime `q`, `T = 1`** via Schatten–Hölder, weighted energy conjectures,
   Bohr sets, hybrid dilation splits, adversarial / Singer / unimodular large-value sets, fourth-moment caps,
   popular differences (`cgl-s3` §§2–7).
2. **Block-sum / sixth-moment route at `T = 1`** and the counting problem with shifts (`cgl-s3` §§8–9): known
   Weyl / fourth / sixth moment inputs only recover classical ranges; the missing input is a sixth moment for
   one modulus beyond `q^{4/3}`.
3. **Bettin–Chandee trilinear form** after Poisson on the multilinear Kloosterman sum (`cgl-s3` §10): saving
   `x^{1/4}` vs needed `∼ x q^η`; large-sieve-type conjecture stated but not proved.
4. **Deshouillers–Iwaniec / Kuznetsov as tried** on moduli `b₂b₃` with `q` fixed (`cgl-s3` §11, `kuznetsov.py`):
   worse than trivial or equal at `θ = 1/2`; Linnik–Selberg cancellation in the transition range not obtained.
5. **Deeper Buchstab decomposition** beyond depth eight: only ~1/4 of the certificate cost (`papers/linnik-exponent`
   limits).
6. **Stronger half-plane `Re s > 7/8`**: does not help the sieve certificate (§S6).
7. **Re-chosen Type II window only** (no new density): reaches ~`2.198`, not formalised; orthogonal to improving `A`.
8. **CGL Remark 12.3 itself**: improving the binding term needs "joint cancellation in `R` and the `m` sums",
   called "quite difficult" by the authors; this hunt may touch that term but must not merely restate their
   obstacle.
9. **GM large values for `q = 1`**: already the engine behind CGL; re-deriving Guth–Maynard for zeta is out of
   scope.

Literature check (web, 2026-11-09): arXiv:2507.08296 remains the state of the art for the uniform `A` over all
characters mod `q`; no later improvement of `7/3` was found. Guth–Maynard (arXiv:2405.20552) is the `q = 1`
ancestor. Petrow–Young give Weyl subconvexity `L(1/2+it,χ) ≪ (q|t|)^{1/6+ε}` and related moments; that input is
already accounted for in `cgl-s3` §9 as insufficient alone for a better uniform `A`.

## Randomised order

Seed `20261109` (`scripts/density_hunt/seed.txt`). Twenty-four openings were listed, shuffled with
`random.Random(20261109)`. This batch assesses the first eight. Later batches continue down the list without
reshuffling.

| # | id | opening |
|---|---|---|
| 01 | `smooth_mean_value` | Short-interval / mean-value of Dirichlet polynomials with smooth coefficients |
| 02 | `iwasawa_log` | Iwaniec–Kowalski style log-free density with half-plane truncation |
| 03 | `turan_power` | Turán power-sum method on `log L` / zero clusters |
| 04 | `delta_method` | δ-method / Voronoi on the detector bilinear forms |
| 05 | `HB_LV_variants` | Heath-Brown large-values / Halász–Montgomery with different weights |
| 06 | `combinatorial_energy` | Combinatorial energy increment / graph theory of large-value sets |
| 07 | `real_complex_split` | Split real vs complex characters |
| 08 | `bombieri_large_sieve` | Bombieri large sieve in hybrid `(q,T)` with asymmetric lengths |
| 09–24 | (queued) | see `scripts/density_hunt/seed.txt` |

---

## 01. `smooth_mean_value` — Dead

**Idea.** Replace CGL's detector (or the Type II character polynomials) by a mean-value estimate for
Dirichlet polynomials with *smooth* coefficients on short intervals of length `≪ N`, hoping the smoothness
buys a better large-value bound near `V = N^{5/7}` at length `N = (qT)^{7/9}` (the CGL critical length at
`σ = 5/7`).

**Bookkeeping at `σ = 5/7`.** Need `|W| ≪ (qT)^{A(1−σ)}` with `A < 7/3`, i.e. `|W| ≪ (qT)^{2/3 − ε'}` at the
critical point where currently `|W| ≪ (qT)^{2/3}`. Smooth coefficients typically improve logarithmic factors
or allow integration by parts / Poisson with rapid decay; they do not by themselves beat the Montgomery mean
value `∫|D|^{2} ≪ (T+N)Σ|a|^{2}` in the `V ≈ N^{3/4}` large-value regime that sits under `7/3`.

**Where it breaks.** CGL's critical detector at `T = 1` is already essentially a *block sum* (smooth of width
`(qT)^ε`) — recorded in `cgl-s3` §8. Smoothness is already spent. Further smoothing shortens the effective
support and *raises* the relative large-value threshold, which is the wrong direction.

**Literature.** Classical mean-value / short-interval mean-value theorems (Montgomery, Huxley, …) are the
baseline CGL improves on via Guth–Maynard. No new opening.

**Verdict: Dead.** Smoothness is already used; it does not touch Remark 12.3's `S₃` term.

## 02. `iwasawa_log` — Dead (for lowering uniform `A`)

**Idea.** Log-free zero-density estimates (e.g. in the style of Iwaniec–Kowalski §10 / Gallagher) often lose a
power of `log(qT)` but keep a clean exponent. Combine with the half-plane `Re s > 11/12` to truncate the
Dirichlet polynomials sharply and hope the truncated log-free bound beats `7/3` near `σ = 5/7`.

**Bookkeeping.** Log-free bounds of shape `Σ_χ N(σ,T,χ) ≪ (qT)^{c(1−σ)}` classically have `c ≥ 12/5` or worse
in the `q`-aspect without GM input; the half-plane only removes zeros with `β > 11/12`, which the Linnik paper
already notes is irrelevant to the value of `A` on `[1/2, 11/12]` (any fixed `η₀ > 0` works). Truncation at
height `≪ (qT)^{O(1)}` does not change the critical length `N ≍ (qT)^{7/9}`.

**Where it breaks.** Log-free methods trade logs for worse (or equal) main exponents. They are useful for
Linnik-type applications that cannot afford `(log q)^B`, but this library's Linnik theorem already absorbs
logs into `K`. They do not improve `A`.

**Verdict: Dead** as a route to `A < 7/3`. Possibly useful later for an *effective* `K`, which is out of scope
here.

## 03. `turan_power` — Dead (near `σ = 5/7`)

**Idea.** Turán's power-sum method controls clusters of zeros of `L(s,χ)` via power sums of `ρ^{-k}`. Use it
to limit how many zeros a single character can contribute near `σ = 5/7`, then sum over `χ`.

**Bookkeeping.** Density estimates already allow ~`(qT)^{A(1−σ)}` *characters with at least one zero*; Turán
helps with *multiplicity / clustering for one L-function*. At `σ = 5/7`, `1−σ = 2/7`, a single character has
≪ `log(qT)` zeros in a bounded height interval by standard zero-counts. Replacing "one zero per character" by
"≪ log zeros" only costs logs inside CGL's already `ε`-power.

**Where it breaks.** The binding constraint is the number of distinct characters with a large Dirichlet
polynomial (CGL Prop. 3.1), not multiple zeros on one character. Turán does not reduce `|W|`.

**Verdict: Dead** for uniform `A`. (May still matter for plain `N(σ,T,χ)` for a fixed `χ`, not our sum.)

## 04. `delta_method` — Dead as tried via Poisson; residual note

**Idea.** Apply the δ-method (Duke–Friedlander–Iwaniec) or Voronoi summation to the bilinear forms that appear
when expanding `|Σ a_n χ(n)|^{2k}`, hoping for Kloosterman-type cancellation beyond CGL's affine/GCD sums.

**Relation to exclusion.** `cgl-s3` §§10–11 already Poisson-summed the critical sixth-moment counting problem
into Bettin–Chandee / Kuznetsov shapes and recorded the barrier. The δ-method on the *same* forms is a close
cousin: it produces similar Kloosterman fractions with factorable moduli.

**Where it breaks.** Same Weil barrier / transition-range Bessel issue as `cgl-s3` §10–11. Without a new
estimate for those Kloosterman sums (e.g. beyond Kim–Sarnak in Kuznetsov), no gain.

**Residual (Heuristic, not pursued here).** A δ-method aimed at a *different* bilinear form — e.g. the off-diagonal
of CGL's energy `E(W)` in Prop. 10.2 — might be a distinct opening; that is closer to `hybrid_energy` /
`spectral_large_sieve_var` later in the queue, not a fresh δ-method win on the already-Poisson'd count.

**Verdict: Dead** as a redo of §§10–11. Flag the "δ on `E(W)`" variant for the `hybrid_energy` batch item.

## 05. `HB_LV_variants` — Dead for beating `7/3`

**Idea.** Revisit Heath-Brown's large-value estimates and Halász–Montgomery inequalities with nonstandard
weights (e.g. Fejér, Selberg minorants, or GCD-biased weights) to improve the large-value count at
`V = N^{5/7}`.

**Bookkeeping.** Pre-GM character large values sit at Huxley's `12/5` or Jutila's ~`2.46`. CGL's gain is
precisely the GM-type improvement in the `N^{3/4}`-neighbourhood. Classical HM/HB variants live on the
other side of that threshold.

**Where it breaks.** Any improvement available from reshaping HM weights at `V ≥ N^{3/4}` was already
optimised for decades and still gave `A ≥ 12/5 > 7/3`. To beat `7/3` one must improve the GM/CGL critical
term, not the classical large-value lemma.

**Literature.** Montgomery–Halász–Huxley, Heath-Brown LV: superseded near the critical point by GM/CGL.

**Verdict: Dead** for `A < 7/3`.

## 06. `combinatorial_energy` — Partial / speculative

**Idea.** Treat the large-value set `W` of characters as a graph or hypergraph (edges when
`|Σ_n a_n χ₁(n)χ̄₂(n)|` is large), run an energy-increment argument, and obtain a density increment or a
structure theorem that forces `W` into a Bohr set / subgroup, where character-sum cancellation is stronger.

**Relation to exclusion.** `cgl-s3` §5–6 already tested Bohr sets and a weighted-energy *conjecture*
`(iv) ⪅ E(W)(Σ|H|²)²` numerically; structured sets were a blind spot of norm bounds, not an obstruction.
A full combinatorial energy-increment proof is **not** in the exclusion list — only the numerical Bohr probe.

**What it would need (Heuristic).**
- An energy theorem: if `E(W)` is large then `W` correlates with a short Bohr set mod `q`.
- On that Bohr set, bound `S₃` (or CGL's Prop. 3.1 count) better than `|W|^{3/2}` by using the additive
  structure (e.g. completing sums).
- Combine with the small-energy case already handled by CGL.

**Where it likely breaks.** At prime `q`, the dual group is a field; Bohr sets of low rank are well understood,
but CGL's adversarial numerical examples (`cgl-s3` §3, §6) already achieve `S₃` close to the `|W|^{3/2}` bound
*without* obvious Bohr structure. An increment argument that assumes "large energy ⇒ structure" must explain
those near-extremisers. Also, even a perfect structure theorem only helps if the structured case beats
Remark 12.3; `cgl-s3` §6 found structured sets *far below* the bound, so the danger is the unstructured
near-extremisers.

**Verdict: Partial.** Not excluded; not promising without a new inequality that handles near-extremal
unstructured `W`. Worth a short numerical check: measure additive energy of the adversarial `W` from
`scripts/cgl_s3/` at reachable `q` (queued as a script task). No analytic gain claimed.

## 07. `real_complex_split` — Dead for uniform `A`

**Idea.** Prove a stronger density theorem for non-real `χ`, and handle real `χ` by the half-plane /
classical zero-free regions (or Siegel zeros separately).

**Bookkeeping.** Number of real characters mod `q` is `≪ q^ε` (essentially `O(1)` primitive quadratic
characters whose conductor divides `q`). Even if each has the trivial `N(σ,T,χ) ≪ T log(qT)` zeros, their
total contribution is `≪_ε (qT)^ε · T`, which is absorbed in `(qT)^{A(1−σ)+ε}` for any `A > 0` once
`1−σ` is bounded below (as on `[5/7, 16/21]`). So the uniform sum is dominated by complex characters.

**Where it breaks.** CGL's bound is already a sum over *all* `χ`; removing the real ones does not change the
exponent. (This is the same reason the d2-density work on real `χ_D` does not feed Linnik — see prior
catch-up.)

**Verdict: Dead** for lowering `A`.

## 08. `bombieri_large_sieve` — Dead for beating `7/3`

**Idea.** Use Bombieri's large sieve in a hybrid `(q,T)` form with asymmetric lengths (e.g. sieve over moduli
up to `Q` and heights up to `T` with `Q ≠ T`) to improve large values at the CGL critical point.

**Bookkeeping.** The classical large sieve / mean value already gives the Montgomery-type term in large-value
estimates; GM/CGL beat it precisely where that term was binding. Asymmetric Bombieri forms are powerful for
averaged moduli (Bombieri–Vinogradov territory) but Linnik / CGL need a bound *for each q*.

**Where it breaks.** Averaging over `q` would give density theorems for almost-all moduli, which is a different
theorem (and does not lower `Linnik22000E.linnik_22000e`, which is for every `q`). For a single `q`, Bombieri's
inequality reduces to forms already underlying Huxley/Montgomery.

**Verdict: Dead** for the every-`q` exponent `A`.

---

## Batch summary

| # | id | verdict | one-line reason |
|---|---|---|---|
| 01 | `smooth_mean_value` | Dead | smoothness already used in CGL block detectors |
| 02 | `iwasawa_log` | Dead | log-free ≠ better `A`; half-plane value irrelevant to `A` |
| 03 | `turan_power` | Dead | controls clusters per `χ`, not `|W|` |
| 04 | `delta_method` | Dead | redo of cgl-s3 Poisson/Kloosterman barrier |
| 05 | `HB_LV_variants` | Dead | classical LV cannot beat GM/CGL critical regime |
| 06 | `combinatorial_energy` | Partial | see Batch 2 energy probe: 3–7× random E₊, ≪ AP |
| 07 | `real_complex_split` | Dead | too few real `χ` to affect the sum |
| 08 | `bombieri_large_sieve` | Dead | helps almost-all `q`, not every `q` |

**Promising enough to keep alive:** only `combinatorial_energy`, and weakly. Next batch should prioritise
queued items that could touch Remark 12.3 differently: `moment_half`, `GM_q_aspect` (only *refinements*
beyond CGL, not a redo), `hybrid_energy`, `jutila_mollifier`, `pretentious`, `decoupling`,
`halfplane_shorten` — still in seed order, not cherry-picked, when continuing.

**No Lean claims. No improvement of `A` claimed.**


---

## Additive energy of near-extremal `W` (Numerical; opening #06)

Script: `scripts/density_hunt/energy_adversarial.py`. `W ⊂ Z/(q−1)Z` via discrete logs; adversarial = truncated
power method of `scripts/cgl_s3/probe.py` at `R = round(q^{2/3})`, `N ≈ q^{7/9}`. Additive energy
`E₊(W) = Σ_s r_W(s)²` with `r_W = 1_W ∗ 1_W`. Random baseline in `Z/M` is `E₊ ∼ R⁴/M`.

| `q` | `R` | adv `E₊/(R⁴/M)` | random `E₊/(R⁴/M)` | AP `E₊/(R⁴/M)` | adv/random |
|---|---|---|---|---|---|
| `1009` | `101` | `3.58` | `≈ 1.16` | `≈ 9.0` | `≈ 3.1` |
| `10007` | `464` | `5.94` | `≈ 1.08` | `≈ 14.4` | `≈ 5.5` |
| `30011` | `966` | `6.68` | `≈ 1.06` | `≈ 20.7` | `≈ 6.3` |

(Raw `E₊/R³`: adv `0.359`, `0.275`, `0.215`; random `0.116`, `0.050`, `0.034`; AP `0.903`/`0.667`/`0.667`.
Computed 2026-11-09, seed `0` in the script; tpm ≤ 41 iters.)

**Reading.** Adversarial `W` carries **3–7×** the additive energy of a random set of the same size, and the ratio
grows slowly with `q`. It remains **well below** arithmetic progressions / intervals (`∼ 9–21×` random). So there is
genuine additive structure, but not AP-level structure. Opening #06 stays **Partial**: an energy-increment proof
would have to exploit a moderate-energy regime, not only Bohr/AP extremisers. Combined with `cgl-s3` §3 (adversarial
`S₃` near the CGL bound), the near-extremisers for `S₃` are **not** the same as max-energy sets; high `S₃` and high
`E₊` may diverge.

---

## CGL parameter re-optimisation (Numerical; opening #15 / `GM_q_aspect`)

Script: `scripts/density_hunt/cgl_reopt.py`, same LV terms as `scripts/cgl_s3/price.py`.

**Critical point arithmetic at `σ = 5/7`, `y = 7/9`, `c = 4/3`:**

| term | value |
|---|---|
| `y(2−2σ)` (diag) | `0.444444` |
| `½ + y(3−4σ)` | `0.611111` |
| **`c + y(2−4σ)` (S₃)** | **`0.666667`** |
| `1 + y(12/5−4σ)` (GM) | `0.644444` |
| MVT `1 + y(1−2σ)` | `0.666667` |
| target `(7/3)(1−σ)` | `0.666667` |

So at the classical critical point the **S₃ term and MVT tie** at `2/3`; GM and half are strictly smaller. Any
improvement of uniform `A` must beat this tie.

**Baseline peak** of `min(Ingham, A_CGL, Huxley)`: `≈ 2.3334` at `σ ≈ 0.7148`, binding CGL with **`S₃`**, `a* ≈ 0.777`.

**Retuning free numerical parameters (same four LV terms):**

| change | peak `A` | note |
|---|---|---|
| dyadic ratio `3/2 → 1.2` | `≈ 2.160` | **not free**: ratio `3/2` is CGL’s covering of detector lengths in §12; shrinking leaves lengths untreated unless a new covering is proved |
| ratio `1.3`, `1.4` | `≈ 2.210`, `≈ 2.267` | same objection |
| ratio `≥ 1.5` | `≥ 7/3` | baseline or worse |
| `y_floor ∈ [0.5, 0.75]` | `≈ 2.333` unchanged | no gain |
| widen/narrow `a`-range | `≈ 2.333`–`2.334` | no gain |
| drop `c` below `4/3` | peak falls to Ingham–GM glue `≈ 2.308` (`30/13`) once `c ≲ 1.30` | **requires an analytic `S₃` saving**; matches `cgl-s3` §1 |

**Binding term along `σ`:** near `0.70`–`0.71` the optimiser reports `MVT`; from `≈ 0.715` the binding CGL term is
`S₃` (alternating with MVT depending on grid). Consistent with Remark 12.3.

**Verdict for free re-optimisation: Dead.** The only numerical move that lowers the peak below `7/3` without
changing LV terms is an illegitimate shrink of the dyadic ratio, or a smaller `c` (analytic work on `S₃`).

---

## Batch 2: openings 09–16

### What must be beaten at `σ = 5/7` (common ledger)

Write `|W| ≪ (qT)^α` for the large-value set at detector length `N = (qT)^y`. Density needs
`α ≤ A(1−σ)`. At `σ = 5/7`, `1−σ = 2/7`, target `A = 7/3` means `α ≤ 2/3`. CGL achieves `α = 2/3` via
`min(MVT, Thm1.1) = 2/3` with the S₃ contribution `c + y(2−4σ) = 2/3` at `y = 7/9`, `c = 4/3`. Equivalently,
`S₃ ≪ (qT)² |W|^{3/2}` at `T = 1` forces `|W| ≪ q^{4/3} N^{2−4σ} = q^{2/3}` at criticality
(`cgl-s3` §1, `price.py`). **To get `A < 7/3` one needs either `α < 2/3` at this point, or a shift of the
Ingham/CGL meeting point by lowering the CGL curve on a neighbourhood of `5/7`.**

### 09. `sum_product` — Dead

**Idea.** Sum–product estimates (`max(|W+W|, |W·W|) ≫ |W|^{1+δ}`) on the large-value set in `F_q` or on
`Z/(q−1)Z` to force expansion and then bound character sums on expanding sets.

**Bookkeeping.** Need `α ≤ 2/3 − ε`. Sum–product gives expansion of `W`, not a bound on `S₃ = tr(E³)` or on
`Σ_{χ∈W} |D(χ)|⁴`. Even with `|W+W| ≫ |W|^{1+δ}`, the CGL energy/S₃ estimates do not automatically improve:
their Prop. 10.2 / 11.1 already handle general `W`. Expansion helps when one *completes sums* over `W+W`; that
requires a different expansion of `S₃` than CGL’s.

**Specific obstruction.** The additive-energy probe shows adversarial `W` is only moderately expanding
(`E₊/(R⁴/M) ≈ 6–7`, so `|W+W|` is smaller than random but not tiny). Sum–product in `F_q` is for subsets of
fields; `W` lives in the dual of `F_q^*` (circle group). Translating SP to a saving on `c = 4/3` needs a new
identity. No such identity is in hand; without it SP does not move `α`.

**Verdict: Dead** until coupled to an `S₃` identity. (Not the same as excluded Bohr tests; still blocked.)

### 10. `pretentious` — Dead for uniform `A`

**Idea.** Granville–Soundararajan pretentiousness: a character with a large Dirichlet polynomial is pretentious
to a characters of small conductor / `n^{it}`, so large-value characters are scarce.

**Bookkeeping.** Pretentious large-value theorems typically give `|W| ≪ (qT)^{ε}` or weak powers for
*extremal* `|D(χ)| ≈ N`, not for the critical threshold `V = N^{5/7} = N^σ`. At `V = N^σ` with `σ = 5/7`,
one is far below the Halász extremal regime. CGL’s count `|W| ≪ (qT)^{2/3}` is already a polynomial bound for
medium-large values; pretentious methods shine near the maximum.

**Specific obstruction.** Halász–type / pretentious bounds degrade as `V/N` drops. At `V = N^{5/7}` they do not
beat `α = 2/3`. (cf. classical Halász–Montgomery already excluded as #05.)

**Verdict: Dead.**

### 11. `jutila_mollifier` — Dead for beating `7/3`

**Idea.** Replace CGL’s soft detector / mollifier lengths by Jutila-style zero-detection with different
mollifier support, hoping the large-value input is applied at a friendlier `(y, V)`.

**Bookkeeping.** Jutila’s classical density exponent was `≈ 2.46 > 7/3`. CGL already optimises detector length
`y` against their Thm 1.1 (the `min_a max_{[a,3a/2]}` in `price.py`). Changing mollifier length moves you along
the same LV curve; it cannot undercut the curve’s maximum without a better LV theorem.

**Specific obstruction.** At `σ = 5/7` the binding point is `y = 7/9` where S₃ ties MVT. Any mollifier that
pushes `y` away from `7/9` either hits a worse CGL term or leaves the Ingham range. Recomputing `A_cgl` over
`y` is exactly `cgl_reopt.py`; free length changes do not drop the peak below `7/3`.

**Verdict: Dead.**

### 12. `matomaki_radziwill` — Dead

**Idea.** Use Matomäki–Radziwiłł short-interval multiplicative cancellation for `χ(n)` / coefficients along
short intervals of integers, to improve mean values of detectors.

**Bookkeeping.** MR gives cancellation for multiplicative functions on short intervals in the *integer*
aspect, averaged over starting points. CGL’s critical objects are *characters* with a fixed smooth detector of
length `N ≍ q^{7/9}`. Swapping in MR would target `Σ_{n∼N} a_n χ(n)` for many `χ` — the same mean value
already bounded by large sieve / MVT at strength giving `α = 2/3` on the MVT side of the tie.

**Specific obstruction.** MR does not improve the character-aspect large sieve at the critical `V = N^{5/7}`.
It also does not touch `S₃`’s Kloosterman/R-structure (Remark 12.3). Wrong aspect for the binding term.

**Verdict: Dead.**

### 13. `composite_q_DI` — Dead for uniform `A` (every `q`)

**Idea.** For composite `q`, Deshouillers–Iwaniec / factorable moduli already appear in CGL’s method and give
Guth–Maynard’s `30/13` when `q` has a suitable factor; push this harder and glue to prime `q`.

**Bookkeeping.** Uniform `A` is the max over all `q`. CGL explicitly: the `7/3` comes from **prime** `q` at
`T = 1` (`cgl-s3` intro). Improving composite `q` only cannot lower the uniform exponent. Linnik needs every
`q`.

**Specific obstruction.** Excluded cousin of `cgl-s3` §11 for the prime case; for composite `q` the exponent
is already ≤ `30/13 < 7/3`. No uniform gain.

**Verdict: Dead.**

### 14. `ingham_refinement` — Dead without CGL improvement

**Idea.** Improve Ingham’s `3/(2−σ)` below `σ = 5/7` so that even with CGL unchanged the meeting point drops,
lowering uniform `A`.

**Bookkeeping.** Uniform `A = max( max_{σ≤5/7} Ingham(σ), max_{σ≥5/7} CGL(σ) )`. Ingham is decreasing in `σ`;
its value at `5/7` is already `7/3`. Improving Ingham for `σ < 5/7` does not change the value at the meeting
point if CGL still hits `7/3` at `5/7`. To move the meeting point left/down one must lower the CGL curve
(see `cgl_reopt` `c`-sweep: only then the peak slides to `≈ 0.70` with height `30/13`).

**Specific obstruction.** At `σ = 5/7`, Ingham = CGL = `7/3` exactly. Refining Ingham elsewhere leaves this
tie intact.

**Verdict: Dead.**

### 15. `GM_q_aspect` — Dead as free reopt; Partial as research direction

**Idea.** Re-read CGL’s adaptation of Guth–Maynard for lossy case splits, unused savings, or parameter slack;
re-optimise numerically; seek a sharper q-aspect LV theorem than CGL Thm 1.1.

**What we checked (Numerical + reading).**
- Term ledger at criticality: S₃ ties MVT; GM term `0.644 < 0.667` has **slack** of `0.022` in the `|W|`
  exponent — improving GM alone by less than that does **nothing** at `σ = 5/7`.
- Free parameters `y_floor`, `a`-range: no gain (`cgl_reopt.py`).
- Dyadic ratio `< 3/2`: numerically drops peak below `7/3`, but **not justified** by CGL’s covering (see above).
- Reducing `c` (S₃ constant) is the only analytic path that moves the peak; then Ingham/GM glue at `30/13`.

**Specific obstruction for a free win.** The binding term is S₃/`c`, not the GM large-value term. “More GM” is
the wrong corner of the max in Thm 1.1 at the critical point. A new GM-style inequality that *also* improves
the affine/GCD sums feeding Prop. 8.1 / 11.1 could help, but that is exactly CGL’s hard step (Remark 12.3),
already hunted in `cgl-s3`.

**Verdict: Dead** as a free re-optimisation. **Partial** only as a synonym for “improve S₃ / Prop. 11.1”, which
is the existing open problem—not a new opening.

### 16. `zero_repulsion` — Dead for the density sum

**Idea.** Deuring–Heilbronn repulsion / zero repulsion between nearby zeros or characters to limit how many
`χ` can have a zero near `σ = 5/7` simultaneously.

**Bookkeeping.** Repulsion gives spacing for zeros of a *fixed* L-function, or landau–Siegel type repulsion for
an exceptional real zero. The half-plane `Re s > 11/12` already removes exceptional zeros. For the density
*sum* `Σ_χ N(σ,T,χ)`, repulsion does not give a power saving on `|W|` at medium heights: characters are
orthogonal, and many can vanish near the same height without sharing an exceptional zero.

**Specific obstruction.** No exceptional-zero term remains in the Linnik chain (half-plane). Classical
repulsion does not bound the number of distinct characters with a zero at `β ≈ 5/7`.

**Verdict: Dead.**

---

## Batch 2 summary

| # | id | verdict | obstruction / lead |
|---|---|---|---|
| 06 | `combinatorial_energy` | **Partial** (updated) | adv `E₊` is 3–7× random but ≪ AP; structure exists, not AP-shaped |
| 09 | `sum_product` | Dead | no bridge from expansion to `S₃` / `α < 2/3` |
| 10 | `pretentious` | Dead | wrong regime (`V ≈ N`, not `N^{5/7}`) |
| 11 | `jutila_mollifier` | Dead | length retune cannot undercut LV curve max |
| 12 | `matomaki_radziwill` | Dead | integer short-interval aspect, not binding character LV |
| 13 | `composite_q_DI` | Dead | uniform `A` fixed by prime `q` |
| 14 | `ingham_refinement` | Dead | meeting point tied at `5/7` by CGL, not Ingham |
| 15 | `GM_q_aspect` | Dead (free reopt) / Partial (≡ improve S₃) | GM term has slack; S₃ binds; ratio shrink not free |
| 16 | `zero_repulsion` | Dead | no exceptional-zero lever left; doesn’t bound `|W|` |

**Still alive after 16 openings:** `#06 combinatorial_energy` (weak, now quantified), and `#15` only as restatement
of the S₃ problem. **No improvement of `A` claimed.**


---

## The S₃–MVT tie (structural fact for Batch 3)

At `(σ, y, c) = (5/7, 7/9, 4/3)` both the S₃ term `c + y(2−4σ)` and the MVT term `1 + y(1−2σ)` equal
`2/3`. So:

- an S₃-only saving (`c ↓`) at **fixed** `y = 7/9` immediately makes **MVT** the binding term at `α = 2/3`;
- uniform `A` can still fall slightly because the optimiser may move `(a, y)` (`delta_targets.py`);
- but under the present four LV terms the peak **freezes at ≈ 2.308 (`30/13`)** once `δ ≳ 1/26` — further S₃
  savings alone never reach `A = 2.30`.

Therefore Batch 3 prefers openings that **change the tie** (move/break MVT, change effective `y`, split `W`,
mix detectors, interpolate in `σ`), not only Remark 12.3.

### `δ` needed for target `A` (Numerical; re-optimised `a,y`)

Script: `scripts/density_hunt/delta_targets.py`. `c = 4/3 − 2δ/3`.

| target peak `A` | `δ` needed | `c` | sieve floor `1+A/2` | notes |
|---|---|---|---|---|
| `2.330` | `≈ 0.0057` | `≈ 1.3295` | `≈ 2.1650` | tiny S₃ saving |
| `2.325` | `≈ 0.0128` | `≈ 1.3248` | `≈ 2.1625` | |
| `2.320` | `≈ 0.0198` | `≈ 1.3201` | `≈ 2.1600` | |
| `2.310` | `≈ 0.0355` | `≈ 1.3097` | `≈ 2.1550` | near `1/26` |
| `30/13 ≈ 2.3077` | `δ ≳ 1/26` | `≲ 1.3077` | `≈ 2.1540` | **floor under these LV terms** |
| `2.300` | **unreachable** | — | — | peak freezes ≈ `2.308` |

At fixed `y = 7/9`, `σ = 5/7`: for any `δ > 0`, `min(S₃, MVT) = MVT = 2/3`. Re-optimisation of `y` is what
buys the rows above; the MVT wall is why `2.30` is impossible without a new LV term.

### `W` energy split — quantitative model (Numerical / Heuristic)

From the energy probe (`q = 30011`): adv `E₊/(R⁴/M) ≈ 6.68`, random `≈ 1.06`, AP `≈ 20.7`.
A crude two-point mixture gives structured fraction `f ≈ (6.68−1.06)/(20.7−1.06) ≈ 0.29`.

Optimistic bookkeeping (ignore harmful cross terms in `tr(E³)`): `R ≤ R_s + R_u` with
`R_s ≪ q^β` (structure) and `R_u ≪ q^{α_u}` (random-like). Need `max(β, α_u) < 2/3`.

Even if the structured core is **removed entirely** (`β = −∞`), `R_u ≈ (1−f)R ≈ 0.71 q^{2/3}`, so
`α_u = 2/3 + log(0.71)/log q → 2/3` as `q → ∞`. At `q = 10^{12}`, `α_u ≈ 0.654` still — only a
log-factor, **not** a power saving on uniform `A`.

**Verdict on pure split:** cannot asymptotically beat `A = 7/3` without a power saving on the unstructured
majority. Cross terms likely make this worse. Opens a door only if unstructured `W` admits `α_u ≤ 2/3 − ε`
(new LV), which is circular.

---

## Batch 3 randomised openings

Seed `60783343` (`scripts/density_hunt/seed_batch3.txt`), distinct from Batch 1’s `20261109`. Sixteen openings
(tie-structure + fresh unlikely), shuffled; assessed in that order below.

### 01. `bourgain_restrict` — Dead

**Idea.** Bourgain-type large values for Dirichlet polynomials with **restricted support** (e.g. smooth, friable,
or short interval support) to beat MVT in the binding range.

**Bookkeeping.** Need `α < 2/3` on the MVT side, or a usable `y` where `min(MVT, Thm1.1) < 2/3` while still
detecting `σ = 5/7` zeros. CGL’s detectors at criticality are already smooth block sums (`cgl-s3` §8). Restricted
support is already spent; Bourgain’s classical restricted-support gains target different (`N`, `V`) regimes and do
not undercut `1 + y(1−2σ) = 2/3` at `y = 7/9`.

**Obstruction.** Same as excluded smooth/block-sum path: restriction is present; the MVT term at this
`(y, σ)` is the large sieve / mean value for those coefficients, not an unrestricted monomial probe.

### 02. `decoupling_char` — Partial / long-shot

**Idea.** Bourgain–Demeter decoupling for exponential sums / extension estimates, applied to character
polynomials `Σ a_n χ(n) n^{it}` or to the affine/GCD forms behind CGL Prop. 8.1.

**Bookkeeping.** Decoupling has improved restriction and moment estimates for toral exponential sums. If it
upgraded the GM-type term `1 + y(12/5−4σ)` or the half term enough to also force a new inequality for S₃/energy,
one could break the tie. At criticality GM is `0.644 < 2/3`, so improving GM alone by `< 0.022` does nothing
(`cgl_reopt`). Decoupling must hit **MVT or S₃**, not only GM.

**Obstruction / lead.** No off-the-shelf decoupling theorem for Dirichlet characters mod `q` in the literature
search sense of CGL; translating BD to the GCD-twist affine sums is open research. **Partial** as a possible
tool against Prop. 8.1/11.1, not a ready gain. Not counted as promising without a concrete inequality.

### 03. `selberg_zd` — Dead for the tie

**Idea.** Selberg-style zero detection (AFE + mollifier) to replace CGL’s detector family.

**Bookkeeping.** Changes the map “zero → detector length `y`”. If every `σ = 5/7` zero admits a detector with
`y` in a region where present LV terms give `α ≤ 2/3 − ε`, uniform `A` drops. Mapping `A_cgl(σ)` over `y`
(`cgl_reopt`) shows the **maximum** over admissible blocks is `7/3`; Selberg detectors still produce some `y`,
and the worst `y` dominates.

**Obstruction.** Detector redesign without new LV cannot undercut `max_y min(MVT, Thm1.1)`.

### 04. `afe_reflect_y` — Dead (with a caveat)

**Idea.** Approximate functional equation / reflection sends a long poly to a dual of length `∼ qT/N`, changing
`y ↦ 1−y` (roughly), hoping the dual side has better LV.

**Bookkeeping.** At `y = 7/9`, dual `∼ 2/9 < 2/3`, where Thm 1.1’s floor `y_floor = 2/3` forces pure MVT:
`max(y(2−2σ), 1+y(1−2σ))` at `y = 2/9`, `σ = 5/7` is `max(0.127, 0.905) = 0.905 ≫ 2/3` — **worse**.
Reflection at criticality lands in a bad MVT region.

**Obstruction.** Dual length is on the wrong side of `2/3` for `y = 7/9`. Caveat: hybrid long+short AFE
(two pieces) is `two_detector_mix` / `short_dirichlet` below.

### 05. `power_amplify_k` — Dead as redo; Partial if new `k`-moment

**Idea.** Amplify with `|D|^{2k}` for `k ≠` CGL’s path (their energy / `S₃ ∼ tr(E³)` is a 3-fold form).

**Bookkeeping.** Higher `k` usually needs stronger input (harder moments). Lower `k` returns toward MVT.
CGL’s S₃ is already the critical multilinear form at the GM/`N^{3/4}` threshold.

**Obstruction.** Changing `k` without a new moment estimate either worsens constants or retreats to MVT
(still `2/3`). **Partial** only if a genuine new `k = 2` large-value inequality in the character aspect beats
`α = 2/3` for some usable `y` — that would be a new LV theorem, not a free tweak.

### 06. `huxley_subdiv_q` — Dead for beating `7/3`

**Idea.** Huxley exponent-pair / subdivision methods in the `q`-aspect.

**Bookkeeping.** Huxley’s density exponent `3/(3σ−1)` equals `7/3` at `σ = 5/7` only at the old glue with
Ingham; for `σ > 3/4` Huxley is better than Ingham but CGL already improves the `[5/7, 16/21]` range.
Exponent pairs help classical LV for `V` larger than `N^{3/4}`; the tie is at medium `V = N^{5/7}`.

**Obstruction.** Wrong `V`-regime for the binding MVT/S₃ tie; cannot undercut CGL’s critical point.

### 07. `poly_partition_q` — Partial / long-shot

**Idea.** Guth-style polynomial partitioning / polynomial method in the `q`-aspect large-value geometry
(points `(χ, n)` or frequencies in `Z/(q−1)`).

**Bookkeeping.** Same target as decoupling: improve affine/GCD or large-value counts feeding `c` or MVT.
GM itself is already a Fourier-analytic / incidence advance; CGL adapted it. A further partitioning step would
need to save on the specific GCD-twist sums of Prop. 8.1.

**Obstruction.** No written inequality. **Partial** as research direction synonymous with improving CGL’s hard
sums — not a new soft opening.

### 08. `kloosterman_avg_q` — Dead for Linnik

**Idea.** Average Kloosterman sums over small moduli **including the modulus `q`**, to gain cancellation.

**Bookkeeping.** Spectral averaging (Deshouillers–Iwaniec, Kuznetsov) needs a family of moduli. If the family
includes a range of `q`, bounds are for **almost all** `q` or averages over `q`. Linnik /
`Linnik22000E.linnik_22000e` needs a bound for **every** `q`. Averaging in `q` yields a different theorem
(Bombieri–Vinogradov flavour), not a smaller uniform `A(q)` for each `q`.

**Obstruction.** Structural: average over `q` does not imply uniform in `q`. (Averaging the *other* moduli
`b₂b₃` with `q` fixed was already tried in `cgl-s3` §11 and failed for prime `q`.)

### 09. `two_detector_mix` — Dead under present LV

**Idea.** Partition zeros into two classes, detected at lengths `y₁` and `y₂`, so the uniform count is
`≪ (qT)^{α₁} + (qT)^{α₂}` with each `α_i = min(MVT, Thm1.1)(y_i) < 2/3`, avoiding the single worst `y`.

**Bookkeeping.** For this to help, **every** zero at `σ = 5/7` must admit a detector at some `y` with
`α(y) < 2/3`. But the zero-detection construction produces a specific length scale from the zero’s height and
conductor; one cannot freely assign `y`. If one could choose `y` freely, one would pick a minimiser of `α(y)` —
and `cgl_reopt` shows that after optimising blocks, the **worst necessary** `y` still forces peak `A = 7/3`.

**Obstruction.** No freedom to park all zeros at friendly `y` without a new detection identity. Sum of two
bad classes is still bad if each class can be large.

### 10. `W_energy_split` — Dead asymptotically (quantified)

**Idea.** Split `W = W_s ∪ W_u` using additive energy; bind `W_s` by completion/AP methods, `W_u` by
random-like S₃.

**Bookkeeping.** See the quantitative model above: even with `f ≈ 0.29` structured and `W_s` deleted,
`α_u → 2/3`. Ignoring cross terms is optimistic; including them typically adds positive contributions to `S₃`.

**Obstruction.** Unstructured majority preserves `α = 2/3` as a power. **Dead** for asymptotic uniform `A`.
(Finite-`q` log factors irrelevant to Linnik’s exponent.)

### 11. `short_dirichlet` — Dead

**Idea.** AFE residual + half-plane contour truncation → short Dirichlet polynomials; apply LV at small `y`.

**Bookkeeping.** Half-plane `η₀ = 1/12` truncates horizontal integrals but does not shorten the critical
detector below the length needed to see zeros at `β = 5/7` (Linnik paper: value of `η₀` irrelevant to `A`).
Short duals land in the bad MVT region (`afe_reflect_y`).

**Obstruction.** Same as #04 + excluded half-plane length heuristics.

### 12. `halasz_amplify` — Dead

**Idea.** Halász large values with amplified coefficient sets (pretentious amplifier, pretentious majorant).

**Bookkeeping.** Halász is strongest near `|D| ≈ ‖a‖₁`; critical `V = N^{5/7}` is medium-large. Amplifiers
change coefficients but CGL already allows general `|a_n| ≤ 1` smooth weights. Does not break MVT at
`y = 7/9`.

**Obstruction.** Wrong `V`-regime; overlaps excluded pretentious / HB_LV openings.

### 13. `hybrid_mvt_s3` — Dead without new inputs (tie restatement)

**Idea.** Apply a stronger-than-MVT bound on unstructured `W`, and an S₃ saving only on structured `W`.

**Bookkeeping.** This is exactly `W_energy_split` + `mvt_beyond`. Needs **both** a power saving on unstructured
large values **and** structure bounds — either alone fails the ledger (`α_u → 2/3`, and S₃-only freezes at
`30/13` even with reopt). Combining two missing inputs is not progress.

**Obstruction.** Product of two open problems; no reduction to one.

### 14. `moment_half_det` — Dead for uniform `A` (known barrier)

**Idea.** Use Conrey–Iwaniec / Petrow–Young moments of `L(1/2, χ)` as zero detectors.

**Bookkeeping.** Already analysed in `cgl-s3` §9: Weyl / sixth-moment inputs give sixth-moment counting
`≪ q^{4/3}` type bounds, insufficient to replace the critical S₃/MVT tie for density at `σ = 5/7`.
Improving the sixth-moment end moved a dual route’s `θ`, not the fourth-moment/S₃ end that produces `7/3`.

**Obstruction.** Documented in exclusion/`cgl-s3` §9; moment detectors hit a different face of the same cube.

### 15. `mvt_beyond` — Partial (the correct face of the tie)

**Idea.** Prove a large-value inequality that beats MVT in the region where MVT currently binds — in particular
near `y ≈ 7/9`, `V = N^{5/7}`, or along the locus where `1 + y(1−2σ)` dominates after S₃ drops.

**Bookkeeping.** If MVT is improved to `α_MVT ≤ 2/3 − ε` at the critical point, then even without S₃ saving one
gets `A ≤ 7/3 − (7/2)ε` from that `y`. If S₃ is also improved, the `30/13` floor from `delta_targets.py` can
finally be undercut — that floor exists precisely because when S₃ drops, **MVT/GM glue** stops the fall.

**Obstruction today.** No such inequality; this *is* the content of a better character large-value theorem in the
medium-`V` range. CGL/GM targeted the `N^{3/4}` neighbourhood (S₃/GM side). The MVT side of the tie is the
classical mean value / large sieve, long studied. **Partial**: correctly identified as necessary to break the
`2.308` floor, not a soft win.

### 16. `sigma_interp` — Dead

**Idea.** Replace pointwise density exponents by a convex envelope / interpolated bound in `σ`, hoping the
envelope’s max is `< 7/3`.

**Bookkeeping.** Zero-density exponents `A(σ)` enter as `|W| ≪ (qT)^{A(σ)(1−σ)}`. The uniform Linnik input uses
`sup_σ A(σ)` on `[1/2, 11/12]` (essentially `7/3` at `5/7`). A convex envelope of an already-peaked curve
cannot reduce the peak: `max envelope = max function` for convex envelopes of functions that are already
evaluated pointwise as upper bounds.

**Obstruction.** Envelope of upper bounds is ≥ each bound; the peak stays `≥ 7/3`.

---

## Batch 3 summary

| # | id | verdict | note |
|---|---|---|---|
| 01 | `bourgain_restrict` | Dead | restricted support already in block detectors |
| 02 | `decoupling_char` | Partial | long-shot tool for hard CGL sums; no inequality yet |
| 03 | `selberg_zd` | Dead | cannot dodge worst `y` on the LV curve |
| 04 | `afe_reflect_y` | Dead | dual `y∼2/9` makes MVT worse (`α∼0.91`) |
| 05 | `power_amplify_k` | Dead / Partial | needs new moment LV |
| 06 | `huxley_subdiv_q` | Dead | wrong `V`-regime |
| 07 | `poly_partition_q` | Partial | long-shot ≡ improve Prop. 8.1 sums |
| 08 | `kloosterman_avg_q` | Dead | averages `q` ⇒ not every-`q` Linnik |
| 09 | `two_detector_mix` | Dead | no free assignment of friendly `y` |
| 10 | `W_energy_split` | Dead | unstructured ≈71% keeps `α→2/3` |
| 11 | `short_dirichlet` | Dead | half-plane / short dual don’t help `A` |
| 12 | `halasz_amplify` | Dead | wrong `V`-regime |
| 13 | `hybrid_mvt_s3` | Dead | needs two missing inputs |
| 14 | `moment_half_det` | Dead | known `cgl-s3` §9 barrier |
| 15 | `mvt_beyond` | **Partial (key)** | necessary to break the `≈2.308` floor after S₃ drops |
| 16 | `sigma_interp` | Dead | envelope cannot cut the peak |

### Promising / structural leads (honest)

1. **`mvt_beyond`**: After any S₃ saving, MVT (or GM/Ingham glue) caps uniform `A` at `≈ 2.308`. Beating MVT in
   the medium-large character regime is mandatory for `A < 30/13` under this architecture — and is historically
   hard. No concrete inequality claimed here.
2. **`decoupling_char` / `poly_partition_q`**: Only as speculative tools against CGL’s GCD-twist sums; not soft.
3. **S₃ `δ` table**: Even optimal S₃-only path yields sieve floor `≈ 2.154`, vs current formalised Linnik `2.2`
   and window-only `≈ 2.198`. Worth at most `∼0.01` on the sieve floor if `δ ∼ 1/26` were proved — and still
   needs no MVT advance to claim that much, but **does** need a real S₃ inequality (Remark 12.3).

**No improvement of `A` claimed. No Lean.**

## Next steps

1. Optional Batch 4: try to write a *minimal* inequality that would constitute `mvt_beyond` (state the exact
   LV hypothesis at `(y, V) = (7/9, N^{5/7})` needed for target `A`), and/or correlate `S₃` with `E₊` on the
   same `W` samples.
2. Continue pushing docs/scripts only to PR #98.


---

## Batch 4 — deep dive: `mvt_beyond` + conjectural inequalities for `decoupling_char` / `poly_partition_q`

Focus (no new breadth). Scripts: `scripts/density_hunt/mvt_s3_coexist.py`. Seed unchanged from batch 3.

### (A) `mvt_beyond` — precise CGL use of MVT at the critical point

**Citation (CGL arXiv:2507.08296).** The classical hybrid mean-value / large-sieve input is their **(1.2)**:

\[
|W|\le(qT)^{o(1)}\bigl(N^{2}V^{-2}+qTN\,V^{-2}\bigr).
\]

(This is the \(qT\)-analogue of Montgomery’s mean value theorem; cf. also `LinnikHybrid.mean_value_chars` /
`large_values_chars` in this repo, Gallagher’s hybrid large sieve.) Their Remark 12.3 / §12 case split
(detector \(N\sim q^{1/2}\), powers of length \(N^{k}\in[q^{a},q^{3a/2}]\)) uses (1.2) on the
medium-large character regime. At the binding parameters

\[
\sigma=\tfrac57,\qquad y=\tfrac79\qquad\bigl(N=q^{y},\ V=N^{\sigma},\ T=1\bigr)
\]

the two summands of (1.2) become, in \(q\)-exponents,

\[
y(2-2\sigma)=\tfrac79\cdot\tfrac47=\tfrac49,\qquad
1+y(1-2\sigma)=1+\tfrac79\cdot\bigl(-\tfrac37\bigr)=\tfrac23.
\]

So **MVT binds at \(\alpha=2/3\) via the \(qTN/V^{2}\) term**. Independently, Theorem 1.1’s \(S_3\) term
(with \(c=4/3\)) gives \(c+y(2-4\sigma)=2/3\), and the GM term \(1+y(12/5-4\sigma)=29/45\approx0.644\) has
slack. Exact tie: \(\min(\mathrm{MVT},\mathrm{Thm\,1.1})=2/3\), hence \(A=(2/3)/(1-5/7)=7/3\).
(Bookkeeping: `scripts/cgl_s3/price.py`, `scripts/density_hunt/delta_targets.py`.)

**Minimal LV hypothesis that would constitute `mvt_beyond`.** A theorem of the shape

\[
|W|\le(qT)^{o(1)}\bigl(N^{2}V^{-2}+(qT)^{1-\eta}N\,V^{-2}\bigr)
\]

(with \(\eta>0\) absolute, in the window \(N=(qT)^{y}\), \(V=N^{\sigma}\) near \((y,\sigma)=(7/9,5/7)\),
\(T\) small) would replace \(1+y(1-2\sigma)\) by \(1-\eta+y(1-2\sigma)\). At the critical point that is
\(\alpha\le 2/3-\eta\), hence \(A\le 7/3-(7/2)\eta\) from this \(y\) alone. Combined with any positive
\(S_3\) saving \(\delta\), the `delta_targets.py` floor \(\approx 30/13\) can finally be undercut.

---

#### Survey: known ways to beat MVT for Dirichlet polynomials over characters mod \(q\), \(T\) small

| Method | What it does | Status at our \((\sigma,y)\) / for characters |
|---|---|---|
| Classical MVT / hybrid large sieve | (1.2): \(\|W\|\ll N^{2}/V^{2}+qTN/V^{2}\) | **Baseline**; binds at \(\alpha=2/3\) |
| Halász–Montgomery–Huxley LV | (1.3): \(+\,qTN^{4}V^{-6}\) | Beats MVT only for **large** \(\sigma\) (essentially \(\sigma>3/4\)); at \(\sigma=5/7\) Huxley is *worse* than MVT |
| Montgomery’s large-value conjecture (modified) | With \(\|b_{n}\|_{\infty}\le1\): \(\|W\|\lessapprox N^{2-2\sigma}\) (density hypothesis) | **Open**, “far beyond current techniques” (Guth survey arXiv:2503.07410, Conj. 3.3). Original *unrestricted* form **false** (Bourgain, geometric-series / \(\ell^{2}\)-normalised counterexample, early 90s; cf. IHES M/90/31) |
| Bourgain restricted-support / wave-packet LV | Gains for special coefficient support; also Kakeya implications of Montgomery | Different \((N,V)\) regimes; already partially spent in block detectors (`bourgain_restrict`, Batch 3 #01 Dead) |
| Guth–Maynard (arXiv:2405.20552), **\(q=1\)** | Cubic singular-value + Poisson *without* stationary phase + affine equidistribution + Heath-Brown energy → first improvement of MVT for \(N^{7/10}<V<N^{8/10}\), \(N\le T^{5/6}\) | Engine behind CGL; **excluded from re-derivation** (exclusion list). Gives \(30/13\) for \(\zeta\) |
| CGL (arXiv:2507.08296) | Character adaptation of GM | Uniform \(A=7/3\); \(30/13\) only when \(q\) is \(T\)-smooth / has good factors |

**Guth–Maynard \(q=1\) mechanism vs what fails in the \(q\)-aspect (pinpoint, no re-derivation).**

GM’s post-cubic-trace pipeline (sketch §2 of arXiv:2405.20552) produces, before subdivision,

\[
|W|\lessapprox T^{1/2}+T^{4/3}N^{-1}.
\]

When \(T\ge N^{6/5}\) the second term dominates; **\(T\)-subdivision** (cut \([0,T]\) into \(T/T_{0}\) pieces
balancing the two terms) upgrades this to \(|W|\lessapprox T^{1/2}+TN^{-3/5}\), which is what feeds
\(30/13\).

CGL’s analogous bound is (their (2.4))

\[
|W|\lessapprox(qT)^{1/2}+(qT)^{4/3}N^{-1}.
\]

**The step that fails for characters / prime \(q\):** the \(T\)-subdivision upgrade has **no full
\(q\)-analogue**. CGL §2 (after (2.5)): *“Subdivision in the \(q\)-aspect involves splitting \(q\) into
its factors. For general moduli \(q\), this is not available.”* Prime moduli are the worst case. (A
second, related obstruction is that character twists insert **GCD weights** \((am_{1}+bm_{2}+m_{3},q)\)
into the affine sums; CGL Prop. 8.1 controls those but does not restore subdivision.) So the mechanism
that turns GM’s intermediate bound into \(30/13\) is exactly the piece missing uniformly in \(q\).

---

#### Numerics: can MVT-extremisers coexist with \(S_3\)-extremisers?

Script: `scripts/density_hunt/mvt_s3_coexist.py` (q=1009, 10007; N=q^{7/9}, R=q^{2/3}, T=1).

| sample | q=1009 | q=10007 |
|---|---|---|
| ADV (tpm) `@R`: sharp_mvt = \(\sum_W\|D\|^2/((q+N)\|c\|_2^2)\) | 0.675 | 0.626 |
| ADV `@R`: \|W\|/Wbound_mvt | 0.180 | 0.220 |
| ADV `@R`: S3/CGL | 0.549 | 0.628 |
| ADV `@R`: Vmin / N^{5/7} | 0.032 | 0.014 |
| ADV at **critical** \(V=N^{5/7}\): \|W_crit\| | **0** | **0** |
| short-interval coeffs `@R`: S3/CGL | 0.08–0.24 | 0.06–0.11 |
| flat / rand: V-crit \|W\| | 1 | 1 |

**Label: Numerical.**

- \(S_3\)-near-extremal (tpm) \(W\) of size \(q^{2/3}\) uses \(\sim 0.6\) of the MVT \(\ell^{2}\) budget on those
  characters, and sits a **constant** factor \(\sim 5\) below the MVT cardinality bound
  (\(|W|/W_{\mathrm{bound}}\approx 0.2\) at both primes — **not** a power of \(q\)).
- At the actual critical height \(V=N^{5/7}\), ADV configs produce **no** large values
  (\(|W_{\mathrm{crit}}|=0\)); top-\(R\) values are \(\ll N^{5/7}\). Short-interval / flat coeffs likewise
  fail to saturate MVT at critical \(V\) (at most the principal character).
- So the two extremal regimes **do not appear to coexist** at these finite \(q\): structured
  \(S_3\)-extremisers are not critical-\(V\) large-value sets, and MVT-friendly short supports give
  small \(S_3\).

**Hybrid quantification (honest).** An \(O(1)\) factor in \(|W|/W_{\mathrm{bound}}\) is **not** an
exponent saving: \(\log C/\log q\to 0\). A hybrid bound beating \(\alpha=2/3\) would require a
*structural* theorem that every near-\(S_3\)-extremal \(W\) obeys
\(|W|\ll q^{2/3-\varepsilon}\) at \(V=N^{5/7}\), or that every critical-\(V\) large-value set has
\(S_3\ll q^{2-\delta}|W|^{3/2}\). The numerics are consistent with such a split but **do not prove**
one and **do not quantify** an asymptotic \(\varepsilon>0\). Verdict: hybrid remains **Heuristic /
unproven**; no claimed improvement of \(A\).

---

### (B) Concrete conjectural inequalities

#### `decoupling_char` — Conjecture (Partial / long-shot)

**Target object.** CGL Proposition 8.1 / sketch (2.2): for a family \(\{f_b\}_{b\bmod q}\) of
non-negative smooth functions supported on \(u\asymp 1\) with Fourier decay
\(\sum_b|\hat f_b(\xi)|\lessapprox_j (T/|\xi|)^j\,\phi(q)\,\|f\|_\infty\), and \(0<M\le(qT)^{\varpi}\),

\[
J(\vec f)=\sup_{M_i\le M}\int\sum_a\Bigl(\sum_{b,|m_i|\sim M_i}f_b\Bigl(\tfrac{m_1u+m_3}{m_2}\Bigr)\,(am_1+bm_2+m_3,q)\Bigr)^2\,du.
\]

CGL proves \(J(\vec f)\lessapprox \phi(q)M^6\bigl(\int\sum f_b\bigr)^2+\phi(q)^2 M^4\int\sum f_b^2\).

**Conjectural improvement (decoupling form).** For some absolute \(\theta>0\),

\[
J(\vec f)\lessapprox \phi(q)^{1-\theta}M^6\Bigl(\int\sum_b f_b\Bigr)^2+\phi(q)^{2-\theta}M^4\int\sum_b f_b^2,
\]

in the range of parameters feeding CGL’s \(S_3\) at \(N\ge(qT)^{2/3}\) (equivalently: a
Bourgain–Demeter-type \(\ell^{2}\) decoupling for the GCD-twisted affine extension operator at the
scale of Prop. 8.1). Weaker variants (saving only on the \(M^6\) term, or only for \(f_b\) constant in
\(b\)) would still help.

**Exponent consequence at \(\sigma=5/7\).** A factor \(q^{-\delta}\) in \(S_3\) (i.e.
\(S_3\lessapprox q^{2-\delta}|W|^{3/2}\)) replaces \(c=4/3\) by \(c=4/3-2\delta/3\). Then
`delta_targets.py` / `price.py`: peak \(A\) drops as \(7/3-2\delta/3\), **floored at \(30/13\)** once
\(\delta\gtrsim 1/26\) (when MVT/GM glue takes over). So even a full decoupling win against Prop. 8.1
**does not by itself** break the \(\approx 2.308\) floor — that still needs `mvt_beyond`.

**vs known counterexamples.** Does **not** contradict Bourgain’s disproof of unrestricted Montgomery
(different normalisation: \(\ell^{2}\) vs \(\ell^{\infty}\), and a different matrix). The two model
extremisers for Prop. 8.1 (random \(f\) saturating the \(M^6\|f\|_1^2\) term; rationals \(r/s\)
saturating the \(M^4\|f\|_2^2\) term — CGL/GM §9) show both terms are needed in general; a
\(\phi(q)^{-\theta}\) saving on *both* is a genuine strengthening, not ruled out by those examples,
but also **not implied** by any published decoupling theorem for Dirichlet characters.

**Label: Partial / long-shot.** Worth pursuing only as a tool against Remark 12.3’s \(S_3\), and only
jointly with `mvt_beyond` if the goal is \(A<30/13\).

---

#### `poly_partition_q` — Conjecture (Partial / long-shot)

**Target.** Same \(J(\vec f)\) / same \(S_3\) pipeline, attacked by **polynomial partitioning** (Guth) /
polynomial method on the incidence set

\[
\bigl\{\bigl(u,\tfrac{m_1u+m_3}{m_2}\bigr): |m_i|\sim M_i\bigr\}
\]

with GCD multiplicity \((am_1+bm_2+m_3,q)\), aiming to improve the high-energy / structured term of
Prop. 8.1 (or the energy-weighted bound feeding Prop. 10.1 / 11.1).

**Conjectural inequality (incidence form).** For \(0<\theta\le 1\) and \(f\) as above,

\[
\int\sum_a\Bigl(\sum_{b,m}f_b\Bigl(\tfrac{m_1u+m_3}{m_2}\Bigr)\,(am_1+bm_2+m_3,q)\Bigr)^2\,du
\ \ll\ \phi(q)\,M^{6-\theta}\Bigl(\int\sum f\Bigr)^2+\phi(q)^2 M^{4-\theta/2}\int\sum f^2,
\]

or any saving that, once inserted into CGL (2.3)–(2.4), yields \(S_3\lessapprox q^{2-\delta}|W|^{3/2}\)
with \(\delta>0\).

**Exponent consequence at \(5/7\).** Identical bookkeeping to decoupling: \(\delta\) in \(S_3\) →
\(A\mapsto 7/3-2\delta/3\), floored at \(30/13\) by MVT. No path to \(A<30/13\) without also beating
MVT.

**vs known counterexamples.** The rational example saturating \(M^4\|f\|_2^2\) in Prop. 8.1 is a
**structured** incidence configuration; partitioning methods are designed precisely for such
structure, so there is no immediate contradiction — but also no theorem. GM already *is* a
Fourier/incidence advance; a further partitioning step must save on the **GCD-twisted** form, which
is the new arithmetic difficulty CGL introduced. Not implied by the \(q=1\) theory.

**Label: Partial / long-shot.** Same strategic role as `decoupling_char`: speculative \(S_3\) tool,
not a soft win, and subordinate to `mvt_beyond` for breaking \(30/13\).

---

### Batch 4 summary

| id | verdict | concrete output |
|---|---|---|
| `mvt_beyond` | **Partial (key)** | Exact MVT use: CGL (1.2) at \((\sigma,y)=(5/7,7/9)\) binds via \(1+y(1-2\sigma)=2/3\). Minimal inequality stated. Montgomery modified conjecture open; Bourgain killed unrestricted form. GM \(q=1\) subdivision is the step that fails for prime \(q\). Numerics: S₃- and MVT-extremisers do not coexist at critical \(V\), but slack is \(O(1)\) → **no quantified hybrid exponent**. |
| `decoupling_char` | Partial / long-shot | Conjectural \(\phi(q)^{-\theta}\) saving on Prop. 8.1’s \(J(\vec f)\); ⇒ \(S_3\) \(\delta\)-saving ⇒ \(A\le 7/3-2\delta/3\) floored at \(30/13\). No counterexample collision; not implied by BD. |
| `poly_partition_q` | Partial / long-shot | Conjectural incidence saving on the same GCD-twisted affine sums; same \(5/7\) bookkeeping as decoupling. |

### Inequality worth pursuing

**Primary:** the `mvt_beyond` LV hypothesis at \((y,V)=(7/9,N^{5/7})\) —

\[
|W|\ll(qT)^{o(1)}\bigl(N^{2}V^{-2}+(qT)^{1-\eta}NV^{-2}\bigr)\quad(\eta>0),
\]

for 1-bounded Dirichlet polynomials over characters, \(T\) small / \(T=1\). This is mandatory for
\(A<30/13\) under the CGL architecture, and historically the hard face of the cube.

**Secondary (only with the above):** any \(\delta>0\) saving in CGL Prop. 8.1 / \(S_3\) via decoupling
or polynomial partitioning — valuable toward Remark 12.3, but by itself freezes at \(\approx 2.308\).

**No improvement of \(A\) claimed. No Lean. Docs/scripts only.**


---

## Batch 5 — Attack: try to prove (`J(f)` saving + MVT-beyond)

Mandate: move from mapping to line-by-line attempts. Scripts:
`scripts/density_hunt/j_prop81_probe.py`, `scripts/density_hunt/mvt_beyond_attack.py`.
**No genuine inequality proved.** Strongest outputs are negative (tightness / stall maps)
and Numerical fits.

---

### Attack 1 — power saving on CGL Prop. 8.1’s `J(f)` at prime `q`

#### Explicit `J(f)` (arXiv:2507.08296, Prop. 8.1)

For a family \(\vec f=\{f_b\}_{1\le b\le q,\ (b,q)=1}\) of non-negative smooth functions
supported on \(|u|\ll 1\), with Fourier decay
\(\sum_b|\hat f_b(\xi)|\lessapprox_j(T/|\xi|)^j\,\phi(q)\,\|f\|_\infty\), and \(0<M\le(qT)^{\varpi}\),

\[
J(\vec f)=\sup_{0<M_i<M}\int_{\mathbb{R}}\sum_{\substack{1\le a\le q\\(a,q)=1}}
\Biggl(\sum_{\substack{1\le b\le q\\(b,q)=1}}\sum_{\substack{|m_1|\sim M_1\\ m_2\sim M_2\\ |m_3|\ll M_3}}
f_b\Bigl(\frac{m_1u+m_3}{m_2}\Bigr)\,(am_1+bm_2+m_3,q)\Biggr)^2\,du.
\]

CGL proves

\[
J(\vec f)\lessapprox \phi(q)\,M^6\Bigl(\int\sum_b f_b\Bigr)^2+\phi(q)^2 M^4\int\sum_b f_b^2.
\]

**Prime `q` simplification.** \((L,q)\in\{1,q\}\), so the weight is
\(1+(q-1)\mathbf{1}_{L\equiv 0\pmod q}\). For a single channel \(b\) and \(M<q\)
(so \(m_1\not\equiv 0\)), writing \(A=\sum_m f(\mathrm{affine})\) and
\(H_a=\sum_{m:\,am_1+bm_2+m_3\equiv 0}f(\mathrm{affine})\),

\[
\sum_{a=1}^{q-1}S_a(u)^2=3(q-1)A(u)^2+(q-1)^2\sum_a H_a(u)^2,
\]

with \(\sum_a H_a=A\). The second summand is the GCD-hit contribution and dominates
numerically (below).

#### Tight sub-cases in CGL’s proof (from their / GM §9 discussion)

1. **Random / L¹-saturating:** \(f\) a smooth bump of measure \(\asymp 1\) → first term
   \(\phi(q)M^6\|f\|_1^2\) is sharp up to \((qT)^{o(1)}\).
2. **Rational / L²-saturating:** \(f\) a \(1/T\)-neighbourhood of \(\{r/s:r,s\sim B\}\) →
   second term \(\phi(q)^2 M^4\|f\|_2^2\) is sharp (approximate closure under
   \(u\mapsto(m_1u+m_3)/m_2\)).

Any power saving \(\phi(q)^{-\theta}\) must beat **both** model extremisers, or show that
in the CGL application range the rational extremiser cannot arise from a large-value set \(W\).

---

#### Route (i) — ℓ² decoupling / finite-field restriction
**Attempt.** View the affine extension \(u\mapsto(m_1u+m_3)/m_2\) as a curved
restriction problem. Mockenhaupt–Tao (Duke Math. J. 2004, arXiv:math/0204234):
restriction for the parabola in \(\mathbb{F}_p^2\), \(R^*(2\to 4)\) bounded. Bourgain–Demeter
ℓ² decoupling is Euclidean (Annals 2015) and has \(p\)-adic analogues, not a direct
\(\mathbb{F}_p\) theorem for Möbius orbits.

**Line-by-line stall.**
1. Prop. 8.1’s integrand is a **triple product** \(R(v_1)R((m_1v_1+m_3)/(m_2v_1))R((m_1v_1+m_3)/m_2)\)
   averaged over \(\vec m\), not the Fourier extension of a single hypersurface measure.
2. The GCD weight \((am_1+bm_2+m_3,q)\) is an arithmetic multiplicity absent from MT/BD.
3. Reducing to a parabola restriction would require freezing two of three Möbius parameters
   and absorbing the third into a phase — the resulting phase is linear fractional, not
   quadratic; MT does not apply as stated.
4. Even a sharp \(\mathbb{F}_p\) decoupling for \(\mathrm{PGL}_2\) orbits is not in the literature
   in a form that yields \(\phi(q)^{-\theta}\) on both CGL terms.

**Verdict: Dead as an off-the-shelf import. Partial as a research programme** (would need a
new decoupling theorem for GCD-twisted Möbius averages).

#### Route (ii) — Stepanov / Weil / Deligne complete sums
**Attempt.** Complete the \(m\)-sums in \(H_a\) against an additive character, apply Weil
bound \(|\sum_x e_q(f(x))|\ll \deg\sqrt{q}\) for non-trivial square-free \(f\).

**Line-by-line stall.**
1. \(f_b\) in Prop. 8.1 is an **arbitrary** smooth function with Fourier decay (coming from
   \(|R|^2\) smoothed), not an algebraic function of bounded degree.
2. Inserting a smooth \(f\) via Melin/Fourier expands into many frequencies; Weil gives
   \(\sqrt{q}\) per frequency, but the number of significant frequencies is \(\asymp T\)
   (the decay scale), and \(T\) can be as large as the CGL application allows — the
   \(\sqrt{q}\cdot T\) reconstruction rebuilds at best the trivial bound.
3. The rational extremiser is **combinatorial** (many affine relations over \(\mathbb{Q}\)),
   not oscillatory; complete-sum cancellation is the wrong tool against it.
4. Stepanov’s method likewise needs polynomial equations of controlled degree.

**Verdict: Dead** for a uniform saving against both extremisers.

#### Route (iii) — point-line incidences over \(\mathbb{F}_p\) (Stevens–de Zeeuw, Rudnev)
**Attempt.** Cast \(\bigl(u,\,(m_1u+m_3)/m_2\bigr)\) as incidences between a point set
(support of \(f\)) and a line set indexed by \(\vec m\). Stevens–de Zeeuw: for
\(P=A\times B\) and lines \(L\),
\(I(P,L)\ll |A|^{3/4}|B|^{1/2}|L|^{3/4}+|P|+|L|\) (under small-set constraints).
Rudnev: point-plane incidences in \(\mathbb{F}^3\).

**Line-by-line stall.**
1. GCD multiplicity again: geometric incidence counts each line once; Prop. 8.1 weights
   some triples by \(q\). Reducing GCD-hits to a congruence hyperplane replaces one
   incidence problem by a thinner one, but the weight \(q\) puts a factor back.
2. Small-set hypothesis \(|P|^{13}|L|^{-2}<p^{15}\) (Stevens–de Zeeuw general form): with
   \(|L|\sim M^3\sim q^{2/3}\) (critical \(M\sim q^{2/9}\)) this constrains \(|P|\) above
   which the bound fails — the rational extremiser’s effective \(|P|\) after \(1/T\)-smoothing
   sits near the boundary.
3. Optimistically inserting ST-type saving into \(\int\sum_a H_a^2\) improves the second
   CGL term by a fractional power of \(M\), hence a \(\delta\) in \(S_3\) of size
   \(O(1/\log q)\) or a small fixed \(\delta\) at best — **not enough alone** to break
   \(A=7/3\) past the MVT floor at \(30/13\) without `mvt_beyond` (Batch 4 bookkeeping).
4. No written inequality obtained; the incidence dictionary is plausible but lossy.

**Verdict: Partial / stalled** — best-looking geometric route, no theorem.

#### Route (iv) — Bourgain–Katz–Tao sum-product in \(\mathbb{F}_p\)
**Attempt.** If \(U=\mathrm{supp}(f)\) has small multiplicative energy, affine images
\((m_1U+m_3)/m_2\) expand and overlaps in \(J\) drop.

**Line-by-line stall.**
1. The **rational extremiser** is essentially closed under the affine maps in question —
   \(U\cdot U\approx U\) in the strong sense of many representations \(r/s\). Sum-product
   non-triviality **fails exactly on the configuration that saturates the second CGL term**.
2. On the random extremiser, sum-product is not the bottleneck (the first term already
   matches \(M^6\|f\|_1^2\) by Cauchy-Schwarz, no energy input).
3. Therefore BKT cannot yield a saving that covers both tight cases.

**Verdict: Dead** against the rational extremiser; irrelevant to the random one.

---

#### Numerics for `J(f)` — `j_prop81_probe.py` (**Numerical**)

Discrete single-channel model with the exact prime-`q` GCD expansion above; grid \(G=128\) on
\([1/2,2]\); \(M=\min(8,\lceil q^{2/9}\rceil)\); kinds = random / rational / flat.
CGL comparison: \(T_1=q M^6\mathrm{mass}^2\), \(T_2=q^2 M^4\mathrm{mass}_2\).

| q | kind | J/(T1+T2) | JH/JA |
|---|---|---|---|
| 103 | flat | 0.229 | 4.0 |
| 223 | flat | 0.220 | 8.6 |
| 509 | flat | 0.206 | 10.4 |
| 1013 | flat | 0.212 | 13.8 |
| 2011 | flat | 0.209 | 27.3 |
| 3011 | flat | 0.215 | 29.3 |
| 103–3011 | random | 0.09–0.17 | 8–45 |
| 103–3011 | rational | 0.11–0.17 | 8–47 |

Fit \(\log J\sim a+b\log q\), \(\log(T_1+T_2)\sim c+d\log q\):

| kind | slope_J | slope_bound | apparent saving \(d-b\) |
|---|---|---|---|
| flat | 2.812±0.097 | 2.833±0.095 | **0.021±0.136** |
| random | 2.719±0.039 | 2.836±0.090 | 0.117±0.098 |
| rational | 2.707±0.080 | 2.851±0.093 | 0.144±0.123 |

**Reading (honest).**
- Flat ratio is **stable ≈0.21** across \(q\in[10^2,3\cdot 10^3]\); fitted saving consistent with **0**.
- Random/rational show a mild positive saving inside ~1–1.5σ — **not** significant evidence of
  \(\phi(q)^{-\theta}\); could be \(M(q)\)-clamping / single-channel / grid artefacts.
- JH ≫ JA: the GCD-hit term dominates, so any real attack must save on \(\sum_a H_a^2\).
- **Caveats:** single \(b\)-channel (multi-\(b\) is the full Prop. 8.1); small \(M\); continuous
  \(u\)-grid proxy; CGL’s \(\lessapprox\) hides \((qT)^{\varepsilon}\) and absolute constants.
  This does **not** prove sharpness, but it **fails to support** a power saving large enough
  to matter for \(A\).

**Attack 1 strongest result:** no inequality; numerics + stall map. Flat extremiser looks
order-sharp for the \(\phi(q)^2 M^4\) scale. **Label: Numerical + Dead/Partial by route.**

---

### Attack 2 — MVT-beyond at \((y,V)=(7/9,N^{5/7})\)

Target inequality (**Heuristic**, from Batch 4):

\[
|W|\ll N^2V^{-2}+(qT)^{1-\eta}NV^{-2}\qquad(\eta>0),\quad T\ \text{small},\ q\ \text{prime}.
\]

#### (H1) Amplify the O(1) coexistence slack into a power
**Idea.** Batch 4: ADV configs have \(|W|/W_{\mathrm{MVT}}\approx 0.18\text{–}0.22\). Dirichlet-power
amplification on the discrete-log group (`mvt_beyond_attack.py`).

**Numerical.** At \(q=10007\): ratio \(0.226\,(k=1)\to 0.086\,(k=2)\to 0.019\,(k=3)\), but
\(\alpha_{\mathrm{mvt,emp}}\) **increases** \(0.83\to 0.93\to 1.10\) (c₂ grows under convolution).
Slack shrinks as a constant, not as \(q^{-\varepsilon}\).

**Stall.** No renormalisation of \(V\) turns this into a uniform \(\eta>0\) in the density
exponent: the large-value threshold and the coefficient \(\ell^2\) mass co-vary. Iterating
does not produce a power of \(q\).

**Verdict: Dead** as a path from O(1) slack → \(\eta>0\).

#### (H3) Direct η-test on ADV and flat at top-R threshold
Measure \(|W|/[(q^{1-\eta}+N)c_2/V_R^2]\) with \(V_R=\) the \(R\)-th largest \(|D|\) so \(|W|\sim R=q^{2/3}\).

| q | config | η=0 | η=0.1 | η=0.2 | η=0.3 | η=0.5 |
|---|---|---|---|---|---|---|
| 1009 | ADV | 0.18 ✓ | 0.31 ✓ | 0.47 ✓ | 0.65 ✓ | 0.89 ✓ |
| 10007 | ADV | 0.22 ✓ | 0.47 ✓ | 0.86 ✓ | **1.29 ✗** | **1.79 ✗** |
| 30011 | ADV | 0.22 ✓ | 0.53 ✓ | **1.06 ✗** | **1.65 ✗** | **2.27 ✗** |
| 1009–30011 | flat | ≤0.17 ✓ | ≤0.29 ✓ | ≤0.44 ✓ | ≤0.60 ✓ | ≤0.83 ✓ |

**Reading.** ADV’s room for \(\eta\) **shrinks with \(q\)**: the largest η that holds is
\(>0.5\) at \(q=1009\), \(\approx 0.2\) at \(q=10007\), \(<0.2\) at \(q=30011\). Extrapolation:
any fixed \(\eta>0\) eventually fails on ADV-type configs. Flat retains slack, but density
estimates need the **worst** case.

**Verdict: Dead** for a uniform positive \(\eta\) (Numerical evidence against).

#### (H2) Multiplicative-subgroup subdivision of \((\mathbb{Z}/q\mathbb{Z})^\times\)
**Idea.** Replace GM’s factor-subdivision of \(q\) by cosets of a subgroup
\(H\le(\mathbb{Z}/q\mathbb{Z})^\times\cong\mathbb{Z}/(q-1)\), apply a local LV bound on each coset.

**Numerical / structural stall.**
1. For prime \(q\) with \(q-1=2p'\) (safeprime-ish, e.g. \(q=10007\)), subgroups are trivial —
   no intermediate \(|H|\sim q^{\alpha}\).
2. When subgroups exist (\(q=1009\), \(q-1=1008\)), pieces of ADV top-\(R\) have small S₃/CGL
   (\(\sim 10^{-3}\)) and \(\alpha_{\mathrm{piece}}\sim 0.2\text{–}0.35\), but the number of cosets is
   \(q^{1-\alpha}\). Union bound rebuilds
   \(|W|\ll q^{1-\alpha}\cdot q^{\alpha_{\mathrm{piece}}}\), which beats \(q^{2/3}\) only if
   \(1-\alpha+\alpha_{\mathrm{piece}}<2/3\), i.e. \(\alpha>1/3+\alpha_{\mathrm{piece}}\gtrsim 0.5\text{–}0.7\) —
   then each piece is so large that the local bound does not improve on MVT.
3. Characters in a coset of \(H\) are not a spectral window for the GCD-twisted forms; the
   CGL matrix \(M_W\) does not block-diagonalise over cosets.

**Verdict: Dead** for prime \(q\) (structural, with Numerical confirmation).

#### (H2b) Additive \(t\)-twist shifts as fake subdivision
**Idea.** Use \(\chi(n)n^{it}\) shifts to mimic \(T\)-subdivision inside one character.

**Stall.** At the Linnik/CGL critical point one takes \(T=1\) (one point per character;
Remark 12.3). There is no \(t\)-room to subdivide. For \(T>1\) this is ordinary GM
\(T\)-subdivision, already available and already used by CGL when \(T\) is large; it does
not help the **\(q\)-aspect** prime-modulus bottleneck.

**Verdict: Dead** at the binding \((T=1)\) point.

---

### Batch 5 summary

| Attack | Route | Verdict | Strongest output |
|---|---|---|---|
| 1 | (i) decoupling / MT | Dead as import / Partial as programme | Stall: triple Möbius + GCD ≠ parabola restriction |
| 1 | (ii) Weil / Deligne | **Dead** | Stall: \(f\) not algebraic; rational extremiser combinatorial |
| 1 | (iii) incidences SdZ/Rudnev | **Partial / stalled** | Plausible dictionary; GCD weight + small-set limits; no theorem |
| 1 | (iv) BKT sum-product | **Dead** | Fails on the rational extremiser |
| 1 | Numerics `J/(T1+T2)` | **Numerical** | Flat ratio ≈0.21 stable; saving 0.02±0.14 (null) |
| 2 | (H1) amplify slack | **Dead** | Constant shrinks, not \(q^{-\varepsilon}\) |
| 2 | (H3) η-test | **Dead** (uniform η) | ADV breaks any fixed η as \(q\) grows |
| 2 | (H2) subgroup subdiv | **Dead** | Safeprime \(q-1\); covering kills gain |
| 2 | (H2b) t-twist subdiv | **Dead** | No room at \(T=1\) |

### Inequality worth pursuing after the attack

**None proved.** The only route not killed outright is Attack 1(iii) (incidences on the
GCD-hit sum \(\sum_a H_a^2\)), and even an optimistic saving there is bookkept to land at
the MVT floor \(30/13\) without a separate `mvt_beyond` theorem — which Attack 2’s numerics
now make look **harder**, not easier (ADV saturates reduced MVT bounds as \(q\to\infty\)).

Revised priority:
1. Still need a new idea for `mvt_beyond` (Attack 2 closed the obvious amplification /
   subdivision loopholes).
2. Attack 1(iii) remains a long-shot for Remark 12.3’s \(S_3\), subordinate to (1) for
   \(A<30/13\).

**No improvement of `A` claimed. No Lean. Docs/scripts only.**


---

## Batch 6 — Attack continued: incidences on `∑_a H_a²` + proper η-fit

Scripts: `scripts/density_hunt/incidence_Ha2.py`, `scripts/density_hunt/mvt_eta_fit.py`.

---

### (1) Incidences on `∑_a H_a²` — exact problem, hypotheses, bookkeeping, numerics

#### Exact incidence problem (discrete, prime `q`, single channel `b=1`)

Identify the support of a non-negative `f: F_q → R` with a set `U ⊂ F_q` (indicator case
`f=1_U`; general `f` by level sets). Let `M ≥ 1` and

\[
L_M=\Bigl\{\ell_{\mathbf{m}}:v=\frac{m_1}{m_2}u+\frac{m_3}{m_2}\ \Big|\ m_i\in\{1,\dots,M\}\Bigr\}
\subset\{\text{affine lines in }\mathbb{F}_q^2\},
\]

so `|L_M|=M^3` (before reducing duplicates). Point set: the **Cartesian product**
`P=U×U ⊂ F_q²`. An incidence is `( (u,v), \ell_m )` with `v=α_m(u)`.

GCD-hit subfamily (Prop. 8.1 weight): for each `a ∈ F_q^*`,

\[
L_a=\{\ell_{\mathbf{m}}\in L_M: a m_1 + m_2 + m_3 \equiv 0\pmod q\}.
\]

For `m_1\not\equiv 0` (automatic if `M<q`) each line lies in **exactly one** `L_a`, so as
*sets* `⊔_a L_a = L_M`. The factor `q` in the GCD weight is already encoded by using
`H_a` rather than a weight-1 sum: 

\[
H_a(u)=\sum_{\ell_m\in L_a}f(\alpha_m(u)),\qquad
\sum_{a}\|H_a\|_{\ell^2(u)}^2
=\sum_{\mathbf{m},\mathbf{m}'}\mathbf{1}_{\mathrm{compat}}\!\sum_u f(\alpha_m(u))f(\alpha_{m'}(u)).
\]

Compatible pairs are pairs of lines that share an `a`-slot (concurrent in the
`(m_1,m_2,m_3)` congruence). Bounding this by Cauchy–Schwarz on fibres reduces to
controlling `I(P,L_M)` (and pair incidences); that is the incidence problem.

**Rudnev point-plane lift (optional dictionary).** Viewing
`(u, m_2, m_1 u+m_3)` in `F_q³` with planes from the congruence/`v`-condition is possible
but not needed for the primary point-line form above; Rudnev’s hypothesis
`|Q|<q²` and a collinearity parameter `k` would have to be checked after the lift. We use
point-line bounds as the main tool.

#### Which hypotheses hold at CGL criticality?

Critical parameters: `T=1`, `N=q^{7/9}`, `M∼qT/N=q^{2/9}`, `|L|=M³=q^{2/3}`, `|U|=q^β`,
`|P|=q^{2β}`.

| Theorem | Statement (scale) | Hypothesis at criticality | Verdict |
|---|---|---|---|
| **Stevens–de Zeeuw Cartesian** | `I(A×B,L) ≪ \|A\|^{3/4}\|B\|^{1/2}\|L\|^{3/4}+\|A\|\|B\|+\|L\|` | General form needs `|P|^{13}|L|^{-2}<q^{15}` ⇒ **`β<49/78≈0.628`** | **Holds** for rational extremiser `β≈2/9` and for random `β≤1/2`; **fails** for `β≥2/3` (large/`flat`) |
| **Stevens–de Zeeuw general** | `I ≪ (|P||L|)^{11/15}+\|P\|+\|L\|` | Same small-set constraint | Same as above |
| **Vinh (large sets)** | `|I−|P||L|/q|≤√(q|P||L|)` so `I≤|P||L|/q+√(q|P||L|)` | None (all sizes) | Always applicable; **does not beat trivial** `I≤|U||L|=q^{β+2/3}` for `β≥2/3` (Vinh exponent `≥ β+5/6 > β+2/3`) |
| **Rudnev point-plane** | `I(Q,Π) ≪ |Q|^{1/2}|Π| + k|Q|` (roughly) with `|Q|<q²` | Needs a non-degenerate lift; collinear `k` from rational sets can be large | Not cleanly triggered for free; not used below |

**Small/large split.** Use SdZ on pieces with `β<0.628`, Vinh on the rest.

- **Rational extremiser (`β≈2/9`)**: SdZ applies. Exponent of `I`: trivial `β+2/3≈0.889`; SdZ `5β/4+1/2≈0.778`; Vinh `≈1.056` (worse than trivial). **Best available: SdZ, saving `Δ_I≈0.111` in the `log_q I` exponent.**
- **Large/`flat` (`β≥2/3`)**: SdZ fails; Vinh **worse than trivial**. Split does **not** improve on the trivial bound. The large part is controlled only by `I≤|U||L|`, which is what CGL’s L¹/CS already uses.

So the split **does** cover the rational extremiser with a fractional SdZ saving, and **does not** help the large/random-L¹ face.

#### Bookkeeping at `σ=5/7` — which face moves? (**Heuristic**, corrected)

CGL (2.3) / Prop. 10.1:

\[
S_3\lessapprox(qT)^2|W|^{3/2}+qTN|W|^{1/2}E(W)^{1/2}.
\]

- **First summand** ← Prop. 8.1’s `φ(q)M^6‖f‖₁²` (random/L¹ face) → after `M∼qT/N` gives the
  bound producing **`c=4/3`** and the `7/3` tie at `(σ,y)=(5/7,7/9)`.
- **Second summand** ← Prop. 8.1’s `φ(q)²M^4‖f‖₂²` / GCD-hit `∑‖H_a‖²` (rational/L² face) + energy.

**SdZ saves on the second face only.** It does **not** touch `(qT)^2|W|^{3/2}`, hence does
**not** reduce `c=4/3` or the binding `α=2/3` from the first face.

Optimistic conversion (Heuristic, **not proved**): `Δ_I≈0.111` on rational ⇒ at most
`δ≲Δ_I/2≈0.056` in a second-face `q^{2-δ}` — improves the *energy* pathway in (2.3), useful
when `E(W)` is large, but at the `7/3` critical point the first face already ties MVT at
`2/3`. After an energy-pathway-only saving:

\[
\min(\underbrace{1+y(1-2σ)}_{MVT=2/3},\underbrace{c_{\mathrm{first}}+y(2-4σ)}_{=2/3},\underbrace{\alpha_{\mathrm{energy}}}_{<2/3})=2/3,
\]

so **`A` stays `7/3`**. (Earlier Batch-5-style optimism that fed `δ` into `c=4/3` was
**wrong**: that `c` comes from the first face.)

**Best available incidence bound, stated explicitly (even if ≥ CGL for the binding face):**

At criticality, for the Cartesian incidence problem with `|U|=q^β`, `|L|=q^{2/3}`:

| regime | best bound on `I` | vs CGL’s use |
|---|---|---|
| `β<49/78` (incl. rational `2/9`) | SdZ: `≪ q^{5β/4+1/2}+q^{2β}+q^{2/3}` | Beats trivial by `Δ_I=β+2/3−(5β/4+1/2)=(2/3−1/2)−β/4=1/6−β/4` (`=1/9` at `β=2/9`) on the **non-binding** face |
| `β≥49/78` | trivial `≪ q^{β+2/3}` (Vinh worse) | Same as CGL L¹ input; **no gain** |

No improvement of the binding `7/3` exponent from available incidence theorems.

#### Numerics — `incidence_Ha2.py` (**Numerical**)

`I(U×U, L_M)` for random and rational `U`, `M=⌈q^{2/9}⌉` capped at 6, `q∈{509,1013,2011,3011}`:

| q | kind | β-target | I/triv | SdZ_ok |
|---|---|---|---|---|
| 509–3011 | random | 2/9 | 0.003–0.023 | True |
| 509–3011 | rational | 2/9 | 0.08–0.18 | True |

Rational incidences sit **well below** both trivial and SdZ (SdZ not sharp on these samples).
Fit for rational `β≈2/9`: `slope_I=0.58±0.16` vs `slope_triv=0.76±0.13` (theory `0.889`);
apparent saving `0.17±0.20` — consistent with a fractional saving but **not** significant, and
in any case on the non-binding face.

**Attack 1(iii) verdict after Batch 6:** Partial tool for the energy/rational face; **Dead as a
path to `A<7/3`** with present incidence theorems, because the binding `(qT)^2|W|^{3/2}` face is
untouched and the large-set half of a Vinh split does not improve on trivial.

---

### (2) MVT-beyond — η grid + growth-exponent fit (**Numerical**)

Method (`mvt_eta_fit.py`): for primes
`q∈{503,1009,2003,5003,10007,20011,30011}`, ADV tpm configs at `V=V_R` (so `|W|∼q^{2/3}`),
η-grid `{0,0.01,…,0.20}`,

\[
\mathrm{ratio}(q,\eta)=\frac{|W|}{(q^{1-\eta}+N)\,c_2/V^2}.
\]

Fit `log ratio = a + ρ(η) log q`. A uniform `≪` with fixed η requires **`ρ(η)≤0`**
(up to `q^ε`). Finite-q `ratio>1` is **not** a counterexample to `≪`.

**ADV results:**

| η | ρ | SE | ρ+1.96 SE | ρ≤0? |
|---|---|---|---|---|
| 0.00 | 0.024 | 0.034 | 0.090 | no (but ≈0 within ~1σ; classical MVT) |
| 0.05 | 0.077 | 0.034 | 0.143 | no |
| 0.10 | 0.126 | 0.034 | 0.193 | no |
| 0.15 | 0.169 | 0.034 | 0.236 | no |
| 0.20 | 0.203 | 0.035 | 0.271 | no |

- Largest η with point-estimate `ρ≤0`: **`0.00`**
- Largest η with conservative `ρ+1.96SE≤0`: **`0.00`**
- Pattern: `ρ(η)≈η` — ADV saturates the classical `q` scale, so replacing `q` by `q^{1-η}`
  makes the ratio grow like `q^η`.

**Flat control:** `ρ(η)<0` for all η∈[0,0.20] (conservative OK throughout) — flat leaves
increasing slack, irrelevant for worst-case density.

**Verdict:** **No η>0 is consistent with the ADV data.** Strengthens Batch 5’s Attack-2
negative, now with an honest `≪`-compatible statistical reading and larger `q` (to `3·10^4`).

---

### Batch 6 summary

| Item | Verdict | Result |
|---|---|---|
| Incidence formulation for `∑H_a²` | Written | Cartesian `U×U` vs affine `L_M`; GCD-hit = partition of `L_M` |
| SdZ on rational `β=2/9` | Hypothesis **holds**; saving `Δ_I=1/9` in exponent | Non-binding face only |
| Vinh on large `β` | Applicable but **worse than trivial** | Split does not help large face |
| Binding-face bookkeeping | **Dead for `A<7/3`** | First face of (2.3) untouched ⇒ `A` stays `7/3` |
| Incidence numerics | Numerical | Rational `I/triv∼0.1`; fit saving `0.17±0.20` (ns) |
| η-fit ADV | Numerical / **Dead for η>0** | `ρ(η)≈η>0` for all η∈(0,0.2]; best η=`0` |

### Inequality worth pursuing

Still **none proved**. Batch 6 closes the natural incidence loophole as a route past `7/3`
(wrong face) and confirms statistically that MVT-beyond with a fixed power `η>0` is not
visible in ADV data up to `q≈3·10^4`.

Remaining open directions (not claimed live without a new idea):
- Improve the **first** face of Prop. 8.1 / `(qT)^2|W|^{3/2}` (L¹/random), where incidences
  do not help.
- A structural theorem excluding ADV-type saturators at `V=N^{5/7}` simultaneously with
  near-extremal S₃ — beyond the O(1) slack already measured.

**No improvement of `A` claimed. No Lean. Docs/scripts only.**


---

## Batch 7 — outside the zero-detection + large-values architecture

CGL’s LV/detector cube is saturated at `σ=5/7` (Batches 3–6). This batch asks for
openings that **avoid** that architecture: different inputs to Linnik, different objects
than `#{χ : N(σ,T,χ)≥1}`, or exotic tools. Weird is allowed; fabrication is not.

**Seed.** `98127453` (`scripts/density_hunt/seed_batch7.txt`), distinct from Batch 1
(`20261109`) and Batch 3 (`60783343`). Canonical id list shuffled by
`random.Random(98127453)`.

**Excluded / not re-done.** Anything already in this file or `cgl-s3` notes: Kuznetsov on
`b₂b₃` as tried, Deuring–Heilbronn as exceptional-zero repulsion (#16 Batch 2), Bombieri
*large sieve* (#08), `iwasawa_log` as *log-free density* (#02 — different from p-adic
Iwasawa below), GM/`mvt_beyond`/`decoupling`/`poly_partition`, moment detectors, etc.

**Linnik ledger (for “does Linnik need full `A`?”).** Formalised route:
`Linnik22000E.linnik_22000e` at `L=11/5` on a Type II window, using uniform density of
peak `A=7/3` (CGL at `σ=5/7`). Sieve floor `≳ 1+A/2` (`docs/research-opportunities.md` §3):
`A=7/3 ⇒ L≥13/6≈2.166`, with `2.199` the computed regeneration floor. Improving `L` below
`≈2.2` in *this* architecture needs `A<7/3`. Architecture changes that skip density
altogether are a different game (existence of some `L` vs beating `11/5`).

---

### 01. `de_branges` — Dead

**Idea.** de Branges’s Hilbert spaces of entire functions as a substitute structure for
`L(s,χ)` (Riemann–Hilbert / canonical systems), hoping for RH-quality zero control.

**Literature / obstruction.** de Branges’s claimed proof of RH is not accepted; no theorem
gives a zero-density exponent for Dirichlet `L`-functions from that formalism that beats
CGL. No path to a bound on `∑_χ N(σ,T,χ)`.

**Verdict: Dead.**

### 02. `hecke_cyclotomic` — Dead (worse exponents)

**Idea.** Pass to Hecke `L`-functions of the cyclotomic field `K=ℚ(ζ_q)`, apply
Weiss / Thorner–Zaman field-uniform log-free density, deduce character density as a
corollary.

**Bookkeeping.** `Dedekind ζ_K = ∏_{χ mod q} L(s,χ)` (up to archimedean factors). Zero
density for `ζ_K` *implies* a bound on `∑_χ N(σ,T,χ)`, but Weiss-type bounds are of shape
`(D_K Q)^{c(1−σ)}` with `D_K ≍ q^{φ(q)}` and `[K:ℚ]=φ(q)≍q`. The resulting exponent in `q`
is **far worse** than `7/3` (exponential in `q` from the discriminant). Thorner–Zaman
(arXiv:1510.08086, 1604.01750) make Weiss explicit for Chebotarev / least prime ideal —
valuable for number fields, not for beating Dirichlet `A=7/3`.

**Verdict: Dead** for `A<7/3` (wrong size of discriminant).

### 03. `iwasa_padic` — Dead for complex zeros in `T≍1`

**Idea.** p-adic `L`-functions / Iwasawa main conjecture control the µ/λ-invariants and
p-adic zeros of Kubota–Leopoldt `L_p(s,χ)`.

**Obstruction.** p-adic zeros are not the complex zeros counted by `N(σ,T,χ)` at
`T=1`, `σ=5/7`. Iwasawa theory does not bound the number of complex zeros off the
critical line in the CGL box. (Distinct from Batch 1’s `iwasawa_log` = log-free density.)

**Verdict: Dead.**

### 04. `jensen_weird_contour` — Dead

**Idea.** Jensen / argument-principle zero counting on non-rectangular contours (tilted
parallelograms, circles centred near `σ=5/7`) to gain from convexity or Phragmén–Lindelöf.

**Obstruction.** Contour moves change the integral of `|L'/L|`; without a better bound on
`L` or `L'/L` on the new contour (subconvexity in `q` at `σ=5/7` is not strong enough to
beat density methods), one recovers at best classical convexity-density hybrids already
inferior to CGL near `5/7`.

**Verdict: Dead.**

### 05. `slice_rank_W` — Dead

**Idea.** Croot–Lev–Pach / Ellenberg–Gijswijt slice-rank on the indicator of the
large-value set `W⊂(ℤ/(q−1)ℤ)` to force `|W|≪q^{2/3−ε}`.

**Obstruction.** Slice-rank caps sizes of *cap sets* / three-term AP-free sets in
`(𝔽_p)^n`. The set `W` of characters where a Dirichlet polynomial is large has no
reason to be AP-free; Batch 3’s energy numerics show nontrivial additive energy, i.e. the
opposite. No algebraic equation defines `W`.

**Verdict: Dead.**

### 06. `rankin_selberg_zeros` — Dead

**Idea.** Encode zeros of `L(s,χ)` as poles/residues of Rankin–Selberg
`L(s,χ₁×χ₂)` or Eisenstein series data, then use GL(2) spectral theory.

**Obstruction.** Rankin–Selberg for two Dirichlet characters is again a Dirichlet
`L`-function (or a shift). No new density. Eisenstein Fourier coefficients involve
`L(s,χ)` but spectral large-sieve / Kuznetsov returns to averaging over moduli or levels —
excluded flavour when used as in `cgl-s3` §11; as a zero-detector replacement it does not
produce a better pointwise-in-`q` count.

**Verdict: Dead.**

### 07. `bombieri_asymp_sieve` — Partial (architecture) / Dead for `L<11/5`

**Idea.** Bombieri’s asymptotic sieve with Selberg weights to detect primes in one class
`a mod q`, avoiding uniform zero density at `σ=5/7`.

**Literature.** Friedlander–Iwaniec’s sieve Linnik (dispense with log-free density and
repulsion; published exponent enormous, `L=75 744 000` in their account) and
Matomäki–Merikoski–Teräväinen’s prime-detecting sieve (`P(a,q)≪q^{350}`). These show
**some** `L<∞` without CGL-type density, but nowhere near `11/5`.

**Bookkeeping.** The formalised density→sieve floor `L≳1+A/2` is architecture-specific.
A pure-sieve proof can in principle beat `11/5` without touching `A`, but known sieve
Linnik exponents do not. Hybrid “use density where cheap + sieve where density binds” is
exactly the current paper’s shape; the binding still sits at `5/7`.

**Verdict: Partial** as a reminder that Linnik need not *logically* go through `A=7/3`.
**Dead** as a route to improve the formalised `11/5` with present sieve technology.
**Next step if revived:** track any new sieve Linnik with `L<3`; until then, park.

### 08. `furstenberg_W` — Dead

**Idea.** Furstenberg correspondence / ergodic structural theorems for the large-value set
`W` as a subset of the circle or of `ℤ/(q−1)`.

**Obstruction.** Correspondence principles yield multiple recurrence, not cardinality
bounds of the strength `|W|≪q^{2/3−ε}`. No ergodic input is known to beat combinatorial
energy bounds already probed in Batches 2–3.

**Verdict: Dead.**

### 09. `selberg_class_axioms` — Dead

**Idea.** Deduce density for all degree-1 Selberg-class elements from axioms (Euler
product, functional equation, Ramanujan) without LV.

**Obstruction.** Density theorems in the Selberg class still use zero-detection /
convexity / LV analogues; axioms alone do not improve Dirichlet exponents beyond what
CGL uses (Dirichlet `L` are the model degree-1 objects).

**Verdict: Dead.**

### 10. `chebotarev_linnik` — Dead for Dirichlet Linnik

**Idea.** Bound the least prime in an arithmetic progression via Chebotarev in a suitable
extension, using Thorner–Zaman explicit least-prime-ideal bounds.

**Bookkeeping.** For the progression `a mod q`, the cyclotomic extension again has
discriminant `≍ q^{φ(q)}`, giving superpolynomial-in-`q` bounds inferior to Linnik’s
polynomial `q^L`. Chebotarev is the right tool for general Galois conjugacy classes, not
for beating `q^{11/5}`.

**Verdict: Dead** for this problem.

### 11. `entropy_compression` — Dead

**Idea.** Entropy / information-compression bounds on the number of characters admitting a
zero in the CGL box (Lovász Local Lemma / entropy compression style).

**Obstruction.** Zeros of different `χ` are not a family of bad events with small
dependency degree in any known probabilistic model that is also rigorous for
`L`-functions. Random-matrix heuristics predict `|W|≍(qT)^{o(1)}N^{2−2σ}` (Montgomery),
which is stronger than `7/3` but not a proof.

**Verdict: Dead.**

### 12. `sieve_skip_density` — Partial (same as #07) / Dead for `11/5`

**Idea.** Maynard-style weights or modern prime-detecting sieves so that Linnik needs
density only for a **sparse** set of `(σ,T)`, or not at all.

**Assessment.** Same literature as #07 (FI, MMT). Maynard’s multidimensional weights
shine for bounded gaps / `m`-tuples, not for least prime in one progression with small
`L`. The density hypothesis (Montgomery) would give almost GRH-quality short intervals /
progressions, but that is again an unproved LV-type statement.

**Does the current sieve route need full uniform density at `5/7`?** In
`Linnik22000E`’s architecture: **yes** — the Type II window and peak `A` are pinned by the
worst `σ` on the density curve, which is `5/7` at `A=7/3`. Sparse-`T` density would help
only if the certificate could avoid that corner; the computed regeneration
(`tools/linnik/density_payoff.py` / research-opportunities §3) shows the corner is load-bearing.

**Verdict: Partial** (architecture escape exists in principle). **Dead** for improving
`11/5` today. **Next step:** watch sieve-Linnik exponents; no action inside LV.

### 13. `kuznetsov_theta_lift` — Dead as redo; note

**Idea.** Kuznetsov via theta lifts / Shimura correspondence (half-integral weight) as a
*new* spectral average, not the `cgl-s3` §11 `B=b₂b₃` try.

**Obstruction.** Still spectral averaging over a family (levels, nebentypus). Linnik /
uniform `A` need every prime `q`. Same obstruction as Batch 3 `kloosterman_avg_q` and the
exclusion of Deshouillers–Iwaniec/Kuznetsov as tried for the S₃ sum. A half-integral lift
does not remove the need to average.

**Verdict: Dead** for uniform `A` (averaged moduli).

### 14. `galois_orbit_W` — Dead for exponent (constant factor only)

**Idea.** `{χ : L(·,χ)` has a zero in the box`}` is closed under complex conjugation and
under `Gal(ℚ(ζ_{q−1})/ℚ)` acting by `χ ↦ χ^σ`. Orbit multiplicity ⇒ `|W|` divisible by
large orbit sizes ⇒ saving.

**Bookkeeping.** Conjugation gives factor `2`. Galois orbits on characters mod prime `q`
have size `|⟨(ℤ/(q−1)ℤ)ˣ⟩·j|`, often `≍φ(q−1)/O(1)` for primitive label `j`, but **many
characters lie in small orbits** (those with small field of values). Even if every bad
`χ` dragged `|Gal|` conjugates, the density bound is on a sum of non-negative terms
`N(σ,T,χ)`: orbit-closure multiplies both the count and the trivial bound by the same
factor, giving **no power of `q` saving**. At best a constant in the `≪`.

**Verdict: Dead** for `A<7/3`.

### 15. `deuring_reverse_all` — Dead (excluded flavour)

**Idea.** Deuring–Heilbronn repulsion among *all* characters, not only against one
exceptional zero.

**Obstruction.** Already assessed as Batch 2 `#16 zero_repulsion` (Dead): repulsion is a
spacing/exceptional-zero tool, not a bound on `|W|`. Classical DH needs an exceptional
zero to repel others; without it, one recovers ordinary zero-free regions already used in
Linnik. Not re-opened.

**Verdict: Dead.**

### 16. `ff_transference` — Dead

**Idea.** Over `𝔽_q[t]`, RH is known for curves ⇒ essentially optimal density. Transfer
the exponent to `ℤ`.

**Obstruction.** No known transference principle takes function-field zero-density
exponents to characteristic zero. Weil’s proof inspired RH but does not prove it over
`ℤ`. Function-field Linnik analogues are a different theorem.

**Verdict: Dead.**

### 17. `ils_one_level` — Dead for off-line counts

**Idea.** Iwaniec–Luo–Sarnak one-level density (with extended support under GRH / for
low-lying zeros) as a rigorous upper bound on zeros with `σ>5/7`.

**Obstruction.** One-level density is a *statistical* statement about zeros on or near
the critical line (averaged over families), typically conditional or for low height. It
does not yield
`∑_χ N(σ,T,χ)≪(qT)^{c(1−σ)}` for fixed `σ=5/7`, `T=1`, every `q`. Extending support
improves vertical distribution under hypotheses, not the horizontal density exponent.

**Verdict: Dead.**

### 18. `beurling_detector` — Partial (constants) / Dead for `A`

**Idea.** Beurling–Selberg extremal majorants / Carneiro–Chandee–Milinovich-style Fourier
optimisation to sharpen the zero detector or the explicit formula weights.

**Literature.** Fourier-optimisation detectors have sharpened constants for zeta zero
counts and prime gaps in some ranges; they do not change the LV exponent `A` that comes
from large values of Dirichlet polynomials.

**Bookkeeping.** Better detectors can improve implied constants in
`∑ N(σ,T,χ)≪ …` or the range of an explicit formula, not the power `(7/3)(1−σ)` at the
CGL critical point (which is LV-limited).

**Verdict: Partial** for constants / effective `K` in Linnik. **Dead** for `A<7/3`.
**Next step:** only if the project switches to optimising `K` rather than `L`.

### 19. `stickelberger_gauss` — Dead

**Idea.** Stickelberger’s theorem / Gauss-sum factorisations constrain the arithmetic of
`L(1,χ)` or Bernoulli distributions enough to limit zeros near `σ=5/7`.

**Obstruction.** Stickelberger governs annihilators of class groups (via `L(0,χ)` /
Bernoulli), not the horizontal distribution of zeros at height `T=1` in `Re s∈[5/7,1]`.
Gauss sums appear in functional equations already fully used in CGL/GM.

**Verdict: Dead.**

### 20. `sdp_detector` — Partial / long-shot (constants) ; Numeric null

**Idea.** Search numerically (LP/SDP) over detector weights on small `q` for a mean-value
inequality better than Gallagher/MVT, then check scaling in `q`.

**Numerical (cheap probe).** Nonnegative weights on `n≤7`, projected subgradient
minimising `max_{χ≠1}|∑ w_n χ(n)|/‖w‖₁` vs flat:

| q | flat | opt | opt/flat |
|---|---|---|---|
| 101 | 0.845 | 0.998 | 1.18 |
| 503 | 0.899 | 0.996 | 1.11 |
| 1009 | 1.000 | 1.000 | 1.00 |
| 3001 | 0.973 | 1.000 | 1.03 |

Optimisation did **not** beat flat (often worse). Consistent with short-support uncertainty:
no free MVT-beating inequality visible at this scale.

**Verdict: Partial** only as a methodology for constant-hunting. **Dead** so far for
exponents; the probe is a null result. **Next step:** if revived, a real SDP over longer
smooth detectors with an explicit `q`-scaling target — still unlikely to beat `α=2/3`.

### 21. `hadamard_mellin_q` — Dead

**Idea.** Hadamard three-lines / Mellin convexity in the `q`-aspect to interpolate density
bounds between easy regions (`σ→1` and `σ=1/2`).

**Obstruction.** Convexity of `log` of a counting function is not free: `N(σ)` need not
satisfy the hypotheses of Hadamard three-lines. Classical density already uses convexity
of `L`-functions (Phragmén–Lindelöf) as input to Ingham; that is how one gets exponents
like `3/(2−σ)`, already worse than CGL near `5/7`.

**Verdict: Dead.**

### 22. `weighted_chi_a` — Partial (the right meta-question) / Dead as LV dodge

**Idea.** Linnik is about **one** class `a mod q`. The explicit formula / character
orthogonality weights zeros by `χ̄(a)`. Seek cancellation among `∑_χ χ̄(a) ∑_{ρ_χ} x^ρ/ρ`
rather than a bound on `∑_χ N(σ,T,χ)`.

**Bookkeeping.** The triangle inequality `|∑_χ χ̄(a) ∑_ρ …| ≤ ∑_χ ∑_ρ |…|` recovers the
density route. Beating it requires **signed** cancellation. That is the classical
Fogels / Pintz / soft density territory, or pretentious/Halász methods (Batch 2 `#10`,
Dead for uniform power saving). No known cancellation among zeros of *different*
characters at `σ=5/7` gives a power of `q` better than density.

**Does Linnik need the full uniform density?** In the formalised sieve-certificate route:
the peak `A` enters as a worst-case input, so **yes**. In a hypothetical signed-explicit-formula
proof: one might need less than uniform `|W|` control — that is exactly the open
classical approach that density methods replaced because cancellation was unavailable.

**Verdict: Partial** as the correct “outside architecture” question. **Dead** without a
new cancellation theorem. **Deep dive:** see **Signed estimate deep dive** below
(`scripts/density_hunt/signed/`).

---

## Batch 7 summary

| # | id | verdict | note |
|---|---|---|---|
| 01 | `de_branges` | Dead | no accepted density theorem |
| 02 | `hecke_cyclotomic` | Dead | `D_K≍q^{φ(q)}` kills exponents |
| 03 | `iwasa_padic` | Dead | p-adic ≠ complex zeros in CGL box |
| 04 | `jensen_weird_contour` | Dead | no better `|L'/L|` on new contours |
| 05 | `slice_rank_W` | Dead | `W` not cap-set-like |
| 06 | `rankin_selberg_zeros` | Dead | reduces to Dirichlet `L` / averages |
| 07 | `bombieri_asymp_sieve` | **Partial** / Dead for `11/5` | FI/MMT exist, `L` huge |
| 08 | `furstenberg_W` | Dead | no cardinality saving |
| 09 | `selberg_class_axioms` | Dead | axioms don’t beat CGL |
| 10 | `chebotarev_linnik` | Dead | cyclotomic discriminant too large |
| 11 | `entropy_compression` | Dead | no rigorous dependency graph |
| 12 | `sieve_skip_density` | **Partial** / Dead for `11/5` | same as #07; corner is load-bearing in current cert |
| 13 | `kuznetsov_theta_lift` | Dead | still averages moduli |
| 14 | `galois_orbit_W` | Dead | constant factor only |
| 15 | `deuring_reverse_all` | Dead | Batch 2 #16 redo |
| 16 | `ff_transference` | Dead | no ℤ-transfer |
| 17 | `ils_one_level` | Dead | statistics on the line ≠ `N(σ)` |
| 18 | `beurling_detector` | **Partial** (constants) | Dead for `A` |
| 19 | `stickelberger_gauss` | Dead | wrong arithmetic (class groups) |
| 20 | `sdp_detector` | **Partial** / null numeric | short-weight LP does not beat flat |
| 21 | `hadamard_mellin_q` | Dead | classical convexity already used |
| 22 | `weighted_chi_a` | **Partial** (meta) / deep dive **Dead** for power saving | see Signed estimate section |

### Live / worth a next step (honest)

None of the 22 yields a concrete inequality toward `A<(7/3)(1−σ)` or `L<11/5`. The only
**Partial** items with a clear next step are architectural, not analytic wins:

1. **`sieve_skip_density` / `bombieri_asymp_sieve` (#07,#12):** Linnik *can* avoid CGL
   density (FI, MMT), but known `L` are useless for beating `11/5`. **Next step:** monitor
   sieve-Linnik exponents; no repo action until `L<3` appears in the literature.
2. **`weighted_chi_a` (#22):** Right question (“one class ⇒ signed weights”). Deep dive
   + barrier: triangle is achievable under all zero-constraints (linear-in-`k` zeros);
   every-`a` saving is circular with Linnik unless new arithmetic input. Random-phase
   heuristic `L≈1.58` remains the conditional deliverable. **Next step:** only with
   arithmetic input beyond zeros (not pursued — sieve route already does that).
3. **`beurling_detector` / `sdp_detector` (#18,#20):** Constant/`K` optimisation, null so far
   for exponents. **Next step:** only if priorities shift from `L`/`A` to effective constants.

**No improvement of `A` or `L` claimed. No Lean. Docs/scripts only.**


---

## Signed estimate deep dive (`weighted_chi_a`)

Goal: decide whether cancellation in `χ̄(a)` across characters can replace (part of)
the zero-density input in the Linnik deduction at `σ ≈ 5/7`, for **prime** `q`.
Scripts: `scripts/density_hunt/signed/`. Labels: Written / Heuristic / Numerical / Dead.

### 1. Exact target

Smoothed explicit formula (Heath-Brown / classical; cf. also Friedlander–Iwaniec
arXiv:2303.06122 §1 for the GRH-cancellation remark):

```
ψ_f(x; q, a) = f̂(1)·x/φ(q) − (1/φ(q)) ∑_{χ ≠ χ₀} χ̄(a) ∑_ρ f̂(ρ) x^ρ
               + archimedean / principal-character error.
```

Define the **signed quantity** (box = zeros with `β ≥ σ₀`, `|γ| ≤ T`, `T` of Linnik
height ≪ `x^ε`):

```
Z(a) := ∑_χ χ̄(a) ∑_{ρ_χ ∈ box} f̂(ρ) x^ρ .
```

(The repo’s sieve certificate does **not** feed on `Z(a)` directly; density enters as a
curve `A(σ)`. The signed question is either (i) a replacement architecture, or (ii) a
way to weaken the peak `A` by a signed large-values input. Both are recorded.)

**Triangle vs density.** With `N(σ,T) ≪ (qT)^{A(1−σ)}` and `|f̂(ρ) x^ρ| ≍ x^σ` at the
critical scale,

```
|Z(a)| ≤ |Z|_△  ≍  (qT)^{A(1−σ)} x^σ .
```

**Sieve-certificate route** (formalised; `docs/research-opportunities.md` §3.1):
Type II needs `L > 1 + A/2`. Today `A = 7/3`, floor `13/6 ≈ 2.1667`, deep certificate
reaches ≈ `2.199` (`2.198` fails). Slack ≈ `0.032`.

| Target | Needed `A'` (same slack) | `ΔA = 7/3 − A'` | Viable? |
|---|---|---|---|
| `L < 11/5 = 2.2` | already at/above today’s pass | — | formal `11/5` is the Lean target; computational pass is `2.199` |
| `L < 2.198` | `A' ≲ 2.331` | `≳ 0.002` | tiny improvement of peak `A` |
| `L < 2.167` | `A' ≲ 2.269` | `≳ 0.064` | needs a real density win |
| near floor `13/6` | `A' → 7/3` with slack → 0 | certificate engineering, not `Z` |

So in the **sieve** architecture, signed cancellation helps Linnik only if it improves
the density *curve* (or its use). A pointwise bound on one `Z(a)` does not plug into
`tools/linnik/density_payoff.py` by itself.

**Pure explicit-formula route** (Fogels-type, crude): need `|Z| ≪ x` (up to `φ(q)`
factors cancelling the main term). Triangle forces `L ≥ A = 7/3`. A power saving
`|Z| ≤ q^{−θ} |Z|_△` yields the requirement

```
θ > (A − L)(1 − σ) .
```

At `σ = 5/7`:

| Target | Needed `θ` (vs triangle) |
|---|---|
| `L < 11/5` | `θ > 0.0381` |
| `L < 2.198` | `θ > 0.0387` |
| `L < 2.167` | `θ > 0.0475` |

Script: `signed/bookkeeping.py`.

### 2. Reformulation and random-phase heuristic

Orthogonality: `Z(a)` is the contribution of zeros to the single progression `a mod q`.
Equivalently: among characters whose Dirichlet polynomial / explicit-formula weight is
large, how many have phase `χ(a) x^{iγ}` **aligned**?

**Equidistribution / anti-concentration.** There is no theorem that the ordinates
`γ_{χ,j}` of distinct `χ mod q` are independent at `σ = 5/7`, nor a GUE-across-family
result that would force square-root cancellation in `Z(a)`. One-level densities
(Iwaniec–Luo–Sarnak and successors) control zeros *on the critical line* for families,
not off-line zeros in a density box. **Heuristic** (standard, not a theorem): treat
`{χ̄(a) x^{iγ}}` as iid uniform on the circle.

Then `|Z| ~ √N · x^σ` with `N = (qT)^{A(1−σ)}` (**square-root cancellation**).

**Conditional-on-random-phases Linnik exponent** (`bookkeeping.random_phase_heuristic_L`):

| Quantity | Value |
|---|---|
| Effective density exponent | `A_eff = A/2 = 7/6 ≈ 1.167` |
| Pure-explicit crude `L` | `A/2 ≈ 1.167` |
| Sieve floor if peak becomes `A/2` | `1 + A/4 ≈ 1.583` |
| Optimistic sieve `L` (same slack) | ≈ `1.616` |

**Numerical (synthetic random phases, `heuristic_random_phases.py`, seed 42+q):**

| `q` | `N ≈ q^{A(1−σ)}` | `max\|Z\|/N` | empirical `α` (`max ~ N^α`) |
|---|---|---|---|
| 31 | 9 | 0.72 | 0.85 |
| 127 | 25 | 0.47 | 0.77 |
| 503 | 63 | 0.30 | 0.71 |
| 1009 | 100 | 0.28 | 0.72 |

`α` trends down toward `1/2` slowly (small-`N` / `√(N log q)` effects). Triangle is
`α = 1`. **Heuristic deliverable:** under random phases, Linnik exponents drop below `2`
(sieve floor `≈ 1.58`). **No theorem.**

### 3. Rigorous attempts

#### (a) Second moment over `a` — Written (identity) / Dead for every-`a`

```
∑_{a=1..q, (a,q)=1} |Z(a)|² = φ(q) ∑_χ |∑_{ρ_χ} f̂(ρ) x^ρ|² .
```

Gives the average-`a` bound `|Z|_{rms} ≍ (∑_χ |c_χ|²)^{1/2}` — square-root in the
`ℓ²` sense. Linnik needs **every** `a`.

**Amplification (DFI-style).** Weight `∑_{b ∈ 𝒜} |Z(ab)|²` over a short multiplicative
set `𝒜`. Expansion produces `∑_χ |c_χ|² |∑_{b∈𝒜} χ(b)|²`. A useful amplifier needs
`|∑_𝒜 χ|` large on the “bad” set `W = {χ : c_χ ≠ 0}` and small off `W`. Here `W` is
defined by existence of a zero in a box — not by a multiplicative relation — so there
is no known amplifier that preferentially detects `W`. **Dead** as a route from average
to every `a`.

**Tao uncertainty (prime `q`).** Tao, *An uncertainty principle for cyclic groups of
prime order* (Math. Res. Lett. 12 (2005); arXiv:math/0308286): for nonzero
`f : ℤ/pℤ → ℂ`,

```
|supp f| + |supp f̂| ≥ p + 1 .
```

If `f̂` is supported on `W` with `|W| = M = q^{A(1−σ)}`, then `|supp f| ≥ q+1−M`: `Z` is
**non-sparse** on the `a`-side. That prevents concentration on few residue classes; it
does **not** upper-bound `|Z(a)|` pointwise. Constructed spike (`tao_uncertainty.py`):
`hat = 1_W` gives `max|Z| / triangle = 1` exactly. Amplifier windows over multiplicative
shifts have `max/mean = O(1)` for random `W`. **Dead** for a pointwise power saving.
(Caveat, corrected in the barrier follow-up: `Z` is Fourier on `(ℤ/q)* ≅ ℤ/(q−1)`,
and for prime `q>3` the order `q−1` is composite, so Tao’s strong form does **not**
apply on the character group. On additive `𝔽_q` it applies but points the wrong way.)

#### (b) Higher moments / Hölder — Dead

`∑_a |Z|^{2k} = φ(q) · (# of 2k-tuples in `W` with character product `1`)`.
Without additive/multiplicative structure on `W`, Hölder recovers at best random-like
bounds, not a power below triangle uniformly in `a`. Numeric
(`second_moment_positivity.py`): `max/triangle` decreases slowly; no fitted power saving
compatible with `θ > 0.038` at these sizes.

#### (c) One-sided positivity / Fejér — Dead for exponents

Linnik needs `ψ_f > 0`, i.e. a lower bound, so only `Re Z(a)` from above. Nonnegative
kernels (Fejér, Selberg majorants) can smooth in the `a`-aspect or the `t`-aspect; they
do not create cross-character cancellation. Numeric: Fejér-smoothed `max Re Z / triangle`
is smaller by a **constant**, not a power of `q`.

**No rigorous gain**, even in a toy regime (average-`a` is classical Plancherel; every-`a`
power saving not obtained).

### 4. Numerics

**Real low-lying zeros** (`real_zeros_Z.py`): truncated Dirichlet series on the critical
line for prime `q ∈ {5,7,11,13}`, `|t| ≤ 12`. Label: `NUMERICAL_GRH_LOW_LYING`.
Off-line zeros were **not** located (consistent with GRH at this height). Empirical
`max|Z|/triangle ∈ [0.25, 0.64]`, `α ∈ [0.72, 0.75]` — mild cancellation among low-lying
terms, **not** a density-regime test.

| `q` | #zeros found | `max\|Z\|/△` | `α` |
|---|---|---|---|
| 5 | 8 | 0.64 | 0.75 |
| 7 | 15 | 0.46 | 0.74 |
| 11 | 33 | 0.33 | 0.75 |
| 13 | 42 | 0.25 | 0.72 |

**Synthetic off-line** (`synthetic_Z.py`, labelled `SYNTHETIC`): place `M = q^{A(1−σ)}`
zeros at `σ = 5/7` with random phases, `x = q^{2.2}`. Same picture as the random-phase
heuristic (`max/△` falling, `α → ~1/2` slowly). A parallel “GRH-all characters on the
line” model gives stronger apparent cancellation simply from larger `M`.

**Empirical cancellation exponent:** ≈ `0.7` at accessible sizes; compatible with
`√(N log)` and **not** with a proven `θ > 0.03` power below triangle for every `a`.

### 5. Literature check

- **Heath-Brown**, *Zero-free regions for Dirichlet L-functions and the least prime in
  an AP* (PLMS 1992): explicit formula with `χ̄(a)` weights; improvements via zero-free
  regions and density, not cross-character cancellation at fixed `a`.
- **Xylouris** (Acta Arith. 2011): sharpens Heath-Brown; same architecture (`L = 5.18`).
- **Bombieri**, *Le grand crible* (Astérisque): log-free density / large sieve; counts,
  does not cancel `χ̄(a)` across `χ`.
- **Friedlander–Iwaniec**, *Sifting for small primes from an AP* (arXiv:2303.06122) and
  sister paper: Linnik **without** log-free density, via sieves; the signed weight
  `λ = 1 ∗ χ` is used for the **exceptional real character**, not for cancellation among
  many `χ` at `σ = 5/7`. Resulting `L` is huge (`≈ 7.5 × 10⁷` in that write-up). They
  explicitly note that GRH + square-root cancellation in `∑_ρ` would give `L < 2`.
- **Graham**, Heath-Brown’s earlier `L = 20` etc.: density + zero-free, not signed
  multi-character cancellation.
- No reference found that proves a power saving `|Z(a)| ≤ q^{−θ} |Z|_△` uniformly in `a`
  at `σ = 5/7` for prime `q`.

### Verdict

| Claim | Label |
|---|---|
| Plancherel second-moment identity | **Written** (classical) |
| Average-`a` square-root bound | **Written** |
| Every-`a` power saving via Tao uncertainty | **Dead** (wrong direction) |
| Every-`a` via DFI amplifier on zero-set `W` | **Dead** (no amplifier for `W`) |
| Higher moments / Hölder every-`a` | **Dead** |
| Fejér / one-sided positivity ⇒ power saving | **Dead** |
| Random-phase heuristic `L ≈ 1.58` (sieve) / `≈ 1.17` (pure) | **Heuristic** |
| Synthetic / low-lying numerics | **Numerical** (no density-regime theorem) |
| Replace CGL density by signed estimate for `L < 11/5` | **Dead** without a new theorem |

**Flag:** no rigorous gain toward `L < 11/5` or `A < 7/3`. The honest positive
deliverable is the **conditional-on-random-phases** exponent (≈ `1.58` sieve floor /
≈ `1.17` pure-explicit crude). Prime-modulus Tao uncertainty was checked and does not
help pointwise. Live status of `#22` unchanged: right question, no estimate.


---

## Signed estimate: barrier, function-field model, circularity

Follow-up to the deep dive. Question: is **any** every-`a` saving
`|Z(a)| ≤ q^{-θ} |Z|_△` with `θ > 0` (even tiny) forced by known zero-constraints,
or can an adversary achieve the triangle bound?

Scripts: `barrier_linear_zeros.py`, `large_sieve_k.py`, `function_field_model.py`,
`circularity_check.py`.

### Barrier construction — **Yes, triangle is achievable under zero-information constraints**

**Construction.** Prime `q`, identify `χ_k(a) = e(k·ind(a)/(q−1))`, `k ∈ ℤ/(q−1)`.
Pick a density-sized set `W ⊂ {1,…,q−2}` with `|W| ≤ q^{A(1−σ)}`, closed under
`k ↦ −k` (conjugation). Place one zero of each `χ_k`, `k∈W`, at

```
ρ_k = σ + i γ_k ,   γ_k = 2π k·ind(a₀) / ((q−1) log x)
```

with `σ = 5/7`. Then `χ̄_k(a₀) x^{iγ_k} = 1` for all `k∈W`, so

```
Z(a₀) = ∑_{k∈W} x^σ = |W| x^σ = |Z|_△ .
```

**Constraints respected.**

| Constraint | Status |
|---|---|
| Conjugation `χ ↔ χ̄` (`k ↔ −k`, `γ ↔ −γ`) | enforced by symmetric `W` and odd `γ(k)` |
| Functional equation `ρ ↔ 1−ρ̄` | reflected zeros at `1−σ` recorded; relative size `x^{1−2σ} → 0` (`≈ q^{L(1−2σ)}`); not used in the aligned sum |
| Density `|W| ≤ (qT)^{A(1−σ)}` | saturated at `T≍1` |
| Zero-counting `N(T,χ) ≍ (T/2π)log(qT)` | one zero per `χ` in the box — far below |
| Half-plane `11/12` | `5/7 < 11/12`, box allowed |
| Orthogonality / FFT definition of `Z` | exact |

**Not imposed** (this is the point): that the resulting `ψ(x,χ) = −∑_ρ x^ρ/ρ + …`
equals an actual `∑ Λ(n)χ(n)`. That is arithmetic input from primes.

**Numeric** (`barrier_linear_zeros.py`, `L=2.2`, `a₀` with `ind=1`):

| `q` | `M` | `Z(a₀)/△` | `max/△` | random-phase `max/△` |
|---|---|---|---|---|
| 31 | 9 | **1.000** | 1.000 | 0.60 |
| 127 | 25 | **1.000** | 1.000 | 0.42 |
| 503 | 63 | **1.000** | 1.000 | 0.36 |
| 2003 | 158 | **1.000** | 1.000 | 0.21 |

At `q=503`: `|Z(a₀)|/x ≈ 1.22 > 1`, so the explicit-formula proxy for `ψ` is
**negative** — the barrier kills positivity exactly when triangle is sharp.

**Barrier statement (precise).**

> From zero-location constraints alone (conjugation, FE bookkeeping, CGL density,
> zero-counting upper bounds, half-plane), there is no obstruction to
> `|Z(a₀)| = |Z|_△` for some `a₀`. Therefore no every-`a` saving
> `|Z(a)| ≤ q^{-θ}|Z|_△` with `θ>0` is provable from zero-information alone.
> Any such saving requires arithmetic input (prime structure / Euler product).

Label: **Written** (model construction) / **Numerical** (ratios) /
**Dead** as a zero-only route to `θ>0`.

### Multiplicative structure and large sieve over `k`

Alignment needs `γ_k` linear in the character index `k` — compatible with
`χ(a)` being a homomorphism of the dual group. The coefficient sequence
`c_k = 1_W(k)·e^{iαk}` is a modulated indicator; its Fourier transform (in `a`)
is a Dirichlet-kernel spike of height `|W|`.

- **Large sieve / Plancherel:** control `∑_a |Z(a)|²`, hence the average, not the max.
- **Tao on `(ℤ/q)* ≅ ℤ/(q−1)`:** for prime `q>3`, `q−1` is even, hence **composite**.
  Tao’s strong form `|supp|+|supp hat|≥p+1` **never applies** on the character group
  of a prime modulus. (Earlier Tao checks were on additive `𝔽_q`, a different group.)
- **Donoho–Stark** `|supp|·|supp hat|≥q−1` applies and is saturated by subgroups; it
  does not bound `‖Z‖_∞/‖c‖_1`.
- Numeric (`large_sieve_k.py`): adversary has `‖Z‖_∞/△ = 1`, while
  `frac{|Z|>½ max} → 0` (sharp spike) and `supp Z` is still almost full (sidelobes).

**No obstruction from the homomorphism structure.** Label: **Dead**.

### Function-field controlled model

Over `𝔽_q[t]`, modulus irreducible of degree `d`, character group cyclic of order
`N = q^d−1`. Weil RH puts zeros on the critical circle. Scripts keep the
homomorphism `χ(a) = e(k·ind(a)/N)`.

| Experiment | Result | Label |
|---|---|---|
| **E1** RH-random angles (proxy) | `max/△` falls (`0.35→0.09` as `N=16→256`) — generic cancellation | **Numerical** / Heuristic |
| **E2** Adversarial off-line + linear angles | `Z(a₀)/△ = 1.000` for all tested `N` — homomorphism does not prevent alignment | **Numerical** (barrier transfers) |
| **E3** `EXACT_FF_PRIMES` tiny enumeration | e.g. `(q,d,n)=(2,2,7)`: mean `13.3` irreds/class, `rel_spread≈0.10`; `(3,2,5)`: `rel_spread≈0.22` — modest variation under actual RH primes | **Numerical** (exact, tiny) |

Under genuine RH (E1/E3) one sees cancellation; under adversarial off-line displacement
with linear phases (E2) the triangle is again achieved. The homomorphism structure
alone never saves every `a`.

### Circularity verdict — **Yes, circular**

```
φ(q) ψ_f(x;q,a) = f̂(1)·x − Z(a) + O(error).
```

An every-`a` bound `|Z(a)| ≤ q^{-θ}|Z|_△` at `x = q^L` is equivalent to a uniform
PNT in APs at that scale — i.e. a Linnik-type theorem. Proving signed saving in
order to deduce Linnik is **circular**, unless the proof uses information not
equivalent to `{ψ(·;q,a)}` for this fixed `q`.

**What breaks circularity (honest list):**

| Input | Why it is not circular | Limitation for every-`(q,a)` |
|---|---|---|
| Bombieri–Vinogradov | averages over many moduli | almost-all `q`, not every |
| Barban–Davenport–Halberstam | averages over `a` | almost-all `a`, not every |
| Short intervals / Type I–II (sieve certificate) | bilinear forms, not signed `Z` | the repo’s existing route |
| Deuring–Heilbronn | exceptional-zero arithmetic | one character, not `σ=5/7` box |
| RMT / pair correlation off the line | would be new analytic input | heuristic only for off-line zeros |

Zero-density + triangle remains the non-circular classical route: it uses **counts**,
not signs. The barrier shows those counts are compatible with worst-case signs.

Script: `circularity_check.py`. At `σ=5/7`, `A=7/3`, `L=11/5`:
`|Z|_△/x ≍ q^{4/105} = q^{0.038…}` — triangle fails positivity by `q^{0.038}`; a
saving of that order restores the threshold.

### Updated verdict

| Claim | Label |
|---|---|
| Barrier: triangle achievable under zero-constraints | **Written + Numerical** |
| Every-`a` `θ>0` from zero-info alone | **Dead** (barrier) |
| Homomorphism / Tao-on-`(Z/q)*` obstruction | **Dead** (group mismatch + spike) |
| FF model: generic RH cancels; adversary aligns | **Numerical** |
| Circularity of every-`a` signed saving with Linnik | **Written** (equivalence) |
| Genuinely new route to `L<11/5` via signed `Z` | **None found** |

**No improvement of `A` or `L` claimed.** The valuable negative result is the barrier
statement: every-`a` signed saving is not a theorem about zeros; it is a theorem
about primes (or needs new arithmetic input).

---

## See also

Ingredient-level attack (restricted LV loophole, arithmetic every-`(q,a)` survey):
`docs/ingredient-hunt.md`, `scripts/ingredient_hunt/`.
