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

