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
| 06 | `combinatorial_energy` | Partial | not excluded; near-extremisers look unstructured |
| 07 | `real_complex_split` | Dead | too few real `χ` to affect the sum |
| 08 | `bombieri_large_sieve` | Dead | helps almost-all `q`, not every `q` |

**Promising enough to keep alive:** only `combinatorial_energy`, and weakly. Next batch should prioritise
queued items that could touch Remark 12.3 differently: `moment_half`, `GM_q_aspect` (only *refinements*
beyond CGL, not a redo), `hybrid_energy`, `jutila_mollifier`, `pretentious`, `decoupling`,
`halfplane_shorten` — still in seed order, not cherry-picked, when continuing.

**No Lean claims. No improvement of `A` claimed.**

## Next steps

1. Continue openings 09–16 in seed order with the same template.
2. Add `scripts/density_hunt/energy_adversarial.py` wrapping `scripts/cgl_s3/` data to measure additive energy
   of near-extremal `W` (supports or kills `combinatorial_energy`).
3. Keep this note updated on branch `density-exponent-hunt`; no force-push.
