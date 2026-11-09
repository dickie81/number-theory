# Ingredient hunt — attack the two ingredients

**Date:** 2026-11-09. **Branch / PR:** `density-exponent-hunt` / #98.
**Method:** same as `docs/density-exponent-hunt.md`: exclusion lists, ~15–20 openings
per ingredient, shuffled with a recorded seed, honest bookkeeping, cheap numerics,
literature, verdicts **Dead / Partial / Promising**. Barrier test cases that any
approach must defeat: (i) adversarial TPM sets saturating MVT (Batches 4–6);
(ii) linear-in-`k` zero alignment achieving `|Z(a₀)| = |Z|_△` (signed deep dive).

Scripts: `scripts/ingredient_hunt/`. **No Lean.** Never fabricate.

## The two ingredients

| | Ingredient I | Ingredient II |
|---|---|---|
| **Object** | Large values of Dirichlet polynomials over characters mod prime `q` | Arithmetic input about primes `≡ a (mod q)` for **every** `(q,a)` |
| **Target** | Beat `\|W\| ≪ N²/V² + qT·N/V²` by `(qT)^{-η}` at `(y,V)=(7/9, N^{5/7})`, `T` small | Any every-`(q,a)` statement at `x ~ q^{2.2}` beyond what zero-density+triangle gives |
| **Pays** | `mvt_beyond` ⇒ floor below `≈2.308`, and with S₃ room possibly `A<7/3` | Bypass or weaken density in the Linnik deduction |

Seed `20261207` (`scripts/ingredient_hunt/seed.txt`). Ingredient I: 18 openings.
Ingredient II: 20 openings. Assessed in shuffled order below.

---

## Exclusion lists (do not redo)

### From repo (`density-exponent-hunt.md`, `cgl-s3-prime-moduli.md`, signed deep dive)

**Ingredient I — already tried / excluded:**
1. Unrestricted MVT-beyond η-test on ADV: `ρ(η)≈η`, no fixed `η>0` (Batches 5–6).
2. S₃ / Prop. 8.1 power saving via decoupling, Weil, incidences, sum-product (Batches 5–6): stalls; even optimistic incidence hits non-binding face.
3. Direct S₃ attacks at prime `q`, `T=1` (cgl-s3 §§2–7): Schatten, Bohr, weighted energy, fourth-moment caps.
4. Block-sum sixth moment / Bettin–Chandee / Kuznetsov as tried (cgl-s3 §§8–11).
5. Free CGL parameter re-optimisation; GM `q=1` re-derivation; HB classical LV variants; pretentious at `V≈N`; Jutila mollifier length retune; Matomäki–Radziwiłł short-interval transfer (Batches 1–3).
6. SDP/LP short-weight detector (Batch 7): null vs flat.

**Ingredient II — already tried / excluded:**
1. Signed `χ̄(a)` every-`a` saving from zero-info alone: **barrier** (linear-in-`k`); circular with Linnik (signed deep dive).
2. Tao uncertainty on additive `𝔽_q` / character group: wrong direction or wrong group (`q−1` composite).
3. FI/MMT sieve-without-density as a route to `L<11/5`: exists, `L` huge (Batch 7 `#07/#12`).
4. Chebotarev / Hecke cyclotomic: discriminant kills (Batch 7).
5. Rankin–Selberg / Kuznetsov theta as density replacement (Batch 7): reduces to averages.
6. Deuring–Heilbronn reverse for all `χ` (Batch 2 `#16`, Batch 7 `#15`): no lever on `|W|`.
7. Deeper Buchstab only; stronger half-plane only (exclusion list / §S6).

### Literature dead ends (checked 2026-11-09; no fabricated citations)

- Bourgain: unrestricted Montgomery LV conjecture false; modified `|a_n|≤1` form open (and still far from character-aspect MVT-beyond at our critical point).
- Montgomery modified conjecture / density hypothesis: open; would give density hyp for `ζ`, not automatically our hybrid `(q,T)` character MVT saving.
- Heath-Brown `L=5.5`, Xylouris `5.18`: use zero-density + zero-free — not a density-free every-`(q,a)` input at `2.2`.
- Friedlander–Iwaniec arXiv:2303.06122: Linnik without log-free density, `L` enormous.
- Bombieri–Vinogradov / BFI / Maynard well-factorable: **averages** over moduli, not every prime `q` with `x=q^{2.2}`.
- Zhang/Polymath: smooth moduli / dispersion averages.

---

## Ingredient I — shuffled assessments

### I.01 `pretentious_LV` — Dead

**Idea.** Halász/pretentious large values for structured `D(χ)`.
**Bookkeeping.** Pretentious methods control `∑_{n≤x} a_n χ(n)` when `a_n` is multiplicative and `V` is near the absolute max (`≍ ‖a‖_1`). Critical regime is `V = N^{5/7}`, far below.
**vs ADV/barrier.** ADV is not pretentious-multiplicative (`corr(ADV,μ)≈0.03` at `q=10⁴`); barrier is about zeros not coeffs.
**Lit.** Granville–Soundararajan pretentious; wrong regime (Batch 2 `#10`).
**Verdict: Dead.**

### I.02 `sidon_W` — Dead

**Idea.** Force `W` Sidon-like ⇒ `|W|` small.
**Bookkeeping.** Need `|W| ≪ q^{2/3−η}`; Sidon in `(ℤ/q)*` or additive `ℤ/(q−1)` gives `|W|≪q^{1/2}`, which would be a huge win — but ADV/tpm `W` is **not** Sidon (additive energy 3–7× random, Batch 2). No theorem forces large-value `W` to be Sidon.
**vs ADV.** ADV has moderate energy, not Sidon-thin.
**Verdict: Dead.**

### I.03 `decoupling_LV` — Dead (as direct LV); Partial only as Prop. 8.1 redo

**Idea.** `ℓ²` decoupling for character exponential sums at critical `(y,V)`.
**Bookkeeping.** Same stall as Batch 5 Attack 1 on `J(f)`: finite-field decoupling does not match GCD-twisted triple products; even a Prop. 8.1 win floors at `30/13` without `mvt_beyond`.
**Verdict: Dead** for MVT-beyond; excluded as Prop. 8.1 redo.

### I.04 `szemeredi_W` — Dead

**Idea.** Szemerédi regularity on `W` ⇒ structured pieces handleable.
**Bookkeeping.** Density Szemerédi needs positive upper density in `[1..q]`; `|W|~q^{2/3}` has density `q^{-1/3}→0`. Relative Szemerédi/hypergraph tools do not yield a power saving on `|W|` without an energy hypothesis ADV already partially violates.
**Verdict: Dead.**

### I.05 `short_mollifier_block` — **Partial (live with restr_coeff)**

**Idea.** CGL at `T=1` reduces detectors to interval sums `S_I(χ)` (`cgl-s3` §8; mollifier `X=(qT)^ε`). Attack LV **only** for `b = 1_I`.
**Bookkeeping.** At `σ=5/7`, `N=q^{7/9}`, a power saving η on interval-LV replaces the MVT face and can lower the peak if the `T=1` corner remains binding.
**Numeric** (`adv_realisability.py`, `restr_coeff_probe.py`):

| `q` | ADV `sharp_mvt` | interval `sharp_mvt` | ADV `\|W_crit\|` | interval `\|W_crit\|` |
|---|---|---|---|---|
| 1009 | 0.67 | 0.35 | 11 | 1 |
| 2003 | 0.50 | 0.30 | 4 | 1 |
| 10007 | 0.63 | 0.22 | 36 | 1 |

Interval is **far** from ADV saturation; `|W_crit|` stays `O(1)` for interval vs growing for ADV.
**vs ADV.** ADV is the wrong test case for this opening — the opening **rejects** unrestricted ADV and asks for interval-only theorems.
**Lit.** Ayyad–Cochrane–Zheng fourth moment for intervals; cgl-s3 §7 proves dilated short intervals are harmless for the fourth-moment form (factor `q^{1/6}` below CGL). That is evidence interval-LV is easier than general LV — not yet a theorem beating MVT by `q^{-η}`.
**Verdict: Partial.** Strongest I-side lead. Needs a theorem: `|W| ≪ N²/V² + q^{1−η} N/V²` for `b=1_I` at the critical point.

### I.06 `entropy_increment` — Dead

**Idea.** Entropy increment on `W⊂(ℤ/q)*`.
**Bookkeeping.** No known entropy-increment lemma giving hybrid large-sieve savings for Dirichlet polynomials over characters. Soft without an inequality.
**Verdict: Dead.**

### I.07 `amplify_chi_powers` — Dead (tested)

**Idea.** Amplify by `χ ↦ χ^k` (Batch 5 H1).
**Numeric.** Amplification failed to turn `O(1)` coexistence slack into a power (Batch 5).
**Verdict: Dead.**

### I.08 `montgomery_mult` — Partial (conjectural; not a proof)

**Idea.** Montgomery’s modified conjecture for **multiplicative** coefficients (or `|a_n|≤1` multiplicative).
**Bookkeeping.** Even the `|a_n|≤1` modified conjecture is open for `ζ`; a multiplicative-only variant is not in the literature as a theorem. If true for character polynomials with `a_n ∈ {μ(d): d|n,d≤X}`, it could give density-type bounds — exponent bookkeeping would still need the hybrid `q`-aspect form.
**vs ADV.** ADV has `corr(ADV,μ)≈0.03–0.07` — not multiplicative — so a multiplicative Montgomery statement **evades** the ADV barrier (same loophole family as I.05/I.09/I.10).
**Verdict: Partial** as a conjectural target; **Dead** as a known theorem.

### I.09 `restr_coeff_LV` — **Partial / Promising (loophole)**

**Idea.** Prove MVT-beyond only for detector-realisable `b` (interval / short `μ`-mollifier convolutions / Type I–II shapes).
**Bookkeeping.** Same payoff as I.05 if the restricted class includes CGL’s detectors. Precise target:

```
|W| ≪ N²/V² + q^{1−η} N/V²
for all b in B_detector, at (N,V)=(q^{7/9}, N^{5/7}), T≲1.
```

**Numeric.** See I.05 / I.10: detector and interval stay well below ADV sharpness; short-detector `corr(ADV)≈0.26` at `q=10⁴` (not ADV-like).
**Barrier test.** Unrestricted ADV need **not** be defeated; only structured `b`. Linear-`k` `W` with interval `b` shows no preferred alignment (`frac_above_median≈0.16–0.6`, not spiked).
**Verdict: Partial / Promising.** The live loophole.

### I.10 `ADV_realisability` — **Partial (loophole confirmed numerically)**

**Idea.** Are TPM-ADV coefficients realisable as zero-detector coefficients?
**Numeric** (`adv_realisability.py`):

| `q` | `corr(ADV, interval)` | `corr(ADV, μ)` | `corr(ADV, short det)` | `corr(ADV, det √N)` |
|---|---|---|---|---|
| 503 | 0.38 | 0.07 | 0.49 | 0.15 |
| 1009 | 0.30 | 0.03 | 0.36 | 0.05 |
| 2003 | 0.40 | 0.05 | 0.30 | 0.05 |
| 10007 | 0.21 | 0.04 | 0.26 | 0.08 |

ADV is essentially **orthogonal to μ/Liouville** and only moderately aligned with interval/short-detector. `|b|≤1` projection does not change ADV (already flat-phase). Structured families never reach ADV’s `sharp_mvt≈0.6`.
**Conclusion.** ADV saturators used to kill `η>0` in Batches 5–6 are **not** evidence against restricted-coefficient MVT-beyond. Label: **Numerical loophole — Written as a barrier distinction**.
**Verdict: Partial** (positive methodological finding).

### I.11 `holder_moment_cascade` — Dead for general `b`; Partial for intervals

**Idea.** 6th/8th moments of structured character polynomials.
**Bookkeeping.** cgl-s3 §9: classical moments recover only classical ranges; missing sixth moment beyond `q^{4/3}` for one modulus. For **intervals**, fourth-moment theory is stronger (Ayyad–Cochrane–Zheng) — already used to show intervals are “harmless” in one form, not yet upgraded to MVT-beyond.
**Verdict: Dead** unrestricted; fold into I.05/I.09 for intervals.

### I.12 `random_multiplicative` — Dead (model only)

**Idea.** Random multiplicative model for `μ * 1_{[1,X]}`.
**Bookkeeping.** Heuristic; no theorem giving `η>0`. Useful only as intuition for I.09.
**Verdict: Dead** as a proof route.

### I.13 `sparse_spectrum_FFT` — Dead

**Idea.** Sparse-spectrum constraints on `W` via Fourier on the dual.
**Bookkeeping.** Tao/Donoho–Stark give non-sparsity of `Z`, not LV savings on `|W|`. Batch signed deep dive.
**Verdict: Dead.**

### I.14 `type_I_II_detector` — Partial (subsumed by I.09)

**Idea.** Detector coefficients factor as Type I/II bilinear forms; use that in LV.
**Bookkeeping.** CGL short mollifier: `a_n = ∑_{d|n,d≤X} μ(d)` with tiny `X` ⇒ essentially Type I (interval after writing `n=dm`). Same as I.05/I.09.
**Verdict: Partial** (= I.09).

### I.15 `bourgain_special` — Dead for our critical point

**Idea.** Bourgain LV for special polynomial forms.
**Lit.** Bourgain’s work kills unrestricted Montgomery and gives partial results for special structures; no off-the-shelf theorem gives character-aspect `η>0` at `(7/9, N^{5/7})`.
**Verdict: Dead** as a citation to invoke; techniques may feed I.09 later.

### I.16 `incidence_LV` — Dead

**Idea.** Incidences on the `(χ,n)` large-value graph.
**Bookkeeping.** Batch 6 incidence on `∑ H_a²` did not move the binding face. Redo risk.
**Verdict: Dead.**

### I.17 `HB12_q_aspect` — Dead for beating `7/3`

**Idea.** Heath-Brown 12th moment / Huxley with structure in `q`-aspect.
**Bookkeeping.** Batch 1 `#05`: classical LV cannot undercut GM/CGL critical regime. Structured refinement folds into I.09 without a new moment theorem.
**Verdict: Dead** unrestricted.

### I.18 `GM_energy_gauss` — Dead as tried; Partial as slogan for I.09

**Idea.** Import GM additive-energy of large-value *ordinates* via Gauss sums for characters.
**Bookkeeping.** GM `q=1` subdivision fails in `q`-aspect (Batch 4); Gauss-sum identities are what CGL already use to reach Prop. 8.1. No new inequality stated.
**Verdict: Dead** without a new estimate; not a separate live lead from I.09.

---

## Ingredient I summary

| # | id | verdict | note |
|---|---|---|---|
| 01 | `pretentious_LV` | Dead | wrong `V` regime |
| 02 | `sidon_W` | Dead | ADV not Sidon; no force |
| 03 | `decoupling_LV` | Dead | Prop. 8.1 redo / floors at 30/13 |
| 04 | `szemeredi_W` | Dead | density too low |
| 05 | `short_mollifier_block` | Partial → **Dead for Thm 1.3** | T=1 route only; see sceptical § |
| 06 | `entropy_increment` | Dead | no inequality |
| 07 | `amplify_chi_powers` | Dead | Batch 5 null |
| 08 | `montgomery_mult` | Partial (conjectural) | open; evades ADV |
| 09 | `restr_coeff_LV` | **Dead for Thm 1.3** (retracted) | arbitrary `|a_n|≤1` in CGL LV |
| 10 | `ADV_realisability` | Partial numeric / **Dead transfer** | ADV valid for Thm 1.3 |
| 11 | `holder_moment_cascade` | Dead / ⊂09 | intervals only |
| 12 | `random_multiplicative` | Dead | model |
| 13 | `sparse_spectrum_FFT` | Dead | signed redo |
| 14 | `type_I_II_detector` | Partial (=09) | short mollifier = interval |
| 15 | `bourgain_special` | Dead | no off-shelf η |
| 16 | `incidence_LV` | Dead | Batch 6 redo |
| 17 | `HB12_q_aspect` | Dead | classical LV ceiling |
| 18 | `GM_energy_gauss` | Dead | CGL already uses this shape |

**Strongest I finding (superseded by sceptical follow-up):** ADV is unlike μ/interval numerically, but CGL Thm 1.3 applies to **arbitrary** `|a_n|≤1`, so ADV remains a valid saturator for the main density theorem. See **ADV-realisability loophole — sceptical verification** below: loophole **retracted** for Thm 1.3→1.4; residual open problem is only `cgl-s3` §8 hypothesis (H).

---

## Ingredient II — shuffled assessments

### II.01 `linear_k_barrier_break` — Dead without new arithmetic

**Idea.** Defeat linear-in-`k` zero alignment by arithmetic.
**Bookkeeping.** Equivalent to proving phases `χ̄(a)x^{iγ}` cannot align — i.e. a signed saving — circular with Linnik / defeated by the barrier under zero-info (signed deep dive).
**Verdict: Dead** as a separate ingredient; same as signed estimate.

### II.02 `short_interval_AP` — Dead for every `(q,a)` at `x=q^{2.2}`

**Idea.** Primes in short intervals inside one progression.
**Bookkeeping.** Needs simultaneous short-interval + AP control; current theorems are averaged or conditional. Does not give every `(q,a)` at Linnik scale.
**Verdict: Dead** for the test.

### II.03 `DH_cluster_repulsion` — Dead

**Idea.** Many zeros near `σ=5/7` repel each other (DH for clusters).
**Bookkeeping.** Classical DH repels from an exceptional zero near `s=1`, not from a density-box cluster at `5/7`. Batch 2/7 repulsion items Dead.
**Verdict: Dead.**

### II.04 `chebotarev_cyclotomic` — Dead

**Idea.** Chebotarev in `ℚ(ζ_q)`.
**Bookkeeping.** `disc ~ q^{φ(q)}` kills any Linnik-quality exponent (Batch 7).
**Verdict: Dead.**

### II.05 `maynard_GPY_AP` — Dead alone for every `(q,a)`

**Idea.** Maynard/GPY weights on a single AP.
**Bookkeeping.** GPY/Maynard need a level of distribution averaged over moduli (BV/BFI). For one fixed prime `q ~ x^{1/2.2}`, that input is not available; the method does not produce Linnik.
**Lit.** Maynard bounded gaps; weights are multidimensional sieves over *shifts*, not a substitute for single-modulus PNT.
**Verdict: Dead** for the test.

### II.06 `automorphic_theta` — Dead

**Idea.** Theta lifts / half-integral weight for AP primes.
**Bookkeeping.** Batch 7 `#13`: still averages moduli / reduces to known `L`-functions.
**Verdict: Dead.**

### II.07 `bombieri_asymp_one_AP` — Partial / Dead for `L<11/5`

**Idea.** Bombieri asymptotic sieve with Type II for one AP.
**Bookkeeping.** FI’s Linnik-without-density is the modern form; every-`(q,a)` yes, `L` huge. Batch 7 Partial for architecture, Dead for exponent.
**Verdict: Partial** (exists, wrong exponent) / **Dead** for `2.2`.

### II.08 `vinogradov_exp_AP` — Dead for full Linnik@2.2

**Idea.** Vinogradov exponential sums for `Λ` twisted by additive characters, then detect `n≡a (mod q)`.
**Bookkeeping.** Gives Type I/II estimates in restricted ranges; not a complete every-`(q,a)` prime at `x=q^{2.2}`.
**Verdict: Dead** for the test.

### II.09 `bettin_chandee_AP` — Dead (excluded for S₃; not an AP-Linnik tool)

**Idea.** Bettin–Chandee trilinear for primes in AP.
**Bookkeeping.** Exclusion: used for multilinear Kloosterman in cgl-s3 §10, saving too small. Not a standalone Linnik input.
**Verdict: Dead.**

### II.10 `rankin_selberg_AP` — Dead

**Idea.** Rankin–Selberg / Eisenstein for one AP.
**Bookkeeping.** Batch 7 `#06`: reduces to Dirichlet `L` / averages.
**Verdict: Dead.**

### II.11 `HB_identity_Weil` — Partial as Type I/II fuel; Dead alone

**Idea.** Heath-Brown identity + Weil bound for complete sums mod prime `q`.
**Bookkeeping.** Standard Type I input for sieves on prime moduli. Feeds Ingredient II sieges but does not by itself give `ψ(x;q,a)≫ x/φ(q)` at `x=q^{2.2}` every `(q,a)`.
**vs barrier.** Weil on complete sums does not constrain zero ordinates’ phases.
**Verdict: Partial** (useful fuel) / **Dead** alone for the test.

### II.12 `parity_breaking_AP` — Dead

**Idea.** Parity-breaking specialised to one residue class.
**Bookkeeping.** Parity barrier is why pure sieves struggle to produce primes; known breakers (FI norms, Harman’s sieve combinations) do not yield Linnik@2.2 every `(q,a)`.
**Verdict: Dead.**

### II.13 `algebraic_traces` — Dead for Linnik@2.2

**Idea.** Trace functions mod prime `q` for `Λ`.
**Bookkeeping.** Fouvry–Kowalski–Michel etc. give excellent complete-sum bounds; again Type I/II fuel, not every-`(q,a)` at `2.2`.
**Verdict: Dead** for the test.

### II.14 `BV_to_pointwise` — Dead

**Idea.** Amplify Bombieri–Vinogradov to a single `(q,a)`.
**Bookkeeping.** BV is an `ℓ¹` average over `q ≤ x^{1/2}/log^B`. Amplifiers cannot upgrade that to every prime `q` of size `x^{1/2.2}` (larger than the BV range for `x=q^{2.2}`: need moduli `q` with `x=q^{2.2}` ⇒ `q=x^{1/2.2}≈x^{0.455}`, inside BV’s `x^{1/2}`, but BV still allows exceptional moduli). Pointwise at the BV edge is essentially Siegel–Walfisz / GRH territory for the worst modulus.
**Numeric bookkeeping:** at `L=2.2`, `q = x^{1/2.2} ≈ x^{0.4545} < x^{1/2}`, so the modulus is *inside* the BV range on average — but Linnik needs the **worst** `(q,a)`, exactly what BV does not give.
**Verdict: Dead** for every-`(q,a)`.

### II.15 `zhang_dispersion_fixed` — Dead for prime `q` every `a`

**Idea.** Zhang/Polymath dispersion for a fixed residue.
**Bookkeeping.** Designed for smooth/well-factorable moduli and averaged estimates. Prime moduli of size `x^{0.45}` are the worst case, not the intended range.
**Verdict: Dead.**

### II.16 `DH_nonstandard` — Dead

**Idea.** Non-standard Deuring–Heilbronn near `σ=5/7`.
**Bookkeeping.** No such theorem; classical DH is for zeros near `s=1`. Batch 7 Dead.
**Verdict: Dead.**

### II.17 `BDH_to_pointwise` — Dead

**Idea.** Upgrade Barban–Davenport–Halberstam to every `a` via amplification.
**Bookkeeping.** BDH controls `∑_a |ψ(x;q,a)−x/φ(q)|²`. Amplification / Hölder cannot produce uniform every-`a` saving of the strength needed without essentially a large-sieve converse that fails for the barrier configuration (spike at one `a`).
**vs barrier.** Linear-`k` alignment is exactly a BDH-compatible spike (one bad `a`, average still fine).
**Verdict: Dead.**

### II.18 `exceptional_helps` — Partial (conditional; wrong box)

**Idea.** Exceptional character helps (FI: `L=2−1/55` under Siegel zero).
**Bookkeeping.** Gives every-`a` under an exceptional zero, with strong `L`. Does **not** help the CGL density box at `σ=5/7` without a Siegel zero; the repo’s certificate already assumes the non-exceptional landscape for the hard corner.
**Verdict: Partial** (known conditional win) / **Dead** for unconditional `A<7/3`.

### II.19 `DFI_kloosterman` — Dead for Linnik@2.2 every `a`

**Idea.** DFI bilinear forms / Kloosterman fractions.
**Bookkeeping.** Powerful in ranges for Type II; exclusion overlaps cgl-s3 Kloosterman attempts. Not a complete every-`(q,a)` at `2.2`.
**Verdict: Dead** for the test.

### II.20 `FI_sieve_Linnik` — Partial / Dead for `L<11/5`

**Idea.** Friedlander–Iwaniec sieve Linnik without density.
**Bookkeeping.** Every-`(q,a)` **yes**; `L≈7.57×10⁷` in arXiv:2303.06122. Architectural Partial (Batch 7); exponent Dead for our target.
**Verdict: Partial** (architecture) / **Dead** (`L<11/5`).

---

## Ingredient II summary

| # | id | verdict | every-`(q,a)` at `x~q^{2.2}` beyond density? |
|---|---|---|---|
| 01 | `linear_k_barrier_break` | Dead | no (circular) |
| 02 | `short_interval_AP` | Dead | no |
| 03 | `DH_cluster_repulsion` | Dead | no |
| 04 | `chebotarev_cyclotomic` | Dead | no |
| 05 | `maynard_GPY_AP` | Dead | no |
| 06 | `automorphic_theta` | Dead | no |
| 07 | `bombieri_asymp_one_AP` | Partial/Dead | yes but huge `L` |
| 08 | `vinogradov_exp_AP` | Dead | no |
| 09 | `bettin_chandee_AP` | Dead | no |
| 10 | `rankin_selberg_AP` | Dead | no |
| 11 | `HB_identity_Weil` | Partial fuel | no alone |
| 12 | `parity_breaking_AP` | Dead | no |
| 13 | `algebraic_traces` | Dead | no |
| 14 | `BV_to_pointwise` | Dead | no (avg only) |
| 15 | `zhang_dispersion_fixed` | Dead | no |
| 16 | `DH_nonstandard` | Dead | no |
| 17 | `BDH_to_pointwise` | Dead | no (barrier spikes) |
| 18 | `exceptional_helps` | Partial cond. | conditional only |
| 19 | `DFI_kloosterman` | Dead | no |
| 20 | `FI_sieve_Linnik` | Partial/Dead | yes, useless `L` |

**Strongest II finding:** no arithmetic input checked gives a new unconditional every-`(q,a)` prime lower bound at `x~q^{2.2}` beyond zero-density+triangle, except sieve-Linnik with unusable `L`. Averages (BV/BDH/Zhang) fail the every-`(q,a)` test; the linear-`k` barrier specifically kills BDH→pointwise upgrades.

---

## Cross-cutting: barrier test results

| Test case | What it kills | What survives |
|---|---|---|
| TPM-ADV MVT saturation | unrestricted `η>0` (Batches 5–6) | **restricted-coeff LV** (ADV not realisable) |
| Linear-in-`k` zero alignment | every-`a` signed saving from zero-info; BDH→pointwise | sieve architectures that never pass through signed `Z` |

---

## Live leads (honest)

1. **`restr_coeff_LV` / ADV-loophole (Ingredient I):** **Retracted** as a path into CGL
   Thm 1.3→1.4 (LV is for arbitrary `|a_n|≤1`). Residual: `cgl-s3` §8 hypothesis (H) on
   sixth-moment equidistribution of short intervals at `|I|≈q^{7/18}` — open, not advanced here.

2. **Ingredient II:** no live analytic lead toward `L<11/5`. Monitor FI/MMT only if
   their `L` drops below `~3` in the literature.

**No improvement of `A` or `L` claimed. No Lean. Docs/scripts only.**


---

## ADV-realisability loophole — sceptical verification

**Date:** 2026-11-09 (follow-up). **Script:** `scripts/ingredient_hunt/loophole_verify.py`.
**Sources:** CGL arXiv:2507.08296 (Thm 1.3, Prop 3.1, Lemmas 4.1–4.2, §12 as read in
`docs/cgl-s3-prime-moduli.md` §8); Guth–Maynard (arbitrary `|a_n|≤1`).

### 1. What coefficients does CGL’s LV apply to?

**Theorem 1.3 / Proposition 3.1 (verbatim structure).** The large-values estimate is for

```
D_N(t,χ) = ∑_{N<n≤2N} a_n χ(n) n^{it},     |a_n| ≤ 1,
S_N(t,χ) = ∑_n w(n/N) b_n χ(n) n^{it},     |b_n| ≤ 1,
```

with `w` a fixed smooth bump on `[1,2]`. The matrix in §4 is

```
M_{(t,χ),n} = w(n/N) χ(n) n^{it}
```

— **coefficient-free**. Lemma 4.1 absorbs `|b_n|≤1` into `|W| ≲ N^{1−2σ} s_1(M)^2`. So the
proved LV bound is for **arbitrary 1-bounded coefficients**, exactly as in Guth–Maynard.

**Zero-density (§12) pipeline.**
1. Short mollifier `M_X` with `X = (qT)^ε` produces coefficients `c_n = ∑_{d|n, d≤X} μ(d)`.
2. Class-I detection gives a large value of a weighted Dirichlet polynomial in those `c_n`.
3. After dyadic decomposition / partial summation (and, in the general-`T` argument, the
   application of Thm 1.3 as a black box), the LV theorem is invoked in the **arbitrary
   `|a_n|≤1`** form.
4. Hölder / power-raising (as in the `S_2` estimate, §6: rewriting `|D|^{2k}` as a longer
   Dirichlet polynomial with divisor-bounded coefficients `|b_m| ≲_k M^ε`) **destroys**
   pure interval structure: the resulting coefficients are divisor-bounded, then treated
   as general 1-bounded sequences.

**Structure that survives into Thm 1.3:** only `|a_n|≤1` (or divisor-bounded, absorbed in
`(qT)^ε`). Multiplicativity / interval support / mollifier shape is **not** an input to
Thm 1.3.

**At `T = 1` only** (`cgl-s3` §8, reading CGL §12): short mollifier + `|t|≤1` reduces
class-I to **interval character sums** `S_I(χ)` of length `x ≤ q^{1/2+ε}`, with the
fourth/sixth-moment meeting at `x = q^{7/18}`. There “the arbitrary coefficients of
Theorem 1.1 never arise.” That is a **different route** from Thm 1.3→1.4.

### 2. Verdict on the loophole

| Claim from ingredient hunt | After sceptical check |
|---|---|
| ADV is not μ/interval-like (`corr≈0.04–0.26`) | **Still true** numerically |
| Therefore restricted-coeff MVT-beyond plugs into CGL density | **False** for the main Thm 1.3→1.4 route: that LV is for arbitrary `|a_n|≤1`, and ADV is exactly a legitimate saturator of that theorem’s hypothesis |
| Interval LV at `(N,V)=(q^{7/9},N^{5/7})` has slack vs ADV | **Toy**: that pair is the Thm 1.3 critical length, but for **pure intervals** Pólya–Vinogradov gives `|S_I| ≪ √q log q`, while `N^{5/7}=q^{5/9}`; asymptotically `5/9>1/2`, so `|W|=0` for large `q`. Empirically `W_init=0` already at `q≤3·10^4` (`max|S| < V`). This does **not** feed Thm 1.4 |
| Completing `N=q^{7/9}` → dual length `q^{2/9}` beats MVT’s `2/3` | **Does not apply**: PV already kills the object; dual-moment bookkeeping cannot beat PV |

**Realisability for the main theorem: loophole closed.**
ADV (TPM, `|b_n|` free then projected to `|b|≤1`) is a valid test case for Thm 1.3.
Batches 5–6 η-kills on ADV stand.

**Residual Partial (narrow):** the `T=1` interval-only alternate route of `cgl-s3` §8 —
hypothesis (H) on `J_6(I)` at `|I|≈q^{7/18}` — was already identified there; it is **not**
the ADV-realisability loophole, and it does not follow from completing at `N=q^{7/9}`.

### 3. Numerics (`loophole_verify.py`)

**(A) Intervals at Thm 1.3 length `N=q^{7/9}`, `V=N^{5/7}`:**

| `q` | `N` | `V` | `max\|S_{[1,N]}\||` | `W_init` |
|---|---|---|---|---|
| 503 | 126 | 31.6 | 25.4 | **0** |
| 1009 | 217 | 46.7 | 35.4 | **0** |
| 10007 | 1292 | 167 | 131 | **0** |
| 30011 | 3036 | 307 | 216 | **0** |

**(B) True `T=1` length `x=q^{7/18}`, `V=x^{5/7}`** (matches `cgl-s3` §8):

| `q` | `x` | `W_{[1,x]}` | `W_{(x,2x]}` | `q^{2/3}` |
|---|---|---|---|---|
| 10007 | 36 | 428 | 164 | 464 |
| 30011 | 55 | 940 | 318 | 966 |
| 100003 | 88 | 2246 | 698 | 2154 |

Initial segment saturates `~q^{2/3}`; dyadic block is milder — as previously recorded.

**(C) ADV vs structure at `q=10007`:** `corr(ADV, interval)=0.21`,
`corr(ADV, short det)=0.26`, `corr(ADV, d₂)=0.09`, `corr(ADV, rand mult)=0.02`.
ADV is not detector-like — but Thm 1.3 does not require detector-like coefficients.

### 4. Restricted LV bound? Exponent?

**No new bound beating `2/3` that transfers into Thm 1.4.**

- Pure intervals at `(q^{7/9}, N^{5/7})`: trivial `|W|=0` by PV (asymptotic) / numerics — **toy**.
- `T=1` intervals at `q^{7/18}`: fourth and sixth moments both give `|W|≪ q^{2/3}`; completing
  the sum (dual length `q^{11/18} > √q`) does not improve the exponent with known complete-sum
  technology (Weil / PV). Beating `2/3` here is exactly conjecture (H) of `cgl-s3` §8 —
  open, not proved here.
- Structured coefficients inside Thm 1.3: would require a **new** LV theorem for a subclass
  closed under the detector→Hölder pipeline. Mollifier coefficients `μ*1_{[1,X]}` with tiny `X`
  become near-interval after writing `n=dm`; Hölder then produces divisor-bounded sequences.
  No such restricted theorem is proved in this follow-up.

### 5. Transfer checklist (line-by-line honesty)

1. Does Thm 1.3 assume only `|a_n|≤1`? **Yes** (Prop 3.1, Lemma 4.1).
2. Does zero-density invoke Thm 1.3 as a black box on general coefficients? **Yes** for the
   `4/(1+σ)` half (Thm 1.4).
3. Does `|W_crit|=0` for intervals at `N=q^{7/9}` improve `A`? **No** — wrong object.
4. Does ADV fail to match `μ`/interval imply Thm 1.3 has slack on detectors? **No** — Thm 1.3’s
   proof never uses coefficient structure; S₃/Prop 8.1 bounds are coefficient-free (they bound
   `s_1(M)` for the character matrix).
5. Is there a written restricted LV inequality here that beats MVT’s `2/3` and transfers?
   **No.**

### Updated live-lead status

| Previous claim | Updated |
|---|---|
| `restr_coeff_LV` / ADV-loophole **Partial / Promising** | **Dead** as a plug-in to Thm 1.3→1.4 / `mvt_beyond` |
| Residual | `T=1` hypothesis (H) on `J_6` at `\|I|≈q^{7/18}` — already in `cgl-s3` §8; unchanged Partial / open |

**No improvement of `A` or `L`. Loophole retracted for the main density theorem.**
