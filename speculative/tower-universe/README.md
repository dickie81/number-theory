# The tower as a universe: what works, and what it assumes

This folder is exploratory and separate from the library: no paper uses it and nothing in it is proved in Lean. It
records a series of numerical tests of one idea: that the orbit Gram matrix of
[`docs/ball-conjecture.md`](../../docs/ball-conjecture.md), here called the tower, could be a model of physics.

**Method.**
- Each round's test was written down before its numbers were computed (`rounds/PREREG*.md`).
- Its result is in `rounds/RESULTS*.md`.
- The few checks added after seeing the data are marked as such there.
- Numerical coincidences were judged against random numbers (round 1).

**Page.** [`gravastar-tower.html`](gravastar-tower.html) shows the tower being built, one integer at a time. Open it
in a browser. It shows:
- λ_N, computed live to 2048 and from precomputed tables to 32768;
- the prime clock;
- what happens when the first zero is moved off the line.

**Summary.**
- The mathematics behaves like quantum mechanics in several exact ways.
- With three extra axioms, two physical tests pass: isotropy and the age of the universe.
- No reading reproduces the expansion history. The tower looks the same at every scale, and the data need a special
  epoch.

## The object

- **The tower.**
  - `w_n = (n^ρ/|ρ|)_ρ`, in `ℓ²` of the nontrivial zeros of ζ.
  - Gram matrix `G_N(m, n) = √(mn)·K(m/n)`, with `K(r) = Σ_ρ r^{ρ−½}/(ρ(1−ρ))`, computed from the primes by the
    explicit formula (`scripts/ball_orbit.py`).
  - `G_N` is positive definite for every `N` exactly when RH holds (`BallKernel.rh_iff_posDef`).
- **The thinnest axis.** `λ_N`, the smallest eigenvalue of `G_N`.
  - Fitted: `λ_N·N = 0.0434·log N + 0.032` for `10³ ≤ N ≤ 3·10⁴`.
  - Proved on paper under RH: the upper bound `λ_N ≤ (0.04294 + o(1))·log N/N`
    ([`formalisations/ball-rate.md`](../../formalisations/ball-rate.md)).
  - Proved in Lean: `√log N/N ≪ λ_N ≪ log N/N` under RH.
- **A quantum system.**
  - `w_n = √n·U(log n)v₀`, with `U(u) = diag(e^{iγu})` unitary and `v₀ = (1/|ρ|)_ρ`.
  - That is a state evolving with the zeros as its energies, sampled at the times `log n`.
  - RH says that these overlaps come from a genuine Hilbert space.

## The axioms

The mathematics below needs none of these. Each physical reading uses some of them, named in its row.

| | Axiom | Introduced in |
|---|---|---|
| A1 | **Clock.** One integer per Planck time, so now is `N ≈ t₀/t_P ≈ 8.07·10⁶⁰`. A variant, A1′, takes one prime per Planck time. | Round 1 |
| A2 | **Embedded observer.** An observer is a vector of the tower and observes only through inner products (correlations) with other vectors. | Round 7 |
| A3 | **3D window.** Our space is the observer's 3D window in the hyperspace, built from the tower's own current vectors. It therefore turns with the spiral: it is the outer product's top three axes. | Round 10 |
| A4 | **Light and redshift.** Light is the zeros' modes `n^{iγ}`. Redshift is the ratio of a mode's frequency per tick at emission and at observation, `1 + z = N/n`. | Round 3 |
| A5 | **Outcomes.** A measurement outcome is a click, a kink in an observer's correlation. Apparent randomness is the arithmetic behind the clicks, for example the parity of the number of clicks per tick. | Rounds 7–8 |

**Background assumptions,** used only when extrapolating to `N ≈ 10⁶⁰`:
- RH, so that the tower exists there;
- the `λ_N` law above.

## What works

### Mathematics: no axioms

| Result | Numbers | Round |
|---|---|---|
| **Wave–particle duality, both ways** | From the primes alone, the Fourier transform of `K(e^u)` (`u ≤ log 2²²`) peaks at the first 8 zeros, to within the grid step of 0.002. From 100 zeros alone, `−Σ cos(γ_k u)` peaks at all 16 prime powers `≤ 30` and nowhere else. | 4 |
| **Level repulsion** | The spacings of the first 3000 zeros are GUE: KS distance 0.035, against 0.102 for GOE and 0.313 for Poisson. 0.7% of the spacings are below 0.25. | 4 |
| **The primes need dimensions** | An observer seeing `K` zeros (`2K` dimensions) tells the prime powers in `[2, 1000]` from other integers with AUC 0.53 (2 dimensions), 0.69 (100), 0.86 (600) and 0.999 (6000). Seeing the primes up to `P` takes about `2P·log P` dimensions, so a 3D slice is blind to them. | 5 |
| **Each integer adds a dimension** | In the full space every `w_n` leaves the span of the earlier ones (RH). In any 3D slice, the first three integers already fill it. | 5 |
| **The outer product's two parts** | The bulk of `Σ_{n≤N} w_n w_n^†` is frozen: its top three axes hold 30.23% of the trace, with participation ratio 22.7, at every `N`. Its smallest nonzero eigenvalue is `λ_N`, `2·10⁻⁹` of the largest at `N = 4096`. | 5, 10 |
| **Prime packets** | A packet is a prime and the integers after it, up to the next prime. The prime's own kick to `1/λ_N` is 2.5 integers' worth (quartiles 2.2–2.9). The packet's size is about `1.75 + 0.75·gap`. | 6 |
| **Clicks** | `G(N, n)`, as a function of `N`, has a kink of strength `log p/p^k` exactly when `N = n·p^k`, and nowhere else. The residual is `≤ 2·10⁻⁶` for `N ≥ 100`. At tick `N`, an embedded observer registers one click for each prime power dividing `N`, so the clicks spell out `N`'s factorisation. A prime is the quietest tick: one click, against `n = 1`. An embedded observer finds the click times perfectly (AUC 1.000); an observer in a 3D slice cannot (0.57). | 7 |
| **Who is registered** | Per tick, species `p` contributes `log p/(p² − 1)` out of a total of `−ζ′(2)/ζ(2) = 0.570`. That is 40.5% for 2, 24.1% for 3, 11.8% for 5 and 7.1% for 7. All primes above 100 together give 1.7%, though they hold 96.7% of `Σ log n` at our epoch. A prime born at tick `p` first appears in a composite at `2p`, then once every `p` ticks. At any `N`, about half the primes (those in `(N/2, N]`) appear in no composite yet. | `exchanges.py` |
| **Every place holds the tower up** | Split `K` place by place. The real place alone fails positive definiteness at `N = 3`, and the finite places alone give no lengths. Keeping only the places `p ≤ P`, the tower fails one or two integers after the first missing prime. Dropping one place `p`, it fails at `p + 1` for `p ≤ 31`, at 103 for 101, and at 1017 for 1009. | 2 |
| **A deterministic coin** | The click parity `λ(N) = (−1)^{Ω(N)}` is locally fair up to `10⁷`: all 8 three-step patterns occur at 0.1249–0.1251. Its running sum drifts by `√N/ζ(½)` (measured −0.682, predicted −0.685). The zeros predict its wiggles, with correlation 0.961, 0.985 and 0.995 from 10, 50 and 200 zeros. RH holds exactly when the running sum is `O(N^{½+ε})`. | 8 |
| **Isotropy in the turning frame** | In axes that turn with the spiral, the 3D cloud's shape is frozen at `1 : 0.947 : 0.617`. Every axis expands at `H·t = ½`, and the shear falls like `1/N`: `1.8·10⁻⁶` at `N = 2²¹`. | 10 |
| **Self-similarity forces power laws** | If the expansion looks the same from every epoch, then `H(a_e)/H(a_o) = f(a_o/a_e)` with `f(xy) = f(x)·f(y)`, so `H ∝ a^{−k}`. | 11 |

### Physics readings that pass a test

| Reading | Axioms | Test | Result |
|---|---|---|---|
| **Isotropic expansion** | A1, A2, A3 | The CMB limit on shear, `σ/H < 4.7·10⁻¹¹` (Saadeh et al. 2016) | **Pass**: `σ/H ≈ 7·10⁻⁶²`, extrapolated to now (round 10). In fixed outside axes it fails, with `σ/H ≈ 0.8` (round 2). |
| **The age** | A1, A2, A4 | `H₀t₀` from the distance-ladder `H₀` and the ages of the oldest stars: 0.92–1.03 | **Pass**: `H₀t₀ = 1` (round 3). Planck's 0.950 ± 0.008 assumes ΛCDM; against it, the reading is 6.3σ off. |
| **Randomness as hidden variables** | A1, A5 | 2·10⁸ ANU quantum random bits (Kavulich, Van Deren and Schlosshauer 2021) | **Consistent** (round 9). Neither the quantum bits nor the tower's coin at `N ≥ 10¹²` shows the coin's fingerprints from its origin. This is consistency, not support: at our epoch no randomness test can tell the two apart. |
| **Quantum statistics** | The zeros as energies | The zeros' class, GUE, is the one measured in chaotic quantum systems without time-reversal symmetry (So et al. 1995) | **Agrees** (round 4). The class is universal, so it supports no model in particular. |
| **Light as the main messenger** | A2 | — | Species 2 carries 40.5% of what an embedded observer registers. Qualitative only. |
| **Bell tests** | A2, A5 | Loophole-free Bell tests (2015) | **Consistent only through superdeterminism.** An observer's choice of setting is fixed by the same arithmetic as the outcome. An interpretation, not a test. |
| **Flat space** | A3 | `Ω_k ≈ 0` | A hyperplane is flat. Every model gets this. |

## What does not work

| Attempt | Result | Round |
|---|---|---|
| `λ_N` as the expansion rate or the vacuum energy | `H₀t₀ = 6.05`, 0.043, 17.5 or 0.667, against 0.950 | 1 |
| The expansion history, in every reading | Against DESI DR2 BAO with `H₀r_d` free: the best power law is 9.3σ worse than ΛCDM, `a ∝ t` 13.3σ, `a ∝ t^{½}` gives χ² = 5436, and `a ∝ t^{2/3}` is 37σ worse | 1–3 |
| A brane's geometry (DGP) | Fits DESI's BAO alone (2.2σ), fails BAO with the CMB by 13.4σ, and needs its crossover length set by hand | 11 |
| Numerical coincidences | Against 38 measured constants, the model's numbers match no better than random numbers do (p = 0.21 for the best direct match). See [The coincidences](#the-coincidences) | 1 |
| The window's share as the matter fraction | 30.23%, against Ω_m = 30.27 ± 0.36% (DESI + CMB). Not blind, and frozen: a constant matter fraction means Einstein–de Sitter expansion, excluded at 37σ. See [The coincidences](#the-coincidences) | 10 |
| Primes as matter, composites as radiation | 138 composites per prime, against 1.6·10⁹ photons per baryon. Matter comes first and radiation after, the reverse of our history. The share of primes changes about 270 times too slowly | `exchanges.py` |
| 2 and its multiples as photons | The lightest, commonest, bosonic species, and the main messenger. But it is not massless, it is 17% of all quanta, and from inside its share is frozen and its light comes only from the shells `1 + z = 2, 4, 8, …` | `exchanges.py` |

**The common cause.** The tower looks the same at every scale. What an observer at `N` sees depends only on `n/N`, and
the tower's only epoch-dependent quantities move like `log N`, 130 to 270 times too slowly for cosmic history. So
every reading gives a power-law expansion with no special epoch, while the data need a switch from deceleration to
acceleration about 6 Gyr ago. Fixing this needs a fixed second scale. That would be a new axiom: nothing in the tower
supplies one.

## The coincidences

Several of the tower's numbers land close to measured ones. None of them counts as evidence. They are recorded here in
full so that they are neither lost nor oversold.

### The 3D window and the matter fraction

- **The match.** The observer's 3D window (A3) is the outer product's top three axes. It holds 30.23% of the tower:
  0.3024, 0.3024 and 0.3023 at `N` = 1024, 2048 and 4096. The other 69.77% lies in the hidden dimensions. Against
  today's matter fraction:

  | Measurement | Ω_m | Distance |
  |---|---|---|
  | DESI DR2 + CMB | 30.27 ± 0.36% | 0.1σ |
  | DESI DR2 BAO alone | 29.75 ± 0.86% | 0.6σ |
  | Planck 2018 | 31.53 ± 0.73% | 1.8σ |

  The hidden share matches Ω_Λ in the same way. That is the same coincidence, not a second one: both sides add to 1.
- **How blind it was.** Not at all. The share first came out of round 5, which computed it for another purpose, and
  both numbers were known when round 10 compared them. Other shares had already been compared with Ω_m: the drawn
  slice (26%) and the first two zeros (31.4%).
- **Why it does not count.** The window's share is the same at every `N`; the matter fraction is not. It was about 78%
  at z = 1. At the CMB it was 76%, with radiation at 24% and Λ at `10⁻⁹`. A matter fraction fixed at 30% means
  Einstein–de Sitter expansion, which DESI excludes at 37σ (round 1).
- **What would change that.** A mechanism inside the tower that made the window's share evolve like Ω_m(z). Nothing in
  the tower does.

### Other near-matches

| Tower | Measured | Context |
|---|---|---|
| The share of each unit vector in the first two zeros' planes: 31.44% | Ω_m = 31.53 ± 0.73% (Planck 2018): 0.13σ | Found by the round 1 audit, among 44 model numbers and 38 measurements. Random numbers match this well 21% of the time. It is 2.0σ from DESI BAO alone and 3.3σ from DESI + CMB. |
| `τ·λ_N` at `N = 4096`: 0.0541 | The reionisation optical depth, 0.0544 ± 0.0073: 0.04σ | The round 1 audit's best direct match. An imprecise measurement is an easy target. |
| Integers with at most two prime factors at our epoch: about 4.4% | Ω_b = 4.9% | The cut is a free choice: 0.7% for primes only, about 13% for up to three factors (`exchanges.py`). |
| Integers per prime at our epoch: `N/π(N) = 139.24` | `1/α = 137.036` | A miss. The tower's number is fixed to about `10⁻⁵`, so 1.6% is far off. It would have matched when the universe was 1.53 Gyr old. |

## Reproducing

`rounds/` holds each round's pre-registration (`PREREG*.md`), script, raw output (`*.out`) and results
(`RESULTS*.md`). Run the scripts from that directory:

```sh
sh fetch_data.sh   # DESI DR2 BAO (from CobayaSampler/bao_data) and the first 2.5·10⁸ ANU quantum bits (Zenodo 4440318)
python3 fit.py     # round 1
```

The rounds and their scripts:

| Round | Scripts |
|---|---|
| 1 | `fit.py` |
| 2 | `round2.py` |
| 3 | `round3.py` |
| 4 | `quantum.py`. It recomputes the 3000 zeros (about 15 minutes) unless `zeros_3000.npy` is present. |
| 5 | `slice5.py`, `outer7.py` |
| 6 | `packets.py` |
| 7 | `clicks.py` |
| 8 | `liouville.py` |
| 9 | `round9.py`, `round9b.py` |
| 10 | `window10.py` |
| 11 | `dgp11.py`, `dgp11b.py` |
| Discussion between rounds | `exchanges.py` |

`page/offline.py` recomputes the page's tables: one Cholesky factorisation per scenario, up to `N = 32768`, taking
about 15 minutes. `page/inject.py` then writes them into the page.

**Sources:**
- DESI Collaboration, DR2 Results II (2025), arXiv:2503.14738.
- Chen, Huang and Wang, JCAP 02 (2019) 028: the Planck 2018 shift parameter.
- Saadeh, Feeney, Pontzen, Peiris and McEwen, PRL 117 (2016) 131302.
- So, Anlage, Ott and Oerter, PRL 74 (1995) 2662.
- Kavulich, Van Deren and Schlosshauer, Phys. Lett. A 388 (2021) 127032.
