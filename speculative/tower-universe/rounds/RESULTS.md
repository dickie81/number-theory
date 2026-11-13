# Results of the tests in PREREG.md

The raw output is in `fit.out` (T1, T2) and `t3.out` (T3, rerun with the null rounded like the model's numbers).
Data: DESI DR2 BAO means and covariance from CobayaSampler/bao_data. As a check, flat ΛCDM fitted to those 13 points
gives `Ω_m = 0.2975`, the DESI DR2 paper's BAO-only value (`0.2975 ± 0.0086`).

**Verdict: no fit.** No reading passes T1 or T2, and T3's best direct match has p = 0.21.

## T1, no free parameters

`N_now = 8.07·10⁶⁰`, `log N_now = 140.24`. `N·λ_N` at `N_now` is `6.05` by the law, and `5.61–6.02` on the arithmetic
class. With only what is proven under RH, it is anywhere in `[1.8·10⁻⁵, 6.02]`.

| Reading | `H₀t₀` | `q₀` | `Ω_vac` | Measured |
|---|---|---|---|---|
| D1 rate, integer clock | 6.05 | −0.84 | – | `H₀t₀ = 0.950 ± 0.008`, `q₀ = −0.53`, `Ω_Λ = 0.685` |
| D2 rate, prime clock | 0.043 | +22 | – | |
| D3 density, integer clock (G = 1 / 8πG = 1) | 17.5 / 3.45 | −0.94 / −0.71 | 1 (no room for matter) | |
| D4 density, prime clock (G = 1 / 8πG = 1) | 0.667 | +0.5 | 0.036 / 0.0014 | |

## T2, shape only (DESI DR2 BAO, `H₀r_d` free)

| Shape | χ² (dof) | p | Δχ² against ΛCDM |
|---|---|---|---|
| flat ΛCDM | 10.3 (11) | 0.51 | 0 |
| D1, `H·t = A·log t` | 94.9 (11) | 2·10⁻¹⁵ | 84.6 (9.2σ), best `H₀t₀ = 0.91` |
| D2, power law | 97.0 (11) | 7·10⁻¹⁶ | 86.7 (9.3σ), best `p = 0.91` |
| D3/D4, `a ∝ t^{2/3}` | 1420 (12) | ~0 | 1410 (37σ) |

D3 with `V > 4/9` has no matter and is a power law, the D2 row. D1 with its own amplitude has `χ² = 10442`.

**Why the shapes fail.** Any reading in which `H·t` follows `λ_N·N` makes `H·t` nearly constant. Between `z = 2.33` and
today it changes by 1.1% in D1, while the data need 42% (best-fit ΛCDM: `0.68 → 0.97`).

## T3, numerology audit

44 model numbers were compared with 38 measurements. The null replaces each model number with a random one: U(0,1)
for fractions, log-uniform over a decade otherwise, rounded to the same decimals.

| Level | Best match | Random do as well | Within 1σ (random median) |
|---|---|---|---|
| L0 | `τλ at N = 4096 = 0.0541` vs reionisation `τ = 0.0544`, 0.04σ | 21% | 8 (6), p = 0.34 |
| L1 | same | 67% | 33 (28), p = 0.17 |
| L2 | `½·0.0439 = 0.02195` vs `sin²θ₁₃ = 0.02195`, 0.00σ | 26% | 453 (458), p = 0.62 |

**The `Ω_m` look-alike.** The share of the first two zeros is `0.3144`.

| Against | Measured `Ω_m` | Distance |
|---|---|---|
| Planck 2018 | 0.3153 ± 0.0073 | 0.13σ |
| DESI DR2 BAO | 0.2975 ± 0.0086 | 1.96σ |
| DESI + CMB | 0.3027 ± 0.0036 | 3.25σ |

## Departure from the pre-registration

The first run of T3 used an unrounded null, which cannot reproduce exact coincidences between 3–4-digit numbers. That
made L2 look significant (p = 0). Rounding the null like the model's numbers fixes it (p = 0.26). Nothing else changed.
