# Pre-registration: can the tower be fitted to measurements without wangling?

Written 2026-11-06, before any model-vs-data comparison below was computed. Nothing in this file is edited after
the results exist; results go in `RESULTS.md`.

## The model (not changed)

`G_N(m,n) = Σ_ρ m^ρ n^ρ̄ / |ρ|²`, its smallest eigenvalue `λ_N`, the zeros `ρ = ½ + iγ`. Model values used:

- `λ_N·N = Λ*·log N + b`, with `Λ* = 0.0429` (variational constant; proved upper bound `0.04294 + o(1)` under RH;
  `≥ 0.0400` on the arithmetic class) and `b = 0.032` (fit, `N ≤ 3·10⁴`). Proven-only range under RH:
  `√log N/(220e⁸) ≤ λ_N·N ≤ (0.04294 + o(1))·log N`.
- Every pure number already reported for the model in this conversation or the repo (list in `fit.py`, section T3),
  except proof constants (`e²⁴`, `220e⁸`, `67`, `1/100`) and counterfactual runs with moved zeros.

## The dictionary: only what was fixed before

- **Clock.** One integer per Planck time, `N = t/t_P` (the user's "10⁶⁰ far down"), or one prime per Planck time,
  `π(N) = t/t_P` (the prime clock). Now: `t₀ = 13.787 ± 0.020 Gyr` (Planck 2018), so `N_now = t₀/t_P ≈ 8.07·10⁶⁰`.
- **Quantities.** The model has one scale, `λ_N`, falling like `1/N`. In Planck units a rate falls like `1/t` and an
  energy density like `1/t²`. So the only dimensionally honest readings are:
  - **D1.** `H(t)·t_P = λ_N`, integer clock.
  - **D2.** `H(t)·t_P = λ_N`, prime clock.
  - **D3.** `ρ_vac(t) = λ_N²` in Planck density units, integer clock; matter conserved separately.
  - **D4.** As D3, prime clock.
- **Units.** Unreduced (`ħ = c = G = 1`). Reduced units (`8πG = 1`) are reported as the convention spread, never chosen
  per test.

## The tests

- **T1, no free parameters.**
  - D1, D2: `H₀t₀` against `0.950 ± 0.008` (Planck 2018). Also against stellar ages with SH0ES, range `0.92–1.03`.
  - D3, D4: `Ω_vac` against `0.685 ± 0.007`.
  - Pass: within 2σ, or within the spread over unit conventions.
- **T2, shape only.** The amplitude is free, as Λ is in ΛCDM.
  - Data: DESI DR2 BAO, all 13 points, full covariance, `H₀r_d` free (no CMB, no `r_d` prior).
  - Pass: `p > 0.01` and `Δχ²` against flat ΛCDM (same parameter count) `< 9`.
- **T3, numerology audit.**
  - Every model number against headline dimensionless measurements (PDG 2024, CODATA 2022, Planck 2018), with
    `z = |M − P|/√(σ_P² + σ_M²)`.
  - Report the best direct match. Its look-elsewhere p-value comes from random replacements of the model numbers:
    U(0,1) for fractions, log-uniform over one decade around the value otherwise.
  - Repeat with wangling allowed, to show the null keeps pace:
    - L1: `x, 1/x, 1−x, x², √x`.
    - L2: L1 times `{1, 2, 3, 4, ½, ⅓, ¼, π, 1/π, 2π, 1/2π, 4π, 1/4π, 8π, 1/8π, e, 1/e}`.

## Decision rule

The model fits only if some dictionary passes both T1 and T2, or if T3's direct-match p-value is `< 0.003`.
