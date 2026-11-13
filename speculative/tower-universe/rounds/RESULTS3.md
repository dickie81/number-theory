# Results of round 3 (PREREG3.md)

Raw output: `round3.out` (from `round3.py`).

**Verdict: no fit.** O1 is the first of the eight readings to pass a T1, but it fails T2.

## O1: from inside, `a ∝ t` (coasting), on either clock

| Test | Prediction | Measured | Result |
|---|---|---|---|
| T1 | `H₀t₀ = 1` | cosmology-independent range `0.92–1.03` (fixed in round 1) | inside |
| T1 | `H₀t₀ = 1` | Planck `0.950 ± 0.008`, which assumes ΛCDM | 6.3σ off |
| T2, DESI DR2 BAO | χ² = 187.1 for 12 dof (p = 10⁻³³) | flat ΛCDM: χ² = 10.3 for 11 dof | Δχ² = 176.8 (13.3σ), fails |

## O2: what marks "now" from inside

- **The view of the past is a function of `1 + z` only.** `corr(w_N, w_n) = K(N/n)/H₀` depends on `N/n = 1 + z` alone.
  This is exact, from `G = √(mn)·K(m/n)`. So every epoch is a rescaled copy of every other.
- **Only the arithmetic marks the epoch.** Two examples:
  - The share of new integers that are prime is `1/log N = 1/140`.
  - `N·λ_N = 6.05`.
- **They move about 130 times too slowly.** Each changes by 0.71% per e-fold of time. In our universe `Ω_Λ` changes by
  about 90% per e-fold of time (`3Ω_m·H·t`). The factor is about `log N`.
