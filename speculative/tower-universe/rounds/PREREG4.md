# Pre-registration, round 4: quantum-like behaviour, and "prime → orthogonal → quarter rotation"

Written 2026-11-06, before any of these numbers were computed. These are tests of the tower's own geometry. They are
not fits to measurements, except Q4, which compares with a class of measured spectra.

## Q1. Does a prime arrive orthogonal?

- **Measure.** The angle `θ_n` between `w_n` and the span of `w_1, …, w_{n−1}`, from `sin²θ_n = d_n/(n·H₀)` (Cholesky
  pivots), for `n ≤ 4096`.
- **Confirmed if** primes arrive at `≥ 45°` while composites do not.

## Q2. Does a prime turn the thinnest axis a quarter turn?

- **Measure.** The angle between the smallest eigenvectors of `G_N` and `G_{N−1}`, the latter padded with a 0, for
  `N ≤ 600`.
- **Confirmed if** primes turn it by `≥ 45°` (a quarter turn is 90°) while composites do not.

## Q3. Wave–particle duality: build each side back from the other

- **Particles → waves.** Fourier-transform the tower's correlation `K(e^u)`, computed from the primes alone
  (`u ≤ log 2²²`). Pass: peaks within 0.5 of each of `γ₁, …, γ₈`.
- **Waves → particles.** Sum `−Σ cos(γ_k u)` over the first zeros. Pass: peaks within 0.02 of `log pᵏ` for every prime
  power `pᵏ ≤ 30`.

## Q4. Quantum class

- **Measure.** The zeros' unfolded nearest-neighbour spacings, against three distributions (Wigner surmises):
  - GUE: a quantum system without time-reversal symmetry;
  - GOE: one with time-reversal symmetry;
  - Poisson: no quantum correlations.
- **Report** the share of spacings below 0.25 and the KS distance to each. The class is whichever is closest.
