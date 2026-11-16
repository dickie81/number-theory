# Pre-registration, round 9: real quantum random bits against the tower's coin

Written 2026-11-06, before any of the bulk data was downloaded or examined.

## Sequences

Every sequence is 10⁷ steps of ±1, read from its first bit.

- **QRNG.** ANU quantum random bits (vacuum fluctuations), from Kavulich, Van Deren and Schlosshauer, Phys. Lett. A 388,
  127032 (2021), Zenodo 4440318 (CC-BY). The first 2·10⁸ bits of `anubits_1`, as 20 consecutive chunks. Bit 1 is +1.
- **Tower, from its origin.** λ(n) = (−1)^Ω(n) for n = 1 … 10⁷.
- **Tower, late.** λ(n) on windows of 10⁷ integers: 4 starting at 10¹² and 4 starting at 10¹⁵.
- **Pseudo-random control.** 20 chunks from numpy's PCG64, seed 20261106.

## Statistics, each anchored at the sequence's first step

- **S1, local.**
  - The 8 three-step patterns: the largest deviation from 1/8, in binomial standard deviations.
  - The bias, mean(bits), in units of 1/√L.
  - Correlations at lags 1–3, in units of 1/√L.
- **S2, drift.** D = the mean of S(N)/√N at 4000 log-spaced N in [10³, 10⁷]. The tower from its origin predicts
  1/ζ(½) = −0.685.
- **S3, tones.** The correlation between S(N)/√N (minus its mean) and the tower's predicted wiggle pattern from 200
  zeros, at 2000 log-spaced N in [10⁴, 10⁷]. The tower from its origin gives 0.995.

## Decision

A sequence carries the tower's from-origin fingerprints if D is within 0.3 of −0.685 and S3 > 0.5.

## Predictions, made now

- **Tower from its origin.** It carries the fingerprints (already seen in round 8).
- **QRNG and pseudo-random.** No fingerprints. D is roughly N(0, 0.5²) across chunks, S3 roughly 0 ± 0.2, and S1
  passes.
- **Tower, late.** No fingerprints either, and indistinguishable from the QRNG on S1–S3. At N₀ ≥ 10¹² the drift changes
  by less than 10⁻⁶ per step, and the tones, which move with log N, are frozen.

If all three predictions hold, randomness tests at our epoch cannot tell the tower's hidden variables from true
randomness.
