# Pre-registration, round 8: randomness as hidden variables

Written 2026-11-06, before computing.

The parity of the click count at tick N is Liouville's λ(N) = (−1)^Ω(N). Its running sum is L(N) = Σ_{n≤N} λ(n). RH holds
exactly when L(N) = O(N^{1/2+ε}).

## Q10. Does the deterministic coin look fair? (N ≤ 10⁷)

- **Drift.** The perfect squares give L(N)/√N an average of exactly 1/ζ(½) = −0.685. Predict that mean, with the
  ratio staying O(1).
- **Local randomness.** Correlations at lags 1–3, and the frequencies of the 8 three-step patterns, should lie within
  about 3/√N of a fair coin's. Compare with a seeded random coin of the same length.

## Q11. Do the hidden variables predict its noise?

- **Wiggles.** r(N) = L(N)/√N − 1/ζ(½), at 2000 log-spaced N in [10⁴, 10⁷].
- **Prediction from the first K zeros.** 2·Re Σ_{k≤K} ζ(2ρ_k)·N^{iγ_k}/(ρ_k·ζ′(ρ_k)), the explicit formula for
  L(N), truncated.
- **Report** the correlation between r and the prediction, for K = 10, 50 and 200.
