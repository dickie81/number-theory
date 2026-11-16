# Results of round 8 (PREREG8.md): randomness as hidden variables

Raw output: `liouville.out` (from `liouville.py`).

## Q10: the click-parity coin, `λ(N) = (−1)^Ω(N)`, for N ≤ 10⁷

| | Click parity | Seeded random coin |
|---|---|---|
| 3-step pattern frequencies | 0.1249–0.1251 | 0.1249–0.1251 |
| Correlations at lags 1, 2, 3 | −2.0e−4, +1.2e−4, −3.2e−4 | −1.2e−4, −6.1e−5, −2.4e−4 |
| Running sum / √N, range over 10³–10⁷ | −1.32 to −0.05 | −2.70 to +1.90 |

The noise level for the correlations is about 3·10⁻⁴.

- **Locally it is indistinguishable from a fair coin.**
- **Globally it differs.** Its running sum has a fixed drift: mean −0.682, against the predicted
  `1/ζ(½) = −0.685` from the perfect squares. And it wanders much less than chance does.
- **It cancels like a fair coin up to √N.** RH holds exactly when `L(N) = O(N^{1/2+ε})`, the same RH that holds when
  the tower is positive definite for every N.

## Q11: the hidden zeros predict the coin's wiggles

The wiggles are `r(N) = L(N)/√N − 1/ζ(½)`, at 2000 log-spaced N in [10⁴, 10⁷]. Their rms is 0.268.

| Zeros used | Correlation with the prediction | rms left over |
|---|---|---|
| 10 | 0.961 | 0.074 |
| 50 | 0.985 | 0.046 |
| 200 | 0.995 | 0.028 |

200 zeros explain 99% of the wiggles' variance.
