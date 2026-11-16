# Results of round 7 (PREREG7.md): an observer made of the tower

Raw output: `clicks.out` (from `clicks.py`), for N ≤ 3000.

**Verdict: confirmed.** An embedded observer registers clicks exactly at the predicted times and strengths. A 3D
observer is nearly blind to them.

## The click rule

`D(N) = click − 1/N + residual`. The residual is checked for N ≥ 100; below that the −1/N background is only a rough
approximation.

| Past integer n | Clicks predicted | Max residual (N ≥ 100) | Faintest click there | AUC, embedded | AUC, 3D |
|---|---|---|---|---|---|
| 1 | 465 | 1.6·10⁻⁷ | 3.4·10⁻⁴ | 1.000 | 0.566 |
| 6 | 114 | 2.0·10⁻⁶ | 2.7·10⁻³ | 0.999 | 0.594 |

So a click of strength `log p/p^k` occurs exactly when `N = n·p^k`.

At each tick N, the embedded observer registers one click per prime-power divisor of N, against the past integer
`N/p^k`. The clicks spell out N's factorisation.

## Total click strength per tick

`Σ_{p^k | N} log p/p^k`:

| | Median | Example |
|---|---|---|
| Primes | 0.0054 | N = 2999: 0.0027, one faint click, against n = 1 |
| Composites | 0.636 | N = 2520 = 2³·3²·5·7: 1.69 |

A prime is the quietest tick. No past integer clicks with it except 1.
