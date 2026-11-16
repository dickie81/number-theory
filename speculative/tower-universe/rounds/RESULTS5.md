# Results of round 5 (PREREG5.md): the 3D slice, and the outer product

Raw output: `slice5.out` (from `slice5.py`) and `outer7.out` (from `outer7.py`). Rounds 1–4 all used the full
hyperspace, with every zero.

## Q6: room in 3D

`det[p₁, p₂, p₃] = −0.0005 ≠ 0`. The first three integers already span the slice, so every later integer arrives at
angle 0 there.

In the full space every integer brings a new dimension for ever: that is positive definiteness, so RH.

## Q5: dimensions needed to see the primes

AUC for picking out the prime powers in `[2, M]` from an observer who sees the first K zeros (`2K` real dimensions).
0.5 means blind; 1 means perfect.

| K | dims | height | M = 30 | M = 100 | M = 1000 |
|---|---|---|---|---|---|
| 1 | 2 | 14.1 | 0.630 | 0.611 | 0.530 |
| 2 | 4 | 21.0 | 0.702 | 0.631 | 0.540 |
| 3 | 6 | 25.0 | 0.721 | 0.641 | 0.551 |
| 5 | 10 | 32.9 | 0.774 | 0.680 | 0.566 |
| 10 | 20 | 49.8 | 0.851 | 0.753 | 0.594 |
| 20 | 40 | 77.1 | 0.918 | 0.833 | 0.627 |
| 50 | 100 | 143.1 | 1.000 | 0.921 | 0.685 |
| 100 | 200 | 236.5 | 1.000 | 0.968 | 0.741 |
| 300 | 600 | 541.8 | 1.000 | 1.000 | 0.864 |
| 1000 | 2000 | 1419.4 | 1.000 | 1.000 | 0.978 |
| 2999 | 5998 | 3532.0 | 1.000 | 1.000 | 0.999 |

- The drawn slice lies between K = 1 and K = 2. Up to 1000 it is nearly blind (0.53–0.54).
- Seeing the primes up to P takes about `2P log P` dimensions: zeros up to height about `2πP`.

## Q7: the outer product `Σ_{n≤N} w_n w_n^†`

| N | Top-3 share | e^S | Participation ratio | Smallest / largest eigenvalue |
|---|---|---|---|---|
| 64 | 0.314 | 32.3 | 19.6 | 2.6·10⁻⁴ |
| 256 | 0.303 | 58.0 | 22.4 | 5.5·10⁻⁶ |
| 1024 | 0.302 | 73.9 | 22.7 | 1.1·10⁻⁷ |
| 4096 | 0.302 | 80.5 | 22.7 | 1.9·10⁻⁹ |
| limit, from 3000 zeros | 0.307 | 72.0 | 22.1 | – |

- **The bulk freezes.** About 30% of the trace sits in the top 3 axes, and the participation ratio stays near 22.
  `e^S` still creeps up because of the long tail of small eigenvalues (the limit row truncates that tail at 3000
  zeros).
- **The thinnest axis shrinks.** `λ_N/λ_max ∝ log N/N³`. This is where the primes tick: `λ_N` is the smallest nonzero
  eigenvalue of this operator.
