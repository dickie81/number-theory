# Results of round 4 (PREREG4.md)

Raw output: `quantum.out` (from `quantum.py`; 3000 zeros computed with mpmath in 869 s).

| Test | Verdict |
|---|---|
| Q1, primes arrive orthogonal | not confirmed |
| Q2, primes turn the thinnest axis a quarter turn | not confirmed |
| Q3, wave–particle duality | passes both ways |
| Q4, quantum class | GUE |

## Q1: the arrival angle of each new integer (`n ≤ 4096`)

**First arrivals:**

| n | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| angle | 68.0° | 62.8° | 64.0° | 60.2° | 55.2° | 60.3° | 58.8° | 57.2° | 52.8° | 62.2° | 51.0° | 59.4° |

**Medians by range** (maximum in brackets):

| Range of n | Primes | Prime powers | Composites |
|---|---|---|---|
| [2, 64) | 56.2° (68.0°) | 53.5° (64.0°) | 45.1° (55.2°) |
| [64, 512) | 28.7° (45.1°) | 32.3° (42.7°) | 27.0° (42.1°) |
| [512, 4096) | 13.1° (22.9°) | 14.3° (22.6°) | 12.8° (22.9°) |

Arrivals at 45° or more: every n up to 29, then a few up to 67 (the last), primes and composites alike.

Not confirmed. Primes arrive somewhat steeper early on, but nothing arrives at 90°. Angles shrink for every kind of
integer.

## Q2: how far the thinnest axis turns (`N ≤ 600`)

| Range of N | Primes | Prime powers | Composites |
|---|---|---|---|
| [3, 50] | 2.70° | 2.23° | 1.40° |
| [50, 600] | 0.23° | 0.20° | 0.12° |

- The largest turn is 23.4°, at `N = 2`.
- No turn reaches 45°. There are no near-crossings: `λ₂/λ₁ ≥ 3.10`.

Not confirmed. Primes turn the axis about twice as far as composites, but never by a quarter turn.

## Q3: wave–particle duality, each side rebuilt from the other

**Primes → zeros.** Fourier peaks of `K(e^u)`, computed from the primes alone with `u ≤ log 2²²`:

| | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| Peak | 14.134 | 21.022 | 25.010 | 30.424 | 32.934 | 37.586 | 40.918 | 43.326 |
| True zero | 14.135 | 21.022 | 25.011 | 30.425 | 32.935 | 37.586 | 40.919 | 43.327 |

Each peak is within the grid step (0.002). The weakest peak at a zero is 13× stronger than any other peak. Passes.

**Zeros → primes.** Peaks of `−Σ cos(γ_k u)` (Fejér-tapered):

| Zeros used | Prime powers ≤ 30 found | Weakest of them | Strongest other peak |
|---|---|---|---|
| 100 | 16/16 | 1.5 (at 16) | −0.1 |
| 3000 | 16/16 | 46.7 (at 16) | 5.4, at x = 30.92 (the prime 31 at the range edge) |

Passes.

## Q4: nearest-neighbour spacings, 2999 of them

| | Share below 0.25 | KS distance |
|---|---|---|
| Zeros | 0.0070 | – |
| GUE (no time reversal) | 0.0161 | 0.035 |
| GOE (time reversal) | 0.0479 | 0.102 |
| Poisson (uncorrelated) | 0.2212 | 0.313 |

The class is GUE. The low zeros repel slightly more than the GUE surmise predicts, a finite-height effect.
