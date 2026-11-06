# Results of round 10 (PREREG10.md): universe scale through the observer's own 3D window

Raw output: `window10.out` (from `window10.py`).

## Q12: isotropy in the co-rotating window (N from 2¹² to 2²¹)

- **Shape.** Frozen. The axis ratios are `1 : 0.9470–0.9471 : 0.6171–0.6172`.
- **Rates.** The mean `H·t` is 0.5000, and each axis's own rate is within `2·10⁻⁴` of ½.
- **Shear and turning,** by range of N:

  | N | Max shear σ/H | Max turning (rad per unit log N) |
  |---|---|---|
  | [2¹², 2¹⁵) | 1.2·10⁻⁴ | 2.6·10⁻³ |
  | [2¹⁵, 2¹⁸) | 1.4·10⁻⁵ | 2.7·10⁻⁴ |
  | [2¹⁸, 2²¹) | 1.8·10⁻⁶ | 3.4·10⁻⁵ |

- **Extrapolation.** The shear falls like `N^{−1.00}`, so at `N ≈ 8·10⁶⁰` it is about `7·10⁻⁶²`. That is far below the
  CMB bound of `4.7·10⁻¹¹`. **Pass.**

Round 2's failure (shear 0.77, turning 14.1 rad per unit log N) came from fixed outside axes.

## Q13: the window's share of the tower (not blind)

| N | Top-3 share | Axes |
|---|---|---|
| 1024 | 0.3024 | 0.1274, 0.1117, 0.0633 |
| 2048 | 0.3024 | 0.1273, 0.1117, 0.0633 |
| 4096 | 0.3023 | 0.1273, 0.1117, 0.0633 |

Against today's matter fraction Ω_m:

| Measurement | Ω_m | Distance |
|---|---|---|
| DESI DR2 + CMB | 0.3027 ± 0.0036 | 0.1σ |
| DESI BAO alone | 0.2975 ± 0.0086 | 0.6σ |
| Planck 2018 | 0.3153 ± 0.0073 | 1.8σ |

**Why it doesn't count.** The share is frozen at every epoch. A frozen matter share means Einstein–de Sitter expansion,
which round 1 excluded: DESI DR2 χ² = 1420, 37σ. In our universe the matter share was about 0.78 at z = 1. At the CMB
it was 0.76, with radiation at 0.24 and Λ at 10⁻⁹. So this is a present-day look-alike.

(Corrected after the round: the first version said "about 0.75 at z = 1 and over 0.99 at the CMB", which left out
radiation.)

## Overall

At universe scale, isotropy now passes and H₀t₀ = 1 (from inside) passes. The shape of the expansion history still
fails in every reading, because the tower is self-similar and has no special epoch.
