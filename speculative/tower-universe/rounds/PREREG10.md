# Pre-registration, round 10: universe scale, seen through the observer's own 3D window

Written 2026-11-06, before the round-10 numbers were computed.

**The window.** An observer made of the fabric builds its axes from the tower's current vectors. Those turn with the
spiral, in each zero's plane at that zero's rate. So the observer's 3D window is not fixed in the hyperspace: it
co-rotates with the spiral.

The natural version is the outer product's top three axes. Since `S_N = U(N)·C₀·U(N)†` with
`U(N) = diag(N^{iγ})`, these turn at exactly the zeros' rates. The drawn slice made to co-rotate is the simplest
example: plane 1 plus the unit vector at angle `γ₂ log N` in plane 2.

## Q12. Isotropy in the co-rotating window

- **Measure,** for N from 2¹² to 2²¹: the window's moment tensor, its axis ratios, each axis's own rate `H_i·t`, the
  shear `σ/H`, and how far its principal axes turn.
- **Prediction.** The shape is frozen up to O(1/N), because the past seen from N depends only on n/N. So the shear
  goes to 0 like 1/N, and the turning vanishes.
- **Pass:** `σ/H` extrapolated to `N ≈ 10⁶⁰` is below the CMB bound of `4.7·10⁻¹¹`.

Round 2's failure (`σ/H ≈ 0.8`) then came from using fixed outside axes.

## Q13. How much of the tower the window holds

- **Measure** the top-3 share of the outer product at N = 1024, 2048 and 4096, to 4 decimals.
- **Disclosure: this comparison is not blind.** Round 5 already gave 0.302, and I knew `Ω_m ≈ 0.30` (DESI + CMB:
  `0.3027 ± 0.0036`).
- **The decisive check uses round 1.** The share is frozen at every epoch. If the window holds matter, which dilutes as
  `a⁻³`, a frozen matter share makes the total dilute as `a⁻³` too, which is Einstein–de Sitter expansion. DESI DR2
  gave that χ² = 1420, a 37σ exclusion.
