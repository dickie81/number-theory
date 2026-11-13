# Pre-registration, round 11: can a hyperplane's geometry explain DESI?

Written 2026-11-06, before computing.

## The no-go, by argument

Through the observer's window the tower's geometry is the same at every epoch (round 10: the shape is frozen, the
shear falls like 1/N).

In any FRW reading, an expansion history that looks the same from every epoch has `H(a_e)/H(a_o) = f(a_o/a_e)`. That
forces `f(xy) = f(x)·f(y)`, so `H ∝ a^{−k}`, a power law.

Round 1 already measured power laws against DESI DR2 BAO: the best, p = 0.91, gives χ² = 97.0 against ΛCDM's 10.3.

## Q14. The physics version: DGP braneworld self-acceleration

Our 3D world is a brane in a higher-dimensional bulk, and gravity leaks off it beyond a crossover distance `r_c`.

- **Flat, self-accelerating branch:** `E(z) = √Ω_rc + √(Ω_rc + Ω_m(1+z)³)`, with `Ω_rc = ((1 − Ω_m)/2)²`.
- **Parameters:** one, Ω_m, the same count as flat ΛCDM.
- **Data:** DESI DR2 BAO, 13 points, full covariance, `H₀r_d` free.
- **Pass:** Δχ² against ΛCDM < 9.

Either way, `r_c ≈ 1/H₀` must be put in by hand: a second scale.
