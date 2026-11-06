# Pre-registration, round 2: the 3D slice over time, and the adelic split

Written 2026-11-06 after round 1 failed (`RESULTS.md`) and before any round-2 number was computed. Round 2 adds three
readings to round 1's four. A pass must survive a Bonferroni factor of 7.

## The 3D slice

This is the slice drawn on the page. Its axes are the real and imaginary axes of the first zero's plane and one real
axis of the second zero's plane. In the true geometry it is not the page's log-radius display:

`p_n = √(2n)·(cos(γ₁ log n)/|ρ₁|, sin(γ₁ log n)/|ρ₁|, cos(γ₂ log n)/|ρ₂|)`.

Its shape at time `N` is the moment tensor `M(N) = Σ_{n≤N} p_n p_nᵀ`. Its axis scale factors are
`a_i = √(eig_i(M)/N)`, on the integer clock `t = N·t_P`.

- **S1.** The scale factor is the tower's size, `a(t) ∝ ‖w_N‖` (in the full space, and in the slice's mean).
  - T1: `H₀t₀` against `0.950 ± 0.008`.
  - T2: DESI DR2 BAO with no free shape parameter (only `H₀r_d` free). Pass as in round 1.
- **S2.** The slice is our space: is it isotropic?
  - Report the axis ratios, how far the principal axes turn, and the swing of each axis's own rate `H_i·t`.
  - Measured: shear `(σ/H)₀ < 4.7·10⁻¹¹` (95%; Saadeh et al. 2016, CMB). Pass: shear within that bound.

## The adelic split

`kos(x) = [A(x) − ψ(x)/x] + [−log x + 1 + γ − log(2π)/x + tail(1/x)]`. The first bracket is the finite places, one
step at each prime power `≤ x`. The second is the real place with the pole. At time `N` the places `p ≤ N` have joined.

- **A1.** Is either bracket alone a geometry (a positive definite Gram matrix)? If one is, it gets T1/T2 like S1.
- **A2.** Is every place load-bearing? Drop the place `p` (all its powers) and find the `N` at which the Gram matrix
  stops being positive definite. Do the same with only the real place. This is description, not a fit.
