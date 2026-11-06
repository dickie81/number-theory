# Results of round 2 (PREREG2.md)

Raw output: `round2.out` (from `round2.py`). **Verdict: no fit.** Seven readings have now been tried and none passes.

## S1: the tower's size as the scale factor

`‖w_N‖ = √(N·H₀)` exactly, because `|n^ρ| = √n` on the critical line. So `a ∝ t^{1/2}` at every `N`, which is the
radiation-era law with no parameters.

| Test | Prediction | Measured | Result |
|---|---|---|---|
| T1 | `H₀t₀ = 0.500` | `0.950 ± 0.008` | 56σ off |
| T2, DESI DR2 BAO | χ² = 5436 for 12 dof | flat ΛCDM: χ² = 10.3 for 11 dof | excluded |

## S2: the drawn slice as our space (moment tensor, `N = 4096` to `2²¹`)

**Shape.** The axes are in ratio `1 : 0.91–0.96 : 0.57–0.62`.

**Rotation.** The long axis turns 14.14 rad per unit `log N` (`γ₁ = 14.13`). That is once per `×1.249` in `N`, or 28 rad
per e-fold of expansion.

**Each axis's own expansion rate `H_i·t`.** The mean over the three axes is 0.50. Individually:

| Axis | `H_i·t` range |
|---|---|
| long | −0.02 to +1.18 |
| middle | −0.04 to +1.26 |
| short | −0.50 to +1.57 (it contracts at times) |

**Shear.** σ/H has median 0.77 and maximum 3.6. The CMB limit is `< 1.0·10⁻⁶` (tensor mode) and `< 4.7·10⁻¹¹` (vector
mode; Saadeh et al., PRL 117, 131302, 2016). So the slice is off by at least `10⁶`.

This doesn't depend on the slice chosen. The latest integers dominate the cloud, and they all point along the spiral's
current direction. A zero at height γ gives a wobble of size `~1/γ` at speed `~γ`, so the shear is of order the
expansion rate in any slice.

## A1: is either half of the adelic split a geometry?

`kos(1) = H₀` has no prime in it (`A(1) = ψ(1) = 0`), so every length comes from the real place.

| Part kept | Result |
|---|---|
| Finite places alone | No lengths: every diagonal entry is 0. Not a geometry at `N = 1`. |
| Real place alone | Not positive definite at `N = 3`. |
| All places | Positive definite to `N = 4096` (and to 32768, as computed before). |

Neither half is a space, so "our world = the real place" has nothing to fit.

## A2: every place is load-bearing

**Keep only the places `p ≤ P`.** The tower fails one or two integers after the first missing prime `q` arrives:

| P | 2 | 3 | 5 | 7 | 11 | 13 | 23 | 47 | 59 | 89 | 97 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| first missing q | 3 | 5 | 7 | 11 | 13 | 17 | 29 | 53 | 61 | 97 | 101 |
| fails at N | 4 | 6 | 8 | 12 | 14 | 18 | 30 | 54 | 63 | 99 | 103 |

**Drop a single place `p`.** It fails at:

| p | 2–31 | 101 | 307 | 1009 |
|---|---|---|---|---|
| fails at N | p + 1 | 103 | 311 | 1017 |

So positivity at level `N` needs every place up to `N`, each almost as soon as its prime arrives. The slack is 1, 2, 4
and 8 integers for p = 31, 101, 307 and 1009.
