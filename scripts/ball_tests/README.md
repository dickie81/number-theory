# Numerical and certified tests of the orbit-lattice conjecture

Companion scripts for `docs/ball-conjecture-tests.md`. Needs `numpy scipy mpmath python-flint matplotlib`. CI does not run them.

| dir | contents |
|---|---|
| `function_field/` | curve analogue (`ffcore.py` kernel and Gram matrix, `curves.py` point counting, `run.py`); `zeta_mp.py` is the dps-40 rerun of `ball_orbit.py` |
| `dirichlet/` | Dirichlet analogue: closed form (`dcore.py`), zero-sum validation, pivots for q ≤ 47 |
| `hunt/` | exact k=2 criterion (`k2.py`, arb), character scans, zero-sum verification, an arb cross-check of the zeta pivots for k ≤ 500 (`cert_zeta.py`; `scripts/ball_certificate.py` proves k ≤ 10⁴) |
| `horizon/` | λ_min of G_N and of the normalised and flat-model pencils; arb inertia certificates |
| `spread/` | dyadic weight distribution of bottom eigenvectors (`spread.py 6000` regenerates `spread_6000.json`, 4 MB, not committed) |
| `algebraic/` | notes (`notes.md`, `eigvec.md`, `lower.md`) and checks |

Data files that some scripts read and others write (not committed):
- `horizon/zeta_eigs.json`: written by `horizon/horizon.py`, read by `horizon/analyse.py` and `horizon/plot.py`.
  `horizon/cert_inertia.py` does not need it: it computes its float64 estimates itself.
- `spread/curve.json` and `spread/spread_6000.json`: written by `spread/curve.py` and `spread/spread.py 6000`, read by
  `spread/plot.py`.

Run each script from its own directory.
