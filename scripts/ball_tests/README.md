# Numerical and certified tests of the orbit-lattice conjecture

Companion scripts for `docs/ball-conjecture-tests.md`. Needs `numpy scipy mpmath python-flint matplotlib`. CI does not run them.

| dir | contents |
|---|---|
| `function_field/` | curve analogue (`ffcore.py` kernel and Gram matrix, `curves.py` point counting, `run.py`); `zeta_mp.py` is the dps-40 rerun of `ball_orbit.py` |
| `dirichlet/` | Dirichlet analogue: closed form (`dcore.py`), zero-sum validation, pivots for q ≤ 47 |
| `hunt/` | exact k=2 criterion (`k2.py`, arb), character scans, zero-sum verification, an arb cross-check of the zeta pivots for k ≤ 500 (`cert_zeta.py`; `scripts/ball_certificate.py` proves k ≤ 10⁴); `kmin.py`: pivots certified to k = 8 and computed to k = 300 for every character, to find where min d_k/d_1 sits (`kmin_all400.txt`, `kmin_real10000.txt`) |
| `horizon/` | λ_min of G_N and of the normalised and flat-model pencils; arb inertia certificates |
| `spread/` | dyadic weight distribution of bottom eigenvectors (`spread.py 6000` regenerates `spread_6000.json`, 4 MB, not committed) |
| `algebraic/` | notes (`notes.md`, `eigvec.md`, `lower.md`) and checks |
| `shortest/` | the shortest-vector form (B) on the analogues (`shortest.py`, output `out.txt`; its `res.json`, every curve's row and the characters that fail or nearly fail, is not committed): curves, both orbits, with exact rational rechecks and the integral null vector of Theorem C′; every primitive character mod q ≤ 400 and every real one mod q ≤ 10⁴, with failures certified in arb |
| `prior_art/` | checks behind `reports/Orbit lattice criterion prior art.md`: the pivots of Lagarias's Li-basis Gram matrix (`li_orbit.py`) and Yoshida's formulas (5.15) and (6.7) (`yoshida_*.py`) |

Data files that some scripts read and others write (not committed):
- `horizon/zeta_eigs.json`: written by `horizon/horizon.py`, read by `horizon/analyse.py` and `horizon/plot.py`.
  `horizon/cert_inertia.py` does not need it: it computes its float64 estimates itself.
- `hunt/kmin_<mode>_<Q0>_<Q1>_N<N>.json`: every character's row, written by `hunt/kmin.py` (12 MB for q ≤ 400).
- `spread/curve.json` and `spread/spread_6000.json`: written by `spread/curve.py` and `spread/spread.py 6000`, read by
  `spread/plot.py`.

Run each script from its own directory.
