# d₂ < d₁ density: Lean files (not wired into the lakefile)

Check each file with `lake env lean scratch/d2density/<file>.lean`. Each one ends with `#print axioms`. None uses `sorry`,
and every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. See `docs/d2-density.md` for the mathematics.

| file | main results |
|---|---|
| `D2Criterion.lean` | `criterion` (d₂ ≥ d₁ ⇔ −2K₁−2c ≤ ℓ ≤ −2c), `c0_closed`, `c1_closed` |

The Granville–Soundararajan part (Pólya–Vinogradov, Lemma 4.1 for all non-square `n` with the Kronecker symbol, the unconditional moments, and the densities `δ±(r) = (3/π²)∏_{p∣r} p/(p+1)` with `ν(1) = 4/π²`) is now in the library: `lib/pnt/D2GS.lean`, printed in `lib/check/CheckAll.lean`, documented in `formalisations/d2-density.md`. It is unconditional.

`D2Density.lean` (`re_inv_pos`, `K1_pos`, `density_of_dist`, `d2_density`, `L0_finite`, `d2_density_log`) moved to `lib/pnt/D2Density.lean`. Its `hdist` is discharged, CONDITIONAL on the half-plane, in `lib/pnt/D2Hdist.lean` (`D2Hdist.d2_density_pos`, `D2Hdist.d2_density_neg`). `hK1`, `hpos` and `hB` are discharged in `lib/pnt/D2Good.lean`. So `D2Good.d2_density_pos_closed` and `D2Good.d2_density_neg_closed` have no hypotheses, and are conditional only on the half-plane (table in `docs/d2-density.md`).
