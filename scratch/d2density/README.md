# d₂ < d₁ density: Lean files (not wired into the lakefile)

Check each file with `lake env lean scratch/d2density/<file>.lean`. Each one ends with `#print axioms`. None uses `sorry`,
and every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. See `docs/d2-density.md` for the mathematics.

| file | main results |
|---|---|
| `D2Criterion.lean` | `criterion` (d₂ ≥ d₁ ⇔ −2K₁−2c ≤ ℓ ≤ −2c), `c0_closed`, `c1_closed` |
| `D2Density.lean` | `re_inv_pos`, `K1_pos`, `density_of_dist`, `d2_density`, `L0_finite`, `d2_density_log` |

The Granville–Soundararajan part (Pólya–Vinogradov, Lemma 4.1 for all non-square `n` with the Kronecker symbol, the unconditional moments, and the densities `δ±(r) = (3/π²)∏_{p∣r} p/(p+1)` with `ν(1) = 4/π²`) is now in the library: `lib/pnt/D2GS.lean`, printed in `lib/check/CheckAll.lean`, documented in `formalisations/d2-density.md`. It is unconditional.

Remaining hypotheses of `d2_density_log`: `hdist`, `hB` and `hpos` (table in `docs/d2-density.md`).
