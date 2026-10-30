# The Linnik paper's certificate tools

These scripts compute the sieve route's certificate outside Lean and generate the Lean files that the kernel checks.
They need Python 3 only.

| File | What it does |
|---|---|
| `route_limits.py` | Computes, for a density curve, an exponent `L` and a grid size `n`: the Halász–Montgomery window, its corners in exact rationals, and the depth-4 certificate's total (`replay`: the first certificate, before its two deeper levels, its kept parts and its sharper cell bounds, kept as a cross-check of the window and the grid's conditions). It reads the curves from `lib/pnt`. Its docstring lists its commands. |
| `route_limits.jsonl` | The rows `route_limits.py run` recorded: a curve, `L`, `n`, the window, the corners and the total. |
| `refine_k2_probe.py` | Replays the depth-4 refined certificate (before the deeper levels) on the same grids (`replay2`); the refined certificate's `total2` is `mirror2.py`'s. |
| `mirror2.py` | Evaluates `total` and `total2` of the refined certificate of `SieveCertDefs.lean` and `SieveCert2Defs.lean`, the earlier theorem's at `278/125` (depths up to 6, with the coarse grid of `n/4` cells of four for `p₅` and `p₆`, the kept parts, Buchstab's `ω` on `[2, 3]` with its table `lnT`, and the cells' trapezoid and exact prime sums) cell by cell in exact integers, in parallel, and writes each cell's cost and kernel work to JSON. It prints the totals and the boxes tested at depths three to six below the decomposed cells. With `--depth4` no cell of depth four is decomposed: the decomposition stopped at depth four, whose `total` on the paper's grid is the paper's `1.45721𝒦`. With `--ib a/b` it is the certificate under the bilinear Type I rule of `SieveRuleDefs.lean` at `L = a/b` (`ibRule`, `total2R`), and each cell also records the rule's `ibOK` tests. The kernel is the check of the Lean; this is the cut's source. |
| `mirror8.py` | Evaluates `totalD` of `SieveDeepDefs.lean`, the certificate of the decomposition to depth 8 under the bilinear Type I rule (the cells of depth 4 dropped or decomposed over the coarse cells of `p₅` and `p₆`, those of depth 6 dropped or decomposed over `p₇` and `p₈`, the masks of the surely evaluable boxes, the block test `okD` and the memoised bounds by index sums), cell by cell in exact integers, in parallel, and writes each candidate cell's cost and the kernel work it makes (the boxes `ok3D` tests, the counted cells of depths 3 and 4, those of depth 4 in the pure and the masked modes, the terms of depths 5 and 6). About a minute on four cores at `n = 272`. |
| `gen_cert8.py` | Cuts `mirror8.py`'s certificate into parts by the kernel's predicted time (a least-squares fit of the kernel's time on the cells' work, at most 30 seconds a part) and writes `SieveGrid22000E.lean`, `SieveCert22000EP<k>.lean` (114 files of at most 10 parts) and `SieveCert22000E.lean` (`totalD < K`). |
| `gen_cgl_curve.py` | Writes `LinnikCGLSteps.lean` (Chen–Gupta–Li's Proposition 3.1 on 30 steps of `[5/7, 131/168]`, fourteen of width `1/1680` and then sixteen of `1/280`, with `ParC` parameters computed here and every field of `ParC.Good` checked in exact rationals, and Ingham's last step at `ε = 1/400000`), `SieveCurve7D.lean` (the curve `g7d`, `g7d_le_one`, `g7d_half`, `g7d_le_lin` and its counts; the window and Type II estimate at `L = 278/125` are in the git history), and, for the decomposition to depth 8, `SieveTypeIIU22000D.lean` (the window and Type II estimate of `g7d` at `L = 11/5`) and `Linnik22000E.lean` (the theorem at `L = 11/5`, with no hypothesis). `--check` compares them with `lib/pnt`; `--table` prints the steps. |
| `density_payoff.py` | What a lower density curve would buy: for hypothetical curves made from `g7d` (a cap on its exponent, Chen–Gupta–Li's bound without the term behind its `7/3`, Heath-Brown's exponent `2` from `15/19`, with or without Ingham's estimate below `4/7`; and `classical`, without Chen–Gupta–Li, with Ingham's and Huxley's exponents in steps of `1/1680` on `[5/7, 131/168]`, which starts from `23/10` and gave the earlier version's `2.2685`), the window, `mirror2.py`'s `total2` at `n = 340`, and the lowest `L` passed with `total2 < 0.999K`. For each curve it computes a window admissible at `L` (the sampled scan, then the exact corners in rationals, moving an end inward by `10⁻⁵` while a corner fails), evaluates `total2` on it in exact integers, starts from `278/125` (which must pass), lowers `L` by `1/1000` while the total stays below `0.999K`, then tests once the value `1/2000` below the last one passed, and reports the lowest `L` passed. Computations, not theorems; all variants take about an hour. With `--deep` it replays the certificate at `11/5` instead, `mirror8.py`'s `totalD` at `n = 272` under the bilinear rule at `L`, on grids that satisfy the Lean's conditions (a narrow window fails `4H + 4HC ≤ V`), starting from `11/5`, and from `56/25` for `classical`, which gives the paper's `2239/1000` (its Section 8 and its supplement's §S6); a few minutes for each `L`. |
| `choices.py` | The certificate's choices at depths two and four, from `mirror2.py`'s definitions: the candidate cells and the ones the sharp rule allows, whether each would be cheaper decomposed (so that the sharp rule makes every choice), the counted cells of depth four below the decomposed ones, the ones decomposed and what the others would save decomposed, and the cost of the dropped cells that reach the line `α₁ + α₂ = 1 − U₁/D`. The figures of the earlier version of the paper, at `278/125`; about a minute. |
| `fig_cells.py` | Draws the paper's Figure 1, the cells of depth two of the certificate at `11/5` by kind (decomposed by the split at `X′`, decomposed whole by the bilinear test, dropped, evaluated, corner, the window's strip), as a TikZ picture in `papers/linnik-exponent/fig-cells.tex`, from `mirror8.py`'s definitions, and prints the counts and costs of the three kinds of candidate cell, their total, and the dropped cells' cost on either side of the line `α₁ + α₂ = 1 − U₁/D`; about two minutes on four cores. |
| `check_certificate.py` | Runs `mirror8.py` and `gen_cert8.py` in a temporary directory, for the certificate (`22000E`), and compares the generated files with `lib/pnt` byte for byte. |

To check that the committed certificate is the one these scripts generate:

```sh
python3 tools/linnik/check_certificate.py           # `22000E`, about a minute and a half
```

It prints the totals, the cross-checks, the number of parts and the comparison, and ends with
`CERTIFICATE <tag> PASS` when all its files are identical:

| Tag | `L` | Window | Curve | `totalD/K` | Parts | Files |
|---|---|---|---|---|---|---|
| `22000E` | `11/5` | `[43457, 46959]/100000` | `g7d` | `0.9321382` | 1136 | 114 part files + grid + assembly |

`gen_cgl_curve.py --check` regenerates the four files of the curve, its windows and the theorem (about a minute, for the windows' scans).

The kernel's check of the certificate is the build itself: each part file proves its parts by `decide +kernel`, and
`SieveCert22000E.lean` assembles them into `SieveDeep.totalD_lt_22000E`. The kernel's check of the 114 part files took
6.2 hours of one core in all (`gen_cert8.py` predicts 8.2), 1.6 hours on four cores, with at most 2.8 GB for any one
file.

The curve `g7d` (`SieveCurve7D.g7d`) is the paper's: the steps of `LinnikCGLSteps.lean` on
`[5/7, 131/168]` in place of the plateau `7/3 + 1/2000` on `[5/7, 16/21]` and its first five Huxley steps, and Ingham's
last step at `ε = 1/400000` in the Lean lemma's convention (its exponent is `2 + 4c + 4ε`, so the slack is
`4ε = 1/100000` in place of `1/2000`). `route_limits.jsonl` has its row at `278/125` (`g7d`, `n = 340`, window
`[41556, 47531]`; its total is the first, depth-4 certificate's, `1.49216K`). Between `11161/5000` and `89/40` the curve
took Huxley's bound on the three steps of `[1307/1680, 131/168]` (`LinnikHuxJunction.lean`, in the git history): at
`11161/5000` the window's lower end was set near `7/9`. From `89/40` on both ends are set on the first Chen–Gupta–Li step
and those steps do not change the window, so they are Chen–Gupta–Li's again. The first fourteen steps are of width
`1/1680`; from `5/7 + 14/1680` on, steps of `1/280` leave the window as it is (the least slack of their corners is
`4.4·10⁻⁵` at `278/125` and `6.8·10⁻⁴` at `11/5`), and at `278/125` the curve has thirty Chen–Gupta–Li steps in place of the earlier `110` of `1/1680`.

The theorem at `278/125` (`Linnik22240R`, in the git history with its certificate `22240R`) used the refined
certificate of `SieveCert2Defs.lean` at `n = 340`: the two deeper levels of the Buchstab decomposition, the coarse grid
of `85` cells of four, the kept parts, and the cells' bounds (Buchstab's `ω` itself on `[2, 3]`, `omKw`, with the table
`lnT` of `log((16 + k)/16)` and `log y ≤ (y − 1/y)/2`; `0.565073` above `3`; the trapezoid bound of each cell's
`Σ 1/p` and the exact `log x · Σ 1/(p log p)` of the last cell; and the bound `2h/(2e + h)` from below for the kept
parts) brought its `total2/K` to `0.99754`. The theorem at `11/5` (`Linnik22000E`) replaced it: its certificate
(`SieveDeepDefs.lean`) adds the bilinear Type I rule and two more levels of the decomposition, and totals `0.9321382K`
at `n = 272`, without the kept parts. Both theorems have no hypothesis.
