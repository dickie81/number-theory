# The Linnik paper's certificate tools

These scripts compute the sieve route's certificate outside Lean and generate the Lean files that the kernel checks.
They need Python 3 only.

| File | What it does |
|---|---|
| `route_limits.py` | Computes, for a density curve, an exponent `L` and a grid size `n`: the Halász–Montgomery window, its corners in exact rationals, and the depth-4 certificate's total (`replay`: the library's first certificate, before its two deeper levels, its kept parts and its sharper cell bounds, kept as a cross-check of the window and the grid's conditions, not the library's `total`). It reads the curves from `lib/pnt`. Its docstring lists its commands. |
| `route_limits.jsonl` | The rows `route_limits.py run` recorded: a curve, `L`, `n`, the window, the corners and the total. |
| `refine_k2_probe.py` | Replays the depth-4 refined certificate (before the deeper levels) on the same grids (`replay2`); the library's `total2` is `mirror2.py`'s. |
| `mirror2.py` | Evaluates `total` and `total2` of the library (depths up to 6, with the coarse grid of `n/4` cells of four for `p₅` and `p₆`, the kept parts, Buchstab's `ω` on `[2, 3]` with its table `lnT`, and the cells' trapezoid and exact prime sums) cell by cell in exact integers, in parallel, and writes each cell's cost and kernel work to JSON. It prints the totals and the boxes tested at depths three to six below the decomposed cells. With `--depth4` no cell of depth four is decomposed: the decomposition stopped at depth four, whose `total` on the library's grid is the paper's `1.45721𝒦`. The kernel is the check of the Lean; this is the cut's source. |
| `gen_cert.py` | Cuts a certificate into parts, and writes `SieveGrid<T>.lean`, `SieveCert<T>P<k>.lean` and `SieveCert<T>.lean`. With no options it is the library's certificate, at `L = 278/125`, `n = 340` (tag `22240R`), in 387 files of at most 40 parts and 100000 units of work; `--tag`, `--L`, `--curve` and `--typeii` set the names and text of another one (the window and `n` come from `mirror2.py`'s output). Certificates at weaker exponents are in the git history and this script no longer generates them. |
| `gen_cgl_curve.py` | Writes `LinnikCGLSteps.lean` (Chen–Gupta–Li's Proposition 3.1 on 30 steps of `[5/7, 131/168]`, fourteen of width `1/1680` and then sixteen of `1/280`, with `ParC` parameters computed here and every field of `ParC.Good` checked in exact rationals, and Ingham's last step at `ε = 1/400000`), `SieveTypeIIU22240D.lean` (the curve `g7d`, `g7d_le_one`, `g7d_le_lin`, its counts, its window and Type II estimate) and `Linnik22240R.lean` (the theorem at `L = 278/125`). `--check` compares them with `lib/pnt`; `--table` prints the steps. |
| `density_payoff.py` | What a lower density curve would buy: for hypothetical curves made from `g7d` (a cap on its exponent, Chen–Gupta–Li's bound without the term behind its `7/3`, Heath-Brown's exponent `2` from `15/19`, with or without Ingham's estimate below `4/7`; and `classical`, without Chen–Gupta–Li, with Ingham's and Huxley's exponents in steps of `1/1680` on `[5/7, 131/168]`, which starts from `23/10` and gives the paper's `2.2685`), the window, `mirror2.py`'s `total2` at `n = 340`, and the lowest `L` passed with `total2 < 0.999K`. For each curve it computes a window admissible at `L` (the sampled scan, then the exact corners in rationals, moving an end inward by `10⁻⁵` while a corner fails), evaluates `total2` on it in exact integers, starts from `278/125` (which must pass), lowers `L` by `1/1000` while the total stays below `0.999K`, then tests once the value `1/2000` below the last one passed, and reports the lowest `L` passed. Computations for the paper's remark in Section 8, not theorems; all variants take about an hour. |
| `check_certificate.py` | Runs `mirror2.py` and `gen_cert.py` in a temporary directory, for the certificate (`22240R`), and compares the generated files with `lib/pnt` byte for byte. |

To check that the committed certificates are the ones these scripts generate:

```sh
python3 tools/linnik/check_certificate.py           # `22240R`, the only one, about half a minute
```

It prints the totals, the cross-checks, the number of parts and the comparison, and ends with
`CERTIFICATE <tag> PASS` when all its files are identical:

| Tag | `L` | Window | Curve | `total2/K` | Parts | Files |
|---|---|---|---|---|---|---|
| `22240R` | `278/125` | `[41556, 47531]/100000` | `g7d` | `0.9975361` | 5066 | 387 part files + grid + assembly |

`gen_cgl_curve.py --check` regenerates the four files of the curve and the theorem (about a minute, for its window's scan).

The kernel's check of a certificate is the build itself: each part file proves its parts by `decide +kernel`, and
`SieveCert22240R.lean` assembles them into `SieveCert.total2_lt_22240R`.

`Linnik22240R.linnik_22240r` is the route of the paper with the curve `g7d`: the steps of `LinnikCGLSteps.lean` on
`[5/7, 131/168]` in place of the plateau `7/3 + 1/2000` on `[5/7, 16/21]` and its first five Huxley steps, and Ingham's
last step at `ε = 1/400000` in the Lean lemma's convention (its exponent is `2 + 4c + 4ε`, so the slack is
`4ε = 1/100000` in place of `1/2000`). `route_limits.jsonl` has its row (`g7d`, `278/125`, `n = 340`, window
`[41556, 47531]`; its total is the first, depth-4 certificate's, `1.49216K`). Between `11161/5000` and `89/40` the curve
took Huxley's bound on the three steps of `[1307/1680, 131/168]` (`LinnikHuxJunction.lean`, in the git history): at
`11161/5000` the window's lower end was set near `7/9`. From `89/40` on both ends are set on the first Chen–Gupta–Li step
and those steps do not change the window, so they are Chen–Gupta–Li's again. The first fourteen steps are of width
`1/1680`; from `5/7 + 14/1680` on, steps of `1/280` leave the window as it is (the least slack of their corners is
`4.4·10⁻⁵`), and at `278/125` the curve has thirty Chen–Gupta–Li steps in place of the earlier `110` of `1/1680`.

What brings `total2/K` below `1` at `278/125` is the two deeper levels of the Buchstab decomposition, the coarse grid of
`85` cells of four, the kept parts, and the cells' bounds: Buchstab's `ω` itself on `[2, 3]` (`omKw`, with the table
`lnT` of `log((16 + k)/16)` and `log y ≤ (y − 1/y)/2`), `0.565073` above `3`, the trapezoid bound of each cell's
`Σ 1/p` and the exact `log x · Σ 1/(p log p)` of the last cell, and the bound `2h/(2e + h)` from below for the kept
parts. With them `total2/K` is `0.99754` at `278/125`; with the earlier bounds it was `0.99602` at `89/40`, the theorem
this one replaced (`Linnik22250R`, in the git history). The theorem has no hypothesis.
