# The Linnik paper's certificate tools

These scripts compute the sieve route's certificate outside Lean and generate the Lean files that the kernel checks.
They need Python 3 only.

| File | What it does |
|---|---|
| `route_limits.py` | Computes, for a density curve, an exponent `L` and a grid size `n`: the Halász–Montgomery window, its corners in exact rationals, and the certificate's total (`replay`, as `SieveCertDefs.lean` defines it). It reads the curves from `lib/pnt`. Its docstring lists its commands. |
| `route_limits.jsonl` | The rows `route_limits.py run` recorded: a curve, `L`, `n`, the window, the corners and the total. |
| `refine_k2_probe.py` | Replays the refined certificate (`SieveCert2Defs.lean`'s `total2`) on the same grids (`replay2`). |
| `mirror2.py` | Evaluates `total2` cell by cell in exact integers, cross-checks it against both replays, and writes each cell's cost and kernel work to JSON. |
| `gen_22475r.py` | Cuts a certificate into parts, and writes `SieveGrid<T>.lean`, `SieveCert<T>P<k>.lean` and `SieveCert<T>.lean`. With no options it is the certificate at `L = 899/400`, `n = 300` (tag `22475R`); `--tag`, `--L`, `--curve` and `--typeii` set the names and text of another one (the window and `n` come from `mirror2.py`'s output). |
| `gen_cgl_curve.py` | Writes `LinnikCGLSteps.lean` (Chen–Gupta–Li's Proposition 3.1 on 19 steps of `[5/7, 131/168]`, with `ParC` parameters computed here and every field of `ParC.Good` checked in exact rationals), `SieveTypeIIU22335D.lean` (the curve `g7d`, its counts, its window and Type II estimate) and `Linnik22335R.lean` (the theorem at `L = 4467/2000`). `--check` compares them with `lib/pnt`; `--table` prints the steps. |
| `check_certificate.py` | Runs `mirror2.py` and `gen_22475r.py` in a temporary directory, for each certificate (`22475R`, `22335R`) or the one named, and compares the generated files with `lib/pnt` byte for byte. |

To check that the committed certificates are the ones these scripts generate:

```sh
python3 tools/linnik/check_certificate.py           # both, about three minutes
python3 tools/linnik/check_certificate.py 22335R    # one of them
```

For each it prints the totals, the cross-checks, the number of parts and the comparison, and ends with
`CERTIFICATE <tag> PASS` when all its files are identical:

| Tag | `L` | Window | Curve | `total2/K` | Parts | Files |
|---|---|---|---|---|---|---|
| `22475R` | `899/400` | `[41335, 48069]/100000` | `g7c` | `0.99386` | 534 | 135 parts + grid + assembly |
| `22335R` | `4467/2000` | `[40993, 47746]/100000` | `g7d` | `0.98816` | 549 | 140 parts + grid + assembly |

`gen_cgl_curve.py --check` regenerates the three files of the second route (about a minute, for its window's scan).

The kernel's check of a certificate is the build itself: each part file proves its parts by `decide +kernel`, and
`SieveCert22475R.lean` (`SieveCert22335R.lean`) assembles them into `SieveCert.total2_lt_22475R`
(`SieveCert.total2_lt_22335R`).

The second route, `Linnik22335R.linnik_22335r`, replaces `g7c`'s plateau `7/3 + 1/2000` on `[5/7, 16/21]` and its first
five Huxley steps by the steps of `LinnikCGLSteps.lean`; `route_limits.jsonl` has its row (`g7d`, `4467/2000`, `n = 300`).
It has no hypothesis, like `Linnik22475R.linnik_22475r`.
