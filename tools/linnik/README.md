# The Linnik paper's certificate tools

These scripts compute the sieve route's certificate outside Lean and generate the Lean files that the kernel checks.
They need Python 3 only.

| File | What it does |
|---|---|
| `route_limits.py` | Computes, for a density curve, an exponent `L` and a grid size `n`: the Halász–Montgomery window, its corners in exact rationals, and the certificate's total (`replay`, as `SieveCertDefs.lean` defines it). It reads the curves from `lib/pnt`. Its docstring lists its commands. |
| `route_limits.jsonl` | The rows `route_limits.py run` recorded: a curve, `L`, `n`, the window, the corners and the total. |
| `refine_k2_probe.py` | Replays the refined certificate (`SieveCert2Defs.lean`'s `total2`) on the same grids (`replay2`). |
| `mirror2.py` | Evaluates `total2` cell by cell in exact integers, cross-checks it against both replays, and writes each cell's cost and kernel work to JSON. |
| `gen_22475r.py` | Cuts the certificate at `L = 899/400`, `n = 300`, into parts, and writes `SieveGrid22475R.lean`, `SieveCert22475RP<k>.lean` and `SieveCert22475R.lean`. |
| `check_certificate.py` | Runs `mirror2.py` and `gen_22475r.py` in a temporary directory and compares the generated files with `lib/pnt` byte for byte. |

To check that the committed certificate is the one these scripts generate:

```sh
python3 tools/linnik/check_certificate.py   # about two minutes
```

It prints the totals (`total2/K = 0.99386`, below `1`), the cross-checks, the number of parts (534, in 135 files) and
the comparison. It ends with `CERTIFICATE PASS` when all 137 files are identical.

The kernel's check of the certificate is the build itself: each part file proves its parts by `decide +kernel`, and
`SieveCert22475R.lean` assembles them into `SieveCert.total2_lt_22475R`.
