# The Linnik paper's certificate tools

These scripts compute the sieve route's certificate outside Lean and generate the Lean files that the kernel checks.
They need Python 3 only.

| File | What it does |
|---|---|
| `route_limits.py` | Computes, for a density curve, an exponent `L` and a grid size `n`: the Halász–Montgomery window, its corners in exact rationals, and the certificate's total (`replay`, as `SieveCertDefs.lean` defines it). It reads the curves from `lib/pnt`. Its docstring lists its commands. |
| `route_limits.jsonl` | The rows `route_limits.py run` recorded: a curve, `L`, `n`, the window, the corners and the total. |
| `refine_k2_probe.py` | Replays the refined certificate (`SieveCert2Defs.lean`'s `total2`) on the same grids (`replay2`). |
| `mirror2.py` | Evaluates `total2` cell by cell in exact integers, cross-checks it against both replays, and writes each cell's cost and kernel work to JSON. |
| `gen_22475r.py` | Cuts a certificate into parts, and writes `SieveGrid<T>.lean`, `SieveCert<T>P<k>.lean` and `SieveCert<T>.lean`. With no options it is the certificate at `L = 899/400`, `n = 300` (tag `22475R`, no longer in `lib/pnt`: its files are at commit `6df0ebd`); `--tag`, `--L`, `--curve` and `--typeii` set the names and text of another one (the window and `n` come from `mirror2.py`'s output). |
| `gen_cgl_curve.py` | Writes `LinnikCGLSteps.lean` (Chen–Gupta–Li's Proposition 3.1 on 107 steps of width `1/1680` on `[5/7, 1307/1680]`, with `ParC` parameters computed here and every field of `ParC.Good` checked in exact rationals, and Ingham's last step at `ε = 1/400000`), `LinnikHuxJunction.lean` (Huxley's bound on the three steps of `[1307/1680, 131/168]`, every field of `Par.Good` checked in exact rationals), `SieveTypeIIU22322D.lean` (the curve `g7d`, its counts, its window and Type II estimate) and `Linnik22322R.lean` (the theorem at `L = 11161/5000`). `--check` compares them with `lib/pnt`; `--table` prints the steps. |
| `check_certificate.py` | Runs `mirror2.py` and `gen_22475r.py` in a temporary directory, for the certificate (`22322R`), and compares the generated files with `lib/pnt` byte for byte. |

To check that the committed certificates are the ones these scripts generate:

```sh
python3 tools/linnik/check_certificate.py           # `22322R`, the only one, about two minutes
```

It prints the totals, the cross-checks, the number of parts and the comparison, and ends with
`CERTIFICATE <tag> PASS` when all its files are identical:

| Tag | `L` | Window | Curve | `total2/K` | Parts | Files |
|---|---|---|---|---|---|---|
| `22322R` | `11161/5000` | `[40981, 47725]/100000` | `g7d` | `0.99872` | 561 | 143 parts + grid + assembly |

`gen_cgl_curve.py --check` regenerates the four files of the curve and the theorem (about a minute, for its window's scan).

The kernel's check of a certificate is the build itself: each part file proves its parts by `decide +kernel`, and
`SieveCert22322R.lean` assembles them into `SieveCert.total2_lt_22322R`.

`Linnik22322R.linnik_22322r` replaces the plateau `7/3 + 1/2000` on `[5/7, 16/21]` and its first
five Huxley steps by the steps of `LinnikCGLSteps.lean` on `[5/7, 1307/1680]` and of `LinnikHuxJunction.lean` on
`[1307/1680, 131/168]` (Huxley's exponent is the smaller from `7/9` on), and Ingham's last step by one at `ε = 1/400000`;
`route_limits.jsonl` has its row (`g7d`, `11161/5000`, `n = 300`). The exponent before the Huxley steps on `[1307/1680, 131/168]`
was `893/400`: with Chen–Gupta–Li's steps there, `total2/K` was `0.98877` at `893/400` and above `1` at `11161/5000`.
It has no hypothesis. It replaced `Linnik22475R.linnik_22475r` (exponent `899/400`, curve `g7c`), which was removed from the tree and is at commit `6df0ebd`.
