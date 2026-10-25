# The Linnik paper's certificate tools

These scripts compute the sieve route's certificate outside Lean and generate the Lean files that the kernel checks.
They need Python 3 only.

| File | What it does |
|---|---|
| `route_limits.py` | Computes, for a density curve, an exponent `L` and a grid size `n`: the Halász–Montgomery window, its corners in exact rationals, and the depth-4 certificate's total (`replay`: the certificate that `SieveCertDefs.lean` had before its two deeper levels, kept as a cross-check of the window and the first four levels, not the library's `total`). It reads the curves from `lib/pnt`. Its docstring lists its commands. |
| `route_limits.jsonl` | The rows `route_limits.py run` recorded: a curve, `L`, `n`, the window, the corners and the total. |
| `refine_k2_probe.py` | Replays the depth-4 refined certificate (before the deeper levels) on the same grids (`replay2`); the library's `total2` is `mirror2.py`'s. |
| `mirror2.py` | Evaluates `total` and `total2` of the library (depths up to 6, with the coarse grid of `n/4` cells for `p₅` and `p₆`, and the kept parts) cell by cell in exact integers, in parallel, and writes each cell's cost and kernel work to JSON. The kernel is the check of the Lean; this is the cut's source. |
| `gen_cert.py` | Cuts a certificate into parts, and writes `SieveGrid<T>.lean`, `SieveCert<T>P<k>.lean` and `SieveCert<T>.lean`. With no options it is the library's certificate, at `L = 89/40`, `n = 340` (tag `22250R`), in 351 files of at most 40 parts and 100000 units of work; `--tag`, `--L`, `--curve` and `--typeii` set the names and text of another one (the window and `n` come from `mirror2.py`'s output). Certificates at weaker exponents are in the git history and this script no longer generates them. |
| `gen_cgl_curve.py` | Writes `LinnikCGLSteps.lean` (Chen–Gupta–Li's Proposition 3.1 on 107 steps of width `1/1680` on `[5/7, 1307/1680]`, with `ParC` parameters computed here and every field of `ParC.Good` checked in exact rationals, and Ingham's last step at `ε = 1/400000`), `LinnikHuxJunction.lean` (Huxley's bound on the three steps of `[1307/1680, 131/168]`, every field of `Par.Good` checked in exact rationals), `SieveTypeIIU22250D.lean` (the curve `g7d`, its counts, its window and Type II estimate) and `Linnik22250R.lean` (the theorem at `L = 89/40`). `--check` compares them with `lib/pnt`; `--table` prints the steps. |
| `check_certificate.py` | Runs `mirror2.py` and `gen_cert.py` in a temporary directory, for the certificate (`22250R`), and compares the generated files with `lib/pnt` byte for byte. |

To check that the committed certificates are the ones these scripts generate:

```sh
python3 tools/linnik/check_certificate.py           # `22250R`, the only one, about half a minute
```

It prints the totals, the cross-checks, the number of parts and the comparison, and ends with
`CERTIFICATE <tag> PASS` when all its files are identical:

| Tag | `L` | Window | Curve | `total2/K` | Parts | Files |
|---|---|---|---|---|---|---|
| `22250R` | `89/40` | `[41479, 47555]/100000` | `g7d` | `0.9960153` | 4715 | 351 part files + grid + assembly |

`gen_cgl_curve.py --check` regenerates the four files of the curve and the theorem (about a minute, for its window's scan).

The kernel's check of a certificate is the build itself: each part file proves its parts by `decide +kernel`, and
`SieveCert22250R.lean` assembles them into `SieveCert.total2_lt_22250R`.

`Linnik22250R.linnik_22250r` replaces the plateau `7/3 + 1/2000` on `[5/7, 16/21]` and its first
five Huxley steps by the steps of `LinnikCGLSteps.lean` on `[5/7, 1307/1680]` and of `LinnikHuxJunction.lean` on
`[1307/1680, 131/168]` (Huxley's exponent is the smaller from `7/9` on), and Ingham's last step by one at `ε = 1/400000` in the Lean lemma's convention (its exponent is `2 + 4c + 4ε`, so the slack is `4ε = 1/100000` in place of `1/2000`);
`route_limits.jsonl` has its row (`g7d`, `89/40`, `n = 340`: its total is the depth-4 certificate's, `1.42355K`). The exponent before the Huxley steps on `[1307/1680, 131/168]`
was `893/400`; with Chen–Gupta–Li's steps there and the depth-4 certificate, `total2/K` was `0.98877` at `893/400` and above `1` at `11161/5000`; the two deeper levels of the Buchstab decomposition and the coarse grid bring it to `0.99602` at `89/40`.
It has no hypothesis. It replaced an earlier theorem at a weaker exponent (`899/400`), which is no longer in the tree; see the git history.
