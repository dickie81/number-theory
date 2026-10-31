# number-theory

A library of number theory papers whose results are checked by the Lean 4 kernel.

**Read the papers at <https://dickie81.github.io/number-theory/>**: each paper and its supplement as PDFs, rebuilt
from `main` on every push.

| Paper | Read it |
|---|---|
| *Linnik's constant below the zero-density exponent: 11/5 from a zero-free half-plane and the Chen–Gupta–Li density estimate*. Every reduced residue class mod `q` contains a prime `p ≤ Kq^{11/5}` (`Linnik22000E.linnik_22000e`), by Harman's sieve with a Type II estimate over the zeros' real parts, a bilinear Type I estimate and a Buchstab decomposition to depth eight. | [Paper (PDF)](https://dickie81.github.io/number-theory/linnik-exponent.pdf) · [Supplement (PDF)](https://dickie81.github.io/number-theory/linnik-exponent-supplement.pdf) · [Source](papers/linnik-exponent/README.md) |

## What is here

- [`docs/account.md`](docs/account.md): the library on one page. What it proves, what that rests on, how much of
  number theory it covers, what a new input would give at once, and where the next results are.
- `lib/`: the Lean library, built with Lake against Mathlib. [`docs/inventory.md`](docs/inventory.md) lists its
  results: every theorem of the check files `lib/check/Check.lean`, `CheckAll.lean`, `CheckZeta23.lean` and
  `CheckDH.lean`, with its headline. CI checks that the library keeps nothing that these theorems do not use.
- [`formalisations/`](formalisations/README.md): a note for each published result that a paper uses, and for a few
  others that the library formalises. Each note gives the result's source and attribution, and any differences
  between the Lean statement and the published one.
- [`papers/`](papers/README.md): the papers. Each claims only its own steps and cites `formalisations/` for the
  results it uses.
- [The Strip and the Count](https://dickie81.github.io/number-theory/zeros.html), a page of the site: what the
  library's theorems say about the zeros of `ζ` and of Dirichlet L-functions, and what that gives for Linnik's
  exponent. `scripts/zeros_page.py` writes it from `site/zeros.html`, reading every number from the statement of the
  theorem that proves it, and CI checks that it agrees with the Lean.

## Layout

| Path | Contents |
|---|---|
| `lib/core` | The library's modules that need only Mathlib: 325 files. |
| `lib/pnt` | The modules that also use PrimeNumberTheoremAnd, among them the Linnik paper's: 344 files. |
| `lib/dh` | The Davenport–Heilbronn function and its zeros: 53 files. |
| `lib/zeta23` | The modules that also use `zeta23`: 7 files. |
| `lib/vendor/pnt-plus`, `lib/vendor/zeta23` | Two upstream libraries, ported to this toolchain, each with its license and its port patch. See their READMEs. |
| `lib/check/Check.lean` | The axioms of the papers' theorems. This is the default build target. |
| `lib/check/CheckAll.lean` | The axioms of every final theorem of the library. Not built by default; CI builds it whenever it builds the Lean. |
| `lib/check/CheckZeta23.lean` | The axioms of the final theorems of `lib/zeta23`, which `CheckAll` cannot import: zeta23's copies of PrimeNumberTheoremAnd's files declare the same names. Not built by default; CI builds it whenever it builds the Lean. |
| `lib/check/CheckDH.lean` | The axioms of the final theorems of `lib/dh`. `CheckAll` does not import the layer, so that its build leaves out the layer's numerical certificates. Not built by default; CI builds it whenever it builds the Lean. |
| `formalisations/` | The notes on the results from the literature. See its [README](formalisations/README.md), the index of the notes. |
| `papers/` | The papers. See its [README](papers/README.md). |
| `scripts/` | The build script and the checks (see [`docs/building.md`](docs/building.md)), and `build_site.py`, which builds the papers' web site. |
| `site/` | `zeros.html`, the template of the site's page on the zeros, which `scripts/zeros_page.py` fills from the Lean sources. |
| `docs/` | [`account.md`](docs/account.md): the library on one page, with its frontier; `scripts/check_account.py` checks its Lean names. [`inventory.md`](docs/inventory.md): the library's results, written by `scripts/inventory.py`. [`building.md`](docs/building.md): building, memory, the checks and CI. [`dry-efficiency-survey.md`](docs/dry-efficiency-survey.md) and [`stack-bridges.md`](docs/stack-bridges.md): a survey of duplication and build cost, and three modules that join parts of the library. |
| `tools/linnik/` | The Linnik paper's certificate tools: the route's computations outside Lean and the generator of the certificate's Lean files. See its README. |

## Building

You need [elan](https://github.com/leanprover/elan), git and Python 3.

```sh
lake exe cache get               # Mathlib's prebuilt files
scripts/build.sh                 # the default target, lib/check/Check.lean, and everything it imports
python3 scripts/check_axioms.py  # the papers' theorems depend only on Lean's standard axioms
```

A cold build takes several hours, and the kernel's checks of the certificate need a lot of memory.
[`docs/building.md`](docs/building.md) gives the memory limits and how the build script keeps within them, the other
checks (among them that the sources contain no `sorry` and no declared axiom), and what CI and the site's workflow do.

## License

This repository is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) (`LICENSE`), with these
exceptions:

- the vendored libraries in `lib/vendor/`, which keep their own licenses (the Apache License 2.0, in each library's
  `LICENSE`);
- `lib/pnt/Architect.lean`, which reproduces the attribute and command syntax of LeanArchitect
  (`https://github.com/hanwenzhu/LeanArchitect`) under its license, the Apache License 2.0.
