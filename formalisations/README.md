# Formalisations

A paper in this repository claims only its own results. When a paper uses a result from the literature, that result
is formalised in `lib/` and documented here. Each note gives:

- the source;
- the Lean statement;
- how the Lean statement differs from the source's;
- how the formalisation was done.

The paper cites the note and does not restate the result as its own.

## Index

| Result | Source | Lean | Used by | Note |
|---|---|---|---|---|
| No zero of any Dirichlet `L`-function in `Re s > 11/12`, the pole at `s = 1` excepted | OpenAI, `github.com/openai/math`, entry 003 (the companion preprint of 5 October 2026) | `Eis.LFunction_ne_zero_of_re_gt` | The Linnik exponent paper. One use is the top bin of the Type II estimate (`SieveTypeII.bin_rect`). | [openai-half-plane.md](openai-half-plane.md) |
| At most `C(qT)^{(7/3)(1−σ)+ε}` characters mod `q` have an `L`-function with a zero in `Re s ≥ σ`, `\|Im s\| ≤ T`, for `5/7 ≤ σ ≤ 16/21` | B. Chen, V. Gupta and Y. C. Li, arXiv:2507.08296v2 | `LinnikCGLDensity.cglDensity`, which proves `LinnikCGL.CGLDensity` | The Linnik exponent paper: `Linnik22475R.linnik_22475r` is `linnik_22475r_of` at it | [chen-gupta-li-density.md](chen-gupta-li-density.md) |

The Chen–Gupta–Li note also covers the paper's Theorem 10.1, which they state for primitive characters and credit to
Heath-Brown. Heath-Brown's paper could not be read, so the library proves the theorem (`LinnikCGLHB101.cglt101`) by
combining two other sources. It is documented with the rest of the formalisation of their paper, and no paper here
claims it.

## Further results

The Linnik theorem's proof uses further results from the literature, formalised in the library. Notes on them are not
yet written. Here is what the proof terms read so far show.

- **The density curve of the Type II estimate** (`SieveTypeIIU226C.counts_7c`) is glued from these pieces:
  - Ingham's estimate, on twenty steps of `[4/7, 5/7]` (`LinnikStairs7`, from `LinnikInghamC.charDensity_ingham_c`);
  - Chen–Gupta–Li's estimate, on `[5/7, 16/21]`;
  - Huxley's estimate, on twenty steps of `[16/21, 5/6]` (`LinnikStairs7`, from `LinnikHuxStep.charDensity_gen`);
  - a step of Huxley's bound with the exponent `101/50`, on `[5/6, 1]` (`LinnikStep.charDensity_step`).

  Each piece counts characters, not zeros. The Ingham and Huxley steps use, among other results, a hybrid fourth
  moment of Dirichlet `L`-functions (`LinnikFourth.fourth_moment`).
- **The Halász–Montgomery inequality over the characters mod `q`** (`LinnikPower.hm_duality`). The Type II estimate
  uses it on its top piece `[5/6, 11/12]` (`SieveHMBin`).
- **Harman's fundamental theorem, in the form used** (`SieveProp6`).

A census of the declarations the theorem's proof uses will complete this list. Each result it needs will then get an
entry in the index.

## The vendored libraries

`lib/vendor/` holds two upstream Lean libraries, each with its license, its upstream commit and the patch that ports
it to this repository's Lean and Mathlib:

- PrimeNumberTheoremAnd (`lib/vendor/pnt-plus`);
- `zeta23` of `anthropics/formal-math` (`lib/vendor/zeta23`).

Their results are those projects' own, and the notes above do not cover them.
