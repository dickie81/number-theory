# Papers

The compiled papers and their supplements are at <https://dickie81.github.io/number-theory/>.

Each paper has a directory here with its LaTeX source, `main.tex`, and a README, and may have a supplement,
`supplement.tex`, which refers to the paper's numbering through its `main.aux`.

- **Every numbered result is a Lean theorem.** Each paper has a table that names the Lean theorem behind each of its numbered results. Historical remarks, comparisons with other methods and heuristics in a paper are not Lean theorems, and the paper says so.
  `lib/check/Check.lean` prints the axioms of those theorems, and `scripts/check_axioms.py` checks that they are
  `propext`, `Classical.choice` and `Quot.sound` only.
- **A paper claims only its own steps.** The results it uses from the literature are proved in `lib/` too. Each has a
  note in [`formalisations/`](../formalisations/README.md) with its source and the differences between the Lean
  statement and the published one. The paper cites the result to its source and to the note, and does not restate
  it as its own.

## The papers

| Paper | Its theorem | Lean | State |
|---|---|---|---|
| [Linnik's exponent](linnik-exponent/README.md) ([PDF](https://dickie81.github.io/number-theory/linnik-exponent.pdf), [supplement](https://dickie81.github.io/number-theory/linnik-exponent-supplement.pdf)) | There is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{278/125}` | `Linnik22240R.linnik_22240r` at [`8ba053b`](https://github.com/dickie81/number-theory/tree/8ba053b75eb56a65dcfd1cf986ecb3d58c6945bb); the library now proves `11/5` (`Linnik22000E.linnik_22000e`) | A full draft: every section is written; the bibliography is checked except Buchstab (1937), which is unverified |

## Building

In a paper's directory, `latexmk -pdf main.tex`, and then, for a supplement, `latexmk -pdf supplement.tex`. On every
pull request and push to `main`, CI compiles every `papers/<name>/main.tex` and then every
`papers/<name>/supplement.tex`, and keeps the PDFs as an artifact for 14 days (`.github/workflows/ci.yml`).

On every push to `main`, `.github/workflows/pages.yml` compiles the papers and their supplements in the same way and
publishes the PDFs to <https://dickie81.github.io/number-theory/>, each paper as `<name>.pdf` and its supplement as
`<name>-supplement.pdf`, with an index page that lists both.

## Adding a paper

- Make a directory `papers/<name>/` with `main.tex` and a README.
- Put the paper's theorems in `lib/`, and add their `#print axioms` lines to `lib/check/Check.lean`.
- Write a note in `formalisations/` for each result from the literature the paper uses, and list it in that
  directory's index.
- Add a row to the table above and to the top-level README's. CI and the site pick the paper up by themselves.
