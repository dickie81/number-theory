# Papers

Each paper has a directory here with its LaTeX source, `main.tex`, and a README.

- **Every claim is a Lean theorem.** Each paper has a table that names the Lean theorem behind each of its claims.
  `lib/check/Check.lean` prints the axioms of those theorems, and `scripts/check_axioms.py` checks that they are
  `propext`, `Classical.choice` and `Quot.sound` only.
- **A paper claims only its own steps.** The results it uses from the literature are proved in `lib/` too. Each has a
  note in [`formalisations/`](../formalisations/README.md) with its source and the differences between the Lean
  statement and the published one. The paper cites the result to its source and to the note, and does not restate
  it as its own.

## The papers

| Paper | Its theorem | Lean | State |
|---|---|---|---|
| [Linnik's exponent](linnik-exponent/README.md) | There is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ Kq^{899/400}` | `Linnik22475R.linnik_22475r` | A skeleton: the theorem, its two hypotheses from the literature and the table of claims are written, and the other sections say what they will contain |

## Building

In a paper's directory, `latexmk -pdf main.tex`. CI compiles `linnik-exponent/main.tex` on every pull request and push
to `main`, and keeps the PDF as an artifact for 14 days (`.github/workflows/ci.yml`).

## Adding a paper

- Make a directory `papers/<name>/` with `main.tex` and a README.
- Put the paper's theorems in `lib/`, and add their `#print axioms` lines to `lib/check/Check.lean`.
- Write a note in `formalisations/` for each result from the literature the paper uses, and list it in that
  directory's index.
- Add a row to the table above, and a job to `.github/workflows/ci.yml` that compiles the paper.
