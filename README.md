# number-theory

A library of number theory papers whose results are checked by the Lean 4 kernel.

- `lib/`: the Lean library, built with Lake against Mathlib.
- `formalisations/`: one note for each published result that the library formalises, giving its source, its
  attribution and any differences between the Lean statement and the published one.
- `papers/`: the papers. Each claims only its own steps and cites `formalisations/` for the results it uses.

The first paper is on Linnik's exponent: the least prime in an arithmetic progression.
