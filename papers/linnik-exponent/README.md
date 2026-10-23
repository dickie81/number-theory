# Linnik's exponent

`main.tex` is the paper: Linnik's theorem with exponent `899/400`. It is a skeleton for now. Its theorem statement,
its two inputs and its claims table are written, and the comments in the other sections say what each will contain.
The paper claims only its own steps. The two results it uses from the literature are cited to their sources and to
`formalisations/`.

The theorem is `Linnik22475R.linnik_22475r` in `lib/pnt/Linnik22475R.lean`. Section 7's table names the Lean theorem
behind each claim, and `lib/check/Check.lean` prints their axioms.

To build: `latexmk -pdf main.tex`.
