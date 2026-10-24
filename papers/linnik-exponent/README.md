# Linnik's exponent

`main.tex` is the paper: Linnik's theorem with exponent `899/400`. All eight sections are written: the introduction,
the two inputs and the density curve, the Type II estimate, Type I and Harman's sieve, the decomposition and its
certificate, the proof, the formalisation, and a comparison with what the inputs give without the sieve. The
bibliography still needs checking against the sources. The paper claims only its own steps. The results it uses from the literature are cited to their sources and to
[`formalisations/`](../../formalisations/README.md): its two hypotheses, OpenAI's zero-free half-plane and Chen, Gupta
and Li's density estimate, and the classical results its proof uses, among them Ingham's and Huxley's density estimates,
the Halász–Montgomery inequality and Harman's sieve.

The theorem is `Linnik22475R.linnik_22475r` in `lib/pnt/Linnik22475R.lean`. Section 7's table names the Lean theorem
behind each claim, and `lib/check/Check.lean` prints their axioms.

To build: `latexmk -pdf main.tex`.
