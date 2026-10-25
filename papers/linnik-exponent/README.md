# Linnik's exponent

`main.tex` is the paper: Linnik's theorem with exponent `11161/5000`. All eight sections are written: the introduction,
the two inputs and the density curve, the Type II estimate, Type I and Harman's sieve, the decomposition and its
certificate, the proof, the formalisation, and a comparison with what the inputs give without the sieve. The
bibliography still needs checking against the sources. The paper claims only its own steps. The results it uses from the literature are cited to their sources and to
[`formalisations/`](../../formalisations/README.md): its two hypotheses, OpenAI's zero-free half-plane and Chen, Gupta
and Li's density estimate, and the classical results its proof uses, among them Ingham's and Huxley's density estimates,
the Halász–Montgomery inequality and Harman's sieve.

The theorem is `Linnik22322R.linnik_22322r` in `lib/pnt/Linnik22322R.lean`. It depends on the zero-free half-plane `Re s > 11/12` of OpenAI's preprints, which have not been refereed, and on
Chen, Gupta and Li's arXiv preprint. Section 7's table names the Lean theorem
behind each claim, and `lib/check/Check.lean` prints their axioms (of the 107 Chen–Gupta–Li density steps it prints the first and the last, of the three Huxley junction steps the first and the last, and it prints Ingham's last step and Chen, Gupta and Li's Proposition 3.1; the other steps print their axioms in `LinnikCGLSteps.lean` when it is built; `lib/check/CheckAll.lean`, with `python3 scripts/check_axioms.py --all`, prints the axioms of further declarations of the library).

To build: `latexmk -pdf main.tex`.
