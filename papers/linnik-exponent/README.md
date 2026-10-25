# Linnik's exponent

`main.tex` is the paper: Linnik's theorem with exponent `11161/5000`. All eight sections are written: the introduction,
the two inputs and the density curve, the Type II estimate, Type I and Harman's sieve, the decomposition and its
certificate, the proof, the formalisation, and a comparison with what the inputs give without the sieve. The
bibliography entries were checked against the publishers', arXiv and repository pages and, for Ingham and Huxley,
against scans of the originals; Buchstab's volume, issue and pages (1937) are still unverified, having been seen in secondary
sources only, and the entries for the OpenAI preprints and the AIProofWatch record are web pages, not refereed sources. The paper claims only its own steps. The results it uses from the literature are cited to their sources and to
[`formalisations/`](../../formalisations/README.md): its two inputs, OpenAI's zero-free half-plane and Chen, Gupta
and Li's density estimate, and the classical results its proof uses, among them Ingham's and Huxley's density estimates,
the Halász–Montgomery inequality and Harman's sieve.

The theorem is `Linnik22322R.linnik_22322r` in `lib/pnt/Linnik22322R.lean`. It has no hypotheses in Lean. Its correctness rests on two unrefereed results that the library formalises itself: the zero-free half-plane `Re s > 11/12` of OpenAI's preprints, and Chen, Gupta and Li's arXiv preprint (density estimate). It is correct if those preprints are correct and the Lean formalisations are faithful to them. The only independent machine check of the half-plane result that the author has seen reported (by AIProofWatch) covers the Riemann zeta function only. Its exponent is not comparable with the unconditional results of Heath-Brown and Xylouris. Section 7's table names the Lean theorem
behind each claim, and `lib/check/Check.lean` prints their axioms (of the 107 Chen–Gupta–Li density steps it prints the first and the last, of the three Huxley junction steps the first and the last, and it prints Ingham's last step and Chen, Gupta and Li's Proposition 3.1; the other steps print their axioms in `LinnikCGLSteps.lean` when it is built; `lib/check/CheckAll.lean`, with `python3 scripts/check_axioms.py --all`, prints the axioms of further declarations of the library).

To build: `latexmk -pdf main.tex` (pdfLaTeX, as CI does). The preamble also lets XeTeX (for example `tectonic main.tex`) compile it; the Lean blocks then lack some glyphs of the monospace font.
