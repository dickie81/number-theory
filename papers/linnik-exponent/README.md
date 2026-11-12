# Linnik's exponent

Read it: [the paper (PDF)](https://dickie81.github.io/number-theory/linnik-exponent.pdf) and
[its supplement (PDF)](https://dickie81.github.io/number-theory/linnik-exponent-supplement.pdf), rebuilt from `main`
on every push.

`main.tex` is the paper: Linnik's theorem with exponent `43/20`. Its nine sections are the introduction, the input
and the density curve, the Type II estimate in two variables (with its region), the Type I estimates (the classical
one and a bilinear one, proved by Parseval's identity) and Harman's comparison in two variables, the decomposition by
trees of Buchstab steps (its tests, its drops, the reversal of a term through its largest prime), its certificate (the
plan of a search that the kernel follows by hints), the proof, the formalisation, and a comparison with what the input
gives without the sieve; its appendix is the claims table. `supplement.tex` is its supplement: the proofs of the prime
sums' lemma and of the kernel bound (§S1), of the family lemmas in two variables (§S2), of Harman's comparisons in two
variables and of the leaves' lemma (§S3) and of the bound for rough numbers (§S4), the Lean details of the paper (§S5)
and the computations around the exponent (§S6). The two share their references, `references.tex`, so that each work has
the same number in both; the supplement adds three of its own. The
bibliography entries were checked against the publishers', arXiv and repository pages and, for Ingham and Huxley,
against scans of the originals; Xylouris's Acta Arith. 150 paper (L = 5.18, checked against the journal's PDF and EUDML) and the Lamzouri–Li–Soundararajan corrigendum (checked against the AMS contents page, Math. Comp. 86 (2017), 2551–2554) were added later; Buchstab's volume, issue and pages (1937) are still unverified, having been seen in secondary
sources only; Banks and Shparlinski's entry and their exponent `2.1115` are taken from R. Li's and Chen, Gupta and Li's citations of that paper, whose published version was not read (its arXiv version, 1605.07553v2, says that it does not improve the Linnik exponent); and the entries for the OpenAI preprints, OpenAI's `lean/formalization.yaml` catalogue and the AIProofWatch record are web pages, not refereed sources. The paper claims only its own steps. The results it uses from the literature are cited to their sources and to
[`formalisations/`](../../formalisations/README.md): its input, OpenAI's zero-free half-plane, and the classical
results its proof uses, among them Huxley's density estimate, the Halász–Montgomery inequality and Harman's sieve.

The paper and its supplement describe the library at the commit that contains them. Their earlier versions proved
the exponent `11/5`, by a Type II estimate in one variable on a window, with Chen, Gupta and Li's density estimate as a
second input, and a decomposition to depth eight; that theorem, `Linnik22000E.linnik_22000e`, is still in the library,
and the paper that proved it is in the git history at commit
[`49dc981`](https://github.com/dickie81/number-theory/tree/49dc9812703c80448f96349e06a4c793a9339f6b). Before that they proved `278/125`
(`Linnik22240R.linnik_22240r`, at commit
[`8ba053b`](https://github.com/dickie81/number-theory/tree/8ba053b75eb56a65dcfd1cf986ecb3d58c6945bb)).

The theorem is `Linnik21500.linnik_21500` in `lib/pnt/Linnik21500.lean`, with the exponent written `2150/1000`. It
has no hypotheses in Lean. Its proof uses one unrefereed result, which the library re-proves itself: the zero-free
half-plane `Re s > 11/12` of OpenAI's preprints (the library follows the companion preprint). Its density estimate is
Huxley's, which the library proves, used only from `7789/10000` on: below that the Type II estimate bounds both of its
variables by orthogonality. Neither Ingham's estimate nor Chen, Gupta and Li's is in its proof (no module of the
library's formalisation of their paper is in its import cone). Its truth rests on Lean's kernel, Mathlib and the pinned
toolchain (with the vendored upstream ports and the provenance of the build cache), not on the preprint; whether the
Lean statement faithfully captures the preprint's theorem matters for attribution and interpretation, not for the
truth of the theorem. Independent checking of the half-plane result is partial: OpenAI's release has its own Lean
formalisation (its catalogue `lean/formalization.yaml` marks it "partial progress", review status "unchecked"), which
is not independent of OpenAI; and the AIProofWatch record covers the Riemann zeta function only. The theorem is
unconditional. Its exponent is to be compared with `12/5`, which the classical deduction gives from the same results
(the half-plane and Huxley's estimate), and with `7/3`, which it gives with Chen, Gupta and Li's estimate as well: the
paper's sieve brings them down to `43/20 = 2.15`. It is not on the same footing as the exponents `5.5` and `5` of
Heath-Brown and Xylouris, whose proofs use refereed results only, while this one uses the half-plane through its
formalisation. The claims table (Appendix A) names the Lean theorem behind each claim, and `lib/check/Check.lean`
prints their axioms (`lib/check/CheckAll.lean`, with `python3 scripts/check_axioms.py --all`, prints the axioms of
further declarations of the library). The certificate is checked by the kernel in 1510 parts, in the 39 files
`lib/pnt/SieveHint21500P1.lean` to `SieveHint21500P39.lean`, which `tools/linnik/hint_cert.py` writes.

To build: `latexmk -pdf main.tex`, then `latexmk -pdf supplement.tex` (pdfLaTeX, as CI does; the supplement reads the
paper's numbering from `main.aux` through `xr-hyper`). The preamble also lets XeTeX (for example
`tectonic main.tex`) compile the paper; the Lean blocks then lack some glyphs of the monospace font.
