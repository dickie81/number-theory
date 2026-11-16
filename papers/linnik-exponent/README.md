# Linnik's exponent

Read it: [the paper (PDF)](https://dickie81.github.io/number-theory/linnik-exponent.pdf) and
[its supplement (PDF)](https://dickie81.github.io/number-theory/linnik-exponent-supplement.pdf), rebuilt from `main`
on every push.

`main.tex` is the paper: Linnik's theorem with exponent `21/10` (its Theorem 1.1), and with exponent `43/20` from the
half-plane and Huxley's estimate alone (its Theorem 1.2). Its twelve sections are the introduction, the two inputs
and the two density curves, the Type II estimate in two variables (with its region), the Type I estimates (the
classical one and a bilinear one, proved by Parseval's identity) and Harman's comparison in two variables, the
decomposition by trees of Buchstab steps (its tests, its drops, the reversal of a term through its largest prime), its
certificate at `43/20` (the plan of a search that the kernel follows by hints), the proof of Theorem 1.2; then, for
Theorem 1.1, the resonant window (a Type II estimate in one variable that sorts the characters by the sizes of the
rest's prime sums too, and its tests), two more rules (the leaves of a comparison cut in three, with a fourth moment,
and the reversal of a term of the sign `+`), and the certificate at `21/10` with the proof; then the formalisation,
and a comparison with what the inputs give without the sieve; its appendix is the claims table. `supplement.tex` is its
supplement: the proofs of the prime sums' lemma and of the kernel bound (§S1), of the family lemmas in two variables
(§S2), of Harman's comparisons in two variables and of the leaves' lemma (§S3) and of the bound for rough numbers
(§S4), the Lean details of the paper (§S5), the computations around the exponents (§S6), and the proofs for the
resonant window (§S7) and for the leaves cut in three (§S8). The two share their references, `references.tex`, so that each work has
the same number in both; the supplement adds three of its own. The
bibliography entries were checked against the publishers', arXiv and repository pages and, for Ingham and Huxley,
against scans of the originals; Xylouris's Acta Arith. 150 paper (L = 5.18, checked against the journal's PDF and EUDML) and the Lamzouri–Li–Soundararajan corrigendum (checked against the AMS contents page, Math. Comp. 86 (2017), 2551–2554) were added later; Buchstab's volume, issue and pages (1937) are still unverified, having been seen in secondary
sources only; Banks and Shparlinski's entry and their exponent `2.1115` are taken from R. Li's and Chen, Gupta and Li's citations of that paper, whose published version was not read (its arXiv version, 1605.07553v2, says that it does not improve the Linnik exponent); and the entries for the OpenAI preprints, OpenAI's `lean/formalization.yaml` catalogue and the AIProofWatch record are web pages, not refereed sources. The paper claims only its own steps. The results it uses from the literature are cited to their sources and to
[`formalisations/`](../../formalisations/README.md): its two inputs, OpenAI's zero-free half-plane and Chen, Gupta and
Li's large values estimate (their Proposition 3.1), and the classical results its proofs use, among them Ingham's and
Huxley's density estimates, the Halász–Montgomery inequality and Harman's sieve. Naslund's entry was checked against
its Hexagon record on 16 November 2026.

The paper and its supplement describe the library at the commit that contains them.

Theorem 1.1 is `Linnik21000.linnik_21000` in `lib/pnt/Linnik21000.lean`, with the exponent written `2100/1000`, and
Theorem 1.2 is `Linnik21500.linnik_21500` in `lib/pnt/Linnik21500.lean`, with the exponent written `2150/1000`. Neither
has a hypothesis in Lean.

The proof of Theorem 1.2 uses one unrefereed result, which the library re-proves itself: the zero-free half-plane
`Re s > 11/12` of OpenAI's preprints (the library follows the companion preprint). Its density estimate is Huxley's,
which the library proves, used only from `7789/10000` on: below that the Type II estimate bounds both of its variables
by orthogonality. Neither Ingham's estimate nor Chen, Gupta and Li's is in its proof (no module of the library's
formalisation of their paper is in its import cone): its tests are those of the namespace `SieveAd.Plain`, with the
paper's conditions on the leaves of a comparison alone.

The proof of Theorem 1.1 uses a second unrefereed result, which the library also re-proves: Chen, Gupta and Li's
Proposition 3.1, a large values estimate for Dirichlet polynomials with characters (`LinnikCGLHB101.prop31`). It
enters twice: in the counts of the resonant window, for the powers of a prime sum, and through the density curve `g*`
(`SieveCurve7D.g7d`: the trivial count, Ingham's estimate, steps from Proposition 3.1, Huxley's estimate), in the
estimate for the leaves cut in three.

The truth of the two theorems rests on Lean's kernel, Mathlib and the pinned toolchain (with the vendored upstream
ports and the provenance of the build cache), not on the preprints; whether a Lean statement faithfully captures a
preprint's theorem matters for attribution and interpretation, not for the truth of the theorems. Independent checking
of the half-plane result is partial: OpenAI's release has its own Lean formalisation (its catalogue
`lean/formalization.yaml` marks it "partial progress", review status "unchecked"), which is not independent of OpenAI;
and the AIProofWatch record covers the Riemann zeta function only. Chen, Gupta and Li's preprint is not refereed. The
theorems are unconditional (Theorem 1.1 once the kernel's check of its certificate ends). Their exponents are to be compared with `12/5`, which the classical deduction gives from
the half-plane and Huxley's estimate, and with `7/3`, which it gives with Chen, Gupta and Li's density estimate: the
paper's sieve brings them down to `43/20 = 2.15` and to `21/10 = 2.1`. They are not on the same footing as the
exponents `5.5` and `5` of Heath-Brown and Xylouris, whose proofs use refereed results only, while these use the two
recent results through their formalisations.

The claims table (Appendix A) names the Lean theorem behind each claim. `lib/check/Check.lean`, the default build,
prints the axioms of Theorem 1.2 and of the theorems of Sections 2 to 7; `lib/check/CheckAll.lean` (with
`python3 scripts/check_axioms.py --all`) prints those of Theorem 1.1 and of the theorems of Sections 8 to 10, with
further declarations of the library. The certificate at `43/20` is checked by the kernel in 1552 parts, in the 17
files `lib/pnt/SieveHint21500P1.lean` to `SieveHint21500P17.lean`, about 63 minutes of the kernel's time. The
certificate at `21/10` has 107374 parts, in the 1150 files `lib/pnt/SieveHint21000P1.lean` to
`SieveHint21000P1150.lean`, about 76 hours of one core by the generator's estimate; the kernel's check of them was not
finished on 16 November 2026, and Theorem 1.1 is a theorem of the library once it ends without error. `tools/linnik/hint_cert.py` writes
both.

To build: `latexmk -pdf main.tex`, then `latexmk -pdf supplement.tex` (pdfLaTeX, as CI does; the supplement reads the
paper's numbering from `main.aux` through `xr-hyper`). The preamble also lets XeTeX (for example
`tectonic main.tex`) compile the paper; the Lean blocks then lack some glyphs of the monospace font.
