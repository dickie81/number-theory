# Linnik's exponent

Read it: [the paper (PDF)](https://dickie81.github.io/number-theory/linnik-exponent.pdf) and
[its supplement (PDF)](https://dickie81.github.io/number-theory/linnik-exponent-supplement.pdf), rebuilt from `main`
on every push.

`main.tex` is the paper: Linnik's theorem with exponent `11/5`. Its eight sections are the introduction, the two
inputs and the density curve, the Type II estimate (with where its window comes from), the Type I estimates (the
classical one and a bilinear one, proved by Parseval's identity) and Harman's sieve, the decomposition to depth eight
and its certificate (with the bound for rough numbers and a figure of the cells, drawn by `tools/linnik/fig_cells.py`
into `fig-cells.tex`), the proof, the formalisation, and a comparison with what the inputs give without the sieve; its
appendix is the claims table. `supplement.tex` is its supplement: the proofs of four standard results (the prime sums,
the Type II families, Harman's comparison and the rough numbers, §S1–§S4), with the proofs of the bilinear estimate's
form at the leaves and of Harman's comparison with it (§S3), the Lean details of the paper (§S5) and the computations
around the exponent (§S6). The two share their references, `references.tex`, so that each work has
the same number in both; the supplement adds three of its own. The
bibliography entries were checked against the publishers', arXiv and repository pages and, for Ingham and Huxley,
against scans of the originals; Xylouris's Acta Arith. 150 paper (L = 5.18, checked against the journal's PDF and EUDML) and the Lamzouri–Li–Soundararajan corrigendum (checked against the AMS contents page, Math. Comp. 86 (2017), 2551–2554) were added later; Buchstab's volume, issue and pages (1937) are still unverified, having been seen in secondary
sources only; Banks and Shparlinski's entry and their exponent `2.1115` are taken from R. Li's and Chen, Gupta and Li's citations of that paper, whose published version was not read (its arXiv version, 1605.07553v2, says that it does not improve the Linnik exponent); and the entries for the OpenAI preprints, OpenAI's `lean/formalization.yaml` catalogue and the AIProofWatch record are web pages, not refereed sources. The paper claims only its own steps. The results it uses from the literature are cited to their sources and to
[`formalisations/`](../../formalisations/README.md): its two inputs, OpenAI's zero-free half-plane and Chen, Gupta
and Li's density estimate, and the classical results its proof uses, among them Ingham's and Huxley's density estimates,
the Halász–Montgomery inequality and Harman's sieve.

The paper and its supplement describe the library at the commit that contains them. Their earlier versions proved
the exponent `278/125`, by the decomposition to depth six with kept parts and without the bilinear estimate; that
theorem, `Linnik22240R.linnik_22240r`, is in the git history at commit
[`8ba053b`](https://github.com/dickie81/number-theory/tree/8ba053b75eb56a65dcfd1cf986ecb3d58c6945bb).

The theorem is `Linnik22000E.linnik_22000e` in `lib/pnt/Linnik22000E.lean`. It has no hypotheses in Lean. Its proof uses two unrefereed results that the library re-proves itself: the zero-free half-plane `Re s > 11/12` of OpenAI's preprints (the library follows the companion preprint), and Chen, Gupta and Li's arXiv preprint (density estimate), of which the library formalises Proposition 3.1 (in the form for one point per character that their proof uses) and what it rests on, and derives the 30 density steps from it; their Theorem 1.2 as they state it and the rest of their paper are not formalised. Its truth rests on Lean's kernel, Mathlib and the pinned toolchain (with the vendored upstream ports and the provenance of the build cache), not on the preprints; whether the Lean statements faithfully capture the preprints' theorems matters for attribution and interpretation, not for the truth of the theorem. Independent checking of the half-plane result is partial: OpenAI's release has its own Lean formalisation (its catalogue `lean/formalization.yaml` marks it "partial progress", review status "unchecked"), which is not independent of OpenAI; and the AIProofWatch record covers the Riemann zeta function only. The theorem is unconditional. Its exponent is to be compared with `7/3`, which the classical deduction gives from the same two results (the half-plane and Chen, Gupta and Li's density estimate): the paper's sieve brings `7/3 ≈ 2.333` down to `11/5 = 2.2`. It is not on the same footing as the exponents `5.5` and `5` of Heath-Brown and Xylouris, whose proofs use refereed results only, while this one uses the two unrefereed results through their formalisations. The claims table (Appendix A) names the Lean theorem
behind each claim, and `lib/check/Check.lean` prints their axioms (of the 30 Chen–Gupta–Li density steps it prints the first and the last, and it prints Ingham's last step and Chen, Gupta and Li's Proposition 3.1; `SieveCurve7D.counts_7d` uses every step, so all of them are in the dependency cone of the theorem, whose axioms are checked; `lib/check/CheckAll.lean`, with `python3 scripts/check_axioms.py --all`, prints the axioms of further declarations of the library).

To build: `latexmk -pdf main.tex`, then `latexmk -pdf supplement.tex` (pdfLaTeX, as CI does; the supplement reads the
paper's numbering from `main.aux` through `xr-hyper`). The figure needs TikZ. The preamble also lets XeTeX (for example
`tectonic main.tex`) compile the paper; the Lean blocks then lack some glyphs of the monospace font.
