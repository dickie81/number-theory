# Linnik's exponent

Read it: [the paper (PDF)](https://dickie81.github.io/number-theory/linnik-exponent.pdf) and
[its supplement (PDF)](https://dickie81.github.io/number-theory/linnik-exponent-supplement.pdf), rebuilt from `main`
on every push.

`main.tex` is the paper. It proves Linnik's theorem with exponent `21/10` (its Theorem 1.1), and with exponent `43/20`
from fewer inputs (its Theorem 1.2): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a
prime `p ≡ a (mod q)` with `p ≤ K·q^L`, where `L = 21/10` or `L = 43/20`. Its Corollary 1.3 gives both in number.

The proofs use recent results that have not been refereed. Theorem 1.2 uses one, OpenAI's zero-free half-plane
`Re s > 11/12` for Dirichlet L-functions, and of the density estimates only Huxley's; Theorem 1.1 also uses Chen, Gupta
and Li's large values estimate. The exponents are not to be compared with Xylouris's `5`. They are to be compared
with `12/5` and `7/3`, and with the `1/0.472 < 2.1187` that the half-plane gives through Harman's theorem of 2005:
Theorem 1.2's `43/20` is larger than that, Theorem 1.1's `21/10` smaller ([below](#what-the-proofs-rest-on)).

## The paper and the supplement

Section 1 of the paper is the introduction. Sections 2 to 7 prove Theorem 1.2:

- 2: the two inputs and the two density curves;
- 3: the Type II estimate in two variables, and its region;
- 4: the Type I estimates (the classical one, and a bilinear one proved by Parseval's identity) and Harman's
  comparison in two variables;
- 5: the decomposition by trees of Buchstab steps, with its tests, its drops and its reversals;
- 6: the certificate at `43/20`;
- 7: the proof of Theorem 1.2.

Sections 8 to 10 add what Theorem 1.1 needs:

- 8: the resonant window, a Type II estimate in one variable, and its tests;
- 9: two more rules, the leaves of Harman's comparison cut in three (with a fourth moment) and the reversal of a term
  of the sign `+`;
- 10: the certificate at `21/10`, and the proof of Theorem 1.1.

Section 11 is on the formalisation, and Section 12 compares the theorems with what the inputs give by the classical
argument and through Harman's theorems on primes in a progression.
Appendix A is the claims table, and Appendix B lists the paper's terms and notation.

`supplement.tex` is the supplement:

- §S1: the proofs of the prime sums' lemma and of the kernel bound (for the kernel `k_Y` of the Halász–Montgomery
  inequality);
- §S2: those of the family lemmas in two variables;
- §S3: those of Harman's comparisons in two variables and of the leaves' lemma;
- §S4: that of the bound for rough numbers;
- §S5: the Lean details of the paper;
- §S6: the computations around the exponents;
- §S7 and §S8: the proofs for the resonant window and for the leaves cut in three.

The paper claims only its own steps: the results it uses from the literature are cited to their sources and to
[`formalisations/`](../../formalisations/README.md): its two inputs, OpenAI's zero-free half-plane and Chen, Gupta and
Li's large values estimate (their Proposition 3.1), and the classical results its proofs use, among them Ingham's and
Huxley's density estimates, the Halász–Montgomery inequality and Harman's sieve.

## The theorems in the library

The paper and its supplement describe the library at the commit that contains them. Paths that begin with `lib/`,
`scripts/` or `tools/` are from the repository root.

Theorem 1.1 is `Linnik21000.linnik_21000` in `lib/pnt/Linnik21000.lean`, with the exponent written `2100/1000`, and
Theorem 1.2 is `Linnik21500.linnik_21500` in `lib/pnt/Linnik21500.lean`, with the exponent written `2150/1000`. Neither
has a hypothesis in Lean. Both rest on certificates whose build is opt-in: `lib/check/CheckLinnik.lean` prints their
axioms, and neither the repository's default build nor its CI on every change compiles them
([below](#checking-the-proofs)).

Corollary 1.3 is the two theorems in number: there are `c > 0` and `K` such that for every `q ≥ 1`, every `a` prime
to `q` and every `x ≥ K·q^L` the residue class of `a` mod `q` has at least `c·x/(φ(q) log x)` primes `p ≤ x`; and
for large `q` and every `a` prime to `q` it has at least `(1 − C)/2·q^L/(φ(q) log q^L)` primes in `(q^L, 2q^L]`,
where `C` (the certificate's bound for the fraction of the primes that the sieve loses) is `0.97716...` at `21/10` and
`0.94846...` at `43/20`.
It is `Linnik21000.count_21000` and `Linnik21000.count_large_21000` in
`lib/pnt/Linnik21000Count.lean`, and `Linnik21500.count_21500` and `Linnik21500.count_large_21500` in
`lib/pnt/Linnik21500Count.lean`; the step from `x = q^L` to every `x` (Lemma 5.16) is
`SieveAd.count_of_large` in `lib/pnt/SieveAdCount.lean`, and uses no input. At `21/10` the corollary rests on the
certificate of Theorem 1.1 ([below](#checking-the-proofs)).

## What the proofs rest on

The proof of Theorem 1.2 uses one unrefereed result, which the library re-proves itself: the zero-free half-plane
`Re s > 11/12` of OpenAI's preprints (the library follows the companion preprint). The proof's only density estimate is
Huxley's, which the library proves, and the proof uses it only for zeros of real part at least `0.7789`: below that,
the Type II estimate in two variables bounds both of its Dirichlet polynomials by orthogonality.

The proof of Theorem 1.2 uses neither Ingham's estimate nor anything from Chen, Gupta and Li's paper. Its tests are
those of Definition 5.3 with the leaves' condition (L) alone (the namespace `SieveAd.Plain`), not the leaves cut in
three of Section 9. So no module of the library's formalisation of Chen, Gupta and Li's paper is in its import cone,
and no declaration of Ingham's estimate is reachable from it (`scripts/decl_reach.py`); Ingham's zero detector is
used, in the proof of Huxley's estimate.

The proof of Theorem 1.1 uses a second unrefereed result, which the library also re-proves: Chen, Gupta and Li's
Proposition 3.1, a large values estimate for Dirichlet polynomials with characters (`LinnikCGLHB101.prop31`). It
enters twice: in the counts of the resonant window, for the powers of a prime sum, and through the second density curve
`g*` of Proposition 2.3, in the estimate for the leaves cut in three. A density curve `g` bounds by `(qT)^g(σ)`, up to
a constant and a power of `log qT`, the number of characters mod `q` whose L-function has a zero of real part at least
`σ` and height at most `T`; `g*` (`SieveCurve7D.g7d`) is made of the trivial count, Ingham's estimate, steps from
Chen, Gupta and Li's Proposition 3.1 and Huxley's estimate.

The truth of the two theorems rests on Lean's kernel, Mathlib and the pinned toolchain (with the vendored upstream
files and the provenance of Mathlib's prebuilt files, §S5), not on the preprints. Whether a Lean statement
faithfully captures a preprint's theorem matters for attribution and interpretation, not for the truth of the
theorems. Independent checking
of the half-plane result is limited: OpenAI's release has its own Lean formalisation (its catalogue
`lean/formalization.yaml` marks it "partial progress", review status "unchecked"), which is not independent of OpenAI;
the library's proof follows the companion preprint's route and is the author's formalisation, so it is not a review of
the mathematics independent of OpenAI and of the author;
and the AIProofWatch record covers the Riemann zeta function only. Chen, Gupta and Li's preprint is not refereed. The
theorems are unconditional (see [below](#checking-the-proofs)).
Their exponents are to be compared with `12/5` and `7/3`: from the half-plane, the classical deduction gives every
exponent above `12/5` with Huxley's estimate, and every exponent above `7/3` with Chen, Gupta and Li's density
estimate (their Theorem 1.2, not their Proposition 3.1). The paper's sieve brings these down to `43/20 = 2.15` and to
`21/10 = 2.1`. They are also to be compared with what the half-plane gives through Harman's theorems on primes in a
progression, which assume a zero-free region for the modulus that the half-plane supplies (the paper's Section 12).
His Theorem 2 of 2005 then gives Linnik's theorem with `1/0.472 < 2.1187` for every modulus, and his Theorem 1.2 of
2008 gives `1/0.4736 < 2.1115` for large moduli with only small prime factors. So Theorem 1.2's `43/20` is not the
smallest exponent that the half-plane gives; it is stated because its proof, from the half-plane and Huxley's
density estimate, is given in full and formalised, and because Theorem 1.1's proof builds on it. Theorem 1.1's
`21/10` is below both of the exponents that the half-plane gives through Harman's theorems. What Harman's argument
would give with this paper's inputs in the place of its own has not been examined.
The paper's exponents are not on the same footing as the
exponents `5.5` and `5` of Heath-Brown and Xylouris, whose proofs use refereed results only, while Theorem 1.2 uses one
of the two recent results and Theorem 1.1 both, through their formalisations.

## Checking the proofs

The claims table (Appendix A) names the Lean theorem behind each claim. From the repository root:

```sh
lake exe cache get                        # Mathlib's prebuilt files
scripts/build.sh                          # the default target, lib/check/Check.lean, and what it imports
python3 scripts/check_axioms.py           # the theorems of Sections 2 to 7, the literature, the deduction
scripts/build.sh CheckAll                 # lib/check/CheckAll.lean
python3 scripts/check_axioms.py --all     # the theorems of Sections 8 to 10, and more
scripts/build.sh CheckLinnik              # opt-in: lib/check/CheckLinnik.lean, with both certificates
python3 scripts/check_axioms.py --linnik  # Theorems 1.1 and 1.2, Corollary 1.3, the certificates' bounds
```

The script fails unless every theorem it prints depends only on `propext`, `Classical.choice` and `Quot.sound`.
[`docs/building.md`](../../docs/building.md) gives the memory limits and the other checks.

The certificate at `43/20` is checked by Lean's kernel in 1552 parts, in the 17
files `lib/pnt/SieveHint21500P1.lean` to `SieveHint21500P17.lean`, about 63 minutes of the kernel's time. The
certificate at `21/10` has 107374 parts, in the 1150 files `lib/pnt/SieveHint21000P1.lean` to
`SieveHint21000P1150.lean`, which the kernel checks in 128 to 349 seconds each, about 61 hours of one core in all
(Lake's build times in CI; the program that wrote the hints predicted 76), and the 29349 Buchstab steps that join the
parts are in the 58 files `lib/pnt/SieveHint21000N1.lean` to `SieveHint21000N58.lean`, 24 minutes in all. These
files are opt-in: the repository's default build and its CI on every change leave them out, and the workflow
`.github/workflows/linnik.yml` builds them in stages, with `lib/check/CheckLinnik.lean`, every week and on request.
`tools/linnik/hint_cert.py` writes both.

## Building the PDFs

To build: `latexmk -pdf main.tex`, then `latexmk -pdf supplement.tex` (pdfLaTeX, as CI does; the supplement reads the
paper's numbering from `main.aux` through `xr-hyper`). The preamble also lets XeTeX (for example
`tectonic main.tex`) compile the paper; the Lean blocks then lack some glyphs of the monospace font.

The paper's three figures are TikZ files, `fig-density.tex`, `fig-region.tex` and `fig-cost.tex`, which
`tools/linnik/fig_density.py`, `tools/linnik/fig_region.py` and `tools/linnik/fig_cost.py` write from the Lean sources
(the two density curves, the region of Definition 3.1, `SieveTwoZone7D.Zone7d`, and the pieces of the two
certificates' bounds); with `--check` a script compares
its file with what it would write. They need `pgfplots`.

## The bibliography

The paper and the supplement share their references, `references.tex`, so that each work has the same number in both;
the supplement adds three of its own. The entries were checked against the publishers', arXiv and repository pages
and, for Ingham and Huxley (1972), against scans of the originals. Xylouris's Acta Arith. 150 paper (L = 5.18) was
checked against the journal's PDF, the Lamzouri–Li–Soundararajan corrigendum against the AMS contents page (Math.
Comp. 86 (2017), 2551–2554), and Naslund's entry against its Hexagon record on 16 November 2026. The exceptions:

- Buchstab's volume, issue and pages (1937) are unverified, having been seen in secondary sources only.
- Alford, Granville and Pomerance's paper of 1994 was not read, and its publisher's page could not be reached; what
  the paper says of it is taken from Harman's papers of 2005 and 2008, which were read in full on 17 November 2026,
  and from Wright's, Lichtman's and Baier and Pujahari's citations. Both of Harman's papers print its volume as
  140; Wright's and Lichtman's reference lists give 139, as the entry does.
- Harman, Kumchev and Lewis's paper of 2004 and Lewis's thesis of 2002, on which Harman's exponent `0.472` rests,
  were not read; the paper says of them what Harman's paper of 2005 says, and their entries follow R. Li's
  reference list and that of arXiv:2303.05822.
- Banks and Shparlinski's entry and their exponent `2.1115` are taken from R. Li's and Chen, Gupta and Li's citations
  of that paper, whose published version was not read; its arXiv version, 1605.07553v2, says that it does not improve
  the Linnik exponent.
- The entries for the OpenAI preprints, OpenAI's `lean/formalization.yaml` catalogue and the AIProofWatch record are
  web pages, not refereed sources.
