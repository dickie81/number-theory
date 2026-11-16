# Secondary sources and the 2026 preprints (13 November 2026)

A follow-up to the other notes in this folder, made while the paper `papers/orbit-lattice` was fleshed out. It
covers three sources the first search could not read and a search of arXiv for 2026 preprints. Everything below comes
from reviews, abstracts, citing papers and arXiv full texts. The three older sources themselves remain unread.

## Mazhouda (2013), from its zbMATH review

K. Mazhouda, "On the Li coefficients for the Dirichlet L-functions", Monatsh. Math. 170 (2013), no. 3–4, 405–423,
[doi:10.1007/s00605-012-0436-3](https://doi.org/10.1007/s00605-012-0436-3). zbMATH review: Zbl 1326.11047 (read through
the zbMATH Open API).

- For χ primitive mod q, q > 1, the review states an arithmetic formula for λ_χ(n) in terms of Λ, χ, log q/π, γ and ζ
  values.
- **Its main results, by the review.** GRH for L(s, χ) is equivalent to an asymptotic formula for λ_χ(n). Also
  "the Riemann hypothesis for the Dirichlet L-functions holds if and only if the coefficients λ_χ(n) are increasing in
  n". The first Li coefficients are increasing unconditionally (via Bell polynomials). It also gives a probabilistic
  interpretation.
- **Citing papers** (Semantic Scholar citation contexts): papers of 2018 and 2020 on τ-Li criteria say that Mazhouda
  "investigated the non-negativity of the Li coefficients for the Dirichlet L-functions if the Generalized Riemann
  Hypothesis holds up to height T". A 2014 paper says "[12] or with Omar and Ouni [19, 20] conjectured that the Li
  coefficients for some L-functions are increasing".
- **For the paper.** This is the diagonal Li margin of `extremal_and_margin_criteria.md`, here stated as an
  equivalence: under GRH, λ_χ(n) ≥ λ_χ(1) > 0. It covers primitive χ with q > 1 only, so not ζ. It is a margin in Li's
  basis, where the pivots collapse (`scripts/ball_tests/prior_art/li_orbit.py`), not a pivot margin. The paper's
  Section 7 now says this and cites the review. Two cautions:
  - The proof is unchecked. The notes record that a related paper by the same group was retracted.
  - The citing papers describe non-negativity "up to height T", which the review does not mention. The paper may
    contain both.

## Bombieri (2003), from its review and citing papers

E. Bombieri, "A variational approach to the explicit formula", Comm. Pure Appl. Math. 56 (2003), no. 8, 1151–1164,
[doi:10.1002/cpa.10089](https://doi.org/10.1002/cpa.10089). zbMATH review: Zbl 1048.11070.

- **Review.** Weil's criterion is RH ⟺ 𝒯[f ∗ f̄*] ≥ 0, for f smooth with compact support in ℝ₊, with equality only
  for f = 0, where 𝒯 is the explicit-formula functional with its archimedean and p-adic terms. The paper considers
  "the problem of minimization of 𝒯[f ∗ f̄*] in two Hilbert spaces". It argues that if RH were false, the extremals would
  behave unusually. Most of it applies to more general L-series.
- **Coffey (2008).** "New results concerning power series expansions of the Riemann xi function and the Li/Keiper
  constants" cites two things:
  - "theorem 3.1 of Bombieri (2003)" for RH ⟺ positivity of a Weil inner product;
  - "Bombieri 2003, §8" for "positivity of the asymptotic form of an integral that may be interpreted as over Brownian
    motion on the real line".
- **Suzuki, arXiv:2606.09096 (2026)**, cites Bombieri twice:
  - Bombieri's Lagrangian ([1, Lemma 1], [2, §§5–6], with [1] the Rend. Lincei paper of 2000 and [2] the 2003 one);
  - "analogues of the infimum" of Weil's form on even and odd functions supported in [1/λ, λ] ([1, Theorem 5],
    [2, Theorem 4.4]), whose continuity in λ is "asserted, but the details of the proof are not fully provided".
- **For the paper.** Bombieri minimises Weil's form over test functions on windows, which bounds eigenvalues, the
  continuous relatives of λ_N in Section 8. As described, he does not take pivots against a first vector or consider
  integer lattices. The paper's wording, "minimisation over test functions on windows", stands.
- **A lead to check before submission.** Section 8 of Bombieri (2003) meets Brownian motion. In the paper the flat
  model (Proposition 2.5) gives the covariance of Brownian motion at integer times, min(m, n). The paper should
  compare the two once Bombieri's text is read.

## Broughan's three volumes

Crossref lists the chapters of all three volumes (`Equivalents of the Riemann Hypothesis`, Cambridge, Encyclopedia of
Mathematics and its Applications). Volumes 1 and 2 appeared in 2017
([vol. 1](https://doi.org/10.1017/9781108178228), [vol. 2](https://doi.org/10.1017/9781108178266)) and Volume 3 in
2023 ([vol. 3](https://doi.org/10.1017/9781009384780)).

- **Volume 3** has 11 chapters:
  - Nicolas's π(x) < li(θ(x)) equivalence;
  - Nicolas's number-of-divisors equivalence;
  - zero-gap estimates;
  - the Rogers–Tao equivalence;
  - Dobner's Dirichlet series;
  - the de Bruijn–Newman upper bound;
  - Pólya–Jensen;
  - Jensen polynomials (Ono et al.);
  - Gonek–Bagchi universality;
  - undecidable propositions;
  - decidability for ζ.

  None is about Weil's form, Gram matrices, Hermitian forms or lattices, so Volume 3 is unlikely to contain (A) or (B).
- **Volume 2** has the chapters where an older criterion of this kind would be catalogued:
  - Banach and Hilbert space methods;
  - orthogonal polynomials;
  - Weil's explicit formula, inequality and conjectures;
  - discrete measures;
  - Hermitian forms (likely Yoshida's).

  These are still unread, and they remain the largest unread source.

## arXiv, 2024–2026

arXiv API searches on 13 November 2026, sorted by submission date and kept from June 2024 on:
- abstracts containing "Weil quadratic form";
- abstracts containing "Weil positivity";
- "Riemann hypothesis" together with "Schur complement", "Gram-Schmidt", "Gram matrix", or lattice and "shortest
  vector";
- "Riemann hypothesis" with "Dirichlet polynomials", zeros and positive;
- "screw function".

The four pairings of RH with Schur complements, Gram–Schmidt, Gram matrices or shortest vectors returned nothing in
that period. The hits:

- **R. Andrews, A. Connes, A. La Gatta**, "The uncertainty operator, the Weil ground state and the zeros of zeta: a
  numerical study and conditional positivity of the Weil quadratic form", [arXiv:2611.13129](https://arxiv.org/abs/2611.13129)
  (9 November 2026, 57 pp.). Read in its arXiv text for the parts that touch the paper. Its object is Weil's form QW_λ
  on L²([λ⁻¹, λ], d*u), with the primes p ≤ λ², and its minuscule eigenvalues, which follow Fuchs's prolate ladder.
  - *Numerically.* The Gram–Schmidt vectors built from the images of zero-integral prolate functions under
    E(f)(u) = u^{1/2}Σf(nu) reproduce the minuscule eigenvectors. Conditioning the form by them and by the pole
    functional leaves it bounded below by about 2/λ.
  - *Theorem 8.14*, under a hypothesis (H2′) on the semilocal cutoff projections: QW_λ ≥ ½ log σ·‖f‖² on the orthogonal
    complement of an explicit finite-dimensional space. They call this "positivity with a margin on an explicit
    subspace".
  - *Lemma 8.16* is a Schur-complement lemma: Q ≥ 0 if and only if S ≥ 0 on V.
  - *Proposition 8.18*, under (H2′), (R1) and (R2): RH follows if the Schur complement on a block of dimension
    O(Aσ² log λ) + 2 has λ_min ≥ −η(λ) → 0.

  This is the closest work in method: a margin of Weil's form and Schur complements. The differences:
  - the test functions are general functions on a window, where (A) and (B) concern the orbit's vectors. On the
    hyperplane Σ xₙ = 0 those are step functions in the window at λ = √N (`OrbitWindow.form_eq_weilQg`, proved after
    this note was written);
  - the conditioning is by prolate and pole directions, not along the orbit's own order;
  - the results are conditional and aim at proving positivity, where (A) and (B) are unconditional equivalences;
  - there are no lattices.

  The paper now cites it in Sections 1 and 7.
- **M. Suzuki**, "Weil's quadratic form via the screw function", [arXiv:2606.09096](https://arxiv.org/abs/2606.09096)
  (June 2026). An operator-theoretic frame, through the screw function, for the results of Yoshida, Bombieri,
  Connes–Consani and Connes–Consani–Moscovici, with a conjecture on self-adjoint operators on [−a, a] that would
  converge to the ordinates of the zeros. Its full text contains no Gram matrix, Schur complement, pivot or lattice. It
  is cited in Section 7.
- **M. Suzuki**:
  - "Spectral convergence associated with Weil's quadratic form", [arXiv:2610.32704](https://arxiv.org/abs/2610.32704);
    under RH, the eigenvalues of a local self-adjoint extension converge to the ordinates of the zeros;
  - "A spectral theory of zeta functions of function fields", [arXiv:2610.41115](https://arxiv.org/abs/2610.41115).

  Both are continuous and spectral. Not cited.
- **A. Groskin**:
  - "High-precision approximation of Riemann zeros via the truncated Weil form", [arXiv:2605.20224](https://arxiv.org/abs/2605.20224);
  - "A finite Guinand–Weil dictionary and archimedean tail order for the truncated Weil quadratic form",
    [arXiv:2607.02828](https://arxiv.org/abs/2607.02828).

  These compute the Connes–van Suijlekom and Connes–Consani–Moscovici Galerkin matrices. The second certifies their
  positivity by an interval LDLᵀ factorization, whose pivots are positivity certificates in a Fourier basis on an
  interval, not a margin, and it "makes no Riemann Hypothesis … claim". Not cited; it could be, as the nearest use of
  pivots.
- **T. Kim et al.**, a numerical realisation of Suzuki's operator, [arXiv:2607.24830](https://arxiv.org/abs/2607.24830).
  Not cited.
- **M. Desogus**, "The Three Gates: A Rooted-Operator Approach to Weil Positivity",
  [arXiv:2609.20367](https://arxiv.org/abs/2609.20367). It claims Weil positivity in an odd channel by "Schur
  induction" and certified computation. Unrefereed, and its abstract does not make a mainstream claim checkable from
  the abstract alone. Not cited.
- **A. Connes**, "The Riemann Hypothesis: past, present and a letter through time",
  [arXiv:2602.04022](https://arxiv.org/abs/2602.04022), J. Open Math. Problems 2 (2026). A survey. Not cited.

The truncation programme of Connes and his collaborators is cited in the paper only through Andrews–Connes–La Gatta and
its references:
- Connes–Consani–Moscovici, "Zeta zeros and prolate wave operators", arXiv:2310.18423;
- Connes–Consani–Moscovici, "Zeta spectral triples", arXiv:2511.22755;
- Connes–van Suijlekom, "Quadratic forms, real zeros and echoes of the spectral action", arXiv:2511.23257.

## The bibliography check

Each entry was checked on the same day:
- the journal articles against Crossref, by title and DOI;
- Weil 1952 (Zbl 0049.03205), Bombieri 2000, Báez-Duarte 2003, Conrey–Li and Yoshida against zbMATH Open;
- every arXiv number against arXiv.

Corrected:
- Matsumoto–Suzuki's published title is "M-functions and screw functions: applications to Goldbach's problem and zeros
  of the Riemann zeta-function"; the arXiv title differs.
- Lamzouri's paper appeared in J. Math. Anal. Appl. 432 (2015), 632–653.
- Conrey–Li is IMRN 2000, no. 18, 929–940.

Also noted:
- Hallouin–Perret's arXiv:1409.2357 carries a different title, "From Hodge index theorem to the number of points of
  curves over finite fields". Its abstract describes the same work as the TAMS paper.
- Dimitrov–Oliveira has no journal version on zbMATH, which lists the arXiv preprint only.
