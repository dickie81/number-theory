# A margin in Weil's criterion: the Riemann hypothesis as a lattice minimum

Read it: [the paper (PDF)](https://dickie81.github.io/number-theory/orbit-lattice.pdf), rebuilt from `main` on every
push once the paper is on `main`.

`main.tex` is the paper. Its eight sections are:
1. the introduction;
2. the kernel `K_H`, the orbit and the two forms;
3. the main results;
4. the proof of the margin;
5. the formalisation;
6. the analogues (curves over finite fields, the Frobenius orbit, Dirichlet characters, Li's basis);
7. related work;
8. the smallest eigenvalue of `G_N`, and questions.

Appendix A is the claims table. `references.tex` is the bibliography, which follows the literature report
[`reports/Orbit lattice criterion prior art.md`](../../reports/Orbit%20lattice%20criterion%20prior%20art.md).

## The theorems

The main theorems are `PivotSharp.rh_iff_orbitLattice` and `PivotSharp.rh_iff_shortest` in `lib/core/PivotSharp.lean`.
Neither has a hypothesis:
- RH holds if and only if every Gram–Schmidt pivot of the orbit is at least the first;
- RH holds if and only if `w_1` is a shortest nonzero vector of the lattice the orbit spans.

The orbit's Gram matrix `√(mn)·K_H(m/n)` in their statements is computed from the primes (`BallWeil.gram`, through
`BallPsi.kerH_explicit`). Their content is the margin `PivotSharp.pivot_ge_rh`: under RH every pivot after the first is
at least `(999/1000)(2/45)(13/10) = 0.05772`, against `K_H(1) = 0.04619`.

Proposition 2.3 places the orbit in the windows of Connes and his collaborators. On `Σ x_n = 0`, the orbit form is Weil's
form on the step functions `u^{1/2}Σ_n x_n 1_{(0, n]}(u)` of the window `[λ⁻¹, λ]`, `λ = √N`
(`OrbitWindow.form_eq_weilQg`, no RH input). Corollary 3.3 then reads the margin in that window: Weil's form is
`≥ 0.0577` at every nonzero integer-valued step function.

Appendix A names the Lean theorem behind each numbered result. `lib/check/Check.lean` prints their axioms, which are
`propext`, `Classical.choice` and `Quot.sound` only. Two computations are checked by kernel evaluation (`decide
+kernel`):
- the interval certificate of the archimedean minorant (`PivotCert.mu_le`);
- `lcm(1, …, n) ≤ 3ⁿ` for `n ≤ 2000`, behind the Mertens bound (`PivotTop`).

[`formalisations/ball-rate.md`](../../formalisations/ball-rate.md) documents the Lean proofs, section by section.
[`scripts/pivot_constants.py`](../../scripts/pivot_constants.py) replays every number of Section 4 in exact rational
arithmetic, including the 1181 cells of the certificate, for readers without Lean.

## What is not a Lean theorem

These parts of the paper are not formalised. They are proved in the text or computed:
- the remarks, including:
  - the upper bound for the pivots in §3;
  - the numerical values of §3.1;
  - those of the remark "How the hyperplane sits" at the end of §2, which come from
    [`scripts/window_hyperplane.py`](../../scripts/window_hyperplane.py);
  - the numerics of Section 8;
- Section 6 on the analogues, except the two limits of the density of real characters with `d₂ < d₁`, one for each sign
  of `D`. They are `D2Good.d2_density_pos_closed` and `d2_density_neg_closed`, whose Lean proofs use the library's
  formalisation of the zero-free half-plane of an unrefereed preprint; the paper cites them as conditional on it. The
  paper's own argument is Lamzouri's, whose approximation step uses Heath-Brown's zero-density estimate instead, and it
  gives the positive proportion of the abstract from Lamzouri's published theorem alone;
- the conjecture `λ_N ~ c·log N/N`, with `c ≈ 0.043` numerically, and the questions of Section 8;
- the historical and comparative statements.

The paper is self-contained apart from its citations of other papers and preprints. It points to the repository only
for code: the Lean theorems and the scripts behind its numerical remarks.

The analogues are computed by [`scripts/ball_tests/`](../../scripts/ball_tests/README.md). Their write-up is
[`docs/ball-conjecture-tests.md`](../../docs/ball-conjecture-tests.md).

The paper claims only its own steps, the margin and the equivalences it gives. Several layers come from the
literature, and the paper credits them:
- The positivity layer, RH ⟺ every `G_N ⪰ 0`, is in substance Matsumoto and Suzuki's screw-function theorem.
- Its `2 × 2` case is Nicolas's.
- The constant `K_H(1)` is Burnol's, and Gun, Murty and Rath's.
- Weil's explicit formula, which the library proves.

## State

A draft, of 13 November 2026. What remains:
- **The acknowledgements.** They are general.
- **Reading before submission.** Several sources are known only from reviews, abstracts and citing papers:
  - Mazhouda (2013), whose review states that GRH for `L(s, χ)`, `q > 1`, is equivalent to Li's coefficients
    increasing;
  - Bombieri (2003), whose §8 meets Brownian motion, as the flat model of Proposition 2.5 does;
  - the chapters of Broughan's Volume 2 on Weil's explicit formula, discrete measures and Hermitian forms.

  [`secondary_sources_2026.md`](../../research_notes/Orbit%20lattice%20criterion%20prior%20art/secondary_sources_2026.md)
  records what those accounts say. It also covers the 2026 preprints, among them Andrews, Connes and La Gatta's
  (arXiv:2611.13129), the closest work in method, which Sections 1 and 7 discuss.

Done since the first draft:
- The proofs of Section 4 are complete.
- The bibliography was checked against Crossref, zbMATH Open and arXiv; `references.tex` records the corrections.
- The paper is self-contained. Proposition 2.1, the pivot upper bound of §3 and the density remark of §6 now carry their
  proofs.
- After a hostile review:
  - Proposition 2.2 has its proof, by Landau's theorem;
  - the proof of Theorem 3.1 no longer uses a false inequality;
  - the abstract states the equivalences for `G_N`, whose Gram realisation by the `w_n` needs RH;
  - Binet's remainder and Lemma 4.7 are proved from citations, with the Lean routes stated;
  - statements equivalent to RH say "under RH";
  - the hygiene sentence excepts the vendored libraries.

  The review's framing points, for the abstract, the introduction and Section 6, are drafted separately.
- Results whose proofs are only in the library are out. Each rests on the sampling theorem at the zeros and the
  bounds for `λ_N`, which would roughly double the paper:
  - the pivot growth `d_N ≫ log N` under RH (`BallPivot.pivot_ge`);
  - the bounds `√log N/(220e⁸N) ≤ λ_N ≤ 67(1 + log N)/N` under RH, and `λ_N ≪ log N/N` without it (`BallGap.rate_gap`,
    `BallUpperEta.rate_upper_rh`, `rate_upper`);
  - the window bound `OrbitWindow.weilQg_step_ge`;
  - the paper proof of `λ_N ≤ (0.04294 + o(1))·log N/N`.

  They could make a second paper. Section 8 keeps the conjecture and the numerics.

## Building

Run `latexmk -pdf main.tex`. This is pdfLaTeX, as CI uses.
