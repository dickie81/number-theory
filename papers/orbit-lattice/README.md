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

Appendix A names the Lean theorem behind each numbered result. `lib/check/Check.lean` prints their axioms, which are
`propext`, `Classical.choice` and `Quot.sound` only. Two computations are checked by kernel evaluation (`decide
+kernel`):
- the interval certificate of the archimedean minorant (`PivotCert.mu_le`);
- `lcm(1, …, n) ≤ 3ⁿ` for `n ≤ 2000`, behind the Mertens bound (`PivotTop`).

[`formalisations/ball-rate.md`](../../formalisations/ball-rate.md) documents the Lean proofs, section by section.

## What is not a Lean theorem

These parts of the paper are not formalised:
- the remarks, including the numerical values of §3.1;
- Section 6 on the analogues, except the density of real characters with `d₂ < d₁`. That density is
  `D2Good.d2_density_pos_closed` and `d2_density_neg_closed`, and its proof uses the library's formalisation of the
  zero-free half-plane of an unrefereed preprint;
- the conjecture `λ_N ~ 0.0429·log N/N` and the questions of Section 8;
- the historical and comparative statements.

The analogues are computed by [`scripts/ball_tests/`](../../scripts/ball_tests/README.md). Their write-up is
[`docs/ball-conjecture-tests.md`](../../docs/ball-conjecture-tests.md).

The paper claims only its own steps, the margin and the equivalences it gives. Several layers come from the
literature, and the paper credits them:
- The positivity layer, RH ⟺ every `G_N ⪰ 0`, is in substance Matsumoto and Suzuki's screw-function theorem.
- Its `2 × 2` case is Nicolas's.
- The constant `K_H(1)` is Burnol's, and Gun, Murty and Rath's.
- Weil's explicit formula, which the library proves.

## State

A first draft, of 13 November 2026. What remains:
- **The proofs of Section 4.** Lemmas 4.2, 4.4, 4.5 and 4.7 and Proposition 4.8 have sketches only, to be written out
  in full. The Lean proofs are complete, and `formalisations/ball-rate.md` has the details.
- **The novelty statements of Sections 1 and 7.** The literature check could not read three sources: Bombieri (2003),
  Broughan's *Equivalents of the Riemann Hypothesis* and Mazhouda (2013). The statements are final only once those
  are read.
- **Section 8.** Whether the smallest eigenvalue stays in this paper.
- **The bibliography.** It is to be checked against the publishers' pages. Weil (1952) was not consulted, and
  `references.tex` records the state of each entry.

## Building

Run `latexmk -pdf main.tex`. This is pdfLaTeX, as CI uses.
