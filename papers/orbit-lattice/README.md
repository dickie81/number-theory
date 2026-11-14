# A margin in Weil's criterion

Read it: [the paper (PDF)](https://dickie81.github.io/number-theory/orbit-lattice.pdf), rebuilt from `main` on every
push once the paper is on `main`.

`main.tex` is the paper. Its eight sections are:
1. the introduction;
2. the kernel `K_H`, the orbit and the forms (A), (B) and (B′);
3. the main results;
4. the proof of the margin;
5. the formalisation;
6. the analogues (curves over finite fields, the Frobenius orbit, Dirichlet characters, Li's basis);
7. related work;
8. the smallest eigenvalue of `G_N`, and questions.

Appendix A is the claims table. `references.tex` is the bibliography, which follows the literature report
[`reports/Orbit lattice criterion prior art.md`](../../reports/Orbit%20lattice%20criterion%20prior%20art.md).

## The theorems

The main theorem, Theorem 1.1, is the margin `PivotSharp.pivot_ge_rh` in `lib/core/PivotSharp.lean`. Under RH,
`Q_N(x) ≥ c₀·x_N²` for every `N ≥ 2` and every real `x`, with `c₀ = (999/1000)(2/45)(13/10) = 0.05772`, against
`K_H(1) = 0.04619`. So every pivot after the first is at least `c₀`.

Corollary 1.2 states its consequences as equivalences, `PivotSharp.rh_iff_orbitLattice` and `PivotSharp.rh_iff_shortest`.
Neither has a hypothesis:
- RH holds if and only if every Gram–Schmidt pivot of the orbit is at least the first;
- RH holds if and only if the form is at least `K_H(1)` at every nonzero integer vector, which under RH makes `w_1` a
  shortest nonzero vector of the lattice the orbit spans.

The orbit's Gram matrix `√(mn)·K_H(m/n)` in their statements is computed from the primes (`BallWeil.gram`, through
`BallPsi.kerH_explicit`). The threshold `K_H(1)` is a choice. Given positivity, a uniform lower bound `ε` for the pivots
is equivalent to RH for every `ε ∈ (0, K_H(1)]`, and `K_H(1)` is the value at which the statement becomes a lattice
minimum.

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
[`scripts/pivot_constants.py`](../../scripts/pivot_constants.py) replays the numbers of Section 4 for readers without
Lean: in exact rational arithmetic, including the 1181 cells of the certificate, except the top vertex's rooms and prime
terms, which it computes in floating point.

## What is not a Lean theorem

These parts of the paper are not formalised. They are proved in the text or computed:
- the remarks, including:
  - the upper bound for the pivots in §3;
  - the numerical values of §3.1;
  - those of the remark "How the hyperplane sits" at the end of §2, which come from
    [`scripts/window_hyperplane.py`](../../scripts/window_hyperplane.py);
  - the numerics of Section 8;
- the numerical values quoted in the introduction, among them the comparison of the pivots for six densities of zeros,
  which shows that the scarcity of zeros below height about `2π`, not the growth of their density, makes the pivots
  exceed the first at `k = 2` (`scripts/ball_orbit.py --densities`);
- the equivalence of the lattice form (B′) with RH, which the text derives from Proposition 2.2 and Corollary 1.2;
- Section 6 on the analogues. Its density remark follows Lamzouri, whose approximation step uses Heath-Brown's
  zero-density estimate, and gets the positive proportion of the abstract from his published theorems. The repository
  also proves the two limits for each sign of `D` in Lean, `D2Good.d2_density_pos_closed` and `d2_density_neg_closed`;
  their proofs use the library's formalisation of the zero-free half-plane `Re s > 11/12` of an unrefereed preprint, an
  extraordinary claim, and the paper does not rely on them;
- the conjecture `λ_N ~ c·log N/N`, where a fit suggests `c ≈ 0.043`, and the questions of Section 8;
- the historical and comparative statements.

The paper is self-contained apart from its citations of other papers and preprints. It points to the repository only
for code: the Lean theorems and the scripts behind its numerical remarks.

The analogues are computed by [`scripts/ball_tests/`](../../scripts/ball_tests/README.md). Their write-up is
[`docs/ball-conjecture-tests.md`](../../docs/ball-conjecture-tests.md).

The paper claims only its own steps, the margin and the equivalences it gives. Several layers come from the
literature, and the paper credits them:
- The positivity layer, RH ⟺ every `G_N ⪰ 0`, is in substance Matsumoto and Suzuki's screw-function theorem.
- Its `2 × 2` case is noted by Nicolas under RH. Its lower half alone, `K_H(r) ≥ −K_H(1)` at the rationals, is already
  equivalent to RH (Proposition 2.2, `BallWeil.rh_iff_weil_bound`).
- The value of `K_H(1)` is classical; RH ⟺ `Σ_ρ 1/|ρ|² = K_H(1)` is Burnol's remark, also proved by Gun, Murty and Rath.
- Weil's explicit formula, which the library proves.

## State

A draft, of 13 November 2026. What remains:
- **The acknowledgements.** They are general.
- **Reading before submission.** Several sources are known only from reviews, abstracts and citing papers:
  - Mazhouda (2013), whose review states that GRH for `L(s, χ)`, `q > 1`, is equivalent to Li's coefficients
    increasing;
  - Bombieri (2003), whose §8 meets Brownian motion, as the flat model of Proposition 2.5 does;
  - the chapters of Broughan's Volume 2 on Weil's explicit formula, discrete measures and Hermitian forms;
  - the sources of the method that Section 7 and Lemma 4.1 cite: Landau (1912) and Gonek (1993) for Landau's formula,
    Fujii (1989), Montgomery–Odlyzko (1984) and Conrey–Ghosh–Gonek (1984) on gaps between zeros, and Iwaniec–Kowalski's
    Theorem 5.12.
    They are cited from Goldston–Gonek (2007), whose Lemma 1 was checked against Lemma 4.1 term by term, from Bui,
    Milinovich and Ng (arXiv:0910.2052) and from Goldston's survey (arXiv:math/0412313).

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

  Then its framing points:
  - the title drops "the Riemann hypothesis as a lattice minimum";
  - the abstract and the introduction lead with the margin, now Theorem 1.1, with the equivalences as Corollary 1.2;
  - the flat model is described as a constant density;
  - Section 6 tests the lattice form (B′). (A) fails for every curve, and (B′) for 43 of the 148 sampled, on the
    indices tested. The two forms part for complex characters.
- The method's sources are cited: Guinand and Goldston–Gonek's Lemma 1 for the explicit formula in the form of Lemma
  4.1, Landau and Gonek for Landau's form, and in Section 7 Montgomery, Montgomery–Odlyzko, Conrey–Ghosh–Gonek, Vaaler
  and Carneiro–Milinovich–Soundararajan.
- After a second hostile review:
  - Lemma 4.1, the explicit formula, has the standard contour proof: no cited source proves it for test functions whose
    transform is not smooth, as none of the paper's is;
  - the margin is attributed to the gap below the first zeros, not to the growth of their density, which the first
    round had wrongly concluded from a comparison that changed both at once;
  - Andrews, Connes and La Gatta's eigenvalue rate is stated as their upper bound;
  - the per-sign density limits are no longer claimed as Lean theorems;
  - the equivalences are Corollary 1.2, and the lattice form (B′) is defined;
  - the second minimum is settled for every `N ≤ 10⁴` by the certificate;
  - credit and wording are corrected (the Nyman–Beurling distance, Báez-Duarte–Balazard–Landreau–Saias, Fujii,
    Dimitrov–Oliveira, Connes–Consani, Gun–Murty–Rath, the value of `d₁`), and the classical formulas are cited to the
    DLMF;
  - "What is new", the uncertified 1.449 remark and repeated statements are cut.
- After a third hostile review:
  - the bibliography no longer prints an uncited, unrefereed preprint on a zero-free half-plane;
  - Section 7 credits Conrey, Ghosh and Gonek's bound on the weighted Landau form for every choice of coefficients (as
    Bui, Milinovich and Ng report), and says what is new: an identity exact at every `N`, and Schur's test at the top
    vertex leaving `(13/10)c_N²` to spare;
  - Corollary 3.2 covers `a = mδ₁`, `|m| ≥ 2`, in the text and in Lean (`PivotSharp.lattice_second`, with
    `PivotSharp.gram_one_gt`: `K_H(1) > 1/50`);
  - Proposition 2.2 also states that `K_H(r) ≥ −K_H(1)` at the rationals is equivalent to RH, which its proof already
    showed (`BallWeil.rh_iff_weil_bound`);
  - the claims table lists the Lean theorems behind the equality in Proposition 2.5, the convergence in Proposition 2.1,
    and the hypothesis of `PivotSharp.form_ge`; Section 5 lists the remaining statements that are not Lean theorems;
  - the density comparison describes its controls correctly. Two are added: a gap up to the first zero, and a density
    with no gap that is small near height 0. What sets the pivots at `k = 2` is the scarcity of zeros below height
    about `2π`;
  - credit is corrected for Andrews–Connes–La Gatta (the eigenvalue bound is Kastoris's and Connes–Kastoris's, and
    their reduction leaves an estimate open), Yoshida (the spaces of his results, and his Lemma 3 as the earlier margin
    of that shape), Connes–Consani (support in `(1/2, 2)`, after Yoshida), Fujii, Báez-Duarte–Balazard–Landreau–Saias
    (distinct zeros), Dimitrov–Oliveira, Nicolas, Matsumoto–Suzuki, Kreĭn–Langer, Mazhouda, the DLMF names and
    Szegő's theorem; Groskin's pivot certification of truncated Weil forms is cited;
  - the window factor of Section 8 grows like `√log N`, the fitted constant depends on the law fitted, the per-sign
    density limits are marked as a sketch, and the notation and wording are tidied.
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
