# Chen–Gupta–Li's zero-density estimate on `[5/7, 16/21]`

**Lean:** `LinnikCGLDensity.cglDensity` (`lib/pnt/LinnikCGLDensity.lean`) proves `LinnikCGL.CGLDensity`
(`lib/pnt/LinnikCGL.lean`):

```lean
def CGLDensity : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (σ T : ℝ), 5 / 7 ≤ σ → σ ≤ 16 / 21 → 2 ≤ T →
    ((Finset.univ.filter fun χ : DirichletCharacter ℂ q =>
      ∃ s : ℂ, σ ≤ s.re ∧ |s.im| ≤ T ∧ LFunction χ s = 0).card : ℝ) ≤ C * ((q : ℝ) * T) ^ (7 / 3 * (1 - σ) + ε)
```

In words: for every `ε > 0` there is `C` such that, for every `q ≥ 1`, `5/7 ≤ σ ≤ 16/21` and `T ≥ 2`, at most
`C(qT)^{(7/3)(1−σ)+ε}` characters mod `q` have an `L`-function with a zero in `Re s ≥ σ`, `|Im s| ≤ T`.
`LFunction` is Mathlib's `DirichletCharacter.LFunction`. The theorem depends on `propext`, `Classical.choice` and
`Quot.sound` only (`lib/check/CheckAll.lean`).

## Attribution

The estimate is B. Chen, V. Gupta and Y. C. Li's: "Large value estimates for Dirichlet polynomials with characters
and zero density of Dirichlet `L`-functions", arXiv:2507.08296v2 (27 July 2026). Version 1 (11 July 2025) was
B. Chen's alone. Their abstract states `Σ_{χ mod q} N(σ, T, χ) ≪_ε (qT)^{7(1−σ)/3+ε}`, and "The exponent 7/3
improves upon Huxley’s earlier exponent of 12/5". Their method is Guth and Maynard's (Ann. of Math. 203 (2026),
623–675; arXiv:2405.20552).

The proof formalised here is theirs. Nothing in this library claims the estimate, or its proof, as its own.

**Scope.** The library formalises their Proposition 3.1 at one point per character (`LinnikCGLHB101.prop31`) with the
results it rests on (Propositions 4.6, 6.1, 8.1 and 11.1 and Theorem 10.1, see below), and derives from it the steps
`LinnikCGLSteps.charDensity_s0` … `charDensity_s29` of the Linnik paper and the estimate `CGLDensity` below. It does not
formalise their Theorem 1.2 beyond the range `[5/7, 16/21]` (nor `[5/7, 131/168]` as a single statement), their Theorem
1.1, or the other parts of their paper. Some of what it does formalise was read only in outline (list below). The Lean
statements are the library's own, and the kernel checks their proofs, not that they faithfully capture the preprint's
theorems.

## What the formalisation here is

The formalisation follows the paper. It was read from the PDF's text layer:

- **in full:** §§1–7, §8 (Proposition 8.1, and Lemma 8.2 with its proof), §9, §11.2, and §§12.1, 12.2 and 12.4;
- **statements and early lemmas:** §10's statements and Lemmas 10.4–10.6, and §12.3 up to the statement of Lemma
  12.1;
- **in outline only:** Lemmas 10.7–10.10 and the proof of Proposition 10.2, §11.1, and the proof of Lemma 12.1.

The text layer drops the bar over `χ₂` in the statement of Theorem 10.1 (p. 40). The PDF has it, and so does
`LinnikCGLT101.CGLT101`.

The chain in Lean is as follows.

- **The density count from the large values** (their §12). `LinnikCGLStep.charDensity_cglGen` derives it from their
  Proposition 3.1 at one point per character. With the step's internal `ε` free, it gives the count at the exponent
  `(7/3 + 26e)(1 − σ)` with the factor `(log qT)^{10}` (`LinnikCGLDensity.charDensity_e`).
- **Their Proposition 3.1 at one point per character** (`LinnikCGLHB101.prop31`). Its inputs are:
  - their Proposition 4.6 (`LinnikCGLMat.prop46`);
  - their Proposition 6.1, the bound on `S₂` (`LinnikCGLS2.cgls2`);
  - their Proposition 11.1, the bound on `S₃` (`LinnikCGLHB101.cgls3`), with §§7–10 behind it.
- **Their Proposition 8.1** (`LinnikCGLP81.cglp81`), by their downward induction on `ε` from Lemma 8.2.
- **Their Theorem 10.1, Heath-Brown's bound for double sums with characters** (`LinnikCGLHB101.cglt101`). See below.
- **Ending at `CGLDensity` itself.** `cglDensity` takes the step's internal `ε` to `0` and absorbs the factor
  `(log qT)^{10}` into `(qT)^ε`.

The formalisation is in `lib/pnt`, in the modules whose names begin with `LinnikCGL`.

## Differences from the source

- **Characters, not zeros.** The source bounds `Σ_χ N(σ, T, χ)`, the number of zeros. The Lean statement bounds the
  number of characters with a zero, which is at most that sum. So the source implies the Lean statement, and not the
  other way round. Counting characters lets every large-values set carry one point per character, which is the form
  the density count uses. The lemmas behind it hold for several points per character, as long as the points of each
  character are separated: their Propositions 4.6 and 6.1 and Theorem 10.1 (`CGLT101`) for points at least `1` apart,
  and Lemmas 10.5, 10.6, 10.9 and 10.10 and Proposition 10.2 for points more than `2` apart (`LinnikCGLL105.Spaced`);
  Lemma 10.7 (`LinnikCGLL107.lemma107`) needs no separation. One point per
  character is a case of both, and at `q = 1` the general form gives Guth and Maynard's large values estimate
  (`ZetaGMLV.gm_large_values`).
- **The range.** The source's Theorem 1.2 holds for `1/2 < σ < 1`. Their §12 says that "Theorem 1.2 follows from
  Ingham’s result (1.4) when σ ≤ 0.7 and Huxley’s result (1.5) when σ ≥ 0.8", so the paper's own argument is needed
  only on `[0.7, 0.8]`. The Lean statement covers only `[5/7, 16/21]`, which lies inside `[0.7, 0.8]`. The Linnik
  paper uses Proposition 3.1 on `[5/7, 131/168]`, also inside `[0.7, 0.8]`, through its steps (below).
- **Their Theorem 1.1 is not formalised.** The step needs the large-values count only at `V = N^σ/Z` with
  `5/7 ≤ σ ≤ 16/21`. That lies inside Proposition 3.1's range `[N^{7/10}, N^{4/5}]`, where the paper's reduction is
  the three-part split of the polynomial alone (`LinnikCGLLV.lv_range`). The subdivision in `T`, the mean value
  theorem and Huxley's estimate, which their proof of Theorem 1.1 uses, are not needed.
- **Explicit constants and extra factors.** Several of the paper's `≪` and `⪅` bounds are stated in Lean with
  explicit constants. Where the Lean form carries an extra factor, the factor is absorbed by `(qTN)^ε`. For example,
  the Ramanujan-sum bound is used as `|C_q(n)| ≤ d(q)(n, q)` where the paper has `(n, q)`.
- **The cut-off in `ξ`.** Their proof of Lemma 8.2 splits the integral of `Σ_a|ĝ_a(ξ)|²` at `|ξ| = (qT)²` and
  discards `|ξ| > (qT)²` by the decay of `Σ_b|f̂_b|` (p. 29). The library's bound on that range (`LinnikCGLTail`) is
  the same argument with a cut-off `X` in place of their `(qT)²`, and `LinnikCGLForm` takes `X = (qT)³`.
- **Lemma 10.8 is not formalised as stated.** `LinnikCGLSep.sum_cube_le` does its part in the proof of Lemma 10.9.

## Corrections to the source

The formalisation found seven places where the paper's text needs a small repair. None of them affects the paper's
results.

- **Proposition 7.1.** The Cauchy–Schwarz step in the proof of Proposition 7.2 bounds an integral over `v₂` by
  `R̃_{M₂}` (their (7.5), p. 24), whose integral runs over `[1/2, 2]` only. So the step needs the integrand restricted
  to `v₂/v₁ ∈ [1/2, 2]`, which Proposition 7.1 as stated does not give. The restriction holds because the kernel `J`
  vanishes unless `v₂/v₁ ∈ (1/2, 2)` (`LinnikCGLSym.Jk_eq_zero_of_ratio`). The library's form of Proposition 7.1
  includes it (`LinnikCGLSym.prop71r`); Proposition 7.1 as they state it, at one point per character and with
  explicit constants, is `LinnikCGLP71.prop71`.
- **The proof of Proposition 7.2 (p. 26).** After the substitution `u′ = v₂/v₁`, a display omits the factor
  `√v₁ ≤ √2` that comes from `dv₂ = v₁du′`. The next line is stated with `≪_ϵ`, which absorbs it (`LinnikCGLRt`).
- **The proof of Lemma 8.2 (p. 28).** The affine change of variables in `ĝ_a` prints the factor `m₂/m₁`, which has
  the wrong sign when `m₁ < 0`; it should be `m₂/|m₁|`. Only `|ĝ_a|²` is used afterwards, so nothing changes. The
  library has `m₂/|m₁|` (`LinnikCGLNsum.Fb`, `LinnikCGLG.fourier_comp_affine`).
- **The proof of Lemma 9.2 (p. 39).** After the change of variables `v = e^τ`, the majorized integral in the display
  carries the Jacobian `e^τ`, and the identity that follows drops it. If it is kept, `e^τ` grows like `e^{(qT)^ϵ}` on
  the support of the majorant. The library bounds `e^τ ≤ 2` on the original range `|τ| ≤ log 2` before majorizing,
  at the cost of a factor `2` (`LinnikCGLMom4.lemma92`).
- **Remark 10.3 (p. 40).** The remark holds as stated, strictly and with the constant `1`, since `E(W) ≤ |W|³`.
  The slip is in the chain of inequalities given for it. Its step `(qT)³|W|³N^{−3} < qT|W|³` needs `N³ > (qT)²`, which
  fails for `(qT)^{2/3}/2 ≤ N ≤ (qT)^{2/3}`. The library proves the remark directly (`LinnikCGLCase.remark103`),
  without assuming `E ≤ |W|³` and with the constant `8`, which is then attained.
- **The bump `ψ` of §11 (p. 48).** To bound `S₃,₄` they apply Proposition 8.1 to `f_b(v) = ψ(v)|R̃_{M₂}(v, −b)|²`,
  "where ψ(v) is a smooth bump function supported on v ≍ 1 and such that ψ(1) > 0" (p. 48). Comparing `S₃,₄` with
  `J(f⃗)` term by term needs `f_{−b} ≥ R̃_{M₂}(·, b)²` at every centre `(m₁v + m₃)/m₂`. The centres include points
  near `0`, where such a `ψ` vanishes and `R̃_{M₂}` need not. On the library's dyadic blocks the centres lie in
  `[−3, 3]`, and the library takes for `ψ` Mathlib's smooth bump with radii `3` and `4`, which is `1` on `[−3, 3]`
  (`LinnikCGLFb.psiW`, `LinnikCGLFb.Rt_sq_le_fb`, `LinnikCGLJ.S34_le_Jint`).
- **The change of variables `u = v⁻¹` in §11 (p. 48).** It takes `(m₁v + m₃)/(m₂v)` to `(m₁ + m₃u)/m₂`, the form
  Proposition 8.1 needs, but the displays that follow print the denominator as `m₂u`. The library's bound on `S₃,₃`
  uses `(m₁ + m₃u)/m₂` (`LinnikCGLJ.S33_le_S34`).

## An audit of the chain (8 November 2026)

An independent pass over the chain from `cglDensity` down, looking for anything that could make the theorem say less
than it appears to, or rest on more than it should.

- **Axioms.** CI's Lean build on `f89aa26`, a cold build of every library with `autoImplicit` and
  `relaxedAutoImplicit` off (below), and on `5dac8f3`, after the documentation fixes (below), reports
  `[propext, Classical.choice, Quot.sound]` for `cglDensity`, `charDensity_e`, `parCGLe_good` and `prop31`, as it
  does on `main` at `b48f5a3`. Its gate `scripts/check_axioms.py`,
  which elaborates each check file afresh, finds every report within those three: 146 of 146 in `Check.lean`, 1206 of
  1206 in `CheckAll.lean`, 34 of 34 in `CheckZeta23.lean` and 71 of 71 in `CheckDH.lean`. A local build of
  `LinnikCGLDensity` from `bb094dc` (`scripts/build.sh`, Mathlib from its cache) reports the same axioms for
  `cglDensity`. Since `bb094dc`, seven Lean files have changed in plain comments and in `set_option` lines put on blank
  lines, three have gained an explicit binder, and the lakefile has turned the two options off (below). None of this
  changes a compiled module. The six files of `5b346ff` compile to the same `.olean` as before, byte for byte, and CI,
  building them, replayed every module that imports them, which Lake does only when the recompiled `.olean` is
  unchanged. Rebuilt with the options off, the 427 library modules built here, the proof's 109 among them, compile to
  the same `.olean` as before, byte for byte; PNT+, whose options did not change, was not rebuilt. So the checks below,
  made on the builds of `bb094dc` and `5fc056f`, hold at the head. The documentation fixes of `5dac8f3` change no
  constant either: `scripts/lean/ClosureFingerprint.lean` prints the same line for each of `cglDensity`'s 83,231
  constants (its kind, universe parameters and the hashes of its type and value) before them and after.
- **No route around the kernel.** The lakefile sets only `autoImplicit` and `relaxedAutoImplicit`, both off, for the
  whole package. Nothing in `lib/`, the vendored
  libraries included, uses `skipKernelTC`, `addDeclWithoutChecking`, `unsafe`, `implemented_by`, `native_decide` or
  `ofReduceBool`. The `LinnikCGL` modules declare one `NeZero` instance and one tactic macro (`cgl_good`).
- **Other kernels.** `#print axioms` reads the environment that elaboration built, so it cannot see a declaration that
  a metaprogram added without the kernel. A module that adds `bogus : False := True.intro` with `debug.skipKernelTC`
  on, and proves `uses_bogus : False` from it, gets "'uses_bogus' does not depend on any axioms".
  `scripts/kernel_check.sh` re-checks a theorem with every constant it depends on, outside the build, by the checkers
  the pinned toolchain ships. It first makes each of them reject that module. For `cglDensity`, built locally from
  `bb094dc` (and again from `5fc056f`, with the same export and the same verdicts, in 13 min 45 s in all):
  - `leanexport` (lean4export 3.1.0) writes the theorem with what it depends on: 14,591,566 records, 785 MB.
  - Lean's kernel reading that export (`leanchecker --from-export`) accepts it, in 214 s.
  - nanoda 0.4.17, an independent kernel in Rust, accepts it: "Checked 84260 declarations with no typechecker
    errors", in 154 s. Only `propext`, `Classical.choice` and `Quot.sound` are permitted, and any other axiom is a hard
    error. Its one "pretty printer error" is "Unable to print axioms": after the check it fails to print the list of
    axioms, which the configuration has already restricted.
  - con-leche and con-ron each report "accepted 81578 declarations", in 77 s and 100 s. They run in `--verified` mode,
    the mode of con-leche's theorem `ConLeche.no_proof_of_False`: an environment it accepts holds no constant of type
    `False`. Both note that they modelled one inductive block, `Lean.Syntax`, in-process. It comes in through
    structure fields with a default tactic (`AddMonoid.mk` mentions `AddMonoid.nsmul_succ._autoParam`).
  - `scripts/lean/ReplayClosure.lean` replays the same constants from the `.olean` files into an empty kernel
    environment, with `Lean.Kernel.Environment.replay`, as `leanchecker --fresh` does for a module. All 83,231 of them
    come back identical, in 177 s. They are 64,971 theorems, 15,272 definitions, 1282 inductive types,
    1394 constructors, 255 recursors, 50 opaques, 4 quotient constants and 3 axioms, exactly `propext`,
    `Classical.choice` and `Quot.sound`. None is unsafe or partial.
  - The three counts are of the same constants. con-leche and con-ron count the theorems, definitions, inductive
    types, opaques and axioms (81,578), and generate constructors, recursors and the quotient themselves. The export
    carries every recursor of each inductive type, so nanoda's 84,260 is the 83,231 with the 1027 recursors that no
    proof uses and the two auxiliary recursors of the nested `Lean.Syntax` (`rec_1`, `rec_2`;
    `scripts/lean/StatementClosure.lean` counts them).
  - lean4lean, also shipped, reads only `.olean` files, and not this toolchain's ("incompatible header"). It was not
    run.

  So the theorem does not rest on the elaborator, on the Mathlib cache or on Lean's kernel alone.
- **Every interface is discharged.** `CGLT101`, `CGLP81`, `CGLS2`, `CGLS3` and `CGLProp31` are proved by `cglt101`,
  `cglp81`, `cgls2`, `cgls3` and `prop31`, with no hypotheses. `CGLThird` is built inside `LinnikCGLS3.prop31_pt` as
  `third_of_s23 cgls2 (cgls3 cglp81 cglt101)`. `charDensity_cglGen` takes only `CGLProp31` and `ParC.Good`, and
  `parCGLe_good` proves `Good`.
- **The interfaces match the paper.**
  - `CGLProp31` is their Proposition 3.1 (p. 13) at one point per character: their smooth `w` is replaced by the
    indicator of `S ⊆ [6N/5, 9N/5]`, where `w = 1`, and their `⪅` is made explicit.
  - `CGLT101` is their Theorem 10.1, term for term.
  - `CGLS3` carries their `(qT)²|W|^{3/2}`.
- **No implicit argument by accident.** Under Lean's default `autoImplicit`, a misspelt name in a declaration's header
  becomes an implicit argument, without a warning. That cannot touch `CGLDensity`, whose header has no binders, nor
  the proof's soundness, but it could make an intermediate statement, an interface above say, mean less than it
  reads. All 109 library modules whose declarations the proof uses elaborate with `-DautoImplicit=false
  -DrelaxedAutoImplicit=false`, under Lake's setup file and under a bare `lean`, so no declaration in them binds a
  name that way. (A bare `lean` used to time out in `LinnikLindelof`'s `lindelof`, with the flags or without, for the
  reason under "Heartbeat margins" below. It now passes, in 29 s with the flags.) The same test on the other 318
  library modules built here (427 of the library's 1125) found three declarations that relied on the default, all in
  the import cone and none used by the proof. All three were benign: the auto-bound name was a parameter that the
  statement means to quantify over (`s` in `KubotaCompleted.mem_S_of_term_ne_zero`, `δ` in
  `Mollify.archIntegrand_Av_le`, `a` in `ParitySplit.arch_part`). Each is now declared where Lean put it, so the three
  statements are unchanged. The package now turns both options off for every library, the vendored ones included
  (`scripts/gen_lakefile.py`), so a name that a declaration does not bind is an error. The change rebuilds every
  module. CI's cold build of every library with both options off passes at `f89aa26` (10,229 jobs, the axiom gates,
  dead code and warnings included), so no other declaration relied on the default: not in the 698 modules not built
  here, nor in the vendored Zeta23, whose upstream turns off only `relaxedAutoImplicit`. Rebuilt here with the options
  off, the 427 library modules built here, the three with a new binder included, compile to the same `.olean` as
  before, byte for byte. A local build of every library with both options off then passes as well (10,229 jobs: the
  1125 modules of `lib/`, the 698 not built here before included, the vendored PNT+ and Zeta23, the check files and
  `deadcode`), and so do its four axiom gates and the dead-code check.
- **Heartbeat margins.** Lean stops elaborating a declaration after `maxHeartbeats`, 200,000 by default, which the
  library keeps except where a declaration raises it. Re-elaborating the 109 modules under Lake's setup with the
  default lowered to 150,000, 175,000 and 190,000 finds 15 declarations that need more than 150,000:
  - more than 190,000, within 5% of the limit: `LinnikCGLEps.lemma1010_eps`, which the proof uses, and
    `LinnikTwelve.class1_twelve` and `LinnikLindelof.lindelof`, which it does not;
  - between 175,000 and 190,000: `InghamDensity.densityXi_of_zetaCrit`, `LinnikChar.norm_Sx_le` and
    `LinnikIngham.class2_count_ingham`, none of them used;
  - between 150,000 and 175,000: `LinnikCGL112.S3_le_blocks`, `LinnikCGLHBIter.caseA`, `LinnikCGLS3.cgls3` and
    `LinnikMoment.refined_moment`, which the proof uses, and `DensityAsym.window_count`,
    `DensityAsym.density_of_detect`, `LinnikDensity.block_count_chars`, `LinnikHuxley.charDensity_huxley` and
    `LinnikTwelve.charDensity_twelve_fifths`, which it does not.

  How little it takes to cross the limit: `lindelof` needs between 195,000 and 200,000 heartbeats when its module is
  named `LinnikLindelof`, as Lake names it, and between 200,000 and 210,000 when it is named
  `lib.pnt.LinnikLindelof`, as a bare `lean lib/pnt/LinnikLindelof.lean` run from the repository's root names it. So
  the bare run times out, at line 338. Lake's setup file with the names `SomeOtherName`, `Foo.Bar` or `_stdin` passes,
  and with `a.b.LinnikLindelof` fails: the elaborator's work varies a little with the module's name. None of this
  touches validity, since the kernel checks the terms, but a Lean or Mathlib update could break the build at these
  declarations. The three within 5% now carry `set_option maxHeartbeats 400000 in`, as 39 declarations of the
  library already do. Each sits on the blank line before its declaration, so no line moves. Each module's `.olean`
  is then byte for byte what it was (checked by compiling both versions), and Lake rebuilds nothing downstream: in a
  local rebuild, `LinnikSubconvex`, `LinnikHuxStep` and `LinnikCGLS3`, which import them, were replayed, not rebuilt.
  A bare `lean lib/pnt/LinnikLindelof.lean` now passes.
- **The step.**
  - The mollifier has length `X ≈ Q^{1/2000}`, with `Y = Q^{201/400}` and `Q = q(T + 6)`
    (`LinnikCGLStep.count_cgl_at`). It is short, like their `(qT)^ε`.
  - The integral class uses the library's fourth moment at one point per character (`LinnikFourth.fourth_moment`,
    proved by the approximate functional equation).
  - The trivial character is added by hand. The factor `(log qT)^{10}` of `charDensity_cglGen` only absorbs that `1`.
- **The half-plane is imported but not used.** `DirichletCharHalfPlane` is in the import cone by several routes, all
  through `ChiPNT`, the only module of the cone that imports it: for example `LinnikDetect → ChiUniform → ChiPNT`, or
  `LinnikCGLMellin → SieveWeight → SieveLemma1 → LinnikChar → ChiUniform → ChiPNT`. `lib/check/CheckAll.lean` walks,
  in Lean, the constants that `cglDensity`'s type and value mention, transitively. A proof term names every lemma a
  tactic used, so the walk is exact. It finds 83,231 constants: from 109 of the library's modules, from 5 of
  PrimeNumberTheoremAnd's (`Auxiliary`, `EulerMaclaurin`, `Rectangle`, `ResidueCalcOnRectangles`, `ZetaBounds`), and
  from Mathlib, Batteries, Aesop and Lean, 2613 modules in all. Neither `Eis.LFunction_ne_zero_of_re_gt` nor any
  other declaration of `DirichletCharHalfPlane` is among them, and CI fails if one comes in. `scripts/census.py`, run
  locally in the environment of `LinnikCGLDensity` alone, counts the same 83,231 constants and the same 109 modules of
  the library. It attributes them to 2614 modules: 2341 of Mathlib, 146 of Lean's `Init`, 12 of Batteries and one of
  Aesop. The two module counts differ in attribution, not in constants. 54 of the constants are equation and
  congruence lemmas (`.eq_n`, `.congr_simp`, `.hcongr_n`) that Lean generates on demand, so that several modules
  declare them. Import accepts such copies because they are theorems with the same name, type and universe
  parameters, and attributes each to the first module in import order. In the environment of `LinnikCGLDensity`, five
  modules are counted only because such a lemma is attributed to them, and four of those lemmas are also declared in
  a module counted anyway; `CheckAll` imports more modules, in another order, and counts one fewer
  (`scripts/lean/StatementClosure.lean` lists them).
  `scripts/decl_reach.py`, a static over-approximation from the sources, had already found the half-plane
  unreachable (2096 of 8988 declarations reachable, with every identifier linked to every declaration that shares its
  last name component).
- **The proofs, against the paper.** Each main proof was read through its cited lemmas and its module's header, and
  its statement against the paper's. The kernel checks the lines.
  - Proposition 3.1 (`prop31_of_third`): for `N ≤ qT`, Proposition 4.6 (`prop46`, Guth and Maynard's moment step for
    the points, `(|R|N^{2σ})³ ≤ (216N)³X`) with the bound on `X` (`CGLThird`, from `cgls2` and `cgls3` by
    `third_of_s23`); for `N ≥ max(qT, 10)` the mean value theorem; for `qT < N < 10` at most `q < 10` characters.
  - Proposition 6.1 (`cgls2`): their `S₂ ⪅ qT|W|N^{3−2σ}`, stated for `‖E‖_F² = S₂/(3μ₀)`.
  - Proposition 8.1 (`cglp81`): their downward induction on `ε` (`P81_base`, `P81_step`, `P81_all`). Its decay
    hypothesis bounds `Σ_b|f̂_b(ξ)|` by `D_j(T/|ξ|)^jφ(q)f_{b₀}(u₀)` at a point of the user's choice, where the
    paper has `sup_{b,u} f_b(u)`. That hypothesis is the stronger, so the paper's proposition implies the library's;
    the library's uses supply it.
  - Theorem 10.1 (`cglt101`) and Lemma 10.7 (`lemma107`): the paper's three terms, with the factor
    `d(q)(⌊log₂|R|²⌋ + 1)` of the grouping by conductor made explicit.
  - Lemma 10.9 (`lemma109`): the explicit form of `(DqT + N²)|W|^{1/2}E(W)^{1/2}`, split by the gcd `d` and the residue
    `n₁n₂⁻¹`, with `sum_cube_le` in place of Lemma 10.8 (above).
  - Lemma 10.10 (`lemma1010`): the Cauchy–Schwarz of Lemma 10.6's second moment against Lemma 10.7's fourth, before
    the paper's case analysis, which `LinnikCGLCase` and `LinnikCGLEps` carry out.
  - Proposition 10.2 (`prop102`): `lemma105`, then `lemma109_eps` and `lemma1010_eps` at `D = ⌊N²/(qT)⌋`, then
    `E ≤ A + B√E ⇒ E ≤ 2A + B²`. It does not need the paper's `N ≤ qT`: the factor `(qTN)^ε` absorbs larger `N`.
  - Proposition 11.1 (`cgls3`): the paper's four terms, from `prop102` and the bounds of §11.
  - The step (`count_cgl_at`): one zero per character with `σ ≤ Re s < 1` (Mathlib's
    `LFunction_ne_zero_of_one_le_re` excludes `Re s ≥ 1`); Montgomery's detection (`LinnikDetect.dichotomy`, Perron's
    formula with `e^{−n/Y}` and the contour moved to `Re s = ½` with `L`'s growth bound); the polynomial class by
    dyadic blocks, powers and `cgl_shift`; the integral class by the fourth moment. It uses Proposition 3.1 on the
    whole range `[Q^a, Q^λ]` of the powers' lengths, in place of the paper's §12 split with the mean value
    theorem. `ParC.Good` asks exactly the three terms of Proposition 3.1 at both ends of the range. At `σ = 5/7` and
    `e = 0` three of its conditions are equalities: `N^{2−2σ}` and `(qT)^{1/2}N^{3−4σ}` at `N = Q^{7/6}`, and
    `(qT)^{4/3}N^{2−4σ}` at `N = Q^{7/9}`.
- **What the statement is.** It bounds the number of characters with a zero, not the number of zeros (above). It is
  not vacuous: the count is at most `φ(q) ≤ q`, while `(7/3)(1 − σ) ≤ 2/3 < 1` on the range. At `T = 2` and large
  `q` the bound is a genuine density estimate, below Huxley's `12/5`.
  - Printed from the built `.olean` with `pp.numericTypes`, its numerals are real: `(5 / 7 : ℝ) ≤ σ`,
    `σ ≤ (16 / 21 : ℝ)`, `(2 : ℝ) ≤ T` and the exponent `(7 / 3 : ℝ) * ((1 : ℝ) - σ) + ε`. No natural-number
    division truncates a bound.
  - `LFunction χ` unfolds to Mathlib's `ZMod.LFunction χ`. Mathlib proves it equals the `L`-series on `Re s > 1`
    (`DirichletCharacter.LFunction_eq_LSeries`), is entire for `χ ≠ 1` (`differentiable_LFunction`), and does not
    vanish on `Re s ≥ 1` except perhaps at `χ = 1`, `s = 1` (`LFunction_ne_zero_of_one_le_re`). So it is the
    `L`-function, and the count is of the characters with a zero in `σ ≤ Re s < 1`, `|Im s| ≤ T`, with at most the
    trivial character besides.
  - That needs none of `ZMod.LFunction`'s construction, which goes through Hurwitz zeta functions, Mellin transforms
    of theta kernels and `Γ`. `LFunction χ` is differentiable at every `s ≠ 1` (`differentiableAt_LFunction`), so it
    is analytic on the connected open set `ℂ ∖ {1}`, and it agrees there with the `L`-series on `Re s > 1`. By the
    identity theorem it is the analytic continuation of `Σ χ(n)n^{−s}`, however it is built. The statement's
    number-theoretic definitions, 70 of its 5275 constants, are these: `MulChar`, `ZMod` and `DirichletCharacter`
    (`MulChar (ZMod q) ℂ`) with its `Fintype`, `LFunction` with the functions it is built from, and the real and
    complex powers, logarithms and `π`. The others are Mathlib's and Lean's foundations: algebra, order, the real and
    complex numbers, finite sets, measure and topology.
  - It depends on the library only through `CGLDensity` (`scripts/lean/StatementClosure.lean`). Followed through
    types and the bodies of definitions, but not through proofs, `cglDensity`'s type reaches 5275 constants: 5267 of
    Mathlib, Lean, Batteries and Aesop, `CGLDensity` itself, and seven facts its body abstracts, `Nat.AtLeastTwo` for
    the numerals 5, 7, 16, 21, 2 and 3 and `IsDomain ℂ`. No other declaration of the library, and none of
    PrimeNumberTheoremAnd's, can change what the theorem says. They enter only through proofs, which the kernels
    check.

### Module by module

The proof uses declarations of 109 of the library's modules: 1594 named declarations in all. Nine reviewers, each
given a slice of these modules and the list of the declarations used from each, read every module in full. For each
used declaration they checked three things:

- that the statement says what its docstring and its source (the paper's v2 PDF, or the classical result it cites)
  say;
- that no definition it rests on hides a junk value: a division by `0`, `Real.log 0`, natural-number subtraction, a
  `tsum` or integral of something not summable or integrable, a `Classical.choose` definition;
- that no hypothesis is unsatisfiable or vacuous where the chain applies it.

Every finding below was checked against the sources again. None is a crack: no used statement says less than it
appears to.

The proof also uses 175 constants of 5 of PrimeNumberTheoremAnd's modules, which were not read this way: none of them
is in what the statement says (under "What the statement is" above), so they matter only through proofs. The library
names 17 of them: the rectangle, vertical and horizontal integrals (`RectangleIntegral`, `VerticalIntegral`,
`HIntegral`, `UpperUIntegral`, `LowerUIntegral`, and primed forms) with two lemmas on rectangles
(`DiffVertRect_eq_UpperLowerUs`, `rectangle_mem_nhds_iff`); `HolomorphicOn` and `HolomorphicOn.vanishesOnRectangle`;
the residue theorem `ResidueTheoremOnRectangleWithSimplePole'`; and `riemannZeta0` with `Zeta0EqZeta` and
`ZetaBnd_aux1`. The
users are the contour shifts (`SmoothPerron.verticalIntegral_shift`, `LinnikGamma.verticalIntegral_sub_eq`, and
the approximate functional equation of `LinnikAFE` and `LinnikFourth`) and `LinnikCGLRefl0.norm_zeta_le_strip`.

| Module | What the chain takes from it | Source |
|---|---|---|
| `BinetProof` | the Laplace form of `ψ`, for the bounds on `Γ` | Binet's first formula, derivative form |
| `DigammaGauss` | Gauss's integral for `ψ(z) − ψ(w)` | classical |
| `LinnikGammaRatio` | bounds on `Γ` ratios and Euler factors; the reflected functional equation | Mathlib's functional equation |
| `LinnikFE` | root numbers: `ε(χ⁻¹) = conj ε(χ)`, `\|ε(χ)\| = 1` for primitive `χ` | classical |
| `LinnikChar` | Perron's formula with weight `e^{−n/x}`; `\|L(s,χ)\| ≤ 3(q + 1)(\|t\| + 2)` on `½ ≤ σ ≤ 3` | classical |
| `ChiUniform` | the constant `ζ(3/2)`; a termwise comparison of `L`-series | — |
| `LFunctionGrowth` | `\|L(s,χ)\| ≤ (N + 1)\|s\|/Re s` for `χ ≠ 1`, by partial summation | classical |
| `HalfPlaneLindelof` | `d log\|f\| = Re(f′/f)`; `\|ζ(s)\| ≤ ζ(3/2)` on `Re s ≥ 3/2` | elementary |
| `LinnikLindelof` | `\|L(s,χ)\| ≤ ζ(3/2)` on `Re s ≥ 3/2` | absolute convergence |
| `LinnikSubconvex` | `∏_{p\|q}(1 + p^{−1/2}) ≤ 2^{⌈e^{1/ε}⌉}q^ε` | elementary |
| `Subconvexity` | bounds on `Γ` on vertical lines | Stirling-type |
| `LinnikHalf` | partial-summation split of `L`; `\|L(½ + it,χ)\| ≤ 11(q(\|t\| + 2))^{1/2}` | convexity bound |
| `LinnikReflect` | the reflection factor `Φ`; dual sum and tail of `L(1 − s,χ)` | functional equation |
| `LinnikDual` | dual terms as conjugated Dirichlet polynomials | — |
| `LinnikAFE` | approximate functional equation for `L²`; a `Γ`-ratio bound | smoothed AFE |
| `LinnikFourth` | `fourth_moment`, at one point per character | classical hybrid fourth moment |
| `LinnikMoment` | the singular-value third-moment inequality of Proposition 4.6 | Lemma 4.2 |
| `DirMean` | Dirichlet polynomials, Gallagher's lemma, an off-line Taylor bound | Montgomery, Gallagher |
| `DivSq` | `Σ_{j≤M} d(j)² ≤ M(1 + log M)³` | classical |
| `SquarefreeCount` | `sum_rpow_neg_le` only | integral comparison |
| `MollId` | the Möbius divisor sum; `cpow` splitting for the mollifier | elementary |
| `LinnikPoints` | large values at separated points | Gallagher, hybrid mean value |
| `LinnikPower` | the divisor bound; powers of polynomials | classical |
| `LinnikHybrid` | hybrid mean value and large values over characters | Gallagher's hybrid large sieve |
| `LinnikCGLTail` | explicit tails `\|n\| > N₀`, `\|ξ\| > X` of Lemma 8.2 | pp. 29, 32 |
| `LinnikCGLTrunc` | truncation of `S₃`'s Poisson expansion to `0 < \|m\| ≤ M` | §7, (7.1) |
| `LinnikCGLSym` | support of `J`; cyclic symmetry | Proposition 7.1 |
| `InghamDensity` | detector parameters `X`, `Y`, `N`; the weight; block masses | Ingham's method |
| `InghamDetect` | coefficients; bounds on `Γ` in strips; Mellin inversion of `e^{−x}` | Montgomery-type detector |
| `Landau` | two helpers for `\|ζ(s)\| ≤ ζ(3/2)` | — |
| `LandauLaplace` | the identity theorem on a convex open set | Mathlib's identity theorem |
| `SmoothPerron` | moving a vertical contour; `cpow` algebra | smoothed Perron |
| `LinnikDetect` | `dichotomy`: each zero gives a large value or the integral class | Montgomery's detection |
| `LinnikIngham` | the integral-class integrand on `Re s = ½` | Ingham-style bound |
| `LinnikHuxley` | `class2_count_small`, the integral-class count; block bookkeeping | the library's own route |
| `LinnikHuxStep` | bookkeeping at large `Q` (`choose_m_gen`, `absorb_K_gen`, `eventually_gen`) | — |
| `LinnikTwelve` | `CEQ` only, in a conjunct the step discards | — |
| `LinnikTwelveBins` | `F^m` normalised at `σ_b` | Huxley's large values (set-up) |
| `LinnikTwelveSizes` | `2^{ω(q)} ≤ d(q)`; a limit of log powers | elementary |
| `LinnikWeighted` | the product trick, `pv_eq_dp`, `LSX` | weighted Halász–Montgomery |
| `LinnikDensity` | dyadic blocks of `P_χ`; `#R ≤ q` | — |
| `LinnikCGL` | the statement `CGLDensity` | abstract; Theorem 1.2 on `[5/7, 16/21]` |
| `LinnikCGLDensity` | `parCGLe`, `parCGLe_good`, `e → 0`, `cglDensity` | the exponent `7/3` |
| `LinnikCGLStep` | detection, blocks, powers, bins, the two classes, the count | §12 |
| `LinnikCGLLV` | `CGLProp31`; the three-part split; reduction to conductors | Proposition 3.1, §3 |
| `LinnikCGLMat` | the Gram-matrix moment step, `prop46`, `prop31_of_third` | Lemmas 4.1–4.2, Proposition 4.6, §11.2 |
| `LinnikCGLS23` | `X = 3μ₀‖E‖_F² + S₃`; `CGLS2`, `CGLS3` | (5.2), Propositions 6.1 and 11.1 |
| `LinnikCGLS3` | `cgls3`, from Propositions 8.1 and 10.2 through (11.2) | Proposition 11.1 |
| `LinnikCGLCount` | a lattice count with a gcd weight | Lemma 8.2 (p. 32) |
| `LinnikCGLConst` | constants; `Σ(h, q) ≤ q·d(q)`; `n ≤ φ(n)d(n)` | Lemma 8.2 |
| `LinnikCGLBlock` | bounds on `S₃,₃`, `S₃,₄` and block sums | §11.1 |
| `LinnikCGLCov` | the change of variables `ξ → τ`; a Tonelli bound | Lemma 8.2, (8.7) |
| `LinnikCGLDiag` | `\|μ − μ₀\|`; dropping "not all equal" | §7 |
| `LinnikCGLTrace` | the library's `S3` is the paper's `S₃` | (5.2), §7 |
| `LinnikCGLMom` | Lemma 9.1, at one point per character | Lemma 9.1 |
| `LinnikCGLMom4` | Lemma 9.2 with the energy and an explicit error | Lemma 9.2, repaired |
| `LinnikCGLS2` | `cgls2`, the bound on `‖E‖_F²` | Proposition 6.1 |
| `LinnikCGLJ` | `J(f⃗)` and `CGLP81`; `S₃,₃` and `S₃,₄` reduced to `J` | §8, Proposition 8.1 |
| `LinnikCGLJtil` | Cauchy–Schwarz of `Σ_II` back to `J(f̃)` | Lemma 8.2 (pp. 33–34) |
| `LinnikCGLDecay` | `CGLP81`'s decay premise for `f_b`, at its maximum | §11 (p. 49) |
| `LinnikCGLP81` | the downward induction; `cglp81` | Proposition 8.1 |
| `LinnikCGLFourier` | `(2π\|ξ\|)^K\|ĥ_τ(ξ)\| ≤ C_K(1 + \|τ\|)^K` | Lemma 4.3(1) |
| `LinnikCGLMellin` | `H = 𝓜(w²)` and its decay; Perron for Gram entries | (6.2) |
| `LinnikCGLPoisson` | scaled Poisson summation; Gram entries by residues | (6.1), Lemmas 4.4 and 4.5 |
| `LinnikCGLPois8` | Poisson for `ĝ_a`, then the shift `d → d + am₁ + bm₂` | Lemma 8.2 (p. 28) |
| `LinnikCGLFtil` | `f̃ = Tψ̃₀(T·) ⋆ f`; a majorant of `Σ_II`'s integral | Lemma 8.2 (pp. 33–34) |
| `LinnikCGLFtilP` | support, decay, `L¹` and `L²` bounds of `f̃` | the induction step (p. 27) |
| `LinnikCGLFb` | `f_b = ψR̃(·, −b)²` with `ψ = 1` on `[−3, 3]` | §11 (pp. 48–49) |
| `LinnikCGLPhi` | Fourier decay of the pieces of `f_b` | §11 (p. 49) |
| `LinnikCGLG` | the majorant `g_a`, Plancherel, `ĝ_a` by an affine change of variables | Lemma 8.2 (p. 28) |
| `LinnikCGLL82` | Lemma 8.2 with explicit constants | Lemma 8.2 |
| `LinnikCGLP71` | a pointwise bound on `Ψ`; the constants `CJ` | Proposition 7.1 |
| `LinnikCGLP72` | `S₃` bounded by dyadic sums of `Ĩ` and explicit errors | Proposition 7.2 |
| `LinnikCGLT101` | `CGLT101`, `dyad`, Lemma 10.6 | Theorem 10.1, Lemma 10.6 |
| `LinnikCGLHB101` | `cglt101`, from the bound on `σ(N)` | Theorem 10.1, by Kerr and Jutila |
| `LinnikCGLHBIter` | Kerr's iteration, its cases A and B | Kerr's Theorem 16, with characters |
| `LinnikCGLHBLen` | lengthening by characters modulo an auxiliary prime | Kerr's Lemma 20, Corollary 21 |
| `LinnikCGLHBPos` | double sums, positivity, the dyadic split | Jutila's Lemma 2, Kerr's Lemma 22 |
| `LinnikCGLHBRefl` | reflection of Gram entries | Kerr's Corollary 28, Jutila's Lemma 1 |
| `LinnikCGLL105` | the energy bounded by `N^{−2σ}` times a third moment; `Spaced` | Lemma 10.5 |
| `LinnikCGLL107` | the fourth moment of `R₂`, grouped by conductor and class size | Lemma 10.7 |
| `LinnikCGLL109` | the small-gcd third moment | Lemma 10.9 |
| `LinnikCGLL1010` | the large-gcd third moment | Lemma 10.10 |
| `LinnikCGLCase` | the case analysis; Remark 10.3 | Lemma 10.10, Remark 10.3 |
| `LinnikCGLEps` | the bookkeeping in `ε`; `prop102` | Proposition 10.2 |
| `LinnikCGL112` | Proposition 7.2's blocks summed into (11.2) | (11.2) |
| `LinnikCGLCS` | the two Cauchy–Schwarz steps of §11 | the proof of Proposition 11.1 |
| `LinnikCGLRt` | `R̃`; Proposition 7.2's inner integral | (7.4), (7.5) |
| `LinnikCGLRFact` | `I′_m` as an integral with Ramanujan sums | (7.3) |
| `LinnikCGLProd` | three `ĥ`'s as an integral of the kernel `J` | the proof of Proposition 7.1 |
| `LinnikCGLRam` | `\|C_q(n)\| ≤ d(q)(n, q)`; decay and support of `J` | inputs to Proposition 7.1 |
| `LinnikCGLForm` | Lemma 8.2 at fixed parameters | Lemma 8.2 |
| `LinnikCGLAsum` | the sum over `a`, by Ramanujan sums | §8.2.2 |
| `LinnikCGLNsum` | `ĝ_a` by Poisson; the terms `n ≠ 0` | (8.2)–(8.3) |
| `LinnikCGLN0` | the term `n = 0` | §8.2.5 |
| `LinnikCGLSig2` | `Σ_II`; `Σ₂` by Poisson | Lemma 8.2 (p. 33) |
| `LinnikCGLLoc` | local averages of exponential sums | Lemmas 10.4 and 10.8 |
| `LinnikCGLSep` | separation of fractions; cubes at separated points | the proof of Lemma 10.9 |
| `LinnikCGLFrob` | the off-diagonal Gram mass `‖E‖_F²` | Proposition 6.1, from Lemma 6.2 |
| `LinnikCGLPair` | one reflected Gram entry | Lemma 6.2 |
| `LinnikCGLReflect` | reflection of Gram entries with `χ_i ≠ χ_k` | Lemma 6.2 |
| `LinnikCGLRefl0` | reflection of principal entries through the pole | Jutila-style |
| `DensityCore` | dyadic blocks `(2^kX, 2^{k+1}X]` | — |
| `DensityAsym` | `log U ≥ ½` for `U ≥ 2` | elementary |
| `SieveLemma1` | Perron's formula with a smooth weight (`perron_weight`) | Mellin inversion |
| `SieveSmooth` | `(2π\|ξ\|)^K\|f̂(ξ)\| ≤ ‖f^{(K)}‖₁` | classical |
| `SieveWeight` | support and derivative bounds of `w²(e^{−v})` | — |
| `KaiserZeroWeight` | `Re ψ(z) ≤ log\|z\| + 4` on `Re z ≥ ¼` | the Laplace form of `ψ` |
| `RealDirichlet` | `\|γ_χ\| ≤ 8` on `½ ≤ Re z ≤ 3` | bounds on `Γ` |

**What the reading confirms**, beyond the bullets above:

- **The counting set.** `charDensity_cglGen` (`LinnikCGLStep.lean:1008`) states `CGLDensity`'s filter exactly, and
  bounds it by the count of nontrivial characters plus `1`. `count_cgl_at` picks one zero for each `χ ≠ 1`, with
  `σ ≤ Re s < 1`.
- **Detection.** `LinnikDetect.dichotomy` turns every zero with `½ < β < 1`, at any height, into one of two values at
  least `¼`: the mollified polynomial at the zero itself, or the integral class. The step's cover `Z ⊆ Z1 ∪ Z2`
  (`LinnikCGLStep.lean:803–815`) applies it to each counted character. It is the library's explicit form of
  Montgomery's detection, not a transcription of the paper's §12.
- **The integral class.** `LinnikHuxley.class2_count_small` bounds it by `LinnikFourth.fourth_moment`, which holds
  for every modulus, imprimitive characters included, with one free ordinate per character and a constant that
  depends on `ε` only. Bounding the mollifier by `X` costs `X⁴ ≤ Q^{1/500}`, the `1/500` of `ParC.Good`.
- **Uniformity in `ε`.** In §10 every constant is chosen before `∀ q`. The factors `d(q)(⌊log₂|R|²⌋ + 1)`,
  `1 + log max(1, N)` and `|{n ∼ N}|` stay in the statements until `lemma1010_eps` absorbs them into `(2qTN)^ε`.
- **The interfaces, more precisely.**
  - `cglt101` proves `CGLT101` with `Q₀ = 0`, without using primitivity.
  - `cgls2` uses neither primitivity nor the range of `σ`.
  - `CGLP81`'s premise is discharged at the maximum of `f` (`LinnikCGLDecay.exists_max`), with constants that depend
    on `j` only.
- **Junk values.** Each definition with a junk value is used only where its value is genuine, or where the junk value
  cannot help:
  - `Gχ` is built with `dslope` and evaluated only at zeros.
  - `Ivχ`, `Jint` and the other Bochner integrals are proved integrable.
  - `dualT` is a `tsum`, used only on `Re s < 0`, where it converges.
  - `Phi` uses Mathlib's `Γ(−n) = 0`, which is the true value of `1/Γ`.
  - `Z2` drops `m = 0` through `0^{−2} = 0`.
  - `blk` takes natural-number subtraction and `Nat.log` only with `X ≥ 1`.
  - `p31B` would divide by `0` only at `V = 0`, which is never reached.
  - `LinnikCGLRefl0` handles entries with `χ_i = χ_k` and `i ≠ k`, which the chain's injectivity rules out.
- **Inside the 109 modules, the half-plane is used only off the chain.** Two declarations restate it:
  `LinnikChar`'s `zeroFree_ball_global` and `LinnikLindelof.LFunction_ne_zero`. Neither of them, nor any of the 137
  declarations that depend on it statically, is in the closure.

**Documentation that misstated its declaration.** None of these changes what a used statement says, and all but the
first concern declarations that the proof does not use. Three were in a module's plain `/- … -/` header, which Lean
does not keep. They are corrected here, line for line, and those modules' `.olean` files are unchanged:

- `LinnikCGLStep.lean:24` said "the step takes `δ = 1/4`"; `count_cgl_at` takes `δ = 1/5` (line 826).
- `ChiUniform.lean`'s title and statement spoke of real, quadratic characters; `psiChi_le_uniform` holds for every
  `χ ≠ 1`.
- `SieveLemma1.lean`'s header presented `norm_Sw_le` as needing a zero-free rectangle. Its proof also uses the
  zero-free half-plane, which the header now says (`SieveWeight.norm_Sp_le` applies it).

The others are docstrings, which the `.olean` keeps, so that correcting one rebuilds everything downstream of its
module. They are corrected too, line for line, now that the switch of options has rebuilt the library anyway:

- `InghamDetect.lean:750`: `tail_le`'s docstring had `|ρ − 1| ≤ 3U`, its hypothesis `‖ρ − 1‖ ≤ 2U + 1`, and left
  out its hypothesis `Re ρ ≥ 0`.
- `LinnikGammaRatio.lean:58`: `KQ_le`'s docstring had `2 log(15e⁴)`, its statement `6 log(15e⁴)`. The docstring's
  bound fails at `a = b = 3`.
- `KaiserZeroWeight.lean:49`: `im_logDeriv_Xi_le`'s docstring had `3 + kLam`, its statement `5 + kLam`.
- `MollId.lean:9`, in the module's docstring: `norm_moll_le` was stated for `β ≥ σ ≥ 0`. The theorem assumes
  `σ ≤ β` and `σ ≤ 1`, and not `σ ≥ 0`.
- `RealDirichlet.lean:11`, in the module's docstring: it cited `abs_sum_cR_le` with `≤ N` and `norm_LFunction_le`.
  The lemmas are `abs_summ_cR_le`, with `≤ N + 1` for the sum over `1 ≤ k ≤ x`, and `norm_LFunction_leC`.

A mechanical sweep then checked every name these modules' comments cite. It took the 1882 distinct
identifier-like tokens between backquotes in the comments of the 109 modules and resolved each against the
declarations of `LinnikCGLDensity`'s environment, 501,832 of them. Of the tokens that resolve to nothing, all are
notation (`f_b`, `B_J`, `χ_i`), file names, or names of modules outside that environment (`LinnikStep`, `lib/dh`, and
`LinnikCGLLegacy.lean`, cited as removed), with four exceptions. Each is a stale name, now corrected: the header of
`ChiUniform.lean` cited `PsiOmega.norm_LFunction_le` for `norm_LFunction_leC`; that of `InghamDensity.lean`,
`ZeroLocal.card_local_le` for `ShortWeil.card_local_le`; that of `Landau.lean`, `delta_choice` for `delta_choiceW`; and
the docstring of `Landau.delta_choiceW`, `zero_gap` for `zero_gapW`.

None of these corrections changes a constant: `cglDensity`'s fingerprint (`scripts/lean/ClosureFingerprint.lean`) is
the same before and after them, line for line. CI rebuilt the 756 modules they reach and passes (`5dac8f3`).

The statement's own docstring (`LinnikCGL.lean`) said that `CGLDensity` follows from their Theorem 1.2. That needs the
theorem's `o(1)` to be uniform in `σ`, and the docstring now says so.

## Heath-Brown's Theorem 10.1, with characters

The paper states its Theorem 10.1 for primitive characters and credits it to Heath-Brown: "Theorem 10.1
(Heath-Brown, [6]). Let T be a set of pairs (t, χ), where χ is a primitive character modulo q …". Their [6] is "A
large values estimate for Dirichlet polynomials", J. London Math. Soc. 20 (1979), 8–18. That paper could not be
obtained and was not read. The formalisation (`LinnikCGLHB101.cglt101`) follows two sources:

- B. Kerr's proof of the case `q = 1` (arXiv:1909.12075, Theorem 16 and §§5–6): positivity, lengthening, squaring
  and a reflection;
- for the reflection with characters, in place of Kerr's van der Corput B-process, M. Jutila's Lemma 1 ("Zero-density
  estimates for `L`-functions", Acta Arith. 32 (1977), 55–62).

The statement proved (`LinnikCGLT101.CGLT101`) is the paper's Theorem 10.1 for primitive characters, with its implicit
constants explicit and a factor `(qTM)^ε`, which their statement implies.

The result is adapted rather than transcribed: its cited source was not read, and the proof combines two other
sources. It is documented here, as part of the formalisation of the paper that states and uses it, and no paper in
this repository claims it.

## Where the Linnik paper uses it

The density curve of the Linnik paper's Type II estimate is `g7d` (`SieveCurve7D.counts_7d`), which takes their
Proposition 3.1 directly, on 30 steps of `[5/7, 131/168]` (next section), and not `CGLDensity`. An earlier curve, `g7c`
(`SieveTypeIIU226C.counts_7c`, now in the git history), used `CGLDensity`; it was built from these pieces:

- the trivial count below `4/7`;
- twenty steps from Ingham's estimate;
- this estimate on `[5/7, 16/21]` at `ε = 1/8400`, giving the exponent `(7/3 + 1/2000)(1 − σ)`
  (`SieveTypeIIU227.rangeCounts_cgl`, also in the git history);
- twenty steps from Huxley's estimate up to `5/6`;
- the library's `(101/50)(1 − σ)` from `5/6` on (`LinnikStep.charDensity_step`).

The theorem of the proof built on `g7c`, at an earlier exponent (`899/400`), was superseded too. `cglDensity` stays
and is printed by `lib/check/CheckAll.lean`.

## Proposition 3.1 on `[5/7, 131/168]`: the Linnik paper's steps

`LinnikCGLSteps` uses the same step (`LinnikCGLStep.charDensity_cglGen`, from Proposition 3.1,
`LinnikCGLHB101.prop31`) at other parameters, 30 steps of `[5/7, 131/168]`: fourteen of width `1/1680` from `5/7`, then
sixteen of width `1/280`. Each step's exponent is
`A(1 − σ)` with `A` within `10⁻⁴` of `4/(1 + lo)` (the table in the file's header), which is the divisor form `4/(1 + σ)` of the
paper's Theorem 1.2 at `q₁ = q`, taken at the step's left end. The library does not prove Theorem 1.2: the exponents
come from what `ParC.Good` allows the library's own Proposition 3.1 route (`tools/linnik/gen_cgl_curve.py` computes
the parameters and checks every field of `ParC.Good` in exact rationals). For `σ > 5/7` this is below the flat
`7/3 + 1/2000` of `charDensity_cgl`, which the earlier route (at `899/400`, in the git history) used on `[5/7, 16/21]` and took to `ε → 0`
(`cglDensity`). No hypothesis is involved: the steps hold at `e = 1/100000` and need no `ε`.

From `7/9` on Huxley's exponent `3/(3σ − 1)` is below `4/(1 + σ)`. On the last step, `[163/210, 131/168]`, his
exponent at the step's left end, plus the slack `1/2000` of his steps, is `2.2586`, above the step's `2.25207`;
pointwise, `3/(3σ − 1)` is below the step's exponent from `σ ≈ 0.7774` on, by up to `1.2·10⁻²` at `131/168`. At
`11/5` taking it there would not change the window, whose corners on that step have a slack of at least
`3.9·10⁻³`. Between the exponents `11161/5000` and `89/40` the library took Huxley's bound on `[1307/1680, 131/168]`,
in a file `LinnikHuxJunction.lean` (in the git history); at `11161/5000` the window's lower end was set near `7/9`.

The curve is `g7d` (`SieveCurve7D.lean`): `g7c` with the Chen–Gupta–Li steps on `[5/7, 131/168]`, in place of the
plateau and Huxley's steps `hx7_0` … `hx7_4`, and with Ingham's last step
`[99/140, 5/7]` at `ε = 1/400000` (`LinnikCGLSteps.charDensity_inT`: `LinnikInghamC.charDensity_ingham_c` has exponent `2 + 4c + 4ε`, so the slack is `4ε`, and the exponent is `7/3 + 1/100000` in place of `7/3 + 1/2000` at `ε = 1/8000`). Huxley's steps
`hx7_5` … `hx7_19` stay, since their exponents are smaller than the Chen–Gupta–Li step's from `131/168` on. The first
steps are narrow because both ends of the window are set where a step's exponent most exceeds the curve it bounds, on
the first step `[5/7, 1201/1680]`, at its right end; its exponent `2.3334` is the curve's largest, `7/3` at `5/7`, where
Ingham's and Chen–Gupta–Li's exponents meet. The corners' slack grows along the steps, and from `5/7 + 14/1680` on
steps of `1/280` leave the window as it is (steps of `1/140` would too at `11/5`, but moved its lower end at `278/125`). `Linnik22000E.linnik_22000e`, the paper's theorem, is Linnik's theorem with exponent `11/5` on `g7d` (the earlier theorem at `278/125`, `Linnik22240R.linnik_22240r`, is in the git history);
the classical deduction from the same curve gives `2.3334 + ε` (`LinnikG7.linnik_g7d`, with
`SieveCurve7D.g7d_le_lin`: `g7d σ ≤ 2.3334(1 − σ)`).
What lets the certificate close at `11/5` is the bilinear Type I estimate, which lets the decomposition go on past the
Type I level for the boxes that pass its test, together with the decomposition's levels seven and eight: on the same
grid the total would be `2.43K` without the bilinear test and `1.56K` with the decomposition stopped at depth six,
against `0.93K` (the Linnik paper, Section 5).
