# Lean formalization accompanying Alpöge's Riemann Hypothesis claim, and the state of its technical verification

Snapshot time: all findings are as of Friday 20 November 2026, about 14:35–14:48 UTC (the last poll of the Lean Zulip thread was at 14:48:17 UTC). This is roughly two hours after the statement PDF was generated (12:52:48 UTC) and 50 minutes after the first Lean Zulip post (13:58:06 UTC). All times below are UTC.

How these notes were made (read this first):
- "Tarball inspection" means this researcher downloaded the 14 parts from alpo.ge at about 14:35 UTC, concatenated them (gzip integrity test passed), extracted them, and searched the source text with ripgrep and a small import-graph script. **Nothing was compiled.** No `lake build`, no `#print axioms`, no kernel or external checker was run. Every tarball finding is therefore a statement about the source text, not about whether Lean accepts it.
- Three levels are kept apart throughout: (A) someone built it and Lean accepted it; (B) someone audited that the theorem statement is the Riemann Hypothesis; (C) experts accept the proof. As of the snapshot, **no public report of (A), (B) or (C) exists**. The only (B)-type evidence is this researcher's own static reading, labelled as such.

## 1. Where is the Lean code published (URL, owner, dates, size, license, toolchain, Mathlib pin, build instructions)?

### Takeaway
The code is not on GitHub. It is a single gzip tarball split into 14 raw parts on Alpöge's personal site (`https://alpo.ge/lean.tar.gz.part01` … `part14`), linked only from footnote 1 of his statement; it holds 175,187 `.lean` files (17,374,215 lines, about 1.03 GB) pinned to Lean `v4.33.1` and Mathlib's `v4.33.1` tag commit of 21 August 2026. It ships with no README, license, build instructions, version history, comments or logs.

### Cited Findings
- The statement's footnote 1, attached to the word "proof", reads: "https://alpo.ge/lean.tar.gz.part01, . . . , https://alpo.ge/lean.tar.gz.part14." — [remark.pdf](https://alpo.ge/remark.pdf)
- The statement says "I decided to only present Lean" (no informal write-up posted), and that a generated informal document "hit 250,000+ pages". — [remark.pdf](https://alpo.ge/remark.pdf)
- `remark.pdf` metadata: CreationDate and ModDate "Fri Nov 20 12:52:48 2026 UTC", 4 pages, produced by pdfTeX (read with `pdfinfo`). — [remark.pdf](https://alpo.ge/remark.pdf)
- The alpo.ge home page, fetched at about 14:33 UTC, had no mention of the Riemann Hypothesis, Lean or the tarball; the code is reachable only through the PDF footnote. — [alpo.ge](https://alpo.ge/)
- Parts 01–13 are exactly 18,000,000 bytes each and part 14 is 5,275,554 bytes; total 239,275,554 bytes compressed. `part15` returns the site's HTML fallback page, so there are exactly 14 parts. Served through Cloudflare with no `Last-Modified` header. — [part01](https://alpo.ge/lean.tar.gz.part01), [part14](https://alpo.ge/lean.tar.gz.part14)
- Tarball inspection: `cat` of the 14 parts gives a valid gzip stream (`gzip -t` passed); SHA-256 of the concatenated `lean.tar.gz` as downloaded at about 14:35 UTC is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`; uncompressed tar size 1,270,753,280 bytes. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection: 175,190 regular files under `lean/`: 175,187 `.lean` files plus `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`. No README, no LICENSE, no `.git`, no CI config, no build log, no blueprint. All tar entries have mtime 1970-01-01 and owner 0/0, so the archive carries no creation or modification dates. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection: `lean-toolchain` is `leanprover/lean4:v4.33.1`. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection: `lakefile.toml` names the package `tree`, `srcDir = "src"`, requires `mathlib` from `https://github.com/leanprover-community/mathlib4` at `rev = "0df444a360eaa60ab8c11dca51a86af692955474"`, sets `moreLeanArgs = ["--tstack=400000"]`, and global options `autoImplicit = false`, `relaxedAutoImplicit = false`, `maxSynthPendingDepth = 3`, `pp.unicode.fun = true`, `maxHeartbeats = 4000000` (20 times Lean's default of 200,000). Eleven `lean_lib` targets: `BuildAid`, `CompanionTheory`, `Development`, `Formalism`, `GroundTheory`, `GroundTheoryFields` (with `synthInstance.maxHeartbeats = 400000`), `Lemmata`, `PositivityTheory`, `ReciprocityTheory`, `Supplements`, `Main` (roots `Statements`, `Main`). — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection: `lake-manifest.json` pins Mathlib at the same commit and its usual dependencies (batteries `4488d40…`, aesop, Qq, proofwidgets, importGraph, LeanSearchClient, plausible, Cli `v4.33.0`). No other third-party Lean package is required. — [part01](https://alpo.ge/lean.tar.gz.part01)
- The pinned Mathlib commit `0df444a…` exists in the official repository: author Kim Morrison, date 2026-08-21T12:04:53Z, subject "chore: bump toolchain to v4.33.1"; its own `lean-toolchain` is `leanprover/lean4:v4.33.1` and its batteries pin matches the tarball's manifest (checked by `git fetch` from the official URL). GitHub's branch-containment page lists it under the tag `v4.33.1` and under no branch, i.e. it is Mathlib's release-tag commit for that toolchain, not a `master` commit. — [mathlib4 commit 0df444a](https://github.com/leanprover-community/mathlib4/commit/0df444a360eaa60ab8c11dca51a86af692955474); [branch_commits](https://github.com/leanprover-community/mathlib4/branch_commits/0df444a360eaa60ab8c11dca51a86af692955474)
- Lean `v4.33.1` was released 2026-08-21 as a patch release that "contains runtime and kernel fixes". — [Lean v4.33.1 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.33.1/)
- Lean has since moved on: tags `v4.34.0`, `v4.34.1`, `v4.35.0`, `v4.36.0` exist in `leanprover/lean4` (checked with `git ls-remote`), and Riccardo Brasca speaks of porting "to 4.36". — [Zulip, Brasca 14:29:46](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642233992)
- Lean Zulip, Jack McCarthy, 13:58:06: "Uploaded less than an hour ago to Levent Alpöge's page, with no formal announcement yet." At 14:04:26 he listed the 14 part URLs. — [Zulip, McCarthy 13:58](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642224678)
- Lean Zulip, Chris Henson, 14:17:52: "Not putting this into a Github repo is obscene. I'm convinced they just like the attention that their odd presentations bring." — [Zulip, Henson](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642230537)
- Scientific American (Joseph Howlett, 20 November 2026) gives no link to the code other than the statement PDF, names no one who has checked it, and says the story "will be updated". — [Scientific American](https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/)

### Inferences
- The implied build procedure is the standard one for a Lake project (`lake exe cache get` for Mathlib, then `lake build`); the tarball itself states none.
- The Mathlib pin (21 August 2026) predates the earliest date in the statement's own timeline ("10/6/26") by about six weeks, so the project was built against a fixed older Mathlib throughout rather than tracking `master`.
- With no license file and no copyright headers, reuse terms are undefined.

### Gaps
- Upload time of the tarball: no server timestamp. Only bounds are the PDF creation time (12:52:48 UTC) and McCarthy's "less than an hour ago" at 13:58 UTC.
- No GitHub (or other forge) repository by Alpöge or Anthropic for this code was found. A search hit `github.com/alerad/alpoge-lean` is unrelated (a third-party formalization of Alpöge's July 2026 Jacobian-conjecture counterexample). — [alerad/alpoge-lean](https://github.com/alerad/alpoge-lean)
- Hardware, wall-clock build time and memory needed: not stated by the author anywhere found.

## 2. What is the exact Lean statement of the main theorem(s)? Is it Mathlib's `RiemannHypothesis`? Is there a GRH statement?

### Takeaway
By static reading, the top-level file `Main.lean` states five hypothesis-free theorems: `riemannHypothesis : RiemannHypothesis` (the Mathlib constant, by name), a literal restatement of it, and three statements about all Dirichlet L-functions (non-vanishing for Re s > 1/2; zeros in the open critical strip lie on Re s = 1/2, for all characters and for primitive ones). The "GRH" in the code is for Dirichlet L-functions only; nothing for Dedekind zeta or automorphic L-functions is stated in `Main.lean`.

### Cited Findings
- Tarball inspection, `lean/src/Main.lean`, complete file:
  ```lean
  import Statements
  import Supplements.Kernels.MainTheoremsAll

  theorem riemannHypothesis : RiemannHypothesis := rhOfAll

  theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

  theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

  theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

  theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
  ```
  — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection, `lean/src/Statements.lean`, complete file (imports only `Mathlib`):
  ```lean
  import Mathlib

  def RiemannZetaZerosOnLine : Prop :=
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

  def DirichletLNonvanishingRightOfHalf : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

  def DirichletLZerosOnLine : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

  def PrimitiveDirichletLZerosOnLine : Prop :=
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
  ```
  — [part01](https://alpo.ge/lean.tar.gz.part01)
- Mathlib's definition at the pinned commit (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`, lines 182–186):
  ```lean
  /-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
  million dollars. -/
  @[wikidata Q205966]
  def RiemannHypothesis : Prop :=
    ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
  ```
  — [Mathlib RiemannZeta.lean at 0df444a](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L182-L186)
- Tarball inspection: no declaration named exactly `RiemannHypothesis` (in any namespace), and no `notation`/`macro`/`syntax` mentioning `riemannZeta`, `RiemannHypothesis` or `LFunction`, exists in the 175,187 files. `Main.lean` has no `open` or `namespace`, and it imports Mathlib through `Statements`, so the identifier `RiemannHypothesis` in `theorem riemannHypothesis : RiemannHypothesis` can only resolve to Mathlib's constant. The file `Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean` also contains `theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl` for the project's own `Claim.Zeta`. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection: the central internal statement is `UpperTheory.EveryCharacter` (`Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`): `∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0`. The other four statements are derived from it in short, readable files: `Formalism/GammaFactorNonvanishing/RhOfRight.lean` and `CritLine.lean` (functional equation of zeta and of completed L-functions; specialisation to the character mod 1 via `LFunction_modOne_eq`) and `ClaimStrip.lean` (reduction to the primitive character, Euler-factor non-vanishing, functional equation). — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection, chain of names from the top: `riemannHypothesis := rhOfAll`; `rhOfAll := Formalism.VW.rh_of_every allChi`; `allChi := UpperTheory.FinalTheorems.everyCharacter` (`Supplements/Kernels/MainTheorems.lean`); `everyCharacter := everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`; `everyCharacter_of_row h := UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)` (`Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`). — [part01](https://alpo.ge/lean.tar.gz.part01)
- The statement claims more than the code states: "the method easily extends much further, resolving the so-called Generalized Riemann Hypothesis, and I expect, with more time, the Extended Riemann Hypothesis too." — [remark.pdf](https://alpo.ge/remark.pdf)

### Inferences
- `RiemannZetaZerosOnLine` differs from Mathlib's `RiemannHypothesis` only in writing the cast `((n : ℂ) + 1)` explicitly; the code proves both from the same term `rhOfAll`, which type-checks only if the two are definitionally equal. That is this researcher's reading, not a compiled check.
- The Dirichlet statements quantify over every modulus `N ≠ 0` and every character, primitive or not, using Mathlib's own `DirichletCharacter.LFunction`; the side condition `χ ≠ 1 ∨ s ≠ 1` removes only the pole case. On its face this is the usual Generalized Riemann Hypothesis for Dirichlet L-functions. `[NeZero N]` is the only type-class argument and is required by Mathlib's `LFunction` itself.
- "Extended RH" (Dedekind zeta functions) is described in the statement as expected "with more time", and no such theorem appears in `Main.lean`, so it is not part of the formal claim.

### Gaps
- No third party has yet published a statement audit. On the Lean Zulip thread nobody had quoted or analysed `Main.lean` or `Statements.lean` as of 14:48 UTC.
- Whether these files elaborate as written (and so whether the five theorems really have these types) is unverified without a build.

## 3. What does "without assumptions" mean in the code (`#print axioms`, `sorry`, `axiom`, `native_decide`, etc.; hidden hypotheses)?

### Takeaway
No `#print axioms` output for the main theorem has been published by anyone, and none is in the tarball. A text search of all 175,187 files finds zero occurrences of `sorry`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `ofReduceBool`, `reduceBool`, `skipKernelTC`, `extern`, `opaque`, `csimp` or `#eval`, and the five top-level theorems take no hypotheses; the tree does contain a small amount of custom metaprogramming that an auditor will want to read.

### Cited Findings
- Statement: "Claude and I have also formalized the arguments without assumptions." and "its formalization is finished". — [remark.pdf](https://alpo.ge/remark.pdf)
- Tarball inspection, whole-word or literal text search over `lean/src` (files matched / matches): `sorry` 0/0; `sorryAx` 0/0; `axiom` 0/0; `native_decide` 0/0; `implemented_by` 0/0; `unsafe` (word) 0/0; `ofReduceBool` 0/0; `reduceBool` 0/0; `skipKernelTC` 0/0; `debug.` 0/0; `trustCompiler` 0/0; `extern` 0/0; `opaque` 0/0; `csimp` 0/0; `initialize` 0/0; `#eval` 0/0; `bv_decide` 0/0; `proof_wanted` 0/0; `unsafeCast`, `lcProof` 0/0. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection: `#print axioms` appears 4 times in 2 files, for intermediate lemmas only (`Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UnitaryClassMass.lean`: `tensor_localization`, `hermitian_approximation`, `unitary_class_mass`; `…/LocalUnimodularLattice/Transf.lean`: `transfer_holds`). There is no `#print axioms riemannHypothesis` and no recorded output. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection: `decide +kernel` is used 151 times (kernel evaluation of decidable propositions; this does not add axioms, unlike `native_decide`). — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection, metaprogramming that touches proof terms or the environment:
  - `Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean` defines a tactic `kexactB` that elaborates a term and assigns it to the goal with no elaborator-side type check (`g.assign (← instantiateMVars v)`); it is wrapped by local macros `kc%` and `kq%` in several files. Correctness of each use rests on the kernel's check of the finished declaration.
  - `Formalism/LocalToGlobal/NumberFieldFamilies/OwnStruct.lean` defines a similar tactic `kcopy` and a command `#kcopy_probe`.
  - `Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean` defines a command `cpt_copy_thms` that walks the environment, renames a set of declarations (suffix `Cpt`), substitutes constants in their types and values, and re-adds them as new definitions and theorems with `addDecl`; it is invoked once, in `CutMainCpt.lean` line 945.
  - `BuildAid/D1.lean`–`D5.lean` each run `run_cmd Lean.modifyEnv … Lean.LibrarySuggestions.nameDenyListExt.addEntry …`, adding the names `CompanionTheory`, `CrystallineSemistableComparison`, `GlobalTheory`, `PositivityTheory`, `UpperTheory` to a library-suggestion deny list.
  — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection, options: `set_option` occurs 88,139 times in 75,197 files. By name: `maxHeartbeats` 57,556 (largest value 64,000,000), `autoImplicit` 11,203, `maxSynthPendingDepth` 7,478, `synthInstance.maxHeartbeats` 7,381, `backward.isDefEq.respectTransparency` 1,879, `allowUnsafeReducibility` 37 (used with `attribute [local irreducible]`), `maxRecDepth` 34, `Elab.async` 1, plus linter switches. None of the options found disables kernel checking. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection: the five theorems in `Main.lean` have no explicit hypotheses and no type-class hypotheses of their own; the only instance argument inside the statements is `[NeZero N]`. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection: many internal names refer to assumed literature (directories `PublishedTheorems`, `PublishedInputs`, `LiteratureResults`, about 2,000 files in total; structures such as `Hypotheses`, `LiteratureHypotheses`, `GlobalAutomorphicGaloisHypotheses`). One structure, `UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop`, has three fields (`caraianiLocalGlobalDual`, `localLanglandsExists`, `galoisRepOfPolarizedPairLit`); in `MainConclusion.lean` it is filled with in-tree terms (`⟨h, UpperTheory.Zero.LLC.recTExists, h⟩`, with `h := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) rather than left as a hypothesis of the final theorem. — [part01](https://alpo.ge/lean.tar.gz.part01)
- What a clean result would look like, for comparison: the separate August 2026 Anthropic formalization is described as having "`#print axioms` returning only the three standard axioms" (`propext`, `Classical.choice`, `Quot.sound`). — [arXiv 2608.13637](https://arxiv.org/html/2608.13637v1)

### Inferences
- If the tree compiles as shipped, the absence of `axiom`, `sorry`, `native_decide` and `implemented_by` in the source means `#print axioms riemannHypothesis` could report at most Lean's three standard axioms. This is conditional on a successful build, which has not been reported.
- The naming suggests that literature results were at some stage carried as explicit hypotheses and later discharged inside the tree; "without assumptions" in the statement most plausibly refers to that final discharge. This is an inference from names and from one file, not something any source states.
- `kexactB`, `kcopy` and `cpt_copy_thms` bypass the elaborator's checks and lean entirely on the kernel. They are legitimate in principle, since `addDecl` and normal theorem elaboration send terms to the kernel, but they concentrate trust in the kernel and are the first places an adversarial auditor would look.
- A text search cannot rule out every trick (for example a kernel bug exploited through ordinary-looking terms). Only a build plus independent kernels addresses that.

### Gaps
- No published `#print axioms` output for `riemannHypothesis` or the other four theorems from any source.
- Not checked here: whether all `instance` declarations and `attribute [local instance]` lines (51,926 attribute-instance lines in 47,667 files) are benign; whether any definition used on the way has a degenerate meaning. These cannot affect the meaning of Mathlib's `RiemannHypothesis`, but they matter for understanding intermediate statements.

## 4. Who has independently built and checked it so far, and with what result?

### Takeaway
As of 14:48 UTC on 20 November 2026 nobody has reported a completed build, an axiom report, an independent-kernel check or a statement audit. Two people on the Lean Zulip said they had started compiling (Jack McCarthy at 13:58, Riccardo Brasca at 14:12, "In a sandbox"), and no result had been posted. No statement on the code was found from Terence Tao, Kim Morrison, Leonardo de Moura, the Lean FRO or other maintainers beyond the Zulip remarks quoted here.

### Cited Findings
- The discussion venue is the public Lean Zulip, channel `#general`, topic "Discussion: Alpöge Proves the Riemann Hypothesis": 21 messages between 13:58:06 and 14:39:48 UTC, none newer at the 14:48:17 UTC poll. It was the only topic on the claim in the public channels at that time. — [Zulip topic](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis)
- Jack McCarthy, 13:58:06: "Alpöge claims a full, unconditional Lean proof of the (generalized) Riemann hypothesis. I'm compiling it now on two separate devservers to verify the claim." (24 reactions.) — [Zulip, McCarthy](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642224678)
- Jack McCarthy, 14:05:45: "It's 17 million lines of code, zero comments or docstrings". — [Zulip, McCarthy](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642227002)
- Riccardo Brasca (Mathlib maintainer), 14:12:44 and 14:12:50: "I am compiling it" / "In a sandbox :D". — [Zulip, Brasca](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642229032)
- Riccardo Brasca, 14:23:53 (verbatim, typos in original): "it's also quite old so use comparator in paranoid mode is to available (and there is no challenge that only imports mathlib). I really hate that is not done "well"." — [Zulip, Brasca](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642232248)
- Riccardo Brasca, 14:29:46 and 14:29:54: "I dont have the time, and the tokens, to port to 4.36 and run a proper check, but it should be totally doable" / "17M lines is a lot but nothing crazy". — [Zulip, Brasca](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642233992)
- Floris van Doorn (Mathlib maintainer), 14:30:29: "It uses the Lean toolchain where all the kernel bugs that were mention in Leo's blog post were fixed. I don't recall a kernel bug after that (but there might be one). But as Riccardo says: we should be able to port the proof to a newer version of Lean and verify it there." — [Zulip, van Doorn](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642234267)
- Riccardo Brasca, 14:32:19 and 14:32:28, on what proper checking means: "we should test with state of the art tools that it really works." / "nanoda, con-leche etc". — [Zulip, Brasca](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642234870)
- Floris van Doorn, 14:32:38: "accidental exploit is very unlikely if `comparator --paranoid` succeeds. Malicious exploit is possible." — [Zulip, van Doorn](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642234917)
- Kevin Buzzard, 14:35:48, replying to "Malicious exploit is possible": "But this would have to find bugs in several independently-written kernels including at least one which is formally verified, no?" — [Zulip, Buzzard](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642235897)
- Shreyas Srinivas, 14:39:48, in reply: "Independent up to the choice of type checking algorithm iirc, because of the undecidability of the type theory." — [Zulip, Srinivas](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642237030)
- Terence Tao's most recent Mathstodon post at the time of checking (about 14:45 UTC) is dated 2026-11-10 and concerns his book; nothing on this claim. — [Tao on Mathstodon](https://mathstodon.xyz/@tao)
- Hacker News thread "Anthropic employee claims general proof of the Riemann Hypothesis [pdf]" (posted 14:16:21 UTC, 47 points and 8 comments at 14:45 UTC) contains no build or audit report; one commenter (14:45:06) notes "He has linked to the Lean formalization in this note." — [Hacker News item 50574968](https://news.ycombinator.com/item?id=50574968)
- Scientific American quotes no Lean expert and names no checker; it says experts should be able to verify fairly quickly whether the hypothesis is properly coded and the proof correct. — [Scientific American](https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/)
- What `comparator` checks, for context: for each listed theorem the solution must "Prove the same statement as provided in `Challenge`", "Use no more axioms than listed in `permitted_axioms`", and be accepted by the Lean kernel; extra kernels such as nanoda can be enabled; the challenge file's import closure must be trusted. Comparator was merged into Lean core as `lake comparator` / `lake check` as of v4.35.0. — [comparator README](https://raw.githubusercontent.com/leanprover/comparator/master/README.md)

### Inferences
- Status against the three levels: (A) build accepted by Lean: started by two people, no result; (B) statement audit: none published; (C) expert acceptance of the proof: none, and nobody in the thread claims it.
- Brasca's "no challenge that only imports mathlib" matches the tarball: `Statements.lean` imports only Mathlib but holds only definitions; the theorem statements sit in `Main.lean`, which imports the whole tree. A comparator-style challenge file would have to be written by the checker, which is a few lines.
- Because comparator moved into core at v4.35.0 and the tarball pins v4.33.1, the current comparator workflow cannot be applied without porting the 17 million lines to a newer toolchain or using the older stand-alone tool; that is the practical obstacle the maintainers are describing.

### Gaps
- No report yet from lean4checker, comparator, nanoda, lean4lean, con-leche or any export-based checker.
- X/Twitter and Bluesky posts by maintainers could not be read from this environment; Reddit could not be fetched. Statements there, if any, are not captured.
- McCarthy's and Brasca's hardware and expected build times were not stated.
- The thread is minutes old; all of this will be out of date quickly.

## 5. What issues have been raised about formal proofs of this kind, and this one in particular?

### Takeaway
The concerns voiced so far are about process rather than a found defect: an old pinned toolchain that blocks the current `comparator` paranoid workflow, no Mathlib-only challenge file, no repository, no comments, sheer size, and the non-zero chance of a kernel-bug exploit in 17 million machine-written lines. Nobody has reported an actual error, mis-statement or exploit in this code.

### Cited Findings
- Old toolchain and missing challenge file: Brasca, 14:23:53 (quoted in section 4). — [Zulip, Brasca](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642232248)
- Kernel-bug worry: Shreyas Srinivas, 14:27:13, "So is there a finite chance it exploited an old kernel bug?" and 14:31:39, "We can't rule out a newer bug or even an accidental exploit of an undiscovered bug in 17 million lines can we?"; Brasca, 14:32:19, "Of course this is possible, this is why we should test with state of the art tools that it really works." — [Zulip, Srinivas](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642233223)
- Background to that worry: Lean v4.33.1 (2026-08-21), the version pinned here, is the patch release that fixed kernel soundness bugs, including #14806 ("fixes a soundness issue in the kernel", a route to `False` through the `is_def_eq` cache), #14807 (the `is_prop` bug), #14838 (reference-count overflow that "could be extended into a proof of False"), #14582, #14808, #14849. — [Lean v4.33.1 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.33.1/)
- The Lean v4.34.0 notes (2026-09-14) describe the same fixes as "three soundness issues, found with AI adversarial testing", all "reported by Daniel Selsam (OpenAI) using their internal models". — [Lean v4.34.0 release notes](https://lean-lang.org/doc/reference/4.35.0-rc2/releases/v4.34.0/)
- Earlier in summer 2026 a kernel soundness bug (#14576) was exposed by a "CollatzLean" project claiming a Collatz disproof; secondary coverage says bugs in both the Lean kernel and nanoda were exploited together, that Leonardo de Moura published a postmortem dated 1 August 2026, and that Lean 4.32.2 with the fix was released 28 July 2026. (Secondary sources; the postmortem itself was not read.) — [Gigazine](https://gigazine.net/gsc_news/en/20260803-collatz-lean-kernel-bug); [oss-security advisory](https://openwall.com/lists/oss-security/2026/08/02/1)
- Presentation: Henson's "Not putting this into a Github repo is obscene" (14:17:52); McCarthy's "zero comments or docstrings" (14:05:45). — [Zulip, Henson](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642230537)
- Tarball inspection confirms the last point: no line in the 175,187 files begins with `--` and the string `/-` does not occur at all, so there are no comments, docstrings or module headers. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Understanding versus checking: the author himself writes "I am presenting the world with a complete argument before having mastered a massive neighbourhood around its mathematics", that for parts "in which Claude is the expert and not me I am sort of paraphrasing a "slop" summary, which might make zero sense … though the Lean should suffice to clarify everything", and that "the argument is incredibly long at the moment". — [remark.pdf](https://alpo.ge/remark.pdf)
- Comparator's own stated limits: its guarantees assume the Lean kernel is correct and the sandbox (`landrun`) holds, and that the challenge's import closure and lakefile are trusted. — [comparator README](https://raw.githubusercontent.com/leanprover/comparator/master/README.md)
- A Hacker News commenter (14:42:56) raised the readability concern: "if the proof is so convoluted and hard to read, is it actually something a human will ever find the time to go through and understand?" — [Hacker News item 50574968](https://news.ycombinator.com/item?id=50574968)

### Inferences
- Mis-stated theorem: the usual first failure mode for claimed Lean proofs of famous problems is unlikely to apply to the zeta statement here, because the top-level theorem is typed by Mathlib's own `RiemannHypothesis` constant and not by a project-local definition (section 2). This is this researcher's static reading; no source has said it yet.
- Reliance on unmerged Mathlib material: the lakefile depends only on the official Mathlib `v4.33.1` tag commit; everything else is inside the tarball. So the question is not "unmerged PRs" but that the tree itself must contain, unreviewed, whatever advanced theory the proof uses. Directory names (for example `EtaleCohomology`, `PAdicHodge`, `ResolutionOfSingularities`, `LocalLanglands`, `ClassFieldTheory`, `Chebotarev`, `ThetaCorrespondence`, `SiegelWeilFormula`) suggest that this is a great deal of mathematics that Mathlib does not have.
- The pinned toolchain already includes the summer 2026 kernel fixes, which supports van Doorn's remark; a port to v4.36 and a run through independent kernels is what the maintainers regard as the convincing test.
- The custom tactics that skip elaborator checks (section 3) raise the stakes on kernel correctness, which is exactly the area where bugs were found in July–August 2026.

### Gaps
- No concrete defect, exploit or mis-statement has been reported by anyone as of the snapshot. Absence of reports this early is not evidence of soundness.
- Leonardo de Moura's postmortem was not read directly; details above come from secondary coverage.

## 6. How large and how deep is the formal development, and how does the informal proof map to it?

### Takeaway
By this researcher's count: 175,187 modules, 17,374,215 lines (about 1.03 GB), roughly 819,000 `theorem`/`lemma` and 213,000 `def` declarations, a longest import chain of 203 modules, and every module reachable from `Main`. There is no blueprint, dependency graph, README or comment; the only informal outline is the 20-item dated timeline in the statement, which the author says was "provided" by Claude and may "make zero sense" in places.

### Cited Findings
- Tarball inspection, size: 175,187 `.lean` files; 17,374,215 lines, of which 1,842,456 blank; 1,030,531,854 bytes. Median file 58 lines, mean 99.2, largest 17,981 lines (`Formalism/HermitianCurvature/HermitianCurvatureProofs/IsAdmissibleSplittingCharPairMulTwist.lean`). — [part01](https://alpo.ge/lean.tar.gz.part01)
- This agrees with McCarthy's "17 million lines of code" and Brasca's "17M lines". — [Zulip, McCarthy](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642227002)
- Tarball inspection, files per top-level directory: `Development` 141,928 (767 MB); `Formalism` 18,254 (165 MB); `GroundTheory` 8,507 (55 MB); `ReciprocityTheory` 3,845 (29 MB); `CompanionTheory` 2,027 (11 MB); `PositivityTheory` 449; `Lemmata` 167; `BuildAid` 5; `Supplements` 3; plus `Main.lean` and `Statements.lean`. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection, largest second-level directories by file count: `Development/AbelianVarietyTheory` 99,187; `Development/AutomorphicArithmetic` 18,431; `Development/AutomorphicSpectrum` 15,147; `Development/WeilBound` 7,051; `GroundTheory/HeightsAndTheta` 6,410; `Formalism/LocalToGlobal` 5,501; `Formalism/PeriodIntegrals` 4,350; `Formalism/SharpRestriction` 3,093; `ReciprocityTheory/ReductiveGroups` 2,799; `Formalism/HermitianCurvature` 1,922; `Development/EtaleCohomology` 1,398; `CompanionTheory/SpectralGeometry` 1,254; `Development/ResolutionOfSingularities` 499. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection, declaration keywords at line start (regex count, approximate): `theorem` 784,092; `lemma` 34,663; `def` 212,819; `abbrev` 13,202; `structure` 8,286; `instance` 8,199; `example` 4,662; `inductive` 121; `class` 43. — [part01](https://alpo.ge/lean.tar.gz.part01)
- Tarball inspection, import graph: all 175,187 modules are reachable from `Main` (zero unreachable), so the default target needs the whole tree; the longest import chain ending at `Main` is 203 modules; 155,753 files contain `import Mathlib` (the whole library); external imports are only `Mathlib…`, `Lean…` and `Batteries…` modules. — [part01](https://alpo.ge/lean.tar.gz.part01)
- The statement's only outline is a numbered timeline "Claude provided after a thorough search", with items dated 10/6/26 to 11/16/26, for example "10/6/26: Stepanov determinant", "11/15/26: Iterated theta lifts U(X0) → U(X1) → · · · → U(Xm) between totally definite unitary groups", "10/6/26: Bost slope inequality", "10/14/26: Relative trace formula", "11/15/26: … fight for a significant weakening of Vandiver", "10/19/26: precise choice of the Iwasawa tower, specifically using Behrend!!", "11/16/26: GRH." — [remark.pdf](https://alpo.ge/remark.pdf)
- The author on the outline's reliability: "The parts in which Claude is the expert and not me I am sort of paraphrasing a "slop" summary, which might make zero sense, and I apologize, though the Lean should suffice to clarify everything." — [remark.pdf](https://alpo.ge/remark.pdf)
- The author on length: "it is routine to produce a huge, unreadable document containing sufficient detail"; footnote: "I of course amused myself, and hit 250, 000+ pages. Claude cutely called it the GRH . . . "book"". — [remark.pdf](https://alpo.ge/remark.pdf)
- Scale reference from the same day on the Lean Zulip, about a different project: an independent kernel ("Gruszka") re-checked a formalization of the classification of finite simple groups "in a bit over 3 h on 32 workers, 185 GB peak RAM" (Szymon Teżewski, 09:55:51 UTC). — [Zulip, "Lean checkers on FLT"](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Lean.20checkers.20on.20FLT/near/642161283)

### Inferences
- Some directory names echo timeline items (`ThetaCorrespondence/ThetaPairLifts`, `SiegelWeilFormula`, `UnitaryGroupMassFormula`, `WeilBound`, `IwasawaDecomposition`, `HarderNarasimhan`), but with no comments or blueprint any mapping from the 20 timeline items to modules would be guesswork; none is offered by the author.
- The short average file length (99 lines), the 4,000,000-heartbeat global limit and 57,556 local `maxHeartbeats` overrides are consistent with machine-generated code split into many small modules; no source states how it was produced.
- Because every file imports all of Mathlib and all files feed `Main`, a full build is a job for a many-core server; "17M lines is a lot but nothing crazy" (Brasca) is the only expert sizing so far.

### Gaps
- Build time, peak memory and hardware: no figure from the author or from anyone who has started a build.
- No blueprint, dependency graph or module-level description exists in the tarball or on alpo.ge.
- Declaration counts are regex-based and approximate; they were not obtained from a compiled environment.

## 7. Is there a GitHub issue tracker or discussion with findings, and what do the most substantive comments say?

### Takeaway
There is no repository and so no issue tracker. The only technical discussion found is the Lean Zulip `#general` topic (21 messages by 14:48 UTC); its substance is the maintainers' view that the right test is to port to a current Lean and run comparator plus independent kernels, and their irritation that the release was not packaged for that.

### Cited Findings
- No GitHub repository for this code: complaint by Chris Henson (14:17:52) and the fact that the only links are the 14 raw parts. — [Zulip, Henson](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642230537)
- Most substantive comments so far, in order: Brasca 14:23:53 (old toolchain, no Mathlib-only challenge); van Doorn 14:30:29 (toolchain has the kernel fixes from "Leo's blog post"; port and re-verify); Brasca 14:32:28 ("nanoda, con-leche etc"); van Doorn 14:32:38 ("accidental exploit is very unlikely if `comparator --paranoid` succeeds. Malicious exploit is possible."); Buzzard 14:35:48 (a malicious exploit would need bugs in several independent kernels, one formally verified); Srinivas 14:39:48 (independent "up to the choice of type checking algorithm"). — [Zulip topic](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis)
- Same thread, 14:35:57, Jack McCarthy: "In other news, Alpöge and Buckmaster have also claim to have proven Unforced Navier-Stokes https://github.com/tristanbuckmaster/navier-stokes/". — [Zulip, McCarthy](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642235936)
- Precedent for how the community treated earlier Alpöge formalizations: on 8 September 2026 Terence Tao wrote on the Lean Zulip that Alpöge and Buckmaster's fluid-equation proofs "are formalized in Lean and verified with comparator at https://github.com/tristanbuckmaster/fluid_lean . (It is all a rush job, for reasons explained in the mastodon post.)" — [Zulip, Tao, "Lean in the wild: Navier-Stokes proved"](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Lean.20in.20the.20wild.3A.20Navier-Stokes.20proved/near/622429170)
- Context only, a different result: Anthropic's August 2026 theorem that more than two thirds of zeta zeros are simple and on the critical line (arXiv 2608.13637) has its own Lean formalization "orchestrated by Eric Easley", reported with `#print axioms` showing only the three standard axioms, in the repository `github.com/anthropics/zeta-23-lean`, and Anthropic's write-up says it "passes the standard validation tool comparator". None of the 20 November sources read here (statement, Scientific American, Zulip thread, Hacker News) links that formalization to the new tarball, and search engines conflate the two. — [arXiv 2608.13637](https://arxiv.org/html/2608.13637v1); [Anthropic research post](https://www.anthropic.com/research/riemann-zeta)

### Inferences
- The contrast the maintainers are drawing is with earlier releases from the same circle that came as GitHub repositories checked with comparator; this one came as a bare tarball on an older toolchain.
- Until someone posts a build log, an axiom report and a comparator or independent-kernel result on a current toolchain, the formal claim is unverified by anyone other than its authors.

### Gaps
- No GitHub issues, pull requests or Mathlib tickets about this code were found.
- Whether the new tarball reuses any code from `anthropics/zeta-23-lean` was not checked.
- The Navier–Stokes repository mentioned at 14:35:57 was not examined; it is outside this assignment.
