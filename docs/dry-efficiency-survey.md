# Lean DRY / efficiency survey

> Historical. The older certificates and stepping-stone modules that this survey names (`225C`, `225R`, `226`, `226C`, `227`, `229`, `2285U`, `229U`, `230`, `232`, `22325R`, `LinnikCGLLegacy`, `LinnikCGLLinnik` and the modules only they used) have since been removed from the tree and are in the git history; the module names and counts below describe the repository at the time of each pass.

Snapshot: `main` at `268d99e` (after PR #4; sections 1 and 2's "before" columns); the second pass below is on `main` at `6df0ebd`, 1,158 `.lean` files under `lib/` outside `lib/vendor`
(`core` 349, `pnt` 743 before this pass and 744 after, `dh` 53, `zeta23` 11, `check` 2), about 28 MB.
How the numbers were obtained is stated for each one. **Measured** means run on this box; **derived** means computed
from the sources or from the repository's own generators; **estimate** means extrapolated and may be off by tens of
percent. Nothing here is a CI timing: CI has not run on this branch.

## 0. Second pass (Ritchie's instructions on PR #5: drop 22475R, act on the small items, delete the DH duplicates)

| Item | What happened |
|---|---|
| Drop `22475R` | **Done.** 139 files deleted (`SieveCert22475RP1..P135`, `SieveCert22475R`, `SieveGrid22475R`, `Linnik22475R`, `SieveTypeIIU22475C`; 7,153 lines). They live at commit `6df0ebd` on `main`; no tag. `Check`'s cone: 742 -> 603 modules, certificate parts 277 -> 142 (`SieveCert22325R` only, predicted 5.73 lane-h; the `22475R` 5.45 lane-h is gone). `CheckAll`: 1043 -> 904 modules, 509 -> 374 parts. `Check.lean` now imports `LinnikCGLDensity` and `SieveTypeIIU226C` itself (it prints `cglDensity` and `counts_7c`, which it had from the removed cone). `check_certificate.py` checks `22325R` only. No `.github` file mentions `22475`. |
| `LinnikCGLSteps` (item 5) | **Done** via `gen_cgl_curve.py`: macro `cgl_good`; 5,897 -> 3,176 lines, names and statements unchanged, `--check` matches, built; compile time unchanged (22.1 s vs 21.5 s). |
| `LinnikStairs`, `LinnikStairs7` (item 6) | **Done**: new `LinnikStairsGen` (tactics `stairs_good`, `stairs_good_y`, lemma `charDensity_ingham_inst`); 30 Ingham steps and 50 `Good` proofs use them; `LinnikStairs7` 2,429 -> 1,330 lines, `LinnikStairs` 718 -> 409; all names and statements unchanged; built with the downstream `SieveTypeIIU227/232/22325D`. |
| Mathlib re-proofs (item 8) | Done earlier (`0193c7f`). |
| CI step for `import_cone.py` | Not pushed (no `workflow` scope); no workflow file was touched. |
| `import Mathlib` trims (item 9) | Not done: no measurement here shows a saving, and a bulk trim risks hidden transitive imports (as the density chain showed). |
| Reproducibility gap (item 4) | Left. The `22475R` certificate can still be regenerated: `gen_22475r.py` with no options; `check_certificate.py` no longer compares it. 232 older part files (`225C`, `225R`, `2285U`, `229U`, `226`) have no generator invocation in the repository. |
| **`lib/dh` duplicates (item 3)** | **Not deleted, and the premise of the first survey was too strong.** The families are not copies: `DHLocate2Num`, `DHLocate3Num` and `DHLocate4Num` (0.39, 0.51 and 0.51 MB) are numeric instances for three different zeros, and `DHLocateFour` imports all three (`DHLocateNum`, `DHLocate2Num`, `DHLocate3Num`, `DHLocate4Num`), then `DHBohrSphere` and `DHJoins` build on it. The first survey hashed declaration bodies modulo numerals and the declaration name; whole files differ even after masking digits (`DHLocate2Base` vs `DHLocate3Base`: 610 differing lines), and no two files are identical. There is no canonical copy to redirect to. The only exact duplicate found is a 9-line lemma repeated in the three `*Base` files (18 lines). `lib/dh` is the separate `lean_lib DH`, in neither `Check`'s nor `CheckAll`'s cone, so it costs the default build nothing. The four missing generators remain the blocker for any real dedupe. |

## 1. Headline: the default build carried two legacy certificates that nothing it certifies needs

`lib/check/Check.lean` (the default target) imported `Linnik22475R` and `Linnik22325R` (this section is the first pass; `22475R` was dropped in the second). Their import cone, computed from
the sources (`scripts/import_cone.py`), reached `SieveCert225C` (167 certificate part files) and `SieveCert226`
(5 part files) through one chain:

```
Check -> Linnik22475R -> LinnikCGLDensity -> LinnikCGLHB101 -> LinnikCGLHBIter -> LinnikCGLHBRefl -> LinnikCGLRefl0
      -> LinnikCGLPair -> LinnikCGLReflect -> LinnikCGLMellin -> LinnikCGLS23 -> LinnikCGLMat -> LinnikCGLLinnik
      -> Linnik226C -> Linnik226 -> SieveCert226 -> SieveCert226P1      (and -> Linnik225C -> SieveCert225C -> ...)
```

`LinnikCGLMat` imported `LinnikCGLLinnik` only for two corollaries at its end (`linnik_225c_third`,
`linnik_226c_third`: Linnik at the exponents 9/4 and 226/100 from the cubic-trace hypothesis). The same pattern repeats
at each stage of the chain: `LinnikCGLS23`, `LinnikCGLS2`, `LinnikCGLS3`, `LinnikCGLP81`, `LinnikCGLHB101` and
`LinnikCGLDensity` each end with two such corollaries built on the previous stage's. No module of the density chain,
`Linnik22475R` or `Linnik22325R` uses any of the 14 corollaries.

| | before | after (this PR) |
|---|---|---|
| modules in `Check`'s cone (derived) | 925 | 741 |
| certificate part files in `Check`'s cone (derived) | 449 (22325R 142, 22475R 135, 225C 167, 226 5) | 277 (22325R 142, 22475R 135) |

Time. The repository's generator predicts 5.45 lane-hours for the `22475R` certificate and 5.73 for `22325R`
(`check_certificate.py` output; its model is `secs = work/180`). I timed three part files of the removed `225C`
certificate and one of `22325R` on this box (measured, one core each): the `225C` parts took about 105, 141 and 190
CPU-seconds (peak RSS 3.6 to 4.3 GB); the `22325R` part took about 68 s (peak RSS 4.0 GB). With a mean near 145 s for
`225C`, its 167 parts are **about 6.7 lane-hours (estimate, n = 3)**. The five `226` parts were not run (the README
says more than 10 GiB each), so their cost is unmeasured. So the default build's certificate work falls from about
`11.2 + 6.7 + (226)` to `11.2` lane-hours, and with `LEAN_HEAVY = 2` its floor from about 9 h to 5.6 h wall
(estimates). The 226 parts also no longer set the memory peak of the default build.

Nothing is removed: the corollaries moved to a new module, `LinnikCGLLegacy`, in their old namespaces with the same
names and proofs, and `CheckAll` imports it, so `CheckAll` still prints their axioms.

## 2. Ranked opportunities

Value is the saving or clarity gained; risk is the chance of breaking the proof or the CI; "verifiable here" is whether
this box could check it.

| # | Opportunity | Size (how obtained) | Value | Risk | Verifiable here | Status |
|---|---|---|---|---|---|---|
| 1 | Cut the legacy certificates out of the default build (section 1) | -184 modules, -172 cert parts, about -6.7 lane-h plus the 226 parts (derived / estimate) | High | Low | Yes, by compiling (see PR) | **Done** |
| 2 | `SieveCert22475R` (135 parts, predicted 5.45 lane-h) was in the default build for the superseded route | -5.45 lane-h, about -2.7 h wall at 2 heavy slots (derived) | High | Medium: changes what the default target certifies | Yes (mechanical) | **Done** (section 0): deleted, not moved; at `6df0ebd` |
| 3 | `lib/dh` generated families: 53 files, 9.1 MB; 71k duplicated declaration lines, of which 53k are across the `DHLocate{2,3,4}{Base,Exp,Num,Trig,Trig2}` copies, which differ in numerals only (derived: declaration bodies hashed modulo numerals and the declaration's name) | up to about 50k lines | High (size) / none (CI: `dh` is not in `Check`'s cone) | High | No (hours of builds, `CheckAll` only) | **Not done, and not safe to delete** (section 0). **18 of these files say they are generated by `gen_locate_zero.py` / `gen_locate.py`, and `gen_logext.py` and `gen_oddterms.py` are named too; none of the four generators is in the repository**, so the files cannot be regenerated or checked. Next step: add the generators and a `check_generated.py` like `check_certificate.py`, then dedupe at generator level |
| 4 | Certificates other than the two checked ones are not reproducible: `225C` (167 parts), `225R` (27), `2285U` (28), `229U` (5), `226` (5) come from earlier generator versions; `check_certificate.py` covers only `22325R` (and `22475R` until its removal) | 232 part files, 0.35 MB | Medium (reproducibility) | Low | Partly | Not done. Next step: `gen_22475r.py` flags for each tag, or delete the older certificates if the old theorems are not wanted |
| 5 | `LinnikCGLSteps.lean` (generated, 5,897 lines): 110 copies of a 30-line `ParC.Good` proof and a 20-line theorem. The statement-level duplication is already removed (`charDensity_cglGen`); what remains is the proof script (about 4.0k duplicated lines, derived) | about -2k lines by a tactic macro in the generator; no compile-time effect (the whole `LinnikCGLSteps` module built in 29 s, measured) | Low | Low-medium | Yes (regenerate + compile), but low payoff | **Done** (section 0) |
| 6 | `LinnikStairs`, `LinnikStairs7`: 30 near-identical step lemmas (about 1.2k duplicated lines; no generator in the repository) | about -1k lines | Low | Medium | Yes | **Done** (section 0), by shared tactics and a lemma rather than a generator |
| 7 | Hand-written near-copies across the Sieve family: `SieveTypeIIU22475C`/`225C`/`226C` (about 290 lines), `SieveTypeIIU2285`/`229`/`230` (about 165), `SieveTypeIIU226`/`227` (about 140), `Linnik226`/`227`/`229`/`230`/`232` and `SieveMain` (about 120 of boilerplate) (derived; all non-DH cross-module duplication totals 1.6k lines) | about 700 lines | Low | Medium | Yes | Not done |
| 8 | Mathlib re-proofs: a name scan of 163,532 Mathlib declaration names against the library's declarations whose last name component has 14 or more characters found 14 hits; two were exact re-proofs (`WindowForm.sin_sub_nat_mul_pi`, `sin_add_nat_mul_pi` = `Real.sin_sub_nat_mul_pi`, `Real.sin_add_nat_mul_pi`). The others are different statements or namespace collisions (checked: `Curvature.norm_prod_one_add_sub_one_le`, `QuadIdeals.sum_neg_one_pow`, `SieveLeaf.exp_neg_two_mul_le`; not checked: `card_multiples`, `mellinConvergent`, `differentiable_mellin`, `locallyIntegrableOn`, `im_inner_apply_self`, `intervalIntegrable`, `linearIndependent`, `isIntegral_iff`, `integral_kernel`) | 2 lemmas | Low | Low | Yes | **Done** for the two. A scan by statement shape was not attempted |
| 9 | 210 files `import Mathlib` in full (core 162, dh 31, pnt 13, zeta23 4). Targeted imports would cut module load time and rebuild triggers | unmeasured | Unknown | Medium: each file needs its imports found by trial | Yes, but a trial compile per file | Not done: no measurement to justify it |
| 10 | Lane balance of certificate parts: per-file work is at most 30,000 units (about 167 s by the generator's model) and at least 4,056, so with list scheduling the tail is at most one file, which is about 0.8% of the 5.7 lane-hours (derived) | negligible | None | - | - | Nothing to do |
| 11 | `LEAN_HEAVY = 2` on a 4-core, 16 GB runner: measured part peaks are 3.6 to 4.3 GB (n = 3 complete runs), so three at once would need about 13 GB beside Mathlib's mapping | - | - | - | Measured | Keep 2. (Six at once ran this box out of memory.) |
| 12 | CI stages: with sections 1 and 2 the cold build might fit two stages instead of three (estimate, needs CI evidence). Drop `build-3` only after a cold run shows it | up to one 355-minute stage | Medium | Medium | No | Not done |
| 13 | `scripts/import_cone.py`: prints a module's cone, certificate parts included, and `--why MODULE` prints the import chain that put a module there. It found item 1. A CI step that prints the cone of `Check` (`run: python3 scripts/import_cone.py Check` in the `checks` job of `ci.yml`) is a one-line follow-up that this PR leaves out, because the token used to push it cannot change workflow files | - | Medium | None | Yes | **Done** |
| 14 | Stale README numbers (`lib/pnt` 596 files, "307 certificate parts") | - | Low | None | Yes | **Done** |
| 15 | `#print axioms` lines: every module prints its own, so a cold build re-prints them; the traversals cost seconds in total | negligible | None | - | - | Nothing to do |

## 3. Why the rest was not attempted

The rule for this pass was to change only what compiles here or is provably equivalent. Items 3 to 7 are either
outside the default cone (so there is no CI saving), or have no generator in the repository (so a change cannot be
checked for equivalence), or save lines rather than time. Item 2 was the biggest unrealised saving; it is done in the second pass.

## 4. Verification of the implemented changes

See the PR description. In short: the seven density-chain modules, `LinnikCGLFrob`, `SieveTypeIIU22325D` and
`WindowForm` were built with `lake build` on the pinned Mathlib; `Linnik22325R`, `Linnik225R`,
`LinnikCGLLegacy` and `Check.lean` were elaborated against stand-in certificate modules (a scratch copy of each
certificate's assembly file whose final theorem is `sorry`, kept outside the repository), because the certificates
cost hours; `check_hygiene.py`, `gen_lakefile.py --check`, `check_certificate.py` (both tags) and
`gen_cgl_curve.py --check` pass. The full build and `check_axioms.py` are for CI.

Second pass: `lake build LinnikCGLSteps LinnikCGLDensity SieveTypeIIU22325D` and `lake build LinnikStairs LinnikStairs7
SieveTypeIIU227 SieveTypeIIU232 SieveTypeIIU22325D` succeed; `Check.lean` (37 `#print axioms` lines, all resolved) and
`Linnik22325R` elaborate against a stand-in for `SieveCert22325R` kept outside the repository (the only `sorryAx` is the
stand-in's); `check_hygiene.py`, `gen_lakefile.py --check`, `gen_cgl_curve.py --check` and `check_certificate.py
22325R` pass. Not verified here: the kernel build of the 142 certificate parts, `check_axioms.py`, `lake build CheckAll`
(the `dh` layer is unbuilt on this box), and every file of `CheckAll`'s cone that does not depend on a changed module.
CI is the final check.
