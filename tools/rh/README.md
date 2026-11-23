# The Lean archive of the claimed proof of the Riemann Hypothesis (20 November 2026)

On 20 November 2026 Levent Alpöge posted a statement (<https://alpo.ge/remark.pdf>) claiming, with Claude, a proof
of the Riemann Hypothesis and of its analogue for Dirichlet `L`-functions. The proof is given only as a Lean
archive, linked from the statement's first footnote. This directory fetches that archive, reads it and builds it,
so that its theorems can be joined to this library's.

On 23 November 2026 the build here was complete and checked: on the archive's own pins (Lean `v4.33.1`, Mathlib
`0df444a`) Lean's kernel accepts every one of the 1 777 302 constants that the archive's needed files compile to,
each checked against Mathlib and the constants before it (`bundle_replay.py`), and the archive's
`riemannHypothesis` (Mathlib's `RiemannHypothesis`) and `LFunction_eq_zero_re` (this library's `DirichletRH`,
stated independently in `scratch/rh-claim/RHClaim.lean`) rest on `propext`, `Classical.choice` and `Quot.sound`
only, read by walking 1 483 900 constants of the kernel's terms, Mathlib's included (`RHJoin.lean`). What that
takes on trust is Lean's kernel, the reader of compiled files, and the compiled Mathlib at that pin; how the files
were compiled (bundles, pins, copies) plays no part in it. See "The state of the build".

## The archive

| | |
|---|---|
| Source | `https://alpo.ge/lean.tar.gz.part01` … `part14`, 239 MB in all |
| SHA-256 of the 14 parts joined | `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` |
| Contents | `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json` and 175 187 `.lean` files under `lean/src`: 17.5 million lines, 1.03 GB, 1 067 553 declarations. No license, no README, no comments |
| Pins | Lean `v4.33.1`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (21 August 2026) and its usual dependencies, all from their official repositories |
| Imports | 155 753 files import all of Mathlib. The import graph has 203 levels and no cycle, and `Main` reaches every file |
| Statements | `src/Statements.lean` (imports Mathlib only) defines four propositions. `src/Main.lean` states five theorems with no hypothesis: `riemannHypothesis : RiemannHypothesis` (Mathlib's), the same unfolded, and three on every Dirichlet `L`-function: no zero on `Re s > 1/2`, and every zero in the open critical strip on `Re s = 1/2`, for all characters and for the primitive ones |

The archive is not in this repository, because it has no license. `fetch_archive.sh` fetches it into
`external/alpoge-rh/`, which `.gitignore` excludes. Nothing made from it (patched files, compiled files, exported
terms) is in the repository either.

## The scripts

| Command | What it does |
|---|---|
| `tools/rh/fetch_archive.sh` | Downloads the 14 parts, checks the SHA-256 above, refuses an archive with a member that is not a regular file or directory under `lean/`, and extracts to `external/alpoge-rh/extract/lean` |
| `python3 -I tools/rh/scan_archive.py SRC OUT.json` | Reads every file as text: the import graph, sizes, and the places that matter for running the code and for what its theorems rest on. Twenty minutes |
| `python3 -I tools/rh/decl_map.py SRC OUT_DIR --names NAMES.tsv` | Reads every file as text again, declaration by declaration: what each one names, resolved as Lean resolves names. One minute on ten cores. An estimate; its docstring says what it cannot see |
| `python3 -I tools/rh/decl_query.py MAP summary\|explain\|inputs\|path\|write …` | What a declaration reaches in that map, and why |
| `python3 -I tools/rh/capture_rewrites.py OUT.json` | The names and namespaces that a file would read otherwise in a bundle than under its own imports, each with what it means there, and the files of one level that must not share a bundle |
| `python3 -I tools/rh/pin_trace.py FILE NAME [DECLARATION]` | How one name of one file is read by the file's own imports and by a bundle: the first thing to run when a bundle fails on a name |
| `python3 -I tools/rh/unfold_overlay.py [--function Matrix.mulVec] [--full-only]` | The copies of the archive's files in which an `unfold` list is cut at a function whose `eq_def` some other file names (`unfold a f b` becomes `(unfold a; delta f; unfold b)`), for the files that do not see such a file: what `unfold` does for them alone. Written under `external/alpoge-rh/overlay`, which the build reads |
| `python3 -I tools/rh/dup_names.py OUT.json [--state STATE] [--keep OUT.json]` | The declarations of a name that another file declares too, and the other name that each is compiled under |
| `python3 -I tools/rh/bundle_build.py --out OUT [--jobs N] [--threads T] [--retry\|--replan] [--again BUNDLE …]` | Compiles the files that the top theorems need, about a hundred files to a process (`lean/Bundle.lean`), level by level of the import graph, and records every error against its declaration. Resumable; `--retry` compiles again the bundles with an error and those named with `--again` |
| `python3 -I tools/rh/bundle_slim.py --out OUT` | Writes beside each bundle the copy without the proofs of theorems that the bundles above import (`lean/Slim.lean`); `bundle_build.py` does it itself after each level |
| `python3 -I tools/rh/bundle_recheck.py --out OUT [--jobs N] [--bundle NAME …]` | Sends every constant of a bundle to the kernel once more, against the bundles below it as they are now (`lean/Recheck.lean`). It imports everything below for each bundle, half a minute to some minutes: the tool for the few bundles above a repair, while the build runs |
| `python3 -I tools/rh/bundle_replay.py --out OUT [--threads 8] [--fresh]` | The check of the whole build, in one process and one pass over the whole files (`lean/ReplayAll.lean`): starting from Mathlib it puts every constant of every bundle in the environment in the order of the levels, and the kernel checks each one, on all the threads, against Mathlib and the constants before it. Nothing of the build is imported and no copy without proofs is read. It also reports the axioms that a bundle declares and the axioms below that its constants name. A pass that was interrupted, or that follows a repair, starts checking at the first bundle that is new or changed (`OUT/replay.jsonl`). Eleven seconds of one core a bundle on the first levels; a single check can need 4 GB |
| `python3 -I tools/rh/proof_refs.py --out OUT BUNDLE …` | After bundles were compiled again: the bundles above them whose terms name a constant of theirs that is gone or has changed, read from the compiled files in a few minutes (`lean/ProofRefs.lean`). They are the ones for `bundle_recheck.py --bundle` to look at now, instead of at the end |
| `python3 -I tools/rh/bundle_check.py --out OUT NAME …` | For a theorem that the build holds: the axioms it depends on, the declarations compiled with `sorry` that it reaches, and the exact list of what it rests on, from the kernel's terms (`lean/Cone.lean`) |
| `python3 -I tools/rh/bundle_axioms.py --out OUT` | For the whole build, without importing it: the declarations of each bundle that are axioms, that name `sorryAx`, or that name an axiom other than `propext`, `Classical.choice` and `Quot.sound` (`lean/Axioms.lean`). With none, and every bundle accepted by `bundle_recheck.py`, no theorem of the build rests on more than those three |
| `python3 -I tools/rh/bundle_files.py --src ROOT --out OUT --workspace WS TARGET` | The same compiler for any tree of Lean files, one file a process with its own imports, with every error of every level in one run. For a port |
| `python3 tools/rh/port_tree.py make\|save\|status\|errors TREE` | The tree of the port: the library's files that `RHClaim.lean` imports with the port's patches applied; the patches written back from the tree; the recorded errors of a file with the lines around them |
| `python3 -I tools/rh/simp_diff.py OLD NEW OLD_NAMES NEW_NAMES` | How the simp sets of two versions of Mathlib differ (`lean/DumpSimp.lean` writes them), as far as a port can undo it |
| `python3 -I tools/rh/build_archive.py` | The first driver: one `lean` process a file. Exact, and twenty times slower; kept for a file that must be compiled alone |
| `python3 -I tools/rh/fp_compare.py OLD.tsv NEW.tsv [--by-name] NAME …` | Compares two environments constant by constant at the level of the kernel, from the fingerprints that `lean/Fingerprint.lean` writes |
| `lean/Export.lean`, `lean/Replay.lean` | Write what a theorem rests on as kernel terms, and check them again with the kernel of another version of Lean, with no elaboration |
| `python3 tools/rh/driver_test.py [--driver COPY]` | Sixteen jobs of two small files each (`lean/tests/`), one for each thing that `lean/Bundle.lean` had to learn, run under the archive's toolchain and the library's: what a change to the driver has to pass before it replaces the file |
| `python3 tools/rh/replay_test.py [--workspace DIR]` | What `bundle_replay.py` has to refuse: five files of a few lines (`lean/tests/replay/`), compiled, with one constant of a compiled file changed by `lean/Tamper.lean` (a theorem with the proof of another, a statement changed below a proof that uses it, a definition with another body, a proof taken away, a theorem made an axiom, a `sorry`, one name with two statements). The pass must accept the files as compiled and name exactly the constants that no longer hold; and on a made-up build of three bundles, check again what a change reaches and nothing before it. Passes under both toolchains |
| `lean/DumpNames.lean` | The names of an environment's constants, with the new name of each deprecated one |

`python3` is `/opt/homebrew/bin/python3` here, and every command wants `~/.elan/bin` on the `PATH`.

The archive's own pins need a workspace that holds only them:

```sh
mkdir -p external/alpoge-rh/native-ws && cd external/alpoge-rh/native-ws
cp ../extract/lean/lean-toolchain ../extract/lean/lake-manifest.json .
printf 'name = "nativews"\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4"\nrev = "0df444a360eaa60ab8c11dca51a86af692955474"\n' > lakefile.toml
lake exe cache get && cd ../../..
```

The whole pipeline, from the fetched archive:

```sh
python3 -I tools/rh/scan_archive.py external/alpoge-rh/extract/lean/src external/alpoge-rh/scan.json
# the names of Mathlib at the archive's pin: tools/rh/lean/DumpNames.lean with a line
#   #dump_names "…/external/alpoge-rh/names/names_native.tsv"
# added, run with `lake env lean` in native-ws; aliases_native.tsv, the names that Mathlib exports from a
# namespace with what each stands for, is `getAliasState` written out the same way
# protected_native.tsv, the protected constants, is `#dump_protected` of the same file
python3 -I tools/rh/decl_map.py external/alpoge-rh/extract/lean/src external/alpoge-rh/declmap \
    --names external/alpoge-rh/names/names_native.tsv --names external/alpoge-rh/names/aliases_native.tsv \
    --protected external/alpoge-rh/names/protected_native.tsv
python3 -I tools/rh/dup_names.py external/alpoge-rh/dup-renames.json
python3 -I tools/rh/unfold_overlay.py
python3 -I tools/rh/unfold_overlay.py --function Finsupp.prod --full-only
python3 -I tools/rh/capture_rewrites.py external/alpoge-rh/rewrites.json
caffeinate -i python3 -I tools/rh/bundle_build.py --out external/alpoge-rh/bundle-native --jobs 5 --threads 3 --retry
python3 -I tools/rh/bundle_replay.py --out external/alpoge-rh/bundle-native
python3 -I tools/rh/bundle_check.py --out external/alpoge-rh/bundle-native riemannHypothesis
```

## What compiling the archive runs

Elaborating Lean runs the tactics, macros and commands of the files, so the archive was read before anything was
compiled. A search of all 175 187 files finds:

- no `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `#eval` or `debug.` option.
  The word `admitted` occurs thousands of times, always as the name of a declaration or a field;
- no call that reads or writes a file, starts a process, reads the environment or opens a connection;
- `run_cmd` in five files (`BuildAid/D1.lean` … `D5.lean`): each adds one namespace to the deny list of Lean's
  library suggestions;
- four `elab` declarations: the tactics `kexactB` and `kcopy`, which assign a term to the goal without the
  elaborator's check, the command `#kcopy_probe`, and the command `cpt_copy_thms`, which copies a few dozen
  declarations under their names with `Cpt` added, with `addDecl`. They read and extend Lean's environment and do
  nothing else. What they add still goes through the kernel;
- 77 `macro` declarations, each a tactic or term written with a syntax quotation, and 32 uses of `run_tac`, 30 of
  them to revert the hypotheses of a goal.

Every compile still runs under `sandbox-exec` (macOS): no network, no write outside the output directory, and of
the home directory only the toolchain, the packages, the sources, the output and these scripts are readable.

## Where the time goes

Measured on an M2 Pro with 12 cores and 32 GB, on the archive's own pins.

- **One process a file is almost all import.** `lean` on a file that holds only `import Mathlib` takes 4.4 s (the
  files of Mathlib are mapped, not copied: 136 MB of the process's own memory). Over 441 files compiled one by one,
  eight at a time, the time fits 8.2 s + 7.1 ms a line, and the files have 100 lines on average: 94% of the time is
  the import. At that rate the 175 187 files take 340 CPU-hours and more.
- **Many files in one process.** `lean/Bundle.lean` imports once, then elaborates each file of a list in turn, each
  with its own command state, its own module name (so its private names are its own) and its own scope for scoped
  attributes and `open`, and writes one `.olean` for all of them. Forty files of the first level took 24 s of
  elaboration against 524 CPU-seconds one by one. A process has 3 GB of its own once it elaborates, which is what
  limits how many run at once: four or five here, not twelve.
- **Proofs on the other threads.** With `Elab.async`, as in `lean` itself, the proof of a theorem is elaborated and
  every declaration is checked by the kernel on the process's other threads. The same 92 files took 34 s instead
  of 53 s with three more threads, and gave the same output.
- **The import comes back.** To import a module Lean looks at every constant in it, and in a compiled file the
  constants lie among their proofs: an import reads every page of every file below. At the 34th level that was
  819 bundles and 30 GB, more than five processes of 4 GB leave free in 32 GB, so each import read most of it
  from the disk again (800 000 page faults for one import): 140 to 230 seconds a bundle, against 110 to 180 for
  compiling it, and growing with every level; the kernel check of the whole build at the end would have paid
  the same for each bundle. What is built on a theorem needs its statement and not its proof: the elaborator
  never unfolds a theorem, and for the kernel two proofs of one statement are equal. So beside each bundle a
  copy is kept in which the value of each theorem is a constant that does not exist (`lean/Slim.lean`,
  `bundle_slim.py`; a fifth of the size, three seconds a bundle), and the bundles above import the copies:
  20 to 50 seconds an import. A bundle is still written whole, and each proof is checked from its own bundle's
  whole file, when the bundle is compiled and when `bundle_recheck.py` checks it again; `bundle_check.py` reads
  what a theorem rests on from the whole files. A check that passes against the copies passes against the
  whole files, since it never looked at a proof. The kernel does look at one when it computes a function
  defined by well-founded recursion (it unfolds the proof that the recursion ends): it then stops at the
  missing constant, says so, and the bundle is compiled, or checked, again against the whole files
  (`whole-imports.json`; six of the 130 bundles of the 35th to the 46th level, and about one a level after
  that, at ten minutes each). Since the 65th level the missing constant bears the name of its theorem
  (`_slim_.T`), so the kernel's message says which proof it wanted: that theorem keeps its proof in the copy
  of its bundle from then on (`slim-keep.json`), the copy is made again, and the bundle is compiled, or
  checked, once more against the copies. At the 87th level one bundle took five compilations that way: its
  proofs make the kernel run a proof by recursion (`iter_levels`), the kernel reduces each proof to a
  constructor, a proof is as a rule another theorem applied to proofs, and each compilation showed one more
  link of the chain before the whole files were used. So `lean/Slim.lean` now names, for each proof that a
  copy keeps, the constants at the head of that proof, and `bundle_build.py` keeps the proofs of those too,
  and of theirs, nearest first, up to 250 at a time (`keep_chain`): a minute for the copies of the hundred
  bundles that hold them, 40 MB more to import, and one compilation instead of five.
- **What a bundle changes.** A file sees the declarations, instances and simp lemmas of the files before it in its
  bundle and of every bundle below, also of those it does not import. That is the one difference from `lean` on
  the file alone; the archive's imports are loose already (a file that proves RH from one statement imports 210
  modules and needs none). The kernel checks every declaration as before, and a theorem's axioms are read from
  the result, so a bundle cannot make something true: it can only make a proof fail that passes alone.
- **Where it does make a proof fail**, and what `bundle_build.py` does about each. All were met in the first
  23 000 files:
  - *Two private declarations with one name.* Lean keeps the declarations of the module it compiles under their
    names without the private prefix, so `private theorem key` in two files of one bundle is a panic and the
    second is lost. 3 802 private names are in more than one file. What a `local notation` declares is private
    too, and named after its atoms: 168 of those are in more than one file. Such files go to different bundles.
  - *A private name that is public elsewhere.* A file that declares `private theorem main` and sees a public
    `main` that it never imports is refused. 22 declarations in 17 files; each is renamed in its file, by
    `Bundle.lean`, on the parsed identifiers.
  - *Part of Mathlib.* 56 files never see all of Mathlib, and one of them reads `Finset.antidiagonal` otherwise
    when it does. They are compiled one to a bundle, with exactly their own imports.
  - *A name captured.* `discr E` under `open NumberField` means `NumberField.discr`, until a file that is not
    imported declares `PI.discr` in the namespace at hand. And `open WittVector` inside
    `namespace GlobalTheory.WittGauss` opens `GlobalTheory.WittVector`, and only that, once a file that is not
    imported declares something there. `capture_rewrites.py` reads every name of every declaration in three
    views: the file's own imports, all the lower levels (what a bundle shows), and the lower levels with the
    file's own. Where the second differs from the first, the name is pinned to what the file meant
    (`_root_.NumberField.discr`, `open _root_.WittVector`): 28 067 names and 1 895 namespaces (and the namespace of
    49 841 `open N (a b)`, below), in 32 984 files;
    `Bundle.lean` replaces them on the parsed identifiers. Where the third differs from the second, the two files
    are of one level and go to different bundles (356 pairs, beside the 454 files that the map's own references
    keep apart). The cases that this had to learn, each from a failure:
    - a namespace that the file itself makes counts for an `open` only from the line where it makes it:
      `namespace GalTw` … `open GlobalTheory.RoadU` … `namespace GlobalTheory.RoadU` opens the root's
      `GlobalTheory.RoadU`, the file makes `GalTw.GlobalTheory.RoadU` three lines later, and in a bundle a file
      of the same directory has made it before (`Unknown identifier CharLift`, 104th level; 15 more pins);
    - a command that is not a declaration has no entry in the map and can name a constant too
      (`variable {r : G E Ω →* K}`): it got the pins of its file's declarations (755 names), until `variable`
      commands were given entries of their own (below);
    - a file's own private declaration needs a pin like any other: `private theorem mem_box` at the root beside
      an opened namespace that holds a public `mem_box` of a file not imported is ambiguous, and a private one
      in an opened namespace is hidden by a public one in the namespace around. The pin is then to the private
      name;
    - 406 names resolve to two constants in the file's own view, between which Lean chooses by type (`borel`:
      Mathlib's, or the one of an opened namespace), and a third constant of a file not imported hides both.
      The identifier is then replaced by a choice of the two, as an overloaded notation is;
    - `open A.B C` opens `A.B.C` if there is one, and a name found that way is a constant too (and
      `open _root_.A` is `A`); `open N (a b)`
      shows `a` and `b` only, and taking it for all of `N` made a choice of two where the file has one; an
      `open … in` inside a proof opens for the rest of it, and the names found through it make their files
      needed; and an `open` of a namespace that is around one declaration is still to be followed for the
      next one outside it (the map had kept the shorter list, and a file whose names were reached that way
      was never compiled: "unknown identifier" three levels up);
    - a name that `export N (a)` makes stands for `N.a`, and the pin is to that: a file not imported may declare
      a constant of the very name. Mathlib exports 634 names this way (`mul_mem` is `MulMemClass.mul_mem`);
      they are no constants, and the map, which knew Mathlib's constants only, took `mul_mem` for a local
      variable until an archive `P5.mul_mem` around the file captured it;
    - a name bound in a chain of bracketed groups that runs over lines, or after a group with brackets inside
      (`∀ (K : F ℚ_[p] (G p))` … `(A T' G : Type)`), is a variable: the map missed the later groups and a pin
      replaced the binder. `Bundle.lean` now also leaves a name alone in a command that binds it;
    - two files that a third imports may both declare a theorem of one name and one type up to the kind of
      binders (Lean keeps the one imported last, and the two differ in which arguments are explicit): the pin
      is to the one that the file's own order of imports keeps;
    - a field that a `structure` declares, or that an instance gives a value, is not a reference, though a
      constant of that name may be in view: pinning it broke the structure. And the other way: in
      `(hE : (divCycle P s E : ℤ) = 1)` the inner group is a term with its type, not a binder, and a line of a
      statement that begins with a function named `ext` is not the tactic. The map took the names in both for
      bound, and they went without a pin. So it did with what follows a function named like a tactic inside a
      term: in `(congrArg g (funext hxs)).trans (psum_one t.G I)` it read `funext` as the tactic and the rest
      of the line as the names it introduces, and `psum_one`, which a file not imported made ambiguous, had no
      pin. The names that a binder word introduces now end at the bracket that closes around it. A field on a
      line of its own (`cpt := fun b hb => …` between the braces of a structure instance) the map still takes
      for a reference, and a constant `cpt` of a file not imported then had the field renamed: "`_root_` is not
      a field". That is now settled where it can be known: `Bundle.lean` never replaces what the parser gives as
      the name of a field, or of an argument in `(x := v)`;
    - a name with a dot whose first part the declaration binds somewhere may be a constant all the same:
      `T.isTangent_constant_coords_generic_fibre` is a theorem of the namespace `GlobalTheory.T`, in a proof
      that also has a variable `T` in a `fun`. The map took every `T.x` there for a field of the variable, the
      theorem's file was not needed, and the name was unknown. Such a name is now followed when the whole of
      it is a constant (606 references, 57 files more), and never pinned;
    - the name of a field of a `structure` is the field only from the next field on. In
      `twist : ∀ …, Nonempty (π'.π.Equiv (twist π.π χ)) → …` the second `twist` is the function of an opened
      namespace, which a file not imported had captured; the map took both for the field. It now keeps the
      name as one to look up when the field's own type uses it, and `Bundle.lean` goes through the fields of a
      `structure` in order: it never replaces the name that a field declares, and stops replacing that name
      after it;
    - `open A in` / `attribute [local instance] A.inst in` / `theorem …`, on three lines, is one command, and
      the `open` is for the theorem. The map read the middle line as a command of its own, which took the
      `open` with it: a name of the theorem found through `A` resolved to nothing, and had no pin (710 such
      lines). They are read as a prefix now, and what they name is needed with the theorem;
    - a `variable` command is elaborated whether a declaration uses its variables or not, so what it names
      must be there, and may be captured: `variable … (hI : SIso D.s (sOf hF))` on the last line of a file,
      with an `sOf` of the namespace around from a file not imported. Such a command had the pins of its
      file's declarations and none of its own. It has an entry in the map now (121 000 of them), is pinned by
      what it names, and what it names is needed with its file;
    - `variable (h : IsPlaceOver A w) in` before a `def` gives the definition a binder. The map skipped such
      a line (12 679 of them) with the `set_option … in` lines, so that what it names was neither followed
      nor pinned, and an `IsPlaceOver` that two opened namespaces hold, one of them from a file not imported,
      was ambiguous there and nowhere else in its file. The line is read with the declaration now;
    - the map follows a name to what the whole archive makes of it, and pins it to what the file's own imports
      make of it; where the two differ, the declaration that the file means was pinned and not followed.
      `core_of` under `open Leaf2Aux` is `Cz.Leaf2Aux.core_of`; a file not imported has a `BcB.core_of` in a
      namespace around, the map went there, and the file of the first was never compiled: "unknown
      identifier `_root_.….Leaf2Aux.core_of`", at the seventy-eighth level. `capture_rewrites.py` now also
      gives what each pinned name refers to (31 243 references), and `bundle_build.py` follows them; fifteen
      files more were needed;
    - a field of a structure instance is not a variable: in `def cxStage : CxSt F where … Met := Met …` the
      second `Met` is the function of an opened namespace. The map had taken the names of fields for bound,
      so that they would not be pinned where they are declared; `Bundle.lean` knows those places itself by
      now, and the map lets the names be looked up. (A captured `Met` left the field without a value, and
      every proof of the structure that needed it failed on a goal with a hole in it.) 48 pins more;
    - the names that a quantifier binds end at `∂` and at `in`: in `∀ᵐ q ∂quotMeasure Γ μ, …` the map took the
      measure for a bound name too, and in that one theorem of its file `quotMeasure`, captured by a namesake
      of a file not imported, had no pin: the theorem was stated about the other measure and its proof did not
      fit (1 709 references more, 7 pins);
    - `open N hiding a b` does not show `N.a`. The map took it for all of `N`, so a name that the file hides
      there and finds in another opened namespace had two readings, the pin was a choice, and in a `simp only
      [embT, …]`, where no type decides, the choice was "ambiguous". 66 choices became one name;
    - a variable stays a variable in a later `variable` command. After `variable {O V Q G C : Type}`, the
      command `variable (gl : G → Γ)` names that `G`; the map had only kept the names that a `variable`
      command binds itself out of what the command uses, so `G` went to every declaration below as a name
      to look up, an opened namespace of the archive holds a constant `G`, and the pin made the variable that
      constant ("type expected"). 5 055 references of that kind are gone from the map, with 46 pins;
    - a namespace opened inside a declaration is captured like one opened by a command. The archive has a
      namespace `GlobalTheory.CompanionTheory.Classical`, of one file, and 4 272 files write `open Classical in`:
      a definition under `GlobalTheory.CompanionTheory` whose body says `open Classical in if InFibre ξ p q
      then …` opened that namespace in the bundle, and found no way to decide the condition. Such an `open` is
      now read and pinned as the others are (29 more pins).

    1 991 names resolve to nothing in the file's own view: local variables that the map took for constants,
    left alone. One name was pinned by hand before the choices were there (`external/alpoge-rh/pins-manual.json`).
  - *A name declared in two files.* Lean lets two modules declare one name as long as nothing imports both.
    The archive does it for 133 names, and for 89 of them the two texts differ; for some the statements do
    (`wd_congr` takes a number in one file and a proof in another). Two modules with one theorem of one
    statement can be imported together, and the first build relied on that: within a level the two files went
    to different bundles, and across levels the upper declaration was left out. With two statements that fails.
    So each declaration of such a name but the first is compiled under another name (`wd_congr_b2`,
    `dup_names.py`): `Bundle.lean` renames the declaration in its own file, with the places of that file that
    reach it by the type of a term (`h.wd_congr`), and the name is pinned in every file whose own imports give
    that declaration. 116 declarations in 72 files; the files that the build had already compiled keep the older
    treatment, but for one whose first declaration is in a file that the build does not compile at all. Every
    declaration of such a name is held needed: the map's reference goes to the first, and the file that uses the
    name may import another.
  - *`open N (a b)`.* The command is an error if `N.a` is not a constant, and a file may list a name that it
    never uses: the build compiles only the files whose declarations are used, so the file that declares `N.a`
    may not be there. `Bundle.lean` drops such a name from the command, also in `open N (a b) in …`.
    The command is an error too if Lean finds a name twice among the namespaces that `N` may be, and in a
    bundle it can find one constant twice. After `open A`, `open Chart (JetR zR)` means `A.Chart`; if a file
    that is not imported has made a namespace `Chart` at the root, Lean also looks there, finds no
    `Chart.JetR`, looks the name `Chart.JetR` up as it would in a term, reaches `A.Chart.JetR` through the
    `open A`, and reports "ambiguous identifier `JetR`, possible interpretations: [Chart.JetR, Chart.JetR]".
    The first version of the repair above then dropped every name of the list, since it looked for them
    around the command only, and seventeen proofs failed on unknown identifiers. The archive has 49 845 such
    commands. In each, `N` is now pinned to the one namespace in which the file's own view finds all the names
    (`open _root_.A.Chart (JetR zR)`; 49 841 of them), and for the rest `Bundle.lean`, when the command
    fails, names the namespace outright itself if one namespace holds the names that are there.
  - *`open private a from M`.* 157 files open a private declaration of another by the name of its module, and a
    file that a bundle holds is not a module. `Bundle.lean` does the command itself, from the private constants
    that still bear the file's name. A private declaration is named by no one outside its file, so the map has
    no reference to it: a file of which only private lemmas are used, through such commands, was needed by
    nothing and not compiled ("unknown module", four files of the 103rd to 105th level). `bundle_build.py` now
    holds needed the declarations that the `open private` commands of a needed file name (220 commands, 114
    modules, kept in `open-private.json`): 48 more files.
  - *A field under an opened namespace.* `B.host.splitsC_facts` is `Formalism.HC.HostAx.splitsC_facts` by the
    type of `B.host`, and Lean looks that name up through the namespaces that are open: the theorem is
    declared as `UpperTheory.HF.Formalism.HC.HostAx.splitsC_facts`, in a file that only `open`s
    `UpperTheory.HF`. The map followed a field `h.foo` to `N.foo` for the structures `N` it had reached, and
    not to `O.N.foo`; the theorem's file was not needed, not compiled, and the field was "not in the
    environment". The end of a namespace now counts as the structure (142 more files are needed).
  - *A protected name.* `protected theorem Matrix.sub_mul` is not what `sub_mul` means under `open Matrix`: Lean
    finds a protected constant only under a name of two parts or more. The map did not know which constants
    are protected, so for `rw [sub_mul]` in a file that opens `Matrix` it saw two readings in the file's own
    view; when a file not imported added a third, the pin was a choice of the two, both of which elaborate
    where no type is expected, and the rewrite was "ambiguous". The map now has the protected constants of
    Mathlib (`lean/DumpNames.lean`, `#dump_protected`) and marks the archive's: 87 choices became one name.
  - *A lemma that Lean makes on demand.* `unfold f` rewrites with `f.eq_def` if the environment has it and,
    for an `f` that is not recursive, puts the body of `f` in its place otherwise; the two differ where `f` is
    not applied to all of its arguments (`M *ᵥ fun a => …`: the first "fails to unfold"). Lean makes `f.eq_def`
    when something asks for it and keeps it in the compiled file of whoever asked. Four files of the archive
    name `Matrix.mulVec.eq_def`, the first at the third level, so in a bundle every file above has the lemma,
    and alone only a file that imports one of the four: none of the 29 files that unfold `mulVec` does. Three
    proofs failed on it, one at a time, before the rest were counted. `unfold_overlay.py` now writes, for each
    such file, a copy under `external/alpoge-rh/overlay` with the list cut at the function
    (`unfold a Matrix.mulVec b` becomes `(unfold a; delta Matrix.mulVec; unfold b)`, which is what `unfold`
    does without the lemma): 21 files, 25 lists, beside the two lines first changed by hand; and the same
    for `Finsupp.prod`, whose `eq_def` one file names and 109 files unfold (132 lists), before any of them
    failed. `bundle_build.py` compiles such a copy in place of the archive's file. Nothing else of the
    archive's text is changed. The archive names the `eq_def` of twelve more functions, in 15 places; nine
    are unfolded nowhere else, and the three others (`mid`, `pj`, `invN`) by a short name that may be another
    function's, so they are left until one fails.
  - *A lifted proof named.* Lean lifts the proofs inside a definition out as `d._proof_1`, `d._proof_2`, and
    uses one again when the same statement comes up in the module; 15 files name such a constant, in 40 places
    (`attribute [local instance] S.lf._proof_1`), and no other kind of name that Lean makes and that depends on
    what else is in the module. Across the files of one process that sharing gives other names: a definition
    whose only lifted proof an earlier file of the bundle had made has no `_proof_1` at all, and one whose first
    of two was shared calls the second `_proof_1`. So `Bundle.lean` now starts each file with none shared, as
    the file has alone, and the ten bundles that hold a definition so named were compiled again.

    That repair is the one that changed what the bundles above rest on. The term of a declaration that unfolds
    `d` names `d._proof_2`, and 316 of the 501 bundles above those ten name a lifted proof of theirs. A lifted
    proof that got another number is another statement under the old name, and the bundle above that names it
    no longer passes the kernel: it was checked before, and nothing compiles it again. Two things were done.
    The 572 bundles made before the change are compiled again, when they have to be, as they were made
    (`shareProofs` in the job; `bundle-native/shared-proofs.json` lists them), so that a later repair does not
    renumber their lifted proofs and start the same thing higher up; `bundle_build.py --own-proofs` takes a
    bundle off that list, which is what was done to the ten. And `proof_refs.py` finds, from the compiled
    files, the bundles above a bundle compiled again that name a constant of it which is gone or not the same
    (`bundle_build.py` keeps what the bundle held as `<name>.olean.before`; for the ten, compiled again before
    that, it finds the lifted proofs that can have been renumbered: 45 bundles name one). Those bundles are
    checked by the kernel at once (`bundle_recheck.py --bundle`), and the ones it refuses are compiled again.
  - *`open Topology in`.* The parser itself opens the namespace for the rest of the command, to read its
    notations, before `Bundle.lean` can pin the name on the parsed command; where a file not imported has made
    a nearer `Topology`, `𝓝` is then an unknown identifier. For those lines the pin is made in the text, in a
    copy of the file that `bundle_build.py` writes (`overlay-auto/`).
  - *An instance, or a simp lemma, of a file that is not imported.* The worst case met: a file of the first
    level makes an instance of a field of a structure (`attribute [instance] Frame.hl`, a
    `Fact (Nat.Prime Φ.l)`), and from then on the instance searches of unrelated files wander into it and run out
    of budget: 26 declarations failed at the third level, in 18 files, nearly all on the same search. The map
    does not know what a search will use, so this is done in the compiler: `Bundle.lean` writes down what each
    file adds to the instances and to the simp set, and for each file of a later bundle everything that was added
    by a file it does not import is erased, in a scope that ends with the file. So a file sees the instances and
    the simp lemmas of its own imports, as it does alone. (The budget of an instance search is also ten times the
    default, `synthInstance.maxHeartbeats`.) Other sets that tactics read (`ext`, `fun_prop`, `norm_cast`, `aesop`)
    are not treated.

  - *The order of two instances.* When a file imports two instances that fit a goal equally, Lean tries the
    one that was imported last first. Alone, that is the order of the file's own header, module after module;
    in a bundle it is the order of the levels. The archive declares `MeasurableSpace (Matrix m n k)` three
    times, as the product structure and as the Borel one (and removes one with `attribute [-instance]` in
    eight files); a proof that imports two of them and needs the first got the second, and a measure built on
    the one did not fit a lemma stated with the other. Three levels on, the other way round: two files state
    lemmas with two `Module` structures on a stalk, a third converts one statement into the other and closes
    the difference with `rfl`; in a bundle both files had chosen the same instance, the difference was not
    there, and the `rfl` met the next goal. 306 keys of the table of instances have instances from two files
    or more in the first 43 levels, and two files in three of the levels that follow see some of them in
    another order than a bundle does. So `Bundle.lean` writes the key of each instance beside its name
    (`lean/DumpInstKeys.lean` gives the keys of the bundles made before), `bundle_build.py` works out for each
    file the order in which Lean would import its modules, and where instances of one key come out otherwise,
    `Bundle.lean` makes them change places in the table for that file. The first of the two failures was
    repaired by hand before that (`external/alpoge-rh/hide-manual.json`: an instance taken out of one file's
    view), and the rule gives the same answer there. A bundle compiled in the new way states its theorems
    with the instances that its files find alone; the second failing bundle, compiled again, changed three
    statements that two bundles of the next level had already used, and the kernel accepted both against the
    new statements (the instances are equal by unfolding). The 974 bundles made before
    (`bundle-native/bundle-order.json`) keep the order of the bundles if they are compiled again without
    having failed, so that their statements stay what the bundles above were checked against.

  - *A limit of the file's own.* `set_option maxHeartbeats 1000000 in` before a theorem is the limit that fits
    the proof when its file is compiled alone. In a bundle the same elaboration takes more, because the tables
    of instances and of simp lemmas hold the whole archive below, and the proof ends in "(deterministic)
    timeout". `Bundle.lean` reads every such limit of a file as four times what it says, and no less than
    the bundle's own; a timeout is not something a proof can catch, so nothing else changes.
  - *Something that the file before left behind.* One proof (`typeclass instance problem is stuck` on a
    variable introduced by `set`) fails after any file of its bundle that holds a real proof, and passes
    alone and after a file of one trivial theorem; it fails with one thread as with three, and passes if the
    environment that the earlier file leaves is thrown away. What in that environment does it was not
    found: the earlier files add no instance and no simp lemma, only their theorems, the lemmas that `simp`
    makes for them and two equation lemmas made on demand. So this is not repaired at its cause. Instead a
    bundle in which one to three files fail is compiled again without them, and each of them in a bundle of
    its own (`bundle-native/alone.json`), where it starts from the imports alone.
  - *The name that Lean gives an instance.* An `instance` without a name gets one made from its type, and Lean
    adds the root of the module to it (`…PadicIntO_development`) when no constant of the type is of the same
    module or of a module of the same root: so the name tells where the file stands. Alone, a file under
    `Development/` that states an instance about a structure of another file under `Development/` gets no
    suffix; in a bundle that structure is of a module `B.l…`, and the instance gets one. Nothing notices,
    until a file names the instance: `attribute [-instance] …instIsLocalRingSubtypePadicAlgClMemSubalgebraPadicIntO`
    in eleven files of the 99th level and above, "Unknown constant". Of the 13 967 instances that the build
    had recorded by then, 501 have such a suffix, and the source names this one only (and one with a suffix,
    which the build holds as written), so it is a pin written by hand in `pins-manual.json` for those eleven
    files, and no rule.
  - *An instance stated for an abbreviation.* `instance : GrpObj (bcObj a A)`, where
    `abbrev bcObj a A := (Over.pullback (spMap a)).obj A`, is the instance that a proof uses when it writes
    the pullback out and never names `bcObj`: Lean unfolds the abbreviation when it files the instance. The
    map held an instance needed once every name of its signature was reached, `bcObj` was reached by nothing,
    and the file was not compiled ("failed to synthesize instance GrpObj A₁", three theorems of the 143rd
    level, in their bundles and alone). An abbreviation, or a definition marked reducible, in the signature
    of an instance now counts as what it stands for (`decl_query.py`): 42 more files.

  None of these changes what a file says, but the pins: they do not either if the map resolves a name as Lean
  does, and where it does not, the pinned file fails, and is in `failed.json`.

Two things the first version of `Bundle.lean` got wrong, and that anyone doing this again will meet:

- The command elaborator empties the message log at each command, and puts the messages of a declaration in the
  snapshot of its elaboration. A driver that reads the log at the end of a file sees no error at all.
- Lean goes on after an error. A theorem whose proof fails is still declared, with `sorry` as its proof, and a
  declaration that the kernel rejects is added as an axiom. So the test of a build is never "no error was
  printed": it is the axioms of the top theorem, which `bundle_check.py` reads. `Bundle.lean` keeps a failed
  theorem, so that what uses it is checked against its statement, and undoes any other command that fails, so
  that what rests on a failed definition fails too, and is seen. The statement of a kept theorem is whole only
  when the error was in the proof. An unknown name in the statement itself is elaborated as `sorry` there
  (`… ∧ CharLift π P` became `… ∧ sorry`), and a bundle above that destructures the theorem is compiled
  against that, without an error, and keeps a copy of the `sorry` in its proof. Repairing the theorem later
  does not repair that bundle: the kernel refuses it once the statement is right (`l105n004`, below). So a
  bundle whose constants name `sorryAx` in a build that reports no error is a stale bundle, and is compiled
  again; `bundle_replay.py` lists them.
- The errors of a file compiled from a copy (`overlay/`, `overlay-auto/`) are reported by Lean under the copy's
  path. Until 22 November `bundle_build.py` matched error lines against the archive's paths only, and two
  errors in copies went unrecorded, the theorems kept with `sorry`: found by the kernel pass, as `sorryAx`.

## What the top theorems need

`decl_map.py` reads the 1 067 553 declarations and resolves the names in each (the namespaces, the `open`s, fields
after a dot, local instances and notations). From the five theorems of `Main`:

| | declarations | files | lines of declarations |
|---|---|---|---|
| What they name, and so on (rule M of `decl_query.py`) | 813 396 | 148 499 | 10.7 million, 61% |
| With the simp lemmas of what is reached (rule W) | 815 353 | 148 506 | 10.8 million |
| With every declaration of a file that holds a needed one, and so on | 990 911 | 159 325 | 12.4 million, 71% |

So the proof is not a small part of the archive: three fifths of it is under the top theorem. The map is close to
the truth where it was tested: for one theorem of a first build, the kernel's own list of what it rests on had 331
declarations where the map said 313. The map had 18 that the kernel does not use, and lacked 36: instances on
Mathlib's types, which nothing names, and the lemmas that those instances use.

Compiling only the declarations of the first row does not work. A pilot on one input of the top theorem
(`recTExists`, 21 216 declarations) left errors in one file in ten: a proof used, through `simp`, a lemma of its
own file that nothing names; `lift_ι_assoc` is made by an attribute on `lift_ι`; an `open` named a namespace whose
declarations were all left out. Compiling whole files for one input does not work either: the files of
`recTExists` drag in 76 160 files, 9 million lines, because a file's other declarations need their own files. What
works is the third row, all of it, bottom up: 159 471 files with the commands that define syntax and the instances
that nothing names, the `example`s left out.

## The shape of the proof

Read from the sources, which have no comments; the names are the archive's. Nothing here was checked by compiling,
except where it says so.

- **One statement.** `Main`'s five theorems all come from `UpperTheory.EveryCharacter`: no `L(s, χ)` vanishes on
  `Re s > 1/2`, the pole aside (`Supplements/Kernels/MainTheorems.lean`). The steps from it to RH for `ζ` and to
  the critical strip are 135 lines that need only Mathlib: `CharacterBoxes/HalfPlane.lean`, `ClaimStrip.lean`
  and the last 20 lines of `RiemannHypothesisOfEveryCharacter.lean`. Those compile unchanged on this
  repository's pins.
- **The analytic step: a bound from one side, and Landau's theorem.** The chain proves no positivity of a form:
  the four declarations named after Castelnuovo–Severi or the Hodge index are not reached. It works with
  `Sz x = Σ_{n ≤ x} Λ(n)(x/n − 1)` and its error `Gz x = Sz x − x log x + (1 + γ)x`, the same with a character
  (`gChi`), and for the cyclic group of characters that one character `ψ` generates (`Level.cyc ψ`, of order `o`)
  the sum `Gm = Gz + (3o + 1)⁻¹ Σ_{ψ′ ≠ 1} Re g_{ψ′}`. Two things give the half-plane
  (`CharacterBoxes/ZeroFreeAllOfTopG.lean`, `TotientGaloisClasses/TopWin.lean`):
  - `Level.FormBAt`: if `Gm x ≤ x^θ` on a set of scales with windows, no `L`-function of the level vanishes on
    `Re s > θ`. This is Landau's theorem on an integral of one sign; the bound is needed from above only.
  - `core_gm`: `Gm x ≤ x^{1/2 + cε}` at those scales, for every `ε`. It comes from `Deduction.ch_top`, a bound from
    above for a sum over inert primes with the weights `2 log p · max(a/pⁱ − w, 0)` less its main term (`ASK`,
    `MAIN`), by an exact identity that writes that difference through the errors `g_ψ` (`ch_balance`) and by the
    same bound in every coset of a subgroup (`ch_core`). The bound on the primes is read off lattice data: ranks,
    slopes and sizes under a list of conditions (`SizeData₂`) with a slope inequality among them; the archive
    states Bost's (`Formalism.HN.SlopeIneq`). Where the lattices come from, the theta lifts, was not read.

  `Formalism/Statement*.lean` state the same idea in small: `RHofG` (RH and GRH for a real `χ` from
  `G χ x ≥ −C x^{1/2+ε}`, with the weights `Λ(n)(1 + Re χ(n))`), and `ForcedSumCM` (the classes that a CM type and
  its dual count make up everything, so a bound from above for both is a bound from below for each). The top
  theorems do not reach those files, by the map.
- **The inputs of the top theorem.** `EveryCharacter` is `everyCharacter_of_row h`, and that is
  `every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)`. What each needs, by the map:

  | Input | What it is | Declarations | Lines |
  |---|---|---|---|
  | `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` | `h`: local–global compatibility for Galois representations | 198 000 | 2.4 million |
  | `UpperTheory.Zero.LLC.recTExists` | the local Langlands correspondence for `GL_n` exists | 14 305 | 156 000 |
  | `UpperTheory.One.vwin_of_row` | `VWin` from `h` | 184 043 | 2.4 million |
  | `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` | the published results and the core theorem | 685 396 | 8.9 million |

  The inputs share most of what they need. To state `h` takes 2 325 declarations; to state `EveryCharacter`, one.
- **The core theorem.** `every_character_of_theta_integrals_local_matching`
  (`Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`) has seven inputs: two
  bundles of published results, the agreement of two theta integrals, a local matching, a bound for a covolume,
  the local Langlands correspondence for `GL_n`, and `VWin`. `VWin` (`CharacterBoxes/ExistsPageN.lean`) bounds the
  lengths of groups of Tate–Shafarevich type over subfields of cyclotomic fields, along a tower of conductors
  `2^e`; it reads as the "weakening of Vandiver" of the author's statement.
- **The published results.** The inputs are 162 propositions `GlobalTheory.Published.*`, among them Deligne and
  Ribet's theorem, global Artin reciprocity, Casselman and Wallach's theorem, Clozel's purity, Bhatt and
  Scholze's integral comparison, Kawamata–Viehweg vanishing, the Siegel–Weil formula, Howe duality and toroidal
  compactifications. The archive proves each of them (`…_holds`).
- **A statement in the middle.** `UpperTheory.Top.plugAll` (`CharacterBoxes/EveryCharacter.lean`, level 90 of the
  203) gives `EveryCharacter` from three hypotheses: `GlobalTheory.GLq.Green`, `VWin`, and a family `Hyps`. It
  needs 4% of the archive's lines.
- **Where the needed lines are.** `Development.AbelianVarietyTheory` 4.8 million,
  `Development.AutomorphicArithmetic` 1.2 million, `Development.AutomorphicSpectrum` 0.8 million,
  `Development.WeilBound` 0.6 million, `Formalism.LocalToGlobal` 0.5 million.

## The state of the build

`external/alpoge-rh/bundle-native` holds the build on the archive's own pins: 159 531 files to compile, level by
level. `run.log` there has a line a level, `state.jsonl` a line a bundle, and `failed.json` the declarations with
an error, rewritten after each level. It was started on the evening of 20 November 2026 and takes this laptop some
twelve hours awake; run the `bundle_build.py` line above again to take it up where it stopped.

A first run reached the third level on 20 November 2026 (13 708 files) with no failure at the first level, one at
the second and 26 at the third: all but a few were the instance of a file not imported that is described above.
The build was then started again from nothing at 22:40, with each file given its own view of the instances and
the simp set, and its first three levels, 13 708 files and 1.44 million lines, compiled with no declaration
failing. The fourth, fifth and sixth levels failed in five files, each for a reason not met before: a name
ambiguous in the bundle only, a name captured in a `variable` command, `open private … from M`, a lemma made on
demand by a file not imported, and a name that its own file reads in two ways. Each is described above with what
was done about it; the bundles were compiled again, and at 00:30 on 21 November the first six levels, 23 602
files and 2.6 million lines, held no declaration with an error. The seventh to the nineteenth levels brought the
rest of the list above, a failure or two a level, each a kind not met before: a file's own private name, a name
read in several ways by its own file, a name found through an earlier `open`, one name declared in two files
with two statements, `open N (a b)`, a field taken for a reference, a name that Mathlib exports, a file whose
names the map did not follow and that was therefore never compiled. Each was repaired where it arose, in the map,
in the pins or in the compiler, and the bundles were compiled again. At 04:50 the first nineteen levels, 47 773
files of 159 020 and 5.5 of 16.3 million lines, held no declaration with an error. A few chunks hung with their
proofs on other threads, and compiled on one.

The twentieth to the twenty-sixth levels went the same way, one or two files a level: a lifted proof named
in the source, `open Topology in`, a function named like a tactic, `open N (a b)` finding one constant twice,
`open Classical in` inside a definition, a field of a structure instance on a line of its own, and a protected
constant of Mathlib that the map took for what a short name means (`sub_mul` under `open Matrix` is not
`Matrix.sub_mul`; the map now has Mathlib's 39 794 protected names and the archive's own). At 07:17 the first
twenty-six levels, 59 359 files and 7.0 million lines, were compiled, with seven declarations of three files
failing for the last three of those reasons; compiled again, they hold none. The twenty-seventh and
twenty-eighth levels brought one failure each: a third `unfold … mulVec`, after which that whole kind was
settled ahead of the build, and a field reached through an opened namespace. The twenty-ninth and thirtieth
had none, the first two levels since the sixth to compile in one pass, and the thirty-first one file (a
variable of an earlier `variable` command). At 09:00 on 21 November: 68 085 files and 8.1 of 16.3 million
lines. The thirty-second to thirty-fourth had none again; by then a bundle spent more time importing than
compiling ("The import comes back", above), and from the thirty-fifth on the bundles import copies without
proofs. The thirty-fifth and thirty-sixth: `open … hiding`, and the first theorem whose check needs a proof
from below. The thirty-seventh: a constant under a namespace named like a variable, and a field named like a
function. The thirty-eighth had none; the thirty-ninth, a measure after `∂` taken for a bound name; the
fortieth, two instances in another order; the forty-first and forty-second none; the forty-third the order of
two instances again, after which each file is given its own; the forty-fourth none; the forty-fifth, a field
given the function of its own name. At 13:25: 90 126 files and 10.5 million lines. The forty-sixth to the
fifty-second level compiled in one pass. The fifty-third: a proof that fails after any other file of its
bundle and passes alone; the fifty-fourth: an `open … in` cut off from its theorem by an `attribute … in`;
the fifty-sixth: a heartbeat limit of the file's own; the fifty-seventh: a name in a `variable` command that
no declaration uses. At 16:48: the first 58 levels, 108 636 files, two thirds, and 12.2 million lines, with
no failing declaration. The fifty-ninth and sixtieth had none; the sixty-first, a name in a `variable … in`
line. At 17:25: 112 057 files and 12.5 million lines. The sixty-second to the seventy-seventh level compiled
in one pass, sixteen levels; the seventy-eighth: a file that the map had not found needed. At 20:05: 126 771
files, four fifths, and 13.8 million lines. The seventy-ninth to the eighty-sixth level compiled in one pass.
At 21:05: 131 598 files and 14.2 million lines. The eighty-seventh: a chain of proofs that the kernel unfolds
("The import comes back", above); the eighty-eighth to the ninety-eighth in one pass; the ninety-ninth: an
instance named by Lean. At 23:30: 146 146 files and 15.3 million lines, with no failing declaration; 13 087
files and one million lines are left, on 103 levels. The hundredth to the hundred-and-second in one pass; the
hundred-and-third to hundred-and-fifth: `open` of a namespace that the file makes further down, and four files
that open private lemmas of a module that nothing else needs. At 00:30 on 22 November: 151 742 files of
159 239, with no failing declaration; 7 500 files and 590 000 lines are left, on 97 levels of one to three
bundles. The hundred-and-sixth to the hundred-and-forty-second in one pass (two bundles hung with their
proofs on other threads and were compiled on one); the hundred-and-forty-third: an instance stated for an
abbreviation. At 02:40: 158 826 files of 159 281, with no failing declaration; 37 000 lines are left, on 57
levels of one small bundle each.

The pace was 140 to 300 lines a second with five processes (a process holds some 4 GB of its own), falling as
the imports grew; with the copies without proofs a bundle of 12 000 lines takes about three minutes alone. At
the eightieth level five processes at once no longer fit in 32 GB: the system compresses their memory, an
import that takes half a minute alone takes one to three minutes beside four others, and the pace is 100 to
110 lines a second. At 21:05 there remained 2.1 million lines in some 320 bundles on 117 levels: twenty levels
of four to ten bundles, thirty of three, and sixty-five of one bundle of a few files, each of which still
imports everything below it.

The build ended at 03:05 on 22 November 2026: 1 716 bundles on 203 levels, 159 321 files and 16.3 million
lines, and no declaration reported with an error. The kernel pass (`bundle_replay.py`, six threads, 111 hours
of checks on one thread, two hours awake) then went through all of it: 1 777 302 constants, 5 442 theorems
stated twice and their second proofs checked under another name, 601 constants marked `unsafe` or `partial`
left out. No bundle declares an axiom; the constants name `propext`, `Classical.choice` and `Quot.sound`, and
in three bundles `sorryAx`. The kernel refused one constant, in one of the three:

- `l105n004` had been compiled at 00:13, against the statements that the 104th level held before its repair at
  00:19 (`CharLift` unknown, so `… ∧ sorry`), and was not compiled again: the kernel refuses its proof of
  `GalTw.GlobalTheory.RoadU.TorLiftC.exists_cm_lift_fix_charKer` against the statement as it is now;
- `l030n000` and `l032n013` each hold a theorem whose proof had failed, unreported, in an overlay copy
  (``Tactic `delta` failed: did not delta reduce [Finsupp.prod] at hp``): there the cut that `unfold_overlay.py`
  makes is wrong and the archive's own `unfold Finsupp.prod at hp` passes in the bundle (`LEAVE` in that
  script).

The three were compiled again with no error; `proof_refs.py` found that they hold the same constants with the
same statements as before, so nothing above them is affected, and the pass was run again from the first of
them. (The machine was on its battery and slept from 04:25 to 21:04 on the 22nd, with the pass halfway: the
pass waited, and went on when the power came back.)

The second pass ended at 23:13 on 22 November: it took the first 775 bundles as accepted and unchanged and
checked the other 941 (6.2 hours of checks on one thread, 68 minutes awake). Nothing refused, no bundle declares
an axiom, and no constant of the build names an axiom but `propext`, `Classical.choice` and `Quot.sound`. Then
`scratch/rh-claim/port/RHJoin.lean` compiled, on the archive's pins, against the port of the library and all
1 716 bundles, with no error (32 minutes, most of it reading the 68 GB of compiled bundles): `RHJoin.claim :
RHClaim.Claim := ⟨riemannHypothesis, LFunction_eq_zero_re⟩` elaborates, so the archive's two theorems have the
types that the library states (`RiemannHypothesis` is Mathlib's definition; `DirichletRH` the library's, the
same words as the archive's `DirichletLZerosOnLine`), and its last command walked 1 483 900 constants from the
thirteen theorems of the file and met the axioms `propext`, `Classical.choice` and `Quot.sound` and no other:

    assert_axioms_by_walk: 1483900 constants walked from 13 theorems; the axioms met: #[propext, Classical.choice, Quot.sound]

The cone of `riemannHypothesis` in the build (`bundle_check.py`, `bundle-native/cone/`) is 1 262 629 constants
of the archive: 1 072 415 theorems, 178 272 definitions, 5 569 inductive types with their constructors and
recursors, and no axiom; 71% of the constants compiled.

What this takes on trust: Lean's kernel (`v4.33.1`), the reader of `.olean` files, the compiled Mathlib (and
Batteries and Lean) at the archive's pin, which was not checked again here, and the two programs of this
directory that the result rests on, `lean/ReplayAll.lean` (`replay_test.py` has it refuse each kind of tampered
file) and the walk in `RHJoin.lean` (tested on a theorem that uses an axiom of its own). What it does not take on
trust is how the files were compiled: bundles, pins, renamed duplicates, overlay copies, lifted proofs, instance
orders and copies without proofs all served to get the archive's text elaborated, and the kernel then checked
what came out, constant by constant, from Mathlib up, and the statements of the two theorems were matched
against Mathlib's and the library's own.

One repair reached further than its own bundle: see "A lifted proof named" above. Of the 45 bundles whose
terms name a lifted proof that could have been renumbered when ten bundles of the first levels were compiled
again, the kernel refused three (`l004n012`, `l015n014`, `l021n003`) and accepted 42; the three are being
compiled again. Until `bundle_replay.py` has been over the whole build, checks of this kind (the bundles that
`proof_refs.py` names after each repair, sent to the kernel by `bundle_recheck.py --bundle`) are the only
evidence that the bundles made before a repair still fit what is below them. A first run of
`lean/ReplayAll.lean` over the 169 bundles of the first three levels (175 162 constants, 893 theorems held
twice) refused none.

It stops by itself after a level where more than a few definitions failed, because what is built on them would
fail too. Then, and at the end:

- `failed.json` says which declarations failed and why. A name that the map missed is added with `--add NAME`,
  and `bundle_build.py --retry` compiles again the bundles that had an error, in the order of the levels;
- a theorem that still fails in its bundle and not alone stays declared with `sorry`. Nearly every failure so
  far was a name: `pin_trace.py FILE NAME` says how the file's own imports read it and how the bundle does, and
  the repair was then in what the map takes for a name (`decl_map.py`), in what gets a pin
  (`capture_rewrites.py`), in which files are needed (`bundle_build.py`) or in the compiler (`lean/Bundle.lean`:
  every job reads it, so a change is made on a copy, `python3 tools/rh/driver_test.py --driver COPY` runs the
  sixteen small jobs of `lean/tests/` on it under both toolchains, and the copy then replaces the file with
  `mv`; a new kind of failure gets a job there). For anything
  else, compile the file alone against the bundles below it: copy its entry of `job/<bundle>.json` into a job
  of one file (`bundle-native/probe` has examples). After a repair: the map again if `decl_map.py` changed,
  `capture_rewrites.py` again, then `bundle_build.py --retry`;
- a bundle that is compiled again replaces its `.olean`; the bundles above it were checked against what it
  held and are not compiled again. `proof_refs.py --out OUT BUNDLE …` then names the bundles above whose terms
  hold a constant of it that is gone or not the same; `bundle_recheck.py --bundle` has the kernel look at
  those, and `bundle_build.py --again BUNDLE … --retry` compiles again the ones it refuses. Repeat with those
  until none is refused.

Until `bundle_check.py` reports `riemannHypothesis` with the axioms `propext`, `Classical.choice` and `Quot.sound`,
nothing compiled with `sorry` under it and no name missing, the archive is not checked here. A build that printed
no error is not that check.

Two things make a repaired build harder to trust than one made in a single pass, and each has its answer:

- A bundle compiled again replaces its `.olean`, and the bundles above it were checked against what it held
  before. If only a proof was mended, nothing above changes. If a statement changed (a name in it that had been
  read as another constant), a proof above may not fit it any more, and no one has looked.
  `bundle_recheck.py` looks at the bundles above a repair: for each it imports the bundles below as they are
  now and has the kernel check every constant of the bundle again, with no elaboration. `bundle_replay.py`
  looks at everything, once the build has ended: one pass in the order of the levels, each constant checked by
  the kernel against Mathlib and the constants before it, read from the whole files. When it ends with nothing
  refused, the build in its final state is what the kernel would have accepted had it been given the constants
  one after another, in whatever order the bundles were made, repaired and compiled again; the copies without
  proofs and the pins have no part in that check. `replay_test.py` shows the pass refusing what it should.
- Lean records in each `.olean` the axioms that each declaration depended on when its file was compiled, and
  `#print axioms` answers from the record. After a repair those records are out of date in the bundles above:
  they still list `sorryAx` for what rested on a proof that has since been mended. So the axioms of the top
  theorems are read from the kernel's terms, by walking what each constant names to the end
  (`lean/Cone.lean`; `#assert_axioms_by_walk` in `scratch/rh-claim/port/RHJoin.lean`), not asked of Lean.

## The two pins do not meet at the level of the kernel

A proof term does not depend on tactics, so it was worth asking whether the terms that Lean 4.33.1 checks could be
checked again by the kernel of Lean 4.35.0-rc3 over this repository's Mathlib, with no source ported.
`Export.lean` and `Replay.lean` do that, and it works where the two Mathlibs agree: three theorems of Mathlib of
21 August were carried into the environment of 29 September, accepted by its kernel, and used from an ordinary
file. But the two Mathlibs do not agree where it matters. `fp_compare.py --by-name` on the 771 174 constants of
the older one:

- 71 141 are gone or have a type of another shape in the newer one, and 336 644 (44%) rest on one of those in
  their type;
- among them the algebraic hierarchy. `AddZeroClass.mk` takes an `AddZero M` in the older one, and a `Zero M` and
  an `Add M` in the newer one; `AddMonoid.add_zero` is stated through `AddSemigroup.toAdd` in one and
  `AddMonoid.toAdd` in the other. So `ℝ` and `ℂ` are built on different structures: of the 4 961 constants that
  `RiemannHypothesis` means, 2 481 do not read the same.

A proof carried over would be about a second copy of `ℂ` and of `ζ`, and joining the copy to Mathlib's `ζ` is a
development of its own (an isomorphism of the two fields, and the identity theorem for the two functions). It is
not a shortcut. The tools stay: they carry a proof between versions of Lean whenever the statement's constants
agree, and `fp_compare.py` says in a few minutes whether they do.

## What joining it to the library needs

The library's deductions are stated for any input (`docs/account.md`, "What a new input buys at once"), and
`scratch/rh-claim/RHClaim.lean` states them from the archive's own statements: it compiles here, and each of its
theorems depends on the three standard axioms only. What is missing is one environment in which both the archive's
`Main` and that file are checked. There are three ways to get one:

1. **Port the archive to this repository's pins.** One file in ten fails at each level, for a hundred reasons
   (lemmas renamed, arguments made explicit, instances not found, tactics that close goals differently): some
   20 000 declarations to repair by hand. Not by the kernel either, by the section above.
2. **Port the library's 347 modules behind `RHClaim.lean` to the archive's pins.** This is the route taken, and
   the section below is its account. The repairs are to this library's own files, and they turned out few.
3. **Wait for the archive to be ported to a current toolchain** by its author or by the Lean community, which was
   proposed on the Lean Zulip on the day of the claim, and pin this repository there.

The second also needs the archive's build finished on its own pins, which is the build above.

## The port of the library to the archive's pins

`RHClaim.lean` reaches 347 modules of the library, 164 000 lines, written for Lean `v4.35.0-rc3` and the Mathlib of
29 September 2026. They are compiled on Lean `v4.33.1` and the Mathlib of 21 August, each file in its own process
with exactly its own imports (`bundle_files.py`; a bundle is not needed here, and it would only add its
artifacts). The port does not see the archive: only the last file imports both.

```sh
python3 tools/rh/port_tree.py make external/alpoge-rh/port/src         # the library's files, patched
python3 -I tools/rh/bundle_files.py --src external/alpoge-rh/port/src --out external/alpoge-rh/port/build \
    --workspace external/alpoge-rh/native-ws --prelude scratch/rh-claim/port/PortCompat.lean \
    --simp-out scratch/rh-claim/port/simp_out.json \
    --option autoImplicit=bool:false --option relaxedAutoImplicit=bool:false \
    --jobs 2 --deep RHClaim scratch/rh-claim/port/PortCheck.lean
# and, when the archive's build is finished:
python3 -I tools/rh/bundle_files.py … --with external/alpoge-rh/bundle-native scratch/rh-claim/port/RHJoin.lean
```

A first run with nothing done gave 838 errors in 152 of the 347 files. Nearly all of them went without touching
a proof, by making the older pair behave as the newer one where a difference can be undone. What was left took
27 small patches, 67 lines in all. On 21 November 2026 at 03:10 a build of everything from the first file up
(`--deep`, 93 minutes of compiling in all, two processes) ended with no error in any of the 349 files and none
compiled against an earlier state of what it imports, `PortCheck.lean` among them. All of it is in
`scratch/rh-claim/port/`:

- **`PortCompat.lean`**, a file that the port compiles first and every file imports:
  - *names.* The newer Lean and Mathlib keep the former name of a renamed declaration as a deprecated alias, so
    the renames between the two pins are read from the newer one: 875 of them. `ite_eq_left` is `if_pos`
    (424 of the errors were the four names of that family), `Finset.prod_le_prod₀` is the older
    `Finset.prod_le_prod`, `Isometry.antilipschitzWith` is `Isometry.antilipschitz`. The file declares the
    aliases that the library can reach;
  - *lemmas that only the newer Mathlib has* and the library uses, proved for the older one: the digamma
    recurrences, reflection and duplication, the bounds on `Σ log n`, the substitution `y = exp x`, bounds on the
    derivatives of a compactly supported function, temperate growth of `sin`, `cos`, `re` and `exp (x * I)`, a
    comparison of a sum with an integral, and a few more. A scan of the tree against the two pins' names finds
    them all at once (26 names);
  - *`convert`.* The newer Mathlib's `convert` closes an equation between two instances before its congruence
    step, at the transparency of instances; the older one leaves `Complex.instAddCommMonoid =
    Complex.addCommGroup.toAddCommMonoid` as a goal, and every case after it is then one off. That one default
    was behind most of the 152 "unsolved goals". The file declares the tactic again with the newer defaults;
  - *the simp set.* `simp_diff.py` compares the two simp sets (`lean/DumpSimp.lean`): 97 885 lemmas in both, 71
    that both pins have and only the newer marks, 342 the other way. The file marks the 71;
  - `#assert_standard_axioms`, a check that is an error when it fails.
- **`simp_out.json`**: the 342, which `bundle_files.py --simp-out` takes out of the simp set of every file.
- **`patches/`**: what is left, as one patch a file against the library's file (`port_tree.py save`): 27 files.
  They are small and of few kinds: a hypothesis of another type (`MemLp.indicator` wants a `MeasurableSet` in
  the older Mathlib and a `NullMeasurableSet` in the newer; `MemLp` is a conjunction in the older and a bound on
  the norm in the newer), a name that means another lemma (`Finset.prod_le_prod`), a name that the older Lean
  reads two ways where the newer chooses (`dist_zero_right` under `open Nat`, `not_imp` under `open Classical`,
  `arctan` under `open Real Complex`), a definition that is an `abbrev` only in the newer Mathlib
  (`Quaternion`), an `if` that `norm_num` no longer decides, a coercion lemma that left the simp set and has no
  successor in the older Mathlib (`MonoidHom.coe_coe`, named in two `simp` calls), and five limits of
  heartbeats. No statement is changed, but in three lemmas of the vendored `PrimeNumberTheoremAnd` where
  `arctan` is written `Real.arctan`, which is what the newer Lean reads there (`port_tree.py status` lists the
  patched lines that are part of a statement).
- **`PortCheck.lean`**: the bridge file's theorems depend on the three standard axioms on the archive's pins.
  It asks Lean (`#assert_standard_axioms`), whose answer rests on what each `.olean` recorded when it was
  compiled, so it is to be believed after a `--deep` build only: after the first pass it still named `sorryAx`
  for proofs that had been mended since.
- **`RHJoin.lean`**: the archive's `riemannHypothesis` and `LFunction_eq_zero_re` given to `RHClaim.Claim`, and
  each conclusion of `RHClaim.lean` without its hypothesis. It is compiled with the archive's bundles, and its
  last command is an error unless every theorem in it depends on the three standard axioms only.

A scan of the names finds no declaration and no module that the port and the archive both declare, which is what
importing both into one environment needs.
