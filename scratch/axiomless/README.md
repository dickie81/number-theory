# Mathematics with no axioms (not wired into the lakefile)

An exploration of what Lean proves with no axiom at all: not `propext`, not `Quot.sound`, not `Classical.choice`.
[`LOG.md`](LOG.md) is the log of what was asked and found, in order.

`./check.sh` compiles the Lean files and fails if a declaration that should be free of axioms is not. It needs
only the pinned Lean toolchain, not Mathlib, and takes fifteen seconds.

| file | contents |
|---|---|
| `LOG.md` | the log |
| `Bare.lean` | no imports at all (`prelude`): equality, the natural numbers and `a + b = b + a` from the kernel alone |
| `AxiomTools.lean` | the commands `#axiom_free`, `#axioms_table`, `#why` (a shortest chain from a constant to each axiom it depends on), `#entries` and `#without` |
| `Spectroscopy.lean` | one small proof for each tactic, with the axioms it brings in |
| `Tower.lean` | number theory with no axioms: Euclid's theorem, Euclid's lemma, the irrationality of `√p`, the fundamental theorem of arithmetic |
| `Compute.lean` | the kernel runs those proofs: the prime that Euclid's proof finds above `n`, factorizations |
| `Principles.lean` | the axioms as hypotheses: the implications between excluded middle, extensionality, choice and the principles between |
| `Stuck.lean` | unbounded search from a proof of existence, which the kernel runs when the proof has no axiom; closed terms of type `Nat` that an axiom keeps from computing |
| `Ladder.lean` | one proposition generates infinitely many without excluded middle (the Rieger–Nishimura ladder, a Kripke model, non-derivability in intuitionistic logic) and four with it |
| `DivLt.lean` | core's lemma `n / k < n`, which core proves with `propext`, proved with no axiom |
| `CertAxioms.lean` | the axioms of a certificate part of this library's Linnik theorem, and the one route by which `propext` reaches it; needs `lake build SieveHint21500P1`, so `check.sh` does not run it |
| `LandBench.lean` | the kernel's time for `Nat.land`, for a remainder and for a hand-written `and`: what removing `propext` from the certificates inside the library would cost; 80 s, so `check.sh` does not run it |
| `Census.lean` | the axioms of every constant of an environment: `lean --run Census.lean OUT.tsv Init Std Lean`, or `lake env lean --run scratch/axiomless/Census.lean --edges EDGES OUT.tsv Mathlib` (ten minutes, 10 GB) |
| `census_report.py` | tables from a census |
| `gateways.c`, `gateways_report.py` | the dominator tree of an axiom: the constants through which every use of it passes |
| `labels.c`, `choice_kinds.py` | how the theorems reach `Classical.choice`: by excluded middle, by classical decidability, or by the choice of an element |
