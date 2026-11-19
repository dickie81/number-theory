# Mathematics with no axioms (not wired into the lakefile)

An exploration of what Lean proves with no axiom at all: not `propext`, not `Quot.sound`, not `Classical.choice`.
[`LOG.md`](LOG.md) is the log of what was asked and found, in order.

`./check.sh` compiles the Lean files and fails if a declaration that should be free of axioms is not. It needs
only the pinned Lean toolchain, not Mathlib, and takes ten seconds.

| file | contents |
|---|---|
| `LOG.md` | the log |
| `Bare.lean` | no imports at all (`prelude`): equality, the natural numbers and `a + b = b + a` from the kernel alone |
| `AxiomTools.lean` | the commands `#axiom_free`, `#axioms_table` and `#why` (a shortest chain from a constant to each axiom it depends on) |
| `Spectroscopy.lean` | one small proof for each tactic, with the axioms it brings in |
| `Tower.lean` | number theory with no axioms: Euclid's theorem, Euclid's lemma, the irrationality of `√p`, the fundamental theorem of arithmetic |
| `Compute.lean` | the kernel runs those proofs: the prime that Euclid's proof finds above `n`, factorizations |
| `Census.lean` | the axioms of every constant of an environment: `lean --run Census.lean OUT.tsv Init Std Lean`, or `lake env lean --run scratch/axiomless/Census.lean --edges EDGES OUT.tsv Mathlib` (ten minutes, 10 GB) |
| `census_report.py` | tables from a census |
| `gateways.c`, `gateways_report.py` | the dominator tree of an axiom: the constants through which every use of it passes |
| `labels.c`, `choice_kinds.py` | how the theorems reach `Classical.choice`: by excluded middle, by classical decidability, or by the choice of an element |
