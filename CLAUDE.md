# CLAUDE.md

In this repository, if it is proved in Lean, it is considered proved. We trust Lean.

Do not second-guess a result the kernel has accepted, and do not spend effort decoupling or re-proving Lean-verified results already in this repository.

There is no `sorry`, `admit`, extra `axiom` declaration, or any other jiggery-pokery. A theorem may depend only on Lean's three standard axioms: `propext`, `Classical.choice`, and `Quot.sound`. CI enforces this (`scripts/check_hygiene.py`, `scripts/check_axioms.py`); see [`docs/building.md`](docs/building.md).
