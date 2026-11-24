/- The axioms of the Linnik paper's two theorems (`papers/linnik-exponent/main.tex`), at `21/10` and at `43/20`, of its
corollary in number and of the bounds of their certificates. Every line this file prints must be
`[propext, Classical.choice, Quot.sound]` or a subset of them (`scripts/check_axioms.py --linnik`).

The certificates are opt-in: neither the default build nor CI's build of a change compiles them. Each is the plan of a
search that the kernel follows by hints: at `43/20` 17 part files (`lib/pnt/SieveHint21500P<k>.lean`, about an hour of
the kernel), at `21/10` 1150 part files and 58 files of cells (`lib/pnt/SieveHint21000P<k>.lean` and
`SieveHint21000N<j>.lean`, about 61 hours of one core). With the theorems they give (`Linnik21500.lean`,
`Linnik21000.lean` and their files `…Count.lean`) they are the Lake library `LinnikCert`, which only this file imports.
`lake build CheckLinnik` builds them, and the workflow `.github/workflows/linnik.yml` builds them and checks this file
every week and on request. The steps of the two proofs that need no certificate are printed by `Check.lean` (the
paper's Sections 2 to 7, and its inputs) and `CheckAll.lean` (its Sections 8 to 10); the library's headline Linnik
exponent is `2 + η` under GRH (`LinnikGRH.linnik_two`, in `Check.lean`). -/
import Linnik21500Count
import Linnik21000Count

/- Theorem 1.2, at `43/20`, from the half-plane and Huxley's estimate alone, its form in number (the case `43/20` of
Corollary 1.3), and its certificate: the tests are sound, each part of the search bounds its term, and the term of the
box of the first prime is bounded. -/
#print axioms Linnik21500.linnik_21500
#print axioms Linnik21500.count_21500
#print axioms Linnik21500.count_large_21500
#print axioms Linnik21500.tree21500
#print axioms Linnik21500.part21500
#print axioms Linnik21500.sound21500
#print axioms Linnik21500.soundF21500

/- Theorem 1.1, at `21/10`, from the half-plane, Chen, Gupta and Li's Proposition 3.1 and Ingham's and Huxley's
estimates, its form in number (the case `21/10` of Corollary 1.3), and its certificate. -/
#print axioms Linnik21000.linnik_21000
#print axioms Linnik21000.count_21000
#print axioms Linnik21000.count_large_21000
#print axioms Linnik21000.tree21000
#print axioms Linnik21000.part21000
#print axioms Linnik21000.sound21000
#print axioms Linnik21000.soundF21000
