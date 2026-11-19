# Mathematics with no axioms: a log

Lean's theorems usually rest on three axioms: `propext` (equivalent propositions are equal), `Quot.sound` (related
elements have equal classes in a quotient, from which function extensionality follows) and `Classical.choice` (an
element of every nonempty type, from which excluded middle follows). This library allows exactly those three. This
log asks what is left with none of them: a theorem is *free of axioms* here when `#print axioms` reports that it
depends on no axioms at all.

The entries are in the order of the work. Each says what was asked, what was done and what was found. The files
are in this directory; `README.md` says how to check them. Numbers are for Lean v4.35.0-rc3 and Mathlib at the
commit this repository pins.

## 1. What the kernel provides before anything is declared

**Question.** What exists when nothing has been declared, not even the axioms?

**Done.** `Bare.lean` starts with `prelude`, so it does not import `Init`, where `Eq`, `Nat` and the three axioms
are declared. It defines equality as an inductive family, the natural numbers, and addition by the recursor, and
proves that addition is commutative, by terms alone.

**Found.**

- The kernel accepts all of it. Sorts, functions, inductive types, their recursors and computation need no
  declaration. Symmetry, transitivity and congruence of equality are each one application of the recursor of
  equality. `2 + 2 = 4` holds by computation.
- The compiler, not the kernel, wants more: it refuses a definition until `Init`'s constant `lcAny` exists, and it
  does not compile recursors. So the definitions are marked `noncomputable`. The logic has no such needs.
- Tactics are not available either. Their syntax is declared in `Init`.
- Two facts that other systems take as axioms are already rules of this kernel. Any two proofs of a proposition
  are equal by definition, so uniqueness of identity proofs needs no axiom. And `Quot`, with `Quot.mk`,
  `Quot.lift` and `Quot.ind`, is built in; only `Quot.sound` is an axiom.

## 2. How much of Lean's own library is free of axioms

**Question.** Lean's core library (`Init`, `Std`, `Lean`) is written without regard for axioms. How much of it
uses none?

**Done.** `Census.lean` imports the modules, and for every constant computes the axioms it depends on, as
`#print axioms` does, in one pass over the graph of constants. It also computes the axioms that a constant reaches
without entering the proof of a theorem. For a theorem that is what its statement rests on.
`census_report.py` prints the tables.

**Found.** 207 900 constants, 57 258 of them theorems with a name a person wrote.

| | theorems | share |
|---|---|---|
| free of axioms | 10 110 | 17.7% |
| statement free of axioms, proof not | 43 045 | 75.2% |
| statement rests on an axiom | 4 103 | 7.2% |

- Three quarters of the theorems state something that mentions no axiom, and prove it with one.
- The axioms enter through few constants. `Classical.choice` is named by 25 constants and `Quot.sound` by 56.
  `propext` is named by 13 463, of which 10 703 are auxiliary lemmas that `simp` generates.
- Of the 2 069 theorems of the namespace `Nat`, 420 are free of axioms.

## 3. Which tactics bring axioms in

**Question.** If the statements are free of axioms, where do the axioms come from?

**Done.** `Spectroscopy.lean` proves one small statement with each tactic and prints the axioms of each proof.
`AxiomTools.lean` adds the command `#why c`, which prints a shortest chain of constants from `c` to each axiom it
depends on.

**Found.**

| axioms | tactics |
|---|---|
| none | `rfl`, `exact`, `induction`, `cases`, `match`, `rw` by an equation, `simp only` when it leaves the goal open, `by_cases` on a decidable proposition, `split`, `contradiction`, `injection`, `subst`, `obtain`, `calc`, `congr`, `conv`, `decide` and `decide +kernel` (if the `Decidable` instance is free of axioms), structural recursion |
| `propext` | `rw` by an equivalence, `simp` whenever it closes the goal, `exact_mod_cast` |
| `propext`, `Quot.sound` | `omega`, `ac_rfl`, `decide` on a bounded `∃` over `Nat` (core's instance) |
| all three | `grind`, `by_cases` on an undecidable proposition, `bv_decide` |
| an axiom of its own for each use | `native_decide` (and `bv_decide`) |
| `Quot.sound` | `funext` |

- `simp` closes a goal `a = a` with `eq_self : (a = a) = True`, an equality between propositions, which is
  `propext`. That one step accounts for most of the 75%.
- Basic lemmas of core depend on `propext` this way: `Nat.succ_ne_zero`, `Nat.one_ne_zero`, `Nat.mul_assoc`,
  `Nat.sub_add_cancel`, `Nat.dvd_trans`, `Int.add_comm`, `List.append_assoc`, and all of the theory of `/` and
  `%` (`Nat.div_add_mod`, `Nat.mod_eq_of_lt`, …). `Nat.pow_lt_pow_right` depends on `Classical.choice`, through a
  `simp` lemma on the negation of an implication. `by decide` proves `3 ∣ 12` with `propext`, through core's
  instance `Nat.decidable_dvd`. `Nat.gcd_zero_left` depends on `Quot.sound`: the unfolding lemma of well-founded
  recursion on `Nat` (`WellFounded.Nat.fix_eq`) is proved with `funext`.
- So a proof that is to be free of axioms cannot use `simp`, `omega` or most of core's lemmas on division. It can
  use `induction`, `cases`, `rw` by equations, `decide`, and the 420 lemmas.
- Axioms in a termination proof do not stop the kernel from computing. A function defined by well-founded
  recursion whose decrease is proved by `omega` (`propext`, `Quot.sound`) still evaluates under `decide +kernel`.
  The proof that an argument decreases is passed along and never inspected; only the proof that the relation is
  well-founded is taken apart, and core's proof for `<` on `Nat` is free of axioms.

## 4. How much of Mathlib is free of axioms

**Question.** The same census, for Mathlib.

**Done.** `Census.lean` on `Mathlib`: 792 586 constants, 30 373 982 edges, ten minutes. The census agrees with
`collectAxioms` on 60 declarations drawn at random.

**Found.** 327 179 theorems with a name a person wrote (Lean's core included).

| | theorems | share |
|---|---|---|
| free of axioms | 30 232 | 9.2% |
| statement free of axioms, proof not | 182 447 | 55.8% |
| statement rests on an axiom | 114 500 | 35.0% |

| axiom | in the proof or the statement | in the statement |
|---|---|---|
| `propext` | 89.1% | 0.1% |
| `Quot.sound` | 83.8% | 5.1% |
| `Classical.choice` | 71.6% | 33.4% |

- `propext` is almost never part of what a theorem says. `Classical.choice` is part of a third of the statements:
  through the real numbers, cardinalities, and definitions by cases on an undecidable proposition.
- By area, the share free of axioms: `Order` 21.3%, `Logic` 26.0%, `Data` 12.7%, `Algebra` 12.6%, `Combinatorics`
  11.2%, `GroupTheory` 6.1%, `CategoryTheory` 5.6%, `Topology` 3.1%, `RingTheory` 1.9%, `NumberTheory` 1.5%,
  `MeasureTheory` 1.4%, `LinearAlgebra` 1.1%, `Analysis` 0.8%, `Probability` 0.1%. In `Analysis`, 88.9% of the
  statements already rest on an axiom.
- The 95 theorems of `Mathlib.NumberTheory` that are free of axioms are projections and extensionality lemmas
  (`Zsqrtd.im_add`, `ModularForm.neg_apply`). No theorem of Mathlib on the primes of `ℕ` is free of axioms.
  `Nat.exists_infinite_primes`, `Nat.Prime.dvd_mul`, `Nat.primeFactorsList_unique` and `Nat.Prime.irrational_sqrt`
  depend on all three; the definition `Nat.Prime` itself depends on `propext`.
- Free of axioms in Mathlib: `mul_assoc`, `mul_comm`, `mul_left_cancel`, `inv_inv` (the algebraic hierarchy's
  first lemmas), `Function.cantor_surjective` (Cantor's theorem), and `Nat.find` with `Nat.find_spec` and
  `Nat.find_min` (entry 9).

## 5. Number theory with no axioms

**Question.** Mathlib proves Euclid's theorem with three axioms. Is that needed? How far does number theory go
with none?

**Done.** `Tower.lean`, on core's `Nat` and its lemmas that are free of axioms. Its last command prints the axioms
of every declaration of the file; `check.sh` fails if any has one.

**Found.** All of the following are free of axioms.

| | Lean name |
|---|---|
| the least number principle for a decidable predicate, as a function | `Ax.least` |
| divisibility and primality are decidable | `Ax.decDvd`, `Ax.decPrime` |
| every `n ≥ 2` has a prime factor | `Ax.primeFactor`, `Ax.exists_prime_dvd` |
| Euclid: there is a prime above every `n` | `Ax.nextPrime`, `Ax.exists_prime_gt` |
| division with remainder | `Ax.div_rem` |
| Euclid's lemma: a prime that divides `ab` divides `a` or `b` | `Ax.Prime.dvd_mul` |
| `√p` is irrational: `a² = p·b²` only if `b = 0` | `Ax.Prime.sq_ne` |
| every positive number is a product of primes | `Ax.factor`, `Ax.exists_factorization` |
| and in one way only: two lists of primes with the same product hold each prime equally often | `Ax.factorization_unique` |

- None of this needed an axiom, and none of it needed a new idea. What it needed was to avoid `simp` and `omega`
  and to prove again the arithmetic that core proves with `propext` (`mul_assoc`, cancellation, `dvd_trans`).
- Euclid's lemma is proved without the gcd. For a prime `p` that divides `ab` and not `a`, take the least `m > 0`
  with `p ∣ mb`. Division with remainder shows that `m` divides every such number, among them `p` and `a`. So `m`
  is `1` or `p`; it is not `p`, which does not divide `a`; so `p ∣ b`.
- Uniqueness avoids permutations. `q^k` divides a product of primes if and only if `q` occurs at least `k` times
  in the list, so the number of occurrences is determined by the product.
- Core's `/` and `%` can be used without knowing anything about them. `Ax.decDvd` computes `n / d` and `n % d`,
  which the kernel runs on numerals with GMP, and only checks the result: `d * (n / d) = n` proves `d ∣ n`, and a
  remainder with `0 < r < d` and `d * q + r = n` refutes it. If neither check passes, a search decides. That case
  cannot occur, but no proof of that is needed, and core's depends on `propext`.

## 6. Proofs that run

**Question.** A proof with no axiom is a closed term of a type theory that computes. Does it run?

**Done.** `Tower.lean` states existence as a function into a subtype: `nextPrime n : {p // n < p ∧ Prime p}` is
Euclid's proof, and `factor n : {l // AllPrime l ∧ prod l = n}` is the existence half of the fundamental theorem.
`Compute.lean` asks the kernel to evaluate them (`decide +kernel`).

**Found.**

- Euclid's proof returns the least prime factor of `n! + 1`. For `n = 1, …, 10` the kernel computes
  `2, 3, 7, 5, 11, 7, 71, 61, 19, 11`, and `13` for `n = 12`.
- The proof of factorization factors: `360 = [2, 2, 2, 3, 3, 5]`, `1000001 = [101, 9901]`, and
  `10! + 1 = [11, 329891]` in two minutes of the kernel (329 891 steps of the search). The statements
  `Prime 9901` and `¬ Prime 5041` are decided the same way. Each of these theorems depends on no axiom.
- The kernel passes arguments unevaluated and does not share their evaluation. Three things were needed before
  the larger runs finished.
  1. A counter that a recursion passes on as `s + 1` becomes a tower `0 + 1 + 1 + …` that is evaluated again at
     each use: the search was quadratic (`Prime 9901` took 101 s). `Ax.strict` matches on the number before
     passing it on, which makes the kernel reduce it to a numeral first (4 s).
  2. A quotient passed down a recursion carries the whole computation above it and is used several times at each
     level: `factor 360`, six levels deep, took 9.6 s. Matching the quotient against `0` and `m + 1` evaluates
     it once (0.8 s).
  3. A recursive call wrapped in a `match` nests the kernel's evaluation as deep as the search is long. With
     the search's result type fixed (`start + fuel = bound`), the call is the whole result of a step.

## 7. Where the axioms enter Mathlib

**Question.** 71.6% of Mathlib's theorems depend on `Classical.choice`. Through what?

**Done.** `gateways.c` computes the dominator tree of the graph of constants, reversed, from an axiom. A constant
dominates a theorem if every chain of uses from the theorem to the axiom passes through it: if the constant were
proved without the axiom, the theorem would be free of it. `choice_kinds.py` sorts the theorems by which of three
kinds of constant their chains meet first: excluded middle (the theorems of the namespace `Classical` whose
statement is free of choice, such as `Classical.em` and `Classical.byContradiction`), classical decidability
(`Classical.propDecidable`, an instance of `Decidable p` for every `p`), and the choice of an element (every
other route, such as `Classical.choose`).

**Found.**

- `Classical.choice` is named by 222 constants, `Quot.sound` by 285, `propext` by 85 592.
- Half of the theorems that depend on `Quot.sound` (137 419 of 274 063) depend on it only through `funext`.
- `propext` has no gateway. The constant that dominates most is `eq_true`, with 4.5%.
- `Classical.propDecidable` dominates 26.6% of the theorems that depend on choice. No other constant dominates
  more than 5.1% (`Classical.byContradiction`, itself below `propDecidable`): most theorems reach choice by
  several routes.
- Of the 234 116 theorems that depend on `Classical.choice`, 75 027 (32.0%) never reach it by the choice of an
  element: they use excluded middle and classical decidability only. Among the 124 916 whose statement is free
  of choice, it is 71 209 (57.0%).

| route to `Classical.choice` | theorems | share |
|---|---|---|
| excluded middle, classical decidability and the choice of an element | 141 272 | 60.3% |
| excluded middle and classical decidability | 49 342 | 21.1% |
| excluded middle only | 14 121 | 6.0% |
| classical decidability only | 11 564 | 4.9% |
| excluded middle and the choice of an element | 11 207 | 4.8% |
| classical decidability and the choice of an element | 3 333 | 1.4% |
| the choice of an element only | 3 277 | 1.4% |
