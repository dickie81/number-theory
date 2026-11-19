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
- Two things that other systems add as axioms are already rules of this kernel. Any two proofs of a proposition
  are equal by definition, so uniqueness of identity proofs holds by `refl` (`uip`). And once an equality exists
  the kernel provides `Quot`, with `Quot.mk`, `Quot.lift` and `Quot.ind`, and `Quot.lift` computes on `Quot.mk`
  (`Quot.lift_mk`); only `Quot.sound` is an axiom.

## 2. How much of Lean's own library is free of axioms

**Question.** Lean's core library (`Init`, `Std`, `Lean`) is written without regard for axioms. How much of it
uses none?

**Done.** `Census.lean` imports the modules, and for every constant computes the axioms it depends on, as
`#print axioms` does, in one pass over the graph of constants. It also computes the axioms that a constant reaches
without entering the proof of a theorem. For a theorem that is what its statement rests on.
`census_report.py` prints the tables.

**Found.** 207 900 constants. 57 258 are theorems whose name is not internal or private. Lean generated 10 246
of those itself (`injEq`, `inj`, `sizeOf_spec`, `congr_simp`, `eq_def` and the like, which come with every
inductive type and definition); the tables count the other 47 012, the theorems that a person wrote.

| | theorems | share |
|---|---|---|
| free of axioms | 5 011 | 10.7% |
| statement free of axioms, proof not | 38 309 | 81.5% |
| statement rests on an axiom | 3 692 | 7.9% |

- Four fifths of the theorems state something that mentions no axiom, and prove it with one.
- The axioms enter through few constants. `Classical.choice` is named by 25 constants and `Quot.sound` by 56.
  `propext` is named by 13 463, of which 10 703 are auxiliary lemmas that `simp` generates.
- Lean itself generates a theorem that depends on `propext` for every constructor with arguments:
  `C.injEq : (C a = C b) = (a = b)`, an equality between propositions. None of the 2 595 is free of axioms.
- Of the 2 012 theorems of the namespace `Nat`, 380 are free of axioms.

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
  `propext`. It also turns each equivalence it rewrites by into an equality, in an auxiliary lemma `_simp_n` that
  names `propext`.
- Basic lemmas of core depend on `propext` this way: `Nat.succ_ne_zero`, `Nat.one_ne_zero`, `Nat.mul_assoc`,
  `Nat.sub_add_cancel`, `Nat.dvd_trans`, `Int.add_comm`, `List.append_assoc`, and all of the theory of `/` and
  `%` (`Nat.div_add_mod`, `Nat.mod_eq_of_lt`, …). `Nat.pow_lt_pow_right` depends on `Classical.choice`, through a
  `simp` lemma on the negation of an implication. `by decide` proves `3 ∣ 12` with `propext`, through core's
  instance `Nat.decidable_dvd`. `Nat.gcd_zero_left` depends on `Quot.sound`: the unfolding lemma of well-founded
  recursion on `Nat` (`WellFounded.Nat.fix_eq`) is proved with `funext`.
- So a proof that is to be free of axioms cannot use `simp`, `omega` or most of core's lemmas on division. It can
  use `induction`, `cases`, `rw` by equations, `decide`, and the 380 lemmas.
- Axioms in a termination proof do not stop the kernel from computing. A function defined by well-founded
  recursion whose decrease is proved by `omega` (`propext`, `Quot.sound`) still evaluates under `decide +kernel`.
  Lean compiles a recursion on a measure in `Nat` to a structural recursion on a bound (`WellFounded.Nat.fix`),
  and the proof that the argument decreases is passed along and never taken apart.

## 4. How much of Mathlib is free of axioms

**Question.** The same census, for Mathlib.

**Done.** `Census.lean` on `Mathlib`: 792 586 constants, 30 373 982 edges, ten minutes. The census agrees with
`collectAxioms` on 60 declarations drawn at random.

**Found.** 306 370 theorems that a person wrote (Lean's core included; Lean generated another 20 809).

| | theorems | share |
|---|---|---|
| free of axioms | 22 475 | 7.3% |
| statement free of axioms, proof not | 173 084 | 56.5% |
| statement rests on an axiom | 110 811 | 36.2% |

| axiom | in the proof or the statement | in the statement |
|---|---|---|
| `propext` | 90.9% | 0.1% |
| `Quot.sound` | 86.3% | 5.2% |
| `Classical.choice` | 73.6% | 34.5% |

- `propext` is almost never part of what a theorem says. `Classical.choice` is part of a third of the statements:
  through the real numbers, cardinalities, and definitions by cases on an undecidable proposition.
- By area, the share free of axioms: `Logic` 25.7%, `Order` 20.7%, `Algebra` 12.1%, `Data` 11.8%, `Combinatorics`
  10.3%, `GroupTheory` 5.3%, `CategoryTheory` 4.5%, `Topology` 2.8%, `RingTheory` 1.7%, `NumberTheory` 1.4%,
  `MeasureTheory` 1.4%, `LinearAlgebra` 0.9%, `Analysis` 0.7%, `Probability` 0.1%. In `Analysis`, 89.2% of the
  statements already rest on an axiom.
- The 84 theorems of `Mathlib.NumberTheory` (of 5 964) that are free of axioms are projections and extensionality lemmas
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
- The kernel's time is linear in the length of the search, about 0.3 ms a step: `Prime 9901` takes 4 s,
  `Prime 99991` 35 s, `Prime 329891` 86 s. Its memory grows too: the run on `10! + 1` peaks at 13.5 GB.
- How an instance is written decides the cost. The first primality test here was a bounded `∀ d < p + 1`, decided
  by core's `Nat.decidableBallLT`. That instance wraps the predicate once more at each step, and the kernel takes
  quadratic time: 1.9 s for `Prime 1009`, 17.6 s for `4001`, 117 s for `9901`. `Ax.decPrime` asks instead whether
  the least divisor above `1` is `p`.
- The kernel passes arguments on unevaluated. The candidate of the search, passed on as `s + 1`, becomes a term
  `0 + 1 + 1 + …`. `Ax.strict` matches on the number first, so that the kernel reduces it to a numeral and passes
  the numeral. Up to 100 000 steps this makes no difference. At 329 891 steps the search takes 86 s with it, and
  without it was stopped after nine minutes.
- A correction. An earlier version of this entry said that three devices were needed (`strict`, matching the
  quotient against `0` and `m + 1` in `factor`, and making the recursive call the whole result of a step), with a
  timing for each. Those timings compared runs that differed in more than one way: one was a first run that also
  loaded the libraries, one used the quadratic primality test. Measured one at a time on the same inputs, the
  last two devices change nothing (`10! + 1`: 115 s without the match on the quotient, 117 s with it), and they
  are no longer in the file.

## 7. Where the axioms enter Mathlib

**Question.** 73.6% of Mathlib's theorems depend on `Classical.choice`. Through what?

**Done.** `gateways.c` computes the dominator tree of the graph of constants, reversed, from an axiom. A constant
dominates a theorem if every chain of uses from the theorem to the axiom passes through it: if the constant were
proved without the axiom, the theorem would be free of it. `choice_kinds.py` sorts the theorems by which of three
kinds of constant their chains meet first: excluded middle (the theorems of the namespace `Classical` whose
statement is free of choice, such as `Classical.em` and `Classical.byContradiction`), classical decidability
(`Classical.propDecidable`, an instance of `Decidable p` for every `p`), and the choice of an element (every
other route, such as `Classical.choose`).

**Found.**

- `Classical.choice` is named by 222 constants, `Quot.sound` by 285, `propext` by 85 592 (51 134 of them
  auxiliary lemmas of `simp`).
- Half of the theorems that depend on `Quot.sound` (131 052 of 264 342) depend on it only through `funext`.
- `propext` has no gateway. The constant that dominates most is `eq_true`, with 4.6%.
- `Classical.propDecidable` dominates 25.8% of the theorems that depend on choice. No other constant dominates
  more than 5.0% (`Classical.byContradiction`, itself below `propDecidable`): most theorems reach choice by
  several routes.
- Of the 225 532 theorems that depend on `Classical.choice`, 70 735 (31.4%) never reach it by the choice of an
  element: they use excluded middle and classical decidability only. Among the 119 890 whose statement is free
  of choice, it is 66 997 (55.9%).

| route to `Classical.choice` | theorems | share |
|---|---|---|
| excluded middle, classical decidability and the choice of an element | 137 758 | 61.1% |
| excluded middle and classical decidability | 45 978 | 20.4% |
| excluded middle only | 13 498 | 6.0% |
| classical decidability only | 11 259 | 5.0% |
| excluded middle and the choice of an element | 10 771 | 4.8% |
| classical decidability and the choice of an element | 3 218 | 1.4% |
| the choice of an element only | 3 050 | 1.4% |

## 8. The axioms as hypotheses

**Question.** With no axiom, excluded middle and the others are not theorems. What can still be said about them?

**Done.** `Principles.lean` states each principle as a proposition and proves the implications between them.
Every proof is free of axioms: the principles appear only as hypotheses.

**Found.**

    EM ⟺ DNE ⟺ Peirce              EM ⟹ Linear ⟹ WEM ⟺ DeMorgan
    TwoValued ⟺ EM ∧ PropExt        EM ⟹ LPO ⟺ WLPO ∧ MP

- `TwoValued` says that every proposition is equal to `True` or to `False`. It is exactly excluded middle
  together with propositional extensionality (`twoValued_iff`). So with no axiom the number of propositions is
  left open: `TwoValued` cannot be refuted, since the axioms prove it, and a proof of it would be a proof of
  excluded middle.
- Diaconescu's theorem needs little choice (`em_of_choice`): a function that picks a point from each predicate
  on `Bool` that holds somewhere, with extensionality for those predicates, gives excluded middle.
- `Quot.sound` at a function type gives function extensionality at that type (`funext_of_sound`). The step that
  makes it work is a rule of the kernel: `Quot.lift f h (Quot.mk r a)` computes to `f a`.
- Some classical-looking facts need nothing: `¬¬(p ∨ ¬p)` for each `p`, `¬¬¬p ↔ ¬p`, excluded middle for a
  decidable proposition, and Cantor's theorem (`cantor`), where an equality of predicates is only used to
  transport a proof.

## 9. A proof as fuel, and an axiom as a term that does not compute

**Question.** An existence proof in `Prop` cannot be opened to get its witness. Can it be used at all for
computing? And what exactly does an axiom do to computation?

**Done.** `Stuck.lean`.

**Found.**

- `Search.find` takes a decidable predicate on `Nat` and a proof of `∃ n, P n`, and returns the least such `n`,
  with no bound on the search. It recurses on a proof of `Acc`. A proposition can be eliminated into data when
  it has one constructor whose arguments are proofs or are fixed by its type; `Acc` is such a proposition, and
  it is recursive. Mathlib's `Nat.find` is the same construction and is free of axioms too.
- When the proof is free of axioms, the kernel runs the search. Given the proof that `n = 1000` satisfies
  `1000 < n²`, it finds `32` (`find_sq`). The proof is the fuel: the kernel takes it apart as it goes.
- When the proof is by contradiction (`Classical.byContradiction`), the same definition does not evaluate: the
  kernel stops at a term that is not a pair of a number and a proof. The value is still `32`, by a theorem
  (`find_sq_classical`) and not by computation.
- `five` is the numeral `5` carried along an equality of propositions that `propext` gives. It is a closed term
  of type `Nat`, it is equal to `5` (`five_eq`), and it does not reduce to `5`: `#reduce five` prints
  `five._proof_1 ▸ 5`.
- `chosen := Classical.choice ⟨5⟩` is a closed term of type `Nat` that is not provably equal to any numeral.
- So an axiom is a constant with no rule of computation. Where the kernel must take a proof apart (the
  equality in a cast, the accessibility proof in a recursion, the pair in an existence proof), an axiom stops
  it. Where a proof is only passed along, an axiom changes nothing (entry 3). With no axiom, a closed term of
  type `Nat` computes to a numeral in every case tried here.

## 10. What one proposition generates

**Question.** With excluded middle, a proposition `p` generates four propositions up to equivalence: `False`,
`p`, `¬p`, `True`. How many without it?

**Done.** `Ladder.lean` defines the formulas in one variable, derivability in intuitionistic propositional logic
(a Hilbert system), and the ladder of Rieger and Nishimura:

    A 0 = p            B 0 = ¬p
    A (k+1) = A k ∨ B k            B (k+1) = A (k+1) → A k

It also defines truth in one Kripke model: the worlds are the natural numbers, world `w` sees itself and every
world at least two below, and `p` holds at world `0` only.

**Found.** All free of axioms.

- What the Hilbert system derives holds for every proposition of Lean (`sound_eval`) and at every world of the
  model (`sound`).
- In the model, `A k` holds exactly at the worlds `≤ k`, and `B k` at the worlds `< k` and at `k + 1` (`truth`).
  So every formula of the ladder fails somewhere, and any two differ somewhere: none is derivable
  (`not_derivable_A`, `not_derivable_B`), and no two are equivalent (`A_A`, `B_B`, `A_B`). One proposition
  generates infinitely many.
- The first rungs are the classical principles: `A 1` for all `p` is excluded middle, `A 2` is weak excluded
  middle, `B 2` is double negation elimination (`A_one`, `A_two`, `B_two`). In particular `p ∨ ¬p` is not
  derivable (`not_derivable_em`).
- With excluded middle as a hypothesis, the ladder collapses: `A k` holds for `k ≥ 1`, `B k` for `k ≥ 2`, and
  `B 1` is equivalent to `p` (`collapse_A`, `collapse_B`, `B_one`).
- What this does not prove: that Lean with no axiom cannot prove `∀ p, A k` for `k ≥ 1`. That is a statement
  about Lean, not in it. The theorems here are about the Hilbert system, and about propositions that vary over
  the worlds of a model; that Lean's own propositional reasoning with no axiom derives no more than the Hilbert
  system is the expected metatheorem and is not checked here.

## 11. The library's own certificates

**Question.** This library's Linnik theorems rest on kernel computations on natural numbers: 1552 parts for
Theorem 1.2, each proved by `decide +kernel`. That is the kind of proof that needs no axiom. Do they have one?

**Done.** `lake build SieveHint21500P1` builds the first of the 17 part files (89 parts, four minutes of the
kernel) and the 18 modules it imports, which load no more of Mathlib than `Mathlib.Data.Nat.Notation`. Then
`CertAxioms.lean`, the census on those modules, and `DivLt.lean`. `AxiomTools.lean` has two more commands for
this: `#entries c`, the constants below `c` that name an axiom, and `#without c d`, the axioms `c` still reaches
when `d` is not entered.

**Found.**

- Each of the 89 parts depends on exactly one axiom, `propext`, and on neither `Classical.choice` nor
  `Quot.sound`. Of the 246 definitions of the 19 modules, 168 are free of axioms and 78 depend on `propext`.
- The route is one chain. `SieveAd.cfgJM` reads the hints with `&&&`. Core's `Nat.land` is `Nat.bitwise`, a
  definition by well-founded recursion, and its termination proof uses `Nat.div_lt_self : 0 < n → 1 < k → n / k < n`,
  which core proves with `simp`:

      tree21500_0 → solve21500 → cfgJM → Nat.land → Nat.bitwise → … → Nat.bitwise_rec_lemma → Nat.div_lt_self
        → eq_false → propext

- It is the only route. A part depends on 550 constants; three of them name `propext` (`eq_false`, `eq_true`,
  `and_self`); and with `Nat.div_lt_self` left out, a part reaches no axiom.
- `Ax.div_lt_self` in `DivLt.lean` proves the same statement with no axiom, from the definition of core's
  division. So the dependence is an accident of one proof in core. The certificates of the Linnik theorems are
  one lemma of Lean's core library away from depending on no axiom at all, and nothing in this library would
  have to change.
- The same holds for any definition that uses `&&&`, `|||`, `^^^` or `Nat.testBit`: in core they are
  definitions that depend on `propext`.

## What the entries add up to

- With no axiom, Lean is a programming language whose programs are proofs: Euclid's theorem is a function that
  returns a prime, and the kernel runs it (5, 6, 9).
- The three axioms are used for three different things. `propext` is what `simp` uses to turn an equivalence
  into an equality; it is in 90.9% of Mathlib's proofs and 0.1% of its statements, and number theory up to the
  fundamental theorem of arithmetic needs none of it (3, 4, 5). `Quot.sound` is used half of the time only
  as `funext` (7). `Classical.choice` is the one that statements rest on, and 31.4% of the theorems that
  depend on it never choose an element: they use it as excluded middle (7).
- What the axioms cost is computation: each is a constant that the kernel cannot reduce (9). What they buy,
  at the level of one proposition, is the collapse of an infinite ladder to four values (8, 10).
- Much of the dependence on axioms is an accident of how a proof was written, and it travels. One `simp` in
  core's proof of `n / k < n` puts `propext` under bitwise `and`, and from there under every kernel certificate
  of this library's Linnik theorems (11).

## Not done

- Of this repository's library, only the first certificate part file and its imports were built and measured
  (entry 11). The whole build takes hours. `Census.lean` runs on any built module.
- No theorem here goes beyond the fundamental theorem of arithmetic. The next candidates are Fermat's little
  theorem and the sum of two squares; Mathlib's proofs of both (`ZMod.pow_card_sub_one_eq_one`,
  `Nat.Prime.sq_add_sq`) depend on all three axioms.
- A linear arithmetic tactic free of axioms would remove most of the hand work in `Tower.lean`. `omega`'s
  support lemmas depend on `propext` and `funext` (entry 3); a version by reflection, with a checker proved once,
  is the obvious design.
