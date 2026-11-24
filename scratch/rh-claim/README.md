# The library's theorems from the claimed proof of RH (not wired into the lakefile)

`RHClaim.lean` takes as a hypothesis two statements of the Lean archive that Levent Alpöge posted on
20 November 2026 (`tools/rh/README.md`): Mathlib's `RiemannHypothesis`, and the archive's `DirichletLZerosOnLine`,
that every zero of every Dirichlet `L`-function in the open critical strip has real part `1/2`. It shows that the
archive's other three statements follow from those two, and states what this library then gives.

Nothing in it is unconditional here: the archive is not compiled in this repository's environment. On the archive's
own pins the hypothesis is discharged (`port/RHJoin.lean`, below). The library itself now proves the deductions of
the table below, but those on the orbit's form, from its own statement of RH and GRH, `HalfPlaneGRH.RHandGRH`:
`HalfPlaneGRH.RHandGRH.corollaries` (`lib/pnt/RHHarvest.lean`), and Linnik's through
`LinnikGRH.dirichletRH_of_rhAndGRH`.

Check it with

```sh
lake build LinnikGRH InghamDensity SquarefreeCount DivisorExponent ChiPNT HalfPlanePNT Subconvexity PivotSharp BallRate
lake env lean scratch/rh-claim/RHClaim.lean
```

The file ends with `#print axioms` for each theorem. Every one depends on `propext`, `Classical.choice` and
`Quot.sound` only.

| Theorem | From | Statement | By |
|---|---|---|---|
| `RHClaim.psi` | RH | `ψ(x) = x + O(x^{1/2+ε})` | `HalfPlanePNT.psi_isBigO_of_zeroFree` |
| `RHClaim.mertens` | RH | `M(x) = O(x^{1/2+η})` | `MertensExponent.mertens_isBigO_of_zeroFree` |
| `RHClaim.divisor` | RH | `Σ_{n ≤ x} d_k(n) = x P_k(log x) + O(x^{1/2+η})` | `DivisorExponent.divisor_isBigO_of_zeroFree` |
| `RHClaim.squarefree` | RH | the squarefree numbers up to `x` number `(6/π²)x + O(x^{2/5+η})` | `SquarefreeCount.squarefree_isBigO_of_zeroFree` |
| `RHClaim.lindelof`, `RHClaim.densityHypothesis` | RH | the Lindelöf hypothesis and the density hypothesis | `Subconvexity.lindelof_of_RH`, `InghamDensity.densityHypothesis_of_lindelof` |
| `RHClaim.pivot_ge`, `RHClaim.orbitLattice`, `RHClaim.shortest` | RH | the orbit-lattice paper's statements: every pivot after the first is at least `0.0577`, the orbit-lattice conjecture, and `w_1` a shortest vector | `PivotSharp.pivot_ge_rh`, `PivotSharp.orbitLattice_of_rh`, `PivotSharp.shortest_of_rh` |
| `RHClaim.balance` | RH | balance at every level: `−Q_N(x) ≤ 0` for every `N` and `x`, the excess of `BallRate` is zero. The archive does not prove this as a positivity of the form (`tools/rh/README.md`, "The analytic step") | `BallRate.rh_iff_balance` |
| `RHClaim.psiChi` | RH for the `L`-functions | `ψ(x, χ) = O(x^{1/2+η})` for `χ ≠ 1` | `ChiPNT.psiChi_isBigO_of_zeroFree` |
| `RHClaim.linnik_two` | RH for the `L`-functions | Linnik's theorem with every exponent above `2` | `LinnikGRH.linnik_two_of_GRH` |

When the archive's `Main` and this file compile in one environment, `RHClaim.Claim` is
`⟨riemannHypothesis, LFunction_eq_zero_re⟩`, and each theorem loses its hypothesis.

## On the archive's pins

The archive pins Lean `v4.33.1` and a Mathlib of 21 August 2026; this library pins Lean `v4.35.0-rc3` and a
Mathlib of 29 September. `port/` holds what it takes to compile this file and the 346 modules of the library
that it reaches on the archive's pair (`tools/rh/README.md`, "The port of the library to the archive's pins",
has the account and the commands):

| File | What it is |
|---|---|
| `port/PortCompat.lean` | Compiled first and imported by every file of the port: the names of the newer Lean and Mathlib that the library uses and the older lack, the newer defaults of `convert`, the lemmas that only the newer Mathlib marks `@[simp]` |
| `port/simp_out.json` | The lemmas that only the older Mathlib marks `@[simp]`, taken out of the simp set of the port's files |
| `port/patches/` | 27 patches against the library's files, 67 lines: the proofs that still needed a hand. No statement changes, but for `arctan` written `Real.arctan` in three lemmas of the vendored `PrimeNumberTheoremAnd` |
| `port/PortCheck.lean` | An error unless every theorem of `RHClaim.lean` depends on the three standard axioms on the archive's pins |
| `port/RHJoin.lean` | `RHClaim.Claim` from the archive's `riemannHypothesis` and `LFunction_eq_zero_re`, and each theorem above without its hypothesis; compiled with the archive's build, and an error unless each depends on the three standard axioms, read from the kernel's terms |

The port compiles: on 21 November 2026 all 349 files, `PortCheck.lean` among them, compiled on the archive's pins
with no error. `RHJoin.lean` needed the archive's own build finished and checked, which was still running then. It
has since compiled against that build, with no error, and every theorem in it depends on `propext`,
`Classical.choice` and `Quot.sound` only (`tools/rh/README.md`, "The state of the build"). So on the archive's pins
the theorems of this directory hold without their hypothesis; in this repository's environment they stay
conditional.
