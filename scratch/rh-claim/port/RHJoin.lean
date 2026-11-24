import RHClaim

/-!
# The archive's statements and the library's deductions in one environment

This file is compiled on the archive's pins by

    python3 -I tools/rh/bundle_files.py … --with external/alpoge-rh/bundle-native scratch/rh-claim/port/RHJoin.lean

which imports, beside `RHClaim` and what it imports (the port of the library), every bundle of the archive's
build. `riemannHypothesis` and `LFunction_eq_zero_re` are the archive's (`Main.lean`).

It compiles only if the archive's build holds those two theorems, and its last command is an error unless every
theorem here depends on the three standard axioms only: a proof of the archive or of the port that failed and
was kept as `sorry` would show there. Until that command passes on a finished build, nothing here is established.

The last command does not ask Lean for the axioms. Lean keeps, in each `.olean`, the axioms that each declaration
depended on when its file was compiled, and answers from that; the archive's build compiles a bundle again after
a repair without compiling again what was built on it, so those records can be out of date in either direction.
`#assert_axioms_by_walk` reads the constants themselves, from the kernel's environment: everything that the
theorem's statement and proof name, and what those name, to the end.
-/

open Lean Elab Command in
/-- An error unless the constants named depend on no axiom but `propext`, `Classical.choice` and `Quot.sound`,
found by walking the kernel's terms and not from the axioms recorded when each file was compiled. -/
elab "#assert_axioms_by_walk" ids:(ppSpace ident)+ : command => do
  let env := (← getEnv).checked.get
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    unless seen.contains n do
      seen := seen.insert n
      todo := todo.push n
  let mut bad : Array Name := #[]
  let mut found : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut count : Nat := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    count := count + 1
    let mut used : Array Name := #[]
    match env.find? n with
    | some (.axiomInfo v) =>
      found := found.push n
      unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do bad := bad.push n
      used := v.type.getUsedConstants
    | some (.defnInfo v) => used := v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v) => used := v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => used := v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.quotInfo _) => pure ()
    | some (.ctorInfo v) => used := v.type.getUsedConstants
    | some (.recInfo v) => used := v.type.getUsedConstants
    | some (.inductInfo v) => used := v.type.getUsedConstants ++ v.ctors.toArray
    | none => missing := missing.push n
    for u in used do
      unless seen.contains u do
        seen := seen.insert u
        todo := todo.push u
  unless bad.isEmpty && missing.isEmpty do
    throwError "of {count} constants walked, axioms beyond the standard three: {bad}; not in the environment: {missing}"
  -- said on standard output as well, so that a run shows the walk and not only the absence of an error
  let line := s!"assert_axioms_by_walk: {count} constants walked from {ids.size} theorems; the axioms met: {found.qsort Name.lt}"
  IO.println line
  logInfo line

open Complex Real Filter Topology Asymptotics
open scoped Chebyshev

namespace RHJoin

/-- The archive's `riemannHypothesis` and `LFunction_eq_zero_re`: the hypothesis of `RHClaim.lean`. -/
theorem claim : RHClaim.Claim := ⟨riemannHypothesis, LFunction_eq_zero_re⟩

theorem psi {ε : ℝ} (hε : 0 < ε) : (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ (1 / 2 + ε) :=
  RHClaim.psi claim.rh hε

theorem mertens {η : ℝ} (hη : 0 < η) :
    (fun x ↦ PsiOmega.summ PsiOmega.fμ x) =O[atTop] fun x ↦ x ^ (1 / 2 + η) :=
  RHClaim.mertens claim.rh hη

theorem divisor {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    (fun x ↦ PsiOmega.summ (fun n ↦ (DivisorExponent.dk k n : ℝ)) x
      - x * (DivisorExponent.Pk k).eval (Real.log x)) =O[atTop] fun x ↦ x ^ (1 / 2 + η) :=
  RHClaim.divisor claim.rh hk hη

theorem squarefree {η : ℝ} (hη : 0 < η) :
    (fun x ↦ PsiOmega.summ SquarefreeCount.sqf x - 6 / π ^ 2 * x) =O[atTop] fun x ↦ x ^ (2 / 5 + η) :=
  RHClaim.squarefree claim.rh hη

theorem lindelof : CrossCriteria.Lindelof := RHClaim.lindelof claim.rh

theorem densityHypothesis : CrossCriteria.DensityHypothesis := RHClaim.densityHypothesis claim.rh

theorem pivot_ge {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) :
    999 / 1000 * (2 / 45) * (13 / 10) * x N ^ 2 ≤ BallWeil.form N x :=
  RHClaim.pivot_ge claim.rh hN x

theorem orbitLattice (k : ℕ) (c : ℕ → ℝ) (hk : 1 ≤ k) :
    BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n) :=
  RHClaim.orbitLattice claim.rh k c hk

theorem shortest {N : ℕ} (a : ℕ → ℤ) (ha : ∃ n ∈ Finset.Icc 1 N, a n ≠ 0) :
    BallWeil.gram 1 1 ≤ BallWeil.form N (fun n => (a n : ℝ)) :=
  RHClaim.shortest claim.rh a ha

theorem balance (N : ℕ) : BallRate.ExcessLe N 0 := RHClaim.balance claim.rh N

theorem psiChi {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {η : ℝ} (hη : 0 < η) :
    ChiPNT.psiChi χ =O[atTop] fun x ↦ x ^ (1 / 2 + η) :=
  RHClaim.psiChi claim.grh hχ hη

theorem linnik_two {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ (2 + η) :=
  RHClaim.linnik_two claim.grh hη

end RHJoin

#assert_axioms_by_walk RHJoin.claim RHJoin.psi RHJoin.mertens RHJoin.divisor RHJoin.squarefree RHJoin.lindelof
  RHJoin.densityHypothesis RHJoin.pivot_ge RHJoin.orbitLattice RHJoin.shortest RHJoin.balance RHJoin.psiChi
  RHJoin.linnik_two
