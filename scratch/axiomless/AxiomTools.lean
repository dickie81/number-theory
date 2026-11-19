import Lean

/-!
# Instruments

* `#axiom_free c₁ c₂ …` fails unless each constant depends on no axiom at all (what `#print axioms` reports as
  "does not depend on any axioms").
* `#axioms_table ns` prints the axioms of every theorem and definition of the namespace `ns`, in source order.
* `#why c` prints, for each axiom that `c` depends on, a shortest chain of constants from `c` to the axiom.

The other files of this directory import this one; `check.sh` compiles it first.
-/

open Lean Elab Command

namespace AxiomTools

/-- The constants `#print axioms` follows from a constant. -/
def uses (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- Breadth-first search from `c`: for each axiom reached, the chain of constants that reaches it first. -/
def chains (env : Environment) (c : Name) : Array (List Name) := Id.run do
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : Std.HashSet Name := {c}
  let mut queue : Array Name := #[c]
  let mut found : Array (List Name) := #[]
  let mut i := 0
  while i < queue.size do
    let x := queue[i]!
    i := i + 1
    let some ci := env.find? x | continue
    if ci matches .axiomInfo _ then
      let mut path := [x]
      let mut y := x
      while y != c do
        y := parent[y]!
        path := y :: path
      found := found.push path
    for d in uses ci do
      unless seen.contains d do
        seen := seen.insert d
        parent := parent.insert d x
        queue := queue.push d
  return found

end AxiomTools

open AxiomTools

elab "#axiom_free " cs:ident+ : command => do
  for c in cs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo c)
    let axs ← liftCoreM (collectAxioms n)
    unless axs.isEmpty do
      throwErrorAt c "{n} depends on axioms: {axs.qsort Name.lt}"

elab "#axioms_table " ns:ident : command => do
  let env ← getEnv
  let mut rows : Array (Nat × String) := #[]
  for (n, _) in env.constants.map₂.toList do
    if ns.getId.isPrefixOf n && !n.isInternalDetail then
      let axs := (← liftCoreM (collectAxioms n)).qsort Name.lt
      let line := (← liftCoreM (findDeclarationRanges? n)).map (·.range.pos.line) |>.getD 0
      let shown := if axs.isEmpty then "—" else ", ".intercalate (axs.toList.map toString)
      rows := rows.push (line, s!"{n.replacePrefix ns.getId .anonymous}: {shown}")
  for (_, r) in rows.qsort (fun a b => a.1 < b.1) do
    logInfo r

elab "#why " c:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo c)
  let found := chains (← getEnv) n
  if found.isEmpty then logInfo m!"{n} depends on no axiom"
  for path in found do
    logInfo (" → ".intercalate (path.map toString))
