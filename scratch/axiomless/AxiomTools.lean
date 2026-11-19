import Lean

/-!
# Instruments

* `#axiom_free c₁ c₂ …` fails unless each constant depends on no axiom at all (what `#print axioms` reports as
  "does not depend on any axioms").
* `#axioms_table ns` prints the axioms of every theorem and definition of the namespace `ns`, in source order.
  It leaves out the lemmas `injEq` that Lean generates for the constructors of an inductive type: each states an
  equality between propositions and depends on `propext`.
* `#why c` prints, for each axiom that `c` depends on, a shortest chain of constants from `c` to the axiom.
* `#entries c` prints the constants that `c` depends on and that name an axiom themselves.
* `#without c d` prints the axioms that `c` still reaches when the constant `d` is not entered: none, if every
  chain from `c` to an axiom passes through `d`.

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
    if ns.getId.isPrefixOf n && !n.isInternalDetail && n.getString! != "injEq" then
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

elab "#entries " c:ident : command => do
  let env ← getEnv
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo c)
  let mut seen : Std.HashSet Name := {n}
  let mut queue : Array Name := #[n]
  let mut entries : Array Name := #[]
  let mut i := 0
  while i < queue.size do
    let x := queue[i]!
    i := i + 1
    let some ci := env.find? x | continue
    let ds := uses ci
    if !(ci matches .axiomInfo _) && ds.any (fun d => (env.find? d).any (· matches .axiomInfo _)) then
      entries := entries.push x
    for d in ds do
      unless seen.contains d do
        seen := seen.insert d
        queue := queue.push d
  logInfo m!"{n} depends on {seen.size - 1} constants; {entries.size} of them name an axiom: {entries}"

elab "#without " c:ident d:ident : command => do
  let env ← getEnv
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo c)
  let cut ← liftCoreM (realizeGlobalConstNoOverloadWithInfo d)
  let mut seen : Std.HashSet Name := {n}
  let mut queue : Array Name := #[n]
  let mut axs : Array Name := #[]
  let mut i := 0
  while i < queue.size do
    let x := queue[i]!
    i := i + 1
    if x == cut then continue
    let some ci := env.find? x | continue
    if ci matches .axiomInfo _ then axs := axs.push x
    for y in uses ci do
      unless seen.contains y do
        seen := seen.insert y
        queue := queue.push y
  if axs.isEmpty then logInfo m!"{n} without {cut}: no axiom" else logInfo m!"{n} without {cut}: {axs}"
