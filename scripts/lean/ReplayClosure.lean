import Lean.Replay

/-!
# Replaying a theorem's dependencies into an empty kernel (`scripts/kernel_check.sh`)

`lean --run scripts/lean/ReplayClosure.lean MODULE THEOREM` (under `lake env`) imports `MODULE` and collects the
constants that `THEOREM`'s type and value mention, transitively. It adds each inductive's mutual block and
constructors, each constructor's inductive and each recursor's block, which re-adding an inductive needs. Then it
sends them, in dependency order, to the kernel of `mkEmptyEnvironment` with `Lean.Kernel.Environment.replay`, as
`leanchecker --fresh` does for every constant a module imports. Every definition, theorem, opaque and inductive is
re-checked. Constructors and recursors are compared with the ones the kernel generates. Nothing is taken from the
`.olean` files but the terms. It then checks that every constant of the closure is in the replayed environment,
identical to the imported one, and prints the closure's size, its constants by kind and its axioms.

`#print axioms` reads the environment as the elaborator left it, so it does not see a declaration that a metaprogram
added without the kernel (`debug.skipKernelTC`). This does.
-/

open Lean

/-- The constants `root` depends on, with what replaying an inductive needs. -/
def closure (env : Environment) (root : Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut seen : Std.HashMap Name ConstantInfo := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    let some ci := env.find? c | throw <| IO.userError s!"{c} is not in the environment"
    seen := seen.insert c ci
    stack := stack ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then stack := stack ++ v.getUsedConstants
    match ci with
    | .inductInfo v => stack := stack ++ v.all.toArray ++ v.ctors.toArray
    | .ctorInfo v => stack := stack.push v.induct
    | .recInfo v => stack := stack ++ v.all.toArray
    | _ => pure ()
  return seen

def main (args : List String) : IO UInt32 := do
  let [modArg, rootArg] := args
    | IO.eprintln "usage: lean --run scripts/lean/ReplayClosure.lean MODULE THEOREM"; return 2
  initSearchPath (← findSysroot)
  let root := rootArg.toName
  let t0 ← IO.monoMsNow
  let env ← importModules #[{ module := modArg.toName }] {}
  let m ← closure env root
  let mut kinds : Std.HashMap String Nat := {}
  let mut skipped := 0
  for (_, ci) in m.toList do
    let k := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    kinds := kinds.insert k (kinds.getD k 0 + 1)
    -- `replay` skips unsafe and partial constants; a safe proof cannot use them, and none is expected.
    if ci.isUnsafe || ci.isPartial then skipped := skipped + 1
  let axioms := (m.toList.filterMap fun (n, ci) => if ci matches .axiomInfo _ then some n.toString else none)
    |>.toArray.qsort (· < ·)
  IO.println s!"{root}: {m.size} constants, {skipped} unsafe or partial; \
    {(kinds.toList.toArray.qsort (fun a b => a.1 < b.1)).toList}; axioms {axioms.toList}"
  -- Adding `Quot` makes the kernel add `Quot.mk`, `Quot.lift` and `Quot.ind` too; they are compared afterwards.
  let m' := [``Quot.mk, ``Quot.lift, ``Quot.ind].foldl (init := m) fun acc n => acc.erase n
  let t1 ← IO.monoMsNow
  let kenv ← (← mkEmptyEnvironment).toKernelEnv.replay m'
  let t2 ← IO.monoMsNow
  let mut bad := 0
  for (n, ci) in m.toList do
    match kenv.find? n with
    | some ci' =>
      unless ci == ci' do
        bad := bad + 1
        IO.eprintln s!"differs after the replay: {n}"
    | none =>
      bad := bad + 1
      IO.eprintln s!"missing after the replay: {n}"
  if bad != 0 || skipped != 0 then
    IO.eprintln s!"REPLAY FAIL: {bad} constants missing or different, {skipped} unsafe or partial"
    return 1
  IO.println s!"REPLAY PASS: all {m.size} constants replayed into an empty kernel environment in \
    {(t2 - t1) / 1000} s (import and walk {(t1 - t0) / 1000} s), identical to the imported ones"
  return 0
