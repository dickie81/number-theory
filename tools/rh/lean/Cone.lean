import Lean
open Lean Elab Command

/-!
`#cone root "FILE"`: what a constant rests on, read from the environment and not from the source.

It writes to FILE the constants that `root` reaches through types and values and that are not Mathlib's (their
module is a bundle `B.*`, or the current file), and logs the axioms among them (a declaration that the kernel
refused is kept as one), and the constants among them that name `sorryAx`: the declarations whose elaboration
failed. A constant that is named and is not in the environment is reported too: a bundle that was compiled again
must still hold what the bundles above it use. This is the exact list of what the theorem needs; the map of
`decl_map.py` is an estimate of it.

The axioms are read from this walk. Lean's own answer (`collectAxioms`, what `#print axioms` prints) is logged
beside it and is not to be relied on after a repair: Lean records in each `.olean` the axioms that each
declaration depended on when its file was compiled, and a bundle above one that was compiled again still holds
the earlier record. Mathlib's constants are not walked; its record is the one Mathlib was built with.
-/

elab "#cone " root:ident path:str : command => do
  let env ← getEnv
  let rootName := root.getId
  unless env.contains rootName do
    throwError "{rootName} is not in the environment"
  let mods := env.header.moduleNames
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[rootName]
  let mut out : Array String := #[]
  let mut outside : Nat := 0
  let mut sorried : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut ownAxioms : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n
      | missing := missing.push n
        continue
    let ours := match env.getModuleIdxFor? n with
      | some i => mods[i.toNat]!.getRoot == `B
      | none => true
    unless ours do
      outside := outside + 1
      continue
    let kind := match ci with
      | .thmInfo _ => "t" | .defnInfo _ => "d" | .axiomInfo _ => "a" | .opaqueInfo _ => "o"
      | .quotInfo _ => "q" | .inductInfo _ => "i" | .ctorInfo _ => "c" | .recInfo _ => "r"
    let mut used := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      used := used ++ v.getUsedConstants
    -- a declaration whose proof failed is declared with `sorryAx` in its place
    if used.contains ``sorryAx then
      sorried := sorried.push n
    if kind == "a" then
      ownAxioms := ownAxioms.push n
    out := out.push s!"{kind}\t{n}"
    stack := stack ++ used
    match ci with
    | .inductInfo v => stack := stack ++ v.ctors.toArray
    | .ctorInfo v => stack := stack.push v.induct
    | .recInfo v => stack := stack ++ v.all.toArray
    | _ => pure ()
  IO.FS.writeFile path.getString ("\n".intercalate out.toList)
  let axioms ← liftCoreM (collectAxioms rootName)
  logInfo m!"cone of {rootName}: {out.size} constants of the archive, {outside} of Mathlib; axioms among the archive's constants: {ownAxioms.size} {ownAxioms.toList.take 40}; declared with sorry: {sorried.size} {sorried.toList.take 40}; named and not in the environment: {missing.size} {missing.toList.take 20}; Lean's record of the axioms (out of date after a repair): {axioms.toList}"
