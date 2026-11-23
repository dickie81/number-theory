import Mathlib
open Lean Elab Command

/-- Write every constant of the environment that is not internal: name, kind, module, and the new name if it is a
deprecated alias (`!` if it is deprecated with no new name). -/
elab "#dump_names " path:str : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if n.isInternal then continue
    let k := match ci with
      | .thmInfo _ => "t" | .defnInfo _ => "d" | .axiomInfo _ => "a" | .opaqueInfo _ => "o"
      | .quotInfo _ => "q" | .inductInfo _ => "i" | .ctorInfo _ => "c" | .recInfo _ => "r"
    let m := match env.getModuleIdxFor? n with
      | some i => toString mods[i.toNat]!
      | none => "?"
    let dep := match Lean.Linter.deprecatedAttr.getParam? env n with
      | some e => match e.newName? with
        | some x => toString x
        | none => "!"
      | none => ""
    lines := lines.push s!"{n}\t{k}\t{m}\t{dep}"
  IO.FS.writeFile path.getString ("\n".intercalate lines.toList)

/-- Write the protected constants, a name a line: `N.a` that `open N` does not make `a` mean. -/
elab "#dump_protected " path:str : command => do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if n.isInternal then continue
    if isProtected env n then
      lines := lines.push (toString n)
  IO.FS.writeFile path.getString ("\n".intercalate lines.toList)
