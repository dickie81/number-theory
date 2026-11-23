import Lean
open Lean

/-!
The key of every instance that the bundles of a build declare.

    lean --run DumpInstKeys.lean MODULES.txt OUT.tsv

MODULES.txt names the modules to import, a line each (`Mathlib`, then the bundles `B.l001n000`, …). OUT.tsv gets
a line for each instance of a bundle: its name and its key in the table of instances, as text. Two instances
with one key fit the same goals, and Lean tries the one imported last first: `bundle_build.py` needs to know
which those are (`inst_orders`). `Bundle.lean` writes the same keys beside each file's instances when it
compiles a bundle; this program gives them for the bundles made before it did.
-/

unsafe def main (args : List String) : IO UInt32 := do
  let names := (← IO.FS.lines args[0]!).filter (· != "")
  let imports : Array Import := #[{ module := `Init }] ++ names.map fun s => { module := s.toName }
  enableInitializersExecution
  let env ← importModules imports {} 0 (loadExts := true)
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for (n, e) in (Meta.instanceExtension.getState env).instanceNames do
    let ours := match env.getModuleIdxFor? n with
      | some i => mods[i.toNat]!.getRoot == `B
      | none => false
    if ours then
      out := out.push s!"{n}\t{" ".intercalate (e.keys.toList.map fun k => toString (format k))}"
  IO.FS.writeFile args[1]! ("\n".intercalate out.toList ++ "\n")
  IO.println s!"{out.size} instances of {names.size} modules"
  (← IO.getStdout).flush
  IO.Process.exit 0
