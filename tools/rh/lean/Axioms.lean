import Mathlib
open Lean

/-!
For every bundle of a build: the axioms that it declares, and the declarations that name `sorryAx` or an axiom
other than the three that Mathlib rests on.

    lean --run Axioms.lean JOB.json

    JOB.json: {"files": ["…/olean/B/l001n000.olean", …]}

`bundle_check.py` walks what one theorem rests on. This looks at everything that was compiled, bundle by bundle,
without importing a bundle: each `.olean` is read as data. A declaration whose elaboration failed is declared
with `sorryAx` in its place, and one that the kernel refused is kept as an axiom; a proof by `native_decide`
names `Lean.ofReduceBool`. If no bundle has any of these, then every theorem of the build, whatever it uses of
the build, rests on `propext`, `Classical.choice` and `Quot.sound` alone, provided the kernel has accepted every
bundle against the others (`bundle_recheck.py`).

The axioms of Lean and Mathlib are read from the environment of this program, which imports Mathlib. It prints a
line of JSON for each file with something to report, `{"olean": …, "axioms": […], "sorry": […], "other": […]}`
(the names that are declared as axioms, that name `sorryAx`, that name another axiom), and at the end
`{"files": n, "constants": n, "bad": n, "known": […]}` with the axioms of the environment.
-/

structure AxiomsJob where
  files : Array String
deriving FromJson

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | throw <| IO.userError "usage: Axioms.lean JOB.json"
  let job : AxiomsJob ← IO.ofExcept ((Json.parse (← IO.FS.readFile path)) >>= fromJson?)
  let env ← importModules #[{ module := `Init }, { module := `Mathlib }] {} 0
  let standard : NameSet := [``propext, ``Classical.choice, ``Quot.sound].foldl (fun s n => s.insert n) {}
  let mut known : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    if ci matches .axiomInfo _ then
      known := known.insert n
  let other := known.toArray.filter fun n => !standard.contains n
  let otherSet : NameSet := other.foldl (fun s n => s.insert n) {}
  let mut total := 0
  let mut bad := 0
  for p in job.files do
    let (data, region) ← readModuleData p
    let mut axioms : Array String := #[]
    let mut sorried : Array String := #[]
    let mut others : Array String := #[]
    for ci in data.constants do
      total := total + 1
      if ci matches .axiomInfo _ then
        axioms := axioms.push ci.name.toString
      let mut used := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        used := used ++ v.getUsedConstants
      if used.contains ``sorryAx then
        sorried := sorried.push ci.name.toString
      else if used.any otherSet.contains then
        others := others.push ci.name.toString
    if axioms.size + sorried.size + others.size > 0 then
      bad := bad + 1
      IO.println (Json.mkObj [("olean", toJson p), ("axioms", toJson axioms), ("sorry", toJson sorried),
        ("other", toJson others)]).compress
    region.free
  IO.println (Json.mkObj [("files", toJson job.files.size), ("constants", toJson total), ("bad", toJson bad),
    ("known", toJson (known.toArray.map (·.toString)))]).compress
  (← IO.getStdout).flush
  IO.Process.exit 0
