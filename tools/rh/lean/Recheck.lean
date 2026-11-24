import Lean
import Lean.Replay
open Lean

/-!
Check the declarations of one compiled bundle again, in the kernel, against what it imports as it is now.

    lean --tstack=400000 --run Recheck.lean JOB.json

    JOB.json: {"imports": ["Mathlib", "B.l001n000", …], "olean": "…/B/l004n033.olean"}

`bundle_build.py` compiles a bundle again after a repair and does not compile again the bundles built on it:
their proofs were checked against the statements that the bundle held before. If a repair changes a statement
(a name in it that was read as another constant), a proof above may no longer fit, and nothing has looked. This
program looks: it imports what the bundle imports, reads the bundle's `.olean` as data, and sends every constant
in it to the kernel again (`Lean.Environment.replay`), as `lean4checker` does for a module. Nothing is elaborated.

It prints one line of JSON: `{"ok": true, "constants": n, "known": k, "ms": t}`, where `known` counts the
constants that an import holds already with the same type (a theorem that two files state alike, a lemma that
Lean makes on demand), or `{"ok": false, "error": "…"}` with the kernel's message for the first constant it
refuses, or the name of a constant that an import holds with another type.
-/

structure RecheckJob where
  imports : Array String
  olean : String
deriving FromJson

def recheck (job : RecheckJob) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let imports : Array Import :=
    #[{ module := `Init }] ++ job.imports.map fun s => { module := s.toName }
  let env ← importModules imports {} 0
  let (data, _) ← readModuleData job.olean
  let mut fresh : Std.HashMap Name ConstantInfo := {}
  let mut known := 0
  for ci in data.constants do
    match env.find? ci.name with
    | some old =>
      if old.type == ci.type then
        known := known + 1
      else
        IO.println s!"\{\"ok\": false, \"error\": {(Json.str s!"{ci.name} is in an import with another type").compress}}"
        return 1
    | none => fresh := fresh.insert ci.name ci
  try
    let _ ← env.replay fresh
    let t1 ← IO.monoMsNow
    IO.println s!"\{\"ok\": true, \"constants\": {fresh.size}, \"known\": {known}, \"ms\": {t1 - t0}}"
    return 0
  catch e =>
    IO.println s!"\{\"ok\": false, \"error\": {(Json.str (toString e)).compress}}"
    return 1

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | throw <| IO.userError "usage: Recheck.lean JOB.json"
  let job : RecheckJob ← IO.ofExcept ((Json.parse (← IO.FS.readFile path)) >>= fromJson?)
  -- the main thread's stack is the system's; a dedicated thread has the stack that `--tstack` asks for
  let task ← IO.asTask (prio := .dedicated) (recheck job)
  match task.get with
  | .ok r => return r
  | .error e => throw e
