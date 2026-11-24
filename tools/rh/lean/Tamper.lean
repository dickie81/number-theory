import Lean
open Lean

/-!
Write a copy of a compiled file with one constant changed, for the tests of `ReplayAll.lean`.

    lean --run Tamper.lean IN.olean OUT.olean HOW A B

    proof      the theorem A gets the proof of the theorem B
    statement  the theorem A gets the statement of the theorem B, and keeps its proof
    body       the definition A gets the body of the definition B
    axiom      the theorem A becomes an axiom with its statement
    gone       the proof of the theorem A becomes a constant that does not exist (what `Slim.lean` writes)

A check of the kernel that is worth anything refuses each of the first three and the last, and the fourth is an
axiom in the build. `replay_test.py` runs them.
-/

unsafe def main (args : List String) : IO UInt32 := do
  let [src, dst, how, a, b] := args
    | throw <| IO.userError "usage: Tamper.lean IN.olean OUT.olean proof|statement|body|axiom|gone A B"
  let (data, _) ← readModuleData src
  let find (n : String) : IO ConstantInfo :=
    match data.constants.find? (fun c => toString c.name == n) with
    | some c => pure c
    | none => throw <| IO.userError s!"no constant {n} in {src}"
  let ca ← find a
  let cb ← find b
  let changed : ConstantInfo ← match how, ca, cb with
    | "proof", .thmInfo v, .thmInfo w => pure (.thmInfo { v with value := w.value })
    | "statement", .thmInfo v, .thmInfo w => pure (.thmInfo { v with type := w.type })
    | "body", .defnInfo v, .defnInfo w => pure (.defnInfo { v with value := w.value })
    | "axiom", .thmInfo v, _ =>
      pure (.axiomInfo { name := v.name, levelParams := v.levelParams, type := v.type, isUnsafe := false })
    | "gone", .thmInfo v, _ => pure (.thmInfo { v with value := .const (`_slim_ ++ v.name) [] })
    | _, _, _ => throw <| IO.userError s!"{how} does not fit {a} and {b}"
  saveModuleData dst `Tampered { data with constants := data.constants.map fun c => if c.name == ca.name then changed else c }
  return 0
