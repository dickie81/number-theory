import Lean

/-!
# A fingerprint of a theorem's dependencies

`lean --run scripts/lean/ClosureFingerprint.lean MODULE THEOREM` (under `lake env`; by default `LinnikCGLDensity` and
`LinnikCGLDensity.cglDensity`) imports `MODULE` and prints one line for each constant that `THEOREM`'s type and value
mention, transitively, as `lib/check/CheckAll.lean`'s walk finds them: its name, its kind, its universe parameters,
and the structural hashes of its type and of its value. The lines are sorted.

Two builds whose fingerprints are equal have the same constants with the same terms, up to the hash. A change that
leaves every line as it was, such as an edit to a docstring or a comment, which the `.olean` keeps outside the
constants, leaves the theorem's kernel checks (`scripts/kernel_check.sh`) as they were, without running them again.
Save the output before the change and compare it with `cmp` after.
-/

open Lean

def kind : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor"
  | .opaqueInfo _ => "opaque" | .recInfo _ => "rec" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let modName := (args[0]?.getD "LinnikCGLDensity").toName
  let root := (args[1]?.getD "LinnikCGLDensity.cglDensity").toName
  let env ← importModules #[{ module := modName }] {}
  unless env.contains root do throw <| IO.userError s!"{root} is not in {modName}"
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    stack := stack ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then stack := stack ++ v.getUsedConstants
    if let .inductInfo v := ci then stack := stack ++ v.ctors.toArray
  let mut rows : Array String := #[]
  for c in seen do
    if let some ci := env.find? c then
      let vh := (ci.value? (allowOpaque := true)).map (·.hash) |>.getD 0
      rows := rows.push s!"{c} {kind ci} {ci.levelParams} {ci.type.hash} {vh}"
  let out ← IO.getStdout
  for r in rows.qsort (· < ·) do out.putStrLn r
  out.flush
