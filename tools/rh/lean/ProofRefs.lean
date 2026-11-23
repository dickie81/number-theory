import Lean
open Lean

/-!
After bundles were compiled again: which bundles above them name, inside their terms, a constant of theirs that
is no longer what it was.

    lean --run ProofRefs.lean JOB.json

    JOB.json: {"watch": ["…/B/l001n033.olean", …], "before": ["…/B/l001n033.olean.before", "", …],
               "scan": ["…/B/l002n000.olean", …]}

A bundle above was checked by the kernel against what the `watch` files held then. This program finds the
bundles to check again, without importing anything: it reads each `.olean` as data. `before` gives, for each
file of `watch`, the file as it was (`bundle_build.py` keeps it), or `""` if there is none.

With the earlier file, the comparison is exact. A constant is `gone` if the file no longer holds it, and
`changed` if its type is another, or its value and it is no theorem (the kernel unfolds a definition; a proof
it only needs the statement of).

Without it, only one kind of change can be looked for, the one that made this program necessary. Lean lifts a
proof that stands inside a definition out of it, as a theorem `d._proof_1`, `d._proof_2`, …, and a term of a
later file that unfolds `d` names that theorem. Lean uses a lifted proof again for the same statement, and a
bundle compiled with `shareProofs` (`Bundle.lean`) did so across its files: a declaration then made no proof of
its own for a statement that an earlier file had, and numbered the rest from 1. Compiled again without
`shareProofs`, `d._proof_2` may be what `d._proof_1` was. That can only be if a proof of `d` with a lower number
has a statement that another lifted proof of the same bundle has too: the lifted proofs for which that holds
are `moved`. A lifted proof of a declaration of the file that the file does not hold is `gone`.

It prints a first line `{"gone": n, "changed": n, "moved": n}` for the `watch` files, and then, for each file of
`scan` that names such a constant, `{"olean": …, "gone": […], "changed": […], "moved": […]}`.
`bundle_recheck.py --bundle` then says whether the kernel still accepts the bundle.
-/

structure RefsJob where
  watch : Array String
  before : Array String
  scan : Array String
  /-- Other files that may hold what a `watch` file no longer holds: a file of the archive that failed in its
  bundle is compiled again in a bundle of its own, and its declarations are then there. -/
  elsewhere : Option (Array String)
deriving FromJson

/-- The number at the end of `d._proof_12`. -/
def liftedIndex (n : Name) : Option Nat :=
  match n with
  | .str _ s => if s.startsWith "_proof_" then (s.splitOn "_proof_")[1]!.toNat? else none
  | _ => none

/-- The lifted proofs of one `.olean` that may be numbered otherwise when its files share them. -/
def mayMove (data : ModuleData) : NameSet := Id.run do
  let mut count : Std.HashMap Expr Nat := {}
  let mut mine : Array (Name × Nat × Expr) := #[]
  for ci in data.constants do
    if let some k := liftedIndex ci.name then
      count := count.insert ci.type (count.getD ci.type 0 + 1)
      mine := mine.push (ci.name, k, ci.type)
  -- under each declaration, the least number of a lifted proof whose statement another one of the bundle has
  let mut first : NameMap Nat := {}
  for (n, k, t) in mine do
    if count.getD t 0 > 1 then
      let d := n.getPrefix
      if (first.find? d).all (k < ·) then
        first := first.insert d k
  let mut out : NameSet := {}
  for (n, k, _) in mine do
    if let some k0 := first.find? n.getPrefix then
      if k > k0 then
        out := out.insert n
  return out

/-- What one file no longer holds of what it held, and what it holds with another type or value. -/
def compare (was now : ModuleData) : NameSet × NameSet := Id.run do
  let mut held : Std.HashMap Name ConstantInfo := {}
  for ci in now.constants do
    held := held.insert ci.name ci
  let mut gone : NameSet := {}
  let mut changed : NameSet := {}
  for ci in was.constants do
    match held[ci.name]? with
    | none => gone := gone.insert ci.name
    | some cj =>
      let same := ci.type == cj.type && (match ci, cj with
        | .thmInfo _, .thmInfo _ => true
        | _, _ => ci.value? (allowOpaque := true) == cj.value? (allowOpaque := true))
      unless same do
        changed := changed.insert ci.name
  return (gone, changed)

structure Watched where
  /-- The constants of the `watch` files that have no earlier file. -/
  names : NameSet := {}
  gone : NameSet := {}
  changed : NameSet := {}
  moved : NameSet := {}

/-- The names of such constants in the terms of one `.olean`, as text, so that nothing of the file is kept. -/
def refsOf (w : Watched) (data : ModuleData) : Array String × Array String × Array String := Id.run do
  let mut gone : NameSet := {}
  let mut changed : NameSet := {}
  let mut moved : NameSet := {}
  for ci in data.constants do
    let mut used := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      used := used ++ v.getUsedConstants
    for u in used do
      if w.gone.contains u then
        gone := gone.insert u
      else if w.changed.contains u then
        changed := changed.insert u
      else if w.moved.contains u then
        moved := moved.insert u
      else if (liftedIndex u).isSome && !w.names.contains u && w.names.contains u.getPrefix then
        gone := gone.insert u
  let text (s : NameSet) : Array String := s.toArray.map (·.toString)
  return (text gone, text changed, text moved)

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | throw <| IO.userError "usage: ProofRefs.lean JOB.json"
  let job : RefsJob ← IO.ofExcept ((Json.parse (← IO.FS.readFile path)) >>= fromJson?)
  let mut w : Watched := {}
  for p in job.watch, b in job.before do
    let (data, _) ← readModuleData p
    if b.isEmpty then
      for n in data.constNames do
        w := { w with names := w.names.insert n }
      for n in mayMove data do
        w := { w with moved := w.moved.insert n }
    else
      let (was, _) ← readModuleData b
      let (gone, changed) := compare was data
      for n in gone do
        w := { w with gone := w.gone.insert n }
      for n in changed do
        w := { w with changed := w.changed.insert n }
  -- what is gone from one bundle and is in another now is not gone
  for p in job.elsewhere.getD #[] do
    if w.gone.isEmpty then break
    let (data, region) ← readModuleData p
    let here : NameSet := data.constNames.foldl (fun acc n => acc.insert n) {}
    let mut kept : NameSet := {}
    for n in w.gone do
      unless here.contains n do
        kept := kept.insert n
    w := { w with gone := kept }
    region.free
  IO.println (Json.mkObj [("gone", toJson w.gone.size), ("changed", toJson w.changed.size),
    ("moved", toJson w.moved.size)]).compress
  for p in job.scan do
    let (data, region) ← readModuleData p
    let (gone, changed, moved) := refsOf w data
    -- the text is made before the file is let go
    let line := (Json.mkObj [("olean", toJson p), ("gone", toJson gone), ("changed", toJson changed),
      ("moved", toJson moved)]).compress
    if gone.size + changed.size + moved.size > 0 then
      IO.println line
    region.free
  return 0
