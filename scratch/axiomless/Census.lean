import Lean

/-!
# A census of axioms

`lean --run scratch/axiomless/Census.lean OUT MODULE...` (under `lake env` for Mathlib) imports the modules and
writes to `OUT` one line for each constant of the environment:

    name <TAB> kind <TAB> module <TAB> full <TAB> stmt <TAB> direct <TAB> depth <TAB> internal

* `full`: the axioms the constant depends on, as `#print axioms` counts them (through types and values, proofs
  included), as a bit mask. The first lines of `OUT`, which start with `#axiom`, give the bit of each axiom.
* `stmt`: the axioms reached without entering the proof of a theorem: through the type of every constant, the value
  of every definition and opaque, and the constructors of every inductive type. For a theorem this is what its
  statement rests on.
* `direct`: the axioms that the constant's own type or value names.
* `depth`: the length of the longest chain of constants below it (types and values).
* `internal`: 1 for a name Lean generated or a private one.

With `--edges FILE` it also writes the graph: a line `i<TAB>j j j ...` for the constants (numbered as the lines of
`OUT`) that constant `i` names.
-/

open Lean

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .opaqueInfo _ => "opaque" | .recInfo _ => "recursor" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

/-- The constants `#print axioms` follows from `ci`; with `proofs := false`, a theorem's proof is left out. -/
def uses (ci : ConstantInfo) (proofs : Bool) : Array Name :=
  match ci with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => if proofs then v.type.getUsedConstants ++ v.value.getUsedConstants else v.type.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- A depth-first postorder of the graph: every constant after the constants it names, cycles aside. -/
def postorder (deps : Array (Array Nat)) : Array Nat := Id.run do
  let n := deps.size
  let mut seen : Array Bool := Array.replicate n false
  let mut order : Array Nat := Array.mkEmpty n
  let mut nodes : Array Nat := #[]
  let mut pos : Array Nat := #[]
  for root in [0:n] do
    if seen[root]! then continue
    seen := seen.set! root true
    nodes := nodes.push root
    pos := pos.push 0
    while !nodes.isEmpty do
      let c := nodes.back!
      let k := pos.back!
      let ds := deps[c]!
      if k < ds.size then
        pos := pos.set! (pos.size - 1) (k + 1)
        let d := ds[k]!
        if !seen[d]! then
          seen := seen.set! d true
          nodes := nodes.push d
          pos := pos.push 0
      else
        nodes := nodes.pop
        pos := pos.pop
        order := order.push c
  return order

/-- The union of `own` over everything reachable. Cycles (an inductive type and its constructors) need a second pass. -/
def closure (deps : Array (Array Nat)) (order : Array Nat) (own : Array Nat) : Array Nat := Id.run do
  let mut mask := own
  let mut changed := true
  while changed do
    changed := false
    for i in order do
      let mut m := mask[i]!
      for d in deps[i]! do
        m := m ||| mask[d]!
      if m != mask[i]! then
        mask := mask.set! i m
        changed := true
  return mask

def depths (deps : Array (Array Nat)) (order : Array Nat) : Array Nat := Id.run do
  let mut depth : Array Nat := Array.replicate deps.size 0
  for i in order do
    let mut m := 0
    for d in deps[i]! do
      m := max m depth[d]!
    depth := depth.set! i (m + 1)
  return depth

def main (args : List String) : IO Unit := do
  let (edgesFile, args) := match args with
    | "--edges" :: f :: rest => (some f, rest)
    | _ => (none, args)
  let out :: modules := args | throw (IO.userError "usage: Census.lean [--edges FILE] OUT MODULE...")
  initSearchPath (← findSysroot)
  let env ← importModules (modules.toArray.map fun m => { module := m.toName }) {} (loadExts := false)
  let mut names : Array Name := #[]
  let mut infos : Array ConstantInfo := #[]
  for (n, ci) in env.constants.toList do
    names := names.push n
    infos := infos.push ci
  let n := names.size
  let mut idx : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity n
  for i in [0:n] do
    idx := idx.insert names[i]! i
  -- the axioms, each with its bit
  let mut axioms : Array Nat := #[]
  for i in [0:n] do
    if infos[i]! matches .axiomInfo _ then axioms := axioms.push i
  let mut bit : Std.HashMap Nat Nat := {}
  for k in [0:axioms.size] do
    bit := bit.insert axioms[k]! k
  let toIdx (a : Array Name) : Array Nat := a.filterMap (idx[·]?)
  let mut full : Array (Array Nat) := Array.mkEmpty n
  let mut stmt : Array (Array Nat) := Array.mkEmpty n
  let mut own : Array Nat := Array.mkEmpty n
  let mut direct : Array Nat := Array.mkEmpty n
  for i in [0:n] do
    let f := toIdx (uses infos[i]! true)
    full := full.push f
    stmt := stmt.push (if infos[i]! matches .thmInfo _ then toIdx (uses infos[i]! false) else f)
    own := own.push (match bit[i]? with | some k => 1 <<< k | none => 0)
    direct := direct.push (f.foldl (fun m d => match bit[d]? with | some k => m ||| (1 <<< k) | none => m) 0)
  let order := postorder full
  let fullMask := closure full order own
  let stmtMask := closure stmt (postorder stmt) own
  let depth := depths full order
  let h ← IO.FS.Handle.mk out .write
  for k in [0:axioms.size] do
    h.putStrLn s!"#axiom\t{k}\t{names[axioms[k]!]!}"
  for i in [0:n] do
    let nm := names[i]!
    let modName := match env.getModuleIdxFor? nm with
      | some m => toString env.header.moduleNames[m.toNat]!
      | none => "?"
    let internal := if nm.isInternalDetail || isPrivateName nm then 1 else 0
    h.putStrLn s!"{nm}\t{kind infos[i]!}\t{modName}\t{fullMask[i]!}\t{stmtMask[i]!}\t{direct[i]!}\t{depth[i]!}\t{internal}"
  h.flush
  if let some f := edgesFile then
    let h ← IO.FS.Handle.mk f .write
    for i in [0:n] do
      h.putStrLn s!"{i}\t{" ".intercalate (full[i]!.toList.map toString)}"
    h.flush
  IO.println s!"{n} constants, {axioms.size} axioms"
