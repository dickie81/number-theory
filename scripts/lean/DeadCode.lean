import Lean
import Lean.Server.References

/-!
# The dead-code check's Lean side (`lake exe deadcode`)

`deadcode OURS ROOTS ALLOW MODULE...` imports the modules `MODULE...` (check files) and prints one JSON object. `OURS`
is a file of the library's own module names, one a line, `ROOTS` a file of the theorems that the check files print,
and `ALLOW` a file of the roots that are conditional on purpose (results under GRH, say).
It walks the constants that the roots use, through their types and values and through the names their sources cite
(the `.ilean` files that Lake writes, which record, for each use of a constant, the declaration it is in: a lemma that
`simp` applies by `rfl` appears in no proof term), transitively, within the library's own modules (the vendored
libraries, Mathlib and Lean cannot use the library's constants), and reports:

* `dead`: every constant of the library's modules that no root reaches, with its module, the lines of its source
  and the first line of its docstring, except those Lean generates (recursors, `noConfusion`, matchers,
  projections, equation lemmas, internal names, and whatever has no place in the sources) and the declarations of
  macros, syntax and elaborators, which no term mentions, and whether another of them uses it (`top` if none does:
  the end of a chain of unused declarations, which a review reads first);
* `roots`: for each root, its closed hypotheses (a binder of its statement, under `∀`, `∃` or `∧`, that is a
  proposition or an instance and mentions none of its variables, such as `RiemannHypothesis` or `[SieveCert.Grid]`),
  a root without closed hypotheses, or in `ALLOW`, whose proof uses it (`usedBy`), or none, and any other root whose
  proof uses it (`usedByAny`), or none.

`scripts/dead_code.py` runs it on the check files and decides what fails.
-/

open Lean

namespace DeadCode

/-- Whether `e` is a proposition: the head of its body, after any `∀`, is a constant whose type ends in `Prop`, or
`e` is itself a `∀` over a proposition. -/
partial def isPropType (env : Environment) (e : Expr) : Bool :=
  match e with
  | .forallE _ _ b _ => isPropType env b
  | .mdata _ b => isPropType env b
  | _ =>
    match e.getAppFn with
    | .const c _ =>
      match env.find? c with
      | some ci => ci.type.getForallBody.isProp
      | none => false
    | _ => false

/-- The closed hypotheses of a statement: binders under `∀`, `∃` and `∧` that are propositions or instances and
mention none of the statement's variables. -/
partial def closedHyps (env : Environment) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e with
  | .forallE _ d b bi =>
    let acc := if (bi.isInstImplicit || isPropType env d) && !d.hasLooseBVars then acc.push d else acc
    closedHyps env b acc
  | .mdata _ b => closedHyps env b acc
  | _ =>
    if e.isAppOfArity ``Exists 2 then
      match e.appArg! with
      | .lam _ _ b _ => closedHyps env b acc
      | _ => acc
    else if e.isAppOfArity ``And 2 then
      closedHyps env e.appArg! (closedHyps env e.appFn!.appArg! acc)
    else acc

/-- Whether Lean generates the constant, rather than the sources declaring it. A private constant is judged by the
name its source gives it. -/
def generated (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  (privateToUserName? n |>.getD n).isInternalDetail || isAuxRecursor env n || isNoConfusion env n || isRecCore env n
    || Meta.isMatcherCore env n || env.isProjectionFn n || ci matches .ctorInfo _ || ci matches .recInfo _
    || ci matches .quotInfo _
    || (match n with
        | .str _ s => s == "injEq" || s == "inj" || s == "sizeOf_spec" || s == "ext_iff" || s == "eq_def"
            || s.startsWith "eq_" || s.startsWith "_"
        | _ => false)

/-- Whether the constant belongs to Lean's meta level (a macro, a parser, an elaborator, a tactic): its type
mentions a constant of the namespace `Lean`. No term of the library mentions such a constant. -/
def isMeta (ci : ConstantInfo) : Bool :=
  ci.type.getUsedConstants.any fun c => c.getRoot == `Lean

/-- The lines `[start, stop]` of a constant's declaration in its source, if Lean recorded them. -/
def lines (env : Environment) (n : Name) : Option (Nat × Nat) :=
  let r := declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n
  r.map fun r => (r.range.pos.line, r.range.endPos.line)

/-- The first line of a constant's docstring, if it has one. -/
def doc (env : Environment) (n : Name) : Option String :=
  let d := docStringExt.find? (level := .server) env n <|> docStringExt.find? (level := .private) env n
  d.map fun s => ((s.splitOn "\n").head!.take 200).toString

structure Walk where
  /-- The constants reached. -/
  seen : Std.HashSet Name := {}
  /-- For a root, a source that uses it, and a root that uses it. -/
  usedBy : Std.HashMap Name Name := {}
  usedByAny : Std.HashMap Name Name := {}

/-- Walk from each source in turn, expanding each constant once, under the first source that reaches it. Every
use of a root `d` by a constant `c` is an edge from `c`, seen when `c` is expanded, under a source other than `d`
(else `d` would use itself), so `usedByAny` misses no root that another uses, and `usedBy`, for the sources walked
with `isSource`, none that a source uses. -/
def walk (env : Environment) (ours : Name → Bool) (srcRefs : Std.HashMap Name (Array Name))
    (rootSet : Std.HashSet Name) (sources : Array Name) (isSource : Name → Bool) (w : Walk := {}) : Walk := Id.run do
  let mut w := w
  for s in sources do
    let mut stack := #[s]
    while !stack.isEmpty do
      let c := stack.back!
      stack := stack.pop
      if w.seen.contains c then continue
      w := { w with seen := w.seen.insert c }
      let some ci := env.find? c | continue
      let mut deps := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
      if let .inductInfo v := ci then deps := deps ++ v.ctors.toArray
      deps := deps ++ srcRefs.getD c #[]
      for d in deps do
        if !ours d then continue
        if d != s && rootSet.contains d then
          if !w.usedByAny.contains d then w := { w with usedByAny := w.usedByAny.insert d s }
          if isSource s && !w.usedBy.contains d then w := { w with usedBy := w.usedBy.insert d s }
        if !w.seen.contains d then stack := stack.push d
  return w

def readLines (path : String) : IO (Array String) := do
  return (← IO.FS.lines path).filter (!·.isEmpty)

/-- The names that the sources of the modules `mods` cite, by the declaration that cites them, from their `.ilean`
files: an edge from each declaration to each constant of the library that its source names. `byStr` reads a name as
the `.ilean` writes it. -/
def sourceRefs (mods : Array Name) (byStr : Std.HashMap String Name) : IO (Std.HashMap Name (Array Name)) := do
  let mut out : Std.HashMap Name (Array Name) := {}
  for m in mods do
    let path := (← findOLean m).withExtension "ilean"
    unless ← path.pathExists do continue
    let ilean ← Lean.Server.Ilean.load path
    for (ident, info) in ilean.references do
      let .const _ target := ident | continue
      let some t := byStr[target]? | continue
      for u in info.usages do
        let some p := u.parentDecl? | continue
        let some parent := byStr[p]? | continue
        if parent != t then out := out.insert parent ((out.getD parent #[]).push t)
  return out

end DeadCode

open DeadCode in
def main (args : List String) : IO UInt32 := do
  let oursFile :: rootsFile :: allowFile :: mods := args
    | IO.eprintln "usage: deadcode OURS ROOTS ALLOW MODULE..."; return 2
  initSearchPath (← findSysroot)
  let oursMods : Std.HashSet Name := (← readLines oursFile).foldl (fun s m => s.insert m.toName) {}
  let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {} (trustLevel := 1024)
  let modNames := env.header.moduleNames
  let oursIdx : Array Bool := modNames.map oursMods.contains
  let ours (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some i => oursIdx[i.toNat]!
    | none => false
  let roots := (← readLines rootsFile).map (·.toName) |>.filter fun n => (env.find? n).isSome
  -- the library's constants by the strings that `.ilean` files write for them, and the names their sources cite
  let mut byStr : Std.HashMap String Name := {}
  for i in [:modNames.size] do
    if !oursIdx[i]! then continue
    for n in env.header.moduleData[i]!.constNames do
      byStr := byStr.insert n.toString n |>.insert (n.toString (escape := false)) n
      if let some u := privateToUserName? n then
        byStr := byStr.insert u.toString n
  let srcRefs ← sourceRefs (modNames.filter oursMods.contains) byStr
  -- every root, with its closed hypotheses
  let hyps := roots.map fun n => (n, closedHyps env (env.find? n).get!.type)
  let allow : Std.HashSet Name := (← readLines allowFile).foldl (fun s m => s.insert m.toName) {}
  let isSource (n : Name) := allow.contains n || (closedHyps env (env.find? n).get!.type).isEmpty
  let sources := roots.filter isSource
  let rootSet : Std.HashSet Name := roots.foldl (fun s n => s.insert n) {}
  -- the sources first, so that a use by a source is seen as one; then the other roots
  let w := walk env ours srcRefs rootSet sources isSource
  let w := walk env ours srcRefs rootSet (roots.filter (!isSource ·)) isSource w
  let live := w.seen
  -- the unreached constants that another unreached one uses
  let mut usedDead : Std.HashSet Name := {}
  for i in [:modNames.size] do
    if !oursIdx[i]! then continue
    for ci in env.header.moduleData[i]!.constants do
      if live.contains ci.name then continue
      let mut deps := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
      deps := deps ++ srcRefs.getD ci.name #[]
      for d in deps do
        -- a constant's own equation lemmas, matchers and auxiliary proofs (`d.eq_1`, `d._proof_1`) do not count
        if !d.isPrefixOf ci.name && ours d && !live.contains d then usedDead := usedDead.insert d
  -- the constants of the library's modules that no root reaches, and for each module its declarations, the live ones
  -- among them and its macros, syntax and elaborators (a module with none live goes as a whole, unless it has some)
  let mut dead : Array Json := #[]
  let mut stats : Array (String × Json) := #[]
  for i in [:modNames.size] do
    if !oursIdx[i]! then continue
    let md := env.header.moduleData[i]!
    let mut total := 0
    let mut alive := 0
    let mut metas := 0
    for ci in md.constants do
      let n := ci.name
      if generated env n ci || (lines env n).isNone then continue
      if isMeta ci then metas := metas + 1; continue
      total := total + 1
      if live.contains n then alive := alive + 1
    stats := stats.push (modNames[i]!.toString, toJson #[total, alive, metas])
    for ci in md.constants do
      let n := ci.name
      if live.contains n || generated env n ci || isMeta ci then continue
      let some (start, stop) := lines env n | continue
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
        | .inductInfo _ => "inductive" | _ => "other"
      dead := dead.push <| Json.mkObj [("name", toJson (privateToUserName? n |>.getD n).toString),
        ("private", toJson (isPrivateName n)), ("module", toJson modNames[i]!.toString),
        ("kind", toJson kind), ("start", toJson start), ("stop", toJson stop), ("doc", toJson (doc env n)),
        ("top", toJson (!usedDead.contains n))]
  let rootsJson := hyps.map fun (n, hs) => Json.mkObj [("name", toJson n.toString),
    ("module", toJson ((env.getModuleIdxFor? n).map (fun i => modNames[i.toNat]!.toString))),
    ("closed", toJson (hs.map toString)), ("usedBy", toJson ((w.usedBy.get? n).map (·.toString))),
    ("usedByAny", toJson ((w.usedByAny.get? n).map (·.toString))), ("doc", toJson (doc env n))]
  let oursHere := (modNames.filter oursMods.contains).map (·.toString)
  IO.println (Json.mkObj [("modules", toJson (mods.toArray)), ("ours", toJson oursHere), ("roots", Json.arr rootsJson),
    ("dead", Json.arr dead), ("live", toJson live.size), ("stats", Json.mkObj stats.toList)]).compress
  return 0
