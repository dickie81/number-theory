import Lean
open Lean Elab Command

/-!
`#export_cone "OUT" "NOTWIN" "RENAMED" "TAKEN" root₁ root₂ …`: write what some constants rest on, as terms of the
kernel, for another version of Lean to check (`Replay.lean`).

The other environment has a newer Mathlib. `fp_compare.py` says which constants of this Mathlib have a twin there:
the same term over the same constants all the way down. A constant with a twin is not written; a mention of it is
written as the twin's name. Everything else that the roots reach is written: the constants of the archive, under
their own names, and the constants of this Mathlib with no twin, under `MathlibOld.` and their name, with their
proofs. So the file holds exactly what the other kernel needs to check the roots again, and nothing is elaborated
there: a proof is carried as the term that this kernel checked.

* NOTWIN: the names of this Mathlib's constants with no twin, one a line.
* RENAMED: lines `old<TAB>new`, the constants whose twin has another name.
* TAKEN: the names in use in the other environment, one a line (the first field of each line); a constant of the
  archive whose name is taken goes under `MathlibOld.` too.

The format is lines. Names, universe levels and terms are numbered from 0 in the order of their lines, each kind
on its own count; name 0 is the anonymous name and level 0 is zero.

    N p s | I p k | X s        a name: parent and string, parent and number, or the constant that prints as s
    LS a | LM a b | LI a b | LP n      a level
    V i | S l | C n l… | A f a | L t b | P t b | T t v b | J n i e | Ln k | Ls s     a term
    D …                        a constant (see `Replay.lean`)

Binder names and annotations are dropped: the kernel does not read them.
-/

namespace Xp

structure Cfg where
  noTwin : Std.HashSet String
  renamed : Std.HashMap String String
  taken : Std.HashSet String
  env : Environment
  mods : Array Name
  out : IO.FS.Handle

inductive Fate where
  /-- Not written; mentioned under this name. -/
  | leaf (n : Name)
  /-- Not written; mentioned as the constant of the other environment that prints as this. -/
  | twin (s : String)
  /-- Written, under this name. -/
  | copy (n : Name)

structure St where
  names : Std.HashMap Name Nat := (∅ : Std.HashMap Name Nat).insert .anonymous 0
  strNames : Std.HashMap String Nat := {}
  nNames : Nat := 1
  levels : Std.HashMap Level Nat := (∅ : Std.HashMap Level Nat).insert .zero 0
  nLevels : Nat := 1
  exprs : Std.HashMap Expr Nat := {}
  nExprs : Nat := 0
  fate : Std.HashMap Name Fate := {}
  todo : Array Name := #[]
  roots : NameSet := {}

abbrev M := ReaderT Cfg <| StateRefT St IO

def esc (s : String) : String :=
  ((s.replace "\\" "\\\\").replace "\n" "\\n").replace " " "\\s"

def emit (s : String) : M Unit := do (← read).out.putStrLn s

partial def nameId (n : Name) : M Nat := do
  if let some i := (← get).names[n]? then return i
  match n with
  | .anonymous => return 0
  | .str p s => emit s!"N {← nameId p} {esc s}"
  | .num p k => emit s!"I {← nameId p} {k}"
  let i := (← get).nNames
  modify fun st => { st with names := st.names.insert n i, nNames := i + 1 }
  return i

def strNameId (s : String) : M Nat := do
  if let some i := (← get).strNames[s]? then return i
  emit s!"X {esc s}"
  let i := (← get).nNames
  modify fun st => { st with strNames := st.strNames.insert s i, nNames := i + 1 }
  return i

partial def levelId (l : Level) : M Nat := do
  if let some i := (← get).levels[l]? then return i
  match l with
  | .zero => return 0
  | .succ a => emit s!"LS {← levelId a}"
  | .max a b => emit s!"LM {← levelId a} {← levelId b}"
  | .imax a b => emit s!"LI {← levelId a} {← levelId b}"
  | .param n => emit s!"LP {← nameId n}"
  | .mvar _ => throw <| IO.userError "a level metavariable"
  let i := (← get).nLevels
  modify fun st => { st with levels := st.levels.insert l i, nLevels := i + 1 }
  return i

/-- What becomes of a constant. A constant that is to be written is queued the first time it is met. -/
def fateOf (n : Name) : M Fate := do
  if let some f := (← get).fate[n]? then return f
  let cfg ← read
  let s := toString n
  let ours := match cfg.env.getModuleIdxFor? n with
    | some i => cfg.mods[i.toNat]!.getRoot == `B
    | none => true
  let isRoot := (← get).roots.contains n
  let f : Fate :=
    if ours then .copy (if cfg.taken.contains s then `MathlibOld ++ n else n)
    else if isRoot || cfg.noTwin.contains s then .copy (`MathlibOld ++ n)
    else match cfg.renamed[s]? with
      | some t => .twin t
      | none => .leaf n
  modify fun st => { st with fate := st.fate.insert n f }
  if f matches .copy _ then
    modify fun st => { st with todo := st.todo.push n }
  return f

def constId (n : Name) : M Nat := do
  match ← fateOf n with
  | .leaf m => nameId m
  | .copy m => nameId m
  | .twin s => strNameId s

partial def exprId (e : Expr) : M Nat := do
  if let .mdata _ b := e then return ← exprId b
  if let some i := (← get).exprs[e]? then return i
  match e with
  | .bvar i => emit s!"V {i}"
  | .sort l => emit s!"S {← levelId l}"
  | .const n ls =>
    let mut s := s!"C {← constId n}"
    for l in ls do
      s := s ++ s!" {← levelId l}"
    emit s
  | .app f a =>
    let fi ← exprId f
    let ai ← exprId a
    emit s!"A {fi} {ai}"
  | .lam _ t b _ =>
    let ti ← exprId t
    let bi ← exprId b
    emit s!"L {ti} {bi}"
  | .forallE _ t b _ =>
    let ti ← exprId t
    let bi ← exprId b
    emit s!"P {ti} {bi}"
  | .letE _ t v b _ =>
    let ti ← exprId t
    let vi ← exprId v
    let bi ← exprId b
    emit s!"T {ti} {vi} {bi}"
  | .proj s i b =>
    let si ← constId s
    let bi ← exprId b
    emit s!"J {si} {i} {bi}"
  | .lit (.natVal k) => emit s!"Ln {k}"
  | .lit (.strVal s) => emit s!"Ls {esc s}"
  | _ => throw <| IO.userError "a free variable or a metavariable in a constant"
  let i := (← get).nExprs
  modify fun st => { st with exprs := st.exprs.insert e i, nExprs := i + 1 }
  return i

def ids (xs : List Nat) : String := " ".intercalate (toString xs.length :: xs.map toString)

def bit (b : Bool) : String := if b then "1" else "0"

/-- Write one constant. The names it gives are the names in the other environment. -/
def writeConst (n : Name) : M String := do
  let some ci := (← read).env.find? n | throw <| IO.userError s!"no constant {n}"
  let me ← constId n
  let lps ← ci.levelParams.mapM nameId
  let ty ← exprId ci.type
  let head := s!"{me} {ids lps} {ty}"
  match ci with
  | .defnInfo v =>
    let val ← exprId v.value
    let hint := match v.hints with
      | .opaque => "o"
      | .abbrev => "a"
      | .regular h => s!"r{h}"
    let safety := match v.safety with
      | .unsafe => "u"
      | .safe => "s"
      | .partial => "p"
    emit s!"D d {head} {val} {hint} {safety} {ids (← v.all.mapM constId)}"
    return "d"
  | .thmInfo v =>
    let val ← exprId v.value
    emit s!"D t {head} {val} {ids (← v.all.mapM constId)}"
    return "t"
  | .axiomInfo v =>
    emit s!"D a {head} {bit v.isUnsafe}"
    return "a"
  | .opaqueInfo v =>
    let val ← exprId v.value
    emit s!"D o {head} {val} {bit v.isUnsafe} {ids (← v.all.mapM constId)}"
    return "o"
  | .quotInfo _ => return "q"
  | .inductInfo v =>
    emit s!"D i {head} {v.numParams} {v.numIndices} {ids (← v.all.mapM constId)} {ids (← v.ctors.mapM constId)} {v.numNested} {bit v.isRec} {bit v.isUnsafe} {bit v.isReflexive}"
    return "i"
  | .ctorInfo v =>
    emit s!"D c {head} {← constId v.induct} {v.cidx} {v.numParams} {v.numFields} {bit v.isUnsafe}"
    return "c"
  | .recInfo v =>
    let mut rules := s!"{v.rules.length}"
    for r in v.rules do
      rules := rules ++ s!" {← constId r.ctor} {r.nfields} {← exprId r.rhs}"
    emit s!"D r {head} {ids (← v.all.mapM constId)} {v.numParams} {v.numIndices} {v.numMotives} {v.numMinors} {rules} {bit v.k} {bit v.isUnsafe}"
    return "r"

partial def run (roots : Array Name) : M (Std.HashMap String Nat) := do
  modify fun st => { st with roots := roots.foldl (·.insert ·) {} }
  for r in roots do
    let _ ← fateOf r
  let mut counts : Std.HashMap String Nat := {}
  let mut done : NameSet := {}
  repeat
    let st ← get
    if st.todo.isEmpty then break
    let n := st.todo.back!
    set { st with todo := st.todo.pop }
    if done.contains n then continue
    done := done.insert n
    let kind ← writeConst n
    let cfg ← read
    let ours := match cfg.env.getModuleIdxFor? n with
      | some i => cfg.mods[i.toNat]!.getRoot == `B
      | none => true
    let key := (if ours then "archive " else "Mathlib ") ++ kind
    counts := counts.insert key (counts.getD key 0 + 1)
  return counts

def firstField (line : String) : String := (line.splitOn "\t").head!

end Xp

open Xp in
elab "#export_cone " out:str noTwin:str renamed:str taken:str roots:ident* : command => do
  let env ← getEnv
  let rootNames := roots.map (·.getId)
  for r in rootNames do
    unless env.contains r do
      throwError "{r} is not in the environment"
  let mut nt : Std.HashSet String := {}
  for l in ← IO.FS.lines noTwin.getString do
    nt := nt.insert l
  let mut rn : Std.HashMap String String := {}
  for l in ← IO.FS.lines renamed.getString do
    match l.splitOn "\t" with
    | [a, b] => rn := rn.insert a b
    | _ => pure ()
  let mut tk : Std.HashSet String := {}
  for l in ← IO.FS.lines taken.getString do
    tk := tk.insert (firstField l)
  let h ← IO.FS.Handle.mk out.getString .write
  let cfg : Cfg := { noTwin := nt, renamed := rn, taken := tk, env, mods := env.header.moduleNames, out := h }
  let (counts, st) ← ((run rootNames).run cfg).run {}
  h.flush
  logInfo m!"wrote {st.nNames} names, {st.nLevels} levels, {st.nExprs} terms; constants: {counts.toList}"
