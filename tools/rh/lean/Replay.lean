import Lean
open Lean Elab Command

/-!
`#replay "FILE"`: read the constants that `Export.lean` wrote, and add them to the environment through the kernel.

Nothing is elaborated: each constant arrives as a term, and `Lean.Kernel.Environment.replay` sends each one to the
kernel of this version of Lean, which checks it as it checks any declaration. Constructors and recursors are not
sent: the kernel makes them from the inductive type, and `replay` checks that they are the ones in the file.

The command refuses a file that holds an axiom: what is carried over must be proved.

The lines of a constant, after `D` and its kind (names are numbers of the file's names, `k x…` is a list of length
`k`):

    d name lps type value hint safety all        t name lps type value all
    o name lps type value unsafe all             a name lps type unsafe
    i name lps type params indices all ctors nested rec unsafe reflexive
    c name lps type induct cidx params fields unsafe
    r name lps type all params indices motives minors k (ctor nfields rhs)… kFlag unsafe
-/

namespace Rp

def unesc (s : String) : String := Id.run do
  let mut out := ""
  let mut escaped := false
  for c in s.toList do
    if escaped then
      out := out.push (if c == 'n' then '\n' else if c == 's' then ' ' else c)
      escaped := false
    else if c == '\\' then
      escaped := true
    else
      out := out.push c
  return out

structure St where
  names : Array Name := #[.anonymous]
  levels : Array Level := #[.zero]
  exprs : Array Expr := #[]
  consts : Std.HashMap Name ConstantInfo := {}
  byString : Std.HashMap String Name := {}
  env : Environment

abbrev M := StateRefT St IO

/-- A cursor over the fields of a line. -/
structure Cur where
  ws : Array String
  i : Nat := 0

def Cur.nat (c : Cur) : Nat × Cur := (c.ws[c.i]!.toNat!, { c with i := c.i + 1 })

def Cur.str (c : Cur) : String × Cur := (c.ws[c.i]!, { c with i := c.i + 1 })

def Cur.nats (c : Cur) : List Nat × Cur := Id.run do
  let (k, c) := c.nat
  let mut c := c
  let mut out := #[]
  for _ in [0:k] do
    let (x, c') := c.nat
    out := out.push x
    c := c'
  return (out.toList, c)

def twin (s : String) : M Name := do
  if (← get).byString.isEmpty then
    let env := (← get).env
    let mut m : Std.HashMap String Name := {}
    for (n, _) in env.constants.map₁.toList do
      m := m.insert (toString n) n
    modify fun st => { st with byString := m }
  match (← get).byString[s]? with
  | some n => return n
  | none => throw <| IO.userError s!"the file names the constant {s}, which this environment does not have"

def line (l : String) : M Unit := do
  let ws := (l.splitOn " ").toArray
  let st ← get
  let nm (i : Nat) : Name := st.names[i]!
  let ex (i : Nat) : Expr := st.exprs[i]!
  let lv (i : Nat) : Level := st.levels[i]!
  let n (i : Nat) : Nat := ws[i]!.toNat!
  let pushE (e : Expr) : M Unit := modify fun st => { st with exprs := st.exprs.push e }
  let pushL (u : Level) : M Unit := modify fun st => { st with levels := st.levels.push u }
  let pushN (x : Name) : M Unit := modify fun st => { st with names := st.names.push x }
  match ws[0]! with
  | "N" => pushN (.str (nm (n 1)) (unesc ws[2]!))
  | "I" => pushN (.num (nm (n 1)) (n 2))
  | "X" => pushN (← twin (unesc ws[1]!))
  | "LS" => pushL (.succ (lv (n 1)))
  | "LM" => pushL (.max (lv (n 1)) (lv (n 2)))
  | "LI" => pushL (.imax (lv (n 1)) (lv (n 2)))
  | "LP" => pushL (.param (nm (n 1)))
  | "V" => pushE (.bvar (n 1))
  | "S" => pushE (.sort (lv (n 1)))
  | "C" => pushE (.const (nm (n 1)) ((ws.extract 2 ws.size).toList.map fun w => lv w.toNat!))
  | "A" => pushE (.app (ex (n 1)) (ex (n 2)))
  | "L" => pushE (.lam `x (ex (n 1)) (ex (n 2)) .default)
  | "P" => pushE (.forallE `x (ex (n 1)) (ex (n 2)) .default)
  | "T" => pushE (.letE `x (ex (n 1)) (ex (n 2)) (ex (n 3)) false)
  | "J" => pushE (.proj (nm (n 1)) (n 2) (ex (n 3)))
  | "Ln" => pushE (.lit (.natVal (n 1)))
  | "Ls" => pushE (.lit (.strVal (unesc (ws.getD 1 ""))))
  | "D" =>
    let kind := ws[1]!
    let c : Cur := { ws, i := 2 }
    let (me, c) := c.nat
    let (lps, c) := c.nats
    let (ty, c) := c.nat
    let name := nm me
    let levelParams := lps.map nm
    let type := ex ty
    let names (xs : List Nat) : List Name := xs.map nm
    let ci : ConstantInfo ← match kind with
      | "d" =>
        let (v, c) := c.nat
        let (hint, c) := c.str
        let (safety, c) := c.str
        let (all, _) := c.nats
        let hints : ReducibilityHints :=
          if hint == "o" then .opaque else if hint == "a" then .abbrev
          else .regular (hint.drop 1).toNat!.toUInt32
        let safety : DefinitionSafety :=
          if safety == "u" then .unsafe else if safety == "p" then .partial else .safe
        pure <| .defnInfo { name, levelParams, type, value := ex v, hints, safety, all := names all }
      | "t" =>
        let (v, c) := c.nat
        let (all, _) := c.nats
        pure <| .thmInfo { name, levelParams, type, value := ex v, all := names all }
      | "o" =>
        let (v, c) := c.nat
        let (u, c) := c.nat
        let (all, _) := c.nats
        pure <| .opaqueInfo { name, levelParams, type, value := ex v, isUnsafe := u == 1, all := names all }
      | "i" =>
        let (numParams, c) := c.nat
        let (numIndices, c) := c.nat
        let (all, c) := c.nats
        let (ctors, c) := c.nats
        let (numNested, c) := c.nat
        let (isRec, c) := c.nat
        let (isUnsafe, c) := c.nat
        let (isReflexive, _) := c.nat
        pure <| .inductInfo { name, levelParams, type, numParams, numIndices, all := names all, ctors := names ctors,
                              numNested, isRec := isRec == 1, isUnsafe := isUnsafe == 1,
                              isReflexive := isReflexive == 1 }
      | "c" =>
        let (induct, c) := c.nat
        let (cidx, c) := c.nat
        let (numParams, c) := c.nat
        let (numFields, c) := c.nat
        let (isUnsafe, _) := c.nat
        pure <| .ctorInfo { name, levelParams, type, induct := nm induct, cidx, numParams, numFields,
                            isUnsafe := isUnsafe == 1 }
      | "r" =>
        let (all, c) := c.nats
        let (numParams, c) := c.nat
        let (numIndices, c) := c.nat
        let (numMotives, c) := c.nat
        let (numMinors, c) := c.nat
        let (k, c) := c.nat
        let mut cur := c
        let mut rules : Array RecursorRule := #[]
        for _ in [0:k] do
          let (ctor, c1) := cur.nat
          let (nfields, c2) := c1.nat
          let (rhs, c3) := c2.nat
          rules := rules.push { ctor := nm ctor, nfields, rhs := ex rhs }
          cur := c3
        let (kFlag, c4) := cur.nat
        let (isUnsafe, _) := c4.nat
        pure <| .recInfo { name, levelParams, type, all := names all, numParams, numIndices, numMotives, numMinors,
                           rules := rules.toList, k := kFlag == 1, isUnsafe := isUnsafe == 1 }
      | "a" => throw <| IO.userError s!"the file holds an axiom, {name}: refused"
      | k => throw <| IO.userError s!"unknown kind of constant: {k}"
    modify fun st => { st with consts := st.consts.insert name ci }
  | "" => pure ()
  | op => throw <| IO.userError s!"unknown line: {op}"

partial def readAll (h : IO.FS.Handle) : M Unit := do
  let l ← h.getLine
  if l.isEmpty then return
  line (l.splitOn "\n").head!
  readAll h

end Rp

open Rp in
elab "#replay " path:str : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk path.getString .read
  let ((), st) ← (readAll h).run { env }
  let t0 ← IO.monoMsNow
  let kenv ← env.toKernelEnv.replay st.consts
  let t1 ← IO.monoMsNow
  setEnv (Environment.ofKernelEnv kenv)
  let kinds := st.consts.fold (init := (∅ : Std.HashMap String Nat)) fun m _ ci =>
    let k := match ci with
      | .thmInfo _ => "theorems" | .defnInfo _ => "definitions" | .inductInfo _ => "inductive types"
      | .ctorInfo _ => "constructors" | .recInfo _ => "recursors" | _ => "others"
    m.insert k (m.getD k 0 + 1)
  logInfo m!"the kernel accepted {st.consts.size} constants in {t1 - t0} ms: {kinds.toList}"
