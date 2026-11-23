import Lean
open Lean

/-!
Check every declaration of every compiled bundle again, in the kernel, in one pass over the whole files.

    lean -j 10 --tstack=400000 --run ReplayAll.lean JOB.json

    JOB.json: {"imports": ["Mathlib", …],                               -- taken as they are
               "bundles": [["l001n000", "…/olean/B/l001n000.olean", "check"], …],   -- in the order of the build
               "window": 4000}

`Recheck.lean` checks one bundle: it imports everything below it and sends the bundle's constants to the kernel.
For a build of sixteen hundred bundles that is sixteen hundred imports of everything, each of some gigabytes of
memory. This program imports nothing of the build. It starts from the environment of the modules in `imports`
and goes through the bundles in order, a bundle of a level after all bundles of the levels below. Each `.olean`
is read as data. Every constant in it is put in the environment without a check, in an order in which a
constant comes after the constants it names, and is checked by the kernel in a task of its own against the
environment as it was just before the constant went in. The environment is a persistent structure, so the one
before each constant costs a path of a tree, and the checks run on all the threads while the main thread goes
on.

What that proves. Write c₁, c₂, … for the constants in the order in which they went in. The task of cₙ asks
the kernel (`Lean.Kernel.Environment.addDeclCore`, the function that checks every declaration that Lean
elaborates) whether cₙ is a correct declaration over the modules of `imports` and c₁ … cₙ₋₁. If every task
says yes, then by induction on n every cₙ is one, and the environment that holds them all is what the kernel
would have built by checking them one after another. Nothing that the build did is taken on trust for it: not
the order in which the bundles were made, not the copies without proofs (`Slim.lean`), not the repairs. What is
taken on trust is the kernel, the reader of `.olean` files, and the compiled files of the modules in `imports`.

Inductive types are added with the check, on the main thread (the kernel has no other way to add one, and
they are cheap); constructors and recursors are not sent, the kernel makes them, and the ones in the file are
compared with the ones it made, as `Lean.Environment.replay` does. Constants marked `unsafe` or `partial` are
left out, as there: nothing that the kernel accepts can name one.

A theorem that the environment holds already under the same name with the same statement (a lemma that Lean
makes on demand, made in two bundles) is counted as `known`, and its proof is checked under another name. Any
other constant whose name is taken is refused.

A bundle marked "trust" is put in without the tasks: `bundle_replay.py` marks so the bundles that an earlier
pass accepted, when their files and the files of all bundles before them are the same bytes.

One line of JSON a bundle, in order:

    {"bundle": …, "ok": true, "constants": n, "known": k, "skipped": s, "declares": [axioms it declares],
     "uses": [axioms of the modules below that its constants name], "absent": imports not before it,
     "errors": [[constant, the kernel's message], …], "refused": number of errors, "ms": since the start,
     "check_ms": the time of its checks added up, "slow": [[constant, ms], …] the longest of 5 s and more,
     "n_slow": how many took that long}

and a last line `{"done": true, …}`.
-/

structure PassJob where
  imports : Array String
  bundles : Array (Array String)
  window : Nat := 4000
deriving FromJson

/-- What a check says: nothing, or the kernel's refusal. -/
abbrev Verdict := Option Kernel.Exception

def checkDecl (env : Kernel.Environment) (d : Declaration) : Verdict :=
  match env.addDeclCore 0 0 d none with
  | .ok _ => none
  | .error ex => some ex

/-- A check on a thread of its own, with the milliseconds it took. -/
abbrev Timed := Task (Except IO.Error (Verdict × Nat))

def timed (env : Kernel.Environment) (d : Declaration) : BaseIO Timed :=
  IO.asTask do
    let t0 ← IO.monoMsNow
    let v ← IO.lazyPure fun _ => checkDecl env d
    return (v, (← IO.monoMsNow) - t0)

structure Uses where
  /-- the constants of the same bundle that a constant names -/
  inside : Array Name := #[]
  /-- the axioms below the bundle that it names -/
  axioms : Array Name := #[]

def usesOf (env : Kernel.Environment) (fresh : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) : Uses := Id.run do
  let mut u : Uses := {}
  for n in ci.getUsedConstantsAsSet do
    if fresh.contains n then
      u := { u with inside := u.inside.push n }
    else if let some (.axiomInfo _) := env.find? n then
      u := { u with axioms := u.axioms.push n }
  return u

/-- A bundle whose checks are running. -/
structure Running where
  bundle : String
  checks : Array (Name × Timed) := #[]
  errors : Array (Name × String) := #[]
  constants : Nat := 0
  known : Nat := 0
  skipped : Nat := 0
  declares : Array Name := #[]
  uses : Array Name := #[]
  absent : Nat := 0
deriving Inhabited

structure St where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  ctors : Array Name := #[]
  recs : Array Name := #[]
  run : Running

abbrev M := StateRefT St IO

def fail (name : Name) (msg : String) : M Unit :=
  modify fun s => { s with run := { s.run with errors := s.run.errors.push (name, msg) } }

def say (ex : Kernel.Exception) : IO String := do
  let s ← (ex.toMessageData {}).toString
  return if s.length > 1500 then String.ofList (s.toList.take 1500) ++ " …" else s

/-- Put a definition, theorem, opaque constant or axiom in, and start its check. -/
def plain (check : Bool) (name : Name) (d : Declaration) : M Unit := do
  let env := (← get).env
  if check then
    let t ← timed env d
    modify fun s => { s with run := { s.run with checks := s.run.checks.push (name, t) } }
  match env.addDeclWithoutChecking d with
  | .ok env' => modify fun s => { s with env := env' }
  | .error ex => fail name (← say ex)

/-- `Lean.Environment.Replay.replayConstant`, with `plain` for the kernel's `addDecl`. -/
partial def visit (fresh : Std.HashMap Name ConstantInfo) (uses : Std.HashMap Name (Array Name)) (check : Bool)
    (name : Name) : M Unit := do
  unless (← get).remaining.contains name do return
  modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
  let some ci := fresh[name]? | return
  for n in uses.getD name #[] do
    visit fresh uses check n
  -- a block of inductive types may have taken care of it
  unless (← get).pending.contains name do return
  match ci with
  | .defnInfo info => plain check name (.defnDecl info)
  | .thmInfo info => plain check name (.thmDecl info)
  | .opaqueInfo info => plain check name (.opaqueDecl info)
  | .axiomInfo info =>
    modify fun s => { s with run := { s.run with declares := s.run.declares.push name } }
    plain check name (.axiomDecl info)
  | .inductInfo info =>
    let mut all : Array ConstantInfo := #[]
    for n in info.all do
      match fresh[n]? with
      | some c => all := all.push c
      | none => fail name s!"the inductive type {n} of its block is not in the bundle"
    for o in all do
      modify fun s => { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
    let mut types : Array InductiveType := #[]
    let mut whole := all.size == info.all.length
    for c in all do
      match c with
      | .inductInfo iv =>
        let mut ctors : Array Constructor := #[]
        for cn in iv.ctors do
          match fresh[cn]? with
          | some cc =>
            -- what the constructors name must be in before the type
            for n in uses.getD cn #[] do
              visit fresh uses check n
            ctors := ctors.push { name := cc.name, type := cc.type }
          | none =>
            fail name s!"the constructor {cn} is not in the bundle"
            whole := false
        types := types.push { name := c.name, type := c.type, ctors := ctors.toList }
      | _ =>
        fail name s!"{c.name} of its block is not an inductive type"
        whole := false
    if whole then
      match (← get).env.addDeclCore 0 0 (.inductDecl info.levelParams info.numParams types.toList false) none with
      | .ok env' => modify fun s => { s with env := env' }
      | .error ex => fail name (← say ex)
  | .ctorInfo _ => modify fun s => { s with ctors := s.ctors.push name }
  | .recInfo _ => modify fun s => { s with recs := s.recs.push name }
  | .quotInfo _ => fail name "a bundle declares the quotient"
  modify fun s => { s with pending := s.pending.erase name }

/-- Put the constants of one bundle in; its checks are left running. -/
def addBundle (env : Kernel.Environment) (base bundles : NameSet) (name path : String) (check : Bool) :
    IO (Kernel.Environment × Running) := do
  let (data, _) ← readModuleData path
  let mut run : Running := { bundle := name }
  for i in data.imports do
    unless base.contains i.module do
      if (toString i.module).startsWith "B." then
        unless bundles.contains i.module do run := { run with absent := run.absent + 1 }
      else
        run := { run with errors := run.errors.push (i.module, "the bundle imports this module, and the pass does not hold it") }
  -- the constants that are new, the theorems that are there already, the ones that are left out
  let mut fresh : Std.HashMap Name ConstantInfo := {}
  let mut again : Array TheoremVal := #[]
  for ci in data.constants do
    match env.find? ci.name with
    | some old =>
      match old, ci with
      | .thmInfo a, .thmInfo b =>
        if a.type == b.type && a.levelParams == b.levelParams && a.all == b.all then
          again := again.push b
        else
          run := { run with errors := run.errors.push (ci.name, "a theorem of this name with another statement is below") }
      | _, _ => run := { run with errors := run.errors.push (ci.name, "a constant of this name is below") }
    | none =>
      if ci.isUnsafe || ci.isPartial then
        run := { run with skipped := run.skipped + 1 }
      else if fresh.contains ci.name then
        run := { run with errors := run.errors.push (ci.name, "the bundle holds two constants of this name") }
      else
        fresh := fresh.insert ci.name ci
  run := { run with constants := fresh.size, known := again.size }
  -- what each constant names: the traversals run on the threads, before the checks that wait there
  let tasks := data.constants.filterMap fun ci =>
    if fresh.contains ci.name then
      some (ci.name, Task.spawn (prio := .max) fun _ => usesOf env fresh ci)
    else none
  let mut uses : Std.HashMap Name (Array Name) := {}
  let mut axioms : NameSet := {}
  for (n, t) in tasks do
    let u := t.get
    uses := uses.insert n u.inside
    for a in u.axioms do axioms := axioms.insert a
  run := { run with uses := axioms.toArray }
  let st : St := { env, run, remaining := fresh.fold (init := {}) fun s n _ => s.insert n }
  let ((), st) ← (do
    for n in data.constNames do
      visit fresh uses check n
    -- the constructors and recursors of the file are the ones that the kernel made
    let s ← get
    for c in s.ctors do
      match s.env.find? c, fresh[c]? with
      | some (.ctorInfo a), some (.ctorInfo b) =>
        unless a == b do fail c "is not the constructor that the kernel makes"
      | _, _ => fail c "the kernel made no such constructor"
    for r in s.recs do
      match s.env.find? r, fresh[r]? with
      | some (.recInfo a), some (.recInfo b) =>
        unless a == b do fail r "is not the recursor that the kernel makes"
      | _, _ => fail r "the kernel made no such recursor"
    unless (← get).remaining.isEmpty && (← get).pending.isEmpty do
      fail .anonymous "constants were left over"
    : M Unit).run st
  run := st.run
  if check then
    -- the proofs of the theorems that were there already, under another name
    for t in again do
      let other := t.name ++ `_checked_again_
      let d := Declaration.thmDecl { t with name := other, all := [other] }
      run := { run with checks := run.checks.push (t.name, ← timed st.env d) }
  return (st.env, run)

def names (xs : Array Name) : Json := Json.arr (xs.map fun n => Json.str (toString n))

def allDone (run : Running) : IO Bool := do
  for (_, t) in run.checks do
    unless ← IO.hasFinished t do return false
  return true

def notDone (run : Running) : IO Nat := do
  let mut k := 0
  for (_, t) in run.checks do
    unless ← IO.hasFinished t do k := k + 1
  return k

/-- Wait for the checks of a bundle and print its line. Returns (constants, errors). -/
def finish (run : Running) (t0 : Nat) : IO (Nat × Nat) := do
  let mut errors := run.errors
  let mut spent := 0
  let mut slow : Array (Name × Nat) := #[]
  for (n, t) in run.checks do
    match t.get with
    | .ok (v, ms) =>
      spent := spent + ms
      if ms >= 5000 then slow := slow.push (n, ms)
      if let some ex := v then
        errors := errors.push (n, ← say ex)
    | .error e => errors := errors.push (n, toString e)
  let shown := errors.extract 0 20
  let slowest := (slow.qsort fun a b => a.2 > b.2).extract 0 8
  let line := Json.mkObj [
    ("bundle", Json.str run.bundle), ("ok", Json.bool errors.isEmpty), ("constants", toJson run.constants),
    ("known", toJson run.known), ("skipped", toJson run.skipped), ("declares", names run.declares),
    ("uses", names run.uses), ("absent", toJson run.absent),
    ("errors", Json.arr (shown.map fun (n, m) => Json.arr #[Json.str (toString n), Json.str m])),
    ("refused", toJson errors.size), ("ms", toJson ((← IO.monoMsNow) - t0)), ("check_ms", toJson spent),
    ("slow", Json.arr (slowest.map fun (n, ms) => Json.arr #[Json.str (toString n), toJson ms])),
    ("n_slow", toJson slow.size)]
  IO.println line.compress
  (← IO.getStdout).flush
  return (run.constants, errors.size)

def pass (job : PassJob) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let imports : Array Import := #[{ module := `Init }] ++ job.imports.map fun s => { module := s.toName }
  -- the environment of the modules below the build lives as long as the process: no counting of references
  let env ← importModules imports {} 0 (leakEnv := true)
  let base : NameSet := env.header.moduleNames.foldl (init := {}) fun s n => s.insert n
  let mut kenv := env.toKernelEnv
  let mut bundles : NameSet := {}
  let mut queue : Array Running := #[]
  let mut head := 0
  let mut total := 0
  let mut refused := 0
  let mut bad := 0
  for row in job.bundles do
    let (kenv', run) ← addBundle kenv base bundles row[0]! row[1]! (row[2]! != "trust")
    kenv := kenv'
    bundles := bundles.insert (`B ++ row[0]!.toName)
    queue := queue.push run
    -- print the bundles that are done, in order; go on while fewer than `window` checks are not
    repeat
      while head < queue.size do
        let r := queue[head]!
        unless ← allDone r do break
        let (n, e) ← finish r t0
        total := total + n
        refused := refused + e
        if e > 0 then bad := bad + 1
        queue := queue.set! head { bundle := r.bundle }
        head := head + 1
      let mut waiting := 0
      for k in [head:queue.size] do
        waiting := waiting + (← notDone queue[k]!)
      if waiting < job.window then break
      IO.sleep 20
  while head < queue.size do
    let (n, e) ← finish queue[head]! t0
    total := total + n
    refused := refused + e
    if e > 0 then bad := bad + 1
    queue := queue.set! head { bundle := queue[head]!.bundle }
    head := head + 1
  let line := Json.mkObj [("done", Json.bool true), ("bundles", toJson job.bundles.size), ("constants", toJson total),
    ("refused", toJson refused), ("bad", toJson bad), ("ms", toJson ((← IO.monoMsNow) - t0))]
  IO.println line.compress
  return if refused == 0 then 0 else 1

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | throw <| IO.userError "usage: ReplayAll.lean JOB.json"
  let job : PassJob ← IO.ofExcept ((Json.parse (← IO.FS.readFile path)) >>= fromJson?)
  -- the main thread's stack is the system's; a dedicated thread has the stack that `--tstack` asks for
  let task ← IO.asTask (prio := .dedicated) (pass job)
  match task.get with
  | .ok r => return r
  | .error e => throw e
