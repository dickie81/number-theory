import Lean
open Lean

/-!
Write a copy of a compiled bundle that holds every constant with its type, and no proof of a theorem.

    lean --run Slim.lean JOB.json

    JOB.json: {"files": [["…/olean/B/l001n000.olean", "…/olean-slim/B/l001n000.olean", "B.l001n000"], …],
               "keep": ["Formalism.X.wf_lemma", …]}

To import a module Lean looks at every constant of it, and the constants of a compiled file lie among their
proofs: an import reads every page of every file. With 800 bundles that is 30 GB, more than the memory that the
five processes of a build leave free, so each import reads most of it from the disk again: three minutes a
bundle, more than compiling it takes, and more with every level.

Nothing that is built on a theorem needs its proof, only its statement: the elaborator never unfolds a theorem,
and for the kernel any two proofs of a statement are equal. (The one exception is a function defined by
well-founded recursion that the kernel is made to compute: it then unfolds the proof that the recursion ends.)
So the bundles above are compiled, and checked again by the kernel, against these copies, in which the value of
a theorem `T` is the constant `_slim_.T`, which does not exist. A check that passes against them passes against
the whole files, because it never looked at a proof; one that needs the proof of `T` stops at `_slim_.T`, and
the kernel's message names it. `T` then goes on the list of the theorems whose proofs the copies keep (`keep` in
the job), the copy of its bundle is made again, and the check is run again. The proofs themselves are checked where they are: each bundle is compiled, and
checked again, from its own whole file. What a theorem rests on is read from the whole files too
(`bundle_check.py`).

A proof that the kernel unfolds is seldom the last: it reduces the proof to a constructor, and the proof of
`T` is as a rule another theorem applied to proofs, so the kernel unfolds that one next, and stops at the next
`_slim_`. To spare a compilation for each link of such a chain, the line of a file names, for each theorem whose
proof it keeps, the constants at the head of that proof (`heads` below); `bundle_build.py` keeps the proofs of
those that are theorems of the archive too, and so on to the end of the chain.

It prints one line of JSON a file: `{"slim": name, "bytes": n, "of": m, "theorems": k, "heads": {T: [names]}}`.
-/

/-- The constants that the kernel may unfold next when it reduces the proof `e` to a constructor: the head of
the term under its binders, through applications and projections, and the heads of the arguments, to the depth
given (a proof is unfolded when the body of the theorem it is given to takes it apart). -/
partial def heads (e : Expr) (depth : Nat) (acc : NameSet) : NameSet :=
  match e with
  | .lam _ _ b _ => heads b depth acc
  | .letE _ _ v b _ => heads b depth (heads v depth acc)
  | .mdata _ b => heads b depth acc
  | .proj _ _ s => heads s depth acc
  | .const n _ => acc.insert n
  | .app .. =>
    let acc := match e.getAppFn with
      | .const n _ => acc.insert n
      | f => if f.isApp then acc else heads f depth acc
    if depth == 0 then acc else e.getAppArgs.foldl (fun acc a => heads a (depth - 1) acc) acc
  | _ => acc

structure SlimJob where
  files : Array (Array String)
  /-- The theorems whose proofs stay, by their printed names. -/
  keep : Option (Array String)
deriving FromJson

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | throw <| IO.userError "usage: Slim.lean JOB.json"
  let job : SlimJob ← IO.ofExcept ((Json.parse (← IO.FS.readFile path)) >>= fromJson?)
  let keep : Std.HashSet String := (job.keep.getD #[]).foldl (fun acc n => acc.insert n) {}
  for row in job.files do
    let src := row[0]!
    let dst := row[1]!
    let (data, region) ← readModuleData src
    let mut k := 0
    let mut cs : Array ConstantInfo := Array.mkEmpty data.constants.size
    let mut next : Array (String × Json) := #[]
    for c in data.constants do
      match c with
      | .thmInfo v =>
        if keep.contains (toString v.name) then
          cs := cs.push c
          let hs := (heads v.value 2 {}).toArray.filterMap fun n =>
            if n == v.name then none else some (Json.str (toString n))
          next := next.push (toString v.name, Json.arr hs)
        else
          k := k + 1
          cs := cs.push (.thmInfo { v with value := .const (`_slim_ ++ v.name) [] })
      | c => cs := cs.push c
    -- written beside the place and moved there, so that a process that imports never sees half a file
    let tmp := dst ++ ".part"
    saveModuleData tmp row[2]!.toName { data with constants := cs }
    IO.FS.rename tmp dst
    let a := (← System.FilePath.metadata dst).byteSize
    let b := (← System.FilePath.metadata src).byteSize
    IO.println s!"\{\"slim\": {(Json.str row[2]!).compress}, \"bytes\": {a}, \"of\": {b}, \"theorems\": {k}, \"heads\": {(Json.mkObj next.toList).compress}}"
    (← IO.getStdout).flush
    region.free
  return 0
