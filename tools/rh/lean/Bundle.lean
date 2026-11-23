import Lean
open Lean Elab

/-!
Elaborate many source files in one process, as one module.

    lean --tstack=400000 --run Bundle.lean JOB.json

`lean` spends most of the time of a short file on importing Mathlib. This program imports once, then elaborates
each file of the job in turn, in the order given, and writes one `.olean` that holds the declarations of all of
them. Each file is elaborated as `lean` would elaborate it alone:

* its own command state: no namespace, no `open`, the options that the job gives;
* its own main module name, so that its private names are its own;
* its own scope for the scoped extensions, popped at its end, so that an `open` or a `local` attribute of one
  file does not reach the next.

What differs from one process a file: a file sees the declarations, instances and simp lemmas of the files before
it in the job and of every module that the job imports, also of those that the file does not import. A file's own
`import` lines are not read; the job lists the modules to import, and must list the files in an order that respects
their imports. And two files of one job must not declare a private name with the same name: Lean keeps the
declarations of the module being compiled under their names without the private prefix.

Three more things, for a job that does not compile everything:

* the job may give, for a file, line ranges to skip: a command that overlaps one is parsed and not elaborated;
* a namespace that an `open` names is registered first, so that opening a namespace whose declarations were all
  left out is not an error;
* the job may give, for a file, names to rename: a private declaration of a file may bear the name of a public one
  of a file that it does not import, and in a bundle it sees that one;
* and identifiers to read as a given constant in given lines: a short name may mean another declaration in a
  bundle than under the file's own imports (`capture_rewrites.py`); `_private_.X` there is the file's own private
  `X`;
* the proofs that Lean lifts out of a declaration (`d._proof_1`) are shared within a module by their
  statement; each file starts with none, so that they are named as when the file is compiled alone;
* `open N (a b)` wants `N.a` to be a constant, and the file that declares it may be one that the build leaves
  out because nothing uses it: such a name is dropped from the command;
* `open private a from M` names a module, and a file that a bundle holds is not one: the command is done here,
  from the private constants that bear the file's name;
* the instances and the simp lemmas that a file does not import are taken out of its view. One instance made from
  a field of a structure (`attribute [instance] Frame.hl`, a `Fact (Nat.Prime Φ.l)`) is enough to send the
  instance searches of unrelated files astray. The program writes down what each file adds (`views`); the job
  says which files of the lower bundles each file does not import (`leak`, `eraseAll`, `erase`), and what they
  added is erased in a scope that ends with the file. The files before it in the same job are of its level, so
  all that they added is erased too;
* Lean goes on after an error, and a declaration whose elaboration fails may still be declared, with `sorry`
  where the error was. For a theorem that is harmless: its statement is whole, and whoever uses it is checked
  against the statement. For anything else it is not, so with `rollback` the job gives the line ranges of the
  theorems, and a command outside them that logs an error leaves the environment as it was.

With `async` the proof of a theorem is elaborated, and every declaration is checked by the kernel, on the other
threads of the process (`lean -j N`), as `lean` does by default; the errors of those are logged when they end.

Every declaration that is added goes through the kernel, as in `lean`. The errors go to the job's log, and one
line a file to the standard output.
-/

structure FileJob where
  path : String
  module : String
  /-- Ranges of lines to leave out, from 0, both ends included, sorted. -/
  skip : Array (Array Nat)
  /-- Ranges of lines of the theorems, in the same form. -/
  thm : Array (Array Nat)
  /-- Whether the job's `slowOptions` apply. -/
  slow : Bool
  /-- Pairs `[old, new]`: every component `old` of an identifier of the file is read as `new`. A triple
  `[old, new, "decl"]` gives the declarations of the file whose name ends in `old` the name ending in `new`,
  and touches no other identifier (`renameDeclared`). -/
  rename : Option (Array (Array String))
  /-- `[first line, last line, old, new, kind]`: in a command that meets those lines, the identifier `old` is
  read as `new`; inside an `open` if the kind is `"o"` (a namespace), outside one otherwise (a constant). `new`
  may list several constants, `A|B`: the identifier is then a choice among them. -/
  rewrite : Option (Array (Array String))
  /-- Places in the job's `leak` table: what those files added is taken out of view for this file. -/
  erase : Option (Array Nat)
  /-- Groups of instances with one key, each `[name, place]`: within a group Lean is to try them as if they
  had been declared in the order of the places (`reorderInst`). -/
  instOrder : Option (Array (Array (Array String)))
deriving FromJson

/-- The instances and the simp lemmas (`[name, post, inv]`) that one file added, by their printed names. -/
structure Added where
  inst : Array String
  simp : Array (Array String)
deriving FromJson

structure Job where
  name : String
  olean : String
  log : String
  imports : Array String
  /-- The options of every file: `[name, "bool" or "nat", value]`. -/
  options : Array (Array String)
  /-- More options, for the files marked `slow`. -/
  slowOptions : Array (Array String)
  /-- Undo a command that logs an error and is not a theorem. -/
  rollback : Bool
  /-- Elaborate the proofs of theorems, and check declarations in the kernel, on other threads (`lean -j`), as
  `lean` does. Left out, it is false. -/
  async : Option Bool
  /-- What files of lower bundles added, for `erase`. -/
  leak : Option (Array Added)
  /-- The places of `leak` that no file of this job imports: taken out of view for the whole job. -/
  eraseAll : Option (Array Nat)
  /-- Where to write what each file of this job adds, one line of JSON a file. -/
  views : Option String
  /-- Let a file use the proofs that Lean lifted out of the declarations of the files before it in the job
  (`runFile`). Left out, it is false: each file names its lifted proofs as it does alone. -/
  shareProofs : Option Bool
  files : Array FileJob
deriving FromJson

def addOpts (o : Options) (xs : Array (Array String)) : Options := Id.run do
  let mut o := o
  for e in xs do
    let name := e[0]!.toName
    if e[1]! == "bool" then
      o := o.setBool name (e[2]! == "true")
    else
      o := o.set name e[2]!.toNat!
  return o

def fileOpts (job : Job) (slow : Bool) : Options :=
  let o := addOpts (({} : Options).setBool `Elab.async (job.async.getD false)) job.options
  if slow then addOpts o job.slowOptions else o

/-- The messages of a snapshot tree that were not reported before, with those of its children. -/
partial def treeMessages (t : Language.SnapshotTree) (acc : Array Message) : Array Message :=
  t.children.foldl (fun acc c => treeMessages c.get acc) (acc ++ t.element.diagnostics.msgLog.unreported.toArray)

partial def idents (stx : Syntax) (acc : Array Name) : Array Name :=
  match stx with
  | .ident _ _ n _ => acc.push n
  | .node _ _ args => args.foldl (fun acc a => idents a acc) acc
  | _ => acc

def isOpenDecl (k : SyntaxNodeKind) : Bool :=
  k == ``Lean.Parser.Command.openSimple || k == ``Lean.Parser.Command.openScoped
    || k == ``Lean.Parser.Command.openOnly || k == ``Lean.Parser.Command.openHiding
    || k == ``Lean.Parser.Command.openRenaming

/-- The namespaces that the `open`s of a piece of syntax name. -/
partial def openedNamespaces (stx : Syntax) (acc : Array Name) : Array Name :=
  match stx with
  | .node _ k args =>
    if k == ``Lean.Parser.Command.openSimple || k == ``Lean.Parser.Command.openScoped then
      idents stx acc
    else if isOpenDecl k then
      match (idents stx #[])[0]? with
      | some n => acc.push n
      | none => acc
    else
      args.foldl (fun acc a => openedNamespaces a acc) acc
  | _ => acc

/-- Replace the components of the identifiers of a piece of syntax. -/
partial def renameIdents (pairs : Array (String × String)) (stx : Syntax) : Syntax :=
  match stx with
  | .ident info _ n _ =>
    let rec go : Name → Name
      | .str p s => .str (go p) ((pairs.find? (·.1 == s)).map (·.2) |>.getD s)
      | .num p k => .num (go p) k
      | .anonymous => .anonymous
    let n' := go n
    if n' == n then stx else .ident info n'.toString.toRawSubstring n' []
  | .node info k args => .node info k (args.map (renameIdents pairs))
  | _ => stx

/-- The names that the declarations of a command are given (`theorem A.b`, `structure C`), as written. -/
partial def declaredNames (stx : Syntax) (acc : Array Name) : Array Name :=
  match stx with
  | .node _ k args =>
    if k == ``Lean.Parser.Command.declId then
      match args[0]? with
      | some a => if a.isIdent then acc.push a.getId else acc
      | none => acc
    else args.foldl (fun acc a => declaredNames a acc) acc
  | _ => acc

/-- Give another name to the declarations of a command whose name ends in `old`: the last component becomes
`new`, in the declaration's name and wherever the command writes that name again (a recursive definition). No
other identifier is touched: another declaration may end in the same component. -/
partial def renameDeclared (pairs : Array (String × String)) (stx : Syntax) : Syntax :=
  let last (n : Name) : Option (String × Name) := match n with
    | .str p s => some (s, p)
    | _ => none
  let hits := (declaredNames stx #[]).filterMap fun n =>
    match last n with
    | some (s, p) => (pairs.find? (·.1 == s)).map fun (_, new) => (n, Name.str p new)
    | none => none
  if hits.isEmpty then stx else
    let rec go (stx : Syntax) : Syntax :=
      match stx with
      | .ident info _ n _ =>
        match hits.find? (·.1 == n) with
        | some (_, n') => .ident info n'.toString.toRawSubstring n' []
        | none => stx
      | .node info k args => .node info k (args.map go)
      | _ => stx
    go stx

/-- In a file that gives a declaration another name (`renameDeclared`), `h.old` may be that declaration reached
by the type of `h`, which no pin can see. An identifier of several components that ends in `old` and is not, as
a whole, a constant in view gets the new ending. (`A.B.old` that is a constant is another declaration, or the
same one written out, which the pins name.) -/
partial def renameFieldUses (env : Environment) (opts : Options) (ns : Name) (openDecls : List OpenDecl)
    (pairs : Array (String × String)) (stx : Syntax) : Syntax :=
  match stx with
  | .ident info _ n _ =>
    match n with
    | .str p s =>
      if p.isAnonymous then stx else
      match pairs.find? (·.1 == s) with
      | some (_, new) =>
        let whole := (ResolveName.resolveGlobalName env opts ns openDecls n).any (·.2.isEmpty)
        if whole then stx else
          let n' := Name.str p new
          .ident info n'.toString.toRawSubstring n' []
      | none => stx
    | _ => stx
  | .node info k args =>
    if k == ``Lean.Parser.Command.declId then stx
    else .node info k (args.map (renameFieldUses env opts ns openDecls pairs))
  | _ => stx

def nameOfString (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => .str n c) .anonymous

/-- The constant that a pin names: `_private_.X` is the private declaration `X` of the file's own module. -/
def pinName (module : Name) (s : String) : Name :=
  match s.splitOn "." with
  | "_private_" :: rest => mkPrivateNameCore module (rest.foldl (fun n c => .str n c) .anonymous)
  | _ => nameOfString s

/-- A file that sets `maxHeartbeats` for a declaration has measured what the declaration takes when the file is
compiled alone. In a bundle the same elaboration takes more (the tables of instances and of simp lemmas hold
the whole archive below, and looking something up in them costs more), and a limit that the file chose to fit
is passed: "(deterministic) timeout". A timeout is not something a proof can catch and go another way, so a
higher limit changes no result. Every `set_option maxHeartbeats n` and `set_option synthInstance.maxHeartbeats
n` of a file, as a command or before `in`, is read as four times `n` and no less than the bundle's own limit;
`0`, no limit, stays. -/
partial def raiseHeartbeats (stx : Syntax) : Syntax :=
  match stx with
  | .node info k args =>
    let args := args.map raiseHeartbeats
    let floor? : Option Nat :=
      if (k == `Lean.Parser.Command.set_option || k == `Lean.Parser.Term.set_option
          || k == `Lean.Parser.Tactic.set_option) && args.size ≥ 3 then
        if args[1]!.getId == `maxHeartbeats then some 4000000
        else if args[1]!.getId == `synthInstance.maxHeartbeats then some 400000
        else none
      else none
    -- (the value is the third or the fourth part of the command, after a part for a name ending in a dot)
    match floor?, args.findIdx? (·.isNatLit?.isSome) with
    | some low, some i =>
      let n := args[i]!.isNatLit?.getD 0
      if n == 0 then .node info k args
      else .node info k (args.set! i (Syntax.mkNumLit (toString (max (4 * n) low)) (SourceInfo.fromRef args[i]!)))
    | _, _ => .node info k args
  | _ => stx

/-- Replace whole identifiers of a piece of syntax: those of `open` by the pairs marked `true`, the others by
the pairs marked `false`. A pair with several names stands for a name that its file reads in several ways, among
which Lean chooses by type: the identifier becomes a `choice` of them, as an overloaded notation is. -/
partial def rewriteIdents (pairs : Array (String × Array Name × Bool)) (inOpen : Bool) (stx : Syntax) : Syntax :=
  match stx with
  | .ident info _ n _ =>
    match pairs.find? (fun (old, _, o) => o == inOpen && old == n.toString) with
    | some (_, alts, _) =>
      let mk (n' : Name) : Syntax := .ident info n'.toString.toRawSubstring n' []
      if alts.size == 1 then mk alts[0]! else .node info choiceKind (alts.map mk)
    | none => stx
  | .node info k args =>
    -- the name of a field in `{ x := v }` or after `where`, and of an argument in `(x := v)`, is no reference,
    -- though a constant of that name may be in view: the map, which reads the text, takes some for one
    if k == `Lean.Parser.Term.structInstLVal then stx
    else if k == `Lean.Parser.Term.namedArgument && args.size == 5 then
      .node info k (args.mapIdx fun i a => if i == 1 then a else rewriteIdents pairs inOpen a)
    else if k == `Lean.Parser.Command.structFields && args.size == 1 && args[0]!.isOfKind nullKind then
      -- the fields of a `structure`, in order. The name that a field declares is not replaced; in its own
      -- type the name still means what it meant outside (`twist : … twist π.π …`), and from the next field on
      -- it is the field
      let step (acc : Array Syntax × Array (String × Array Name × Bool)) (f : Syntax) :=
        let (out, ps) := acc
        let at? : Option Nat :=
          if f.isOfKind `Lean.Parser.Command.structSimpleBinder then some 1
          else if f.isOfKind `Lean.Parser.Command.structExplicitBinder
            || f.isOfKind `Lean.Parser.Command.structImplicitBinder
            || f.isOfKind `Lean.Parser.Command.structInstBinder then some 2
          else none
        match at? with
        | some i =>
          let declared := (if f[i].isIdent then #[f[i]] else f[i].getArgs).map (·.getId.toString)
          let f' := f.setArgs (f.getArgs.mapIdx fun j a => if j == i then a else rewriteIdents ps inOpen a)
          (out.push f', ps.filter fun (old, _, _) => !declared.contains old)
        | none => (out.push (rewriteIdents ps inOpen f), ps)
      let (fields, _) := args[0]!.getArgs.foldl step (#[], pairs)
      .node info k #[args[0]!.setArgs fields]
    else .node info k (args.map (rewriteIdents pairs (inOpen || isOpenDecl k)))
  | _ => stx

/-- The names that a piece of syntax binds in brackets, after `fun`, in a pattern of `rcases` or by `intro`,
`let` and `have`. The map that says which names to pin finds binders by pattern and misses some; a name that
its command binds this way is not pinned in that command. -/
partial def boundIdents (stx : Syntax) (acc : Array Name) : Array Name :=
  match stx with
  | .node _ k args =>
    let acc := args.foldl (fun acc a => boundIdents a acc) acc
    let direct (a : Syntax) (acc : Array Name) : Array Name :=
      if a.isIdent then acc.push a.getId
      else a.getArgs.foldl (fun acc b => if b.isIdent then acc.push b.getId else acc) acc
    if k == ``Lean.Parser.Term.explicitBinder || k == ``Lean.Parser.Term.implicitBinder
        || k == ``Lean.Parser.Term.strictImplicitBinder || k == ``Lean.Parser.Term.instBinder then
      direct (args[1]?.getD .missing) acc
    else if k == ``Lean.binderIdent || k == ``Lean.Parser.Tactic.rcasesPat.one then
      direct (args[0]?.getD .missing) acc
    else if k == ``Lean.Parser.Term.basicFun then
      direct (args[0]?.getD .missing) acc
    else if k == ``Lean.Parser.Term.letIdDecl || k == `Lean.Parser.Term.haveIdDecl
        || k == `Lean.Parser.Term.haveId || k == `Lean.Parser.Term.letId then
      direct (args[0]?.getD .missing) acc
    else if k == ``Lean.Parser.Tactic.intro then
      direct (args[1]?.getD .missing) acc
    else acc
  | _ => acc

/-- The first range of `rs` from index `i` on that does not end before `first`, and whether it meets
`first..last`. -/
def meets (rs : Array (Nat × Nat)) (i first last : Nat) : Nat × Bool := Id.run do
  let mut i := i
  while i < rs.size && rs[i]!.2 < first do
    i := i + 1
  return (i, i < rs.size && rs[i]!.1 ≤ last && first ≤ rs[i]!.2)

/-- The instances and simp lemmas in view, by printed name, and those met so far. -/
structure Views where
  instOf : Std.HashMap String Name := {}
  simpOf : Std.HashMap String Meta.Origin := {}
  seenInst : Std.HashSet Name := {}
  seenSimp : Std.HashSet Meta.Origin := {}
  /-- Added by the files of this job so far. -/
  mineInst : Array Name := #[]
  mineSimp : Array Meta.Origin := #[]

def simpKey : Meta.Origin → Option (String × String × String)
  | .decl n post inv => some (toString n, if post then "1" else "0", if inv then "1" else "0")
  | _ => none

def Views.ofEnv (env : Environment) : Views := Id.run do
  let mut v : Views := {}
  for (n, _) in (Meta.instanceExtension.getState env).instanceNames do
    v := { v with instOf := v.instOf.insert (toString n) n, seenInst := v.seenInst.insert n }
  for o in (Meta.simpExtension.getState env).lemmaNames do
    v := { v with seenSimp := v.seenSimp.insert o }
    if let some (a, b, c) := simpKey o then
      v := { v with simpOf := v.simpOf.insert (a ++ "|" ++ b ++ "|" ++ c) o }
  return v

/-- Take instances and simp lemmas out of view, in the scope at hand. -/
def eraseFrom (env : Environment) (insts : Array Name) (simps : Array Meta.Origin) : Environment :=
  let env := if insts.isEmpty then env else
    Meta.instanceExtension.modifyState env fun s =>
      insts.foldl (fun s n => if s.instanceNames.contains n then s.eraseCore n else s) s
  if simps.isEmpty then env else
    Meta.simpExtension.modifyState env fun s =>
      simps.foldl (fun s o => if s.lemmaNames.contains o then s.eraseCore o else s) s

/-- The values at the end of a path of keys in a discrimination tree, changed by `f`. -/
partial def modifyLeaf {α : Type} (keys : Array Meta.DiscrTree.Key) (f : Array α → Array α) (i : Nat) :
    Meta.DiscrTree.Trie α → Meta.DiscrTree.Trie α
  | .node vs cs =>
    if i < keys.size then
      .node vs (cs.map fun (k, c) => if k == keys[i]! then (k, modifyLeaf keys f (i + 1) c) else (k, c))
    else
      .node (f vs) cs

/-- Among the instances that fit a goal equally, Lean tries the one declared last first, and for imported
instances "last" is the order in which the modules were imported. A file compiled alone imports its modules in
the order of its own header; in a bundle the instances of the lower levels come level by level. Where a file
sees two instances of one key (`MeasurableSpace (Matrix _ _ _)`, declared three times in the archive, not all
equal by definition) and the two orders differ, the job says so: each group lists instances of one key with
the place of each one's file in the file's own order of imports, and the instances of the group change places
in the tree, in the scope at hand, so that they stand in that order. Instances of one file keep their order. -/
def reorderInst (env : Environment) (groups : Array (Array (Name × Nat))) : Environment :=
  if groups.isEmpty then env else
  Meta.instanceExtension.modifyState env fun s => groups.foldl (init := s) fun s group =>
    let es := group.filterMap fun (n, r) => (s.instanceNames.find? n).map fun e => (e, r)
    if es.size < 2 then s else
    let keys := es[0]!.1.keys
    if keys.isEmpty || !es.all (·.1.keys == keys) then s else
    match s.discrTree.root.find? keys[0]! with
    | none => s
    | some c =>
      let f (vs : Array Meta.InstanceEntry) : Array Meta.InstanceEntry := Id.run do
        -- the places in the tree of the instances of the group, and those instances sorted by their file's
        -- place (an insertion sort: stable, so that the instances of one file keep their order)
        let mut places : Array Nat := #[]
        let mut found : Array (Meta.InstanceEntry × Nat) := #[]
        for h : j in [0:vs.size] do
          if let some (_, r) := es.find? (·.1 == vs[j]) then
            places := places.push j
            found := found.push (vs[j], r)
        let sorted := found.insertionSort fun a b => a.2 < b.2
        let mut out := vs
        for p in places, (e, _) in sorted do
          out := out.set! p e
        return out
      { s with discrTree := { s.discrTree with root := s.discrTree.root.insert keys[0]! (modifyLeaf keys f 1 c) } }

/-- What some places of the job's table added, as names of this environment. -/
def Views.pick (v : Views) (leak : Array Added) (places : Array Nat) : Array Name × Array Meta.Origin := Id.run do
  let mut insts := #[]
  let mut simps := #[]
  for i in places do
    if let some a := leak[i]? then
      for s in a.inst do
        if let some n := v.instOf[s]? then insts := insts.push n
      for t in a.simp do
        if let some o := v.simpOf[t[0]! ++ "|" ++ t[1]! ++ "|" ++ t[2]!]? then simps := simps.push o
  return (insts, simps)

/-- The instances and simp lemmas that are in view now and were not met before. -/
def Views.fresh (v : Views) (env : Environment) : Views × Array Name × Array Meta.Origin := Id.run do
  let mut v := v
  let mut insts := #[]
  let mut simps := #[]
  -- every instance and simp lemma in view is looked at, after every file: a name is printed only if it is new
  for (n, _) in (Meta.instanceExtension.getState env).instanceNames do
    unless v.seenInst.contains n do
      insts := insts.push n
      v := { v with seenInst := v.seenInst.insert n, instOf := v.instOf.insert (toString n) n }
  for o in (Meta.simpExtension.getState env).lemmaNames do
    unless v.seenSimp.contains o do
      v := { v with seenSimp := v.seenSimp.insert o }
      if let some (a, b, c) := simpKey o then
        simps := simps.push o
        v := { v with simpOf := v.simpOf.insert (a ++ "|" ++ b ++ "|" ++ c) o }
  return ({ v with mineInst := v.mineInst ++ insts, mineSimp := v.mineSimp ++ simps }, insts, simps)

/-- `open N (a b)` is an error if `N.a` is not a constant. A file may list a name that it never uses, and the
build compiles only the files whose declarations are used, so the file that declares `N.a` may not be there.
The names that are no constant in any namespace that `N` could be are taken out of the command; `none` if
none is left. The namespaces that `N` could be are those around the command and those that an earlier `open`
reaches (`open A` then `open Chart (a b)` for `A.Chart`).

The command is an error too when Lean finds a name twice, and it can find one constant twice: if a bundle has a
namespace `Chart` at the root, which holds no `a`, Lean looks `Chart.a` up as a name and finds `A.Chart.a`
through the `open A`, beside finding it in `A.Chart`. So when one namespace holds all the names that are left,
the command is made to name that namespace outright (`open _root_.A.Chart (a b)`). -/
def openOnlyKnown (env : Environment) (current : Name) (opened : List OpenDecl) (cmd : Syntax) :
    Option Syntax := Id.run do
  unless cmd.getKind == ``Lean.Parser.Command.open && cmd.getNumArgs == 2 do return some cmd
  let decl := cmd[1]
  unless decl.getKind == ``Lean.Parser.Command.openOnly && decl.getNumArgs == 4 do return some cmd
  let ns := decl[0].getId
  let rooted := ns.getRoot == `_root_
  let ns := if rooted then ns.replacePrefix `_root_ .anonymous else ns
  -- the namespaces around the command, innermost first, what the open namespaces make of `N`, and the root
  let mut around : Array Name := #[]
  unless rooted do
    let mut c := current
    while !c.isAnonymous do
      around := around.push (c ++ ns)
      c := c.getPrefix
    for o in opened do
      if let .simple o _ := o then
        around := around.push (o ++ ns)
  around := around.push ns
  -- a name that `export` put in the namespace is an alias, and no constant
  let holds (p id : Name) : Bool :=
    env.contains (p ++ id) || !(getAliases env (p ++ id) (skipProtected := false)).isEmpty
  let ids := decl[2].getArgs
  let kept := ids.filter fun i => around.any (holds · i.getId)
  if kept.isEmpty then return none
  let homes := around.foldl (init := (#[] : Array Name)) fun acc p =>
    if !acc.contains p && kept.any (fun i => holds p i.getId) then acc.push p else acc
  let decl := decl.setArg 2 (decl[2].setArgs kept)
  let decl := if homes.size == 1 then decl.setArg 0 (mkIdentFrom decl[0] (`_root_ ++ homes[0]!)) else decl
  return some (cmd.setArg 1 decl)

/-- The same for the `open` of `open N (a b) in c`, also behind `set_option … in`; `c` alone if no name is
left. -/
partial def openOnlyKnownIn (env : Environment) (current : Name) (opened : List OpenDecl) (cmd : Syntax) :
    Option Syntax :=
  if cmd.getKind == ``Lean.Parser.Command.in && cmd.getNumArgs == 3 then
    let rest := (openOnlyKnownIn env current opened cmd[2]).getD cmd[2]
    if cmd[0].getKind == ``Lean.Parser.Command.open then
      match openOnlyKnown env current opened cmd[0] with
      | some o => some ((cmd.setArg 0 o).setArg 2 rest)
      | none => some rest
    else
      some (cmd.setArg 2 rest)
  else
    openOnlyKnown env current opened cmd

def jsonStr (s : String) : String := (Json.str s).compress

/-- `open private a b from M` (Batteries) looks `M` up among the imported modules. A file of the archive that a
bundle holds is not one: its private declarations are constants of the bundle, still named after the file
(`_private.M.0.a`). If some module of the command is not imported, the command is done here: the open
declarations that it would add, or `none` if a name is not found exactly once (the command is then left to
Batteries, which reports it). -/
def openPrivateBundled (env : Environment) (cmd : Syntax) : Option (List OpenDecl) := Id.run do
  unless cmd.getKind == `Lean.Elab.Command.openPrivate && cmd.getNumArgs == 5 do return none
  -- "open" "private" ident* (" in" ident*)? (" from" ident*)?
  unless cmd[3].getNumArgs == 0 && cmd[4].getNumArgs == 2 do return none
  let ids := cmd[2].getArgs.map (·.getId)
  let mods := cmd[4][1].getArgs.map (·.getId)
  let imported := env.allImportedModuleNames
  if mods.all (imported.contains ·) then return none
  let idx := mods.filterMap (imported.idxOf? ·)
  let found : Array (List Name) := env.constants.fold (init := ids.map fun _ => []) fun found c _ =>
    match privateToUserName? c with
    | none => found
    | some user =>
      let here := mods.any (fun m => mkPrivateNameCore m user == c) ||
        (match env.getModuleIdxFor? c with
         | some i => idx.contains i.toNat
         | none => false)
      if here then found.mapIdx fun k l => if ids[k]!.isSuffixOf c then c :: l else l else found
  let mut decls := []
  for k in [0:ids.size] do
    match found[k]! with
    | [c] => decls := OpenDecl.explicit ids[k]! c :: decls
    | _ => return none
  return some decls

structure Tally where
  errors : Array Message := #[]
  skipped : Nat := 0
  undone : Nat := 0
  /-- The snapshots of theorems whose proofs may still be running. -/
  pending : Array (Language.SnapshotTask Language.SnapshotTree) := #[]

/-- Parse and elaborate the commands of the current file. The command elaborator empties the message log at each
command, and puts the messages of a declaration in the snapshot of its elaboration: the errors are taken from both
after each command, and from the parser. -/
partial def processFile (rollback : Bool) (skip thm : Array (Nat × Nat)) (rename declRename : Array (String × String))
    (rewrite : Array (Nat × Nat × String × Array Name × Bool)) (tally : IO.Ref Tally) (i j : Nat) :
    Frontend.FrontendM Unit := do
  Frontend.updateCmdPos
  let cmdState ← Frontend.getCommandState
  let ictx ← Frontend.getInputContext
  let pstate ← Frontend.getParserState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace,
                 openDecls := scope.openDecls }
  let (cmd, ps, parseMsgs) := Parser.parseCommand ictx pmctx pstate {}
  let cmd := raiseHeartbeats cmd
  let cmd := if rename.isEmpty then cmd else renameIdents rename cmd
  let cmd := if declRename.isEmpty then cmd else
    renameFieldUses cmdState.env scope.opts scope.currNamespace scope.openDecls declRename (renameDeclared declRename cmd)
  Frontend.setParserState ps
  let keep (xs : Array Message) : Array Message := xs.filter (·.severity matches .error)
  tally.modify fun t => { t with errors := t.errors ++ keep parseMsgs.unreported.toArray }
  let line (p : Option String.Pos.Raw) (d : Nat) : Nat :=
    match p with
    | some p => (ictx.fileMap.toPosition p).line - 1
    | none => d
  let first := line cmd.getPos? 0
  let last := line cmd.getTailPos? first
  -- the namespaces are registered as the file writes them, before any is pinned
  let spaces := openedNamespaces cmd #[]
  let here := rewrite.filterMap fun (a, b, old, new, o) =>
    if a ≤ last && first ≤ b then some (old, new, o) else none
  let cmd := if here.isEmpty then cmd else
    let bound := (boundIdents cmd #[]).map (·.toString)
    rewriteIdents (here.filter fun (old, _, o) => o || !bound.contains old) false cmd
  let (i, out) := meets skip i first last
  let (j, isThm) := meets thm j first last
  if out then
    tally.modify fun t => { t with skipped := t.skipped + 1 }
  else
    unless spaces.isEmpty do
      Frontend.setCommandState { cmdState with env := spaces.foldl (·.registerNamespace ·) cmdState.env }
    let before := (← Frontend.getCommandState).env
    match openPrivateBundled before cmd with
    | some decls =>
      let st0 ← Frontend.getCommandState
      Frontend.setCommandState { st0 with scopes := match st0.scopes with
        | s :: rest => { s with openDecls := decls ++ s.openDecls } :: rest
        | [] => [] }
    | none => Frontend.elabCommandAtFrontend cmd
    let st ← Frontend.getCommandState
    let mut msgs := st.messages.unreported.toArray
    -- a theorem is not undone, so its proof need not be waited for
    let later := isThm && Elab.async.get scope.opts
    unless later do
      for t in st.snapshotTasks do
        msgs := treeMessages t.get msgs
    let mut errs := keep msgs
    -- `open N (a b)` that failed, alone or before `in`: once more without the names that are not there, and
    -- with the namespace named outright (see `openOnlyKnown`)
    if !errs.isEmpty && (cmd.getKind == ``Lean.Parser.Command.open || cmd.getKind == ``Lean.Parser.Command.in) then
      match openOnlyKnownIn before scope.currNamespace scope.openDecls cmd with
      | some cmd' =>
        if cmd' != cmd then
          Frontend.setCommandState cmdState
          Frontend.elabCommandAtFrontend cmd'
          let st' ← Frontend.getCommandState
          let mut msgs' := st'.messages.unreported.toArray
          unless later do
            for t in st'.snapshotTasks do
              msgs' := treeMessages t.get msgs'
          errs := keep msgs'
      | none =>
        Frontend.setCommandState cmdState
        errs := #[]
    let st ← Frontend.getCommandState
    let undo := rollback && !isThm && !errs.isEmpty
    tally.modify fun t => { t with
      errors := t.errors ++ errs, undone := if undo then t.undone + 1 else t.undone,
      pending := if later then t.pending ++ st.snapshotTasks else t.pending }
    Frontend.setCommandState { st with snapshotTasks := #[], env := if undo then before else st.env }
  if Parser.isTerminalCommand cmd then
    return
  processFile rollback skip thm rename declRename rewrite tally i j

/-- Elaborate one file on top of `env`. -/
def runFile (job : Job) (env : Environment) (f : FileJob) (log : IO.FS.Handle) (views : Views)
    (side : Option IO.FS.Handle) : IO (Environment × Tally × Views) := do
  let input ← IO.FS.readFile f.path
  let inputCtx := Parser.mkInputContext input f.path
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let env := env.setMainModule f.module.toName
  -- Lean names the proofs that it lifts out of a declaration `d._proof_1`, `d._proof_2`, and uses one again
  -- when the same statement comes up in the module. A file may name them (`attribute [local instance]
  -- S.lf._proof_1`), so each file starts with none, as it does alone. The bundles made before this was so
  -- shared them across their files, and the terms of the bundles above name what they made: such a bundle is
  -- compiled again with `shareProofs`, which gives its lifted proofs the names and numbers that they had
  let env := if job.shareProofs.getD false then env else Meta.auxLemmasExt.setState env {}
  let cmdState := Command.mkState env {} (fileOpts job f.slow)
  let pair (r : Array Nat) : Nat × Nat := (r[0]!, r[1]!)
  let tally ← IO.mkRef ({ errors := messages.unreported.toArray.filter (·.severity matches .error) } : Tally)
  -- out of view for this file: what the files before it in the job added (they are of its level, so it does not
  -- import them), and what the job says of the lower bundles
  let (lowInst, lowSimp) := views.pick (job.leak.getD #[]) (f.erase.getD #[])
  let act : Frontend.FrontendM Unit := do
    Frontend.runCommandElabM (do
      pushScope
      modifyEnv fun env => eraseFrom env (views.mineInst ++ lowInst) (views.mineSimp ++ lowSimp)
      modifyEnv fun env => reorderInst env ((f.instOrder.getD #[]).map fun g =>
        g.filterMap fun r => if r.size == 2 then (views.instOf[r[0]!]?).map (·, r[1]!.toNat!) else none))
    processFile job.rollback (f.skip.map pair) (f.thm.map pair)
      (((f.rename.getD #[]).filter (·.size == 2)).map fun r => (r[0]!, r[1]!))
      (((f.rename.getD #[]).filter (·.size == 3)).map fun r => (r[0]!, r[1]!))
      ((f.rewrite.getD #[]).map fun r =>
        (r[0]!.toNat!, r[1]!.toNat!, r[2]!, ((r[3]!.splitOn "|").map (pinName f.module.toName)).toArray,
          r[4]? == some "o")) tally 0 0
    Frontend.runCommandElabM (do
      let n := (← get).scopes.length
      for _ in [0:n] do
        popScope)
  let ((), st) ← (act.run { inputCtx }).run
    { commandState := cmdState, parserState, cmdPos := parserState.pos }
  let t ← tally.get
  for msg in t.errors do
    log.putStrLn (← msg.toString)
  log.flush
  let env := st.commandState.env
  let (views, insts, simps) := views.fresh env
  if let some h := side then
    let simpRows := simps.filterMap fun o => (simpKey o).map fun (a, b, c) => s!"[{jsonStr a},\"{b}\",\"{c}\"]"
    -- with each instance its key, as text: two instances with one key are tried in the order of their import
    let tree := (Meta.instanceExtension.getState env).instanceNames
    let keyOf (n : Name) : String := match tree.find? n with
      | some e => " ".intercalate (e.keys.toList.map fun k => toString (format k))
      | none => ""
    h.putStrLn s!"\{\"m\": {jsonStr f.module}, \"inst\": [{", ".intercalate (insts.toList.map fun n => jsonStr (toString n))}], \"keys\": [{", ".intercalate (insts.toList.map fun n => jsonStr (keyOf n))}], \"simp\": [{", ".intercalate simpRows.toList}]}"
    h.flush
  return (env, t, views)

/-- Wait for the proofs still running, and log their errors. -/
def drain (pending : Array (Language.SnapshotTask Language.SnapshotTree)) (log : IO.FS.Handle) : IO Nat := do
  let mut n := 0
  for t in pending do
    for msg in treeMessages t.get #[] do
      if msg.severity matches .error then
        n := n + 1
        log.putStrLn (← msg.toString)
  log.flush
  return n

def runJob (job : Job) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let log ← IO.FS.Handle.mk job.log .write
  let imports : Array Import :=
    #[{ module := `Init }, { module := `Init, isMeta := true }] ++ job.imports.map fun s => { module := s.toName }
  let mut env ← importModules (loadExts := true) imports (fileOpts job false) 0
  let mut views := Views.ofEnv env
  let (allInst, allSimp) := views.pick (job.leak.getD #[]) (job.eraseAll.getD #[])
  env := eraseFrom env allInst allSimp
  let side ← job.views.mapM fun p => IO.FS.Handle.mk p .write
  let t1 ← IO.monoMsNow
  IO.println s!"\{\"imported\": {t1 - t0}}"
  let mut bad := 0
  let mut pending : Array (Language.SnapshotTask Language.SnapshotTree) := #[]
  let mut late := 0
  for f in job.files do
    let s ← IO.monoMsNow
    try
      let (env', t, views') ← runFile job env f log views side
      env := env'
      views := views'
      pending := pending ++ t.pending
      if pending.size > 2000 then
        late := late + (← drain pending log)
        pending := #[]
      if !t.errors.isEmpty then
        bad := bad + 1
      let e ← IO.monoMsNow
      IO.println s!"\{\"m\": \"{f.module}\", \"errors\": {t.errors.size}, \"skipped\": {t.skipped}, \"undone\": {t.undone}, \"ms\": {e - s}}"
    catch ex =>
      bad := bad + 1
      log.putStrLn s!"{f.path}:1:0: error: exception: {ex}"
      IO.println s!"\{\"m\": \"{f.module}\", \"errors\": -1, \"skipped\": 0, \"undone\": 0, \"ms\": 0}"
    (← IO.getStdout).flush
  late := late + (← drain pending log)
  let t2 ← IO.monoMsNow
  writeModule (env.setMainModule job.name.toName) job.olean
  let t3 ← IO.monoMsNow
  IO.println s!"\{\"done\": \"{job.name}\", \"files\": {job.files.size}, \"bad\": {bad}, \"late\": {late}, \"elab_ms\": {t2 - t1}, \"write_ms\": {t3 - t2}}"
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | throw <| IO.userError "usage: Bundle.lean JOB.json"
  let job : Job ← IO.ofExcept ((Json.parse (← IO.FS.readFile path)) >>= fromJson?)
  enableInitializersExecution
  -- the main thread's stack is the system's; a dedicated thread has the stack that `--tstack` asks for
  let task ← IO.asTask (prio := .dedicated) (runJob job)
  match task.get with
  | .ok r => return r
  | .error e => throw e
